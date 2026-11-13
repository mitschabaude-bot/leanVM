module

public import LeanVM.Cost.EvaluationsSize
public import LeanVM.Cost.Bounds.Evaluations
public import LeanVM.Cost.Efficient
import all LeanVM.Protocol.Extraction.Extractor
import all LeanVM.Protocol.Extraction.Fast.Evaluations
import all LeanVM.Protocol.Extraction.Fast.Lookup

/-!
# The extractor on a list of evaluations, run within its budget

`compiledEvaluationsExtractor` (`Cost/EvaluationsProgram.lean`) runs `extractorEvaluations`, the
extractor entered after the transcript's replay, on a list of evaluations. Where `Cost/Efficient.lean`
runs the transcript's extractor within `leanVmKnowledgeExtractorBudget` at the permutation queries'
count, this program runs within the same budget at the evaluations' count, and within the same size
bound.

* **`evaluationsExtractor_output`**: on evaluations of at most `512` bytes, the output within
  `leanVmKnowledgeExtractorBudget` at the announced stack size and the evaluations' count, decoded, is
  `extractorEvaluations`'s;
* **`extractorEvaluations_shortEvaluations`**: on the short evaluations of answers and keys
  (`shortEvaluations`), `extractorEvaluations` is `Extraction.extract` on those answers and keys:
  the stack's root has leaves of `64` words (`afterRootLite_roots`), so the extractor looks up
  preimages of `64` and `512` bytes only;
* **`evaluationsExtractor_extract`**: the two together;
* **`evaluationsExtractor_output_of_le`**: the same output within any larger budget, such as the
  budget at the largest stack `afterRoot` admits (`stackLog_le_of_afterRoot`, `2^30` rows);
* **`extractorEvaluations_steps`**: an execution the extractor on evaluations returns takes at most
  `2^35` steps, the halting search's cap at the sizes it admits.
-/

namespace LeanVM.Cost

open LeanVM LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Compile
open LeanVM.Protocol.Verifier LeanVM.Extraction LeanVM.Extraction.Fast LeanVM.Cost.Extractor

public section

/-! ## The program -/

/-- The program holds its bodies: their indices are distinct (`Cost/EvaluationsSize.lean`). -/
theorem evaluationsProgram_includes_all : Includes compiledEvaluationsExtractor
    evaluationsProgramBodies := by
  have h := nodup_of_increasing evaluationsProgram_indices_increasing
  refine includes_ofList _ ?_
  rw [evaluationsProgramBodies_eq, List.map_cons]
  exact h

/-- **The program's size is within `leanVmKnowledgeExtractorSizeBound`** (exactly `13721`). -/
theorem evaluationsProgram_size_le : compiledEvaluationsExtractor.size ≤
    leanVmKnowledgeExtractorSizeBound :=
  evaluationsProgram_size_le_measured.trans (by decide)

/-- The program holds the compiled extractor's bodies on evaluations. -/
theorem evaluationsProgram_includes :
    Includes compiledEvaluationsExtractor extractorEvaluationsC.costDeps :=
  evaluationsProgram_includes_all.mono fun _ hp ↦ by
    rw [evaluationsProgramBodies_eq]; exact List.mem_cons_of_mem _ hp

/-- Its function `0` is the entry calling the compiled extractor on evaluations. -/
theorem evaluationsProgram_entry : compiledEvaluationsExtractor[0]? = some (entryBody
    extractorEvaluationsC.costIdx) :=
  evaluationsProgram_includes_all.get (by rw [evaluationsProgramBodies_eq]; exact List.mem_cons_self)

/-! ## Its output -/

/-- Where the proof announces no shape, the extractor on evaluations returns nothing. -/
theorem extractorEvaluations_eq_none {prog : LeanIsaProgram} {π : Proof}
    (h : afterRoot (bytecodeWords prog) π = none) (input : PublicInput)
    (Ev : List (Bytes × Digest)) : extractorEvaluations prog input Ev π = none := by
  rw [extractorEvaluations_eq_full, extractorEvaluationsFull, afterRootDirect_eq_afterRoot, h]
  rfl

/-- **The extractor on evaluations, run within a budget**: on evaluations of at most `512`
bytes, the output within any budget at least `leanVmKnowledgeExtractorBudget` at the stack size of
the layout `afterRoot` reads and the evaluations' count, decoded, is `extractorEvaluations`'s. -/
theorem evaluationsExtractor_output_of_le (prog : LeanIsaProgram) (input : PublicInput)
    (Ev : List (Bytes × Digest)) (hEv : ∀ e ∈ Ev, e.1.length ≤ 512) (proof : Proof)
    {budget : ℕ} (hbudget : ∀ layout R st, afterRoot (bytecodeWords prog) proof = some ((layout, R), st) →
      leanVmKnowledgeExtractorBudget layout.stackLog Ev.length ≤ budget) :
    (outputWithin compiledEvaluationsExtractor leanVmKnowledgeExtractorSizeBound budget
        (encodeEvaluationsExtractorInput prog input Ev proof)).bind (decodeExecution prog) =
      extractorEvaluations prog input Ev proof := by
  obtain ⟨c, hc, hentryRun⟩ := runsBody_entry evaluationsProgram_entry
    (extractorEvaluationsC.costSpec compiledEvaluationsExtractor evaluationsProgram_includes
      prog input Ev proof)
  cases ht : extractorEvaluations prog input Ev proof with
  | none =>
    rw [ht] at hentryRun
    cases ho : outputWithin compiledEvaluationsExtractor leanVmKnowledgeExtractorSizeBound budget
        (encodeEvaluationsExtractorInput prog input Ev proof) with
    | none => rfl
    | some v =>
      obtain ⟨c', hv⟩ := runsBody_of_outputWithin ho
      obtain ⟨rfl, -⟩ := RunsBody.unique hv hentryRun
      exact decodeExecution_unwrap prog none
  | some t =>
    rw [ht] at hentryRun
    cases ha : afterRoot (bytecodeWords prog) proof with
    | none =>
      have := extractorEvaluations_eq_none ha input Ev
      rw [ht] at this
      exact absurd this (by simp)
    | some r =>
      obtain ⟨⟨layout, R⟩, st⟩ := r
      have hb := Bounds.extractorEvaluationsC_within compiledEvaluationsExtractor
        evaluationsProgram_includes prog input Ev hEv proof layout R st ha
      rw [show encodeEvaluationsExtractorInput prog input Ev proof =
          .constructor 0 [encodeValue prog, encodeValue input, encodeValue Ev, encodeValue proof]
        from rfl, outputWithin_of_runs evaluationsProgram_size_le hentryRun
          (hc.trans (hb.trans (Bounds.announcedStackLog_of_afterRoot ha ▸ hbudget _ _ _ ha)))]
      exact decodeExecution_unwrap prog (some t)

/-- **The extractor on evaluations, run within its budget**: on evaluations of at most `512`
bytes, the output within `leanVmKnowledgeExtractorBudget` at the announced stack size and the
evaluations' count, decoded, is `extractorEvaluations`'s. -/
theorem evaluationsExtractor_output (prog : LeanIsaProgram) (input : PublicInput)
    (Ev : List (Bytes × Digest)) (hEv : ∀ e ∈ Ev, e.1.length ≤ 512) (proof : Proof) :
    (outputWithin compiledEvaluationsExtractor leanVmKnowledgeExtractorSizeBound
        (leanVmKnowledgeExtractorBudget (announcedStackLog prog proof) Ev.length)
        (encodeEvaluationsExtractorInput prog input Ev proof)).bind (decodeExecution prog) =
      extractorEvaluations prog input Ev proof :=
  evaluationsExtractor_output_of_le prog input Ev hEv proof fun _ _ _ ha ↦
    (Bounds.announcedStackLog_of_afterRoot ha).symm ▸ le_rfl

/-- **The stack `afterRoot` reads has at most `2^30` rows.** -/
theorem stackLog_le_of_afterRoot {bytecode : List K} {π : Proof} {layout : Verifier.Layout}
    {R : ℕ} {st : VerifierProgramState} (ha : afterRoot bytecode π = some ((layout, R), st)) :
    layout.stackLog ≤ 30 := by
  have hl : afterRootLite bytecode π = some ((layoutLite layout, R), st) := by
    rw [afterRootLite_eq, ha]; rfl
  exact (Bounds.afterRootLite_facts hl).2.2.1

/-! ## The evaluations `extract` reads -/

/-- The short evaluations are evaluations of at most `512` bytes. -/
theorem length_le_of_mem_shortEvaluations {answers : Bytes → Option Digest} {keys : List Bytes}
    {e : Bytes × Digest} (h : e ∈ shortEvaluations answers keys) : e.1.length ≤ 512 := by
  unfold shortEvaluations answerPairs at h
  obtain ⟨x, hx, he⟩ := List.mem_filterMap.1 h
  obtain ⟨d, -, rfl⟩ := Option.map_eq_some_iff.1 he
  exact of_decide_eq_true (List.mem_filter.1 hx).2

/-- An answer pair's first answer is its answer. -/
theorem lookupEvaluation_answerPairs (answers : Bytes → Option Digest) (keys : List Bytes)
    {x : Bytes} (hx : x ∈ keys) {d : Digest} (hd : answers x = some d) :
    lookupEvaluation (answerPairs answers keys) x = some d := by
  induction keys with
  | nil => simp at hx
  | cons k keys ih =>
    unfold lookupEvaluation answerPairs at ih ⊢
    rw [List.filterMap_cons]
    by_cases hk : k = x
    · subst hk
      simp only [hd, Option.map_some, List.find?_cons, decide_true]
    · have ih' := ih ((List.mem_cons.1 hx).resolve_left (Ne.symm hk))
      cases answers k with
      | none => exact ih'
      | some d' =>
        simp only [Option.map_some, List.find?_cons, hk, decide_false]
        exact ih'

/-- The evaluations' first answers at their keys are the evaluations. -/
theorem answerPairs_lookupEvaluation (answers : Bytes → Option Digest) (keys : List Bytes) :
    answerPairs (lookupEvaluation (answerPairs answers keys)) ((answerPairs answers keys).map (·.1)) =
      answerPairs answers keys := by
  have hmem : ∀ e ∈ answerPairs answers keys,
      lookupEvaluation (answerPairs answers keys) e.1 = some e.2 := fun e he ↦ by
    unfold answerPairs at he
    obtain ⟨x, hx, hxe⟩ := List.mem_filterMap.1 he
    obtain ⟨d, hd, rfl⟩ := Option.map_eq_some_iff.1 hxe
    exact lookupEvaluation_answerPairs answers keys hx hd
  generalize answerPairs answers keys = E at hmem ⊢
  suffices h : ∀ F : List (Bytes × Digest), (∀ e ∈ F, lookupEvaluation E e.1 = some e.2) →
      answerPairs (lookupEvaluation E) (F.map (·.1)) = F from h E hmem
  intro F hF
  induction F with
  | nil => rfl
  | cons e F ih =>
    simp only [List.map_cons, answerPairs, List.filterMap_cons] at ih ⊢
    rw [hF e (List.mem_cons_self ..)]
    simp only [Option.map_some, List.cons.injEq, true_and]
    exact ih fun e' he' ↦ hF e' (List.mem_cons_of_mem _ he')

/-- **The index of the short evaluations looks up the preimages `extract` looks up**, of at most
`512` bytes. -/
theorem preimageIn_shortEvaluations (answers : Bytes → Option Digest) (keys : List Bytes)
    (d : Digest) (len : ℕ) (hlen : len ≤ 512) :
    preimageIn (evaluationsIndex (shortEvaluations answers keys)) d len =
      preimage (answerPairs answers keys) d len := by
  rw [evaluationsIndex, preimageIn_preimageIndex, answerPairs_firstAnswers, shortEvaluations,
    answerPairs_lookupEvaluation]
  have hf : answerPairs answers (keys.filter fun x ↦ decide (x.length ≤ 512)) =
      (answerPairs answers keys).filter fun e ↦ decide (e.1.length ≤ 512) := by
    unfold answerPairs
    rw [List.filter_filterMap, List.filterMap_filter]
    refine List.filterMap_congr fun x _ ↦ ?_
    cases answers x with
    | none => simp
    | some v => by_cases h : x.length ≤ 512 <;> simp [h, Option.filter]
  rw [hf, preimage_filter]
  intro p _ hp
  simp [hp, hlen]

/-- **On the short evaluations, the extractor on evaluations is `extract`**: the stack's root has
leaves of `64` words, so the extractor looks up preimages of `64` and `512` bytes only, which the
short evaluations' index looks up as `extract` does. -/
theorem extractorEvaluations_shortEvaluations (prog : LeanIsaProgram) (input : PublicInput)
    (answers : Bytes → Option Digest) (keys : List Bytes) (π : Proof) :
    extractorEvaluations prog input (shortEvaluations answers keys) π =
      Extraction.extract prog input (bytecodeWords prog) answers keys π := by
  rw [extractorEvaluations_eq_full, extractorEvaluationsFull_eq_extractWith, ← extractFast_eq,
    ← extractWith_preimage]
  unfold extractWith
  simp only [Option.bind_eq_bind]
  refine Option.bind_congr fun r h ↦ ?_
  obtain ⟨⟨layout, R⟩, st⟩ := r
  have hl : afterRootLite (bytecodeWords prog) π = some ((layoutLite layout, R), st) := by
    rw [afterRootLite_eq, h]; rfl
  obtain ⟨root, hroots⟩ := Bounds.afterRootLite_roots hl
  refine Option.bind_congr fun x hx ↦ ?_
  rw [show ((layout, R), st).2.roots = st.roots from rfl, hroots, List.head?_cons,
    Option.some.injEq] at hx
  subst hx
  rw [subtreeLeavesWith_congr (w := 64) (pre' := preimage (answerPairs answers keys))
    (fun d ↦ preimageIn_shortEvaluations answers keys d 64 (by omega))
    (fun d ↦ preimageIn_shortEvaluations answers keys d (8 * 64) (by omega))]

/-- **The extractor on evaluations computes `extract`**: on the short evaluations of answers and
keys, the program's output within `leanVmKnowledgeExtractorBudget` at the announced stack size and
the short evaluations' count, decoded, is `Extraction.extract` on those answers and keys. -/
theorem evaluationsExtractor_extract (prog : LeanIsaProgram) (input : PublicInput)
    (answers : Bytes → Option Digest) (keys : List Bytes) (proof : Proof) :
    (outputWithin compiledEvaluationsExtractor leanVmKnowledgeExtractorSizeBound
        (leanVmKnowledgeExtractorBudget (announcedStackLog prog proof)
          (shortEvaluations answers keys).length)
        (encodeEvaluationsExtractorInput prog input (shortEvaluations answers keys) proof)).bind
          (decodeExecution prog) =
      Extraction.extract prog input (bytecodeWords prog) answers keys proof := by
  rw [evaluationsExtractor_output prog input _ (fun _ he ↦ length_le_of_mem_shortEvaluations he),
    extractorEvaluations_shortEvaluations]

/-! ## The executions it returns -/

/-- The halting search stops within its fuel. -/
theorem haltLoopVec_le (memT codeT : Array (ℕ × ℕ)) (prog : LeanIsaProgram) {κ : ℕ}
    (mem : Vector E (2 ^ κ)) (fin : Registers K) :
    ∀ fuel n r m, haltLoopVec memT codeT prog mem fin fuel n r = some m → m ≤ n + fuel
  | 0, n, r, m, h => by
    simp only [haltLoopVec] at h
    split_ifs at h
    cases h; omega
  | fuel + 1, n, r, m, h => by
    simp only [haltLoopVec] at h
    split_ifs at h
    · cases h; omega
    · split at h
      · cases h
      · have := haltLoopVec_le memT codeT prog mem fin fuel (n + 1) _ m h
        omega

/-- A stack's execution from the runner's tables takes at most the layout's step cap. -/
theorem runWithTables_runnerTables_steps {prog : LeanIsaProgram} {input : PublicInput}
    {layout : LayoutLite} {q : Vector K (2 ^ layout.stackLog)} {t : Execution prog}
    (h : runWithTables (runnerTables prog layout) prog input layout q = some t) :
    t.stepCount ≤ stepCapLite layout := by
  unfold runWithTables runnerTables at h
  split_ifs at h
  unfold candidateExecutionVec at h
  split_ifs at h
  obtain ⟨n, hn, rfl⟩ := Option.map_eq_some_iff.1 h
  have := haltLoopVec_le _ _ _ _ _ _ _ _ _ hn
  simpa using this

/-- An execution `runFromLeaves` returns takes at most the layout's step cap. -/
theorem runFromLeaves_steps {prog : LeanIsaProgram} {input : PublicInput} {layout : LayoutLite}
    {R : ℕ} {leaves : Array (List K)} {h w : ℕ} {t : Execution prog}
    (ht : runFromLeaves prog input layout R leaves h w = some t) :
    t.stepCount ≤ stepCapLite layout := by
  unfold runFromLeaves runBoth at ht
  simp only at ht
  rcases (Option.orElse_eq_some _ _ _).1 ht with ht | ⟨-, ht⟩ <;>
  · obtain ⟨q, -, hq⟩ := List.exists_of_findSome?_eq_some ht
    exact runWithTables_runnerTables_steps hq

/-- **The extractor on evaluations returns executions of at most `2^35` steps**: the halting
search runs within the layout's step cap, at most `2^35` at the sizes `afterRootLite` admits. -/
theorem extractorEvaluations_steps {prog : LeanIsaProgram} {input : PublicInput}
    {P : List (Bytes × Digest)} {π : Proof} {t : Execution prog}
    (h : extractorEvaluations prog input P π = some t) : t.stepCount ≤ 2 ^ 35 := by
  unfold extractorEvaluations afterRootStageE stageE at h
  obtain ⟨⟨⟨layout, R⟩, st⟩, hr, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨root, -, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨hf, -⟩ := Bounds.afterRootLite_facts hr
  exact (runFromLeaves_steps h).trans
    (Bounds.stepCapLite_le layout hf.logMemory_le hf.logBytecode_le hf.heights_le
      hf.heights_length)

end

end LeanVM.Cost
