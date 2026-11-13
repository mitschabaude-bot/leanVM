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
* **`evaluationsExtractor_extract`**: the two together.
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

/-- **The extractor on evaluations, run within its budget**: on evaluations of at most `512`
bytes, the output within `leanVmKnowledgeExtractorBudget` at the announced stack size and the
evaluations' count, decoded, is `extractorEvaluations`'s. -/
theorem evaluationsExtractor_output (prog : LeanIsaProgram) (input : PublicInput)
    (Ev : List (Bytes × Digest)) (hEv : ∀ e ∈ Ev, e.1.length ≤ 512) (proof : Proof) :
    (outputWithin compiledEvaluationsExtractor leanVmKnowledgeExtractorSizeBound
        (leanVmKnowledgeExtractorBudget (announcedStackLog prog proof) Ev.length)
        (encodeEvaluationsExtractorInput prog input Ev proof)).bind (decodeExecution prog) =
      extractorEvaluations prog input Ev proof := by
  obtain ⟨c, hc, hentryRun⟩ := runsBody_entry evaluationsProgram_entry
    (extractorEvaluationsC.costSpec compiledEvaluationsExtractor evaluationsProgram_includes
      prog input Ev proof)
  cases ht : extractorEvaluations prog input Ev proof with
  | none =>
    rw [ht] at hentryRun
    cases ho : outputWithin compiledEvaluationsExtractor leanVmKnowledgeExtractorSizeBound
        (leanVmKnowledgeExtractorBudget (announcedStackLog prog proof) Ev.length)
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
        from rfl, outputWithin_of_runs evaluationsProgram_size_le hentryRun (hc.trans hb)]
      exact decodeExecution_unwrap prog (some t)

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
    unfold lookupEvaluation at ih ⊢
    simp only [answerPairs, List.filterMap_cons] at ih ⊢
    by_cases hk : k = x
    · subst hk
      simp [hd]
    · rcases List.mem_cons.1 hx with rfl | hx
      · exact absurd rfl hk
      cases answers k with
      | none => exact ih hx
      | some d' => simp [hk, ih hx]

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
  generalize hE : answerPairs answers keys = E at hmem ⊢
  clear hE
  induction E with
  | nil => rfl
  | cons e E ih =>
    simp only [List.map_cons, answerPairs, List.filterMap_cons] at ih ⊢
    rw [hmem e (List.mem_cons_self ..)]
    simp only [Option.map_some, List.cons.injEq, true_and]
    exact ih fun e' he' ↦ hmem e' (List.mem_cons_of_mem _ he')

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
    cases answers x <;> simp
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
  simp only [hroots, List.head?_cons, Option.bind_some]
  rw [subtreeLeavesWith_congr (pre' := preimage (answerPairs answers keys))
    (fun d ↦ preimageIn_shortEvaluations answers keys d 64 (by norm_num))
    (fun d ↦ preimageIn_shortEvaluations answers keys d (8 * 64) (by norm_num))]

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

end

end LeanVM.Cost
