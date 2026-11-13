module

public import LeanVM.Cost.Bounds.Top
public import LeanVM.Cost.Extractor.Evaluations
import all Statement.LeanIsa
import all LeanVM.Protocol.Extraction.Extractor
import all LeanVM.Protocol.Extraction.Fast.Compiled
import all LeanVM.Protocol.Extraction.Fast.Evaluations
import all LeanVM.Protocol.Extraction.Fast.Lookup
import all LeanVM.Protocol.Extraction.Fast.SortedMap

/-!
# Bounds: the extractor on a list of evaluations

`extractorEvaluationsC` (`Cost/Extractor/Evaluations.lean`) is `extractorC` (`Bounds/Top.lean`)
with the transcript's index replaced by the index of a list of evaluations
(`evaluationsIndexC`). Its prices are `extractorC`'s, the evaluations' count in place of the
permutation queries': the index costs at most `transcriptIndexPrice` without the replay of the
transcript, and every other step is `extractorC`'s, priced by the same lemmas.

* `evaluationsIndex_cost`: per evaluation of at most `L` bytes, an amortized first-answer
  insertion, a lookup in the first answers and an amortized preimage-index insertion;
* `leavesOfEvaluationsC_cost`, `stageEC_cost`, `afterRootStageEC_cost`: as `leavesOfC_cost`,
  `stageTC_cost`, `afterRootStageC_cost`, within the same closed forms;
* **`extractorEvaluationsC_cost`**: at most `extractorPrice` at the shape `afterRootLite` announces,
  `N` the evaluations, `replayPrice` if the replay fails;
* **`extractorEvaluationsC_within`**: with the entry's `14`, within
  `leanVmKnowledgeExtractorBudget` at the announced stack size, the evaluations' count in place of
  the permutation queries', wherever `afterRoot` announces a shape.
-/

namespace LeanVM.Cost.Bounds

open LeanVM.Cost LeanVM.Cost.Extractor LeanVM.Cost.Library LeanVM.Parameters LeanVM.Semantics
open LeanVM.Extraction LeanVM.Extraction.Fast LeanVM.Protocol.Verifier LeanVM.Protocol.Compile

public section

attribute [local instance] lexOrd

variable (P : LeanVM.Cost.MachineProgram)

/-! ## The evaluations' index -/

/-- The evaluations' index is a good map of at most as many insertions as evaluations. -/
theorem evaluationsIndex_bounds (Ev : List (Bytes × LeanVM.Protocol.Digest)) :
    smGood (evaluationsIndex Ev) ∧ smWeightSum (evaluationsIndex Ev) ≤ Ev.length := by
  rw [evaluationsIndex, preimageIndex]
  have hgen : ∀ (l : List (Bytes × LeanVM.Protocol.Digest)) (m : SortedMap (List UInt64 × ℕ) Hits),
      smGood m →
      smGood (l.foldl (fun m p ↦ m.insert (hitKey p) ((m.getD (hitKey p) .none).merge (.one p.1))) m) ∧
      smWeightSum (l.foldl (fun m p ↦ m.insert (hitKey p) ((m.getD (hitKey p) .none).merge (.one p.1))) m)
        = smWeightSum m + l.length := by
    intro l
    induction l with
    | nil => intro m hm; exact ⟨hm, by simp⟩
    | cons x l ih =>
      intro m hm
      obtain ⟨h1, h2⟩ := smGood_insert hm (hitKey x) ((m.getD (hitKey x) .none).merge (.one x.1))
      obtain ⟨h3, h4⟩ := ih _ h1
      refine ⟨h3, ?_⟩
      rw [List.foldl_cons, h4, h2, List.length_cons]
      omega
  obtain ⟨h1, h2⟩ := hgen _ _ smGood_empty
  refine ⟨h1, ?_⟩
  rw [h2, smWeightSum_empty, Nat.zero_add, answerPairs]
  refine (List.length_filterMap_le _ _).trans ?_
  rw [List.length_map]

/-- The evaluations' index has the preimage index's keys. -/
theorem evaluationsIndex_keys (Ev : List (Bytes × LeanVM.Protocol.Digest))
    (hEv : ∀ e ∈ Ev, e.1.length < 2 ^ 64) : KeysIn PreKey (evaluationsIndex Ev).levels := by
  rw [evaluationsIndex, preimageIndex]
  have hgen : ∀ (l : List (List UInt8 × LeanVM.Protocol.Digest))
      (m : SortedMap (List UInt64 × ℕ) Hits), KeysIn PreKey m.levels →
      (∀ p ∈ l, p.1.length < 2 ^ 64) →
      KeysIn PreKey (l.foldl (fun m p ↦
        m.insert (hitKey p) ((m.getD (hitKey p) .none).merge (.one p.1))) m).levels := by
    intro l
    induction l with
    | nil => intro m hm _; exact hm
    | cons x l ih =>
      intro m hm hl
      rw [List.foldl_cons]
      exact ih _ (keysIn_insert hm (preKey_hitKey x (hl x (by simp))) _)
        (fun p hp ↦ hl p (by simp [hp]))
  refine hgen _ _ (fun _ h ↦ by simp [SortedMap.empty] at h) (fun p hp ↦ ?_)
  obtain ⟨e, he, h⟩ := List.mem_map.1 (mem_answerPairs_fst hp)
  rw [← h]
  exact hEv e he

/-- **The evaluations' index** (`evaluationsIndex Ev`, compiled as `evaluationsIndexC`), `N`
evaluations of at most `L` bytes, `N + 2 ≤ 2^D`: per evaluation an amortized first-answer
insertion (`firstAnswers_cost`), a lookup in the first answers (`D` binary searches of `D + 2`
probes of `40 + 26·L + 9·W`) and an amortized preimage-index insertion (`preimageIndex_cost`). -/
theorem evaluationsIndex_cost (hP : Includes P evaluationsIndexC.costDeps) (D L W : ℕ)
    (hW : ∀ x, x ≤ 2 * 2 ^ D → limbCount x ≤ W) (hL : L < 2 ^ 61)
    (Ev : List (Bytes × LeanVM.Protocol.Digest)) (hN : Ev.length + 2 ≤ 2 ^ D)
    (hmem : ∀ e ∈ Ev, e.1.length ≤ L) :
    machineCost P evaluationsIndexC.costIdx [encodeValue Ev] ≤
      (Ev.length + 1) * ((firstAnswersStepPrice L D W + 11) + (preimageStepPrice L D W + 11) +
        D * (20 + (40 + 26 * L + 9 * W) * (D + 2)) + 67) + 44 := by
  rw [evaluationsIndexC.costEq P hP]
  have hFA := firstAnswers_cost P (by includes) L D W hW Ev (by omega) hmem
  have hmap := map_cost P (by includes) _ (.closure transcriptIndexC.lam1.costIdx [])
    (fun a ↦ RunsApp.of_spec (transcriptIndexC.lam1.costSpec P (by includes) a)) 2 Ev
    (fun a _ ↦ by rw [appCost_fn, List.nil_append, transcriptIndexC.lam1.costEq P (by includes),
      List.length_nil])
  have hinv : BytesInv L D (firstAnswers Ev) 1 := bytesInv_firstAnswers P (by includes) L D W hW 1 Ev
    SortedMap.empty hmem
    ⟨smGood_empty, fun _ h ↦ by simp [SortedMap.empty] at h, by simp [smWeightSum_empty]; omega⟩
  obtain ⟨hg, -, hw⟩ := hinv
  obtain ⟨hlv, hsz⟩ := smGood_levels_le hg (by omega : smWeightSum (firstAnswers Ev) < 2 ^ D)
  set G := D * (20 + (40 + 26 * L + 9 * W) * (D + 2)) with hG
  have hget : ∀ x : List UInt8, x.length ≤ L →
      machineCost P getBytesC.costIdx [encodeValue (firstAnswers Ev), encodeValue x] ≤ G + 9 := by
    intro x hx
    have := getBytes_cost P (by includes) (firstAnswers Ev) (2 ^ D) W hW
      (fun l hl ↦ (hsz l hl).1.trans (hsz l hl).2) x
    rw [Nat.log2_two_pow] at this
    have h1 : (firstAnswers Ev).levels.length * (20 + (40 + 26 * x.length + 9 * W) * (D + 2)) ≤ G :=
      Nat.mul_le_mul hlv (Nat.add_le_add_left (Nat.mul_le_mul_right _ (by omega)) _)
    omega
  have hAP : machineCost P answerPairsC.costIdx
      [.closure evaluationsIndexC.lam0.costIdx [encodeValue (firstAnswers Ev)], encodeValue (Ev.map (·.1))] ≤
      (G + 52) * (Ev.length + 1) + 8 := by
    rw [answerPairsC.costEq P (by includes) (firstAnswers Ev).get? _
      (fun a ↦ RunsApp.of_spec (evaluationsIndexC.lam0.costSpec P (by includes) _ a))]
    have := filterMap_cost P (by includes) _
      (.closure answerPairsC.lam0.costIdx [.closure evaluationsIndexC.lam0.costIdx [encodeValue (firstAnswers Ev)]])
      (fun a ↦ RunsApp.of_spec (answerPairsC.lam0.costSpec P (by includes) (firstAnswers Ev).get? _
        (fun a ↦ RunsApp.of_spec (evaluationsIndexC.lam0.costSpec P (by includes) _ a)) a))
      (G + 36) (Ev.map (·.1)) (fun x hx ↦ by
        obtain ⟨e, he, rfl⟩ := List.mem_map.1 hx
        simp only [appCost_fn, List.cons_append, List.nil_append, List.length_cons, List.length_nil]
        rw [answerPairsC.lam0.costEq P (by includes) (firstAnswers Ev).get? _
          (fun a ↦ RunsApp.of_spec (evaluationsIndexC.lam0.costSpec P (by includes) _ a)),
          appCost_fn, List.cons_append, List.nil_append,
          evaluationsIndexC.lam0.costEq P (by includes)]
        simp only [List.length_cons, List.length_nil]
        have := hget e.1 (hmem e he)
        generalize (firstAnswers Ev).get? e.1 = o
        cases o with
        | none =>
          rw [Auto.Option.map.c194.costEq_none P (by includes) _
            (.closure answerPairsC.lam0.lam0.costIdx [encodeValue e.1])
            (fun a ↦ RunsApp.of_spec (answerPairsC.lam0.lam0.costSpec P (by includes) e.1 a))]
          omega
        | some d =>
          rw [Auto.Option.map.c194.costEq_some P (by includes) _
            (.closure answerPairsC.lam0.lam0.costIdx [encodeValue e.1])
            (fun a ↦ RunsApp.of_spec (answerPairsC.lam0.lam0.costSpec P (by includes) e.1 a)),
            appCost_fn, List.cons_append, List.nil_append, answerPairsC.lam0.lam0.costEq P (by includes)]
          simp only [List.length_cons, List.length_nil]
          omega)
    rw [List.length_map] at this
    have : (G + 36 + 16) * Ev.length ≤ (G + 52) * (Ev.length + 1) :=
      Nat.mul_le_mul_left _ (Nat.le_succ _)
    omega
  have hPI := preimageIndex_cost P (by includes) D L W hW (by omega)
    (answerPairs (firstAnswers Ev).get? (Ev.map (·.1)))
    (by have := answerPairs_length_le (firstAnswers Ev).get? (Ev.map (·.1))
        simp only [List.length_map] at this; omega)
    (fun p hp ↦ by
      obtain ⟨e, he, h⟩ := List.mem_map.1 (mem_answerPairs_fst hp)
      rw [← h]; exact hmem e he)
  have hPl : (answerPairs (firstAnswers Ev).get? (Ev.map (·.1))).length ≤ Ev.length + 1 := by
    have := answerPairs_length_le (firstAnswers Ev).get? (Ev.map (·.1))
    simp only [List.length_map] at this; omega
  have e1 : (Ev.length + 1) * ((firstAnswersStepPrice L D W + 11) + (preimageStepPrice L D W + 11) + G + 67) =
      (Ev.length + 1) * (firstAnswersStepPrice L D W + 11) + (Ev.length + 1) * (preimageStepPrice L D W + 11) +
        (Ev.length + 1) * G + 67 * (Ev.length + 1) := by
    ring
  have e2 : (G + 52) * (Ev.length + 1) = (Ev.length + 1) * G + 52 * (Ev.length + 1) := by ring
  have f1 : Ev.length * (firstAnswersStepPrice L D W + 11) ≤
      (Ev.length + 1) * (firstAnswersStepPrice L D W + 11) := Nat.mul_le_mul_right _ (Nat.le_succ _)
  have f2 : (answerPairs (firstAnswers Ev).get? (Ev.map (·.1))).length * (preimageStepPrice L D W + 11) ≤
      (Ev.length + 1) * (preimageStepPrice L D W + 11) := Nat.mul_le_mul_right _ hPl
  omega

/-- The evaluations' index costs at most the transcript's, at the evaluations' count. -/
theorem evaluationsIndexPrice_le (D L N W : ℕ) :
    (N + 1) * ((firstAnswersStepPrice L D W + 11) + (preimageStepPrice L D W + 11) +
        D * (20 + (40 + 26 * L + 9 * W) * (D + 2)) + 67) + 44 ≤ transcriptIndexPrice D L N W := by
  unfold transcriptIndexPrice
  omega

/-! ## The committed leaves and the stages -/

/-- **A preimage lookup** in the evaluations' index (`leavesOfC.lam0`, `preimageIn.c705`): a
binary search per level, at most `D·(20 + (162 + 9·W)·(D + 2)) + 42`. -/
theorem preimageLookupE_cost (hP : Includes P leavesOfC.lam0.costDeps)
    (Ev : List (Bytes × LeanVM.Protocol.Digest)) (hEv : ∀ e ∈ Ev, e.1.length < 2 ^ 64) (D W : ℕ)
    (hW : ∀ x, x ≤ 2 * 2 ^ D → limbCount x ≤ W) (hN : Ev.length + 2 ≤ 2 ^ D)
    (d : LeanVM.Protocol.Digest) (len : ℕ) (hlen : len < 2 ^ 64) :
    appCost P (.closure leavesOfC.lam0.costIdx [encodeValue (evaluationsIndex Ev)])
        [encodeValue d, encodeValue len] ≤
      D * (20 + (162 + 9 * W) * (D + 2)) + 42 := by
  simp only [appCost_fn, List.cons_append, List.nil_append, List.length_cons, List.length_nil]
  rw [leavesOfC.lam0.costEq P hP,
    Auto.LeanVM.Extraction.Fast.preimageIn.c705.costEq P (by includes)]
  obtain ⟨hg, hw⟩ := evaluationsIndex_bounds Ev
  obtain ⟨hlev, hsz⟩ := smGood_levels_le hg (D := D)
    (lt_of_le_of_lt hw (by omega))
  have hget := getPre_cost P (by includes) (evaluationsIndex Ev) (2 ^ D) W hW
    (fun l hl ↦ (hsz l hl).1.trans (hsz l hl).2) (evaluationsIndex_keys Ev hEv)
    (d.toList, len) ⟨by simp, hlen⟩
  rw [Nat.log2_two_pow] at hget
  have hlv : (evaluationsIndex Ev).levels.length * (20 + (162 + 9 * W) * (D + 2)) ≤
      D * (20 + (162 + 9 * W) * (D + 2)) := Nat.mul_le_mul_right _ hlev
  simp only [Vector.size_toArray]
  generalize (evaluationsIndex Ev).get? (d.toList, len) = o1
  generalize (evaluationsIndex Ev).getD (d.toList, len) Hits.none = o2
  cases o1 <;> cases o2 <;> dsimp only <;> omega

/-- **The committed leaves** from the evaluations (`leavesOfEvaluationsC`, width `64`), evaluations
of at most `512` bytes: the index, then the subtree. -/
theorem leavesOfEvaluationsC_cost (hP : Includes P leavesOfEvaluationsC.costDeps)
    (Ev : List (Bytes × LeanVM.Protocol.Digest)) (hEv : ∀ e ∈ Ev, e.1.length ≤ 512) (D W : ℕ)
    (hW : ∀ x, x ≤ 2 * 2 ^ D → limbCount x ≤ W)
    (hN : Ev.length + 2 ≤ 2 ^ D) (h : ℕ) (root : LeanVM.Protocol.Digest) :
    machineCost P leavesOfEvaluationsC.costIdx
        [encodeValue Ev, encodeValue 64, encodeValue h, encodeValue root] ≤
      19 + transcriptIndexPrice D 512 Ev.length W + committedLeavesPrice D h W := by
  rw [leavesOfEvaluationsC.costEq P hP]
  have hT := evaluationsIndex_cost P (by includes) D 512 W hW (by norm_num) Ev hN hEv
  have hT' := evaluationsIndexPrice_le D 512 Ev.length W
  have hS := subtreeLeavesWithC_cost P (by includes) _
    (.closure leavesOfC.lam0.costIdx [encodeValue (evaluationsIndex Ev)])
    (fun d n ↦ RunsApp.of_spec (leavesOfC.lam0.costSpec P (by includes) _ d n))
    (D * (20 + (162 + 9 * W) * (D + 2)) + 42)
    (fun d n hn ↦ preimageLookupE_cost P (by includes) Ev
      (fun e he ↦ by have := hEv e he; omega) D W hW hN d n hn)
    64 (by norm_num) h root
  have e : D * (20 + (162 + 9 * W) * (D + 2)) + 42 + 15 * 64 + 30725 +
      (D * (20 + (162 + 9 * W) * (D + 2)) + 42 + 453 * 64 + 35) + 5 * h =
      2 * (D * (20 + (162 + 9 * W) * (D + 2)) + 42) + 60712 + 5 * h := by ring
  rw [e] at hS
  unfold committedLeavesPrice
  omega

/-- **A stage** from the evaluations (`stageEC`) at the root `afterRootLite` returns. -/
theorem stageEC_cost (hP : Includes P stageEC.costDeps) (prog : Semantics.LeanIsaProgram)
    (input : PublicInput) (Ev : List (Bytes × LeanVM.Protocol.Digest))
    (hEv : ∀ e ∈ Ev, e.1.length ≤ 512)
    (D W : ℕ) (hW : ∀ x, x ≤ 2 * 2 ^ D → limbCount x ≤ W) (hN : Ev.length + 2 ≤ 2 ^ D)
    {bytecode : List K} {π : Proof}
    {L : LayoutLite} {R : ℕ} {st : VerifierProgramState} (har : afterRootLite bytecode π = some ((L,
        R), st))
    (root : LeanVM.Protocol.Digest) :
    machineCost P stageEC.costIdx [encodeValue prog, encodeValue input, encodeValue L, encodeValue R,
        encodeValue Ev, encodeValue (root, L.stackLog - 6 + R, 64)] ≤
      afterRootStagePrice L.stackLog R L.logMemory prog.logSize D Ev.length (L.stackLog - 6 + R) W := by
  obtain ⟨hf, hμ1, hμ2, hR1, hR2, -⟩ := afterRootLite_facts har
  have hadm := admissible_of_afterRootLite har
  rw [stageEC.costEq P hP]
  dsimp only
  have hL := leavesOfEvaluationsC_cost P (by includes_sub) Ev hEv D W hW hN (L.stackLog - 6 + R) root
  have hR := runFromLeavesC_cost P (by includes_sub) prog input L R hf hadm
    (leavesOfEvaluations Ev 64 (L.stackLog - 6 + R) root) (L.stackLog - 6 + R) (by omega)
    (fun l hl ↦ (subtreeLeavesWith_mem_length _ _ _ _ l hl).le)
  unfold afterRootStagePrice
  omega

/-- **After the replay** (`afterRootStageEC`): the root, then the stage. -/
theorem afterRootStageEC_cost (hP : Includes P afterRootStageEC.costDeps) (prog :
    Semantics.LeanIsaProgram)
    (input : PublicInput) (Ev : List (Bytes × LeanVM.Protocol.Digest))
    (hEv : ∀ e ∈ Ev, e.1.length ≤ 512)
    (D W : ℕ) (hW : ∀ x, x ≤ 2 * 2 ^ D → limbCount x ≤ W) (hN : Ev.length + 2 ≤ 2 ^ D)
    {bytecode : List K} {π : Proof}
    {L : LayoutLite} {R : ℕ} {st : VerifierProgramState} (har : afterRootLite bytecode π = some ((L,
        R), st)) :
    machineCost P afterRootStageEC.costIdx [encodeValue prog, encodeValue input, encodeValue Ev,
        encodeValue ((L, R), st)] ≤
      afterRootStagePrice L.stackLog R L.logMemory prog.logSize D Ev.length (L.stackLog - 6 + R) W + 43 := by
  obtain ⟨root, hroots⟩ := afterRootLite_roots har
  have hk : ∀ t : LeanVM.Protocol.Digest × ℕ × ℕ, RunsApp P
      (.closure afterRootStageEC.lam0.costIdx [encodeValue prog, encodeValue input, encodeValue Ev,
        encodeValue R, encodeValue L]) [encodeValue t]
      (encodeValue (stageE prog input L R Ev t)) := fun t ↦
    RunsApp.of_spec (us := [encodeValue prog, encodeValue input, encodeValue Ev, encodeValue R,
      encodeValue L]) (vs := [encodeValue t])
      (afterRootStageEC.lam0.costSpec P (by includes_sub) prog input Ev R L t)
  have hb := Auto.Option.bind.c154.costEq P (by includes_sub) st.roots.head? (stageE prog input L R Ev)
    _ hk
  have hlam := afterRootStageEC.lam0.costEq P (by includes_sub) prog input Ev R L
    (root, L.stackLog - 6 + R, 64)
  have hst := stageEC_cost P (by includes_sub) prog input Ev hEv D W hW hN har root
  rw [afterRootStageEC.costEq P hP]
  simp only [hroots, List.head?_cons] at hb ⊢
  simp only [appCost_fn, List.cons_append, List.nil_append, List.length_cons, List.length_nil] at hb
  omega

/-! ## The extractor -/

/-- **The price of the extractor on evaluations** (`extractorEvaluationsC`), on every input of
evaluations of at most `512` bytes: at most `extractorPrice` at the shape `afterRootLite`
announces, the evaluations' count in place of the permutation queries', or `replayPrice` when the
replay fails. -/
theorem extractorEvaluationsC_cost (hP : Includes P extractorEvaluationsC.costDeps)
    (prog : Semantics.LeanIsaProgram) (input : PublicInput)
    (Ev : List (Bytes × LeanVM.Protocol.Digest)) (hEv : ∀ e ∈ Ev, e.1.length ≤ 512) (π : Proof) :
    machineCost P extractorEvaluationsC.costIdx
        [encodeValue prog, encodeValue input, encodeValue Ev, encodeValue π] ≤
      match afterRootLite (bytecodeWords prog) π with
      | none => replayPrice prog.logSize
      | some ((L, R), _) => extractorPrice L.stackLog R L.logMemory prog.logSize Ev.length := by
  have hls : prog.logSize ≤ 30 := prog.logSize_le
  have hbc := bytecodeWords_length prog
  have hW := bytecodeWordsC_cost P (by includes_sub) prog
  have hA := afterRootLite_cost P (by includes_sub) (bytecodeWords prog) π (by
    rw [hbc]
    have : 2 ^ prog.logSize ≤ 2 ^ 30 := Nat.pow_le_pow_right (by norm_num) hls
    omega)
  rw [hbc] at hA
  have hk : ∀ r : (LayoutLite × ℕ) × VerifierProgramState, RunsApp P
      (.closure extractorEvaluationsC.lam0.costIdx [encodeValue prog, encodeValue input, encodeValue Ev])
      [encodeValue r] (encodeValue (afterRootStageE prog input Ev r)) := fun r ↦
    RunsApp.of_spec (us := [encodeValue prog, encodeValue input, encodeValue Ev]) (vs := [encodeValue r])
      (extractorEvaluationsC.lam0.costSpec P (by includes_sub) prog input Ev r)
  rw [extractorEvaluationsC.costEq P hP, Auto.Option.bind.c154.costEq P (by includes_sub)
    (afterRootLite (bytecodeWords prog) π) (afterRootStageE prog input Ev) _ hk]
  cases har : afterRootLite (bytecodeWords prog) π with
  | none =>
    show _ ≤ bytecodeWordsPrice prog.logSize + (128 * 2 ^ prog.logSize + 977128522) + 15
    dsimp only
    omega
  | some r =>
    obtain ⟨⟨L, R⟩, st⟩ := r
    show _ ≤ bytecodeWordsPrice prog.logSize + (128 * 2 ^ prog.logSize + 977128522) +
      afterRootStagePrice L.stackLog R L.logMemory prog.logSize (Nat.log2 (Ev.length + 2) + 1)
        Ev.length (L.stackLog - 6 + R) (limbsBelowTwoPow (Nat.log2 (Ev.length + 2) + 1 + 1)) + 69
    simp only [appCost_fn, List.cons_append, List.nil_append, List.length_cons, List.length_nil]
    have hl := extractorEvaluationsC.lam0.costEq P (by includes_sub) prog input Ev ((L, R), st)
    have hN : Ev.length + 2 ≤ 2 ^ (Nat.log2 (Ev.length + 2) + 1) := Nat.le_of_lt Nat.lt_log2_self
    have hs := afterRootStageEC_cost P (by includes_sub) prog input Ev hEv _ _
      limbs_le_wl_two hN har
    omega

/-- **The price within the budget**: wherever `afterRoot` announces a shape, the price of the
extractor on evaluations and the entry's `14` are within `leanVmKnowledgeExtractorBudget` at the
announced stack size, the evaluations' count in place of the permutation queries'. -/
theorem extractorEvaluationsC_within (hP : Includes P extractorEvaluationsC.costDeps)
    (prog : Semantics.LeanIsaProgram) (input : PublicInput)
    (Ev : List (Bytes × LeanVM.Protocol.Digest)) (hEv : ∀ e ∈ Ev, e.1.length ≤ 512) (π : Proof)
    (layout : Layout) (logInverseRate : ℕ) (st : VerifierProgramState)
    (ha : afterRoot (bytecodeWords prog) π = some ((layout, logInverseRate), st)) :
    machineCost P extractorEvaluationsC.costIdx
        [encodeValue prog, encodeValue input, encodeValue Ev, encodeValue π] + 14 ≤
      leanVmKnowledgeExtractorBudget (announcedStackLog prog π) Ev.length := by
  have h := extractorEvaluationsC_cost P hP prog input Ev hEv π
  have hl : afterRootLite (bytecodeWords prog) π = some ((layoutLite layout, logInverseRate), st) := by
    rw [afterRootLite_eq, ha]; rfl
  rw [hl] at h
  dsimp only at h
  obtain ⟨hf, -, hμ, -, hR, -⟩ := afterRootLite_facts hl
  have hb := extractorPrice_le_budget Ev.length hμ hR hf.logMemory_le prog.logSize_le
  rw [announcedStackLog_of_afterRoot ha]
  exact le_trans (Nat.add_le_add_right h _) hb

end

end LeanVM.Cost.Bounds
