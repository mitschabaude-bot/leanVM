/-
  LeanVM.SecondDigest.Phase

  The public-input phase for two digests as a specification: the extension of a column at
  `(r, 1, 0, …, 0)`, the bound of one challenge per candidate whose first four memory words differ
  from the public words, and the phase's specification on the candidates that hold the second
  digest.
-/

module

public import LeanVM.SecondDigest.Claims
public import LeanVM.Protocol.EndToEnd.Front.LayoutBridgeB
public import LeanVM.Protocol.EndToEnd.Complete.Public
public import LeanVM.Protocol.ToCompPoly.Multilinear
public import LeanVM.Protocol.ToVCVio.UniformSample
public import Mathlib.Algebra.CharP.Two
public import Mathlib.Tactic.LinearCombination

/-!
# The phase for two digests as a specification

Fix a program `prog`, sizes `s` and the verifier's layout at them; `C` is a family of candidates
on the layout's stack, `toI` reads a candidate as a stack of the leanISA instance, and
`WireHolds` reads the program's claims on it (leanVM's `LayoutBridgeB`).

* `eval₂Mle_secondLinePoint`: the extension of a column at `(r, 1, 0, …, 0)` is
  `(1 - r)·q(2) + r·q(3)`, for at least two variables.
* `sixClaims_unique`: **a candidate whose first four memory words differ from the public words
  satisfies the phase's six claims at one challenge at most**. If its public lines fail
  (`PublicLinesHold`, cells `0` and `1`) or it does not hold the second digest
  (`StackHoldsSecondDigest`, cells `2` and `3`), one of the six lines through two cells differs from
  the line through the public values, and two different lines agree at one challenge at most
  (`line_challenge_unique`).
* `secondLayout_verifierLayout`: the program's claim on memory column `j` at `(r, 1, 0, …, 0)` is
  the instance's claim on `MEM_j` at that point, as leanVM's `pubLayoutHyp_verifierLayout` is at
  `(r, 0, …, 0)`; `sixClaimsHold_of_claims`: the program's six claims read on a candidate are the
  instance's.
* `pubPhaseSpec₂`: **the phase's specification** from `PubPre₂`, leanVM's `PubPre` on the
  candidates that hold the second digest (`HoldingSecond`), to leanVM's `PubPost` with the six
  claims on all candidates of `C`, with lead `L₀/|E|` plus the follower's. A candidate that holds
  the second digest and satisfies the earlier claims and the Keccak predicate fails its public
  lines by the precondition; one that does not hold it fails cells `2` and `3`; either way its six
  claims hold at one challenge at most (`pub_escape₂`). The layout check gives the memory's two
  variables (`memoryHasFourWords_iff`).
-/

namespace Recursion.SecondDigest

open LeanVM LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Compile
open LeanVM.Protocol.Verifier LeanVM.Protocol.EndToEnd LeanVM.Protocol.EndToEnd.Front
open LeanVM.Protocol.LeanIsa CompPoly CMlPolynomialEval
open scoped ENNReal NNReal

@[expose] public section

/-! ## The line through cells 2 and 3 -/

/-- The point `(r, 1, 0, …, 0)` of `E^n`, for `n ≥ 2`. -/
def secondLinePoint {n : ℕ} (hn : 2 ≤ n) (r : E) : Vector E n :=
  Vector.cast (by omega : 2 + (n - 2) = n) (#v[r, 1] ++ Vector.replicate (n - 2) (0 : E))

/-- **The extension of a column on the line through its cells 2 and 3**:
`q̃(r, 1, 0, …, 0) = (1 - r)·q(2) + r·q(3)`. The coordinates after the first select the slice at
index one, cells `2` and `3`, and the first coordinate interpolates between them. -/
theorem eval₂Mle_secondLinePoint {n : ℕ} (hn : 2 ≤ n) (q : CMlPolynomialEval K n) (r : E) :
    eval₂Mle q (algebraMap K E) (secondLinePoint hn r) =
      (1 - r) * ofK (q.get ⟨2, by have := Nat.pow_le_pow_right (by norm_num : 0 < 2) hn; omega⟩) +
        r * ofK (q.get ⟨3, by have := Nat.pow_le_pow_right (by norm_num : 0 < 2) hn; omega⟩) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  have h : 1 + (m + 1) = m + 2 := by omega
  have h1 : 1 < 2 ^ (m + 1) := Nat.one_lt_two_pow (by omega)
  have hpt : secondLinePoint hn r =
      Vector.cast h (#v[r] ++ (boolVec (⟨1, h1⟩ : Fin (2 ^ (m + 1))) : Vector E (m + 1))) := by
    apply Vector.ext
    intro i hi
    simp only [secondLinePoint, Vector.getElem_cast, Vector.getElem_append, boolVec,
      Vector.getElem_ofFn]
    rcases i with _ | _ | i
    · simp
    · simp
    · simp only [Vector.getElem_replicate]
      simp [Nat.testBit_eq_false_of_lt (Nat.one_lt_two_pow (n := i + 1) (by omega))]
  have hq : eval₂Mle q (algebraMap K E) (secondLinePoint hn r) =
      eval₂Mle (Vector.cast (congrArg (2 ^ ·) h) (Vector.cast (congrArg (2 ^ ·) h.symm) q))
        (algebraMap K E) (Vector.cast h (#v[r] ++ (boolVec (⟨1, h1⟩ : Fin (2 ^ (m + 1))) :
          Vector E (m + 1)))) := by
    rw [hpt, Vector.cast_cast, Vector.cast_rfl]
  rw [hq, eval₂Mle_cast (algebraMap K E) h, eval₂Mle, evalMle_append_boolVec,
    evalMle_succ, evalMle_zero, evalMleLayer_get]
  simp only [Vector.head, Nat.reduceAdd, Vector.getElem_mk, List.getElem_toArray,
    List.getElem_cons_zero, Nat.reducePow, slice, CMlPolynomialEval.map,
    Extension.Ext.algebraMap_eq_ofBase, cubeIndex, pow_one, Fin.getElem_fin,
    Vector.getElem_map, Vector.getElem_cast, Vector.get_eq_getElem, Vector.getElem_ofFn]

/-! ## One challenge per candidate -/

/-- **Two lines through cells in `K` that differ agree at one challenge at most**: the difference
is a polynomial of degree one in `r` with a nonzero coefficient. -/
theorem line_challenge_unique {a b c0 c1 : K} (hne : ¬ (a = c0 ∧ b = c1)) {r₁ r₂ : E}
    (h₁ : (1 - r₁) * ofK a + r₁ * ofK b = (1 + r₁) * ofK c0 + r₁ * ofK c1)
    (h₂ : (1 - r₂) * ofK a + r₂ * ofK b = (1 + r₂) * ofK c0 + r₂ * ofK c1) : r₁ = r₂ := by
  have e₁ : (ofK a - ofK c0) + r₁ * (ofK b - ofK a - ofK c0 - ofK c1) = 0 := by
    linear_combination h₁
  have e₂ : (ofK a - ofK c0) + r₂ * (ofK b - ofK a - ofK c0 - ofK c1) = 0 := by
    linear_combination h₂
  by_cases hβ : ofK b - ofK a - ofK c0 - ofK c1 = 0
  · exfalso
    apply hne
    have hα : ofK a = ofK c0 := by
      rw [hβ, mul_zero, add_zero, sub_eq_zero] at e₁
      exact e₁
    refine ⟨ofK_injective hα, ofK_injective ?_⟩
    have hb : ofK b = ofK c0 + ofK c0 + ofK c1 := by linear_combination hβ + hα
    rw [hb, CharTwo.add_self_eq_zero, zero_add]
  · have h : (r₁ - r₂) * (ofK b - ofK a - ofK c0 - ofK c1) = 0 := by
      linear_combination e₁ - e₂
    exact sub_eq_zero.mp ((mul_eq_zero.mp h).resolve_right hβ)

section Candidate

variable (prog : LeanIsaProgram) (s : Sizes)

/-- **The six claims of the phase hold of a stack at `r`**: on each memory limb column `j`, the
claim at `(r, 0, …, 0)` whose value is the line through limb `j` of the first digest's halves, and
the claim at `(r, 1, 0, …, 0)` whose value is the line through limb `j` of the second's. -/
def SixClaimsHold (hm : 2 ≤ s.logMem) (input second : PublicInput)
    (q : Column (leanIsaInstance prog s).μ) (r : E) : Prop :=
  ∀ j : Fin 3,
    (⟨memCol j.castSucc, PublicInput.linePoint s.logMem_pos r,
        pubLimb (publicInputDigest input) r j⟩ :
      Protocol.ColumnClaim (leanIsaInstance prog s)).Holds q ∧
    (⟨memCol j.castSucc, secondLinePoint hm r, pubLimb (publicInputDigest second) r j⟩ :
      Protocol.ColumnClaim (leanIsaInstance prog s)).Holds q

/-- **A candidate whose first four memory words differ from the public words satisfies the six
claims at one challenge at most**: some cell of memory words `0` to `3` differs from the public
value, so one of the six lines through two cells differs from the line through the public values,
and two lines that differ agree at one challenge at most. -/
theorem sixClaims_unique (hm : 2 ≤ s.logMem) {input second : PublicInput}
    {q : Column (leanIsaInstance prog s).μ}
    (hne : ¬ ((leanIsaInstance prog s).PublicLinesHold input q ∧
      StackHoldsSecondDigest prog s second q))
    {r₁ r₂ : E} (h₁ : SixClaimsHold prog s hm input second q r₁)
    (h₂ : SixClaimsHold prog s hm input second q r₂) : r₁ = r₂ := by
  have h4 : 3 < 2 ^ s.logMem := by
    have := Nat.pow_le_pow_right (by norm_num : 0 < 2) hm
    omega
  by_cases hp : (leanIsaInstance prog s).PublicLinesHold input q
  · have hs : ¬ StackHoldsSecondDigest prog s second q := fun hs ↦ hne ⟨hp, hs⟩
    simp only [StackHoldsSecondDigest, secondLines, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq, not_and] at hs
    have key : ∀ j : Fin 3, ∀ a b : K,
        ¬ (((leanIsaInstance prog s).column q (memCol j.castSucc)).values[2]? = some a ∧
          ((leanIsaInstance prog s).column q (memCol j.castSucc)).values[3]? = some b) →
        (∀ r, pubLimb (publicInputDigest second) r j = (1 + r) * ofK a + r * ofK b) →
        r₁ = r₂ := by
      intro j a b hab e
      have c₁ := (h₁ j).2
      have c₂ := (h₂ j).2
      unfold Protocol.ColumnClaim.Holds at c₁ c₂
      simp only at c₁ c₂
      replace c₁ := (eval₂Mle_secondLinePoint (n := s.logMem) hm _ r₁).symm.trans (c₁.trans (e r₁))
      replace c₂ := (eval₂Mle_secondLinePoint (n := s.logMem) hm _ r₂).symm.trans (c₂.trans (e r₂))
      refine line_challenge_unique ?_ c₁ c₂
      rintro ⟨ha, hb⟩
      apply hab
      have h4' : 3 < 2 ^ (leanIsaInstance prog s).κ (memCol j.castSucc) := h4
      exact ⟨by rw [Vector.getElem?_eq_getElem (by omega)]; exact congrArg some ha,
        by rw [Vector.getElem?_eq_getElem (by omega)]; exact congrArg some hb⟩
    have limb : ∀ (j : Fin 3) (r : E), pubLimb (publicInputDigest second) r j =
        (1 + r) * ofK (second.word0.limb j) + r * ofK (second.word1.limb j) := by
      intro j r
      rw [pubLimb_eq, EndToEnd.Complete.digestScalars_publicDigest]
    by_contra hne₂
    by_cases e0 : ((leanIsaInstance prog s).column q (memCol (Fin.castSucc 0))).values[2]? =
          some (second.lanes 0) ∧
        ((leanIsaInstance prog s).column q (memCol (Fin.castSucc 0))).values[3]? =
          some (second.lanes 2)
    · by_cases e1 : ((leanIsaInstance prog s).column q (memCol (Fin.castSucc 1))).values[2]? =
            some (second.lanes 1) ∧
          ((leanIsaInstance prog s).column q (memCol (Fin.castSucc 1))).values[3]? =
            some (second.lanes 3)
      · exact hne₂ (key 2 0 0 (fun h ↦ hs e0 e1 h.1 h.2) fun r ↦ by
          simp [limb, PublicInput.word0, PublicInput.word1])
      · exact hne₂ (key 1 _ _ e1 fun r ↦ by simp [limb, PublicInput.word0, PublicInput.word1])
    · exact hne₂ (key 0 _ _ e0 fun r ↦ by simp [limb, PublicInput.word0, PublicInput.word1])
  · simp only [M3Instance.PublicLinesHold, not_forall] at hp
    obtain ⟨l, hl, hne'⟩ := hp
    obtain ⟨j, rfl⟩ : ∃ j : Fin 3, (LeanIsa.publicLines prog s input)[j] = l := by
      obtain ⟨j, hj, hjl⟩ := List.mem_iff_getElem.mp hl
      exact ⟨⟨j, by simpa using hj⟩, by simpa using hjl⟩
    have c₁ := (h₁ j).1
    have c₂ := (h₂ j).1
    unfold Protocol.ColumnClaim.Holds at c₁ c₂
    simp only at c₁ c₂
    replace c₁ := (PublicInput.eval₂Mle_linePoint (n := s.logMem) s.logMem_pos _ r₁).symm.trans c₁
    replace c₂ := (PublicInput.eval₂Mle_linePoint (n := s.logMem) s.logMem_pos _ r₂).symm.trans c₂
    have hv := fun r ↦ lineValue_eq_pubLimb prog s (fl := some (LeanIsa.keccakRegion prog s))
      (EndToEnd.Complete.digestScalars_publicDigest input) r j
    rw [← hv r₁, PublicInput.lineValue] at c₁
    rw [← hv r₂, PublicInput.lineValue] at c₂
    fin_cases j <;> exact line_challenge_unique hne' c₁ c₂

end Candidate

/-! ## The layout's reading of the second claims -/

section Layout

variable (prog : LeanIsaProgram) (s : Sizes)

/-- The memory columns of the verifier's layout have the memory's variables. -/
theorem variableCount_memory0 :
    ((verifierLayout prog s).placement memory0).variableCount = s.logMem := by
  have h := placement_committed prog s (memCol 0) (not_isVirtual_memCol 0)
  rw [refCol_memCol] at h
  simp only [Fin.val_zero] at h
  rw [show memory0 = 0 from rfl, h]
  rfl

/-- The layout condition at the verifier's layout is that the memory has at least two variables. -/
theorem memoryHasFourWords_iff : MemoryHasFourWords (verifierLayout prog s) ↔ 2 ≤ s.logMem := by
  rw [MemoryHasFourWords, variableCount_memory0]

/-- The second point of the program is the instance's point `(r, 1, 0, …, 0)`. -/
theorem secondPoint_eq (hm : 2 ≤ s.logMem) (r : E) :
    secondPoint (verifierLayout prog s) r = (secondLinePoint hm r).toList := by
  rw [secondPoint, variableCount_memory0]
  apply List.ext_getElem (by simp; omega)
  intro i h1 h2
  simp only [secondLinePoint, Vector.toList_cast, Vector.toList_append]
  rcases i with _ | _ | i <;> simp

/-- **The memory claims at the second point**: the program's claim on memory column `j < 3` at
`(r, 1, 0, …, 0)` holding of a candidate is the instance's claim on `MEM_j` at `secondLinePoint r`
holding of its reading. -/
theorem secondLayout_verifierLayout (hm : 2 ≤ s.logMem) (j : Fin 3) (r v : E)
    (q : Column (verifierLayout prog s).stackLog)
    (h : WireHolds prog s ⟨j.val, secondPoint (verifierLayout prog s) r, v⟩ q) :
    (⟨memCol j.castSucc, secondLinePoint hm r, v⟩ :
      Protocol.ColumnClaim (leanIsaInstance prog s)).Holds (toI prog s q) := by
  have hcol : (j.val : ℕ) = refCol (memCol j.castSucc) := by
    rw [refCol_memCol]; rfl
  rw [hcol, secondPoint_eq prog s hm] at h
  exact (wireHolds_iff prog s (memCol j.castSucc) (secondLinePoint hm r) v q).mp h

/-- **The six claims of the program, read on a candidate, are the instance's six claims.** -/
theorem sixClaimsHold_of_claims (hm : 2 ≤ s.logMem) (input second : PublicInput) (r : E)
    (q : Column (verifierLayout prog s).stackLog)
    (h : ClaimsHoldBy (WireHolds prog s)
      (pubClaims (verifierLayout prog s) (publicInputDigest input) r ++
        secondClaims (verifierLayout prog s) (publicInputDigest second) r) q) :
    SixClaimsHold prog s hm input second (toI prog s q) r := by
  intro j
  refine ⟨pubLayoutHyp_verifierLayout prog s j r _ q (h _ (List.mem_append_left _ ?_)),
    secondLayout_verifierLayout prog s hm j r _ q (h _ (List.mem_append_right _ ?_))⟩
  · fin_cases j <;> simp [pubClaims, memory0, memory1, memory2]
  · fin_cases j <;> simp [secondClaims, memory0, memory1, memory2]

end Layout

/-! ## The specification -/

section Spec

variable (prog : LeanIsaProgram) (s : Sizes)
  (C : List Ev → Set (Column (verifierLayout prog s).stackLog))
  (claims : List Verifier.ColumnClaim) (input second : PublicInput)
  (pt : Vector E (leanIsaInstance prog s).τmax)

/-- **The candidates that hold the second digest**: those of `C` whose reading holds it. -/
def HoldingSecond (h : List Ev) : Set (Column (verifierLayout prog s).stackLog) :=
  {q | q ∈ C h ∧ StackHoldsSecondDigest prog s second (toI prog s q)}

/-- **The phase's precondition**: leanVM's `PubPre` on the candidates that hold the second digest:
none of them satisfies the earlier claims, the public lines and the Keccak predicate at `pt`. -/
abbrev PubPre₂ : List Ev → Prop :=
  PubPre prog s (verifierLayout prog s) (HoldingSecond prog s C second) (toI prog s)
    (WireHolds prog s) claims input pt

/-- The phase's claims at the challenge `r`: leanVM's, then the second claims. -/
abbrev pubClaims₂ (r : E) : List Verifier.ColumnClaim :=
  pubClaims (verifierLayout prog s) (publicInputDigest input) r ++
    secondClaims (verifierLayout prog s) (publicInputDigest second) r

/-- **The challenge's escape.** Under `PubPre₂`, the average over the challenge of "some candidate
satisfies the earlier claims, the six claims and the Keccak predicate" is at most `L₀ / |E|`:
per candidate that satisfies the earlier claims and the Keccak predicate, its first four memory
words differ from the public words (it does not hold the second digest, or by `PubPre₂` its public
lines fail), so the six claims hold at one challenge at most (`sixClaims_unique`); and the union
bound. -/
theorem pub_escape₂ (hm : 2 ≤ s.logMem) {L₀ : ℕ} (hcard : ∀ h, (C h).ncard ≤ L₀) {h₀ : List Ev}
    (hpre : PubPre₂ prog s C claims input second pt h₀) :
    avgE (fun r ↦ indE (∃ q ∈ C h₀,
      ClaimsHoldBy (WireHolds prog s) (claims ++ pubClaims₂ prog s input second r) q ∧
        (leanIsaInstance prog s).auxAt pt.toList (toI prog s q))) ≤
      L₀ * ((overE 1 : ℝ≥0) : ℝ≥0∞) := by
  have := finite_column (verifierLayout prog s).stackLog
  have hfin : (C h₀).Finite := Set.toFinite _
  let P : Column (verifierLayout prog s).stackLog → E → Prop := fun q r ↦
    (ClaimsHoldBy (WireHolds prog s) claims q ∧
      (leanIsaInstance prog s).auxAt pt.toList (toI prog s q)) ∧
    ClaimsHoldBy (WireHolds prog s) (pubClaims₂ prog s input second r) q
  refine (avgE_mono fun r ↦ indE_mono ?_).trans
    (avgE_indE_exists_le hfin (hcard h₀) (P := P) fun q hq ↦ ?_)
  · rintro ⟨q, hq, hcl, haux⟩
    exact ⟨q, hq, ⟨fun c hc ↦ hcl c (List.mem_append_left _ hc), haux⟩,
      fun c hc ↦ hcl c (List.mem_append_right _ hc)⟩
  · by_cases hc : ClaimsHoldBy (WireHolds prog s) claims q ∧
        (leanIsaInstance prog s).auxAt pt.toList (toI prog s q)
    · have hne : ¬ ((leanIsaInstance prog s).PublicLinesHold input (toI prog s q) ∧
          StackHoldsSecondDigest prog s second (toI prog s q)) := fun hl ↦
        hpre q ⟨hq, hl.2⟩ ⟨hc.1, hl.1, hc.2⟩
      refine (avgE_mono fun r ↦ indE_mono fun hP ↦ hP.2).trans ?_
      rw [avgE_indE_eq_prEvent, overE, Nat.cast_one]
      exact prEvent_uniformSample_le_of_subsingleton _ fun r₁ r₂ h₁ h₂ ↦
        sixClaims_unique prog s hm hne (sixClaimsHold_of_claims prog s hm input second r₁ q h₁)
          (sixClaimsHold_of_claims prog s hm input second r₂ q h₂)
    · refine (avgE_mono fun r ↦ indE_mono (q := False) fun hP ↦ absurd hP.1 hc).trans ?_
      refine (avgE_le_of_le fun r ↦ (indE_of_not not_false).le).trans ?_
      exact zero_le

open Classical in
/-- **The public-input phase for two digests as a specification.** From `PubPre₂`, doom on the
candidates that hold the second digest, to leanVM's `PubPost` with the six claims appended, on all
candidates, with lead `L₀ / |E|` plus the follower's `T`, for candidates stable along the phase and
at most `L₀` of them. The layout check gives the memory's two variables; then the challenge escapes
by `pub_escape₂`. -/
noncomputable def pubPhaseSpec₂ (hstable : CandsStable (verifierLayout prog s) C) {L₀ : ℕ}
    (hcard : ∀ h, (C h).ncard ≤ L₀) {εmax T : ℝ≥0∞} :
    Spec (publicInputPhase₂ (verifierLayout prog s) (publicInputDigest input)
        (publicInputDigest second))
      (PubPre₂ prog s C claims input second pt)
      (PubPost prog s (verifierLayout prog s) C (toI prog s) (WireHolds prog s) claims pt) εmax
      (L₀ * ((overE 1 : ℝ≥0) : ℝ≥0∞) + T) T :=
  Spec.congr (publicInputPhase₂_eq _ _ _).symm
    ((Spec.require (Post := fun _ h ↦ PubPre₂ prog s C claims input second pt h ∧ 2 ≤ s.logMem)
      fun _ hp hc ↦ ⟨hp, (memoryHasFourWords_iff prog s).mp hc⟩).bind' fun _ ↦
    (Spec.sampleE (L₀ * ((overE 1 : ℝ≥0) : ℝ≥0∞))
      (Post := fun r h ↦ PubPost prog s (verifierLayout prog s) C (toI prog s) (WireHolds prog s)
        claims pt (pubClaims₂ prog s input second r) h)
      fun h₀ hpre ↦ by
        refine le_trans ?_ (pub_escape₂ prog s C claims input second pt hpre.2 hcard hpre.1)
        unfold avgE
        gcongr
        refine card_filter_le_sum_indE fun r hr ↦ ?_
        by_contra hg
        refine hr fun q hq hq' ↦ hg ⟨q, ?_, hq'⟩
        rwa [hstable h₀ [Ev.sample r] rfl] at hq).bind' fun r ↦
      Spec.ret (Post := PubPost prog s (verifierLayout prog s) C (toI prog s) (WireHolds prog s)
        claims pt) (pubClaims₂ prog s input second r))

end Spec

end
end Recursion.SecondDigest
