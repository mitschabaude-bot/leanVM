/-
  LeanVM.SaltedGuest.B1.Terminal.LibK

  What the salted `check_opening_terminal` reads besides the deployed terminal's lemmas: a
  committed column's selector over the salted calls, the second claims' chain and its value, and
  the batched weight over the claims and the second claims.
-/

module

public import LeanVM.SaltedGuest.B1.Terminal.TemplateK
public import LeanVM.SaltedGuest.B1.VerifySub.AssembleLib

/-!
# The salted terminal's library

* `sel_valueK`: the deployed `sel_value` for a selector block whose calls are the salted core
  IR's (the selectors are unchanged functions, `colSel_same`).
* `chainFrom_value`: a chain written by `chain[k + 1] = chain[k]·p1[k]` from `chain[s]`;
  `chain2_eq`: from `chain[2] = (rm + p1[0])·point[1]`, its word `m` is the weight of the second
  claims' point `(rm, 1, 0, …, 0)` against `x`.
* `stackWeight_eqS`: the batched weight over the claims, the second claims and the outputs' claim
  is the deployed sum with the three second claims' weights at `λ^(1 + poolRank 167 + i)` and
  the outputs' claim at `λ^(4 + poolRank 167)`.
-/

namespace LeanVM.SaltedGuest.B1.Terminal

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Guest.B1 LeanVM.Guest.B1.VerifySub LeanVM.Protocol LeanVM.Protocol.Verifier Finset
open LeanVM.Protocol.Compile Recursion.SecondDigest

@[expose] public section

/-! ## The selectors -/

/-- **Committed column `c`'s selector**, over the salted core IR's calls. -/
theorem sel_valueK (hcs : Tables.column_selector_Spec) (hst : Tables.selector_tables_Spec)
    {μ : ℕ} (hμ : μ ≤ 32) (Lm : MemoryImage μ)
    {σ : Val} {c κ o L : ℕ} {x : List E} {kret : List E → Prop}
    (h : Stmt.HoldsList (SaltedGuest.coreProgram.Rel Lm.read) Lm.read σ (selBlockT c) True kret)
    (hstc : Guest.coreProgram.Rel Lm.read "selector_tables" [σ (.n 13), σ (.n 14)] [σ (.n 41)])
    (hgt : Tables.GTabsAt Lm.read (σ (.n 0) * gen ^ 34))
    (hkap : σ (.n (kbV (Tables.colKappaSrc c))) * gen ^ Tables.colKappaAdj c = gen ^ κ)
    (hoff : LoadHolds Lm.read (σ (.n 10)) c (gen ^ o)) (hdvd : 2 ^ κ ∣ o)
    (hκ : κ ≤ L) (hL : L ≤ 32) (ho : o < 2 ^ L) (hx : x.length = L)
    (hpt : ReadsAt Lm.read (σ (.n 13)) (padPoint x))
    (hpt1 : ReadsAt Lm.read (σ (.n 14)) ((padPoint x).map (1 + ·))) :
    σ (.n (selV c)) = selProd o κ (L - κ) x := by
  have hadj : Tables.colKappaAdj c < 64 := by unfold Tables.colKappaAdj; split_ifs <;> omega
  simp only [selBlockT, holdsList_append, Stmt.HoldsList, Stmt.Holds, Atom.Holds] at h
  obtain ⟨loff, h⟩ := h
  obtain ⟨hkv, h⟩ := kapT_sound (src := Tables.colKappaSrc c) (r := selStart c + 1) (rest := [])
    hadj (by rw [List.append_nil]; exact h)
  simp only [Stmt.HoldsList, List.map_cons, List.map_nil] at h
  obtain ⟨c34, m35, ⟨j, hj, hkj, hcall⟩, -⟩ := h
  have hjl : j < 31 := by simpa [colSelNames] using hj
  have hkv' : σ (.n (selKap c).2.1) = gen ^ κ := hkv.trans hkap
  rw [hkv', ← gen_pow_eq_ofK] at hkj
  have hjκ : κ = j := gen_pow_inj_le (by omega) (by omega) hkj
  subst hjκ
  simp only [colSelNames, List.getElem_map, List.getElem_range] at hcall
  have hsg : σ (.n ((selKap c).2.2 + 1)) = σ (.n 0) * gen ^ 34 := by
    rw [m35, c34, show (17179869184 : ℕ) = 2 ^ 34 from rfl, word_two_pow (by decide)]
  rw [hsg] at hcall
  have hcallD := (Same.rel_same' _ (colSel_same κ hjl).1 (colSel_same κ hjl).2 _ _).mp hcall
  have hout := hcs κ hjl μ hμ Lm _ _ hcallD
  have hxl : x.length ≤ termPointCap := by simp only [termPointCap]; omega
  have hpl : (padPoint x).length = termPointCap := padPoint_length hxl
  have htabs := hst Lm.read _ _ hstc ((padPoint x).take 32) (((padPoint x).map (1 + ·)).take 32)
    (by simp [hpl, termPointCap]) (by simp [hpl, termPointCap]) (readsAt_take hpt 32)
    (readsAt_take hpt1 32)
  obtain ⟨o', ho', -, hoff', hsel⟩ := hout hgt
  have e := loadHolds_unique loff hoff
  rw [e] at hoff'
  have ho2 : o < 2 ^ 32 := lt_of_lt_of_le ho (Nat.pow_le_pow_right (by decide) hL)
  have hoo : o = o' :=
    gen_pow_inj (lt_trans ho2 (by norm_num)) (lt_trans ho' (by norm_num)) hoff'
  subst hoo
  rw [hsel hdvd _ _ (by simp [hpl, termPointCap]) (by simp [hpl, termPointCap]) htabs,
    bitsEq_sel o (by omega) hxl, selProd_pad hx ho hκ (by omega)]

/-! ## The second claims' chain -/

/-- **A chain from word `s`**: from `chain[s] = v` and the steps at `g^k`, `s ≤ k < m`, every
`chain[k]`, `s ≤ k ≤ m`, is `v·Π_{s ≤ i < k} p1[i]`. -/
theorem chainFrom_value {rd : Reader} {chain p1 v : E} {ps : List E} (hps : ReadsAt rd p1 ps)
    {s m : ℕ} (hm : m ≤ ps.length) (hs : LoadHolds rd chain s v)
    (hstep : ∀ k, s ≤ k → k < m → PiStep rd chain p1 (gen ^ k)) :
    ∀ k, s ≤ k → k ≤ m → LoadHolds rd chain k (v * ∏ i ∈ Ico s k, ps.getD i 0) := by
  intro k hk hkm
  induction k with
  | zero =>
    have h0 : s = 0 := by omega
    subst h0
    simpa using hs
  | succ k ih =>
    rcases Nat.eq_or_lt_of_le hk with h | h
    · subst h
      simpa using hs
    · have ihk := ih (by omega) (by omega)
      obtain ⟨a, b, la, lb, lab⟩ := hstep k (by omega) (by omega)
      rw [loadHolds_mul_gen_pow, Nat.add_zero] at la lb
      rw [loadHolds_mul_gen_pow] at lab
      have ea := loadHolds_unique la ihk
      have hpk : LoadHolds rd p1 k (ps.getD k 0) := by
        rw [List.getD_eq_getElem _ _ (by omega)]; exact hps k (by omega)
      have eb := loadHolds_unique lb hpk
      rw [ea, eb] at lab
      rw [prod_Ico_succ_top (by omega), ← mul_assoc]
      exact lab

theorem one_add_one_E : (1 : E) + 1 = 0 := e_add_eq_zero_iff.mpr rfl

/-- **The second claims' chain is their point's weight**: `(rm, 1, 0, …, 0)` against `x`. -/
theorem chain2_eq {rm : E} {x : List E} {m : ℕ} (h2 : 2 ≤ m) (hm : m ≤ x.length) :
    (rm + (1 + x.getD 0 0)) * x.getD 1 0 * ∏ i ∈ Ico 2 m, (1 + x.getD i 0) =
      eqEval (rm :: 1 :: List.replicate (m - 2) 0) (x.take m) := by
  rw [eqEval_prod]
  simp only [List.length_cons, List.length_replicate, List.length_take]
  rw [show min (m - 2 + 1 + 1) (min m x.length) = 2 + (m - 2) by omega, prod_range_add,
    Finset.prod_Ico_eq_prod_range]
  simp only [prod_range_succ, prod_range_zero, one_mul]
  rw [getD_take' (by omega), getD_take' (by omega)]
  simp only [List.getD_cons_zero, List.getD_cons_succ]
  have h11 : (1 : E) + 1 + x.getD 1 0 = x.getD 1 0 := by rw [one_add_one_E, zero_add]
  rw [h11]
  refine congrArg₂ (· * ·) (by ring) (prod_congr rfl fun i hi ↦ ?_)
  have hi' := mem_range.mp hi
  rw [getD_take' (by omega), show 2 + i = i + 1 + 1 by omega, List.getD_cons_succ,
    List.getD_cons_succ]
  simp only [List.getD_eq_getElem?_getD, List.getElem?_replicate]
  split <;> simp

/-! ## The batched weight -/

/-- The batch of the ring claim `R`, the weights `Ws`, three more and the last weight `wo`. -/
theorem stack_dot4 (R a b c wo lam : E) (Ws : List E) :
    dot (powers lam (R :: (Ws ++ [a, b, c, wo])).length) (R :: (Ws ++ [a, b, c, wo])) =
      R + ∑ i ∈ range Ws.length, lam ^ (1 + i) * Ws.getD i 0 + lam ^ (1 + Ws.length) * a +
        lam ^ (1 + Ws.length + 1) * b + lam ^ (1 + Ws.length + 2) * c +
        lam ^ (1 + Ws.length + 3) * wo := by
  have e : Ws ++ [a, b, c, wo] = (Ws ++ [a, b, c]) ++ [wo] := by simp
  rw [e, stack_dot]
  simp only [List.length_append, List.length_cons, List.length_nil]
  rw [show Ws.length + (0 + 1 + 1 + 1) = Ws.length + 1 + 1 + 1 by omega, sum_range_succ,
    sum_range_succ, sum_range_succ]
  have g : ∀ i < Ws.length, (Ws ++ [a, b, c]).getD i 0 = Ws.getD i 0 := fun i hi ↦ by
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
  rw [sum_congr rfl fun i hi ↦ by rw [g i (mem_range.mp hi)]]
  have ga : (Ws ++ [a, b, c]).getD Ws.length 0 = a := by simp [List.getD_eq_getElem?_getD]
  have gb : (Ws ++ [a, b, c]).getD (Ws.length + 1) 0 = b := by
    rw [List.getD_append_right _ _ _ _ (by omega), show Ws.length + 1 - Ws.length = 1 by omega]
    rfl
  have gc : (Ws ++ [a, b, c]).getD (Ws.length + 1 + 1) 0 = c := by
    rw [List.getD_append_right _ _ _ _ (by omega), show Ws.length + 1 + 1 - Ws.length = 2 by omega]
    rfl
  rw [ga, gb, gc]
  ring_nf

/-- **The batched weight over the claims and the second claims, as the guest sums it.** -/
theorem stackWeight_eqS (layout : Layout) {claims : List ColumnClaim} (out : ColumnClaim)
    (second : Digest) (r : E) (ringPoint coeffs : List E) (lam : E) (x : List E)
    (hcols : claims.map (·.column) = Tables.claimColumns) :
    stackWeight layout (openedClaims (claims ++ secondClaims layout second r) [out]) ringPoint
        coeffs lam x =
      (ringSwitchClaim layout 0 (fun rP ↦ ringWeight ringPoint rP coeffs)).1 x +
      (∑ j ∈ range Tables.nClaims, if Tables.claimColumns.getD j 0 ∉ keccakOutputColumns then
        lam ^ (1 + poolRank j) * wOf layout x (claims.getD j default) else 0) +
      lam ^ (1 + poolRank Tables.nClaims) *
        wOf layout x ((secondClaims layout second r).getD 0 default) +
      lam ^ (1 + poolRank Tables.nClaims + 1) *
        wOf layout x ((secondClaims layout second r).getD 1 default) +
      lam ^ (1 + poolRank Tables.nClaims + 2) *
        wOf layout x ((secondClaims layout second r).getD 2 default) +
      lam ^ (1 + poolRank Tables.nClaims + 3) * wOf layout x out := by
  have hlen : claims.length = Tables.nClaims := by
    rw [← List.length_map (f := (·.column)), hcols]; decide +kernel
  have hcol : ∀ i < claims.length,
      (claims.getD i default).column = Tables.claimColumns.getD i 0 := by
    intro i hi
    rw [← hcols, List.getD_eq_getElem _ _ hi, List.getD_eq_getElem _ _ (by simpa using hi),
      List.getElem_map]
  let P : ColumnClaim → Bool := fun c ↦ decide (c.column ∉ keccakOutputColumns)
  have hrank : ∀ j ≤ claims.length, keptRank P claims j = poolRank j := by
    intro j hj
    unfold keptRank poolRank
    congr 1
    refine List.filter_congr fun i hi ↦ ?_
    simp only [P]
    rw [hcol i (by have := List.mem_range.mp hi; omega)]
  have hsc : (secondClaims layout second r).filter P = secondClaims layout second r :=
    LeanVM.SaltedGuest.B1.VerifySub.notLanes_secondClaims layout second r
  have hmap : (ringSwitchClaim layout 0 (fun rP ↦ ringWeight ringPoint rP coeffs) ::
      (openedClaims (claims ++ secondClaims layout second r) [out]).map
        (·.stackClaim layout)).map (fun c ↦ c.1 x) =
      (ringSwitchClaim layout 0 (fun rP ↦ ringWeight ringPoint rP coeffs)).1 x ::
        ((claims.filter P).map (wOf layout x) ++
          [wOf layout x ((secondClaims layout second r).getD 0 default),
            wOf layout x ((secondClaims layout second r).getD 1 default),
            wOf layout x ((secondClaims layout second r).getD 2 default), wOf layout x out]) := by
    have ho : openedClaims (claims ++ secondClaims layout second r) [out] =
        claims.filter P ++ secondClaims layout second r ++ [out] := by
      rw [openedClaims, List.filter_append]
      exact congrArg (fun l ↦ claims.filter P ++ l ++ [out]) hsc
    rw [ho]
    simp [wOf, secondClaims]
  simp only [stackWeight]
  rw [← List.length_map (fun c : StackClaim ↦ c.1 x), hmap, stack_dot4, List.length_map,
    filter_length_rank P claims, hrank _ le_rfl, hlen]
  have e : ∀ i ∈ range (poolRank Tables.nClaims),
      lam ^ (1 + i) * ((claims.filter P).map (wOf layout x)).getD i 0 =
        lam ^ (1 + i) * wOf layout x ((claims.filter P).getD i default) := by
    intro i hi
    have hi' : i < (claims.filter P).length := by
      rw [filter_length_rank P claims, hrank _ le_rfl, hlen]; exact mem_range.mp hi
    rw [List.getD_eq_getElem _ _ (by simpa using hi'), List.getElem_map,
      List.getD_eq_getElem _ _ hi']
  have hF := filter_pow_sum P (wOf layout x) lam claims 1
  rw [filter_length_rank P claims, hrank _ le_rfl, hlen] at hF
  have hsum : ∑ i ∈ range (poolRank Tables.nClaims),
      lam ^ (1 + i) * ((claims.filter P).map (wOf layout x)).getD i 0 =
      ∑ j ∈ range Tables.nClaims, if Tables.claimColumns.getD j 0 ∉ keccakOutputColumns then
        lam ^ (1 + poolRank j) * wOf layout x (claims.getD j default) else 0 := by
    rw [sum_congr rfl e, hF]
    refine sum_congr rfl fun j hj ↦ ?_
    have hj' := mem_range.mp hj
    simp only [P]
    rw [hcol j (by omega), hrank j (by omega)]
    simp only [decide_eq_true_eq]
  rw [hsum]

end

end LeanVM.SaltedGuest.B1.Terminal
