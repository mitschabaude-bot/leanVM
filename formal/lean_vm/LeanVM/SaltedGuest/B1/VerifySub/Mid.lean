/-
  LeanVM.SaltedGuest.B1.VerifySub.Mid

  The salted `verify_sub`'s sizes and push total.
-/

module

public import LeanVM.SaltedGuest.B1.VerifySub.Template
public import LeanVM.SaltedGuest.B1.Callee
public import LeanVM.Guest.B1.VerifySub.Mid

/-!
# The sizes and the push total

`vsSizesS_holds`: the rate exponent and the memory's log-size (`2 ≤ logMem ≤ 30`: the range check
against the four public words is the salted guest's), `dims_g`, `kb` in the frame (`150 .. 157`)
and `kappa_base`; `vsPushS_holds`: the push blocks' total and the bus depth. The callees
(`g_power_of_word`, `log2_ceil_in_the_exponent__L0_L34`) are unchanged (`toD_le`), and the deployed
lemmas on values (`rc_pow`, `push_read`, `pushKappa_lt`, …) are reused.
-/

namespace LeanVM.SaltedGuest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Guest.B1 LeanVM.Guest.B1.VerifySub LeanVM.Protocol.Verifier

@[expose] public section

variable {C : CallRel} {σ : Val} {next : Prop} {kret : List E → Prop}

/-- **The sizes**: the rate exponent and the memory's log-size, `dims`, `kb` in the frame
(`150 .. 157`) and `kappa_base`. -/
theorem vsSizesS_holds {κ : ℕ} (hκ : κ ≤ 32) (L : MemoryImage κ)
    (hC : CallRel.Le C (SaltedGuest.coreProgram.Rel L.read))
    (h : Stmt.HoldsList C L.read σ vsSizesS next kret) :
    ∃ lir logMem : ℕ, 1 ≤ lir ∧ lir ≤ 4 ∧ σ (.n 114) = eOfNat lir ∧ σ (.n 126) = gen ^ (lir - 1) ∧
      2 ≤ logMem ∧ logMem ≤ 30 ∧ σ (.n 31) = eOfNat logMem ∧ σ (.n 132) = gen ^ logMem ∧
      ∃ ds : List E, ds.length = 6 ∧ ReadsAt L.read (σ (.n 131)) (gen ^ logMem :: ds) ∧
        ReadsAt L.read (σ (.n 149)) (1 :: gen ^ logMem :: ds) ∧
        (∀ s < 8, σ (.n (150 + s)) = (1 :: gen ^ logMem :: ds).getD s 0) ∧ next := by
  rw [vsSizesS, show (List.range 6) = [0, 1, 2, 3, 4, 5] from rfl,
    show (List.range 8) = [0, 1, 2, 3, 4, 5, 6, 7] from rfl] at h
  simp only [List.map_cons, List.map_nil, List.cons_append, List.nil_append, Stmt.HoldsList,
    Stmt.Holds, vsCall, vsConst, vsMul, vsRange, vsAlloc, vsLd, Atom.Holds, true_and] at h
  obtain ⟨c112, e123, m122, e125, r124, c29, e131, r130, e135, e136, m130, r137, e143, e144, m145,
    r145, l130, e142, cp141, l0, l1, l2, l3, l4, l5, s0, s1, s2, s3, s4, s5, s6, s7, hn⟩ := h
  -- the rate
  obtain ⟨n, hn64, h112, hr122⟩ :=
    (g_power_of_word_holds _ _ _).1 (toD_le hC (by decide +kernel) (by decide +kernel) c112)
  simp only [List.cons.injEq, and_true] at hr122
  obtain ⟨e, he, h124⟩ := rc_pow hκ L (a := 3) (by norm_num)
    (by rw [e125, show (8 : ℕ) = 2 ^ 3 from rfl, word_pow2 (by norm_num)]) r124
  have hne : n = e + 1 := by
    rw [hr122, h124, e123, word_gen, ← pow_succ] at m122
    exact gen_pow_eq_iff (by omega) (by omega) m122
  -- the memory's log-size
  obtain ⟨m, hm64, h29, hr130⟩ :=
    (g_power_of_word_holds _ _ _).1 (toD_le hC (by decide +kernel) (by decide +kernel) c29)
  simp only [List.cons.injEq, and_true] at hr130
  obtain ⟨e1, he1, h130⟩ := rc_pow hκ L (a := 30) (by norm_num)
    (by rw [e131, word_pow2 (by norm_num)]) r130
  obtain ⟨e2, he2, h137⟩ := rc_pow hκ L (a := 32) le_rfl
    (by rw [e135, word_pow2 (by norm_num)]) r137
  obtain ⟨e3, he3, h145⟩ := rc_pow hκ L (a := 32) le_rfl
    (by rw [e143, word_pow2 (by norm_num)]) r145
  have hm1 : m = e1 := by rw [hr130] at h130; exact gen_pow_eq_iff (by omega) (by omega) h130
  have hm2 : m = e2 + 1 := by
    rw [hr130, h137, e136, show (2 : ℕ) = 2 ^ 1 from rfl, word_pow2 (by norm_num),
      ← pow_add] at m130
    exact gen_pow_eq_iff (by omega) (by omega) m130
  have hm3 : m = e3 + 2 := by
    rw [hr130, h145, e144, show (4 : ℕ) = 2 ^ 2 from rfl, word_pow2 (by norm_num),
      ← pow_add] at m145
    exact gen_pow_eq_iff (by omega) (by omega) m145
  have h140 : σ (.n 150) = 1 := by rw [e142, word_one]
  have h141 : σ (.n 151) = gen ^ m := by rw [cp141, hr130]
  refine ⟨n, m, by omega, by omega, h112, by rw [h124, hne]; rfl, by omega, by omega, h29, hr130,
    [σ (.n 152), σ (.n 153), σ (.n 154), σ (.n 155), σ (.n 156), σ (.n 157)], rfl, ?_, ?_,
    fun s hs ↦ ?_, hn⟩
  · intro k hk
    simp only [List.length_cons, List.length_nil] at hk
    interval_cases k
    · simp only [List.getElem_cons_zero]; rw [← hr130]; exact l130
    · exact l0
    · exact l1
    · exact l2
    · exact l3
    · exact l4
    · exact l5
  · intro k hk
    simp only [List.length_cons, List.length_nil] at hk
    interval_cases k
    · simp only [List.getElem_cons_zero]; rw [← h140]; exact s0
    · simp only [List.getElem_cons_succ, List.getElem_cons_zero]; rw [← h141]; exact s1
    · exact s2
    · exact s3
    · exact s4
    · exact s5
    · exact s6
    · exact s7
  · interval_cases s
    · exact h140
    · exact h141
    all_goals rfl

theorem push_blockS {κ : ℕ} {L : MemoryImage κ} (hexp : B1.ExpTables L.read (σ (.n 4)))
    {logMem : ℕ} {hs : List ℕ} (hh : ∀ x ∈ hs, x < 33) (hm : logMem ≤ 32)
    (hkbv : ∀ s < 8, σ (.n (150 + s)) = gen ^ (([0, logMem] ++ hs).getD s 0))
    {b : ℕ} (hb : b < 54) {q a : V}
    (ha : σ a = σ (.n 4) * σ (.n (150 + Tables.blockKappaSrc.getD b 0)))
    (hq : LoadHolds L.read (σ a) (Tables.blockKappaAdj b) (σ q)) :
    σ q = gen ^ 2 ^ pushKappa logMem hs b :=
  push_read hexp (pushKappa_lt hh hm hb) (hkbv _ (blockKappaSrc_lt b (by show b < 153; omega))) ha hq

theorem push_loopS {κ : ℕ} {L : MemoryImage κ} (hexp : B1.ExpTables L.read (σ (.n 4)))
    {logMem : ℕ} {hs : List ℕ} (hh : ∀ x ∈ hs, x < 33) (hm : logMem ≤ 32)
    (hkbv : ∀ s < 8, σ (.n (150 + s)) = gen ^ (([0, logMem] ++ hs).getD s 0)) :
    ∀ n < 54, ∀ {nx : Prop},
      Stmt.HoldsList C L.read σ ((List.range (n + 1)).flatMap vsPushStepS) nx kret →
      σ (.n (vsPVS n)) = gen ^ ((List.range (n + 1)).map fun b ↦ 2 ^ pushKappa logMem hs b).sum ∧
        nx := by
  intro n
  induction n with
  | zero =>
    intro _ nx h
    rw [show List.range (0 + 1) = [0] from rfl] at h
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, vsPushStepS,
      ↓reduceIte, Stmt.HoldsList, Stmt.Holds, Atom.Holds, vsLd, vsMul] at h
    obtain ⟨m, l, hn⟩ := h
    refine ⟨?_, hn⟩
    rw [show vsPVS 0 = 159 from rfl, push_blockS hexp hh hm hkbv (b := 0) (by norm_num) m l]
    simp
  | succ n ih =>
    intro hn nx h
    rw [List.range_succ, List.flatMap_append, holdsList_append] at h
    obtain ⟨hp, h⟩ := ih (by omega) h
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, vsPushStepS,
      Nat.add_one_ne_zero, ↓reduceIte, Stmt.HoldsList, Stmt.Holds, Atom.Holds, vsLd, vsMul] at h
    obtain ⟨m, l, m2, hn'⟩ := h
    refine ⟨?_, hn'⟩
    rw [m2, Nat.add_sub_cancel, hp, push_blockS hexp hh hm hkbv hn m l, ← pow_add,
      List.range_succ (n := n + 1), List.map_append, List.sum_append]
    simp

/-- **The push total**: the bus depth `g^(log2Ceil Σ)` over the push blocks' `Σ 2^κ_b`. -/
theorem vsPushS_holds {κ : ℕ} (hκ : κ ≤ 32) (hκ6 : 6 ≤ κ) (L : MemoryImage κ)
    (hC : CallRel.Le C (SaltedGuest.coreProgram.Rel L.read)) (hexp : B1.ExpTables L.read (σ (.n 4)))
    {logMem : ℕ} {hs : List ℕ} (hh : ∀ x ∈ hs, x < 33) (hm : logMem ≤ 32)
    (hkbv : ∀ s < 8, σ (.n (150 + s)) = gen ^ (([0, logMem] ++ hs).getD s 0))
    (h : Stmt.HoldsList C L.read σ vsPushS next kret) :
    σ (.n 319) = gen ^ log2Ceil ((List.range 54).map fun b ↦ 2 ^ pushKappa logMem hs b).sum ∧
      log2Ceil ((List.range 54).map fun b ↦ 2 ^ pushKappa logMem hs b).sum < 34 ∧ next := by
  unfold vsPushS at h
  rw [holdsList_append] at h
  obtain ⟨hp, h⟩ := push_loopS hexp hh hm hkbv 53 (by norm_num) h
  simp only [Stmt.HoldsList, Stmt.Holds, vsCall, List.map_cons, List.map_nil, Atom.Holds,
    true_and] at h
  obtain ⟨hc, hn⟩ := h
  rw [show vsPVS 53 = 318 from rfl] at hp
  replace hp : σ (.n 318) = gen ^ ((List.range 54).map fun b ↦ 2 ^ pushKappa logMem hs b).sum := hp
  have hr := (log2_holds.1 hκ hκ6 L _ _ hexp _).1
    (toD_le hC (by decide +kernel) (by decide +kernel) hc)
  rw [hp, meaningLog2CeilExp_pow (by norm_num) (by have := push_sum_lt hh hm; omega)] at hr
  simp only [List.cons.injEq, and_true, Nat.zero_max] at hr
  exact ⟨hr.2, hr.1, hn⟩

end
end LeanVM.SaltedGuest.B1.VerifySub
