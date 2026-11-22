/-
  LeanVM.SaltedGuest.B1.Terminal.HoldsK

  **The salted `check_opening_terminal` is sound**: the WHIR terminal with the stack's weight over
  the claims and the second claims.
-/

module

public import LeanVM.SaltedGuest.B1.Terminal.LibK
public import LeanVM.Guest.B1.Terminal.Holds

/-!
# The salted `check_opening_terminal`, assembled

The deployed `check_opening_terminal_holds_of` over the salted template `termTK`: its head, the
selectors and the claims' blocks are the deployed ones at `σ ∘ termR`, its tail at `σ ∘ termR2`
(read at the salted values); its callees are unchanged functions, their deployed meanings
(`eq_prefix_chain_holds`, `ring_switch_weight_holds`, `column_selector_holds`,
`selector_tables_holds`, `__loop14`'s step) through the transfer. The inserted second chain is
the second claims' point's weight (`chainFrom_value` over `__loop15`'s step, `chain2_eq`); the
inserted terms are the three second claims' weights at their powers of `λ` (`term_committed`
with the memory columns' selectors), so with `stackWeight_eqS` the last check is the WHIR
terminal over the claims and the second claims.
-/

namespace LeanVM.SaltedGuest.B1.Terminal

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Guest.B1 LeanVM.Guest.B1.VerifySub LeanVM.Protocol LeanVM.Protocol.Verifier Finset
open LeanVM.Protocol.Compile Recursion.SecondDigest

@[expose] public section

theorem termR2_n (k : ℕ) : termR2 (.n k) = .n (termR2i k) := rfl

theorem selV_five : selV 5 = 69 := by decide

/-- **The salted `check_opening_terminal` is sound**, on a memory image of at most `2^32` words. -/
theorem check_opening_terminal_holdsK {μ : ℕ} (hμ : μ ≤ 32) (Lm : MemoryImage μ) :
    LeanVM.SaltedGuest.B1.VerifySub.check_opening_terminal_SpecK Lm.read := by
  have hep := eq_prefix_chain_holds
  have hrsw := ring_switch_weight_holds
  have hcs := Tables.column_selector_holds
  have hst := Tables.selector_tables_holds
  have tD : ∀ {f : String} {a r : List E}, (Same.inS f = true ∧ Same.rho f = f) →
      SaltedGuest.coreProgram.Rel Lm.read f a r → Guest.coreProgram.Rel Lm.read f a r :=
    fun hs h ↦ (Same.rel_same' _ hs.1 hs.2 _ _).mp h
  intro args rets h
  obtain ⟨fn, hf, hpar0, hbody⟩ := termFoundK
  obtain ⟨σ, hpar, hb⟩ := (rel_iff_sem hf args rets).mp h
  rw [hpar0] at hpar
  simp only [termParams, List.map_cons, List.map_nil] at hpar
  subst hpar
  rw [hbody, termTK, holdsList_append, holdsList_append, holdsList_append, holdsList_append] at hb
  -- the head up to the public input's chain
  simp only [termHeadT, List.take_succ_cons, List.take_zero, Stmt.HoldsList, Stmt.Holds,
    Atom.Holds, List.map_cons, List.map_nil] at hb
  obtain ⟨-, e19, hcz, -, e21, hcr, e22, e23, -, -, -, l26, e27, l27, e28, e29, e30, -, hloop, e31,
    l32, hb⟩ := hb
  -- the second claims' chain
  simp only [termIns1, Stmt.HoldsList, Stmt.Holds, Atom.Holds, List.map_cons, List.map_nil] at hb
  obtain ⟨-, l34, l35, e36, l36, e37, e38, e39, -, hloop2, e40, l41, hb⟩ := hb
  -- the base, the selectors and the claims, at `σ ∘ termR`
  rw [Stmt.holdsList_rename termR σ termMidT] at hb
  set τ := σ ∘ termR with hτ
  rw [termMidT, holdsList_append, holdsList_append] at hb
  simp only [termHeadT, List.drop_succ_cons, List.drop_zero, Stmt.HoldsList, Stmt.Holds,
    Atom.Holds, List.map_cons, List.map_nil] at hb
  obtain ⟨k0, k1, k2, k3, k4, k5, k6, k7, hstc, hb⟩ := hb
  change Stmt.HoldsList _ _ τ ((List.range Tables.nCommittedCols).map selBlockT).flatten _ _ at hb
  rw [holdsList_range_flatten Tables.nCommittedCols selBlockT selBlockT_noRet] at hb
  obtain ⟨hsels, hb⟩ := hb
  rw [holdsList_noRet termClaims.1 (claimsT_noRet _ _ _ _)] at hb
  obtain ⟨hcl, hb⟩ := hb
  -- the second claims' terms
  simp only [termIns2, Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hb
  obtain ⟨f1775, f1776, f1777, f1778, f1779, f1780, f1781, f1782, f1783, f1784, f1785, f1786,
    hb⟩ := hb
  -- the tail, at the salted values
  rw [Stmt.holdsList_rename termR2 σ] at hb
  simp only [termTailT, Stmt.HoldsList, Stmt.Holds, Atom.Holds, List.map_cons, List.map_nil,
    Function.comp_apply, termR2_n, selV_five, Nat.reduceAdd, termR2i, Nat.reduceLT, Nat.reduceEqDiff,
    ↓reduceIte] at hb
  obtain ⟨-, e1788, e1789, e1790, hco, e1791, e1792, e1793, e1794, hrw, e1796, l1797, e1798,
    e1799, e1800, e1801, e1802, afin, hret⟩ := hb
  refine ⟨hret.symm, ?_⟩
  intro layout bus claims out lam ringPoint coeffs x second hpre hlm2
  simp only [TermPre] at hpre
  obtain ⟨hT, hPC, -, hP, hSL, hSL30, hlm1, -, hbus40, hHL, -, hglm, hgtau, hkbR, hgt, hlamC,
    hoc, hopl, hoz, hrpl, hrp, hcfl, hct, hxl, hpt, hpt1⟩ := hpre
  have hSL28 : layout.stackLog ≤ 32 := by omega
  obtain ⟨chis, hzR, hgmu, hchR, hgzc, hchL, -, hcols, hpts⟩ := hT
  obtain ⟨hkap, hOr⟩ := hPC
  simp only [List.getD_cons_succ, List.getD_cons_zero]
  -- names
  set kappas := columnKappas layout.logMemory Tables.guestLogBytecode layout.tableLogHeights
    with hkdef
  set KC := Tables.committedKappas kappas with hKCdef
  set τk := layout.tableLogHeights.getD opKeccak 0 with hτk
  have hKClen : KC.length = Tables.nCommittedCols := Tables.committedKappas_length _ hkap
  have hKC : KC = (List.range Tables.nCommittedCols).map fun c ↦
      (0 :: layout.logMemory :: layout.tableLogHeights).getD (Tables.colKappaSrc c) 0 +
        Tables.colKappaAdj c :=
    Tables.committedKappas_columnKappas layout.logMemory layout.tableLogHeights hHL
  have hLdef : layout.stackLog = max Whir.minLogStack (stackOffsets KC).2 := by
    rw [hSL, placementsOf_snd]
  have hK : ∀ c < Tables.nCommittedCols, KC.getD c 0 ≤ layout.stackLog := fun c hc ↦ by
    have := size_le_stackOffsets KC (i := c) (by omega); rw [hLdef]; omega
  have hO : ∀ c, (stackOffsets KC).1.getD c 0 < 2 ^ layout.stackLog := fun c ↦
    lt_of_lt_of_le (stackOffsets_lt KC c) (Nat.pow_le_pow_right (by decide) (by rw [hLdef]; omega))
  -- the base
  have hkb : ∀ i < 8, τ (.n (kbV i)) = gen ^ kbExp layout i := by
    intro i hi
    have hk := kb_loads k0 k1 k2 k3 k4 k5 k6 k7 i hi
    have hr := hkbR i (by simp [hHL]; omega)
    rw [kb_words hHL hi] at hr
    exact loadHolds_unique hk hr
  have hKCv : ∀ c < Tables.nCommittedCols, KC.getD c 0 =
      kbExp layout (Tables.colKappaSrc c) + Tables.colKappaAdj c := fun c hc ↦ by
    rw [hKC, List.getD_eq_getElem _ _ (by simpa using hc), List.getElem_map, List.getElem_range]
    rfl
  have hsrc8 : ∀ c, Tables.colKappaSrc c < 8 := fun c ↦ by
    unfold Tables.colKappaSrc; split_ifs <;> omega
  have hkapc : ∀ c < Tables.nCommittedCols,
      τ (.n (kbV (Tables.colKappaSrc c))) * gen ^ Tables.colKappaAdj c = gen ^ KC.getD c 0 :=
    fun c hc ↦ by rw [hkb _ (hsrc8 c), hKCv c hc, pow_add]
  have hoff' : ∀ c < Tables.nCommittedCols,
      LoadHolds Lm.read (τ (.n 10)) c (gen ^ (stackOffsets KC).1.getD c 0) := fun c hc ↦ by
    have hl : c < (stackOffsets KC).1.length := by rw [stackOffsets_length]; omega
    have := hOr c (by simpa using hl)
    rw [List.getElem_map] at this
    rw [List.getD_eq_getElem _ _ hl]; exact this
  have hstcD := tD same_selector_tables hstc
  have hselc := fun c (hc : c < Tables.nCommittedCols) ↦ sel_valueK hcs hst hμ Lm (σ := τ)
    (hsels c hc) hstcD hgt (hkapc c hc) (hoff' c hc) (stackOffsets_dvd KC c) (hK c hc) hSL28
    (hO c) hxl hpt hpt1
  -- sizes
  have hk6 : kappas.take 6 = [layout.logMemory, layout.logMemory, layout.logMemory,
      layout.logMemory, Tables.guestLogBytecode, τk + 6] := kappas_small hHL
  have hksmall : ∀ c < 6, kappas.getD c 0 =
      [layout.logMemory, layout.logMemory, layout.logMemory, layout.logMemory,
        Tables.guestLogBytecode, τk + 6].getD c 0 := fun c hc ↦ by
    rw [← hk6, getD_take_nat hc]
  have hK5 : KC.getD 5 0 = τk + 6 := by
    rw [committedKappas_small hkap (by decide), hksmall 5 (by decide)]; rfl
  have hmem : ∀ c < 3, KC.getD c 0 = layout.logMemory := fun c hc ↦ by
    rw [committedKappas_small hkap (by omega), hksmall c (by omega)]
    interval_cases c <;> rfl
  have hK5L := hK 5 (by decide)
  rw [hK5] at hK5L
  have hxl40 : x.length ≤ termPointCap := by simp only [termPointCap]; omega
  have hpl40 : ((padPoint x).map (1 + ·)).length = termPointCap := by
    simp [padPoint_length hxl40]
  -- the chains
  rw [e19, word_one] at hcz
  rw [e21, word_one] at hcr
  have hzc := chain_value ((hep _ _ _).mp (tD same_eq_prefix_chain hcz)) hgmu hbus40 hzR hxl40
    hpt1
  have hrc := chain_value ((hep _ _ _).mp (tD same_eq_prefix_chain hcr)) hgzc (by omega) hchR
    hxl40 hpt1
  -- the slot points
  have hs1 : ∀ k < 6, valOf Lm.read (σ (.n 22)) k = x.getD (τk + k) 0 := fun k hk ↦ by
    have l := readsAt_getD hpt (k := τk + k)
      (by rw [padPoint_length hxl40]; simp only [termPointCap]; omega)
    rw [← loadHolds_mul_gen_pow, ← hgtau, ← e22] at l
    rw [valOf_eq l, padPoint_getD]
  have hs0 : ∀ k < 6, valOf Lm.read (σ (.n 23)) k = 1 + x.getD (τk + k) 0 := fun k hk ↦ by
    have l := readsAt_getD hpt1 (k := τk + k) (by rw [hpl40]; simp only [termPointCap]; omega)
    rw [← loadHolds_mul_gen_pow, ← hgtau, ← e23] at l
    rw [valOf_eq l, x1_getD hxl40 (by simp only [termPointCap]; omega)]
  -- the public input's chain
  have hlmL : layout.logMemory ≤ layout.stackLog := by
    have := hK 0 (by decide); rw [hmem 0 (by decide)] at this; exact this
  have hstep : ∀ k, 1 ≤ k → k < layout.logMemory →
      PiStep Lm.read (σ (.n 24)) (σ (.n 14)) (gen ^ k) := by
    intro k hk1 hk2
    have hne : σ (.n 29) ≠ 0 := by
      rw [e29, e28, word_gen, hglm]
      intro h0
      have := gen_pow_inj_le (a := 1) (b := layout.logMemory) (by omega) (by omega)
        (by rw [pow_one]; exact e_add_eq_zero_iff.mp h0)
      omega
    have hc : Guest.coreProgram.Rel Lm.read "__loop14"
        (gen ^ 1 :: [σ (.n 6), σ (.n 24), σ (.n 14)]) [] := by
      rw [pow_one, ← word_gen, ← e30]; exact tD same_loop14 (hloop hne)
    exact loop_sound (P := Guest.coreProgram) (f := "__loop14")
      (ps := [σ (.n 6), σ (.n 24), σ (.n 14)])
      (N := σ (.n 6)) (B := PiStep Lm.read (σ (.n 24)) (σ (.n 14))) (m := layout.logMemory)
      (fun d y h ↦ loop15_step d y _ _ _ h) hglm (by unfold ordG; omega) 1 hc k hk1 hk2
  have hx1_0 := loadHolds_unique l26 (readsAt_getD hpt1 (k := 0) (by rw [hpl40]; decide))
  have h1 : LoadHolds Lm.read (σ (.n 24)) 1 (σ (.n 3) + ((padPoint x).map (1 + ·)).getD 0 0) := by
    rw [← hx1_0, ← e27]; exact l27
  have hpi := piChain_value hpt1 (m := layout.logMemory)
    (by rw [hpl40]; simp only [termPointCap]; omega) h1 hstep layout.logMemory hlm1 le_rfl
  rw [e31, hglm, loadHolds_mul_gen_pow, Nat.add_zero] at l32
  have h32 : σ (.n 32) = eqEval (σ (.n 3) :: List.replicate (layout.logMemory - 1) 0)
      (x.take layout.logMemory) := by
    rw [loadHolds_unique l32 hpi, x1_getD hxl40 (by decide), ← piChain_eq hlm1 (by omega)]
    refine congrArg (_ * ·) (prod_congr rfl fun i hi ↦ ?_)
    rw [x1_getD hxl40 (by have := (mem_Ico.mp hi).2; simp only [termPointCap]; omega)]
  -- the second claims' chain
  have hstep2 : ∀ k, 2 ≤ k → k < layout.logMemory →
      PiStep Lm.read (σ (.n 33)) (σ (.n 14)) (gen ^ k) := by
    intro k hk1 hk2
    have hw4 : word 4 0 0 = gen ^ 2 := word_two_pow (a := 2) (by decide)
    have hne : σ (.n 38) ≠ 0 := by
      rw [e38, e37, hw4, hglm]
      intro h0
      have := gen_pow_inj_le (a := 2) (b := layout.logMemory) (by omega) (by omega)
        (e_add_eq_zero_iff.mp h0)
      omega
    have hc : SaltedGuest.coreProgram.Rel Lm.read "__loop15"
        (gen ^ 2 :: [σ (.n 6), σ (.n 33), σ (.n 14)]) [] := by
      rw [← hw4, ← e39]; exact hloop2 hne
    exact loop_sound (P := SaltedGuest.coreProgram) (f := "__loop15")
      (ps := [σ (.n 6), σ (.n 33), σ (.n 14)])
      (N := σ (.n 6)) (B := PiStep Lm.read (σ (.n 33)) (σ (.n 14))) (m := layout.logMemory)
      (fun d y h ↦ loop16_step d y _ _ _ h) hglm (by unfold ordG; omega) 2 hc k hk1 hk2
  have h34 : σ (.n 34) = σ (.n 3) + (1 + x.getD 0 0) := by
    rw [loadHolds_unique l34 h1, x1_getD hxl40 (by decide)]
  have hxl2 : 2 ≤ x.length := by omega
  have h35 : σ (.n 35) = x.getD 1 0 := by
    rw [loadHolds_unique l35 (readsAt_getD hpt (k := 1)
      (by rw [padPoint_length hxl40]; decide)), padPoint_getD]
  rw [e36] at l36
  have hch2 := chainFrom_value hpt1 (s := 2) (m := layout.logMemory)
    (by rw [hpl40]; simp only [termPointCap]; omega) l36 hstep2 layout.logMemory hlm2 le_rfl
  rw [e40, hglm, loadHolds_mul_gen_pow, Nat.add_zero] at l41
  have h41 : σ (.n 41) = eqEval (σ (.n 3) :: 1 :: List.replicate (layout.logMemory - 2) 0)
      (x.take layout.logMemory) := by
    rw [loadHolds_unique l41 hch2, h34, h35, ← chain2_eq hlm2 (by omega)]
    refine congrArg (_ * ·) (prod_congr rfl fun i hi ↦ ?_)
    rw [x1_getD hxl40 (by have := (mem_Ico.mp hi).2; simp only [termPointCap]; omega)]
  -- the claims' points and the batching powers
  have hclen : claims.length = 167 := by
    rw [← List.length_map (f := (·.column)), hcols, claimColumns_eq]; simp
  have hptj : ∀ j < 167, (claims.map (·.point))[j]? = some (claims.getD j default).point :=
    fun j hj ↦ by
      rw [List.getElem?_map, List.getElem?_eq_getElem (by omega),
        List.getD_eq_getElem _ _ (by omega)]
      rfl
  rw [termClaims, List.range_eq_range'] at hcl
  obtain ⟨hsum, hlamO, -⟩ := claimsT_sound (C := SaltedGuest.coreProgram.Rel Lm.read) hkb
    (rk := poolRank) (σ := τ) hlamC 167 0 claimsStart 15 9 (fun j hj ↦ poolRank_succ (by omega))
    (show σ (.n 9) = _ by rw [hlamC]; simp [poolRank]) hcl
  rw [show (claimsT (List.range' 0 167) claimsStart 15 9).2 = (1766, 1764, 1765) by
    rw [← termClaims_end, termClaims, List.range_eq_range']] at hsum hlamO
  have hsumS : σ (.n 1773) = σ (.n 15) +
      ∑ i ∈ range 167, claimTerm Lm.read τ (kbExp layout) (lam ^ (1 + poolRank (0 + i))) (0 + i) :=
    hsum
  have hlamOS : σ (.n 1774) = lam ^ (1 + poolRank (0 + 167)) := hlamO
  have hmem0 : (layout.placement memory0).variableCount = layout.logMemory := by
    have := placement_committed hkap hP (cc := 0) (by decide)
    rw [committedCols_getD (by decide)] at this
    rw [show memory0 = 0 from rfl, show colOfCommitted 0 = 0 from rfl] at *
    rw [this, hmem 0 (by decide)]
  have T : ClaimsCtx Lm.read τ layout kappas claims bus.point chis x (σ (.n 3)) :=
    { hkap := hkap, hKC := hKC, hP := hP, hx := hxl, hL := hSL28, hK := hK,
      hq := stackOffsets_dvd KC 5, hK5 := hK5,
      hlane := fun g h1 h2 ↦ kappas_keccak hHL (by omega) (by omega), hmem := hmem,
      hlm := hlm1, hmem0 := hmem0, hcols := hcols, hzs := hbus40, hchis := hchL,
      hpz := fun j hj ↦ (hpts j _ (hptj j (by omega))).2.1 hj,
      hpc := fun j h1 h2 ↦ (hpts j _ (hptj j (by omega))).2.2.1 h1 h2,
      hpp := fun j h1 h2 ↦ (hpts j _ (hptj j h2)).2.2.2 h1,
      hlen := fun j hj ↦ (hpts j _ (hptj j (by omega))).1 hj,
      hsel := fun c hc ↦ hselc c hc,
      hzc := fun n h1 h2 ↦ hzc n h1 (by rw [hxl]; exact h2),
      hrc := fun n h1 h2 ↦ hrc n h1 (by rw [hxl]; exact h2),
      hs1 := hs1, hs0 := hs0, hpi := h32 }
  -- the second claims' weights
  have hw2 : ∀ i < 3, wOf layout x ((secondClaims layout second (σ (.n 3))).getD i default) =
      σ (.n 41) * τ (.n (selV i)) := by
    intro i hi
    have hNC : i < Tables.nCommittedCols := by
      have : Tables.nCommittedCols = 101 := rfl
      omega
    have hc : ((secondClaims layout second (σ (.n 3))).getD i default).column =
        (Tables.committedCols 165).getD i 0 := by
      rw [committedCols_getD hNC]
      interval_cases i <;> rfl
    have hp : ((secondClaims layout second (σ (.n 3))).getD i default).point =
        secondPoint layout (σ (.n 3)) := by
      interval_cases i <;> rfl
    have hlen : ((secondClaims layout second (σ (.n 3))).getD i default).point.length =
        KC.getD i 0 := by
      rw [hp, hmem i hi, secondPoint]
      simp only [List.length_cons, List.length_replicate, hmem0]
      omega
    have := term_committed (L := 1) (cc := i) hNC hkap hP hc hxl (hK i hNC) hlen
      (chainV := σ (.n 41)) (sel := τ (.n (selV i)))
      (by rw [h41, hlen, hmem i hi, hp, secondPoint, hmem0]) (hselc i hNC)
    simpa using this.symm
  -- the tail: the outputs' claim and the ring switch's
  have hq5 := placement_committed hkap hP (cc := 5) (by decide)
  rw [committedCols_getD (by decide), show colOfCommitted 5 = 5 from rfl] at hq5
  have hw64 : word 64 0 0 = gen ^ 6 := word_two_pow (a := 6) (by decide)
  have h1790 : σ (.n 1790) = gen ^ out.point.length := by
    rw [e1790, e1789, hw64, hgtau, ← pow_add, hopl, Tables.qkeccakSlotBits_eq]
  rw [e1788, word_one, h1790] at hco
  have hoL : out.point.length = τk + 6 := by rw [hopl, Tables.qkeccakSlotBits_eq]
  have hoc' := chain_value ((hep _ _ _).mp (tD same_eq_prefix_chain hco)) rfl (by omega) hoz
    hxl40 hpt1
  rw [e1796, hgtau, loadHolds_mul_gen_pow] at l1797
  have h1797 : σ (.n 1797) = eqEval out.point (x.take (τk + 6)) := by
    rw [eq_valOf l1797, show τk + 6 = out.point.length from hoL.symm, hoc' _ le_rfl (by omega),
      List.take_of_length_le le_rfl]
  obtain ⟨n, hn, hng, rs, ps, cs, hrsl, hpsl, hcsl, hrsR, hpsR, hcsR, hret'⟩ :=
    hrsw _ _ _ (tD same_ring_switch_weight hrw)
  have hn6 : n = τk + 6 := by
    rw [e1794, e1793, hw64, hgtau, ← pow_add] at hng
    exact gen_pow_inj_le (by omega) (by omega) hng.symm
  subst hn6
  rw [e1792, e1791, show (549755813888 : ℕ) = 2 ^ 39 from rfl, word_two_pow (by decide)] at hrsR
  have hrs : rs = ringPoint :=
    readsAt_unique hrsR hrp (by rw [hrsl, hrpl, Tables.qkeccakSlotBits_eq])
  have hps : ps = ((padPoint x).map (1 + ·)).take (τk + 6) :=
    readsAt_unique hpsR (readsAt_take hpt1 _)
      (by rw [hpsl, List.length_take, hpl40]; simp only [termPointCap]; omega)
  have hcs' : cs = coeffs := readsAt_unique hcsR hct (by rw [hcsl, hcfl])
  simp only [List.cons.injEq, and_true] at hret'
  rw [hrs, hps, hcs', map_one_take (by omega)] at hret'
  have hs5 : σ (.n 78) = τ (.n (selV 5)) := by rw [selV_five]; rfl
  have hs0' : σ (.n 54) = τ (.n (selV 0)) := rfl
  have hs1' : σ (.n 58) = τ (.n (selV 1)) := rfl
  have hs2' : σ (.n 62) = τ (.n (selV 2)) := rfl
  -- the terminal check
  have hfin : σ (.n 1802) = σ (.n 17) := e_add_eq_zero_iff.mp afin
  rw [stackWeight_eqS layout out second (σ (.n 3)) ringPoint coeffs lam x hcols, ← hfin, e1802,
    e1801, f1785, f1784, f1783, f1781, f1780, f1779, f1777, f1776, f1775, f1782, f1778, hsumS,
    e1800, e1799, e1798, f1786, f1782, f1778, hret', h1797, hlamOS, hlamC, hs5, hs0', hs1', hs2',
    hw2 0 (by decide), hw2 1 (by decide), hw2 2 (by decide)]
  simp only [zero_add]
  rw [sum_congr rfl fun j hj ↦ claimTerm_eq T (mem_range.mp hj),
    ringClaim_eq (show layout.placement qkeccak = _ from hq5) hxl,
    wOf_committed (by rw [hoc]; exact hq5) (by rw [hoL, hK5]) hxl (hK 5 (by decide)),
    hselc 5 (by decide), hK5]
  ring

end

end LeanVM.SaltedGuest.B1.Terminal
