/-
  LeanVM.SaltedGuest.B1.VerifySub.FrontAll

  The salted `verify_sub`'s front, up to its call of `verify_tables`, as one structure.
-/

module

public import LeanVM.SaltedGuest.B1.VerifySub.Front
public import LeanVM.SaltedGuest.B1.VerifySub.Mid
public import LeanVM.Guest.B1.VerifySub.FrontAll

/-!
# The salted front

`vsFpwS_holds`: `fp_w`, the bus challenges' equality weights (the deployed `vsFpwT_holds`
renumbered); `vsCalls1S_holds`: the bus's GKR and the tables' calls; `VsFrontS`: what the head, the
announced words, the sizes, the push total, the root, the challenges, `fp_w` and the two calls
establish, the transcript starting at the seed state of the child's digest under the seed
(`seedInput₂ seed pi seed`), the memory at least four words (`2 ≤ logMem`); `vs_frontS`: they hold.
-/

namespace LeanVM.SaltedGuest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Guest.B1 LeanVM.Guest.B1.VerifySub
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open Recursion.SecondDigest LeanVM.Protocol.KeccakGkr

@[expose] public section

variable {C : CallRel} {rd : Reader} {σ : Val} {next : Prop} {kret : List E → Prop}

/-! ## `fp_w` -/

theorem vsEqwFactorS_holds {x t v : ℕ} {a : E} (ha : LoadHolds rd (σ (.n 356)) t a)
    (h : Stmt.HoldsList C rd σ (vsEqwFactorS x t v).1 next kret) :
    σ (.n (vsEqwFactorS x t v).2.1) = (if x.testBit t then a else 1 + a) ∧ next := by
  unfold vsEqwFactorS at h ⊢
  by_cases hb : x.testBit t
  · simp only [hb, ↓reduceIte, Stmt.HoldsList, Stmt.Holds, Atom.Holds, vsLd] at h ⊢
    exact ⟨loadHolds_unique h.1 ha, h.2⟩
  · simp only [hb, Bool.false_eq_true, ↓reduceIte, Stmt.HoldsList, Stmt.Holds, Atom.Holds, vsLd,
      vsConst, vsAdd] at h ⊢
    obtain ⟨l, c, s, n⟩ := h
    refine ⟨?_, n⟩
    rw [s, c, loadHolds_unique l ha, word_one]

theorem vsEqwS_holds {x v : ℕ} {a0 a1 a2 a3 : E}
    (ha : ReadsAt rd (σ (.n 356)) [a0, a1, a2, a3])
    (h : Stmt.HoldsList C rd σ (vsEqwS x v).1 next kret) :
    σ (.n (vsEqwS x v).2.1) = eqAt [a0, a1, a2, a3] x ∧ next := by
  have l0 : LoadHolds rd (σ (.n 356)) 0 a0 := ha 0 (by simp)
  have l1 : LoadHolds rd (σ (.n 356)) 1 a1 := ha 1 (by simp)
  have l2 : LoadHolds rd (σ (.n 356)) 2 a2 := ha 2 (by simp)
  have l3 : LoadHolds rd (σ (.n 356)) 3 a3 := ha 3 (by simp)
  unfold vsEqwS at h ⊢
  simp only [holdsList_append] at h
  obtain ⟨e0, h⟩ := vsEqwFactorS_holds l0 h
  obtain ⟨e1, h⟩ := vsEqwFactorS_holds l1 h
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, vsMul] at h
  obtain ⟨m1, h⟩ := h
  obtain ⟨e2, h⟩ := vsEqwFactorS_holds l2 h
  obtain ⟨m2, h⟩ := h
  obtain ⟨e3, h⟩ := vsEqwFactorS_holds l3 h
  obtain ⟨m3, h⟩ := h
  refine ⟨?_, h⟩
  rw [m3, m2, m1, e0, e1, e2, e3, testBit_eqAt]

theorem fpw_loopS {a0 a1 a2 a3 : E} (ha : ReadsAt rd (σ (.n 356)) [a0, a1, a2, a3]) :
    ∀ (l : List ℕ) {next : Prop}, Stmt.HoldsList C rd σ (l.flatMap fun x ↦
      (vsEqwS x (vsFpwStartS x)).1 ++ [vsLd (vsEqwS x (vsFpwStartS x)).2.1 437 x]) next kret →
      (∀ x ∈ l, LoadHolds rd (σ (.n 437)) x (eqAt [a0, a1, a2, a3] x)) ∧ next
  | [], _, h => ⟨fun _ hx ↦ absurd hx (by simp), h⟩
  | x :: l, _, h => by
    rw [List.flatMap_cons, holdsList_append, holdsList_append] at h
    obtain ⟨e, h⟩ := vsEqwS_holds ha h
    simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, vsLd] at h
    obtain ⟨lx, h⟩ := h
    obtain ⟨hl, hn⟩ := fpw_loopS ha l h
    refine ⟨fun y hy ↦ ?_, hn⟩
    rcases List.mem_cons.1 hy with rfl | hy
    · rw [← e]; exact lx
    · exact hl y hy

/-- **`fp_w`**: the bus challenges' equality weights, then `β`'s squeeze. -/
theorem vsFpwS_holds {alphas : List E} (hl : alphas.length = 4)
    (ha : ReadsAt rd (σ (.n 356)) alphas) (h : Stmt.HoldsList C rd σ vsFpwS next kret) :
    ReadsAt rd (σ (.n 437)) (eqKernel alphas) ∧ Stmt.HoldsList C rd σ (vsSqzS 425 614) next kret := by
  match alphas, hl with
  | [a0, a1, a2, a3], _ =>
    unfold vsFpwS at h
    rw [holdsList_append] at h
    simp only [Stmt.HoldsList, Stmt.Holds, vsAlloc, Atom.Holds, true_and] at h
    obtain ⟨hw, hn⟩ := fpw_loopS ha (List.range 16) h
    refine ⟨fun k hk ↦ ?_, hn⟩
    have hk' : k < 16 := by rw [eqKernel_length] at hk; simpa using hk
    have e := eqKernel_getD [a0, a1, a2, a3] k
    rw [List.getD_eq_getElem _ _ hk, ite_eq_left_of_eq_true _ _ (eq_true (by simpa using hk'))] at e
    rw [e]
    exact hw k (List.mem_range.2 hk')

/-! ## The bus's GKR and the tables -/

/-- **The first two calls.** -/
theorem vsCalls1S_holds (h : Stmt.HoldsList C rd σ vsCalls1S next kret) :
    σ (.n 635) = σ (.n 29) * gen ^ 10 ∧
    C "verify_bus_gkr" [σ (.n 622), σ (.n 623), σ (.n 624), σ (.n 625), σ (.n 626), σ (.n 635),
      σ (.n 319), σ (.n 320)] ((List.range 9).map fun k ↦ σ (.n (636 + k))) ∧
    C "verify_tables" [σ (.n 636), σ (.n 637), σ (.n 638), σ (.n 639), σ (.n 640), σ (.n 641),
      σ (.n 0), σ (.n 1), σ (.n 320), σ (.n 319), σ (.n 131), σ (.n 30), σ (.n 4), σ (.n 437),
      σ (.n 633), σ (.n 6), σ (.n 645), σ (.n 642), σ (.n 643), σ (.n 644)]
      ((List.range 10).map fun k ↦ σ (.n (646 + k))) ∧ next := by
  simp only [vsCalls1S, vsConst, vsMul, vsCall, vsAlloc, Stmt.HoldsList,
    Stmt.Holds, List.map_cons, List.map_nil, List.map_map] at h
  obtain ⟨c837, m838, cg, -, ct, h⟩ := h
  simp only [Atom.Holds] at c837 m838
  refine ⟨by rw [m838, c837, word_1024], ?_, ?_, h⟩
  · simpa [Function.comp_def] using cg
  · simpa [Function.comp_def] using ct

theorem vsPushS_noRet : Stmt.noRetList vsPushS = true := by decide +kernel

/-! ## The front -/

/-- The bus challenges' values. -/
def vsAlphaVals (σ : Val) : List E := [σ (.n 376), σ (.n 396), σ (.n 416), σ (.n 436)]

/-- **What the salted `verify_sub`'s front establishes**, up to its call of `verify_tables`. -/
structure VsFrontS (bytecode : List K) (C : CallRel) (rd : Reader) (σ : Val) : Type where
  seed : Digest
  pi : Digest
  hseed : (σ (.n 2), σ (.n 3)) = digestHalves seed
  hpi : (σ (.n 0), σ (.n 1)) = digestHalves pi
  hcap0 : [σ (.n 24), σ (.n 25), σ (.n 26), σ (.n 27), σ (.n 28)] =
    capOf (keccakF1600 (seedInput₂ seed pi seed))
  h7 : σ (.n 7) = σ (.n 2)
  h8 : σ (.n 8) = σ (.n 3)
  h9 : σ (.n 9) = 0
  h9' : σ (.n 10) = 0
  h10 : σ (.n 12) = 0
  h11 : σ (.n 13) = 0
  h12 : σ (.n 14) = 0
  h13 : σ (.n 15) = 0
  hw : ∀ i < 8, WordAtS rd σ i (vsXS i)
  hrw : ∀ i < 6, LoadHolds rd (σ (.n 30)) i (σ (.n (vsXS (i + 1))))
  w8 : WordAtS rd σ 8 334
  w9 : WordAtS rd σ 9 344
  hc537 : IsCanonical128 (σ (.n 334))
  hc547 : IsCanonical128 (σ (.n 344))
  hab8 : (⟨[σ (.n 24), σ (.n 25), σ (.n 26), σ (.n 27), σ (.n 28)], []⟩ : Fs).absorbAll
      (vsWordsS σ) dsObserve =
    ⟨[σ (.n 79), σ (.n 80), σ (.n 81), σ (.n 82), σ (.n 83)],
      [(σ (.n 84), dsObserve), (σ (.n 94), dsObserve), (σ (.n 104), dsObserve),
        (σ (.n 114), dsObserve)]⟩
  habR : (((⟨[σ (.n 79), σ (.n 80), σ (.n 81), σ (.n 82), σ (.n 83)],
      [(σ (.n 84), dsObserve), (σ (.n 94), dsObserve), (σ (.n 104), dsObserve),
        (σ (.n 114), dsObserve)]⟩ : Fs).absorb (σ (.n 334)) dsObserve).absorb (σ (.n 344))
      dsObserve) =
    ⟨[σ (.n 329), σ (.n 330), σ (.n 331), σ (.n 332), σ (.n 333)],
      [(σ (.n 334), dsObserve), (σ (.n 344), dsObserve)]⟩
  halpha : (⟨[σ (.n 329), σ (.n 330), σ (.n 331), σ (.n 332), σ (.n 333)],
      [(σ (.n 334), dsObserve), (σ (.n 344), dsObserve)]⟩ : Fs).squeezeN 4 =
    (vsAlphaVals σ, ⟨[σ (.n 425), σ (.n 426), σ (.n 427), σ (.n 428), σ (.n 429)], []⟩)
  hbeta : (⟨[σ (.n 425), σ (.n 426), σ (.n 427), σ (.n 428), σ (.n 429)], []⟩ : Fs).squeeze =
    (σ (.n 633), ⟨[σ (.n 622), σ (.n 623), σ (.n 624), σ (.n 625), σ (.n 626)], []⟩)
  halphaR : ReadsAt rd (σ (.n 356)) (vsAlphaVals σ)
  hfpw : ReadsAt rd (σ (.n 437)) (eqKernel (vsAlphaVals σ))
  lir : ℕ
  logMem : ℕ
  hl1 : 1 ≤ lir
  hl4 : lir ≤ 4
  e112 : σ (.n 114) = eOfNat lir
  e124 : σ (.n 126) = gen ^ (lir - 1)
  hlm1 : 2 ≤ logMem
  hm30 : logMem ≤ 30
  e29 : σ (.n 31) = eOfNat logMem
  e130 : σ (.n 132) = gen ^ logMem
  rowsN : List ℕ
  hrowsL : rowsN.length = 6
  hrows : ReadsAt rd (σ (.n 30)) (rowsN.map eOfNat)
  hdims : ReadsAt rd (σ (.n 131)) (gen ^ logMem :: (Tables.tableHeightsOf rowsN).map (gen ^ ·))
  hh31 : ∀ h ∈ Tables.tableHeightsOf rowsN, h < 31
  hkb : ReadsAt rd (σ (.n 149)) (1 :: gen ^ logMem :: (Tables.tableHeightsOf rowsN).map (gen ^ ·))
  hkbv : ∀ s < 8, σ (.n (150 + s)) = gen ^ (([0, logMem] ++ Tables.tableHeightsOf rowsN).getD s 0)
  e522 : σ (.n 319) = gen ^ log2Ceil (pushTotal logMem (Tables.tableHeightsOf rowsN))
  hdep : log2Ceil (pushTotal logMem (Tables.tableHeightsOf rowsN)) < 33
  xsG : List E
  r : E × List E × List E
  capG : List E
  hxsG : ReadsAt rd (σ (.n 29) * gen ^ 10) xsG
  hrunG : RunsTo (Tables.gkrPhase (log2Ceil (pushTotal logMem (Tables.tableHeightsOf rowsN))))
    ⟨[σ (.n 622), σ (.n 623), σ (.n 624), σ (.n 625), σ (.n 626)], []⟩ xsG r ⟨capG, []⟩
  hptL : r.2.1.length = log2Ceil (pushTotal logMem (Tables.tableHeightsOf rowsN))
  hvL : r.2.2.length = 3
  hzeta : ReadsAt rd (σ (.n 320)) r.2.1
  hretG : [σ (.n 636), σ (.n 637), σ (.n 638), σ (.n 639), σ (.n 640), σ (.n 641), σ (.n 642),
    σ (.n 643), σ (.n 644)] = capG ++ [σ (.n 29) * gen ^ 10 * gen ^ xsG.length] ++ r.2.2
  xsT : List E
  capT : List E
  bus : BusResult
  claims : List ColumnClaim
  hxsT : ReadsAt rd (σ (.n 641)) xsT
  hrunT : ∀ ev, Tables.BytecodeAt ev bytecode
      (r.2.1.take (Tables.layoutOf bytecode logMem rowsN).logBytecode ++ vsAlphaVals σ) (σ (.n 653)) →
    RunsTo (Tables.tablesSeg ev (Tables.layoutOf bytecode logMem rowsN) pi (vsAlphaVals σ) (σ (.n 633))
      r.2.1 r.2.2) ⟨[σ (.n 636), σ (.n 637), σ (.n 638), σ (.n 639), σ (.n 640)], []⟩ xsT
      (bus, claims) ⟨capT, []⟩
  hclaimsL : claims.length = Tables.nClaims
  hpool : ReadsAt rd (σ (.n 6)) ((claims.take Tables.nBusClaims).map (·.value))
  hcew : ReadsAt rd (σ (.n 655))
    (((claims.drop Tables.nBusClaims).take Tables.nColEvals).map (·.value))
  hpoolPI : ReadsAt rd (σ (.n 6) * gen ^ Tables.nPooled) ((claims.drop Tables.nPooled).map (·.value))
  hctx : Tables.TCtx rd (Tables.layoutOf bytecode logMem rowsN) bus claims
    [σ (.n 320), σ (.n 645), σ (.n 654), σ (.n 319), σ (.n 652)]
  hcapT : [σ (.n 646), σ (.n 647), σ (.n 648), σ (.n 649), σ (.n 650)] = capT
  e854 : σ (.n 651) = σ (.n 641) * gen ^ xsT.length

/-- The memory's log-size (`hm30` weakened). -/
theorem VsFrontS.hm32 {bytecode : List K} {C : CallRel} {rd : Reader} {σ : Val}
    (F : VsFrontS bytecode C rd σ) : F.logMem ≤ 32 := by have := F.hm30; omega

/-- The tables' heights below `33` (`hh31` weakened). -/
theorem VsFrontS.hh33 {bytecode : List K} {C : CallRel} {rd : Reader} {σ : Val}
    (F : VsFrontS bytecode C rd σ) : ∀ h ∈ Tables.tableHeightsOf F.rowsN, h < 33 :=
  fun h hh ↦ by have := F.hh31 h hh; omega

/-- The rows certified by a `verify_tables` call, at any point its precondition admits. -/
theorem tables_heightsS {bytecode : List K} {rd : Reader} {pi : Digest} {logMem : ℕ}
    {alphas point values : List E} {σ : Val}
    (hT : Tables.TablesOut bytecode pi logMem alphas point values rd
      [σ (.n 636), σ (.n 637), σ (.n 638), σ (.n 639), σ (.n 640), σ (.n 641), σ (.n 0), σ (.n 1),
        σ (.n 320), σ (.n 319), σ (.n 131), σ (.n 30), σ (.n 4), σ (.n 437), σ (.n 633), σ (.n 6),
        σ (.n 645), σ (.n 642), σ (.n 643), σ (.n 644)]
      [σ (.n 646), σ (.n 647), σ (.n 648), σ (.n 649), σ (.n 650), σ (.n 651), σ (.n 652),
        σ (.n 653), σ (.n 654), σ (.n 655)]) :
    ∃ rowsN : List ℕ, rowsN.length = 6 ∧
      ReadsAt rd (σ (.n 131)) (gen ^ logMem :: (Tables.tableHeightsOf rowsN).map (gen ^ ·)) ∧
      ∀ h ∈ Tables.tableHeightsOf rowsN, h < 31 := by
  obtain ⟨-, -, rowsN, -, -, hl, -, hd, hh, -⟩ := hT
  exact ⟨rowsN, hl, hd, hh⟩

/-- **The salted `verify_sub`'s front**, up to its call of `verify_tables`. -/
theorem vs_frontS {κ : ℕ} (hκ : κ ≤ 32) (hκ6 : 6 ≤ κ) (L : MemoryImage κ) {C : CallRel}
    (hC : CallRel.Le C (SaltedGuest.coreProgram.Rel L.read)) (bytecode : List K)
    (hgkr : Tables.verify_bus_gkr_SpecC L.read C) (htab : Tables.verify_tables_SpecC bytecode L.read C)
    {σ : Val} {next : Prop} {kret : List E → Prop}
    (hexp : ExpTables L.read (σ (.n 4)))
    (h : Stmt.HoldsList C L.read σ (vsHeadS ++ vsReadsS ++ vsSizesS ++ vsPushS ++
      vsRootsS ++ vsAlphasS ++ vsFpwS ++ vsCalls1S) next kret) :
    Nonempty (VsFrontS bytecode C L.read σ) ∧ next := by
  simp only [holdsList_append] at h
  obtain ⟨h7, h8, h9, h9', h10, h11, h12, h13, hk, h⟩ := vsHeadT_holdsS h
  obtain ⟨seed, pi, hseed, hpi, hcap0⟩ := vs_seedS hk h7 h8 h9 h9' h10 h11 h12 h13
  obtain ⟨hw, hrw, hk50, h⟩ := vsReadsT_holdsS h
  obtain ⟨lir, logMem, hl1, hl4, e112, e124, hlm1, hm30, e29, e130, ds, hdsL, hdims0, hkb0, hkbv0,
    h⟩ := vsSizesS_holds hκ L hC h
  obtain ⟨hP, h⟩ := (holdsList_noRet vsPushS vsPushS_noRet _ _).1 h
  obtain ⟨hk649, w8, w9, ca1, ca2, h⟩ := vsRootsT_holdsS h
  obtain ⟨halpha, halphaR, h⟩ := vsAlphasT_holdsS h10 h11 h12 h13 w8 w9 h
  obtain ⟨hfpw, h⟩ := vsFpwS_holds (alphas := vsAlphaVals σ) rfl halphaR h
  obtain ⟨hbeta, h⟩ := vsSqzT_holdsS h10 h11 h12 h13 h
  obtain ⟨e838, cg, ct, hn⟩ := vsCalls1S_holds h
  have hc537 := ((assert_canonical_holds L.read _ _).1
    (toD_le hC (by decide +kernel) (by decide +kernel) ca1)).1
  have hc547 := ((assert_canonical_holds L.read _ _).1
    (toD_le hC (by decide +kernel) (by decide +kernel) ca2)).1
  have ct' : C "verify_tables" [σ (.n 636), σ (.n 637), σ (.n 638), σ (.n 639), σ (.n 640),
      σ (.n 641), σ (.n 0), σ (.n 1), σ (.n 320), σ (.n 319), σ (.n 131), σ (.n 30), σ (.n 4),
      σ (.n 437), σ (.n 633), σ (.n 6), σ (.n 645), σ (.n 642), σ (.n 643), σ (.n 644)]
      [σ (.n 646), σ (.n 647), σ (.n 648), σ (.n 649), σ (.n 650), σ (.n 651), σ (.n 652),
        σ (.n 653), σ (.n 654), σ (.n 655)] := ct
  have hTA : ∀ point : List E, ReadsAt L.read (σ (.n 320)) point →
      σ (.n 319) = gen ^ point.length → point.length < 33 →
      Tables.TablesOut bytecode pi logMem (vsAlphaVals σ) point [σ (.n 642), σ (.n 643), σ (.n 644)]
        L.read _ _ := fun point hp hg hl ↦ htab pi logMem (vsAlphaVals σ) point _ _ _
      (by
        simp only [Tables.TablesPre]
        exact ⟨hpi, hp, hg, hl, by omega, by omega, ⟨ds, hdsL, hdims0⟩, expTablesAt_of hexp, rfl,
          hfpw, trivial⟩) ct'
  -- the push total, once the heights are certified
  have hpush : ∀ rowsN : List ℕ, rowsN.length = 6 →
      ReadsAt L.read (σ (.n 131)) (gen ^ logMem :: (Tables.tableHeightsOf rowsN).map (gen ^ ·)) →
      (∀ h ∈ Tables.tableHeightsOf rowsN, h < 31) →
      ds = (Tables.tableHeightsOf rowsN).map (gen ^ ·) ∧
      σ (.n 319) = gen ^ log2Ceil (pushTotal logMem (Tables.tableHeightsOf rowsN)) ∧
        log2Ceil (pushTotal logMem (Tables.tableHeightsOf rowsN)) < 34 := by
    intro rowsN hrl hd hh
    have eds : ds = (Tables.tableHeightsOf rowsN).map (gen ^ ·) := by
      have := readsAt_ext (by simp [hdsL, tableHeights_length rowsN hrl]) hdims0 hd
      simpa using this
    subst eds
    have hh33 : ∀ x ∈ Tables.tableHeightsOf rowsN, x < 33 := fun x hx ↦ by have := hh x hx; omega
    have hm32 : logMem ≤ 32 := by omega
    obtain ⟨e, b, -⟩ := vsPushS_holds hκ hκ6 L hC hexp hh33 hm32
      (fun s hs ↦ by rw [hkbv0 s hs, kbase_getD (tableHeights_length rowsN hrl) hs]) hP
    exact ⟨rfl, e, b⟩
  have hpos : ∀ rowsN : List ℕ, 0 < log2Ceil (pushTotal logMem (Tables.tableHeightsOf rowsN)) :=
    fun rowsN ↦ lt_log2Ceil_iff.2 (lt_of_lt_of_le (by
      have := Nat.one_lt_two_pow_iff.2 (show logMem ≠ 0 by omega)
      simpa using this) (pushTotal_ge logMem _))
  have hne : σ (.n 319) ≠ 1 := by
    intro h1
    obtain ⟨rowsN, hrl, hd, hh⟩ := tables_heightsS (hTA [] (fun k hk ↦ absurd hk (by simp))
      (by rw [h1, List.length_nil, pow_zero]) (by simp))
    obtain ⟨-, e, b⟩ := hpush rowsN hrl hd hh
    rw [h1, ← pow_zero gen] at e
    have := gen_pow_inj (by norm_num) (by omega) e
    have := hpos rowsN
    omega
  obtain ⟨depth, xsG, r, capG, hgmu, hdlt, hxsG, hrunG, hptL, hvL, hzeta, hretG⟩ :=
    hgkr _ _ (by simpa using hne) cg
  have hretG' : [σ (.n 636), σ (.n 637), σ (.n 638), σ (.n 639), σ (.n 640), σ (.n 641)] ++
      [σ (.n 642), σ (.n 643), σ (.n 644)] = (capG ++ [σ (.n 635) * gen ^ xsG.length]) ++ r.2.2 :=
    hretG
  obtain ⟨hret1, hvals⟩ := List.append_inj' hretG' (by rw [hvL]; rfl)
  rw [show [σ (.n 636), σ (.n 637), σ (.n 638), σ (.n 639), σ (.n 640), σ (.n 641)] =
    [σ (.n 636), σ (.n 637), σ (.n 638), σ (.n 639), σ (.n 640)] ++ [σ (.n 641)] from rfl] at hret1
  obtain ⟨hcapG, h844⟩ := List.append_inj' hret1 rfl
  simp only [List.cons.injEq, and_true] at h844
  have hT := hTA r.2.1 hzeta (by rw [hptL]; exact hgmu) (by rw [hptL]; exact hdlt)
  obtain ⟨xsT, capT, rowsN, bus, claims, hrl, hrows, hdims, hh, hxsT, hrunT, hcl, hpool, hcew,
    hpoolPI, hctx, hcapT, e854⟩ := hT
  obtain ⟨eds, e522, hlt⟩ := hpush rowsN hrl hdims hh
  have edep : depth = log2Ceil (pushTotal logMem (Tables.tableHeightsOf rowsN)) :=
    gen_pow_inj (by omega) (by omega) (hgmu.symm.trans e522)
  have hkbv : ∀ s < 8, σ (.n (150 + s)) =
      gen ^ (([0, logMem] ++ Tables.tableHeightsOf rowsN).getD s 0) := fun s hs ↦ by
    rw [hkbv0 s hs, eds, kbase_getD (tableHeights_length rowsN hrl) hs]
  rw [eds] at hkb0
  rw [edep] at hrunG hptL hdlt
  refine ⟨⟨VsFrontS.mk
    (seed := seed) (pi := pi) (hseed := hseed) (hpi := hpi) (hcap0 := hcap0) (h7 := h7)
    (h8 := h8) (h9 := h9) (h9' := h9') (h10 := h10)
    (h11 := h11) (h12 := h12) (h13 := h13) (hw := hw) (hrw := hrw) (w8 := w8) (w9 := w9)
    (hc537 := hc537)
    (hc547 := hc547) (hab8 := vs_absorb8S hw hk50) (habR := vs_absorbRootS hw hk649)
    (halpha := halpha) (hbeta := hbeta) (halphaR := halphaR) (hfpw := hfpw) (lir := lir)
    (logMem := logMem) (hl1 := hl1) (hl4 := hl4) (e112 := e112) (e124 := e124) (hlm1 := hlm1)
    (hm30 := hm30) (e29 := e29) (e130 := e130) (rowsN := rowsN) (hrowsL := hrl) (hrows := hrows)
    (hdims := hdims) (hh31 := hh) (hkb := hkb0) (hkbv := hkbv) (e522 := e522) (hdep := hdlt)
    (xsG := xsG) (r := r) (capG := capG) (hxsG := (by rw [← e838]; exact hxsG)) (hrunG := ?_)
    (hptL := hptL) (hvL := hvL) (hzeta := hzeta)
    (hretG := (by rw [← e838]; exact hretG')) (xsT := xsT) (capT := capT)
    (bus := bus) (claims := claims) (hxsT := hxsT) (hrunT := ?_) (hclaimsL := hcl)
    (hpool := hpool) (hcew := hcew) (hpoolPI := hpoolPI) (hctx := hctx) (hcapT := hcapT)
    (e854 := e854)⟩, hn⟩
  · exact hrunG
  · rw [← hvals]; exact hrunT

end
end LeanVM.SaltedGuest.B1.VerifySub
