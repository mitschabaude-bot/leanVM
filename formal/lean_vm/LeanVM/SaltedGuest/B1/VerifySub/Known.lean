/-
  LeanVM.SaltedGuest.B1.VerifySub.Known

  `VsKnown`: the salted `verify_sub`'s `kappa_base` in range at its call of
  `check_opening_terminal`.
-/

module

public import LeanVM.SaltedGuest.B1.VerifySub.FrontAll
public import LeanVM.SaltedGuest.Sound
public import LeanVM.Guest.B1.VerifySub.Known
public import LeanVM.Guest.B1.Tables.HoldsC

/-!
# `kappa_base`, from the placement and the stack's log

As the deployed `vsKnown_of`: the front (`vs_frontS`) gives `kappa_base = [1, g^logMem, g^h…]`
with the memory's log at most `30` and the heights below `31` certified by `verify_tables`; the
seed's claims, the Keccak reduction, the ring map, `c_table` and the batching have no `ret` and
are skipped; the tail's first `6` statements (`certify_placement`, the stack's log and its range
check, `vsKnown_tailS`) bound the Keccak table's height by `24` (the deployed `kb_bounds` then
gives the bounds). The callees `verify_bus_gkr`, `verify_tables`, `certify_placement` and
`log2_ceil_in_the_exponent__L16_L34` are unchanged: their deployed specifications apply to the
salted calls (`onlyS_le`, `toD_le`).

`vsKnown_proved : VsKnown`.
-/

namespace LeanVM.SaltedGuest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Guest.B1 LeanVM.Guest.B1.VerifySub LeanVM.Protocol.Verifier

@[expose] public section

variable {C : CallRel} {σ : Val} {next : Prop} {kret : List E → Prop}

/-- **The tail of `VsKnown`**: the placement and the stack's log check put every committed
column's log below `31`, so the Keccak table's height is at most `24`. -/
theorem vsKnown_tailS {κ : ℕ} (hκ : κ ≤ 32) (hκ6 : 6 ≤ κ) (L : MemoryImage κ)
    (hC : CallRel.Le C (SaltedGuest.coreProgram.Rel L.read)) (hcp : Tables.certify_placement_Spec L.read)
    (hexp : B1.ExpTables L.read (σ (.n 4)))
    {logMem : ℕ} {hs : List ℕ} (hm : logMem ≤ 32) (hl : hs.length = 6) (hh : ∀ x ∈ hs, x < 33)
    (hkb : ReadsAt L.read (σ (.n 149)) (1 :: gen ^ logMem :: hs.map (gen ^ ·)))
    (h : Stmt.HoldsList C L.read σ (vsTailS.take 6) next kret) :
    hs.getD 5 0 ≤ 24 := by
  simp only [vsTailS, List.cons_append, List.take_succ_cons, List.take_zero, Stmt.HoldsList,
    Stmt.Holds, vsCall, vsConst, vsMul, vsRange, List.map_cons, List.map_nil, Atom.Holds] at h
  obtain ⟨c1, c2, e1685, m1686, e1687, r1686, -⟩ := h
  obtain ⟨hsq, hrk, -⟩ := expTablesAt_of hexp
  have e178 : Tables.rankKeysAt = 178 := rfl
  rw [e178] at hrk
  obtain ⟨off, hr, hP⟩ := hcp logMem hs _ _ _ hm hl hh hkb hsq hrk
    (toD_le hC (by decide +kernel) (by decide +kernel) c1)
  simp only [List.cons.injEq, and_true] at hr
  obtain ⟨h1674, -⟩ := hr
  have hST0 := kn_stackTotal_lt (Tables.columnKappas_length logMem Tables.guestLogBytecode hs)
    (kn_columnKappas_le hh hm)
  have hr2 := (log2_holds.2 hκ hκ6 L _ _ hexp _).1
    (toD_le hC (by decide +kernel) (by decide +kernel) c2)
  rw [h1674, meaningLog2CeilExp_pow (by norm_num) hST0] at hr2
  simp only [List.cons.injEq, and_true] at hr2
  obtain ⟨hlt34, hr2⟩ := hr2
  obtain ⟨e, he, h1686⟩ := rc_pow hκ L (a := 10) (by norm_num)
    (by rw [e1687, show (1024 : ℕ) = 2 ^ 10 from rfl, word_pow2 (by norm_num)]) r1686
  have hm32 : max 16 (log2Ceil (Tables.stackTotal (columnKappas logMem Tables.guestLogBytecode hs)))
      = e + 20 := by
    have := congrArg (· * gen ^ 20) (m1686.symm.trans h1686)
    simp only [hr2, e1685, mul_assoc, kn_word_ginv20_mul, mul_one, ← pow_add] at this
    exact gen_pow_inj (by omega) (by omega) this
  have h30 : log2Ceil (Tables.stackTotal (columnKappas logMem Tables.guestLogBytecode hs)) ≤ 30 := by
    omega
  have hK := Tables.hypKappa_holds _ (Tables.columnKappas_length _ _ _) h30
  have hck := Tables.committedKappas_columnKappas logMem hs hl
  have k5 := hK 5 (by decide)
  rw [hck, List.getD_eq_getElem _ _ (by simp only [List.length_map, List.length_range]; decide),
    List.getElem_map, List.getElem_range,
    show Tables.colKappaSrc 5 = 7 from rfl, show Tables.colKappaAdj 5 = 6 from rfl] at k5
  clear * - k5 hl
  obtain ⟨h0, h1, h2, h3, h4, h5, rfl⟩ : ∃ h0 h1 h2 h3 h4 h5, hs = [h0, h1, h2, h3, h4, h5] := by
    match hs, hl with
    | [h0, h1, h2, h3, h4, h5], _ => exact ⟨_, _, _, _, _, _, rfl⟩
  simp only [List.getD_cons_succ, List.getD_cons_zero] at k5 ⊢
  omega

/-- The sections before the tail. -/
def vsPreS : List Stmt :=
  vsHeadS ++ vsReadsS ++ vsSizesS ++ vsPushS ++ vsRootsS ++ vsAlphasS ++ vsFpwS ++
    vsCalls1S ++ vsSeedClaimsS ++ vsCalls2S ++ vsMapsS ++ vsCtabS ++ vsLamS

theorem vsPreS_length : vsPreS.length = 1628 := by decide +kernel

theorem vsTS_take : vsTS.take 1635 = vsPreS ++ vsTailS.take 7 := by
  rw [show vsTS = vsPreS ++ vsTailS from rfl, List.take_append, List.take_of_length_le
    (by rw [vsPreS_length]; omega), vsPreS_length]

theorem noRet_midS :
    Stmt.noRetList (vsSeedClaimsS ++ vsCalls2S ++ vsMapsS ++ vsCtabS ++ vsLamS) = true := by
  decide +kernel

theorem vsTailS_take7 : vsTailS.take 7 = vsTailS.take 6 ++ (vsTailS.take 7).drop 6 := by
  have := List.take_append_drop 6 (vsTailS.take 7)
  rw [List.take_take, show min 6 7 = 6 from rfl] at this
  exact this.symm

end
end LeanVM.SaltedGuest.B1.VerifySub

namespace LeanVM.SaltedGuest.End

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Guest.B1 LeanVM.Guest.B1.VerifySub LeanVM.SaltedGuest.B1 LeanVM.SaltedGuest.B1.VerifySub
open LeanVM.Protocol.Verifier

@[expose] public section

/-- **`verify_sub`'s `kappa_base`** below `vsKbBound`. -/
theorem vsKnown_proved : VsKnown := by
  intro κ L _ h32 σ hexp h
  have hκ : κ ≤ 32 := h32.trans (by decide)
  have hκ6 : 6 ≤ κ := by
    obtain ⟨hsq, -, -⟩ := expTablesAt_of hexp
    have hm := mem_size hκ L (n := 34) (by norm_num) fun j hj ↦
      ⟨_, hsq j (by simp [Tables.gSquaresList]; omega)⟩
    by_contra hlt
    have : 2 ^ κ ≤ 2 ^ 5 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hle : CallRel.Le (SaltedGuest.coreProgram.Rel L.read) (SaltedGuest.coreProgram.Rel L.read) :=
    fun _ _ _ h ↦ h
  have hgkr : Tables.verify_bus_gkr_SpecC L.read (SaltedGuest.coreProgram.Rel L.read) :=
    fun args rets hne hc ↦ Tables.verify_bus_gkr_holdsC hκ L
      (onlyS_le (f := "verify_bus_gkr") (by decide +kernel) (by decide +kernel)) args rets hne
      ⟨rfl, hc⟩
  have htab : Tables.verify_tables_SpecC (List.replicate (2 ^ 23) 0) L.read
      (SaltedGuest.coreProgram.Rel L.read) :=
    fun pi logMem alphas point values args rets hpre hc ↦ Tables.verify_tables_holdsC hκ L _
      List.length_replicate (onlyS_le (f := "verify_tables") (by decide +kernel) (by decide +kernel))
      pi logMem alphas point values args rets hpre ⟨rfl, hc⟩
  have hcp := Tables.certify_placement_holds hκ L
  rw [show (coreOf 19).body = vsTS from vsS_body, vsTS_take, vsPreS] at h
  rw [holdsList_append, holdsList_append, holdsList_append, holdsList_append, holdsList_append,
    holdsList_append] at h
  obtain ⟨⟨F⟩, h⟩ := vs_frontS hκ hκ6 L hle (List.replicate (2 ^ 23) 0) hgkr htab hexp h
  rw [← holdsList_append, ← holdsList_append, ← holdsList_append, ← holdsList_append] at h
  have h' := ((holdsList_noRet _ noRet_midS _ _).1 h).2
  rw [vsTailS_take7, holdsList_append] at h'
  have hsL := tableHeights_length F.rowsN F.hrowsL
  have h5 := vsKnown_tailS hκ hκ6 L hle hcp hexp F.hm32 hsL F.hh33 F.hkb h'
  exact kb_bounds hsL F.hh31 F.hm30 h5 F.hkb

end
end LeanVM.SaltedGuest.End
