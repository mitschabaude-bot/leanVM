/-
  LeanVM.SaltedGuest.B1.VerifySub.LamS

  The salted `verify_sub`'s batching: the target over the `145` claims the opening batches.
-/

module

public import LeanVM.SaltedGuest.B1.VerifySub.BackRen
public import LeanVM.SaltedGuest.B1.VerifySub.Front
public import LeanVM.Guest.B1.VerifySub.Lam

/-!
# The salted batching

The deployed `Lam` (`vsLamT_holds`) over the salted pool of `170` claims: the deployed `167`
(`Tables.claimColumns`) and the second digest's three on the memory columns (`claimColumnsS`).
After `λ`'s squeeze, `vsLamS` walks the `145` claims the opening batches (all but the `25` output
lanes', `vsKept`), claim `i`'s value read at `vsClaimAtS`, the target accumulating `λ^(i+1)·value`;
then `λ^146` times the output lanes' claim: `vsLamS_holds`, the specification's
`dot (powers λ (n + 2)) (ring target :: values ++ [outputs' value])`.
-/

namespace LeanVM.SaltedGuest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Protocol.KeccakGkr Finset LeanVM.Guest.B1.VerifySub

@[expose] public section

variable {C : CallRel} {rd : Reader} {σ : Val} {next : Prop} {kret : List E → Prop}

/-- The salted pool's claims: the deployed ones and the second digest's three. -/
abbrev nClaimsS : ℕ := 170

/-- The salted pool's columns: the deployed ones, then the second digest's on the memory columns. -/
def claimColumnsS : List ℕ := Tables.claimColumns ++ [memory0, memory1, memory2]

/-! ## The batched claims -/

/-- **The batched claims are the kept ones**: the pool's claims whose column is not an output
lane are `vsKept 0, …, vsKept 144`. -/
theorem kept_eqS : (List.range nClaimsS).filter
    (fun j ↦ claimColumnsS.getD j 0 ∉ keccakOutputColumns) = (List.range 145).map vsKept := by
  decide +kernel

theorem vsKept_ltS {i : ℕ} (hi : i < 145) : vsKept i < nClaimsS := by
  unfold vsKept; show _ < 170; split <;> omega


/-- The batched claims' values: claim `vsKept i`'s, in order. -/
theorem kept_valuesS {claims : List ColumnClaim} (hcol : claims.map (·.column) = claimColumnsS) :
    (claims.filter fun c ↦ c.column ∉ keccakOutputColumns).map (·.value) =
      (List.range 145).map fun i ↦ (claims.map (·.value)).getD (vsKept i) 0 := by
  have hl : claims.length = nClaimsS := by
    rw [← List.length_map (f := (·.column)), hcol]; decide +kernel
  have hc : ∀ j < claims.length, (claims.getD j default).column = claimColumnsS.getD j 0 := by
    intro j hj
    rw [← hcol, List.getD_eq_getElem _ _ hj, List.getD_eq_getElem _ _ (by simpa using hj),
      List.getElem_map]
  rw [filter_eq_map_idx, List.filter_congr (q := fun j ↦ claimColumnsS.getD j 0 ∉
      keccakOutputColumns) fun j hj ↦ by
    rw [hc j (List.mem_range.1 hj)], hl, kept_eqS, List.map_map, List.map_map]
  refine List.map_congr_left fun i hi ↦ ?_
  have hk := vsKept_ltS (List.mem_range.1 hi)
  simp only [Function.comp_apply]
  rw [List.getD_eq_getElem _ _ (by rw [hl]; exact hk), List.getD_eq_getElem _ _ (by simp [hl, hk]),
    List.getElem_map]





/-! ## The walk -/

theorem vsPwS_succ (n : ℕ) : vsPwS (n + 1) = 1142 + 4 * n := by
  simp only [vsPwS, Nat.add_one_ne_zero, ↓reduceIte]; omega

theorem vsTgS_succ (n : ℕ) : vsTgS (n + 1) = 1141 + 4 * n := by
  simp only [vsTgS, Nat.add_one_ne_zero, ↓reduceIte]; omega

/-- The first `n` batched claims: the power `λ^(n+1)`, the target. -/
theorem lam_loopS {lam T : E} {vals : List E} (hlam : σ (.n 1138) = lam) (hT : σ (.n 1118) = T)
    (hval : ∀ j < nClaimsS, LoadHolds rd (σ (.n (vsClaimAtS j).1)) (vsClaimAtS j).2
      (vals.getD j 0)) :
    ∀ n ≤ 145, ∀ {nx : Prop}, Stmt.HoldsList C rd σ ((List.range n).flatMap vsLamStepS) nx kret →
      σ (.n (vsPwS n)) = lam ^ (n + 1) ∧
      σ (.n (vsTgS n)) = T + ∑ i ∈ range n, lam ^ (i + 1) * vals.getD (vsKept i) 0 ∧ nx
  | 0, _, nx, h => ⟨by simp [vsPwS, hlam], by simp [vsTgS, hT], h⟩
  | n + 1, hn, nx, h => by
    rw [List.range_succ, List.flatMap_append, holdsList_append] at h
    obtain ⟨hp, ht, h⟩ := lam_loopS hlam hT hval n (by omega) h
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, vsLamStepS, Stmt.HoldsList,
      Stmt.Holds, Atom.Holds, vsLd, vsMul, vsAdd] at h
    obtain ⟨ld, m1, a1, m2, h⟩ := h
    have hv : σ (.n (1139 + 4 * n)) = vals.getD (vsKept n) 0 :=
      loadHolds_unique ld (hval _ (vsKept_ltS (by omega)))
    refine ⟨?_, ?_, h⟩
    · rw [vsPwS_succ, m2, hp, hlam]; ring
    · rw [vsTgS_succ, a1, ht, m1, hp, hv, Finset.sum_range_succ]; ring

/-- **The batching** (G:3472-3485), after `λ`'s squeeze (`hsq`, the squeeze's facts `SQ`):
`λ^146` at `1718`, and the batched target at `1720`. -/
theorem vsLamS_holds_of {SQ : Prop}
    (hsq : ∀ {nx : Prop}, Stmt.HoldsList C rd σ (vsSqzS 781 1119) nx kret → SQ ∧ nx)
    {claims : List ColumnClaim} (hcol : claims.map (·.column) = claimColumnsS)
    (hval : ∀ j < nClaimsS, LoadHolds rd (σ (.n (vsClaimAtS j).1)) (vsClaimAtS j).2
      ((claims.map (·.value)).getD j 0))
    (h : Stmt.HoldsList C rd σ vsLamS next kret) :
    SQ ∧ σ (.n 1718) = σ (.n 1138) ^ 146 ∧
    σ (.n 1720) = dot (powers (σ (.n 1138))
      ((claims.filter fun c ↦ c.column ∉ keccakOutputColumns).length + 2))
      (σ (.n 1118) :: ((claims.filter fun c ↦ c.column ∉ keccakOutputColumns).map (·.value) ++
        [σ (.n 684)])) ∧ next := by
  unfold vsLamS at h
  rw [holdsList_append, holdsList_append] at h
  obtain ⟨hS, h⟩ := hsq h
  obtain ⟨hp, ht, h⟩ := lam_loopS rfl rfl hval 145 le_rfl h
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, vsMul, vsAdd] at h
  obtain ⟨m, a, h⟩ := h
  have hv := kept_valuesS hcol
  have hfl : (claims.filter fun c ↦ c.column ∉ keccakOutputColumns).length = 145 := by
    rw [← List.length_map (f := (·.value)), hv, List.length_map, List.length_range]
  rw [show vsTgS 145 = 1717 from rfl] at ht
  rw [show vsPwS 145 = 1718 from rfl] at hp
  refine ⟨hS, hp, ?_, h⟩
  rw [hv, hfl, dot_powers_batch, a, m, ht, hp]

/-- **The batching** (G:3472-3485): `λ`'s squeeze, `λ^146` at `1718`, and the batched target at
`1720`. -/
theorem vsLamS_holds (h10 : σ (.n 12) = 0) (h11 : σ (.n 13) = 0) (h12 : σ (.n 14) = 0)
    (h13 : σ (.n 15) = 0) {claims : List ColumnClaim}
    (hcol : claims.map (·.column) = claimColumnsS)
    (hval : ∀ j < nClaimsS, LoadHolds rd (σ (.n (vsClaimAtS j).1)) (vsClaimAtS j).2
      ((claims.map (·.value)).getD j 0))
    (h : Stmt.HoldsList C rd σ vsLamS next kret) :
    (⟨[σ (.n 781), σ (.n 782), σ (.n 783), σ (.n 784), σ (.n 785)], []⟩ : Fs).squeeze =
      (σ (.n 1138), ⟨[σ (.n 1127), σ (.n 1128), σ (.n 1129), σ (.n 1130), σ (.n 1131)], []⟩) ∧
    σ (.n 1718) = σ (.n 1138) ^ 146 ∧
    σ (.n 1720) = dot (powers (σ (.n 1138))
      ((claims.filter fun c ↦ c.column ∉ keccakOutputColumns).length + 2))
      (σ (.n 1118) :: ((claims.filter fun c ↦ c.column ∉ keccakOutputColumns).map (·.value) ++
        [σ (.n 684)])) ∧ next :=
  vsLamS_holds_of (fun hs ↦ vsSqzT_holdsS (capb := 781) (o := 1119) h10 h11 h12 h13 hs) hcol hval h

end
end LeanVM.SaltedGuest.B1.VerifySub
