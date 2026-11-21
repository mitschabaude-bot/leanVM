/-
  LeanVM.SaltedGuest.B1.VerifySub.BackS

  The salted `verify_sub` after its calls, assembled: the ring map, `c_table`, the batching and the
  tail.
-/

module

public import LeanVM.SaltedGuest.B1.VerifySub.LamS
public import LeanVM.Guest.B1.VerifySub.Back

/-!
# The back of the salted `verify_sub`

`vs_backS`: the deployed `vs_back` for the salted body: from the zero cells and the pooled claims,
the statements after the calls give the ring map's challenges and their coefficients
(`vsMapsS_holds`, `vsCtabS_holds`), the batching challenge and the target over the `145` batched
claims (`vsLamS_holds`), and the tail's facts (`vsTailS_holds`).
-/

namespace LeanVM.SaltedGuest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.VerifySub

@[expose] public section

variable {C : CallRel} {rd : Reader} {σ : Val} {kret : List E → Prop}

/-- The salted ring map's five squeezed challenges. -/
def vsChsS (σ : Val) : List E := [σ (.n 712), σ (.n 732), σ (.n 752), σ (.n 772), σ (.n 792)]

/-- **The back of the salted `verify_sub`.** -/
theorem vs_backS (h12 : σ (.n 12) = 0) (h13 : σ (.n 13) = 0) (h14 : σ (.n 14) = 0)
    (h15 : σ (.n 15) = 0) {claims : List ColumnClaim}
    (hcol : claims.map (·.column) = claimColumnsS)
    (hval : ∀ j < nClaimsS, LoadHolds rd (σ (.n (vsClaimAtS j).1)) (vsClaimAtS j).2
      ((claims.map (·.value)).getD j 0))
    (h : Stmt.HoldsList C rd σ (vsMapsS ++ (vsCtabS ++ (vsLamS ++ vsTailS))) False kret) :
    -- the ring map
    (⟨[σ (.n 686), σ (.n 687), σ (.n 688), σ (.n 689), σ (.n 690)], []⟩ : Fs).squeezeN 5 =
      (vsChsS σ, ⟨[σ (.n 781), σ (.n 782), σ (.n 783), σ (.n 784), σ (.n 785)], []⟩) ∧
    ReadsAt rd (σ (.n 691)) (σ (.n 685) :: vsChsS σ) ∧
    ReadsAt rd (σ (.n 692)) (ringCoefficients (σ (.n 685) :: vsChsS σ)) ∧
    C "ring_switch_target" [σ (.n 675), σ (.n 691)] [σ (.n 1118)] ∧
    -- the batching
    (⟨[σ (.n 781), σ (.n 782), σ (.n 783), σ (.n 784), σ (.n 785)], []⟩ : Fs).squeeze =
      (σ (.n 1138), ⟨[σ (.n 1127), σ (.n 1128), σ (.n 1129), σ (.n 1130), σ (.n 1131)], []⟩) ∧
    σ (.n 1718) = σ (.n 1138) ^ 146 ∧
    σ (.n 1720) = dot (powers (σ (.n 1138)) ((notLanes claims).length + 2))
      (σ (.n 1118) :: ((notLanes claims).map (·.value) ++ [σ (.n 684)])) ∧
    -- the tail
    C "certify_placement" [σ (.n 149), σ (.n 4)] [σ (.n 1721), σ (.n 1722)] ∧
    C "log2_ceil_in_the_exponent__L16_L34" [σ (.n 1721), σ (.n 4)] [σ (.n 1723)] ∧
    σ (.n 1725) = σ (.n 1723) * word 14347465658197868555 0 0 ∧
    (LoadHolds rd (σ (.n 1725)) 0 (σ (.n 1728)) ∧ word 1024 0 0 = σ (.n 1725) * σ (.n 1727) ∧
      LoadHolds rd (σ (.n 1727)) 0 (σ (.n 1729))) ∧
    (∃ (j : ℕ) (hj : j < vsOpenNames.length), σ (.n 1725) = ofK (addressOfIndex j) ∧
      C vsOpenNames[j] [σ (.n 126), σ (.n 1127), σ (.n 1128), σ (.n 1129), σ (.n 1130),
        σ (.n 1131), σ (.n 1720), σ (.n 334), σ (.n 344), σ (.n 683)]
        [σ (.n 1730), σ (.n 1731), σ (.n 1732), σ (.n 1733), σ (.n 1734)]) ∧
    C "check_opening_terminal" [σ (.n 4), σ (.n 320), σ (.n 645), σ (.n 654), σ (.n 319),
      σ (.n 652), σ (.n 132), σ (.n 673), σ (.n 149), σ (.n 1138), σ (.n 1722), σ (.n 674),
      σ (.n 692), σ (.n 1731), σ (.n 1732), σ (.n 1733), σ (.n 1734), σ (.n 1730)] [] ∧
    (∀ k < 19, ∃ v, LoadHolds rd (σ (.n 320)) k v ∧ LoadHolds rd (σ (.n 5)) k v) ∧
    (∀ k < 4, ∃ v, LoadHolds rd (σ (.n 356)) k v ∧ LoadHolds rd (σ (.n 5)) (19 + k) v) ∧
    LoadHolds rd (σ (.n 5)) 23 (σ (.n 653)) ∧ kret [] := by
  rw [holdsList_append, holdsList_append, holdsList_append] at h
  obtain ⟨hm, hmR, h⟩ := vsMapsS_holds h12 h13 h14 h15 h
  obtain ⟨hct, hrst, h⟩ := vsCtabS_holds (chs := σ (.n 685) :: vsChsS σ) rfl hmR h
  obtain ⟨hlam, h1884, h1886, h⟩ := vsLamS_holds h12 h13 h14 h15 hcol hval h
  exact ⟨hm, hmR, hct, hrst, hlam, h1884, h1886, vsTailS_holds h⟩

end
end LeanVM.SaltedGuest.B1.VerifySub
