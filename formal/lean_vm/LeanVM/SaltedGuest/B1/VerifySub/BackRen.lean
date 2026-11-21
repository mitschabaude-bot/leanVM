/-
  LeanVM.SaltedGuest.B1.VerifySub.BackRen

  The salted `verify_sub`'s ring map, `c_table` and tail: the deployed ones renamed.
-/

module

public import LeanVM.SaltedGuest.B1.VerifySub.Template
public import LeanVM.Guest.B1.VerifySub.Tail
public import LeanVM.Guest.B1.VerifySub.Ctab
public import LeanVM.Guest.Renumber

/-!
# The salted ring map, `c_table` and tail, by renaming

The salted `verify_sub`'s values are the deployed ones moved by `vsR` (below `7` kept, then by `4`,
`10`, `27` and `39` in four ranges). Its ring map (`vsMapsS`), `c_table` (`vsCtabS`) and tail
(`vsTailS`) are the deployed blocks renamed by `vsR` (`vsMapsS_eq`, `vsCtabS_eq`, `vsTailS_eq`,
by the kernel's evaluation of `stmtsEqb`), so the deployed `vsMapsT_holds`, `vsCtabT_holds`,
`vsTailT_holds` hold at `σ ∘ vsR` (`Stmt.holdsList_rename`): `vsMapsS_holds`, `vsCtabS_holds`,
`vsTailS_holds`, stated at the salted values.
-/

namespace LeanVM.SaltedGuest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Guest.B1 LeanVM.Guest.B1.VerifySub
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-- The salted `verify_sub`'s value of the deployed one's value `k`. -/
def vsRi (k : ℕ) : ℕ :=
  if k < 7 then k else if k < 135 then k + 4 else if k < 646 then k + 10
  else if k < 1680 then k + 27 else k + 39

/-- The salted `verify_sub`'s value of a deployed one's value. -/
def vsR (v : V) : V := ⟨v.path, v.tag, vsRi v.idx⟩

set_option maxRecDepth 100000 in
theorem vsMapsS_eq : vsMapsS = Stmt.renameList vsR vsMapsT := stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem vsCtabS_eq : vsCtabS = Stmt.renameList vsR vsCtabT := stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem vsTailS_eq : vsTailS = Stmt.renameList vsR vsTailT := stmtsEqb_sound (by decide +kernel)

variable {C : CallRel} {rd : Reader} {σ : Val} {next : Prop} {kret : List E → Prop}

/-- **The salted ring map's challenges.** -/
theorem vsMapsS_holds (h12 : σ (.n 12) = 0) (h13 : σ (.n 13) = 0) (h14 : σ (.n 14) = 0)
    (h15 : σ (.n 15) = 0) (h : Stmt.HoldsList C rd σ vsMapsS next kret) :
    (⟨[σ (.n 686), σ (.n 687), σ (.n 688), σ (.n 689), σ (.n 690)], []⟩ : Fs).squeezeN 5 =
      ([σ (.n 712), σ (.n 732), σ (.n 752), σ (.n 772), σ (.n 792)],
        ⟨[σ (.n 781), σ (.n 782), σ (.n 783), σ (.n 784), σ (.n 785)], []⟩) ∧
      ReadsAt rd (σ (.n 691))
        [σ (.n 685), σ (.n 712), σ (.n 732), σ (.n 752), σ (.n 772), σ (.n 792)] ∧ next := by
  rw [vsMapsS_eq, Stmt.holdsList_rename] at h
  exact vsMapsT_holds (σ := σ ∘ vsR) h12 h13 h14 h15 h

/-- **The salted `c_table`**, then `ring_switch_target`. -/
theorem vsCtabS_holds {chs : List E} (hl : chs.length = 6) (hc : ReadsAt rd (σ (.n 691)) chs)
    (h : Stmt.HoldsList C rd σ vsCtabS next kret) :
    ReadsAt rd (σ (.n 692)) (ringCoefficients chs) ∧
      C "ring_switch_target" [σ (.n 675), σ (.n 691)] [σ (.n 1118)] ∧ next := by
  rw [vsCtabS_eq, Stmt.holdsList_rename] at h
  exact vsCtabT_holds (σ := σ ∘ vsR) hl hc h

/-- **The salted tail**: the placement, the stack's log, the dispatch, the terminal, the deferred
claim's words. -/
theorem vsTailS_holds (h : Stmt.HoldsList C rd σ vsTailS next kret) :
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
  rw [vsTailS_eq, Stmt.holdsList_rename] at h
  exact vsTailT_holds (σ := σ ∘ vsR) h

end
end LeanVM.SaltedGuest.B1.VerifySub
