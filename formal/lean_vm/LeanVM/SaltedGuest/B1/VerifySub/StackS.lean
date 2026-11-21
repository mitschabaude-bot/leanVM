/-
  LeanVM.SaltedGuest.B1.VerifySub.StackS

  The salted `verify_sub`'s stack: the placement, the stack's log and its size selector.
-/

module

public import LeanVM.SaltedGuest.B1.VerifySub.FrontAll
public import LeanVM.Guest.B1.VerifySub.Stack

/-!
# The salted stack

`vs_stackS`: the deployed `vs_stack` for the salted front (`VsFrontS`), its unchanged callees
(`certify_placement`, `log2_ceil_in_the_exponent__L16_L34`) at the deployed core IR through the
transfer (`toDRel`).
-/

namespace LeanVM.SaltedGuest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.VerifySub

@[expose] public section

/-- A salted call of an unchanged function of the same deployed name. -/
theorem toDRel {rd : Reader} {f : String} (hf : Same.inS f = true) (hr : Same.rho f = f)
    {args rets : List E} (h : SaltedGuest.coreProgram.Rel rd f args rets) :
    Guest.coreProgram.Rel rd f args rets :=
  (Same.rel_same' rd hf hr args rets).mp h

/-- **The salted stack**, as the deployed `vs_stack`: the placement certified, the stack's log `μ ∈ [20, 30]`, the size
selector `g^(μ - 20)` dispatched on, and the committed columns' logs below `31`. -/
theorem vs_stackS {κ : ℕ} (hκ : κ ≤ 32) (hκ6 : 6 ≤ κ) (L : MemoryImage κ) {C : CallRel}
    (hLe : CallRel.Le C (SaltedGuest.coreProgram.Rel L.read)) (hcpS : Tables.certify_placement_Spec L.read)
    {bytecode : List K}
    (hbl : bytecode.length = 2 ^ 23) {σ : Val} (F : VsFrontS bytecode C L.read σ)
    (hexp : ExpTables L.read (σ (.n 4)))
    (hcp : C "certify_placement" [σ (.n 149), σ (.n 4)] [σ (.n 1721), σ (.n 1722)])
    (hl2 : C "log2_ceil_in_the_exponent__L16_L34" [σ (.n 1721), σ (.n 4)] [σ (.n 1723)])
    (e1686 : σ (.n 1725) = σ (.n 1723) * word 14347465658197868555 0 0)
    (r1 : LoadHolds L.read (σ (.n 1725)) 0 (σ (.n 1728)) ∧ word 1024 0 0 = σ (.n 1725) * σ (.n 1727) ∧
      LoadHolds L.read (σ (.n 1727)) 0 (σ (.n 1729))) :
    B1.Whir.minOpenLog ≤ (Tables.layoutOf bytecode F.logMem F.rowsN).stackLog ∧
      (Tables.layoutOf bytecode F.logMem F.rowsN).stackLog ≤ 30 ∧
      σ (.n 1725) = gen ^ ((Tables.layoutOf bytecode F.logMem F.rowsN).stackLog - B1.Whir.minOpenLog) ∧
      Tables.PCtx L.read (columnKappas F.logMem 19 (Tables.tableHeightsOf F.rowsN)) (σ (.n 1722)) ∧
      Tables.KappasBelow (columnKappas F.logMem 19 (Tables.tableHeightsOf F.rowsN)) := by
  have hsL := tableHeights_length _ F.hrowsL
  -- the placement
  obtain ⟨hsq, hrk, -⟩ := expTablesAt_of hexp
  have e178 : Tables.rankKeysAt = 178 := rfl
  rw [e178] at hrk
  obtain ⟨off, hrets, hP⟩ := hcpS F.logMem (Tables.tableHeightsOf F.rowsN) _ _ _ F.hm32 hsL F.hh33
    F.hkb hsq hrk (toDRel (by decide +kernel) (by decide +kernel) (hLe _ _ _ hcp))
  simp only [List.cons.injEq, and_true, Tables.guestLogBytecode] at hrets hP
  obtain ⟨e1682, rfl⟩ := hrets
  -- the stack's log
  have hT := sl_stackTotal_lt F.hm32 hsL F.hh33
  have hr2 := (log2_holds.2 hκ hκ6 L _ _ hexp _).1 (toDRel (by decide +kernel) (by decide +kernel) (hLe _ _ _ hl2))
  rw [e1682, meaningLog2CeilExp_pow (by norm_num) (lt_trans hT (by norm_num))] at hr2
  simp only [List.cons.injEq, and_true] at hr2
  obtain ⟨hm34, hret⟩ := hr2
  rw [← stackLog_eq hbl] at hret hm34
  set μ := (Tables.layoutOf bytecode F.logMem F.rowsN).stackLog with hμ
  -- the size selector
  obtain ⟨e, he, hx⟩ := rc_lt hκ hκ6 L (a := 10) (by omega) r1.1 (by simpa using r1.2.1) r1.2.2
  have hμe : μ = e + 20 := size_sel_eq hm34 (by omega) (by rw [← hret, ← e1686, hx])
  refine ⟨by unfold B1.Whir.minOpenLog; omega, by omega,
    by rw [hx]; congr 1; unfold B1.Whir.minOpenLog; omega, hP, Tables.hypKappa_holds _ hP.1 ?_⟩
  have : max 16 (log2Ceil (Tables.stackTotal (columnKappas F.logMem 19
    (Tables.tableHeightsOf F.rowsN)))) ≤ 30 := by rw [← stackLog_eq hbl]; omega
  omega

end
end LeanVM.SaltedGuest.B1.VerifySub
