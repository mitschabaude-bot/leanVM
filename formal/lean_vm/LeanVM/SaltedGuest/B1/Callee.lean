/-
  LeanVM.SaltedGuest.B1.Callee

  A salted call of an unchanged function is the deployed function's call.
-/

module

public import LeanVM.SaltedGuest.Same
public import LeanVM.Guest.CoreLemmas

/-!
# Unchanged callees

`toD`: a call of a function of the closed set whose name the renaming keeps
(`Same.inS f`, `Same.rho f = f`, both decided by the kernel at a literal name) holds in the
deployed core IR when it holds in the salted one (`Same.rel_same'`); `toD_le`: so does every call
of a relation below the salted core IR's. `onlyS f rd`, the salted core IR's calls of `f` alone,
lies below the deployed core IR's (`onlyS_le`): a deployed statement about the calls of a relation
below the deployed core IR (`…_SpecC`) applies to it.
-/

namespace LeanVM.SaltedGuest.B1

open LeanVM.Parameters LeanVM.Guest LeanVM.Guest.Core

@[expose] public section

theorem toD {rd : Reader} {f : String} {args rets : List E} (hf : Same.inS f = true)
    (hr : Same.rho f = f) (h : SaltedGuest.coreProgram.Rel rd f args rets) :
    Guest.coreProgram.Rel rd f args rets :=
  (Same.rel_same' rd hf hr args rets).mp h

theorem toD_le {rd : Reader} {C : CallRel} (hC : CallRel.Le C (SaltedGuest.coreProgram.Rel rd))
    {f : String} {args rets : List E} (hf : Same.inS f = true) (hr : Same.rho f = f)
    (h : C f args rets) : Guest.coreProgram.Rel rd f args rets :=
  toD hf hr (hC _ _ _ h)

/-- The salted core IR's calls of `f` alone. -/
def onlyS (f : String) (rd : Reader) : CallRel :=
  fun g args rets ↦ g = f ∧ SaltedGuest.coreProgram.Rel rd g args rets

theorem onlyS_le {f : String} {rd : Reader} (hf : Same.inS f = true) (hr : Same.rho f = f) :
    CallRel.Le (onlyS f rd) (Guest.coreProgram.Rel rd) := by
  rintro g args rets ⟨rfl, h⟩
  exact toD hf hr h

end
end LeanVM.SaltedGuest.B1
