/-
  LeanVM.SaltedGuest.KernelRfl

  `kernel_rfl`: an equation proved by `rfl`, checked by the kernel alone.
-/

module

public meta import Lean.Elab.Command
public meta import Lean.Meta.Basic

/-!
# Equations the kernel checks by `rfl`

`kernel_rfl x : a = b` adds `theorem x : a = b := Eq.refl a`, which the kernel checks by its
definitional equality, unfolding `a` and `b` as far as it needs to; the elaborator does not compare
them. Two large terms of the same text compare structurally there, where an evaluation of a
Boolean equality (`decide +kernel`) would put every subterm in normal form.
-/

public meta section

namespace LeanVM.SaltedGuest.KernelRfl

open Lean Elab Command

/-- `kernel_rfl x : a = b` adds `theorem x : a = b`, by `rfl`, which the kernel alone checks. -/
syntax (name := kernelRfl) (docComment)? "kernel_rfl " ident " : " term : command

@[command_elab kernelRfl] def elabKernelRfl : CommandElab := fun stx => do
  let name := (← getCurrNamespace) ++ stx[2].getId
  let ty ← liftTermElabM do
    let ty ← Term.elabType stx[4]
    Term.synthesizeSyntheticMVarsNoPostponing
    instantiateMVars ty
  if ty.hasMVar then throwError "kernel_rfl: the equation is not known"
  let some (α, a, _) := ty.eq? | throwError "kernel_rfl: not an equation"
  let u ← liftTermElabM <| Meta.getLevel α
  liftCoreM <| addDecl (.thmDecl (mkTheoremValEx name [] ty (mkApp2 (mkConst ``Eq.refl [u]) α a) []))
  if let some doc := stx[0].getOptional? then
    liftTermElabM <| addDocString name (mkNullNode #[]) ⟨doc⟩

end LeanVM.SaltedGuest.KernelRfl
