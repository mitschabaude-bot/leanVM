/-
  LeanVM.SaltedGuest.Exec

  The salted guest's code fetched at its pcs: the part of `LeanVM.Guest.Exec` about the program,
  for the salted program.
-/

module

public import LeanVM.Guest.Exec
public import LeanVM.SaltedGuest.Bytecode

/-!
# The salted guest's fetches

`LeanVM.Guest.Exec` is generic but for `guest_fetches`, about the deployed program; this is that
theorem for the salted program (`LeanVM.SaltedGuest.guestProgram`). Modules of the salted guest
import this module where the deployed guest's import `LeanVM.Guest.Exec`, and find its
`guest_fetches` first, inside `LeanVM.SaltedGuest`.
-/

namespace LeanVM.SaltedGuest

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Exec

@[expose] public section

/-- The code of a salted guest function is fetched at its pcs. -/
theorem guest_fetches {f : CompiledFunction} (hf : f ∈ Data.functions) :
    Fetches guestProgram f.entryPc f.code := by
  intro j ins hj
  have hw := CompiledFunction.wellChunked_of_mem hf
  obtain ⟨hjl, -⟩ := List.getElem?_eq_some_iff.mp hj
  rw [CompiledFunction.length_code hw] at hjl
  rw [CompiledFunction.getElem?_code hw hjl] at hj
  obtain rfl := Option.some.inj hj
  exact ⟨guest_fetch hf hjl, guest_pc_lt hf hjl⟩

end
end LeanVM.SaltedGuest
