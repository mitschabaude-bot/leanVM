/-
  LeanVM.SaltedGuest.Same.Defs

  What a salted function being a deployed one up to the renaming of its callees is.
-/

module

public import LeanVM.SaltedGuest.Same.Pairs
public import LeanVM.SaltedGuest.CoreNames
public import LeanVM.Guest.CoreNames
public import LeanVM.SaltedGuest.KernelRfl

/-!
# The pair check

`PairOk (f, j, j')`: function `j` of the salted core IR has the name `f`, function `j'` of the
deployed core IR the name `rho f` (names are distinct in both, `coreProgram_find_getElem`), they
have the same parameters, the deployed body is the salted one with its callees renamed by `rho`,
and every callee of the salted body is in the closed set (`inS`). The generated checks
(`Same/Check*.lean`) prove it of each pair: the functions and the body by the kernel's `rfl`
(`kernel_rfl`), the rest by `decide +kernel`.

`agreesOn_of`: if every pair of the closed set passes, the salted core IR agrees with the deployed
one on the closed set up to `rho` (`Core.AgreesOn`).
-/

namespace LeanVM.SaltedGuest.Same

open LeanVM.Guest LeanVM.Guest.Core

@[expose] public section

/-- **One pair** (salted name, salted index, deployed index) of the closed set. -/
def PairOk (p : String × Nat × Nat) : Prop :=
  ∃ g g', SaltedGuest.coreProgram[p.2.1]? = some g ∧ Guest.coreProgram[p.2.2]? = some g' ∧
    g.name = p.1 ∧ g'.name = rho p.1 ∧ g'.params = g.params ∧
    g'.body = Stmt.mapCallsList rho g.body ∧ Stmt.callsAllList inS g.body = true

/-- **The salted core IR agrees with the deployed one on the closed set**, up to `rho`, if every
pair passes. -/
theorem agreesOn_of (h : ∀ p ∈ closed, PairOk p) :
    AgreesOn SaltedGuest.coreProgram Guest.coreProgram rho inS := by
  intro f hf
  obtain ⟨p, hp, rfl⟩ : ∃ p ∈ closed, p.1 = f := by
    simpa only [inS, List.contains_iff_mem, List.mem_map] using hf
  obtain ⟨g, g', hg, hg', h1, h2, h3, h4, h5⟩ := h p hp
  obtain ⟨hj, rfl⟩ := List.getElem?_eq_some_iff.mp hg
  obtain ⟨hj', rfl⟩ := List.getElem?_eq_some_iff.mp hg'
  refine ⟨_, _, ?_, ?_, h3, h4, h5⟩
  · rw [← h1]; exact SaltedGuest.coreProgram_find_getElem hj
  · rw [← h2]; exact Guest.coreProgram_find_getElem hj'

end
end LeanVM.SaltedGuest.Same
