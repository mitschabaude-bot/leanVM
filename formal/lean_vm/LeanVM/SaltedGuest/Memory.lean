/-
  LeanVM.SaltedGuest.Memory

  The salted guest's jump table in `main`'s frame: the part of `LeanVM.Guest.Memory` about the
  program, for the salted program.
-/

module

public import LeanVM.Guest.Memory
public import LeanVM.SaltedGuest.Data.Bytecode

/-!
# The salted guest's jump table

`LeanVM.Guest.Memory` is generic but for `tableCells` and its facts, read off the deployed
`__jump_tables`; these are they for the salted guest's `__jump_tables`. Modules of the salted guest
import this module where the deployed guest's import `LeanVM.Guest.Memory`.
-/

namespace LeanVM.SaltedGuest.Memory

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest

@[expose] public section

/-- **`main`'s jump table**: the slot each `SET` of `__jump_tables` writes in `main`'s frame,
and its word. -/
def tableCells : List (ℕ × E) :=
  Data.f0.code.filterMap fun
    | .set o k0 k1 k2 => some (o, OffsetInstruction.immediateWord k0 k1 k2)
    | _ => none

set_option maxRecDepth 100000 in
/-- The slots are `458, 470, …`, one per `SET`. -/
theorem tableCells_offsets : tableCells.map Prod.fst = List.range' 458 13952 := by
  decide +kernel

/-- The slots lie in `main`'s frame past its header, below `458 + 13952`. -/
theorem tableCells_off {q : ℕ × E} (hq : q ∈ tableCells) : 2 ≤ q.1 ∧ q.1 < 458 + 13952 := by
  have := tableCells_offsets ▸ List.mem_map_of_mem (f := Prod.fst) hq
  rw [List.mem_range'_1] at this
  omega

/-- Two slots at one offset are one slot. -/
theorem tableCells_agree {q q' : ℕ × E} (hq : q ∈ tableCells) (hq' : q' ∈ tableCells)
    (he : q.1 = q'.1) : q.2 = q'.2 := by
  have hnd : (tableCells.map Prod.fst).Nodup := tableCells_offsets ▸ List.nodup_range'
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hq
  obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hq'
  have : i = j := by
    have hi' : i < (tableCells.map Prod.fst).length := by simpa using hi
    have hj' : j < (tableCells.map Prod.fst).length := by simpa using hj
    exact (List.Nodup.getElem_inj_iff hnd (hi := hi') (hj := hj')).mp (by simpa using he)
  subst this
  rfl

end
end LeanVM.SaltedGuest.Memory
