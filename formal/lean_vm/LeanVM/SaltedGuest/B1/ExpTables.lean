/-
  LeanVM.SaltedGuest.B1.ExpTables

  `exponent_tables`' returns are the exponent tables, in the salted guest.
-/

module

public import LeanVM.SaltedGuest.Same
public import LeanVM.SaltedGuest.Sound
public import LeanVM.Guest.B1.Bits.Tables

/-!
# `ExpTablesSound`

`exponent_tables` is an unchanged function (`Same.closed`), so its salted relation is the deployed
one (`Same.rel_same'`), which is the exponent tables (`B1.exponent_tables_holds`).
-/

namespace LeanVM.SaltedGuest.End

open LeanVM.Guest LeanVM.Guest.Core

@[expose] public section

/-- **`exponent_tables`' relation is the exponent tables.** -/
theorem expTablesSound : ExpTablesSound := fun rd q h ↦
  (B1.exponent_tables_holds rd [] [q]).mp
    ((Same.rel_same' rd (f := "exponent_tables") (by decide +kernel) (by decide +kernel) [] [q]).mp h)

end
end LeanVM.SaltedGuest.End
