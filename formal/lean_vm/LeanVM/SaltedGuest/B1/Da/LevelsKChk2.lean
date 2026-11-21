/-
  LeanVM.SaltedGuest.B1.Da.LevelsKChk2

  The salted `da_levels`' specializations 5, 6, checked by kernel evaluation.
-/

module

public import LeanVM.SaltedGuest.B1.Da.LevelsK

namespace LeanVM.SaltedGuest.B1.Da

@[expose] public section

set_option maxRecDepth 100000 in
theorem dl_okS5 : dlEntryOkS 5 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem dl_okS6 : dlEntryOkS 6 = true := by decide +kernel

end
end LeanVM.SaltedGuest.B1.Da
