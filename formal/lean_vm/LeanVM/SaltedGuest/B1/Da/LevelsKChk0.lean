/-
  LeanVM.SaltedGuest.B1.Da.LevelsKChk0

  The salted `da_levels`' specializations 0, 1, 2, checked by kernel evaluation.
-/

module

public import LeanVM.SaltedGuest.B1.Da.LevelsK

namespace LeanVM.SaltedGuest.B1.Da

@[expose] public section

set_option maxRecDepth 100000 in
theorem dl_okS0 : dlEntryOkS 0 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem dl_okS1 : dlEntryOkS 1 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem dl_okS2 : dlEntryOkS 2 = true := by decide +kernel

end
end LeanVM.SaltedGuest.B1.Da
