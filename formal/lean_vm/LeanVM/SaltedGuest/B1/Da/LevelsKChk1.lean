/-
  LeanVM.SaltedGuest.B1.Da.LevelsKChk1

  The salted `da_levels`' specializations 3, 4, checked by kernel evaluation.
-/

module

public import LeanVM.SaltedGuest.B1.Da.LevelsK

namespace LeanVM.SaltedGuest.B1.Da

@[expose] public section

set_option maxRecDepth 100000 in
theorem dl_okS3 : dlEntryOkS 3 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem dl_okS4 : dlEntryOkS 4 = true := by decide +kernel

end
end LeanVM.SaltedGuest.B1.Da
