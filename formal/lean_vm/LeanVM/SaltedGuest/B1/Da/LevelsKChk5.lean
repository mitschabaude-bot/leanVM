/-
  LeanVM.SaltedGuest.B1.Da.LevelsKChk5

  The salted `da_levels`' specializations 9, checked by kernel evaluation.
-/

module

public import LeanVM.SaltedGuest.B1.Da.LevelsK

namespace LeanVM.SaltedGuest.B1.Da

@[expose] public section

set_option maxRecDepth 100000 in
theorem dl_okS9 : dlEntryOkS 9 = true := by decide +kernel

end
end LeanVM.SaltedGuest.B1.Da
