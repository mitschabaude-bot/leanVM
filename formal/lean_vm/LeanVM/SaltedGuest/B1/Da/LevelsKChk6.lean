/-
  LeanVM.SaltedGuest.B1.Da.LevelsKChk6

  The salted `da_levels`' specializations 10, checked by kernel evaluation.
-/

module

public import LeanVM.SaltedGuest.B1.Da.LevelsK

namespace LeanVM.SaltedGuest.B1.Da

@[expose] public section

set_option maxRecDepth 100000 in
theorem dl_okS10 : dlEntryOkS 10 = true := by decide +kernel

end
end LeanVM.SaltedGuest.B1.Da
