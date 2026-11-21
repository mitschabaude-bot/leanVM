/-
  LeanVM.SaltedGuest.B1.Da.LevelsKAll

  The salted `da_levels`' specializations compute their meanings.
-/

module

public import LeanVM.SaltedGuest.B1.Da.LevelsKChk0
public import LeanVM.SaltedGuest.B1.Da.LevelsKChk1
public import LeanVM.SaltedGuest.B1.Da.LevelsKChk2
public import LeanVM.SaltedGuest.B1.Da.LevelsKChk3
public import LeanVM.SaltedGuest.B1.Da.LevelsKChk4
public import LeanVM.SaltedGuest.B1.Da.LevelsKChk5
public import LeanVM.SaltedGuest.B1.Da.LevelsKChk6

/-!
# The salted `da_levels`, sound

`da_levels_soundK`: the eleven entries of `dlTabS` are checked (`LevelsKChk*`), so each
specialization computes `MeaningDaLevelsK k` (`dl_soundK`).
-/

namespace LeanVM.SaltedGuest.B1.Da

open LeanVM.Parameters LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.B1.Da

@[expose] public section

/-- **The salted `da_levels`' specializations compute their meanings.** -/
theorem da_levels_soundK : ∀ k ≤ 10, ∀ (rd : Reader) (args rets : List E),
    SaltedGuest.coreProgram.Rel rd (daLevelsName k) args rets → MeaningDaLevelsK k rd args rets := by
  intro k hk
  interval_cases k
  · exact dl_soundK (by norm_num) dl_okS0
  · exact dl_soundK (by norm_num) dl_okS1
  · exact dl_soundK (by norm_num) dl_okS2
  · exact dl_soundK (by norm_num) dl_okS3
  · exact dl_soundK (by norm_num) dl_okS4
  · exact dl_soundK (by norm_num) dl_okS5
  · exact dl_soundK (by norm_num) dl_okS6
  · exact dl_soundK (by norm_num) dl_okS7
  · exact dl_soundK (by norm_num) dl_okS8
  · exact dl_soundK (by norm_num) dl_okS9
  · exact dl_soundK (by norm_num) dl_okS10

end
end LeanVM.SaltedGuest.B1.Da
