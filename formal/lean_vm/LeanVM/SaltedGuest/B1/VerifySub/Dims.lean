/-
  LeanVM.SaltedGuest.B1.VerifySub.Dims

  `VsDimsKnown`: the salted `verify_sub`'s `dims_g[g^0]` below `g^34` at its call of
  `verify_tables`.
-/

module

public import LeanVM.SaltedGuest.Sound
public import LeanVM.SaltedGuest.B1.Extract
public import LeanVM.SaltedGuest.KernelRfl
public import LeanVM.Guest.B1.VerifySub.Mid

/-!
# `dims_g`'s first word

`verify_sub` (function `19`) stores its memory's log `g_log_mem` (value `132`) at `dims_g[g^0]`
(value `131`, statement `110`) after range-checking it below `g^30` (statement `101`, the constant
`2^30` at statement `100`: `assert log(g_log_mem) < MAX_LOG_MEM + 1`). The three statements are
read off the salted core IR by index (`atom_of_take`), the range check giving `g_log_mem = g^e`,
`e ≤ 30` (`VerifySub.rc_pow`).
-/

namespace LeanVM.SaltedGuest.End

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol.Verifier

@[expose] public section

set_option maxRecDepth 100000

kernel_rfl vs_s100 : (coreOf 19).body[100]? = some (.atom (.const (.n 133) (word 1073741824 0 0)))
kernel_rfl vs_s101 : (coreOf 19).body[101]? =
  some (.atom (.rangeCheck (.n 132) (.n 134) (.n 135) (.n 136) (.n 133)))
kernel_rfl vs_s110 : (coreOf 19).body[110]? = some (.atom (.load (.n 132) (.n 131) 0))

theorem vs_noRet110 : Stmt.noRetList ((coreOf 19).body.take 110) = true := by decide +kernel

/-- **`verify_sub`'s `dims_g[g^0]`** below `g^34`. -/
theorem vsDimsKnown_proved : VsDimsKnown := by
  intro κ L _ h32 σ h
  have hκ : κ ≤ 32 := h32.trans (by decide)
  have hnr100 : Stmt.noRetList ((coreOf 19).body.take 100) = true := by decide +kernel
  have hnr101 : Stmt.noRetList ((coreOf 19).body.take 101) = true := by decide +kernel
  have c := atom_of_take h (by omega) vs_s100 hnr100
  have r := atom_of_take h (by omega) vs_s101 hnr101
  have l := atom_of_take h (by omega) vs_s110 vs_noRet110
  simp only [Atom.Holds] at c l
  obtain ⟨e, he, hx⟩ := B1.VerifySub.rc_pow hκ L (a := 30) (by norm_num)
    (by rw [c, show (1073741824 : ℕ) = 2 ^ 30 from rfl, B1.VerifySub.word_pow2 (by norm_num)]) r
  exact ⟨e, by omega, by rw [← gen_pow_eq_ofK, ← hx]; exact l⟩

end
end LeanVM.SaltedGuest.End
