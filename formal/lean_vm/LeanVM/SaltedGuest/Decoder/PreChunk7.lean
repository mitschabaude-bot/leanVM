/-
  LeanVM.SaltedGuest.Decoder.PreChunk7

  The salted functions' preconditions `1351 … 1538`, written out by the kernel.
-/

module

public import LeanVM.Guest.Fast.PreSig
public import LeanVM.SaltedGuest.Glob
public import LeanVM.Guest.KernelLit

/-! The preconditions of the salted functions `1351 … 1538` as their test reads them
(`Guest.Fast.fnPreOf (glob.sig j)`), the kernel's evaluation in a module of its own. -/

namespace LeanVM.SaltedGuest.Decoder

open LeanVM.Guest.Check LeanVM.Guest.Fast

@[expose] public section

/-- The salted functions' preconditions `1351 … 1538`. -/
kernel_lit preChunk7 : List (Option FnPre) :=
  (List.range' 1351 188).map fun j ↦ fnPreOf (glob.sig j)

end

end LeanVM.SaltedGuest.Decoder
