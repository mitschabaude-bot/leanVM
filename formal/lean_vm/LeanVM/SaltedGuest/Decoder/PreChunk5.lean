/-
  LeanVM.SaltedGuest.Decoder.PreChunk5

  The salted functions' preconditions `965 … 1157`, written out by the kernel.
-/

module

public import LeanVM.Guest.Fast.PreSig
public import LeanVM.SaltedGuest.Glob
public import LeanVM.Guest.KernelLit

/-! The preconditions of the salted functions `965 … 1157` as their test reads them
(`Guest.Fast.fnPreOf (glob.sig j)`), the kernel's evaluation in a module of its own. -/

namespace LeanVM.SaltedGuest.Decoder

open LeanVM.Guest.Check LeanVM.Guest.Fast

@[expose] public section

/-- The salted functions' preconditions `965 … 1157`. -/
kernel_lit preChunk5 : List (Option FnPre) :=
  (List.range' 965 193).map fun j ↦ fnPreOf (glob.sig j)

end

end LeanVM.SaltedGuest.Decoder
