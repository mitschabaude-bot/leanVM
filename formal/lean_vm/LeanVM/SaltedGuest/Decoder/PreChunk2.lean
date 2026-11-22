/-
  LeanVM.SaltedGuest.Decoder.PreChunk2

  The salted functions' preconditions `386 … 578`, written out by the kernel.
-/

module

public import LeanVM.Guest.Fast.PreSig
public import LeanVM.SaltedGuest.Glob
public import LeanVM.Guest.KernelLit

/-! The preconditions of the salted functions `386 … 578` as their test reads them
(`Guest.Fast.fnPreOf (glob.sig j)`), the kernel's evaluation in a module of its own. -/

namespace LeanVM.SaltedGuest.Decoder

open LeanVM.Guest.Check LeanVM.Guest.Fast

@[expose] public section

/-- The salted functions' preconditions `386 … 578`. -/
kernel_lit preChunk2 : List (Option FnPre) :=
  (List.range' 386 193).map fun j ↦ fnPreOf (glob.sig j)

end

end LeanVM.SaltedGuest.Decoder
