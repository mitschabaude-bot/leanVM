/-
  LeanVM.SaltedGuest.Decoder.Indices

  The salted decoder program's bodies' indices increase, by evaluation.
-/

module

public import LeanVM.SaltedGuest.Decoder.Top
public import LeanVM.Cost.DecoderProgram

/-!
# The salted decoder program's indices

A module of its own, importing the compiled top and the program's definition alone, as
`Cost/DecoderSize.lean` is the deployed decoder's: `saltedDecoder_indices_increasing`, the
indices of the compiled top's bodies increase from the entry's `0` (`increasingFrom`, by
`decide +kernel`, which reads the indices, not the bodies).
-/

namespace LeanVM.SaltedGuest.Decoder

open LeanVM.Cost

@[expose] public section

set_option maxRecDepth 100000 in
/-- The bodies' indices increase from the entry's `0`. -/
theorem saltedDecoder_indices_increasing :
    increasingFrom 0 (decTopKC.costDeps.map (·.1)) = true := by
  decide +kernel

end

end LeanVM.SaltedGuest.Decoder
