/-
  LeanVM.SaltedGuest.Decoder.Program

  The salted decoder program and its output on every valid execution of the salted guest.
-/

module

public import LeanVM.SaltedGuest.Decoder.Indices
public import LeanVM.SaltedGuest.Decoder.TopEq

/-!
# The salted decoder program

`saltedDecoder`: the entry (`decoderEntryBody`, `Cost/DecoderProgram.lean`), then the compiled
top's bodies (`decTopKC`). Its price on an execution (`saltedDecoderPrice`): the top's on the
program, `κ` and the memory vector, and the entry's `13`. **`outputWithin_saltedDecoder`**: on an
execution of a memory below `2^64` words, within its own size and price, it outputs the encoding of
the salted decoding by replay (`decTopK_eq`), so **`decoderComputesR_saltedDecoder`**: the salted
guest's decoder obligation `End.DecoderComputesR` at the program's size and price.
-/

namespace LeanVM.SaltedGuest.Decoder

open LeanVM.Cost LeanVM.Parameters LeanVM.Semantics LeanVM.Node LeanVM.SaltedGuest.B1
open LeanVM.Cost.Decoder

@[expose] public section

/-- **The salted decoder program**: the entry at `0`, then the compiled top's bodies. -/
def saltedDecoder : MachineProgram := decoderProgramOf decTopKC.costIdx decTopKC.costDeps

/-- The program holds the top's bodies. -/
theorem saltedDecoder_includes : Includes saltedDecoder decTopKC.costDeps :=
  decoderProgramOf_includes saltedDecoder_indices_increasing

/-- The program's function `0` is the entry. -/
theorem saltedDecoder_entry : saltedDecoder[0]? = some (decoderEntryBody decTopKC.costIdx) :=
  decoderProgramOf_entry saltedDecoder_indices_increasing

/-- **The salted decoder program's price** on an execution: the top's on the program, `κ` and the
memory vector, and the entry's `13`. -/
noncomputable def saltedDecoderPrice (t : Execution guestProgram) : ℕ :=
  machineCost saltedDecoder decTopKC.costIdx
    [encodeValue guestProgram, encodeValue t.logMemorySize, encodeValue (memoryVector t.memory)] + 13

/-- **The salted decoder program outputs the salted decoding by replay**, within its own size and
price, on an execution of a memory below `2^64` words. -/
theorem outputWithin_saltedDecoder (t : Execution guestProgram) (hκ : t.logMemorySize < 64) :
    outputWithin saltedDecoder saltedDecoder.size (saltedDecoderPrice t)
        (encodeGuestWitnessDecoderInput guestProgram t) =
      some (encodeValue (End.decodeWithR (Main.decK VerifySub.vsPiOfK) t.memory)) := by
  rw [← decTopK_eq hκ]
  exact outputWithin_decoderEntry le_rfl saltedDecoder_entry guestProgram t
    (decTopKC.costSpec saltedDecoder saltedDecoder_includes guestProgram t.logMemorySize
      (memoryVector t.memory)) le_rfl

/-- **The salted guest's decoder obligation holds of the salted decoder program**, at its own size
and price. -/
theorem decoderComputesR_saltedDecoder :
    End.DecoderComputesR saltedDecoder saltedDecoder.size saltedDecoderPrice
      (Main.decK VerifySub.vsPiOfK) := by
  intro input t hv
  have h32 : t.logMemorySize ≤ 32 := hv.1.1.2.1.trans (by decide)
  exact outputWithin_saltedDecoder t (by omega)

end

end LeanVM.SaltedGuest.Decoder
