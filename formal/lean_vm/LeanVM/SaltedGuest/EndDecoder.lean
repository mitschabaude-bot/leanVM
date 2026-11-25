/-
  LeanVM.SaltedGuest.EndDecoder

  The salted guest with its compiled decoder is knowledge sound.
-/

module

public import LeanVM.SaltedGuest.Decoder.OutputSize

/-!
# The salted guest is knowledge sound

`saltedGuest`: the salted guest program with its compiled decoder (`Decoder.saltedDecoder`), the
decoder's size bound its own size and its budget on an execution its own price
(`Decoder.saltedDecoderPrice`). **`saltedGuest_knowledgeSound`**: it is knowledge sound, with no
hypothesis: the decoder's obligation for the decoding by replay
(`Decoder.decoderComputesR_saltedDecoder`) in `knowledgeSound_of_decoderR`.
**`saltedGuest_decodingsBounded`**: on every execution, every decoding its decoder's output decodes
to has an encoding of size at most `Decoder.decodingSizeBoundK` (about `2^72.9`), the form of the
downstream `SaltedGuest.DecodingsBounded` at that bound.
-/

namespace LeanVM.SaltedGuest.End

@[expose] public section

/-- **The salted guest with its compiled decoder**, the decoder's size bound and budget its own
size and price. -/
noncomputable def saltedGuest : Recursion.Salted.SaltedGuest :=
  ⟨guestProgram, Decoder.saltedDecoder, Decoder.saltedDecoder.size, Decoder.saltedDecoderPrice⟩

/-- **The salted guest with its compiled decoder is knowledge sound.** -/
theorem saltedGuest_knowledgeSound : saltedGuest.KnowledgeSound :=
  knowledgeSound_of_decoderR Decoder.decoderComputesR_saltedDecoder

/-- **The salted guest's decodings are bounded**: on every execution of the salted guest, every
decoding the decoder's output (within its size bound and budget) decodes to has an encoding of size
at most `Decoder.decodingSizeBoundK`. -/
theorem saltedGuest_decodingsBounded :
    ∀ (execution : Semantics.Execution saltedGuest.program) (output : Cost.MachineValue)
      (decoding : Recursion.Salted.SaltedDecoding),
      Cost.outputWithin saltedGuest.decoder saltedGuest.decoderSizeBound
          (saltedGuest.decoderBudget execution)
          (Cost.encodeGuestWitnessDecoderInput saltedGuest.program execution) = some output →
        Cost.MachineDecoding.decodeValue output = some decoding →
        (Cost.encodeValue decoding).size ≤ Decoder.decodingSizeBoundK := by
  intro execution output decoding h hd
  unfold saltedGuest at h
  dsimp only at h
  exact Decoder.saltedDecoder_decodings_bounded execution output decoding h hd

end
end LeanVM.SaltedGuest.End
