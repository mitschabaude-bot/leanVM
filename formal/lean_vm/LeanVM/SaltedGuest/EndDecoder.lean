/-
  LeanVM.SaltedGuest.EndDecoder

  The salted guest with its compiled decoder is knowledge sound.
-/

module

public import LeanVM.SaltedGuest.Decoder.Program

/-!
# The salted guest is knowledge sound

`saltedGuest`: the salted guest program with its compiled decoder (`Decoder.saltedDecoder`), the
decoder's size bound its own size and its budget on an execution its own price
(`Decoder.saltedDecoderPrice`). **`saltedGuest_knowledgeSound`**: it is knowledge sound, with no
hypothesis: the decoder's obligation for the decoding by replay
(`Decoder.decoderComputesR_saltedDecoder`) in `knowledgeSound_of_decoderR`.
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

end
end LeanVM.SaltedGuest.End
