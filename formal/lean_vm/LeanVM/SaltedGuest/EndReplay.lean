/-
  LeanVM.SaltedGuest.EndReplay

  The salted guest's knowledge soundness with the replayed frame map: the decoding read off the
  memory by replaying the run, so that the decoder program's obligation is about a decoding that
  chooses nothing.
-/

module

public import LeanVM.SaltedGuest.EndDec
public import LeanVM.SaltedGuest.Located.Replay

/-!
# The salted guest's soundness, its decoding by replay

`decodeWithR dec L`: `dec` at `main`'s frame, the memory and the replayed frame map
(`Located.replayFrameVK`), as the deployed decoder reads it. `DecoderComputesR`: the decoder
program's obligation for that decoding. On a valid execution the salted located relation unfolds
along the replayed frame map (`Located.unfoldsV_replayK`), so `main`'s obligation applies there
(`explains_ofR`), and the salted guest is knowledge sound from `DecoderComputesR` for the
decoding `B1.Main.decK B1.VerifySub.vsPiOfK` alone (`knowledgeSound_of_decoderR`).
-/

namespace LeanVM.SaltedGuest.End

open LeanVM.Guest
open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.SaltedGuest.Check LeanVM.Node
open LeanVM.Protocol LeanVM.Protocol.KeccakHash Recursion.Salted Recursion.SecondDigest

@[expose] public section

/-- **The decoding off a memory, by replay**: `dec` at `main`'s frame, the memory, and the
replayed frame map. -/
noncomputable def decodeWithR (dec : Val → Reader → FrameMap → SaltedDecoding)
    {κ : ℕ} (L : MemoryImage κ) : SaltedDecoding :=
  dec (valG L 1 (certOf 1)) L.read (Located.replayFrameVK L)

/-- **The decoder program's obligation, by replay**: on every valid execution of the salted guest
for a public input of two digests, the decoder, of size at most `sizeBound`, run on the encoded
program and execution within `budget`, outputs the encoding of `dec`'s decoding off the memory by
replay. -/
def DecoderComputesR (decoder : Cost.MachineProgram) (sizeBound : ℕ)
    (budget : Execution guestProgram → ℕ) (dec : Val → Reader → FrameMap → SaltedDecoding) :
    Prop :=
  ∀ input (t : Execution guestProgram), ValidExecution₂ guestProgram input t →
    Cost.outputWithin decoder sizeBound (budget t) (Cost.encodeGuestWitnessDecoderInput guestProgram t) =
      some (Cost.encodeValue (decodeWithR dec t.memory))

variable {dec : Val → Reader → FrameMap → SaltedDecoding}

/-- **Every valid execution explains its public input under its second digest**, its decoding by
replay. -/
theorem explains_ofR (hb2 : B2SoundL) (hmain : MainSound dec) (input : PublicInput₂)
    (t : Execution guestProgram) (hv : ValidExecution₂ guestProgram input t) :
    (decodeWithR dec t.memory).seed = publicInputDigest input.second ∧
      saltedStatementDigest (decodeWithR dec t.memory).seed (decodeWithR dec t.memory).statement
          (decodeWithR dec t.memory).nodeCount = publicInputDigest input.first ∧
      SaltedNodeRelation (bytecodeWords guestProgram) (decodeWithR dec t.memory).seed
        (decodeWithR dec t.memory).statement (decodeWithR dec t.memory).nodeCount
        (decodeWithR dec t.memory).witness (decodeWithR dec t.memory).childCounts ∧
      (decodeWithR dec t.memory).witness.children.length ≤ 16 := by
  obtain ⟨hb, h0, h1⟩ := mainBodyL_of hb2 hv.1
  obtain ⟨h2, h3⟩ := second_loads hv
  have hm : MemOk t.memory.read :=
    ⟨t.logMemorySize, hv.1.1.1, hv.1.1.2.1.trans (by decide), t.memory, rfl⟩
  exact hmain t.memory.read hm _ _ (Located.unfoldsV_replayK hb2 hv.1)
    (Located.rlg_le_rel t.memory) _ _ _ h0 h1 h2 h3 hb

/-- **The salted guest is knowledge sound**, from B2, `main`'s obligation and the decoder
program's, by replay. -/
theorem knowledgeSound_of_b2R {decoder : Cost.MachineProgram} {sizeBound : ℕ}
    {budget : Execution guestProgram → ℕ} (hb2 : B2SoundL) (hmain : MainSound dec)
    (hd : DecoderComputesR decoder sizeBound budget dec) :
    (⟨guestProgram, decoder, sizeBound, budget⟩ : SaltedGuest).KnowledgeSound :=
  fun input t hv ↦ ⟨decodeWithR dec t.memory, hd input t hv, explains_ofR hb2 hmain input t hv⟩

/-- **`main`'s obligation** for the decoding `B1.Main.decK B1.VerifySub.vsPiOfK`. -/
theorem mainSound_decK : MainSound (B1.Main.decK B1.VerifySub.vsPiOfK) :=
  B1.Main.mainSound_of_sub (B1.VerifySub.verify_sub_sound_wK
    (fun hκ L ↦ B1.Terminal.check_opening_terminal_holdsK hκ L))

/-- **The salted guest is knowledge sound**, from the decoder program's obligation for the decoding
`B1.Main.decK B1.VerifySub.vsPiOfK` by replay. -/
theorem knowledgeSound_of_decoderR {decoder : Cost.MachineProgram} {sizeBound : ℕ}
    {budget : Execution guestProgram → ℕ}
    (hd : DecoderComputesR decoder sizeBound budget (B1.Main.decK B1.VerifySub.vsPiOfK)) :
    (⟨guestProgram, decoder, sizeBound, budget⟩ : SaltedGuest).KnowledgeSound :=
  knowledgeSound_of_b2R b2SoundL mainSound_decK hd

end
end LeanVM.SaltedGuest.End
