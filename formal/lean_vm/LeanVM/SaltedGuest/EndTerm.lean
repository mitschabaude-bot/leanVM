/-
  LeanVM.SaltedGuest.EndTerm

  The salted guest's knowledge soundness from its terminal's obligation and the decoder program's:
  `verify_sub`'s obligation proved but for its terminal.
-/

module

public import LeanVM.SaltedGuest.EndMain
public import LeanVM.SaltedGuest.B1.VerifySub.SoundOfS

/-!
# `verify_sub`'s obligation, proved from its terminal's

The salted `verify_sub` is sound with its child proof `vsPiOfK`, given the salted
`check_opening_terminal`'s obligation (`B1.VerifySub.verify_sub_sound_wK`), so the salted guest is
knowledge sound from that obligation and the decoder program's for the decoding
`B1.Main.decK B1.VerifySub.vsPiOfK` alone (`knowledgeSound_of_term`).
-/

namespace LeanVM.SaltedGuest.End

open LeanVM.Guest
open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Node Recursion.Salted

@[expose] public section

/-- **The salted guest is knowledge sound**, from its terminal's obligation and the decoder
program's for the decoding `B1.Main.decK B1.VerifySub.vsPiOfK`. -/
theorem knowledgeSound_of_term {decoder : Cost.MachineProgram} {sizeBound : ℕ}
    {budget : Execution guestProgram → ℕ}
    (hterm : ∀ {κ : ℕ}, κ ≤ 32 → ∀ (L : MemoryImage κ),
      B1.VerifySub.check_opening_terminal_SpecK L.read)
    (hd : DecoderComputes decoder sizeBound budget (B1.Main.decK B1.VerifySub.vsPiOfK)) :
    (⟨guestProgram, decoder, sizeBound, budget⟩ : SaltedGuest).KnowledgeSound :=
  knowledgeSound_of_sub (B1.VerifySub.verify_sub_sound_wK hterm) hd

end
end LeanVM.SaltedGuest.End
