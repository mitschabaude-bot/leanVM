/-
  LeanVM.SaltedGuest.EndDec

  The salted guest's knowledge soundness from the decoder program's obligation alone: the salted
  `check_opening_terminal` proved.
-/

module

public import LeanVM.SaltedGuest.EndTerm
public import LeanVM.SaltedGuest.B1.Terminal.HoldsK

/-!
# The salted guest's soundness from `DecoderComputes`

The salted `check_opening_terminal` is sound on every memory image of at most `2^32` words
(`B1.Terminal.check_opening_terminal_holdsK`), so the salted guest is knowledge sound from the
decoder program's obligation for the decoding `B1.Main.decK B1.VerifySub.vsPiOfK` alone
(`knowledgeSound_of_decoder`).
-/

namespace LeanVM.SaltedGuest.End

open LeanVM.Guest
open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Node Recursion.Salted

@[expose] public section

/-- **The salted guest is knowledge sound**, from the decoder program's obligation for the
decoding `B1.Main.decK B1.VerifySub.vsPiOfK`. -/
theorem knowledgeSound_of_decoder {decoder : Cost.MachineProgram} {sizeBound : ℕ}
    {budget : Execution guestProgram → ℕ}
    (hd : DecoderComputes decoder sizeBound budget (B1.Main.decK B1.VerifySub.vsPiOfK)) :
    (⟨guestProgram, decoder, sizeBound, budget⟩ : SaltedGuest).KnowledgeSound :=
  knowledgeSound_of_term (fun hκ L ↦ B1.Terminal.check_opening_terminal_holdsK hκ L) hd

end
end LeanVM.SaltedGuest.End
