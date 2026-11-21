/-
  LeanVM.SaltedGuest.EndMain

  The salted guest's knowledge soundness from `verify_sub`'s obligation and the decoder program's:
  `main`'s obligation proved.
-/

module

public import LeanVM.SaltedGuest.EndB2
public import LeanVM.SaltedGuest.B1.Main.SoundVK

/-!
# `main`'s obligation, proved

`main`'s obligation (`MainSound`) holds for the decoding `B1.Main.decK piOf` whenever the salted
`verify_sub` is sound with its child proof named by `piOf` (`B1.Main.SubSoundWK`,
`B1.Main.mainSound_of_sub`). So the salted guest is knowledge sound from `verify_sub`'s obligation
and the decoder program's for that decoding alone (`knowledgeSound_of_sub`).
-/

namespace LeanVM.SaltedGuest.End

open LeanVM.Guest
open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Node Recursion.Salted

@[expose] public section

/-- **The salted guest is knowledge sound**, from `verify_sub`'s obligation with its proof named
by `piOf` and the decoder program's for the decoding `B1.Main.decK piOf`. -/
theorem knowledgeSound_of_sub {piOf : Reader → Val → FrameMap → LeanVM.Protocol.Compile.Proof}
    {decoder : Cost.MachineProgram} {sizeBound : ℕ} {budget : Execution guestProgram → ℕ}
    (hsub : B1.Main.SubSoundWK piOf)
    (hd : DecoderComputes decoder sizeBound budget (B1.Main.decK piOf)) :
    (⟨guestProgram, decoder, sizeBound, budget⟩ : SaltedGuest).KnowledgeSound :=
  knowledgeSound_of_main (B1.Main.mainSound_of_sub hsub) hd

end
end LeanVM.SaltedGuest.End
