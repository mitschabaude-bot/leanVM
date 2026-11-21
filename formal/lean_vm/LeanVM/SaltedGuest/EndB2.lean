/-
  LeanVM.SaltedGuest.EndB2

  B2 for the salted bytecode, proved, and the salted guest's knowledge soundness from `main`'s
  obligation and the decoder program's.
-/

module

public import LeanVM.SaltedGuest.EndSound
public import LeanVM.SaltedGuest.B1.ExpTables
public import LeanVM.SaltedGuest.B1.VerifySub.Dims
public import LeanVM.SaltedGuest.B1.VerifySub.Known
public import LeanVM.SaltedGuest.WalkKnownAll

/-!
# B2, proved

The four facts about the salted core IR that the checked windows' cuts take are theorems:
`expTablesSound` (`exponent_tables`, unchanged), `vsDimsKnown_proved` and `vsKnown_proved`
(`verify_sub`'s `dims_g` and `kappa_base` bounds), `walkKnown_proved` (the windowed Merkle walks
and the GKR layer loop). So B2 holds (`b2SoundL`), and the salted guest is knowledge sound from
`main`'s obligation and the decoder program's alone (`knowledgeSound_of_main`).
-/

namespace LeanVM.SaltedGuest.End

open LeanVM.Guest
open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Node Recursion.Salted

@[expose] public section

/-- **B2 for the salted bytecode, proved.** -/
theorem b2SoundL : B2SoundL :=
  b2SoundL_of expTablesSound vsDimsKnown_proved vsKnown_proved walkKnown_proved

/-- **The salted guest is knowledge sound**, from `main`'s obligation and the decoder program's. -/
theorem knowledgeSound_of_main {dec : Val → Reader → FrameMap → SeedStatementAndWitness}
    {decoder : Cost.MachineProgram} {sizeBound : ℕ} {budget : Execution guestProgram → ℕ}
    (hmain : MainSound dec) (hd : DecoderComputes decoder sizeBound budget dec) :
    (⟨guestProgram, decoder, sizeBound, budget⟩ : SaltedGuest).KnowledgeSound :=
  knowledgeSound_of_b2 b2SoundL hmain hd

end
end LeanVM.SaltedGuest.End
