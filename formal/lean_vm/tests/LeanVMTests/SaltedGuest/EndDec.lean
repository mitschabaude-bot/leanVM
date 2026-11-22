import LeanVM.SaltedGuest.EndDec

/-!
# The salted guest's soundness from `DecoderComputes`: its axioms

`LeanVM.SaltedGuest.End.knowledgeSound_of_decoder` (the salted guest knowledge sound from
`DecoderComputes` alone) and the salted `check_opening_terminal`'s soundness; their axiom
footprints are Lean's three.
-/

open LeanVM.SaltedGuest.End

example {decoder : LeanVM.Cost.MachineProgram} {sizeBound : ℕ}
    {budget : LeanVM.Semantics.Execution LeanVM.SaltedGuest.guestProgram → ℕ}
    (hd : DecoderComputes decoder sizeBound budget
      (LeanVM.SaltedGuest.B1.Main.decK LeanVM.SaltedGuest.B1.VerifySub.vsPiOfK)) :
    (⟨LeanVM.SaltedGuest.guestProgram, decoder, sizeBound, budget⟩ :
      Recursion.Salted.SaltedGuest).KnowledgeSound :=
  knowledgeSound_of_decoder hd

/--
info: 'LeanVM.SaltedGuest.B1.Terminal.check_opening_terminal_holdsK' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms LeanVM.SaltedGuest.B1.Terminal.check_opening_terminal_holdsK

/-- info: 'LeanVM.SaltedGuest.End.knowledgeSound_of_decoder' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.SaltedGuest.End.knowledgeSound_of_decoder
