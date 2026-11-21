import LeanVM.SaltedGuest.EndMain

/-!
# The salted guest's soundness from `verify_sub`'s obligation: its axioms

`LeanVM.SaltedGuest.End.knowledgeSound_of_sub` (the salted guest knowledge sound from
`SubSoundWK` and `DecoderComputes`, `main`'s obligation proved) and `mainSound_of_sub`; their
axiom footprints are Lean's three.
-/

open LeanVM.SaltedGuest.End

example {piOf : LeanVM.Guest.Core.Reader → LeanVM.Guest.Core.Val → FrameMap → LeanVM.Protocol.Compile.Proof}
    {decoder : LeanVM.Cost.MachineProgram} {sizeBound : ℕ}
    {budget : LeanVM.Semantics.Execution LeanVM.SaltedGuest.guestProgram → ℕ}
    (hsub : LeanVM.SaltedGuest.B1.Main.SubSoundWK piOf)
    (hd : DecoderComputes decoder sizeBound budget (LeanVM.SaltedGuest.B1.Main.decK piOf)) :
    (⟨LeanVM.SaltedGuest.guestProgram, decoder, sizeBound, budget⟩ :
      Recursion.Salted.SaltedGuest).KnowledgeSound :=
  knowledgeSound_of_sub hsub hd

/-- info: 'LeanVM.SaltedGuest.B1.Main.mainSound_of_sub' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.SaltedGuest.B1.Main.mainSound_of_sub

/-- info: 'LeanVM.SaltedGuest.End.knowledgeSound_of_sub' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.SaltedGuest.End.knowledgeSound_of_sub
