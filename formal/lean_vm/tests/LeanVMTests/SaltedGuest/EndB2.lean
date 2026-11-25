import LeanVM.SaltedGuest.EndB2

/-!
# B2 for the salted bytecode, and the soundness from `main`'s obligation: their axioms

`LeanVM.SaltedGuest.End.b2SoundL` (B2 with its four facts about the salted core IR proved) and
`LeanVM.SaltedGuest.End.knowledgeSound_of_main` (the salted guest knowledge sound from `MainSound`
and `DecoderComputes`); their axiom footprints are Lean's three.
-/

open LeanVM.SaltedGuest.End

example {dec : LeanVM.Guest.Core.Val → LeanVM.Guest.Core.Reader → FrameMap → Recursion.Salted.SaltedDecoding}
    {decoder : LeanVM.Cost.MachineProgram} {sizeBound : ℕ}
    {budget : LeanVM.Semantics.Execution LeanVM.SaltedGuest.guestProgram → ℕ}
    (hmain : MainSound dec) (hd : DecoderComputes decoder sizeBound budget dec) :
    (⟨LeanVM.SaltedGuest.guestProgram, decoder, sizeBound, budget⟩ :
      Recursion.Salted.SaltedGuest).KnowledgeSound :=
  knowledgeSound_of_main hmain hd

/-- info: 'LeanVM.SaltedGuest.End.b2SoundL' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.SaltedGuest.End.b2SoundL

/-- info: 'LeanVM.SaltedGuest.End.knowledgeSound_of_main' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.SaltedGuest.End.knowledgeSound_of_main
