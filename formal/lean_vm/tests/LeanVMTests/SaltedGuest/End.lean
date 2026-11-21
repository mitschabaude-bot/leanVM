import LeanVM.SaltedGuest.EndSound

/-!
# The salted guest's soundness theorem: its statement and its axioms

`LeanVM.SaltedGuest.End.knowledgeSound` proves the salted guest knowledge sound
(`Recursion.Salted.SaltedGuest.KnowledgeSound`) from its open per-function obligations
(`Obligations`) and the decoder program's (`DecoderComputes`); its axiom footprint is Lean's three.
-/

open LeanVM.SaltedGuest.End

example {dec : LeanVM.Guest.Core.Val → LeanVM.Guest.Core.Reader → FrameMap → LeanVM.Node.SeedStatementAndWitness}
    {decoder : LeanVM.Cost.MachineProgram} {sizeBound : ℕ}
    {budget : LeanVM.Semantics.Execution LeanVM.SaltedGuest.guestProgram → ℕ}
    (h : Obligations dec) (hd : DecoderComputes decoder sizeBound budget dec) :
    (⟨LeanVM.SaltedGuest.guestProgram, decoder, sizeBound, budget⟩ :
      Recursion.Salted.SaltedGuest).KnowledgeSound :=
  knowledgeSound h hd

/-- info: 'LeanVM.SaltedGuest.End.knowledgeSound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.SaltedGuest.End.knowledgeSound
