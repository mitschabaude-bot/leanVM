import LeanVM.SaltedGuest.EndReplay

/-!
# The salted guest's soundness with the replayed frame map: its axioms

`LeanVM.SaltedGuest.End.knowledgeSound_of_decoderR` (the salted guest knowledge sound from
`DecoderComputesR`, the decoder's obligation for the decoding by replay) and
`Located.unfoldsV_replayK`; their axiom footprints are Lean's three.
-/

open LeanVM.SaltedGuest.End

example {decoder : LeanVM.Cost.MachineProgram} {sizeBound : ℕ}
    {budget : LeanVM.Semantics.Execution LeanVM.SaltedGuest.guestProgram → ℕ}
    (hd : DecoderComputesR decoder sizeBound budget
      (LeanVM.SaltedGuest.B1.Main.decK LeanVM.SaltedGuest.B1.VerifySub.vsPiOfK)) :
    (⟨LeanVM.SaltedGuest.guestProgram, decoder, sizeBound, budget⟩ :
      Recursion.Salted.SaltedGuest).KnowledgeSound :=
  knowledgeSound_of_decoderR hd

/-- info: 'LeanVM.SaltedGuest.Located.unfoldsV_replayK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.SaltedGuest.Located.unfoldsV_replayK

/-- info: 'LeanVM.SaltedGuest.End.knowledgeSound_of_decoderR' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.SaltedGuest.End.knowledgeSound_of_decoderR
