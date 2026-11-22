import LeanVM.SaltedGuest.EndTerm

/-!
# The salted guest's soundness from its terminal's obligation: its axioms

`LeanVM.SaltedGuest.End.knowledgeSound_of_term` (the salted guest knowledge sound from the salted
`check_opening_terminal`'s obligation and `DecoderComputes`), `verify_sub_sound_wK` and the salted
`open_stacked`'s soundness at the keyed hash; their axiom footprints are Lean's three.
-/

open LeanVM.SaltedGuest.End

example {decoder : LeanVM.Cost.MachineProgram} {sizeBound : ℕ}
    {budget : LeanVM.Semantics.Execution LeanVM.SaltedGuest.guestProgram → ℕ}
    (hterm : ∀ {κ : ℕ}, κ ≤ 32 → ∀ (L : LeanVM.Semantics.MemoryImage κ),
      LeanVM.SaltedGuest.B1.VerifySub.check_opening_terminal_SpecK L.read)
    (hd : DecoderComputes decoder sizeBound budget
      (LeanVM.SaltedGuest.B1.Main.decK LeanVM.SaltedGuest.B1.VerifySub.vsPiOfK)) :
    (⟨LeanVM.SaltedGuest.guestProgram, decoder, sizeBound, budget⟩ :
      Recursion.Salted.SaltedGuest).KnowledgeSound :=
  knowledgeSound_of_term hterm hd

/-- info: 'LeanVM.SaltedGuest.B1.Whir.open_stacked_sound_wK_lvWK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.SaltedGuest.B1.Whir.open_stacked_sound_wK_lvWK

/-- info: 'LeanVM.SaltedGuest.B1.VerifySub.verify_sub_sound_wK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.SaltedGuest.B1.VerifySub.verify_sub_sound_wK

/-- info: 'LeanVM.SaltedGuest.End.knowledgeSound_of_term' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.SaltedGuest.End.knowledgeSound_of_term
