import LeanVM.SaltedGuest.EndBounds

/-!
# The salted guest's decodings on its valid executions, their axioms

On every valid execution for a public input of two digests, every decoding the salted guest's
decoder outputs has a statement and children of at most `2^20` signature claims each
(`saltedGuest_claimsWithin`), batching hints of at most `log₂ |bytecode|` rounds
(`saltedGuest_hintsWithinRounds`), an encoding of size at most `346031412953` and a DA matrix of at
most `1024` rows (`saltedGuest_decodingsValid`), and with knowledge soundness the first two
together (`saltedGuest_correct_claims_hints`); the axiom footprint of each is Lean's three.
-/

/-- info: 'LeanVM.SaltedGuest.End.saltedGuest_claimsWithin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.SaltedGuest.End.saltedGuest_claimsWithin

/-- info: 'LeanVM.SaltedGuest.End.saltedGuest_hintsWithinRounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.SaltedGuest.End.saltedGuest_hintsWithinRounds

/-- info: 'LeanVM.SaltedGuest.End.saltedGuest_decodingsValid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.SaltedGuest.End.saltedGuest_decodingsValid

/-- info: 'LeanVM.SaltedGuest.End.saltedGuest_correct_claims_hints' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.SaltedGuest.End.saltedGuest_correct_claims_hints

/-- The size bound is the number `346031412953`. -/
example : LeanVM.SaltedGuest.Bounds.decodingSizeBoundValid = 346031412953 := rfl
