import LeanVM.SaltedGuest.EndBounds

/-!
# The salted guest's decodings on its valid executions, their axioms

On every valid execution for a public input of two digests, every decoding the salted guest's
decoder outputs has a statement and children of at most `2^30 - 1` signature claims each
(`saltedGuest_claimsWithin`), batching hints of at most `log₂ |bytecode|` rounds
(`saltedGuest_hintsWithinRounds`), an encoding of size at most `2760663911915` and a DA matrix of at
most `1024` rows (`saltedGuest_decodingsValid`); the axiom footprint of each is Lean's three.
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

/-- The size bound is the number `2760663911915`. -/
example : LeanVM.SaltedGuest.Bounds.decodingSizeBoundValid = 2760663911915 := rfl
