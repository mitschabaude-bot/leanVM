import LeanVM.SaltedGuest.EndBounds

/-!
# The salted guest's decodings on its valid executions, their axioms

`LeanVM.SaltedGuest.End.saltedGuest_decodingsValid`: on every valid execution for a public input of
two digests, every decoding the salted guest's decoder outputs has children of at most `2^30 - 1`
signature claims, an encoding of size at most `2760663911915`, and a DA matrix of at most `1024`
rows; its axiom footprint is Lean's three.
-/

/-- info: 'LeanVM.SaltedGuest.End.saltedGuest_decodingsValid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.SaltedGuest.End.saltedGuest_decodingsValid

/-- The size bound is the number `2760663911915`. -/
example : LeanVM.SaltedGuest.Bounds.decodingSizeBoundValid = 2760663911915 := rfl
