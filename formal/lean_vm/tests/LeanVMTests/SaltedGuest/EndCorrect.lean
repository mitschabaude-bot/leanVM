import LeanVM.SaltedGuest.EndCorrect

/-!
# The salted guest's correctness, its axioms

Knowledge soundness, the decoder's budget at most `2^52` on a valid execution of at most `2^30`
steps with the claims at `2^20` (`saltedGuest_decodesWithin`), the hints' rounds and the decoder's bits at most `2^64`
together (`saltedGuest_correct`); the price's formula in the steps (`saltedDecoderPrice_le`) and its
numbers at `2^30` and `2^35` steps. The axiom footprint of each is Lean's three.
-/

/-- info: 'LeanVM.SaltedGuest.End.saltedGuest_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.SaltedGuest.End.saltedGuest_correct

/-- info: 'LeanVM.SaltedGuest.End.saltedGuest_decodesWithin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.SaltedGuest.End.saltedGuest_decodesWithin

/-- info: 'LeanVM.SaltedGuest.Bounds.saltedDecoderPrice_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.SaltedGuest.Bounds.saltedDecoderPrice_le

/-- info: 'LeanVM.SaltedGuest.Bounds.saltedDecoderPrice_le_of_steps35' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.SaltedGuest.Bounds.saltedDecoderPrice_le_of_steps35

/-- The price at `2^30` steps, about `2^50.87`. -/
example : LeanVM.SaltedGuest.Bounds.saltedPrice30 = 2053965829417304 := by decide +kernel

/-- The price at `2^35` steps, about `2^55.83`. -/
example : LeanVM.SaltedGuest.Bounds.saltedPrice35 = 63883479205009923 := by decide +kernel

/-- info: 'LeanVM.SaltedGuest.Decoder.saltedDecoder_bits_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.SaltedGuest.Decoder.saltedDecoder_bits_le

/-- The bit length's bound evaluated: `57790849`. -/
example : LeanVM.SaltedGuest.Decoder.saltedDecoderBitsBound = 57790849 := by decide +kernel
