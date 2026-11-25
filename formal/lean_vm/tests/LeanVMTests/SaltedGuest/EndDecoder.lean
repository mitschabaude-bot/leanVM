import LeanVM.SaltedGuest.EndDecoder

/-!
# The salted guest with its compiled decoder: knowledge sound, its axioms

`LeanVM.SaltedGuest.End.saltedGuest_knowledgeSound`: the salted guest program with its compiled
decoder, the decoder's size bound and budget its own size and price, is knowledge sound; its axiom
footprint is Lean's three.
-/

open LeanVM.SaltedGuest.End

example : (⟨LeanVM.SaltedGuest.guestProgram, LeanVM.SaltedGuest.Decoder.saltedDecoder,
    LeanVM.SaltedGuest.Decoder.saltedDecoder.size, LeanVM.SaltedGuest.Decoder.saltedDecoderPrice⟩ :
      Recursion.Salted.SaltedGuest).KnowledgeSound :=
  saltedGuest_knowledgeSound

/-- info: 'LeanVM.SaltedGuest.End.saltedGuest_knowledgeSound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.SaltedGuest.End.saltedGuest_knowledgeSound

/-- info: 'LeanVM.SaltedGuest.Decoder.decTopK_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.SaltedGuest.Decoder.decTopK_eq

/-- info: 'LeanVM.SaltedGuest.End.saltedGuest_decodingsBounded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.SaltedGuest.End.saltedGuest_decodingsBounded

/-- The bound is the number `8633083319205129881992`. -/
example : LeanVM.SaltedGuest.Decoder.decodingSizeBoundK = 8633083319205129881992 := rfl
