/-
  LeanVM.Salted.Decoding

  The encoding of a salted decoding is injective.
-/

module

public import LeanVM.Salted.Node
public import LeanVM.Cost.GuestDecoding

/-!
# The encoding of a salted decoding is injective

A salted guest's decoder outputs the encoding of a salted decoding (`SaltedDecoding`: a seed, a
statement, its node count, a witness and its children's counts). Its parse (`MachineDecoding
SaltedDecoding`, linear, the deployed parses of its fields) inverts the encoding, so the output
determines the decoding: **`encodeValue_saltedDecoding_injective`**.
-/

namespace Recursion.Salted

open LeanVM.Cost

@[expose] public section

/-- The parse of a salted decoding: a constructor of tag `0` with its five fields. -/
instance : MachineDecoding SaltedDecoding where
  decodeValue
    | .constructor 0 [s, t, n, w, cs] =>
      do pure ⟨← decodeValue s, ← decodeValue t, ← decodeValue n, ← decodeValue w, ← decodeValue cs⟩
    | _ => none

instance : LawfulMachineDecoding SaltedDecoding := ⟨fun ⟨s, t, n, w, cs⟩ ↦ by
  show (do pure ⟨← decodeValue (encodeValue s), ← decodeValue (encodeValue t),
    ← decodeValue (encodeValue n), ← decodeValue (encodeValue w),
    ← decodeValue (encodeValue cs)⟩ : Option SaltedDecoding) = _
  simp⟩

/-- **The encoding of a salted decoding is injective**: a salted guest decoder program's output
determines the decoding. -/
theorem encodeValue_saltedDecoding_injective :
    Function.Injective (encodeValue : SaltedDecoding → MachineValue) :=
  fun a b h ↦ Option.some.inj (by rw [← decodeValue_encodeValue a, h, decodeValue_encodeValue])

end
end Recursion.Salted
