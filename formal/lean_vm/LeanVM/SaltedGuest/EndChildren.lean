/-
  LeanVM.SaltedGuest.EndChildren

  The children's claims of what a salted decoder outputs: at most `2^35 - 2` signature claims each.
-/

module

public import LeanVM.SaltedGuest.EndReplay
public import LeanVM.SaltedGuest.B1.Main.ChildClaims
public import LeanVM.Salted.Decoding

/-!
# The children's claims of a salted decoder's output

A decoder program that outputs, on an execution, the encoding of the salted decoding by replay
outputs nothing else there (`Recursion.Salted.encodeValue_saltedDecoding_injective`), so every child of a decoding it
outputs has a statement of at most `2^35 - 2` signature claims (`B1.Main.decK_child_claims`):
`childClaims_of_output`, the second half of the downstream `SaltedGuest.DecodesWithin B C` at
`C = 2^35 - 2`.
-/

namespace LeanVM.SaltedGuest.End

open LeanVM.Parameters LeanVM.Semantics LeanVM.Node

@[expose] public section

/-- **The children's claims of a salted decoder's output**: where a decoder program outputs the
encoding of the salted decoding by replay, every child of a decoding it outputs has at most
`2^35 - 2` signature claims. -/
theorem childClaims_of_output {decoder : Cost.MachineProgram} {sizeBound b : ℕ}
    {t : Execution guestProgram}
    (ho : Cost.outputWithin decoder sizeBound b (Cost.encodeGuestWitnessDecoderInput guestProgram t) =
      some (Cost.encodeValue (decodeWithR (B1.Main.decK B1.VerifySub.vsPiOfK) t.memory))) :
    ∀ dec : Recursion.Salted.SaltedDecoding,
      Cost.outputWithin decoder sizeBound b (Cost.encodeGuestWitnessDecoderInput guestProgram t) =
        some (Cost.encodeValue dec) →
      ∀ child ∈ dec.witness.children,
        child.statement.claims.xmss.length + child.statement.claims.sphincs.length ≤ 2 ^ 35 - 2 := by
  intro dec h
  rw [ho] at h
  have e := Recursion.Salted.encodeValue_saltedDecoding_injective (Option.some.inj h)
  subst e
  exact B1.Main.decK_child_claims _ _ _ _

end
end LeanVM.SaltedGuest.End
