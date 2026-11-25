/-
  LeanVM.SaltedGuest.EndCorrect

  The salted guest's correctness: knowledge soundness and its decoder's bounds on valid
  executions, the clauses of the recursion's `SaltedGuest.Correct`.
-/

module

public import LeanVM.SaltedGuest.EndBounds
public import LeanVM.SaltedGuest.Bounds.PriceK
public import LeanVM.SaltedGuest.Decoder.Bits

/-!
# The salted guest's correctness

Over the executions `SaltedGuest.KnowledgeSound` quantifies over (`ValidExecution₂`):

* **`saltedGuest_budgetWithin`**: on an execution of at most `2^30` steps, the decoder's budget
  (the salted decoder program's price, `saltedDecoderPrice`) is at most `2^52`
  (`Bounds.saltedDecoderPrice_le_of_steps30`: at most `2053965829417304`, about `2^50.87`);
* **`saltedGuest_decodesWithin`**: that budget and the claims at `2^20` together, the shape of the
  recursion's `SaltedGuest.DecodesWithin decoderBound (2 ^ 20)` (`extractedStepCap = 2^30`,
  `decoderBound = 2^52`);
* **`saltedGuest_decoderBits`**: the decoder program's bit length (`MachineProgram.bits`, the
  recursion statement's, `LeanVM/Salted/ProgramCode.lean`) is at most `2^64`
  (`Decoder.saltedDecoder_bits_le`: at most `57794817`);
* **`saltedGuest_correct`**: knowledge soundness, `saltedGuest_decodesWithin`, the hints' rounds
  and the decoder's bits together, the clauses of the recursion's `SaltedGuest.Correct`.
-/

namespace LeanVM.SaltedGuest.End

open LeanVM.Cost LeanVM.Semantics LeanVM.Node Recursion.SecondDigest

@[expose] public section

/-- **The salted guest's decoder budget on its valid executions**: on every valid execution for a
public input of two digests of at most `2^30` steps, at most `2^52`. -/
theorem saltedGuest_budgetWithin :
    ∀ input (execution : Execution saltedGuest.program),
      ValidExecution₂ saltedGuest.program input execution →
      execution.stepCount ≤ 2 ^ 30 → saltedGuest.decoderBudget execution ≤ 2 ^ 52 :=
  fun _ _ hv hs ↦ (Bounds.saltedDecoderPrice_le_of_steps30 hv hs).trans Bounds.saltedPrice30_le

/-- **The salted guest decodes within `2^52` and `2^20`**: on every valid execution for a public
input of two digests, the decoder's budget is at most `2^52` where the execution takes at most
`2^30` steps, and a decoding the decoder outputs and each of its children have at most `2^20`
signature claims. -/
theorem saltedGuest_decodesWithin :
    ∀ input (execution : Execution saltedGuest.program),
      ValidExecution₂ saltedGuest.program input execution →
      (execution.stepCount ≤ 2 ^ 30 → saltedGuest.decoderBudget execution ≤ 2 ^ 52) ∧
        ∀ dec : Recursion.Salted.SaltedDecoding,
          outputWithin saltedGuest.decoder saltedGuest.decoderSizeBound
              (saltedGuest.decoderBudget execution)
              (encodeGuestWitnessDecoderInput saltedGuest.program execution) =
            some (encodeValue dec) →
          dec.statement.claims.xmss.length + dec.statement.claims.sphincs.length ≤ 2 ^ 20 ∧
            ∀ child ∈ dec.witness.children,
              child.statement.claims.xmss.length + child.statement.claims.sphincs.length ≤
                2 ^ 20 :=
  fun input t hv ↦ ⟨saltedGuest_budgetWithin input t hv, saltedGuest_claimsWithin input t hv⟩

set_option maxRecDepth 100000 in
/-- **The salted guest's decoder program has at most `2^64` bits.** -/
theorem saltedGuest_decoderBits : saltedGuest.decoder.bits ≤ 2 ^ 64 := by
  have h := Decoder.saltedDecoder_bits_le
  unfold saltedGuest
  dsimp only
  exact h

/-- **The salted guest is correct**: knowledge sound; on every valid execution for a public input
of two digests its decoder's budget is at most `2^52` where the execution takes at most `2^30`
steps, and a decoding the decoder outputs and each of its children have at most `2^20` signature
claims; the decoding's batching hints have at most `log₂ |bytecode|` rounds; and its decoder
program has at most `2^64` bits. -/
theorem saltedGuest_correct :
    saltedGuest.KnowledgeSound ∧
    (∀ input (execution : Execution saltedGuest.program),
      ValidExecution₂ saltedGuest.program input execution →
      (execution.stepCount ≤ 2 ^ 30 → saltedGuest.decoderBudget execution ≤ 2 ^ 52) ∧
        ∀ dec : Recursion.Salted.SaltedDecoding,
          outputWithin saltedGuest.decoder saltedGuest.decoderSizeBound
              (saltedGuest.decoderBudget execution)
              (encodeGuestWitnessDecoderInput saltedGuest.program execution) =
            some (encodeValue dec) →
          dec.statement.claims.xmss.length + dec.statement.claims.sphincs.length ≤ 2 ^ 20 ∧
            ∀ child ∈ dec.witness.children,
              child.statement.claims.xmss.length + child.statement.claims.sphincs.length ≤
                2 ^ 20) ∧
    (∀ input (execution : Execution saltedGuest.program),
      ValidExecution₂ saltedGuest.program input execution →
      ∀ dec : Recursion.Salted.SaltedDecoding,
        outputWithin saltedGuest.decoder saltedGuest.decoderSizeBound
            (saltedGuest.decoderBudget execution)
            (encodeGuestWitnessDecoderInput saltedGuest.program execution) =
          some (encodeValue dec) →
        dec.witness.batchingHints.sumcheckMessages.length ≤
          Nat.log2 saltedGuest.bytecode.length) ∧
    saltedGuest.decoder.bits ≤ 2 ^ 64 :=
  ⟨saltedGuest_knowledgeSound, saltedGuest_decodesWithin, saltedGuest_hintsWithinRounds,
    saltedGuest_decoderBits⟩

end
end LeanVM.SaltedGuest.End
