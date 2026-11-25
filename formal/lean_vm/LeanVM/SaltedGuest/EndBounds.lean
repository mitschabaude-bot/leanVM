/-
  LeanVM.SaltedGuest.EndBounds

  The salted guest's decodings on its valid executions: the claims of their statements and the
  rounds of their batching hints.
-/

module

public import LeanVM.SaltedGuest.Bounds.Decoding

/-!
# The salted guest's decodings on its valid executions

Over the executions `SaltedGuest.KnowledgeSound` quantifies over (`ValidExecution₂`: a valid
execution for the first digest, the second digest in memory words `2` and `3`), every decoding the
salted guest's decoder outputs, within its size bound and budget:

* **`saltedGuest_claimsWithin`**: its statement and the statement of each of its children have at
  most `2^20` signature claims (`Bounds.stmtClaims_valid`, `Bounds.childClaims_valid`; `main` caps
  the two regions of its coverage table at `MAX_CLAIMS = 2^20 - 1` slots together, and a claim it
  declares or a child's claim takes a slot);
* **`saltedGuest_hintsWithinRounds`**: its batching hints have at most `log₂ |bytecode| = 23`
  sumcheck messages (`Bounds.hints_le`; the decoder reads `23` rounds, with or without children);
* **`saltedGuest_correct_claims_hints`**: knowledge soundness, the claims at `2^20` and the hints'
  rounds together, the clauses of the recursion's `SaltedGuest.Correct` but its budget;
* `saltedGuest_decodingsValid`: its encoding's size is at most `Bounds.decodingSizeBoundValid`,
  about `2^38.33`, and its DA matrix has at most `LeanDa.maxRows = 1024` rows.
-/

namespace LeanVM.SaltedGuest.End

open LeanVM.Cost LeanVM.Semantics LeanVM.Node Recursion.SecondDigest

@[expose] public section

/-- **The claims of the salted guest's decodings**: on every valid execution for a public input of
two digests, the statement of a decoding the decoder outputs and the statement of each of its
children have at most `2^20` signature claims. -/
theorem saltedGuest_claimsWithin :
    ∀ input (execution : Execution saltedGuest.program),
      ValidExecution₂ saltedGuest.program input execution →
      ∀ dec : Recursion.Salted.SaltedDecoding,
        outputWithin saltedGuest.decoder saltedGuest.decoderSizeBound
            (saltedGuest.decoderBudget execution)
            (encodeGuestWitnessDecoderInput saltedGuest.program execution) =
          some (encodeValue dec) →
        dec.statement.claims.xmss.length + dec.statement.claims.sphincs.length ≤ 2 ^ 20 ∧
          ∀ child ∈ dec.witness.children,
            child.statement.claims.xmss.length + child.statement.claims.sphincs.length ≤
              2 ^ 20 := by
  intro input t hv dec h
  unfold saltedGuest at h
  dsimp only at h
  exact ⟨Bounds.stmtClaims_valid hv dec h, Bounds.childClaims_valid hv dec h⟩

/-- **The rounds of the salted guest's batching hints**: on every valid execution for a public
input of two digests, the batching hints of a decoding the decoder outputs have at most
`log₂ |bytecode|` sumcheck messages. -/
theorem saltedGuest_hintsWithinRounds :
    ∀ input (execution : Execution saltedGuest.program),
      ValidExecution₂ saltedGuest.program input execution →
      ∀ dec : Recursion.Salted.SaltedDecoding,
        outputWithin saltedGuest.decoder saltedGuest.decoderSizeBound
            (saltedGuest.decoderBudget execution)
            (encodeGuestWitnessDecoderInput saltedGuest.program execution) =
          some (encodeValue dec) →
        dec.witness.batchingHints.sumcheckMessages.length ≤ Nat.log2 saltedGuest.bytecode.length := by
  intro input t _ dec h
  unfold saltedGuest at h
  dsimp only at h
  have hb : Nat.log2 saltedGuest.bytecode.length = 23 := by
    show Nat.log2 bytecode.length = 23
    rw [bytecode_length, Nat.log2_two_pow]
  rw [hb]
  exact Bounds.hints_le t dec h

/-- **The salted guest's decodings on its valid executions**: a child's claims, the encoded size,
the DA matrix's rows. -/
theorem saltedGuest_decodingsValid :
    ∀ input (execution : Execution saltedGuest.program),
      ValidExecution₂ saltedGuest.program input execution →
      ∀ decoding : Recursion.Salted.SaltedDecoding,
        outputWithin saltedGuest.decoder saltedGuest.decoderSizeBound
            (saltedGuest.decoderBudget execution)
            (encodeGuestWitnessDecoderInput saltedGuest.program execution) =
          some (encodeValue decoding) →
        (encodeValue decoding).size ≤ Bounds.decodingSizeBoundValid ∧
        ∀ claim matrix, decoding.witness.daMatrix = some (claim, matrix) →
          matrix.rows.length ≤ LeanDa.maxRows := by
  intro input t hv dec h
  unfold saltedGuest at h
  dsimp only at h
  exact ⟨Bounds.decodingSize_valid hv _ dec h (decodeValue_encodeValue dec), Bounds.daRows_le t dec h⟩

/-- **The salted guest is knowledge sound, its decodings have at most `2^20` claims, and its
batching hints at most `log₂ |bytecode|` rounds**, each over the valid executions for a public input
of two digests: the clauses of `SaltedGuest.Correct` but the budget. -/
theorem saltedGuest_correct_claims_hints :
    saltedGuest.KnowledgeSound ∧
    (∀ input (execution : Execution saltedGuest.program),
      ValidExecution₂ saltedGuest.program input execution →
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
          Nat.log2 saltedGuest.bytecode.length) :=
  ⟨saltedGuest_knowledgeSound, saltedGuest_claimsWithin, saltedGuest_hintsWithinRounds⟩

end
end LeanVM.SaltedGuest.End
