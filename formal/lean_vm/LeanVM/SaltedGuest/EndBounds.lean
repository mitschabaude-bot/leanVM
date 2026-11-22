/-
  LeanVM.SaltedGuest.EndBounds

  The salted guest's decodings on its valid executions: the children's claims, the encoded size,
  the DA matrix's rows.
-/

module

public import LeanVM.SaltedGuest.Bounds.Decoding

/-!
# The salted guest's decodings on its valid executions

**`saltedGuest_decodingsValid`**: on every execution `SaltedGuest.KnowledgeSound` quantifies over
(valid for a public input of two digests, `ValidExecution₂`), every decoding the salted guest's
decoder outputs (within its size bound and budget):

* has children of at most `2^30 - 1` signature claims each (`Bounds.childClaims_valid`; the
  guest bounds the two regions of its coverage table together by the memory's size, `2^30` words
  at most, and by nothing smaller);
* has an encoding of size at most `Bounds.decodingSizeBoundValid = 2760663911915`, about `2^41.33`
  (`Bounds.decodingSize_valid`);
* has a DA matrix of at most `LeanDa.maxRows = 1024` rows (`Bounds.daRows_le`, which holds on
  every execution; on a valid one the salted node relation's `OpensUnder` states it as well).
-/

namespace LeanVM.SaltedGuest.End

open LeanVM.Cost LeanVM.Semantics LeanVM.Node Recursion.SecondDigest

@[expose] public section

/-- **The salted guest's decodings on its valid executions**: a child's claims, the encoded size,
the DA matrix's rows. -/
theorem saltedGuest_decodingsValid :
    ∀ input (execution : Execution saltedGuest.program),
      ValidExecution₂ saltedGuest.program input execution →
      ∀ decoding : SeedStatementAndWitness,
        outputWithin saltedGuest.decoder saltedGuest.decoderSizeBound
            (saltedGuest.decoderBudget execution)
            (encodeGuestWitnessDecoderInput saltedGuest.program execution) =
          some (encodeValue decoding) →
        (∀ child ∈ decoding.witness.children,
          child.statement.claims.xmss.length + child.statement.claims.sphincs.length ≤
            2 ^ 30 - 1) ∧
        (encodeValue decoding).size ≤ Bounds.decodingSizeBoundValid ∧
        ∀ claim matrix, decoding.witness.daMatrix = some (claim, matrix) →
          matrix.rows.length ≤ LeanDa.maxRows := by
  intro input t hv dec h
  unfold saltedGuest at h
  dsimp only at h
  exact ⟨Bounds.childClaims_valid hv dec h,
    Bounds.decodingSize_valid hv _ dec h (decodeDecoded_enc dec),
    Bounds.daRows_le t dec h⟩

end
end LeanVM.SaltedGuest.End
