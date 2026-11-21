/-
  LeanVM.SecondDigest.Program

  The public-input phase for two digests as a layout check, a challenge and two lists of claims,
  and its first three claims as leanVM's public-input phase.
-/

module

public import LeanVM.SecondDigest.Verifier
public import LeanVM.Protocol.EndToEnd.Front.PubPhase

/-!
# The phase for two digests, against leanVM's

* `secondPoint layout r`: `(r, 1, 0, …, 0)` on the memory's variables.
* `secondClaims layout second r`: the three claims on the memory columns at `secondPoint`, each
  the line through a limb of the second digest's two halves at `r` (leanVM's `pubLimb`).
* `publicInputPhase₂_eq`: the phase is the layout check, a challenge, then leanVM's claims at
  `(r, 0, …, 0)` (`pubClaims`) followed by `secondClaims`.
* `publicInputPhase₂_take`: keeping the first three claims of what it returns, the phase is the
  layout check followed by leanVM's public-input phase for the first digest.
-/

namespace Recursion.SecondDigest

open LeanVM LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Compile
open LeanVM.Protocol.Verifier LeanVM.Protocol.EndToEnd.Front

@[expose] public section

/-- The point of the second claims, `(r, 1, 0, …, 0)` on the memory's variables. -/
def secondPoint (layout : Layout) (r : E) : List E :=
  r :: 1 :: List.replicate ((layout.placement memory0).variableCount - 2) 0

/-- **The second claims**: the three limbs of the second digest's halves on the three memory
columns at `(r, 1, 0, …, 0)`. -/
def secondClaims (layout : Layout) (second : Digest) (r : E) : List ColumnClaim :=
  List.zipWith (fun column value ↦ ⟨column, secondPoint layout r, value⟩)
    [memory0, memory1, memory2] (([0, 1, 2] : List (Fin 3)).map (pubLimb second r))

/-- The phase for two digests is the layout check, a challenge, then the claims of leanVM's phase
and the second claims. -/
theorem publicInputPhase₂_eq (layout : Layout) (publicInput second : Digest) :
    publicInputPhase₂ layout publicInput second =
      (VerifierProgram.require (MemoryHasFourWords layout)).bind fun _ ↦
        VerifierProgram.sampleChallenge.bind fun r ↦
          VerifierProgram.ret (pubClaims layout publicInput r ++ secondClaims layout second r) :=
  rfl

/-- **Without the second claims, the phase is leanVM's**: the first three claims of what the
phase for two digests returns are what leanVM's public-input phase returns for the first digest,
after the layout check. -/
theorem publicInputPhase₂_take (layout : Layout) (publicInput second : Digest) :
    (publicInputPhase₂ layout publicInput second).bind (fun claims ↦ VerifierProgram.ret
        (claims.take 3)) =
      (VerifierProgram.require (MemoryHasFourWords layout)).bind fun _ ↦
        publicInputPhase layout publicInput := by
  rw [publicInputPhase₂_eq, publicInputPhase_eq, VerifierProgram.bind_assoc]
  unfold VerifierProgram.require
  split
  · simp only [VerifierProgram.ret_bind]
    rw [VerifierProgram.bind_assoc]
    simp only [VerifierProgram.ret_bind, VerifierProgram.bind_eq]
    congr 1
  · rfl

end
end Recursion.SecondDigest
