/-
  LeanVM.Salted.Verifier

  The verifier with a second public digest under a seed, compiled: the full verifier and the
  deferring one with the keyed hash, and the proof's wire decoding with the keyed hash.
-/

module

public import LeanVM.Salted.Hash
public import LeanVM.Wire.Encoding

/-!
# The salted verifier, compiled

Under a seed `s` a proof's transcript starts at `transcriptSeed s p` for the digest `p` in memory
words `0` and `1`, the second public digest is `s`, and every Merkle leaf and node is hashed with
`keyedHash s`, as the Rust verifier's `verify_execution(bytecode, seed, public_input, proof)` runs
it (`crates/verifier/src/lib.rs`, `transcript.rs`: `Sponge::new(seed, public_input, seed)`,
`Key::new(seed)`).

* `keyedVerify bytecode s p π`: the verifier program with a second public digest
  (`leanVmVerifierProgram₂`), its bytecode evaluated, run with the keyed hash from
  `transcriptSeed s p`.
* `keyedVerifyDeferred bytecode s p claim π`: the deferring verifier with a second public digest
  as a node runs it on a child (`SaltedChildrenProven`): `verifyDeferredWithHash₂` with the IV `s`,
  the second digest `s` and the keyed hash.
* `Proof.fromBytesWithHash H bytes`: `Proof.fromBytes` (`Proof::from_bytes`,
  `crates/fiat_shamir/src/wire.rs`) with the leaves and nodes rehashed by `H`; under a seed `s` the
  Rust decodes with `H = keyedHash s` (`Proof::from_bytes(bytes, &Key::new(seed))`).
-/

namespace Recursion.Salted

open LeanVM LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Compile
open LeanVM.Protocol.KeccakHash LeanVM.Protocol.Verifier

@[expose] public section

/-- **The verifier with a second public digest under `seed`**, compiled: the verifier program for
the digest `publicInput` and the second digest `seed`, run with the keyed hash under `seed` and
Keccak-f[1600] from the transcript's seed call under `seed`. -/
def keyedVerify (bytecode : List K) (seed publicInput : Digest) (π : Proof) : Bool :=
  Id.run (runProofWithHash (m := Id) (keyedHash seed) keccakF1600
    (SecondDigest.leanVmVerifierProgram₂ bytecode publicInput seed)
    (transcriptSeed seed publicInput) π)

/-- **The deferring verifier with a second public digest under `seed`**, as a node runs it on a
child: the IV and the second digest `seed`, the keyed hash under `seed`, Keccak-f[1600]. -/
def keyedVerifyDeferred (bytecode : List K) (seed publicInput : Digest) (claim : BytecodeClaim)
    (π : Proof) : Bool :=
  Id.run (SecondDigest.verifyDeferredWithHash₂ (m := Id) keccakF1600 (keyedHash seed) bytecode
    seed publicInput seed claim π)

/-- The deferring verifier under `seed` is the one `SaltedChildrenProven` names. -/
theorem keyedVerifyDeferred_eq (bytecode : List K) (seed publicInput : Digest)
    (claim : BytecodeClaim) (π : Proof) :
    keyedVerifyDeferred bytecode seed publicInput claim π =
      Id.run (SecondDigest.verifyDeferredWithHash₂ (m := Id) keccakF1600 (keyedHash seed)
        bytecode seed publicInput seed claim π) := rfl

/-! ## The wire decoding with a hash -/

section Unprune

variable {m : Type → Type} [Monad m] (H : Bytes → m Digest)

/-- One level of the climb (`climbLevel`), each parent hashed by `H`. -/
def climbLevelWithHash (nodes carried : List (ℕ × Digest)) :
    m (List (ℕ × Digest) × List (ℕ × Digest)) := do
  let siblingOf (node : ℕ) : Digest :=
    ((nodes.lookup (node ^^^ 1)).orElse fun _ ↦ carried.lookup node).getD default
  let firstChildren := nodes.filter fun (node, _) ↦ node % 2 = 0 ∨ (node ^^^ 1) ∉ nodes.map (·.1)
  let parents ← firstChildren.mapM fun (node, digest) ↦ do
    let (left, right) :=
      if node % 2 = 0 then (digest, siblingOf node) else (siblingOf node, digest)
    let parent ← H (digestBytes left ++ digestBytes right)
    pure (node >>> 1, parent)
  pure (nodes.map fun (node, _) ↦ (node, siblingOf node), parents)

/-- Climb the levels (`climbLevels`), each parent hashed by `H`. -/
def climbLevelsWithHash : List (List (ℕ × Digest)) → List (ℕ × Digest) →
    m (List (List (ℕ × Digest)))
  | [], _ => pure []
  | carried :: above, nodes => do
    let (siblings, parents) ← climbLevelWithHash H nodes carried
    let rest ← climbLevelsWithHash above parents
    pure (siblings :: rest)

/-- Unprune a phase (`unprunePhase`), its leaves and nodes hashed by `H`. -/
def unprunePhaseWithHash (phase : PrunedPhase) : m (List Opening) := do
  let leafDigests ← phase.leaves.mapM fun leaf ↦ H (leaf.flatMap K.toBytes)
  let siblings ← climbLevelsWithHash H phase.carried (phase.positions.zip leafDigests)
  pure (phase.queries.map fun query ↦
    ⟨query, ((phase.positions.zip phase.leaves).lookup query).getD [],
      (List.range phase.height).map fun level ↦
        ((siblings.getD level []).lookup (query >>> level)).getD default⟩)

/-- **The proof the bytes encode, its Merkle hash `H`** (`Proof::from_bytes(bytes, key)`): the
bytes read (`readProof`), then each phase unpruned with `H`, in order; `none` unless the bytes are
exactly one proof's encoding within the bounds. Nothing is verified. -/
def Proof.fromBytesWithHash (bytes : Bytes) : m (Option Proof) :=
  match readProof bytes with
  | none => pure none
  | some (stream, phases) => do
    let openings ← phases.mapM (unprunePhaseWithHash H)
    pure (some ⟨stream, openings⟩)

/-- With Keccak-256 over a permutation for its hash, the climb is `climbLevels`. -/
theorem climbLevelsWithHash_keccak256With (π : KeccakState → m KeccakState) :
    ∀ (carried : List (List (ℕ × Digest))) (nodes : List (ℕ × Digest)),
      climbLevelsWithHash (keccak256With π) carried nodes = climbLevels π carried nodes
  | [], _ => rfl
  | c :: above, nodes => by
    have h : climbLevelWithHash (keccak256With π) nodes c = climbLevel π nodes c := rfl
    simp only [climbLevelsWithHash, climbLevels, h, climbLevelsWithHash_keccak256With π above]

/-- With Keccak-256 over a permutation for its hash, the decoding is `Proof.fromBytes`. -/
theorem Proof.fromBytesWithHash_keccak256With (π : KeccakState → m KeccakState) (bytes : Bytes) :
    Proof.fromBytesWithHash (keccak256With π) bytes = Proof.fromBytes π bytes := by
  have h : unprunePhaseWithHash (keccak256With π) = unprunePhase π := by
    funext phase
    unfold unprunePhaseWithHash unprunePhase
    simp only [climbLevelsWithHash_keccak256With]
  unfold Proof.fromBytesWithHash Proof.fromBytes
  rw [h]
  rfl

end Unprune

end
end Recursion.Salted
