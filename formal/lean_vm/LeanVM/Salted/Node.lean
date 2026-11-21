/-
  LeanVM.Salted.Node

  The salted node relation, the salted guest, and its knowledge soundness.
-/

module

public import LeanVM.Salted.Hash

/-!
# The salted node relation and the salted guest

**The salted node relation** (`SaltedNodeRelation bytecode seed statement witness`) is leanVM's
`NodeRelation` with every hash and sponge taken under `seed`:

* every raw signature verifies and every signature claim is a raw signature's or a child's
  (leanVM's `SignatureClaimsHeld`, at the unsalted Keccak-256);
* the DA digest is the keyed digest of the DA claim a matrix opens under the keyed hash, or zero, or
  a child's (`SaltedDaDigestHeld`);
* every child's proof is accepted by the deferring verifier with a second public digest
  (`verifyDeferredWithHash₂`) with the IV `seed` and the keyed hash, for the child's statement's
  digest under `seed` and `seed` (`SaltedChildrenProven`);
* the deferred claim batches the children's claims in leanVM's batching program run from the
  batching's seed call under `seed` (`SaltedDeferredClaimBatched`).

**The guest is a parameter** (`SaltedGuest`): a leanISA program, the program of leanVM's cost
machine that decodes a node's seed, statement and witness from an execution, and that decoder's size
bound and budget. Its correctness is one hypothesis (`SaltedGuest.KnowledgeSound`), of the form of
leanVM's `GuestKnowledgeSoundness`: on every valid execution of the guest on a public input of two
digests (`ValidExecution₂`: the first in memory words `0` and `1`, the second in words `2` and
`3`), the decoder outputs a seed that is the second digest, a statement whose digest under that seed
is the first digest, and a witness that satisfies the salted node relation under that seed, with at
most `16` children (`ExplainsUnderSeed`). The relation gives the decoded statement the bytecode's
shape, as leanVM's does: the batching defers a claim at a point of `log₂ |bytecode|` coordinates,
or the zero point.
-/

namespace Recursion.Salted

open LeanVM LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Compile
open LeanVM.Protocol.KeccakHash LeanVM.Protocol.Verifier LeanVM.Node

@[expose] public section

/-! ## The salted node relation -/

/-- **What a node batches of its children under `seed`**: each child's statement digest under
`seed`, its proof's claim and its statement's deferred claim. -/
def saltedChildClaims (seed : Digest) (children : List Child) : List ChildClaims :=
  children.map fun child ↦
    ⟨saltedStatementDigest seed child.statement, child.freshClaim, child.statement.deferredClaim⟩

/-- **The DA digest is held under `seed`**: it is the keyed digest of the DA claim that the matrix
checked here opens under the keyed hash; without such a matrix, zero or some child's DA digest. -/
def SaltedDaDigestHeld (seed : Digest) (statement : NodeStatement) (witness : NodeWitness) : Prop :=
  match witness.daMatrix with
  | some (claim, matrix) =>
    statement.claims.daDigest = saltedDaClaimDigest seed claim ∧
      OpensUnder seed claim.daRoot claim.membershipChallenge matrix
  | none =>
    statement.claims.daDigest = zeroDigest ∨
      ∃ child ∈ witness.children, child.statement.claims.daDigest = statement.claims.daDigest

/-- **Every child is proven under `seed`**: its deferred claim has the bytecode's shape, and the
deferring verifier with a second public digest, with the IV `seed`, the keyed hash under `seed` and
Keccak-f[1600], accepts its proof for its statement's digest under `seed` and `seed`. -/
def SaltedChildrenProven (bytecode : List K) (seed : Digest) (witness : NodeWitness) : Prop :=
  ∀ child ∈ witness.children,
    let publicInput := saltedStatementDigest seed child.statement
    child.statement.deferredClaim.HasBytecodeShape bytecode ∧
      Id.run (SecondDigest.verifyDeferredWithHash₂ (m := Id) keccakF1600 (keyedHash seed) bytecode
        seed publicInput seed child.freshClaim child.proof) = true

/-- **The deferred claim batches the children's under `seed`**: without children, the bytecode at
the zero point; with children, leanVM's batching program, run over Keccak-f[1600] from the
batching's seed call under `seed`, accepts the stream of the children's claims under `seed` and the
hints, with the statement's deferred claim as its outcome. -/
def SaltedDeferredClaimBatched (bytecode : List K) (seed : Digest) (statement : NodeStatement)
    (witness : NodeWitness) : Prop :=
  if witness.children = [] then statement.deferredClaim.HasZeroPoint bytecode
  else
    let children := saltedChildClaims seed witness.children
    let program := Guest.Batch.nodeBatchingProgram (· = statement.deferredClaim) bytecode children
    let stream := Guest.Batch.batchingStream children witness.batchingHints
    Id.run (runProof (m := Id) keccakF1600 program (batchingSeed seed) ⟨stream, []⟩) = true

/-- **The salted node relation**: leanVM's node relation with every hash and sponge under `seed`.
The signatures verify at the unsalted Keccak-256. -/
def SaltedNodeRelation (bytecode : List K) (seed : Digest) (statement : NodeStatement)
    (witness : NodeWitness) : Prop :=
  SignatureClaimsHeld statement witness ∧ SaltedDaDigestHeld seed statement witness ∧
    SaltedChildrenProven bytecode seed witness ∧
    SaltedDeferredClaimBatched bytecode seed statement witness

/-! ## The salted guest -/

/-- **A salted guest**: a leanISA program, the decoder program of leanVM's cost machine that names
a node's seed, statement and witness on an execution of it, and that decoder's size bound and
budget on an execution. -/
structure SaltedGuest where
  /-- The guest program. -/
  program : LeanIsaProgram
  /-- The decoder program. -/
  decoder : Cost.MachineProgram
  /-- The decoder's size bound. -/
  decoderSizeBound : ℕ
  /-- The decoder's budget on an execution. -/
  decoderBudget : Execution program → ℕ

/-- The guest's bytecode, as the verifier reads it. -/
abbrev SaltedGuest.bytecode (G : SaltedGuest) : List K := bytecodeWords G.program

/-- **A decoding explains a public input of two digests under its seed**: the decoded seed is the
second digest, the decoded statement's digest under it is the first, the decoded witness satisfies
the salted node relation under it, and it has at most `16` children. -/
def ExplainsUnderSeed (G : SaltedGuest) (input : SecondDigest.PublicInput₂)
    (decoding : SeedStatementAndWitness) : Prop :=
  decoding.seed = publicInputDigest input.second ∧
    saltedStatementDigest decoding.seed decoding.statement = publicInputDigest input.first ∧
    SaltedNodeRelation G.bytecode decoding.seed decoding.statement decoding.witness ∧
    decoding.witness.children.length ≤ 16

/-- **Knowledge soundness of the salted guest**: on every valid execution of the guest program on a
public input of two digests, the decoder, of size at most its bound, run on the encoded program and
execution within its budget, outputs the encoding of a decoding that explains the input under its
seed, the second digest. -/
def SaltedGuest.KnowledgeSound (G : SaltedGuest) : Prop :=
  ∀ input (execution : Execution G.program), SecondDigest.ValidExecution₂ G.program input execution →
    ∃ decoding : SeedStatementAndWitness,
      Cost.outputWithin G.decoder G.decoderSizeBound (G.decoderBudget execution)
          (Cost.encodeGuestWitnessDecoderInput G.program execution) =
        some (Cost.encodeValue decoding) ∧
      ExplainsUnderSeed G input decoding

end
end Recursion.Salted
