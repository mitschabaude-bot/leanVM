import LeanVM.Salted.Node
import LeanVM.Facts.NodeWith
import LeanVMTests.Salted.NodeVectors

/-!
# The salted digests and seedings against the salted Rust

The Rust vectors (`NodeVectors.lean`, written by `scripts/guest-export` from the salted
`crates/rec_aggregation/src/aggregation/` at the guest's shape, under the seed of the exporter's
salt) against the definitions of `LeanVM/Salted/Hash.lean`:

* the claim lists' keyed digests (`keyedHash` of `claimListPreimage`), the DA claim's keyed digest
  (`saltedDaClaimDigest`), its membership challenge (`membershipChallenge`) and the statement's
  salted digest with a node count (`saltedStatementDigest`) are the Rust's (`claim_list_digest`,
  `verifier::da::digest`, `membership_challenge`, `statement_digest`);
* the batching of two children's true claims, run from the batching's seed call under the seed
  (`batchingSeed`) with the Rust's hints, defers the Rust's claim (`aggregate_deferred_claims`);
* mutations: another seed gives another statement digest and another list digest, the batching
  from the unsalted seed call or with a final value one off rejects.

That the seed is `seedOfSalt` of the salted guest program, its `2^23` bytecode words hashed, is
checked compiled, by `lake exe salted-node-diff` (`cli/SaltedNodeDiff.lean`).
-/

namespace LeanVMTests.Salted.Node

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Verifier
open LeanVM.Protocol.KeccakHash LeanVM.Node Recursion.Salted

/-! ## The claim lists and the DA claim -/

#guard keyedHash NodeVectors.seed (claimListPreimage xmssPublicKeyBytes NodeVectors.xmss) =
  NodeVectors.xmssListDigest
#guard keyedHash NodeVectors.seed (claimListPreimage Sphincs.PublicKey.toBytes NodeVectors.sphincs) =
  NodeVectors.sphincsListDigest
#guard membershipChallenge NodeVectors.seed NodeVectors.daClaim.daRoot =
  NodeVectors.daClaim.membershipChallenge
#guard saltedDaClaimDigest NodeVectors.seed NodeVectors.daClaim = NodeVectors.daDigest
#guard saltedDaDigestOf NodeVectors.seed (some NodeVectors.daClaim.daRoot) = NodeVectors.daDigest
#guard saltedDaDigestOf NodeVectors.seed none = NodeVectors.daNone

-- Mutation: another seed, another list digest.
#guard keyedHash (Vector.replicate 4 0) (claimListPreimage xmssPublicKeyBytes NodeVectors.xmss) ≠
  NodeVectors.xmssListDigest

/-! ## The statement -/

/-- The statement of the vectors' claims, deferring their claim. -/
def vectorStatement : NodeStatement :=
  ⟨⟨NodeVectors.xmss, NodeVectors.sphincs, NodeVectors.daDigest⟩, NodeVectors.defer⟩

#guard saltedStatementDigest NodeVectors.seed vectorStatement NodeVectors.nodeCount =
  NodeVectors.statementDigest

-- Mutation: another seed, another digest.
#guard saltedStatementDigest (Vector.replicate 4 0) vectorStatement NodeVectors.nodeCount ≠
  NodeVectors.statementDigest

-- Mutation: another node count, another digest.
#guard saltedStatementDigest NodeVectors.seed vectorStatement (NodeVectors.nodeCount + 1) ≠
  NodeVectors.statementDigest

/-! ## The batching -/

/-- The batching of the vectors' children from the sponge state `s0`, with the hints `h`. -/
def batchFrom (s0 : KeccakState) (h : BatchingHints) : Option DeferredClaim :=
  Id.run (batchWith (m := Id) keccakF1600 s0 NodeVectors.children h)

#guard (batchFrom (batchingSeed NodeVectors.seed) NodeVectors.hints).map (·.bytecodePoint) =
  some NodeVectors.batched.bytecodePoint
#guard (batchFrom (batchingSeed NodeVectors.seed) NodeVectors.hints).map (·.bytecodeValue) =
  some NodeVectors.batched.bytecodeValue

-- Mutation: a final value one off.
#guard (batchFrom (batchingSeed NodeVectors.seed) { NodeVectors.hints with
  finalBytecodeValue := NodeVectors.hints.finalBytecodeValue + 1 }).isNone

-- Mutation: the batching from leanVM's unsalted seed call, the same hints.
#guard (batchFrom batchSeed NodeVectors.hints).isNone

end LeanVMTests.Salted.Node
