/-
  LeanVM.Salted.Node

  The salted node relation, the salted guest, and its knowledge soundness.
-/

module

public import LeanVM.Salted.Hash

/-!
# The salted node relation and the salted guest

**The salted node relation** (`SaltedNodeRelation bytecode seed statement nodeCount witness
childCounts`) is leanVM's `NodeRelation` with every hash and sponge taken under `seed`, a node
count for the statement and one for each child:

* every raw signature verifies and every signature claim is a raw signature's or a child's
  (leanVM's `SignatureClaimsHeld`, at the unsalted Keccak-256);
* the DA digest is the keyed digest of the DA claim a matrix opens under the keyed hash, or zero, or
  a child's (`SaltedDaDigestHeld`);
* every child's proof is accepted by the deferring verifier with a second public digest
  (`verifyDeferredWithHash₂`) with the IV `seed` and the keyed hash, for the digest under `seed` of
  the child's statement with its count, and `seed` (`SaltedChildrenProven`);
* the deferred claim batches the children's claims in leanVM's batching program run from the
  batching's seed call under `seed` (`SaltedDeferredClaimBatched`);
* the node count is one more than the sum of the children's counts, one count for each child, each
  below `2^60` (`NodeCountHeld`). A child's count is then below its parent's
  (`NodeCountHeld.lt_of_mem`), so no node is its own descendant, and a tree of nodes whose counts
  are held has at most its root's count of nodes (`CountTree.size_le_count`).

**The guest is a parameter** (`SaltedGuest`): a leanISA program, the program of leanVM's cost
machine that decodes a node's seed, statement, node count, witness and children's counts from an
execution, and that decoder's size
bound and budget. Its correctness is one hypothesis (`SaltedGuest.KnowledgeSound`), of the form of
leanVM's `GuestKnowledgeSoundness`: on every valid execution of the guest on a public input of two
digests (`ValidExecution₂`: the first in memory words `0` and `1`, the second in words `2` and
`3`), the decoder outputs a decoding (`SaltedDecoding`: a seed, a statement, its node count, a witness and its
children's counts) whose seed is the second digest, whose statement's digest with its count under
that seed is the first digest, and whose witness and counts satisfy the salted node relation under
that seed, with at most `16` children (`ExplainsUnderSeed`). The relation gives the decoded statement the bytecode's
shape, as leanVM's does: the batching defers a claim at a point of `log₂ |bytecode|` coordinates,
or the zero point.
-/

namespace Recursion.Salted

open LeanVM LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Compile
open LeanVM.Protocol.KeccakHash LeanVM.Protocol.Verifier LeanVM.Node

@[expose] public section

/-! ## The salted node relation -/

/-- **What a node batches of its children under `seed`**, `childCounts` their node counts: each
child's statement digest with its count under `seed`, its proof's claim and its statement's
deferred claim. -/
def saltedChildClaims (seed : Digest) (children : List Child) (childCounts : List ℕ) :
    List ChildClaims :=
  (children.zip childCounts).map fun (child, count) ↦
    ⟨saltedStatementDigest seed child.statement count, child.freshClaim,
      child.statement.deferredClaim⟩

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

/-- **Every child is proven under `seed`**, `childCounts` their node counts: its deferred claim has
the bytecode's shape, and the deferring verifier with a second public digest, with the IV `seed`,
the keyed hash under `seed` and Keccak-f[1600], accepts its proof for the digest under `seed` of its
statement with its count, and `seed`. -/
def SaltedChildrenProven (bytecode : List K) (seed : Digest) (witness : NodeWitness)
    (childCounts : List ℕ) : Prop :=
  ∀ child count, (child, count) ∈ witness.children.zip childCounts →
    let publicInput := saltedStatementDigest seed child.statement count
    child.statement.deferredClaim.HasBytecodeShape bytecode ∧
      Id.run (SecondDigest.verifyDeferredWithHash₂ (m := Id) keccakF1600 (keyedHash seed) bytecode
        seed publicInput seed child.freshClaim child.proof) = true

/-- **The deferred claim batches the children's under `seed`**, `childCounts` their node counts:
without children, the bytecode at the zero point; with children, leanVM's batching program, run
over Keccak-f[1600] from the batching's seed call under `seed`, accepts the stream of the children's
claims under `seed` and the hints, with the statement's deferred claim as its outcome. -/
def SaltedDeferredClaimBatched (bytecode : List K) (seed : Digest) (statement : NodeStatement)
    (witness : NodeWitness) (childCounts : List ℕ) : Prop :=
  if witness.children = [] then statement.deferredClaim.HasZeroPoint bytecode
  else
    let children := saltedChildClaims seed witness.children childCounts
    let program := Guest.Batch.nodeBatchingProgram (· = statement.deferredClaim) bytecode children
    let stream := Guest.Batch.batchingStream children witness.batchingHints
    Id.run (runProof (m := Id) keccakF1600 program (batchingSeed seed) ⟨stream, []⟩) = true

/-- **The bound on a child's node count**: a child's count is below `2^60`, so one more than the
sum of `16` children's counts is below `2^64 - 1`, the order of `g`, in whose exponent the guest
adds them. -/
abbrev childCountBound : ℕ := 2 ^ 60

/-- **The node count is held**: a count for each child, each below `2^60`, and the node's count
one more than their sum. -/
def NodeCountHeld (nodeCount : ℕ) (witness : NodeWitness) (childCounts : List ℕ) : Prop :=
  childCounts.length = witness.children.length ∧ (∀ c ∈ childCounts, c < childCountBound) ∧
    nodeCount = childCounts.sum + 1

/-- **The salted node relation**, `nodeCount` the statement's node count and `childCounts` the
children's: leanVM's node relation with every hash and sponge under `seed`, and the node count one
more than the children's. The signatures verify at the unsalted Keccak-256. -/
def SaltedNodeRelation (bytecode : List K) (seed : Digest) (statement : NodeStatement)
    (nodeCount : ℕ) (witness : NodeWitness) (childCounts : List ℕ) : Prop :=
  SignatureClaimsHeld statement witness ∧ SaltedDaDigestHeld seed statement witness ∧
    SaltedChildrenProven bytecode seed witness childCounts ∧
    SaltedDeferredClaimBatched bytecode seed statement witness childCounts ∧
    NodeCountHeld nodeCount witness childCounts

/-! ## The node counts -/

/-- A member of a list of numbers is at most their sum. -/
theorem le_sum_of_mem : ∀ {l : List ℕ} {c : ℕ}, c ∈ l → c ≤ l.sum
  | _ :: _, _, .head _ => by simp only [List.sum_cons]; omega
  | _ :: _, _, .tail _ h => by simp only [List.sum_cons]; have := le_sum_of_mem h; omega

/-- Termwise, a sum of a map is at most another's. -/
theorem sum_map_le {α : Type} {l : List α} {f g : α → ℕ} (h : ∀ a ∈ l, f a ≤ g a) :
    (l.map f).sum ≤ (l.map g).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons]
    exact Nat.add_le_add (h a (by simp)) (ih fun b hb ↦ h b (by simp [hb]))

/-- **A child's count is below its parent's**: where the node count is held, every child's count
is smaller than the node's. -/
theorem NodeCountHeld.lt_of_mem {nodeCount : ℕ} {witness : NodeWitness} {childCounts : List ℕ}
    (h : NodeCountHeld nodeCount witness childCounts) {c : ℕ} (hc : c ∈ childCounts) :
    c < nodeCount := by
  have := le_sum_of_mem hc
  rw [h.2.2]
  omega

/-- **A node count's bytes fix it below the order of `g`**: two counts below `2^64 - 1` with the same
bytes are equal. -/
theorem nodeCountBytes_inj {a b : ℕ} (ha : a < 2 ^ 64 - 1) (hb : b < 2 ^ 64 - 1)
    (h : nodeCountBytes a = nodeCountBytes b) : a = b := by
  unfold nodeCountBytes K.toBytes at h
  have h8 := List.append_inj_left h (by simp only [wordBytes_length])
  exact gpow_injOn ha hb (K.lane_injective (wordBytes_injective h8))

/-- **A held count is below the order of `g`**, for at most `16` children: it is at most
`16 · (2^60 - 1) + 1`. -/
theorem NodeCountHeld.lt_order {nodeCount : ℕ} {witness : NodeWitness} {childCounts : List ℕ}
    (h : NodeCountHeld nodeCount witness childCounts) (hk : witness.children.length ≤ 16) :
    nodeCount < 2 ^ 64 - 1 := by
  obtain ⟨hl, hb, hn⟩ := h
  have hs : childCounts.sum ≤ childCounts.length * (childCountBound - 1) := by
    have := sum_map_le (l := childCounts) (f := id) (g := fun _ ↦ childCountBound - 1)
      (fun c hc ↦ Nat.le_sub_one_of_lt (hb c hc))
    simpa using this
  rw [hl] at hs
  have : witness.children.length * (childCountBound - 1) ≤ 16 * (childCountBound - 1) :=
    Nat.mul_le_mul_right _ hk
  unfold childCountBound at hs this
  omega

/-- **A tree of node counts**: a node's count and its subtrees. -/
inductive CountTree where
  /-- A node of count `count` with the subtrees `children`. -/
  | node (count : ℕ) (children : List CountTree)

/-- The count at a tree's root. -/
def CountTree.count : CountTree → ℕ
  | .node count _ => count

/-- The number of nodes of a tree. -/
def CountTree.size : CountTree → ℕ
  | .node _ children => (children.map CountTree.size).sum + 1

/-- **The counts of a tree are held**: at every node, the count is at least one more than the sum
of its subtrees' counts. A node whose count is held (`NodeCountHeld`), its subtrees' counts its
children's, satisfies it with equality. -/
inductive CountTree.Held : CountTree → Prop
  /-- A node's count is at least one more than its subtrees', whose counts are held. -/
  | node {count : ℕ} {children : List CountTree} :
      (children.map CountTree.count).sum + 1 ≤ count → (∀ t ∈ children, t.Held) →
        (CountTree.node count children).Held

/-- **A tree has at most its root's count of nodes**, where its counts are held. -/
theorem CountTree.size_le_count {t : CountTree} (h : t.Held) : t.size ≤ t.count := by
  induction h with
  | @node count children hc _ ih =>
    have hs := sum_map_le (f := CountTree.size) (g := CountTree.count) ih
    simp only [CountTree.size, CountTree.count]
    omega

/-! ## The salted guest -/

/-- **A salted guest**: a leanISA program, the decoder program of leanVM's cost machine that names
a node's salted decoding on an execution of it, and that decoder's size bound and budget on an
execution. -/
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

/-- **A salted decoding**: a seed, a statement, its node count, a witness and its children's node
counts. -/
structure SaltedDecoding where
  /-- The seed. -/
  seed : Digest
  /-- The statement. -/
  statement : NodeStatement
  /-- The statement's node count. -/
  nodeCount : ℕ
  /-- The witness. -/
  witness : NodeWitness
  /-- The children's node counts, in the children's order. -/
  childCounts : List ℕ

/-- A salted decoding's encoding: a constructor of tag `0`, its fields in order. -/
instance : Cost.MachineEncoding SaltedDecoding :=
  ⟨fun d ↦ .constructor 0 [Cost.encodeValue d.seed, Cost.encodeValue d.statement,
    Cost.encodeValue d.nodeCount, Cost.encodeValue d.witness, Cost.encodeValue d.childCounts]⟩

/-- **A decoding explains a public input of two digests under its seed**: the decoded seed is the
second digest, the digest under it of the decoded statement with its node count is the first, the
decoded witness and children's counts satisfy the salted node relation under it, and it has at most
`16` children. -/
def ExplainsUnderSeed (G : SaltedGuest) (input : SecondDigest.PublicInput₂)
    (decoding : SaltedDecoding) : Prop :=
  decoding.seed = publicInputDigest input.second ∧
    saltedStatementDigest decoding.seed decoding.statement decoding.nodeCount =
      publicInputDigest input.first ∧
    SaltedNodeRelation G.bytecode decoding.seed decoding.statement decoding.nodeCount
      decoding.witness decoding.childCounts ∧
    decoding.witness.children.length ≤ 16

/-- **Knowledge soundness of the salted guest**: on every valid execution of the guest program on a
public input of two digests, the decoder, of size at most its bound, run on the encoded program and
execution within its budget, outputs the encoding of a decoding that explains the input under its
seed, the second digest. -/
def SaltedGuest.KnowledgeSound (G : SaltedGuest) : Prop :=
  ∀ input (execution : Execution G.program), SecondDigest.ValidExecution₂ G.program input execution →
    ∃ decoding : SaltedDecoding,
      Cost.outputWithin G.decoder G.decoderSizeBound (G.decoderBudget execution)
          (Cost.encodeGuestWitnessDecoderInput G.program execution) =
        some (Cost.encodeValue decoding) ∧
      ExplainsUnderSeed G input decoding

end
end Recursion.Salted
