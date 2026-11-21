/-
  LeanVM.Salted.Hash

  The salt, the seed, the keyed hash, the three sponge seedings and the salted digests.
-/

module

public import LeanVM.SecondDigest.Verifier
public import LeanVM.Guest.Batch.Children
public import LeanVM.Facts.DaWith

/-!
# The salted functions

A salt (`Salt`) is a uniform 256-bit string published after the adversary's program is fixed.
Its seed for a guest program (`seedOfSalt`) is Keccak-256 of the salt, then the input of the
program's IV (`ivInput`: leanVM's version tag and the bytecode's words). The seed enters every hash
on data the
adversary chooses:

* **the keyed hash** under a seed `s` (`keyedHash s x`) is Keccak-256 of `s`, `240` zero bytes and
  `x` (`keyedInput`): the key and the zeros fill two blocks of `136` bytes, so the blocks of `x` sit
  at the positions they have in Keccak-256 of `x`. Merkle leaves and nodes of a proof, the DA cells
  and nodes, the claim lists and the DA claim are hashed with it;
* **a node's public input** under a seed (`nodeInputAt`) is two digests: its statement's digest
  under the seed and the seed. A transcript starts at Keccak-f[1600] of the seed's four words and
  the two digests' (`transcriptSeed`, `seedInput₂` with the seed as the IV). The verifier with a
  second public digest run with the hash answers `keyedAnswers` (the seed at the IV input, the
  keyed hash elsewhere) is that verifier with this IV and the keyed hash;
* **the batching** starts at Keccak-f[1600] of the seed's four words and the four words of the
  digest of leanVM's batching label (`batchingSeed`);
* **the membership challenge** of a DA root (`membershipChallenge`) is squeezed once from
  Keccak-f[1600] of the seed's four words, the root's four and the four words of the digest of
  leanDA's membership label;
* **the statement digest** under a seed (`saltedStatementDigest`) is leanVM's statement digest with
  the two claim-list digests keyed: Keccak-256 of the seed, the keyed digests of the two claim
  lists, the DA digest and the deferred claim's cells. The DA digest of a claim is the keyed digest
  of its preimage (`saltedDaClaimDigest`).

Every string these functions hash, except the seed's own input, starts with the seed's `32` bytes.
-/

namespace Recursion

open LeanVM LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Compile
open LeanVM.Protocol.KeccakHash LeanVM.Protocol.Verifier LeanVM.Node

@[expose] public section

/-! ## The IV's input and the DA claim's preimage -/

/-- The input the verifier hashes into its IV: the version tag, then the bytecode's words. -/
def ivInput (prog : LeanIsaProgram) : Bytes := versionTag ++ (bytecodeWords prog).flatMap K.toBytes

/-- The bytes a DA claim's digest hashes: the root, the challenge's three limbs and a zero word. -/
def daClaimPreimage (claim : DaClaim) : Bytes :=
  digestBytes claim.daRoot ++ E.toBytes claim.membershipChallenge ++ List.replicate 8 0

end
end Recursion

namespace Recursion.Salted

open LeanVM LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Compile
open LeanVM.Protocol.KeccakHash LeanVM.Protocol.Verifier LeanVM.Node

@[expose] public section

/-! ## The salt and the seed -/

/-- **A salt**: `256` bits, as four words of `64` bits. -/
abbrev Salt : Type := Digest

/-- **The seed of a salt** for the guest program `guest`: Keccak-256 of the salt's `32` bytes and
the input of the program's IV (the version tag, then the bytecode's words). -/
def seedOfSalt (guest : LeanIsaProgram) (salt : Salt) : Digest :=
  keccak256 (digestBytes salt ++ ivInput guest)

/-! ## The keyed hash -/

/-- **The input of the keyed hash** under the key `seed`: the key's `32` bytes, `240` zero bytes,
then the message. -/
def keyedInput (seed : Digest) (x : Bytes) : Bytes :=
  digestBytes seed ++ List.replicate 240 0 ++ x

/-- **The keyed hash** under the key `seed`: Keccak-256 of the keyed input. -/
def keyedHash (seed : Digest) (x : Bytes) : Digest := keccak256 (keyedInput seed x)

/-- **The hash answers under `seed`** for the guest program `guest`: the seed at the input of the
program's IV, and the keyed hash at every other input. The verifier run with these answers starts
its transcript at `transcriptSeed seed`, and hashes every Merkle leaf and node with the keyed
hash. -/
def keyedAnswers (guest : LeanIsaProgram) (seed : Digest) : Bytes → Option Digest :=
  fun x ↦ some (if x = ivInput guest then seed else keyedHash seed x)

/-! ## The three seedings -/

/-- **A transcript's seed call** under `seed`, for the digest `publicInput`: Keccak-f[1600] of the
seed's four words, the digest's four words, the seed's four words again and zeros. -/
def transcriptSeed (seed publicInput : Digest) : KeccakState :=
  keccakF1600 (SecondDigest.seedInput₂ seed publicInput seed)

/-- **The batching's seed call** under `seed`: Keccak-f[1600] of the seed's four words, the four
words of the Keccak-256 digest of leanVM's batching label, and zeros. -/
def batchingSeed (seed : Digest) : KeccakState :=
  keccakF1600 (seedInput seed (keccak256 batchingLabel))

/-- **The input of the membership seed call** under `seed` for the DA root `root`, with `label` the
Keccak-256 digest of leanDA's membership label: the seed's four words, the root's four words, the
label's four words, then zeros. -/
def membershipSeedInput (label seed root : Digest) : KeccakState :=
  Vector.ofFn fun i ↦
    if h : i.val < 4 then seed[i.val]
    else if h' : i.val < 8 then root[i.val - 4]
    else if h'' : i.val < 12 then label[i.val - 8]
    else 0

/-- **The membership challenge** of the DA root `root` under `seed`: the membership seed call, then
one squeeze of the sponge (a second Keccak-f[1600] call), its challenge. -/
def membershipChallenge (seed root : Digest) : E :=
  let label := keccak256 LeanDa.membershipLabel
  let state := keccakF1600 (membershipSeedInput label seed root)
  (Id.run (Compile.squeeze (m := Id) keccakF1600 ⟨state, []⟩)).1

/-! ## The salted digests -/

/-- **The preimage of a statement's digest under `seed`, from its claim lists' digests**: the seed's
`32` bytes, the digests `xmssDigest` and `sphincsDigest`, the DA digest, then the padded deferred
cells. -/
def statementPreimageFrom (seed xmssDigest sphincsDigest : Digest) (statement : NodeStatement) :
    Bytes :=
  let cells := (paddedDeferredClaimCells statement.deferredClaim).flatMap E.toBytes
  digestBytes seed ++ digestBytes xmssDigest ++ digestBytes sphincsDigest ++
    digestBytes statement.claims.daDigest ++ cells

/-- **The preimage of a statement's digest under `seed`**: the seed's `32` bytes, the keyed digests
of the leanXMSS and the leanSPHINCS claim lists, the DA digest, then the padded deferred cells. -/
def saltedStatementPreimage (seed : Digest) (statement : NodeStatement) : Bytes :=
  let xmssDigest := keyedHash seed (claimListPreimage xmssPublicKeyBytes statement.claims.xmss)
  let sphincsDigest :=
    keyedHash seed (claimListPreimage Sphincs.PublicKey.toBytes statement.claims.sphincs)
  statementPreimageFrom seed xmssDigest sphincsDigest statement

/-- **A statement's digest under `seed`**: Keccak-256 of its preimage. -/
def saltedStatementDigest (seed : Digest) (statement : NodeStatement) : Digest :=
  keccak256 (saltedStatementPreimage seed statement)

/-- **A node's public input under `seed`**: its statement's digest under `seed` in memory words
`0` and `1`, and `seed` in memory words `2` and `3`. -/
def nodeInputAt (seed : Digest) (statement : NodeStatement) : SecondDigest.PublicInput₂ :=
  ⟨PublicInput.ofDigest (saltedStatementDigest seed statement), PublicInput.ofDigest seed⟩

/-- **A DA claim's digest under `seed`**: the keyed digest of the root, the challenge's three limbs
and a zero word. -/
def saltedDaClaimDigest (seed : Digest) (claim : DaClaim) : Digest :=
  keyedHash seed (daClaimPreimage claim)

/-- **The DA claim the outer verifier derives** from the DA root `root` under `seed`: the root with
its membership challenge. -/
def derivedDaClaim (seed root : Digest) : DaClaim := ⟨root, membershipChallenge seed root⟩

/-- **The DA digest the outer verifier expects** under `seed`: the digest of the claim it derives
from the DA root, or the zero digest without one. -/
def saltedDaDigestOf (seed : Digest) : Option Digest → Digest
  | none => zeroDigest
  | some root => saltedDaClaimDigest seed (derivedDaClaim seed root)

/-- **A matrix opens the DA claim `⟨root, z⟩` under `seed`**: leanVM's `Opens` with the matrix's
root computed by the keyed hash: `1` to `1024` rows of `2^15` symbols, whose root under the keyed
hash is `root`, each orthogonal to the dual codeword of `z`. -/
def OpensUnder (seed root : Digest) (z : E) (matrix : Da.MatrixWitness) : Prop :=
  let hash (x : List UInt8) : Vector UInt8 32 := (keyedHash seed x).toBytes
  let rows := matrix.rows
  1 ≤ rows.length ∧ rows.length ≤ LeanDa.maxRows ∧ (∀ row ∈ rows, row.length = 2 ^ LeanDa.logM) ∧
    LeanDa.commitCellsWithHash hash (LeanDa.cellsOfRows rows) = root.toBytes ∧
    ∀ row ∈ rows, LeanDa.innerProduct (LeanDa.dualCodewordAt z) (fun b ↦ row.getD b 0) = 0

end
end Recursion.Salted
