import LeanVM.Salted.Verifier
import LeanVM.Salted.Node
import LeanVM.Facts.NodeWith
import LeanVM.SaltedGuest.Program
import LeanVM.Guest.Code
import LeanVM.Guest.Word
import LeanVM.Guest.B1.Da.DualMath
import LeanVM.Cli.Common
import LeanVMTests.SaltedGuest.Manifest
import LeanVMTests.Salted.NodeVectors

/-!
# `salted-node-diff`: the salted node relation on real salted aggregations

`lake exe salted-node-diff <case>...` first checks what is slow in the interpreter of the salted
vectors `scripts/guest-export` writes:

* the seed of the manifest's salt (`Manifest.seed`, `Seed::of_salt`) is `seedOfSalt` of the salted
  guest program (`LeanVM.SaltedGuest.guestProgram`, its `2^23` bytecode words hashed): so the Lean
  program is the bytecode the Rust proves, every instruction, and `seedOfSalt` is the Rust's
  `seed_of_salt`; the node vectors' seed is that seed.

Then it reads the cases written by the exporter's ignored test `node_diff`
(`scripts/guest-export/src/export/node_diff.rs`, format `leanvm-salted-node 1`): a real salted
aggregation's seed, public input, statement `s` with its node count `n`, node witness `w` and
children's counts. For each case it checks

* the seed is the manifest's;
* the public input is the two words of `saltedStatementDigest seed s n` (`nodeInputAt`'s first
  digest);
* `w` holds `s` under the seed, `SaltedNodeRelation`'s parts, each computed: every child's
  deferred claim has the bytecode's shape and its proof is accepted by the deferring verifier with
  a second public digest under the keyed hash for its statement's salted digest with its count
  (`SaltedChildrenProven`, `keyedVerifyDeferred`); every raw signature verifies and every
  signature claim is a raw signature's or a child's (`SignatureClaimsHeld`); the DA digest is the
  keyed digest of the claim the directly checked matrix opens under the keyed hash, that claim's
  challenge the membership challenge of its root under the seed, or else zero or a child's
  (`SaltedDaDigestHeld`, `OpensUnder`, its commitment computed row by row,
  `LeanDa.commitCodewords_eq_commitCells`); and the batching, from the batching's seed call under
  the seed, defers the statement's claim (`SaltedDeferredClaimBatched`, its transcript as
  `LeanVM.Node.batchWith`), or a leaf defers the bytecode at zero; and the node count is one more
  than the children's, each below `2^60` (`NodeCountHeld`).

It prints each check and exits with `1` if any fails.
-/

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Compile LeanVM.Protocol.Verifier LeanVM.Node LeanVM.Guest LeanVM.Cli
open Recursion Recursion.Salted

namespace SaltedNodeDiff

/-! ## Reading a case -/

/-- A reader over the case's tokens. -/
abbrev R := ReaderT (Array String) (StateT Nat (Except String))

def tok : R String := do
  let i ← get
  let some t := (← read)[i]? | throw s!"the case ends at token {i}"
  set (i + 1)
  return t

def expect (t : String) : R Unit := do
  let u ← tok
  if u != t then throw s!"expected `{t}` at token {(← get) - 1}, found `{u}`"

def nat : R Nat := do
  let t ← tok
  let some n := t.toNat? | throw s!"`{t}` is not a number"
  return n

def hexOf (t : String) : Option Nat :=
  t.foldl (fun acc c => do return 16 * (← acc) + (← hexDigit? c)) (some 0)

def hex : R Nat := do
  let t ← tok
  let some n := hexOf t | throw s!"`{t}` is not hex"
  return n

def many {α : Type} (item : R α) : R (List α) := do
  let n ← nat
  (List.range n).mapM fun (_ : Unit) => item

def eR : R E := do return word (← hex) (← hex) (← hex)

def kR : R K := do return K.ofBits (← hex)

def bytesR : R (List UInt8) := do
  let t ← tok
  let cs := t.toList
  if cs.length % 2 != 0 then throw s!"`{t}` is not bytes"
  (List.range (cs.length / 2)).mapM fun i => do
    let some hi := hexDigit? cs[2 * i]! | throw s!"`{t}` is not bytes"
    let some lo := hexDigit? cs[2 * i + 1]! | throw s!"`{t}` is not bytes"
    return (16 * hi + lo).toUInt8

def digestR : R Digest := do return digestOfBytes (← bytesR)

def d128 : R (BitVec 128) := do return bitsLE 128 ((← bytesR).map (·.toNat))

/-- A key as its 32 bytes, split in halves, and a message: a leanXMSS key is its root then its
parameter, a leanSPHINCS key `PK.seed` then `PK.root` (`to_bytes`). -/
def claimR : R ((BitVec 128 × BitVec 128) × BitVec 256) := do
  let pk := (← bytesR).map (·.toNat)
  let m := (← bytesR).map (·.toNat)
  return ((bitsLE 128 (pk.take 16), bitsLE 128 (pk.drop 16)), bitsLE 256 m)

def deferR : R DeferredClaim := do
  expect "defer"
  return ⟨← many eR, ← eR⟩

/-- A statement and its node count. -/
def statementR : R (NodeStatement × ℕ) := do
  expect "xmss"
  let xmss ← many do let ((r, p), m) ← claimR; return ((⟨r, p⟩ : HashSig.PublicKey), m)
  expect "sphincs"
  let sphincs ← many do let ((p, r), m) ← claimR; return ((⟨p, r⟩ : Sphincs.PublicKey), m)
  expect "da"
  let da ← digestR
  let defer ← deferR
  expect "count"
  return (⟨⟨xmss, sphincs, da⟩, defer⟩, ← nat)

/-- A child and its node count. -/
def childR : R (Child × ℕ) := do
  expect "child"
  let (statement, count) ← statementR
  expect "fresh"
  let fresh : BytecodeClaim := ⟨← many eR, ← eR⟩
  expect "proof"
  let stream ← many eR
  let openings ← many do many do return (⟨← nat, ← many kR, ← many digestR⟩ : Opening)
  return (⟨statement, fresh, ⟨stream, openings⟩⟩, count)

def fn128 {n : Nat} (xs : List (BitVec 128)) : Fin n → BitVec 128 := fun i => xs.getD i 0

def xmssSigR : R LeanXmss.Signature := do
  let index ← nat
  let layer : R LeanXmss.LayerSignature := do
    return ⟨← d128, fn128 (← many d128), fn128 (← many d128)⟩
  let bottom ← layer
  let top ← layer
  return ⟨⟨index % 2 ^ 32, Nat.mod_lt _ (by decide)⟩, fun l => if l.val = 0 then bottom else top⟩

def sphincsSigR : R Sphincs.Signature := do
  let randomizer ← d128
  let fors ← (List.range Sphincs.forsTreeCount).mapM fun (_ : Unit) => do
    return (⟨← d128, fn128 (← many d128)⟩ : Sphincs.ForsTreeOpening)
  let layers ← (List.range Sphincs.layerCount).mapM fun (_ : Unit) => do
    return (BitVec.ofNat 32 (← nat), (← many d128), (← many d128))
  let layer := fun (l : Sphincs.Layer) =>
    let (counter, values, path) := layers.getD l.val (0, [], [])
    (⟨counter, fn128 values, fn128 path⟩ : Sphincs.LayerSignature l)
  return ⟨randomizer, fun c => fors.getD c ⟨0, fun _ => 0⟩, layer⟩

/-- A raw leanXMSS signature with its claim. -/
def rawXmssR : R (LeanXmssClaim × LeanXmss.Signature) := do
  let ((r, p), m) ← claimR
  return (((⟨r, p⟩ : HashSig.PublicKey), m), ← xmssSigR)

/-- A raw leanSPHINCS signature with its claim. -/
def rawSphincsR : R (LeanSphincsClaim × Sphincs.Signature) := do
  let ((p, r), m) ← claimR
  return (((⟨p, r⟩ : Sphincs.PublicKey), m), ← sphincsSigR)

def daWitnessR : R LeanVM.Da.MatrixWitness := do return ⟨← many (many kR)⟩

/-- The blob matrix checked directly, with the DA claim it opens (`NodeWitness.daMatrix`):
`direct`, the root, the membership challenge, the rows; or `none`. -/
def daR : R (Option (DaClaim × LeanVM.Da.MatrixWitness)) := do
  match ← tok with
  | "direct" =>
    let claim := DaClaim.mk (← digestR) (← eR)
    return some (claim, ← daWitnessR)
  | "none" => return none
  | t => throw s!"`{t}` is no DA witness"

/-- A case. -/
structure Case where
  name : String
  seed : Digest
  publicInput : List E
  statement : NodeStatement
  nodeCount : ℕ
  witness : NodeWitness
  childCounts : List ℕ

def caseR : R Case := do
  expect "leanvm-salted-node"; expect "1"
  expect "case"; let name ← tok
  expect "seed"; let seed ← digestR
  expect "public_input"; let publicInput ← many eR
  expect "statement"; let (statement, nodeCount) ← statementR
  expect "children"; let children ← many childR
  expect "raw_xmss"; let xmss ← many rawXmssR
  expect "raw_sphincs"; let sphincs ← many rawSphincsR
  expect "da_witness"; let da ← daR
  expect "batch"
  let pairs := fun (xs : List E) => (List.range (xs.length / 2)).map fun i => (xs[2 * i]!, xs[2 * i + 1]!)
  let bc ← many eR
  let stars ← many eR
  let hints : BatchingHints := ⟨pairs bc, stars.getD 0 0⟩
  expect "end"
  return ⟨name, seed, publicInput, statement, nodeCount,
    ⟨children.map (·.1), xmss, sphincs, da, hints⟩, children.map (·.2)⟩

def readCase (path : System.FilePath) : IO Case := do
  let text ← IO.FS.readFile path
  let toks := (((text.split Char.isWhitespace).toList.map (·.toString)).filter (· != "")).toArray
  match (caseR.run toks).run' 0 with
  | .ok c => return c
  | .error e => throw (IO.userError s!"{path}: {e}")

/-! ## The checks -/

/-- The salted guest program with its slots computed once. -/
def program : LeanIsaProgram := assembleArray LeanVM.SaltedGuest.Data.functions 19 (by decide)

example : program = LeanVM.SaltedGuest.guestProgram := assembleArray_eq _ _ _

/-- The salted guest's bytecode words, as the verifier reads them. -/
def bytecode : List K := LeanVM.bytecodeWords program

def digestEq (a b : Digest) : Bool := a.toList == b.toList

/-- `OpensUnder seed root z`, its dot products computed and its commitment computed row by row
(`LeanDa.commitCodewordsWithHash`, on codewords of `2^15` symbols the statement's
`commitCellsWithHash` of the matrix they form: `LeanDa.commitCodewords_eq_commitCells`), the dual
codeword of `z` as `dualAt` (`LeanDa.dualCodewordAt`: `Guest.B1.Da.dualAt_eq`). -/
def opensUnder (seed root : Digest) (z : E) (w : LeanVM.Da.MatrixWitness) : Bool :=
  let hash (x : List UInt8) : Vector UInt8 32 := (keyedHash seed x).toBytes
  let dual := (List.range (2 ^ LeanDa.logM)).map (LeanVM.Guest.B1.Da.dualAt z)
  1 ≤ w.rows.length && w.rows.length ≤ LeanDa.maxRows &&
    w.rows.all (·.length == 2 ^ LeanDa.logM) &&
    (LeanDa.commitCodewordsWithHash hash w.rows).toList == (LeanVM.Protocol.Digest.toBytes root).toList &&
    w.rows.all fun row => (dual.zip row).foldl (fun acc (v, x) => acc + v * ofK x) 0 == 0

/-- Every raw signature of a kind verifies, and every claim of the kind is a raw signature's or in
a child's list, each by name. -/
def held {α W : Type} [BEq α] (children : List Child) (kind : String) (claims : List α)
    (raws : List (α × W)) (verifies : α → W → Bool) (inChild : Child → α → Bool) :
    List (String × Bool) :=
  raws.zipIdx.map (fun ((claim, σ), i) => (s!"{kind} raw signature {i} verifies", verifies claim σ)) ++
    claims.zipIdx.map fun (claim, i) => (s!"{kind} claim {i} held",
      raws.any (·.1 == claim) || children.any (inChild · claim))

/-- The checks of a case, each by name. -/
def caseChecks (c : Case) : List (String × (Unit → Bool)) :=
  let s := c.statement
  let w := c.witness
  let seed := c.seed
  let shaped := fun (d : DeferredClaim) => d.bytecodePoint.length == Nat.log2 bytecode.length
  let input := PublicInput.ofDigest (saltedStatementDigest seed s c.nodeCount)
  [("the seed is the manifest's", fun (_ : Unit) => digestEq seed LeanVMTests.SaltedGuest.Manifest.seed),
    ("the public input is the statement's salted digest", fun (_ : Unit) =>
      [input.word0, input.word1] == c.publicInput),
    ("the statement's deferred claim is shaped", fun (_ : Unit) => shaped s.deferredClaim)] ++
  (w.children.zip c.childCounts).zipIdx.flatMap (fun ((ch, n), i) =>
    [(s!"child {i}'s deferred claim is shaped", fun (_ : Unit) => shaped ch.statement.deferredClaim),
      (s!"child {i}'s proof is accepted under the seed (keyedVerifyDeferred)", fun (_ : Unit) =>
        keyedVerifyDeferred bytecode seed (saltedStatementDigest seed ch.statement n) ch.freshClaim
          ch.proof)]) ++
  [("the node count is one more than the children's, each below 2^60", fun (_ : Unit) =>
      c.childCounts.length == w.children.length && c.childCounts.all (· < childCountBound) &&
        c.nodeCount == c.childCounts.sum + 1)] ++
  ((held w.children "leanXMSS" s.claims.xmss w.xmssSignatures (fun cl σ
      => LeanXmss.verifyWithKeccak cl.1 cl.2 σ)
    (fun ch cl => ch.statement.claims.xmss.any (· == cl)) ++
  held w.children "leanSPHINCS" s.claims.sphincs w.sphincsSignatures (fun cl σ
      => Sphincs.verifyWithKeccak cl.1 cl.2 σ)
    (fun ch cl => ch.statement.claims.sphincs.any (· == cl))).map fun (n, b) => (n, fun (_ : Unit) => b)) ++
  (match w.daMatrix with
    | some (cl, m) =>
      [("the directly checked claim's challenge is its root's membership challenge", fun (_ : Unit) =>
          cl.membershipChallenge == membershipChallenge seed cl.daRoot),
        ("the DA digest is the directly checked claim's keyed digest", fun (_ : Unit) =>
          digestEq s.claims.daDigest (saltedDaClaimDigest seed cl)),
        ("the directly checked matrix opens its claim under the keyed hash", fun (_ : Unit) =>
          opensUnder seed cl.daRoot cl.membershipChallenge m)]
    | none =>
      [("the DA digest is zero or a child's", fun (_ : Unit) => digestEq s.claims.daDigest zeroDigest ||
        w.children.any fun ch => digestEq ch.statement.claims.daDigest s.claims.daDigest)]) ++
  [if w.children = [] then
      ("the leaf defers the bytecode at zero", fun (_ : Unit) => s.deferredClaim.bytecodePoint.all (· == 0))
    else ("the batching from the seed's batching seed call defers the statement's claim", fun (_ : Unit) =>
      (Id.run (batchWith (m := Id) keccakF1600 (batchingSeed seed)
        (saltedChildClaims seed w.children c.childCounts) w.batchingHints)).map DeferredClaim.cells ==
          some s.deferredClaim.cells)]

/-- The vectors' checks. -/
def vectorChecks : List (String × (Unit → Bool)) := [
  ("seedOfSalt: the manifest's seed is seedOfSalt of the salted guest program", fun (_ : Unit) =>
    digestEq (seedOfSalt program LeanVMTests.SaltedGuest.Manifest.salt)
      LeanVMTests.SaltedGuest.Manifest.seed),
  ("seed: the node vectors' seed is the manifest's", fun (_ : Unit) =>
    digestEq LeanVMTests.Salted.NodeVectors.seed LeanVMTests.SaltedGuest.Manifest.seed)]

end SaltedNodeDiff

open SaltedNodeDiff

/-- Run the checks, printing each; whether all pass. -/
def runChecks (checks : List (String × (Unit → Bool))) : IO Bool := do
  let mut ok := true
  for (name, check) in checks do
    let start ← IO.monoMsNow
    let passed := check ()
    IO.println s!"  {name}: {if passed then "ok" else "FAILED"} ({(← IO.monoMsNow) - start} ms)"
    (← IO.getStdout).flush
    ok := ok && passed
  return ok

/-- The driver: `salted-node-diff <case>...`. -/
def main (paths : List String) : IO UInt32 := do
  IO.println "the salted vectors:"
  let mut ok ← runChecks vectorChecks
  for path in paths do
    let c ← readCase path
    IO.println s!"case {c.name} ({path}): {c.witness.children.length} children, \
      {c.statement.claims.xmss.length} leanXMSS, {c.statement.claims.sphincs.length} leanSPHINCS, \
      {if c.witness.daMatrix.isSome then "a blob matrix" else "no blob matrix"}"
    ok := (← runChecks (caseChecks c)) && ok
  return if ok then 0 else 1
