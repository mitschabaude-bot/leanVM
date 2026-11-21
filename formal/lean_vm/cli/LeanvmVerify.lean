import LeanVM.Protocol.Verifier
import LeanVM.Salted.Verifier
import LeanVM.Cli.Common

/-!
# `leanvm-verify`: the verifier with a second public digest, under a seed, on a proof's files

The forms below, on the files the Rust prover writes (`scripts/export-verifier-fixtures-rust.sh`):
the bytecode, the seed (`seed.bin`, 32 bytes: the transcript's IV, the second public digest and
the key of the Merkle hashes), the public input and the proof. Each prints the verdict, and the
exit code is `0` on acceptance. `scripts/fuzz-verifier.py` compares them with the Rust verifier
(`scripts/rust-verifier-cli`, its forms) on mutated proofs.

* `lake exe leanvm-verify <bytecode> <seed> <public input> <stream> <merkle phases>`: the proof in
  its structured form, the Rust `Proof` (`crates/verifier/src/transcript.rs`): the scalars
  (`stream.bin`) and the phases of unpruned Merkle paths (`merkle_phases.bin`, `readPhasesFile`);
  runs `Salted.keyedVerify` (`LeanVM/Salted/Verifier.lean`: `leanVmVerifierProgram₂` under the
  keyed hash, compiled, on the program's bytecode words) on it.
* `lake exe leanvm-verify <bytecode> <seed> <public input> <proof wire>`: the proof's one wire
  encoding (`Proof::to_bytes`, `crates/fiat_shamir/src/wire.rs`, `proof.wire`), decoded with
  `Proof.fromBytesWithHash` under the keyed hash, a proof that does not decode rejected, as the
  Rust verifier does, then `Salted.keyedVerify` on the decoded proof.
* `lake exe leanvm-verify --deferred <bytecode> <seed> <public input> <claim> <stream> <merkle
  phases>`: the deferring verifier a node runs on a child (`Salted.keyedVerifyDeferred`,
  `verifyDeferredWithHash₂`), the bytecode's value claimed by `claim` (`claim.bin`: the point's
  coordinates, then the value, 24-byte elements, as `scripts/rust-verifier-cli --claim` writes it).
* `lake exe leanvm-verify --events <bytecode> <seed> <public input> <stream> <merkle phases>`: run
  the verifier on an honest structured proof and print, as one JSON object, the stream offset
  where each of its phases starts, where each commitment root and proof-of-work nonce is read, and
  the stream's length: the positions `scripts/fuzz-verifier.py` mutates. The phases are marked by
  a copy of `verifyExecution₂`'s and `verifyKeccak`'s sequencing that runs the statement's own
  sub-programs (`tracedExecution`); the roots and nonces come from a logging copy of the compiled
  reading (`runLog`), run both on that copy and on `leanVmVerifierProgram₂` itself, and the two
  logs must agree, so a change to the verifier's sequencing that the copy does not follow is
  reported rather than silently mutating the wrong positions.
-/

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Verifier
open LeanVM.Protocol.Compile
open LeanVM.Protocol.KeccakHash Recursion.Salted Recursion.SecondDigest

namespace LeanvmVerify

/-- **`merkle_phases.bin`**, the Rust `Vec<Vec<MerklePath>>` (`LeanVM.Cli.readPhases`); trailing
bytes or a short read are refused. -/
def readPhasesFile (b : ByteArray) : Option (List (List Opening)) := do
  let (phases, pos) ← LeanVM.Cli.readPhases b 0
  if pos = b.size then some phases else none

/-- **The verifier on the structured proof**: decode the bytecode, the seed, the public input,
the scalars and the phases, and run `keyedVerify`; anything that does not decode is rejected. -/
def verifyStructured (bytecode seed publicInput stream : List UInt8) (phases : ByteArray) : Bool :=
  match decodeWords bytecode, decodeDigest seed, decodeDigest publicInput, decodeScalars stream,
      readPhasesFile phases with
  | some words, some s, some digest, some scalars, some openings =>
    keyedVerify words s digest ⟨scalars, openings⟩
  | _, _, _, _, _ => false

/-- **The verifier on the wire**: decode the bytecode, the seed, the public input and the proof's
bytes (`Proof.fromBytesWithHash` under the keyed hash), and run `keyedVerify`; anything that does
not decode is rejected. -/
def verifyWire (bytecode seed publicInput proof : List UInt8) : Bool :=
  match decodeWords bytecode, decodeDigest seed, decodeDigest publicInput with
  | some words, some s, some digest =>
    match Id.run (Proof.fromBytesWithHash (m := Id) (keyedHash s) proof) with
    | some π => keyedVerify words s digest π
    | none => false
  | _, _, _ => false

/-- **The deferring verifier on the structured proof**: decode the bytecode, the seed, the public
input, the claim (its point's coordinates, then its value), the scalars and the phases, and run
`keyedVerifyDeferred`; anything that does not decode is rejected. -/
def verifyDeferredStructured (bytecode seed publicInput claim stream : List UInt8)
    (phases : ByteArray) : Bool :=
  match decodeWords bytecode, decodeDigest seed, decodeDigest publicInput, decodeScalars claim,
      decodeScalars stream, readPhasesFile phases with
  | some words, some s, some digest, some (c :: cs), some scalars, some openings =>
    let elements := c :: cs
    keyedVerifyDeferred words s digest ⟨elements.dropLast, elements.getLast (by simp)⟩
      ⟨scalars, openings⟩
  | _, _, _, _, _, _ => false

/-! ## The mutation positions of an honest proof (`--events`) -/

/-- Where an honest run reads what the fuzz mutates: each phase's first stream offset, each root's
and each proof-of-work nonce's (with its bits). -/
structure Log where
  phases : Array (String × ℕ) := #[]
  roots : Array ℕ := #[]
  nonces : Array (ℕ × ℕ) := #[]

/-- The compiled reading (`runWithHash` over the hash `H` and Keccak-f[1600]), logging the stream
offset of every root and nonce read; `total` is the whole stream's length. -/
def runLog {α : Type} (H : Bytes → Digest) (total : ℕ) : VerifierProgram α → VerifierProgramState → Log →
    Option (α × VerifierProgramState) × Log
  | .ret a, s, log => (some (a, s), log)
  | .fail, _, log => (none, log)
  | .read k, s, log => match s.stream with
    | [] => (none, log)
    | x :: xs =>
      let sp := Id.run (absorb keccakF1600 s.sponge x dsObserve)
      runLog H total (k x) { s with sponge := sp, stream := xs } log
  | .sample k, s, log =>
    let (c, sp) := Id.run (squeeze keccakF1600 s.sponge)
    runLog H total (k c) { s with sponge := sp } log
  | .grind bits k, s, log => match s.stream with
    | [] => (none, log)
    | n :: xs =>
      let log := { log with nonces := log.nonces.push (total - s.stream.length, bits) }
      let sp := Id.run (absorb keccakF1600 s.sponge n dsPowNonce)
      let (c, sp) := Id.run (squeeze keccakF1600 sp)
      if powOk bits c then runLog H total k { s with sponge := sp, stream := xs } log
      else (none, log)
  | .commit height width k, s, log => match s.stream with
    | x0 :: x1 :: xs =>
      let log := { log with roots := log.roots.push (total - s.stream.length) }
      let sp := Id.run (absorb keccakF1600 s.sponge x0 dsObserve)
      let sp := Id.run (absorb keccakF1600 sp x1 dsObserve)
      match digestFromHalves (x0, x1) with
      | some root => runLog H total k
          { s with sponge := sp, stream := xs, roots := s.roots ++ [(root, height, width)] } log
      | none => (none, log)
    | _ => (none, log)
  | .query i ps k, s, log => match s.roots[i]?, s.openings with
    | some (root, height, width), phase :: rest =>
      match Id.run (openPhaseWithHash (m := Id) H root height width ps phase) with
      | some rows => runLog H total (k rows) { s with openings := rest } log
      | none => (none, log)
    | _, _ => (none, log)

/-- A traced run: the state and the log, `none` once the proof is rejected. -/
abbrev Traced := StateT (VerifierProgramState × Log) Option

/-- Run one of the verifier's sub-programs. -/
def exec {α : Type} (H : Bytes → Digest) (total : ℕ) (program : VerifierProgram α) : Traced α :=
  fun (s, log) ↦
  match runLog H total program s log with
  | (some (a, s), log) => some (a, (s, log))
  | (none, _) => none

/-- Mark that the phase `name` starts here. -/
def mark (total : ℕ) (name : String) : Traced Unit := modify fun (s, log) ↦
  (s, { log with phases := log.phases.push (name, total - s.stream.length) })

/-- `verifyKeccak`'s sequencing, its layers and its two openings of `q_keccak` marked. -/
def tracedKeccak (H : Bytes → Digest) (total logSteps : ℕ) (inst output : List E) :
    Traced (List ColumnClaim × List E × List E) := do
  mark total "keccak"
  let packBits := logSteps - 4
  let rLow := inst.take 4
  let segment ← exec H total (VerifierProgram.sampleChallenges keccakSegmentBits)
  let lanePoint ← exec H total (VerifierProgram.sampleChallenges keccakLaneBits)
  let committed ← exec H total (if 1 < keccakSegments then VerifierProgram.readScalar else pure 0)
  let first := keccakFirstClaim inst segment lanePoint output committed
  let claim ← (List.range keccakDepth).foldlM (fun claim step ↦ do
    mark total "keccak-layer"
    exec H total (verifyKeccakLayer logSteps step claim)) first
  let outputs ← if 1 < keccakSegments then do
      mark total "keccak-open"
      let (slot, weights, value) ← exec H total (keccakOpen logSteps first 1 (keccakSegments - 1)
        committed)
      let word ← exec H total VerifierProgram.readScalar
      exec H total (VerifierProgram.require (weights.headD 0 * word = value))
      pure [(⟨qkeccak, rLow ++ inst.drop 4 ++ slot, word⟩ : ColumnClaim)]
    else pure []
  let (low, value) ← exec H total (sumcheck claim.value 3 (List.replicate 4 none))
  mark total "keccak-open"
  let (slot, weights, value) ← exec H total (keccakOpen logSteps claim 0 keccakSegments value)
  let slices ← exec H total (VerifierProgram.readScalars kBits)
  exec H total (VerifierProgram.require (multilinearEval claim.mu low * dot weights slices = value))
  return (outputs, low ++ claim.point.take packBits ++ slot, slices)

/-- `verifyExecution₂ computedBytecodeValue`'s sequencing, each phase marked where the fuzz cuts the
stream (the table sumcheck's end is the public input's start). -/
def tracedExecution (H : Bytes → Digest) (total : ℕ) (bytecode : List K)
    (publicInput second : Digest) : Traced Unit := do
  mark total "sizes"
  let (layout, logInverseRate) ← exec H total (readAnnouncedSizes bytecode)
  exec H total (commitStack layout.stackLog logInverseRate)
  mark total "bus"
  let bus ← exec H total (verifyBusBalance computedBytecodeValue layout)
  mark total "tables"
  let evaluations ← exec H total (tablePhase layout bus)
  mark total "public"
  let claims := bus.claims ++ tableColumnClaims evaluations
  let publicClaims ← exec H total (publicInputPhase₂ layout publicInput second)
  let claims := claims ++ publicClaims
  let (point, values) := evaluations.getD opKeccak ([], [])
  let (outputs, keccakPoint, keccakSlices) ← tracedKeccak H total
    (layout.tableLogHeights.getD opKeccak 0) point
    ((List.range 25).map fun lane ↦ values.getD (keccakOut + lane) 0)
  let claims := claims ++ outputs
  mark total "ring"
  let (ringTarget, ringWeight) ← exec H total (ringSwitch keccakPoint keccakSlices)
  mark total "whir"
  exec H total (verifyStackedOpening layout.stackLog logInverseRate
    (ringSwitchClaim layout ringTarget ringWeight :: claims.filterMap (·.onStack layout)))

/-- The JSON of the log: phases as `[name, offset]`, roots as offsets, nonces as `[offset, bits]`. -/
def Log.json (log : Log) (total : ℕ) : String :=
  let pair (a b : String) := s!"[{a}, {b}]"
  let list (xs : List String) := "[" ++ ", ".intercalate xs ++ "]"
  "{\"phase\": " ++ list (log.phases.toList.map fun (n, o) ↦ pair s!"\"{n}\"" (toString o)) ++
  ", \"root\": " ++ list (log.roots.toList.map toString) ++
  ", \"nonce\": " ++ list (log.nonces.toList.map fun (o, b) ↦ pair (toString o) (toString b)) ++
  s!", \"stream_length\": {total}}"

/-- **The mutation positions of an honest structured proof**, or an error: the traced run must
accept with the stream and openings consumed, and log the same roots and nonces as the verifier
program itself. -/
def events (bytecode seed publicInput stream : List UInt8) (phases : ByteArray) :
    Except String String :=
  match decodeWords bytecode, decodeDigest seed, decodeDigest publicInput, decodeScalars stream,
      readPhasesFile phases with
  | some words, some s, some digest, some scalars, some openings =>
    let total := scalars.length
    let H := keyedHash s
    let start : VerifierProgramState := ⟨⟨transcriptSeed s digest, []⟩, scalars, openings, []⟩
    let (whole, reference) :=
      runLog H total (leanVmVerifierProgram₂ words digest s) start {}
    match tracedExecution H total words digest s |>.run (start, {}), whole with
    | some ((), (st, log)), some (true, _) =>
      if !(st.stream.isEmpty && st.openings.isEmpty) then
        .error "the traced run leaves part of the proof unread"
      else if log.roots != reference.roots || log.nonces != reference.nonces then
        .error "the traced run's roots or nonces differ from the verifier's: \
          tracedExecution no longer follows verifyExecution₂"
      else .ok (log.json total)
    | _, _ => .error "the honest proof is rejected"
  | _, _, _, _, _ => .error "a file does not decode"

/-- The driver. -/
def main (args : List String) : IO UInt32 := do
  let read := fun (p : String) => do return (← IO.FS.readBinFile p).toList
  let verdict (ok : Bool) : IO UInt32 := do
    if ok then
      IO.println "verification succeeded"
      return 0
    else
      IO.println "verification failed"
      return 1
  match args with
  | ["--events", bytecode, seed, publicInput, stream, phases] =>
    match events (← read bytecode) (← read seed) (← read publicInput) (← read stream)
        (← IO.FS.readBinFile phases) with
    | .ok json =>
      IO.println json
      return 0
    | .error message =>
      IO.eprintln s!"leanvm-verify --events: {message}"
      return 1
  | ["--deferred", bytecode, seed, publicInput, claim, stream, phases] =>
    verdict (verifyDeferredStructured (← read bytecode) (← read seed) (← read publicInput)
      (← read claim) (← read stream) (← IO.FS.readBinFile phases))
  | [bytecode, seed, publicInput, stream, phases] =>
    verdict (verifyStructured (← read bytecode) (← read seed) (← read publicInput) (← read stream)
      (← IO.FS.readBinFile phases))
  | [bytecode, seed, publicInput, proof] =>
    verdict (verifyWire (← read bytecode) (← read seed) (← read publicInput) (← read proof))
  | _ =>
    IO.eprintln "usage: leanvm-verify <bytecode> <seed> <public input> (<stream> <merkle phases> | \
      <proof wire>) | --deferred <bytecode> <seed> <public input> <claim> <stream> \
      <merkle phases> | --events <bytecode> <seed> <public input> <stream> <merkle phases>"
    return 2

end LeanvmVerify

def main (args : List String) : IO UInt32 := LeanvmVerify.main args
