/-
  LeanVM.SecondDigest.Verifier

  leanVM's verifier with a second public digest in memory words 2 and 3: the public input of two
  digests, the executions and stacks that hold the second, the public-input phase that binds both
  with one challenge, the verifier program and its deferring form, and the seeding that absorbs
  both digests.
-/

module

public import Statement.LeanVmVerifier
public import LeanVM.Protocol.LeanIsa
public import LeanVM.Protocol.Compile.Rom.Log

/-!
# The verifier with a second public digest

leanVM's verifier binds a public digest `p₀` to memory words `0` and `1` (`publicInputPhase`). The
definitions here add a second digest `p₁` in memory words `2` and `3`, bound by the same phase with
its one challenge:

* `PublicInput₂`: the two digests, each as leanVM's `PublicInput`, four `K` lanes.
* `HoldsSecondDigest second execution`: memory words `2` and `3` of an execution hold the second
  digest's two words, as `HoldsPublicInput` has the first in words `0` and `1`;
  `ValidExecution₂` is leanVM's `ValidExecution` for the first digest together with it.
* `MemoryHasFourWords layout`: the memory columns have at least two variables, so four cells.
* `publicInputPhase₂ layout publicInput second`: the layout condition, one challenge `r`, and for
  each memory limb column `ℓ` the present claim, the line through limb `ℓ` of the first digest's
  two halves at `(r, 0, …, 0)`, and a second claim, the line through limb `ℓ` of the second
  digest's two halves at `(r, 1, 0, …, 0)`, the point whose extension of a column is the line
  through its cells `2` and `3`.
* `verifyExecution₂`, `leanVmVerifierProgram₂`, `deferringVerifierProgram₂`: leanVM's
  `verifyExecution` with that phase in place of step 5, and its two programs.
* `seedInput₂ iv publicInput second`: the IV in lanes `0` to `3`, the first digest in lanes `4` to
  `7`, the second in lanes `8` to `11`, the other lanes zero; `spongeSeedWith₂`, `verifyWith₂`,
  `verifyDeferredWith₂`, `verifyDeferredWithHash₂`, `verifyDeferred₂` as leanVM's with it, and
  `leanVmSeed₂` the seeding of the random-oracle theorem (`Seed`).
* `StackHoldsSecondDigest prog s second q`: cells `2` and `3` of the three memory columns of a
  stack of the leanISA instance hold the second digest's limbs, as `PublicLinesHold` has the first
  digest's in cells `0` and `1` (`LeanIsa.publicLines`).
-/

namespace Recursion.SecondDigest

open LeanVM LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Compile
open LeanVM.Protocol.Verifier LeanVM.Protocol.KeccakHash

@[expose] public section

/-! ## The public input and the executions that hold it -/

/-- **A public input of two digests**: the first in memory words `0` and `1`, the second in memory
words `2` and `3`. -/
structure PublicInput₂ where
  /-- The digest in memory words `0` and `1`. -/
  first : PublicInput
  /-- The digest in memory words `2` and `3`. -/
  second : PublicInput
  deriving DecidableEq

/-- **The execution holds the second digest**: memory word `2` holds its lanes `0` and `1`, memory
word `3` its lanes `2` and `3`, as leanVM's words `0` and `1` hold the public input. -/
def HoldsSecondDigest {program : LeanIsaProgram} (second : PublicInput)
    (execution : Execution program) : Prop :=
  execution.memory.read (addressOfIndex 2) = some second.word0 ∧
    execution.memory.read (addressOfIndex 3) = some second.word1

/-- **A valid execution for a public input of two digests**: leanVM's valid execution for the
first digest, whose memory holds the second digest in words `2` and `3`. -/
def ValidExecution₂ (program : LeanIsaProgram) (input : PublicInput₂)
    (execution : Execution program) : Prop :=
  ValidExecution program input.first execution ∧ HoldsSecondDigest input.second execution

/-! ## The public-input phase -/

/-- **The memory has at least four words**: its columns have at least two variables. -/
def MemoryHasFourWords (layout : Layout) : Prop :=
  2 ≤ (layout.placement memory0).variableCount

instance (layout : Layout) : Decidable (MemoryHasFourWords layout) :=
  inferInstanceAs (Decidable (2 ≤ _))

/-- **The public-input phase for two digests**: the memory has at least four words; then a
challenge, and claims on the three memory columns: each limb's claim at `(challenge, 0, …, 0)`, the
line through that limb of the first digest's two halves at the challenge, and each limb's claim at
`(challenge, 1, 0, …, 0)`, the line through that limb of the second digest's two halves. The prover
sends nothing. -/
def publicInputPhase₂ (layout : Layout) (publicInput second : Digest) :
    VerifierProgram (List ColumnClaim) := do
  VerifierProgram.require (MemoryHasFourWords layout)
  let publicChallenge ← VerifierProgram.sampleChallenge
  let limbsOf := fun digest : Digest ↦
    let halves := digestHalves digest
    ([0, 1, 2] : List (Fin 3)).map fun limb ↦
      multilinearEval [ofK (halves.1.limb limb), ofK (halves.2.limb limb)] [publicChallenge]
  let memoryVariables := (layout.placement memory0).variableCount
  let publicPoint := publicChallenge :: List.replicate (memoryVariables - 1) 0
  let secondPoint := publicChallenge :: 1 :: List.replicate (memoryVariables - 2) 0
  return List.zipWith (fun column value ↦ ⟨column, publicPoint, value⟩)
      [memory0, memory1, memory2] (limbsOf publicInput) ++
    List.zipWith (fun column value ↦ ⟨column, secondPoint, value⟩)
      [memory0, memory1, memory2] (limbsOf second)

/-! ## The programs -/

/-- **`verify_execution` with a second public digest**: leanVM's `verifyExecution`, with the
public-input phase for two digests as its step 5. -/
def verifyExecution₂ (bytecodeValue : List K → List E → VerifierProgram E) (bytecode : List K)
    (publicInput second : Digest) : VerifierProgram Unit := do
  let (layout, logInverseRate) ← readAnnouncedSizes bytecode
  commitStack layout.stackLog logInverseRate
  let bus ← verifyBusBalance bytecodeValue layout
  let evaluations ← tablePhase layout bus
  let claims := bus.claims ++ tableColumnClaims evaluations
  let publicClaims ← publicInputPhase₂ layout publicInput second
  let claims := claims ++ publicClaims
  let (outputs, keccakPoint, keccakSlices) ← keccakPhase layout evaluations
  let claims := claims ++ outputs
  let (ringTarget, ringWeight) ← ringSwitch keccakPoint keccakSlices
  verifyStackedOpening layout.stackLog logInverseRate
    (ringSwitchClaim layout ringTarget ringWeight :: claims.filterMap (·.onStack layout))

/-- **The verifier program with a second public digest**, accepting where `verifyExecution₂`
returns. -/
def leanVmVerifierProgram₂ (bytecode : List K) (publicInput second : Digest) :
    VerifierProgram Bool := do
  verifyExecution₂ computedBytecodeValue bytecode publicInput second
  return true

/-- The verifier program with a second public digest, the fixed polynomial's value claimed by
`claim`. -/
def deferringVerifierProgram₂ (claim : BytecodeClaim) (bytecode : List K)
    (publicInput second : Digest) : VerifierProgram Bool := do
  verifyExecution₂ (claimedBytecodeValue claim) bytecode publicInput second
  return true

/-! ## The seed -/

/-- **The seed call's input for two digests**: the IV in lanes `0` to `3`, the first digest in
lanes `4` to `7`, the second in lanes `8` to `11`, the other lanes zero. -/
def seedInput₂ (iv publicInput second : Digest) : KeccakState :=
  Vector.ofFn fun i ↦
    if h : i.val < 4 then iv[i.val]
    else if h' : i.val < 8 then publicInput[i.val - 4]
    else if h'' : i.val < 12 then second[i.val - 8]
    else 0

section Hash

variable {m : Type → Type} [Monad m] (π : KeccakState → m KeccakState)

/-- The sponge's initial state over the permutation `π`, for two digests: `π` of the IV and the
two digests (`seedInput₂`). -/
def spongeSeedWith₂ (bytecode : List K) (publicInput second : Digest) : m KeccakState := do
  let fiatShamirIv ← fiatShamirIvWith π bytecode
  π (seedInput₂ fiatShamirIv publicInput second)

/-- The compiled verifier with a second public digest over the permutation `π`: the program run
on the proof from the seed. -/
def verifyWith₂ (bytecode : List K) (publicInput second : Digest) (proof : Proof) : m Bool := do
  let seed ← spongeSeedWith₂ π bytecode publicInput second
  runProof π (leanVmVerifierProgram₂ bytecode publicInput second) seed proof

/-- **The deferring verifier with a second public digest** over the permutation `π`: the IV
given, the fixed polynomial's value claimed by `claim`. -/
def verifyDeferredWith₂ (bytecode : List K) (iv publicInput second : Digest)
    (claim : BytecodeClaim) (proof : Proof) : m Bool := do
  let seed ← π (seedInput₂ iv publicInput second)
  runProof π (deferringVerifierProgram₂ claim bytecode publicInput second) seed proof

/-- **The deferring verifier with a second public digest** with the hash `H` and the permutation
`π`, as an aggregate runs it on a child's proof: the IV given, the fixed polynomial's value claimed
by `claim`. -/
def verifyDeferredWithHash₂ (H : Bytes → m Digest) (bytecode : List K)
    (iv publicInput second : Digest) (claim : BytecodeClaim) (proof : Proof) : m Bool := do
  let seed ← π (seedInput₂ iv publicInput second)
  runProofWithHash H π (deferringVerifierProgram₂ claim bytecode publicInput second) seed proof

end Hash

/-- The deferring verifier with a second public digest, over Keccak-f[1600]. -/
def verifyDeferred₂ (bytecode : List K) (iv publicInput second : Digest) (claim : BytecodeClaim)
    (proof : Proof) : Bool :=
  Id.run (verifyDeferredWith₂ (m := Id) keccakF1600 bytecode iv publicInput second claim proof)

/-- **The seeding with a second public digest**, for the random-oracle theorem: the IV, the hash
of the version tag and the bytecode, then the permutation of the IV and the two digests. -/
def leanVmSeed₂ (bytecode : List K) (publicInput second : Digest) : Rom.Seed where
  hs := [fun _ ↦ versionTag ++ bytecode.flatMap K.toBytes]
  fin ds := seedInput₂ (ds.getD 0 default) publicInput second

/-! ## The stacks that hold the second digest -/

/-- The second digest's three lines: memory column `ℓ` holds, at cells `2` and `3`, its limbs of
the second digest's two words, as `LeanIsa.publicLines` has the first digest's at cells `0` and
`1`. -/
def secondLines (second : PublicInput) : List (Fin 3 × K × K) :=
  [(0, second.lanes 0, second.lanes 2), (1, second.lanes 1, second.lanes 3), (2, 0, 0)]

/-- **A stack holds the second digest**: for each of the second digest's lines, cells `2` and `3`
of its memory column, read off the stack of the leanISA instance at sizes `s`, hold the line's two
values. -/
def StackHoldsSecondDigest (prog : LeanIsaProgram) (s : LeanIsa.Sizes) (second : PublicInput)
    (q : Column (leanIsaInstance prog s).μ) : Prop :=
  ∀ line ∈ secondLines second,
    let cells := (M3Instance.column (leanIsaInstance prog s) q
      (LeanIsa.memCol line.1.castSucc)).values
    cells[2]? = some line.2.1 ∧ cells[3]? = some line.2.2

end
end Recursion.SecondDigest
