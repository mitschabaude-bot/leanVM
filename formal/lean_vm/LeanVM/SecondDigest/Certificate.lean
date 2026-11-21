/-
  LeanVM.SecondDigest.Certificate

  The extractor of the verifier with a second public digest, and the statement of its
  round-by-round soundness certificate: every group's error at most `2^-128` after the proof of
  work's discount, and an accepted proof without an extracted stack that holds both digests has a
  doomed boundary.
-/

module

public import LeanVM.SecondDigest.Verifier
public import LeanVM.Protocol.EndToEnd.Sound.Theorem

/-!
# The certificate of the verifier with a second public digest

For a leanISA program `prog` and a public input of two digests `input`, write `P` for the
verifier program with a second public digest (`leanVmVerifierProgram₂`) at the bytecode and the
two digests, and `σ` for its seeding (`leanVmSeed₂`).

* `extractStack₂ prog input c π`: **the extractor**, leanVM's `extractStack` on the run of `P` from
  `σ`: from the extracted history of `π` under the cache `c`, the sizes and rate the history
  announced (leanVM's `announced`) and the stack's committed word (`firstWord`), a candidate of
  that word at level 0's Johnson threshold that satisfies the leanISA relation for the first
  digest (`M3Holds`) and holds the second digest (`StackHoldsSecondDigest`), if one exists. The
  candidate is a classical choice: the extractor specifies what is extracted.
* `Extracted₂ prog input c π`: the extractor returns admissible sizes and such a stack.
* `LeanVmCertificate₂`: **the certificate of the verifier with a second public digest.** For every
  program and public input of two digests there is a doom certificate of `P` (leanVM's `Cert`:
  doom kept by the prover's moves, every group of challenges from a doomed boundary escaping with
  probability at most the certificate's error, and no acceptance in doom) such that every group's
  error, discounted by the proof of work before it (`2^-min(b, 64)`), is at most `2^-128`, and a
  proof that the seeded verifier accepts under the answers of a cache, from which the extractor
  extracts nothing, has a boundary prefix of its extracted history at which the certificate's
  doom holds (leanVM's `DoomedRun`). It is the counterpart of leanVM's `leanVmCert_bound` and
  `doomed_of_not_extracted` for the present verifier.
-/

namespace Recursion.SecondDigest

open LeanVM LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Compile
open LeanVM.Protocol.Compile.Rom LeanVM.Protocol.Verifier LeanVM.Protocol.LeanIsa
open LeanVM.Protocol.EndToEnd LeanVM.Protocol.EndToEnd.Front LeanVM.Protocol.EndToEnd.Sound
open LeanVM.Protocol.KeccakHash
open scoped ENNReal

@[expose] public section

/-- The verifier program with a second public digest at a program's bytecode and the two digests
of `input`. -/
abbrev programOf₂ (prog : LeanIsaProgram) (input : PublicInput₂) : VerifierProgram Bool :=
  leanVmVerifierProgram₂ (bytecodeWords prog) (publicInputDigest input.first)
    (publicInputDigest input.second)

/-- The seeding of the verifier with a second public digest at a program's bytecode and the two
digests of `input`. -/
abbrev seedOf₂ (prog : LeanIsaProgram) (input : PublicInput₂) : Seed :=
  leanVmSeed₂ (bytecodeWords prog) (publicInputDigest input.first)
    (publicInputDigest input.second)

open Classical in
/-- **The extractor of the verifier with a second public digest.** From the cache `c` and the proof
`π`: the extracted history of the verifier's run from its seed, the sizes `s` and rate `ρ` it
announced, and the stack's committed word `W₀`; a candidate of `W₀` at level 0's Johnson threshold
that satisfies the leanISA relation for the first digest and holds the second digest, if one
exists. -/
noncomputable def extractStack₂ (prog : LeanIsaProgram) (input : PublicInput₂)
    (c : KeccakCalls.QueryCache) (π : Proof) : Option (Σ s : Sizes, Column (leanIsaμ prog s)) :=
  let hist := extractedHistory (fun x ↦ c (.inl x)) (fun s ↦ c (.inr s)) (seedOf₂ prog input)
    (programOf₂ prog input) π
  match announced prog hist, firstWord hist with
  | some (s, ρ), some W =>
    if hq : ∃ q ∈ Candidates (leanIsaμ prog s) ρ (thrOf (leanIsaμ prog s) ρ) W,
        M3Holds (leanIsaInstance prog s) input.first q ∧
          StackHoldsSecondDigest prog s input.second q then
      some ⟨s, hq.choose⟩
    else none
  | _, _ => none

/-- **The extractor succeeds**: it returns admissible sizes and a stack that satisfies the leanISA
relation for the first digest and holds the second digest. -/
def Extracted₂ (prog : LeanIsaProgram) (input : PublicInput₂) (c : KeccakCalls.QueryCache)
    (π : Proof) : Prop :=
  ∃ (s : Sizes) (q : Column (leanIsaμ prog s)), extractStack₂ prog input c π = some ⟨s, q⟩ ∧
    s.Admissible prog ∧ M3Holds (leanIsaInstance prog s) input.first q ∧
    StackHoldsSecondDigest prog s input.second q

/-- **The certificate of the verifier with a second public digest**: for every program and public
input of two digests, a doom certificate of the verifier program whose every group's error,
discounted by the proof of work before it, is at most `2^-128`, and at which every proof that the
seeded verifier accepts under a cache's answers, without an extracted stack that satisfies the
relation for the first digest and holds the second, has a doomed boundary prefix of its extracted
history. -/
def LeanVmCertificate₂ : Prop :=
  ∀ (prog : LeanIsaProgram) (input : PublicInput₂),
    let program := programOf₂ prog input
    let seed := seedOf₂ prog input
    ∃ cert : Cert program,
      (∀ history : List Ev,
        (2 : ℝ≥0∞)⁻¹ ^ min (grindBits history) 64 * cert.ε history ≤ (2 : ℝ≥0∞)⁻¹ ^ 128) ∧
      ∀ (cache : KeccakCalls.QueryCache) (proof : Proof),
        Rom.verify (fun x ↦ cache (.inl x)) (fun s ↦ cache (.inr s)) seed program proof =
            some true →
          ¬ Extracted₂ prog input cache proof → DoomedRun cert seed proof cache

end
end Recursion.SecondDigest
