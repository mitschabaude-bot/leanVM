/-
  LeanVM.SaltedGuest.B1.Main.BatchK

  The salted node relation's batching (the batching program run from a seed state) is the
  transcript `batchFrom` from that state.
-/

module

public import LeanVM.SaltedGuest.B1.Main.AggK
public import LeanVM.Guest.Batch.Node

/-!
# The batching from a seed state

The deployed `Batch.batchRun_batchOf_iff` with `Node.batchSeed` replaced by any state `S`:
`batchRun_batchFrom_iff`: for a deferred claim `d` of the bytecode's shape, the batching program
`nodeBatchingProgram (· = d)`, run over Keccak-f[1600] from `S` on the stream of the children's
claims and the hints, accepts exactly where `batchFrom S` defers `d`. With `S = batchingSeed seed`
it is `SaltedDeferredClaimBatched`'s run.
-/

namespace LeanVM.SaltedGuest.B1.Main

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Compile LeanVM.Protocol.Verifier LeanVM.Node LeanVM.Guest.Batch

@[expose] public section

/-- The run of the batching from `S`, with the count's and the children's cells read. -/
theorem runD_batchFrom (S : KeccakState) (check : DeferredClaim → Prop) {bytecode : List K}
    {cs : List ChildClaims} (rest : List E) :
    runD (nodeBatchingProgram check bytecode cs)
        ⟨⟨S, []⟩, cellsBeforeChallenge cs ++ rest, [], []⟩ =
      runD (batchingAfterChildren check bytecode cs)
        ⟨obsAll ⟨S, []⟩ (cellsBeforeChallenge cs), rest, [], []⟩ := by
  rw [nodeBatchingProgram, runD_bind_of_runsTo (runsTo_readN' _ (cellsBeforeChallenge cs) rfl),
    ← List.nil_append rest, runD_bind_of_runsTo (runsTo_require rfl _)]
  rfl

/-- The batching program's run from `S` over Keccak-f[1600], as `runD`. -/
theorem runProof_batching (S : KeccakState) (prog : VerifierProgram Bool) (stream : List E) :
    Id.run (runProof (m := Id) keccakF1600 prog S ⟨stream, []⟩) =
      (match runD prog ⟨⟨S, []⟩, stream, [], []⟩ with
        | some (true, s) => s.stream.isEmpty && s.openings.isEmpty
        | _ => false) := by
  rw [runProof_eq_withHash, keccak256With_keccakF1600]
  rfl

theorem rounds_length_of_acceptsK {S : KeccakState} {check : DeferredClaim → Prop}
    {bytecode : List K} {cs : List ChildClaims} {h : BatchingHints}
    (hacc : Id.run (runProof (m := Id) keccakF1600 (nodeBatchingProgram check bytecode cs) S
      ⟨batchingStream cs h, []⟩) = true) :
    h.sumcheckMessages.length = Nat.log2 bytecode.length := by
  rw [runProof_batching] at hacc
  rw [batchStream_eq, runD_batchFrom S check, batchingAfterChildren,
    ← List.nil_append (List.flatMap _ _ ++ _), runD_bind_of_runsTo (runsTo_sampleE _)] at hacc
  generalize hR : runD (sumcheckRoundsProgram _ _ >>= _) _ = R at hacc
  rcases R with _ | ⟨_ | _, s⟩
  · simp at hacc
  · simp at hacc
  · simp only [Bool.and_eq_true, List.isEmpty_iff] at hacc
    obtain ⟨hle, x, sp', hx⟩ := runD_roundsProg_bind _ _ _ _ _ _ _ hR
    have h1 := runD_tail_accepts hx hacc.1
    simp only [List.length_drop, List.length_append, length_rounds_flat, List.length_singleton]
      at h1 hle
    omega

theorem batchRun_iff_of_roundsK {S : KeccakState} {bytecode : List K} {cs : List ChildClaims}
    {h : BatchingHints} {d : DeferredClaim}
    (hr : h.sumcheckMessages.length = Nat.log2 bytecode.length) :
    Id.run (runProof (m := Id) keccakF1600 (nodeBatchingProgram (· = d) bytecode cs) S
      ⟨batchingStream cs h, []⟩) = true ↔ batchFrom S cs h = some d := by
  rw [runProof_batching]
  rw [batchStream_eq, runD_batchFrom S _, batchingAfterChildren,
    ← List.nil_append (List.flatMap _ _ ++ _),
    runD_bind_of_runsTo (runsTo_sampleE _),
    runD_bind_of_runsTo (runsTo_roundsProg h.sumcheckMessages _ _ hr),
    ← List.append_nil [h.finalBytecodeValue],
    runD_bind_of_runsTo (runsTo_readE _ _), runD_require_true, batchFrom_eq]
  simp only [sqL]
  split_ifs <;> simp_all

/-- `batchFrom` defers a claim at a point of as many coordinates as the hints have rounds. -/
theorem batchFrom_point_length {S : KeccakState} {cs : List ChildClaims} {h : BatchingHints}
    {d : DeferredClaim} (hb : batchFrom S cs h = some d) :
    d.bytecodePoint.length = h.sumcheckMessages.length := by
  have e := hb
  rw [batchFrom_eq] at e
  simp only at e
  split_ifs at e
  have := congrArg (fun c : DeferredClaim ↦ c.bytecodePoint.length) (Option.some.inj e)
  simp only [rsRun_length] at this
  exact this.symm

/-- **The batching from `S` is `batchFrom S`**: for a deferred claim of the bytecode's shape, the
program run from `S` accepts the stream exactly where `batchFrom S` defers that claim. -/
theorem batchRun_batchFrom_iff {S : KeccakState} {bytecode : List K} {cs : List ChildClaims}
    {h : BatchingHints} {d : DeferredClaim} (hd : d.HasBytecodeShape bytecode) :
    Id.run (runProof (m := Id) keccakF1600 (nodeBatchingProgram (· = d) bytecode cs) S
      ⟨batchingStream cs h, []⟩) = true ↔ batchFrom S cs h = some d := by
  constructor
  · intro hacc
    exact (batchRun_iff_of_roundsK (rounds_length_of_acceptsK hacc)).mp hacc
  · intro hb
    have hr : h.sumcheckMessages.length = Nat.log2 bytecode.length := by
      rw [← batchFrom_point_length hb]
      exact hd
    exact (batchRun_iff_of_roundsK hr).mpr hb

end
end LeanVM.SaltedGuest.B1.Main
