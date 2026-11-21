/-
  LeanVM.SecondDigest.Claims

  The verifier with a second public digest on leanVM's claim-list form, its prover moves, the
  claims its public-input phase returns, and its bound on proofs of work.
-/

module

public import LeanVM.SecondDigest.Program
public import LeanVM.Protocol.EndToEnd.Sound.Moves
public import LeanVM.Protocol.EndToEnd.Sound.Returns
public import LeanVM.Protocol.EndToEnd.Sound.Runs

/-!
# The claim-list form of the verifier with a second public digest

* `verifyExecutionClaims₂`: leanVM's `verifyExecutionClaims` with the public-input phase for two
  digests; `verifyExecution₂_claims`: it is `verifyExecution₂`, by leanVM's argument for
  `verifyExecution_claims`, since the phase's claims are on the three memory columns
  (`allRet_publicInputPhase₂`); `leanVmProgram₂_eq`, `deferredProgram₂_eq`: the two programs on it.
* `movesOK_publicInputPhase₂`: the phase makes no prover move; `movesOK_leanVmProgram₂`: the
  program's moves are leanVM's commitments and proofs of work; `grindBits_le_of_reachable₂`.
* `retOK_publicInputPhase₂`: the phase returns at most six claims.
* `verifyExecution₂_ne_ret`: the program does not return without an event.
-/

namespace Recursion.SecondDigest

open LeanVM LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Compile
open LeanVM.Protocol.Verifier LeanVM.Protocol.Verifier.Claims LeanVM.Protocol.EndToEnd.Sound

@[expose] public section

/-- **`verify_execution` with a second public digest, on the claim list.** -/
def verifyExecutionClaims₂ (ev : List K → List E → VerifierProgram E) (bytecode : List K)
    (publicInput second : Digest) : VerifierProgram Unit := do
  let (layout, logInverseRate) ← readAnnouncedSizes bytecode
  commitStack layout.stackLog logInverseRate
  let bus ← verifyBusBalance ev layout
  let claims ← tablePhaseClaims layout bus
  let publicClaims ← publicInputPhase₂ layout publicInput second
  let claims := claims ++ publicClaims
  let (claims, keccakPoint, keccakSlices) ← keccakPhaseClaims layout claims
  let (ringTarget, ringWeight) ← ringSwitch keccakPoint keccakSlices
  verifyStackedOpening layout.stackLog logInverseRate
    (ringSwitchClaim layout ringTarget ringWeight :: claims.map (·.stackClaim layout))

/-- The phase's claims are on the three memory columns. -/
theorem allRet_publicInputPhase₂ (layout : Layout) (publicInput second : Digest) :
    AllRet (publicInputPhase₂ layout publicInput second)
      fun claims ↦ ∀ c ∈ claims, c.column ∈ [memory0, memory1, memory2] := by
  rw [publicInputPhase₂_eq]
  refine AllRet.bind (fun _ _ ↦ ?_) _ (allRet_true _)
  refine AllRet.bind (fun _ _ ↦ .ret fun c hc ↦ ?_) _ (allRet_true _)
  rcases List.mem_append.mp hc with hc | hc
  · exact zipWith_columns _ _ _ id c hc
  · exact zipWith_columns _ _ _ id c hc

/-- **The two forms are one program.** -/
theorem verifyExecution₂_claims (ev : List K → List E → VerifierProgram E) (bytecode : List K)
    (publicInput second : Digest) :
    verifyExecution₂ ev bytecode publicInput second =
      verifyExecutionClaims₂ ev bytecode publicInput second := by
  unfold verifyExecution₂ verifyExecutionClaims₂
  simp only [VerifierProgram.bind_eq]
  refine bind_congr (Q := fun x ↦ LayoutOk x.1) (fun x hl ↦ ?_) _ (allRet_readSizes bytecode)
  refine bind_congr (Q := fun _ ↦ True) (fun _ _ ↦ ?_) _ (allRet_true _)
  refine bind_congr (fun bus hb ↦ ?_) _ (allRet_verifyBusBalance ev x.1)
  rw [tablePhaseClaims_eq, VerifierProgram.bind_assoc]
  refine bind_congr (fun rows hr ↦ ?_) _ (allRet_tablePhase hl hb)
  rw [VerifierProgram.ret_bind]
  refine bind_congr (fun pc hpc ↦ ?_) _ (allRet_publicInputPhase₂ x.1 publicInput second)
  rw [keccakPhaseClaims_eq hb.2 hpc hr, VerifierProgram.bind_assoc]
  refine bind_congr (fun r hout ↦ ?_) _ (allRet_keccakPhase x.1 rows)
  rw [VerifierProgram.ret_bind]
  refine bind_congr (Q := fun _ ↦ True) (fun rs _ ↦ ?_) _ (allRet_true _)
  have hlt : ∀ c ∈ bus.claims ++ tableColumnClaims rows ++ pc ++ r.1, c.column < 165 := by
    intro c hc
    simp only [List.mem_append] at hc
    rcases hc with ((hc | hc) | hc) | hc
    · have := hb.2 c hc
      simp only [framework, memory0, memory1, memory2, memoryFinalCounters, bytecodeFinalCounters,
        List.mem_cons, List.not_mem_nil, or_false] at this
      omega
    · exact tableClaims_lt hr c hc
    · have := hpc c hc
      simp only [memory0, memory1, memory2, List.mem_cons, List.not_mem_nil, or_false] at this
      omega
    · rw [hout c hc]; decide
  have hfm := filterMap_onStack hl _ hlt
  rw [List.filter_append,
    (List.filter_eq_self (l := r.1)).mpr fun c hc ↦ by rw [hout c hc]; decide] at hfm
  exact congrArg (fun l ↦ verifyStackedOpening x.1.stackLog x.2 (_ :: l)) hfm

/-- The verifier program with a second public digest on the claim-list form. -/
theorem leanVmProgram₂_eq (bytecode : List K) (publicInput second : Digest) :
    leanVmVerifierProgram₂ bytecode publicInput second =
      (verifyExecutionClaims₂ computedBytecodeValue bytecode publicInput second).bind fun _ ↦
          VerifierProgram.ret true := by
  unfold leanVmVerifierProgram₂
  rw [verifyExecution₂_claims]
  rfl

/-- The deferring verifier program with a second public digest on the claim-list form. -/
theorem deferredProgram₂_eq (c : BytecodeClaim) (bytecode : List K) (publicInput second : Digest) :
    deferringVerifierProgram₂ c bytecode publicInput second =
      (verifyExecutionClaims₂ (claimedBytecodeValue c) bytecode publicInput second).bind fun _ ↦
          VerifierProgram.ret true := by
  unfold deferringVerifierProgram₂
  rw [verifyExecution₂_claims]
  rfl

/-! ## Moves and returns -/

/-- The public-input phase for two digests makes no prover move: a check and one challenge. -/
theorem movesOK_publicInputPhase₂ (layout : Layout) (publicInput second : Digest) :
    MovesOK (fun _ ↦ False) False (publicInputPhase₂ layout publicInput second) := by
  rw [publicInputPhase₂_eq]
  exact MovesOK.seq (MovesOK.require _) fun _ ↦ MovesOK.seq MovesOK.sampleE fun _ ↦
    MovesOK.pure _

/-- The public-input phase for two digests returns six claims. -/
theorem retOK_publicInputPhase₂ (layout : Layout) (publicInput second : Digest) :
    RetOK (fun claims : List ColumnClaim ↦ claims.length ≤ 6)
      (publicInputPhase₂ layout publicInput second) := by
  rw [publicInputPhase₂_eq]
  refine RetOK.bind_true fun _ ↦ RetOK.bind_true fun _ ↦ RetOK.ret ?_
  simp [EndToEnd.Front.pubClaims, secondClaims]

/-- `verify_execution` with a second public digest: commitments, and proofs of work of
`Whir.queryGrindingBits` bits. -/
theorem movesOK_verifyExecution₂ (bytecode : List K) (publicInput second : Digest) :
    MovesOK GrindOK True
      (verifyExecutionClaims₂ computedBytecodeValue bytecode publicInput second) := by
  refine MovesOK.seq (MovesOK.of_none (movesOK_readSizes bytecode)) fun p ↦ ?_
  obtain ⟨layout, logInverseRate⟩ := p
  refine MovesOK.seq ((movesOK_commitStack _ _).mono (fun _ h ↦ h.elim) id) fun _ ↦
    MovesOK.seq (MovesOK.of_none (movesOK_verifyBusBalance layout)) fun bus ↦
      MovesOK.seq (MovesOK.of_none (movesOK_tablePhase layout bus)) fun _ ↦
        MovesOK.seq (MovesOK.of_none (movesOK_publicInputPhase₂ layout publicInput second))
          fun _ ↦ MovesOK.seq (MovesOK.of_none (movesOK_keccakPhase _ _)) fun r ↦ ?_
  obtain ⟨claims, keccakPoint, keccakSlices⟩ := r
  refine MovesOK.seq (MovesOK.of_none (movesOK_ringSwitch keccakPoint keccakSlices)) fun r ↦ ?_
  obtain ⟨ringTarget, ringWeight⟩ := r
  exact movesOK_verifyStackedOpening _ _ _

/-- **The verifier program with a second public digest**: its commitments, and proofs of work of
`Whir.queryGrindingBits = 17` bits. -/
theorem movesOK_leanVmProgram₂ (bytecode : List K) (publicInput second : Digest) :
    MovesOK GrindOK True (leanVmVerifierProgram₂ bytecode publicInput second) := by
  rw [leanVmProgram₂_eq]
  exact MovesOK.seq (movesOK_verifyExecution₂ bytecode publicInput second) fun _ ↦
    MovesOK.pure _

/-- Along a reachable history of the program, the proofs of work have at most `64` bits. -/
theorem grindBits_le_of_reachable₂ (bytecode : List K) (publicInput second : Digest)
    {h : List Ev} (hh : (leanVmVerifierProgram₂ bytecode publicInput second).Reachable h) :
    grindBits h ≤ 64 :=
  ((movesOK_leanVmProgram₂ bytecode publicInput second).mono
    (fun _ hb ↦ hb.2.trans (by decide)) id).grindBits_le hh

/-- `verify_execution` with a second public digest does not return without an event. -/
theorem verifyExecution₂_ne_ret (bytecode : List K) (publicInput second : Digest) (u : Unit) :
    verifyExecutionClaims₂ computedBytecodeValue bytecode publicInput second ≠ .ret u := by
  intro h
  obtain ⟨a, ha, -⟩ := bind_eq_ret_iff h
  exact readSizes_ne_ret bytecode a ha

end
end Recursion.SecondDigest
