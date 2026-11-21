/-
  LeanVM.SaltedGuest.B1.VerifySub.Accept2

  The deferring verifier with a second public digest accepts, at a Merkle hash, a proof whose
  phases run as the salted `verify_sub`'s callees establish.
-/

module

public import LeanVM.Guest.B1.VerifySub.Accept
public import LeanVM.SecondDigest.Claims
public import LeanVM.SaltedGuest.B1.RunH

/-!
# Acceptance with a second public digest

`tablesSeg₂`: the deployed `Tables.tablesSeg` with the public-input phase for two digests
(`publicInputPhase₂`); `deferredFlat₂`, `deferred_eq₂`: the deferring verifier with a second
public digest, regrouped as the deployed `deferredFlat`. `deferred_accepts₂`: the deployed
`deferred_accepts` for it, at the Merkle hash `H`: from the seed of the two digests' sponge, if
the phases run one after the other (the ones that open nothing as the deployed `RunsTo`, which
hold at any hash, `RunsTo.withRootsH`; the opening at `H`), then
`verifyDeferredWithHash₂ keccakF1600 H` accepts the proof.
-/

namespace LeanVM.SaltedGuest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Whir LeanVM.Guest.B1.VerifySub LeanVM.SaltedGuest.B1 Recursion.SecondDigest

@[expose] public section

/-- The bus's rest, the tables' claims and the public-input phase for two digests. -/
def tablesSeg₂ (ev : (List K → List E → VerifierProgram E)) (layout : Layout)
    (publicInput second : Digest) (alphas : List E) (beta : E) (point treeValues : List E) :
    VerifierProgram (BusResult × List ColumnClaim) := do
  let bus ← Tables.busRest ev layout alphas beta point treeValues
  let claims ← tablePhaseClaims layout bus
  let publicClaims ← publicInputPhase₂ layout publicInput second
  return (bus, claims ++ publicClaims)

/-- **The deferring verifier's program with a second public digest, regrouped.** -/
def deferredFlat₂ (c : BytecodeClaim) (bytecode : List K) (pi second : Digest) : VerifierProgram Bool :=
  (readAnnouncedSizes bytecode).bind fun ls ↦
  (commitStack ls.1.stackLog ls.2).bind fun _ ↦
  (VerifierProgram.sampleChallenges busBits).bind fun alphas ↦
  VerifierProgram.sampleChallenge.bind fun beta ↦
  (Tables.gkrPhase (busLayout [0, ls.1.logMemory, ls.1.logBytecode] ls.1.push).depth).bind fun r ↦
  (tablesSeg₂ (claimedBytecodeValue c) ls.1 pi second alphas beta r.2.1 r.2.2).bind fun bc ↦
  (VerifierProgram.require ((lanesOf bc.2).map (·.column) = keccakOutputColumns ∧
    ∀ c ∈ lanesOf bc.2, c.point = ((lanesOf bc.2).headD default).point)).bind fun _ ↦
  (keccakSeg (ls.1.tableLogHeights.getD opKeccak 0) ((lanesOf bc.2).headD default).point
    ((lanesOf bc.2).map (·.value))).bind fun km ↦
  (VerifierProgram.sampleChallenges 5).bind fun chs ↦
  VerifierProgram.sampleChallenge.bind fun lam ↦
  let all := stackClaims ls.1 bc.2 km.1.1 km.1.2.1 km.1.2.2 (km.2 :: chs)
  (LeanVM.Guest.B1.Whir.whirOpen ls.1.stackLog ls.2 (dot (powers lam all.length) (all.map (·.2)))).bind fun w ↦
  (VerifierProgram.require (w.Accepts fun point ↦ dot (powers lam all.length) (all.map fun c ↦ c.1 point))).bind
    fun _ ↦ VerifierProgram.ret true

theorem deferred_eq₂ (c : BytecodeClaim) (bytecode : List K) (pi second : Digest) :
    deferringVerifierProgram₂ c bytecode pi second = deferredFlat₂ c bytecode pi second := by
  simp only [deferredProgram₂_eq, verifyExecutionClaims₂, deferredFlat₂, VerifierProgram.bind_eq,
    VerifierProgram.bind_assoc]
  refine congrArg _ (funext fun ls ↦ congrArg _ (funext fun _ ↦ ?_))
  rw [verifyBusBalance_split]
  simp only [tablesSeg₂, VerifierProgram.bind_assoc, VerifierProgram.bind_eq,
      VerifierProgram.pure_eq, VerifierProgram.ret_bind]
  refine congrArg _ (funext fun alphas ↦ congrArg _ (funext fun beta ↦ congrArg _ (funext fun r ↦
    congrArg _ (funext fun bus ↦ congrArg _ (funext fun cl ↦ congrArg _ (funext fun pc ↦ ?_))))))
  simp only [keccakPhaseClaims, lanesOf, VerifierProgram.bind_eq, VerifierProgram.pure_eq,
      VerifierProgram.bind_assoc, VerifierProgram.ret_bind]
  refine congrArg _ (funext fun _ ↦ ?_)
  simp only [keccakSeg, VerifierProgram.bind_eq, VerifierProgram.pure_eq,
      VerifierProgram.bind_assoc, VerifierProgram.ret_bind]
  refine congrArg _ (funext fun kr ↦ ?_)
  simp only [ringSwitch, VerifierProgram.bind_eq, VerifierProgram.pure_eq,
      VerifierProgram.bind_assoc, VerifierProgram.ret_bind]
  rw [show ringMapShifts.length = 5 + 1 from rfl, VerifierProgram.sampleChallenges]
  simp only [VerifierProgram.bind_eq, VerifierProgram.pure_eq, VerifierProgram.bind_assoc,
      VerifierProgram.ret_bind]
  refine congrArg _ (funext fun m ↦ congrArg _ (funext fun chs ↦ ?_))
  simp only [verifyStackedOpening, verifyWhir_eq_target, LeanVM.Guest.B1.Whir.verifyWhir_split, stackClaims, VerifierProgram.bind_eq,
    VerifierProgram.bind_assoc]
  refine congrArg _ (funext fun lam ↦ congrArg _ (funext fun w ↦ ?_))
  rfl

/-- **The deferring verifier with a second public digest accepts at the hash `H`**, given its phases'
runs. -/
theorem deferred_accepts₂ {H : Bytes → Digest} {bytecode : List K} {seed pi second : Digest}
    {c : BytecodeClaim} {s0 : Fs}
    (hs0 : s0.Carries ⟨keccakF1600 (Recursion.SecondDigest.seedInput₂ seed pi second), []⟩)
    {L : Layout} {lir : ℕ} {xs0 : List E} {s1 : Fs}
    (h1 : RunsTo (readAnnouncedSizes bytecode) s0 xs0 (L, lir) s1)
    {level : Whir.Level} {rest : List Whir.Level}
    (hcfg : Whir.ladder L.stackLog lir = some (level :: rest))
    {x0 x1 : E} {root : Digest} (hroot : digestFromHalves (x0, x1) = some root)
    {alphas : List E} {s3 : Fs}
    (h3 : ((s1.absorb x0 dsObserve).absorb x1 dsObserve).squeezeN busBits = (alphas, s3))
    {beta : E} {s4 : Fs} (h4 : s3.squeeze = (beta, s4))
    {xsG : List E} {r : E × List E × List E} {s5 : Fs}
    (h5 : RunsTo (Tables.gkrPhase (busLayout [0, L.logMemory, L.logBytecode] L.push).depth) s4 xsG
      r s5)
    {xsT : List E} {bc : BusResult × List ColumnClaim} {s6 : Fs}
    (h6 : RunsTo (tablesSeg₂ (claimedBytecodeValue c) L pi second alphas beta r.2.1 r.2.2) s5
        xsT bc s6)
    (h7 : (lanesOf bc.2).map (·.column) = keccakOutputColumns ∧
      ∀ c ∈ lanesOf bc.2, c.point = ((lanesOf bc.2).headD default).point)
    {xsK : List E} {km : (List ColumnClaim × List E × List E) × E} {s7 : Fs}
    (h8 : RunsTo (keccakSeg (L.tableLogHeights.getD opKeccak 0) ((lanesOf bc.2).headD default).point
      ((lanesOf bc.2).map (·.value))) s6 xsK km s7)
    {chs : List E} {s8 : Fs} (h9 : s7.squeezeN 5 = (chs, s8))
    {lam : E} {s9 : Fs} (h10 : s8.squeeze = (lam, s9))
    {xsW : List E} {os : List (List Opening)} {w : LeanVM.Guest.B1.Whir.WhirEnd} {s10 : Fs}
    {roots' : List (Digest × ℕ × ℕ)}
    (h11 : RunsWithH H (LeanVM.Guest.B1.Whir.whirOpen L.stackLog lir
      (dot (powers lam (stackClaims L bc.2 km.1.1 km.1.2.1 km.1.2.2 (km.2 :: chs)).length)
        ((stackClaims L bc.2 km.1.1 km.1.2.1 km.1.2.2 (km.2 :: chs)).map (·.2))))
      s9 xsW os [(root, LeanVM.Guest.B1.Whir.stackShape L.stackLog lir)] w s10 roots')
    (h12 : w.Accepts fun point ↦
      dot (powers lam (stackClaims L bc.2 km.1.1 km.1.2.1 km.1.2.2 (km.2 :: chs)).length)
        ((stackClaims L bc.2 km.1.1 km.1.2.1 km.1.2.2 (km.2 :: chs)).map fun c ↦ c.1 point)) :
    Id.run (Recursion.SecondDigest.verifyDeferredWithHash₂ (m := Id) keccakF1600 H bytecode seed pi
      second c ⟨xs0 ++ [x0, x1] ++ xsG ++ xsT ++ xsK ++ xsW, os⟩) = true := by
  have hrun0 : RunsWithH H (deferredFlat₂ c bytecode pi second) s0
      (xs0 ++ ([x0, x1] ++ ([] ++ ([] ++ (xsG ++ (xsT ++ ([] ++ (xsK ++ ([] ++ ([] ++ (xsW ++ ([] ++ ([])))))))))))))
      ([] ++ ([] ++ ([] ++ ([] ++ ([] ++ ([] ++ ([] ++ ([] ++ ([] ++ ([] ++ (os ++ ([] ++ ([]))))))))))))) [] true s10 roots' := by
      have hc : RunsWithH H (commitStack L.stackLog lir) s1 [x0, x1] [] []
          () ((s1.absorb x0 dsObserve).absorb x1 dsObserve) [(root, stackShape L.stackLog lir)] := by
        rw [commitStack_eq hcfg]
        exact runsWithH_commitP s1 x0 x1 hroot _ _ []
      refine RunsWithH.bind (RunsTo.withRootsH h1 []) ?_
      refine RunsWithH.bind hc ?_
      have e3 := runsTo_sampleN busBits ((s1.absorb x0 dsObserve).absorb x1 dsObserve)
      rw [h3] at e3
      refine RunsWithH.bind (RunsTo.withRootsH e3 _) ?_
      have e4 := runsTo_sampleE s3
      rw [h4] at e4
      refine RunsWithH.bind (RunsTo.withRootsH e4 _) ?_
      refine RunsWithH.bind (RunsTo.withRootsH h5 _) ?_
      refine RunsWithH.bind (RunsTo.withRootsH h6 _) ?_
      refine RunsWithH.bind (a := ()) (s1 := s6) (xs := []) (os1 := [])
        (r1 := [(root, stackShape L.stackLog lir)]) ?_ ?_
      · rw [require_true h7]
        exact RunsTo.withRootsH (runsTo_ret () s6) _
      refine RunsWithH.bind (RunsTo.withRootsH h8 _) ?_
      have e9 := runsTo_sampleN 5 s7
      rw [h9] at e9
      refine RunsWithH.bind (RunsTo.withRootsH e9 _) ?_
      have e10 := runsTo_sampleE s8
      rw [h10] at e10
      refine RunsWithH.bind (RunsTo.withRootsH e10 _) ?_
      refine RunsWithH.bind h11 ?_
      refine RunsWithH.bind (a := ()) (s1 := s10) (xs := []) (os1 := []) (r1 := roots') ?_ ?_
      · rw [require_true h12]
        exact runsWithH_ret () s10 roots'
      exact runsWithH_ret true s10 roots'
  have hrun : RunsWithH H (deferredFlat₂ c bytecode pi second) s0
      (xs0 ++ [x0, x1] ++ xsG ++ xsT ++ xsK ++ xsW) os [] true s10 roots' :=
    RunsWithH.of_eq hrun0 rfl (by simp) (by simp) rfl rfl rfl rfl
  obtain ⟨sp, -, hsp⟩ := hrun ⟨keccakF1600 (Recursion.SecondDigest.seedInput₂ seed pi second), []⟩ hs0 [] []
  simp only [List.append_nil] at hsp
  rw [← deferred_eq₂] at hsp
  simp only [Recursion.SecondDigest.verifyDeferredWithHash₂, Compile.runProofWithHash]
  simp only [runIdH] at hsp
  exact congrArg (fun o : Option (Bool × VerifierProgramState) ↦ match o with
    | some (true, s) => (s.stream.isEmpty && s.openings.isEmpty : Bool)
    | _ => false) hsp

end
end LeanVM.SaltedGuest.B1.VerifySub
