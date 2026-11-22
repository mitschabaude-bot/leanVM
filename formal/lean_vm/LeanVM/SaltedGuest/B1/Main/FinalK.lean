/-
  LeanVM.SaltedGuest.B1.Main.FinalK

  The salted `main`, soundly: a run of its body establishes the salted node relation of what its
  decoders read, under the seed of memory words `2` and `3`.
-/

module

public import LeanVM.SaltedGuest.B1.Main.HoldersK

/-!
# The salted `main`, soundly

`main_sound_CK`: on a memory image whose words `0`, `1` hold `D` and words `2`, `3` the seed `S`,
under a call relation that unfolds at a frame map and lies below the salted core IR's, given the
callees' contracts under `S` (`CalleesWCK`), a run of the salted `main`'s body gives, at the
deployed decoders read at `mainVal σ`, the statement of digest `D` under `S`
(`saltedStatementDigest`, `own_digestK`) and the salted node relation of the decoded witness: the
signatures held (`signatures_heldK`), the DA digest under `S` (`da_relK`), every child proven by
the deferring verifier with a second public digest (`kid_subK`), the deferred claim the leaf's zero
point or the batching from the batching's seed call under `S` (`batchRun_batchFrom_iff`); and at
most `16` children. As the deployed `Main.main_sound_C`.
-/

namespace LeanVM.SaltedGuest.B1.Main

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Guest.Value.Keccak LeanVM.Guest.B1 LeanVM.Guest.B1.Digest
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Node LeanVM.Guest.B1.Main LeanVM.SaltedGuest.B1 Recursion.Salted

@[expose] public section

variable {C : CallRel} {S : Digest} {key : E} {rd : Reader} {σ : Val} {Kr : ℕ → KidRec}

/-- `SaltedDaDigestHeld` from its two cases. -/
theorem saltedDaHeld_of {s : NodeStatement} {w : NodeWitness}
    (hsome : ∀ c m, w.daMatrix = some (c, m) →
      s.claims.daDigest = saltedDaClaimDigest S c ∧ OpensUnder S c.daRoot c.membershipChallenge m)
    (hnone : w.daMatrix = none → s.claims.daDigest = zeroDigest ∨
      ∃ child ∈ w.children, child.statement.claims.daDigest = s.claims.daDigest) :
    SaltedDaDigestHeld S s w := by
  unfold SaltedDaDigestHeld
  cases hd : w.daMatrix with
  | none => exact hnone hd
  | some p => exact hsome p.1 p.2 hd

/-- **A child's proof**: its fresh claim at `child_fresh · g^(24c)`, and the deferring verifier
with a second public digest, the keyed hash under `S`, accepts its proof for the decoded child's
statement's digest under `S`. -/
theorem kid_subK {bytecode : List K} {wX : List E → LeanXmss.Signature}
    {wS : E → Sphincs.Signature} {wD : List E → List E → LeanVM.Da.MatrixWitness}
    {wV : List E → Proof} {wA : List E → BatchingHints}
    (cw : CalleesWCK bytecode C rd (σ (.n 47)) key S wX wS wD wV wA)
    (MF : MainFactsK C rd σ S key) (hK : ∀ c < lg σ 6, KidOkK C rd σ S c (Kr c))
    {rx rs : ℕ → ℕ} (hW : Writers rd (σ (.n 45)) (segsOf σ Kr) (LXS σ) (LSS σ) (slOf σ Kr rx rs))
    {c : ℕ} (hc : c < lg σ 6) :
    (decKid rd σ wV c).freshClaim.bytecodePoint.length = bytecodeVars ∧
      ReadsAt rd (σ (.n 390) * gen ^ (24 * c)) (DeferredClaim.cells (decKid rd σ wV c).freshClaim) ∧
      Id.run (Recursion.SecondDigest.verifyDeferredWithHash₂ (m := Id) keccakF1600 (keyedHash S)
        bytecode S (saltedStatementDigest S (kidStmt rd σ c)) S (decKid rd σ wV c).freshClaim
        (decKid rd σ wV c).proof) = true := by
  have k := hK c hc
  obtain ⟨pi0, pi1, s0, s1, gsq, out, hargs, seed, pi, fresh, hs, hp, hfl, hfr, hvd⟩ :=
    cw.sub _ _ _ _ _ _ k.sub MF.exp MF.seedLoads.1 MF.seedLoads.2
  simp only [List.cons.injEq, and_true] at hargs
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ := hargs
  have hseed : S = seed := by
    rw [← digestOfCells_scalars S, ← digestOfCells_scalars seed, ← MF.seed, ← hs]
  subst hseed
  have hpi : pi = saltedStatementDigest S (kidStmt rd σ c) := by
    apply digestCells_inj
    rw [← kid_digestK MF hK hW hc, digestCells, ← hp]
  have hlen : (DeferredClaim.cells fresh).length = 24 := by
    simp [DeferredClaim.cells, hfl, bytecodeVars]
  have hfresh : (decKid rd σ wV c).freshClaim = fresh := by
    show fixedOfCells (readCells rd (σ (.n 390) * gen ^ (24 * c)) 24) = fresh
    rw [readCells_of_readsAt hfr hlen, fixedOfCells_cells hfl]
  have hargs : subArgs rd σ c = [(Kr c).p0, (Kr c).p1, σ (.n 26), σ (.n 27), σ (.n 28),
      σ (.n 390) * gen ^ (24 * c)] := by
    unfold subArgs
    rw [cellAt_eq_memAt, memAt_of_load k.pi0, memAt_of_load k.pi1]
  refine ⟨by rw [hfresh]; exact hfl, by rw [hfresh]; exact hfr, ?_⟩
  rw [hfresh, ← hpi]
  show Id.run (Recursion.SecondDigest.verifyDeferredWithHash₂ (m := Id) keccakF1600 (keyedHash S)
    bytecode S pi S fresh (wV (subArgs rd σ c))) = true
  rw [hargs]
  exact hvd

variable {bytecode : List K} {wX : List E → LeanXmss.Signature} {wS : E → Sphincs.Signature}
  {wD : List E → List E → LeanVM.Da.MatrixWitness} {wV : List E → Proof}
  {wA : List E → BatchingHints}

/-- **Every decoded child is proven under the seed.** -/
theorem kids_provenK {τ : Val} (hbl : bytecode.length = 2 ^ bytecodeVars)
    (cw : CalleesWCK bytecode C rd (τ (.n 47)) key S wX wS wD wV wA)
    (MF : MainFactsK C rd τ S key) (hK : ∀ c < lg τ 6, KidOkK C rd τ S c (Kr c))
    {rx rs : ℕ → ℕ} (hW : Writers rd (τ (.n 45)) (segsOf τ Kr) (LXS τ) (LSS τ) (slOf τ Kr rx rs)) :
    SaltedChildrenProven bytecode S (decWit τ rd wX wS wD wV wA) := by
  have hlog := log2_bytecode hbl
  intro ch hch
  obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hch
  rw [List.mem_range, nKids_eq] at hc
  refine ⟨?_, (kid_subK cw MF hK hW hc).2.2⟩
  show (deferOfCells (readCells rd (τ (.n 396) * gen ^ (24 * c)) 24)).bytecodePoint.length = _
  rw [deferOfCells_point (length_readCells _ _ _), hlog]

/-- **The decoded deferred claim is the leaf's zero point or the batching under the seed.** -/
theorem deferred_batchedK {τ : Val} (hbl : bytecode.length = 2 ^ bytecodeVars)
    (cw : CalleesWCK bytecode C rd (τ (.n 47)) key S wX wS wD wV wA)
    (MF : MainFactsK C rd τ S key) (hK : ∀ c < lg τ 6, KidOkK C rd τ S c (Kr c))
    {rx rs : ℕ → ℕ} (hW : Writers rd (τ (.n 45)) (segsOf τ Kr) (LXS τ) (LSS τ) (slOf τ Kr rx rs)) :
    SaltedDeferredClaimBatched bytecode S (decStmt τ rd) (decWit τ rd wX wS wD wV wA) := by
  have hlog := log2_bytecode hbl
  unfold SaltedDeferredClaimBatched
  by_cases h6 : lg τ 6 = 0
  · have hnil : (decWit τ rd wX wS wD wV wA).children = [] := by
      show (List.range (nKids τ)).map _ = []
      rw [nKids_eq, h6]; rfl
    rw [ite_pos' hnil]
    show (deferOfCells (readCells rd (τ (.n 417)) 24)).bytecodePoint = _
    rw [hlog]
    unfold deferOfCells
    simp only
    apply List.ext_getElem (by simp [length_readCells, bytecodeVars])
    intro i h1 h2
    simp only [List.getElem_take, List.getElem_replicate]
    simp only [List.length_replicate] at h2
    simp only [LeanVM.Guest.B1.Main.readCells, List.getElem_map, List.getElem_range]
    exact memAt_of_load (MF.leaf h6 i (by simp [bytecodeVars] at h2; omega))
  · have hne : (decWit τ rd wX wS wD wV wA).children ≠ [] := by
      show (List.range (nKids τ)).map _ ≠ []
      rw [nKids_eq]
      simp only [ne_eq, List.map_eq_nil_iff, List.range_eq_nil]
      exact h6
    rw [ite_neg' hne]
    have hagg := MF.agg h6
    have hs := MF.seed
    simp only [Prod.ext_iff] at hs
    rw [hs.1, hs.2] at hagg
    obtain ⟨out, hol, hor, hb⟩ := cw.agg _ _ _ _ _ hagg (lg τ 6) (by omega) MF.kids.2
      MF.kids.1
    have hdef : (decStmt τ rd).deferredClaim = out := by
      show deferOfCells (readCells rd (τ (.n 417)) 24) = out
      rw [readCells_of_readsAt hor (by simp [DeferredClaim.cells, hol, bytecodeVars]),
        deferOfCells_of hol]
    have hch : (decWit τ rd wX wS wD wV wA).children =
        (List.range (lg τ 6)).map (decKid rd τ wV) := by
      show (List.range (nKids τ)).map _ = _
      rw [nKids_eq]
    have hshape : out.HasBytecodeShape bytecode := by
      rw [DeferredClaim.HasBytecodeShape, hol, hlog]
    dsimp only
    rw [hdef, batchRun_batchFrom_iff hshape, hch]
    refine hb _ (by simp only [saltedChildClaims, List.length_map, List.length_range]) fun c hc => ?_
    simp only [saltedChildClaims, List.length_map, List.length_range] at hc
    simp only [saltedChildClaims, List.getElem_map, List.getElem_range]
    obtain ⟨hfl, hfr, -⟩ := kid_subK cw MF hK hW hc
    have k := hK c hc
    have hkd := kid_digestK MF hK hW hc
    simp only [digestCells, List.cons.injEq, and_true] at hkd
    refine ⟨hfl, ?_, ?_, ?_, hfr, ?_⟩
    · show (deferOfCells (readCells rd (τ (.n 396) * gen ^ (24 * c)) 24)).bytecodePoint.length = _
      exact deferOfCells_point (length_readCells _ _ _)
    · show LoadHolds rd (τ (.n 384)) (2 * c)
        (digestHalves (saltedStatementDigest S (kidStmt rd τ c))).1
      rw [← hkd.1]; exact k.pi0
    · show LoadHolds rd (τ (.n 384)) (2 * c + 1)
        (digestHalves (saltedStatementDigest S (kidStmt rd τ c))).2
      rw [← hkd.2]; exact k.pi1
    · show ReadsAt rd _ (deferOfCells (readCells rd (τ (.n 396) * gen ^ (24 * c)) 24)).cells
      rw [readCells_of_readsAt k.defreads k.deflen, deferOfCells_cells k.deflen]
      exact k.defreads

/-- **The salted `main`, soundly, its witness decoded, under a call relation `C`** that unfolds at
a frame map and lies below the salted core IR's, given the callees' contracts under the seed `S`
of memory words `2` and `3`. -/
theorem main_sound_CK {bytecode : List K} (hbl : bytecode.length = 2 ^ bytecodeVars)
    (hm : End.MemOk rd) {V : End.FrameMap} (hV : End.UnfoldsV rd C V)
    (hle : CallRel.Le C (SaltedGuest.coreProgram.Rel rd))
    (hS2 : LoadHolds rd 1 2 (digestHalves S).1) (hS3 : LoadHolds rd 1 3 (digestHalves S).2)
    {wX : List E → LeanXmss.Signature} {wS : E → Sphincs.Signature}
    {wD : List E → List E → LeanVM.Da.MatrixWitness} {wV : List E → Proof}
    {wA : List E → BatchingHints}
    (cw : CalleesWCK bytecode C rd (mainVal σ (.n 47)) (σ (.n 38)) S wX wS wD wV wA) {D : Digest}
    (hp0 : LoadHolds rd 1 0 (digestHalves D).1) (hp1 : LoadHolds rd 1 1 (digestHalves D).2)
    (hb : Stmt.HoldsList C rd σ (Fn.body LeanVM.SaltedGuest.Data.core0) False (fun rs => rs = [])) :
    saltedStatementDigest S (decStmt (mainVal σ) rd) = D ∧
      SaltedNodeRelation bytecode S (decStmt (mainVal σ) rd)
        (decWit (mainVal σ) rd wX wS wD wV wA) ∧
      (decWit (mainVal σ) rd wX wS wD wV wA).children.length ≤ 16 := by
  have MF := main_factsK hV hle hm hS2 hS3 hb
  generalize mainVal σ = τ at MF cw ⊢
  obtain ⟨Kr, hK⟩ : ∃ Kr : ℕ → KidRec, ∀ c < lg τ 6, KidOkK C rd τ S c (Kr c) := by
    have hex : ∀ c, c < lg τ 6 → ∃ k : KidRec, KidOkK C rd τ S c k := kid_recK hm MF
    choose! Kr hK using hex
    exact ⟨Kr, hK⟩
  obtain ⟨rx, rs, hrx, hrs⟩ := raw_slotsK MF
  have hW := writersK MF hK hrx hrs
  have hown := own_digestK MF
  -- the statement's digest
  have hdig : saltedStatementDigest S (decStmt τ rd) = D := by
    apply digestCells_inj
    rw [← hown, loadHolds_unique MF.pub.1 hp0, loadHolds_unique MF.pub.2 hp1]
    rfl
  refine ⟨hdig, ⟨signatures_heldK MF hK hW hm cw, ?_, kids_provenK hbl cw MF hK hW,
    deferred_batchedK hbl cw MF hK hW⟩, ?_⟩
  · -- the DA digest
    obtain ⟨hsome, hnone⟩ := da_relK MF cw
    exact saltedDaHeld_of hsome hnone
  · -- the children's count
    show ((List.range (nKids τ)).map (decKid rd τ wV)).length ≤ 16
    rw [List.length_map, List.length_range, nKids_eq]
    exact MF.kids.2

end
end LeanVM.SaltedGuest.B1.Main
