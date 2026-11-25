/-
  LeanVM.SaltedGuest.B1.Main.SoundK

  The salted `main`'s statement and its children's: their digests under the seed.
-/

module

public import LeanVM.SaltedGuest.B1.Main.WorldK

/-!
# The salted statements' digests

`own_digestK`: the cells `statement_digest` returns are those of the digest under the seed `S`
(`saltedStatementDigest`) of the decoded statement with the node's count (`nodeCountOf`), its claim
lists' digests the keyed ones; `kid_digestK`: child `c`'s public input is the digest under `S` of
its decoded statement with its count (`kidCount`). As the deployed `Main.own_digest`,
`Main.kid_digest`, with the keyed claim lists' preimages (`xmss_preimage`, `sphincs_preimage`) and
the salted statement's preimage from its parts (`saltedStatementDigest_parts`). The node's count's
cell is the running count after the children (`countRun_eqK`, `ownCount_eqK`), so the node's count
is one more than the children's (`nodeCountOf_eqK`).
-/

namespace LeanVM.SaltedGuest.B1.Main

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Guest.Value.Keccak LeanVM.Guest.B1 LeanVM.Guest.B1.Digest
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Node LeanVM.Guest.B1.Main LeanVM.SaltedGuest.B1 Recursion.Salted

@[expose] public section

variable {C : CallRel} {S : Digest} {key : E} {rd : Reader} {σ : Val} {K : ℕ → KidRec}

/-! ## Preimages -/

theorem xmss_preimage {p : E} {o : ℕ → ℕ} {n : ℕ} {cells : List E} (h : SlotsHold rd p o n cells) :
    claimListPreimage xmssPublicKeyBytes ((List.range n).map fun j => xmssAt rd p (o j)) =
      cellsBytes cells := by
  unfold claimListPreimage
  rw [← claims_digest Sig.xmssClaimOf (fun c : LeanXmssClaim => claimBytesOf c.1.root c.1.parameter c.2)
    (fun a b c d => claimBytes_cells a b c d) h]
  rfl

theorem sphincs_preimage {p : E} {o : ℕ → ℕ} {n : ℕ} {cells : List E}
    (h : SlotsHold rd p o n cells) :
    claimListPreimage Sphincs.PublicKey.toBytes ((List.range n).map fun j => sphincsAt rd p (o j)) =
      cellsBytes cells := by
  unfold claimListPreimage
  rw [← claims_digest Sig.sphincsClaimOf
    (fun c : LeanSphincsClaim => claimBytesOf c.1.publicSeed c.1.root c.2)
    (fun a b c d => claimBytes_cells a b c d) h]
  rfl

/-- **A statement's digest under `seed` from its parts**: the header cells' bytes, the keyed
claim lists' digests among them, the 24 deferred cells and the count's cell `g^n`. -/
theorem saltedStatementDigest_parts {seed : Digest} {s : NodeStatement} (n : ℕ)
    {s0 s1 x0 x1 y0 y1 d0 d1 : E} {defer : List E} (hseed : digestBytes seed = cellsBytes [s0, s1])
    (hx : digestBytes (keyedHash seed (claimListPreimage xmssPublicKeyBytes s.claims.xmss)) =
      cellsBytes [x0, x1])
    (hs : digestBytes (keyedHash seed (claimListPreimage Sphincs.PublicKey.toBytes s.claims.sphincs)) =
      cellsBytes [y0, y1])
    (hda : digestBytes s.claims.daDigest = cellsBytes [d0, d1])
    (hdef : s.deferredClaim.cells = defer) (hlen : defer.length = 24) :
    saltedStatementDigest seed s n =
      keccak256 (stmtBytes [s0, s1, x0, x1, y0, y1, d0, d1] defer ++ cellsBytes [gen ^ n]) := by
  unfold saltedStatementDigest saltedStatementPreimage statementPreimageFrom
    paddedDeferredClaimCells stmtBytes
  simp only
  rw [hseed, hx, hs, hda, hdef, hlen, cellsBytes_eight, nodeCountBytes_gen]
  simp

/-- The decoded seed is the seed. -/
theorem decSeed_eqK (MF : MainFactsK C rd σ S key) : decSeed σ = S := by
  unfold decSeed
  have h := MF.seed
  simp only [Prod.ext_iff] at h
  rw [h.1, h.2, digestOfCells_scalars]

/-! ## The statement's digest -/

/-- The DA digest at the slot `da_pick` holds the cells `statement_digest` reads. -/
theorem pick_cellsK (MF : MainFactsK C rd σ S key) :
    LoadHolds rd (σ (.n 364)) (2 * lg σ 406) (σ (.n 444)) ∧
      LoadHolds rd (σ (.n 364)) (2 * lg σ 406 + 1) (σ (.n 445)) := by
  obtain ⟨h0, h1⟩ := MF.dacells
  rw [MF.picked, loadHolds_gen_pow_iff] at h0 h1
  rw [Nat.add_zero] at h0
  exact ⟨h0, h1⟩

/-! ## The node's count -/

/-- **The running count** after `c` children is `g` to one more than the sum of their counts. -/
theorem countRun_eqK (MF : MainFactsK C rd σ S key) (hK : ∀ c < lg σ 6, KidOkK C rd σ S c (K c)) :
    ∀ c ≤ lg σ 6, LoadHolds rd (σ (.n 1001)) c
      (gen ^ (((List.range c).map (kidCount rd σ)).sum + 1)) := by
  intro c hc
  induction c with
  | zero => simpa using MF.countRun0
  | succ c ih =>
    obtain ⟨r, hr0, hr1⟩ := (hK c (by omega)).run
    have hr := loadHolds_unique hr0 (ih (by omega))
    rw [hr, ← pow_add] at hr1
    rw [List.range_succ, List.map_append, List.sum_append]
    simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hr1

/-- **The node's count's cell** is `g` to one more than the children's counts' sum. -/
theorem ownCount_eqK (MF : MainFactsK C rd σ S key) (hK : ∀ c < lg σ 6, KidOkK C rd σ S c (K c)) :
    σ (.n 1002) = gen ^ ((childCountsOf rd σ).sum + 1) := by
  have h := countRun_eqK MF hK (lg σ 6) le_rfl
  rw [loadHolds_unique MF.countRunN h]
  unfold childCountsOf
  rw [nKids_eq]

/-- **The node's count is one more than the children's**: at most `16` counts below `2^60`, so
their sum and one is below `2^64 - 1` and the logarithm of `g` to it. -/
theorem nodeCountOf_eqK (MF : MainFactsK C rd σ S key)
    (hK : ∀ c < lg σ 6, KidOkK C rd σ S c (K c)) :
    nodeCountOf σ = (childCountsOf rd σ).sum + 1 := by
  have hs := sum_le_length_mul (l := childCountsOf rd σ) (B := 2 ^ 60 - 1) fun x hx ↦ by
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hx
    rw [List.mem_range, nKids_eq] at hc
    exact Nat.le_sub_one_of_lt (hK c hc).count.1
  have hl : (childCountsOf rd σ).length ≤ 16 := by
    simp only [childCountsOf, List.length_map, List.length_range, nKids_eq]
    exact MF.kids.2
  have : (childCountsOf rd σ).length * (2 ^ 60 - 1) ≤ 16 * (2 ^ 60 - 1) :=
    Nat.mul_le_mul_right _ hl
  unfold nodeCountOf
  rw [ownCount_eqK MF hK, cellLog_gen (by omega)]

/-- **The decoded statement's digest under the seed**, with the node's count, is the one
`statement_digest` computes. -/
theorem own_digestK (MF : MainFactsK C rd σ S key) (hK : ∀ c < lg σ 6, KidOkK C rd σ S c (K c)) :
    [σ (.n 446), σ (.n 447)] =
      digestCells (saltedStatementDigest S (decStmt σ rd) (nodeCountOf σ)) := by
  obtain ⟨cells, hlen, hreads, -, hrets⟩ := Digest.statement_digest_soundK rd _ _ MF.stmt
  obtain ⟨cx, hlx, hrx, -, hdx⟩ := MF.xlist
  obtain ⟨cs, hls, hrs, -, hds⟩ := MF.slist
  have hx := xmss_preimage (o := id) (slotsHold_of_readsAt hrx hlx)
  have hs := sphincs_preimage (o := id) (slotsHold_of_readsAt hrs hls)
  obtain ⟨p0, p1⟩ := pick_cellsK MF
  have eX : (decStmt σ rd).claims.xmss = (List.range (lg σ 0)).map (xmssAt rd (σ (.n 31))) := by
    unfold decStmt; simp only [gLog_lg]
  have eS : (decStmt σ rd).claims.sphincs =
      (List.range (lg σ 3)).map (sphincsAt rd (σ (.n 34))) := by
    unfold decStmt; simp only [gLog_lg]
  have eD : (decStmt σ rd).claims.daDigest = daDigestAt rd σ (lg σ 406) := by
    unfold decStmt; simp only [gLog_lg]
  have hdef : (decStmt σ rd).deferredClaim.cells = cells := by
    unfold decStmt; simp only; rw [readCells_of_readsAt hreads hlen]; exact deferOfCells_cells hlen
  have hxd : digestBytes (keyedHash S (claimListPreimage xmssPublicKeyBytes (decStmt σ rd).claims.xmss)) =
      cellsBytes [σ (.n 35), σ (.n 36)] := by
    rw [eX]; erw [hx]; exact digestBytes_of_cells hdx
  have hsd : digestBytes (keyedHash S
      (claimListPreimage Sphincs.PublicKey.toBytes (decStmt σ rd).claims.sphincs)) =
      cellsBytes [σ (.n 37), σ (.n 38)] := by
    rw [eS]; erw [hs]; exact digestBytes_of_cells hds
  have hda : digestBytes (decStmt σ rd).claims.daDigest = cellsBytes [σ (.n 444), σ (.n 445)] := by
    rw [eD]; exact (daDigestAt_of_loads p0 p1).2
  have hseed : digestBytes S = cellsBytes [σ (.n 26), σ (.n 27)] := by
    rw [← decSeed_eqK MF]; exact digestBytes_decSeed σ
  rw [hrets, ownCount_eqK MF hK, nodeCountOf_eqK MF hK,
    saltedStatementDigest_parts _ hseed hxd hsd hda hdef hlen]

/-! ## A child's statement's digest -/

/-- **Child `c`'s statement's digest under the seed**, with its count, is the one its
`statement_digest` call computes. -/
theorem kid_digestK (MF : MainFactsK C rd σ S key) (hK : ∀ c < lg σ 6, KidOkK C rd σ S c (K c))
    {rx rs : ℕ → ℕ} (hW : Writers rd (σ (.n 45)) (segsOf σ K) (LXS σ) (LSS σ) (slOf σ K rx rs))
    {c : ℕ} (hc : c < lg σ 6) :
    [(K c).p0, (K c).p1] =
      digestCells (saltedStatementDigest S (kidStmt rd σ c) (kidCount rd σ c)) := by
  have k := hK c hc
  rw [kidStmt_eqK MF hK hW hc]
  have hx := xmss_preimage (o := (K c).ox) (n := (K c).ex) (p := σ (.n 31))
    ⟨k.xlen, fun j hj i hi => (k.xrec j hj).2.2 i hi⟩
  have hs := sphincs_preimage (o := (K c).os) (n := (K c).es) (p := σ (.n 34))
    ⟨k.slen, fun j hj i hi => (k.srec j hj).2.2 i hi⟩
  have hxd : digestBytes (keyedHash S (claimListPreimage xmssPublicKeyBytes
      ((List.range (K c).ex).map fun j => xmssAt rd (σ (.n 31)) ((K c).ox j)))) =
      cellsBytes [(K c).cx0, (K c).cx1] := by
    rw [hx]; exact digestBytes_of_cells k.xdig
  have hsd : digestBytes (keyedHash S (claimListPreimage Sphincs.PublicKey.toBytes
      ((List.range (K c).es).map fun j => sphincsAt rd (σ (.n 34)) ((K c).os j)))) =
      cellsBytes [(K c).cs0, (K c).cs1] := by
    rw [hs]; exact digestBytes_of_cells k.sdig
  have hda := (daDigestAt_of_loads k.da0 k.da1).2
  have hdef :
      (deferOfCells (readCells rd (σ (.n 396) * gen ^ (24 * c)) 24)).cells = (K c).defer := by
    rw [readCells_of_readsAt k.defreads k.deflen]; exact deferOfCells_cells k.deflen
  have hseed : digestBytes S = cellsBytes [σ (.n 26), σ (.n 27)] := by
    rw [← decSeed_eqK MF]; exact digestBytes_decSeed σ
  have hst := saltedStatementDigest_parts (seed := S) (kidCount rd σ c)
    (s := ⟨⟨(List.range (K c).ex).map fun j => xmssAt rd (σ (.n 31)) ((K c).ox j),
        (List.range (K c).es).map fun j => sphincsAt rd (σ (.n 34)) ((K c).os j),
        daDigestAt rd σ c⟩,
       deferOfCells (readCells rd (σ (.n 396) * gen ^ (24 * c)) 24)⟩)
    hseed hxd hsd hda hdef k.deflen
  rw [k.pdig, hst]

end
end LeanVM.SaltedGuest.B1.Main
