/-
  LeanVM.SaltedGuest.B1.Main.SoundK

  The salted `main`'s statement and its children's: their digests under the seed.
-/

module

public import LeanVM.SaltedGuest.B1.Main.WorldK

/-!
# The salted statements' digests

`own_digestK`: the cells `statement_digest` returns are those of the decoded statement's digest
under the seed `S` (`saltedStatementDigest`), its claim lists' digests the keyed ones;
`kid_digestK`: child `c`'s public input is its decoded statement's digest under `S`. As the
deployed `Main.own_digest`, `Main.kid_digest`, with the keyed claim lists' preimages
(`xmss_preimage`, `sphincs_preimage`) and the salted statement's preimage from its parts
(`saltedStatementDigest_parts`).
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
claim lists' digests among them, and the 24 deferred cells. -/
theorem saltedStatementDigest_parts {seed : Digest} {s : NodeStatement}
    {s0 s1 x0 x1 y0 y1 d0 d1 : E} {defer : List E} (hseed : digestBytes seed = cellsBytes [s0, s1])
    (hx : digestBytes (keyedHash seed (claimListPreimage xmssPublicKeyBytes s.claims.xmss)) =
      cellsBytes [x0, x1])
    (hs : digestBytes (keyedHash seed (claimListPreimage Sphincs.PublicKey.toBytes s.claims.sphincs)) =
      cellsBytes [y0, y1])
    (hda : digestBytes s.claims.daDigest = cellsBytes [d0, d1])
    (hdef : s.deferredClaim.cells = defer) (hlen : defer.length = 24) :
    saltedStatementDigest seed s = keccak256 (stmtBytes [s0, s1, x0, x1, y0, y1, d0, d1] defer) := by
  unfold saltedStatementDigest saltedStatementPreimage statementPreimageFrom
    paddedDeferredClaimCells stmtBytes
  simp only
  rw [hseed, hx, hs, hda, hdef, hlen, cellsBytes_eight]
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

/-- **The decoded statement's digest under the seed** is the one `statement_digest` computes. -/
theorem own_digestK (MF : MainFactsK C rd σ S key) :
    [σ (.n 446), σ (.n 447)] = digestCells (saltedStatementDigest S (decStmt σ rd)) := by
  obtain ⟨cells, hlen, hreads, -, hrets⟩ := statement_digest_sound rd _ _ MF.stmt
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
  rw [hrets, saltedStatementDigest_parts hseed hxd hsd hda hdef hlen]

/-! ## A child's statement's digest -/

/-- **Child `c`'s statement's digest under the seed** is the one its `statement_digest` call
computes. -/
theorem kid_digestK (MF : MainFactsK C rd σ S key) (hK : ∀ c < lg σ 6, KidOkK C rd σ S c (K c))
    {rx rs : ℕ → ℕ} (hW : Writers rd (σ (.n 45)) (segsOf σ K) (LXS σ) (LSS σ) (slOf σ K rx rs))
    {c : ℕ} (hc : c < lg σ 6) :
    [(K c).p0, (K c).p1] = digestCells (saltedStatementDigest S (kidStmt rd σ c)) := by
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
  have hst := saltedStatementDigest_parts (seed := S)
    (s := ⟨⟨(List.range (K c).ex).map fun j => xmssAt rd (σ (.n 31)) ((K c).ox j),
        (List.range (K c).es).map fun j => sphincsAt rd (σ (.n 34)) ((K c).os j),
        daDigestAt rd σ c⟩,
       deferOfCells (readCells rd (σ (.n 396) * gen ^ (24 * c)) 24)⟩)
    hseed hxd hsd hda hdef k.deflen
  rw [k.pdig, hst]

end
end LeanVM.SaltedGuest.B1.Main
