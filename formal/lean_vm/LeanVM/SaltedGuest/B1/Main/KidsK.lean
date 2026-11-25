/-
  LeanVM.SaltedGuest.B1.Main.KidsK

  The salted `main`'s children's records: the deployed `Main.KidOk` with the claim lists' digests
  keyed by the seed.
-/

module

public import LeanVM.SaltedGuest.B1.Main.FactsK
public import LeanVM.SaltedGuest.B1.Main.CountK

/-!
# The salted children's records

`KidOkK C rd σ S c k` is the deployed `Main.KidOk` (at the deployed numbering, `MainFactsK`) with
the child's claim lists' digests the keyed hashes under the seed `S` (`xdig`, `sdig`) and its node
count `kidCount rd σ c`: positive and below `2^60`, its cell at `child_count · g^c`, multiplied
into the running count (`count`, `run`), and hashed last into the child's statement (`pdig`). `kid_recK`: from
`MainFactsK`, every child has its records, by the salted `child_claim_list_digest` under the key
(`child_claim_list_digest_soundK`) and the salted `statement_digest` (`statement_digest_soundK`).
-/

namespace LeanVM.SaltedGuest.B1.Main

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Guest.Value.Keccak LeanVM.Guest.B1 LeanVM.Guest.B1.Digest
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Node LeanVM.Guest.B1.Main LeanVM.SaltedGuest.B1 Recursion.Salted

@[expose] public section

variable {C : CallRel}

/-- **What child `c` establishes**, its claim lists keyed by `S`. -/
structure KidOkK (C : CallRel) (rd : Reader) (σ : Val) (S : Digest) (c : ℕ) (k : KidRec) :
    Prop where
  base : LoadHolds rd (σ (.n 399)) c k.base
  next : LoadHolds rd (σ (.n 399)) (c + 1) (k.base * (gen ^ k.ex * gen ^ k.es))
  bounds : k.ex < 2 ^ 32 ∧ k.es < 2 ^ 32
  xlen : k.cellsx.length = 4 * k.ex
  xcan : AllCanonical k.cellsx
  xrec : ∀ j < k.ex, SlotBelow (σ (.n 22)) (k.ox j) ∧
    LoadHolds rd (σ (.n 45)) (k.ox j) (k.base * gen ^ (if k.mx then 0 else j)) ∧
    ∀ i < 4, LoadHolds rd (σ (.n 31)) (4 * k.ox j + i) (k.cellsx.getD (4 * j + i) 0)
  xmono : k.mx = true → ∀ i j, i < j → j < k.ex → k.ox i < k.ox j
  xdig : [k.cx0, k.cx1] = digestCells (keyedHash S (cellsBytes k.cellsx))
  slen : k.cellss.length = 4 * k.es
  scan : AllCanonical k.cellss
  srec : ∀ j < k.es, SlotBelow (σ (.n 23)) (k.os j) ∧
    LoadHolds rd (σ (.n 46)) (k.os j) (k.base * gen ^ k.ex * gen ^ (if k.ms then 0 else j)) ∧
    ∀ i < 4, LoadHolds rd (σ (.n 34)) (4 * k.os j + i) (k.cellss.getD (4 * j + i) 0)
  smono : k.ms = true → ∀ i j, i < j → j < k.es → k.os i < k.os j
  sdig : [k.cs0, k.cs1] = digestCells (keyedHash S (cellsBytes k.cellss))
  da0 : LoadHolds rd (σ (.n 364)) (2 * c) k.d0
  da1 : LoadHolds rd (σ (.n 364)) (2 * c + 1) k.d1
  deflen : k.defer.length = 24
  defreads : ReadsAt rd (σ (.n 396) * gen ^ (24 * c)) k.defer
  hdrcan : AllCanonical [σ (.n 26), σ (.n 27), k.cx0, k.cx1, k.cs0, k.cs1, k.d0, k.d1]
  /-- The child's node count is positive and below `2^60`, its cell at `child_count · g^c`. -/
  count : 0 < kidCount rd σ c ∧ kidCount rd σ c < 2 ^ 60 ∧
    LoadHolds rd (σ (.n 1000)) c (gen ^ kidCount rd σ c)
  /-- The running count after the child is the one before it times the child's. -/
  run : ∃ r, LoadHolds rd (σ (.n 1001)) c r ∧
    LoadHolds rd (σ (.n 1001)) (c + 1) (r * gen ^ kidCount rd σ c)
  pdig : [k.p0, k.p1] = digestCells (keccak256
    (stmtBytes [σ (.n 26), σ (.n 27), k.cx0, k.cx1, k.cs0, k.cs1, k.d0, k.d1] k.defer ++
      cellsBytes [gen ^ kidCount rd σ c]))
  pi0 : LoadHolds rd (σ (.n 384)) (2 * c) k.p0
  pi1 : LoadHolds rd (σ (.n 384)) (2 * c + 1) k.p1
  sub : C "verify_sub"
    [k.p0, k.p1, σ (.n 26), σ (.n 27), σ (.n 28), σ (.n 390) * gen ^ (24 * c)] []

/-- **Each child's records.** -/
theorem kid_recK {rd : Reader} (hm : End.MemOk rd) {σ : Val} {S : Digest} {key : E}
    (MF : MainFactsK C rd σ S key) :
    ∀ c < lg σ 6, ∃ k : KidRec, KidOkK C rd σ S c k := by
  intro c hc
  obtain ⟨base, cx0, cx1, cs0, cs1, d0, d1, p0, p1, r, ex, es, n, hb, hex, hes, hcx, hcs, hd0, hd1,
    hn0, hn, hcc, hr0, hr1, hsd, hp0, hp1, hsub, hnext⟩ := MF.children c hc
  -- the child's count
  have hcc' := loadHolds_gen_pow_iff.mp hcc
  rw [Nat.add_zero] at hcc'
  have hkc : kidCount rd σ c = n := kidCount_of_load (by omega) hcc'
  -- the leanXMSS records
  obtain ⟨mx, ox, cellsx, hlx, hcanx, hmonox, hrecx, hdigx⟩ :=
    Digest.child_claim_list_digest_soundK rd hm _ _ hcx ex (by omega) rfl S MF.keyIs
  -- the leanSPHINCS records
  obtain ⟨ms, os, cellss, hls, hcans, hmonos, hrecs, hdigs⟩ :=
    Digest.child_claim_list_digest_soundK rd hm _ _ hcs es (by omega) rfl S MF.keyIs
  -- the statement's digest
  obtain ⟨defer, hdlen, hdefr, hhdr, hpdig⟩ := Digest.statement_digest_soundK rd _ _ hsd
  refine ⟨⟨base, cx0, cx1, cs0, cs1, d0, d1, p0, p1, ex, es, ox, cellsx, os, cellss, defer, mx, ms⟩,
    ?_⟩
  refine ⟨?_, ?_, ⟨hex, hes⟩, hlx, hcanx, hrecx, hmonox, hdigx, hls, hcans, hrecs, hmonos, hdigs,
    ?_, ?_, hdlen, ?_, ?_, ⟨by rw [hkc]; exact hn0, by rw [hkc]; exact hn,
      by rw [hkc]; exact hcc'⟩, ⟨r, ?_, ?_⟩,
    by rw [hkc]; exact hpdig, ?_, ?_, ?_⟩
  · have := loadHolds_gen_pow_iff.mp hb; simpa using this
  · have := loadHolds_gen_pow_iff.mp hnext; exact this
  · rw [gen_pow_pow] at hd0
    have := loadHolds_gen_pow_iff.mp hd0
    simpa using this
  · rw [gen_pow_pow] at hd1
    exact loadHolds_gen_pow_iff.mp hd1
  · rwa [gen_pow_pow] at hdefr
  · intro x hx
    exact hhdr x (List.mem_append_left _ hx)
  · have := loadHolds_gen_pow_iff.mp hr0; simpa using this
  · rw [hkc]; exact loadHolds_gen_pow_iff.mp hr1
  · rw [gen_pow_pow] at hp0
    have := loadHolds_gen_pow_iff.mp hp0
    simpa using this
  · rw [gen_pow_pow] at hp1
    exact loadHolds_gen_pow_iff.mp hp1
  · rwa [gen_pow_pow] at hsub

end
end LeanVM.SaltedGuest.B1.Main
