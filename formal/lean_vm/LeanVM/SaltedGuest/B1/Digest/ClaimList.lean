/-
  LeanVM.SaltedGuest.B1.Digest.ClaimList

  B1 for the salted `claim_list_digest`: the keyed digest of a declared claim list.
-/

module

public import LeanVM.SaltedGuest.B1.Keyed
public import LeanVM.SaltedGuest.B1.Callee
public import LeanVM.SaltedGuest.KernelRfl
public import LeanVM.SaltedGuest.B1.Merkle.CapAll
public import LeanVM.Guest.B1.Digest.ClaimList
public import LeanVM.Guest.B1.Digest.Range

/-!
# The keyed claim list

`claim_list_digest(key, entries, n_g)` of the salted guest hashes the claims with the keyed hash:
for `n_g = 1` the empty message continuing from the key's state at `key` (one `KECCAK`, the
padding into cells `0` and `8`); otherwise the heap chain starts at the key's state (`key_chain`:
the thirteen cells copied) in place of the zero state, and the big frames' loop `__loop16`, the
groups' loop `__loop17` and `claim_list_last__L{c}` are the deployed ones (unchanged functions:
`__loop15`, `__loop16` deployed). The deployed proof (`LeanVM.Guest.B1.Digest.ClaimList`) is
written over any prefix of whole blocks; here the prefix is the key's (`keyPrefix s`, two blocks),
so the digest is the keyed hash of the claims' bytes.

`MeaningClaimListDigestK`: `n_g = g^n`, and under every seed whose key's state is at `key`, the
`4n` canonical cells at `entries` hash to the returned cells. `claim_list_digest_soundK`.
-/

namespace LeanVM.SaltedGuest.B1.Digest

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Guest.Value.Keccak LeanVM.Guest.B1 LeanVM.Guest.B1.Digest
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Verifier LeanVM.SaltedGuest.B1
open Recursion.Salted

@[expose] public section

/-- The key's state under `s` at `key`. -/
def KeyAt (rd : Reader) (key : E) (s : Digest) : Prop := StateAt rd key 0 (keyState s)

/-- **What a keyed claim list's call returns**: under every seed whose key's state is at `key`,
the keyed digest of the `4n` canonical cells at `entries`. -/
def ClaimListOutK (rd : Reader) (key entries : E) (n : ℕ) (rets : List E) : Prop :=
  ∀ s : Digest, KeyAt rd key s → ∃ cells : List E, cells.length = 4 * n ∧ ReadsAt rd entries cells ∧
    AllCanonical cells ∧ rets = digestCells (keyedHash s (cellsBytes cells))

/-- **The salted `claim_list_digest(key, entries, n_g)`**. -/
def MeaningClaimListDigestK (rd : Reader) : List E → List E → Prop
  | [key, entries, ng], rets => ∃ n < claimBig * 2 ^ 32, ng = gen ^ n ∧ ClaimListOutK rd key entries n rets
  | _, _ => False

/-- The salted core IR's `claim_list_digest` gives its meaning, on a memory image. -/
def claim_list_digest_sound_SpecK : Prop :=
  ∀ (rd : Reader), MemOk rd → ∀ (args rets : List E),
    SaltedGuest.coreProgram.Rel rd "claim_list_digest" args rets → MeaningClaimListDigestK rd args rets

/-! ## The body -/

/-- The empty list's branch. -/
noncomputable def cl23ZeroS : List Stmt := match Fn.body LeanVM.SaltedGuest.Data.core23 with
  | [_, _, .ite _ z _, _, _, _] => z
  | _ => []

/-- The nonempty list's branch. -/
noncomputable def cl23ElseS : List Stmt := match Fn.body LeanVM.SaltedGuest.Data.core23 with
  | [_, _, .ite _ _ n, _, _, _] => n
  | _ => []

set_option maxRecDepth 100000 in
kernel_rfl core23S_shape : Fn.body LeanVM.SaltedGuest.Data.core23 =
    [.atom (.const (.n 3) (word 1 0 0)), .atom (.add (.n 4) (.n 2) (.n 3)),
     .ite (.n 4) cl23ZeroS cl23ElseS, .atom (.copy (.n 92) (.n 26)), .atom (.copy (.n 93) (.n 27)),
     .ret [.n 92, .n 93]]

/-- The key's cells, as both branches load them: values `5 .. 17` (empty), `40 .. 52` (chain). -/
def keyVs (b : ℕ) : List V := (List.range 13).map fun c ↦ .n (b + c)

/-- The empty list's chain: the empty message from the key's state. -/
noncomputable def czSpecS : ChainSpec := ⟨[], 0, true, some (keyVs 5), keccakBlocks (atomsIn cl23ZeroS)⟩

/-- The empty list's branch hashes the empty string after the key into `.n 26`, `.n 27`, the key's
cells loaded from `key` (`.n 0`). -/
noncomputable def czOkS : Bool :=
  cl23ZeroS.all Stmt.flat && czSpecS.check (atomsIn cl23ZeroS) &&
    stLoadsOk (atomsIn cl23ZeroS) (.n 0) (keyVs 5) 0 &&
    decide (czSpecS.outV (czSpecS.nb - 1) 0 = V.n 26) && decide (czSpecS.outV (czSpecS.nb - 1) 1 = V.n 27)

/-- The nonempty list's branch: `list_split`, the key's state copied to `chain = .n 39`, the big
frames' loop, the groups' loop, the dispatch on the rest. -/
noncomputable def ceOkS : Bool :=
  cl23ElseS.all Stmt.flat &&
  cl23ElseS.any (stmtEqb · (.call "list_split" [.n 2] [.n 28, .n 29, .n 30])) &&
  cl23ElseS.any (stmtEqb · (.callIf (.n 54) "__loop16" [.n 55, .n 28, .n 39, .n 1])) &&
  cl23ElseS.any (stmtEqb · (.callIf (.n 74) "__loop17" [.n 75, .n 29, .n 61, .n 72])) &&
  cl23ElseS.any (stmtEqb · (.dispatch (.n 30) clNames [.n 81, .n 89] [.n 90, .n 91])) &&
  (atomsIn cl23ElseS).any (isConstAt (.n 55) 1 0) &&
  (atomsIn cl23ElseS).any (isAddAt (.n 54) (.n 53) (.n 28)) &&
  (atomsIn cl23ElseS).any (isConstAt (.n 53) 1 0) &&
  (atomsIn cl23ElseS).any (isConstAt (.n 75) 1 0) &&
  (atomsIn cl23ElseS).any (isAddAt (.n 74) (.n 73) (.n 29)) &&
  (atomsIn cl23ElseS).any (isConstAt (.n 73) 1 0) &&
  (List.range 13).all (fun c => (atomsIn cl23ElseS).any (isLoadAt (.n (40 + c)) (.n 39) c) &&
    (atomsIn cl23ElseS).any (isLoadAt (.n (40 + c)) (.n 0) c)) &&
  monoIs (atomsIn cl23ElseS) (.n 61) (.n 39) (.n 28) 13 &&
  monoIs (atomsIn cl23ElseS) (.n 72) (.n 1) (.n 28) 544 &&
  mono2Is (atomsIn cl23ElseS) (.n 81) (.n 39) (.n 28) 13 (.n 29) 13 &&
  mono2Is (atomsIn cl23ElseS) (.n 89) (.n 1) (.n 28) 544 (.n 29) 68 &&
  (atomsIn cl23ElseS).any (isCopyAt (.n 26) (.n 90)) &&
  (atomsIn cl23ElseS).any (isCopyAt (.n 27) (.n 91))

set_option maxRecDepth 100000 in
theorem czS_ok : czOkS = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem ceS_ok : ceOkS = true := by decide +kernel

set_option maxRecDepth 100000 in
kernel_rfl cl_idx23S : SaltedGuest.coreProgram[23]? = some LeanVM.SaltedGuest.Data.core23

theorem find_claim_list_digestS :
    SaltedGuest.coreProgram.find? "claim_list_digest" = some LeanVM.SaltedGuest.Data.core23 :=
  find_of_getElem? cl_idx23S

/-- The two key-state prefixes are the same. -/
theorem key_state_eq {rd : Reader} {key : E} {s : Digest} (hk : KeyAt rd key s) (c : Fin 13) :
    LoadHolds rd key c (cellsOfState (absorbChunks 2 zeroState (keyPrefix s)) false c) := by
  have := hk c
  rwa [Nat.zero_add] at this

/-- **The salted `claim_list_digest` computes the keyed digest of the claims.** -/
theorem claim_list_digest_soundK : claim_list_digest_sound_SpecK := by
  intro rd hm args rets h
  obtain ⟨σ, hp, hb⟩ := (rel_iff_sem find_claim_list_digestS args rets).mp h
  have hp' : args = [σ (.n 0), σ (.n 1), σ (.n 2)] := by rw [← hp]; rfl
  subst hp'
  rw [core23S_shape] at hb
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, List.map_cons, List.map_nil] at hb
  obtain ⟨c2, a3, -, hz, hnz⟩ := hb
  have hz1 := czS_ok
  have he1 := ceS_ok
  simp only [czOkS, Bool.and_eq_true, decide_eq_true_eq] at hz1
  simp only [ceOkS, Bool.and_eq_true, List.all_eq_true, List.mem_range] at he1
  obtain ⟨⟨⟨⟨hzf, hzc⟩, hzl⟩, hz10⟩, hz11⟩ := hz1
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hef, hls⟩, hlp⟩, hlp2⟩, hdis⟩, h50⟩, h49⟩, h48⟩, h70⟩, h69⟩, h68⟩,
    hzs⟩, hm56⟩, hm67⟩, hm76⟩, hm84⟩, hc10⟩, hc11⟩ := he1
  by_cases h3 : σ (.n 4) = 0
  · -- the empty list
    have hn1 : σ (.n 2) = 1 := by
      rw [a3, c2, word_one] at h3; exact e_add_eq_zero_iff.mp h3
    obtain ⟨hall, h65, h66, hr⟩ := holdsList_flat _ hzf _ _ (hz h3)
    have hat := atoms_of_flat hall
    refine ⟨0, by norm_num, by rw [hn1, pow_zero], fun s hk ↦ ⟨[], rfl, readsAt_nil _ _,
      fun _ h => absurd h (by simp), ?_⟩⟩
    have hkl := stLoads_sound hzl hat
    obtain ⟨hd, -⟩ := chain_final hzc rfl hat (pre := keyPrefix s) (n := 2) (keyPrefix_length s)
      (fun c => by
        simp only [ChainSpec.initCell, czSpecS]
        have := hkl c
        rw [Nat.zero_add] at this
        exact loadHolds_unique this (key_state_eq hk c))
    rw [hz10, hz11, show List.take (czSpecS.len / 16) (czSpecS.vals σ) = [] by simp [czSpecS]] at hd
    rw [← hr, h65, h66, keyedHash_eq, digestCells, ← hd]
  · -- a nonempty list
    obtain ⟨hall, h65, h66, hr⟩ := holdsList_flat _ (List.all_eq_true.mpr hef) _ _ (hnz h3)
    have hat := atoms_of_flat hall
    obtain ⟨a, ha, b, hb, c, hc, hn, habc⟩ := list_split_sound rd hm _ _
      (toD (by decide +kernel) (by decide +kernel) (call_of_flat hall hls))
    simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at habc
    obtain ⟨h23, h24, h25⟩ := habc
    simp only [claimGroup, bigGroups] at hb hc
    have hbig := frames_of_loop big_idx (by norm_num) big_ok big_nb (chain := σ (.n 39))
      (entries := σ (.n 1)) (by omega) h23 (fun hne => by
        have := (callIf_of_flat hall hlp).2
          (by rw [add_sound h49 hat, const_sound h48 hat, word_one]; exact hne)
        have h' := (Same.rel_same rd (f := "__loop16") (by decide +kernel) _ _).mp
          (by simpa [const_sound h50 hat, word_one] using this)
        rwa [show Same.rho "__loop16" = "__loop15" by decide +kernel] at h')
    have h56 : σ (.n 61) = σ (.n 39) * gen ^ (13 * a) := by
      rw [monoIs_sound hm56 hat, h23, gen_pow_pow]
    have h67 : σ (.n 72) = σ (.n 1) * gen ^ (544 * a) := by
      rw [monoIs_sound hm67 hat, h23, gen_pow_pow]
    have hgrp := frames_of_loop grp_idx (by norm_num) grp_ok grp_nb (chain := σ (.n 61))
      (entries := σ (.n 72)) (by omega) h24 (fun hne => by
        have := (callIf_of_flat hall hlp2).2
          (by rw [add_sound h69 hat, const_sound h68 hat, word_one]; exact hne)
        have h' := (Same.rel_same rd (f := "__loop17") (by decide +kernel) _ _).mp
          (by simpa [const_sound h70 hat, word_one] using this)
        rwa [show Same.rho "__loop17" = "__loop16" by decide +kernel] at h')
    obtain ⟨j, hj, hsel, hcall⟩ := dispatch_of_flat hall hdis
    have hj17 : j < 17 := hj
    have hjc : j = c := by
      rw [h25, gen_pow_eq_ofK] at hsel
      exact (gpow_injOn (by simp only [Set.mem_Iio]; omega) (by simp only [Set.mem_Iio]; omega)
        (ofK_injective hsel)).symm
    subst hjc
    rw [show clNames[j] = clNames.getD j "" by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]; rfl] at hcall
    have hjs : Same.inS (clNames.getD j "") = true ∧ Same.rho (clNames.getD j "") = clNames.getD j "" := by
      have : ∀ k < 17, Same.inS (clNames.getD k "") = true ∧
          Same.rho (clNames.getD k "") = clNames.getD k "" := by decide +kernel
      exact this j hj17
    obtain ⟨sp, blk, hargs, hlast⟩ := claimLast_sound hj17 (toD hjs.1 hjs.2 hcall)
    simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hargs
    obtain ⟨hsp, hblk⟩ := hargs
    have h76 : σ (.n 81) = σ (.n 61) * gen ^ (13 * b) := by
      rw [mono2Is_sound hm76 hat, h56, h23, h24]; simp only [gen_pow_pow]
    have h84 : σ (.n 89) = σ (.n 72) * gen ^ (68 * b) := by
      rw [mono2Is_sound hm84 hat, h67, h23, h24]; simp only [gen_pow_pow]
    -- the cells, whatever the key
    have hcells (pre : List UInt8) (n0 : ℕ) (hpre0 : pre.length = rate * n0)
        (h0 : StateAt rd (σ (.n 39)) 0 (absorbChunks n0 zeroState pre)) :
        ∃ ca cb cc : List E, ca.length = 4 * 136 * a ∧ cb.length = 4 * 17 * b ∧
          cc.length = 4 * j ∧ ReadsAt rd (σ (.n 1)) ca ∧
          ReadsAt rd (σ (.n 1) * gen ^ (4 * 136 * a)) cb ∧
          ReadsAt rd (σ (.n 1) * gen ^ (4 * 136 * a + 4 * 17 * b)) cc ∧
          AllCanonical (ca ++ cb ++ cc) ∧
          [σ (.n 90), σ (.n 91)] =
            digestCells (keccak256 (pre ++ cellsBytes (ca ++ cb ++ cc))) := by
      obtain ⟨ca, hla, hra, hcana, hSa⟩ := groups_sound (by norm_num) hpre0 h0 hbig a le_rfl
      have hpa : (pre ++ cellsBytes ca).length = rate * (n0 + 64 * a) := by
        rw [List.length_append, hpre0, length_cellsBytes, hla]
        show 136 * n0 + 16 * (4 * 136 * a) = 136 * (n0 + 64 * a)
        ring
      obtain ⟨cb, hlb, hrb, hcanb, hSb⟩ := groups_sound (by norm_num) hpa
        (by rw [h56]; exact hSa) hgrp b le_rfl
      have hpre : (pre ++ cellsBytes ca ++ cellsBytes cb).length = rate * (n0 + 64 * a + 8 * b) := by
        rw [List.length_append, List.length_append, hpre0, length_cellsBytes, length_cellsBytes, hla,
          hlb]
        show 136 * n0 + 16 * (4 * 136 * a) + 16 * (4 * 17 * b) = 136 * (n0 + 64 * a + 8 * b)
        ring
      obtain ⟨cc, hlc, hrc, hcanc, hd⟩ := hlast _ _ hpre (by rw [← hsp, h76]; exact hSb)
      refine ⟨ca, cb, cc, hla, hlb, hlc, hra, ?_, ?_, ?_, ?_⟩
      · rw [show 4 * 136 * a = 544 * a by ring, ← h67]; exact hrb
      · rw [← hblk, h84, h67, mul_assoc, ← pow_add] at hrc
        rwa [show 4 * 136 * a + 4 * 17 * b = 544 * a + 68 * b by ring]
      · intro x hx
        rcases List.mem_append.mp hx with hx | hx
        · rcases List.mem_append.mp hx with hx | hx
          · exact hcana x hx
          · exact hcanb x hx
        · exact hcanc x hx
      · rw [cellsBytes_append, cellsBytes_append]; simpa [List.append_assoc] using hd
    refine ⟨136 * a + 17 * b + j, by simp only [claimBig]; omega, by rw [hn], fun s hk ↦ ?_⟩
    -- the key's state, copied into the chain
    have h0 : StateAt rd (σ (.n 39)) 0 (absorbChunks 2 zeroState (keyPrefix s)) := by
      intro c
      have l1 := load_sound (hzs c c.isLt).1 hat
      have l2 := load_sound (hzs c c.isLt).2 hat
      rw [Nat.zero_add]
      rw [loadHolds_unique l2 (key_state_eq hk c)] at l1
      exact l1
    obtain ⟨ca, cb, cc, hla, hlb, hlc, hra, hrb, hrc, hcan, hd⟩ := hcells _ _ (keyPrefix_length s) h0
    refine ⟨ca ++ cb ++ cc, by rw [List.length_append, List.length_append, hla, hlb, hlc]; ring,
      ?_, hcan, ?_⟩
    · rw [readsAt_append, readsAt_append, List.length_append, hla, hlb]
      exact ⟨⟨hra, hrb⟩, hrc⟩
    · rw [← hr, h65, h66, copy_sound hc10 hat, copy_sound hc11 hat, keyedHash_eq]
      exact hd

end
end LeanVM.SaltedGuest.B1.Digest
