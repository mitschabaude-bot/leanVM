/-
  LeanVM.SaltedGuest.B1.Digest.ChildList

  B1 for the salted `child_claim_list_any`: the keyed digest of a child's claim list rebuilt by
  hinted indices.
-/

module

public import LeanVM.SaltedGuest.B1.Digest.ClaimList
public import LeanVM.Guest.B1.Digest.ChildList

/-!
# A child's keyed claim list, by hinted indices

As the deployed `child_claim_list_any_sound` (`LeanVM.Guest.B1.Digest.ChildList`), its values
shifted by the key's argument (`.n 0`), the chain started at the key's state, and the loops and
`child_claim_list_last__L{c}` the deployed unchanged functions (`__loop17`, `__loop18` deployed).
`child_claim_list_any_soundK`: under every seed whose key is at `key`, the claims at the hinted
slots and their keyed digest.
-/

namespace LeanVM.SaltedGuest.B1.Digest

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Guest.Value.Keccak LeanVM.Guest.B1 LeanVM.Guest.B1.Digest
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Verifier LeanVM.SaltedGuest.B1
open Recursion.Salted

@[expose] public section

/-! ## `child_claim_list_any` -/

/-- `child_claim_list_any`'s body before its `ret`. -/
noncomputable def anyFlatS : List Stmt := (Fn.body LeanVM.SaltedGuest.Data.core25).dropLast

set_option maxRecDepth 100000 in
kernel_rfl core25S_shape : Fn.body LeanVM.SaltedGuest.Data.core25 = anyFlatS ++ [.ret [.n 67, .n 68]]

/-- The body: `limit = last · g`, the zero state at `chain = .n 18`, the big frames' loop,
`mid = chain · bigs^13`, `mid_base = base · bigs^136`, the groups' loop, `last = mid · groups^13`,
the marks `mid_base · groups^17`, the dispatch on the rest. -/
noncomputable def anyBodyOkS : Bool :=
  anyFlatS.all Stmt.flat &&
  anyFlatS.any (stmtEqb · (.callIf (.n 33) "__loop18" [.n 34, .n 5, .n 18, .n 1, .n 2, .n 3, .n 9])) &&
  anyFlatS.any (stmtEqb · (.callIf (.n 51) "__loop19" [.n 52, .n 6, .n 40, .n 1, .n 2, .n 49, .n 9])) &&
  anyFlatS.any (stmtEqb · (.dispatch (.n 7) cclNames [.n 58, .n 1, .n 2, .n 64, .n 9] [.n 65, .n 66])) &&
  genMulOk (atomsIn anyFlatS) (.n 4) (.n 9) &&
  (atomsIn anyFlatS).any (isConstAt (.n 34) 1 0) &&
  (atomsIn anyFlatS).any (isAddAt (.n 33) (.n 32) (.n 5)) &&
  (atomsIn anyFlatS).any (isConstAt (.n 32) 1 0) &&
  (atomsIn anyFlatS).any (isConstAt (.n 52) 1 0) &&
  (atomsIn anyFlatS).any (isAddAt (.n 51) (.n 50) (.n 6)) &&
  (atomsIn anyFlatS).any (isConstAt (.n 50) 1 0) &&
  (List.range 13).all (fun c => (atomsIn anyFlatS).any (isLoadAt (.n (19 + c)) (.n 18) c) &&
    (atomsIn anyFlatS).any (isLoadAt (.n (19 + c)) (.n 0) c)) &&
  monoIs (atomsIn anyFlatS) (.n 40) (.n 18) (.n 5) 13 &&
  monoIs (atomsIn anyFlatS) (.n 49) (.n 3) (.n 5) 136 &&
  mono2Is (atomsIn anyFlatS) (.n 58) (.n 18) (.n 5) 13 (.n 6) 13 &&
  mono2Is (atomsIn anyFlatS) (.n 64) (.n 3) (.n 5) 136 (.n 6) 17 &&
  (atomsIn anyFlatS).any (isCopyAt (.n 67) (.n 65)) &&
  (atomsIn anyFlatS).any (isCopyAt (.n 68) (.n 66))

set_option maxRecDepth 100000 in
theorem anyBodyS_ok : anyBodyOkS = true := by decide +kernel

set_option maxRecDepth 100000 in
kernel_rfl any_idxS : SaltedGuest.coreProgram[25]? = some LeanVM.SaltedGuest.Data.core25

theorem find_child_claim_list_anyS :
    SaltedGuest.coreProgram.find? "child_claim_list_any" = some LeanVM.SaltedGuest.Data.core25 :=
  find_of_getElem? any_idxS

/-- **`child_claim_list_any`** (G:4210-4230): on `bigs = g^a`, `groups = g^b`, `rest = g^c`, the
`136a + 17b + c` claims read at hinted slots of the region below the log of `limit`, marked
`base · g^j`, and their digest. -/
theorem child_claim_list_any_soundK {rd : Reader} (hm : MemOk rd) {args rets : List E}
    (h : SaltedGuest.coreProgram.Rel rd "child_claim_list_any" args rets) :
    ∃ key entries region base limit bigs groups rest,
      args = [key, entries, region, base, limit, bigs, groups, rest] ∧
      ∀ a b c, a < 2 ^ 32 → b < 8 → c < 17 → bigs = gen ^ a → groups = gen ^ b → rest = gen ^ c →
        ∀ s : Digest, KeyIs rd key s → ∃ (os : List ℕ) (cells : List E),
          ClaimsAt rd region limit entries base (136 * a + 17 * b + c) os cells ∧
          AllCanonical cells ∧ rets = digestCells (keyedHash s (cellsBytes cells)) := by
  obtain ⟨σ, hp, hb⟩ := (rel_iff_sem find_child_claim_list_anyS args rets).mp h
  refine ⟨σ (.n 0), σ (.n 1), σ (.n 2), σ (.n 3), σ (.n 4), σ (.n 5), σ (.n 6), σ (.n 7),
    by rw [← hp]; rfl, fun a b c ha hb' hc h4 h5 h6 s hk => ?_⟩
  rw [core25S_shape, holdsList_append] at hb
  have hok := anyBodyS_ok
  simp only [anyBodyOkS, Bool.and_eq_true, List.all_eq_true, List.mem_range] at hok
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hfl, hl17⟩, hl18⟩, hdis⟩, h3⟩, h33⟩, h32⟩, h31⟩, h51⟩, h50⟩, h49⟩,
    hzs⟩, hm39⟩, hm48⟩, hm57⟩, hm63⟩, hc66⟩, hc67⟩ := hok
  obtain ⟨hall, hret⟩ := holdsList_flat _ (List.all_eq_true.mpr hfl) _ _ hb
  simp only [Stmt.HoldsList, Stmt.Holds, List.map_cons, List.map_nil] at hret
  have hat := atoms_of_flat hall
  have hlim : σ (.n 4) = σ (.n 9) * gen := genMul_sound h3 hat
  -- the key's state, copied into the chain
  have h0 : StateAt rd (σ (.n 18)) 0 (absorbChunks 2 zeroState (keyPrefix s)) := by
    intro c
    have l1 := load_sound (hzs c c.isLt).1 hat
    have l2 := load_sound (hzs c c.isLt).2 hat
    rw [Nat.zero_add]
    rw [show σ (.n (19 + c)) = keyCells s ⟨c, c.isLt⟩ from hk.load l2] at l1
    exact l1
  -- the big frames
  have hbig := childFrames_of_loop hm any136_idx (by norm_num) any136_ok any136_nb
    (chain := σ (.n 18)) (entries := σ (.n 1)) (region := σ (.n 2)) (base := σ (.n 3))
    (last := σ (.n 9)) (by omega) h4 (fun hne => by
      have := (callIf_of_flat hall hl17).2
        (by rw [add_sound h32 hat, const_sound h31 hat, word_one]; exact hne)
      have h' := (Same.rel_same rd (f := "__loop18") (by decide +kernel) _ _).mp
        (by simpa [const_sound h33 hat, word_one] using this)
      rwa [show Same.rho "__loop18" = "__loop17" by decide +kernel] at h')
  obtain ⟨osa, ca, hcla, hcana, hSa⟩ := childGroups_sound (by norm_num) (n0 := 2)
    (pre := keyPrefix s) (keyPrefix_length s) h0
    hbig a le_rfl
  -- the groups
  have h39 : σ (.n 40) = σ (.n 18) * gen ^ (13 * a) := by
    rw [monoIs_sound hm39 hat, h4, gen_pow_pow]
  have h48 : σ (.n 49) = σ (.n 3) * gen ^ (136 * a) := by
    rw [monoIs_sound hm48 hat, h4, gen_pow_pow]
  have hgrp := childFrames_of_loop hm any17_idx (by norm_num) any17_ok any17_nb
    (chain := σ (.n 40)) (entries := σ (.n 1)) (region := σ (.n 2)) (base := σ (.n 49))
    (last := σ (.n 9)) (by omega) h5 (fun hne => by
      have := (callIf_of_flat hall hl18).2
        (by rw [add_sound h50 hat, const_sound h49 hat, word_one]; exact hne)
      have h' := (Same.rel_same rd (f := "__loop19") (by decide +kernel) _ _).mp
        (by simpa [const_sound h51 hat, word_one] using this)
      rwa [show Same.rho "__loop19" = "__loop18" by decide +kernel] at h')
  have hpa : (keyPrefix s ++ cellsBytes ca).length = rate * (2 + 64 * a) := by
    rw [List.length_append, keyPrefix_length, length_cellsBytes, hcla.2.1]
    show 136 * 2 + 16 * (4 * (136 * a)) = 136 * (2 + 64 * a)
    ring
  obtain ⟨osb, cb, hclb, hcanb, hSb⟩ := childGroups_sound (by norm_num) hpa
    (by rw [h39]; exact hSa) hgrp b le_rfl
  -- the rest
  obtain ⟨j, hj, hsel, hcall⟩ := dispatch_of_flat hall hdis
  have hj17 : j < 17 := hj
  have hjc : j = c := by
    rw [h6, gen_pow_eq_ofK] at hsel
    exact (gpow_injOn (by simp only [Set.mem_Iio]; omega) (by simp only [Set.mem_Iio]; omega)
      (ofK_injective hsel)).symm
  subst hjc
  rw [show cclNames[j] = cclNames.getD j "" by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]; rfl] at hcall
  have hjs : Same.inS (cclNames.getD j "") = true ∧ Same.rho (cclNames.getD j "") = cclNames.getD j "" := by
    have : ∀ k < 17, Same.inS (cclNames.getD k "") = true ∧
        Same.rho (cclNames.getD k "") = cclNames.getD k "" := by decide +kernel
    exact this j hj17
  obtain ⟨sp, ent, reg, mk, lst, hargs, hlast⟩ := childLast_sound hm hj17 (toD hjs.1 hjs.2 hcall)
  simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hargs
  obtain ⟨hsp, hent, hreg, hmk, hlst⟩ := hargs
  have h57 : σ (.n 58) = σ (.n 40) * gen ^ (13 * b) := by
    rw [mono2Is_sound hm57 hat, h39, h4, h5]; simp only [gen_pow_pow]
  have h63 : σ (.n 64) = σ (.n 49) * gen ^ (17 * b) := by
    rw [mono2Is_sound hm63 hat, h48, h4, h5]; simp only [gen_pow_pow]
  have hpre : (keyPrefix s ++ cellsBytes ca ++ cellsBytes cb).length =
      rate * (2 + 64 * a + 8 * b) := by
    rw [List.length_append, List.length_append, keyPrefix_length, length_cellsBytes,
      length_cellsBytes, hcla.2.1, hclb.2.1]
    show 136 * 2 + 16 * (4 * (136 * a)) + 16 * (4 * (17 * b)) = 136 * (2 + 64 * a + 8 * b)
    ring
  obtain ⟨osc, cc, hclc, hcanc, hd⟩ := hlast _ _ hpre (by rw [← hsp, h57]; exact hSb)
  rw [← hent, ← hreg, ← hmk, ← hlst, h63, h48, mul_assoc, ← pow_add] at hclc
  rw [h48] at hclb
  rw [← hlim] at hcla hclb hclc
  refine ⟨osa ++ osb ++ osc, ca ++ cb ++ cc, ?_, ?_, ?_⟩
  · exact claimsAt_append (claimsAt_append hcla hclb) hclc
  · intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · rcases List.mem_append.mp hx with hx | hx
      · exact hcana x hx
      · exact hcanb x hx
    · exact hcanc x hx
  · simp only [List.map_cons, List.map_nil] at hd
    rw [← hret, copy_sound hc66 hat, copy_sound hc67 hat, hd, cellsBytes_append,
      cellsBytes_append, keyedHash_eq]
    simp

end
end LeanVM.SaltedGuest.B1.Digest
