/-
  LeanVM.SaltedGuest.B1.Digest.ChildMono

  B1 for the salted `child_claim_list_mono`: the keyed digest of a child's claim list rebuilt by
  hinted gaps.
-/

module

public import LeanVM.SaltedGuest.B1.Digest.ChildList
public import LeanVM.Guest.B1.Digest.ChildMono

/-!
# A child's keyed claim list, by hinted gaps

As the deployed `child_claim_list_mono_sound`, its values shifted by the key's argument, the
chain started at the key's state, the loops and `child_claim_list_mono_last__L{c}` the deployed
unchanged functions (`__loop19`, `__loop20` deployed). `child_claim_list_mono_soundK`.
-/

namespace LeanVM.SaltedGuest.B1.Digest

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Guest.Value.Keccak LeanVM.Guest.B1 LeanVM.Guest.B1.Digest
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Verifier LeanVM.SaltedGuest.B1
open Recursion.Salted

@[expose] public section

/-! ## `child_claim_list_mono` -/

/-- `child_claim_list_mono`'s body before its `ret`. -/
noncomputable def monoFlatS : List Stmt := (Fn.body LeanVM.SaltedGuest.Data.core26).dropLast

set_option maxRecDepth 100000 in
kernel_rfl core26S_shape : Fn.body LeanVM.SaltedGuest.Data.core26 = monoFlatS ++ [.ret [.n 53, .n 54]]

/-- The body: the zero state at `chain = .n 17`, `region` and `entries` at `chain · g^13`,
`chain · g^14`, the big frames' loop, `mid = chain · bigs^15`, the groups' loop,
`last = mid · groups^15`, the dispatch on the rest. -/
noncomputable def monoBodyOkS : Bool :=
  monoFlatS.all Stmt.flat &&
  monoFlatS.any (stmtEqb · (.callIf (.n 32) "__loop20" [.n 33, .n 5, .n 17, .n 3])) &&
  monoFlatS.any (stmtEqb · (.callIf (.n 42) "__loop21" [.n 43, .n 6, .n 40, .n 3])) &&
  monoFlatS.any (stmtEqb · (.dispatch (.n 7) mlNames [.n 50, .n 2, .n 3, .n 4] [.n 51, .n 52])) &&
  (atomsIn monoFlatS).any (isConstAt (.n 33) 1 0) &&
  (atomsIn monoFlatS).any (isAddAt (.n 32) (.n 31) (.n 5)) &&
  (atomsIn monoFlatS).any (isConstAt (.n 31) 1 0) &&
  (atomsIn monoFlatS).any (isConstAt (.n 43) 1 0) &&
  (atomsIn monoFlatS).any (isAddAt (.n 42) (.n 41) (.n 6)) &&
  (atomsIn monoFlatS).any (isConstAt (.n 41) 1 0) &&
  (List.range 13).all (fun c => (atomsIn monoFlatS).any (isLoadAt (.n (18 + c)) (.n 17) c) &&
    (atomsIn monoFlatS).any (isLoadAt (.n (18 + c)) (.n 0) c)) &&
  (atomsIn monoFlatS).any (isLoadAt (.n 2) (.n 17) 13) &&
  (atomsIn monoFlatS).any (isLoadAt (.n 1) (.n 17) 14) &&
  monoIs (atomsIn monoFlatS) (.n 40) (.n 17) (.n 5) 15 &&
  mono2Is (atomsIn monoFlatS) (.n 50) (.n 17) (.n 5) 15 (.n 6) 15 &&
  (atomsIn monoFlatS).any (isCopyAt (.n 53) (.n 51)) &&
  (atomsIn monoFlatS).any (isCopyAt (.n 54) (.n 52))

set_option maxRecDepth 100000 in
theorem monoBodyS_ok : monoBodyOkS = true := by decide +kernel

set_option maxRecDepth 100000 in
kernel_rfl mono_idxS : SaltedGuest.coreProgram[26]? = some LeanVM.SaltedGuest.Data.core26

theorem find_child_claim_list_monoS :
    SaltedGuest.coreProgram.find? "child_claim_list_mono" = some LeanVM.SaltedGuest.Data.core26 :=
  find_of_getElem? mono_idxS

/-- **`child_claim_list_mono`** (G:4255-4286): on `bigs = g^a`, `groups = g^b`, `rest = g^c`, the
`136a + 17b + c` claims walked by hinted gaps from slot 0 to `O`, every claim marked `base`, their
digest, and the bound on `O`: `region · g^O = g^e · region`, `limit = g^(e + e')`. -/
theorem child_claim_list_mono_soundK {rd : Reader} (hm : MemOk rd) {args rets : List E}
    (h : SaltedGuest.coreProgram.Rel rd "child_claim_list_mono" args rets) :
    ∃ key entries region base limit bigs groups rest,
      args = [key, entries, region, base, limit, bigs, groups, rest] ∧
      ∀ a b c, a < 2 ^ 32 → b < 8 → c < 17 → bigs = gen ^ a → groups = gen ^ b → rest = gen ^ c →
        ∀ s : Digest, KeyIs rd key s →
        ∃ (os : List ℕ) (cells : List E) (O : ℕ), os.length = 136 * a + 17 * b + c ∧
          MonoWalk 0 os O ∧ MonoAt rd region entries base os cells ∧ AllCanonical cells ∧
          rets = digestCells (keyedHash s (cellsBytes cells)) ∧
          ∃ e e', e < 2 ^ 32 ∧ e' < 2 ^ 32 ∧ region * gen ^ O = gen ^ e * region ∧
            limit = gen ^ (e + e') := by
  obtain ⟨σ, hp, hb⟩ := (rel_iff_sem find_child_claim_list_monoS args rets).mp h
  refine ⟨σ (.n 0), σ (.n 1), σ (.n 2), σ (.n 3), σ (.n 4), σ (.n 5), σ (.n 6), σ (.n 7),
    by rw [← hp]; rfl, fun a b c ha hb' hc h4 h5 h6 s hk => ?_⟩
  rw [core26S_shape, holdsList_append] at hb
  have hok := monoBodyS_ok
  simp only [monoBodyOkS, Bool.and_eq_true, List.all_eq_true, List.mem_range] at hok
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hfl, hl19⟩, hl20⟩, hdis⟩, h32⟩, h31⟩, h30⟩, h42⟩, h41⟩, h40⟩, hzs⟩,
    hl1⟩, hl0⟩, hm39⟩, hm49⟩, hc52⟩, hc53⟩ := hok
  obtain ⟨hall, hret⟩ := holdsList_flat _ (List.all_eq_true.mpr hfl) _ _ hb
  simp only [Stmt.HoldsList, Stmt.Holds, List.map_cons, List.map_nil] at hret
  have hat := atoms_of_flat hall
  -- the key's record
  have h0 : StateAt rd (σ (.n 17)) 0 (absorbChunks 2 zeroState (keyPrefix s)) := by
    intro c
    have l1 := load_sound (hzs c c.isLt).1 hat
    have l2 := load_sound (hzs c c.isLt).2 hat
    rw [Nat.zero_add]
    rw [show σ (.n (18 + c)) = keyCells s ⟨c, c.isLt⟩ from hk.load l2] at l1
    exact l1
  have hc0 : LoadHolds rd (σ (.n 17)) 13 (σ (.n 2) * gen ^ 0) := by
    rw [pow_zero, mul_one]; exact load_sound hl1 hat
  have he0 : LoadHolds rd (σ (.n 17)) 14 (σ (.n 1) * gen ^ (4 * 0)) := by
    rw [mul_zero, pow_zero, mul_one]; exact load_sound hl0 hat
  -- the big frames
  have hbig := monoFrames_of_loop hm mono136_idx (by norm_num) mono136_ok word_g136 word_g544
    mono136_nb (chain := σ (.n 17)) (mark := σ (.n 3)) (by omega) h4 (fun hne => by
      have := (callIf_of_flat hall hl19).2
        (by rw [add_sound h31 hat, const_sound h30 hat, word_one]; exact hne)
      have h' := (Same.rel_same rd (f := "__loop20") (by decide +kernel) _ _).mp
        (by simpa [const_sound h32 hat, word_one] using this)
      rwa [show Same.rho "__loop20" = "__loop19" by decide +kernel] at h')
  obtain ⟨osa, ca, Oa, hla, hwa, hata, hcana, hSa, hca, hea⟩ :=
    monoFrames_sound (by norm_num) (n0 := 2) (pre := keyPrefix s) (keyPrefix_length s) h0 hc0 he0
      hbig a le_rfl
  -- the groups
  have h39 : σ (.n 40) = σ (.n 17) * gen ^ (15 * a) := by
    rw [monoIs_sound hm39 hat, h4, gen_pow_pow]
  have hgrp := monoFrames_of_loop hm mono17_idx (by norm_num) mono17_ok word_g17 word_g68
    mono17_nb (chain := σ (.n 40)) (mark := σ (.n 3)) (by omega) h5 (fun hne => by
      have := (callIf_of_flat hall hl20).2
        (by rw [add_sound h41 hat, const_sound h40 hat, word_one]; exact hne)
      have h' := (Same.rel_same rd (f := "__loop21") (by decide +kernel) _ _).mp
        (by simpa [const_sound h42 hat, word_one] using this)
      rwa [show Same.rho "__loop21" = "__loop20" by decide +kernel] at h')
  have hpa : (keyPrefix s ++ cellsBytes ca).length = rate * (2 + 64 * a) := by
    rw [List.length_append, keyPrefix_length, length_cellsBytes, hata.1, hla]
    show 136 * 2 + 16 * (4 * (136 * a)) = 136 * (2 + 64 * a)
    ring
  obtain ⟨osb, cb, Ob, hlb, hwb, hatb, hcanb, hSb, hcb, heb⟩ :=
    monoFrames_sound (by norm_num) hpa (by rw [h39]; exact hSa) (by rw [h39]; exact hca)
      (by rw [h39]; exact hea) hgrp b le_rfl
  -- the rest
  obtain ⟨j, hj, hsel, hcall⟩ := dispatch_of_flat hall hdis
  have hj17 : j < 17 := hj
  have hjc : j = c := by
    rw [h6, gen_pow_eq_ofK] at hsel
    exact (gpow_injOn (by simp only [Set.mem_Iio]; omega) (by simp only [Set.mem_Iio]; omega)
      (ofK_injective hsel)).symm
  subst hjc
  rw [show mlNames[j] = mlNames.getD j "" by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]; rfl] at hcall
  have hjs : Same.inS (mlNames.getD j "") = true ∧ Same.rho (mlNames.getD j "") = mlNames.getD j "" := by
    have : ∀ k < 17, Same.inS (mlNames.getD k "") = true ∧
        Same.rho (mlNames.getD k "") = mlNames.getD k "" := by decide +kernel
    exact this j hj17
  obtain ⟨rec, reg, mk, lim, hargs, hlast⟩ := monoLast_sound hm hj17 (toD hjs.1 hjs.2 hcall)
  simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hargs
  obtain ⟨hrec, hreg, hmk, hlim⟩ := hargs
  have h49 : σ (.n 50) = σ (.n 40) * gen ^ (15 * b) := by
    rw [mono2Is_sound hm49 hat, h39, h4, h5]; simp only [gen_pow_pow]
  have hpre : (keyPrefix s ++ cellsBytes ca ++ cellsBytes cb).length =
      rate * (2 + 64 * a + 8 * b) := by
    rw [List.length_append, List.length_append, keyPrefix_length, length_cellsBytes,
      length_cellsBytes, hata.1, hla, hatb.1, hlb]
    show 136 * 2 + 16 * (4 * (136 * a)) + 16 * (4 * (17 * b)) = 136 * (2 + 64 * a + 8 * b)
    ring
  rw [← hreg, ← hmk] at hlast
  obtain ⟨osc, cc, Oc, hlc, hwc, hatc, hcanc, hd, hbd⟩ := hlast (σ (.n 1)) _ Ob _ hpre
    (by rw [← hrec, h49]; exact hSb) (by rw [← hrec, h49]; exact hcb)
    (by rw [← hrec, h49]; exact heb)
  refine ⟨osa ++ osb ++ osc, ca ++ cb ++ cc, Oc, ?_,
    monoWalk_append (monoWalk_append hwa hwb) hwc, monoAt_append (monoAt_append hata hatb) hatc,
    ?_, ?_, by rw [hlim]; exact hbd⟩
  · rw [List.length_append, List.length_append, hla, hlb, hlc]
  · intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · rcases List.mem_append.mp hx with hx | hx
      · exact hcana x hx
      · exact hcanb x hx
    · exact hcanc x hx
  · simp only [List.map_cons, List.map_nil] at hd
    rw [← hret, copy_sound hc52 hat, copy_sound hc53 hat, hd, cellsBytes_append,
      cellsBytes_append, keyedHash_eq]
    simp

end
end LeanVM.SaltedGuest.B1.Digest
