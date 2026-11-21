/-
  LeanVM.SaltedGuest.B1.Digest.ChildDigest

  B1 for the salted `child_claim_list_digest`: a child's claim list rebuilt at hinted slots, by
  either walk, and its keyed digest.
-/

module

public import LeanVM.SaltedGuest.B1.Digest.ChildMono
public import LeanVM.Guest.B1.Digest.ChildDigest

/-!
# A child's keyed claim list

`child_claim_list_digest(key, entries, region, base, limit_g, n_g)`: the deployed function with the
key's argument first, the empty list hashed from the key's state, and the two walks the keyed ones
(`child_claim_list_any_soundK`, `child_claim_list_mono_soundK`). `ChildListOutK`: the deployed
`ChildListOut` with the keyed digest under every seed whose key is at `key`;
`child_claim_list_digest_soundK`.
-/

namespace LeanVM.SaltedGuest.B1.Digest

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Guest.Value.Keccak LeanVM.Guest.B1 LeanVM.Guest.B1.Digest
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Verifier LeanVM.SaltedGuest.B1
open Recursion.Salted

@[expose] public section

/-- **A child's claim list rebuilt from this node's table, keyed**: as `ChildListOut`, under every
seed whose key is at `key`, `rets` the keyed digest of the cells. -/
def ChildListOutK (rd : Reader) (key entries region base limit : E) (n : ℕ) (rets : List E) : Prop :=
  ∀ s : Digest, KeyIs rd key s →
  ∃ (mono : Bool) (o : ℕ → ℕ) (cells : List E), cells.length = 4 * n ∧ AllCanonical cells ∧
    (mono = true → ∀ i j, i < j → j < n → o i < o j) ∧
    (∀ j < n, SlotBelow limit (o j) ∧
      LoadHolds rd region (o j) (base * gen ^ (if mono then 0 else j)) ∧
      ∀ c < 4, LoadHolds rd entries (4 * o j + c) (cells.getD (4 * j + c) 0)) ∧
    rets = digestCells (keyedHash s (cellsBytes cells))

/-- **The salted `child_claim_list_digest(key, entries, region, base, limit_g, n_g)`**. -/
def MeaningChildClaimListDigestK (rd : Reader) : List E → List E → Prop
  | [key, entries, region, base, limit, ng], rets => ∀ n < 2 ^ 32,
      ng = gen ^ n → ChildListOutK rd key entries region base limit n rets
  | _, _ => False

/-- The salted core IR's `child_claim_list_digest` gives its meaning, on a memory image. -/
def child_claim_list_digest_sound_SpecK : Prop :=
  ∀ (rd : Reader), MemOk rd → ∀ (args rets : List E),
    SaltedGuest.coreProgram.Rel rd "child_claim_list_digest" args rets →
      MeaningChildClaimListDigestK rd args rets

/-- The branch of an empty list. -/
noncomputable def cc24ZeroS : List Stmt := match Fn.body LeanVM.SaltedGuest.Data.core24 with
  | [_, _, .ite _ z _, _, _, _] => z
  | _ => []

set_option maxRecDepth 100000 in
kernel_rfl core24S_shape : Fn.body LeanVM.SaltedGuest.Data.core24 =
    [.atom (.const (.n 6) (word 1 0 0)), .atom (.add (.n 7) (.n 5) (.n 6)),
     .ite (.n 7) cc24ZeroS
      [.call "list_split" [.n 5] [.n 31, .n 32, .n 33],
       .atom (.hint (.witness "child_mono" (.stack [.n 34]))),
       .atom (.const (.n 35) (word 2 0 0)), .atom (.add (.n 36) (.n 34) (.n 35)),
       .ite (.n 36)
        [.call "child_claim_list_mono" [.n 0, .n 1, .n 2, .n 3, .n 4, .n 31, .n 32, .n 33]
          [.n 37, .n 38],
         .atom (.copy (.n 29) (.n 37)), .atom (.copy (.n 30) (.n 38))]
        [.call "child_claim_list_any" [.n 0, .n 1, .n 2, .n 3, .n 4, .n 31, .n 32, .n 33]
          [.n 39, .n 40],
         .atom (.copy (.n 29) (.n 39)), .atom (.copy (.n 30) (.n 40))]],
     .atom (.copy (.n 41) (.n 29)), .atom (.copy (.n 42) (.n 30)), .ret [.n 41, .n 42]]

/-- The empty list's chain: the empty message from the key's state. -/
noncomputable def cc24ZSpecS : ChainSpec := ⟨[], 0, true, some (keyVs 8), keccakBlocks (atomsIn cc24ZeroS)⟩

/-- The empty list's branch hashes the empty string after the key into `.n 29`, `.n 30`. -/
noncomputable def cc24ZOkS : Bool :=
  cc24ZeroS.all Stmt.flat && cc24ZSpecS.check (atomsIn cc24ZeroS) &&
    stLoadsOk (atomsIn cc24ZeroS) (.n 0) (keyVs 8) 0 &&
    decide (cc24ZSpecS.outV (cc24ZSpecS.nb - 1) 0 = V.n 29) &&
    decide (cc24ZSpecS.outV (cc24ZSpecS.nb - 1) 1 = V.n 30)

set_option maxRecDepth 100000 in
theorem cc24zS_ok : cc24ZOkS = true := by decide +kernel

set_option maxRecDepth 100000 in
kernel_rfl ccd_idxS : SaltedGuest.coreProgram[24]? = some LeanVM.SaltedGuest.Data.core24

theorem find_child_claim_list_digestS :
    SaltedGuest.coreProgram.find? "child_claim_list_digest" = some LeanVM.SaltedGuest.Data.core24 :=
  find_of_getElem? ccd_idxS

/-- **The salted `child_claim_list_digest`** rebuilds a child's claim list at hinted slots, by
either walk, and computes its keyed digest. -/
theorem child_claim_list_digest_soundK : child_claim_list_digest_sound_SpecK := by
  intro rd hm args rets h
  obtain ⟨σ, hp, hb⟩ := (rel_iff_sem find_child_claim_list_digestS args rets).mp h
  have hp' : args = [σ (.n 0), σ (.n 1), σ (.n 2), σ (.n 3), σ (.n 4), σ (.n 5)] := by
    rw [← hp]; rfl
  subst hp'
  rw [core24S_shape] at hb
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, List.map_cons, List.map_nil] at hb
  obtain ⟨c5, a6, -, hz, hnz⟩ := hb
  by_cases h6 : σ (.n 7) = 0
  · -- the empty list
    have hz1 := cc24zS_ok
    simp only [cc24ZOkS, Bool.and_eq_true, decide_eq_true_eq] at hz1
    obtain ⟨⟨⟨⟨hzf, hzc⟩, hzl⟩, hz13⟩, hz14⟩ := hz1
    have hn1 : σ (.n 5) = 1 := by
      rw [a6, c5, word_one] at h6; exact e_add_eq_zero_iff.mp h6
    obtain ⟨hall, h36, h37, hr⟩ := holdsList_flat _ hzf _ _ (hz h6)
    have hat := atoms_of_flat hall
    intro m hmb hgm s hk
    obtain rfl : 0 = m := gen_pow_inj (by omega) (by omega) (by rw [← hgm, hn1, pow_zero])
    have hkl := stLoads_sound hzl hat
    obtain ⟨hd, -⟩ := chain_final hzc rfl hat (pre := keyPrefix s) (n := 2) (keyPrefix_length s)
      (fun c => by
        simp only [ChainSpec.initCell, cc24ZSpecS]
        have := hkl c
        rw [Nat.zero_add] at this
        exact hk.load this)
    rw [hz13, hz14, show List.take (cc24ZSpecS.len / 16) (cc24ZSpecS.vals σ) = [] by
      simp [cc24ZSpecS]] at hd
    refine ⟨false, fun j => 0, [], rfl, fun _ h => absurd h (by simp), fun h => absurd h (by simp),
      fun j hj => absurd hj (by omega), ?_⟩
    rw [← hr, h36, h37, keyedHash_eq, digestCells, ← hd]
  · -- a nonempty list
    obtain ⟨hsplit, -, c30, a31, -, hmono, hany⟩ := hnz h6
    obtain ⟨a, ha, b, hb, c, hc, hn, habc⟩ := list_split_sound rd hm _ _
      (toD (by decide +kernel) (by decide +kernel) hsplit)
    simp only [List.cons.injEq, and_true] at habc
    obtain ⟨h26, h27, h28⟩ := habc
    simp only [claimGroup, bigGroups] at hb hc
    intro m hmb hgm s hk
    obtain rfl : 136 * a + 17 * b + c = m :=
      gen_pow_inj (by omega) (by omega) (by rw [← hgm, hn])
    by_cases h31 : σ (.n 36) = 0
    · -- the gap walk
      obtain ⟨hcall, c13, c14, c36, c37, hr⟩ := hmono h31
      obtain ⟨key, entries, region, base, limit, bigs, groups, rest, hargs, hw⟩ :=
        child_claim_list_mono_soundK hm hcall
      simp only [List.cons.injEq, and_true] at hargs
      obtain ⟨hkey, he, hr', hb', hl, hbg, hgr, hrs⟩ := hargs
      rw [← hkey] at hw
      obtain ⟨os, cells, O, hlen, hwk, hat, hcan, hd, hbd⟩ :=
        hw a b c (by omega) hb hc (by rw [← hbg, h26]) (by rw [← hgr, h27]) (by rw [← hrs, h28]) s hk
      rw [← he, ← hr', ← hb', ← hl] at *
      have hs := monoSlots hm hwk hat (by omega) hbd
      rw [← hlen]
      refine ⟨true, fun j => os.getD j 0, cells, by rw [hat.1], hcan,
        fun _ i j hij hj => hwk.1 i j hij hj, fun j hj => ⟨hs j hj, ?_, (hat.2 j hj).2⟩, ?_⟩
      · simpa using (hat.2 j hj).1
      · rw [← hr, c36, c37, c13, c14, hd]
    · -- the walk by hinted indices
      obtain ⟨hcall, c13, c14, c36, c37, hr⟩ := hany h31
      obtain ⟨key, entries, region, base, limit, bigs, groups, rest, hargs, hw⟩ :=
        child_claim_list_any_soundK hm hcall
      simp only [List.cons.injEq, and_true] at hargs
      obtain ⟨hkey, he, hr', hb', hl, hbg, hgr, hrs⟩ := hargs
      rw [← hkey] at hw
      obtain ⟨os, cells, hcl, hcan, hd⟩ :=
        hw a b c (by omega) hb hc (by rw [← hbg, h26]) (by rw [← hgr, h27]) (by rw [← hrs, h28]) s hk
      rw [← he, ← hr', ← hb', ← hl] at hcl
      obtain ⟨-, hl', hc'⟩ := hcl
      refine ⟨false, fun j => os.getD j 0, cells, hl', hcan, fun h => absurd h (by simp),
        fun j hj => ?_, ?_⟩
      · obtain ⟨h1, h2, h3⟩ := hc' j hj
        refine ⟨h1, by simpa using h2, fun c hcc => ?_⟩
        have := h3 c hcc
        rwa [getD_drop'] at this
      · rw [← hr, c36, c37, c13, c14, hd]

end
end LeanVM.SaltedGuest.B1.Digest
