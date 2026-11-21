/-
  LeanVM.SaltedGuest.B1.Merkle.ClimbK

  The cap's meaning under the key climbs a cap leaf to the root, with the keyed hash.
-/

module

public import LeanVM.SaltedGuest.B1.Merkle.Cap

/-!
# Climbing under the key

`climbK s leaf q sibs` is the verifier's climb (`Compile.climbWithHash`) with the keyed hash under
`s`, and `hashPairK s` its node hash. `hashesPairK_digests`: a node hashed under the key is
`hashPairK` of its children's digests. `cap_climbK`: under `verify_merkle_cap`'s meaning
(`MeaningCapK`) with the key's cells those of `s`, a digest written at a cap leaf whose parent is
flagged climbs to the root by the cap's siblings; `query_opens_rootK`: so does the node a path
below the cap reaches.
-/

namespace LeanVM.SaltedGuest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Guest.B1 LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Guest.Value.Keccak
open Recursion.Salted

@[expose] public section

/-! ## The keyed climb -/

/-- The node hash under the key `s`: the keyed digest of the two digests' bytes. -/
def hashPairK (s : Digest) (left right : Digest) : Digest :=
  keyedHash s (digestBytes left ++ digestBytes right)

/-- **The climb under the key** `s` (`Compile.climbWithHash` with the keyed hash). -/
def climbK (s : Digest) (leaf : Digest) (q : ℕ) (sibs : List Digest) : Digest :=
  Id.run (Compile.climbWithHash (m := Id) (keyedHash s) leaf q sibs)

theorem climbK_nil (s x : Digest) (q : ℕ) : climbK s x q [] = x := rfl

theorem climbK_cons (s x : Digest) (q : ℕ) (y : Digest) (ys : List Digest) :
    climbK s x q (y :: ys) =
      climbK s (if q % 2 = 0 then hashPairK s x y else hashPairK s y x) (q / 2) ys := by
  unfold climbK
  simp only [Compile.climbWithHash]
  split <;> rfl

theorem climbK_append (s : Digest) (ss ts : List Digest) (x : Digest) (q : ℕ) :
    climbK s x q (ss ++ ts) = climbK s (climbK s x q ss) (q / 2 ^ ss.length) ts := by
  induction ss generalizing x q with
  | nil => simp [climbK_nil]
  | cons y ss ih =>
    rw [List.cons_append, climbK_cons, climbK_cons, ih, List.length_cons, Nat.div_div_eq_div_mul,
      pow_succ, Nat.mul_comm]

theorem climbK_snoc (s : Digest) (cs : List Digest) (y x : Digest) (q : ℕ) :
    climbK s x q (cs ++ [y]) =
      if q / 2 ^ cs.length % 2 = 0 then hashPairK s (climbK s x q cs) y
      else hashPairK s y (climbK s x q cs) := by
  rw [climbK_append, climbK_cons, climbK_nil]

/-- **A node hashed under the key is `hashPairK` of its children's digests.** -/
theorem hashesPairK_digests {s : Digest} {l0 l1 r0 r1 p0 p1 : E}
    (h : HashesPairK s l0 l1 r0 r1 p0 p1) :
    ∃ dl dr, (l0, l1) = digestHalves dl ∧ (r0, r1) = digestHalves dr ∧
      (p0, p1) = digestHalves (hashPairK s dl dr) := by
  obtain ⟨hc, hd⟩ := h
  obtain ⟨dl, hl⟩ := exists_digest (hc l0 (by simp)) (hc l1 (by simp))
  obtain ⟨dr, hr⟩ := exists_digest (hc r0 (by simp)) (hc r1 (by simp))
  refine ⟨dl, dr, hl, hr, ?_⟩
  rw [hd, hashPairK, ← cellsBytes_digestScalars, ← cellsBytes_digestScalars, ← cellsBytes_append]
  simp only [Prod.ext_iff] at hl hr
  rw [hl.1, hl.2, hr.1, hr.2]
  rfl

/-! ## Up the cap -/

/-- **Up the cap under the key**: under `verify_merkle_cap`'s meaning with the root `root` and the
key's cells those of `s`, a digest written at the cap's leaf `p` whose parent is flagged climbs to
the root by `D` siblings of the cap. -/
theorem cap_climbK {D : ℕ} (hD : 2 ≤ D) {rd : Reader} {cap flags r0 r1 : E} {root s : Digest}
    (hcap : MeaningCapK (2 ^ D) rd [cap, flags] [r0, r1])
    (hkey : ∀ c : Fin 13, LoadHolds rd cap (4 * 2 ^ D + c.val) (keyCells s c))
    (hroot : (r0, r1) = digestHalves root) {p : ℕ} (hp : p < 2 ^ D) {x : Digest}
    (hx0 : LoadHolds rd cap (2 * (2 ^ D + p)) (digestHalves x).1)
    (hx1 : LoadHolds rd cap (2 * (2 ^ D + p) + 1) (digestHalves x).2)
    (hfl : LoadHolds rd flags (2 ^ (D - 1) + p / 2) 1) :
    ∃ cs : List Digest, cs.length = D ∧ climbK s x p cs = root := by
  obtain ⟨kc, cell, fl, hk, hc, hf, hh0, hpin, hret⟩ := hcap
  have hks : kc = keyCells s := funext fun c ↦ loadHolds_unique (hk c) (hkey c)
  have hh := hh0 s hks
  have hpow : ∀ j, j < D → 2 ≤ 2 ^ (D - j) := fun j hj ↦ by
    have := Nat.pow_le_pow_right (show 0 < 2 by norm_num) (show 1 ≤ D - j by omega)
    simpa using this
  have hle : ∀ j, 2 ^ (D - j) ≤ 2 ^ D := fun j ↦ Nat.pow_le_pow_right (by norm_num) (by omega)
  have chain : ∀ j, 1 ≤ j → j < D → fl (capAnc D p j) ≠ 0 := by
    intro j hj1 hjD
    induction j with
    | zero => omega
    | succ j ih =>
      rcases Nat.eq_zero_or_pos j with rfl | hj0
      · show fl (capAnc D p 1) ≠ 0
        have hA : capAnc D p 1 = 2 ^ (D - 1) + p / 2 := by simp [capAnc]
        have hb := capAnc_bounds hp (show 1 ≤ D by omega)
        have hD1 := two_pow_sub_succ (show 0 < D by omega)
        simp only [Nat.sub_zero, Nat.zero_add] at hD1
        have h1 := (hf (capAnc D p 1) (by have := hpow 1 (by omega); omega)
          (by omega)).1
        rw [hA] at h1 ⊢
        rw [loadHolds_unique h1 hfl]
        exact one_ne_zero
      · intro h0
        have hprev := ih (by omega) (by omega)
        have hb := capAnc_bounds hp (show j + 1 ≤ D by omega)
        have hs := capAnc_succ (p := p) (show j < D by omega)
        have hD1 := two_pow_sub_succ (show j < D by omega)
        have hle' := hle j
        have hpw := hpow (j + 1) hjD
        have hle2 : 2 * 2 ^ (D - j) ≤ 2 ^ D := by
          rw [← pow_succ']; exact Nat.pow_le_pow_right (by norm_num) (by omega)
        generalize p / 2 ^ j = t at hs
        obtain ⟨z0, z1⟩ := hpin (capAnc D p (j + 1)) (by omega) (by omega) h0
        have hbj := capAnc_bounds hp (show j ≤ D by omega)
        have hfj := (hf (capAnc D p j) (by omega) (by omega)).1
        apply hprev
        rcases Nat.mod_two_eq_zero_or_one t with hb0 | hb1
        · rw [hs, hb0, Nat.add_zero] at hfj ⊢
          exact loadHolds_unique hfj z0
        · rw [hs, hb1] at hfj ⊢
          exact loadHolds_unique hfj z1
  have climb : ∀ j, j ≤ D → ∃ cs : List Digest, cs.length = j ∧
      (cell (2 * capAnc D p j), cell (2 * capAnc D p j + 1)) =
        digestHalves (climbK s x p cs) := by
    intro j hjD
    induction j with
    | zero =>
      refine ⟨[], rfl, ?_⟩
      have e : capAnc D p 0 = 2 ^ D + p := by simp [capAnc]
      have hpD := Nat.one_le_two_pow (n := D)
      rw [e, climbK_nil, loadHolds_unique (hc _ (by omega) (by omega)) hx0,
        loadHolds_unique (hc _ (by omega) (by omega)) hx1]
    | succ j ih =>
      obtain ⟨cs, hl, hcs⟩ := ih (by omega)
      have hb := capAnc_bounds hp (show j + 1 ≤ D by omega)
      have hs := capAnc_succ (p := p) (show j < D by omega)
      have hle2 : 2 * 2 ^ (D - (j + 1)) ≤ 2 ^ D := by
        rw [← pow_succ']; exact Nat.pow_le_pow_right (by norm_num) (by omega)
      have hflag : capAnc D p (j + 1) = 1 ∨ fl (capAnc D p (j + 1)) ≠ 0 := by
        rcases Nat.lt_or_ge (j + 1) D with h | h
        · exact Or.inr (chain (j + 1) (by omega) h)
        · left; rw [show j + 1 = D by omega]; exact capAnc_last hp
      obtain ⟨dl, dr, hl', hr', hpar⟩ := hashesPairK_digests
        (hh (capAnc D p (j + 1)) (by have := Nat.one_le_two_pow (n := D - (j + 1)); omega)
          (by omega) hflag)
      rcases Nat.mod_two_eq_zero_or_one (p / 2 ^ j) with hb0 | hb1
      · refine ⟨cs ++ [dr], by simp [hl], ?_⟩
        rw [hs, hb0, Nat.add_zero, show 2 * (2 * capAnc D p (j + 1)) = 4 * capAnc D p (j + 1) by
          ring] at hcs
        have hy : dl = climbK s x p cs := capDigestScalars_injective (hl'.symm.trans hcs)
        rw [climbK_snoc, hl, ite_pos' hb0, ← hy]
        exact hpar
      · refine ⟨cs ++ [dl], by simp [hl], ?_⟩
        rw [hs, hb1, show 2 * (2 * capAnc D p (j + 1) + 1) = 4 * capAnc D p (j + 1) + 2 by
          ring] at hcs
        have hy : dr = climbK s x p cs := capDigestScalars_injective (hr'.symm.trans hcs)
        rw [climbK_snoc, hl, ite_neg' (by omega), ← hy]
        exact hpar
  obtain ⟨cs, hl, hcs⟩ := climb D le_rfl
  rw [capAnc_last hp] at hcs
  simp only [List.cons.injEq, and_true] at hret
  refine ⟨cs, hl, capDigestScalars_injective ?_⟩
  rw [← hcs, ← hroot, hret.1, hret.2]

/-- **A query below the cap reaches the root under the key**: with the cap checked
(`MeaningCapK`, root `root`, the key's cells those of `s`), the node a path of `depth - D`
siblings reaches from `leaf` at the position `q < 2^depth`, written at the cap's leaf
`q / 2^(depth - D)` with its parent flagged, climbs on by `D` siblings of the cap to the root. -/
theorem query_opens_rootK {D depth : ℕ} (hD : 2 ≤ D) (hDd : D ≤ depth) {rd : Reader}
    {cap flags r0 r1 : E} {root s : Digest}
    (hcap : MeaningCapK (2 ^ D) rd [cap, flags] [r0, r1])
    (hkey : ∀ c : Fin 13, LoadHolds rd cap (4 * 2 ^ D + c.val) (keyCells s c))
    (hroot : (r0, r1) = digestHalves root) {q : ℕ} (hq : q < 2 ^ depth) {leaf : Digest}
    {sibs : List Digest} (hsl : sibs.length = depth - D)
    (h0 : LoadHolds rd cap (2 * (2 ^ D + q / 2 ^ (depth - D)))
      (digestHalves (climbK s leaf q sibs)).1)
    (h1 : LoadHolds rd cap (2 * (2 ^ D + q / 2 ^ (depth - D)) + 1)
      (digestHalves (climbK s leaf q sibs)).2)
    (hfl : LoadHolds rd flags (2 ^ (D - 1) + q / 2 ^ (depth - D + 1)) 1) :
    ∃ capSibs : List Digest, capSibs.length = D ∧ climbK s leaf q (sibs ++ capSibs) = root := by
  have hp : q / 2 ^ (depth - D) < 2 ^ D := by
    rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _), ← pow_add, Nat.add_sub_cancel' hDd]
    exact hq
  have hf2 : q / 2 ^ (depth - D + 1) = q / 2 ^ (depth - D) / 2 := by
    rw [Nat.div_div_eq_div_mul, pow_succ]
  rw [hf2] at hfl
  obtain ⟨cs, hcl, hc⟩ := cap_climbK hD hcap hkey hroot hp h0 h1 hfl
  exact ⟨cs, hcl, by rw [climbK_append, hsl, hc]⟩

end
end LeanVM.SaltedGuest.B1
