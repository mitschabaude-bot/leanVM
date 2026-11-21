/-
  LeanVM.SaltedGuest.B1.Merkle.OpenK

  A query's opening against a cap checked under the key passes the verifier's check at the keyed
  hash.
-/

module

public import LeanVM.SaltedGuest.B1.Merkle.ClimbK
public import LeanVM.Guest.B1.Whir.QueriesOpenW

/-!
# Openings at the keyed hash

The deployed `Whir.cap_climb_w` and `Whir.query_openOne_w` under the key `s`: with the cap
checked under the key (`MeaningCapK`, the key's cells those of `s`), the cap's siblings its cells
hold (`capSibsOf`) climb a cap leaf to the root under the key (`cap_climb_wK`), and a query's
opening (`toOpening`: its row, its siblings below the cap, the cap's) passes
`openOneWithHash (keyedHash s)` (`query_openOne_wK`), the leaf hashed under the key.
-/

namespace LeanVM.SaltedGuest.B1.Merkle

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest LeanVM.Guest.B1
open LeanVM.Guest.Value LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile
open LeanVM.Protocol.Verifier LeanVM.Guest.B1.Whir LeanVM.SaltedGuest.B1 Recursion.Salted

@[expose] public section

variable {rd : Reader}

theorem cap_climb_wK {D : ℕ} (hD : 2 ≤ D) {cap flags r0 r1 : E} {root s : Digest}
    (hcap : MeaningCapK (2 ^ D) rd [cap, flags] [r0, r1])
    (hkey : ∀ c : Fin 13, LoadHolds rd cap (4 * 2 ^ D + c.val) (keyCells s c))
    (hroot : (r0, r1) = digestHalves root) {p : ℕ} (hp : p < 2 ^ D) {x : Digest}
    (hx0 : LoadHolds rd cap (2 * (2 ^ D + p)) (digestHalves x).1)
    (hx1 : LoadHolds rd cap (2 * (2 ^ D + p) + 1) (digestHalves x).2)
    (hfl : LoadHolds rd flags (2 ^ (D - 1) + p / 2) 1) :
    climbK s x p (capSibsOf rd cap D p) = root := by
  obtain ⟨kc, cell, fl, hk, hc, hf, hh0, hpin, hret⟩ := hcap
  have hks : kc = keyCells s := funext fun c ↦ loadHolds_unique (hk c) (hkey c)
  have hh := hh0 s hks
  have hD2 : 2 ^ (D + 2) = 4 * 2 ^ D := by rw [pow_add]; ring
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
  have climb : ∀ j, j ≤ D →
      (cell (2 * capAnc D p j), cell (2 * capAnc D p j + 1)) =
        digestHalves (climbK s x p ((capSibsOf rd cap D p).take j)) := by
    intro j hjD
    induction j with
    | zero =>
      have e : capAnc D p 0 = 2 ^ D + p := by simp [capAnc]
      have hpD := Nat.one_le_two_pow (n := D)
      rw [List.take_zero, e, climbK_nil, loadHolds_unique (hc _ (by omega) (by omega)) hx0,
        loadHolds_unique (hc _ (by omega) (by omega)) hx1]
    | succ j ih =>
      have hcs := ih (by omega)
      have hb := capAnc_bounds hp (show j + 1 ≤ D by omega)
      have hbj := capAnc_bounds hp (show j ≤ D by omega)
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
      have hlen : ((capSibsOf rd cap D p).take j).length = j := by
        rw [List.length_take, capSibsOf_length]; omega
      rw [take_capSibsOf_succ (by omega), climbK_snoc, hlen]
      set A := capAnc D p (j + 1) with hA
      have hcell : ∀ k, 2 ≤ k → k < 2 ^ (D + 2) → memRead rd cap k = cell k :=
        fun k h1 h2 ↦ memRead_of_load (hc k h1 (by omega))
      rcases Nat.mod_two_eq_zero_or_one (p / 2 ^ j) with hb0 | hb1
      · have hsib : capSib D p j = 2 * A + 1 := by
          unfold capSib; simp only [hb0, ↓reduceIte]; unfold capAnc at hs; omega
        rw [hs, hb0, Nat.add_zero, show 2 * (2 * A) = 4 * A by ring] at hcs
        have hy : dl = climbK s x p ((capSibsOf rd cap D p).take j) :=
          capDigestScalars_injective (hl'.symm.trans hcs)
        have hdr : digestOfCells (memRead rd cap (2 * capSib D p j))
            (memRead rd cap (2 * capSib D p j + 1)) = dr := by
          rw [hsib, hcell _ (by omega) (by omega), hcell _ (by omega) (by omega),
            show 2 * (2 * A + 1) = 4 * A + 2 by ring, show 4 * A + 2 + 1 = 4 * A + 3 by ring]
          simp only [Prod.ext_iff] at hr'
          rw [hr'.1, hr'.2, digestOfCells_scalars]
        simp only [hb0, ↓reduceIte]
        rw [← hy, hdr]
        exact hpar
      · have hsib : capSib D p j = 2 * A := by
          unfold capSib; simp only [show ¬ (p / 2 ^ j % 2 = 0) by omega, ↓reduceIte]; unfold capAnc at hs; omega
        rw [hs, hb1, show 2 * (2 * A + 1) = 4 * A + 2 by ring] at hcs
        have hy : dr = climbK s x p ((capSibsOf rd cap D p).take j) :=
          capDigestScalars_injective (hr'.symm.trans hcs)
        have hdl : digestOfCells (memRead rd cap (2 * capSib D p j))
            (memRead rd cap (2 * capSib D p j + 1)) = dl := by
          rw [hsib, hcell _ (by omega) (by omega), hcell _ (by omega) (by omega),
            show 2 * (2 * A) = 4 * A by ring]
          simp only [Prod.ext_iff] at hl'
          rw [hl'.1, hl'.2, digestOfCells_scalars]
        simp only [show ¬ (p / 2 ^ j % 2 = 0) by omega, ↓reduceIte]
        rw [← hy, hdl]
        exact hpar
  have hcs := climb D le_rfl
  rw [capAnc_last hp, List.take_of_length_le (by rw [capSibsOf_length])] at hcs
  simp only [List.cons.injEq, and_true] at hret
  refine capDigestScalars_injective ?_
  rw [← hcs, ← hroot, hret.1, hret.2]

/-- **A query's opening passes `openOne` at the keyed hash**: its row, its siblings below the cap,
then the cap's siblings its cells hold. -/
theorem query_openOne_wK {D depth width : ℕ} (hD : 2 ≤ D) (hDd : D ≤ depth)
    {cap flags r0 r1 : E} {root s : Digest}
    (hcap : MeaningCapK (2 ^ D) rd [cap, flags] [r0, r1])
    (hkey : ∀ c : Fin 13, LoadHolds rd cap (4 * 2 ^ D + c.val) (keyCells s c))
    (hroot : (r0, r1) = digestHalves root) {q : ℕ} (hq : q < 2 ^ depth) {row : List K}
    (hw : row.length = width) {sibs : List Digest} (hsl : sibs.length = depth - D)
    (h0 : LoadHolds rd cap (2 * (2 ^ D + q / 2 ^ (depth - D)))
      (digestHalves (climbK s (keyedHash s (row.flatMap K.toBytes)) q sibs)).1)
    (h1 : LoadHolds rd cap (2 * (2 ^ D + q / 2 ^ (depth - D)) + 1)
      (digestHalves (climbK s (keyedHash s (row.flatMap K.toBytes)) q sibs)).2)
    (hfl : LoadHolds rd flags (2 ^ (D - 1) + q / 2 ^ (depth - D + 1)) 1) :
    Id.run (Compile.openOneWithHash (m := Id) (keyedHash s) root depth width q
      (toOpening rd cap D depth (q, row, sibs))) = true := by
  have hp : q / 2 ^ (depth - D) < 2 ^ D := by
    rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _), ← pow_add, Nat.add_sub_cancel' hDd]
    exact hq
  have hf2 : q / 2 ^ (depth - D + 1) = q / 2 ^ (depth - D) / 2 := by
    rw [Nat.div_div_eq_div_mul, pow_succ]
  rw [hf2] at hfl
  have hc := cap_climb_wK hD hcap hkey hroot hp h0 h1 hfl
  unfold Compile.openOneWithHash toOpening
  rw [ite_pos' ⟨hw, by simp [hsl, capSibsOf_length]; omega⟩]
  show decide ((climbK s (keyedHash s (row.flatMap K.toBytes)) q (sibs ++ capSibsOf rd cap D (q / 2 ^ (depth - D)))).toList =
    root.toList) = true
  rw [climbK_append, hsl, hc]
  exact decide_eq_true rfl

end
end LeanVM.SaltedGuest.B1.Merkle
