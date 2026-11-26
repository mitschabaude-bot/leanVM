/-
  LeanVM.Protocol.Keccak.Perm

  A segment of Keccak-f[1600] is a permutation of the state.
-/

module

public import LeanVM.Protocol.Keccak.Bits
public import LeanVM.Semantics.KeccakCells

/-!
# The segments of Keccak-f are permutations

A round of Keccak-f[1600] on bits is `ι ∘ χ ∘ L`, `L = π ∘ ρ ∘ θ` (`sbit_round`). Each step is
injective on the state's `1600` bits:

* ι adds a constant, and ρ and π move bits (`rhoPiSrc`, with its inverse `rhoPiDst`);
* χ acts on each row of five bits of a slice by a map that is injective on five bits
  (`chi_row_injective`, decided on the `2^10` pairs);
* θ adds to each bit two column parities, so it maps the column parities `P` by
  `parityMap P = P + P(x - 1, z) + P(x + 1, z - 1)`, and leaves a bit recoverable from its image and
  the parities. In characteristic two, `parityMap` iterated `2^k` times is
  `P + P(x - 2^k, z) + P(x + 2^k, z - 2^k)` (`parityMap_iterate`); at `2^6 = 64` it is
  `P + P(x - 1, z) + P(x + 1, z)` on each slice, injective on five bits (`slice_injective`), so
  `parityMap` is injective (`parityMap_injective`) and so is θ (`thetaB_injective`).

A state is its bits (`ext_sbit`), so a round is injective (`round_injective`), a segment too
(`keccakSegment_injective`), and on the finite state space bijective (`keccakSegment_bijective`).
`keccakSegmentPerm m` is segment `m` as a permutation of the state.
-/

namespace LeanVM.Protocol.KeccakGkr

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.Verifier

@[expose] public section

/-- Exclusive or, `xor` (CompPoly's `^^` is a product of finsets). -/
local infixl:33 " ⊻ " => xor

/-! ## A state is its bits -/

/-- **Two states with the same bits are equal.** -/
theorem ext_sbit {a b : KeccakState} (h : ∀ j < 1600, sbit a j = sbit b j) : a = b := by
  apply Vector.ext
  intro i hi
  apply UInt64.toBitVec_inj.mp
  apply BitVec.eq_of_getLsbD_eq
  intro z hz
  have e := h (64 * i + z) (by omega)
  rwa [sbit_lane _ _ hz, sbit_lane _ _ hz, lane_eq _ hi, lane_eq _ hi] at e

theorem xor_cancel_right {x y c : Bool} (h : (x ⊻ c) = (y ⊻ c)) : x = y := by
  cases x <;> cases y <;> cases c <;> simp_all

/-! ## θ's map on column parities -/

/-- **θ's map on column parities**: the parity of column `x` at slice `z` gains the parities of
column `x - 1` at `z` and of column `x + 1` at `z - 1`. -/
def parityMap (P : ℕ → ℕ → Bool) (x z : ℕ) : Bool :=
  P x z ⊻ P ((x + 4) % 5) z ⊻ P ((x + 1) % 5) ((z + 63) % 64)

/-- `parityMap` iterated `a = 2^k` times: column `x - a` at `z`, column `x + a` at `z - a`. -/
def parityPow (a : ℕ) (P : ℕ → ℕ → Bool) (x z : ℕ) : Bool :=
  P x z ⊻ P ((x + 4 * a) % 5) z ⊻ P ((x + a) % 5) ((z + 63 * a) % 64)

/-- **`parityMap` iterated `2^k` times**, by squaring in characteristic two. -/
theorem parityMap_iterate (k : ℕ) :
    ∀ (P : ℕ → ℕ → Bool) {x z : ℕ}, x < 5 → z < 64 →
      (parityMap^[2 ^ k]) P x z = parityPow (2 ^ k) P x z := by
  induction k with
  | zero =>
    intro P x z _ _
    simp only [pow_zero, Function.iterate_one, parityMap, parityPow, Nat.mul_one]
  | succ k ih =>
    intro P x z hx hz
    rw [pow_succ, Nat.mul_two, Function.iterate_add_apply, ih _ hx hz]
    unfold parityPow
    rw [ih _ hx hz, ih _ (Nat.mod_lt _ (by omega)) hz,
      ih _ (Nat.mod_lt _ (by omega)) (Nat.mod_lt _ (by omega))]
    unfold parityPow
    generalize 2 ^ k = a
    have e1 : ((x + 4 * a) % 5 + 4 * a) % 5 = (x + 4 * (a + a)) % 5 := by omega
    have e2 : ((x + 4 * a) % 5 + a) % 5 = x := by omega
    have e3 : ((x + a) % 5 + 4 * a) % 5 = x := by omega
    have e4 : ((x + a) % 5 + a) % 5 = (x + (a + a)) % 5 := by omega
    have e5 : ((z + 63 * a) % 64 + 63 * a) % 64 = (z + 63 * (a + a)) % 64 := by omega
    rw [e1, e2, e3, e4, e5]
    generalize P x z = b0
    generalize P ((x + 4 * a) % 5) z = b1
    generalize P ((x + a) % 5) ((z + 63 * a) % 64) = b2
    generalize P ((x + 4 * (a + a)) % 5) z = b3
    generalize P x ((z + 63 * a) % 64) = b4
    generalize P ((x + (a + a)) % 5) ((z + 63 * (a + a)) % 64) = b5
    cases b0 <;> cases b1 <;> cases b2 <;> cases b3 <;> cases b4 <;> cases b5 <;> rfl

/-- **On a slice, `x ↦ P x + P (x + 1) + P (x - 1)` is injective** on five bits. -/
theorem slice_injective {p q : ℕ → Bool}
    (h : ∀ x < 5, (p x ⊻ p ((x + 1) % 5) ⊻ p ((x + 4) % 5)) =
      (q x ⊻ q ((x + 1) % 5) ⊻ q ((x + 4) % 5))) : ∀ x < 5, p x = q x := by
  have key : ∀ a0 a1 a2 a3 a4 b0 b1 b2 b3 b4 : Bool,
      (a0 ⊻ a1 ⊻ a4) = (b0 ⊻ b1 ⊻ b4) → (a1 ⊻ a2 ⊻ a0) = (b1 ⊻ b2 ⊻ b0) →
      (a2 ⊻ a3 ⊻ a1) = (b2 ⊻ b3 ⊻ b1) → (a3 ⊻ a4 ⊻ a2) = (b3 ⊻ b4 ⊻ b2) →
      (a4 ⊻ a0 ⊻ a3) = (b4 ⊻ b0 ⊻ b3) →
      a0 = b0 ∧ a1 = b1 ∧ a2 = b2 ∧ a3 = b3 ∧ a4 = b4 := by decide
  have k := key _ _ _ _ _ _ _ _ _ _ (h 0 (by omega)) (h 1 (by omega)) (h 2 (by omega))
    (h 3 (by omega)) (h 4 (by omega))
  intro x hx
  interval_cases x
  · exact k.1
  · exact k.2.1
  · exact k.2.2.1
  · exact k.2.2.2.1
  · exact k.2.2.2.2

/-- Parities agreeing on the columns and slices. -/
def ParEq (P Q : ℕ → ℕ → Bool) : Prop := ∀ x < 5, ∀ z < 64, P x z = Q x z

theorem parityMap_congr {P Q : ℕ → ℕ → Bool} (h : ParEq P Q) : ParEq (parityMap P) (parityMap Q) :=
  fun x _ z hz ↦ by
    unfold parityMap
    rw [h x (by omega) z hz, h _ (Nat.mod_lt _ (by omega)) z hz,
      h _ (Nat.mod_lt _ (by omega)) _ (Nat.mod_lt _ (by omega))]

theorem parityMap_iterate_congr : ∀ (n : ℕ) {P Q : ℕ → ℕ → Bool}, ParEq P Q →
    ParEq (parityMap^[n] P) (parityMap^[n] Q)
  | 0, _, _, h => h
  | n + 1, _, _, h => by
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply]
    exact parityMap_iterate_congr n (parityMap_congr h)

/-- **`parityMap` is injective** on the columns and slices. -/
theorem parityMap_injective {P Q : ℕ → ℕ → Bool} (h : ParEq (parityMap P) (parityMap Q)) :
    ParEq P Q := by
  have h64 : ParEq (parityMap^[2 ^ 6] P) (parityMap^[2 ^ 6] Q) := by
    rw [show 2 ^ 6 = 63 + 1 from rfl, Function.iterate_succ_apply, Function.iterate_succ_apply]
    exact parityMap_iterate_congr 63 h
  intro x hx z hz
  refine slice_injective (p := fun x ↦ P x z) (q := fun x ↦ Q x z) (fun x hx ↦ ?_) x hx
  have e := h64 x hx z hz
  rw [parityMap_iterate 6 _ hx hz, parityMap_iterate 6 _ hx hz] at e
  unfold parityPow at e
  have e1 : (x + 4 * 2 ^ 6) % 5 = (x + 1) % 5 := by simp only [Nat.reducePow, Nat.reduceMul]; omega
  have e2 : (x + 2 ^ 6) % 5 = (x + 4) % 5 := by simp only [Nat.reducePow]; omega
  have e3 : (z + 63 * 2 ^ 6) % 64 = z := by simp only [Nat.reducePow, Nat.reduceMul]; omega
  rw [e1, e2, e3] at e
  exact e

/-! ## θ on bits -/

theorem colB_eq (f : ℕ → Bool) (x z : ℕ) :
    colB f x z = (f (64 * x + z) ⊻ f (64 * (x + 5) + z) ⊻ f (64 * (x + 10) + z) ⊻
      f (64 * (x + 15) + z) ⊻ f (64 * (x + 20) + z)) := rfl

/-- θ at a bit of column `x` and slice `z`. -/
theorem thetaB_at (f : ℕ → Bool) {p x z : ℕ} (hx : p / 64 % 5 = x) (hz : p % 64 = z) :
    thetaB f p = (f p ⊻ (colB f ((x + 4) % 5) z ⊻ colB f ((x + 1) % 5) ((z + 63) % 64))) := by
  unfold thetaB
  rw [hx, hz, Bool.xor_assoc]

/-- **θ maps the column parities by `parityMap`.** -/
theorem colB_thetaB (f : ℕ → Bool) {x z : ℕ} (hx : x < 5) (hz : z < 64) :
    colB (thetaB f) x z = parityMap (colB f) x z := by
  rw [colB_eq (thetaB f), thetaB_at f (p := 64 * x + z) (x := x) (z := z) (by omega) (by omega),
    thetaB_at f (p := 64 * (x + 5) + z) (x := x) (z := z) (by omega) (by omega),
    thetaB_at f (p := 64 * (x + 10) + z) (x := x) (z := z) (by omega) (by omega),
    thetaB_at f (p := 64 * (x + 15) + z) (x := x) (z := z) (by omega) (by omega),
    thetaB_at f (p := 64 * (x + 20) + z) (x := x) (z := z) (by omega) (by omega)]
  unfold parityMap
  rw [colB_eq f x z]
  generalize colB f ((x + 4) % 5) z = d1
  generalize colB f ((x + 1) % 5) ((z + 63) % 64) = d2
  generalize f (64 * x + z) = b0
  generalize f (64 * (x + 5) + z) = b1
  generalize f (64 * (x + 10) + z) = b2
  generalize f (64 * (x + 15) + z) = b3
  generalize f (64 * (x + 20) + z) = b4
  cases d1 <;> cases d2 <;> cases b0 <;> cases b1 <;> cases b2 <;> cases b3 <;> cases b4 <;> rfl

/-- **θ is injective on bits.** -/
theorem thetaB_injective {f g : ℕ → Bool} (h : ∀ p < 1600, thetaB f p = thetaB g p) :
    ∀ p < 1600, f p = g p := by
  have hc : ParEq (colB f) (colB g) := by
    refine parityMap_injective fun x hx z hz ↦ ?_
    rw [← colB_thetaB f hx hz, ← colB_thetaB g hx hz, colB_eq, colB_eq]
    rw [h _ (by omega), h _ (by omega), h _ (by omega), h _ (by omega), h _ (by omega)]
  intro p hp
  have e := h p hp
  rw [thetaB_at f rfl rfl, thetaB_at g rfl rfl,
    hc _ (Nat.mod_lt _ (by omega)) _ (Nat.mod_lt _ (by omega)),
    hc _ (Nat.mod_lt _ (by omega)) _ (Nat.mod_lt _ (by omega))] at e
  exact xor_cancel_right e

/-! ## χ on bits -/

/-- **χ on a row of five bits is injective.** -/
theorem chi_row_injective : ∀ a0 a1 a2 a3 a4 b0 b1 b2 b3 b4 : Bool,
    (a0 ⊻ (!a1 && a2)) = (b0 ⊻ (!b1 && b2)) → (a1 ⊻ (!a2 && a3)) = (b1 ⊻ (!b2 && b3)) →
    (a2 ⊻ (!a3 && a4)) = (b2 ⊻ (!b3 && b4)) → (a3 ⊻ (!a4 && a0)) = (b3 ⊻ (!b4 && b0)) →
    (a4 ⊻ (!a0 && a1)) = (b4 ⊻ (!b0 && b1)) → a0 = b0 := by decide

theorem keccakAlong_along' {j : ℕ} (k m : ℕ) :
    keccakAlong (keccakAlong j k) m = keccakAlong j ((k + m) % 5) := by
  rw [keccakAlong_def, keccakAlong_def, keccakAlong_def]
  omega

/-- **χ is injective on bits.** -/
theorem chiB_injective {b b' : ℕ → Bool} (h : ∀ j < 1600, chiB b j = chiB b' j) :
    ∀ j < 1600, b j = b' j := by
  intro j hj
  have hk : ∀ k, chiB b (keccakAlong j k) = chiB b' (keccakAlong j k) :=
    fun k ↦ h _ (keccakAlong_lt k hj)
  simp only [chiB, keccakAlong_along'] at hk
  have h0 := hk 0
  have h1 := hk 1
  have h2 := hk 2
  have h3 := hk 3
  have h4 := hk 4
  simp only [Nat.reduceAdd, Nat.reduceMod] at h0 h1 h2 h3 h4
  have e := chi_row_injective _ _ _ _ _ _ _ _ _ _ h0 h1 h2 h3 h4
  rwa [keccakAlong_zero hj] at e

/-! ## A round, a segment -/

/-- **`L = π ∘ ρ ∘ θ` is injective on bits.** -/
theorem Lb_injective {f g : ℕ → Bool} (h : ∀ j < 1600, Lb f j = Lb g j) :
    ∀ p < 1600, f p = g p :=
  thetaB_injective fun p hp ↦ by
    have e := h (rhoPiDst p) (rhoPiDst_lt hp)
    unfold Lb at e
    rwa [rhoPiSrc_dst hp] at e

/-- **A round of Keccak-f[1600] is injective.** -/
theorem round_injective (rc : UInt64) : Function.Injective fun a ↦ Keccak.round a rc := by
  intro a b hab
  have hab : Keccak.round a rc = Keccak.round b rc := hab
  refine ext_sbit (Lb_injective (chiB_injective fun j hj ↦ ?_))
  have e := congrArg (fun s ↦ sbit s j) hab
  simp only [sbit_round _ _ hj, roundB] at e
  exact xor_cancel_right e

theorem foldl_round_injective : ∀ l : List UInt64, Function.Injective fun a ↦ l.foldl Keccak.round a
  | [] => fun _ _ h ↦ h
  | rc :: l => fun a b h ↦ by
    simp only [List.foldl_cons] at h
    exact round_injective rc (foldl_round_injective l h)

/-- **A segment of Keccak-f[1600] is injective.** -/
theorem keccakSegment_injective (m : ℕ) : Function.Injective (keccakSegment m) :=
  foldl_round_injective _

instance : Finite KeccakState :=
  Finite.of_injective (fun v : KeccakState ↦ fun i : Fin 25 ↦ v[i].toFin) fun a b h ↦ by
    apply Vector.ext
    intro i hi
    exact UInt64.toFin_inj.mp (congrFun h ⟨i, hi⟩)

/-- **A segment of Keccak-f[1600] is a bijection of the state.** -/
theorem keccakSegment_bijective (m : ℕ) : Function.Bijective (keccakSegment m) :=
  Finite.injective_iff_bijective.mp (keccakSegment_injective m)

/-- **Segment `m` of Keccak-f[1600] as a permutation of the state.** -/
noncomputable def keccakSegmentPerm (m : ℕ) : Equiv.Perm KeccakState :=
  Equiv.ofBijective (keccakSegment m) (keccakSegment_bijective m)

end
end LeanVM.Protocol.KeccakGkr
