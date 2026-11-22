/-
  LeanVM.SaltedGuest.Decoder.Cells

  Frame cells packed into blocks of natural numbers, and a cell read off them.
-/

module

public import Mathlib.Tactic.Ring

/-!
# Frame cells, packed

The salted decoder holds a function's frame cells (each below `2^16`) as a list of natural
numbers, each the next `64` cells in base `2^16`, the first lowest (`packCells`), and reads cell
`i` off it by an index, a shift and a remainder (`cellIn`).

* `blocksOk l bs`: the blocks `bs` are the cells `l` packed (`packOk` on each `64`);
  **`cellIn_of_blocksOk`**: then cell `i` is `l`'s (`0` past its end);
* `blocksOkN n`, `blocksOk_of_split`: the first `n` blocks and the rest, for a long row's check in
  pieces;
* `rowsOkP n ls bss`: the first `n` rows and their blocks, in step (`rowsOkP_get`), for a check of
  consecutive rows.
-/

namespace LeanVM.SaltedGuest.Decoder

@[expose] public section

/-- **A list of cells, packed**: in base `2^16`, the first lowest. -/
def packCells : List ℕ → ℕ
  | [] => 0
  | c :: l => c + 65536 * packCells l

/-- **Cell `i` of a packed number.** -/
def packedCell (r i : ℕ) : ℕ := (r >>> (16 * i)) % 65536

/-- The packed number `r` of the cells `l`, each below `2^16`. -/
def packOk (l : List ℕ) (r : ℕ) : Bool := r == packCells l && l.all fun c ↦ decide (c < 65536)

/-- **A cell of a packed number is the list's.** -/
theorem packedCell_packCells : ∀ (l : List ℕ), (∀ c ∈ l, c < 65536) → ∀ i,
    packedCell (packCells l) i = l.getD i 0
  | [], _, i => by simp [packedCell, packCells]
  | c :: l, h, 0 => by
    have hc := h c List.mem_cons_self
    simp only [packedCell, packCells, Nat.mul_zero, Nat.shiftRight_zero, List.getD_cons_zero]
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hc]
  | c :: l, h, i + 1 => by
    have hc := h c List.mem_cons_self
    have ih := packedCell_packCells l (fun x hx ↦ h x (List.mem_cons_of_mem _ hx)) i
    have hdiv : (c + 65536 * packCells l) >>> 16 = packCells l := by
      rw [Nat.shiftRight_eq_div_pow, show (2 : ℕ) ^ 16 = 65536 by norm_num,
        Nat.add_mul_div_left _ _ (by norm_num), Nat.div_eq_of_lt hc, Nat.zero_add]
    simp only [packedCell, packCells, List.getD_cons_succ] at ih ⊢
    rw [show 16 * (i + 1) = 16 + 16 * i by ring, Nat.shiftRight_add, hdiv, ih]

theorem packedCell_of_packOk {l : List ℕ} {r : ℕ} (h : packOk l r = true) (i : ℕ) :
    packedCell r i = l.getD i 0 := by
  simp only [packOk, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, decide_eq_true_eq] at h
  rw [h.1]
  exact packedCell_packCells l h.2 i

theorem packedCell_zero (i : ℕ) : packedCell 0 i = 0 := by simp [packedCell]

/-! ## Blocks -/

/-- **The blocks `bs` are the cells `l` packed**, `64` to a block. -/
def blocksOk : List ℕ → List ℕ → Bool
  | l, b :: bs => packOk (l.take 64) b && blocksOk (l.drop 64) bs
  | l, [] => l.isEmpty

/-- The first `n` blocks of `bs` are those of the cells `l`. -/
def blocksOkN : ℕ → List ℕ → List ℕ → Bool
  | 0, _, _ => true
  | n + 1, l, b :: bs => packOk (l.take 64) b && blocksOkN n (l.drop 64) bs
  | _ + 1, l, [] => l.isEmpty

/-- **Cell `i` of packed blocks.** -/
def cellIn (bs : List ℕ) (i : ℕ) : ℕ := packedCell (bs.getD (i / 64) 0) (i % 64)

theorem cellIn_of_blocksOk : ∀ {bs : List ℕ} {l : List ℕ}, blocksOk l bs = true → ∀ i,
    cellIn bs i = l.getD i 0
  | [], l, h, i => by
    simp only [blocksOk, List.isEmpty_iff] at h
    subst h
    simp [cellIn, packedCell_zero]
  | b :: bs, l, h, i => by
    simp only [blocksOk, Bool.and_eq_true] at h
    by_cases hi : i < 64
    · rw [cellIn, Nat.div_eq_of_lt hi, Nat.mod_eq_of_lt hi, List.getD_cons_zero,
        packedCell_of_packOk h.1, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
        List.getElem?_take_of_lt hi]
    · have ih := cellIn_of_blocksOk h.2 (i - 64)
      have h1 : i / 64 = (i - 64) / 64 + 1 := by omega
      have h2 : i % 64 = (i - 64) % 64 := by omega
      rw [cellIn, h1, h2, List.getD_cons_succ]
      rw [cellIn] at ih
      rw [ih, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_drop,
        show 64 + (i - 64) = i by omega]

/-- **A check in two pieces**: the first `n` blocks, and the rest. -/
theorem blocksOk_of_split : ∀ (n : ℕ) {l bs : List ℕ}, blocksOkN n l bs = true →
    blocksOk (l.drop (64 * n)) (bs.drop n) = true → blocksOk l bs = true
  | 0, l, bs, _, h => by simpa using h
  | n + 1, l, b :: bs, h1, h2 => by
    simp only [blocksOkN, Bool.and_eq_true] at h1
    simp only [blocksOk, Bool.and_eq_true]
    refine ⟨h1.1, blocksOk_of_split n h1.2 ?_⟩
    rw [List.drop_drop, show 64 + 64 * n = 64 * (n + 1) by ring]
    simpa using h2
  | n + 1, l, [], h1, _ => by
    simp only [blocksOkN] at h1
    simpa [blocksOk] using h1

/-- **A check in pieces of `nb` blocks**: `k` pieces, and the rest. -/
theorem blocksOk_of_pieces (nb : ℕ) : ∀ (k : ℕ) {l bs : List ℕ},
    (∀ i < k, blocksOkN nb (l.drop (64 * nb * i)) (bs.drop (nb * i)) = true) →
    blocksOk (l.drop (64 * nb * k)) (bs.drop (nb * k)) = true → blocksOk l bs = true
  | 0, l, bs, _, h => by simpa using h
  | k + 1, l, bs, hp, h => by
    refine blocksOk_of_split nb (by simpa using hp 0 (by omega)) ?_
    refine blocksOk_of_pieces nb k (fun i hi ↦ ?_) ?_
    · have := hp (i + 1) (by omega)
      rwa [List.drop_drop, List.drop_drop, show 64 * nb + 64 * nb * i = 64 * nb * (i + 1) by ring,
        show nb + nb * i = nb * (i + 1) by ring]
    · rwa [List.drop_drop, List.drop_drop, show 64 * nb + 64 * nb * k = 64 * nb * (k + 1) by ring,
        show nb + nb * k = nb * (k + 1) by ring]

/-! ## Rows -/

/-- **The first `n` rows `ls` and their blocks `bss`, in step.** -/
def rowsOkP : ℕ → List (List ℕ) → List (List ℕ) → Bool
  | 0, _, _ => true
  | n + 1, l :: ls, bs :: bss => blocksOk l bs && rowsOkP n ls bss
  | _ + 1, _, _ => false

theorem rowsOkP_get : ∀ {n : ℕ} {ls bss : List (List ℕ)}, rowsOkP n ls bss = true → ∀ i < n,
    blocksOk (ls.getD i []) (bss.getD i []) = true
  | 0, _, _, _, i, hi => absurd hi (Nat.not_lt_zero i)
  | n + 1, l :: ls, bs :: bss, h, i, hi => by
    simp only [rowsOkP, Bool.and_eq_true] at h
    cases i with
    | zero => simpa using h.1
    | succ i => simpa using rowsOkP_get h.2 i (by omega)
  | _ + 1, [], _, h, _, _ => by simp [rowsOkP] at h
  | _ + 1, _ :: _, [], h, _, _ => by simp [rowsOkP] at h

/-! ## Four parts of `512` rows -/

section Parts

variable {α : Type} {A0 A1 A2 A3 : List α} {j : ℕ} {d : α}

theorem getD_app_left {A B : List α} (h : j < A.length) : (A ++ B).getD j d = A.getD j d := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_app_right {A B : List α} (h : A.length ≤ j) :
    (A ++ B).getD j d = B.getD (j - A.length) d := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right h]

theorem getD_parts4_0 (h0 : A0.length = 512) (hj : j < 512) :
    (A0 ++ A1 ++ A2 ++ A3).getD j d = A0.getD (j - 0) d := by
  rw [getD_app_left (by simp only [List.length_append]; omega),
    getD_app_left (by simp only [List.length_append]; omega), getD_app_left (by omega), Nat.sub_zero]

theorem getD_parts4_1 (h0 : A0.length = 512) (h1 : A1.length = 512) (hj1 : 512 ≤ j)
    (hj2 : j < 1024) : (A0 ++ A1 ++ A2 ++ A3).getD j d = A1.getD (j - 512) d := by
  rw [getD_app_left (by simp only [List.length_append]; omega),
    getD_app_left (by simp only [List.length_append]; omega), getD_app_right (by omega), h0]

theorem getD_parts4_2 (h0 : A0.length = 512) (h1 : A1.length = 512) (h2 : A2.length = 512)
    (hj1 : 1024 ≤ j) (hj2 : j < 1536) : (A0 ++ A1 ++ A2 ++ A3).getD j d = A2.getD (j - 1024) d := by
  rw [getD_app_left (by simp only [List.length_append]; omega),
    getD_app_right (by simp only [List.length_append]; omega), List.length_append, h0, h1]

theorem getD_parts4_3 (h0 : A0.length = 512) (h1 : A1.length = 512) (h2 : A2.length = 512)
    (hj : 1536 ≤ j) : (A0 ++ A1 ++ A2 ++ A3).getD j d = A3.getD (j - 1536) d := by
  rw [getD_app_right (by simp only [List.length_append]; omega), List.length_append,
    List.length_append, h0, h1, h2]

end Parts

/-- Rows `s … s + n - 1` of `ls`, checked from `ls.drop s`. -/
theorem rowsOkP_drop {n s : ℕ} {ls bss : List (List ℕ)}
    (h : rowsOkP n (ls.drop s) (bss.drop s) = true) {j : ℕ} (h1 : s ≤ j) (h2 : j < s + n) :
    blocksOk (ls.getD j []) (bss.getD j []) = true := by
  have := rowsOkP_get h (j - s) (by omega)
  simp only [List.getD_eq_getElem?_getD, List.getElem?_drop] at this
  rwa [show s + (j - s) = j by omega] at this

end

end LeanVM.SaltedGuest.Decoder
