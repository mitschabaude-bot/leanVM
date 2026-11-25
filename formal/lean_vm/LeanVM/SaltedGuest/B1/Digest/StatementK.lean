/-
  LeanVM.SaltedGuest.B1.Digest.StatementK

  B1 for the salted `statement_digest`: the statement's digest with its node count, byte for byte.
-/

module

public import LeanVM.SaltedGuest.B1.Callee
public import LeanVM.Guest.B1.Digest.Statement
public import LeanVM.Guest.B1.Digest.Chain

/-!
# The salted `statement_digest`

`statement_digest(seed_0, seed_1, xd_0, xd_1, sd_0, sd_1, da_0, da_1, defer, count_g)` hashes 45
cells: the seed's two cells, the two claim lists' digests' two each, the DA digest's two, the 24
deferred cells (read at `defer`) two at a time as three canonical cells each (`pack_pair`), then the
node count's cell `count_g`, `720` bytes in six `KECCAK` blocks, the last holding bytes
`680 … 719`, the padding's `0x01` (byte `720`, cell `45`) and `0x80` (byte `815`, cell `50`). Its
core IR (`Data.core21`) is the template `sdAtomsK` (`core21K_body`, by kernel evaluation): the
deployed `sdAtoms` with the values from `9` on moved by one, the count's cell copied to `342`, and
the last block reading cells `42`, `43`, `44` and the padding's `0x01` cell.

`MeaningStatementDigestK`: the header cells and the count's cell are canonical, and the function
returns the two cells of the Keccak-256 digest of the header cells, the deferred cells' limbs and
the count's cell. `statement_digest_soundK`.
-/

namespace LeanVM.SaltedGuest.B1.Digest

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Guest.Value.Keccak LeanVM.Guest.B1 LeanVM.Guest.B1.Digest
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-! ## The meaning -/

/-- **The salted `statement_digest(seed_0, seed_1, xd_0, xd_1, sd_0, sd_1, da_0, da_1, defer,
count_g)`**: the 24 deferred cells at `defer`; the eight header cells and the count's cell are
canonical (the `KECCAK` reads them), and the function returns the two cells of the Keccak-256 digest
of the header cells, the deferred cells' limbs and the count's cell. -/
def MeaningStatementDigestK (rd : Reader) : List E → List E → Prop
  | [s0, s1, x0, x1, y0, y1, a0, a1, dp, cnt], rets => ∃ cells : List E,
      cells.length = deferStmtCells ∧ ReadsAt rd dp cells ∧
      AllCanonical [s0, s1, x0, x1, y0, y1, a0, a1, cnt] ∧
      rets = digestCells (keccak256 (stmtBytes [s0, s1, x0, x1, y0, y1, a0, a1] cells ++
        cellsBytes [cnt]))
  | _, _ => False

/-- The salted core IR's `statement_digest` gives its meaning. -/
def statement_digest_sound_SpecK : Prop :=
  ∀ (rd : Reader) (args rets : List E),
    SaltedGuest.coreProgram.Rel rd "statement_digest" args rets →
      MeaningStatementDigestK rd args rets

/-! ## The template -/

/-- The value of hashed cell `m < 45`: the eight header cells, the three cells of each pair, then
the count's cell. -/
def sdCellK (m : ℕ) : ℕ :=
  if m < 8 then 10 + m else if m < 44 then 18 + 27 * ((m - 8) / 3) + (8 + 9 * ((m - 8) % 3))
  else 342

/-- The value of output cell `c` of block `k < 6`. -/
def sdOutK (k c : ℕ) : ℕ := if k < 5 then 348 + 22 * k + c else 455 + c

/-- The value of input cell `c` of block `k < 6`. -/
def sdInK (k c : ℕ) : ℕ :=
  if c < 9 then
    (if k = 0 then sdCellK c else if k < 5 then 361 + 22 * (k - 1) + c
      else if c < 4 then 449 + c else if c < 8 then sdOutK 4 c else 454)
  else (if k = 0 then 344 + (c - 9) else sdOutK (k - 1) c)

/-- The `KECCAK` of block `k`. -/
def sdKeccakK (k : ℕ) : Atom :=
  .keccak ((List.range 13).map fun c => .n (sdInK k c))
    ((List.range (sdOutN k)).map fun c => .n (sdOutK k c)) (inLayout k) (outLayout 6 k)

/-- The header cells. -/
def sdHdrK : List Atom :=
  [.copy (.n 10) (.n 0), .copy (.n 11) (.n 1), .copy (.n 12) (.n 2), .copy (.n 13) (.n 3),
   .copy (.n 14) (.n 4), .copy (.n 15) (.n 5), .copy (.n 16) (.n 6), .copy (.n 17) (.n 7)]

/-- The count's cell, the padding's `0x01` cell and the zero capacity of the first block. -/
def sdConstsK : List Atom :=
  [.copy (.n 342) (.n 9), .const (.n 343) (word 1 0 0), .const (.n 344) (word 0 0 0),
   .const (.n 345) (word 0 0 0), .const (.n 346) (word 0 0 0), .const (.n 347) (word 0 0 0)]

/-- Block `k ∈ {1, …, 4}`: nine message cells XORed into the previous output, then its `KECCAK`. -/
def sdBlkK (k : ℕ) : List Atom :=
  (List.range 9).map (fun c => .add (.n (361 + 22 * (k - 1) + c)) (.n (sdOutK (k - 1) c))
    (.n (sdCellK (17 * k / 2 + c)))) ++ [sdKeccakK k]

/-- The last block: the message's last three cells, the padding's two cells (the cells between are
zero, their outputs passed on), its `KECCAK`. -/
def sdBlk5K : List Atom :=
  [.add (.n 449) (.n (sdOutK 4 0)) (.n (sdCellK 42)),
   .add (.n 450) (.n (sdOutK 4 1)) (.n (sdCellK 43)),
   .add (.n 451) (.n (sdOutK 4 2)) (.n (sdCellK 44)), .add (.n 452) (.n (sdOutK 4 3)) (.n 343),
   .const (.n 453) padWord, .add (.n 454) (.n (sdOutK 4 8)) (.n 453), sdKeccakK 5]

/-- The salted `statement_digest`'s atoms. -/
def sdAtomsK : List Atom :=
  sdHdrK ++ (List.range 12).flatMap (fun p => pairAtoms (.n 8) (2 * p) (18 + 27 * p)) ++
    sdConstsK ++ [sdKeccakK 0] ++ (List.range 4).flatMap (fun j => sdBlkK (j + 1)) ++ sdBlk5K ++
    [.copy (.n 457) (.n 455), .copy (.n 458) (.n 456)]

theorem core21K_body : Fn.body LeanVM.SaltedGuest.Data.core21 =
    sdAtomsK.map Stmt.atom ++ [.ret [.n 457, .n 458]] :=
  stmtsEqb_sound (by decide +kernel)

theorem core21K_params : Fn.params LeanVM.SaltedGuest.Data.core21 =
    [.n 0, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6, .n 7, .n 8, .n 9] := rfl

theorem find_statement_digestK :
    SaltedGuest.coreProgram.find? "statement_digest" = some LeanVM.SaltedGuest.Data.core21 :=
  Program.find?_of_indexOf? (j := 21) (by decide +kernel) rfl

/-! ## The cells -/

theorem sdCellK_A (p : ℕ) (hp : p < 12) : sdCellK (8 + 3 * p) = 18 + 27 * p + 8 := by
  unfold sdCellK
  rw [ite_neg' (by omega), ite_pos' (by omega), show (8 + 3 * p - 8) / 3 = p by omega,
    show (8 + 3 * p - 8) % 3 = 0 by omega]

theorem sdCellK_B (p : ℕ) (hp : p < 12) : sdCellK (8 + 3 * p + 1) = 18 + 27 * p + 17 := by
  unfold sdCellK
  rw [ite_neg' (by omega), ite_pos' (by omega), show (8 + 3 * p + 1 - 8) / 3 = p by omega,
    show (8 + 3 * p + 1 - 8) % 3 = 1 by omega]

theorem sdCellK_C (p : ℕ) (hp : p < 12) : sdCellK (8 + 3 * p + 2) = 18 + 27 * p + 26 := by
  unfold sdCellK
  rw [ite_neg' (by omega), ite_pos' (by omega), show (8 + 3 * p + 2 - 8) / 3 = p by omega,
    show (8 + 3 * p + 2 - 8) % 3 = 2 by omega]

theorem range45_split (f : ℕ → E) :
    (List.range 45).map f = (List.range 8).map f ++
      (List.range 12).flatMap (fun p => [f (8 + 3 * p), f (8 + 3 * p + 1), f (8 + 3 * p + 2)]) ++
      [f 44] :=
  rfl

/-- Block `k`'s `KECCAK`: canonical inputs, and its written cells the first of their Keccak-f. -/
theorem keccakK_holds {rd : Reader} {σ : Val} {k : ℕ} (h : (sdKeccakK k).Holds rd σ) :
    (∀ c : Fin 13, IsCanonical128 (σ (.n (sdInK k c)))) ∧ ∀ c : Fin 13, c.val < sdOutN k →
      σ (.n (sdOutK k c)) = cellsOfState (keccakF1600 (stateOfCells
        (fun c : Fin 13 => σ (.n (sdInK k c))) (inLayout k))) (outLayout 6 k) c := by
  obtain ⟨-, -, O, hK, hw⟩ := keccak_holds_full h
  have e1 : cells13 (((List.range 13).map fun c => V.n (sdInK k c)).map σ) =
      fun c : Fin 13 => σ (.n (sdInK k c)) := funext (cells13_map_range σ _)
  rw [e1] at hK
  refine ⟨hK.1, fun c hc => ?_⟩
  have := hw c (by simpa using hc)
  simp only [List.getElem_map, List.getElem_range] at this
  rw [this, hK.2 c c.isLt]

/-- The padded 45-cell message past its cells: the `0x01` cell at `45`, the `0x80` cell at `50`,
zero between. -/
theorem padCells_45 (cells : List E) (hl : cells.length = 45) {i : ℕ} (h1 : 45 ≤ i) (h2 : i < 51) :
    (padCells cells 720).getD i 0 =
      if i = 45 then word 1 0 0 else if i = 50 then padWord else 0 := by
  have hr : padRead 720 - cells.length = 6 := by rw [hl]; rfl
  unfold padCells xorByte
  rw [show rate * (720 / rate + 1) - 1 = 815 from rfl, show (815 : ℕ) / 16 = 50 from rfl,
    show (720 : ℕ) / 16 = 45 from rfl, hr, List.getD_eq_getElem?_getD, List.getElem?_modify,
    List.getElem?_modify, List.getElem?_append_right (by omega), hl,
    List.getElem?_replicate_of_lt (by omega)]
  unfold byteCell
  simp only [show (720 : ℕ) % 16 = 0 from rfl, show (815 : ℕ) % 16 = 15 from rfl]
  rcases (show i = 45 ∨ (46 ≤ i ∧ i ≤ 49) ∨ i = 50 by omega) with rfl | ⟨h46, h49⟩ | rfl
  · simp [word_eOfNat]
  · simp [show i ≠ 45 by omega, show i ≠ 50 by omega, show (50 : ℕ) ≠ i by omega,
      show (45 : ℕ) ≠ i by omega]
  · simp [padWord]

/-! ## Soundness -/

/-- **The salted `statement_digest` computes the digest of the statement with its count.** -/
theorem statement_digest_soundK : statement_digest_sound_SpecK := by
  intro rd args rets h
  obtain ⟨σ, hp, hb⟩ := (rel_iff_sem find_statement_digestK args rets).mp h
  rw [core21K_body, holdsList_atoms_ret] at hb
  obtain ⟨hat, hr⟩ := hb
  simp only [sdAtomsK, List.forall_mem_append, List.forall_mem_cons, List.not_mem_nil,
    IsEmpty.forall_iff, implies_true, and_true] at hat
  obtain ⟨⟨⟨⟨⟨⟨hH, hP⟩, hC⟩, hK0⟩, hB⟩, hB5⟩, h457, h458⟩ := hat
  rw [forall_mem_flatMap_range] at hP hB
  -- the header
  simp only [sdHdrK, List.forall_mem_cons, Atom.Holds, List.not_mem_nil, IsEmpty.forall_iff,
    implies_true, and_true] at hH
  obtain ⟨h10, h11, h12, h13, h14, h15, h16, h17⟩ := hH
  -- the count's cell and the constants
  simp only [sdConstsK, List.forall_mem_cons, Atom.Holds, List.not_mem_nil, IsEmpty.forall_iff,
    implies_true, and_true] at hC
  obtain ⟨c342, c343, c344, c345, c346, c347⟩ := hC
  -- the pairs
  have hpair := fun p hp => pair_fwd (hP p hp)
  -- the blocks
  have hadd : ∀ k, 1 ≤ k → k ≤ 4 → ∀ c < 9, σ (.n (361 + 22 * (k - 1) + c)) =
      σ (.n (sdOutK (k - 1) c)) + σ (.n (sdCellK (17 * k / 2 + c))) := by
    intro k hk1 hk4 c hc
    have := hB (k - 1) (by omega) _ (List.mem_append_left _ (List.mem_map.mpr ⟨c, List.mem_range.mpr hc, rfl⟩))
    rwa [show k - 1 + 1 = k by omega] at this
  have hkk : ∀ k, 1 ≤ k → k ≤ 4 → (sdKeccakK k).Holds rd σ := by
    intro k hk1 hk4
    have := hB (k - 1) (by omega) (sdKeccakK (k - 1 + 1)) (List.mem_append_right _ (List.mem_singleton_self _))
    rwa [show k - 1 + 1 = k by omega] at this
  simp only [sdBlk5K, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true,
    and_true] at hB5
  obtain ⟨a449, a450, a451, a452, c453, a454, hk5⟩ := hB5
  -- the chain
  let C45 : List E := (List.range 45).map fun m => σ (.n (sdCellK m))
  have hC45 : C45.length = 45 := by simp [C45]
  have hC45get : ∀ m < 45, C45.getD m 0 = σ (.n (sdCellK m)) := fun m hm => by
    simp [C45, List.getD_eq_getElem?_getD, hm]
  let I : ℕ → Fin 13 → E := fun k c => σ (.n (sdInK k c))
  let O : ℕ → Fin 13 → E := fun k c => if k = 0 then 0 else σ (.n (sdOutK (k - 1) c))
  have hkk' : ∀ k ≤ 5, (sdKeccakK k).Holds rd σ := fun k hk => by
    rcases (show k = 0 ∨ (1 ≤ k ∧ k ≤ 4) ∨ k = 5 by omega) with rfl | ⟨hk1, hk4⟩ | rfl
    · exact hK0
    · exact hkk k hk1 hk4
    · exact hk5
  -- the true outputs: the state after block `k - 1`, whose cells the written values are
  let O' : ℕ → Fin 13 → E := fun k c => if k = 0 then 0 else
    cellsOfState (keccakF1600 (stateOfCells (I (k - 1)) (inLayout (k - 1)))) (outLayout 6 (k - 1)) c
  have hOO : ∀ k ≤ 5, O' k = O k := fun k hk => by
    funext c
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · rfl
    · simp only [O', O, show k ≠ 0 by omega, ↓reduceIte]
      exact ((keccakK_holds (hkk' (k - 1) (by omega))).2 c
        (by simp [sdOutN, show k - 1 < 5 by omega])).symm
  have hP45 : ∀ m < 45, (padCells C45 720).getD m 0 = σ (.n (sdCellK m)) := fun m hm => by
    rw [padCells_getD_lt _ _ (by omega) (by rw [show (720 : ℕ) / 16 = 45 from rfl]; omega)
      (by rw [show rate * (720 / rate + 1) - 1 = 815 from rfl]; omega), hC45get m hm]
  have hB6 : 720 / rate + 1 = 6 := rfl
  have hrate : ∀ k < 720 / rate + 1, ∀ c : Fin 13, c.val < 9 →
      I k c = O k c + (padCells C45 720).getD (17 * k / 2 + c) 0 := by
    intro k hk c hc
    rw [hB6] at hk
    rcases (show k = 0 ∨ (1 ≤ k ∧ k ≤ 4) ∨ k = 5 by omega) with rfl | ⟨hk1, hk4⟩ | rfl
    · simp only [I, O, sdInK, hc, ↓reduceIte, Nat.mul_zero, Nat.zero_div, zero_add]
      rw [hP45 _ (by omega)]
    · simp only [I, O, sdInK, hc, ↓reduceIte, show k ≠ 0 by omega, show k < 5 by omega]
      rw [hadd k hk1 hk4 c hc, hP45 _ (by omega)]
    · rw [show 17 * 5 / 2 + c.val = 42 + c.val by omega]
      rcases (show c.val = 0 ∨ c.val = 1 ∨ c.val = 2 ∨ c.val = 3 ∨ (4 ≤ c.val ∧ c.val < 8) ∨
          c.val = 8 by omega) with h0 | h1 | h2 | h3 | ⟨h4, h8⟩ | h8
      · simp (config := {decide := true}) only [I, O, sdInK, h0, ↓reduceIte]
        rw [a449, hP45 _ (by omega)]
      · simp (config := {decide := true}) only [I, O, sdInK, h1, ↓reduceIte]
        rw [a450, hP45 _ (by omega)]
      · simp (config := {decide := true}) only [I, O, sdInK, h2, ↓reduceIte]
        rw [a451, hP45 _ (by omega)]
      · simp (config := {decide := true}) only [I, O, sdInK, h3, ↓reduceIte]
        rw [a452, c343, padCells_45 C45 hC45 (by omega) (by omega)]
        simp
      · simp (config := {decide := true}) only [I, O, sdInK, hc, ↓reduceIte,
          show ¬ c.val < 4 by omega, h8]
        rw [padCells_45 C45 hC45 (by omega) (by omega)]
        simp [show 42 + c.val ≠ 45 by omega, show 42 + c.val ≠ 50 by omega]
      · simp (config := {decide := true}) only [I, O, sdInK, h8, ↓reduceIte]
        rw [a454, c453, padCells_45 C45 hC45 (by omega) (by omega)]
        simp
  have hcap : ∀ k < 720 / rate + 1, ∀ c : Fin 13, 9 ≤ c.val → I k c = O k c := by
    intro k hk c hc
    rw [hB6] at hk
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · simp only [I, O, sdInK, show ¬ c.val < 9 by omega, ↓reduceIte]
      rcases (show c.val - 9 = 0 ∨ c.val - 9 = 1 ∨ c.val - 9 = 2 ∨ c.val - 9 = 3 by omega) with
        h | h | h | h <;> simp only [h, Nat.reduceAdd] <;>
        first | rw [c344, word_zero] | rw [c345, word_zero] | rw [c346, word_zero] |
          rw [c347, word_zero]
    · simp only [I, O, sdInK, show ¬ c.val < 9 by omega, ↓reduceIte, show k ≠ 0 by omega]
  have hrate' : ∀ k < 720 / rate + 1, ∀ c : Fin 13, c.val < 9 →
      I k c = O' k c + (padCells C45 720).getD (17 * k / 2 + c) 0 := fun k hk c hc => by
    rw [hOO k (by rw [hB6] at hk; omega)]; exact hrate k hk c hc
  have hcap' : ∀ k < 720 / rate + 1, ∀ c : Fin 13, 9 ≤ c.val → I k c = O' k c := fun k hk c hc => by
    rw [hOO k (by rw [hB6] at hk; omega)]; exact hcap k hk c hc
  have hK : ∀ k < 720 / rate + 1,
      KeccakCellsRelation (I k) (inLayout k) (O' (k + 1)) (outLayout (720 / rate + 1) k) .all := by
    intro k hk
    rw [hB6] at hk ⊢
    exact ⟨(keccakK_holds (hkk' k (by omega))).1, fun c _ => by simp [O']⟩
  have h0 : O' 0 = cellsOfState (absorbChunks 0 zeroState []) false := by
    funext c
    simp only [O', ↓reduceIte]
    exact (cellsOfState_zero false c).symm
  have hz : ∀ j, 720 ≤ j → (cellsBytes C45).getD j 0 = 0 := fun j hj =>
    getD_of_length_le (by rw [length_cellsBytes, hC45]; omega)
  have hdig := keccak_final_digest (pre := []) (n := 0) rfl (by rw [hC45]) hz h0 hrate' hcap' hK
  rw [hB6, List.nil_append, List.take_of_length_le (by rw [length_cellsBytes, hC45])] at hdig
  -- the canonical header and count
  have hcan := (hK 0 (by rw [hB6]; omega)).1
  have can : ∀ m < 8, IsCanonical128 (σ (.n (10 + m))) := fun m hm => by
    have := hcan ⟨m, by omega⟩
    simpa [I, sdInK, sdCellK, show m < 9 by omega, hm] using this
  have can44 : IsCanonical128 (σ (.n 342)) := by
    have h451 : IsCanonical128 (σ (.n 451)) := by
      have := (keccakK_holds hk5).1 ⟨2, by omega⟩
      simpa [sdInK] using this
    have hout : IsCanonical128 (σ (.n (sdOutK 4 2))) := by
      rw [(keccakK_holds (hkk 4 (by omega) le_rfl)).2 ⟨2, by omega⟩ (by simp [sdOutN])]
      exact isCanonical128_cellsOfState _ _ _
    have e451 : σ (.n 451) = σ (.n (sdOutK 4 2)) + σ (.n 342) := a451
    rw [e451, add_comm] at h451
    exact isCanonical128_of_add h451 hout
  -- the deferred cells
  let cells : List E := (List.range 24).map fun q => σ (.n (18 + 27 * (q / 2) + q % 2))
  have hcells : cells = (List.range 12).flatMap
      (fun p => [σ (.n (18 + 27 * p)), σ (.n (18 + 27 * p + 1))]) := by
    simp only [cells, range24_split]
    refine List.flatMap_congr fun p _ => ?_
    rw [show 2 * p / 2 = p by omega, show 2 * p % 2 = 0 by omega,
      show (2 * p + 1) / 2 = p by omega, show (2 * p + 1) % 2 = 1 by omega, Nat.add_zero]
  have e1 : (List.range 8).map (fun m => σ (.n (sdCellK m))) =
      [σ (.n 0), σ (.n 1), σ (.n 2), σ (.n 3), σ (.n 4), σ (.n 5), σ (.n 6), σ (.n 7)] := by
    rw [← h10, ← h11, ← h12, ← h13, ← h14, ← h15, ← h16, ← h17]; rfl
  have e2 : (List.range 12).flatMap (fun p => [σ (.n (sdCellK (8 + 3 * p))),
      σ (.n (sdCellK (8 + 3 * p + 1))), σ (.n (sdCellK (8 + 3 * p + 2)))]) =
      (List.range 12).flatMap (fun p => pairCells (σ (.n (18 + 27 * p))) (σ (.n (18 + 27 * p + 1)))) := by
    refine List.flatMap_congr fun p hp => ?_
    obtain ⟨-, -, hc3⟩ := hpair p (List.mem_range.mp hp)
    rw [sdCellK_A p (List.mem_range.mp hp), sdCellK_B p (List.mem_range.mp hp),
      sdCellK_C p (List.mem_range.mp hp)]
    exact hc3
  have e3 : σ (.n (sdCellK 44)) = σ (.n 9) := by
    show σ (.n 342) = σ (.n 9)
    exact c342
  have hbytes : cellsBytes C45 =
      stmtBytes [σ (.n 0), σ (.n 1), σ (.n 2), σ (.n 3), σ (.n 4), σ (.n 5), σ (.n 6), σ (.n 7)]
        cells ++ cellsBytes [σ (.n 9)] := by
    have hp : cellsBytes ((List.range 12).flatMap fun p =>
        pairCells (σ (.n (18 + 27 * p))) (σ (.n (18 + 27 * p + 1)))) =
        ((List.range 12).flatMap fun p => [σ (.n (18 + 27 * p)), σ (.n (18 + 27 * p + 1))]).flatMap
          E.toBytes := by
      simp only [cellsBytes, List.flatMap_assoc]
      refine List.flatMap_congr fun p _ => ?_
      have := pair_bytes (σ (.n (18 + 27 * p))) (σ (.n (18 + 27 * p + 1)))
      simp only [cellsBytes] at this
      rw [this]
      simp
    show cellsBytes ((List.range 45).map fun m => σ (.n (sdCellK m))) = _
    rw [range45_split, e1, e2, e3, cellsBytes_append, cellsBytes_append, stmtBytes, hcells, hp]
  -- the meaning
  simp only [core21K_params, List.map_cons, List.map_nil] at hp
  subst hp
  refine ⟨cells, by simp [cells], fun k hk => ?_, ?_, ?_⟩
  · have hk' : k < 24 := by simpa [cells] using hk
    obtain ⟨la, lb, -⟩ := hpair (k / 2) (by omega)
    simp only [cells, List.getElem_map, List.getElem_range]
    rcases Nat.mod_two_eq_zero_or_one k with h2 | h2
    · rw [h2, Nat.add_zero, show k = 2 * (k / 2) by omega]
      rw [show 2 * (k / 2) / 2 = k / 2 by omega]
      exact la
    · rw [h2, show k = 2 * (k / 2) + 1 by omega, show (2 * (k / 2) + 1) / 2 = k / 2 by omega]
      exact lb
  · intro c hc
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [← h10]; exact can 0 (by omega)
    · rw [← h11]; exact can 1 (by omega)
    · rw [← h12]; exact can 2 (by omega)
    · rw [← h13]; exact can 3 (by omega)
    · rw [← h14]; exact can 4 (by omega)
    · rw [← h15]; exact can 5 (by omega)
    · rw [← h16]; exact can 6 (by omega)
    · rw [← h17]; exact can 7 (by omega)
    · rw [← c342]; exact can44
  · simp only [Atom.Holds] at h457 h458
    have hO6 : ∀ c : Fin 13, c.val < 2 → O' 6 c = σ (.n (sdOutK 5 c)) := fun c hc =>
      ((keccakK_holds hk5).2 c (by simpa [sdOutN] using hc)).symm
    rw [hO6 0 (by decide), hO6 1 (by decide)] at hdig
    rw [← hbytes, digestCells, ← hdig, ← hr]
    simp only [List.map_cons, List.map_nil, h457, h458]
    rfl

end
end LeanVM.SaltedGuest.B1.Digest
