/-
  LeanVM.SaltedGuest.B1.Opening.QueriesLeafK

  The salted leaf hash: from the key's state, the keyed digest of the row.
-/

module

public import LeanVM.SaltedGuest.B1.Opening.QueriesTK
public import LeanVM.Guest.B1.Opening.QueriesLeaf
public import LeanVM.SaltedGuest.B1.Keyed

/-!
# The keyed leaf hash

`oqLeaf_soundK`: with the key's cells of `S` at `kc ..` and the packed cells those of the row's
words, the last block's first two cells are the keyed digest of the row,
`digestHalves (keyedHash S (row.flatMap K.toBytes))` (the leaf of `openOneWithHash (keyedHash S)`):
the deployed `oqLeaf_sound` with the chain started at the key's state (`keyed_final_digest`), every
block XORing its row cells into the previous state.
-/

namespace LeanVM.SaltedGuest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Guest.Value.Keccak LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open Recursion.Salted

@[expose] public section

variable {rd : Reader} {σ : Val}

/-- The cells the keyed leaf's block `k` reads. -/
def oqLeafIK (s : Oq) (emit : Bool) (kc kL : ℕ) (σ : Val) (k : ℕ) (c : Fin 13) : E :=
  if c.val < 9 then σ (.n (oqInK s emit kL k c.val)) else σ (.n (oqPrevK s emit kc kL k c.val))

theorem mem_oqLeafTK {s : Oq} {emit : Bool} {b pr kc kL k : ℕ} (hk : k < s.B) {a : Atom}
    (ha : Stmt.atom a ∈ oqBlockTK s emit b pr kc kL k) :
    Stmt.atom a ∈ oqLeafTK s emit b pr kc kL :=
  List.mem_flatten.mpr ⟨_, List.mem_map.mpr ⟨k, List.mem_range.mpr hk, rfl⟩, ha⟩

theorem mem_oqBlockTK_xor {s : Oq} {emit : Bool} {b pr kc kL k c : ℕ} (hc : c < 9) {a : Atom}
    (ha : Stmt.atom a ∈ oqXorTK s emit b pr kc kL k c) :
    Stmt.atom a ∈ oqBlockTK s emit b pr kc kL k :=
  List.mem_append_left _ (List.mem_flatten.mpr ⟨_, List.mem_map.mpr ⟨c, List.mem_range.mpr hc,
    rfl⟩, ha⟩)

/-- **The keyed leaf hash**: from the key's cells of `S` at `kc ..`, the packed cells those of the
row's words, the padding run (when not emitted) at `pr`, the last block's first two cells are the
keyed digest of the row. -/
theorem oqLeaf_soundK {s : Oq} (hs : s.RowShape) {emit : Bool} {b pr kc kL : ℕ} {row : List K}
    {S : Digest}
    (hA : ∀ a, Stmt.atom a ∈ oqLeafTK s emit b pr kc kL → a.Holds rd σ)
    (hpad : emit = false → σ (.n pr) = word 1 0 0)
    (hkey : ∀ c : Fin 13, σ (.n (kc + c.val)) = keyCells S c)
    (hrow : row.length = 2 * s.ncells)
    (hpk : ∀ j < s.ncells,
      σ (.n (oqPk b s.R j)) = E.ofLimbs (row.getD (2 * j) 0) (row.getD (2 * j + 1) 0) 0) :
    (σ (.n (oqOutK s emit kL (s.B - 1) 0)), σ (.n (oqOutK s emit kL (s.B - 1) 1))) =
      digestHalves (keyedHash S (row.flatMap K.toBytes)) := by
  have hL := leafShape_of s hs
  set cells := (List.range s.ncells).map fun j ↦ σ (.n (oqPk b s.R j)) with hcells
  have hcl : cells.length = s.ncells := by simp [hcells]
  have hcg : ∀ m < s.ncells, cells.getD m 0 = σ (.n (oqPk b s.R m)) := fun m hm => by
    simp [hcells, List.getD_eq_getElem?_getD, hm]
  -- each block's permutation
  have hblk : ∀ k < s.B, (∀ c, IsCanonical128 (oqLeafIK s emit kc kL σ k c)) ∧
      ∀ c : Fin 13, c.val < oqOutN s k → σ (.n (oqOutK s emit kL k c)) = cellsOfState
        (keccakF1600 (stateOfCells (oqLeafIK s emit kc kL σ k) (Keccak.inLayout k)))
        (Keccak.outLayout s.B k) c := by
    intro k hk
    have h := hA _ (mem_oqLeafTK hk (List.mem_append_right _ (List.mem_singleton.mpr rfl) :
      Stmt.atom (.keccak (((List.range 9).map fun c ↦ V.n (oqInK s emit kL k c)) ++
        ((List.range 4).map fun c ↦ V.n (oqPrevK s emit kc kL k (9 + c))))
        ((List.range (oqOutN s k)).map fun c ↦ V.n (oqOutK s emit kL k c)) (Keccak.inLayout k)
        (Keccak.outLayout s.B k)) ∈ oqBlockTK s emit b pr kc kL k))
    obtain ⟨-, -, O, hK, hw⟩ := keccak_holds_full h
    have eI : cells13 ((((List.range 9).map fun c ↦ V.n (oqInK s emit kL k c)) ++
        ((List.range 4).map fun c ↦ V.n (oqPrevK s emit kc kL k (9 + c)))).map σ) =
          oqLeafIK s emit kc kL σ k := by
      funext c; rw [cells13_block]
      simp only [oqLeafIK]
      split
      · rfl
      · rename_i hc
        rw [show 9 + (c.val - 9) = c.val by omega]
    rw [eI] at hK
    refine ⟨hK.1, fun c hc => ?_⟩
    have := hw c (by simpa using hc)
    simp only [List.getElem_map, List.getElem_range] at this
    rw [this, hK.2 c c.isLt]
  -- the true states: the key's, then block `k - 1`'s Keccak-f
  let O' : ℕ → Fin 13 → E := fun k c => if k = 0 then keyCells S c else
    cellsOfState (keccakF1600 (stateOfCells (oqLeafIK s emit kc kL σ (k - 1))
      (Keccak.inLayout (k - 1)))) (Keccak.outLayout s.B (k - 1)) c
  have hOO : ∀ k < s.B, ∀ c : Fin 13, O' k c = σ (.n (oqPrevK s emit kc kL k c.val)) := by
    intro k hk c
    rcases k with _ | k
    · simp only [O', ↓reduceIte, oqPrevK]; exact (hkey c).symm
    · simp only [O', Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel, oqPrevK]
      exact ((hblk k (by omega)).2 c (by simp [oqOutN, show k + 1 ≠ s.B by omega])).symm
  have hB : 16 * s.ncells / rate + 1 = s.B := rfl
  have key := keyed_final_digest (s := S) (cells := cells) (len := 16 * s.ncells)
    (I := oqLeafIK s emit kc kL σ) (O := O') (by rw [hcl])
    (getD_cellsBytes_of_le (by rw [hcl])) (by funext c; simp [O'])
    (by
      intro k hk c hc
      rw [hB] at hk
      rw [hOO k hk c]
      have hkB : 17 * k / 2 ≤ 17 * (s.B - 1) / 2 := Nat.div_le_div_right (by omega)
      have hlast := hL.last
      rw [getD_padCells_leaf hL cells hcl _ (by omega)]
      have hxor : ∀ a, Stmt.atom a ∈ oqXorTK s emit b pr kc kL k c.val → a.Holds rd σ :=
        fun a ha => hA a (mem_oqLeafTK hk (mem_oqBlockTK_xor hc ha))
      simp only [oqLeafIK, hc, ↓reduceIte]
      by_cases h1 : 17 * k / 2 + c.val < s.ncells
      · have := hxor _ (by simp [oqXorTK, h1] : Stmt.atom (.add (.n (oqBsK kL k + c.val))
          (.n (oqPrevK s emit kc kL k c.val)) (.n (oqPk b s.R (17 * k / 2 + c.val)))) ∈ _)
        simp only [Atom.Holds] at this
        simp only [h1, ↓reduceIte, hcg _ h1, oqInK]
        exact this
      · by_cases h2 : 17 * k / 2 + c.val = s.ncells
        · have := hxor _ (by simp [oqXorTK, h2] : Stmt.atom (.add
            (.n (oqBsK kL k + c.val + oqPadN s emit k)) (.n (oqPrevK s emit kc kL k c.val))
            (.n (if emit then oqBsK kL k + c.val else pr))) ∈ _)
          simp only [Atom.Holds] at this
          simp only [h2, ↓reduceIte, oqInK, lt_self_iff_false]
          rw [this]
          congr 1
          cases emit
          · exact hpad rfl
          · exact hxor (.const (.n (oqBsK kL k + c.val)) (word 1 0 0)) (by simp [oqXorTK, h2, oqPadT])
        · have e1 := hxor _ (by simp [oqXorTK, h1, h2] :
            Stmt.atom (.const (.n (oqBsK kL k + c.val + oqPadN s emit k)) (oqW80 s)) ∈ _)
          have e2 := hxor _ (by simp [oqXorTK, h1, h2] :
            Stmt.atom (.add (.n (oqBsK kL k + c.val + oqPadN s emit k + 1))
              (.n (oqPrevK s emit kc kL k c.val)) (.n (oqBsK kL k + c.val + oqPadN s emit k))) ∈ _)
          simp only [Atom.Holds] at e1 e2
          simp only [h1, h2, ↓reduceIte, oqInK]
          rw [e2, e1])
    (by
      intro k hk c hc
      rw [hB] at hk
      rw [hOO k hk c]
      simp [oqLeafIK, show ¬ c.val < 9 by omega])
    (by
      intro k hk
      rw [hB] at hk ⊢
      exact ⟨(hblk k hk).1, fun c _ => by simp [O']⟩)
  rw [hB, List.take_of_length_le (by simp [hcl]), hcells] at key
  have hpk' : (List.range s.ncells).map (fun j ↦ σ (.n (oqPk b s.R j))) =
      (List.range s.ncells).map fun j ↦ E.ofLimbs (row.getD (2 * j) 0) (row.getD (2 * j + 1) 0) 0 :=
    List.map_congr_left fun j hj => hpk j (List.mem_range.mp hj)
  rw [hpk', cellsBytes_packed row s.ncells hrow] at key
  have hlast : ∀ c : Fin 13, c.val < 2 → O' s.B c = σ (.n (oqOutK s emit kL (s.B - 1) c)) :=
    fun c hc => by
      have := (hblk (s.B - 1) (by have := hL.B2; omega)).2 c
        (by simp [oqOutN, show s.B - 1 + 1 = s.B by have := hL.B2; omega]; omega)
      simp only [O', show s.B ≠ 0 by have := hL.B2; omega, ↓reduceIte]
      exact this.symm
  rw [hlast 0 (by decide), hlast 1 (by decide)] at key
  exact key

end
end LeanVM.SaltedGuest.B1
