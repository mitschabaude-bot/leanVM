/-
  LeanVM.SaltedGuest.B1.Keyed

  The keyed hash in the guest's cells: the key's state, computed from the seed's two cells, and a
  chain of `KECCAK`s continuing from it computing the keyed hash.
-/

module

public import LeanVM.Salted.Hash
public import LeanVM.Guest.B1.Digest.Chain
public import LeanVM.Guest.B1.Merkle.Climb
public import LeanVM.Guest.B1.Merkle.Cap

/-!
# The keyed hash

`keyedHash s x` is Keccak-256 of `keyPrefix s ++ x`: the seed's `32` bytes and `240` zeros, two
whole blocks (`keyedHash_eq`). The guest computes the state after them, the key's state
`keyState s` (its cells `keyCells s`), with `keccak_cells([s0, s1, 0 × 15], out, final=0)` from
the seed's two cells (`key_whole`), and continues from it as `state=` (`keyed_final_digest`: a
`final` chain from the key's cells computes the keyed hash of its message). A keyed hash of `64`
bytes is one `KECCAK` whose rate cells are the key's with the message XORed into the first four
and the padding into cells `4` and `8` (`keyed_node`: `keyed_node` of the guest).

* `HashesPairK s`: `HashesPair` under the keyed hash.
-/

namespace LeanVM.SaltedGuest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Guest.B1 LeanVM.Guest.B1.Digest
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Guest.Value.Keccak Recursion.Salted

@[expose] public section

/-! ## The key -/

/-- **The keyed hash's prefix** under `s`: the seed's `32` bytes and `240` zero bytes. -/
def keyPrefix (s : Digest) : List UInt8 := digestBytes s ++ List.replicate 240 0

theorem keyPrefix_length (s : Digest) : (keyPrefix s).length = rate * 2 := by
  rw [keyPrefix, List.length_append, ← cellsBytes_digestScalars, length_cellsBytes]
  simp only [List.length_cons, List.length_nil, List.length_replicate]
  rfl

/-- The keyed hash is Keccak-256 after the prefix. -/
theorem keyedHash_eq (s : Digest) (x : List UInt8) : keyedHash s x = keccak256 (keyPrefix s ++ x) := by
  rw [keyedHash, keyedInput, keyPrefix]

/-- **The key's state**: the prefix's two blocks absorbed from the zero state. -/
def keyState (s : Digest) : KeccakState := absorbChunks 2 zeroState (keyPrefix s)

/-- **The key's cells**: the key's state in the even layout. -/
def keyCells (s : Digest) : Fin 13 → E := cellsOfState (keyState s) false

theorem keyCells_canonical (s : Digest) (c : Fin 13) : IsCanonical128 (keyCells s c) :=
  isCanonical128_cellsOfState _ _ _

/-- The cells the key's computation absorbs: the seed's two cells and fifteen zeros. -/
def keyInput (s : Digest) : List E := [(digestHalves s).1, (digestHalves s).2] ++ List.replicate 15 0

theorem cellsBytes_keyInput (s : Digest) : cellsBytes (keyInput s) = keyPrefix s := by
  rw [keyInput, cellsBytes_append, cellsBytes_digestScalars, cellsBytes_replicate_zero, keyPrefix]

/-- **The key, computed** (`keccak_cells([s0, s1, 0, …], out, final=0)`, two `KECCAK`s from the zero
state): the second output is the key's cells. -/
theorem key_whole {s : Digest} {I O : ℕ → Fin 13 → E}
    (h0 : ∀ c, O 0 c = 0)
    (hrate : ∀ k < 2, ∀ c : Fin 13, c.val < 9 → I k c = O k c + (keyInput s).getD (17 * k / 2 + c) 0)
    (hcap : ∀ k < 2, ∀ c : Fin 13, 9 ≤ c.val → I k c = O k c)
    (hK : ∀ k < 2, KeccakCellsRelation (I k) (inLayout k) (O (k + 1)) (outLayout 2 k) .all) :
    O 2 = keyCells s := by
  have h0' : O 0 = cellsOfState (absorbChunks 0 zeroState []) false := by
    funext c; rw [h0 c, absorbChunks, cellsOfState_zero]
  have := (keccak_whole (pre := []) (n := 0) (cells := keyInput s) (B := 2) rfl
    (by simp [keyInput, rate]) h0' hrate hcap hK).1
  rw [this, List.nil_append, Nat.zero_add, cellsBytes_keyInput]
  rfl

/-- **The key of `s` at `p`**: `p` is in `K` and every readable word at `p·g^c`, `c < 13`, is the key's
cell `c` (what a frame run of the key's cells gives, `addr`, and a heap run holding them). -/
def KeyIs (rd : Reader) (p : E) (s : Digest) : Prop :=
  IsInK p ∧ ∀ c : Fin 13, ∀ w, rd (p.limb 0 * addressOfIndex c.val) = some w → w = keyCells s c

/-- A word loaded from the key's run is the key's cell. -/
theorem KeyIs.load {rd : Reader} {p : E} {s : Digest} (h : KeyIs rd p s) {c : Fin 13} {v : E}
    (hl : LoadHolds rd p c v) : v = keyCells s c :=
  h.2 c v hl.2

/-! ## Chains from the key -/

/-- **A `final` chain from the key's cells computes the keyed hash** of its message, the first
`len` bytes of `cells` (`keccak_final_digest` after the prefix). -/
theorem keyed_final_digest {s : Digest} {cells : List E} {len : ℕ} {I O : ℕ → Fin 13 → E}
    (hlen : len ≤ 16 * cells.length)
    (hz : ∀ j, len ≤ j → (cellsBytes cells).getD j 0 = 0)
    (h0 : O 0 = keyCells s)
    (hrate : ∀ k < len / rate + 1, ∀ c : Fin 13, c.val < 9 →
      I k c = O k c + (padCells cells len).getD (17 * k / 2 + c) 0)
    (hcap : ∀ k < len / rate + 1, ∀ c : Fin 13, 9 ≤ c.val → I k c = O k c)
    (hK : ∀ k < len / rate + 1,
      KeccakCellsRelation (I k) (inLayout k) (O (k + 1)) (outLayout (len / rate + 1) k) .all) :
    (O (len / rate + 1) 0, O (len / rate + 1) 1) =
      digestHalves (keyedHash s ((cellsBytes cells).take len)) := by
  rw [keyedHash_eq]
  exact keccak_final_digest (keyPrefix_length s) hlen hz h0 hrate hcap hK

/-! ## A node under the key -/

/-- A node's two cells hash its children's under the key `s`: the children's four cells are
canonical, and the node's cells are the keyed digest of their `64` bytes. -/
def HashesPairK (s : Digest) (l0 l1 r0 r1 p0 p1 : E) : Prop :=
  AllCanonical [l0, l1, r0, r1] ∧
    (p0, p1) = digestHalves (keyedHash s (cellsBytes [l0, l1, r0, r1]))

/-- The rate cells of a keyed node's `KECCAK`: the key's cells, the message XORed into the first
four, the padding's first byte into cell `4` and its last bit into cell `8`. -/
def nodeIn (s : Digest) (a0 a1 b0 b1 : E) : List E :=
  [keyCells s 0 + a0, keyCells s 1 + a1, keyCells s 2 + b0, keyCells s 3 + b1, keyCells s 4 + word 1 0 0,
    keyCells s 5, keyCells s 6, keyCells s 7, keyCells s 8 + w63, keyCells s 9, keyCells s 10,
    keyCells s 11, keyCells s 12]

/-- **A keyed node** (`keyed_node`): one `KECCAK` on `nodeIn` hashes the four message cells under
the key; they are canonical. -/
theorem keyed_node {s : Digest} {a0 a1 b0 b1 : E} {O : Fin 13 → E}
    (hK : KeccakCellsRelation (cells13 (nodeIn s a0 a1 b0 b1)) false O false .all) :
    HashesPairK s a0 a1 b0 b1 (O 0) (O 1) := by
  have hcan : AllCanonical [a0, a1, b0, b1] := by
    have hc (c : Fin 13) (x : E) (h : cells13 (nodeIn s a0 a1 b0 b1) c = keyCells s c + x) :
        IsCanonical128 x := by
      have := hK.1 c
      rw [h, add_comm] at this
      exact isCanonical128_of_add this (keyCells_canonical s c)
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact hc 0 _ rfl
    · exact hc 1 _ rfl
    · exact hc 2 _ rfl
    · exact hc 3 _ rfl
  refine ⟨hcan, ?_⟩
  let I : ℕ → Fin 13 → E := fun _ ↦ cells13 (nodeIn s a0 a1 b0 b1)
  let O' : ℕ → Fin 13 → E := fun k ↦ if k = 0 then keyCells s else O
  have hB : (64 : ℕ) / rate + 1 = 1 := by simp [rate]
  have hd := keyed_final_digest (s := s) (cells := [a0, a1, b0, b1]) (len := 64) (I := I) (O := O')
    (by simp) (getD_cellsBytes_of_le (by simp)) rfl
    (fun k hk c hc ↦ by
      obtain rfl : k = 0 := by omega
      fin_cases c <;> simp_all [I, O', nodeIn, padCells, xorByte, padRead, rate, byteCell, cells13])
    (fun k hk c hc ↦ by
      obtain rfl : k = 0 := by omega
      fin_cases c <;> simp_all [I, O', nodeIn, cells13])
    (fun k hk ↦ by
      obtain rfl : k = 0 := by omega
      exact hK)
  simp only [hB, O', one_ne_zero, ↓reduceIte] at hd
  rwa [List.take_of_length_le (by simp)] at hd

end
end LeanVM.SaltedGuest.B1
