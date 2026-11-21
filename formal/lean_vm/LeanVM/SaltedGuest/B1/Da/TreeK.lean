/-
  LeanVM.SaltedGuest.B1.Da.TreeK

  The salted guest's trees of cell pairs, every node hashed under the key, as LeanDA's Merkle trees
  over the keyed hash.
-/

module

public import LeanVM.SaltedGuest.B1.Da.Common
public import LeanVM.Guest.B1.Da.VerifyMath

/-!
# Keyed trees

The deployed `nodeCells`, `cellLevel`, `cellRoot`, `upD`, `mRoot` (`LeanVM.Guest.B1.Da`) with the
keyed hash `keyedHash s` in place of Keccak-256: `nodeCellsK`, `cellLevelK`, `cellRootK`, `upDK`,
`mRootK`. With LeanDA's hash `keyedBytes s` (the keyed hash's `32` bytes), `toBytes_mRootK`: the
tree of digests is `LeanDa.merkleRootWithHash (keyedBytes s)`; `cellRootK_mRootK`: as cells it is
`cellRootK`; `levels_rootK`: a tree built level by level in memory, every node the keyed digest of
its children, roots at its last level's node.
-/

namespace LeanVM.SaltedGuest.B1.Da

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Guest.Value.Keccak LeanVM.Guest.B1 LeanVM.Guest.B1.Digest
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Node LeanVM.Guest.B1.Da LeanVM.SaltedGuest.B1 Recursion.Salted

@[expose] public section

variable (s : Digest)

/-- The keyed hash as LeanDA's hash: its `32` bytes. -/
def keyedBytes (x : List UInt8) : Common.DigestBytes := LeanVM.Protocol.Digest.toBytes (keyedHash s x)

/-- The two cells of a tree node from its children's, under the key. -/
def nodeCellsK (l r : E × E) : E × E := digestHalves (keyedHash s (cellsBytes [l.1, l.2, r.1, r.2]))

/-- One level of a tree of cell pairs, under the key. -/
def cellLevelK (nodes : List (E × E)) : List (E × E) :=
  (List.range (nodes.length / 2)).map fun i ↦
    nodeCellsK s (nodes.getD (2 * i) 0) (nodes.getD (2 * i + 1) 0)

/-- The root over `2^k` leaves, `k` levels up, under the key. -/
def cellRootK : ℕ → List (E × E) → E × E
  | 0, nodes => nodes.headD 0
  | k + 1, nodes => cellRootK k (cellLevelK s nodes)

/-- One level up a tree of digests, under the key. -/
def upDK (g : ℕ → Digest) (i : ℕ) : Digest :=
  keyedHash s (digestBytes (g (2 * i)) ++ digestBytes (g (2 * i + 1)))

/-- The root of the tree of digests over the leaves `g 0 … g (2^d - 1)`, under the key. -/
def mRootK : ℕ → (ℕ → Digest) → Digest
  | 0, g => g 0
  | d + 1, g => mRootK d (upDK s g)

theorem toBytes_mRootK : ∀ (d : ℕ) (g : ℕ → Digest),
    LeanVM.Protocol.Digest.toBytes (mRootK s d g) =
      LeanDa.merkleRootWithHash (keyedBytes s) d (LeanVM.Protocol.Digest.toBytes ∘ g)
  | 0, _ => rfl
  | d + 1, g => by
    rw [mRootK, toBytes_mRootK d, LeanDa.merkleRootWithHash]
    congr 1

theorem nodeCellsK_scalars (a b : Digest) :
    nodeCellsK s (digestHalves a) (digestHalves b) =
      digestHalves (keyedHash s (digestBytes a ++ digestBytes b)) := by
  rw [nodeCellsK, Main.digestBytes_eq_cells, Main.digestBytes_eq_cells]
  simp [cellsBytes]

theorem cellLevelK_scalars (d : ℕ) (g : ℕ → Digest) :
    cellLevelK s ((List.range (2 ^ (d + 1))).map fun i => digestHalves (g i)) =
      (List.range (2 ^ d)).map fun i => digestHalves (upDK s g i) := by
  have hlen : 2 ^ (d + 1) / 2 = 2 ^ d := by rw [pow_succ, Nat.mul_div_cancel _ (by norm_num)]
  rw [cellLevelK, List.length_map, List.length_range, hlen]
  refine List.map_congr_left fun i hi => ?_
  rw [List.mem_range] at hi
  have h1 : 2 * i < 2 ^ (d + 1) := by rw [pow_succ]; omega
  have h2 : 2 * i + 1 < 2 ^ (d + 1) := by rw [pow_succ]; omega
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range h1,
    List.getElem?_range h2, Option.map_some, Option.getD_some, upDK, nodeCellsK_scalars]

/-- **The guest's keyed root of cell pairs is the keyed root of the digests.** -/
theorem cellRootK_mRootK : ∀ (d : ℕ) (g : ℕ → Digest),
    cellRootK s d ((List.range (2 ^ d)).map fun i => digestHalves (g i)) = digestHalves (mRootK s d g)
  | 0, _ => rfl
  | d + 1, g => by
    rw [cellRootK, cellLevelK_scalars, cellRootK_mRootK d, mRootK]

/-! ## Trees built level by level -/

variable {s}

theorem cellLevelK_nodes {k j : ℕ} (hj : j < k) {rd : Reader} {tree : E}
    (h : ∀ p < 2 ^ (k - j - 1), node rd tree k (j + 1) p =
      nodeCellsK s (node rd tree k j (2 * p)) (node rd tree k j (2 * p + 1))) :
    cellLevelK s ((List.range (2 ^ (k - j))).map (node rd tree k j)) =
      (List.range (2 ^ (k - (j + 1)))).map (node rd tree k (j + 1)) := by
  have e : 2 ^ (k - j) = 2 * 2 ^ (k - j - 1) := by
    rw [← pow_succ']; congr 1; omega
  unfold cellLevelK
  rw [List.length_map, List.length_range, e, Nat.mul_div_cancel_left _ (by norm_num),
    show k - (j + 1) = k - j - 1 by omega]
  refine List.map_congr_left fun p hp => ?_
  have hp' := List.mem_range.mp hp
  rw [h p hp']
  congr 1
  · simp [List.getD_eq_getElem?_getD, show 2 * p < 2 * 2 ^ (k - j - 1) by omega]
  · simp [List.getD_eq_getElem?_getD, show 2 * p + 1 < 2 * 2 ^ (k - j - 1) by omega]

/-- **The root of the levels, under the key**: with every level's nodes the keyed digests of the
previous level's pairs, the root over the leaves is the last level's node. -/
theorem levels_rootK {k : ℕ} {rd : Reader} {tree : E}
    (h : ∀ j < k, ∀ p < 2 ^ (k - j - 1), node rd tree k (j + 1) p =
      nodeCellsK s (node rd tree k j (2 * p)) (node rd tree k j (2 * p + 1))) :
    cellRootK s k ((List.range (2 ^ k)).map (node rd tree k 0)) = node rd tree k k 0 := by
  have key : ∀ j ≤ k, cellRootK s k ((List.range (2 ^ k)).map (node rd tree k 0)) =
      cellRootK s (k - j) ((List.range (2 ^ (k - j))).map (node rd tree k j)) := by
    intro j
    induction j with
    | zero => intro _; rfl
    | succ j ih =>
      intro hj
      rw [ih (by omega), show k - j = (k - (j + 1)) + 1 by omega, cellRootK,
        show k - (j + 1) + 1 = k - j by omega, cellLevelK_nodes (by omega) (h j (by omega))]
  rw [key k le_rfl, Nat.sub_self, pow_zero]
  rfl

end
end LeanVM.SaltedGuest.B1.Da
