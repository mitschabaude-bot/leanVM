/-
  LeanVM.SaltedGuest.B1.Da.VerifyMathK

  From the keyed digests and sums the salted `da_verify` computes, a witness that opens its claim
  under the seed (`Recursion.Salted.OpensUnder`).
-/

module

public import LeanVM.SaltedGuest.B1.Da.PaddingK

/-!
# The claim the salted `da_verify` returns is opened under the seed

The deployed `Da.opens_of` with the keyed hash: given `r` rows (`1 ≤ r ≤ 1024`, padded to
`2^L = LeanDa.paddedRowCount r`) and the symbols of cell `(i, h)` (`syms i h`, `256`), with every
row orthogonal to the dual codeword of `z`, `opens_ofK` builds the witness, the rows the cells
concatenate (`daRows`). It opens under `s` the root `daRootK s r L syms`, the keyed tree over the
blob roots (`blobLeafK`: a row's keyed tree over its cells' keyed digests `cellDK`, or the padding
root `padRootK s`), and `z`.
-/

namespace LeanVM.SaltedGuest.B1.Da

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Guest.Value.Keccak LeanVM.Guest.B1 LeanVM.Guest.B1.Digest
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Node LeanVM.Guest.B1.Da LeanVM.SaltedGuest.B1 Recursion.Salted

@[expose] public section

section
variable (s : Digest) (r L : ℕ) (syms : ℕ → ℕ → List K)

/-- Cell `(i, h)`'s keyed digest. -/
def cellDK (i h : ℕ) : Digest := keyedHash s ((syms i h).flatMap K.toBytes)

/-- Blob `i`'s root among the padded rows: its keyed tree over its cells' keyed digests, or the
padding root. -/
def blobLeafK (i : ℕ) : Digest := if i < r then mRootK s 7 (cellDK s syms i) else padRootK s

/-- The root: the keyed tree over the blob roots. -/
def daRootK : Digest := mRootK s L (blobLeafK s r syms)

end

/-- **The witness opens the claim under the seed.** -/
theorem opens_ofK {s : Digest} {r L : ℕ} {syms : ℕ → ℕ → List K} {z : E} (hr1 : 1 ≤ r)
    (hr : r ≤ LeanDa.maxRows) (hL : LeanDa.paddedRowCount r = 2 ^ L) (hrL : r ≤ 2 ^ L)
    (hsyms : ∀ i h, (syms i h).length = 256)
    (hdot : ∀ i < r, ∑ h ∈ Finset.range 128, ∑ e ∈ Finset.range 256,
      dualAt z (256 * h + e) * ofK ((syms i h).getD e 0) = 0) :
    OpensUnder s (daRootK s r L syms) z ⟨daRows r syms⟩ := by
  have hrow : ∀ i, ((List.range 128).flatMap (syms i)).length = 2 ^ LeanDa.logM := fun i => by
    rw [length_flatMap_range _ 256 _ (hsyms i)]; rfl
  have hcell : ∀ i, ∀ h < 128, LeanDa.listCell ((List.range 128).flatMap (syms i)) h = syms i h :=
    fun i h hh => block_eq (syms i) 256 (hsyms i) hh 0
  have hlen : (daRows r syms).length = r := by simp [daRows]
  have hrows : ∀ row ∈ daRows r syms, row.length = 2 ^ LeanDa.logM := by
    intro row hrow'
    obtain ⟨i, -, rfl⟩ := List.mem_map.mp hrow'
    exact hrow i
  -- a row's blob root
  have hblob : ∀ i < r, LeanDa.listBlobRootWithHash (keyedBytes s)
      ((List.range 128).flatMap (syms i)) = LeanVM.Protocol.Digest.toBytes (mRootK s 7 (cellDK s syms i)) := by
    intro i hi
    rw [LeanDa.listBlobRootWithHash, show LeanDa.cellsPerRow = 2 ^ 7 from rfl, treeRoot_range,
      toBytes_mRootK]
    refine merkleRoot_congr _ 7 fun h hh => ?_
    rw [LeanDa.listCellDigestWithHash, hcell i h (by simpa using hh)]
    rfl
  refine ⟨by simp only [hlen]; exact hr1, by simp only [hlen]; exact hr, hrows, ?_, ?_⟩
  · -- the commitment
    show LeanDa.commitCellsWithHash (keyedBytes s) (LeanDa.cellsOfRows (daRows r syms)) = _
    rw [← LeanDa.commitCodewords_eq_commitCells _ _ hrows, LeanDa.commitCodewordsWithHash, hlen, hL]
    have hlist : (daRows r syms).map (LeanDa.listBlobRootWithHash (keyedBytes s)) ++
        List.replicate (2 ^ L - r) (LeanDa.paddingBlobRootWithHash (keyedBytes s)) =
        (List.range (2 ^ L)).map (LeanVM.Protocol.Digest.toBytes ∘ blobLeafK s r syms) := by
      refine List.ext_getElem (by simp [hlen]; omega) fun i h1 h2 => ?_
      simp only [List.length_map, List.length_range] at h2
      rw [List.getElem_map, List.getElem_range, Function.comp_apply, blobLeafK]
      by_cases hi : i < r
      · rw [List.getElem_append_left (by simp [hlen, hi]), List.getElem_map, ite_pos' hi, ← hblob i hi]
        simp [daRows]
      · rw [List.getElem_append_right (by simp [hlen]; omega), List.getElem_replicate, ite_neg' hi,
          toBytes_padRootK]
    rw [hlist, treeRoot_range, daRootK, toBytes_mRootK]
  · -- orthogonality
    intro row hrow'
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hrow'
    have hi' := List.mem_range.mp hi
    rw [LeanDa.innerProduct]
    have hfun : ∀ b : Fin (2 ^ 15), LeanDa.dualCodewordAt z b *
        LeanDa.ι (((List.range 128).flatMap (syms i)).getD b 0) =
        dualAt z b * ofK (((List.range 128).flatMap (syms i)).getD b 0) := fun b => by
      rw [dualAt_eq]; rfl
    rw [Finset.sum_congr rfl fun b _ => hfun b, Fin.sum_univ_eq_sum_range (fun b => dualAt z b *
      ofK (((List.range 128).flatMap (syms i)).getD b 0)) (2 ^ 15),
      show 2 ^ 15 = 128 * 256 by norm_num, sum_range_mul _ 256 128]
    refine (Finset.sum_congr rfl fun h hh => Finset.sum_congr rfl fun e he => ?_).trans (hdot i hi')
    have hh' := Finset.mem_range.mp hh
    have he' := Finset.mem_range.mp he
    rw [flatMap_getD (syms i) 256 (hsyms i) 0 128 h e hh' he']

end
end LeanVM.SaltedGuest.B1.Da
