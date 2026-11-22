/-
  LeanVM.SaltedGuest.Decoder.PreTable

  The salted functions' preconditions, a literal table.
-/

module

public import LeanVM.SaltedGuest.Decoder.PreChunk0
public import LeanVM.SaltedGuest.Decoder.PreChunk1
public import LeanVM.SaltedGuest.Decoder.PreChunk2
public import LeanVM.SaltedGuest.Decoder.PreChunk3
public import LeanVM.SaltedGuest.Decoder.PreChunk4
public import LeanVM.SaltedGuest.Decoder.PreChunk5
public import LeanVM.SaltedGuest.Decoder.PreChunk6
public import LeanVM.SaltedGuest.Decoder.PreChunk7

/-!
# The salted functions' preconditions, a literal table

`preTableK`: entry `j` is the salted function `j`'s precondition as its test reads it
(`Guest.Fast.fnPreOf (glob.sig j)`), for the salted guest's `1539` functions, the kernel's
evaluations of `8` chunks (`PreChunk*.lean`, a module each: the deployed table at once
takes 11.5 GB) concatenated. `preTableK_getD`: entry `j` is function `j`'s.
-/

namespace LeanVM.SaltedGuest.Decoder

open LeanVM.Guest.Check LeanVM.Guest.Fast

@[expose] public section

theorem range'_cat {a n b m : ℕ} (h : a + n = b) :
    List.range' a n ++ List.range' b m = List.range' a (n + m) := by
  subst h
  exact List.range'_append_1

/-- **The salted functions' preconditions**, entry `j` function `j`'s. -/
noncomputable def preTableK : Array (Option FnPre) := (preChunk0 ++ preChunk1 ++ preChunk2 ++ preChunk3 ++ preChunk4 ++ preChunk5 ++ preChunk6 ++ preChunk7).toArray

theorem preTableK_eq : preTableK = ((List.range nFns).map fun j ↦ fnPreOf (glob.sig j)).toArray := by
  rw [preTableK, ← preChunk0_eq, ← preChunk1_eq, ← preChunk2_eq, ← preChunk3_eq, ← preChunk4_eq, ← preChunk5_eq, ← preChunk6_eq, ← preChunk7_eq]
  simp only [← List.map_append]
  iterate 7 rw [range'_cat (by norm_num)]
  rw [List.range_eq_range']
  rfl

/-- Entry `j < nFns` of the table is the salted function `j`'s precondition. -/
theorem preTableK_getD {j : ℕ} (hj : j < nFns) :
    preTableK.getD j none = fnPreOf (glob.sig j) := by
  rw [preTableK_eq]
  simp [Array.getD, hj]

end

end LeanVM.SaltedGuest.Decoder
