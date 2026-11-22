/-
  LeanVM.SaltedGuest.Bounds.PcTableK

  The salted decoder's pc table: its shape, its lookup's price and its build price.
-/

module

public import LeanVM.SaltedGuest.Bounds.EntryArray
public import LeanVM.Cost.Bounds.Decoder.PcTable
import all LeanVM.Protocol.Extraction.Fast.SortedMap

/-!
# The salted pc table

`pcTableTK entriesK` (`Decoder/EntryTable.lean`): the salted guest's `1539` functions filed at the
code of their entry pc, the deployed `pcTableT` (`Cost/Bounds/Decoder/PcTable.lean`) with the
entries read off the array `entriesK`:

* `pcTableTK_good`: a good map of word-sized keys, `1539` insertions (below `2^11`);
* **`pcTableTK_get_cost`**: a lookup at most `7093`, the `Gpc` of `entryArrayTK_cost`;
* **`pcTableTK_getD_length`**: at most two functions at one pc, the `M` of `entryArrayTK_cost`;
  `pcTableTK_getD_lt`: every function filed is word-sized;
* **`pcTableTK_cost`**: built at most `14460000`.
-/

namespace LeanVM.SaltedGuest.Bounds

open LeanVM.Cost LeanVM.Cost.Decoder LeanVM.Cost.Library LeanVM.Cost.Bounds LeanVM.Parameters
open LeanVM.Semantics LeanVM.Extraction LeanVM.Extraction.Fast LeanVM.Guest.Located
open LeanVM.SaltedGuest.Decoder

@[expose] public section

/-! ## The entries -/

theorem guestEntriesListK_lt :
    LeanVM.SaltedGuest.Decoder.guestEntriesList.all (· < 2 ^ 19) = true := by decide +kernel

/-- The salted entry pcs increase, a linear check. -/
theorem guestEntriesListK_chain :
    LeanVM.SaltedGuest.Decoder.guestEntriesList.IsChain (· < ·) := by decide +kernel

/-- A salted entry pc is the entry of at most two functions (of one: they increase). -/
theorem guestEntriesListK_count :
    LeanVM.SaltedGuest.Decoder.guestEntriesList.all
      (fun e ↦ LeanVM.SaltedGuest.Decoder.guestEntriesList.count e ≤ 2) = true := by
  have hp : LeanVM.SaltedGuest.Decoder.guestEntriesList.Pairwise (· < ·) :=
    List.isChain_iff_pairwise.mp guestEntriesListK_chain
  have hn : LeanVM.SaltedGuest.Decoder.guestEntriesList.Nodup := hp.imp Nat.ne_of_lt
  rw [List.all_eq_true]
  intro e _
  have := List.nodup_iff_count_le_one.mp hn e
  exact decide_eq_true (by omega)

theorem entriesK_getD (j : ℕ) :
    entriesK.getD j 0 = LeanVM.SaltedGuest.Decoder.guestEntriesList.getD j 0 := by
  rw [entriesK, Array.getD_eq_getD_getElem?, List.getElem?_toArray, List.getD_eq_getElem?_getD]

theorem entryK_lt (j : ℕ) : entriesK.getD j 0 < 2 ^ 19 := by
  have h := guestEntriesListK_lt
  rw [List.all_eq_true] at h
  rw [entriesK_getD, List.getD_eq_getElem?_getD]
  cases hj : LeanVM.SaltedGuest.Decoder.guestEntriesList[j]? with
  | none => simp
  | some x =>
    simp only [Option.getD_some]
    exact of_decide_eq_true (h x (List.mem_of_getElem? hj))

/-- The code of the salted function `j`'s entry pc. -/
def pcCodeK (j : ℕ) : ℕ := laneCode (addressOfIndex (entriesK.getD j 0))

theorem pcCodeK_key (j : ℕ) : NatKey (pcCodeK j) := UInt64.toNat_lt _

theorem addEntryK_eq (m : SortedMap ℕ (List ℕ)) (j : ℕ) :
    addEntryK entriesK m j = m.insert (pcCodeK j) (j :: m.getD (pcCodeK j) []) := rfl

/-! ## The table's shape -/

/-- The pc table's fold keeps a good map of word-sized keys, one insertion per function. -/
theorem pcFoldK_good : ∀ (l : List ℕ) (m : SortedMap ℕ (List ℕ)), smGood m →
    KeysIn NatKey m.levels →
      smGood (l.foldl (addEntryK entriesK) m) ∧ KeysIn NatKey (l.foldl (addEntryK entriesK) m).levels ∧
        smWeightSum (l.foldl (addEntryK entriesK) m) = smWeightSum m + l.length
  | [], m, hg, hQ => ⟨hg, hQ, by simp⟩
  | j :: l, m, hg, hQ => by
    rw [List.foldl_cons, addEntryK_eq]
    obtain ⟨h1, h2⟩ := smGood_insert hg (pcCodeK j) (j :: m.getD (pcCodeK j) [])
    obtain ⟨h3, h4, h5⟩ := pcFoldK_good l _ h1 (keysIn_insert hQ (pcCodeK_key j) _)
    refine ⟨h3, h4, ?_⟩
    rw [h5, h2]
    simp only [List.length_cons]
    omega

/-- **The salted pc table is good**: word-sized keys, `1539` insertions. -/
theorem pcTableTK_good :
    smGood (pcTableTK entriesK) ∧ KeysIn NatKey (pcTableTK entriesK).levels ∧
      smWeightSum (pcTableTK entriesK) = 1539 := by
  have := pcFoldK_good (List.range LeanVM.SaltedGuest.nFns) SortedMap.empty smGood_empty
    (fun _ h ↦ by simp [SortedMap.empty] at h)
  rw [smWeightSum_empty, List.length_range] at this
  exact this

variable (P : MachineProgram)

/-- **A lookup in the salted pc table** (`getPcC`): at most `7093`. -/
theorem pcTableTK_get_cost (hP : Includes P getPcC.costDeps) (k : ℕ) (hk : NatKey k) :
    machineCost P getPcC.costIdx [encodeValue (pcTableTK entriesK), encodeValue k] ≤ 7093 := by
  obtain ⟨hg, hQ, hw⟩ := pcTableTK_good
  obtain ⟨hlev, hsz⟩ := smGood_levels_le hg (D := 11) (by rw [hw]; norm_num)
  have := getPc_cost P hP 11 (pcTableTK entriesK) hQ hlev
    (fun l hl ↦ (hsz l hl).1.trans (hsz l hl).2) k hk
  rw [wl_eleven] at this
  omega

/-! ## The functions at one pc -/

theorem pcFoldK_getD : ∀ (l : List ℕ) (m : SortedMap ℕ (List ℕ)) (k : ℕ),
    (l.foldl (addEntryK entriesK) m).getD k [] =
      (l.filter fun j ↦ decide (pcCodeK j = k)).reverse ++ m.getD k []
  | [], m, k => by simp
  | j :: l, m, k => by
    rw [List.foldl_cons, pcFoldK_getD l _ k, addEntryK_eq, SortedMap.getD_insert]
    by_cases h : pcCodeK j = k
    · subst h
      simp
    · simp [h]

theorem pcTableTK_getD (k : ℕ) :
    (pcTableTK entriesK).getD k [] =
      ((List.range LeanVM.SaltedGuest.nFns).filter fun j ↦ decide (pcCodeK j = k)).reverse := by
  have := pcFoldK_getD (List.range LeanVM.SaltedGuest.nFns) SortedMap.empty k
  rw [SortedMap.getD_empty, List.append_nil] at this
  exact this

/-- **Every function filed is word-sized.** -/
theorem pcTableTK_getD_lt (k : ℕ) : ∀ j ∈ (pcTableTK entriesK).getD k [], j < 2 ^ 64 := by
  intro j hj
  rw [pcTableTK_getD, List.mem_reverse, List.mem_filter, List.mem_range] at hj
  have : LeanVM.SaltedGuest.nFns = 1539 := rfl
  omega

set_option maxRecDepth 100000 in
/-- **At most two functions at one pc.** -/
theorem pcTableTK_getD_length (k : ℕ) : ((pcTableTK entriesK).getD k []).length ≤ 2 := by
  rw [pcTableTK_getD, List.length_reverse, ← List.countP_eq_length_filter]
  have hlen : LeanVM.SaltedGuest.Decoder.guestEntriesList.length = LeanVM.SaltedGuest.nFns := rfl
  by_cases h0 : ∃ j0 ∈ List.range LeanVM.SaltedGuest.nFns, pcCodeK j0 = k
  · obtain ⟨j0, hj0, hk⟩ := h0
    have hj0' := List.mem_range.mp hj0
    have hmono : (List.range LeanVM.SaltedGuest.nFns).countP (fun j ↦ decide (pcCodeK j = k)) ≤
        (List.range LeanVM.SaltedGuest.nFns).countP (fun j ↦ decide
          (LeanVM.SaltedGuest.Decoder.guestEntriesList.getD j 0 =
            LeanVM.SaltedGuest.Decoder.guestEntriesList.getD j0 0)) := by
      refine List.countP_mono_left fun j _ hj ↦ ?_
      rw [decide_eq_true_iff] at hj ⊢
      have hc : pcCodeK j = pcCodeK j0 := hj.trans hk.symm
      unfold pcCodeK at hc
      have hg : addressOfIndex (entriesK.getD j 0) = addressOfIndex (entriesK.getD j0 0) :=
        laneCode_injective hc
      have := gpow_injOn (show entriesK.getD j 0 ∈ Set.Iio (2 ^ 64 - 1) by
          have := entryK_lt j; simp only [Set.mem_Iio]; omega)
        (show entriesK.getD j0 0 ∈ Set.Iio (2 ^ 64 - 1) by
          have := entryK_lt j0; simp only [Set.mem_Iio]; omega) hg
      rwa [entriesK_getD, entriesK_getD] at this
    have hcnt : (List.range LeanVM.SaltedGuest.nFns).countP (fun j ↦ decide
        (LeanVM.SaltedGuest.Decoder.guestEntriesList.getD j 0 =
          LeanVM.SaltedGuest.Decoder.guestEntriesList.getD j0 0)) =
        LeanVM.SaltedGuest.Decoder.guestEntriesList.count
          (LeanVM.SaltedGuest.Decoder.guestEntriesList.getD j0 0) := by
      rw [← hlen]; exact range_countP_getD _ _
    have hc := guestEntriesListK_count
    rw [List.all_eq_true] at hc
    have hmem : LeanVM.SaltedGuest.Decoder.guestEntriesList.getD j0 0 ∈
        LeanVM.SaltedGuest.Decoder.guestEntriesList := by
      rw [List.getD_eq_getElem _ _ (by rw [hlen]; exact hj0')]
      exact List.getElem_mem _
    have := of_decide_eq_true (hc _ hmem)
    omega
  · simp only [not_exists, not_and] at h0
    have : (List.range LeanVM.SaltedGuest.nFns).countP (fun j ↦ decide (pcCodeK j = k)) = 0 :=
      List.countP_eq_zero.2 fun j hj ↦ by simpa using h0 j hj
    omega

/-! ## Building it -/

set_option maxRecDepth 100000 in
/-- One function filed (`addEntryKC`), amortized: at most `9344`. -/
theorem addEntryK_amortized (hP : Includes P addEntryKC.costDeps) (m : SortedMap ℕ (List ℕ))
    (r : ℕ) (hm : PcInv m (r + 1)) (j : ℕ) :
    PcInv (addEntryK entriesK m j) r ∧
      machineCost P addEntryKC.costIdx [encodeValue entriesK, encodeValue m, encodeValue j] +
          37 * potential 11 (addEntryK entriesK m j).levels ≤ 37 * potential 11 m.levels + 9344 := by
  obtain ⟨hg, hQ, hw⟩ := hm
  have hN : smWeightSum m < 2 ^ 11 := by omega
  obtain ⟨hlev, hsz⟩ := smGood_levels_le hg hN
  obtain ⟨h1, h2⟩ := smGood_insert hg (pcCodeK j) (j :: m.getD (pcCodeK j) [])
  refine ⟨by rw [addEntryK_eq]; exact ⟨h1, keysIn_insert hQ (pcCodeK_key j) _, by omega⟩, ?_⟩
  rw [addEntryKC.costEq P hP, addAtC.costEq P (by includes), insertPcC.costEq P (by includes)]
  have hp := powSqW_cost P (by includes) (W := 19) (by norm_num) (by norm_num) (entryK_lt j)
  have hget := getPc_cost P (by includes) 11 m hQ hlev
    (fun l hl ↦ (hsz l hl).1.trans (hsz l hl).2) _ (pcCodeK_key j)
  have hcarry := carryPc_amortized P (by includes) 11 m hg hQ hN
    ⟨1, #[(pcCodeK j, j :: m.getD (pcCodeK j) [])], by simp [Ascending]⟩ rfl rfl
    (fun e he ↦ by simp at he; rw [he]; exact pcCodeK_key j)
  have hins : (addEntryK entriesK m j).levels =
      carry ⟨1, #[(pcCodeK j, j :: m.getD (pcCodeK j) [])], by simp [Ascending]⟩ m.levels := rfl
  rw [hins]
  unfold psAt at hp
  rw [wl_eleven] at hget hcarry
  change machineCost P getPcC.costIdx [encodeValue m, encodeValue (pcCodeK j)] ≤ _ at hget
  generalize m.get? (laneCode (addressOfIndex (entriesK.getD j 0))) = o
  cases o <;> dsimp only <;> unfold pcCodeK at hget hcarry ⊢ <;> omega

set_option maxRecDepth 100000 in
/-- **The salted pc table** (`pcTableTKC` at `entriesK`), built once: at most `14460000`. -/
theorem pcTableTK_cost (hP : Includes P pcTableTKC.costDeps) :
    machineCost P pcTableTKC.costIdx [encodeValue entriesK] ≤ 14460000 := by
  rw [pcTableTKC.costEq P hP]
  have hn : LeanVM.SaltedGuest.nFns = 1539 := rfl
  have hr := rangeLoop_cost P (by includes) LeanVM.SaltedGuest.nFns [] (by rw [hn]; norm_num)
  obtain ⟨-, hF⟩ := listFoldl_amortized' P (by includes) _
    (.closure pcTableTKC.lam0.costIdx [encodeValue entriesK])
    (fun m j ↦ RunsApp.of_spec (pcTableTKC.lam0.costSpec P (by includes) entriesK m j))
    9360 (fun m ↦ 37 * potential 11 m.levels) PcInv (List.range LeanVM.SaltedGuest.nFns)
    SortedMap.empty
    ⟨smGood_empty, fun _ h ↦ by simp [SortedMap.empty] at h, by
      simp [smWeightSum_empty, hn]⟩
    (fun acc r hacc j _ ↦ by
      obtain ⟨h1, h2⟩ := addEntryK_amortized P (by includes) acc r hacc j
      refine ⟨h1, ?_⟩
      rw [appCost_fn, List.singleton_append, pcTableTKC.lam0.costEq P (by includes)]
      simp only [List.length_cons, List.length_nil]
      omega)
  have h0 : potential 11 (SortedMap.empty : SortedMap ℕ (List ℕ)).levels = 0 := rfl
  rw [h0, Nat.mul_zero, Nat.zero_add, List.length_range] at hF
  rw [hn] at hr hF ⊢
  omega

end

end LeanVM.SaltedGuest.Bounds
