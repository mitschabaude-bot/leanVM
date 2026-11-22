/-
  LeanVM.SaltedGuest.Decoder.EntryTableEq

  The salted decoder's compiled frame map is the salted replayed frame map keyed by index.
-/

module

public import LeanVM.SaltedGuest.Decoder.EntryTable
public import LeanVM.SaltedGuest.Decoder.GuestTablesCheck
public import LeanVM.SaltedGuest.Decoder.LocsCheck
public import LeanVM.Cost.Decoder.EntryTableEq
public import LeanVM.SaltedGuest.B1.Main.FactsK
import all LeanVM.Protocol.Extraction.Fast.SortedMap

/-!
# The salted compiled frame map, restated, is the replayed one

At the salted tables (`GuestTablesCheck.lean`, `LocsCheck.lean`): `pcTableTK entriesK = pcTableK`,
`entryTableTK … = entryTableK`, a packed cell is the certificate's (`cellAtK_locsTableK`), and
**`frameAtK_eq`**: the frame map on the entry table is `Located.frameVFastNK pre states rd`, the
salted replayed frame map keyed by index (a call found in the table is of a salted function,
`entryTableK_lt`). The entry table as one sorted array: its binary search is the table's `get?`
(`searchIn_entryArrayTK`, through the deployed lemmas on the stable sort and the first of each
run), so **`frameAtAK_eq`**. `main`'s valuations: **`mainValK_eq`** (the certificate's cells at
`fp = 1`) and **`mainValDK_eq`** (`B1.Main.mainVal` of it, `mainRiK = B1.Main.mainRi`).
-/

namespace LeanVM.SaltedGuest.Decoder

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Extraction.Fast
open LeanVM.Cost.Decoder LeanVM.SaltedGuest.Located

attribute [local instance] lexOrd

@[expose] public section

/-! ## The tables -/

theorem entriesK_getD {j : ℕ} (hj : j < nFns) : entriesK.getD j 0 = (glob.sig j).entry :=
  guestEntries_eq j hj

theorem argCountsK_getD {j : ℕ} (hj : j < nFns) : argCountsK.getD j 0 = (glob.sig j).nargs :=
  guestArgCounts_eq j hj

theorem retCountsK_getD {j : ℕ} (hj : j < nFns) : retCountsK.getD j 0 = (glob.sig j).nret :=
  guestRetCounts_eq j hj

set_option maxRecDepth 100000 in
theorem locsBlocksList_length : locsBlocksList.length = nFns := by
  have h := locsBlocksList_lengths
  simp only [List.cons.injEq, and_true] at h
  obtain ⟨b0, b1, b2, b3⟩ := h
  simp only [locsBlocksList, List.length_append, b0, b1, b2, b3, nFns]

/-- **A packed cell is the certificate's.** -/
theorem cellAtK_locsTableK {j : ℕ} (hj : j < nFns) (i : ℕ) :
    cellAtK (locsTableK.getD j #[]) i = (certOf j).locs.getD i 0 := by
  have hl : j < locsBlocksList.length := locsBlocksList_length ▸ hj
  have hrow : locsTableK.getD j #[] = (locsBlocksList.getD j []).toArray := by
    simp [locsTableK, Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD, hl]
  rw [hrow, ← guestLocsList_eq j hj, ← cellIn_of_blocksOk (locsBlocks_ok j (by unfold nFns at hj; omega)) i]
  simp [cellAtK, cellIn, Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD]

/-! ## The entry table -/

theorem foldl_congr_memK {α β : Type} {f g : α → β → α} :
    ∀ (l : List β) (a : α), (∀ a, ∀ b ∈ l, f a b = g a b) → l.foldl f a = l.foldl g a :=
  foldl_congr_mem

/-- **The table of entries is the salted guest's.** -/
theorem pcTableTK_eq : pcTableTK entriesK = pcTableK := by
  unfold pcTableTK pcTableK
  refine foldl_congr_mem _ _ fun m j hj ↦ ?_
  rw [addEntryK, entriesK_getD (List.mem_range.mp hj)]

theorem entryKeyTK_eq (rd : Reader) (r : Registers K) {j : ℕ} (hj : j < nFns) :
    entryKeyTK argCountsK retCountsK rd r j = entryKeyK rd r j := by
  rw [entryKeyTK, entryKeyK, argCountsK_getD hj, retCountsK_getD hj]

theorem fileStateTK_eq (pre : ℕ → K → Bool) (rd : Reader)
    (m : SortedMap Guest.Located.CallKey K) (r : Registers K) :
    fileStateTK (pcTableTK entriesK) argCountsK retCountsK pre rd m r = fileStateK pre rd m r := by
  rw [fileStateTK, fileStateK, pcTableTK_eq]
  refine foldl_congr_mem _ _ fun m j hj ↦ ?_
  rw [fileOneK, entryKeyTK_eq rd r (mem_pcTableK.mp hj).1]

/-- **The entry table is the salted guest's.** -/
theorem entryTableTK_eq (pre : ℕ → K → Bool) (states : List (Registers K)) (rd : Reader) :
    entryTableTK (pcTableTK entriesK) argCountsK retCountsK pre states rd =
      entryTableK pre states rd := by
  have h : fileStateTK (pcTableTK entriesK) argCountsK retCountsK pre rd = fileStateK pre rd := by
    funext m r
    exact fileStateTK_eq pre rd m r
  rw [entryTableTK, entryTableK, h]

/-- **A call the salted entry table holds is of a salted function.** -/
theorem entryTableK_lt {pre : ℕ → K → Bool} {states : List (Registers K)} {rd : Reader} {j : ℕ}
    {args rets : List E} {fp : K}
    (h : (entryTableK pre states rd).get? (Guest.Located.callKey j args rets) = some fp) :
    j < nFns := by
  unfold entryTableK at h
  rw [get?_entryTable_foldlK, SortedMap.get?_empty, Option.none_or] at h
  obtain ⟨r, -, hr⟩ := List.exists_of_findSome?_eq_some h
  unfold stateHitK at hr
  split at hr
  · rename_i hA
    obtain ⟨j', hj', hk⟩ := List.any_eq_true.mp hA
    rw [Bool.and_eq_true, decide_eq_true_iff, entryKeyK, Guest.Located.callKey_eq_iff] at hk
    obtain ⟨-, rfl, -, -⟩ := hk
    exact (mem_pcTableK.mp hj').1
  · cases hr

/-- **The frame map, restated, is the salted replayed one** (keyed by index). -/
theorem frameAtK_eq (pre : ℕ → K → Bool) (states : List (Registers K)) (rd : Reader) :
    frameAtK (entryTableTK (pcTableTK entriesK) argCountsK retCountsK pre states rd) locsTableK rd =
      frameVFastNK pre states rd := by
  funext j args rets v
  rw [entryTableTK_eq]
  unfold frameAtK frameVFastNK
  cases h : (entryTableK pre states rd).get? (Guest.Located.callKey j args rets) with
  | none => rfl
  | some fp =>
    show Guest.Located.wordWith rd fp (cellAtK (locsTableK.getD j #[]) v.idx) = _
    rw [cellAtK_locsTableK (entryTableK_lt h)]

/-! ## The entry table as one sorted array -/

/-- The sorted array's binary search is the first pair filed for the key. -/
theorem searchIn_entryArrayTK (pcT : SortedMap ℕ (List ℕ)) (ac rc : Array ℕ) (pre : ℕ → K → Bool)
    (states : List (Registers K)) (rd : Reader) (k : Guest.Located.CallKey) :
    searchIn (entryArrayTK pcT ac rc pre states rd) k 0 (entryArrayTK pcT ac rc pre states rd).size =
      Extraction.Fast.lookup (entryPairsK pcT ac rc pre rd states) k := by
  unfold entryArrayTK
  have hs := List.pairwise_mergeSort keyLe_trans keyLe_total (entryPairsK pcT ac rc pre rd states)
  rw [searchIn_eq _ (by rw [List.toList_toArray]; exact ascending_dedupFirst _ hs),
    List.toList_toArray, lookup_dedupFirst, lookup_mergeSort]

theorem fileStateTK_eq_foldl (pcT : SortedMap ℕ (List ℕ)) (ac rc : Array ℕ) (pre : ℕ → K → Bool)
    (rd : Reader) (m : SortedMap Guest.Located.CallKey K) (s : Registers K) :
    fileStateTK pcT ac rc pre rd m s =
      (statePairsK pcT ac rc pre rd s).foldl (fun m p ↦ insertIfNew m p.1 p.2) m := by
  unfold fileStateTK statePairsK
  generalize pcT.getD (Guest.Located.laneCode s.pc) [] = js
  induction js generalizing m with
  | nil => rfl
  | cons j js ih =>
    rw [List.foldl_cons, List.filterMap_cons, ih]
    unfold fileOneK pairOfK
    by_cases h : pre j s.fp = true
    · simp only [h, ↓reduceIte, List.foldl_cons]
    · simp only [h, Bool.false_eq_true, ↓reduceIte]

theorem entryTableTK_eq_foldl (pcT : SortedMap ℕ (List ℕ)) (ac rc : Array ℕ) (pre : ℕ → K → Bool)
    (states : List (Registers K)) (rd : Reader) :
    entryTableTK pcT ac rc pre states rd =
      (entryPairsK pcT ac rc pre rd states).foldl (fun m p ↦ insertIfNew m p.1 p.2) .empty := by
  unfold entryTableTK
  generalize (SortedMap.empty : SortedMap Guest.Located.CallKey K) = m
  induction states generalizing m with
  | nil => rfl
  | cons s ss ih =>
    rw [List.foldl_cons, ih, fileStateTK_eq_foldl, entryPairsK, List.foldl_append]

theorem entryTableTK_get? (pcT : SortedMap ℕ (List ℕ)) (ac rc : Array ℕ) (pre : ℕ → K → Bool)
    (states : List (Registers K)) (rd : Reader) (k : Guest.Located.CallKey) :
    (entryTableTK pcT ac rc pre states rd).get? k =
      Extraction.Fast.lookup (entryPairsK pcT ac rc pre rd states) k := by
  rw [entryTableTK_eq_foldl, get?_foldl_insertIfNew, SortedMap.get?_empty, Option.none_or]

/-- **The frame map on the sorted array is the frame map on the entry table.** -/
theorem frameAtAK_entryArrayTK (pcT : SortedMap ℕ (List ℕ)) (ac rc : Array ℕ)
    (pre : ℕ → K → Bool) (states : List (Registers K)) (locs : Array (Array ℕ)) (rd : Reader) :
    frameAtAK (entryArrayTK pcT ac rc pre states rd) locs rd =
      frameAtK (entryTableTK pcT ac rc pre states rd) locs rd := by
  funext j args rets v
  unfold frameAtAK frameAtK
  rw [searchIn_entryArrayTK, entryTableTK_get?]

/-- **The frame map on the sorted array is the salted replayed one** (keyed by index). -/
theorem frameAtAK_eq (pre : ℕ → K → Bool) (states : List (Registers K)) (rd : Reader) :
    frameAtAK (entryArrayTK (pcTableTK entriesK) argCountsK retCountsK pre states rd) locsTableK rd =
      frameVFastNK pre states rd := by
  rw [frameAtAK_entryArrayTK, frameAtK_eq]

/-! ## `main`'s valuations -/

/-- **The salted `main`'s valuation, compiled**: its certificate's cells at `fp = 1`. -/
theorem mainValK_eq (rd : Reader) :
    mainValK locsTableK rd = fun v ↦ Guest.Located.wordWith rd 1 ((certOf 1).locs.getD v.idx 0) := by
  funext v
  rw [mainValK, cellAtK_locsTableK (by decide)]

theorem mainRiK_eq : mainRiK = B1.Main.mainRi := rfl

/-- **At the deployed `main`'s numbers**, `B1.Main.mainVal` of the salted valuation. -/
theorem mainValDK_eq (rd : Reader) :
    mainValDK locsTableK rd = B1.Main.mainVal (mainValK locsTableK rd) := by
  funext v
  rw [mainValDK, B1.Main.mainVal, mainValK]
  rfl

end

end LeanVM.SaltedGuest.Decoder
