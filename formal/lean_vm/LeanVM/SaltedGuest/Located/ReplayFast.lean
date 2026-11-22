/-
  LeanVM.SaltedGuest.Located.ReplayFast

  The salted replayed frame map, indexed: the entries of the replayed states filed once in a sorted
  map, and the precondition decided by a discrete logarithm.
-/

module

public import LeanVM.SaltedGuest.Located.Replay
public import LeanVM.Guest.Located.ReplayFast

/-!
# The salted replayed frame map, indexed

The deployed `Located/ReplayFast.lean`'s indexed frame map over the salted `glob`, `nFns`,
`nameIndex` and `certByName` (its parts that read no function of the guest are the deployed ones):
`preTestWithK dl` (`preTestWithK_eq`: by a discrete logarithm it is `preTestK`), `pcTableK`,
`entryKeyK`, `entryTableK` (one pass over the states, `entryTableK_get?`: it answers as
`firstEnteredK`), `frameVFastK`, and **`frameVWithK_eq_frameVFastK`**: the salted replayed frame
map reads the table.
-/

namespace LeanVM.SaltedGuest.Located

open LeanVM.Parameters LeanVM.Semantics LeanVM.SaltedGuest LeanVM.Guest.Core LeanVM.Guest.Check
open LeanVM.Extraction LeanVM.Extraction.Fast LeanVM.SaltedGuest.End

@[expose] public section

section Log

variable {dl : K → Option ℕ}

/-- **Function `j`'s precondition, decided by the logarithm** (`preTestK`). -/
noncomputable def preTestWithK (dl : K → Option ℕ) (rd : Reader) (j : ℕ) (fp : K) : Bool :=
  glob.good j && Guest.Located.envTest rd fp (glob.sig j).env && Guest.Located.bndTestWith dl rd fp (glob.sig j).pre &&
    Guest.Located.memTestWith dl rd fp (glob.sig j).mem

/-- **By the logarithm, the precondition's test is `preTestK`.** -/
theorem preTestWithK_eq (hdl : Guest.Located.DiscreteLogSpec dl) : preTestWithK dl = preTestK := by
  funext rd j fp
  rw [preTestWithK, preTestK, Guest.Located.bndTestWith_eq hdl, Guest.Located.memTestWith_eq hdl]

end Log

/-! ## The entries, indexed -/

section Index

attribute [local instance] lexOrd

/-- A callee's name is `f` exactly when its index is `f`'s (the names are distinct). -/
theorem name_eq_iffK {j : ℕ} (hj : glob.good j = true) (f : String) :
    (glob.sig j).name = f ↔ j = nameIndex f := by
  have hj' : 2 ≤ j ∧ j < nFns := by simpa [glob, good] using hj
  have hl : j - 1 < coreProgram.length := by
    have := coreProgram_length; simp only [nFns] at hj'; omega
  have hname : (glob.sig j).name = coreProgram[j - 1].name := by
    show (coreOf j).name = _
    rw [coreOf, nth_eq hl]
  rw [hname, nameIndex]
  constructor
  · rintro rfl
    rw [findIdx_name_of_nodup coreProgram_names_nodup hl]
    omega
  · intro h
    have hi : coreProgram.findIdx (fun g ↦ g.name == f) = j - 1 := by omega
    have hlt : coreProgram.findIdx (fun g ↦ g.name == f) < coreProgram.length := hi ▸ hl
    have := List.findIdx_getElem (w := hlt)
    simp only [hi, beq_iff_eq] at this
    exact this

/-- **The functions entered at each pc**: the code of function `j`'s entry to `j`, `j < nFns`. -/
noncomputable def pcTableK : SortedMap ℕ (List ℕ) :=
  (List.range nFns).foldl (fun m j ↦ Guest.Located.addAt m (Guest.Located.laneCode (addressOfIndex (glob.sig j).entry))
      j) .empty

/-- The functions the table gives at a pc are those entered there. -/
theorem mem_pcTableK {pc : K} {j : ℕ} :
    j ∈ pcTableK.getD (Guest.Located.laneCode pc) [] ↔ j < nFns ∧ pc = addressOfIndex (glob.sig j).entry := by
  rw [pcTableK, Guest.Located.mem_foldl_addAt, SortedMap.getD_empty, List.mem_range]
  simp only [List.not_mem_nil, false_or]
  exact and_congr_right fun _ ↦ ⟨fun h ↦ (Guest.Located.laneCode_injective h).symm, fun h ↦ h ▸ rfl⟩

/-- The key under which state `r`, at function `j`'s entry, files its frame. -/
noncomputable def entryKeyK (rd : Reader) (r : Registers K) (j : ℕ) : Guest.Located.CallKey :=
  Guest.Located.callKey j (Guest.Located.wordsWith rd r.fp 2 (glob.sig j).nargs)
    (Guest.Located.wordsWith rd r.fp (2 + (glob.sig j).nargs) (glob.sig j).nret)

/-- The table with state `r` filed: under the key of each function entered at `r` whose test `pre`
holds there, `r`'s frame, unless the key has one. -/
noncomputable def fileStateK (pre : ℕ → K → Bool) (rd : Reader) (m : SortedMap Guest.Located.CallKey K)
    (r : Registers K) : SortedMap Guest.Located.CallKey K :=
  (pcTableK.getD (Guest.Located.laneCode r.pc) []).foldl
    (fun m j ↦ if pre j r.fp then insertIfNew m (entryKeyK rd r j) r.fp else m) m

/-- **The entries of the states, indexed**: from a call's key to the frame of the first state at
which a function of that key was entered, `pre` holding. -/
noncomputable def entryTableK (pre : ℕ → K → Bool) (states : List (Registers K)) (rd : Reader) :
    SortedMap Guest.Located.CallKey K :=
  states.foldl (fileStateK pre rd) .empty

/-- What state `r` files under `k`. -/
noncomputable def stateHitK (pre : ℕ → K → Bool) (rd : Reader) (r : Registers K) (k : Guest.Located.CallKey) :
    Option K :=
  if (pcTableK.getD (Guest.Located.laneCode r.pc) []).any (fun j ↦ pre j r.fp && decide (entryKeyK rd r j = k))
  then some r.fp else none

theorem get?_fileStateK (pre : ℕ → K → Bool) (rd : Reader) (r : Registers K) (k : Guest.Located.CallKey) :
    ∀ (js : List ℕ) (m : SortedMap Guest.Located.CallKey K),
      (js.foldl (fun m j ↦ if pre j r.fp then insertIfNew m (entryKeyK rd r j) r.fp else m) m).get? k =
        (m.get? k).or (if js.any (fun j ↦ pre j r.fp && decide (entryKeyK rd r j = k))
          then some r.fp else none)
  | [], m => by simp
  | j :: js, m => by
    rw [List.foldl_cons, get?_fileStateK pre rd r k js]
    by_cases hp : pre j r.fp = true
    · rw [ite_eq_left hp, Guest.Located.get?_insertIfNew]
      by_cases hk : entryKeyK rd r j = k
      · simp only [hk, ↓reduceIte, List.any_cons, hp, decide_true, Bool.and_self, Bool.true_or]
        cases m.get? k <;> simp
      · simp only [hk, ↓reduceIte, Option.or_none, List.any_cons, hp, decide_false, Bool.and_false,
          Bool.false_or]
    · rw [ite_eq_right hp]
      simp [hp]

set_option maxRecDepth 100000 in
theorem get?_entryTable_foldlK (pre : ℕ → K → Bool) (rd : Reader) (k : Guest.Located.CallKey) :
    ∀ (states : List (Registers K)) (m : SortedMap Guest.Located.CallKey K),
      (states.foldl (fileStateK pre rd) m).get? k =
        (m.get? k).or (states.findSome? fun r ↦ stateHitK pre rd r k)
  | [], m => by simp
  | r :: states, m => by
    rw [List.foldl_cons, get?_entryTable_foldlK pre rd k states, fileStateK, get?_fileStateK,
      List.findSome?_cons, stateHitK]
    by_cases hA : (pcTableK.getD (Guest.Located.laneCode r.pc) []).any
        (fun j ↦ pre j r.fp && decide (entryKeyK rd r j = k)) = true
    · rw [ite_eq_left hA]
      cases m.get? k <;> rfl
    · rw [ite_eq_right hA]
      cases m.get? k <;> rfl

theorem any_entry_eqK (rd : Reader) (r : Registers K) (f : String) (args rets : List E) :
    ((pcTableK.getD (Guest.Located.laneCode r.pc) []).any fun j ↦
        preTestK rd j r.fp && decide (entryKeyK rd r j = Guest.Located.callKey (nameIndex f) args rets)) =
      (List.range nFns).any (enteredTestK rd f args rets r) := by
  apply Bool.eq_iff_iff.mpr
  rw [List.any_eq_true, List.any_eq_true]
  constructor
  · rintro ⟨j, hj, h⟩
    obtain ⟨hj, hpc⟩ := mem_pcTableK.mp hj
    rw [Bool.and_eq_true, decide_eq_true_iff, entryKeyK, Guest.Located.callKey_eq_iff] at h
    obtain ⟨hp, hn, ha, hr⟩ := h
    have hgood : glob.good j = true := by
      simp only [preTestK, Bool.and_eq_true] at hp; exact hp.1.1.1
    refine ⟨j, List.mem_range.mpr hj, ?_⟩
    simp only [enteredTestK, Bool.and_eq_true]
    exact ⟨⟨⟨⟨decide_eq_true hpc, decide_eq_true ((name_eq_iffK hgood f).mpr hn)⟩, hp⟩,
      decide_eq_true ha⟩, decide_eq_true hr⟩
  · rintro ⟨j, hj, h⟩
    simp only [enteredTestK, Bool.and_eq_true] at h
    obtain ⟨⟨⟨⟨hpc, hn⟩, hp⟩, ha⟩, hr⟩ := h
    have hgood : glob.good j = true := by
      simp only [preTestK, Bool.and_eq_true] at hp; exact hp.1.1.1
    refine ⟨j, mem_pcTableK.mpr ⟨List.mem_range.mp hj, of_decide_eq_true hpc⟩, ?_⟩
    rw [Bool.and_eq_true, decide_eq_true_iff, entryKeyK, Guest.Located.callKey_eq_iff]
    exact ⟨hp, (name_eq_iffK hgood f).mp (of_decide_eq_true hn), of_decide_eq_true ha,
      of_decide_eq_true hr⟩

/-- **The table answers as `firstEnteredK`**, its test the precondition's. -/
theorem entryTableK_get? (states : List (Registers K)) (rd : Reader) (f : String) (args rets : List E) :
    (entryTableK (preTestK rd) states rd).get? (Guest.Located.callKey (nameIndex f) args rets) =
      firstEnteredK states rd f args rets := by
  unfold entryTableK firstEnteredK
  rw [get?_entryTable_foldlK, SortedMap.get?_empty, Option.none_or]
  refine congrArg (fun F ↦ List.findSome? F states) (funext fun r ↦ ?_)
  show stateHitK (preTestK rd) rd r (Guest.Located.callKey (nameIndex f) args rets) = _
  unfold stateHitK
  rw [any_entry_eqK]

/-- **The replayed frame map, read off the table** built once from the states, with the test
`pre`. -/
noncomputable def frameVFastK (pre : ℕ → K → Bool) (states : List (Registers K)) (rd : Reader) :
    FrameMap :=
  let table := entryTableK pre states rd
  fun f args rets ↦ match table.get? (Guest.Located.callKey (nameIndex f) args rets) with
    | some fp => fun v ↦ Guest.Located.wordWith rd fp ((certByName f).locs.getD v.idx 0)
    | none => fun _ ↦ 0

/-- **The frame map reads the table**, built once from the states. -/
theorem frameVWithK_eq_frameVFastK (states : List (Registers K)) (rd : Reader) :
    frameVWithK states rd = frameVFastK (preTestK rd) states rd := by
  funext f args rets
  simp only [frameVFastK, frameVWithK, entryTableK_get?]
  rfl

end Index

end
end LeanVM.SaltedGuest.Located
