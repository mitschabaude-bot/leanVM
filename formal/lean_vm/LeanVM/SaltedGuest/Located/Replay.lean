/-
  LeanVM.SaltedGuest.Located.Replay

  The salted guest's frame map of a valid execution, by replaying its run: a call's valuation is
  that of the first frame at which the run entered the callee on the call's words.
-/

module

public import LeanVM.SaltedGuest.EndKnow
public import LeanVM.SaltedGuest.SoundFacts
public import LeanVM.Guest.Located.Replay

/-!
# The salted replayed frame map

The deployed `Located.replayFrameV` for the salted guest: the run from `(g^0, 1)` replayed
(`Guest.Located.statesIn`, through the indices of the addresses), a call `f args rets` given the
valuation of the first state that is the entry of a salted function named `f`, whose precondition
holds at the state's frame (`preTestK`, decided) and whose frame's argument and return cells hold
`args` and `rets` (`enteredTestK`). It chooses nothing: every test is decided by evaluation.

**`unfoldsV_replayK`**: on a valid execution, the salted located relation `RLg` unfolds along the
replayed frame map (the deployed `unfoldsV_replay`, over the salted `glob` and B2).
-/

namespace LeanVM.SaltedGuest.Located

open LeanVM.Parameters LeanVM.Semantics LeanVM.SaltedGuest LeanVM.Guest LeanVM.Guest.Core
open LeanVM.SaltedGuest.Check LeanVM.Guest.Exec LeanVM.Extraction
open LeanVM.Protocol.Halting LeanVM.SaltedGuest.End

@[expose] public section

/-- **Salted function `j`'s precondition at frame `fp`, decided**, but for the jump table and the
semantic tuples (the deployed `preTest` over the salted `glob`). -/
noncomputable def preTestK (rd : Reader) (j : ℕ) (fp : K) : Bool :=
  glob.good j && Guest.Located.envTest rd fp (glob.sig j).env &&
    Guest.Located.bndTest rd fp (glob.sig j).pre && Guest.Located.memTest rd fp (glob.sig j).mem

section Tests

variable {κ : ℕ} {L : MemoryImage κ} {fp : K}

/-- **The decided precondition is `Check.Pre`**, the jump table and the semantic tuples holding. -/
theorem preTestK_iff (hjt : JTHolds glob L) {j : ℕ} (hsem : SemHolds glob L fp (glob.sig j).sem) :
    preTestK L.read j fp = true ↔ Pre glob L j fp := by
  unfold preTestK Pre
  simp only [Bool.and_eq_true, Guest.Located.envTest_iff, Guest.Located.bndTest_iff,
    Guest.Located.memTest_iff]
  exact ⟨fun ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ ↦ ⟨h1, hjt, h2, h3, h4, hsem⟩,
    fun ⟨h1, _, h2, h3, h4, _⟩ ↦ ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩⟩

theorem frameWords_getDK {n o : ℕ} (h1 : 2 ≤ o) (h2 : o < 2 + n) :
    (frameWords L fp 2 n).getD (o - 2) 0 = wd L fp o := by
  rw [List.getD_eq_getElem _ _ (by simp [frameWords]; omega)]
  simp only [frameWords, List.getElem_map, List.getElem_range]
  congr 1
  omega

/-- **Semantic tuples on argument cells carry over** between frames holding the same argument
words. -/
theorem semHolds_of_argsK {fp' : K} {n : ℕ} {sems : List (ℕ × List ℕ)}
    (hcells : ∀ s ∈ sems, ∀ o ∈ s.2, 2 ≤ o ∧ o < 2 + n)
    (hargs : frameWords L fp 2 n = frameWords L fp' 2 n) (h : SemHolds glob L fp sems) :
    SemHolds glob L fp' sems := by
  intro s hs
  have hw : s.2.map (wd L fp') = s.2.map (wd L fp) := List.map_congr_left fun o ho ↦ by
    obtain ⟨h1, h2⟩ := hcells s hs o ho
    rw [← frameWords_getDK h1 h2, ← frameWords_getDK h1 h2, hargs]
  rw [hw]
  exact h s hs

end Tests

/-! ## The replayed frame map -/

/-- **Salted function `j` was entered at the state `r` on the words `args`, `rets`**, decided. -/
noncomputable def enteredTestK (rd : Reader) (f : String) (args rets : List E) (r : Registers K)
    (j : ℕ) : Bool :=
  decide (r.pc = addressOfIndex (glob.sig j).entry) && decide ((glob.sig j).name = f) &&
    preTestK rd j r.fp &&
    decide (Guest.Located.wordsWith rd r.fp 2 (glob.sig j).nargs = args) &&
    decide (Guest.Located.wordsWith rd r.fp (2 + (glob.sig j).nargs) (glob.sig j).nret = rets)

/-- **The first frame of `states` at which a salted function named `f` was entered on `args`,
`rets`**. -/
noncomputable def firstEnteredK (states : List (Registers K)) (rd : Reader) (f : String)
    (args rets : List E) : Option K :=
  states.findSome? fun r ↦
    if (List.range nFns).any (enteredTestK rd f args rets r) then some r.fp else none

/-- The frame map of the states `states`, read with `rd`: a call's valuation is that of the first
frame of `states` its callee was entered at on the call's words. -/
noncomputable def frameVWithK (states : List (Registers K)) (rd : Reader) : FrameMap :=
  fun f args rets ↦ match firstEnteredK states rd f args rets with
    | some fp => fun v ↦ Guest.Located.wordWith rd fp ((certByName f).locs.getD v.idx 0)
    | none => fun _ ↦ 0

/-- **The salted replayed frame map of the memory `L`**: the run from `(g^0, 1)` replayed through
the indices of the addresses, a call's valuation that of the first frame the run entered its
callee at on the call's words. -/
noncomputable def replayFrameVK {κ : ℕ} (L : MemoryImage κ) : FrameMap :=
  frameVWithK (Guest.Located.statesIn (powIndex κ) (powIndex guestProgram.logSize) guestProgram L
    Guest.Located.replayFuel ⟨addressOfIndex 0, 1⟩) (Guest.Located.readIn (powIndex κ) L)

/-- **The salted located relation unfolds along the replayed frame map**, on a valid execution. -/
theorem unfoldsV_replayK (hb2 : B2SoundL) {input : PublicInput} {t : Execution guestProgram}
    (hv : ValidExecution guestProgram input t) :
    UnfoldsV t.memory.read (RLg t.memory) (replayFrameVK t.memory) := by
  obtain ⟨κ, L, T⟩ := t
  have h16 : minLogMem ≤ κ := hv.1.1
  have h32 : κ ≤ maxLogMem := hv.1.2.1
  have hκ : κ < 64 := by unfold maxLogMem at h32; omega
  have hS : ∀ r, stepIn (powIndex κ) (powIndex guestProgram.logSize) guestProgram L r =
      step guestProgram L r :=
    stepIn_powIndex hκ L
  have hT : run guestProgram L T ⟨addressOfIndex 0, 1⟩ = some (Registers.final guestProgram) :=
    safe_of_validExecution hv
  have hTi : run guestProgram L T Registers.initial = some (Registers.final guestProgram) := hv.2
  have hjt : JTHolds glob L := End.jtHolds_of (End.safe_jumpTables hT).1
  have hfuel : T ≤ Guest.Located.replayFuel := (Guest.Located.steps_lt_replayFuel hTi).le
  have hV : replayFrameVK L = frameVWithK (Guest.Located.statesIn (powIndex κ)
      (powIndex guestProgram.logSize) guestProgram L Guest.Located.replayFuel
      ⟨addressOfIndex 0, 1⟩) L.read := by
    rw [replayFrameVK, Guest.Located.readIn_powIndex hκ]
  set states := Guest.Located.statesIn (powIndex κ) (powIndex guestProgram.logSize) guestProgram L
    Guest.Located.replayFuel ⟨addressOfIndex 0, 1⟩
  show UnfoldsV L.read (RLg L) (replayFrameVK L)
  rw [hV]
  intro f args rets h
  obtain ⟨fn, fp, hfind, ⟨-, j, hname, hpre, ⟨n, hn⟩, hw1, hw2⟩, -, -⟩ :=
    (relL_iff coreProgram f args rets).mp h
  -- the run entered `j` at `fp`: a candidate
  have hmem : (⟨addressOfIndex (glob.sig j).entry, fp⟩ : Registers K) ∈ states :=
    Guest.Located.mem_statesIn hS hn ((Guest.Located.run_le_of_halts hT hn).trans hfuel)
  have hj : j < nFns := by
    have := hpre.1
    simp only [glob, good, Bool.and_eq_true, Nat.blt_eq] at this
    exact this.2
  have htest : enteredTestK L.read f args rets ⟨addressOfIndex (glob.sig j).entry, fp⟩ j = true := by
    simp only [enteredTestK, Bool.and_eq_true]
    exact ⟨⟨⟨⟨by simp, decide_eq_true hname⟩, (preTestK_iff hjt hpre.2.2.2.2.2).mpr hpre⟩,
      decide_eq_true hw1⟩, decide_eq_true hw2⟩
  -- the replay finds a frame
  obtain ⟨fp', hfirst⟩ : ∃ fp', firstEnteredK states L.read f args rets = some fp' := by
    unfold firstEnteredK
    rcases hs : states.findSome? (fun r ↦
        if (List.range nFns).any (enteredTestK L.read f args rets r) then some r.fp else none)
        with _ | fp'
    · have := List.findSome?_eq_none_iff.mp hs _ hmem
      rw [ite_eq_left (List.any_eq_true.mpr ⟨j, List.mem_range.mpr hj, htest⟩)] at this
      cases this
    · exact ⟨fp', rfl⟩
  obtain ⟨r, hr, hsome⟩ := List.exists_of_findSome?_eq_some hfirst
  split at hsome
  · rename_i hany
    obtain rfl := Option.some.inj hsome
    obtain ⟨j', -, htest'⟩ := List.any_eq_true.mp hany
    simp only [enteredTestK, Bool.and_eq_true] at htest'
    obtain ⟨⟨⟨⟨hpc, hname'⟩, hpre'⟩, hw1'⟩, hw2'⟩ := htest'
    have hpc : r.pc = addressOfIndex (glob.sig j').entry := of_decide_eq_true hpc
    have hname' : (glob.sig j').name = f := of_decide_eq_true hname'
    have hw1' : frameWords L r.fp 2 (glob.sig j').nargs = args := of_decide_eq_true hw1'
    have hw2' : frameWords L r.fp (2 + (glob.sig j').nargs) (glob.sig j').nret = rets :=
      of_decide_eq_true hw2'
    have hgood : glob.good j' = true := by
      simp only [preTestK, Bool.and_eq_true] at hpre'
      exact hpre'.1.1.1
    have hj' : 2 ≤ j' ∧ j' < nFns := by simpa [glob, good] using hgood
    have hj2 : 2 ≤ j := by
      have := hpre.1
      simp only [glob, good, Bool.and_eq_true, Nat.ble_eq] at this
      exact this.1
    obtain rfl : j' = j := End.sig_name_inj (by omega) hj'.2 (by omega) hj (hname'.trans hname.symm)
    have hpre'' := (preTestK_iff hjt (semHolds_of_argsK (End.sigSem_args hj)
      (hw1.trans hw1'.symm) hpre.2.2.2.2.2)).mp hpre'
    obtain ⟨n', hn'⟩ := Guest.Located.run_of_mem_statesIn hS hr
    have hreg : r = ⟨addressOfIndex (glob.sig j').entry, r.fp⟩ := regs_ext hpc rfl
    rw [hreg] at hn'
    obtain ⟨-, -, -, -, ⟨⟨fn', hfind', hp', hb'⟩, -, -⟩, -⟩ :=
      End.globSpec hb2 h16 h32 j' r.fp (T - n') hpre''
        ⟨Guest.Located.safe_of_halts hT hn', ⟨n', hn'⟩⟩
    rw [hname'] at hfind' hp' hb'
    rw [hw1'] at hp'
    rw [hw2'] at hb'
    refine ⟨fn', hfind', ?_, ?_⟩
    · simp only [frameVWithK, hfirst]
      exact hp'
    · simp only [frameVWithK, hfirst]
      exact hb'
  · cases hsome

end
end LeanVM.SaltedGuest.Located
