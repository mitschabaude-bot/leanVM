/-
  LeanVM.SaltedGuest.Located.FastK

  The salted replayed frame map as the decoder computes it: the precondition from the literal
  table, the frames keyed by the callee's index.
-/

module

public import LeanVM.SaltedGuest.Located.ReplayFast
public import LeanVM.SaltedGuest.Decoder.PreTable
public import LeanVM.Guest.Fast.PreTest

/-!
# The salted replayed frame map, from the tables

* `preTestAtK D T Pw rd j fp`: the deployed `preTestAt` over the salted functions (`j < nFns`
  of the salted guest), its table `T`; **`preTestK_eq_preTable`**: the decided salted
  precondition is `preTestAtK discreteLogTables preTableK genPows`, the literal table of the
  salted preconditions (`Decoder/PreTable.lean`).
* `frameVFastNK pre states rd j`: the indexed frame map keyed by the salted function's index `j`,
  its frame read through `certOf j`; `frameVFastNK_nameIndex`: at `nameIndex f` it is
  `frameVFastK`'s map at `f`.
-/

namespace LeanVM.SaltedGuest.Located

open LeanVM.Parameters LeanVM.Semantics LeanVM.SaltedGuest LeanVM.Guest.Core LeanVM.Guest.Check
open LeanVM.Extraction LeanVM.Extraction.Fast LeanVM.Guest.Fast LeanVM.SaltedGuest.Decoder

attribute [local instance] lexOrd

@[expose] public section

/-- **Salted function `j`'s precondition at the frame `fp`**, from the table `T` of the
functions' preconditions, the logarithm's baby-step tables `D` and the powers `Pw` given (but for
the jump table, `preTestK`). -/
def preTestAtK (D : DiscreteLogTables) (T : Array (Option FnPre)) (Pw : Array E) (rd : Reader)
    (j : ℕ) (fp : K) : Bool :=
  decide (2 ≤ j) && decide (j < nFns) && fnPreTest D Pw rd fp (T.getD j none)

/-- **From the table, the test is `preTestWithK discreteLog`.** -/
theorem preTestWithK_eq_preTable :
    preTestWithK discreteLog = preTestAtK discreteLogTables preTableK genPows := by
  funext rd j fp
  unfold preTestWithK preTestAtK
  have hg : glob.good j = (decide (2 ≤ j) && decide (j < nFns)) := by
    show (Nat.ble 2 j && Nat.blt j nFns) = _
    exact Bool.eq_iff_iff.mpr (by simp [Nat.ble_eq, Nat.blt_eq])
  rw [hg]
  by_cases hj : 2 ≤ j ∧ j < nFns
  · rw [preTableK_getD hj.2, fnPreTest_fnPreOf]
    simp [hj.1, hj.2, Bool.and_assoc]
  · rcases not_and_or.mp hj with h | h <;> simp [h]

/-- **The salted precondition's test is `preTestAtK discreteLogTables preTableK genPows`.** -/
theorem preTestK_eq_preTable : preTestK = preTestAtK discreteLogTables preTableK genPows :=
  (preTestWithK_eq discreteLog_discreteLogSpec).symm.trans preTestWithK_eq_preTable

/-- **The salted replayed frame map, keyed by index**: the call of the salted function `j` looked
up in the entry table, its frame read through `certOf j`. -/
noncomputable def frameVFastNK (pre : ℕ → K → Bool) (states : List (Registers K)) (rd : Reader)
    (j : ℕ) (args rets : List E) : Val :=
  match (entryTableK pre states rd).get? (Guest.Located.callKey j args rets) with
  | some fp => fun v ↦ Guest.Located.wordWith rd fp ((certOf j).locs.getD v.idx 0)
  | none => fun _ ↦ 0

/-- **Keyed by index, the salted replayed frame map is the one keyed by name.** -/
theorem frameVFastNK_nameIndex (pre : ℕ → K → Bool) (states : List (Registers K)) (rd : Reader)
    (f : String) : frameVFastNK pre states rd (nameIndex f) = frameVFastK pre states rd f := by
  funext args rets
  unfold frameVFastNK frameVFastK
  cases (entryTableK pre states rd).get? (Guest.Located.callKey (nameIndex f) args rets) <;> rfl

end
end LeanVM.SaltedGuest.Located
