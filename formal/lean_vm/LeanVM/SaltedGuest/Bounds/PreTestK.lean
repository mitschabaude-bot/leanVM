/-
  LeanVM.SaltedGuest.Bounds.PreTestK

  The salted decoder's precondition test: its table's shape and the test's price.
-/

module

public import LeanVM.SaltedGuest.Decoder.Top
public import LeanVM.Cost.Bounds.Decoder.PreTest

/-!
# The salted precondition test

The salted decoder tests a state's precondition by `Located.preTestAtK`, the deployed
`preTestAt` (`Cost/Bounds/Decoder/PreTest.lean`) at the salted guest's `1539` functions, on the
salted table `preTableK` (`Decoder/PreTable.lean`):

* `preTableK_shape`: every entry of the salted table has the deployed shape (`fnPreShape`: at most
  one check of each kind, at most `99` bounds and memory cells, exponents below `2^7`, logarithms'
  bounds at most `34`), by evaluation;
* **`preTestAtK_cost`**: on a table of that shape, the test is at most `269R + 99B + 24834`, the
  deployed price (`preTestAt_cost_deployed`).
-/

namespace LeanVM.SaltedGuest.Bounds

open LeanVM.Cost LeanVM.Cost.Decoder LeanVM.Cost.Library LeanVM.Cost.Bounds LeanVM.Parameters
open LeanVM.Semantics LeanVM.Extraction LeanVM.Extraction.Fast LeanVM.Guest.Core LeanVM.Guest.Fast
open LeanVM.SaltedGuest.Decoder

@[expose] public section

/-- **The salted table's shape** (`fnPreShape`), evaluated by the kernel. -/
theorem preTableK_shape : tableShape preTableK = true := by
  decide +kernel

variable (P : MachineProgram)

/-- **The salted precondition test** (`preTestAtKC`), on a table of the deployed shape: at most
`269R + 99B + 24834`. -/
theorem preTestAtK_cost (hP : Includes P preTestAtKC.costDeps) (D : DiscreteLogTables)
    (rd : Reader) (rdVal : MachineValue)
    (hrd : ∀ a : K, RunsApp P rdVal [encodeValue a] (encodeValue (rd a)))
    (R : ℕ) (hR : ∀ a : K, appCost P rdVal [encodeValue a] ≤ R)
    (B : ℕ) (hB : ∀ (w : E) (n : ℕ), n ≤ 34 →
      machineCost P powBelowC.costIdx [encodeValue D, encodeValue w, encodeValue n] ≤ B)
    (T : Array (Option FnPre)) (hT : tableShape T = true) (Pw : Array E) (j : ℕ)
    (hj : j < 2 ^ 64) (fp : K) :
    machineCost P preTestAtKC.costIdx [encodeValue D, encodeValue T, encodeValue Pw, rdVal,
      encodeValue j, encodeValue fp] ≤ 269 * R + 99 * B + 24834 := by
  rw [preTestAtKC.costEq P hP D T Pw rd rdVal hrd, limbs_of_lt hj,
    limbs_of_lt (by unfold LeanVM.SaltedGuest.nFns; norm_num : LeanVM.SaltedGuest.nFns < 2 ^ 64)]
  have := fnPreTest_cost P D rd rdVal hrd R hR B hB (by includes) Pw (W := 7) le_rfl fp
    (T.getD j none) (fun s hs ↦ fnPreWithin_of_shape (fnPreShape_of_getD hT hs))
  simp only [max_self]
  cases hg : T.getD j none with
  | none => rw [hg] at this; simp only [fnPrePrice] at this; split_ifs <;> omega
  | some s =>
    rw [hg] at this
    have := fnPrePrice_of_shape (fnPreShape_of_getD hT hg) R B
    split_ifs <;> omega

end

end LeanVM.SaltedGuest.Bounds
