/-
  LeanVM.SaltedGuest.Bounds.V.Readers

  Deployed decoder bounds with their value hypotheses for indices below `2^64`: `Cost/Bounds/Guest/Readers.lean`.
-/

module

public import LeanVM.Cost.Bounds.Guest.Readers

/-!
Deployed decoder bounds with their value hypotheses for indices below `2^64`: `Cost/Bounds/Guest/Readers.lean`.

Each lemma is the deployed one of the name without `K`, stated with its hypotheses on a valuation or frame closure `∀ v, v.idx < 2^64 → …`: the salted frame cells are read by the value's index (`cellAtK`), whose price is the index's limbs.
-/

namespace LeanVM.SaltedGuest.Bounds

open LeanVM.Cost.Bounds.Guest LeanVM.Cost LeanVM.Cost.Bounds LeanVM.Cost.Library LeanVM.Parameters
open LeanVM.Guest.Core LeanVM.Guest.B1 LeanVM.Guest.B1.Main

public section

/-- `idx_lt`: a value's index below `2^64`, for the value hypotheses at literal values. -/
macro "idx_lt" : tactic => `(tactic| first | decide | omega | simp_all)

variable (P : MachineProgram)

section Reader

variable {rd : Reader} {rdV : MachineValue}
  (hrd : ∀ a : K, RunsApp P rdV [encodeValue a] (encodeValue (rd a)))
  {R : ℕ} (hR : ∀ a : K, appCost P rdV [encodeValue a] ≤ R)
include hrd hR

section Val

variable {σ : Val} {σV : MachineValue}
  (hσ : ∀ v : V, RunsApp P σV [encodeValue v] (encodeValue (σ v)))
  {S : ℕ} (hS : ∀ v : V, v.idx < 2 ^ 64 → appCost P σV [encodeValue v] ≤ S)
include hσ hS

/-- **A DA digest** (`daDigestAtC`), `2·k + 1 < 2^40`: at most `2·S + 2·R + 5995`. -/
theorem daDigestAt_costK (hP : Includes P Decoder.daDigestAtC.costDeps) (k : ℕ)
    (hk : 2 * k + 1 < 2 ^ 40) :
    machineCost P Decoder.daDigestAtC.costIdx [rdV, σV, encodeValue k] ≤ 2 * S + 2 * R + 5995 := by
  rw [Decoder.daDigestAtC.costEq P hP rd rdV hrd σ σV hσ]
  have := hS (.n 364) (by idx_lt)
  have := cellAt_cost P hrd hR (by includes) (σ (.n 364)) (2 * k) (by omega)
  have := cellAt_cost P hrd hR (by includes) (σ (.n 364)) (2 * k + 1) hk
  rw [digestOfCells_cost P (by includes)]
  limbs_one
  omega

end Val

end Reader

end

end LeanVM.SaltedGuest.Bounds
