/-
  LeanVM.SaltedGuest.Bounds.V.Stmt

  Deployed decoder bounds with their value hypotheses for indices below `2^64`: `Cost/Bounds/Guest/Stmt.lean`.
-/

module

public import LeanVM.Cost.Bounds.Guest.Stmt
public import LeanVM.SaltedGuest.Bounds.V.Readers

/-!
Deployed decoder bounds with their value hypotheses for indices below `2^64`: `Cost/Bounds/Guest/Stmt.lean`.

Each lemma is the deployed one of the name without `K`, stated with its hypotheses on a valuation or frame closure `∀ v, v.idx < 2^64 → …`: the salted frame cells are read by the value's index (`cellAtK`), whose price is the index's limbs.
-/

namespace LeanVM.SaltedGuest.Bounds

open LeanVM.Cost.Bounds.Guest LeanVM.Cost LeanVM.Cost.Bounds LeanVM.Cost.Library LeanVM.Parameters
open LeanVM.Guest.Core LeanVM.Guest.B1 LeanVM.Guest.B1.Main

public section

variable (P : MachineProgram) {G : ℕ}

section Readers

variable {rd : Reader} {rdV : MachineValue}
  (hrd : ∀ a : K, RunsApp P rdV [encodeValue a] (encodeValue (rd a)))
  {R : ℕ} (hR : ∀ a : K, appCost P rdV [encodeValue a] ≤ R)

include hrd hR

end Readers

section Val

variable {σ : Val} {σV : MachineValue}
  (hσ : ∀ v : V, RunsApp P σV [encodeValue v] (encodeValue (σ v)))
  {S : ℕ} (hS : ∀ v : V, v.idx < 2 ^ 64 → appCost P σV [encodeValue v] ≤ S)
include hσ hS

/-- **The seed** (`decSeedC`): `2·S + 45` at most. -/
theorem decSeed_costK (hP : Includes P Decoder.decSeedC.costDeps) :
    machineCost P Decoder.decSeedC.costIdx [σV] ≤ 2 * S + 45 := by
  rw [Decoder.decSeedC.costEq P hP σ σV hσ, digestOfCells_cost P (by includes)]
  have := hS (.n 26) (by idx_lt)
  have := hS (.n 27) (by idx_lt)
  omega

section Reader

variable {rd : Reader} {rdV : MachineValue}
  (hrd : ∀ a : K, RunsApp P rdV [encodeValue a] (encodeValue (rd a)))
  {R : ℕ} (hR : ∀ a : K, appCost P rdV [encodeValue a] ≤ R)
include hrd hR

/-- **The statement** (`decStmtC`), the logarithm's tables `D` given: the counts (three
logarithms, the leanXMSS and leanSPHINCS counts at most `X`) and `decStmtAtC`: at most
`decStmtPrice G R S X = 8·R·X + 24734·X + 3·G + 7·S + …`. -/
theorem decStmt_costK (D : LeanVM.Extraction.Fast.DiscreteLogTables)
    (hP : Includes P Decoder.decStmtC.costDeps) (hG : GLogBound P D G) (X : ℕ)
    (hX0 : Decoder.gLogD D (σ (.n 0)) ≤ X) (hX3 : Decoder.gLogD D (σ (.n 3)) ≤ X) :
    machineCost P Decoder.decStmtC.costIdx [encodeValue D, σV, rdV] ≤ decStmtPrice G R S X := by
  rw [Decoder.decStmtC.costEq P hP D σ σV hσ rd rdV hrd]
  have := hG (σ (.n 0)); have := hG (σ (.n 3)); have := hG (σ (.n 406))
  have n0 := gLogD_lt D (σ (.n 0))
  have n3 := gLogD_lt D (σ (.n 3))
  have n387 := gLogD_lt D (σ (.n 406))
  have h := decStmtAt_cost P hrd hR (by includes) (σ (.n 31)) (σ (.n 34)) (σ (.n 364)) (σ (.n 417))
    (Decoder.gLogD D (σ (.n 0))) (Decoder.gLogD D (σ (.n 3))) (Decoder.gLogD D (σ (.n 406)))
    (by omega) (by omega) (by omega)
  have : decStmtAtPrice R (Decoder.gLogD D (σ (.n 0))) (Decoder.gLogD D (σ (.n 3))) ≤
      decStmtAtPrice R X X := by
    unfold decStmtAtPrice
    have := Nat.mul_le_mul_left (4 * R + 12367) hX0
    have := Nat.mul_le_mul_left (4 * R + 12367) hX3
    omega
  cost_facts [hS]
  unfold decStmtPrice
  omega

/-- The sumcheck's rounds the batching hints (`aggRoundsC`): at most `46·S + 46·R + 138040`. -/
theorem aggRounds_costK (hP : Includes P Decoder.aggRoundsC.costDeps) :
    machineCost P Decoder.aggRoundsC.costIdx [rdV, σV] ≤ 46 * S + 46 * R + 138040 := by
  rw [Decoder.aggRoundsC.costEq P hP rd rdV hrd σ σV hσ]
  have m := rangeMap_le P (by includes) (by includes) _
    (.closure Decoder.aggRoundsC.lam0.costIdx [rdV, σV])
    (fun k ↦ RunsApp.of_spec (Decoder.aggRoundsC.lam0.costSpec P (by includes) rd rdV hrd σ σV hσ k))
    (2 * S + 2 * R + 5973) 23 23 le_rfl (by norm_num) (fun k hk ↦ by
      rw [appCost_fn, List.cons_append, List.cons_append, List.nil_append,
        Decoder.aggRoundsC.lam0.costEq P (by includes) rd rdV hrd σ σV hσ, List.length_cons,
        List.length_cons, List.length_nil]
      have := memAt_cost P hrd hR (by includes) (σ (.n 5)) (2 * k) (by omega)
      have := memAt_cost P hrd hR (by includes) (σ (.n 5)) (2 * k + 1) (by omega)
      have := hS (.n 5) (by idx_lt)
      limbs_one
      omega)
  omega

/-- **The batching's hints** (`aggHintsC`): at most `47·S + 46·R + 138055`. -/
theorem aggHints_costK (hP : Includes P Decoder.aggHintsC.costDeps) :
    machineCost P Decoder.aggHintsC.costIdx [rdV, σV] ≤ 47 * S + 46 * R + 138055 := by
  rw [Decoder.aggHintsC.costEq P hP rd rdV hrd σ σV hσ]
  have := aggRounds_costK P hσ hS hrd hR (by includes)
  have := hS (.n 6) (by idx_lt)
  omega

end Reader

end Val

end

end LeanVM.SaltedGuest.Bounds
