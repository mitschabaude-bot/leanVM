/-
  LeanVM.SaltedGuest.B1.Main.CountK

  The node counts the salted `main` hashes: each child's off its cell of `child_count`, the node's
  one more than their sum.
-/

module

public import LeanVM.Guest.B1.Main.Interface
public import LeanVM.Guest.B1.Main.Basic
public import LeanVM.Guest.B1.Digest.Steps
public import LeanVM.Guest.Value.Bits
public import LeanVM.Protocol.Extraction.Fast.DiscreteLog
public import LeanVM.Salted.Hash

/-!
# The node counts

The salted `main` (at the deployed numbering, `MainFactsK`) holds child `c`'s node count `n` as the
cell `g^n` at `child_count · g^c` (`.n 1000`), and hashes the node's count's cell, the running
count `count_run · g^(n_children)` (`.n 1001`) loaded into `.n 1002`, into its statement. Read off
the memory and `main`'s valuation:

* `cellLog x`: the exponent below `2^64 - 1` of the low limb of `x`
  (`Extraction.Fast.discreteLog`), `0` if it has none; at `g^n`, `n < 2^64 - 1`, it is `n`
  (`cellLog_gen`);
* `kidCount rd σ c`: the logarithm of `child_count[c]`; `childCountsOf rd σ`: the children's
  counts, in their order; `nodeCountOf σ`: the logarithm of the node's count's cell.

`nodeCountBytes_gen`: the bytes a count's cell `g^n` hashes are `nodeCountBytes n`.
-/

namespace LeanVM.SaltedGuest.B1.Main

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Guest.Value.Keccak LeanVM.Guest.B1 LeanVM.Guest.B1.Digest LeanVM.Guest.B1.Main
open LeanVM.Protocol.Verifier

@[expose] public section

/-- A logarithm by search is below `2^34`. -/
theorem gLog_lt (x : E) : gLog x < 2 ^ 34 := by
  unfold gLog
  rcases indexSearch 34 (x.limb 0) with _ | i
  · simp
  · simp

/-- **A count's cell's logarithm**: the exponent below `2^64 - 1` of its low limb
(`Extraction.Fast.discreteLog`), `0` if it has none. -/
def cellLog (x : E) : ℕ := (Extraction.Fast.discreteLog (x.limb 0)).getD 0

/-- **Child `c`'s node count**: the logarithm of the cell `child_count[c]` (`.n 1000` at the
deployed numbering). -/
noncomputable def kidCount (rd : Reader) (σ : Val) (c : ℕ) : ℕ := cellLog (cellAt rd (σ (.n 1000)) c)

/-- **The children's node counts**, in the children's order. -/
noncomputable def childCountsOf (rd : Reader) (σ : Val) : List ℕ := (List.range (nKids σ)).map (kidCount rd σ)

/-- **The node's count**: the logarithm of `main`'s cell `count_run[n_children]` (`.n 1002`), which
the statement hashes. -/
def nodeCountOf (σ : Val) : ℕ := cellLog (σ (.n 1002))

/-- At `g^n`, `n < 2^64 - 1`, the logarithm is `n`. -/
theorem cellLog_gen {n : ℕ} (hn : n < 2 ^ 64 - 1) : cellLog (gen ^ n) = n := by
  have e : (gen ^ n).limb 0 = g ^ n := by rw [gen_pow_eq_ofK]; simp
  unfold cellLog
  rw [e, (Extraction.Fast.discreteLog_eq_some_iff (n := n)).mpr ⟨rfl, hn⟩]
  rfl

/-- A logarithm is below `2^64`. -/
theorem cellLog_lt (x : E) : cellLog x < 2 ^ 64 := by
  unfold cellLog
  cases h : Extraction.Fast.discreteLog (x.limb 0) with
  | none => simp
  | some n =>
    have := (Extraction.Fast.discreteLog_eq_some_iff.mp h).2
    simp only [Option.getD_some]
    omega

/-- At a cell `g^n`, `n < 2^64 - 1`, a child's count is `n`. -/
theorem kidCount_of_load {rd : Reader} {σ : Val} {c n : ℕ} (hn : n < 2 ^ 64 - 1)
    (h : LoadHolds rd (σ (.n 1000)) c (gen ^ n)) : kidCount rd σ c = n := by
  unfold kidCount
  rw [cellAt_eq_memAt, memAt_of_load h, cellLog_gen hn]

/-- A child's count is below `2^64`. -/
theorem kidCount_lt (rd : Reader) (σ : Val) (c : ℕ) : kidCount rd σ c < 2 ^ 64 := cellLog_lt _

/-- The node's count is below `2^64`. -/
theorem nodeCountOf_lt (σ : Val) : nodeCountOf σ < 2 ^ 64 := cellLog_lt _

/-- A sum of numbers each at most `B` is at most their count times `B`. -/
theorem sum_le_length_mul : ∀ {l : List ℕ} {B : ℕ}, (∀ x ∈ l, x ≤ B) → l.sum ≤ l.length * B
  | [], _, _ => by simp
  | x :: l, B, h => by
    have := sum_le_length_mul (l := l) (B := B) fun y hy ↦ h y (List.mem_cons_of_mem _ hy)
    have hx := h x List.mem_cons_self
    simp only [List.sum_cons, List.length_cons, Nat.succ_mul]
    omega

/-- **The bytes of a count's cell**: the cell `g^n` hashes as `nodeCountBytes n`. -/
theorem nodeCountBytes_gen (n : ℕ) : cellsBytes [gen ^ n] = Recursion.Salted.nodeCountBytes n := by
  rw [gen_pow_eq_ofK]
  simp [cellsBytes, cellBytes, Recursion.Salted.nodeCountBytes]

end
end LeanVM.SaltedGuest.B1.Main
