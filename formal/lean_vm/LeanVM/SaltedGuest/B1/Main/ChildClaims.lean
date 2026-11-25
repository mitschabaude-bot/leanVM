/-
  LeanVM.SaltedGuest.B1.Main.ChildClaims

  Every child of a salted decoding has a statement of at most `2^35 - 2` signature claims.
-/

module

public import LeanVM.SaltedGuest.B1.Main.SoundVK

/-!
# The children's claims of a salted decoding

A decoded child's statement (`kidStmt`) lists, of the coverage table's leanXMSS region, at most the
region's size of claims, and of its leanSPHINCS region at most that region's size (`kidSlots`
keeps slots of the region, or one per mark it counts there). The regions' sizes are discrete
logarithms (`gLog`), below `2^34`. So every child of `decK piOf σ rd V` has at most
`2·(2^34 - 1) = 2^35 - 2` signature claims (`decK_child_claims`), on any valuation, memory and
frame map.
-/

namespace LeanVM.SaltedGuest.B1.Main

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.B1 LeanVM.Guest.B1.Main
open LeanVM.Node

@[expose] public section

theorem segCount_le (rd : Reader) (σ : Val) (lo len a b : ℕ) : segCount rd σ lo len a b ≤ len := by
  unfold segCount
  exact (List.length_filter_le _ _).trans (by simp)

theorem kidSlots_length_le (rd : Reader) (σ : Val) (lo len a b : ℕ) :
    (kidSlots rd σ lo len a b).length ≤ len := by
  unfold kidSlots
  split
  · exact (List.length_filter_le _ _).trans (by simp)
  · simpa using segCount_le rd σ lo len a b

/-- **A decoded child's statement has at most `2^35 - 2` signature claims.** -/
theorem kidStmt_claims (rd : Reader) (σ : Val) (c : ℕ) :
    (kidStmt rd σ c).claims.xmss.length + (kidStmt rd σ c).claims.sphincs.length ≤ 2 ^ 35 - 2 := by
  have h1 := kidSlots_length_le rd σ 0 (lxSlots σ) (countOf rd σ c) (countOf rd σ (c + 1))
  have h2 := kidSlots_length_le rd σ (lxSlots σ) (lsSlots σ)
    (countOf rd σ c + segCount rd σ 0 (lxSlots σ) (countOf rd σ c) (countOf rd σ (c + 1)))
    (countOf rd σ (c + 1))
  have h3 : lxSlots σ < 2 ^ 34 := gLog_lt _
  have h4 : lsSlots σ < 2 ^ 34 := gLog_lt _
  simp only [kidStmt, List.length_map]
  omega

/-- **Every child of a salted decoding has at most `2^35 - 2` signature claims**, on any
valuation, memory and frame map. -/
theorem decK_child_claims (piOf : Reader → Val → End.FrameMap → LeanVM.Protocol.Compile.Proof)
    (σ : Val) (rd : Reader) (V : End.FrameMap) :
    ∀ child ∈ (decK piOf σ rd V).witness.children,
      child.statement.claims.xmss.length + child.statement.claims.sphincs.length ≤ 2 ^ 35 - 2 := by
  intro child hc
  simp only [decK, decWitK, decWit, List.mem_map, List.mem_range] at hc
  obtain ⟨c, -, rfl⟩ := hc
  exact kidStmt_claims rd (mainVal σ) c

end
end LeanVM.SaltedGuest.B1.Main
