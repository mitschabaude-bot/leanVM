/-
  LeanVM.SaltedGuest.Bounds.V.Raw

  Deployed decoder bounds with their value hypotheses for indices below `2^64`: `Cost/Bounds/Guest/Raw.lean`.
-/

module

public import LeanVM.Cost.Bounds.Guest.Raw
public import LeanVM.SaltedGuest.Bounds.V.Kids

/-!
Deployed decoder bounds with their value hypotheses for indices below `2^64`: `Cost/Bounds/Guest/Raw.lean`.

Each lemma is the deployed one of the name without `K`, stated with its hypotheses on a valuation or frame closure `∀ v, v.idx < 2^64 → …`: the salted frame cells are read by the value's index (`cellAtK`), whose price is the index's limbs.
-/

namespace LeanVM.SaltedGuest.Bounds

open LeanVM.Cost.Bounds.Guest LeanVM.Cost LeanVM.Cost.Bounds LeanVM.Cost.Library LeanVM.Parameters
open LeanVM.Extraction.Fast LeanVM.Guest.Fast LeanVM.Cost.Decoder
open LeanVM.Guest.Core LeanVM.Guest.B1 LeanVM.Guest.B1.Main

public section

variable (P : MachineProgram) {G : ℕ}

section Reader

variable {rd : Reader} {rdV : MachineValue}
  (hrd : ∀ a : K, RunsApp P rdV [encodeValue a] (encodeValue (rd a)))
  {R : ℕ} (hR : ∀ a : K, appCost P rdV [encodeValue a] ≤ R)
include hrd hR

section Xmss

variable {wX : List E → LeanXmss.Signature} {wXV : MachineValue}
  (hwX : ∀ a : List E, RunsApp P wXV [encodeValue a] (encodeValue (wX a)))
  {WX : ℕ} (hWX : ∀ a : List E, a.length ≤ 56 → appCost P wXV [encodeValue a] ≤ WX)
include hwX hWX

end Xmss

section Sphincs

variable {wS : E → Sphincs.Signature} {wSV : MachineValue}
  (hwS : ∀ a : E, RunsApp P wSV [encodeValue a] (encodeValue (wS a)))
  {WS : ℕ} (hWS : ∀ a : E, appCost P wSV [encodeValue a] ≤ WS)
include hwS hWS

end Sphincs

section Val

variable {σ : Val} {σV : MachineValue}
  (hσ : ∀ v : V, RunsApp P σV [encodeValue v] (encodeValue (σ v)))
  {S : ℕ} (hS : ∀ v : V, v.idx < 2 ^ 64 → appCost P σV [encodeValue v] ≤ S)
include hσ hS

section Proof

variable {wV : List E → LeanVM.Protocol.Compile.Proof} {wVV : MachineValue}
  (hwV : ∀ a : List E, RunsApp P wVV [encodeValue a] (encodeValue (wV a)))
include hwV

/-- **The children** (`kidsTC`), off good tables of at most `N ≤ 2^34` marks, `n ≤ K ≤ 2^34`, each
child's proof at most `W` (`wV` at its arguments, `subArgsK`): at most
`kidsTPrice G R S W N K = K·(decKidPrice G R S W N + 48) + 31`. -/
theorem kidsT_costK (D : DiscreteLogTables) (hP : Includes P kidsTC.costDeps)
    (hG : GLogBound P D G) (w380 p53 p56 : E) (tx ts : Array ℕ × Array ℕ) (htx : TableGood tx)
    (hts : TableGood ts) (N : ℕ) (hN : N ≤ 2 ^ 34) (htxN : tx.1.size ≤ N) (htsN : ts.1.size ≤ N)
    (K : ℕ) (hK : K ≤ 2 ^ 34) (n : ℕ) (hn : n ≤ K) {W : ℕ}
    (hW : ∀ c < n, appCost P wVV [encodeValue (subArgsK rd σ c)] ≤ W) :
    machineCost P kidsTC.costIdx [encodeValue D, rdV, σV, wVV, encodeValue w380, encodeValue p53,
      encodeValue p56, encodeValue tx, encodeValue ts, encodeValue n] ≤ kidsTPrice G R S W N K := by
  rw [kidsTC.costEq P hP D rd rdV hrd σ σV hσ wV wVV hwV]
  have h1 := rangeMap_le P (by includes) (by includes) (decKidT D rd σ wV w380 p53 p56 tx ts)
    (.closure kidsTC.lam0.costIdx [encodeValue D, rdV, σV, wVV, encodeValue w380, encodeValue p53,
      encodeValue p56, encodeValue tx, encodeValue ts])
    (fun c ↦ RunsApp.of_spec (kidsTC.lam0.costSpec P (by includes) D rd rdV hrd σ σV hσ wV wVV hwV
      w380 p53 p56 tx ts c))
    (decKidPrice G R S W N + 20) n K hn (by omega) (fun c hc ↦ by
      rw [appCost_fn, List.cons_append, List.cons_append, List.cons_append, List.cons_append,
        List.cons_append, List.cons_append, List.cons_append, List.cons_append, List.cons_append,
        List.nil_append, kidsTC.lam0.costEq P (by includes) D rd rdV hrd σ σV hσ wV wVV hwV, List.length_cons, List.length_cons, List.length_cons, List.length_cons, List.length_cons, List.length_cons, List.length_cons, List.length_cons, List.length_cons, List.length_nil]
      have := decKid_costK P hrd hR hσ hS hwV D (by includes) hG w380 p53 p56 tx ts htx hts N hN
        htxN htsN c (by omega) (hW c hc)
      omega)
  unfold kidsTPrice
  have : (decKidPrice G R S W N + 20 + 28) * K = (decKidPrice G R S W N + 48) * K := by ring
  omega

end Proof

end Val

end Reader

end

end LeanVM.SaltedGuest.Bounds
