/-
  LeanVM.SaltedGuest.Bounds.V.Kids

  Deployed decoder bounds with their value hypotheses for indices below `2^64`: `Cost/Bounds/Guest/Kids.lean`.
-/

module

public import LeanVM.Cost.Bounds.Guest.Kids
public import LeanVM.SaltedGuest.Bounds.V.Stmt

/-!
Deployed decoder bounds with their value hypotheses for indices below `2^64`: `Cost/Bounds/Guest/Kids.lean`.

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

section Val

variable {σ : Val} {σV : MachineValue}
  (hσ : ∀ v : V, RunsApp P σV [encodeValue v] (encodeValue (σ v)))
  {S : ℕ} (hS : ∀ v : V, v.idx < 2 ^ 64 → appCost P σV [encodeValue v] ≤ S)
include hσ hS

/-- **A child's statement, its lists' slots given** (`kidStmtAtC`), `c < 2^34`, at most `N` slots
a list, each below `2^34`: a claim a slot (`xmssSlotClaim_cost`), the DA digest and the deferred
claim: at most `kidStmtAtPrice R S N = (8·R + 30050)·N + …`. -/
theorem kidStmtAt_costK (hP : Includes P kidStmtAtC.costDeps) (p52 p55 : E) (c : ℕ)
    (sx ss : List ℕ) (hc : c < 2 ^ 34) (N : ℕ) (hsx : sx.length ≤ N) (hss : ss.length ≤ N)
    (hsx' : ∀ s ∈ sx, s < 2 ^ 34) (hss' : ∀ s ∈ ss, s < 2 ^ 34) :
    machineCost P kidStmtAtC.costIdx [rdV, σV, encodeValue p52, encodeValue p55, encodeValue c,
      encodeValue sx, encodeValue ss] ≤ kidStmtAtPrice R S N := by
  rw [kidStmtAtC.costEq P hP rd rdV hrd σ σV hσ]
  have h1 := map_cost P (by includes) (xmssSlotClaim rd p52)
    (.closure kidStmtAtC.lam0.costIdx [rdV, encodeValue p52])
    (fun s ↦ RunsApp.of_spec (kidStmtAtC.lam0.costSpec P (by includes) rd rdV hrd p52 s))
    (4 * R + 15012) sx (fun s hs ↦ by
      rw [appCost_fn, List.cons_append, List.cons_append, List.nil_append,
        kidStmtAtC.lam0.costEq P (by includes) rd rdV hrd, List.length_cons, List.length_cons,
        List.length_nil]
      have := xmssSlotClaim_cost P hrd hR (by includes) p52 s (hsx' s hs)
      omega)
  have h2 := map_cost P (by includes) (sphincsSlotClaim rd p55)
    (.closure kidStmtAtC.lam1.costIdx [rdV, encodeValue p55])
    (fun s ↦ RunsApp.of_spec (kidStmtAtC.lam1.costSpec P (by includes) rd rdV hrd p55 s))
    (4 * R + 15012) ss (fun s hs ↦ by
      rw [appCost_fn, List.cons_append, List.cons_append, List.nil_append,
        kidStmtAtC.lam1.costEq P (by includes) rd rdV hrd, List.length_cons, List.length_cons,
        List.length_nil]
      have := sphincsSlotClaim_cost P hrd hR (by includes) p55 s (hss' s hs)
      omega)
  have m1 := Nat.mul_le_mul_left (4 * R + 15012 + 13) hsx
  have m2 := Nat.mul_le_mul_left (4 * R + 15012 + 13) hss
  have h3 := daDigestAt_costK P hrd hR hσ hS (by includes) c (by omega)
  have h4 := hS (.n 396) (by idx_lt)
  have h5 := powSqK_cost_lt P (by includes) Parameters.g (24 * c) 39 (by norm_num) (by norm_num)
    (by omega)
  have h6 := readCellsK_cost P hrd hR (by includes) ((σ (.n 396)).limb 0 * Parameters.g ^ (24 * c))
    24 (by norm_num)
  have h7 := deferOfCells_cost P (by includes)
    (readCellsK rd ((σ (.n 396)).limb 0 * Parameters.g ^ (24 * c)) 24)
  limbs_one
  unfold kidStmtAtPrice
  have : (4 * R + 15012 + 13) * N + (4 * R + 15012 + 13) * N = (8 * R + 30050) * N := by ring
  omega

/-- **A child's statement, its segment `[a, b)` given** (`kidStmtSegC`), the tables of at most `N`
marks: its lists' slots off the tables (`kidSlotsIn_cost`, a count between), then
`kidStmtAt_costK`. -/
theorem kidStmtSeg_costK (hP : Includes P kidStmtSegC.costDeps) (p52 p55 : E)
    (tx ts : Array ℕ × Array ℕ) (htx : TableGood tx) (hts : TableGood ts) (c a b : ℕ)
    (hc : c < 2 ^ 34) (ha : a < 2 ^ 34) (hb : b < 2 ^ 34) (N : ℕ) (hN : N ≤ 2 ^ 34)
    (htxN : tx.1.size ≤ N) (htsN : ts.1.size ≤ N) :
    machineCost P kidStmtSegC.costIdx [rdV, σV, encodeValue p52, encodeValue p55, encodeValue tx,
      encodeValue ts, encodeValue c, encodeValue a, encodeValue b] ≤
      kidStmtAtPrice R S N + 2 * kidSlotsInPrice N + 1890 := by
  rw [kidStmtSegC.costEq P hP rd rdV hrd σ σV hσ]
  have h0 := countIn_le tx.1 a b
  have h1 := countIn_cost P (by includes) tx.1 (lt64_of_good htx) htx.2.1 a b (by omega) (by omega)
  have h2 := kidSlotsIn_cost P (by includes) htx a b (by omega) (by omega) N htxN
  have h3 := kidSlotsIn_cost P (by includes) hts (a + countIn tx.1 a b) b (by omega) (by omega)
    N htsN
  have h4 := kidStmtAt_costK P hrd hR hσ hS (by includes) p52 p55 c
    (kidSlotsIn tx.1 tx.2 a b) (kidSlotsIn ts.1 ts.2 (a + countIn tx.1 a b) b) hc N
    ((kidSlotsIn_length_le tx.1 tx.2 a b).trans htxN)
    ((kidSlotsIn_length_le ts.1 ts.2 _ b).trans htsN)
    (kidSlotsIn_lt htx a b) (kidSlotsIn_lt hts _ b)
  limbs_one
  omega

/-- **Child `c`'s statement** (`kidStmtC`), off good tables of at most `N` marks, `c < 2^34`: its
segment's ends (two logarithms), then `kidStmtSeg_costK`: at most `kidStmtPrice G R S N`. -/
theorem kidStmt_costK (D : DiscreteLogTables) (hP : Includes P kidStmtC.costDeps)
    (hG : GLogBound P D G) (w380 p53 p56 : E) (tx ts : Array ℕ × Array ℕ) (htx : TableGood tx)
    (hts : TableGood ts) (N : ℕ) (hN : N ≤ 2 ^ 34) (htxN : tx.1.size ≤ N) (htsN : ts.1.size ≤ N)
    (c : ℕ) (hc : c < 2 ^ 34) :
    machineCost P kidStmtC.costIdx [encodeValue D, rdV, σV, encodeValue w380, encodeValue p53,
      encodeValue p56, encodeValue tx, encodeValue ts, encodeValue c] ≤ kidStmtPrice G R S N := by
  rw [kidStmtC.costEq P hP D rd rdV hrd σ σV hσ]
  have h1 := countAtW_cost P hrd hR D (by includes) hG w380 c (by omega)
  have h2 := countAtW_cost P hrd hR D (by includes) hG w380 (c + 1) (by omega)
  have h3 := kidStmtSeg_costK P hrd hR hσ hS (by includes) p53 p56 tx ts htx hts c
    (countAtW D rd w380 c) (countAtW D rd w380 (c + 1)) hc (gLogD_lt D _) (gLogD_lt D _) N hN htxN
    htsN
  limbs_one
  unfold kidStmtPrice
  omega

/-- **Child `c`'s `verify_sub` words** (`subArgsC`), `c < 2^34`: at most `7·S + 2·R + 8989`. -/
theorem subArgs_costK (hP : Includes P subArgsC.costDeps) (c : ℕ) (hc : c < 2 ^ 34) :
    machineCost P subArgsC.costIdx [rdV, σV, encodeValue c] ≤ 7 * S + 2 * R + 8989 := by
  rw [subArgsC.costEq P hP rd rdV hrd σ σV hσ]
  have h1 := cellAt_cost P hrd hR (by includes) (σ (.n 384)) (2 * c) (by omega)
  have h2 := cellAt_cost P hrd hR (by includes) (σ (.n 384)) (2 * c + 1) (by omega)
  have h3 := powSqK_cost_lt P (by includes) Parameters.g (24 * c) 39 (by norm_num) (by norm_num) (by omega)
  have h4 := mulK_cost P (by includes) (σ (.n 390)) (Parameters.g ^ (24 * c))
  have := hS (.n 384) (by idx_lt); have := hS (.n 26) (by idx_lt); have := hS (.n 27) (by idx_lt); have := hS (.n 28) (by idx_lt)
  have := hS (.n 390) (by idx_lt)
  limbs_one
  omega

section Proof

variable {wV : List E → LeanVM.Protocol.Compile.Proof} {wVV : MachineValue}
  (hwV : ∀ a : List E, RunsApp P wVV [encodeValue a] (encodeValue (wV a)))
include hwV

/-- **Child `c`** (`decKidC`), off good tables of at most `N` marks, `c < 2^34`: its statement, its
proof's claim (24 reads), its proof (`wV` at its `verify_sub` words, at most `W` there): at most
`decKidPrice G R S W N`. -/
theorem decKid_costK (D : DiscreteLogTables) (hP : Includes P decKidC.costDeps)
    (hG : GLogBound P D G) (w380 p53 p56 : E) (tx ts : Array ℕ × Array ℕ) (htx : TableGood tx)
    (hts : TableGood ts) (N : ℕ) (hN : N ≤ 2 ^ 34) (htxN : tx.1.size ≤ N) (htsN : ts.1.size ≤ N)
    (c : ℕ) (hc : c < 2 ^ 34) {W : ℕ} (hW : appCost P wVV [encodeValue (subArgsK rd σ c)] ≤ W) :
    machineCost P decKidC.costIdx [encodeValue D, rdV, σV, wVV, encodeValue w380, encodeValue p53,
      encodeValue p56, encodeValue tx, encodeValue ts, encodeValue c] ≤ decKidPrice G R S W N := by
  rw [decKidC.costEq P hP D rd rdV hrd σ σV hσ wV wVV hwV]
  have h1 := kidStmt_costK P hrd hR hσ hS D (by includes) hG w380 p53 p56 tx ts htx hts N hN htxN htsN c
    hc
  have h2 := powSqK_cost_lt P (by includes) Parameters.g (24 * c) 39 (by norm_num) (by norm_num) (by omega)
  have h3 := readCellsK_cost P hrd hR (by includes) ((σ (.n 390)).limb 0 * Parameters.g ^ (24 * c)) 24
    (by norm_num)
  have h4 := fixedOfCells_cost P (by includes)
    (readCellsK rd ((σ (.n 390)).limb 0 * Parameters.g ^ (24 * c)) 24)
  have h5 := subArgs_costK P hrd hR hσ hS (by includes) c hc
  have := hS (.n 390) (by idx_lt)
  limbs_one
  unfold decKidPrice
  omega

end Proof

end Val

end Reader

end

end LeanVM.SaltedGuest.Bounds
