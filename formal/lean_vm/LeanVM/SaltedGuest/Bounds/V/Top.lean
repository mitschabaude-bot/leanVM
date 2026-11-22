/-
  LeanVM.SaltedGuest.Bounds.V.Top

  Deployed decoder bounds with their value hypotheses for indices below `2^64`: `Cost/Bounds/Guest/Top.lean`.
-/

module

public import LeanVM.Cost.Bounds.Guest.Top
public import LeanVM.SaltedGuest.Bounds.V.Raw

/-!
Deployed decoder bounds with their value hypotheses for indices below `2^64`: `Cost/Bounds/Guest/Top.lean`.

Each lemma is the deployed one of the name without `K`, stated with its hypotheses on a valuation or frame closure `∀ v, v.idx < 2^64 → …`: the salted frame cells are read by the value's index (`cellAtK`), whose price is the index's limbs.
-/

namespace LeanVM.SaltedGuest.Bounds

open LeanVM.Cost.Bounds.Guest LeanVM.Cost LeanVM.Cost.Bounds LeanVM.Cost.Library LeanVM.Parameters
open LeanVM.Guest.Core LeanVM.Guest.B1 LeanVM.Guest.Fast LeanVM.Extraction.Fast

public section

variable (P : MachineProgram) {G : ℕ}

section Val

variable {σ : Val} {σV : MachineValue}
  (hσ : ∀ v : V, RunsApp P σV [encodeValue v] (encodeValue (σ v)))
  {S : ℕ} (hS : ∀ v : V, v.idx < 2 ^ 64 → appCost P σV [encodeValue v] ≤ S)
include hσ hS

/-- A count read off `main`'s valuation (`nKidsC`, `lxSlotsC`, …): `S + G + 11`. -/
theorem nDirect_costK (D : DiscreteLogTables) (hP : Includes P Decoder.nDirectC.costDeps)
    (hG : GLogBound P D G) :
    machineCost P Decoder.nDirectC.costIdx [encodeValue D, σV] ≤ S + G + 11 := by
  rw [Decoder.nDirectC.costEq P hP D σ σV hσ]
  have := hG (σ (.n 7)); have := hS (.n 7) (by idx_lt); omega

theorem nKids_costK (D : DiscreteLogTables) (hP : Includes P Decoder.nKidsC.costDeps)
    (hG : GLogBound P D G) :
    machineCost P Decoder.nKidsC.costIdx [encodeValue D, σV] ≤ S + G + 11 := by
  rw [Decoder.nKidsC.costEq P hP D σ σV hσ]
  have := hG (σ (.n 6)); have := hS (.n 6) (by idx_lt); omega

theorem lxSlots_costK (D : DiscreteLogTables) (hP : Includes P Decoder.lxSlotsC.costDeps)
    (hG : GLogBound P D G) :
    machineCost P Decoder.lxSlotsC.costIdx [encodeValue D, σV] ≤ S + G + 11 := by
  rw [Decoder.lxSlotsC.costEq P hP D σ σV hσ]
  have := hG (σ (.n 22)); have := hS (.n 22) (by idx_lt); omega

theorem lsSlots_costK (D : DiscreteLogTables) (hP : Includes P Decoder.lsSlotsC.costDeps)
    (hG : GLogBound P D G) :
    machineCost P Decoder.lsSlotsC.costIdx [encodeValue D, σV] ≤ S + G + 11 := by
  rw [Decoder.lsSlotsC.costEq P hP D σ σV hσ]
  have := hG (σ (.n 23)); have := hS (.n 23) (by idx_lt); omega

theorem nRawX_costK (D : DiscreteLogTables) (hP : Includes P Decoder.nRawXC.costDeps)
    (hG : GLogBound P D G) :
    machineCost P Decoder.nRawXC.costIdx [encodeValue D, σV] ≤ S + G + 11 := by
  rw [Decoder.nRawXC.costEq P hP D σ σV hσ]
  have := hG (σ (.n 2)); have := hS (.n 2) (by idx_lt); omega

theorem nRawS_costK (D : DiscreteLogTables) (hP : Includes P Decoder.nRawSC.costDeps)
    (hG : GLogBound P D G) :
    machineCost P Decoder.nRawSC.costIdx [encodeValue D, σV] ≤ S + G + 11 := by
  rw [Decoder.nRawSC.costEq P hP D σ σV hσ]
  have := hG (σ (.n 5)); have := hS (.n 5) (by idx_lt); omega

/-- The DA claim (`dvClaimC`): `4·S + 93`. -/
theorem dvClaim_costK (hP : Includes P Decoder.dvClaimC.costDeps) :
    machineCost P Decoder.dvClaimC.costIdx [σV] ≤ 4 * S + 93 := by
  rw [Decoder.dvClaimC.costEq P hP σ σV hσ, digestOfCells_cost P (by includes),
    Decoder.scalarOfCellsC.costEq P (by includes)]
  cost_facts [hS]
  omega

/-- The words of `aggregate_claims`' call (`aggArgsC`): `5·S + 61`. -/
theorem aggArgs_costK (hP : Includes P Decoder.aggArgsC.costDeps) :
    machineCost P Decoder.aggArgsC.costIdx [σV] ≤ 5 * S + 61 := by
  rw [Decoder.aggArgsC.costEq P hP σ σV hσ]
  cost_facts [hS]
  omega

/-- **`__loop2`'s arguments after the counter** (`l2ArgsDC`): `55` reads, `55·S + 675`. -/
theorem l2ArgsD_costK (hP : Includes P Decoder.l2ArgsDC.costDeps) :
    machineCost P Decoder.l2ArgsDC.costIdx [σV] ≤ 55 * S + 675 := by
  rw [Decoder.l2ArgsDC.costEq P hP σ σV hσ]
  cost_facts [hS]
  omega

/-- **The DA claim and matrix** (`daWitnessC`), the DA witness function's price at most `WD`:
`10·S + G + WD + 181`. -/
theorem daWitness_costK (D : DiscreteLogTables) (hP : Includes P Decoder.daWitnessC.costDeps)
    (hG : GLogBound P D G) {wD : List E → List E → LeanVM.Da.MatrixWitness} {wDV : MachineValue}
    (hwD : ∀ a b : List E, RunsApp P wDV [encodeValue a, encodeValue b] (encodeValue (wD a b)))
    {WD : ℕ} (hWD : ∀ a b : List E, a.length + b.length ≤ 16 →
      appCost P wDV [encodeValue a, encodeValue b] ≤ WD) :
    machineCost P Decoder.daWitnessC.costIdx [encodeValue D, σV, wDV] ≤ 10 * S + G + WD + 181 := by
  rw [Decoder.daWitnessC.costEq P hP D σ σV hσ wD wDV hwD]
  have := nDirect_costK P hσ hS D (by includes) hG
  have := dvClaim_costK P hσ hS (by includes)
  have := hWD [σ (.n 28)] [σ (.n 369), σ (.n 370), σ (.n 371), σ (.n 372)] (by simp)
  have : Decoder.nDirectD D σ < 2 ^ 34 := gLogD_lt D _
  cost_facts [hS]
  limbs_one
  split_ifs <;> omega

end Val

section Witness

variable {rd : Reader} {rdV : MachineValue}
  (hrd : ∀ a : K, RunsApp P rdV [encodeValue a] (encodeValue (rd a)))
  {R : ℕ} (hR : ∀ a : K, appCost P rdV [encodeValue a] ≤ R)
  {σ : Val} {σV : MachineValue}
  (hσ : ∀ v : V, RunsApp P σV [encodeValue v] (encodeValue (σ v)))
  {S : ℕ} (hS : ∀ v : V, v.idx < 2 ^ 64 → appCost P σV [encodeValue v] ≤ S)
  {wX : List E → LeanXmss.Signature} {wXV : MachineValue}
  (hwX : ∀ a : List E, RunsApp P wXV [encodeValue a] (encodeValue (wX a)))
  {WX : ℕ} (hWX : ∀ a : List E, a.length ≤ 56 → appCost P wXV [encodeValue a] ≤ WX)
  {wS : E → Sphincs.Signature} {wSV : MachineValue}
  (hwS : ∀ a : E, RunsApp P wSV [encodeValue a] (encodeValue (wS a)))
  {WS : ℕ} (hWS : ∀ a : E, appCost P wSV [encodeValue a] ≤ WS)
  {wD : List E → List E → LeanVM.Da.MatrixWitness} {wDV : MachineValue}
  (hwD : ∀ a b : List E, RunsApp P wDV [encodeValue a, encodeValue b] (encodeValue (wD a b)))
  {WD : ℕ} (hWD : ∀ a b : List E, a.length + b.length ≤ 16 →
      appCost P wDV [encodeValue a, encodeValue b] ≤ WD)
  {wV : List E → LeanVM.Protocol.Compile.Proof} {wVV : MachineValue}
  (hwV : ∀ a : List E, RunsApp P wVV [encodeValue a] (encodeValue (wV a)))
  {WV : ℕ}
  {wA : List E → LeanVM.Node.BatchingHints} {wAV : MachineValue}
  (hwA : ∀ a : List E, RunsApp P wAV [encodeValue a] (encodeValue (wA a)))
  {WA : ℕ} (hWA : ∀ a : List E, a.length ≤ 16 → appCost P wAV [encodeValue a] ≤ WA)
include hrd hR hσ hS hwX hWX hwS hWS hwD hWD hwV hwA hWA

/-- **The witness off the tables** (`decWitTabC`), the tables good and of at most `N` marks, `nk ≤
K`, `nrx, nrs ≤ X` (`K, N, X ≤ 2^34`): at most `decWitTabPrice G R S WX WS WD WV WA K N X`. -/
theorem decWitTab_costK (D : DiscreteLogTables) (hP : Includes P Decoder.decWitTabC.costDeps)
    (hG : GLogBound P D G) (K N X : ℕ) (hK : K ≤ 2 ^ 34) (hN : N ≤ 2 ^ 34) (hX : X ≤ 2 ^ 34)
    (nk nrx nrs : ℕ) (hnk : nk ≤ K) (hnrx : nrx ≤ X) (hnrs : nrs ≤ X)
    (w380 p53 p56 : E) (tx ts : Array ℕ × Array ℕ) (htx : TableGood tx) (hts : TableGood ts)
    (htxN : tx.1.size ≤ N) (htsN : ts.1.size ≤ N) (args : List E) (hargs : args.length ≤ 55)
    (hWV : ∀ c < nk, appCost P wVV [encodeValue (Decoder.subArgsK rd σ c)] ≤ WV) :
    machineCost P Decoder.decWitTabC.costIdx [encodeValue D, σV, rdV, wXV, wSV, wDV, wVV, wAV,
      encodeValue nk, encodeValue nrx, encodeValue nrs, encodeValue w380, encodeValue p53,
      encodeValue p56, encodeValue tx, encodeValue ts, encodeValue args] ≤
      decWitTabPrice G R S WX WS WD WV WA K N X := by
  rw [Decoder.decWitTabC.costEq P hP D σ σV hσ rd rdV hrd wX wXV hwX wS wSV hwS wD wDV hwD wV wVV
    hwV wA wAV hwA]
  have := kidsT_costK P hrd hR hσ hS hwV D (by includes) hG w380 p53 p56 tx ts htx hts N hN htxN
    htsN K hK nk hnk hWV
  have := xmssRawsT_cost P hrd hR hwX hWX (by includes) p53 args hargs tx htx nrx X hX hnrx
  have := sphincsRawsT_cost P hrd hR hwS hWS (by includes) p56 ts hts nrx nrs X (by omega) hX
    hnrs
  have := daWitness_costK P hσ hS D (by includes) hG hwD hWD
  have := aggArgs_costK P hσ hS (by includes)
  have := hWA (Decoder.aggArgs σ) (by simp [Decoder.aggArgs])
  rw [nodeWitnessOf_cost P (by includes)]
  unfold decWitTabPrice
  omega

/-- **The witness, the counts given** (`decWitAtC`): the two regions' tables built once, then
`decWitTabC`: `nk ≤ K`, `lx, ls ≤ N`, `nrx, nrs ≤ X`, at most
`decWitAtPrice G R S WX WS WD WV WA K N X`. -/
theorem decWitAt_costK (D : DiscreteLogTables) (hP : Includes P Decoder.decWitAtC.costDeps)
    (hG : GLogBound P D G) (K N X : ℕ) (hK : K ≤ 2 ^ 34) (hN : N ≤ 2 ^ 34) (hX : X ≤ 2 ^ 34)
    (nk lx ls nrx nrs : ℕ) (hnk : nk ≤ K) (hlx : lx < 2 ^ 34) (hls : ls ≤ 2 ^ 34) (hlxN : lx ≤ N)
    (hlsN : ls ≤ N) (hnrx : nrx ≤ X) (hnrs : nrs ≤ X)
    (hWV : ∀ c < nk, appCost P wVV [encodeValue (Decoder.subArgsK rd σ c)] ≤ WV) :
    machineCost P Decoder.decWitAtC.costIdx [encodeValue D, σV, rdV, wXV, wSV, wDV, wVV, wAV,
      encodeValue nk, encodeValue lx, encodeValue ls, encodeValue nrx, encodeValue nrs] ≤
      decWitAtPrice G R S WX WS WD WV WA K N X := by
  rw [Decoder.decWitAtC.costEq P hP D σ σV hσ rd rdV hrd wX wXV hwX wS wSV hwS wD wDV hwD wV wVV
    hwV wA wAV hwA]
  have h1 := regionTable_cost P hrd hR D (by includes) hG (σ (.n 45)) 0 lx (by norm_num) hlx.le
  have h2 := regionTable_cost P hrd hR D (by includes) hG (σ (.n 45)) lx ls hlx.le hls
  have := decWitTab_costK P hrd hR hσ hS hwX hWX hwS hWS hwD hWD hwV hwA hWA D (by includes) hG
    K N X hK hN hX nk nrx nrs hnk hnrx hnrs (σ (.n 399)) (σ (.n 31)) (σ (.n 34)) _ _
    (regionTable_good (rd := rd) D (σ (.n 45)) 0 lx hlx.le)
    (regionTable_good (rd := rd) D (σ (.n 45)) lx ls hls)
    ((regionTable_size_le (rd := rd) D (σ (.n 45)) 0 lx).trans hlxN)
    ((regionTable_size_le (rd := rd) D (σ (.n 45)) lx ls).trans hlsN) (Decoder.l2ArgsD σ)
    (by simp [Decoder.l2ArgsD]) hWV
  have := l2ArgsD_costK P hσ hS (by includes)
  have e1 : regionTablePrice G R lx ≤ regionTablePrice G R N := by
    unfold regionTablePrice; exact Nat.add_le_add_right (Nat.mul_le_mul_left _ hlxN) _
  have e2 : regionTablePrice G R ls ≤ regionTablePrice G R N := by
    unfold regionTablePrice; exact Nat.add_le_add_right (Nat.mul_le_mul_left _ hlsN) _
  cost_facts [hS]
  unfold decWitAtPrice
  omega

/-- **The witness** (`decWitC`), the logarithm's tables `D` given, the callees' witness functions'
prices given, the counts within `K N X` (`CountsWithin`): the counts (five logarithms), then
`decWitAtC`: at most `decWitPrice G R S WX WS WD WV WA K N X`. -/
theorem decWitC_costK (D : DiscreteLogTables) (hP : Includes P Decoder.decWitC.costDeps)
    (hG : GLogBound P D G) {K N X : ℕ} (hc : CountsWithin D σ K N X)
    (hWV : ∀ c < Decoder.nKidsD D σ, appCost P wVV [encodeValue (Decoder.subArgsK rd σ c)] ≤ WV) :
    machineCost P Decoder.decWitC.costIdx [encodeValue D, σV, rdV, wXV, wSV, wDV, wVV, wAV] ≤
      decWitPrice G R S WX WS WD WV WA K N X := by
  rw [Decoder.decWitC.costEq P hP D σ σV hσ rd rdV hrd wX wXV hwX wS wSV hwS wD wDV hwD wV wVV
    hwV wA wAV hwA]
  have := nKids_costK P hσ hS D (by includes) hG
  have := lxSlots_costK P hσ hS D (by includes) hG
  have := lsSlots_costK P hσ hS D (by includes) hG
  have := nRawX_costK P hσ hS D (by includes) hG
  have := nRawS_costK P hσ hS D (by includes) hG
  have := decWitAt_costK P hrd hR hσ hS hwX hWX hwS hWS hwD hWD hwV hwA hWA D (by includes) hG
    K N X hc.kidsBound hc.slotsBound hc.claimsBound
    (Decoder.nKidsD D σ) (Decoder.lxSlotsD D σ) (Decoder.lsSlotsD D σ) (Decoder.nRawXD D σ)
    (Decoder.nRawSD D σ) hc.kids (gLogD_lt D _) (gLogD_lt D _).le hc.xmssSlots
    hc.sphincsSlots hc.rawXmss hc.rawSphincs hWV
  unfold decWitPrice
  omega

end Witness

section Top

variable {rd : Reader} {rdV : MachineValue}
  (hrd : ∀ a : K, RunsApp P rdV [encodeValue a] (encodeValue (rd a)))
  {R : ℕ} (hR : ∀ a : K, appCost P rdV [encodeValue a] ≤ R)
  {σ : Val} {σV : MachineValue}
  (hσ : ∀ v : V, RunsApp P σV [encodeValue v] (encodeValue (σ v)))
  {S : ℕ} (hS : ∀ v : V, v.idx < 2 ^ 64 → appCost P σV [encodeValue v] ≤ S)
  {Vn : NFrames} {VnV : MachineValue}
  (hVn : ∀ (k : ℕ) (a r : List E) (v : V),
    RunsApp P VnV [encodeValue k, encodeValue a, encodeValue r, encodeValue v]
      (encodeValue (Vn k a r v)))
  {F : ℕ} (hF : ∀ (k : ℕ) (a r : List E) (v : V), k < 2 ^ 64 → v.idx < 2 ^ 64 → a.length + r.length ≤ 16 →
    appCost P VnV [encodeValue k, encodeValue a, encodeValue r, encodeValue v] ≤ F)
  {cl : E → E → ℕ} {clV : MachineValue}
  (hcl : ∀ a b : E, RunsApp P clV [encodeValue a, encodeValue b] (encodeValue (cl a b)))
  {C : ℕ} (hC : ∀ a b : E, appCost P clV [encodeValue a, encodeValue b] ≤ C)
  {L : ℕ} (hL32 : L ≤ 2 ^ 32)
include hrd hR hσ hS hVn hF hcl hC hL32

end Top

end

end LeanVM.SaltedGuest.Bounds
