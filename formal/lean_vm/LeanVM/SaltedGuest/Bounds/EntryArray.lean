/-
  LeanVM.SaltedGuest.Bounds.EntryArray

  The prices of the salted decoder's entry table and frame map.
-/

module

public import LeanVM.SaltedGuest.Decoder.EntryTableEq
public import LeanVM.Cost.Bounds.Decoder.EntryArray

/-!
# The prices of the salted entry table and frame map

The salted decoder's entry table (`entryArrayTK`) and frame map (`frameAtAK`) are the deployed
ones (`Bounds/Decoder/EntryArray.lean`) with the salted functions' argument and return counts read
off arrays (`argCountsK`, `retCountsK`, at most `56` and `10`, as the deployed guest's) and the
frame cells read off packed blocks (`cellAtK`: an index, a shift of a block of at most `16` limbs
and a remainder). A cell read charges the limbs of the value's index (`v.idx`), so the frame
lookups' prices are stated for `v.idx < 2^64`.

* `argCountsK_le`, `retCountsK_le`; `locsTableK_lt`: every block below `2^1024`;
* `packedCell_cost` (`37`), `cellAtK_cost` (`47`), `frameWordAtK_cost` (`R + 1274`);
* `entryKeyTK_cost`: `66R + 41200`, the deployed key's price; `pairOfK_cost`, `statePairsK_cost`,
  `entryPairsK_cost` (per state `pairsStatePrice Gpc M Pr R`, the deployed);
* **`entryArrayTK_cost`**: at most `entryArrayStatePriceK Gpc M Pr R E · |states| + 28`;
* **`frameAtAK_cost`**: `(64w + 78 + 9·wl E)·(E + 2) + 27w + R + 1323`; `frameFpAK_cost`:
  `(64w + 78 + 9·wl E)·(E + 2) + 27w + 38`; `frameValAtK_cost`: `R + 1283`.
-/

namespace LeanVM.SaltedGuest.Bounds

open LeanVM.Cost LeanVM.Cost.Decoder LeanVM.Cost.Library LeanVM.Cost.Bounds LeanVM.Parameters
open LeanVM.Semantics LeanVM.Extraction LeanVM.Extraction.Fast LeanVM.Guest.Core
open LeanVM.Guest.Located LeanVM.Guest.Fast LeanVM.SaltedGuest.Decoder

@[expose] public section

attribute [local instance] lexOrd

set_option exponentiation.threshold 1100

/-! ## The tables -/

theorem guestArgCountsListK_le : LeanVM.SaltedGuest.Decoder.guestArgCountsList.all (· ≤ 56) = true := by decide +kernel

theorem guestRetCountsListK_le : LeanVM.SaltedGuest.Decoder.guestRetCountsList.all (· ≤ 10) = true := by decide +kernel

theorem argCountsK_le (j : ℕ) : argCountsK.getD j 0 ≤ 56 :=
  toArray_getD_le_of_all guestArgCountsListK_le j

theorem retCountsK_le (j : ℕ) : retCountsK.getD j 0 ≤ 10 :=
  toArray_getD_le_of_all guestRetCountsListK_le j

theorem packCells_lt : ∀ l : List ℕ, (∀ c ∈ l, c < 65536) → packCells l < 65536 ^ l.length
  | [], _ => by simp [packCells]
  | c :: l, h => by
    have ih := packCells_lt l (fun x hx ↦ h x (List.mem_cons_of_mem _ hx))
    have hc := h c List.mem_cons_self
    simp only [packCells, List.length_cons, pow_succ]
    nlinarith

theorem lt_of_packOk {l : List ℕ} {r : ℕ} (h : packOk l r = true) : r < 65536 ^ l.length := by
  simp only [packOk, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, decide_eq_true_eq] at h
  rw [h.1]
  exact packCells_lt l h.2

theorem lt_of_blocksOk : ∀ (l bs : List ℕ), blocksOk l bs = true → ∀ b ∈ bs, b < 2 ^ 1024
  | _, [], _ => by simp
  | l, b :: bs, h => by
    simp only [blocksOk, Bool.and_eq_true] at h
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · have h1 := lt_of_packOk h.1
      have hl : (l.take 64).length ≤ 64 := by simp
      calc x < 65536 ^ (l.take 64).length := h1
        _ ≤ 65536 ^ 64 := Nat.pow_le_pow_right (by norm_num) hl
        _ = 2 ^ 1024 := by rw [show (65536 : ℕ) = 2 ^ 16 by norm_num, ← pow_mul]
    · exact lt_of_blocksOk _ _ h.2 x hx

/-- **Every packed block is below `2^1024`.** -/
theorem locsTableK_lt (j i : ℕ) : (locsTableK.getD j #[]).getD i 0 < 2 ^ 1024 := by
  by_cases hj : j < nFns
  · have hl : j < locsBlocksList.length := locsBlocksList_length ▸ hj
    have hrow : locsTableK.getD j #[] = (locsBlocksList.getD j []).toArray := by
      simp [locsTableK, Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD, hl]
    rw [hrow, Array.getD_eq_getD_getElem?, List.getElem?_toArray]
    have hb := lt_of_blocksOk _ _ (locsBlocks_ok j (by unfold nFns at hj; omega))
    cases h : (locsBlocksList.getD j [])[i]? with
    | none => simp
    | some x => simpa using hb x (List.mem_of_getElem? h)
  · have hl : locsBlocksList.length ≤ j := by rw [locsBlocksList_length]; omega
    have hrow : locsTableK.getD j #[] = #[] := by
      simp [locsTableK, Array.getD_eq_getD_getElem?, List.getElem?_eq_none hl]
    rw [hrow]
    simp

/-! ## A packed cell -/

variable (P : MachineProgram)

theorem limbs_le_16 {x : ℕ} (h : x < 2 ^ 1024) : limbCount x ≤ 16 :=
  (limbs_le_iff (by norm_num)).2 (by simpa using h)

/-- **A cell of a packed block** (`packedCellC`), the block below `2^1024`: at most `37`. -/
theorem packedCell_cost (hP : Includes P packedCellC.costDeps) {r : ℕ} (hr : r < 2 ^ 1024)
    {i : ℕ} (hi : i < 64) :
    machineCost P packedCellC.costIdx [encodeValue r, encodeValue i] ≤ 37 := by
  rw [packedCellC.costEq P hP, limbs_of_lt (by omega : 16 * i < 2 ^ 64),
    limbs_of_lt (by omega : i < 2 ^ 64)]
  have h1 := limbs_le_16 hr
  have h2 : limbCount (r >>> (16 * i)) ≤ 16 :=
    limbs_le_16 (lt_of_le_of_lt (by rw [Nat.shiftRight_eq_div_pow]; exact Nat.div_le_self _ _) hr)
  have h3 : limbCount r ≥ 1 ∨ limbCount r = 0 := by omega
  omega

/-- **A cell of a packed row** (`cellAtKC`), its blocks below `2^1024` and the index word-sized:
at most `47`. -/
theorem cellAtK_cost (hP : Includes P cellAtKC.costDeps) {row : Array ℕ}
    (hrow : ∀ k, row.getD k 0 < 2 ^ 1024) {i : ℕ} (hi : i < 2 ^ 64) :
    machineCost P cellAtKC.costIdx [encodeValue row, encodeValue i] ≤ 47 := by
  rw [cellAtKC.costEq P hP, limbs_of_lt hi]
  have := packedCell_cost P (by includes) (hrow (i / 64)) (Nat.mod_lt i (by norm_num))
  omega

theorem cellAtK_lt (row : Array ℕ) (i : ℕ) : cellAtK row i < 2 ^ 16 := by
  unfold cellAtK packedCell
  exact Nat.mod_lt _ (by norm_num)

section Reads

variable (rd : Reader) (rdVal : MachineValue)
  (hrd : ∀ a : K, RunsApp P rdVal [encodeValue a] (encodeValue (rd a)))
  (R : ℕ) (hR : ∀ a : K, appCost P rdVal [encodeValue a] ≤ R)

include hrd hR in
/-- **A frame's word** (`frameWordAtKC`): a packed cell and a read, at most `R + 1274`. -/
theorem frameWordAtK_cost (hP : Includes P frameWordAtKC.costDeps) (fp : K) (j : ℕ) (v : V)
    (hv : v.idx < 2 ^ 64) :
    machineCost P frameWordAtKC.costIdx [encodeValue locsTableK, rdVal, encodeValue fp,
      encodeValue j, encodeValue v] ≤ R + 1274 := by
  rw [frameWordAtKC.costEq P hP locsTableK rd rdVal hrd]
  have h1 := cellAtK_cost P (by includes) (locsTableK_lt j) hv
  have h2 := wordWith_cost P rd rdVal hrd R hR (W := 16) (by norm_num) (by norm_num) (by includes)
    fp _ (cellAtK_lt (locsTableK.getD j #[]) v.idx)
  unfold psAt at h2
  omega

include hrd hR in
/-- **A state's key** (`entryKeyTKC`): its `≤ 56` argument and `≤ 10` return words read, at most
`66R + 41200`. -/
theorem entryKeyTK_cost (hP : Includes P entryKeyTKC.costDeps) (s : Registers K) (j : ℕ) :
    machineCost P entryKeyTKC.costIdx [encodeValue argCountsK, encodeValue retCountsK, rdVal,
      encodeValue s, encodeValue j] ≤ 66 * R + 41200 := by
  have ha := argCountsK_le j
  have hr := retCountsK_le j
  rw [entryKeyTKC.costEq P hP argCountsK retCountsK rd rdVal hrd,
    limbs_of_lt (by omega : argCountsK.getD j 0 < 2 ^ 64),
    limbs_of_lt (by omega : 2 + argCountsK.getD j 0 < 2 ^ 64)]
  have h1 := wordsWith_cost P rd rdVal hrd R hR (by includes) (W := 7) (by norm_num) (by norm_num)
    s.fp 2 (argCountsK.getD j 0) (show 2 + argCountsK.getD j 0 ≤ 2 ^ 7 by omega)
  have h2 := wordsWith_cost P rd rdVal hrd R hR (by includes) (W := 7) (by norm_num) (by norm_num)
    s.fp (2 + argCountsK.getD j 0) (retCountsK.getD j 0)
    (show 2 + argCountsK.getD j 0 + retCountsK.getD j 0 ≤ 2 ^ 7 by omega)
  have h3 := callKey_cost P (by includes) j (wordsWith rd s.fp 2 (argCountsK.getD j 0))
    (wordsWith rd s.fp (2 + argCountsK.getD j 0) (retCountsK.getD j 0))
  rw [length_wordsWith, length_wordsWith] at h3
  unfold psAt at h1 h2
  simp only [max_self]
  generalize argCountsK.getD j 0 = a at *
  generalize retCountsK.getD j 0 = b at *
  nlinarith

/-- A state's key: of at most `56` argument codes and `10` return codes. -/
theorem entryKeyTK_ok (s : Registers K) {j : ℕ} (hj : j < 2 ^ 64) :
    EntryKeyOK (entryKeyTK argCountsK retCountsK rd s j) :=
  ⟨callKey_ok hj (by rw [length_wordsWith]; exact argCountsK_le j)
    (by rw [length_wordsWith]; have := retCountsK_le j; omega),
   by simp only [entryKeyTK, callKey, List.length_map, length_wordsWith]; exact retCountsK_le j⟩

section Pairs

variable (pre : ℕ → K → Bool) (preVal : MachineValue)
  (hpre : ∀ (a : ℕ) (b : K), RunsApp P preVal [encodeValue a, encodeValue b] (encodeValue (pre a b)))
  (Pr : ℕ) (hPr : ∀ (j : ℕ) (fp : K), j < 2 ^ 64 → appCost P preVal [encodeValue j, encodeValue fp] ≤ Pr)

/-- The price of the pairs one salted state files: the pc lookup, per function entered there its
precondition's test and its key. -/
def pairsStatePriceK (Gpc M Pr R : ℕ) : ℕ := Gpc + (Pr + 66 * R + 41280) * M + 50

/-- The price per state of the salted sorted entry array: its pairs, and per pair the sort and the
dedup. -/
def entryArrayStatePriceK (Gpc M Pr R E : ℕ) : ℕ :=
  pairsStatePriceK Gpc M Pr R + M * ((4343 + 5 * wl E) * E + 7 * wl E + 4373)

include hrd hR hpre hPr in
/-- The pair state `s` files for function `j` (`pairOfKC`): its precondition's test and its key. -/
theorem pairOfK_cost (hP : Includes P pairOfKC.costDeps) (s : Registers K) (j : ℕ)
    (hj : j < 2 ^ 64) :
    machineCost P pairOfKC.costIdx [encodeValue argCountsK, encodeValue retCountsK, preVal, rdVal,
      encodeValue s, encodeValue j] ≤ Pr + 66 * R + 41219 := by
  rw [pairOfKC.costEq P hP argCountsK retCountsK pre preVal hpre rd rdVal hrd]
  have h1 := hPr j s.fp hj
  have h2 := entryKeyTK_cost P rd rdVal hrd R hR (by includes) s j
  split_ifs <;> omega

theorem statePairsK_ok (pcT : SortedMap ℕ (List ℕ)) (hpc : ∀ k, ∀ j ∈ pcT.getD k [], j < 2 ^ 64)
    (s : Registers K) : ∀ p ∈ statePairsK pcT argCountsK retCountsK pre rd s, EntryKeyOK p.1 := by
  intro p hp
  unfold statePairsK at hp
  obtain ⟨j, hj, hpj⟩ := List.mem_filterMap.1 hp
  unfold pairOfK at hpj
  split_ifs at hpj
  cases hpj
  exact entryKeyTK_ok rd s (hpc _ j hj)

theorem length_statePairsK (pcT : SortedMap ℕ (List ℕ)) (s : Registers K) :
    (statePairsK pcT argCountsK retCountsK pre rd s).length ≤ (pcT.getD (laneCode s.pc) []).length :=
  List.length_filterMap_le _ _

include hrd hR hpre hPr in
/-- **The pairs a state files** (`statePairsKC`), at most `M` functions per pc, a pc lookup at
most `Gpc`: at most `Gpc + (Pr + 66R + 41256)·M + 22`. -/
theorem statePairsK_cost (hP : Includes P statePairsKC.costDeps) (pcT : SortedMap ℕ (List ℕ))
    (M Gpc : ℕ) (hpc : ∀ k, ∀ j ∈ pcT.getD k [], j < 2 ^ 64) (hM : ∀ k, (pcT.getD k []).length ≤ M)
    (hG : ∀ k, NatKey k → machineCost P getPcC.costIdx [encodeValue pcT, encodeValue k] ≤ Gpc)
    (s : Registers K) :
    machineCost P statePairsKC.costIdx [encodeValue pcT, encodeValue argCountsK,
      encodeValue retCountsK, preVal, rdVal, encodeValue s] ≤
      Gpc + (Pr + 66 * R + 41256) * M + 22 := by
  rw [statePairsKC.costEq P hP pcT argCountsK retCountsK pre preVal hpre rd rdVal hrd]
  have hg := hG (laneCode s.pc) (UInt64.toNat_lt _)
  have hf := filterMap_cost P (by includes) _
    (.closure statePairsKC.lam0.costIdx [encodeValue argCountsK, encodeValue retCountsK, preVal,
      rdVal, encodeValue s])
    (fun j ↦ RunsApp.of_spec (statePairsKC.lam0.costSpec P (by includes) argCountsK retCountsK pre
      preVal hpre rd rdVal hrd s j))
    (Pr + 66 * R + 41240) (pcT.getD (laneCode s.pc) []) (fun j hj ↦ by
      rw [appCost_fn, List.cons_append, List.cons_append, List.cons_append, List.cons_append,
        List.cons_append, List.nil_append,
        statePairsKC.lam0.costEq P (by includes) argCountsK retCountsK pre preVal hpre rd rdVal hrd]
      simp only [List.length_cons, List.length_nil]
      have := pairOfK_cost P rd rdVal hrd R hR pre preVal hpre Pr hPr (by includes) s j
        (hpc _ j hj)
      omega)
  have hm := Nat.mul_le_mul_left (Pr + 66 * R + 41240 + 16) (hM (laneCode s.pc))
  generalize pcT.get? (laneCode s.pc) = o
  cases o <;> dsimp only <;> nlinarith

theorem entryPairsK_ok (pcT : SortedMap ℕ (List ℕ)) (hpc : ∀ k, ∀ j ∈ pcT.getD k [], j < 2 ^ 64) :
    ∀ (states : List (Registers K)), ∀ p ∈ entryPairsK pcT argCountsK retCountsK pre rd states,
      EntryKeyOK p.1
  | [] => by simp [entryPairsK]
  | s :: ss => by
    intro p hp
    rw [entryPairsK, List.mem_append] at hp
    rcases hp with hp | hp
    · exact statePairsK_ok rd pre pcT hpc s p hp
    · exact entryPairsK_ok pcT hpc ss p hp

theorem length_entryPairsK (pcT : SortedMap ℕ (List ℕ)) (M : ℕ)
    (hM : ∀ k, (pcT.getD k []).length ≤ M) :
    ∀ (states : List (Registers K)),
      (entryPairsK pcT argCountsK retCountsK pre rd states).length ≤ M * states.length
  | [] => by simp [entryPairsK]
  | s :: ss => by
    rw [entryPairsK, List.length_append, List.length_cons, Nat.mul_succ]
    have := length_statePairsK rd pre pcT s
    have := hM (laneCode s.pc)
    have := length_entryPairsK pcT M hM ss
    omega

include hrd hR hpre hPr in
/-- **The pairs the states file** (`entryPairsKC`): at most `pairsStatePriceK Gpc M Pr R` per
state, `3`. -/
theorem entryPairsK_cost (hP : Includes P entryPairsKC.costDeps) (pcT : SortedMap ℕ (List ℕ))
    (M Gpc : ℕ) (hpc : ∀ k, ∀ j ∈ pcT.getD k [], j < 2 ^ 64) (hM : ∀ k, (pcT.getD k []).length ≤ M)
    (hG : ∀ k, NatKey k → machineCost P getPcC.costIdx [encodeValue pcT, encodeValue k] ≤ Gpc) :
    ∀ states : List (Registers K),
      machineCost P entryPairsKC.costIdx [encodeValue pcT, encodeValue argCountsK,
        encodeValue retCountsK, preVal, rdVal, encodeValue states] ≤
        pairsStatePriceK Gpc M Pr R * states.length + 3
  | [] => by rw [entryPairsKC.costEq_nil P hP pcT argCountsK retCountsK pre preVal hpre rd rdVal hrd]; omega
  | s :: ss => by
    rw [entryPairsKC.costEq_cons P hP pcT argCountsK retCountsK pre preVal hpre rd rdVal hrd]
    have h1 := statePairsK_cost P rd rdVal hrd R hR pre preVal hpre Pr hPr (by includes) pcT M Gpc
      hpc hM hG s
    have h2 := entryPairsK_cost hP pcT M Gpc hpc hM hG ss
    have h3 := append_cost P (by includes) (statePairsK pcT argCountsK retCountsK pre rd s)
      (entryPairsK pcT argCountsK retCountsK pre rd ss)
    have h4 := length_statePairsK rd pre pcT s
    have h5 := hM (laneCode s.pc)
    unfold pairsStatePriceK at h2 ⊢
    have e : (Pr + 66 * R + 41280) * M = (Pr + 66 * R + 41256) * M + 24 * M := by ring
    simp only [List.length_cons, Nat.mul_succ]
    omega

/-- The sorted array: keys of at most `56` codes (filed keys), at most `M` per state. -/
theorem entryArrayTK_ok (pcT : SortedMap ℕ (List ℕ)) (M : ℕ)
    (hpc : ∀ k, ∀ j ∈ pcT.getD k [], j < 2 ^ 64) (hM : ∀ k, (pcT.getD k []).length ≤ M)
    (states : List (Registers K)) :
    (∀ e ∈ entryArrayTK pcT argCountsK retCountsK pre states rd, KeyOK 56 e.1) ∧
      (entryArrayTK pcT argCountsK retCountsK pre states rd).size ≤ M * states.length := by
  unfold entryArrayTK
  refine ⟨fun e he ↦ ?_, ?_⟩
  · rw [List.mem_toArray] at he
    exact entryPairsK_ok rd pre pcT hpc states e
      (List.mem_mergeSort.1 (mem_dedupFirst _ e he)) |>.1
  · rw [List.size_toArray]
    have := length_dedupFirst_le ((entryPairsK pcT argCountsK retCountsK pre rd states).mergeSort keyLe)
    rw [List.length_mergeSort] at this
    have := length_entryPairsK rd pre pcT M hM states
    omega

include hrd hR hpre hPr in
/-- **The salted entry table as one sorted array** (`entryArrayTKC`), `M·|states| < 2^E`: the
pairs filed, their stable sort and the dedup, at most `entryArrayStatePriceK Gpc M Pr R E ·
|states| + 28`. -/
theorem entryArrayTK_cost (hP : Includes P entryArrayTKC.costDeps) (pcT : SortedMap ℕ (List ℕ))
    (M Gpc E : ℕ) (hpc : ∀ k, ∀ j ∈ pcT.getD k [], j < 2 ^ 64)
    (hM : ∀ k, (pcT.getD k []).length ≤ M)
    (hG : ∀ k, NatKey k → machineCost P getPcC.costIdx [encodeValue pcT, encodeValue k] ≤ Gpc)
    (states : List (Registers K)) (hn : M * states.length < 2 ^ E) :
    machineCost P entryArrayTKC.costIdx [encodeValue pcT, encodeValue argCountsK,
      encodeValue retCountsK, preVal, encodeValue states, rdVal] ≤
      entryArrayStatePriceK Gpc M Pr R E * states.length + 28 := by
  rw [entryArrayTKC.costEq P hP pcT argCountsK retCountsK pre preVal hpre states rd rdVal hrd]
  have hok := entryPairsK_ok rd pre pcT hpc states
  have hlen := length_entryPairsK rd pre pcT M hM states
  have h1 := entryPairsK_cost P rd rdVal hrd R hR pre preVal hpre Pr hPr (by includes) pcT M Gpc
    hpc hM hG states
  have h2 := mergeSortList_cost_wl P (wl E) (2 * 2 ^ E) (fun x hx ↦ limbs_le_wl' hx)
    (by includes) keyLe (.closure entryArrayTC.lam0.costIdx [])
    (fun a b ↦ RunsApp.of_spec (entryArrayTC.lam0.costSpec P (by includes) a b))
    (64 * 66 + 57) (fun e ↦ EntryKeyOK e.1)
    (fun a b ha hb ↦ keyLeLam_cost P (by includes) a b ha hb)
    (entryPairsK pcT argCountsK retCountsK pre rd states) (by omega) hok
  have h3 := dedupFirst_cost P (by includes)
    ((entryPairsK pcT argCountsK retCountsK pre rd states).mergeSort keyLe)
    (fun e he ↦ hok e (List.mem_mergeSort.1 he))
  have h4 := length_dedupFirst_le ((entryPairsK pcT argCountsK retCountsK pre rd states).mergeSort keyLe)
  rw [List.length_mergeSort] at h3 h4
  generalize (dedupFirst ((entryPairsK pcT argCountsK retCountsK pre rd states).mergeSort
    keyLe)).length = d at h4 ⊢
  generalize (entryPairsK pcT argCountsK retCountsK pre rd states).length = n at hlen h2 h3 h4
  have hclog : Nat.clog 2 n ≤ E := Nat.clog_le_of_le_pow (by omega)
  have hnE : n * Nat.clog 2 n ≤ n * E := Nat.mul_le_mul_left _ hclog
  have hc1 := Nat.mul_le_mul_left (64 * 66 + 57 + 62 + 5 * wl E) hnE
  have hpos := wl_pos E
  have hMs : ((4343 + 5 * wl E) * E + 7 * wl E + 4373) * n ≤
      ((4343 + 5 * wl E) * E + 7 * wl E + 4373) * (M * states.length) :=
    Nat.mul_le_mul_left _ hlen
  unfold entryArrayStatePriceK
  nlinarith

end Pairs

/-! ## A frame lookup -/

include hrd hR in
/-- **The salted frame map on the sorted array** (`frameAtAKC`): one binary search of the call's
key (`w = |args| + |rets|` words) in a table of keys of at most `56` codes and at most `2^E` pairs,
a packed cell and a read: at most `(64w + 78 + 9·wl E)·(E + 2) + 27w + R + 1323`. -/
theorem frameAtAK_cost (hP : Includes P frameAtAKC.costDeps) (E : ℕ)
    (table : Array (CallKey × K)) (ht : ∀ e ∈ table, KeyOK 56 e.1) (hs : table.size ≤ 2 ^ E)
    (j : ℕ) (hj : j < 2 ^ 64) (args rets : List LeanVM.Parameters.E) (v : V) (hv : v.idx < 2 ^ 64) :
    machineCost P frameAtAKC.costIdx [encodeValue table, encodeValue locsTableK, rdVal,
        encodeValue j, encodeValue args, encodeValue rets, encodeValue v] ≤
      (64 * (args.length + rets.length) + 78 + 9 * wl E) * (E + 2) +
        27 * (args.length + rets.length) + R + 1323 := by
  rw [frameAtAKC.costEq P hP table locsTableK rd rdVal hrd]
  have h2 := callKey_cost P (by includes) j args rets
  have hk : KeyOK (args.length + rets.length) (callKey j args rets) :=
    callKey_ok hj (by omega) (by omega)
  have h3 := searchInKey_cost P (by includes) 56 table ht _ hk (2 ^ E) (wl E)
    (fun x hx ↦ limbs_le_wl' hx) hs 0 table.size (Nat.zero_le _) hs
  have hkc : keyCmpPrice (callKey j args rets) = 64 * (args.length + rets.length) + 41 := by
    simp [keyCmpPrice, callKey]
  have hlog : Nat.log2 (table.size - 0) ≤ E := by
    have := log2_mono (show table.size - 0 ≤ 2 ^ E by omega)
    rwa [Nat.log2_two_pow] at this
  have h3' : (keyCmpPrice (callKey j args rets) + 37 + 9 * wl E) *
      (Nat.log2 (table.size - 0) + 2) ≤
      (64 * (args.length + rets.length) + 78 + 9 * wl E) * (E + 2) := by
    rw [hkc]
    exact Nat.mul_le_mul (by omega) (by omega)
  generalize (64 * (args.length + rets.length) + 78 + 9 * wl E) * (E + 2) = X at h3' ⊢
  generalize searchIn table (callKey j args rets) 0 table.size = o
  cases o with
  | none => dsimp only; omega
  | some fp =>
    have h4 := frameWordAtK_cost P rd rdVal hrd R hR (by includes) fp j v hv
    dsimp only; omega

include hrd hR in
/-- **A word of a frame looked up once** (`frameValAtKC`): at most `R + 1283`. -/
theorem frameValAtK_cost (hP : Includes P frameValAtKC.costDeps) (o : Option K) (j : ℕ) (v : V)
    (hv : v.idx < 2 ^ 64) :
    machineCost P frameValAtKC.costIdx [encodeValue locsTableK, rdVal, encodeValue o,
      encodeValue j, encodeValue v] ≤ R + 1283 := by
  rw [frameValAtKC.costEq P hP locsTableK rd rdVal hrd]
  cases o with
  | none => dsimp only; omega
  | some fp =>
    have h4 := frameWordAtK_cost P rd rdVal hrd R hR (by includes) fp j v hv
    dsimp only; omega

end Reads

/-- **A frame looked up once** (`frameFpAKC`, `frameAtAK`'s search): one binary search of the call's
key (`w = |args| + |rets|` words): at most `(64w + 78 + 9·wl E)·(E + 2) + 27w + 38`. -/
theorem frameFpAK_cost (hP : Includes P frameFpAKC.costDeps) (E : ℕ)
    (table : Array (CallKey × K)) (ht : ∀ e ∈ table, KeyOK 56 e.1) (hs : table.size ≤ 2 ^ E)
    (j : ℕ) (hj : j < 2 ^ 64) (args rets : List LeanVM.Parameters.E) :
    machineCost P frameFpAKC.costIdx [encodeValue table, encodeValue j, encodeValue args,
        encodeValue rets] ≤
      (64 * (args.length + rets.length) + 78 + 9 * wl E) * (E + 2) +
        27 * (args.length + rets.length) + 38 := by
  rw [frameFpAKC.costEq P hP]
  have h2 := callKey_cost P (by includes) j args rets
  have hk : KeyOK (args.length + rets.length) (callKey j args rets) :=
    callKey_ok hj (by omega) (by omega)
  have h3 := searchInKey_cost P (by includes) 56 table ht _ hk (2 ^ E) (wl E)
    (fun x hx ↦ limbs_le_wl' hx) hs 0 table.size (Nat.zero_le _) hs
  have hkc : keyCmpPrice (callKey j args rets) = 64 * (args.length + rets.length) + 41 := by
    simp [keyCmpPrice, callKey]
  have hlog : Nat.log2 (table.size - 0) ≤ E := by
    have := log2_mono (show table.size - 0 ≤ 2 ^ E by omega)
    rwa [Nat.log2_two_pow] at this
  have h3' : (keyCmpPrice (callKey j args rets) + 37 + 9 * wl E) *
      (Nat.log2 (table.size - 0) + 2) ≤
      (64 * (args.length + rets.length) + 78 + 9 * wl E) * (E + 2) := by
    rw [hkc]
    exact Nat.mul_le_mul (by omega) (by omega)
  generalize (64 * (args.length + rets.length) + 78 + 9 * wl E) * (E + 2) = X at h3' ⊢
  omega

end
end LeanVM.SaltedGuest.Bounds
