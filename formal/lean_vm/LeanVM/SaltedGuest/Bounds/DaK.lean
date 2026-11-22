/-
  LeanVM.SaltedGuest.Bounds.DaK

  The price of the salted decoder's DA matrix reader.
-/

module

public import LeanVM.SaltedGuest.Bounds.V.Readers
public import LeanVM.Cost.Bounds.Guest.Da
public import LeanVM.SaltedGuest.Decoder.Readers

/-!
# The price of the salted `da_verify`'s witness

The deployed `Cost/Bounds/Guest/Da.lean` for the salted reader (`Decoder/Readers.lean`: the
columns' frames of `da_verify_column`, function `31`, their words `14` and `15`; the blob loop
`__loop26`, function `394`; the cell check `da_verify_cell`, function `32`, the key's word its
second argument; the rows' count off `σ (.n 2)`), the valuation and frame map priced for values of
index below `2^64`. Each lemma is the deployed one of the name without `K`.
-/

namespace LeanVM.SaltedGuest.Bounds

open LeanVM.Cost.Bounds.Guest LeanVM.SaltedGuest.Decoder LeanVM.Cost LeanVM.Cost.Bounds LeanVM.Cost.Library LeanVM.Parameters
open LeanVM.Guest.Core LeanVM.Guest.B1 LeanVM.Guest.B1.Main LeanVM.Guest.Fast

public section

variable (P : MachineProgram) {G : ℕ}

/-- A padded cell's symbols: `256`. -/
theorem length_dvSymsColsK (r : ℕ) (σ : Val) (Vn : NFrames) (cols : Array (E × E)) (i j : ℕ) :
    (dvSymsColsK r σ Vn cols i j).length = 256 := by
  unfold dvSymsColsK dvSymsCellK cellSymsAtK cellSymsOfSK
  split_ifs
  · rw [List.length_map, List.length_range]
  · rw [List.length_replicate]

section Frames

variable {Vn : NFrames} {VnV : MachineValue}
  (hVn : ∀ (k : ℕ) (a r : List E) (v : V),
    RunsApp P VnV [encodeValue k, encodeValue a, encodeValue r, encodeValue v]
      (encodeValue (Vn k a r v)))
  {F : ℕ} (hF : ∀ (k : ℕ) (a r : List E) (v : V), k < 2 ^ 64 → v.idx < 2 ^ 64 → a.length + r.length ≤ 16 →
    appCost P VnV [encodeValue k, encodeValue a, encodeValue r, encodeValue v] ≤ F)
include hVn hF

/-- **A cell's `256` symbols at a row's valuation** (`cellSymsAtC`), the row's valuation a closure
`rowV` of price at most `Rw`: `3·Rw + 256·F + 12863`. -/
theorem cellSymsAt_costK (hP : Includes P cellSymsAtKC.costDeps) (c14 key : E) {row : Val}
    {rowV : MachineValue} (hrow : ∀ v : V, RunsApp P rowV [encodeValue v] (encodeValue (row v)))
    {Rw : ℕ} (hRw : ∀ v : V, v.idx < 2 ^ 64 → appCost P rowV [encodeValue v] ≤ Rw) :
    machineCost P cellSymsAtKC.costIdx [VnV, encodeValue c14, encodeValue key, rowV] ≤
      3 * Rw + 256 * F + 13500 := by
  rw [cellSymsAtKC.costEq P hP Vn VnV hVn c14 key row rowV hrow]
  set a := [row (.n 7), row (.n 8), row (.n 9)]
  have hσ : ∀ v : V, RunsApp P (.closure cellSymsAtKC.lam0.costIdx
      [VnV, encodeValue a, encodeValue [c14, key]]) [encodeValue v] (encodeValue (Vn 32 [c14, key] a v)) :=
    fun v ↦ RunsApp.of_spec (cellSymsAtKC.lam0.costSpec P (by includes) Vn VnV hVn a [c14, key] v)
  rw [cellSymsOfSKC.costEq P (by includes) _ _ hσ]
  have m := rangeMap_le P (by includes) (by includes) _
    (.closure cellSymsOfSKC.lam0.costIdx
      [.closure cellSymsAtKC.lam0.costIdx [VnV, encodeValue a, encodeValue [c14, key]]])
    (fun j ↦ RunsApp.of_spec (cellSymsOfSKC.lam0.costSpec P
      (by includes) _ _ hσ j))
    (F + 24) 256 256 le_rfl (by norm_num) (fun j hj ↦ by
      rw [appCost_fn, List.cons_append, List.nil_append,
        cellSymsOfSKC.lam0.costEq P (by includes) _ _ hσ,
        limbs_of_lt (by omega : j < 2 ^ 64), limbs_of_lt (by omega : j + 2 < 2 ^ 64), appCost_fn, List.cons_append, List.cons_append,
        List.cons_append, List.nil_append,
        cellSymsAtKC.lam0.costEq P (by includes) Vn VnV hVn, List.length_cons, List.length_cons, List.length_cons, List.length_cons, List.length_nil]
      have := hF 32 [c14, key] a (.n (j + 2)) (by norm_num) (by show j + 2 < 2 ^ 64; omega) (by simp [a])
      omega)
  have := hRw (.n 7) (by idx_lt); have := hRw (.n 8) (by idx_lt); have := hRw (.n 9) (by idx_lt)
  omega

section Val

variable {σ : Val} {σV : MachineValue}
  (hσ : ∀ v : V, RunsApp P σV [encodeValue v] (encodeValue (σ v)))
  {S : ℕ} (hS : ∀ v : V, v.idx < 2 ^ 64 → appCost P σV [encodeValue v] ≤ S)
include hσ hS

omit hVn hF in
/-- Column `j`'s arguments (`dvColArgsC`), `j < 128`: `8·S + 4364`. -/
theorem dvColArgs_costK (hP : Includes P dvColArgsKC.costDeps) (j : ℕ)
    (hj : j < 128) :
    machineCost P dvColArgsKC.costIdx [σV, encodeValue j] ≤
      9 * S + 4500 := by
  rw [dvColArgsKC.costEq P hP σ σV hσ]
  have := powSqE_cost_lt P (by includes) LeanVM.Protocol.Verifier.gen j 7 (by norm_num)
    (by norm_num) (by omega)
  have := hS (.n 2) (by idx_lt); have := hS (.n 33) (by idx_lt); have := hS (.n 17) (by idx_lt); have := hS (.n 18) (by idx_lt)
  have := hS (.n 19) (by idx_lt); have := hS (.n 20) (by idx_lt); have := hS (.n 1) (by idx_lt)
  omega

/-- **Column `j`'s valuation** (`dvColVNC`) at `a`, `j < 128`: `F + 8·S + 4378`. -/
theorem dvColVN_costK (hP : Includes P dvColVNKC.costDeps) (j : ℕ) (hj : j < 128) (a : V) (ha : a.idx < 2 ^ 64) :
    machineCost P dvColVNKC.costIdx [σV, VnV, encodeValue j, encodeValue a] ≤
      F + 9 * S + 4520 := by
  rw [dvColVNKC.costEq P hP σ σV hσ Vn VnV hVn]
  have := dvColArgs_costK P hσ hS (by includes) j hj
  have := hF 31 (dvColArgsK σ j) [] a (by norm_num) ha (by simp [dvColArgsK])
  omega

/-- **Column `j`'s two words** (`dvColWordsC`), its frame looked up once per word, `j < 128`:
`2·F + 16·S + 8801`. -/
theorem dvColWords_costK (hP : Includes P dvColWordsKC.costDeps) (j : ℕ) (hj : j < 128) :
    machineCost P dvColWordsKC.costIdx [σV, VnV, encodeValue j] ≤
      2 * F + 18 * S + 9100 := by
  have hv : ∀ v : V, RunsApp P (.closure dvColWordsKC.lam0.costIdx
      [σV, VnV, encodeValue j]) [encodeValue v] (encodeValue (dvColVNK σ Vn j v)) :=
    fun v ↦ RunsApp.of_spec (dvColWordsKC.lam0.costSpec P (by includes) σ σV hσ Vn VnV hVn
      j v)
  rw [dvColWordsKC.costEq P hP σ σV hσ Vn VnV hVn,
    colWordsOfKC.costEq P (by includes) _ _ hv]
  have h : ∀ v : V, v.idx < 2 ^ 64 → appCost P (.closure dvColWordsKC.lam0.costIdx
      [σV, VnV, encodeValue j]) [encodeValue v] ≤ F + 9 * S + 4530 := fun v hv ↦ by
    rw [appCost_fn, List.cons_append, List.cons_append, List.cons_append, List.nil_append,
      dvColWordsKC.lam0.costEq P (by includes) σ σV hσ Vn VnV hVn, List.length_cons, List.length_cons, List.length_cons, List.length_nil]
    have := dvColVN_costK P hVn hF hσ hS (by includes) j hj v hv
    omega
  have := h (.n 14) (by idx_lt); have := h (.n 15) (by idx_lt)
  omega

/-- **The `128` columns' words** (`dvColsC`), each column's frame looked up once:
`256·F + 2048·S + 1131026`. -/
theorem dvCols_costK (hP : Includes P dvColsKC.costDeps) :
    machineCost P dvColsKC.costIdx [σV, VnV] ≤ 256 * F + 2304 * S + 1170000 := by
  rw [dvColsKC.costEq P hP σ σV hσ Vn VnV hVn, List.length_map, List.length_range]
  have m := rangeMap_le P (by includes) (by includes) _
    (.closure dvColsKC.lam0.costIdx [σV, VnV])
    (fun j ↦ RunsApp.of_spec (dvColsKC.lam0.costSpec P (by includes) σ σV hσ Vn VnV hVn j))
    (2 * F + 18 * S + 9106) 128 128 le_rfl (by norm_num) (fun j hj ↦ by
      rw [appCost_fn, List.cons_append, List.cons_append, List.nil_append,
        dvColsKC.lam0.costEq P (by includes) σ σV hσ Vn VnV hVn, List.length_cons, List.length_cons, List.length_nil]
      have := dvColWords_costK P hVn hF hσ hS (by includes) j hj
      omega)
  omega

/-- **Row `i`'s valuation in column `j`** (`dvRowVWC`) at `a`, the column's words `cw` given,
`i < 2^k`, `k ≤ 34`, `j < 128`: `F + 3·S + 73·k + 607`. -/
theorem dvRowVW_costK (hP : Includes P dvRowVWKC.costDeps) (cw : E × E) (k i j : ℕ)
    (hk0 : 0 < k) (hk : k ≤ 34) (hi : i < 2 ^ k) (hj : j < 128) (a : V) (ha : a.idx < 2 ^ 64) :
    machineCost P dvRowVWKC.costIdx
      [σV, VnV, encodeValue cw, encodeValue i, encodeValue j, encodeValue a] ≤
        F + 4 * S + 73 * k + 700 := by
  rw [dvRowVWKC.costEq P hP σ σV hσ Vn VnV hVn]
  have := powSqK_cost_lt P (by includes) Parameters.g i k hk0 (by omega) hi
  have := powSqK_cost_lt P (by includes) Parameters.g j 7 (by norm_num) (by norm_num) (by omega)
  have := hS (.n 1) (by idx_lt); have := hS (.n 2) (by idx_lt); have := hS (.n 33) (by idx_lt)
  have := hF 394 [ofK (Parameters.g ^ i), σ (.n 2), cw.1, σ (.n 1), σ (.n 33), ofK (Parameters.g ^ j),
    cw.2] [] a (by norm_num) ha (by simp)
  omega

/-- **Cell `(i, j)`'s symbols** (`dvSymsCellC`), the column's words given, its row's frame looked
up once, `i < 2^k`, `k ≤ 34`, `j < 128`: `259·F + 9·S + 219·k + 14735`. -/
theorem dvSymsCell_costK (hP : Includes P dvSymsCellKC.costDeps) (cw : E × E) (k i j : ℕ)
    (hk0 : 0 < k) (hk : k ≤ 34) (hi : i < 2 ^ k) (hj : j < 128) :
    machineCost P dvSymsCellKC.costIdx
      [σV, VnV, encodeValue cw, encodeValue i, encodeValue j] ≤
        259 * F + 14 * S + 219 * k + 16500 := by
  rw [dvSymsCellKC.costEq P hP σ σV hσ Vn VnV hVn]
  have hrow : ∀ v : V, RunsApp P (.closure dvSymsCellKC.lam0.costIdx
      [σV, VnV, encodeValue cw, encodeValue i, encodeValue j]) [encodeValue v]
      (encodeValue (dvRowVWK σ Vn cw i j v)) :=
    fun v ↦ RunsApp.of_spec (dvSymsCellKC.lam0.costSpec P (by includes) σ σV hσ Vn VnV hVn
      cw i j v)
  have hRw : ∀ v : V, v.idx < 2 ^ 64 → appCost P (.closure dvSymsCellKC.lam0.costIdx
      [σV, VnV, encodeValue cw, encodeValue i, encodeValue j]) [encodeValue v] ≤
        F + 4 * S + 73 * k + 712 := fun v hv ↦ by
    rw [appCost_fn, List.cons_append, List.cons_append, List.cons_append, List.cons_append,
      List.cons_append, List.nil_append,
      dvSymsCellKC.lam0.costEq P (by includes) σ σV hσ Vn VnV hVn, List.length_cons, List.length_cons, List.length_cons, List.length_cons, List.length_cons, List.length_nil]
    have := dvRowVW_costK P hVn hF hσ hS (by includes) cw k i j hk0 hk hi hj v hv
    omega
  have := cellSymsAt_costK P hVn hF (by includes) cw.1 (σ (.n 1)) hrow hRw
  have := hS (.n 1) (by idx_lt)
  omega

/-- **A cell of the padded matrix** of `r ≤ 2^k` rows (`dvSymsColsC`), `k ≤ 34`, any columns'
words: at most `259·F + 9·S + 219·k + 14768`. -/
theorem dvSymsCols_costK (hP : Includes P dvSymsColsKC.costDeps) (cols : Array (E × E))
    (k r i j : ℕ) (hk0 : 0 < k) (hk : k ≤ 34) (hr : r ≤ 2 ^ k) (hi : i < 2 ^ 64)
    (hj : j < 2 ^ 64) :
    machineCost P dvSymsColsKC.costIdx
      [encodeValue r, σV, VnV, encodeValue cols, encodeValue i, encodeValue j] ≤
        259 * F + 14 * S + 219 * k + 16533 := by
  have h2 : 2 ^ k ≤ 2 ^ 34 := Nat.pow_le_pow_right (by norm_num) hk
  rw [dvSymsColsKC.costEq P hP r σ σV hσ Vn VnV hVn,
    limbs_of_lt (by omega : r < 2 ^ 64), limbs_of_lt hi, limbs_of_lt hj]
  have := replicate_cost P (by includes) (0 : K) 256 (by norm_num)
  split_ifs with h1 h2'
  · have := dvSymsCell_costK P hVn hF hσ hS (by includes) (cols.getD j (0, 0)) k i j hk0 hk
      (by omega) h2'.2
    omega
  · omega
  · omega
  · omega

/-- The witness's price, its columns' words given, at `r ≤ 2^k` rows. -/
@[expose] def dvWitNColsPriceK (k F S : ℕ) : ℕ :=
  (33152 * F + 1792 * S + 28032 * k + 2483890) * 2 ^ k + 100

/-- **`da_verify`'s witness, its columns' words given** (`dvWitNColsC`), `r ≤ 2^k` rows,
`0 < k ≤ 34`: at most `dvWitNColsPriceK k F S`. -/
theorem dvWitNCols_costK (hP : Includes P dvWitNColsKC.costDeps) (cols : Array (E × E))
    (k r : ℕ) (hk0 : 0 < k) (hk : k ≤ 34) (hr : r ≤ 2 ^ k) :
    machineCost P dvWitNColsKC.costIdx [encodeValue r, σV, VnV, encodeValue cols] ≤
      dvWitNColsPriceK k F S := by
  have h2 : 2 ^ k ≤ 2 ^ 34 := Nat.pow_le_pow_right (by norm_num) hk
  rw [dvWitNColsKC.costEq P hP r σ σV hσ Vn VnV hVn]
  have hrows := daRows_cost P (by includes) (dvSymsColsK r σ Vn cols)
    (.closure dvWitNColsKC.lam0.costIdx [encodeValue r, σV, VnV, encodeValue cols])
    (fun i j ↦ RunsApp.of_spec (dvWitNColsKC.lam0.costSpec P (by includes) r σ σV hσ Vn
      VnV hVn cols i j))
    (259 * F + 14 * S + 219 * k + 16544) r (2 ^ k) hr (by omega)
    (fun i hi j hj ↦ by
      rw [appCost_fn, List.cons_append, List.cons_append, List.cons_append, List.cons_append,
        List.nil_append, dvWitNColsKC.lam0.costEq P (by includes) r σ σV hσ Vn VnV hVn, List.length_cons, List.length_cons, List.length_cons, List.length_cons, List.length_nil]
      have := dvSymsCols_costK P hVn hF hσ hS (by includes) cols k r i j hk0 hk hr (by omega)
        (by omega)
      omega)
    (fun i j ↦ (length_dvSymsColsK r σ Vn cols i j).le)
  have e : ((259 * F + 14 * S + 219 * k + 16544 + 34) * 128 + 361906) * 2 ^ k =
      (33152 * F + 1792 * S + 28032 * k + 2483890) * 2 ^ k := by ring
  unfold dvWitNColsPriceK
  omega

/-- The witness's price at `r ≤ 2^k` rows. -/
@[expose] def dvWitNRowsPriceK (k F S : ℕ) : ℕ :=
  (33152 * F + 1792 * S + 28032 * k + 2483890) * 2 ^ k + 256 * F + 2304 * S + 1170200

/-- The witness's price at `r ≤ 2^34` rows. -/
@[expose] def dvWitNAtPriceK (F S : ℕ) : ℕ := dvWitNRowsPriceK 34 F S

/-- **`da_verify`'s witness at `r ≤ 2^k` rows** (`dvWitNAtC`), `0 < k ≤ 34`: the columns' words
built once, then the witness: at most `dvWitNRowsPriceK k F S`. -/
theorem dvWitNAt_costK (hP : Includes P dvWitNAtKC.costDeps) (k r : ℕ) (hk0 : 0 < k)
    (hk : k ≤ 34) (hr : r ≤ 2 ^ k) :
    machineCost P dvWitNAtKC.costIdx [encodeValue r, σV, VnV] ≤ dvWitNRowsPriceK k F S := by
  rw [dvWitNAtKC.costEq P hP r σ σV hσ Vn VnV hVn]
  have := dvCols_costK P hVn hF hσ hS (by includes)
  have := dvWitNCols_costK P hVn hF hσ hS (by includes) (dvColsK σ Vn) k r hk0 hk hr
  unfold dvWitNColsPriceK at this
  unfold dvWitNRowsPriceK
  omega

/-- **`da_verify`'s witness at `r ≤ 2^k` rows** (`dvWitNC`), the logarithm's tables `D` given:
one logarithm, the count clamped to `1024` (`daRowCount`), then the rows: at most
`S + G + dvWitNRowsPriceK k F S + 22`. -/
theorem dvWitN_cost_of_leK (D : LeanVM.Extraction.Fast.DiscreteLogTables)
    (hP : Includes P dvWitNDKC.costDeps) (hG : GLogBound P D G) (k : ℕ) (hk0 : 0 < k)
    (hk : k ≤ 34) (hr : Decoder.daRowCount (Decoder.gLogD D (σ (.n 2))) ≤ 2 ^ k) :
    machineCost P dvWitNDKC.costIdx [encodeValue D, σV, VnV] ≤
      S + G + dvWitNRowsPriceK k F S + 22 := by
  rw [dvWitNDKC.costEq P hP D σ σV hσ Vn VnV hVn]
  have := hG (σ (.n 2))
  have := hS (.n 2) (by idx_lt)
  have := daRowCount_cost P (by includes) (Decoder.gLogD D (σ (.n 2)))
    (by have := gLogD_lt D (σ (.n 2)); omega)
  have := dvWitNAt_costK P hVn hF hσ hS (by includes) k _ hk0 hk hr
  omega

/-- **`da_verify`'s witness** (`dvWitNC`), the logarithm's tables `D` given: one logarithm, the
rows at most `1024` (`daRowCount_le`, on every input): at most
`S + G + dvWitNRowsPriceK 10 F S + 22`. -/
theorem dvWitN_cost_1024K (D : LeanVM.Extraction.Fast.DiscreteLogTables)
    (hP : Includes P dvWitNDKC.costDeps) (hG : GLogBound P D G) :
    machineCost P dvWitNDKC.costIdx [encodeValue D, σV, VnV] ≤
      S + G + dvWitNRowsPriceK 10 F S + 22 :=
  dvWitN_cost_of_leK P hVn hF hσ hS D hP hG 10 (by norm_num) (by norm_num)
    ((Decoder.daRowCount_le _).trans (by norm_num))

/-- **`da_verify`'s witness** (`dvWitNC`), the logarithm's tables `D` given: at most
`S + G + dvWitNAtPriceK F S + 14` (`dvWitN_cost_1024K`, below the price at `2^34` rows). -/
theorem dvWitN_costK (D : LeanVM.Extraction.Fast.DiscreteLogTables)
    (hP : Includes P dvWitNDKC.costDeps) (hG : GLogBound P D G) :
    machineCost P dvWitNDKC.costIdx [encodeValue D, σV, VnV] ≤
      S + G + dvWitNAtPriceK F S + 14 := by
  have := dvWitN_cost_1024K P hVn hF hσ hS D hP hG
  have e : dvWitNRowsPriceK 10 F S + 8 ≤ dvWitNAtPriceK F S := by
    unfold dvWitNAtPriceK dvWitNRowsPriceK
    norm_num
    nlinarith
  omega

end Val

end Frames

end

end LeanVM.SaltedGuest.Bounds
