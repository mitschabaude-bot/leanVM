/-
  LeanVM.SaltedGuest.Bounds.ReadersK

  The prices of the salted decoder's witness readers, as the closures its frames stage passes.
-/

module

public import LeanVM.SaltedGuest.Bounds.ClosuresK
public import LeanVM.Cost.Bounds.Decoder.Cursor

/-!
# The prices of the salted witness readers

The closures `decTopFramesKC.lam0` … `lam4` (`Decoder/Top.lean`), in the price `R` of the
memory's reader and the exponent `e` of the entry table's size, each frame lookup at most
`frameK e R` (`ClosuresK.lean`):

* the leanXMSS signature `__loop2`'s iteration checks (`xmssAtFrameTK`): `xmssReaderK e R`;
* the leanSPHINCS signature `verify_sig_lean_sphincs` checks (`sphincsAtFrameTK`): `sphincsReaderK e R`;
* the DA matrix (`daAtFrameK`): `daReaderK e R`, its rows at most `1024`;
* a child's proof (`proofAtFrameK`): `proofReaderK e R`, its cursor at most `2^32` words;
* the batching's hints (`hintsAtFrameK`): `hintsReaderK e R`.
-/

namespace LeanVM.SaltedGuest.Bounds

open LeanVM.Cost.Bounds.Guest LeanVM.SaltedGuest.Decoder LeanVM.Cost LeanVM.Cost.Bounds
open LeanVM.Cost.Library LeanVM.Parameters LeanVM.Guest.Core LeanVM.Guest.B1 LeanVM.Guest.Fast
open LeanVM.Extraction.Fast LeanVM.Guest.Located

public section

attribute [local instance] lexOrd

/-- The leanXMSS reader's price. -/
@[expose] def xmssReaderK (e R : ℕ) : ℕ := frameK e R + xmssPrice (R + 1310) + 40

/-- The leanSPHINCS reader's price. -/
@[expose] def sphincsReaderK (e R : ℕ) : ℕ := 4 * frameK e R + 1507 * (R + 1310) + 351600

/-- The DA reader's price. -/
@[expose] def daReaderK (e R : ℕ) : ℕ :=
  (frameK e R + 20) + gLogPrice + dvWitNRowsPriceK 10 (frameK e R) (frameK e R + 20) + 300

/-- The child proof reader's price, the cursor at most `2^32` words. -/
@[expose] def proofReaderK (e R : ℕ) : ℕ :=
  vsPiPriceK R (frameK e R + 20) (frameK e R) (125634 + 5) (2 ^ 32) + 60

/-- The batching hints' reader's price. -/
@[expose] def hintsReaderK (e R : ℕ) : ℕ := 48 * (frameK e R + 20) + 46 * R + 140000

variable (P : MachineProgram)

section Reader

variable {rd : Reader} {rdV : MachineValue}
  (hrd : ∀ a : K, RunsApp P rdV [encodeValue a] (encodeValue (rd a)))
  {R : ℕ} (hR : ∀ a : K, appCost P rdV [encodeValue a] ≤ R)
  {table : Array (CallKey × K)} {e : ℕ} (ht : ∀ x ∈ table, KeyOK 56 x.1)
  (hs : table.size ≤ 2 ^ e)
include hrd

/-! ## The signatures -/

theorem xmssClosure_runsK (hP : Includes P decTopFramesKC.lam0.costDeps) (args : List E) :
    RunsApp P (.closure decTopFramesKC.lam0.costIdx [encodeValue readerTabs,
      encodeValue locsTableK, rdV, encodeValue table]) [encodeValue args]
      (encodeValue (xmssAtFrameTK readerTabs table locsTableK rd args)) :=
  RunsApp.of_spec (decTopFramesKC.lam0.costSpec P hP readerTabs locsTableK rd rdV hrd table args)

include hR ht hs

/-- **The leanXMSS reader** (`decTopFramesKC.lam0`), on at most `56` words: `xmssReaderK e R`. -/
theorem xmssClosure_costK (hP : Includes P decTopFramesKC.lam0.costDeps) (args : List E)
    (hargs : args.length ≤ 56) :
    appCost P (.closure decTopFramesKC.lam0.costIdx [encodeValue readerTabs,
      encodeValue locsTableK, rdV, encodeValue table]) [encodeValue args] ≤ xmssReaderK e R := by
  rw [appCost_fn, List.cons_append, List.cons_append, List.cons_append, List.cons_append,
    List.nil_append, decTopFramesKC.lam0.costEq P hP readerTabs locsTableK rd rdV hrd,
    xmssAtFrameTKC.costEq P (by includes) readerTabs table locsTableK rd rdV hrd args]
  have hs' : ∀ v : V, RunsApp P (.closure xmssAtFrameTKC.lam0.costIdx [encodeValue locsTableK,
      rdV, encodeValue (frameFpAK table 39 args [])]) [encodeValue v]
      (encodeValue (frameValAtK locsTableK rd (frameFpAK table 39 args []) 39 v)) :=
    fun v ↦ RunsApp.of_spec (xmssAtFrameTKC.lam0.costSpec P (by includes) locsTableK rd rdV hrd _ v)
  have hS' : ∀ v : V, v.idx < 2 ^ 64 → appCost P (.closure xmssAtFrameTKC.lam0.costIdx
      [encodeValue locsTableK, rdV, encodeValue (frameFpAK table 39 args [])]) [encodeValue v] ≤
        R + 1310 := fun v hv ↦ by
    rw [appCost_fn, List.cons_append, List.cons_append, List.cons_append, List.nil_append,
      xmssAtFrameTKC.lam0.costEq P (by includes) locsTableK rd rdV hrd]
    have := frameValAtK_le P hrd hR (by includes) (frameFpAK table 39 args []) 39 v hv
    simp only [List.length_cons, List.length_nil]
    omega
  have h1 := xmssSigOfN_costK P hs' hS' (by includes) readerTabs.xmss readerTabs_ok.xmss
  have h2 := frameFpAK_le P e table ht hs (by includes) 39 (by norm_num) args []
    (by simp only [List.length_nil]; omega) R
  simp only [List.length_cons, List.length_nil]
  unfold xmssReaderK
  omega

omit hR ht hs in
theorem spFrame_runs (hP : Includes P sphincsAtFpKC.lam0.costDeps) (o : Option K) (v : V) :
    RunsApp P (.closure sphincsAtFpKC.lam0.costIdx [encodeValue locsTableK, rdV, encodeValue o])
      [encodeValue v] (encodeValue (frameValAtK locsTableK rd o 21 v)) :=
  RunsApp.of_spec (sphincsAtFpKC.lam0.costSpec P hP locsTableK rd rdV hrd o v)

omit ht hs in
theorem spFrame_cost (hP : Includes P sphincsAtFpKC.lam0.costDeps) (o : Option K) (v : V)
    (hv : v.idx < 2 ^ 64) :
    appCost P (.closure sphincsAtFpKC.lam0.costIdx [encodeValue locsTableK, rdV, encodeValue o])
      [encodeValue v] ≤ R + 1310 := by
  rw [appCost_fn, List.cons_append, List.cons_append, List.cons_append, List.nil_append,
    sphincsAtFpKC.lam0.costEq P hP locsTableK rd rdV hrd]
  have := frameValAtK_le P hrd hR (by includes) o 21 v hv
  simp only [List.length_cons, List.length_nil]
  omega

omit hR ht hs in
theorem spWots_runs (hP : Includes P sphincsAtFpKC.lam1.costDeps) (o : Option K) (v : V) :
    RunsApp P (.closure sphincsAtFpKC.lam1.costIdx [encodeValue locsTableK, rdV, encodeValue o])
      [encodeValue v] (encodeValue (frameValAtK locsTableK rd o 20 v)) :=
  RunsApp.of_spec (sphincsAtFpKC.lam1.costSpec P hP locsTableK rd rdV hrd o v)

omit ht hs in
theorem spWots_cost (hP : Includes P sphincsAtFpKC.lam1.costDeps) (o : Option K) (v : V)
    (hv : v.idx < 2 ^ 64) :
    appCost P (.closure sphincsAtFpKC.lam1.costIdx [encodeValue locsTableK, rdV, encodeValue o])
      [encodeValue v] ≤ R + 1310 := by
  rw [appCost_fn, List.cons_append, List.cons_append, List.cons_append, List.nil_append,
    sphincsAtFpKC.lam1.costEq P hP locsTableK rd rdV hrd]
  have := frameValAtK_le P hrd hR (by includes) o 20 v hv
  simp only [List.length_cons, List.length_nil]
  omega

/-- The leanSPHINCS signature off `verify_sig_lean_sphincs`' frame pointer (`sphincsAtFpKC`). -/
theorem sphincsAtFpK_costK (hP : Includes P sphincsAtFpKC.costDeps) (o : Option K) :
    machineCost P sphincsAtFpKC.costIdx [encodeValue readerTabs, encodeValue table,
      encodeValue locsTableK, rdV, encodeValue o] ≤
        3 * frameK e R + 1507 * (R + 1310) + 351400 := by
  rw [sphincsAtFpKC.costEq P hP readerTabs table locsTableK rd rdV hrd o]
  have hs0 := spFrame_runs P hrd (by includes) o
  have hS0 := spFrame_cost P hrd hR (by includes) o
  have a0 := spWotsArgs_costK P hs0 hS0 (by includes) 0 (by norm_num)
  have a1 := spWotsArgs_costK P hs0 hS0 (by includes) 1 (by norm_num)
  have a2 := spWotsArgs_costK P hs0 hS0 (by includes) 2 (by norm_num)
  have r0 := spWotsRets_costK P hs0 hS0 (by includes) 0 (by norm_num)
  have r1 := spWotsRets_costK P hs0 hS0 (by includes) 1 (by norm_num)
  have r2 := spWotsRets_costK P hs0 hS0 (by includes) 2 (by norm_num)
  have f0 := frameFpAK_le P e table ht hs (by includes) 20 (by norm_num)
    (spWotsArgs (frameValAtK locsTableK rd o 21) 0) (spWotsRets (frameValAtK locsTableK rd o 21) 0)
    (by simp [spWotsArgs, spWotsRets]) R
  have f1 := frameFpAK_le P e table ht hs (by includes) 20 (by norm_num)
    (spWotsArgs (frameValAtK locsTableK rd o 21) 1) (spWotsRets (frameValAtK locsTableK rd o 21) 1)
    (by simp [spWotsArgs, spWotsRets]) R
  have f2 := frameFpAK_le P e table ht hs (by includes) 20 (by norm_num)
    (spWotsArgs (frameValAtK locsTableK rd o 21) 2) (spWotsRets (frameValAtK locsTableK rd o 21) 2)
    (by simp [spWotsArgs, spWotsRets]) R
  have sg := sphincsSigOfA_costK P hs0 hS0 (by includes) readerTabs.sphincs readerTabs_ok.sphincs
    (spWots_runs P hrd (by includes) (frameFpAK table 20 (spWotsArgs (frameValAtK locsTableK rd o 21) 0)
      (spWotsRets (frameValAtK locsTableK rd o 21) 0)))
    (spWots_cost P hrd hR (by includes) (frameFpAK table 20 (spWotsArgs (frameValAtK locsTableK rd o 21) 0)
      (spWotsRets (frameValAtK locsTableK rd o 21) 0)))
    (spWots_runs P hrd (by includes) (frameFpAK table 20 (spWotsArgs (frameValAtK locsTableK rd o 21) 1)
      (spWotsRets (frameValAtK locsTableK rd o 21) 1)))
    (spWots_cost P hrd hR (by includes) (frameFpAK table 20 (spWotsArgs (frameValAtK locsTableK rd o 21) 1)
      (spWotsRets (frameValAtK locsTableK rd o 21) 1)))
    (spWots_runs P hrd (by includes) (frameFpAK table 20 (spWotsArgs (frameValAtK locsTableK rd o 21) 2)
      (spWotsRets (frameValAtK locsTableK rd o 21) 2)))
    (spWots_cost P hrd hR (by includes) (frameFpAK table 20 (spWotsArgs (frameValAtK locsTableK rd o 21) 2)
      (spWotsRets (frameValAtK locsTableK rd o 21) 2)))
  omega

omit hR ht hs in
theorem sphincsClosure_runsK (hP : Includes P decTopFramesKC.lam1.costDeps) (w47 p : E) :
    RunsApp P (.closure decTopFramesKC.lam1.costIdx [encodeValue readerTabs,
      encodeValue locsTableK, rdV, encodeValue table, encodeValue w47]) [encodeValue p]
      (encodeValue (sphincsAtFrameTK readerTabs table locsTableK rd w47 p)) :=
  RunsApp.of_spec (decTopFramesKC.lam1.costSpec P hP readerTabs locsTableK rd rdV hrd table w47 p)

/-- **The leanSPHINCS reader** (`decTopFramesKC.lam1`): `sphincsReaderK e R`. -/
theorem sphincsClosure_costK (hP : Includes P decTopFramesKC.lam1.costDeps) (w47 p : E) :
    appCost P (.closure decTopFramesKC.lam1.costIdx [encodeValue readerTabs,
      encodeValue locsTableK, rdV, encodeValue table, encodeValue w47]) [encodeValue p] ≤
        sphincsReaderK e R := by
  rw [appCost_fn, List.cons_append, List.cons_append, List.cons_append, List.cons_append,
    List.cons_append, List.nil_append,
    decTopFramesKC.lam1.costEq P hP readerTabs locsTableK rd rdV hrd,
    sphincsAtFrameTKC.costEq P (by includes) readerTabs table locsTableK rd rdV hrd w47 p]
  have h1 := frameFpAK_le P e table ht hs (by includes) 21 (by norm_num) [p, w47] [] (by simp) R
  have h2 := sphincsAtFpK_costK P hrd hR ht hs (by includes) (frameFpAK table 21 [p, w47] [])
  simp only [List.length_cons, List.length_nil]
  unfold sphincsReaderK
  omega


/-! ## The frame map's consumers -/

/-- The frame map, priced at every call of at most `64` words (`frameV_cost`), restricted. -/
theorem frameV_le (hP : Includes P decTopFramesKC.lam2.lam0.costDeps) (n : ℕ) (hn : n ≤ 64) :
    ∀ (k : ℕ) (a r : List E) (v : V), k < 2 ^ 64 → v.idx < 2 ^ 64 → a.length + r.length ≤ n →
      appCost P (.closure decTopFramesKC.lam2.lam0.costIdx [encodeValue locsTableK, rdV,
        encodeValue table]) [encodeValue k, encodeValue a, encodeValue r, encodeValue v] ≤
          frameK e R :=
  fun k a r v hk hv hl ↦ frameV_cost P hrd hR e table ht hs hP k a r v hk hv (by omega)

omit hR ht hs in
theorem daClosure_runsK (D : DiscreteLogTables) (hP : Includes P decTopFramesKC.lam2.costDeps)
    (key : E) (args rets : List E) :
    RunsApp P (.closure decTopFramesKC.lam2.costIdx [encodeValue D, encodeValue locsTableK, rdV,
      encodeValue table, encodeValue key]) [encodeValue args, encodeValue rets]
      (encodeValue (daAtFrameK D (frameAtAK table locsTableK rd) key args rets)) :=
  RunsApp.of_spec (decTopFramesKC.lam2.costSpec P hP D locsTableK rd rdV hrd table key args rets)

/-- **The DA reader** (`decTopFramesKC.lam2`), the call of at most `16` words: `daReaderK e R`. -/
theorem daClosure_costK (D : DiscreteLogTables) (hG : GLogBound P D gLogPrice)
    (hP : Includes P decTopFramesKC.lam2.costDeps) (key : E) (args rets : List E)
    (hl : args.length + rets.length ≤ 16) :
    appCost P (.closure decTopFramesKC.lam2.costIdx [encodeValue D, encodeValue locsTableK, rdV,
      encodeValue table, encodeValue key]) [encodeValue args, encodeValue rets] ≤
        daReaderK e R := by
  rw [appCost_fn, List.cons_append, List.cons_append, List.cons_append, List.cons_append,
    List.cons_append, List.nil_append,
    decTopFramesKC.lam2.costEq P hP D locsTableK rd rdV hrd,
    daAtFrameKC.costEq P (by includes) D _ _ (frameV_runs P hrd table (by includes)) key args rets]
  have hσ : ∀ v : V, RunsApp P (.closure daAtFrameKC.lam0.costIdx
      [.closure decTopFramesKC.lam2.lam0.costIdx [encodeValue locsTableK, rdV, encodeValue table],
        encodeValue rets, encodeValue (args ++ [key])]) [encodeValue v]
      (encodeValue (frameAtAK table locsTableK rd 28 (args ++ [key]) rets v)) :=
    fun v ↦ RunsApp.of_spec (daAtFrameKC.lam0.costSpec P (by includes) _ _
      (frameV_runs P hrd table (by includes)) rets (args ++ [key]) v)
  have hS : ∀ v : V, v.idx < 2 ^ 64 → appCost P (.closure daAtFrameKC.lam0.costIdx
      [.closure decTopFramesKC.lam2.lam0.costIdx [encodeValue locsTableK, rdV, encodeValue table],
        encodeValue rets, encodeValue (args ++ [key])]) [encodeValue v] ≤ frameK e R + 20 :=
    fun v hv ↦ by
      rw [appCost_fn, List.cons_append, List.cons_append, List.cons_append, List.nil_append,
        daAtFrameKC.lam0.costEq P (by includes) _ _ (frameV_runs P hrd table (by includes))]
      have := frameV_cost P hrd hR e table ht hs (by includes) 28 (args ++ [key]) rets v
        (by norm_num) hv (by simp only [List.length_append, List.length_cons, List.length_nil]; omega)
      simp only [List.length_cons, List.length_nil]
      omega
  have h1 := dvWitN_cost_1024K P (frameV_runs P hrd table (by includes))
    (frameV_le P hrd hR ht hs (by includes) 16 (by norm_num)) hσ hS D (by includes) hG
  have h2 := append_cost P (by includes) args [key]
  simp only [List.length_cons, List.length_nil]
  unfold daReaderK
  omega

omit hR ht hs in
theorem proofClosure_runsK (D : DiscreteLogTables) (hP : Includes P decTopFramesKC.lam3.costDeps)
    (args : List E) :
    RunsApp P (.closure decTopFramesKC.lam3.costIdx [encodeValue D, encodeValue whirTabsK,
      encodeValue locsTableK, rdV, encodeValue table]) [encodeValue args]
      (encodeValue (proofAtFrameK whirTabsK rd (frameAtAK table locsTableK rd) (Decoder.cursorLength D)
        args)) :=
  RunsApp.of_spec (decTopFramesKC.lam3.costSpec P hP D whirTabsK locsTableK rd rdV hrd table args)

/-- **The child proof reader** (`decTopFramesKC.lam3`) on the logarithm's tables built, the call
of at most `16` words: `proofReaderK e R`. -/
theorem proofClosure_costK (hP : Includes P decTopFramesKC.lam3.costDeps) (args : List E)
    (hl : args.length ≤ 16) :
    appCost P (.closure decTopFramesKC.lam3.costIdx [encodeValue discreteLogTables,
      encodeValue whirTabsK, encodeValue locsTableK, rdV, encodeValue table]) [encodeValue args] ≤
        proofReaderK e R := by
  rw [appCost_fn, List.cons_append, List.cons_append, List.cons_append, List.cons_append,
    List.cons_append, List.nil_append,
    decTopFramesKC.lam3.costEq P hP discreteLogTables whirTabsK locsTableK rd rdV hrd,
    proofAtFrameKC.costEq P (by includes) whirTabsK rd rdV hrd _ _
      (frameV_runs P hrd table (by includes)) _ _ (cursorClosure_runs P (by includes) _) args]
  have hσ : ∀ v : V, RunsApp P (.closure Decoder.proofAtFrameC.lam0.costIdx
      [.closure decTopFramesKC.lam2.lam0.costIdx [encodeValue locsTableK, rdV, encodeValue table],
        encodeValue args, encodeValue ([] : List E)]) [encodeValue v]
      (encodeValue (frameAtAK table locsTableK rd 19 args [] v)) :=
    fun v ↦ RunsApp.of_spec (Decoder.proofAtFrameC.lam0.costSpec P (by includes) _ _
      (frameV_runs P hrd table (by includes)) _ _ v)
  have hS : ∀ v : V, v.idx < 2 ^ 64 → appCost P (.closure Decoder.proofAtFrameC.lam0.costIdx
      [.closure decTopFramesKC.lam2.lam0.costIdx [encodeValue locsTableK, rdV, encodeValue table],
        encodeValue args, encodeValue ([] : List E)]) [encodeValue v] ≤ frameK e R + 20 :=
    fun v hv ↦ by
      rw [appCost_fn, List.cons_append, List.cons_append, List.cons_append, List.nil_append,
        Decoder.proofAtFrameC.lam0.costEq P (by includes) _ _ (frameV_runs P hrd table (by includes))]
      have := frameV_cost P hrd hR e table ht hs (by includes) 19 args [] v (by norm_num) hv
        (by simp only [List.length_nil]; omega)
      simp only [List.length_cons, List.length_nil]
      omega
  have hC := cursorClosure_cost P (by includes) discreteLogTables 125634
    (fun p q ↦ LeanVM.Cost.Bounds.cursorLength_cost P (by includes) discreteLogTables 122420
      (fun x ↦ discreteLogWith_cost P (by includes) x) discreteLogWith_lt p q)
  have h1 := vsPiOfN_costK P hrd hR hσ hS (frameV_runs P hrd table (by includes))
    (frameV_le P hrd hR ht hs (by includes) 24 (by norm_num))
    (cursorClosure_runs P (by includes) discreteLogTables) hC
    (LeanVM.Cost.Bounds.cursorLenWith_le _ _ _) le_rfl (by includes) whirTabsK whirTabsK_ok
  simp only [List.length_cons, List.length_nil]
  unfold proofReaderK
  omega

omit hR ht hs in
theorem hintsClosure_runsK (hP : Includes P decTopFramesKC.lam4.costDeps) (s0 s1 : E)
    (args : List E) :
    RunsApp P (.closure decTopFramesKC.lam4.costIdx [encodeValue locsTableK, rdV,
      encodeValue table, encodeValue s1, encodeValue s0]) [encodeValue args]
      (encodeValue (hintsAtFrameK rd (frameAtAK table locsTableK rd) s0 s1 args)) :=
  RunsApp.of_spec (decTopFramesKC.lam4.costSpec P hP locsTableK rd rdV hrd table s1 s0 args)

/-- **The batching hints' reader** (`decTopFramesKC.lam4`), the call of at most `16` words:
`hintsReaderK e R`. -/
theorem hintsClosure_costK (hP : Includes P decTopFramesKC.lam4.costDeps) (s0 s1 : E)
    (args : List E) (hl : args.length ≤ 16) :
    appCost P (.closure decTopFramesKC.lam4.costIdx [encodeValue locsTableK, rdV,
      encodeValue table, encodeValue s1, encodeValue s0]) [encodeValue args] ≤
        hintsReaderK e R := by
  rw [appCost_fn, List.cons_append, List.cons_append, List.cons_append, List.cons_append,
    List.cons_append, List.nil_append, decTopFramesKC.lam4.costEq P hP locsTableK rd rdV hrd,
    hintsAtFrameKC.costEq P (by includes) rd rdV hrd _ _ (frameV_runs P hrd table (by includes))]
  have hσ : ∀ v : V, RunsApp P (.closure hintsAtFrameKC.lam0.costIdx
      [.closure decTopFramesKC.lam2.lam0.costIdx [encodeValue locsTableK, rdV, encodeValue table],
        encodeValue ([s0, s1] ++ args), encodeValue ([] : List E)]) [encodeValue v]
      (encodeValue (frameAtAK table locsTableK rd 36 ([s0, s1] ++ args) [] v)) :=
    fun v ↦ RunsApp.of_spec (hintsAtFrameKC.lam0.costSpec P (by includes) _ _
      (frameV_runs P hrd table (by includes)) _ _ v)
  have hS : ∀ v : V, v.idx < 2 ^ 64 → appCost P (.closure hintsAtFrameKC.lam0.costIdx
      [.closure decTopFramesKC.lam2.lam0.costIdx [encodeValue locsTableK, rdV, encodeValue table],
        encodeValue ([s0, s1] ++ args), encodeValue ([] : List E)]) [encodeValue v] ≤
          frameK e R + 20 := fun v hv ↦ by
    simp only [appCost_fn, List.cons_append, List.nil_append, List.length_cons, List.length_nil]
    rw [hintsAtFrameKC.lam0.costEq P (by includes) _ _ (frameV_runs P hrd table (by includes))]
    have := frameV_cost P hrd hR e table ht hs (by includes) 36 (s0 :: s1 :: args) [] v
      (by norm_num) hv (by simp only [List.length_cons, List.length_nil]; omega)
    omega
  rw [aggHintsKC.costEq P (by includes) rd rdV hrd _ _ hσ,
    aggRoundsKC.costEq P (by includes) rd rdV hrd _ _ hσ]
  have hr := rangeLoop_cost P (by includes) 23 [] (by norm_num)
  have hm := map_cost P (by includes) _ _
    (fun k ↦ RunsApp.of_spec (aggRoundsKC.lam0.costSpec P (by includes) rd rdV hrd _ _ hσ k))
    (2 * (frameK e R + 20) + 2 * (R + 2969) + 60) (List.range 23) (fun k hk ↦ by
      rw [List.mem_range] at hk
      rw [appCost_fn, List.cons_append, List.cons_append, List.nil_append,
        aggRoundsKC.lam0.costEq P (by includes) rd rdV hrd _ _ hσ]
      have := memAt_cost P hrd hR (by includes) (frameAtAK table locsTableK rd 36 ([s0, s1] ++ args) [] (.n 7))
        (2 * k) (by omega)
      have := memAt_cost P hrd hR (by includes) (frameAtAK table locsTableK rd 36 ([s0, s1] ++ args) [] (.n 7))
        (2 * k + 1) (by omega)
      have := hS (.n 7) (by idx_lt)
      rw [limbs_of_lt (by omega : 2 * k < 2 ^ 64), limbs_of_lt (by omega : k < 2 ^ 64),
        limbs_of_lt (by omega : 2 * k + 1 < 2 ^ 64)]
      simp only [max_self, List.length_cons, List.length_nil]
      omega)
  have h8 := hS (.n 8) (by idx_lt)
  have ha := append_cost P (by includes) [s0, s1] args
  simp only [List.length_range, List.length_cons, List.length_nil] at hm ha ⊢
  unfold hintsReaderK
  omega

end Reader

end

end LeanVM.SaltedGuest.Bounds
