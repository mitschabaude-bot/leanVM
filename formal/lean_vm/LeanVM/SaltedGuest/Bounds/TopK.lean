/-
  LeanVM.SaltedGuest.Bounds.TopK

  The price of the salted decoder's compiled top, stage by stage.
-/

module

public import LeanVM.SaltedGuest.Bounds.ReadersK
public import LeanVM.SaltedGuest.Bounds.PcTableK
public import LeanVM.SaltedGuest.Bounds.PreTestK
public import LeanVM.Cost.Bounds.GuestReplay
public import LeanVM.Cost.Bounds.Decoder.DecoderEnds

/-!
# The price of the salted decoder's top

`Decoder/Top.lean`'s stages, each in the next one's and the replay's prices, the counts the
witness reads at most `16` children and `2^20` of each other count (`CountsWithin`):

* **`decTopFramesK_costK`**: the witness (`decWitC_costK` at the readers of `ReadersK.lean`) and
  the decoding: `framesPriceK e R`;
* **`decTopStatesK_costK`**: the entry table (`entryArrayTK_cost` at the salted pc table's lookup
  `7093`, two functions a pc, the salted precondition test): `statePriceK e · |states| +
  framesPriceK e R + 59`;
* **`decTopTablesK_costK`**: the replay (`replayStatesOf_cost`) and the states stage at the reader's
  price `1271` (`κ ≤ 30`);
* **`tablesK_cost`**: the salted tables built once (the preconditions, the entries, the argument and
  return counts, the packed frame cells): at most `tablesPriceK`.
-/

namespace LeanVM.SaltedGuest.Bounds

open LeanVM.Cost.Bounds.Guest LeanVM.SaltedGuest.Decoder LeanVM.Cost LeanVM.Cost.Bounds
open LeanVM.Cost.Library LeanVM.Parameters LeanVM.Guest.Core LeanVM.Guest.B1 LeanVM.Guest.Fast
open LeanVM.Extraction.Fast LeanVM.Guest.Located

public section

attribute [local instance] lexOrd

/-- The frames stage's price: `main`'s four words, the witness, the seed and the statement. -/
@[expose] def framesPriceK (e R : ℕ) : ℕ :=
  4 * (R + 1400) + decWitPrice gLogPrice R (R + 1400) (xmssReaderK e R) (sphincsReaderK e R)
    (daReaderK e R) (proofReaderK e R) (hintsReaderK e R) 16 (2 ^ 20) (2 ^ 20) +
    (2 * (R + 1400) + 45) + decStmtPrice gLogPrice R (R + 1400) (2 ^ 20) + 15 + 93

/-- The salted precondition test's price at the reader's `R`, as the closure the states stage
passes. -/
@[expose] def preK (R : ℕ) : ℕ := 269 * R + 99 * 706 + 24834 + 20

/-- The states stage's price per state: filing it in the sorted entry table. -/
@[expose] def statePriceK (e R : ℕ) : ℕ := entryArrayStatePriceK 7093 2 (preK R) R e

variable (P : MachineProgram)

section Reader

variable {rd : Reader} {rdV : MachineValue}
  (hrd : ∀ a : K, RunsApp P rdV [encodeValue a] (encodeValue (rd a)))
  {R : ℕ} (hR : ∀ a : K, appCost P rdV [encodeValue a] ≤ R)
include hrd hR

/-- **The frames stage** (`decTopFramesKC`), the entry table sorted of at most `2^e` pairs, the
counts within `16`, `2^20`, `2^20`: at most `framesPriceK e R`. -/
theorem decTopFramesK_costK (hP : Includes P decTopFramesKC.costDeps)
    (hP0 : Includes P decTopStatesKC.lam0.costDeps) (hP1 : Includes P decTopStatesKC.lam1.costDeps)
    {table : Array (CallKey × K)}
    {e : ℕ} (ht : ∀ x ∈ table, KeyOK 56 x.1) (hs : table.size ≤ 2 ^ e)
    (hc : CountsWithin discreteLogTables (mainValDK locsTableK rd) 16 (2 ^ 20) (2 ^ 20)) :
    machineCost P decTopFramesKC.costIdx [encodeValue discreteLogTables, encodeValue readerTabs,
      encodeValue whirTabsK, encodeValue locsTableK, rdV,
      .closure decTopStatesKC.lam0.costIdx [encodeValue locsTableK, rdV],
      .closure decTopStatesKC.lam1.costIdx [encodeValue locsTableK, rdV], encodeValue table] ≤
        framesPriceK e R := by
  have hσs := valS_runs P hrd hP0
  have hσ := valD_runs P hrd hP1
  have hS := valD_cost P hrd hR hP1
  rw [decTopFramesKC.costEq P hP discreteLogTables readerTabs whirTabsK locsTableK rd rdV hrd _ _
    hσs _ _ hσ table]
  have s47 := hS (.n 47) (by idx_lt)
  have s27 := hS (.n 27) (by idx_lt)
  have s26 := hS (.n 26) (by idx_lt)
  have t38 := valS_cost P hrd hR hP0 (.n 38) (by idx_lt)
  have hG := gLog_bound P (by includes)
  have hW := decWitC_costK P hrd hR hσ hS (xmssClosure_runsK P hrd (by includes))
    (fun a ha ↦ xmssClosure_costK P hrd hR ht hs (by includes) a ha)
    (sphincsClosure_runsK P hrd (by includes) (mainValDK locsTableK rd (.n 47)))
    (fun p ↦ sphincsClosure_costK P hrd hR ht hs (by includes) (mainValDK locsTableK rd (.n 47)) p)
    (daClosure_runsK P hrd discreteLogTables (by includes) (mainValK locsTableK rd (.n 38)))
    (fun a b hl ↦ daClosure_costK P hrd hR ht hs discreteLogTables hG (by includes) (mainValK locsTableK rd (.n 38)) a b hl)
    (proofClosure_runsK P hrd discreteLogTables (by includes))
    (hintsClosure_runsK P hrd (by includes) (mainValDK locsTableK rd (.n 26))
      (mainValDK locsTableK rd (.n 27)))
    (fun a ha ↦ hintsClosure_costK P hrd hR ht hs (by includes) (mainValDK locsTableK rd (.n 26))
      (mainValDK locsTableK rd (.n 27)) a ha)
    discreteLogTables (by includes) hG hc
    (fun c _ ↦ proofClosure_costK P hrd hR ht hs (by includes) _ (by simp [Decoder.subArgsK]))
  have hO : ∀ w : LeanVM.Node.NodeWitness, machineCost P Decoder.decoderOutputC.costIdx
      [encodeValue discreteLogTables, .closure decTopStatesKC.lam1.costIdx [encodeValue locsTableK, rdV],
        rdV, encodeValue w] ≤
        (2 * (R + 1400) + 45) + decStmtPrice gLogPrice R (R + 1400) (2 ^ 20) + 15 := fun w ↦
    decoderOutput_cost P (by includes) discreteLogTables _ _ hσ rd rdV hrd w _ _
      (decSeed_costK P hσ hS (by includes))
      (decStmt_costK P hσ hS hrd hR discreteLogTables (by includes) hG (2 ^ 20) hc.xmssClaims
        hc.sphincsClaims)
  cost_facts [hO]
  unfold framesPriceK
  omega

/-- **The states stage** (`decTopStatesKC`) on the salted tables, the states' entry table of
fewer than `2^e` pairs: at most `statePriceK e R · |states| + framesPriceK e R + 59`. -/
theorem decTopStatesK_costK (hP : Includes P decTopStatesKC.costDeps)
    (states : List (LeanVM.Semantics.Registers K)) (e : ℕ) (hn : 2 * states.length < 2 ^ e)
    (hc : CountsWithin discreteLogTables (mainValDK locsTableK rd) 16 (2 ^ 20) (2 ^ 20)) :
    machineCost P decTopStatesKC.costIdx [encodeValue discreteLogTables, encodeValue preTableK,
      encodeValue genPows, encodeValue readerTabs, encodeValue whirTabsK,
      encodeValue (pcTableTK entriesK), encodeValue argCountsK, encodeValue retCountsK,
      encodeValue locsTableK, rdV, encodeValue states] ≤
        statePriceK e R * states.length + framesPriceK e R + 59 := by
  rw [decTopStatesKC.costEq P hP discreteLogTables preTableK genPows readerTabs whirTabsK
    (pcTableTK entriesK) argCountsK retCountsK locsTableK rd rdV hrd states]
  have hpre : ∀ (j : ℕ) (fp : K), RunsApp P (.closure decTopStatesKC.lam2.costIdx
      [encodeValue discreteLogTables, encodeValue preTableK, encodeValue genPows, rdV])
      [encodeValue j, encodeValue fp]
      (encodeValue (Located.preTestAtK discreteLogTables preTableK genPows rd j fp)) :=
    fun j fp ↦ RunsApp.of_spec (decTopStatesKC.lam2.costSpec P (by includes) discreteLogTables
      preTableK genPows rd rdV hrd j fp)
  have hPr : ∀ (j : ℕ) (fp : K), j < 2 ^ 64 → appCost P (.closure decTopStatesKC.lam2.costIdx
      [encodeValue discreteLogTables, encodeValue preTableK, encodeValue genPows, rdV])
      [encodeValue j, encodeValue fp] ≤ preK R := fun j fp hj ↦ by
    rw [appCost_fn, List.cons_append, List.cons_append, List.cons_append, List.cons_append,
      List.nil_append, decTopStatesKC.lam2.costEq P (by includes) discreteLogTables preTableK
        genPows rd rdV hrd]
    have := preTestAtK_cost P (by includes) discreteLogTables rd rdV hrd R hR 706
      (fun w n hn ↦ powBelow_cost P (by includes) discreteLogTables w n hn) preTableK
      preTableK_shape genPows j hj fp
    simp only [List.length_cons, List.length_nil]
    unfold preK
    omega
  have hE := entryArrayTK_cost P rd rdV hrd R hR _ _ hpre (preK R) hPr (by includes)
    (pcTableTK entriesK) 2 7093 e pcTableTK_getD_lt pcTableTK_getD_length
    (fun k hk ↦ pcTableTK_get_cost P (by includes) k hk) states (by omega)
  obtain ⟨hok, hsz⟩ := entryArrayTK_ok rd
    (Located.preTestAtK discreteLogTables preTableK genPows rd) (pcTableTK entriesK) 2
    pcTableTK_getD_lt pcTableTK_getD_length states
  have hF := decTopFramesK_costK P hrd hR (by includes) (by includes) (by includes) hok (e := e) (by omega) hc
  unfold statePriceK
  omega

end Reader

/-- **The tables stage** (`decTopTablesKC`) at the address tables `decoderTables prog κ`, `κ ≤ 30`:
the replay, then the states stage at the reader's price `1271`. -/
theorem decTopTablesK_costK (hP : Includes P decTopTablesKC.costDeps)
    (prog : LeanVM.Semantics.LeanIsaProgram) {κ : ℕ} (hκ : κ ≤ 30) (mem : Vector E (2 ^ κ))
    (e : ℕ)
    (hn : 2 * (Decoder.replayStatesOf (powTable κ) (powTable prog.logSize) prog mem).length <
      2 ^ e)
    (hc : CountsWithin discreteLogTables
      (mainValDK locsTableK (Decoder.memReader (powTable κ) mem)) 16 (2 ^ 20) (2 ^ 20)) :
    machineCost P decTopTablesKC.costIdx [encodeValue discreteLogTables, encodeValue preTableK,
      encodeValue genPows, encodeValue readerTabs, encodeValue whirTabsK,
      encodeValue (pcTableTK entriesK), encodeValue argCountsK, encodeValue retCountsK,
      encodeValue locsTableK, encodeValue (Decoder.decoderTables prog κ), encodeValue prog,
      encodeValue κ, encodeValue mem] ≤
        (runnerStepPrice κ prog.logSize + 46 + statePriceK e 1271) *
          (Decoder.replayStatesOf (powTable κ) (powTable prog.logSize) prog mem).length +
        framesPriceK e 1271 + 2456 + 85 := by
  have et : Decoder.decoderTables prog κ = (powTable κ, powTable prog.logSize) := rfl
  rw [et, decTopTablesKC.costEq P hP]
  dsimp only
  have h1 := replayStatesOf_cost P (by includes) prog (by omega : κ ≤ 62) mem
  have h2 := decTopStatesK_costK P (readerClosure_runs P (by includes) mem)
    (readerClosure_cost P (by includes) hκ mem) (by includes) _ e hn hc
  rw [Nat.add_mul]
  omega

/-! ## The tables built once -/

theorem preChunks_length : preChunk0.length ≤ 400 ∧ preChunk1.length ≤ 400 ∧
    preChunk2.length ≤ 400 ∧ preChunk3.length ≤ 400 ∧ preChunk4.length ≤ 400 ∧
    preChunk5.length ≤ 400 ∧ preChunk6.length ≤ 400 ∧ preChunk7.length ≤ 400 := by
  decide +kernel

theorem locsBlocks_lengths : locsBlocksList0.length ≤ 1539 ∧ locsBlocksList1.length ≤ 1539 ∧
    locsBlocksList2.length ≤ 1539 ∧ locsBlocksList3.length ≤ 1539 ∧ locsBlocksList.length ≤ 1539 ∧
    guestEntriesList.length ≤ 1539 ∧ guestArgCountsList.length ≤ 1539 ∧
    guestRetCountsList.length ≤ 1539 := by
  decide +kernel

theorem locsBlocks_rows : ∀ r ∈ locsBlocksList, r.length ≤ 2000 := by decide +kernel

/-- The salted tables' price. -/
@[expose] def tablesPriceK : ℕ := 80000000

/-- **The salted tables, built once**: the preconditions (`preTableKC`), the entries, the argument
and return counts, the packed frame cells (`locsTableKC`): at most `tablesPriceK`. -/
theorem tablesK_cost (hP : Includes P preTableKC.costDeps) (hE : Includes P entriesKC.costDeps)
    (hA : Includes P argCountsKC.costDeps) (hR : Includes P retCountsKC.costDeps)
    (hL : Includes P locsTableKC.costDeps) :
    machineCost P preTableKC.costIdx [] + machineCost P entriesKC.costIdx [] +
      machineCost P argCountsKC.costIdx [] + machineCost P retCountsKC.costIdx [] +
      machineCost P locsTableKC.costIdx [] ≤ tablesPriceK := by
  obtain ⟨p0, p1, p2, p3, p4, p5, p6, p7⟩ := preChunks_length
  obtain ⟨l0, l1, l2, l3, ll, le, la, lr⟩ := locsBlocks_lengths
  rw [preTableKC.costEq P hP, preChunk0C.costEq P (by includes), preChunk1C.costEq P (by includes),
    preChunk2C.costEq P (by includes), preChunk3C.costEq P (by includes),
    preChunk4C.costEq P (by includes), preChunk5C.costEq P (by includes),
    preChunk6C.costEq P (by includes), preChunk7C.costEq P (by includes)]
  have a1 := append_cost P (by includes) preChunk0 preChunk1
  have a2 := append_cost P (by includes) (preChunk0 ++ preChunk1) preChunk2
  have a3 := append_cost P (by includes) (preChunk0 ++ preChunk1 ++ preChunk2) preChunk3
  have a4 := append_cost P (by includes) (preChunk0 ++ preChunk1 ++ preChunk2 ++ preChunk3)
    preChunk4
  have a5 := append_cost P (by includes)
    (preChunk0 ++ preChunk1 ++ preChunk2 ++ preChunk3 ++ preChunk4) preChunk5
  have a6 := append_cost P (by includes)
    (preChunk0 ++ preChunk1 ++ preChunk2 ++ preChunk3 ++ preChunk4 ++ preChunk5) preChunk6
  have a7 := append_cost P (by includes)
    (preChunk0 ++ preChunk1 ++ preChunk2 ++ preChunk3 ++ preChunk4 ++ preChunk5 ++ preChunk6)
    preChunk7
  simp only [List.length_append] at a1 a2 a3 a4 a5 a6 a7 ⊢
  rw [entriesKC.costEq P hE, Auto.LeanVM.SaltedGuest.Decoder.guestEntriesList.c1060.costEq P (by includes),
    argCountsKC.costEq P hA, Auto.LeanVM.SaltedGuest.Decoder.guestArgCountsList.c1062.costEq P (by includes),
    retCountsKC.costEq P hR,
    Auto.LeanVM.SaltedGuest.Decoder.guestRetCountsList.c1064.costEq P (by includes),
    locsTableKC.costEq P hL,
    Auto.LeanVM.SaltedGuest.Decoder.locsBlocksList.c1066.costEq P (by includes),
    Auto.LeanVM.SaltedGuest.Decoder.locsBlocksList0.c1067.costEq P (by includes),
    Auto.LeanVM.SaltedGuest.Decoder.locsBlocksRow39.c1068.costEq P (by includes),
    Auto.LeanVM.SaltedGuest.Decoder.locsBlocksList1.c1069.costEq P (by includes),
    Auto.LeanVM.SaltedGuest.Decoder.locsBlocksList2.c1070.costEq P (by includes),
    Auto.LeanVM.SaltedGuest.Decoder.locsBlocksList3.c1071.costEq P (by includes)]
  have b1 := append_cost P (by includes) locsBlocksList0 locsBlocksList1
  have b2 := append_cost P (by includes) (locsBlocksList0 ++ locsBlocksList1) locsBlocksList2
  have b3 := append_cost P (by includes) (locsBlocksList0 ++ locsBlocksList1 ++ locsBlocksList2)
    locsBlocksList3
  have m := map_cost P (by includes) List.toArray (.closure Decoder.tabAC.lam0.costIdx [])
    (fun xs ↦ RunsApp.of_spec (Decoder.tabAC.lam0.costSpec P (by includes) xs)) (2000 + 2)
    locsBlocksList (fun r hr ↦ by
      rw [appCost_fn, List.nil_append, Decoder.tabAC.lam0.costEq P (by includes), List.length_nil]
      have := locsBlocks_rows r hr; omega)
  simp only [List.length_append, List.length_map] at b1 b2 b3 m ⊢
  unfold tablesPriceK
  omega

end

end LeanVM.SaltedGuest.Bounds
