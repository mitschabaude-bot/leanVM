/-
  LeanVM.SaltedGuest.Decoder.TopEq

  The salted decoder's compiled top is the salted decoding by replay.
-/

module

public import LeanVM.SaltedGuest.Decoder.Top
public import LeanVM.SaltedGuest.Decoder.ProofEq
public import LeanVM.SaltedGuest.Decoder.EntryTableEq
public import LeanVM.SaltedGuest.EndReplay
public import LeanVM.Cost.Decoder.TopEq

/-!
# The salted decoder's top is the decoding by replay

* `kidCountsK_tables`: the children's counts at the logarithm's tables are `childCountsOf`;
* `decTopFramesK_eq`: off any entry table and frame cells, the decoding is
  `B1.Main.decK B1.VerifySub.vsPiOfK` at the salted valuation `σs`, its deployed numbers
  `B1.Main.mainVal σs`, and the frame map by name of `frameAtAK table locs rd` (`byName`): the
  deployed staged witness (`decWitStaged_eq`), the statement (`decStmtD_tables`), the counts
  (`kidCountsK_tables`), the cursor's
  length (`cursorLength_tables`, `cursorLenWith_eq`) and the salted readers (`ReadersEq.lean`,
  `ProofEq.lean`);
* **`decTopK_eq`**: on a memory below `2^64` words, the compiled top on the salted guest is
  `End.decodeWithR (decK vsPiOfK)`: the reader of the memory vector (`memReader_memoryVector`,
  `readTable_powTable`), the replay (`replayStatesOf_eq`, `statesTable_eq`), the salted
  precondition (`preTestK_eq_preTable`), the frame map on the sorted array (`frameAtAK_eq`), keyed
  by name the replayed one (`frameVFastNK_nameIndex`, `frameVWithK_eq_frameVFastK`), `main`'s
  valuations (`mainValK_eq`, `mainValDK_eq`).
-/

namespace LeanVM.SaltedGuest.Decoder

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Fast LeanVM.Extraction.Fast
open LeanVM.Node LeanVM.Cost.Decoder LeanVM.SaltedGuest.Located LeanVM.SaltedGuest.B1

@[expose] public section

/-- **The children's counts at the logarithm's tables** are `B1.Main.childCountsOf`. -/
theorem kidCountsK_tables (rd : Reader) (σ : Val) :
    kidCountsK discreteLogTables rd σ = B1.Main.childCountsOf rd σ := by
  unfold kidCountsK B1.Main.childCountsOf nKidsD
  rw [gLogD_tables]
  rfl

/-- **A count's logarithm at the logarithm's tables** is `B1.Main.cellLog`. -/
theorem cellLogK_tables (x : E) : cellLogK discreteLogTables x = B1.Main.cellLog x := rfl

/-- **Off an entry table, the compiled decoding is `decK vsPiOfK`.** -/
theorem decTopFramesK_eq (locs : Array (Array ℕ)) (rd : Reader) (σs : Val)
    (table : Array (Guest.Located.CallKey × K)) :
    decTopFramesK discreteLogTables readerTabs whirTabsK locs rd σs (Main.mainVal σs) table =
      Main.decK VerifySub.vsPiOfK σs rd (byName (frameAtAK table locs rd)) := by
  unfold decTopFramesK decoderOutputK saltedDecodedOf Main.decK Main.decWitK Main.nodeCountOf
  rw [xmssAtFrameTK_eq, sphincsAtFrameTK_eq, daAtFrameK_eq, cursorLength_tables,
    cursorLenWith_eq discreteLog_discreteLogSpec, proofAtFrameK_eq, hintsAtFrameK_eq,
    decWitStaged_eq, decStmtD_tables, kidCountsK_tables, cellLogK_tables]

/-- **The salted decoder's compiled top is the decoding by replay**, on a memory below `2^64`
words. -/
theorem decTopK_eq {κ : ℕ} (hκ : κ < 64) (L : MemoryImage κ) :
    decTopK guestProgram κ (memoryVector L) =
      End.decodeWithR (Main.decK VerifySub.vsPiOfK) L := by
  unfold decTopK decTopTablesK decTopStatesK decoderTables
  rw [memReader_memoryVector, Guest.Located.readTable_powTable hκ, replayStatesOf_eq,
    memoryVector_get, Guest.Located.statesTable_eq hκ, ← preTestK_eq_preTable, mainValDK_eq,
    decTopFramesK_eq, frameAtAK_eq, End.decodeWithR]
  have hV : byName (frameVFastNK (preTestK L.read)
      (Guest.Located.statesIn (Extraction.powIndex κ) (Extraction.powIndex guestProgram.logSize) guestProgram L
        Guest.Located.replayFuel ⟨addressOfIndex 0, 1⟩) L.read) = replayFrameVK L := by
    funext f
    rw [byName, frameVFastNK_nameIndex, replayFrameVK, Guest.Located.readIn_powIndex hκ,
      frameVWithK_eq_frameVFastK]
  have hσ : mainValK locsTableK L.read = Check.valG L 1 (certOf 1) := by
    rw [mainValK_eq]
    rfl
  rw [hV, hσ]

end

end LeanVM.SaltedGuest.Decoder
