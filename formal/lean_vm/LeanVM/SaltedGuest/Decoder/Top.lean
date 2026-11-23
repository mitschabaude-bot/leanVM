/-
  LeanVM.SaltedGuest.Decoder.Top

  The salted decoder's compiled top: the decoding of an execution of the salted guest, by replay.
-/

module

public import LeanVM.SaltedGuest.Decoder.Proof
public import LeanVM.SaltedGuest.Decoder.PreTable

/-!
# The salted decoder's compiled chain: the top

The deployed `Cost/Decoder/Top.lean` for the salted guest, staged point-free, each table built
once and passed down:

* `decTopK prog κ mem`: the logarithm's tables (`discreteLogTables`), the salted preconditions
  (`preTableK`, its eight chunks each a function of no argument), the generator's powers
  (`genPows`), the readers' tables (`readerTabs`, the signatures' as deployed) and `open_stacked`'s
  salted tables (`whirTabsK`), the salted functions' entries, argument and return counts and packed
  frame cells (`entriesK`, `argCountsK`, `retCountsK`, `locsTableK`), the table of entries
  (`pcTableTK`), the address tables (`decoderTables`);
* `decTopTablesK`: the reader (`memReader memT mem`) and the replay (`replayStatesOf`);
* `decTopStatesK`: the salted `main`'s valuation (`mainValK`) and at the deployed numbers
  (`mainValDK`), and the entry table (`entryArrayTK`, the salted precondition
  `Located.preTestAtK D T Pw rd`);
* `decTopFramesK`: the decoding (`decoderOutput`: the seed, the statement), the witness by the
  deployed staged `decWitStaged` with the salted readers (`xmssAtFrameTK`, `sphincsAtFrameTK`,
  `daAtFrameK` with the key's word `34`, `proofAtFrameK`, `hintsAtFrameK` with the seed's words),
  the frame map the closure `frameAtAK table locs rd`.

`TopEq.lean`: **`decTopK_eq : decTopK guestProgram κ (memoryVector L) = End.decodeWithR (decK
vsPiOfK) L`**, on a memory below `2^64` words.
-/

namespace LeanVM.SaltedGuest.Decoder

open LeanVM.Cost LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Fast
open LeanVM.Extraction.Fast LeanVM.Node LeanVM.Cost.Decoder

@[expose] public section

/-! ## The preconditions, held once -/

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
cost_compile preChunk0C := preChunk0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
cost_compile preChunk1C := preChunk1
set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
cost_compile preChunk2C := preChunk2
set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
cost_compile preChunk3C := preChunk3
set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
cost_compile preChunk4C := preChunk4
set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
cost_compile preChunk5C := preChunk5
set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
cost_compile preChunk6C := preChunk6
set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
cost_compile preChunk7C := preChunk7
cost_compile preTableKC := preTableK
cost_compile preTestAtKC := Located.preTestAtK

/-! ## The top -/

/-- **The decoding off `main`'s valuations and the entry table**: the salted valuation `σs` and
at the deployed numbers `σd`. -/
noncomputable def decTopFramesK (D : DiscreteLogTables) (R : ReaderTabs) (W : WhirTabs)
    (locs : Array (Array ℕ)) (rd : Reader) (σs σd : Val)
    (table : Array (Guest.Located.CallKey × K)) : SeedStatementAndWitness :=
  decoderOutput D σd rd (decWitStaged D σd rd (xmssAtFrameTK R table locs rd)
    (sphincsAtFrameTK R table locs rd (σd (.n 47))) (daAtFrameK D (frameAtAK table locs rd) (σs (.n 55)))
    (proofAtFrameK W rd (frameAtAK table locs rd) (cursorLength D))
    (hintsAtFrameK rd (frameAtAK table locs rd) (σd (.n 26)) (σd (.n 27))))

/-- The decoding off the reader and the replayed states. -/
noncomputable def decTopStatesK (D : DiscreteLogTables) (T : Array (Option FnPre))
    (Pw : Array E) (R : ReaderTabs) (W : WhirTabs) (pcT : SortedMap ℕ (List ℕ)) (ac rc : Array ℕ)
    (locs : Array (Array ℕ)) (rd : Reader) (states : List (Registers K)) : SeedStatementAndWitness :=
  decTopFramesK D R W locs rd (mainValK locs rd) (mainValDK locs rd)
    (entryArrayTK pcT ac rc (Located.preTestAtK D T Pw rd) states rd)

/-- The decoding off the address tables and the memory. -/
noncomputable def decTopTablesK (D : DiscreteLogTables) (T : Array (Option FnPre))
    (Pw : Array E) (R : ReaderTabs) (W : WhirTabs) (pcT : SortedMap ℕ (List ℕ)) (ac rc : Array ℕ)
    (locs : Array (Array ℕ)) (tabs : Array (ℕ × ℕ) × Array (ℕ × ℕ)) (prog : LeanIsaProgram) {κ : ℕ}
    (mem : Vector E (2 ^ κ)) : SeedStatementAndWitness :=
  decTopStatesK D T Pw R W pcT ac rc locs (memReader tabs.1 mem)
    (replayStatesOf tabs.1 tabs.2 prog mem)

/-- **The salted decoder's top**: the decoding of an execution of `prog`, its memory the vector
`mem` of `2^κ` words. -/
noncomputable def decTopK (prog : LeanIsaProgram) (κ : ℕ) (mem : Vector E (2 ^ κ)) :
    SeedStatementAndWitness :=
  decTopTablesK discreteLogTables preTableK genPows readerTabs whirTabsK (pcTableTK entriesK)
    argCountsK retCountsK locsTableK (decoderTables prog κ) prog mem

set_option maxRecDepth 100000 in
cost_compile decTopFramesKC := decTopFramesK
set_option maxRecDepth 100000 in
cost_compile decTopStatesKC := decTopStatesK
set_option maxRecDepth 100000 in
cost_compile decTopTablesKC := decTopTablesK
set_option maxRecDepth 100000 in
cost_compile decTopKC := decTopK

end

end LeanVM.SaltedGuest.Decoder
