/-
  LeanVM.SaltedGuest.Decoder.EntryTable

  The salted decoder's compiled replayed frame map, keyed by the salted function's index, and
  `main`'s valuation.
-/

module

public import LeanVM.Cost.Decoder.Top
public import LeanVM.SaltedGuest.Decoder.Cells
public import LeanVM.SaltedGuest.Decoder.Locs
public import LeanVM.SaltedGuest.Decoder.GuestTables
public import LeanVM.SaltedGuest.Located.FastK

/-!
# The salted decoder's entry table, compiled

The deployed `Cost/Decoder/EntryTable.lean` over the salted guest's tables, each built once by the
decoder's top and passed down: the entries' pcs (`entriesK`, `guestEntries`), the argument and
return counts (`argCountsK`, `retCountsK`), and the frame cells packed (`locsTableK`, the blocks of
`Locs.lean`; a cell read by `cellAtK`). The functions entered at each pc (`pcTableTK`), a state's
key at a function's entry (`entryKeyTK`), the entry table as one sorted array (`entryArrayTK`) and
the frame map on it (`frameAtAK`, one binary search), keyed by the salted function's index. The
library functions they call (the sorted maps, the binary search, the call key's codes, the merge
sort, `keyCmp`, `keyLe`, `dedupFirst`) are the deployed compiled ones. The insertion form
(`fileOneK`, `fileStateTK`, `entryTableTK`, `frameAtK`) is the specification the sorted array is
proved equal to (`EntryTableEq.lean`).

`mainValK L rd`: the salted `main`'s valuation, its cells read off function `1`'s packed cells;
`mainValDK L rd`: the same read at the deployed `main`'s numbers (`mainRiK`, `B1.Main.mainRi`),
the valuation the deployed decoders read.
-/

namespace LeanVM.SaltedGuest.Decoder

open LeanVM.Cost LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Extraction.Fast
open LeanVM.Cost.Decoder

attribute [local instance] lexOrd

@[expose] public section

/-! ## The tables -/

/-- The salted functions' entry pcs. -/
def entriesK : Array ℕ := guestEntriesList.toArray

/-- The salted functions' argument counts. -/
def argCountsK : Array ℕ := guestArgCountsList.toArray

/-- The salted functions' return counts. -/
def retCountsK : Array ℕ := guestRetCountsList.toArray

/-- **The salted functions' frame cells, packed**: function `j`'s blocks at `j`. -/
noncomputable def locsTableK : Array (Array ℕ) := (locsBlocksList.map List.toArray).toArray

/-- Cell `i` of a function's packed row. -/
def cellAtK (row : Array ℕ) (i : ℕ) : ℕ := packedCell (row.getD (i / 64) 0) (i % 64)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
cost_compile entriesKC := entriesK
set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
cost_compile argCountsKC := argCountsK
set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
cost_compile retCountsKC := retCountsK
set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
cost_compile locsTableKC := locsTableK
cost_compile packedCellC := packedCell
cost_compile cellAtKC := cellAtK

/-! ## The entry table -/

/-- Function `j`'s entry filed at its entry pc's code. -/
def addEntryK (ent : Array ℕ) (m : SortedMap ℕ (List ℕ)) (j : ℕ) : SortedMap ℕ (List ℕ) :=
  Guest.Located.addAt m (Guest.Located.laneCode (addressOfIndex (ent.getD j 0))) j

/-- **The functions entered at each pc**, from the table of entries. -/
def pcTableTK (ent : Array ℕ) : SortedMap ℕ (List ℕ) := (List.range nFns).foldl (addEntryK ent) .empty

/-- The key under which state `r`, at function `j`'s entry, files its frame. -/
def entryKeyTK (ac rc : Array ℕ) (rd : Reader) (r : Registers K) (j : ℕ) : Guest.Located.CallKey :=
  Guest.Located.callKey j (Guest.Located.wordsWith rd r.fp 2 (ac.getD j 0))
    (Guest.Located.wordsWith rd r.fp (2 + ac.getD j 0) (rc.getD j 0))

/-- State `r` filed under function `j`'s key, if `pre` holds. -/
def fileOneK (ac rc : Array ℕ) (pre : ℕ → K → Bool) (rd : Reader) (r : Registers K)
    (m : SortedMap Guest.Located.CallKey K) (j : ℕ) : SortedMap Guest.Located.CallKey K :=
  if pre j r.fp then insertIfNew m (entryKeyTK ac rc rd r j) r.fp else m

/-- State `r` filed under the key of each function entered at its pc. -/
def fileStateTK (pcT : SortedMap ℕ (List ℕ)) (ac rc : Array ℕ) (pre : ℕ → K → Bool) (rd : Reader)
    (m : SortedMap Guest.Located.CallKey K) (r : Registers K) : SortedMap Guest.Located.CallKey K :=
  (pcT.getD (Guest.Located.laneCode r.pc) []).foldl (fileOneK ac rc pre rd r) m

/-- **The entry table** of the states. -/
def entryTableTK (pcT : SortedMap ℕ (List ℕ)) (ac rc : Array ℕ) (pre : ℕ → K → Bool)
    (states : List (Registers K)) (rd : Reader) : SortedMap Guest.Located.CallKey K :=
  states.foldl (fileStateTK pcT ac rc pre rd) .empty

/-- The word of value `v` in function `j`'s frame at `fp`. -/
def frameWordAtK (locs : Array (Array ℕ)) (rd : Reader) (fp : K) (j : ℕ) (v : V) : E :=
  Guest.Located.wordWith rd fp (cellAtK (locs.getD j #[]) v.idx)

/-- **The frame map** on the entry table, its last argument the value read: the call of function
`j` looked up, its frame's word of `v`; `0` if the call was not entered. -/
def frameAtK (table : SortedMap Guest.Located.CallKey K) (locs : Array (Array ℕ)) (rd : Reader)
    (j : ℕ) (args rets : List E) (v : V) : E :=
  match table.get? (Guest.Located.callKey j args rets) with
  | some fp => frameWordAtK locs rd fp j v
  | none => 0

set_option maxRecDepth 100000 in
cost_compile addEntryKC := addEntryK
set_option maxRecDepth 100000 in
cost_compile pcTableTKC := pcTableTK
set_option maxRecDepth 100000 in
cost_compile entryKeyTKC := entryKeyTK
set_option maxRecDepth 100000 in
cost_compile frameWordAtKC := frameWordAtK

/-! ## The entry table as one sorted array -/

/-- The pair state `s` files for function `j`: its key and the frame, if `pre` holds. -/
def pairOfK (ac rc : Array ℕ) (pre : ℕ → K → Bool) (rd : Reader) (s : Registers K) (j : ℕ) :
    Option (Guest.Located.CallKey × K) :=
  if pre j s.fp then some (entryKeyTK ac rc rd s j, s.fp) else none

/-- The pairs state `s` files: one per function entered at its pc whose precondition holds. -/
def statePairsK (pcT : SortedMap ℕ (List ℕ)) (ac rc : Array ℕ) (pre : ℕ → K → Bool) (rd : Reader)
    (s : Registers K) : List (Guest.Located.CallKey × K) :=
  (pcT.getD (Guest.Located.laneCode s.pc) []).filterMap (pairOfK ac rc pre rd s)

/-- **The pairs the states file**, in filing order. -/
def entryPairsK (pcT : SortedMap ℕ (List ℕ)) (ac rc : Array ℕ) (pre : ℕ → K → Bool) (rd : Reader) :
    List (Registers K) → List (Guest.Located.CallKey × K)
  | [] => []
  | s :: ss => statePairsK pcT ac rc pre rd s ++ entryPairsK pcT ac rc pre rd ss

/-- **The entry table, a sorted array**: the pairs sorted by key, stably, each key's first kept. -/
def entryArrayTK (pcT : SortedMap ℕ (List ℕ)) (ac rc : Array ℕ) (pre : ℕ → K → Bool)
    (states : List (Registers K)) (rd : Reader) : Array (Guest.Located.CallKey × K) :=
  (dedupFirst ((entryPairsK pcT ac rc pre rd states).mergeSort keyLe)).toArray

/-- **The frame map on the sorted array**: one binary search of the call's key. -/
def frameAtAK (table : Array (Guest.Located.CallKey × K)) (locs : Array (Array ℕ)) (rd : Reader)
    (j : ℕ) (args rets : List E) (v : V) : E :=
  match searchIn table (Guest.Located.callKey j args rets) 0 table.size with
  | some fp => frameWordAtK locs rd fp j v
  | none => 0

cost_compile pairOfKC := pairOfK
set_option maxRecDepth 100000 in
cost_compile statePairsKC := statePairsK
set_option maxRecDepth 100000 in
cost_compile entryPairsKC measure fun _ _ _ _ _ l ↦ l.length := entryPairsK
set_option maxRecDepth 100000 in
cost_compile entryArrayTKC := entryArrayTK
set_option maxRecDepth 100000 in
cost_compile frameAtAKC := frameAtAK

/-! ### A frame looked up once -/

/-- The frame pointer of function `j`'s call on `args`, `rets`, if it was entered. -/
def frameFpAK (table : Array (Guest.Located.CallKey × K)) (j : ℕ) (args rets : List E) :
    Option K :=
  searchIn table (Guest.Located.callKey j args rets) 0 table.size

/-- The word of `v` in function `j`'s frame at the pointer `o` (`0` if none). -/
def frameValAtK (locs : Array (Array ℕ)) (rd : Reader) (o : Option K) (j : ℕ) (v : V) : E :=
  match o with
  | some fp => frameWordAtK locs rd fp j v
  | none => 0

theorem frameAtAK_eq_frameValAtK (table : Array (Guest.Located.CallKey × K))
    (locs : Array (Array ℕ)) (rd : Reader) (j : ℕ) (args rets : List E) :
    frameAtAK table locs rd j args rets = frameValAtK locs rd (frameFpAK table j args rets) j := by
  funext v
  unfold frameAtAK frameValAtK frameFpAK
  rfl

set_option maxRecDepth 100000 in
cost_compile frameFpAKC := frameFpAK
cost_compile frameValAtKC := frameValAtK

/-! ## `main`'s valuation -/

/-- **The salted `main`'s valuation**: the word of `v` at `fp = 1`, its cell off function `1`'s
packed cells. -/
def mainValK (locs : Array (Array ℕ)) (rd : Reader) (v : V) : E :=
  Guest.Located.wordWith rd 1 (cellAtK (locs.getD 1 #[]) v.idx)

/-- The salted `main`'s value number of a deployed `main`'s value number (`B1.Main.mainRi`,
`EntryTableEq.lean`). -/
def mainRiK (k : ℕ) : ℕ :=
  if k < 26 then k else if k = 26 then 29 else if k = 27 then 33 else if k < 369 then k + 7
  else if k < 373 then k + 7 else if k = 379 then 408 else if k = 380 then 409
  else if k < 381 then k + 7 else k + 29

/-- **The salted `main`'s valuation at the deployed `main`'s numbers** (`B1.Main.mainVal`): the
word of the salted value `mainRiK v.idx`. -/
def mainValDK (locs : Array (Array ℕ)) (rd : Reader) (v : V) : E :=
  Guest.Located.wordWith rd 1 (cellAtK (locs.getD 1 #[]) (mainRiK v.idx))

cost_compile mainValKC := mainValK
cost_compile mainRiKC := mainRiK
cost_compile mainValDKC := mainValDK

end

end LeanVM.SaltedGuest.Decoder
