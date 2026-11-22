/-
  LeanVM.SaltedGuest.Decoder.Readers

  The salted decoder's compiled readers of the signatures, the DA matrix and the batching's hints,
  off the salted frames by index.
-/

module

public import LeanVM.SaltedGuest.Decoder.EntryTable

/-!
# The salted decoder's readers, compiled

Each callee's witness off its frame, the frames by the salted function's index, the frame map the
closure `frameAtAK table locs rd`:

* the leanXMSS signature `__loop2`'s iteration checks (`xmssAtFrameTK`, salted function `39`) and
  the leanSPHINCS signature `verify_sig_lean_sphincs` checks (`sphincsAtFrameTK`, `21`, its three
  `sp_wots` frames `20`): the deployed readers off arrays (`xmssSigOfA`, `sphincsSigOfA`), these
  functions unchanged, each frame looked up once (`frameFpAK`);
* the DA matrix the salted `da_verify` checks (`daAtFrameK`, `28`, the key's word its last
  argument): `B1.Da.dvWitK` staged as the deployed `dvWitND`, its columns' frames
  (`da_verify_column`, `31`) looked up once, its cells' blob loop `__loop26` (`394`) and cell
  check `da_verify_cell` (`32`) at the salted cells;
* the batching's hints of the salted `aggregate_claims` (`hintsAtFrameK`, `36`, the seed's two
  words its first arguments): `B1.Main.aggHintsS`.

The definitions copy the salted guest's (`dvColArgsK`, `cellSymsOfSK`, `aggRoundsK`, `aggHintsK`);
`ReadersEq.lean` proves them the salted readers at the replayed frame map.
-/

namespace LeanVM.SaltedGuest.Decoder

open LeanVM.Cost LeanVM.Parameters LeanVM.Guest.Core LeanVM.Guest.B1 LeanVM.Guest.Fast
open LeanVM.Guest.B1.Da LeanVM.Extraction.Fast LeanVM.Protocol.Verifier LeanVM.Node
open LeanVM.Cost.Decoder

@[expose] public section

/-! ## The signatures -/

/-- **The leanXMSS signature `__loop2`'s iteration on `args` checks**, its frame (salted function
`39`) looked up once. -/
noncomputable def xmssAtFrameTK (R : ReaderTabs) (table : Array (Guest.Located.CallKey × K))
    (locs : Array (Array ℕ)) (rd : Reader) (args : List E) : LeanXmss.Signature :=
  xmssSigOfA R.xmss (frameValAtK locs rd (frameFpAK table 39 args []) 39)

/-- The leanSPHINCS signature off `verify_sig_lean_sphincs`' frame pointer `o` (salted function
`21`): each layer's `sp_wots` frame (`20`) looked up once. -/
noncomputable def sphincsAtFpK (R : ReaderTabs) (table : Array (Guest.Located.CallKey × K))
    (locs : Array (Array ℕ)) (rd : Reader) (o : Option K) : Sphincs.Signature :=
  sphincsSigOfA R.sphincs (frameValAtK locs rd o 21)
    (frameValAtK locs rd (frameFpAK table 20 (spWotsArgs (frameValAtK locs rd o 21) 0)
      (spWotsRets (frameValAtK locs rd o 21) 0)) 20)
    (frameValAtK locs rd (frameFpAK table 20 (spWotsArgs (frameValAtK locs rd o 21) 1)
      (spWotsRets (frameValAtK locs rd o 21) 1)) 20)
    (frameValAtK locs rd (frameFpAK table 20 (spWotsArgs (frameValAtK locs rd o 21) 2)
      (spWotsRets (frameValAtK locs rd o 21) 2)) 20)

/-- **The leanSPHINCS signature checked at slot address `p`**, `main`'s word `w47` its second
argument, its frame looked up once. -/
noncomputable def sphincsAtFrameTK (R : ReaderTabs) (table : Array (Guest.Located.CallKey × K))
    (locs : Array (Array ℕ)) (rd : Reader) (w47 : E) (p : E) : Sphincs.Signature :=
  sphincsAtFpK R table locs rd (frameFpAK table 21 [p, w47] [])

set_option maxRecDepth 100000 in
cost_compile xmssAtFrameTKC := xmssAtFrameTK
set_option maxRecDepth 100000 in
cost_compile sphincsAtFpKC := sphincsAtFpK
set_option maxRecDepth 100000 in
cost_compile sphincsAtFrameTKC := sphincsAtFrameTK

/-! ## The DA matrix -/

/-- Column `h`'s call's words (`B1.Da.dvColArgsS`). -/
noncomputable def dvColArgsK (σ : Val) (h : ℕ) : List E :=
  [gen ^ h, σ (.n 2), σ (.n 33), σ (.n 17), σ (.n 18), σ (.n 19), σ (.n 20), σ (.n 1)]

/-- A cell's symbols off the salted `da_verify_cell`'s valuation (`B1.Da.cellSymsOfS`). -/
def cellSymsOfSK (σ : Val) : List K := (List.range 256).map fun j ↦ (σ (.n (j + 2))).limb 0

/-- Column `h`'s valuation (salted `da_verify_column`, function `31`). -/
noncomputable def dvColVNK (σ : Val) (Vn : NFrames) (h : ℕ) : Val := Vn 31 (dvColArgsK σ h) []

/-- A column's two words its blob loop reads (`14`, `15`). -/
def colWordsOfK (v : Val) : E × E := (v (.n 14), v (.n 15))

/-- Column `h`'s two words, its frame looked up once. -/
noncomputable def dvColWordsK (σ : Val) (Vn : NFrames) (h : ℕ) : E × E := colWordsOfK (dvColVNK σ Vn h)

/-- The `128` columns' words. -/
noncomputable def dvColsK (σ : Val) (Vn : NFrames) : Array (E × E) :=
  ((List.range 128).map (dvColWordsK σ Vn)).toArray

/-- Blob `i`'s iteration of column `h`'s blob loop (`__loop26`, function `394`), the column's words
`cw` given. -/
def dvRowVWK (σ : Val) (Vn : NFrames) (cw : E × E) (i h : ℕ) : Val :=
  Vn 394 [ofK (Parameters.g ^ i), σ (.n 2), cw.1, σ (.n 1), σ (.n 33), ofK (Parameters.g ^ h), cw.2] []

/-- A cell's symbols off the salted `da_verify_cell`'s frame (`32`), the key's word `key` and the
blob loop's valuation given. -/
def cellSymsAtK (Vn : NFrames) (c14 key : E) (row : Val) : List K :=
  cellSymsOfSK (Vn 32 [c14, key] [row (.n 7), row (.n 8), row (.n 9)])

/-- Cell `(i, h)`'s symbols, the column's words given: its blob loop's frame looked up once. -/
def dvSymsCellK (σ : Val) (Vn : NFrames) (cw : E × E) (i h : ℕ) : List K :=
  cellSymsAtK Vn cw.1 (σ (.n 1)) (dvRowVWK σ Vn cw i h)

/-- The symbols, padded outside the matrix of `r` rows, the columns' words given. -/
def dvSymsColsK (r : ℕ) (σ : Val) (Vn : NFrames) (cols : Array (E × E)) (i h : ℕ) : List K :=
  if i < r ∧ h < 128 then dvSymsCellK σ Vn (cols.getD h (0, 0)) i h else List.replicate 256 0

/-- The salted `da_verify`'s witness, its `r` rows and its columns' words given. -/
def dvWitNColsK (r : ℕ) (σ : Val) (Vn : NFrames) (cols : Array (E × E)) :
    LeanVM.Da.MatrixWitness :=
  ⟨daRows r (dvSymsColsK r σ Vn cols)⟩

/-- The salted `da_verify`'s witness, its `r` rows given: the columns' words built once. -/
noncomputable def dvWitNAtK (r : ℕ) (σ : Val) (Vn : NFrames) : LeanVM.Da.MatrixWitness :=
  dvWitNColsK r σ Vn (dvColsK σ Vn)

/-- **The salted `da_verify`'s witness** (`B1.Da.dvWitK`), the logarithm's tables `D` given: its
rows counted once, at most `1024`. -/
noncomputable def dvWitNDK (D : DiscreteLogTables) (σ : Val) (Vn : NFrames) :
    LeanVM.Da.MatrixWitness :=
  dvWitNAtK (daRowCount (gLogD D (σ (.n 2)))) σ Vn

/-- **The DA matrix the salted `da_verify` (`28`) checks** on the call's words and the key's word
`key`. -/
noncomputable def daAtFrameK (D : DiscreteLogTables) (Vn : NFrames) (key : E) (args rets : List E) :
    LeanVM.Da.MatrixWitness :=
  dvWitNDK D (Vn 28 (args ++ [key]) rets) Vn

cost_compile dvColArgsKC := dvColArgsK
cost_compile cellSymsOfSKC := cellSymsOfSK
cost_compile dvColVNKC := dvColVNK
cost_compile colWordsOfKC := colWordsOfK
cost_compile dvColWordsKC := dvColWordsK
cost_compile dvColsKC := dvColsK
cost_compile dvRowVWKC := dvRowVWK
cost_compile cellSymsAtKC := cellSymsAtK
cost_compile dvSymsCellKC := dvSymsCellK
cost_compile dvSymsColsKC := dvSymsColsK
cost_compile dvWitNColsKC := dvWitNColsK
cost_compile dvWitNAtKC := dvWitNAtK
cost_compile dvWitNDKC := dvWitNDK
cost_compile daAtFrameKC := daAtFrameK

/-! ## The batching's hints -/

/-- The sumcheck's rounds the salted `aggregate_claims` hints (`B1.Main.aggRoundsS`). -/
noncomputable def aggRoundsK (rd : Reader) (σ : Val) : List (E × E) :=
  (List.range 23).map fun k ↦ (Digest.memAt rd (σ (.n 7)) (2 * k), Digest.memAt rd (σ (.n 7)) (2 * k + 1))

/-- The salted `aggregate_claims`' hints (`B1.Main.aggHintsS`). -/
noncomputable def aggHintsK (rd : Reader) (σ : Val) : BatchingHints := ⟨aggRoundsK rd σ, σ (.n 8)⟩

/-- **The batching's hints at the salted `aggregate_claims`' (`36`) call's words**, the seed's two
words `s0`, `s1` its first arguments. -/
noncomputable def hintsAtFrameK (rd : Reader) (Vn : NFrames) (s0 s1 : E) (args : List E) :
    BatchingHints :=
  aggHintsK rd (Vn 36 ([s0, s1] ++ args) [])

cost_compile aggRoundsKC := aggRoundsK
cost_compile aggHintsKC := aggHintsK
cost_compile hintsAtFrameKC := hintsAtFrameK

end

end LeanVM.SaltedGuest.Decoder
