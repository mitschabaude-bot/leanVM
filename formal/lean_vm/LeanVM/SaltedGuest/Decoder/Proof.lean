/-
  LeanVM.SaltedGuest.Decoder.Proof

  The salted decoder's compiled reader of a child's proof, off the salted frames by index.
-/

module

public import LeanVM.SaltedGuest.Decoder.Readers
public import LeanVM.SaltedGuest.Decoder.WhirTables
public import LeanVM.SaltedGuest.B1.Opening.QueriesTK

/-!
# The salted child proof reader, compiled

`B1.VerifySub.vsPiOfK` (the proof the salted `verify_sub` checks) restated off arrays as the
deployed `Guest.Fast.vsPiOfA`, at the salted frames: the cursor from `29` to `683`, `open_stacked`'s
dispatch on the size's selector `1725` and the rate's `126` (salted function `310 + m`, its
arguments `vsOsArgsSK`, its returns `vsOsRetsSK`), each level's `level_queries` dispatch off the
salted table (`WhirTabs` with `osCallsTabK`, `whirTabsK`), the salted `opening_queries`' cells (the
key's loads `9 .. 21` in front: its first query hinted at `25`, a loop iteration's at `22` and `23`,
the loop's other arguments `oqLoopArgsSK`) and each query's salted `walk_path` call
(`oqWalkArgsSK`, the siblings from the chain's `22`). The generic parts (`wordsFrom`, `winPosOfW`,
`oqRow`, `oqSibsOf`, `toOpening`) are the deployed compiled ones. `ProofEq.lean` proves the reader
`vsPiOfK` at the replayed frame map.
-/

namespace LeanVM.SaltedGuest.Decoder

open LeanVM.Cost LeanVM.Parameters LeanVM.Guest.Core LeanVM.Guest.B1 LeanVM.Guest.Fast
open LeanVM.Guest.B1.Whir LeanVM.Protocol.Compile LeanVM.Protocol.Verifier LeanVM.Cost.Decoder
open LeanVM.SaltedGuest.B1

@[expose] public section

/-- The arguments of a salted query's `walk_path` call (`B1.oqWalkArgsK`). -/
def oqWalkArgsSK (s : Oq) (b : ℕ) (emit : Bool) (bp cap flags : E) (σ : Val) : List E :=
  [σ (.n (oqOutK s emit (oqKLK s b) (s.B - 1) 0)), σ (.n (oqOutK s emit (oqKLK s b) (s.B - 1) 1)),
    bp, cap, flags]

/-- The salted loop's arguments after its counter (`B1.oqLoopArgsK`). -/
def oqLoopArgsSK (σ : Val) : List E :=
  [σ (.n 6), σ (.n 4), σ (.n 0), σ (.n 1)] ++ (oqKeyV 9).map σ ++ [σ (.n 5), σ (.n 24), σ (.n 8)]

/-- The salted query hinted at `b`, its position `pos` given. -/
def oqQueryAtK (s : Oq) (walk : ℕ) (bp cap flags : E) (σ : Val) (Vn : NFrames) (b : ℕ)
    (emit : Bool) (pos : ℕ) : QW :=
  (pos, oqRow b s.R σ, oqSibsOf s.pd 22 pos (Vn walk (oqWalkArgsSK s b emit bp cap flags σ) []))

/-- **The salted query hinted at `b`**, its position read once off its windows. -/
def oqQueryAK (s : Oq) (lanes : List ℕ) (walk : ℕ) (rd : Reader) (bp cap flags : E) (b : ℕ)
    (emit : Bool) (σ : Val) (Vn : NFrames) : QW :=
  oqQueryAtK s walk bp cap flags σ Vn b emit (winPosOfW lanes rd bp (s.pd + s.cd) s.cd)

/-- A salted loop iteration's queries, from its frame. -/
def oqIterAK (s : Oq) (lanes : List ℕ) (walk : ℕ) (rd : Reader) (σ : Val) (Vn : NFrames) :
    List QW :=
  if s.base = 1 then
    [oqQueryAK s lanes walk rd (σ (.n 23)) (σ (.n 3)) (σ (.n 4)) 24 true σ Vn,
      oqQueryAK s lanes walk rd (σ (.n (oqE1K s))) (σ (.n 3)) (σ (.n 4)) (oqE1K s + 1) false σ Vn]
  else [oqQueryAK s lanes walk rd (σ (.n 22)) (σ (.n 3)) (σ (.n 4)) 23 true σ Vn]

/-- **The salted loop's iterations from the frame at `x`**, `n` of them, the next at `x·g`. -/
def oqItersFromK (s : Oq) (lanes : List ℕ) (loop walk : ℕ) (rd : Reader) (Vn : NFrames)
    (la : List E) : ℕ → E → List QW
  | 0, _ => []
  | n + 1, x =>
    oqIterAK s lanes walk rd (Vn loop (x :: la) []) Vn ++
      oqItersFromK s lanes loop walk rd Vn la n (x * gen)

/-- **The salted `opening_queries`' queries**: its loop's other arguments read once, each
iteration's frame at the next power of `g`, each query's position once. -/
def oqsOfAK (s : Oq) (lanes : List ℕ) (odd loop walk N : ℕ) (rd : Reader) (σ : Val)
    (Vn : NFrames) : List QW :=
  (if odd = 1 then [oqQueryAK s lanes walk rd (σ (.n 25)) (σ (.n 0)) (σ (.n 1)) 26 true σ Vn]
    else []) ++
    oqItersFromK s lanes loop walk rd Vn (oqLoopArgsSK σ) N 1

/-- A level's openings from its salted `opening_queries` call in the frame `fr` of its
`level_queries` callee, the call's argument words `a` given. -/
def levelOsAtK (lanes : List ℕ) (rd : Reader) (fr : Val) (Vn : NFrames) (c : OsCall)
    (a : List E) : List Opening :=
  (oqsOfAK ⟨c.base, c.I, c.pd, c.cd⟩ lanes c.odd c.loop c.walk c.N rd
    (Vn c.fn a [fr (.n (c.pw + 2))]) Vn).map (toOpening rd (a.headD 0) c.cd c.depth)

/-- A level's openings, the frame `fr` of its `level_queries` callee given: the salted
`opening_queries` call's argument words read once. -/
def levelOsQK (lanes : List ℕ) (rd : Reader) (fr : Val) (Vn : NFrames) (c : OsCall) :
    List Opening :=
  levelOsAtK lanes rd fr Vn c (c.qargsK.map fun k ↦ fr (.n k))

/-- **A level's openings**, its `level_queries` callee's frame read once. -/
def levelOsAK (lanes : List ℕ) (rd : Reader) (σ : Val) (Vn : NFrames) (c : OsCall) :
    List Opening :=
  levelOsQK lanes rd (Vn c.lq (c.args.map fun k ↦ σ (.n k)) (c.rets.map fun k ↦ σ (.n k))) Vn c

/-- **The salted `open_stacked`'s tables**: the lanes of `g^k`, each size and rate's stream words
(`open_stacked` unchanged) and its salted dispatches. -/
def whirTabsK : WhirTabs := ⟨gLanes, osWordsTab.toArray, osCallsTabK.toArray⟩

/-- `open_stacked`'s argument words in the salted `verify_sub` (`VerifySub.vsOsArgsS`). -/
def vsOsArgsSK (σ : Val) : List E :=
  [σ (.n 126), σ (.n 1127), σ (.n 1128), σ (.n 1129), σ (.n 1130), σ (.n 1131), σ (.n 1720),
    σ (.n 334), σ (.n 344), σ (.n 683)]

/-- `open_stacked`'s return words in the salted `verify_sub` (`VerifySub.vsOsRetsS`). -/
def vsOsRetsSK (σ : Val) : List E := [σ (.n 1730), σ (.n 1731), σ (.n 1732), σ (.n 1733), σ (.n 1734)]

/-- The salted child proof, the index `j` of its size and rate and the frame `fr` of its
`open_stacked` call given. -/
def vsPiOfAtK (T : WhirTabs) (rd : Reader) (σ : Val) (Vn : NFrames) (cl : E → E → ℕ) (j : ℕ)
    (fr : Val) : Proof :=
  ⟨wordsFrom rd ((σ (.n 29)).limb 0) (cl (σ (.n 29)) (σ (.n 683))) ++
      wordsFrom rd ((fr (.n 9)).limb 0) (T.words.getD j 0),
    (T.calls.getD j []).map (levelOsAK T.lanes rd fr Vn)⟩

/-- The salted child proof, its size `m` and the index `j` of its size and rate given: the frame of
`open_stacked__L{m}`'s call (salted function `310 + m`) read once. -/
def vsPiOfMK (T : WhirTabs) (rd : Reader) (σ : Val) (Vn : NFrames) (cl : E → E → ℕ) (m j : ℕ) :
    Proof :=
  vsPiOfAtK T rd σ Vn cl j (Vn (310 + m) (vsOsArgsSK σ) (vsOsRetsSK σ))

/-- The salted child proof, its size `m` given. -/
def vsPiOfSK (T : WhirTabs) (rd : Reader) (σ : Val) (Vn : NFrames) (cl : E → E → ℕ) (m : ℕ) :
    Proof :=
  vsPiOfMK T rd σ Vn cl m (logGTWith T.lanes (σ (.n 126)) 4 * 11 + m)

/-- **The child proof the salted `verify_sub` checks, off the tables `T`.** -/
def vsPiOfAK (T : WhirTabs) (rd : Reader) (σ : Val) (Vn : NFrames) (cl : E → E → ℕ) : Proof :=
  vsPiOfSK T rd σ Vn cl (logGTWith T.lanes (σ (.n 1725)) 11)

/-- **A child's proof at its salted `verify_sub` (`19`) call's words**, the tables `T` given. -/
def proofAtFrameK (T : WhirTabs) (rd : Reader) (Vn : NFrames) (cl : E → E → ℕ) (args : List E) :
    Proof :=
  vsPiOfAK T rd (Vn 19 args []) Vn cl

cost_compile oqBsKC := oqBsK
cost_compile oqPadNC := oqPadN
cost_compile oqOutKC := oqOutK
cost_compile oqKLKC := oqKLK
cost_compile oqEndKC := oqEndK
cost_compile oqE1KC := oqE1K
cost_compile oqKeyVC := oqKeyV
cost_compile oqWalkArgsSKC := oqWalkArgsSK
cost_compile oqLoopArgsSKC := oqLoopArgsSK
cost_compile OsCallQargsKC := OsCall.qargsK
set_option maxRecDepth 100000 in
cost_compile osCallsTabKC := osCallsTabK
cost_compile whirTabsKC := whirTabsK
cost_compile oqQueryAtKC := oqQueryAtK
cost_compile oqQueryAKC := oqQueryAK
cost_compile oqIterAKC := oqIterAK
cost_compile oqItersFromKC measure fun _ _ _ _ _ _ _ n _ ↦ n := oqItersFromK
cost_compile oqsOfAKC := oqsOfAK
cost_compile levelOsAtKC := levelOsAtK
cost_compile levelOsQKC := levelOsQK
cost_compile levelOsAKC := levelOsAK
cost_compile vsOsArgsSKC := vsOsArgsSK
cost_compile vsOsRetsSKC := vsOsRetsSK
cost_compile vsPiOfAtKC := vsPiOfAtK
cost_compile vsPiOfMKC := vsPiOfMK
cost_compile vsPiOfSKC := vsPiOfSK
cost_compile vsPiOfAKC := vsPiOfAK
cost_compile proofAtFrameKC := proofAtFrameK

end

end LeanVM.SaltedGuest.Decoder
