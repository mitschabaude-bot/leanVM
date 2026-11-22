/-
  LeanVM.SaltedGuest.B1.Opening.QueriesTK

  The salted `opening_queries` and its loop helper as templates over the shape of a level: the
  key's cells loaded from the cap's buffer, the leaf hashed from the key's state.
-/

module

public import LeanVM.Guest.B1.Opening.QueriesT

/-!
# The templates of the salted `opening_queries`

The deployed templates (`Guest/B1/Opening/QueriesT.lean`) with the leaf hash continued from the key's
state (`keccak_cells(…, state=ks)`, the key's cells `ks` loaded from the cap's buffer after its
`4·2^cd` cells): every block of the leaf hash, block `0` too, XORs its row cells into the previous
state (the key's cells for block `0`), so a block is `22` values (`oqBsK`); the padding run
(`oqPadT`, `1` then four zeros) is emitted at the `0x01` padding cell, not before the hash
(`oqXorTK`); a query reusing the run reads it at `oqPadPosK` of the first query.

The specialization's values from `9` on are the deployed ones moved by `13` (the key's loads
`9 .. 21`), its loop helper's from `5` on (the key's cells its parameters `5 .. 17`).
-/

namespace LeanVM.SaltedGuest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-! ## The leaf hash from the key's state -/

/-- The first value of block `k` of the keyed leaf hash. -/
def oqBsK (kL k : ℕ) : ℕ := kL + 22 * k

/-- The values the padding run takes in block `k` of a query that emits it: five in the last
block. -/
def oqPadN (s : Oq) (emit : Bool) (k : ℕ) : ℕ := if emit ∧ k + 1 = s.B then 5 else 0

/-- Cell `c` of the state after block `k` (`k < B`): block `k`'s outputs. -/
def oqOutK (s : Oq) (emit : Bool) (kL k c : ℕ) : ℕ :=
  if k + 1 = s.B then oqBsK kL k + 10 + oqPadN s emit k + c else oqBsK kL k + 9 + c

/-- Cell `c` of the state before block `k`: the key's cell (values `kc ..`) before block `0`. -/
def oqPrevK (s : Oq) (emit : Bool) (kc kL k c : ℕ) : ℕ :=
  if k = 0 then kc + c else oqOutK s emit kL (k - 1) c

/-- Block `k`'s input cell `c < 9`: the previous state's cell plus the packed cell, the padding
`0x01` (the run's first cell, the run emitted there by a query that emits it) or the padding
`0x80` (a constant), as the cell index is a row cell, the cell after it or the next. -/
def oqXorTK (s : Oq) (emit : Bool) (b pr kc kL k c : ℕ) : List Stmt :=
  let m := 17 * k / 2 + c
  let t := oqBsK kL k + c
  if m < s.ncells then [.atom (.add (.n t) (.n (oqPrevK s emit kc kL k c)) (.n (oqPk b s.R m)))]
  else if m = s.ncells then
    (if emit then oqPadT t else []) ++
      [.atom (.add (.n (t + oqPadN s emit k)) (.n (oqPrevK s emit kc kL k c))
        (.n (if emit then t else pr)))]
  else [.atom (.const (.n (t + oqPadN s emit k)) (oqW80 s)),
    .atom (.add (.n (t + oqPadN s emit k + 1)) (.n (oqPrevK s emit kc kL k c))
      (.n (t + oqPadN s emit k)))]

/-- Block `k`'s input cell `c < 9`'s value. -/
def oqInK (s : Oq) (emit : Bool) (kL k c : ℕ) : ℕ :=
  if 17 * k / 2 + c < s.ncells then oqBsK kL k + c
  else if 17 * k / 2 + c = s.ncells then oqBsK kL k + c + oqPadN s emit k
  else oqBsK kL k + c + oqPadN s emit k + 1

/-- Block `k` of the keyed leaf hash: its input cells, then its `KECCAK` on them and the previous
state's capacity. -/
def oqBlockTK (s : Oq) (emit : Bool) (b pr kc kL k : ℕ) : List Stmt :=
  ((List.range 9).map (oqXorTK s emit b pr kc kL k)).flatten ++
    [.atom (.keccak (((List.range 9).map fun c ↦ .n (oqInK s emit kL k c)) ++
        ((List.range 4).map fun c ↦ .n (oqPrevK s emit kc kL k (9 + c))))
      ((List.range (oqOutN s k)).map fun c ↦ .n (oqOutK s emit kL k c)) (Keccak.inLayout k)
        (Keccak.outLayout s.B k))]

/-- The keyed leaf hash. -/
def oqLeafTK (s : Oq) (emit : Bool) (b pr kc kL : ℕ) : List Stmt :=
  ((List.range s.B).map (oqBlockTK s emit b pr kc kL)).flatten

/-! ## One query -/

/-- The first value of the keyed leaf hash: after the dot product. -/
def oqKLK (s : Oq) (b : ℕ) : ℕ := oqK1 b s.R + s.D

/-- The padding run's first value in a query that emits it: the `0x01` cell of the last block. -/
def oqPadPosK (s : Oq) (b : ℕ) : ℕ :=
  oqBsK (oqKLK s b) (s.B - 1) + (s.ncells - 17 * (s.B - 1) / 2)

/-- The first value after a query. -/
def oqEndK (s : Oq) (b : ℕ) (emit : Bool) : ℕ := oqOutK s emit (oqKLK s b) (s.B - 1) 2

/-- **One salted query** from the value `b`, its windows at `bp`, the key's cells at `kc ..`,
emitting the padding run (`emit`) or reusing the one at `pr`: the row, its dot product, the keyed
leaf hash, and the call of `walk` on the leaf digest, the windows, the cap and the flags. -/
def oqQueryTK (s : Oq) (bp cap flags wp : V) (b : ℕ) (emit : Bool) (pr kc : ℕ) (walk : String) :
    List Stmt :=
  oqRowT b s.R ++ oqPacksT b s.R ++ oqDotT s wp b ++ oqLeafTK s emit b pr kc (oqKLK s b) ++
    [.call walk [.n (oqOutK s emit (oqKLK s b) (s.B - 1) 0),
      .n (oqOutK s emit (oqKLK s b) (s.B - 1) 1), bp, cap, flags] []]

/-! ## The loop and the function -/

/-- The key's cells' values: `kc .. kc + 12`. -/
def oqKeyV (kc : ℕ) : List V := (List.range 13).map fun c ↦ .n (kc + c)

/-- The first value of the second query of a level-0 iteration. -/
def oqE1K (s : Oq) : ℕ := oqEndK s 24 true

/-- The first value of a level-0 iteration's chain step. -/
def oqC1K (s : Oq) : ℕ := oqEndK s (oqE1K s + 1) false

/-- The atoms and calls of the salted loop helper's body at level 0, on its parameters
`x, N, qptrs, cap, flags, key₀ .. key₁₂, wp, chain, μ` (`0 .. 20`). -/
def oqLoop1AK (s : Oq) (odd : ℕ) (walk : String) : List Stmt :=
  let e1 := oqE1K s
  let c := oqC1K s
  [.atom (.mul (.n 21) (.n 2) (.n 0)), .atom (.mul (.n 22) (.n 21) (.n 0)),
    .atom (.load (.n 23) (.n 22) odd)] ++
    oqQueryTK s (.n 23) (.n 3) (.n 4) (.n 18) 24 true 0 5 walk ++
    [.atom (.load (.n e1) (.n 22) (odd + 1))] ++
    oqQueryTK s (.n e1) (.n 3) (.n 4) (.n 18) (e1 + 1) false (oqPadPosK s 24) 5 walk ++
    [.atom (.mul (.n c) (.n 19) (.n 0)), .atom (.load (.n (c + 1)) (.n c) 0),
      .atom (.add (.n (c + 2)) (.n (c + 1)) (.n (oqDot s 24))),
      .atom (.mul (.n (c + 3)) (.n (c + 2)) (.n 20)),
      .atom (.add (.n (c + 4)) (.n (c + 3)) (.n (oqDot s (e1 + 1)))),
      .atom (.mul (.n (c + 5)) (.n (c + 4)) (.n 20)), .atom (.mul (.n (c + 6)) (.n 19) (.n 0)),
      .atom (.load (.n (c + 5)) (.n (c + 6)) 1),
      .atom (.const (.n (c + 7)) (word 2 0 0)), .atom (.mul (.n (c + 8)) (.n 0) (.n (c + 7))),
      .atom (.add (.n (c + 9)) (.n (c + 8)) (.n 1)), .atom (.const (.n (c + 10)) (word 2 0 0)),
      .atom (.mul (.n (c + 11)) (.n 0) (.n (c + 10)))]

/-- The salted loop helper's parameters. -/
def oqLoopParamsK : List V := (List.range 21).map V.n

/-- The salted loop helper's body at level 0. -/
def oqLoop1TK (s : Oq) (odd : ℕ) (walk name : String) : List Stmt :=
  oqLoop1AK s odd walk ++
    [.callIf (.n (oqC1K s + 9)) name (.n (oqC1K s + 11) :: (List.range 20).map fun i ↦ .n (i + 1)),
      .ret []]

/-- The first value of a deeper iteration's chain step. -/
def oqC0K (s : Oq) : ℕ := oqEndK s 23 true

/-- The atoms and the call of the salted loop helper's body deeper. -/
def oqLoop0AK (s : Oq) (walk : String) : List Stmt :=
  let c := oqC0K s
  [.atom (.mul (.n 21) (.n 2) (.n 0)), .atom (.load (.n 22) (.n 21) 0)] ++
    oqQueryTK s (.n 22) (.n 3) (.n 4) (.n 18) 23 true 0 5 walk ++
    [.atom (.mul (.n c) (.n 19) (.n 0)), .atom (.load (.n (c + 1)) (.n c) 0),
      .atom (.add (.n (c + 2)) (.n (c + 1)) (.n (oqDot s 23))),
      .atom (.mul (.n (c + 3)) (.n (c + 2)) (.n 20)), .atom (.mul (.n (c + 4)) (.n 19) (.n 0)),
      .atom (.load (.n (c + 3)) (.n (c + 4)) 1),
      .atom (.const (.n (c + 5)) (word 2 0 0)), .atom (.mul (.n (c + 6)) (.n 0) (.n (c + 5))),
      .atom (.add (.n (c + 7)) (.n (c + 6)) (.n 1)), .atom (.const (.n (c + 8)) (word 2 0 0)),
      .atom (.mul (.n (c + 9)) (.n 0) (.n (c + 8)))]

/-- The salted loop helper's body deeper. -/
def oqLoop0TK (s : Oq) (walk name : String) : List Stmt :=
  oqLoop0AK s walk ++
    [.callIf (.n (oqC0K s + 7)) name (.n (oqC0K s + 9) :: (List.range 20).map fun i ↦ .n (i + 1)),
      .ret []]

/-- The first value after the salted function's start. -/
def oqMKK (s : Oq) (odd : ℕ) : ℕ := if odd = 1 then oqEndK s 26 true + 1 else 26

/-- The atoms and the call of the salted function's start, on its parameters `cap, flags, λ, λ_n,
qptrs, wp, N` (`0 .. 6`): `μ`, the key's cells from the cap's buffer, the chain, its start, the
loop's guard and start. -/
def oqMainAK (s : Oq) (odd : ℕ) (walk : String) : List Stmt :=
  let k := oqMKK s odd
  [.atom (.const (.n 7) (word 1 0 0)), .atom (.mul (.n 7) (.n 8) (.n 2))] ++
  (List.range 13).map (fun c ↦ .atom (.load (.n (9 + c)) (.n 0) (4 * 2 ^ s.cd + c))) ++
  [.atom (.const (.n 22) (word 2 0 0)), .atom (.mul (.n 23) (.n 6) (.n 22)),
    .atom (.hint (.allocDyn (.n 24) (.n 23)))] ++
  (if odd = 1 then
      [.atom (.load (.n 25) (.n 4) 0)] ++ oqQueryTK s (.n 25) (.n 0) (.n 1) (.n 5) 26 true 0 9 walk ++
        [.atom (.mul (.n (k - 1)) (.n (oqDot s 26)) (.n 8)), .atom (.load (.n (k - 1)) (.n 24) 0)]
    else [.atom (.const (.n 25) (word 0 0 0)), .atom (.load (.n 25) (.n 24) 0)]) ++
  [.atom (.const (.n k) (word 1 0 0)), .atom (.add (.n (k + 1)) (.n k) (.n 6)),
    .atom (.const (.n (k + 2)) (word 1 0 0))]

/-- The salted function's body: the start, the loop, the chain's end times `λ_n`. -/
def oqMainTK (s : Oq) (odd : ℕ) (walk loop : String) : List Stmt :=
  let k := oqMKK s odd
  oqMainAK s odd walk ++
    [.callIf (.n (k + 1)) loop ([.n (k + 2), .n 6, .n 4, .n 0, .n 1] ++ oqKeyV 9 ++
        [.n 5, .n 24, .n 8]),
      .atom (.mul (.n (k + 3)) (.n 24) (.n 6)), .atom (.load (.n (k + 4)) (.n (k + 3)) 0),
      .atom (.mul (.n (k + 5)) (.n (k + 4)) (.n 3)), .ret [.n (k + 5)]]

end
end LeanVM.SaltedGuest.B1
