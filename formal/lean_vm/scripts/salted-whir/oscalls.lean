/-
  The salted `level_queries` dispatches of each size and rate, printed for `osgen.py`:
  `lake env lean scripts/salted-whir/oscalls.lean > FILE` after `lake build`.
-/
import LeanVM.Guest.Fast.WhirTablesCheck
import LeanVM.SaltedGuest.B1.Whir.OqSoundK

open LeanVM.Guest.Core LeanVM.Guest.B1 LeanVM.Guest.B1.Whir LeanVM.Guest.Fast LeanVM.SaltedGuest.B1.Whir

/-- One dispatch: its shape, odd query, iterations, depth and cap depth; its argument cells (and
their paths' lengths) and return cells; its callee, the `opening_queries` call in it, the call's
loop helper and `walk_path`; the call's argument and return cells. -/
def row (lvl : ℕ) (lv : OsLv) (args rets : List V) : String :=
  let q := lqCallK lvl lv
  let s := lvOq lvl lv
  s!"{s.base} {s.I} {s.pd} {s.cd} {lv.queries % 2 * (if lvl = 0 then 1 else 0)} " ++
  s!"{lv.queries / (1 + if lvl = 0 then 1 else 0)} {lv.depth} {lv.capDepth} | " ++
  s!"{args.map (·.idx)} {args.map (·.path.length)} | {rets.map (·.idx)} | " ++
  s!"{osQueriesName lvl lv} {q.1} {oqLoopOfK (oqNameOf lvl lv)} {oqWalkOf s} | " ++
  s!"{q.2.1.map (·.idx)} {q.2.2.map (·.idx)}"

#eval do
  for j in List.range 44 do
    for c in osCallsOf j do
      IO.println s!"{j} {row c.1 c.2.1 c.2.2.2.1 c.2.2.2.2}"
