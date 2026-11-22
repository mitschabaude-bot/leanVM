/-
  LeanVM.SaltedGuest.Decoder.WhirTablesDefs

  What the salted dispatches' table is checked against: the template's dispatches, in numbers.
-/

module

public import LeanVM.SaltedGuest.Decoder.WhirTables
public import LeanVM.Guest.Fast.WhirTablesCheck
public import LeanVM.SaltedGuest.B1.Whir.OqSoundK

/-!
# The salted dispatches' table: the check

* `nameK j`: the name of the salted function `j` (`1 ≤ j ≤ 1538`, `fnIdxK`), and
  `nameIndex_nameK`: its index is `j`;
* `callMatchK r c`: the `OsCall` `r` is the template's `level_queries` dispatch `c` (`osQCalls`,
  `open_stacked` being unchanged, the deployed template's) in numbers: its shape, odd query,
  iterations, depth, its arguments' and returns' cells, its callee the salted `level_queries`
  specialization of index `r.lq`, whose `opening_queries` call (`lqCallK`) is `r.fn`'s on the cells
  `r.qargsK` returning `r.pw + 2`, its loop and its queries' `walk_path` the salted functions of
  `r`'s indices;
* `CallsOKK j`: the table's row `j` is the template's, `WhirTablesCheck/C*.lean`.
-/

namespace LeanVM.SaltedGuest.Decoder

open LeanVM.Guest.Core LeanVM.Guest.B1 LeanVM.Guest.B1.Whir LeanVM.Guest.Fast
open LeanVM.SaltedGuest.B1.Whir

@[expose] public section

/-- **The name of the salted function `j`.** -/
noncomputable def nameK (j : ℕ) : String := (SaltedGuest.coreProgram.getD (j - 1) default).name

/-- Whether `j` is a salted function's index but `main`'s. -/
def fnIdxK (j : ℕ) : Bool := decide (1 ≤ j) && decide (j ≤ 1538)

/-- **The index of the salted function `j`'s name is `j`.** -/
theorem nameIndex_nameK {j : ℕ} (h : fnIdxK j = true) : nameIndex (nameK j) = j := by
  simp only [fnIdxK, Bool.and_eq_true, decide_eq_true_eq] at h
  have hl : j - 1 < SaltedGuest.coreProgram.length := by
    rw [SaltedGuest.coreProgram_length]; omega
  unfold nameIndex nameK
  rw [List.getD_eq_getElem _ _ hl, findIdx_name_of_nodup coreProgram_names_nodup hl]
  omega

/-- **The table's call `r` is the template's salted dispatch `c`.** -/
noncomputable def callMatchK (r : OsCall) : ℕ × OsLv × String × List V × List V → Bool
  | (lvl, lv, _, args, rets) =>
    r.base == (lvOq lvl lv).base && r.I == (lvOq lvl lv).I && r.pd == (lvOq lvl lv).pd &&
      r.cd == (lvOq lvl lv).cd && r.odd == lv.queries % 2 * (if lvl = 0 then 1 else 0) &&
      r.N == lv.queries / (1 + if lvl = 0 then 1 else 0) && r.depth == lv.depth &&
      r.cd == lv.capDepth && r.args == args.map vIdx && r.rets == rets.map vIdx &&
      args.all isN && rets.all isN && fnIdxK r.lq && nameK r.lq == osQueriesName lvl lv &&
      fnIdxK r.fn &&
      decide (lqCallK lvl lv = (nameK r.fn, r.qargsK.map V.n, [V.n (r.pw + 2)])) &&
      fnIdxK r.loop && nameK r.loop == oqLoopOfK (oqNameOf lvl lv) &&
      fnIdxK r.walk && nameK r.walk == oqWalkOf (lvOq lvl lv)

/-- The salted table's row `j` is the template's dispatches at `j`. -/
def CallsOKK (j : ℕ) : Prop :=
  (osCallsTabK.getD j []).length = (osCallsOf j).length ∧
    ((osCallsTabK.getD j []).zip (osCallsOf j)).all (fun p ↦ callMatchK p.1 p.2) = true

end

end LeanVM.SaltedGuest.Decoder
