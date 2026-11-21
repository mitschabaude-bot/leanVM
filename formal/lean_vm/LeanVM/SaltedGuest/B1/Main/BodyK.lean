/-
  LeanVM.SaltedGuest.B1.Main.BodyK

  The salted `main`'s body, checked by kernel evaluation.
-/

module

public import LeanVM.SaltedGuest.B1.Main.BatchK
public import LeanVM.SaltedGuest.B1.Main.KeyOfSeed
public import LeanVM.SaltedGuest.B1.Digest.ClaimList
public import LeanVM.SaltedGuest.B1.Digest.ChildDigest
public import LeanVM.Guest.B1.Main.Final

/-!
# The salted `main`'s body

The salted `main` (`core0`) is the deployed one (`Main.preOk` … `Main.postOk`) with its values
moved by `mainR` (the deployed `.n k` is the salted `.n (mainRi k)`) and five changes: the seed's
cells loaded from memory words `2` and `3` (`.n 29`, `.n 33`) in place of the `fs_seed` hint, the
key computed from them (`key_of_seed`, `.n 34`), the claim lists' digests under the key, the DA
branch's digest the keyed hash of the DA claim's four cells (one `KECCAK` on the key's cells,
`keyed_node`), the children's loop `__loop4` and the batching taking the key and the seed's cells.
The blocks are at the deployed positions moved by `8` (the seed's loads and the key) and by `30` in
the DA branch.
-/

namespace LeanVM.SaltedGuest.B1.Main

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Guest.Value.Keccak LeanVM.Guest.B1 LeanVM.Guest.B1.Digest
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Node LeanVM.Guest.B1.Main LeanVM.SaltedGuest.B1 Recursion.Salted LeanVM.Guest.B1.Da

@[expose] public section

/-! ## The value map -/

/-- The salted value of the deployed `main`'s value `k`. -/
def mainRi (k : ℕ) : ℕ :=
  if k < 26 then k else if k = 26 then 29 else if k = 27 then 33 else if k < 369 then k + 7
  else if k < 373 then k + 7 else if k = 379 then 408 else if k = 380 then 409
  else if k < 381 then k + 7 else k + 29

/-- The salted value of a deployed `main`'s value. -/
def mainR (v : V) : V := ⟨v.path, v.tag, mainRi v.idx⟩

/-! ## The shape -/

noncomputable def mPreS : List Stmt := (Fn.body LeanVM.SaltedGuest.Data.core0).take 623
noncomputable def mDaS : List Stmt := match (Fn.body LeanVM.SaltedGuest.Data.core0).getD 623 default with
  | .ite _ z _ => z
  | _ => []
noncomputable def mDaZS : List Stmt := match (Fn.body LeanVM.SaltedGuest.Data.core0).getD 623 default with
  | .ite _ _ n => n
  | _ => []
noncomputable def mMidS : List Stmt := ((Fn.body LeanVM.SaltedGuest.Data.core0).drop 624).take 39
noncomputable def mLeafS : List Stmt := match (Fn.body LeanVM.SaltedGuest.Data.core0).getD 663 default with
  | .ite _ z _ => z
  | _ => []
noncomputable def mAggS : List Stmt := match (Fn.body LeanVM.SaltedGuest.Data.core0).getD 663 default with
  | .ite _ _ n => n
  | _ => []
noncomputable def mPostS : List Stmt := ((Fn.body LeanVM.SaltedGuest.Data.core0).drop 664).take 11

set_option maxRecDepth 100000 in
theorem core0_shapeS : Fn.body LeanVM.SaltedGuest.Data.core0 =
    mPreS ++ [.ite (.n 375) mDaS mDaZS] ++ mMidS ++ [.ite (.n 448) mLeafS mAggS] ++ mPostS ++
      [.ret []] :=
  stmtsEqb_sound (by decide +kernel)

/-- `lx_tags`' values in the salted `main`. -/
def lxTagsVS : List V := (List.range 51).map fun j => .n (311 + j)

/-- The key's cells, loaded in the DA branch. -/
def mainKeyVl : List V := (List.range 13).map fun c => .n (380 + c)

/-- The DA digest's `KECCAK` inputs: the claim's cells added to the key's first four, then the rest
of `node_key`'s run. -/
def mainDaIn : List V := [.n 393, .n 394, .n 395, .n 396, .n 402, .n 403, .n 404, .n 405, .n 407,
  .n 389, .n 390, .n 391, .n 392]

noncomputable def preOkS : Bool :=
  let P := mPreS
  let A := atomsIn mPreS
  P.all Stmt.flat &&
  ((List.range 6).all fun v => isTouch A (.n (8 + v)) (.n v)) &&
  rcConstOk A (.n 6) 65536 && rcConstOk A (.n 7) 2 &&
  isTouch A (.n 25) (.n 24) &&
  isMul A (.n 22) (.n 0) (.n 1) && isMul A (.n 23) (.n 3) (.n 4) &&
  isMul A (.n 24) (.n 22) (.n 23) &&
  hasCall P "exponent_tables" [] [.n 35] &&
  A.any (isConstAt (.n 26) 1 0) && A.any (isConstAt (.n 27) 4 0) && isMul A (.n 28) (.n 26) (.n 27) &&
  isLoad A (.n 29) (.n 28) 0 &&
  A.any (isConstAt (.n 30) 1 0) && A.any (isConstAt (.n 31) 8 0) && isMul A (.n 32) (.n 30) (.n 31) &&
  isLoad A (.n 33) (.n 32) 0 &&
  hasCall P "key_of_seed" [.n 29, .n 33] [.n 34] &&
  hasCall P "claim_list_digest" [.n 34, .n 38, .n 0] [.n 42, .n 43] &&
  hasCall P "claim_list_digest" [.n 34, .n 41, .n 3] [.n 44, .n 45] &&
  ((List.range 256).all fun v => A.any (isConstAt (.n (55 + v)) v 0) &&
    A.any (isLoadAt (.n (55 + v)) (.n 54) v)) &&
  isMul A (.n 53) (.n 52) (.n 22) &&
  guardOk P (.n 363) "__loop2" (.n 364) (.n 2) ([.n 22, .n 52, .n 38] ++ lxTagsVS) &&
  ((List.range 58).all fun i => !Sig.lxTagCarried i ||
    A.any (isConstAt (.n (311 + (Sig.lxTagSlot i - 1))) i 0)) &&
  guardOk P (.n 366) "__loop3" (.n 367) (.n 5) [.n 23, .n 53, .n 2, .n 41, .n 54] &&
  isMul A (.n 372) (.n 6) (.n 6) && isMul A (.n 373) (.n 371) (.n 372) &&
  A.any (isAddAt (.n 375) (.n 7) (.n 374)) && A.any (isConstAt (.n 374) 2 0)

noncomputable def daOkS : Bool :=
  let D := mDaS
  let A := atomsIn mDaS
  D.all Stmt.flat &&
  hasCall D "da_verify" [.n 35, .n 34] [.n 376, .n 377, .n 378, .n 379] &&
  stLoadsOk A (.n 34) mainKeyVl 0 &&
  (List.range 4).all (fun i => A.any (isAddAt (.n (393 + i)) (.n (380 + i)) (.n (376 + i)))) &&
  A.any (isConstAt (.n 397) 1 0) && A.any (isAddAt (.n 402) (.n 384) (.n 397)) &&
  A.any (isCopyAt (.n 403) (.n 385)) && A.any (isCopyAt (.n 404) (.n 386)) &&
  A.any (isCopyAt (.n 405) (.n 387)) &&
  A.any (isConstAt (.n 406) 9223372036854775808 0) && A.any (isAddAt (.n 407) (.n 388) (.n 406)) &&
  A.any (isKeccakAt mainDaIn [.n 408, .n 409] false false) &&
  isLoad A (.n 408) (.n 373) 0 && isLoad A (.n 409) (.n 373) 1

noncomputable def daZOkS : Bool :=
  let A := atomsIn mDaZS
  mDaZS.all Stmt.flat &&
  A.any (isConstAt (.n 410) 0 0) && isLoad A (.n 410) (.n 373) 0 &&
  A.any (isConstAt (.n 411) 0 0) && isLoad A (.n 411) (.n 373) 1

noncomputable def midOkS : Bool :=
  let M := mMidS
  let A := atomsIn mMidS
  M.all Stmt.flat &&
  isMul A (.n 429) (.n 2) (.n 5) && isLoad A (.n 429) (.n 428) 0 &&
  guardOk M (.n 431) "__loop4" (.n 432) (.n 6) [.n 428, .n 34, .n 38, .n 52, .n 22, .n 41, .n 53,
    .n 23, .n 425, .n 371, .n 29, .n 33, .n 413, .n 35, .n 419] &&
  isMul A (.n 433) (.n 428) (.n 6) && isLoad A (.n 434) (.n 433) 0 &&
  A.any (isAssertEqAt (.n 434) (.n 24)) &&
  decide (rcOf A (.n 435) = some (.n 6)) &&
  A.any (isAddAt (.n 439) (.n 435) (.n 6)) && A.any (isAddAt (.n 441) (.n 7) (.n 440)) &&
  A.any (isConstAt (.n 440) 1 0) && isMul A (.n 442) (.n 439) (.n 441) &&
  A.any (isConstAt (.n 443) 0 0) && A.any (isAssertEqAt (.n 442) (.n 443)) &&
  isMul A (.n 444) (.n 435) (.n 435) && isMul A (.n 445) (.n 371) (.n 444) &&
  A.any (isAddAt (.n 448) (.n 6) (.n 447)) && A.any (isConstAt (.n 447) 1 0)

noncomputable def leafOkS : Bool :=
  mLeafS.all Stmt.flat &&
  ((List.range 23).all fun k => (atomsIn mLeafS).any (isConstAt (.n (450 + k)) 0 0) &&
    isLoad (atomsIn mLeafS) (.n (450 + k)) (.n 446) k) &&
  isLoad (atomsIn mLeafS) (.n 449) (.n 446) 23 &&
  mAggS.all Stmt.flat &&
  hasCall mAggS "aggregate_claims" [.n 29, .n 33, .n 6, .n 413, .n 419, .n 425, .n 446] []

noncomputable def postOkS : Bool :=
  let A := atomsIn mPostS
  mPostS.all Stmt.flat &&
  isLoad A (.n 473) (.n 445) 0 && isLoad A (.n 474) (.n 445) 1 &&
  hasCall mPostS "statement_digest" [.n 29, .n 33, .n 42, .n 43, .n 44, .n 45, .n 473, .n 474, .n 446]
    [.n 475, .n 476] &&
  A.any (isConstAt (.n 477) 1 0) && isLoad A (.n 478) (.n 477) 0 &&
  A.any (isAssertEqAt (.n 478) (.n 475)) &&
  A.any (isConstAt (.n 479) 1 0) && A.any (isConstAt (.n 480) 2 0) &&
  isMul A (.n 481) (.n 479) (.n 480) && isLoad A (.n 482) (.n 481) 0 &&
  A.any (isAssertEqAt (.n 482) (.n 476))

set_option maxRecDepth 100000 in
theorem pre_okS : preOkS = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem da_okS : daOkS = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem daZ_okS : daZOkS = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem mid_okS : midOkS = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem leaf_okS : leafOkS = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem post_okS : postOkS = true := by decide +kernel

end
end LeanVM.SaltedGuest.B1.Main
