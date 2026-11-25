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
moved by `mainR` (the deployed `.n k` is the salted `.n (mainRi k)`) and six changes: the cap on
the two regions' slots `.n 24` at `2^20 - 1`, by two hinted digits in base `2^10` (`.n 26`, `.n 27`,
each range-checked against `g^1023`, `.n 28` and `.n 32`), the first's `2^10`-th power by ten
squarings (`.n 36` to `.n 45`) times the second (`.n 46`) asserted equal to `.n 24`; the seed's
cells loaded from memory words `2` and `3` (`.n 50`, `.n 54`) in place of the `fs_seed` hint, the
key computed from them (`key_of_seed`, `.n 55`), the claim lists' digests under the key, the DA
branch's digest the keyed hash of the DA claim's four cells (one `KECCAK` on the key's cells,
`keyed_node`), the children's loop `__loop4` and the batching taking the key and the seed's cells; and the node
count: the buffers `child_count` (`.n 451`) and `count_run` (`.n 454`, its first cell `g`, `.n 455`)
passed to `__loop4`, and the node's count `count_run[n_children]` (`.n 500`) hashed into its
statement. The blocks are at the deployed positions moved by `26` (the cap, the seed's loads and
the key) and by `48` in the DA branch. The node count's three values have no deployed counterpart:
`mainR` takes them at the numbers `1000`, `1001`, `1002`.
-/

namespace LeanVM.SaltedGuest.B1.Main

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Guest.Value.Keccak LeanVM.Guest.B1 LeanVM.Guest.B1.Digest
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Node LeanVM.Guest.B1.Main LeanVM.SaltedGuest.B1 Recursion.Salted LeanVM.Guest.B1.Da

@[expose] public section

/-! ## The value map -/

/-- The salted value of a deployed `main`'s value `k`. -/
def mainRiD (k : ℕ) : ℕ :=
  if k < 26 then k else if k = 26 then 50 else if k = 27 then 54 else if k = 379 then 429
  else if k = 380 then 430 else if k < 381 then k + 28 else if k < 401 then k + 50
  else if k < 444 then k + 55 else k + 57

/-- The salted value of `main`'s value `k` at the deployed numbering: a deployed value's
(`mainRiD`), and the node count's three values at `1000`, `1001`, `1002`. -/
def mainRi (k : ℕ) : ℕ :=
  if k < 1000 then mainRiD k else if k = 1000 then 451 else if k = 1001 then 454 else 500

/-- The salted value of a deployed `main`'s value. -/
def mainR (v : V) : V := ⟨v.path, v.tag, mainRi v.idx⟩

/-! ## The shape -/

noncomputable def mPreS : List Stmt := (Fn.body LeanVM.SaltedGuest.Data.core0).take 641
noncomputable def mDaS : List Stmt := match (Fn.body LeanVM.SaltedGuest.Data.core0).getD 641 default with
  | .ite _ z _ => z
  | _ => []
noncomputable def mDaZS : List Stmt := match (Fn.body LeanVM.SaltedGuest.Data.core0).getD 641 default with
  | .ite _ _ n => n
  | _ => []
noncomputable def mMidS : List Stmt := ((Fn.body LeanVM.SaltedGuest.Data.core0).drop 642).take 45
noncomputable def mLeafS : List Stmt := match (Fn.body LeanVM.SaltedGuest.Data.core0).getD 687 default with
  | .ite _ z _ => z
  | _ => []
noncomputable def mAggS : List Stmt := match (Fn.body LeanVM.SaltedGuest.Data.core0).getD 687 default with
  | .ite _ _ n => n
  | _ => []
noncomputable def mPostS : List Stmt := ((Fn.body LeanVM.SaltedGuest.Data.core0).drop 688).take 13

set_option maxRecDepth 100000 in
theorem core0_shapeS : Fn.body LeanVM.SaltedGuest.Data.core0 =
    mPreS ++ [.ite (.n 396) mDaS mDaZS] ++ mMidS ++ [.ite (.n 474) mLeafS mAggS] ++ mPostS ++
      [.ret []] :=
  stmtsEqb_sound (by decide +kernel)

/-- `lx_tags`' values in the salted `main`. -/
def lxTagsVS : List V := (List.range 51).map fun j => .n (332 + j)

/-- The key's cells, loaded in the DA branch. -/
def mainKeyVl : List V := (List.range 13).map fun c => .n (401 + c)

/-- The DA digest's `KECCAK` inputs: the claim's cells added to the key's first four, then the rest
of `node_key`'s run. -/
def mainDaIn : List V := [.n 414, .n 415, .n 416, .n 417, .n 423, .n 424, .n 425, .n 426, .n 428,
  .n 410, .n 411, .n 412, .n 413]

noncomputable def preOkS : Bool :=
  let P := mPreS
  let A := atomsIn mPreS
  P.all Stmt.flat &&
  ((List.range 6).all fun v => isTouch A (.n (8 + v)) (.n v)) &&
  rcConstOk A (.n 6) 65536 && rcConstOk A (.n 7) 2 &&
  isTouch A (.n 25) (.n 24) &&
  rcConstOk A (.n 26) 140737488388109 && rcConstOk A (.n 27) 140737488388109 &&
  isMul A (.n 36) (.n 26) (.n 26) &&
  ((List.range 9).all fun i => isMul A (.n (37 + i)) (.n (36 + i)) (.n (36 + i))) &&
  isMul A (.n 46) (.n 45) (.n 27) && A.any (isAssertEqAt (.n 46) (.n 24)) &&
  isMul A (.n 22) (.n 0) (.n 1) && isMul A (.n 23) (.n 3) (.n 4) &&
  isMul A (.n 24) (.n 22) (.n 23) &&
  hasCall P "exponent_tables" [] [.n 56] &&
  A.any (isConstAt (.n 47) 1 0) && A.any (isConstAt (.n 48) 4 0) && isMul A (.n 49) (.n 47) (.n 48) &&
  isLoad A (.n 50) (.n 49) 0 &&
  A.any (isConstAt (.n 51) 1 0) && A.any (isConstAt (.n 52) 8 0) && isMul A (.n 53) (.n 51) (.n 52) &&
  isLoad A (.n 54) (.n 53) 0 &&
  hasCall P "key_of_seed" [.n 50, .n 54] [.n 55] &&
  hasCall P "claim_list_digest" [.n 55, .n 59, .n 0] [.n 63, .n 64] &&
  hasCall P "claim_list_digest" [.n 55, .n 62, .n 3] [.n 65, .n 66] &&
  ((List.range 256).all fun v => A.any (isConstAt (.n (76 + v)) v 0) &&
    A.any (isLoadAt (.n (76 + v)) (.n 75) v)) &&
  isMul A (.n 74) (.n 73) (.n 22) &&
  guardOk P (.n 384) "__loop2" (.n 385) (.n 2) ([.n 22, .n 73, .n 59] ++ lxTagsVS) &&
  ((List.range 58).all fun i => !Sig.lxTagCarried i ||
    A.any (isConstAt (.n (332 + (Sig.lxTagSlot i - 1))) i 0)) &&
  guardOk P (.n 387) "__loop3" (.n 388) (.n 5) [.n 23, .n 74, .n 2, .n 62, .n 75] &&
  isMul A (.n 393) (.n 6) (.n 6) && isMul A (.n 394) (.n 392) (.n 393) &&
  A.any (isAddAt (.n 396) (.n 7) (.n 395)) && A.any (isConstAt (.n 395) 2 0)

noncomputable def daOkS : Bool :=
  let D := mDaS
  let A := atomsIn mDaS
  D.all Stmt.flat &&
  hasCall D "da_verify" [.n 56, .n 55] [.n 397, .n 398, .n 399, .n 400] &&
  stLoadsOk A (.n 55) mainKeyVl 0 &&
  (List.range 4).all (fun i => A.any (isAddAt (.n (414 + i)) (.n (401 + i)) (.n (397 + i)))) &&
  A.any (isConstAt (.n 418) 1 0) && A.any (isAddAt (.n 423) (.n 405) (.n 418)) &&
  A.any (isCopyAt (.n 424) (.n 406)) && A.any (isCopyAt (.n 425) (.n 407)) &&
  A.any (isCopyAt (.n 426) (.n 408)) &&
  A.any (isConstAt (.n 427) 9223372036854775808 0) && A.any (isAddAt (.n 428) (.n 409) (.n 427)) &&
  A.any (isKeccakAt mainDaIn [.n 429, .n 430] false false) &&
  isLoad A (.n 429) (.n 394) 0 && isLoad A (.n 430) (.n 394) 1

noncomputable def daZOkS : Bool :=
  let A := atomsIn mDaZS
  mDaZS.all Stmt.flat &&
  A.any (isConstAt (.n 431) 0 0) && isLoad A (.n 431) (.n 394) 0 &&
  A.any (isConstAt (.n 432) 0 0) && isLoad A (.n 432) (.n 394) 1

noncomputable def midOkS : Bool :=
  let M := mMidS
  let A := atomsIn mMidS
  M.all Stmt.flat &&
  isMul A (.n 450) (.n 2) (.n 5) && isLoad A (.n 450) (.n 449) 0 &&
  A.any (isConstAt (.n 455) 2 0) && isLoad A (.n 455) (.n 454) 0 &&
  guardOk M (.n 457) "__loop4" (.n 458) (.n 6) [.n 449, .n 55, .n 59, .n 73, .n 22, .n 62, .n 74,
    .n 23, .n 446, .n 392, .n 451, .n 454, .n 50, .n 54, .n 434, .n 56, .n 440] &&
  isMul A (.n 459) (.n 449) (.n 6) && isLoad A (.n 460) (.n 459) 0 &&
  A.any (isAssertEqAt (.n 460) (.n 24)) &&
  decide (rcOf A (.n 461) = some (.n 6)) &&
  A.any (isAddAt (.n 465) (.n 461) (.n 6)) && A.any (isAddAt (.n 467) (.n 7) (.n 466)) &&
  A.any (isConstAt (.n 466) 1 0) && isMul A (.n 468) (.n 465) (.n 467) &&
  A.any (isConstAt (.n 469) 0 0) && A.any (isAssertEqAt (.n 468) (.n 469)) &&
  isMul A (.n 470) (.n 461) (.n 461) && isMul A (.n 471) (.n 392) (.n 470) &&
  A.any (isAddAt (.n 474) (.n 6) (.n 473)) && A.any (isConstAt (.n 473) 1 0)

noncomputable def leafOkS : Bool :=
  mLeafS.all Stmt.flat &&
  ((List.range 23).all fun k => (atomsIn mLeafS).any (isConstAt (.n (476 + k)) 0 0) &&
    isLoad (atomsIn mLeafS) (.n (476 + k)) (.n 472) k) &&
  isLoad (atomsIn mLeafS) (.n 475) (.n 472) 23 &&
  mAggS.all Stmt.flat &&
  hasCall mAggS "aggregate_claims" [.n 50, .n 54, .n 6, .n 434, .n 440, .n 446, .n 472] []

noncomputable def postOkS : Bool :=
  let A := atomsIn mPostS
  mPostS.all Stmt.flat &&
  isMul A (.n 499) (.n 454) (.n 6) && isLoad A (.n 500) (.n 499) 0 &&
  isLoad A (.n 501) (.n 471) 0 && isLoad A (.n 502) (.n 471) 1 &&
  hasCall mPostS "statement_digest" [.n 50, .n 54, .n 63, .n 64, .n 65, .n 66, .n 501, .n 502,
    .n 472, .n 500] [.n 503, .n 504] &&
  A.any (isConstAt (.n 505) 1 0) && isLoad A (.n 506) (.n 505) 0 &&
  A.any (isAssertEqAt (.n 506) (.n 503)) &&
  A.any (isConstAt (.n 507) 1 0) && A.any (isConstAt (.n 508) 2 0) &&
  isMul A (.n 509) (.n 507) (.n 508) && isLoad A (.n 510) (.n 509) 0 &&
  A.any (isAssertEqAt (.n 510) (.n 504))

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
