/-
  LeanVM.SaltedGuest.B1.VerifySub.Template

  The salted `verify_sub`'s body as a template, section by section.
-/

module

public import LeanVM.Guest.B1.VerifySub.Template
public import LeanVM.SaltedGuest.Glob
public import LeanVM.SaltedGuest.KernelRfl

/-!
# The salted `verify_sub` as a template

The salted `verify_sub` is the deployed one (`LeanVM.Guest.B1.VerifySub.vsT`) with its values
renumbered and four changes:

* the seed call absorbs the seed, the child's public digest and the seed again
  (`keccak_cells([s0, s1, pi0, pi1, s0, s1], sp, final=0)`): the seed's cells copied into `7`, `8`
  and two more zero cells, the zero and padding cells at `11 .. 15` (`vsHeadS`);
* the memory's log is also range-checked against four public words (`assert log(g_log_mem / g^2) <
  COUNT_BITS`, four statements after the deployed one's, `vsSizesS`);
* after `verify_tables`, the seed's binding claims: each seed cell's canonical limbs, and the
  pool's last three claims `lo + rm·(lo + lo')`, `hi + rm·(hi + hi')`, `0` at `claim_pool[167 ..
  169]` (`vsSeedClaimsS`);
* the batching over `145` pooled claims, the three new ones last (`vsLamS`).

`vsTS` is the body; `vsS_body`, by the kernel's `rfl`. The deployed sections' helpers (`vsLd`,
`vsConst`, `fsNextT`, `challengeT`, …) are reused; the squeeze's zero cells are `12 .. 15`
(`vsSqzS`).
-/

namespace LeanVM.SaltedGuest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Guest.B1 LeanVM.Guest.B1.VerifySub

@[expose] public section

/-- A squeeze with nothing waiting (the zero cell `12`, the cells `13 .. 15`), on the capacity
from `capb`, outputs from `o`, the challenge at `o + 19`. -/
def vsSqzS (capb o : ℕ) : List Stmt :=
  keccakA ([.n 12, .n 12, .n 12, .n 12, .n 12, .n 13, .n 14, .n 15] ++ vsRun capb 5) (vsRun o 13) ::
    challengeT (.n o) (.n (o + 1)) (o + 13)

/-- The pool, the seed call, the stream. -/
def vsHeadS : List Stmt :=
  [vsAlloc 6 170, .atom (.copy (.n 7) (.n 2)), .atom (.copy (.n 8) (.n 3)),
    vsConst 9 (word 0 0 0), vsConst 10 (word 0 0 0), vsConst 11 (word 1 0 0),
    vsConst 12 (word 0 0 0), vsConst 13 (word 0 0 0), vsConst 14 (word 0 0 0),
    vsConst 15 (word 0 0 0),
    keccakA [.n 2, .n 3, .n 0, .n 1, .n 7, .n 8, .n 9, .n 10, .n 12, .n 12, .n 13, .n 14, .n 15]
      (vsRun 16 13),
    vsAlloc 29 8192, .atom (.hint (.witness "stream" (.heap (.n 29) 0 8192))), vsAlloc 30 6]

/-- The eight announced words: `x_i` at `31 + 10 i` (`i < 4`) and `84 + 10 (i - 4)`, rows `1 .. 6`
stored in `table_rows`, the first four absorbed after the fourth. -/
def vsReadsS : List Stmt :=
  fsNextT (.n 29) 0 31 ++ fsNextT (.n 29) 1 41 ++ [vsLd 41 30 0] ++ fsNextT (.n 29) 2 51 ++
    [vsLd 51 30 1] ++ fsNextT (.n 29) 3 61 ++ [vsLd 61 30 2] ++
    [keccakA [.n 38, .n 40, .n 48, .n 50, .n 58, .n 60, .n 68, .n 70, .n 24, .n 25, .n 26, .n 27,
      .n 28] (vsRun 71 13)] ++
    fsNextT (.n 29) 4 84 ++ [vsLd 84 30 3] ++ fsNextT (.n 29) 5 94 ++ [vsLd 94 30 4] ++
    fsNextT (.n 29) 6 104 ++ [vsLd 104 30 5] ++ fsNextT (.n 29) 7 114

/-- The rate and the memory's log as `g`-powers, its range checks (the four public words' last),
`dims_g`, `kb` in the frame and `kappa_base`. -/
def vsSizesS : List Stmt :=
  [vsCall "g_power_of_word" [114] [124], vsConst 125 (word 2 0 0), vsMul 124 126 125,
    vsConst 127 (word 8 0 0), vsRange 126 128 129 130 127, vsAlloc 131 7,
    vsCall "g_power_of_word" [31] [132], vsConst 133 (word (2 ^ 30) 0 0),
    vsRange 132 134 135 136 133, vsConst 137 (word (2 ^ 32) 0 0), vsConst 138 (word 2 0 0),
    vsMul 132 139 138, vsRange 139 140 141 142 137, vsConst 143 (word (2 ^ 32) 0 0),
    vsConst 144 (word 4 0 0), vsMul 132 145 144, vsRange 145 146 147 148 143, vsLd 132 131 0,
    .atom (.hint (.witness "table_logs" (.heap (.n 131) 1 6))), vsAlloc 149 8,
    vsConst 150 (word 1 0 0), .atom (.copy (.n 151) (.n 132))] ++
  (List.range 6).map (fun t ↦ vsLd (152 + t) 131 (1 + t)) ++
  (List.range 8).map (fun i ↦ vsLd (150 + i) 149 i)

/-- The running product after push block `b`. -/
def vsPVS (b : ℕ) : ℕ := 159 + 3 * b

/-- Push block `b`: `g_squares[kb[src] · g^adj]`, multiplied in. -/
def vsPushStepS (b : ℕ) : List Stmt :=
  if b = 0 then [vsMul 158 4 (150 + Tables.blockKappaSrc.getD 0 0), vsLd 159 158 (Tables.blockKappaAdj 0)]
  else [vsMul (157 + 3 * b) 4 (150 + Tables.blockKappaSrc.getD b 0),
    vsLd (158 + 3 * b) (157 + 3 * b) (Tables.blockKappaAdj b),
    vsMul (vsPVS b) (vsPVS (b - 1)) (158 + 3 * b)]

/-- The push blocks' total, the bus depth, `zeta`. -/
def vsPushS : List Stmt :=
  (List.range 54).flatMap vsPushStepS ++
    [vsCall "log2_ceil_in_the_exponent__L0_L34" [318, 4] [319],
      .atom (.hint (.allocDyn (.n 320) (.n 319)))]

/-- The last four words absorbed, the root read and checked. -/
def vsRootsS : List Stmt :=
  [keccakA [.n 91, .n 93, .n 101, .n 103, .n 111, .n 113, .n 121, .n 123, .n 79, .n 80, .n 81,
    .n 82, .n 83] (vsRun 321 13)] ++
  fsNextT (.n 29) 8 334 ++ fsNextT (.n 29) 9 344 ++
  [vsCall "assert_canonical" [334] [354], vsCall "assert_canonical" [344] [355], vsAlloc 356 4]

/-- The four bus challenges, the first with the root waiting. -/
def vsAlphasS : List Stmt :=
  keccakA [.n 341, .n 343, .n 351, .n 353, .n 12, .n 13, .n 14, .n 15, .n 329, .n 330, .n 331,
    .n 332, .n 333] (vsRun 357 13) :: challengeT (.n 357) (.n 358) 370 ++ [vsLd 376 356 0] ++
  vsSqzS 365 377 ++ [vsLd 396 356 1] ++ vsSqzS 385 397 ++ [vsLd 416 356 2] ++
  vsSqzS 405 417 ++ [vsLd 436 356 3]

/-- One factor of `eq_weight(bus_alpha, 4, x, 0)` at `v`. -/
def vsEqwFactorS (x t v : ℕ) : List Stmt × ℕ × ℕ :=
  if x.testBit t then ([vsLd v 356 t], v, v + 1)
  else ([vsLd v 356 t, vsConst (v + 1) (word 1 0 0), vsAdd (v + 2) (v + 1) v], v + 2, v + 3)

/-- `eq_weight(bus_alpha, 4, x, 0)` from `v`. -/
def vsEqwS (x v : ℕ) : List Stmt × ℕ × ℕ :=
  let f0 := vsEqwFactorS x 0 v
  let f1 := vsEqwFactorS x 1 f0.2.2
  let p1 := f1.2.2
  let f2 := vsEqwFactorS x 2 (p1 + 1)
  let p2 := f2.2.2
  let f3 := vsEqwFactorS x 3 (p2 + 1)
  let p3 := f3.2.2
  (f0.1 ++ f1.1 ++ [vsMul p1 f0.2.1 f1.2.1] ++ f2.1 ++ [vsMul p2 p1 f2.2.1] ++ f3.1 ++
    [vsMul p3 p2 f3.2.1], p3, p3 + 1)

/-- The first value of `fp_w[x]`'s block. -/
def vsFpwStartS : ℕ → ℕ
  | 0 => 438
  | x + 1 => (vsEqwS x (vsFpwStartS x)).2.2

/-- `fp_w`, then `β`. -/
def vsFpwS : List Stmt :=
  vsAlloc 437 16 :: (List.range 16).flatMap (fun x ↦
    (vsEqwS x (vsFpwStartS x)).1 ++ [vsLd (vsEqwS x (vsFpwStartS x)).2.1 437 x]) ++ vsSqzS 425 614

/-- The bus's GKR and the tables. -/
def vsCalls1S : List Stmt :=
  [vsConst 634 (word 1024 0 0), vsMul 635 29 634,
    vsCall "verify_bus_gkr" [622, 623, 624, 625, 626, 635, 319, 320] ((List.range 9).map (636 + ·)),
    vsAlloc 645 34,
    vsCall "verify_tables" [636, 637, 638, 639, 640, 641, 0, 1, 320, 319, 131, 30, 4, 437, 633, 6,
      645, 642, 643, 644] ((List.range 10).map (646 + ·))]

/-- The seed's binding claims after `verify_tables` (`rm` at `654`): each seed cell's canonical
limbs, the pool's last three claims. -/
def vsSeedClaimsS : List Stmt :=
  [.atom (.hint (.limbs (.n 2) [.n 656])), vsAdd 657 2 656, vsConst 658 (word 1 0 1),
    vsMul 659 657 658, .atom (.assertInK (.n 656) (.n 659)), .atom (.copy (.n 660) (.n 656)),
    .atom (.hint (.limbs (.n 3) [.n 661])), vsAdd 662 3 661, vsConst 663 (word 1 0 1),
    vsMul 664 662 663, .atom (.assertInK (.n 661) (.n 664)), .atom (.copy (.n 665) (.n 661)),
    vsAdd 666 660 665, vsMul 667 654 666, vsAdd 668 660 667, vsLd 668 6 167, vsAdd 669 659 664,
    vsMul 670 654 669, vsAdd 671 659 670, vsLd 671 6 168, vsConst 672 (word 0 0 0),
    vsLd 672 6 169]

/-- The Keccak reduction. -/
def vsCalls2S : List Stmt :=
  [vsLd 673 131 6, vsAlloc 674 78, vsAlloc 675 64, vsConst 676 (word 237494511599616 0 0),
    vsMul 677 655 676,
    vsCall "verify_keccak" [646, 647, 648, 649, 650, 651, 673, 645, 677, 674, 675]
      ((List.range 8).map (678 + ·))] ++
  (List.range 5).map fun i ↦ .atom (.copy (.n (686 + i)) (.n (678 + i)))

/-- The ring map's challenges. -/
def vsMapsS : List Stmt :=
  [vsAlloc 691 6, vsAlloc 692 64, vsLd 685 691 0] ++
  vsSqzS 686 693 ++ [vsLd 712 691 1] ++ vsSqzS 701 713 ++ [vsLd 732 691 2] ++
  vsSqzS 721 733 ++ [vsLd 752 691 3] ++ vsSqzS 741 753 ++ [vsLd 772 691 4] ++
  vsSqzS 761 773 ++ [vsLd 792 691 5]

/-- `v ↦ v²`, `s` times, from `v`. -/
def vsSqChainS (v s : ℕ) : List Stmt := (List.range s).map fun k ↦ vsMul (v + 1 + k) (v + k) (v + k)

/-- Slot `slot` of a stage of shift `s` with challenge `mc`, from `v`. -/
def vsSlotS (mc s slot v : ℕ) : List Stmt :=
  vsLd v 692 (2 * s * slot) :: vsSqChainS v s ++
    [vsMul (v + s + 1) mc (v + s), vsLd (v + s + 1) 692 (2 * s * slot + s)]

/-- Stage `st` of shift `s` from `b`. -/
def vsStageS (st s b : ℕ) : List Stmt :=
  vsLd b 691 st :: (List.range (32 / s)).flatMap fun slot ↦ vsSlotS b s slot (b + 1 + slot * (s + 2))

/-- `c_table`, then `ring_switch_target`. -/
def vsCtabS : List Stmt :=
  [vsConst 793 (word 1 0 0), vsLd 793 692 0] ++ vsStageS 0 32 794 ++ vsStageS 1 16 829 ++
    vsStageS 2 8 866 ++ vsStageS 3 4 907 ++ vsStageS 4 2 956 ++ vsStageS 5 1 1021 ++
    [vsCall "ring_switch_target" [675, 691] [1118]]

/-- Where pooled claim `j`'s value is: `col_eval_words` (`655`) from `j - 5` for the tables'
`159`, else `claim_pool` (`6`). -/
def vsClaimAtS (j : ℕ) : ℕ × ℕ := if 5 ≤ j ∧ j < 164 then (655, j - 5) else (6, j)

/-- The power of `λ` before batched claim `i`. -/
def vsPwS (i : ℕ) : ℕ := if i = 0 then 1138 else 1138 + 4 * i

/-- The target before batched claim `i`. -/
def vsTgS (i : ℕ) : ℕ := if i = 0 then 1118 else 1137 + 4 * i

/-- Batched claim `i`. -/
def vsLamStepS (i : ℕ) : List Stmt :=
  [vsLd (1139 + 4 * i) (vsClaimAtS (vsKept i)).1 (vsClaimAtS (vsKept i)).2,
    vsMul (1140 + 4 * i) (vsPwS i) (1139 + 4 * i), vsAdd (1141 + 4 * i) (vsTgS i) (1140 + 4 * i),
    vsMul (1142 + 4 * i) (vsPwS i) 1138]

/-- The batching challenge, the target over the `145` pooled claims. -/
def vsLamS : List Stmt :=
  vsSqzS 781 1119 ++ (List.range 145).flatMap vsLamStepS ++
    [vsMul 1719 1718 684, vsAdd 1720 1717 1719]

/-- The placement, the stack's log and its size selector, the dispatch on the size, the terminal,
the deferred claim. -/
def vsTailS : List Stmt :=
  [vsCall "certify_placement" [149, 4] [1721, 1722],
    vsCall "log2_ceil_in_the_exponent__L16_L34" [1721, 4] [1723],
    vsConst 1724 (word 14347465658197868555 0 0), vsMul 1725 1723 1724, vsConst 1726 (word 1024 0 0),
    vsRange 1725 1727 1728 1729 1726,
    .dispatch (.n 1725) vsOpenNames
      [.n 126, .n 1127, .n 1128, .n 1129, .n 1130, .n 1131, .n 1720, .n 334, .n 344, .n 683]
      (vsRun 1730 5),
    vsCall "check_opening_terminal" [4, 320, 645, 654, 319, 652, 132, 673, 149, 1138, 1722, 674,
      692, 1731, 1732, 1733, 1734, 1730] []] ++
  (List.range 19).flatMap (fun k ↦ [vsLd (1735 + k) 320 k, vsLd (1735 + k) 5 k]) ++
  (List.range 4).flatMap (fun k ↦ [vsLd (1754 + k) 356 k, vsLd (1754 + k) 5 (19 + k)]) ++
  [vsLd 653 5 23, .ret []]

/-- **The salted `verify_sub`'s body as a template.** -/
def vsTS : List Stmt :=
  vsHeadS ++ vsReadsS ++ vsSizesS ++ vsPushS ++ vsRootsS ++ vsAlphasS ++ vsFpwS ++
    vsCalls1S ++ vsSeedClaimsS ++ vsCalls2S ++ vsMapsS ++ vsCtabS ++ vsLamS ++ vsTailS

set_option maxRecDepth 100000 in
kernel_rfl vsS_body : (LeanVM.SaltedGuest.coreOf 19).body = vsTS

end
end LeanVM.SaltedGuest.B1.VerifySub
