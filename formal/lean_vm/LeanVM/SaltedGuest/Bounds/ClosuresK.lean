/-
  LeanVM.SaltedGuest.Bounds.ClosuresK

  The prices of the closures the salted decoder's top passes down.
-/

module

public import LeanVM.SaltedGuest.Bounds.V.Top
public import LeanVM.SaltedGuest.Bounds.V.Xmss
public import LeanVM.SaltedGuest.Bounds.DaK
public import LeanVM.SaltedGuest.Bounds.WhirK
public import LeanVM.SaltedGuest.Bounds.EntryArray
public import LeanVM.Cost.Bounds.Guest.DecTop
public import LeanVM.SaltedGuest.Decoder.Program

/-!
# The prices of the salted top's closures

In the price `R` of the memory's reader and the exponent `e` of the entry table's size (at most
`2^e` pairs):

* the frame map (`decTopFramesKC.lam2.lam0`, `frameAtAK` on `locsTableK`): a lookup of at most
  `64` words at a value of index below `2^64`, at most `frameK e R` (`frameV_cost`);
* `main`'s valuations (`decTopStatesKC.lam0`, `lam1`: `mainValK`, `mainValDK`): at most
  `R + 1400` at a value of index below `2^64` (`valS_cost`, `valD_cost`);
* the witness's readers (`decTopFramesKC.lam0` … `lam4`): the leanXMSS signature
  (`xmssClosure_costK`), the leanSPHINCS signature (`sphincsClosure_costK`), the DA matrix
  (`daClosure_costK`), a child's proof (`proofClosure_costK`), the batching's hints
  (`hintsClosure_costK`).
-/

namespace LeanVM.SaltedGuest.Bounds

open LeanVM.Cost.Bounds.Guest LeanVM.SaltedGuest.Decoder LeanVM.Cost LeanVM.Cost.Bounds
open LeanVM.Cost.Library LeanVM.Parameters LeanVM.Guest.Core LeanVM.Guest.B1 LeanVM.Guest.Fast
open LeanVM.Extraction.Fast LeanVM.Guest.Located

public section

attribute [local instance] lexOrd

/-- A frame lookup's price: a call of at most `64` words in a table of at most `2^e` pairs, the
cell read, the closure's own. -/
@[expose] def frameK (e R : ℕ) : ℕ := (64 * 64 + 78 + 9 * wl e) * (e + 2) + 27 * 64 + R + 1400

variable (P : MachineProgram)

theorem frameFpAK_le (e : ℕ) (table : Array (CallKey × K)) (ht : ∀ x ∈ table, KeyOK 56 x.1)
    (hs : table.size ≤ 2 ^ e) (hP : Includes P frameFpAKC.costDeps) (j : ℕ) (hj : j < 2 ^ 64)
    (args rets : List E) (hl : args.length + rets.length ≤ 64) (R : ℕ) :
    machineCost P frameFpAKC.costIdx [encodeValue table, encodeValue j, encodeValue args,
      encodeValue rets] ≤ frameK e R := by
  have := frameFpAK_cost P hP e table ht hs j hj args rets
  have h1 : (64 * (args.length + rets.length) + 78 + 9 * wl e) * (e + 2) ≤
      (64 * 64 + 78 + 9 * wl e) * (e + 2) := Nat.mul_le_mul_right _ (by omega)
  unfold frameK; omega

/-- A cell of a packed row at an index below `2^128`: at most `60`. -/
theorem cellAtK_cost2 (hP : Includes P cellAtKC.costDeps) {row : Array ℕ}
    (hrow : ∀ k, row.getD k 0 < 2 ^ 1024) {i : ℕ} (hi : i < 2 ^ 128) :
    machineCost P cellAtKC.costIdx [encodeValue row, encodeValue i] ≤ 60 := by
  rw [cellAtKC.costEq P hP]
  have := packedCell_cost P (by includes) (hrow (i / 64)) (Nat.mod_lt i (by norm_num))
  have := limbs_le_two hi
  omega

section Reader

variable {rd : Reader} {rdV : MachineValue}
  (hrd : ∀ a : K, RunsApp P rdV [encodeValue a] (encodeValue (rd a)))
  {R : ℕ} (hR : ∀ a : K, appCost P rdV [encodeValue a] ≤ R)
include hrd

/-! ## `main`'s valuations -/

theorem valS_runs (hP : Includes P decTopStatesKC.lam0.costDeps) (v : V) :
    RunsApp P (.closure decTopStatesKC.lam0.costIdx [encodeValue locsTableK, rdV]) [encodeValue v]
      (encodeValue (mainValK locsTableK rd v)) :=
  RunsApp.of_spec (decTopStatesKC.lam0.costSpec P hP locsTableK rd rdV hrd v)

theorem valD_runs (hP : Includes P decTopStatesKC.lam1.costDeps) (v : V) :
    RunsApp P (.closure decTopStatesKC.lam1.costIdx [encodeValue locsTableK, rdV]) [encodeValue v]
      (encodeValue (mainValDK locsTableK rd v)) :=
  RunsApp.of_spec (decTopStatesKC.lam1.costSpec P hP locsTableK rd rdV hrd v)

include hR

/-- **The salted `main`'s valuation** (`decTopStatesKC.lam0`, `mainValK`): `R + 1400`. -/
theorem valS_cost (hP : Includes P decTopStatesKC.lam0.costDeps) (v : V) (hv : v.idx < 2 ^ 64) :
    appCost P (.closure decTopStatesKC.lam0.costIdx [encodeValue locsTableK, rdV])
      [encodeValue v] ≤ R + 1400 := by
  rw [appCost_fn, List.cons_append, List.cons_append, List.nil_append,
    decTopStatesKC.lam0.costEq P hP locsTableK rd rdV hrd, mainValKC.costEq P (by includes) locsTableK rd rdV hrd]
  have h1 := cellAtK_cost P (by includes) (locsTableK_lt 1) hv
  have h2 := wordWith_cost P rd rdV hrd R hR (W := 16) (by norm_num) (by norm_num) (by includes) 1
    _ (cellAtK_lt (locsTableK.getD 1 #[]) v.idx)
  unfold psAt at h2
  simp only [List.length_cons, List.length_nil]
  omega

omit hrd hR in
theorem mainRiDK_le (k : ℕ) : mainRiDK k ≤ k + 57 := by
  unfold mainRiDK; split_ifs <;> omega

omit hrd hR in
theorem mainRiK_le (k : ℕ) : mainRiK k ≤ k + 57 := by
  unfold mainRiK; have := mainRiDK_le k; split_ifs <;> omega

omit hrd hR in
/-- The deployed value numbers' map (`mainRiDKC`), below `2^64`: at most `50`. -/
theorem mainRiDK_cost (hP : Includes P mainRiDKC.costDeps) (k : ℕ) (hk : k < 2 ^ 64) :
    machineCost P mainRiDKC.costIdx [encodeValue k] ≤ 50 := by
  rw [mainRiDKC.costEq P hP]
  have l0 := limbs_of_lt hk
  have l1 := limbs_le_two (show k + 28 < 2 ^ 128 by omega)
  have l2 := limbs_le_two (show k + 50 < 2 ^ 128 by omega)
  have l3 := limbs_le_two (show k + 55 < 2 ^ 128 by omega)
  have l4 := limbs_le_two (show k + 57 < 2 ^ 128 by omega)
  simp only [l0, max_def]
  split_ifs <;> omega

omit hrd hR in
/-- The value numbers' map (`mainRiKC`), below `2^64`: at most `80`. -/
theorem mainRiK_cost (hP : Includes P mainRiKC.costDeps) (k : ℕ) (hk : k < 2 ^ 64) :
    machineCost P mainRiKC.costIdx [encodeValue k] ≤ 80 := by
  rw [mainRiKC.costEq P hP]
  have := mainRiDK_cost P (by includes) k hk
  have l0 := limbs_of_lt hk
  simp only [l0]
  split_ifs <;> omega

/-- **The salted `main`'s valuation at the deployed numbers** (`decTopStatesKC.lam1`,
`mainValDK`): `R + 1400`. -/
theorem valD_cost (hP : Includes P decTopStatesKC.lam1.costDeps) (v : V) (hv : v.idx < 2 ^ 64) :
    appCost P (.closure decTopStatesKC.lam1.costIdx [encodeValue locsTableK, rdV])
      [encodeValue v] ≤ R + 1400 := by
  rw [appCost_fn, List.cons_append, List.cons_append, List.nil_append,
    decTopStatesKC.lam1.costEq P hP locsTableK rd rdV hrd, mainValDKC.costEq P (by includes) locsTableK rd rdV hrd]
  have hri := mainRiK_le v.idx
  have hrc := mainRiK_cost P (by includes) v.idx hv
  have h1 := cellAtK_cost2 P (by includes) (locsTableK_lt 1) (i := mainRiK v.idx) (by omega)
  have h2 := wordWith_cost P rd rdV hrd R hR (W := 16) (by norm_num) (by norm_num) (by includes) 1
    _ (cellAtK_lt (locsTableK.getD 1 #[]) (mainRiK v.idx))
  unfold psAt at h2
  simp only [List.length_cons, List.length_nil]
  omega

/-! ## The frame map -/

omit hR in
theorem frameV_runs (table : Array (CallKey × K)) (hP : Includes P decTopFramesKC.lam2.lam0.costDeps)
    (k : ℕ) (a r : List E) (v : V) :
    RunsApp P (.closure decTopFramesKC.lam2.lam0.costIdx [encodeValue locsTableK, rdV,
      encodeValue table]) [encodeValue k, encodeValue a, encodeValue r, encodeValue v]
      (encodeValue (frameAtAK table locsTableK rd k a r v)) :=
  RunsApp.of_spec (decTopFramesKC.lam2.lam0.costSpec P hP locsTableK rd rdV hrd table k a r v)

/-- **The frame map** (`decTopFramesKC.lam2.lam0`): a call of at most `64` words, at a value of
index below `2^64`: at most `frameK e R`. -/
theorem frameV_cost (e : ℕ) (table : Array (CallKey × K)) (ht : ∀ x ∈ table, KeyOK 56 x.1)
    (hs : table.size ≤ 2 ^ e) (hP : Includes P decTopFramesKC.lam2.lam0.costDeps) (k : ℕ)
    (a r : List E) (v : V) (hk : k < 2 ^ 64) (hv : v.idx < 2 ^ 64)
    (hl : a.length + r.length ≤ 64) :
    appCost P (.closure decTopFramesKC.lam2.lam0.costIdx [encodeValue locsTableK, rdV,
      encodeValue table]) [encodeValue k, encodeValue a, encodeValue r, encodeValue v] ≤
        frameK e R := by
  rw [appCost_fn, List.cons_append, List.cons_append, List.cons_append, List.nil_append,
    decTopFramesKC.lam2.lam0.costEq P hP locsTableK rd rdV hrd]
  have := frameAtAK_cost P rd rdV hrd R hR (by includes) e table ht hs k hk a r v hv
  have h1 : (64 * (a.length + r.length) + 78 + 9 * wl e) * (e + 2) ≤
      (64 * 64 + 78 + 9 * wl e) * (e + 2) := Nat.mul_le_mul_right _ (by omega)
  simp only [List.length_cons, List.length_nil]
  unfold frameK; omega

/-! ## A frame's words, looked up once -/

/-- A frame's word at a pointer looked up once (`frameValAtK`), as a closure `lam` of the reader:
`R + 1300`. -/
theorem frameValAtK_le (hP : Includes P frameValAtKC.costDeps) (o : Option K) (j : ℕ) (v : V)
    (hv : v.idx < 2 ^ 64) :
    machineCost P frameValAtKC.costIdx [encodeValue locsTableK, rdV, encodeValue o,
      encodeValue j, encodeValue v] ≤ R + 1300 := by
  have := frameValAtK_cost P rd rdV hrd R hR hP o j v hv
  omega

end Reader

end

end LeanVM.SaltedGuest.Bounds
