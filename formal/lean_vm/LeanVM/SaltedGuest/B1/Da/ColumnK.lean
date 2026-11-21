/-
  LeanVM.SaltedGuest.B1.Da.ColumnK

  The salted `da_verify_column` and its blob loop `__loop26`: what a run of a column establishes
  under the key.
-/

module

public import LeanVM.SaltedGuest.B1.Da.Cell
public import LeanVM.SaltedGuest.B1.Da.LevelsK
public import LeanVM.Guest.B1.Da.Column

/-!
# The salted `da_verify_column`

`da_verify_column(xb, n_blob_g, rowbase, zs, top_leaves, cell_factors, offsets, key)` (`core30`) is
the deployed one (`Da.colOk`) with the key's argument `.n 7` new (the deployed values from `7` on
moved by one) and its blob loop `__loop26` (`core393`, the deployed `__loop25` with the key's
argument `.n 3` new) checking each blob's cell with the salted `da_verify_cell` under the key.
`da_expand__L7_L8` is an unchanged function: its deployed meaning holds of its salted calls
(`toD_le`).

`col_stepWK`: a column's run, under a seed whose key is at `key`: the cell checks' symbols
(`colSymsS`), each cell's keyed digest the blob tree's leaf and its inner product with the dual
codeword stepping the blob's running sum.
-/

namespace LeanVM.SaltedGuest.B1.Da

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Guest.Value.Keccak LeanVM.Guest.B1 LeanVM.Guest.B1.Digest
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Node LeanVM.Guest.B1.Da LeanVM.Guest.B1.Main LeanVM.SaltedGuest.B1 Recursion.Salted

@[expose] public section

/-! ## The checks -/

/-- `__loop26`: blob `x`'s cell of the column, under the key. -/
def l26Ok (fn : Fn) : Bool :=
  let A := atomsIn (loopPre fn)
  loopShapeF fn "__loop26" && decide (fn.params.length = 7) &&
  hasCall (loopPre fn) "da_verify_cell" [.n 2, .n 3] [.n 7, .n 8, .n 9] &&
  isMul A (.n 10) (.n 4) (.n 0) && A.any (isLoadAt (.n 11) (.n 10) 0) &&
  isMul A (.n 12) (.n 11) (.n 5) && A.any (isLoadAt (.n 13) (.n 12) 512) &&
  A.any (isAddAt (.n 14) (.n 13) (.n 9)) && A.any (isLoadAt (.n 14) (.n 12) 513) &&
  isMul A (.n 15) (.n 11) (.n 6) && A.any (isLoadAt (.n 7) (.n 15) 0) &&
  A.any (isLoadAt (.n 8) (.n 15) 1)

/-- The salted `da_verify_column`'s block (its body but the final `ret`). -/
noncomputable def colPS : List Stmt := (Fn.body LeanVM.SaltedGuest.Data.core30).dropLast

/-- **The salted `da_verify_column`'s block, checked.** -/
noncomputable def colOkS : Bool :=
  let P := colPS
  let A := atomsIn P
  decide (LeanVM.SaltedGuest.Data.core30.params = (List.range 8).map V.n) &&
  stmtsEqb (Fn.body LeanVM.SaltedGuest.Data.core30) (P ++ [.ret []]) && P.all Stmt.flat &&
  isMul A (.n 8) (.n 4) (.n 0) && A.any (isLoadAt (.n 9) (.n 8) 0) &&
  monoIs A (.n 13) (.n 6) (.n 0) 8 &&
  hasCall P "da_expand__L7_L8" [.n 9, .n 5, .n 3, .n 13] [.n 14] &&
  isMul A (.n 15) (.n 0) (.n 0) &&
  guardOk P (.n 17) "__loop26" (.n 18) (.n 1) [.n 14, .n 7, .n 2, .n 0, .n 15]

set_option maxRecDepth 100000 in
theorem colS_ok : colOkS = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem l26_ok : l26Ok (SaltedGuest.coreProgram.getD 393 default) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem l26_name : nameS 393 = "__loop26" := by decide +kernel

set_option maxRecDepth 100000 in
kernel_rfl col_idxS : SaltedGuest.coreProgram[30]? = some LeanVM.SaltedGuest.Data.core30

theorem find_da_verify_columnS :
    SaltedGuest.coreProgram.find? "da_verify_column" = some LeanVM.SaltedGuest.Data.core30 :=
  find_of_getElem? col_idxS

theorem find_l26 : SaltedGuest.coreProgram.find? "__loop26" =
    some (SaltedGuest.coreProgram.getD 393 default) :=
  find_getD (by rw [SaltedGuest.coreProgram_length]; omega) l26_name

/-! ## A blob's step and the frames -/

variable {rd : Reader} {C : CallRel} {Vm : End.FrameMap}

/-- **Blob `x`'s cell of the column, at the loop's valuation `σr`**: a `da_verify_cell` call on the
weights at `lv` and the key, its sum `σr (.n 9)` added to the running sum of the region at
`rowbase[x]` (through `xb`), its digest `σr (.n 7)`, `σr (.n 8)` the region's leaf (through
`xb2`). -/
def CellStepWK (C : CallRel) (rd : Reader) (σr : Val) (lv key rowbase xb xb2 x : E) : Prop :=
  C "da_verify_cell" [lv, key] [σr (.n 7), σr (.n 8), σr (.n 9)] ∧
    ∃ base a : E, LoadHolds rd (rowbase * x) 0 base ∧ LoadHolds rd (base * xb) 512 a ∧
      LoadHolds rd (base * xb) 513 (a + σr (.n 9)) ∧ LoadHolds rd (base * xb2) 0 (σr (.n 7)) ∧
      LoadHolds rd (base * xb2) 1 (σr (.n 8))

/-- The valuation of blob `i`'s iteration of `__loop26` in the column called with `cargs`
(`[g^h, n_blob_g, rowbase, zs, top_leaves, cell_factors, offsets, key]`), at the frame map `Vm`. -/
def colRowVS (Vm : End.FrameMap) (cargs : List E) (i : ℕ) : Val :=
  Vm "__loop26" [gen ^ i, cargs.getD 1 0, Vm "da_verify_column" cargs [] (.n 14), cargs.getD 7 0,
    cargs.getD 2 0, cargs.getD 0 0, Vm "da_verify_column" cargs [] (.n 15)] []

/-- The symbols of blob `i`'s cell in the column called with `cargs`: its cell check's. -/
def colSymsS (Vm : End.FrameMap) (cargs : List E) (i : ℕ) : List K :=
  cellSymsOfS (Vm "da_verify_cell" [Vm "da_verify_column" cargs [] (.n 14), cargs.getD 7 0]
    [colRowVS Vm cargs i (.n 7), colRowVS Vm cargs i (.n 8), colRowVS Vm cargs i (.n 9)])

theorem l26_stepWK (hVm : End.UnfoldsV rd C Vm) {x : E} {ps : List E}
    (h : C "__loop26" (x :: ps) []) :
    (∀ N lv key rb xb xb2, ps = [N, lv, key, rb, xb, xb2] →
      CellStepWK C rd (Vm "__loop26" (x :: ps) []) lv key rb xb xb2 x) ∧
      (x * gen + ps.headD 0 ≠ 0 → C "__loop26" (x * gen :: ps) []) := by
  have hok := l26_ok
  simp only [l26Ok, Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hshape, hlen⟩, hcall⟩, hm10⟩, hl11⟩, hm12⟩, hl13⟩, ha14⟩, hl14⟩, hm15⟩, hl7⟩,
    hl8⟩ := hok
  obtain ⟨hx, hps, hall, hnext⟩ := loop_stepVS hVm find_l26 hshape h
  set σ := Vm "__loop26" (x :: ps) [] with hσ
  refine ⟨fun N lv key rb xb xb2 hN ↦ ?_, hnext⟩
  have hat := atoms_of_flat hall
  have hpar : (SaltedGuest.coreProgram.getD 393 default).params =
      [V.n 0, V.n 1, V.n 2, V.n 3, V.n 4, V.n 5, V.n 6] := by
    have hs := hshape
    simp only [loopShapeF, Bool.and_eq_true, decide_eq_true_eq] at hs
    rw [hs.1.2, hlen]; rfl
  rw [hpar, hN] at hps
  simp only [List.tail_cons, List.map_cons, List.map_nil, List.cons.injEq, and_true] at hps
  obtain ⟨-, h2, h3, h4, h5, h6⟩ := hps
  have c := call_of_flat hall hcall
  simp only [List.map_cons, List.map_nil] at c
  rw [h2, h3] at c
  have l11 := load_sound hl11 hat
  rw [isMul_sound hm10 hat, h4, hx] at l11
  have p12 : σ (.n 12) = σ (.n 11) * xb := by rw [isMul_sound hm12 hat, h5]
  have l13 := load_sound hl13 hat
  have l14 := load_sound hl14 hat
  rw [p12] at l13 l14
  rw [add_sound ha14 hat] at l14
  have p15 : σ (.n 15) = σ (.n 11) * xb2 := by rw [isMul_sound hm15 hat, h6]
  have l7 := load_sound hl7 hat
  have l8 := load_sound hl8 hat
  rw [p15] at l7 l8
  exact ⟨c, _, _, l11, l13, l14, l7, l8⟩

/-! ## A column -/

/-- **A salted column's run** at `g^h`, with `da_vector`'s results for `z`, under a call relation
that unfolds at `Vm` and lies below the salted core IR's, for a seed `s` whose key is at `key`: for
every blob `i < r`, the symbols of its cell check's frame (`colSymsS`), whose keyed digest is leaf
`h` of the region at `rowbase[i]` and whose inner product with the dual codeword's entries
`256 h + e` steps the region's running sum from word `512 + h` to `513 + h`. -/
theorem col_stepWK (hVm : End.UnfoldsV rd C Vm) (hle : CallRel.Le C (SaltedGuest.coreProgram.Rel rd))
    {z zs tl cf off rb key : E} {h r : ℕ} {s : Digest} (hks : KeyIs rd key s)
    (hh : h < 128) (hr : r < ordG) (hvec : MeaningDaVector rd [z] [zs, tl, cf, off])
    (hrel : C "da_verify_column" [gen ^ h, gen ^ r, rb, zs, tl, cf, off, key] []) :
    ∀ i < r, (colSymsS Vm [gen ^ h, gen ^ r, rb, zs, tl, cf, off, key] i).length = 256 ∧
      ∃ base a : E, LoadHolds rd (rb * gen ^ i) 0 base ∧
      LoadHolds rd base (2 * h) (digestHalves (keyedHash s
        ((colSymsS Vm [gen ^ h, gen ^ r, rb, zs, tl, cf, off, key] i).flatMap K.toBytes))).1 ∧
      LoadHolds rd base (2 * h + 1) (digestHalves (keyedHash s
        ((colSymsS Vm [gen ^ h, gen ^ r, rb, zs, tl, cf, off, key] i).flatMap K.toBytes))).2 ∧
      LoadHolds rd base (h + 512) a ∧
      LoadHolds rd base (h + 513) (a + ∑ e ∈ Finset.range 256, dualAt z (256 * h + e) *
        ofK ((colSymsS Vm [gen ^ h, gen ^ r, rb, zs, tl, cf, off, key] i).getD e 0)) := by
  obtain ⟨hpar, hb⟩ := body_ofVS hVm find_da_verify_columnS hrel
  set σ := Vm "da_verify_column" [gen ^ h, gen ^ r, rb, zs, tl, cf, off, key] [] with hσ
  have hcol := colS_ok
  unfold colOkS at hcol
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hcol
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hparams, hbody⟩, hflat⟩, hm8⟩, hl9⟩, hm13⟩, hce⟩, hm15⟩, hg⟩ := hcol
  rw [hparams] at hpar
  simp only [List.range_succ, List.range_zero, List.nil_append, List.map_cons, List.map_nil,
    List.cons_append, List.cons.injEq, and_true] at hpar
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := hpar
  rw [stmtsEqb_sound hbody, holdsList_append] at hb
  obtain ⟨hall, -⟩ := holdsList_flat colPS hflat _ _ hb
  have hat := atoms_of_flat hall
  obtain ⟨hzs, htl, hcf, hoff⟩ := hvec
  -- the top leaf
  have l9 := load_sound hl9 hat
  rw [isMul_sound hm8 hat, h4, h0, loadHolds_mul_gen_pow, add_zero] at l9
  have e9 := runAt_load htl hh l9
  -- the weights
  have ce := toD_le hle (by decide +kernel) (by decide +kernel) (call_of_flat hall hce)
  simp only [List.map_cons, List.map_nil] at ce
  have hE := (da_expand_holds).2 rd _ _ ce
  simp only [MeaningDaExpand] at hE
  obtain ⟨F, Z, S, hF, hZ, hS, hrun⟩ := hE
  have p13 : σ (.n 13) = off * (gen ^ h) ^ 8 := by rw [monoIs_sound hm13 hat, h6, h0]
  have hlv : ∀ e < 256, ∀ w, rd ((σ (.n 14)).limb 0 * addressOfIndex e) = some w →
      w = dualAt z (256 * h + e) := by
    intro e he w hw
    rw [hrun.2 e (by norm_num; omega) w hw, e9, ← cellLeaf_eq z he]
    refine expandLeaf_congr (by norm_num; omega) (fun n n1 n2 ↦ ?_) (fun d hd ↦ ?_) (fun d hd ↦ ?_)
    · rw [h5] at hF
      exact loadHolds_unique (hF n n1 n2) (hcf n n1 (by norm_num at n2 ⊢; omega))
    · rw [h3] at hZ
      exact loadHolds_unique (hZ d hd) (hzs _ (by omega))
    · have := hS d hd
      rw [p13, ← pow_mul, loadHolds_mul_gen_pow] at this
      exact loadHolds_unique this (by
        rw [show h * 8 + (7 - d) = 8 * h + (7 - d) by ring]; exact hoff h hh (7 - d) (by omega))
  -- the blobs
  have hgs := guard_soundC hg hall
  simp only [List.map_cons, List.map_nil] at hgs
  rw [h1, h7, h2, h0] at hgs
  have L := loop_soundC (C := C) (f := "__loop26")
    (ps := [gen ^ r, σ (.n 14), key, rb, gen ^ h, σ (.n 15)])
    (B := fun x ↦ CellStepWK C rd (Vm "__loop26" (x :: [gen ^ r, σ (.n 14), key, rb, gen ^ h,
      σ (.n 15)]) []) (σ (.n 14)) key rb (gen ^ h) (σ (.n 15)) x) hr rfl
    (fun x hx ↦ by
      obtain ⟨k1, k2⟩ := l26_stepWK hVm hx
      exact ⟨k1 _ _ _ _ _ _ rfl, k2⟩) hgs
  have p15 : σ (.n 15) = (gen ^ h) ^ 2 := by rw [isMul_sound hm15 hat, h0, sq]
  intro i hi
  obtain ⟨hc, base, a, hbase, ha, has, hd0, hd1⟩ := L i hi
  have hrv : colRowVS Vm [gen ^ h, gen ^ r, rb, zs, tl, cf, off, key] i =
      Vm "__loop26" [gen ^ i, gen ^ r, σ (.n 14), key, rb, gen ^ h, σ (.n 15)] [] := rfl
  have hsy : colSymsS Vm [gen ^ h, gen ^ r, rb, zs, tl, cf, off, key] i =
      cellSymsOfS (Vm "da_verify_cell" [σ (.n 14), key]
        [colRowVS Vm [gen ^ h, gen ^ r, rb, zs, tl, cf, off, key] i (.n 7),
          colRowVS Vm [gen ^ h, gen ^ r, rb, zs, tl, cf, off, key] i (.n 8),
          colRowVS Vm [gen ^ h, gen ^ r, rb, zs, tl, cf, off, key] i (.n 9)]) := rfl
  rw [hrv] at hsy
  rw [hsy]
  obtain ⟨hpc, hbc⟩ := body_ofVS hVm find_da_verify_cellS hc
  obtain ⟨lv, key', hlv0, hsl, hrd, hwl, hrets⟩ := da_verify_cell_valK hpc hbc
  simp only [List.cons.injEq, and_true] at hlv0
  obtain ⟨rfl, rfl⟩ := hlv0
  have hrets' := hrets s hks
  simp only [digestCells, List.cons_append, List.nil_append, List.cons.injEq, and_true] at hrets'
  obtain ⟨e0, e1, es⟩ := hrets'
  have q : ∀ k v, LoadHolds rd (base * σ (.n 15)) k v → LoadHolds rd base (2 * h + k) v :=
    fun k v hk => by rw [p15, shift2] at hk; exact hk
  rw [loadHolds_mul_gen_pow] at ha has
  refine ⟨hsl, base, a, hbase, ?_, ?_, ha, ?_⟩
  · rw [← e0]; simpa using q 0 _ hd0
  · rw [← e1]; exact q 1 _ hd1
  · rw [es] at has
    convert has using 2
    rw [← list_sum_range]
    unfold LeanDa.cellSymbols
    have hwl' : (memRun rd (σ (.n 14)) 256).length = 256 := hwl
    refine congrArg _ (List.map_congr_left fun e he ↦ ?_)
    have he' := List.mem_range.mp he
    rw [List.getD_eq_getElem (memRun rd (σ (.n 14)) 256) 0 (show e < _ by omega),
      hlv e he' _ (hrd e (by omega)).2]

end
end LeanVM.SaltedGuest.B1.Da
