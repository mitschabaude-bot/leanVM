/-
  LeanVM.SaltedGuest.B1.Da.VerifyK

  B1 for the salted `da_verify`: a matrix opening its claim under the seed.
-/

module

public import LeanVM.SaltedGuest.B1.Da.ColumnK
public import LeanVM.SaltedGuest.B1.Da.LevelsKAll
public import LeanVM.SaltedGuest.B1.Da.VerifyMathK
public import LeanVM.Guest.B1.Da.Verify

/-!
# The salted `da_verify`

`da_verify(g_squares, key)` (`core27`) is the deployed one (`Da.dvOk`) with the key's argument `.n 1`
new (the deployed values moved by one) and four changes: the columns' loop `__loop23` and each
column pass the key, the blobs' loop `__loop24` roots each blob's tree with the salted `da_levels`
under the key, `da_padding_root(key)` computes the padding root, which the padding loop
`__loop25` writes from its arguments, and the dispatched `da_levels` over the blob roots takes the
key. The regions' loop `__loop22` is the deployed `__loop21` (an unchanged function: its deployed
step `Da.l17_step` holds of its salted calls through `Same.rel_same`), and so are `da_row_shape`
and `da_vector`.

`dvWitK σ Vm`: the deployed witness's form (`Da.dvWit`) at the salted values, the symbols of the
salted cell checks' frames (`colSymsS`); it mentions no hash. `da_verify_sound_wK`: under a call
relation that unfolds at `Vm` and lies below the salted core IR's, with the exponent table, for a
seed whose key is at `key`, the returned words are the cells of a root and the rate cells of a
challenge `z` that `dvWitK σ Vm` opens under the seed (`OpensUnder`).
-/

namespace LeanVM.SaltedGuest.B1.Da

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Guest.Value.Keccak LeanVM.Guest.B1 LeanVM.Guest.B1.Digest
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Node LeanVM.Guest.B1.Da LeanVM.Guest.B1.Main LeanVM.SaltedGuest.B1 Recursion.Salted

@[expose] public section

/-! ## The loops -/

/-- `guardK_sound` under any call relation. -/
theorem guardK_soundC {C : CallRel} {rd : Reader} {σ : Val} {P : List Stmt} {gc : V} {f : String}
    {one N : V} {rest : List V} (h : guardOk P gc f one N rest = true) {kret : List E → Prop}
    (hall : ∀ s ∈ P, Stmt.Holds C rd σ s True kret) :
    1 + σ N ≠ 0 → C f (1 :: σ N :: rest.map σ) [] := by
  simp only [guardOk, Bool.and_eq_true] at h
  obtain ⟨⟨hc, ha⟩, h1⟩ := h
  have hat := atoms_of_flat hall
  have hcall := callIf_of_flat hall hc
  split at ha
  · rename_i p q hpq
    simp only [Bool.and_eq_true, decide_eq_true_eq] at ha
    obtain ⟨hp1, rfl⟩ := ha
    intro hne
    have hgc : σ gc = 1 + σ q := by rw [addOf_sound hpq hat, const_sound hp1 hat, word_one]
    have := hcall.2 (by rw [hgc]; exact hne)
    rwa [List.map_cons, List.map_cons, const_sound h1 hat, word_one] at this
  · exact absurd ha (by simp)

/-- `__loop24`: the region at `rowbase[x]` has the sum `0` at word `640`; its tree's root under the
key, at `roots·x²`. -/
def l24Ok (fn : Fn) : Bool :=
  let A := atomsIn (loopPre fn)
  loopShapeF fn "__loop24" && decide (fn.params.length = 5) &&
  isMul A (.n 5) (.n 2) (.n 0) && A.any (isLoadAt (.n 6) (.n 5) 0) &&
  A.any (isLoadAt (.n 7) (.n 6) 640) && A.any (isConstAt (.n 8) 0 0) &&
  A.any (isAssertEqAt (.n 7) (.n 8)) &&
  hasCall (loopPre fn) "da_levels__L128_L7" [.n 6, .n 3] [.n 9, .n 10] &&
  isMul A (.n 11) (.n 0) (.n 0) && isMul A (.n 12) (.n 4) (.n 11) &&
  A.any (isLoadAt (.n 9) (.n 12) 0) && A.any (isLoadAt (.n 10) (.n 12) 1)

/-- `__loop25`: the padding root's cells, its arguments, at `roots·n_blob²·x²`. -/
def l25Ok (fn : Fn) : Bool :=
  let A := atomsIn (loopPre fn)
  loopShapeF fn "__loop25" && decide (fn.params.length = 6) &&
  isMul A (.n 6) (.n 3) (.n 3) && isMul A (.n 7) (.n 2) (.n 6) && isMul A (.n 8) (.n 0) (.n 0) &&
  isMul A (.n 9) (.n 7) (.n 8) && A.any (isLoadAt (.n 4) (.n 9) 0) &&
  A.any (isLoadAt (.n 5) (.n 9) 1)

/-- The body of the salted column loop `__loop23`: the column at `x` with the key, then the next. -/
def l23Body : List Stmt :=
  [.call "da_verify_column" ((List.range 8).map V.n) [],
    .atom (.const (.n 8) (word 2 0 0)), .atom (.mul (.n 9) (.n 0) (.n 8)),
    .atom (.const (.n 10) (word 325 0 0)), .atom (.add (.n 11) (.n 9) (.n 10)),
    .atom (.const (.n 12) (word 2 0 0)), .atom (.mul (.n 13) (.n 0) (.n 12)),
    .callIf (.n 11) "__loop23" (.n 13 :: (List.range 7).map fun k => V.n (k + 1)), .ret []]

/-- `__loop23`, checked. -/
def l23Ok (fn : Fn) : Bool :=
  decide (fn.params = (List.range 8).map V.n) && stmtsEqb fn.body l23Body

set_option maxRecDepth 100000 in
theorem l23_ok : l23Ok (SaltedGuest.coreProgram.getD 378 default) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem l24_ok : l24Ok (SaltedGuest.coreProgram.getD 379 default) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem l25_ok : l25Ok (SaltedGuest.coreProgram.getD 380 default) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem dv_names : nameS 378 = "__loop23" ∧ nameS 379 = "__loop24" ∧ nameS 380 = "__loop25" := by
  decide +kernel

theorem find_l23 : SaltedGuest.coreProgram.find? "__loop23" =
    some (SaltedGuest.coreProgram.getD 378 default) :=
  find_getD (by rw [SaltedGuest.coreProgram_length]; omega) dv_names.1

theorem find_l24 : SaltedGuest.coreProgram.find? "__loop24" =
    some (SaltedGuest.coreProgram.getD 379 default) :=
  find_getD (by rw [SaltedGuest.coreProgram_length]; omega) dv_names.2.1

theorem find_l25 : SaltedGuest.coreProgram.find? "__loop25" =
    some (SaltedGuest.coreProgram.getD 380 default) :=
  find_getD (by rw [SaltedGuest.coreProgram_length]; omega) dv_names.2.2

variable {rd : Reader}

theorem params_of_shape {fn : Fn} {f : String} (hshape : loopShapeF fn f = true) {n : ℕ}
    (hlen : fn.params.length = n) : fn.params = (List.range n).map V.n := by
  have hs := hshape
  simp only [loopShapeF, Bool.and_eq_true, decide_eq_true_eq] at hs
  rw [hs.1.2, hlen]

theorem l24_step {x : E} {ps : List E} (h : SaltedGuest.coreProgram.Rel rd "__loop24" (x :: ps) []) :
    (∀ N rb key roots, ps = [N, rb, key, roots] → ∃ base c0 c1, LoadHolds rd (rb * x) 0 base ∧
      LoadHolds rd base 640 0 ∧
      SaltedGuest.coreProgram.Rel rd "da_levels__L128_L7" [base, key] [c0, c1] ∧
      LoadHolds rd (roots * x ^ 2) 0 c0 ∧ LoadHolds rd (roots * x ^ 2) 1 c1) ∧
      (x * gen + ps.headD 0 ≠ 0 → SaltedGuest.coreProgram.Rel rd "__loop24" (x * gen :: ps) []) := by
  have hok := l24_ok
  simp only [Bool.and_eq_true, decide_eq_true_eq, l24Ok] at hok
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hshape, hlen⟩, hm5⟩, hl6⟩, hl7⟩, hc8⟩, hae⟩, hcall⟩, hm11⟩, hm12⟩, hl9⟩,
    hl10⟩ := hok
  obtain ⟨σ, hp, hb⟩ := (rel_iff_sem find_l24 _ _).mp h
  obtain ⟨hx, hps, hall, hnext⟩ := loop_of_body hshape hp hb
  refine ⟨fun N rb key roots hN ↦ ?_, hnext⟩
  have hat := atoms_of_flat hall
  rw [params_of_shape hshape hlen, hN] at hps
  simp only [List.range_succ, List.range_zero, List.nil_append, List.map_cons, List.map_nil,
    List.cons_append, List.tail_cons, List.cons.injEq, and_true] at hps
  obtain ⟨-, h2, h3, h4⟩ := hps
  have l6 := load_sound hl6 hat
  rw [isMul_sound hm5 hat, h2, hx] at l6
  have l7 := load_sound hl7 hat
  rw [assertEq_sound hae hat, const_sound hc8 hat, word_zero] at l7
  have c := call_of_flat hall hcall
  simp only [List.map_cons, List.map_nil] at c
  rw [h3] at c
  have p12 : σ (.n 12) = roots * x ^ 2 := by
    rw [isMul_sound hm12 hat, isMul_sound hm11 hat, h4, hx, sq]
  have l9 := load_sound hl9 hat
  have l10 := load_sound hl10 hat
  rw [p12] at l9 l10
  exact ⟨_, _, _, l6, l7, c, l9, l10⟩

theorem l25_step {x : E} {ps : List E} (h : SaltedGuest.coreProgram.Rel rd "__loop25" (x :: ps) []) :
    (∀ N roots nb p0 p1, ps = [N, roots, nb, p0, p1] →
      LoadHolds rd (roots * nb ^ 2 * x ^ 2) 0 p0 ∧ LoadHolds rd (roots * nb ^ 2 * x ^ 2) 1 p1) ∧
      (x * gen + ps.headD 0 ≠ 0 → SaltedGuest.coreProgram.Rel rd "__loop25" (x * gen :: ps) []) := by
  have hok := l25_ok
  simp only [Bool.and_eq_true, decide_eq_true_eq, l25Ok] at hok
  obtain ⟨⟨⟨⟨⟨⟨⟨hshape, hlen⟩, hm6⟩, hm7⟩, hm8⟩, hm9⟩, hl4⟩, hl5⟩ := hok
  obtain ⟨σ, hp, hb⟩ := (rel_iff_sem find_l25 _ _).mp h
  obtain ⟨hx, hps, hall, hnext⟩ := loop_of_body hshape hp hb
  refine ⟨fun N roots nb p0 p1 hN ↦ ?_, hnext⟩
  have hat := atoms_of_flat hall
  rw [params_of_shape hshape hlen, hN] at hps
  simp only [List.range_succ, List.range_zero, List.nil_append, List.map_cons, List.map_nil,
    List.cons_append, List.tail_cons, List.cons.injEq, and_true] at hps
  obtain ⟨-, h2, h3, h4, h5⟩ := hps
  have p9 : σ (.n 9) = roots * nb ^ 2 * x ^ 2 := by
    rw [isMul_sound hm9 hat, isMul_sound hm7 hat, isMul_sound hm6 hat, isMul_sound hm8 hat, h2, h3,
      hx, sq, sq]
  have l4 := load_sound hl4 hat
  have l5 := load_sound hl5 hat
  rw [p9, h4] at l4
  rw [p9, h5] at l5
  exact ⟨l4, l5⟩

variable {C : CallRel} {Vm : End.FrameMap}

theorem l23_stepW (hVm : End.UnfoldsV rd C Vm) {x : E} {ps : List E} (h : C "__loop23" (x :: ps) []) :
    C "da_verify_column" (x :: ps) [] ∧
      (x * gen + word 325 0 0 ≠ 0 → C "__loop23" (x * gen :: ps) []) := by
  have hok := l23_ok
  unfold l23Ok at hok
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨hparams, hbody⟩ := hok
  obtain ⟨hpar, hb⟩ := body_ofVS hVm find_l23 h
  set σ := Vm "__loop23" (x :: ps) [] with hσ
  rw [stmtsEqb_sound hbody] at hb
  have r8 : (List.range 8).map V.n = [V.n 0, V.n 1, V.n 2, V.n 3, V.n 4, V.n 5, V.n 6, V.n 7] := rfl
  have r7 : (List.range 7).map (fun k => V.n (k + 1)) =
      [V.n 1, V.n 2, V.n 3, V.n 4, V.n 5, V.n 6, V.n 7] := rfl
  rw [hparams, r8] at hpar
  simp only [List.map_cons, List.map_nil] at hpar
  obtain ⟨hx, hps⟩ := List.cons.inj hpar
  simp only [l23Body, Stmt.HoldsList, Stmt.Holds, Atom.Holds, r8, r7, List.map_cons,
    List.map_nil] at hb
  obtain ⟨hc, h8, h9, h10, h11, h12, h13, -, hcall, -⟩ := hb
  refine ⟨?_, fun hne => ?_⟩
  · rw [← hx, ← hps]; exact hc
  · have e11 : σ (.n 11) = x * gen + word 325 0 0 := by rw [h11, h9, h8, h10, word_gen, hx]
    have e13 : σ (.n 13) = x * gen := by rw [h13, h12, word_gen, hx]
    have := hcall (by rw [e11]; exact hne)
    rw [e13] at this
    rw [← hps]
    exact this

/-! ## The levels over digests -/

/-- **A dispatched salted `da_levels` run over digests' cells returns the keyed root's cells.** -/
theorem levels_root_ofK {tree key c0 c1 : E} {k L : ℕ} {s : Digest} (hks : KeyIs rd key s)
    (hk : k < 11) (hL : L ≤ 10) (hkL : ofK (Parameters.addressOfIndex k) = gen ^ L)
    (hrel : SaltedGuest.coreProgram.Rel rd (daLevelsName k) [tree, key] [c0, c1]) {g : ℕ → Digest}
    (hf : ∀ i < 2 ^ L, LoadHolds rd tree (2 * i) (digestHalves (g i)).1 ∧
      LoadHolds rd tree (2 * i + 1) (digestHalves (g i)).2) :
    (c0, c1) = digestHalves (mRootK s L g) := by
  have hkl : k = L := by
    rw [← gen_pow_eq_ofK] at hkL
    exact gen_pow_inj (by omega) (by omega) hkL
  subst hkl
  obtain ⟨leaves, hl, hout⟩ := da_levels_soundK k (by omega) rd _ _ hrel
  obtain ⟨hr, -, hrets⟩ := hout s hks
  have := leaves_of_reads (f := fun i => digestHalves (g i)) hl hr hf
  simp only [List.cons.injEq, and_true] at hrets
  rw [hrets.1, hrets.2, this, cellRootK_mRootK]

/-! ## The witness -/

/-- Column `h`'s call's words. -/
def dvColArgsS (σ : Val) (h : ℕ) : List E :=
  [gen ^ h, σ (.n 2), σ (.n 33), σ (.n 17), σ (.n 18), σ (.n 19), σ (.n 20), σ (.n 1)]

/-- Cell `(i, h)`'s symbols: its cell check's. -/
def dvSymsS (σ : Val) (Vm : End.FrameMap) (i h : ℕ) : List K := colSymsS Vm (dvColArgsS σ h) i

/-- The number of rows: the shape's count, at most `1024`. -/
noncomputable def dvRowsS (σ : Val) : ℕ := min (gLog (σ (.n 2))) 1024

/-- The symbols, padded outside the matrix. -/
noncomputable def dvSymsPS (σ : Val) (Vm : End.FrameMap) (i h : ℕ) : List K :=
  if i < dvRowsS σ ∧ h < 128 then dvSymsS σ Vm i h else List.replicate 256 0

/-- **The salted `da_verify`'s witness**: the rows of the cells' symbols, as many as the shape's
count. -/
noncomputable def dvWitK (σ : Val) (Vm : End.FrameMap) : LeanVM.Da.MatrixWitness :=
  ⟨daRows (dvRowsS σ) (dvSymsPS σ Vm)⟩

/-! ## The body -/

/-- The salted `da_verify`'s block (its body but the final `ret`). -/
noncomputable def dvPS : List Stmt := (Fn.body LeanVM.SaltedGuest.Data.core27).dropLast

/-- **The salted `da_verify`'s block, checked.** -/
noncomputable def dvOkS : Bool :=
  let P := dvPS
  let A := atomsIn P
  decide (LeanVM.SaltedGuest.Data.core27.params = [.n 0, .n 1]) &&
  stmtsEqb (Fn.body LeanVM.SaltedGuest.Data.core27) (P ++ [.ret [.n 51, .n 52, .n 53, .n 54]]) &&
  P.all Stmt.flat &&
  hasCall P "da_row_shape" [.n 2, .n 3, .n 0] [.n 4, .n 5] &&
  hasAtom A (.const (.n 7) (word 0 0 0)) && hasAtom A (.assertInK (.n 10) (.n 7)) &&
  hasAtom A (.const (.n 11) (word 0 0 1)) && hasAtom A (.mul (.n 12) (.n 11) (.n 10)) &&
  hasAtom A (.add (.n 13) (.n 6) (.n 12)) &&
  hasAtom A (.const (.n 14) (word 0 1 0)) && hasAtom A (.mul (.n 15) (.n 14) (.n 7)) &&
  hasAtom A (.add (.n 16) (.n 10) (.n 15)) &&
  hasCall P "da_vector" [.n 6] [.n 17, .n 18, .n 19, .n 20] &&
  guardOk P (.n 35) "__loop22" (.n 36) (.n 2) [.n 32, .n 33] &&
  A.any (isConstAt (.n 37) 1 0) &&
  hasCall P "__loop23" [.n 37, .n 2, .n 33, .n 17, .n 18, .n 19, .n 20, .n 1] [] &&
  monoIs A (.n 39) (.n 4) (.n 4) 3 &&
  guardOk P (.n 42) "__loop24" (.n 43) (.n 2) [.n 33, .n 1, .n 40] &&
  hasCall P "da_padding_root" [.n 1] [.n 44, .n 45] &&
  guardOk P (.n 47) "__loop25" (.n 48) (.n 5) [.n 40, .n 2, .n 44, .n 45] &&
  P.any (stmtEqb · (.dispatch (.n 3) dlNames [.n 40, .n 1] [.n 49, .n 50])) &&
  A.any (isCopyAt (.n 51) (.n 49)) && A.any (isCopyAt (.n 52) (.n 50)) &&
  A.any (isCopyAt (.n 53) (.n 13)) && A.any (isCopyAt (.n 54) (.n 16))

set_option maxRecDepth 100000 in
theorem dvS_ok : dvOkS = true := by decide +kernel

set_option maxRecDepth 100000 in
kernel_rfl dv_idxS : SaltedGuest.coreProgram[27]? = some LeanVM.SaltedGuest.Data.core27

theorem find_da_verifyS :
    SaltedGuest.coreProgram.find? "da_verify" = some LeanVM.SaltedGuest.Data.core27 :=
  find_of_getElem? dv_idxS

/-- **The salted `da_verify`, soundly, its witness named**: under a call relation that unfolds at
`Vm` and lies below the salted core IR's, on a memory image with the exponent table at its first
argument, for a seed whose key is at its second, the returned words are the cells of a root and the
rate cells of a challenge `z` that `dvWitK σ Vm` opens under the seed. -/
theorem da_verify_sound_wK (hVm : End.UnfoldsV rd C Vm)
    (hle : CallRel.Le C (SaltedGuest.coreProgram.Rel rd)) (hm : End.MemOk rd) {σ : Val}
    {gsq key : E} {rets : List E}
    (hpar0 : LeanVM.SaltedGuest.Data.core27.params.map σ = [gsq, key])
    (hb : Stmt.HoldsList C rd σ (Fn.body LeanVM.SaltedGuest.Data.core27) False (fun rs => rs = rets))
    (hsq0 : SquaresAt rd gsq) {s : Digest} (hks : KeyIs rd key s) :
    ∃ (root : Digest) (z c2 : E), OpensUnder s root z (dvWitK σ Vm) ∧ IsInK c2 ∧
      rets = digestCells root ++ [z + y * y * c2, c2 + y * eOfNat 0] := by
  have hok := dvS_ok
  unfold dvOkS at hok
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hparams, hbody⟩, hflat⟩, hcrs⟩, hc7⟩, hink⟩, hc11⟩, hm12⟩,
    ha13⟩, hc14⟩, hm15⟩, ha16⟩, hcv⟩, hg22⟩, hc37⟩, hc23⟩, hm39⟩, hg24⟩, hcpr⟩, hg25⟩, hdisp⟩,
    hcp51⟩, hcp52⟩, hcp53⟩, hcp54⟩ := hok
  have hσ01 : σ (.n 0) = gsq ∧ σ (.n 1) = key := by
    rw [hparams] at hpar0
    simpa using hpar0
  have hsq : SquaresAt rd (σ (.n 0)) := by rw [hσ01.1]; exact hsq0
  have hk1 : KeyIs rd (σ (.n 1)) s := by rw [hσ01.2]; exact hks
  rw [stmtsEqb_sound hbody, holdsList_append] at hb
  obtain ⟨hallC, hret⟩ := holdsList_flat dvPS hflat _ _ hb
  have hall : ∀ s ∈ dvPS, Stmt.Holds (SaltedGuest.coreProgram.Rel rd) rd σ s True
      (fun rs => rs = rets) :=
    fun s hs => holds_mono hle s id (fun _ h => h) (hallC s hs)
  simp only [Stmt.HoldsList, Stmt.Holds, List.map_cons, List.map_nil] at hret
  have hat := atoms_of_flat hall
  -- the shape (`da_row_shape`, an unchanged function)
  have hrs := da_row_shape_holds rd hm _ _
    (toD (by decide +kernel) (by decide +kernel) (call_of_flat hall hcrs))
  simp only [List.map_cons, List.map_nil, MeaningDaRowShape] at hrs
  obtain ⟨r, L, hr1, hr, hL, h1, h2, hnp, h34⟩ := hrs hsq
  simp only [List.cons.injEq, and_true] at h34
  obtain ⟨h3, h4⟩ := h34
  unfold LeanDa.maxRows at hr
  have hL2 : 2 ^ L ≤ 1024 := by
    calc 2 ^ L ≤ 2 ^ 10 := Nat.pow_le_pow_right (by norm_num) hL
      _ = 1024 := by norm_num
  have hrL : r ≤ 2 ^ L := by
    rw [hnp, LeanDa.paddedRowCount, LeanDa.logPaddedRowCount]; exact Nat.le_pow_clog (by norm_num) r
  have hr' : r < ordG := ordG_of (by omega)
  have hg' : 2 ^ L - r < ordG := ordG_of (by omega)
  -- the challenge's cells
  set z := σ (.n 6)
  have c7 := hasAtom_sound hc7 hat
  have c11 := hasAtom_sound hc11 hat
  have m12 := hasAtom_sound hm12 hat
  have a13 := hasAtom_sound ha13 hat
  have c14 := hasAtom_sound hc14 hat
  have m15 := hasAtom_sound hm15 hat
  have a16 := hasAtom_sound ha16 hat
  have ik := hasAtom_sound hink hat
  simp only [Atom.Holds] at c7 c11 m12 a13 c14 m15 a16 ik
  have e13 : σ (.n 13) = z + y * y * σ (.n 10) := by rw [a13, m12, c11, word_yy]
  have e16 : σ (.n 16) = σ (.n 10) + y * eOfNat 0 := by rw [a16, m15, c14, c7, word_y, word_eOfNat]
  -- the dual codeword's builders (`da_vector`, an unchanged function)
  have hvec := da_vector_holds rd _ _
    (toD (by decide +kernel) (by decide +kernel) (call_of_flat hall hcv))
  simp only [List.map_cons, List.map_nil] at hvec
  -- the regions (`__loop22`, the deployed `__loop21`)
  have L17 : ∀ i < r, LoadHolds rd (σ (.n 33) * gen ^ i) 0 (σ (.n 32) * (gen ^ i) ^ 641) ∧
      LoadHolds rd (σ (.n 32) * (gen ^ i) ^ 641) 512 0 :=
    Digest.loop_sound (f := "__loop21") (ps := [σ (.n 2), σ (.n 32), σ (.n 33)]) hr' h1
      (fun y hy => by
        obtain ⟨k1, k2⟩ := l17_step hy
        exact ⟨k1 _ _ _ rfl, k2⟩)
      (fun hne => by
        have hc := guardK_soundC hg22 hall (by simpa using hne)
        have h' := (Same.rel_same rd (f := "__loop22") (by decide +kernel) _ _).mp hc
        rw [show Same.rho "__loop22" = "__loop21" by decide +kernel] at h'
        simpa using h')
  -- the columns
  have c23 := call_of_flat hallC hc23
  simp only [List.map_cons, List.map_nil] at c23
  rw [const_sound hc37 hat, word_one, ← pow_zero gen] at c23
  have Cc : ∀ h < 128, C "da_verify_column" (dvColArgsS σ h) [] := fun h hh =>
    loop_fromC (C := C) (f := "__loop23") (N := gen ^ 128) (m := 128) (a := 0) (ordG_of (by omega))
      rfl (fun x hx => by
        obtain ⟨k1, k2⟩ := l23_stepW hVm hx
        exact ⟨k1, by rw [← word_g128]; exact k2⟩) c23 h (Nat.zero_le _) hh
  have hcargs : ∀ h, dvColArgsS σ h = [gen ^ h, gen ^ r, σ (.n 33), σ (.n 17), σ (.n 18),
      σ (.n 19), σ (.n 20), σ (.n 1)] := fun h => by rw [dvColArgsS, h1]
  have colF : ∀ h i, ∃ a : E, h < 128 → i < r → (dvSymsS σ Vm i h).length = 256 ∧
      LoadHolds rd (σ (.n 32) * (gen ^ i) ^ 641) (2 * h)
        (digestHalves (keyedHash s ((dvSymsS σ Vm i h).flatMap K.toBytes))).1 ∧
      LoadHolds rd (σ (.n 32) * (gen ^ i) ^ 641) (2 * h + 1)
        (digestHalves (keyedHash s ((dvSymsS σ Vm i h).flatMap K.toBytes))).2 ∧
      LoadHolds rd (σ (.n 32) * (gen ^ i) ^ 641) (h + 512) a ∧
      LoadHolds rd (σ (.n 32) * (gen ^ i) ^ 641) (h + 513)
        (a + ∑ e ∈ Finset.range 256, dualAt z (256 * h + e) * ofK ((dvSymsS σ Vm i h).getD e 0)) := by
    intro h i
    by_cases hhi : h < 128 ∧ i < r
    · have hc := Cc h hhi.1
      rw [hcargs] at hc
      obtain ⟨hl, base, a, hb0, k0, k1, k2, k3⟩ := col_stepWK hVm hle hk1 hhi.1 hr' hvec hc i hhi.2
      have e := loadHolds_unique hb0 (L17 i hhi.2).1
      rw [e] at k0 k1 k2 k3
      have hs : dvSymsS σ Vm i h = colSymsS Vm [gen ^ h, gen ^ r, σ (.n 33), σ (.n 17), σ (.n 18),
          σ (.n 19), σ (.n 20), σ (.n 1)] i := by rw [dvSymsS, hcargs]
      rw [hs]
      exact ⟨a, fun _ _ => ⟨hl, k0, k1, k2, k3⟩⟩
    · exact ⟨0, fun a b => absurd ⟨a, b⟩ hhi⟩
  choose acc hcell using colF
  -- the witness's symbols, padded outside the run's ranges
  have hrows : dvRowsS σ = r := by
    rw [dvRowsS, h1, gLog_gen_pow (by omega)]; omega
  let symsP : ℕ → ℕ → List K := dvSymsPS σ Vm
  have hsP : ∀ i h, i < r → h < 128 → symsP i h = dvSymsS σ Vm i h := fun i h hi hh => by
    simp only [symsP, dvSymsPS, hrows, hi, hh, and_self, ite_true]
  have hsL : ∀ i h, (symsP i h).length = 256 := fun i h => by
    by_cases hc : i < r ∧ h < 128
    · rw [hsP i h hc.1 hc.2]; exact (hcell h i hc.2 hc.1).1
    · simp only [symsP, dvSymsPS, hrows, hc, ite_false, List.length_replicate]
  -- the blobs' sums and roots (`__loop24`)
  have L19 : ∀ i < r, ∃ base c0 c1, LoadHolds rd (σ (.n 33) * gen ^ i) 0 base ∧
      LoadHolds rd base 640 0 ∧
      SaltedGuest.coreProgram.Rel rd "da_levels__L128_L7" [base, σ (.n 1)] [c0, c1] ∧
      LoadHolds rd (σ (.n 40) * (gen ^ i) ^ 2) 0 c0 ∧ LoadHolds rd (σ (.n 40) * (gen ^ i) ^ 2) 1 c1 :=
    loop_soundC (C := SaltedGuest.coreProgram.Rel rd) (f := "__loop24")
      (ps := [σ (.n 2), σ (.n 33), σ (.n 1), σ (.n 40)]) hr' h1
      (fun y hy => by
        obtain ⟨k1, k2⟩ := l24_step hy
        exact ⟨k1 _ _ _ _ rfl, k2⟩)
      (fun hne => by simpa using guardK_soundC hg24 hall hne)
  have hdot : ∀ i < r, ∑ h ∈ Finset.range 128, ∑ e ∈ Finset.range 256,
      dualAt z (256 * h + e) * ofK ((symsP i h).getD e 0) = 0 := by
    intro i hi
    obtain ⟨base, c0, c1, hb0, h640, -, -, -⟩ := L19 i hi
    rw [loadHolds_unique hb0 (L17 i hi).1] at h640
    have run : ∀ h ≤ 128, LoadHolds rd (σ (.n 32) * (gen ^ i) ^ 641) (h + 512)
        (∑ h' ∈ Finset.range h, ∑ e ∈ Finset.range 256,
          dualAt z (256 * h' + e) * ofK ((symsP i h').getD e 0)) := by
      intro h
      induction h with
      | zero => intro _; simpa using (L17 i hi).2
      | succ h ih =>
        intro hh
        obtain ⟨-, -, -, k2, k3⟩ := hcell h i (by omega) hi
        rw [loadHolds_unique k2 (ih (by omega)), ← hsP i h hi (by omega)] at k3
        rw [Finset.sum_range_succ, show h + 1 + 512 = h + 513 by ring]
        exact k3
    exact loadHolds_unique (run 128 le_rfl) h640
  have hblob : ∀ i < r, LoadHolds rd (σ (.n 40)) (2 * i) (digestHalves (blobLeafK s r symsP i)).1 ∧
      LoadHolds rd (σ (.n 40)) (2 * i + 1) (digestHalves (blobLeafK s r symsP i)).2 := by
    intro i hi
    obtain ⟨base, c0, c1, hb0, -, hlv, k0, k1⟩ := L19 i hi
    rw [loadHolds_unique hb0 (L17 i hi).1] at hlv
    have hroot := levels_root_ofK (k := 7) (L := 7) (g := cellDK s symsP i) hk1 (by norm_num)
      (by norm_num) (gen_pow_eq_ofK 7).symm hlv fun h hh => by
        obtain ⟨-, k0, k1, -, -⟩ := hcell h i (by simpa using hh) hi
        simp only [cellDK, hsP i h hi (by simpa using hh)]
        exact ⟨k0, k1⟩
    rw [shift2] at k0 k1
    simp only [Prod.ext_iff] at hroot
    simp only [blobLeafK, hi, ite_true]
    rw [← hroot.1, ← hroot.2]
    exact ⟨by simpa using k0, k1⟩
  -- the padding root and the padding blobs (`__loop25`)
  have hpr := da_padding_root_soundK rd _ _ (call_of_flat hall hcpr)
  simp only [List.map_cons, List.map_nil, MeaningDaPaddingRoot] at hpr
  have hpr' := hpr s hk1
  simp only [digestCells, List.cons.injEq, and_true] at hpr'
  obtain ⟨e44, e45⟩ := hpr'
  have L20 : ∀ d < 2 ^ L - r, LoadHolds rd (σ (.n 40) * σ (.n 2) ^ 2 * (gen ^ d) ^ 2) 0
        (digestHalves (padRootK s)).1 ∧
      LoadHolds rd (σ (.n 40) * σ (.n 2) ^ 2 * (gen ^ d) ^ 2) 1 (digestHalves (padRootK s)).2 :=
    loop_soundC (C := SaltedGuest.coreProgram.Rel rd) (f := "__loop25")
      (ps := [σ (.n 5), σ (.n 40), σ (.n 2), σ (.n 44), σ (.n 45)])
      (B := fun x => LoadHolds rd (σ (.n 40) * σ (.n 2) ^ 2 * x ^ 2) 0 (digestHalves (padRootK s)).1 ∧
        LoadHolds rd (σ (.n 40) * σ (.n 2) ^ 2 * x ^ 2) 1 (digestHalves (padRootK s)).2) hg' h4
      (fun y hy => by
        obtain ⟨k1, k2⟩ := l25_step hy
        obtain ⟨k1a, k1b⟩ := k1 _ _ _ _ _ rfl
        rw [e44] at k1a
        rw [e45] at k1b
        exact ⟨⟨k1a, k1b⟩, k2⟩)
      (fun hne => by simpa using guardK_soundC hg25 hall hne)
  -- the root
  have hrt : (σ (.n 49), σ (.n 50)) = digestHalves (daRootK s r L symsP) := by
    obtain ⟨k, hk, hk2, hrel⟩ := dispatch_of_flat hall hdisp
    simp only [dlNames, List.length_map, List.length_range] at hk
    simp only [dlNames, List.getElem_map, List.getElem_range, List.map_cons, List.map_nil] at hrel
    refine levels_root_ofK hk1 hk hL (by rw [← hk2, h2]) hrel fun i hi => ?_
    by_cases hir : i < r
    · exact hblob i hir
    · obtain ⟨g0, g1⟩ := L20 (i - r) (by omega)
      rw [h1, ← pow_mul, shift, show r * 2 + 2 * (i - r) = 2 * i by omega] at g0 g1
      simp only [blobLeafK, hir, ite_false]
      exact ⟨by simpa using g0, g1⟩
  refine ⟨daRootK s r L symsP, z, σ (.n 10), ?_, ik.1, ?_⟩
  · rw [dvWitK, hrows]
    exact opens_ofK hr1 (by unfold LeanDa.maxRows; exact hr) hnp.symm hrL hsL hdot
  rw [← hret, copy_sound hcp51 hat, copy_sound hcp52 hat, copy_sound hcp53 hat,
    copy_sound hcp54 hat, e13, e16]
  simp only [Prod.ext_iff] at hrt
  simp [digestCells, ← hrt.1, ← hrt.2]

end
end LeanVM.SaltedGuest.B1.Da
