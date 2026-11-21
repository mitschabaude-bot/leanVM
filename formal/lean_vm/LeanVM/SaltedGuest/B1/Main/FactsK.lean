/-
  LeanVM.SaltedGuest.B1.Main.FactsK

  What a run of the salted `main`'s body gives (`MainFactsK`), at the deployed `main`'s numbering.
-/

module

public import LeanVM.SaltedGuest.B1.Main.LoopsK
public import LeanVM.SaltedGuest.B1.FrameTransfer
public import LeanVM.SaltedGuest.B1.ExpTables
public import LeanVM.Guest.B1.Sig.XmssLoop2

/-!
# The salted `main`'s facts

`MainFactsK C rd τ S key` is the deployed `Main.MainFacts` at the valuation `τ = σ ∘ mainR` (the
salted `main`'s values read at the deployed numbers, `mainR`), for the seed `S` of memory words `2`
and `3` and its key `key`, with the fields where the salted `main` differs:

* `seed`, `keyIs`: the cells `fs_seed` are the halves of `S`, and `key` holds `S`'s key
  (`key_of_seed`);
* `xlist`, `slist`: the declared claim lists' digests are keyed by `S` (`ClaimListOutS`);
* `rawx`, `raws`: the signature loops' calls, at their deployed names (`toDC C`);
* `da`: the direct DA check takes the key, and the node's own DA digest is the keyed hash of the
  claim's four cells;
* `children`: each child's iteration with its claim lists under the key (`KidStepCK`);
* `agg`: the batching takes the seed's cells;
* `stmt`: `statement_digest` (unchanged) at the deployed core IR.

`main_factsK`: a run of the salted `main`'s body over a call relation that unfolds at a frame map
gives them, at `τ`.
-/

namespace LeanVM.SaltedGuest.B1.Main

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Guest.Value.Keccak LeanVM.Guest.B1 LeanVM.Guest.B1.Digest
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Node LeanVM.Guest.B1.Main LeanVM.SaltedGuest.B1 Recursion.Salted LeanVM.Guest.B1.Da

@[expose] public section

/-- **A claim list's digest under `s`**: the table at `entries` holds `4 n` canonical cells, and
`rets` are the cells of their keyed hash. -/
def ClaimListOutS (rd : Reader) (s : Digest) (entries : E) (n : ℕ) (rets : List E) : Prop :=
  ∃ cells : List E, cells.length = 4 * n ∧ ReadsAt rd entries cells ∧ AllCanonical cells ∧
    rets = digestCells (keyedHash s (cellsBytes cells))

/-- **What a run of the salted `main`'s body gives**, at the deployed numbering. -/
structure MainFactsK (C : CallRel) (rd : Reader) (σ : Val) (S : Digest) (key : E) : Prop where
  counts : ∀ v ∈ [0, 1, 2, 3, 4, 5], σ (.n v) = gen ^ lg σ v ∧ lg σ v < 2 ^ 32
  kids : σ (.n 6) = gen ^ lg σ 6 ∧ lg σ 6 ≤ 16
  direct : σ (.n 7) = gen ^ lg σ 7 ∧ lg σ 7 ≤ 1
  lxs : σ (.n 22) = gen ^ (lg σ 0 + lg σ 1)
  lss : σ (.n 23) = gen ^ (lg σ 3 + lg σ 4)
  total : σ (.n 24) = gen ^ (lg σ 0 + lg σ 1 + (lg σ 3 + lg σ 4)) ∧
    lg σ 0 + lg σ 1 + (lg σ 3 + lg σ 4) < 2 ^ 32
  addr : ∀ v ∈ [0, 1, 2, 3, 4, 5, 24], ∃ t, LoadHolds rd (σ (.n v)) 0 t
  /-- The cells `fs_seed` are the seed's halves. -/
  seed : (σ (.n 26), σ (.n 27)) = digestHalves S
  /-- `key` holds the seed's key. -/
  keyIs : KeyIs rd key S
  exp : ExpTables rd (σ (.n 28))
  xlist : ClaimListOutS rd S (σ (.n 31)) (lg σ 0) [σ (.n 35), σ (.n 36)]
  slist : ClaimListOutS rd S (σ (.n 34)) (lg σ 3) [σ (.n 37), σ (.n 38)]
  bytes : Sig.ByteBits rd (σ (.n 47))
  spcov : σ (.n 46) = σ (.n 45) * σ (.n 22)
  rawx : ∀ i < lg σ 2, toDC C "__loop2" (gen ^ i :: l2Args σ) [] ∧
    ∃ s, BelowLog (σ (.n 22)) s ∧ LoadHolds rd (σ (.n 45)) s (gen ^ i)
  tags : Sig.LxTagsHold (fun j => (l2Args σ).getD (4 + j) 0)
  raws : ∀ j < lg σ 5, RawSStepC (toDC C) rd (σ (.n 23)) (σ (.n 45)) (σ (.n 22)) (σ (.n 2))
    (σ (.n 34)) (σ (.n 47)) (gen ^ j)
  own : σ (.n 366) = σ (.n 364) * gen ^ (2 * lg σ 6)
  da : lg σ 7 = 1 →
    C "da_verify" [σ (.n 28), key] [σ (.n 369), σ (.n 370), σ (.n 371), σ (.n 372)] ∧
    AllCanonical [σ (.n 369), σ (.n 370), σ (.n 371), σ (.n 372)] ∧
    LoadHolds rd (σ (.n 366)) 0
      (digestHalves (keyedHash S (cellsBytes [σ (.n 369), σ (.n 370), σ (.n 371), σ (.n 372)]))).1 ∧
    LoadHolds rd (σ (.n 366)) 1
      (digestHalves (keyedHash S (cellsBytes [σ (.n 369), σ (.n 370), σ (.n 371), σ (.n 372)]))).2
  daz : lg σ 7 = 0 → LoadHolds rd (σ (.n 366)) 0 0 ∧ LoadHolds rd (σ (.n 366)) 1 0
  written0 : LoadHolds rd (σ (.n 399)) 0 (gen ^ (lg σ 2 + lg σ 5))
  children : ∀ c < lg σ 6, KidStepCK C rd (σ (.n 399)) key (σ (.n 31)) (σ (.n 45)) (σ (.n 22))
    (σ (.n 34)) (σ (.n 46)) (σ (.n 23)) (σ (.n 396)) (σ (.n 364)) (σ (.n 26)) (σ (.n 27))
    (σ (.n 384)) (σ (.n 28)) (σ (.n 390)) (gen ^ c)
  writtenN : LoadHolds rd (σ (.n 399)) (lg σ 6) (σ (.n 24))
  pick : σ (.n 406) = gen ^ lg σ 406 ∧ lg σ 406 ≤ lg σ 6 ∧ (lg σ 7 = 1 → lg σ 406 = lg σ 6)
  picked : σ (.n 416) = σ (.n 364) * gen ^ (2 * lg σ 406)
  leaf : lg σ 6 = 0 → ∀ k < 23, LoadHolds rd (σ (.n 417)) k 0
  agg : lg σ 6 ≠ 0 → C "aggregate_claims"
    [σ (.n 26), σ (.n 27), σ (.n 6), σ (.n 384), σ (.n 390), σ (.n 396), σ (.n 417)] []
  dacells : LoadHolds rd (σ (.n 416)) 0 (σ (.n 444)) ∧ LoadHolds rd (σ (.n 416)) 1 (σ (.n 445))
  stmt : Guest.coreProgram.Rel rd "statement_digest"
    [σ (.n 26), σ (.n 27), σ (.n 35), σ (.n 36), σ (.n 37), σ (.n 38), σ (.n 444), σ (.n 445),
      σ (.n 417)] [σ (.n 446), σ (.n 447)]
  pub : LoadHolds rd 1 0 (σ (.n 446)) ∧ LoadHolds rd 1 1 (σ (.n 447))

/-- The salted `main`'s valuation read at the deployed numbers. -/
def mainVal (σ : Val) : Val := fun v => σ (mainR v)

theorem mainVal_n (σ : Val) (k : ℕ) : mainVal σ (.n k) = σ (.n (mainRi k)) := rfl

theorem lg_mainVal (σ : Val) (k : ℕ) : lg (mainVal σ) k = lg σ (mainRi k) := by
  unfold lg; rfl

set_option maxRecDepth 100000 in
theorem noRet_mDaS : Stmt.noRetList mDaS = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem noRet_mDaZS : Stmt.noRetList mDaZS = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem noRet_mLeafS : Stmt.noRetList mLeafS = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem noRet_mAggS : Stmt.noRetList mAggS = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- The DA branch's `node_key` run. -/
theorem da_nodeKeyOk : nodeKeyOk (atomsIn mDaS) (.n 34) mainKeyVl (.n 402) (.n 397) (.n 407)
    (.n 406) = true := by decide +kernel

/-- A salted call of an unchanged function of the same deployed name. -/
theorem relToD {rd : Reader} {f : String} (hf : Same.inS f = true) (hr : Same.rho f = f)
    {args rets : List E} (h : SaltedGuest.coreProgram.Rel rd f args rets) :
    Guest.coreProgram.Rel rd f args rets :=
  (Same.rel_same' rd hf hr args rets).mp h

theorem toDC_same {C : CallRel} {f : String} (hf : Same.inS f = true) (hr : Same.rho f = f)
    {args rets : List E} (h : C f args rets) : toDC C f args rets := by
  have := toDC_of (C := C) hf h
  rwa [hr] at this

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
set_option linter.unusedSimpArgs false in
/-- **The facts of a run of the salted `main`'s body**, at the deployed numbering, for the seed `S`
of memory words `2` and `3`. -/
theorem main_factsK {rd : Reader} {C : CallRel} {V : End.FrameMap} (hV : End.UnfoldsV rd C V)
    (hle : CallRel.Le C (SaltedGuest.coreProgram.Rel rd)) (hm : End.MemOk rd) {S : Digest}
    (hS2 : LoadHolds rd 1 2 (digestHalves S).1) (hS3 : LoadHolds rd 1 3 (digestHalves S).2)
    {σ : Val}
    (h : Stmt.HoldsList C rd σ (Fn.body LeanVM.SaltedGuest.Data.core0) False (fun rs => rs = [])) :
    MainFactsK C rd (mainVal σ) S (σ (.n 34)) := by
  have hVd := unfoldsV_toD hV
  have hCd := unfolds_of_V hVd
  have hX : ∀ args, toDC C "__loop2" args [] → ∃ sig, Loop2Out (toDC C) rd args sig := by
    intro args hx
    obtain ⟨hp, hbx⟩ := body_ofV hVd find_loop2 hx
    exact ⟨_, loop2Out_of_body Sig.verify_lean_xmss_sound_holds hp hbx⟩
  have g0 : lg (mainVal σ) 0 = lg σ 0 := lg_mainVal σ 0
  have g1 : lg (mainVal σ) 1 = lg σ 1 := lg_mainVal σ 1
  have g2 : lg (mainVal σ) 2 = lg σ 2 := lg_mainVal σ 2
  have g3 : lg (mainVal σ) 3 = lg σ 3 := lg_mainVal σ 3
  have g4 : lg (mainVal σ) 4 = lg σ 4 := lg_mainVal σ 4
  have g5 : lg (mainVal σ) 5 = lg σ 5 := lg_mainVal σ 5
  have g6 : lg (mainVal σ) 6 = lg σ 6 := lg_mainVal σ 6
  have g7 : lg (mainVal σ) 7 = lg σ 7 := lg_mainVal σ 7
  have g406 : lg (mainVal σ) 406 = lg σ 435 := lg_mainVal σ 406
  rw [core0_shapeS] at h
  simp only [List.append_assoc, holdsList_append] at h
  have hP := pre_okS
  have hD := da_okS
  have hZ := daZ_okS
  have hM := mid_okS
  have hL := leaf_okS
  have hQ := post_okS
  simp only [preOkS, Bool.and_eq_true, and_assoc, List.all_eq_true, List.mem_range] at hP
  simp only [daOkS, Bool.and_eq_true, and_assoc, List.all_eq_true, List.mem_range] at hD
  simp only [daZOkS, Bool.and_eq_true, and_assoc] at hZ
  simp only [midOkS, Bool.and_eq_true, and_assoc] at hM
  simp only [leafOkS, Bool.and_eq_true, and_assoc, List.all_eq_true, List.mem_range] at hL
  simp only [postOkS, Bool.and_eq_true, and_assoc] at hQ
  obtain ⟨pflat, prc, prc6, prc7, prc42, pm40, pm41, pm42, pexp, pc26, pc27, pm28, pl29, pc30, pc31,
    pm32, pl33, pks, pxl, psl, pbytes, pm67, pl3, ptags, pl4, pm335, pm336, pa338, pc337⟩ := hP
  obtain ⟨dflat, dver, -, dadd, -, -, dcp403, dcp404, dcp405, -, -, dkec, dl408, dl409⟩ := hD
  obtain ⟨zflat, zc362, zl362, zc363, zl363⟩ := hZ
  obtain ⟨mflat, mm381, ml381, ml5, mm385, ml386, meq, mrc, ma395, ma397, mc396,
    mm398, mc399, mae, mm400, mm401, ma404, mc403⟩ := hM
  obtain ⟨lflat, lzero, l405, aflat, acall⟩ := hL
  obtain ⟨qflat, ql429, ql430, qsd, qc433, ql434, qe1, qc435, qc436, qm437, ql438, qe2⟩ := hQ
  -- the blocks
  obtain ⟨hpre, h⟩ := holdsList_flat mPreS (List.all_eq_true.mpr pflat) _ _ h
  simp only [Stmt.HoldsList] at h
  rw [holds_ite_noRet _ _ _ noRet_mDaS noRet_mDaZS] at h
  obtain ⟨⟨-, hdz, hdn⟩, h⟩ := h
  obtain ⟨hmid, h⟩ := holdsList_flat mMidS mflat _ _ h
  rw [holds_ite_noRet _ _ _ noRet_mLeafS noRet_mAggS] at h
  obtain ⟨⟨-, hlz, hln⟩, h⟩ := h
  obtain ⟨hpost, -⟩ := holdsList_flat mPostS qflat _ _ h
  have atP := atoms_of_flat hpre
  have atM := atoms_of_flat hmid
  have atQ := atoms_of_flat hpost
  -- the counts
  have hc : ∀ v < 6, ∃ e < 2 ^ 32, σ (.n v) = gen ^ e :=
    fun v hv => load_gpow hm (touch_sound (prc v hv) atP)
  have hcl : ∀ v < 6, σ (.n v) = gen ^ lg σ v ∧ lg σ v < 2 ^ 32 := fun v hv => by
    obtain ⟨e, he, hv'⟩ := hc v hv
    obtain ⟨h1, h2⟩ := pow_lg (by omega) hv'
    exact ⟨h1, by omega⟩
  obtain ⟨e6, he6, h6⟩ := rcConst_sound hm (by norm_num) word_g16 prc6 atP
  obtain ⟨e7, he7, h7⟩ := rcConst_sound hm (by norm_num) word_g1 prc7 atP
  obtain ⟨e42, he42, h42⟩ := load_gpow hm (touch_sound prc42 atP)
  obtain ⟨l6, r6⟩ := pow_lg (by omega) h6
  obtain ⟨l7, r7⟩ := pow_lg (by omega) h7
  obtain ⟨c0, b0⟩ := hcl 0 (by omega)
  obtain ⟨c1, b1⟩ := hcl 1 (by omega)
  obtain ⟨c2, b2⟩ := hcl 2 (by omega)
  obtain ⟨c3, b3⟩ := hcl 3 (by omega)
  obtain ⟨c4, b4⟩ := hcl 4 (by omega)
  obtain ⟨c5, b5⟩ := hcl 5 (by omega)
  have h40 : σ (.n 22) = gen ^ (lg σ 0 + lg σ 1) := by rw [isMul_sound pm40 atP, c0, c1, pow_add]
  have h41 : σ (.n 23) = gen ^ (lg σ 3 + lg σ 4) := by rw [isMul_sound pm41 atP, c3, c4, pow_add]
  have h42' : σ (.n 24) = gen ^ (lg σ 0 + lg σ 1 + (lg σ 3 + lg σ 4)) := by
    rw [isMul_sound pm42 atP, h40, h41, ← pow_add]
  have hT := gen_pow_inj34 (by omega) (by omega) (h42.symm.trans h42')
  have h336 : σ (.n 373) = σ (.n 371) * gen ^ (2 * lg σ 6) := by
    rw [isMul_sound pm336 atP, isMul_sound pm335 atP, l6, ← pow_add, two_mul]
  -- the seed and its key
  have hs29 : σ (.n 29) = (digestHalves S).1 := by
    have l := load_sound pl29 atP
    rw [isMul_sound pm28 atP, const_sound pc26 atP, const_sound pc27 atP, word_one,
      show word 4 0 0 = gen ^ 2 from word_two_pow (a := 2) (by norm_num)] at l
    exact loadHolds_unique ((loadHolds_mul_gen_pow rd 1 2 0 _).mp l) hS2
  have hs33 : σ (.n 33) = (digestHalves S).2 := by
    have l := load_sound pl33 atP
    rw [isMul_sound pm32 atP, const_sound pc30 atP, const_sound pc31 atP, word_one,
      show word 8 0 0 = gen ^ 3 from word_two_pow (a := 3) (by norm_num)] at l
    exact loadHolds_unique ((loadHolds_mul_gen_pow rd 1 3 0 _).mp l) hS3
  have hkey : KeyIs rd (σ (.n 34)) S :=
    key_of_seed_sound rd _ _ (hle _ _ _ (call_of_flat hpre pks)) S (by rw [hs29, hs33])
  -- the pick
  obtain ⟨p, hp, hbl⟩ := rcDir_sound hm mrc atM
  have h389 : σ (.n 6) * gen = gen ^ (lg σ 6 + 1) := by
    rw [l6, pow_succ]
  have hplt := belowLog_lt (by omega) h389 hbl
  obtain ⟨lp, rp⟩ := pow_lg (by omega) hp
  -- the loops
  have hguard3 := guard_soundC pl3 hpre
  have hguard4 := guard_soundC pl4 hpre
  have h67 : σ (.n 53) = σ (.n 52) * σ (.n 22) := isMul_sound pm67 atP
  have hlx : ∀ j < 51, σ (.n (311 + j)) = mainVal σ (.n (304 + j)) := fun j hj => by
    have e : mainRi (304 + j) = 311 + j := by unfold mainRi; split_ifs <;> omega
    show σ (.n (311 + j)) = σ (.n (mainRi (304 + j)))
    rw [e]
  have hl2 : l2Args (mainVal σ) = [σ (.n 2), σ (.n 22), σ (.n 52), σ (.n 38)] ++
      lxTagsVS.map σ := by
    unfold l2Args lxTagsVS
    simp only [List.map_map]
    congr 1
  refine ⟨fun v hv => ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [List.mem_cons, List.mem_nil_iff, or_false] at hv
    rcases hv with rfl | rfl | rfl | rfl | rfl | rfl <;> simp only [g0, g1, g2, g3, g4, g5] <;>
      first | exact hcl 0 (by omega) | exact hcl 1 (by omega) | exact hcl 2 (by omega) | exact hcl 3 (by omega) | exact hcl 4 (by omega) | exact hcl 5 (by omega)
  · rw [g6]; exact ⟨l6, by omega⟩
  · rw [g7]; exact ⟨l7, by omega⟩
  · simp only [g0, g1, g2, g3, g4, g5, g6, g7, g406]; exact h40
  · simp only [g0, g1, g2, g3, g4, g5, g6, g7, g406]; exact h41
  · simp only [g0, g1, g2, g3, g4, g5, g6, g7, g406]; exact ⟨h42', by omega⟩
  · intro v hv
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hv
    rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp only [mainVal_n, mainRi, Nat.reduceLT, Nat.reduceAdd, Nat.reduceEqDiff, ↓reduceIte]
    all_goals first
      | exact ⟨_, touch_sound prc42 atP⟩
      | exact ⟨_, touch_sound (prc _ (by omega)) atP⟩
  · show (σ (.n 29), σ (.n 33)) = _
    rw [hs29, hs33]
  · exact hkey
  · -- the exponent tables
    exact End.expTablesSound rd _ (hle _ _ _ (call_of_flat hpre pexp))
  · obtain ⟨n, hn, hng, hout⟩ :=
      Digest.claim_list_digest_soundK rd hm _ _ (hle _ _ _ (call_of_flat hpre pxl))
    rw [c0] at hng
    have hn' : n < 136 * 2 ^ 32 := hn
    have := gen_pow_inj (by omega) (by omega) hng
    rw [g0]
    rw [this]
    exact hout S hkey
  · obtain ⟨n, hn, hng, hout⟩ :=
      Digest.claim_list_digest_soundK rd hm _ _ (hle _ _ _ (call_of_flat hpre psl))
    rw [c3] at hng
    have hn' : n < 136 * 2 ^ 32 := hn
    have := gen_pow_inj (by omega) (by omega) hng
    rw [g3]
    rw [this]
    exact hout S hkey
  · intro v hv
    obtain ⟨hcv, hlv⟩ := pbytes v hv
    have := load_sound hlv atP
    rwa [const_sound hcv atP] at this
  · exact h67
  · -- raw leanXMSS
    rw [g2, hl2]
    refine loop_soundC (f := "__loop2") (C := toDC C)
      (ps := [σ (.n 2), σ (.n 22), σ (.n 52), σ (.n 38)] ++ lxTagsVS.map σ)
      (N := σ (.n 2)) (B := fun x => toDC C "__loop2" (x :: ([σ (.n 2), σ (.n 22), σ (.n 52),
        σ (.n 38)] ++ lxTagsVS.map σ)) [] ∧ ∃ s, BelowLog (σ (.n 22)) s ∧ LoadHolds rd (σ (.n 52)) s x)
      (by unfold ordG; omega) c2 (fun x hx => ?_)
      (fun hne => toDC_same (by decide +kernel) (by decide +kernel)
        (by simpa [lxTagsVS, Function.comp_def] using hguard3 hne))
    obtain ⟨h1, h2⟩ := l3_stepC hX hx
    obtain ⟨sig, hout⟩ := hX _ hx
    obtain ⟨s, hbl, hl', -⟩ := rawX_of_out hm hout _ _ _ _ _ rfl
    exact ⟨⟨h1, s, hbl, hl'⟩, h2⟩
  · -- the carried tags
    intro i hi hc
    obtain ⟨h1, h2⟩ := Sig.lxTagSlot_spec i hi hc
    have pt := ptags i hi
    simp only [hc, Bool.not_true, Bool.false_or] at pt
    have e := const_sound pt atP
    rw [word_eOfNat] at e
    show (l2Args (mainVal σ)).getD (4 + (Sig.lxTagSlot i - 1)) 0 = _
    rw [← e, hl2, List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp)]
    simp only [List.length_cons, List.length_nil, List.getElem?_map, lxTagsVS]
    rw [List.getElem?_range (by omega)]
    simp only [Option.map_some, Option.getD_some]
    congr 2
    omega
  · -- raw leanSPHINCS
    rw [g5]
    refine loop_soundC (f := "__loop3") (C := toDC C)
      (ps := [σ (.n 5), σ (.n 23), σ (.n 53), σ (.n 2), σ (.n 41), σ (.n 54)])
      (N := σ (.n 5))
      (B := RawSStepC (toDC C) rd (σ (.n 23)) (σ (.n 52)) (σ (.n 22)) (σ (.n 2)) (σ (.n 41))
        (σ (.n 54)))
      (by unfold ordG; omega) c5 (fun x hx => ?_)
      (fun hne => toDC_same (by decide +kernel) (by decide +kernel) (by simpa using hguard4 hne))
    obtain ⟨h1, h2⟩ := l4_stepC hCd hm hx
    exact ⟨h1 _ _ _ _ _ _ _ (by rw [h67]), h2⟩
  · simp only [g0, g1, g2, g3, g4, g5, g6, g7, g406]; exact h336
  · -- the direct DA check
    intro h71
    rw [g7] at h71
    have h338 : σ (.n 375) = 0 := by
      rw [add_sound pa338 atP, const_sound pc337 atP, word_gen, l7, h71, pow_one, e_add_self]
    obtain ⟨hdall, -⟩ := holdsList_flat mDaS (List.all_eq_true.mpr dflat) _ _ (hdz h338)
    have atD := atoms_of_flat hdall
    have hk := nodeKey_sound da_nodeKeyOk atD hkey rfl
    obtain ⟨-, -, O, hKC, hw⟩ := keccak_holds_full (keccak_sound dkec atD)
    have hx' : ∀ i < 4, σ (.n (393 + i)) = σ (.n (380 + i)) + σ (.n (376 + i)) :=
      fun i hi => add_sound (dadd i hi) atD
    have hin : mainDaIn.map σ =
        [nodeKey S 0 + σ (.n 376), nodeKey S 1 + σ (.n 377), nodeKey S 2 + σ (.n 378),
          nodeKey S 3 + σ (.n 379), nodeKey S 4, nodeKey S 5, nodeKey S 6, nodeKey S 7,
          nodeKey S 8, nodeKey S 9, nodeKey S 10, nodeKey S 11, nodeKey S 12] := by
      simp only [mainDaIn, List.map_cons, List.map_nil]
      rw [hx' 0 (by omega), hx' 1 (by omega), hx' 2 (by omega), hx' 3 (by omega),
        copy_sound dcp403 atD, copy_sound dcp404 atD, copy_sound dcp405 atD,
        ← hk 0, ← hk 1, ← hk 2, ← hk 3, ← hk 4, ← hk 5, ← hk 6, ← hk 7, ← hk 8, ← hk 9, ← hk 10,
        ← hk 11, ← hk 12]
      rfl
    rw [hin] at hKC
    obtain ⟨hcan, hd⟩ := keyed_node_kr (kr := nodeKey S) rfl hKC
    have e0 : σ (.n 408) = O 0 := hw 0 (by simp)
    have e1 : σ (.n 409) = O 1 := hw 1 (by simp)
    have l0 := load_sound dl408 atD
    have l1 := load_sound dl409 atD
    rw [e0] at l0
    rw [e1] at l1
    simp only [Prod.ext_iff] at hd
    rw [hd.1] at l0
    rw [hd.2] at l1
    refine ⟨?_, hcan, l0, l1⟩
    exact call_of_flat hdall dver
  · -- no direct DA check: zeros
    intro h70
    rw [g7] at h70
    have h338 : σ (.n 375) ≠ 0 := by
      rw [add_sound pa338 atP, const_sound pc337 atP, word_gen, l7, h70, pow_zero, add_comm]
      exact gen_add_one_ne
    obtain ⟨hzall, -⟩ := holdsList_flat mDaZS zflat _ _ (hdn h338)
    have atZ := atoms_of_flat hzall
    have z0 := load_sound zl362 atZ
    have z1 := load_sound zl363 atZ
    rw [const_sound zc362 atZ, word_zero] at z0
    rw [const_sound zc363 atZ, word_zero] at z1
    exact ⟨z0, z1⟩
  · have := load_sound ml381 atM
    simp only [g0, g1, g2, g3, g4, g5, g6, g7, g406]
    rwa [isMul_sound mm381 atM, c2, c5, ← pow_add] at this
  · -- the children
    rw [g6]
    have hguard5 := guard_soundC ml5 hmid
    refine loop_soundC (f := "__loop4")
      (ps := [σ (.n 6), σ (.n 428), σ (.n 34), σ (.n 38), σ (.n 52), σ (.n 22), σ (.n 41),
        σ (.n 53), σ (.n 23), σ (.n 425), σ (.n 371), σ (.n 29), σ (.n 33), σ (.n 413), σ (.n 35),
        σ (.n 419)])
      (N := σ (.n 6)) (by unfold ordG; omega) l6 (fun x hx => ?_)
      (fun hne => by simpa using hguard5 hne)
    obtain ⟨h1, h2⟩ := l5_stepCK hV hle hm hx
    exact ⟨h1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ rfl, h2⟩
  · have := load_sound ml386 atM
    rw [isMul_sound mm385 atM, l6, assertEq_sound meq atM] at this
    have := (loadHolds_mul_gen_pow rd _ (lg σ 6) 0 _).mp this
    simp only [mainVal_n, lg_mainVal, mainRi, Nat.reduceLT, Nat.reduceAdd, Nat.reduceEqDiff, ↓reduceIte]
    simpa using this
  · simp only [g0, g1, g2, g3, g4, g5, g6, g7, g406]
    refine ⟨lp, by omega, ?_⟩
    -- with a direct DA check, the node's own slot
    intro h71
    have h398 : σ (.n 442) = 0 := by
      rw [assertEq_sound mae atM, const_sound mc399 atM, word_zero]
    rw [isMul_sound mm398 atM, add_sound ma395 atM, add_sound ma397 atM, const_sound mc396 atM,
      word_one, l7, h71, pow_one] at h398
    rcases mul_eq_zero.mp h398 with h0 | h0
    · rw [hp, l6] at h0
      exact gen_pow_inj34 (by omega) (by omega) (e_add_eq_zero_iff.mp h0) |>.trans rfl |>.symm.trans
        (by rw [rp]) |>.symm
    · exact absurd h0 gen_add_one_ne
  · simp only [mainVal_n, lg_mainVal, mainRi, Nat.reduceLT, Nat.reduceAdd, Nat.reduceEqDiff, ↓reduceIte]
    rw [isMul_sound mm401 atM, isMul_sound mm400 atM, lp, ← pow_add, two_mul]
  · intro h60 k hk
    rw [g6] at h60
    have h404 : σ (.n 448) = 0 := by
      rw [add_sound ma404 atM, const_sound mc403 atM, word_one, l6, h60, pow_zero, e_add_self]
    obtain ⟨hlall, -⟩ := holdsList_flat mLeafS (List.all_eq_true.mpr lflat) _ _ (hlz h404)
    have atL := atoms_of_flat hlall
    obtain ⟨hz, hl'⟩ := lzero k hk
    have := load_sound hl' atL
    rwa [const_sound hz atL, word_zero] at this
  · intro h60
    rw [g6] at h60
    have h404 : σ (.n 448) ≠ 0 := by
      rw [add_sound ma404 atM, const_sound mc403 atM, word_one, l6]
      intro he
      have h2 : gen ^ 0 = gen ^ lg σ 6 := (pow_zero gen).trans (e_add_eq_zero_iff.mp he).symm
      exact h60 (gen_pow_inj34 (by omega) (by omega) h2).symm
    obtain ⟨haall, -⟩ := holdsList_flat mAggS (List.all_eq_true.mpr aflat) _ _ (hln h404)
    exact call_of_flat haall acall
  · simp only [mainVal_n, lg_mainVal, mainRi, Nat.reduceLT, Nat.reduceAdd, Nat.reduceEqDiff, ↓reduceIte]
    exact ⟨load_sound ql429 atQ, load_sound ql430 atQ⟩
  · exact relToD (by decide +kernel) (by decide +kernel) (hle _ _ _ (call_of_flat hpost qsd))
  · simp only [mainVal_n, lg_mainVal, mainRi, Nat.reduceLT, Nat.reduceAdd, Nat.reduceEqDiff, ↓reduceIte]
    have l1 := load_sound ql434 atQ
    rw [const_sound qc433 atQ, word_one, assertEq_sound qe1 atQ] at l1
    have l2 := load_sound ql438 atQ
    rw [isMul_sound qm437 atQ, const_sound qc435 atQ, const_sound qc436 atQ, word_one, word_gen,
      one_mul, assertEq_sound qe2 atQ] at l2
    refine ⟨l1, ?_⟩
    have l2' : LoadHolds rd (1 * gen ^ 1) 0 (σ (.n 476)) := by rwa [one_mul, pow_one]
    have := (loadHolds_mul_gen_pow rd 1 1 0 _).mp l2'
    simpa using this

end
end LeanVM.SaltedGuest.B1.Main
