/-
  LeanVM.SaltedGuest.Decoder.ProofEq

  The salted decoder's compiled child proof reader is `B1.VerifySub.vsPiOfK` at a frame map keyed
  by the salted functions' indices.
-/

module

public import LeanVM.SaltedGuest.Decoder.Proof
public import LeanVM.SaltedGuest.Decoder.ReadersEq
public import LeanVM.SaltedGuest.Decoder.WhirTablesCheck
public import LeanVM.SaltedGuest.B1.VerifySub.DispatchS

/-!
# The salted child proof reader, compiled, is `vsPiOfK`

* `vsPiOfNK rd σ Vn cl`: the salted `vsPiOfK` with the frames by index (`Vn`), `open_stacked`'s
  dispatch read off the salted table (`osCallsTabK`) and the cursor's length a parameter `cl`;
  **`vsPiOfNK_eq`**: at `cl = cursorLen` it is `vsPiOfK rd σ (byName Vn)` (each level by
  `levelOsNK_eq` from the table's check, `callsOKK`; `open_stacked__L{m}` the salted function
  `310 + m`, `openNames_idx`);
* **`vsPiOfAK_tabs`**: the compiled reader off arrays, at the tables `whirTabsK`, is `vsPiOfNK` (as
  the deployed `vsPiOfA_tabs`: each query's position by `winPosOfW_eq`, the loop's frames stepped,
  `oqItersFromK_gen`).
-/

namespace LeanVM.SaltedGuest.Decoder

open LeanVM.Parameters LeanVM.Guest.Core LeanVM.Guest.B1 LeanVM.Guest.Fast LeanVM.Guest.B1.Whir
open LeanVM.Guest.B1.VerifySub LeanVM.Protocol.Compile LeanVM.Protocol.Verifier LeanVM.Cost.Decoder
open LeanVM.SaltedGuest.B1 LeanVM.SaltedGuest.B1.VerifySub LeanVM.SaltedGuest.B1.Whir

@[expose] public section

set_option maxRecDepth 100000

/-! ## The frames by index -/

/-- The salted query hinted at `b`, its walk the frames `walk` of `Vn` (`oqQueryWK`). -/
def oqQueryNK (s : Oq) (walk : ℕ) (rd : Reader) (bp cap flags : E) (b : ℕ) (emit : Bool) (σ : Val)
    (Vn : NFrames) : QW :=
  (winPosOf rd bp (s.pd + s.cd) s.cd, oqRow b s.R σ,
    oqSibsOf s.pd wkCh (winPosOf rd bp (s.pd + s.cd) s.cd)
      (Vn walk (oqWalkArgsK s b emit bp cap flags σ) []))

/-- A salted loop iteration's queries (`oqIterOfK`). -/
def oqIterNK (s : Oq) (walk : ℕ) (rd : Reader) (σ : Val) (Vn : NFrames) : List QW :=
  if s.base = 1 then
    [oqQueryNK s walk rd (σ (.n 23)) (σ (.n 3)) (σ (.n 4)) 24 true σ Vn,
      oqQueryNK s walk rd (σ (.n (oqE1K s))) (σ (.n 3)) (σ (.n 4)) (oqE1K s + 1) false σ Vn]
  else [oqQueryNK s walk rd (σ (.n 22)) (σ (.n 3)) (σ (.n 4)) 23 true σ Vn]

/-- The salted `opening_queries`' queries (`oqsOfK`), its loop and walk the frames `loop`, `walk`. -/
def oqsOfNK (s : Oq) (odd loop walk N : ℕ) (rd : Reader) (σ : Val) (Vn : NFrames) : List QW :=
  (if odd = 1 then [oqQueryNK s walk rd (σ (.n 25)) (σ (.n 0)) (σ (.n 1)) 26 true σ Vn] else []) ++
    (List.range N).flatMap fun j ↦ oqIterNK s walk rd (Vn loop (gen ^ j :: oqLoopArgsK σ) []) Vn

/-- A level's openings from its salted `level_queries` dispatch `c` (`osLevelOsK lvWK`). -/
def levelOsNK (rd : Reader) (σ : Val) (Vn : NFrames) (c : OsCall) : List Opening :=
  let fr := Vn c.lq (c.args.map fun k ↦ σ (.n k)) (c.rets.map fun k ↦ σ (.n k))
  let a := c.qargsK.map fun k ↦ fr (.n k)
  (oqsOfNK ⟨c.base, c.I, c.pd, c.cd⟩ c.odd c.loop c.walk c.N rd
    (Vn c.fn a [fr (.n (c.pw + 2))]) Vn).map (toOpening rd (a.headD 0) c.cd c.depth)

/-- **The child proof the salted `verify_sub` checks** (`vsPiOfK`), the frames by index, `cl` the
cursor's length. -/
def vsPiOfNK (rd : Reader) (σ : Val) (Vn : NFrames) (cl : E → E → ℕ) : Proof :=
  let m := logGT (σ (.n 1725)) 11
  let j := logGT (σ (.n 126)) 4 * 11 + m
  let fr := Vn (310 + m) (vsOsArgsS σ) (vsOsRetsS σ)
  ⟨wordsAt rd (σ (.n 29)) (cl (σ (.n 29)) (σ (.n 683))) ++
      readN rd (fr (.n 9)) (osWordsTab.getD j 0),
    (osCallsTabK.getD j []).map (levelOsNK rd fr Vn)⟩

/-! ## Equal to the salted reader -/

theorem oqQueryNK_eq (s : Oq) {walk : ℕ} (hw : nameIndex (oqWalkOf s) = walk) (rd : Reader)
    (bp cap flags : E) (b : ℕ) (emit : Bool) (σ : Val) (Vn : NFrames) :
    oqQueryNK s walk rd bp cap flags b emit σ Vn = oqQueryWK s rd bp cap flags b emit σ (byName Vn) := by
  simp only [oqQueryNK, oqQueryWK, byName, hw]

theorem oqIterNK_eq (s : Oq) {walk : ℕ} (hw : nameIndex (oqWalkOf s) = walk) (rd : Reader)
    (σ : Val) (Vn : NFrames) : oqIterNK s walk rd σ Vn = oqIterOfK s rd σ (byName Vn) := by
  simp only [oqIterNK, oqIterOfK, oqQueryNK_eq s hw]

theorem oqsOfNK_eq (s : Oq) {walk loop : ℕ} {loopName : String}
    (hw : nameIndex (oqWalkOf s) = walk) (hl : nameIndex loopName = loop) (odd N : ℕ) (rd : Reader)
    (σ : Val) (Vn : NFrames) :
    oqsOfNK s odd loop walk N rd σ Vn = oqsOfK s odd loopName N rd σ (byName Vn) := by
  simp only [oqsOfNK, oqsOfK, oqQueryNK_eq s hw, oqIterNK_eq s hw]
  conv_rhs => rw [byName, hl]

theorem levelOsNK_eq (rd : Reader) (σ : Val) (Vn : NFrames) {r : OsCall}
    {c : ℕ × OsLv × String × List V × List V} (h : callMatchK r c = true) :
    levelOsNK rd σ Vn r = osLevelOsK lvWK rd σ (byName Vn) c := by
  obtain ⟨lvl, lv, name, args, rets⟩ := c
  simp only [callMatchK, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hb, hI⟩, hpd⟩, hcd⟩, hodd⟩, hN⟩, hdep⟩, hcap⟩, hra⟩, hrr⟩, ha⟩, hr⟩,
    hflq⟩, hlq⟩, hffn⟩, hq⟩, hfl⟩, hl⟩, hfw⟩, hw⟩ := h
  have hs : (⟨r.base, r.I, r.pd, r.cd⟩ : Oq) = lvOq lvl lv := by
    rw [hb, hI, hpd, hcd]
  have hw' : nameIndex (oqWalkOf ⟨r.base, r.I, r.pd, r.cd⟩) = r.walk := by
    rw [hs, ← hw, nameIndex_nameK hfw]
  have hl' : nameIndex (oqLoopOfK (oqNameOf lvl lv)) = r.loop := by
    rw [← hl, nameIndex_nameK hfl]
  have hfn : oqNameOf lvl lv = nameK r.fn := congrArg Prod.fst hq
  have hqa : (lqCallK lvl lv).2.1 = r.qargsK.map V.n := congrArg (fun p ↦ p.2.1) hq
  have hqr : (lqCallK lvl lv).2.2 = [V.n (r.pw + 2)] := congrArg (fun p ↦ p.2.2) hq
  have hargs : r.args.map (fun k ↦ σ (.n k)) = args.map σ := by rw [hra]; exact map_vIdx ha
  have hrets : r.rets.map (fun k ↦ σ (.n k)) = rets.map σ := by rw [hrr]; exact map_vIdx hr
  have hlqi : nameIndex (osQueriesName lvl lv) = r.lq := by rw [← hlq, nameIndex_nameK hflq]
  have hfni : nameIndex (oqNameOf lvl lv) = r.fn := by rw [hfn, nameIndex_nameK hffn]
  dsimp only [levelOsNK, osLevelOsK, lqOpeningsK, lvOpenings, lvWK]
  rw [oqsOfNK_eq _ hw' hl', hs, hargs, hrets, byName, byName, hlqi, hqa, hqr, hfni, hodd, hN, hdep,
    hcap]
  simp only [List.map_map, Function.comp_def, List.map_cons, List.map_nil]

theorem openNames_eqK : openNames = (List.range 11).map fun m ↦ nameK (310 + m) := by
  simp only [openNames, ← natStr_eq]
  decide +kernel

theorem openNames_nameK : ∀ m < 11, openNames.getD m "" = nameK (310 + m) := by
  intro m hm
  rw [openNames_eqK, getD_map_range hm]

/-- `open_stacked__L{m}` is the salted function `310 + m`. -/
theorem openNames_idx {m : ℕ} (hm : m < 11) : nameIndex (openNames.getD m "") = 310 + m := by
  rw [openNames_nameK m hm, nameIndex_nameK]
  simp only [fnIdxK, Bool.and_eq_true, decide_eq_true_eq]
  omega

/-- **The salted reader, the frames by index, is `vsPiOfK`.** -/
theorem vsPiOfNK_eq (rd : Reader) (σ : Val) (Vn : NFrames) :
    vsPiOfNK rd σ Vn cursorLen = vsPiOfK rd σ (byName Vn) := by
  have hm := logG_lt (σ (.n 1725)) (bound := 11) (by norm_num)
  rw [logG_eq_logGT _ (by norm_num)] at hm
  have hr := logG_lt (σ (.n 126)) (bound := 4) (by norm_num)
  rw [logG_eq_logGT _ (by norm_num)] at hr
  unfold vsPiOfNK vsPiOfK piOfWS vsOsWK open_stacked_osWK
  rw [dispatchIdx_eq_logGT, rateOf_sub_one]
  generalize logGT (σ (.n 1725)) 11 = m at hm ⊢
  generalize logGT (σ (.n 126)) 4 = ri at hr ⊢
  have hj : ri * 11 + m < 44 := by omega
  have hjm : (ri * 11 + m) % 11 = m := by omega
  have hjr : (ri * 11 + m) / 11 = ri := by omega
  obtain ⟨hlen, hok⟩ := callsOKK _ hj
  unfold osCallsOf osCfgAt at hlen hok
  rw [hjm, hjr] at hlen hok
  have hw : osWordsTab.getD (ri * 11 + m) 0 = osWordsLen (osCfgR m ri) := by
    rw [osWordsTab_eq, getD_map_range hj, osCfgAt, hjm, hjr]
  dsimp only
  rw [byName, openNames_idx hm, hw, Proof.mk.injEq]
  refine ⟨rfl, ?_⟩
  exact map_zip_eq hlen fun p hp ↦ levelOsNK_eq rd _ Vn (List.all_eq_true.mp hok p hp)

/-! ## Off arrays -/

theorem oqQueryAK_eq (s : Oq) (walk : ℕ) (rd : Reader) (bp cap flags : E) (b : ℕ) (emit : Bool)
    (σ : Val) (Vn : NFrames) :
    oqQueryAK s gLanes walk rd bp cap flags b emit σ Vn = oqQueryNK s walk rd bp cap flags b emit σ Vn := by
  rw [oqQueryAK, oqQueryAtK, oqQueryNK, winPosOfW_eq]
  rfl

theorem oqIterAK_eq (s : Oq) (walk : ℕ) (rd : Reader) (σ : Val) (Vn : NFrames) :
    oqIterAK s gLanes walk rd σ Vn = oqIterNK s walk rd σ Vn := by
  simp only [oqIterAK, oqIterNK, oqQueryAK_eq]

theorem oqItersFromK_gen (s : Oq) (loop walk : ℕ) (rd : Reader) (Vn : NFrames) (la : List E) :
    ∀ n k, oqItersFromK s gLanes loop walk rd Vn la n (gen ^ k) =
      (List.range' k n).flatMap fun j ↦ oqIterNK s walk rd (Vn loop (gen ^ j :: la) []) Vn
  | 0, _ => rfl
  | n + 1, k => by
    rw [oqItersFromK, ← pow_succ, oqItersFromK_gen s loop walk rd Vn la n (k + 1), List.range'_succ,
      List.flatMap_cons, oqIterAK_eq]

theorem oqsOfAK_eq (s : Oq) (odd loop walk N : ℕ) (rd : Reader) (σ : Val) (Vn : NFrames) :
    oqsOfAK s gLanes odd loop walk N rd σ Vn = oqsOfNK s odd loop walk N rd σ Vn := by
  have h := oqItersFromK_gen s loop walk rd Vn (oqLoopArgsSK σ) N 0
  rw [pow_zero] at h
  unfold oqsOfAK oqsOfNK
  rw [h, oqQueryAK_eq, List.range_eq_range']
  rfl

theorem levelOsAK_eq (rd : Reader) (σ : Val) (Vn : NFrames) (c : OsCall) :
    levelOsAK gLanes rd σ Vn c = levelOsNK rd σ Vn c := by
  rw [levelOsAK, levelOsQK, levelOsAtK, levelOsNK, oqsOfAK_eq]

/-- **Off the tables built, the compiled reader is `vsPiOfNK`.** -/
theorem vsPiOfAK_tabs (rd : Reader) (σ : Val) (Vn : NFrames) (cl : E → E → ℕ) :
    vsPiOfAK whirTabsK rd σ Vn cl = vsPiOfNK rd σ Vn cl := by
  have hl : levelOsAK gLanes rd = levelOsNK rd := funext fun σ ↦ funext fun Vn ↦ funext fun c ↦
    levelOsAK_eq rd σ Vn c
  simp only [vsPiOfAK, vsPiOfSK, vsPiOfMK, vsPiOfAtK, vsPiOfNK, whirTabsK, logGTWith_gLanes,
    getD_toArray, hl, ← wordsAt_eq_wordsFrom, readN_eq_wordsAt]
  rfl

/-- **The compiled child proof reader is `vsPiOfK`**, at the tables built and the cursor's length
`cursorLen`. -/
theorem proofAtFrameK_eq (rd : Reader) (Vn : NFrames) :
    proofAtFrameK whirTabsK rd Vn cursorLen =
      fun args ↦ vsPiOfK rd (byName Vn "verify_sub" args []) (byName Vn) := by
  funext args
  rw [proofAtFrameK, vsPiOfAK_tabs, vsPiOfNK_eq, byName, idx_verify_sub]

end

end LeanVM.SaltedGuest.Decoder
