/-
  LeanVM.SaltedGuest.B1.Whir.QueriesBlkK

  The template's queries block of a level over the salted `level_queries`: the openings pass the
  verifier's check at the keyed hash.
-/

module

public import LeanVM.SaltedGuest.B1.Whir.LqK
public import LeanVM.SaltedGuest.B1.Whir.QueriesOpenWK
public import LeanVM.SaltedGuest.EndKnow

/-!
# A level's salted queries block

`lqCallK`: the `opening_queries` call in the salted `level_queries`' body. `osQueries_soundK`: the
deployed `osQueries_sound` (`open_stacked`'s template is unchanged) over the salted
`level_queries` (`level_queries_frameK`), with the seed `S` of memory words `2` and `3`: the cap
checked under the key (`MeaningCapK`), the queries' openings passing `openOne` at `keyedHash S`
(`queries_open_wK`).
-/

namespace LeanVM.SaltedGuest.B1.Whir

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest LeanVM.Guest.B1
open LeanVM.Guest.Value LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile
open LeanVM.Protocol.Verifier LeanVM.Guest.B1.Whir LeanVM.SaltedGuest.B1 Recursion.Salted

@[expose] public section

variable {rd : Reader} {σ : Val}

/-- The `opening_queries` call in the salted `level_queries`' body (`lqBodyK`): its name, arguments
and returns. -/
def lqCallK (lvl : ℕ) (lv : OsLv) : String × List V × List V :=
  let pw := osPowSteps 0 (osPowDigits lv.queries) 0 48
  let k := 48 + osPowLen lv.queries
  (oqNameOf lvl lv, [.n 4, .n 45, .n 0, .n pw.2, .n 1, .n 2, .n k], [.n (k + 1)])

/-- **A level's salted queries block**, its openings named (the deployed `osQueries_sound` with
the salted `level_queries`, the key of the seed `S` in memory words `2` and `3`): those the queries' witness `W` gives at the
`opening_queries` call in the frame `V` gives the `level_queries` call the dispatch on the rate
makes (`lvOpenings` at `lqCall`). -/
theorem osQueries_soundK {C : CallRel} (hle : CallRel.Le C (SaltedGuest.coreProgram.Rel rd)) {V : SaltedGuest.End.FrameMap}
    (hU : SaltedGuest.End.UnfoldsV rd C V) {c : OsCfg} {lvl : ℕ} {lv : OsLv} {lam : ℕ} {s : OsSt}
    (hok : AllOk C rd σ (osQueries c lvl lv lam s).1) (hmats : MatsOk σ s.mats)
    (hrate : LvRate σ c lvl lv)
    (hfn : FnIsK (osQueriesName lvl lv) (osParams 3)
      (lqBodyK lv.queries (if lvl = 0 then 1 else 0) lv.interleave lv.leafCells lv.depth lv.capDepth))
    (hdig : digitsVal (osPowDigits lv.queries) 1 = lv.queries)
    (hs : RowShape lvl lv) (hcd : 2 ≤ lv.capDepth) (hcd8 : lv.capDepth ≤ 8)
    (hcdd : lv.capDepth ≤ lv.depth)
    (hRW : ∀ args rets, SaltedGuest.coreProgram.Rel rd ("opening_row_weights__L" ++ natStr lv.folds ++ "_L" ++
      natStr (if lvl = 0 then 1 else 0)) args rets →
        MeaningOpeningRowWeights lv.folds (if lvl = 0 then 1 else 0) rd args rets)
    (hCap : ∀ args rets, SaltedGuest.coreProgram.Rel rd ("verify_merkle_cap__L" ++ natStr lv.capDepth)
      args rets → MeaningCapK (2 ^ lv.capDepth) rd args rets)
    (W : List E → List E → List QW) (hQW : LvQWK rd C lvl lv W)
    {S : Digest} (hS2 : LoadHolds rd 1 2 (digestHalves S).1)
    (hS3 : LoadHolds rd 1 3 (digestHalves S).2)
    {lf : List E} (hlf : lf.length = lv.folds)
    (hfch : ∀ j < lv.folds, LoadHolds rd (σ (.n osFch)) (lv.foldsOff + j) (lf.getD j 0))
    {root : Digest} (hr0 : LoadHolds rd (σ (.n osRoots)) (2 * lvl) (digestHalves root).1)
    (hr1 : LoadHolds rd (σ (.n osRoots)) (2 * lvl + 1) (digestHalves root).2)
    (qs : List ℕ) (hqsl : qs.length = lv.queries) (hqlt : ∀ k < lv.queries, qs.getD k 0 < 2 ^ lv.depth)
    (hpos : ∀ k < lv.queries, ∃ bp, LoadHolds rd (σ (.n osQbp)) (lv.posOff + k) bp ∧
      FrameRun rd bp (qwN lv.depth lv.capDepth) fun i ↦ gen ^ qwVal lv.depth lv.capDepth (qs.getD k 0) i)
    (hbo : lv.foldsOff < u128Bound ∧ lv.posOff < u128Bound ∧
      lv.queries / (1 + if lvl = 0 then 1 else 0) < ordG ∧
      lv.queries / (1 + if lvl = 0 then 1 else 0) < u128Bound) :
    let os := lvOpenings rd (V (osQueriesName lvl lv) ((osQueriesDisp c lvl lv lam s).2.1.map σ)
      ((osQueriesDisp c lvl lv lam s).2.2.map σ)) lv W (lqCallK lvl lv)
    ∃ (ic0 ic2 : E), os.length = lv.queries ∧
      (∀ k (hk : k < qs.length) (ho : k < os.length),
        Id.run (Compile.openOneWithHash (m := Id) (keyedHash S) root lv.depth
          (if lvl = 0 then lv.interleave else 3 * lv.interleave) qs[k] os[k]) = true) ∧
      σ (.n (osQueries c lvl lv lam s).2.2.1) =
        enforcedSum ((os.map (·.leaf)).map (specRow lvl)) lf (powers (σ (.n lam)) lv.queries) ∧
      σ (.n (osQueries c lvl lv lam s).2.2.2.1) = σ (.n lam) ^ lv.queries ∧
      ReadsAt rd (s.cur σ) [ic0, ic2] ∧ σ (.n (osQueries c lvl lv lam s).2.2.2.2.1) = ic0 ∧
      σ (.n (osQueries c lvl lv lam s).2.2.2.2.2.2) = ic2 ∧
      σ (.n (osQueries c lvl lv lam s).2.2.2.2.2.1) =
        σ (.n (osQueries c lvl lv lam s).2.2.1) + ic2 ∧
      MatsOk σ (osQueriesMats c lv s) ∧ os.map Opening.leafIndex = qs := by
  intro os
  obtain ⟨hb1, hb4, hb5, hb6⟩ := hbo
  set k := s.k
  set P := c.plan
  set m0 := s.mats
  set fp := osMatP P m0 osFch lv.foldsOff (k + 2)
  set m1 := osMatsAfter P m0 osFch lv.foldsOff (k + 2)
  set bp := osMatP P m1 osQbp lv.posOff fp.2.2
  set r := bp.2.2
  have hst : (osQueries c lvl lv lam s).1 = osHeap c.maxIl k ++ fp.1 ++
      [.call ("opening_row_weights__L" ++ natStr lv.folds ++ "_L" ++
        natStr (if lvl = 0 then 1 else 0)) [.n fp.2.1, .n (k + 1)] []] ++
      bp.1 ++
      [.dispatch (.n osRate) ((c.lvAt lvl).map (osQueriesName lvl)) [.n lam, .n bp.2.1, .n (k + 1)]
          (osRun r 4),
        .atom (.load (.n r) (.n osRoots) (2 * lvl)), .atom (.load (.n (r + 1)) (.n osRoots) (2 * lvl + 1)),
        .atom (.load (.n (r + 4)) (.n s.cb) s.co), .atom (.load (.n (r + 5)) (.n s.cb) (s.co + 1)),
        .atom (.add (.n (r + 6)) (.n (r + 2)) (.n (r + 5)))] := rfl
  have hr : (osQueries c lvl lv lam s).2 = (r + 7, r + 2, r + 3, r + 4, r + 6, r + 5) := rfl
  have hdisp : osQueriesDisp c lvl lv lam s =
      (osQueriesName lvl lv, [.n lam, .n bp.2.1, .n (k + 1)], osRun r 4) := rfl
  rw [hst] at hok
  rw [hr]
  simp only [os, hdisp] at *
  rw [allOk_append, allOk_cons] at hok
  obtain ⟨hpre, hD, hok⟩ := hok
  simp only [allOk_append, allOk_cons, allOk_nil, and_true, Whir.StmtOk, Atom.Holds, List.map_cons,
    List.map_nil] at hpre hok
  obtain ⟨⟨⟨-, hfp⟩, hrw⟩, hbp⟩ := hpre
  obtain ⟨hs0, hs1, hi0, hi2, hi1⟩ := hok
  have k1 := osMatsAfter_ok hmats hb1 hfp
  have efp := osMatP_val hmats hb1 hfp
  have ebp := osMatP_val k1 hb4 hbp
  have hmq : MatsOk σ (osQueriesMats c lv s) := osMatsAfter_ok k1 hb4 hbp
  -- the dispatch into `level_queries`
  have hcall := dispatch_rate hrate (osQueriesName lvl) hD
  simp only [osRun, List.range_succ, List.range_zero, List.map_cons, List.map_nil,
    List.nil_append, List.cons_append, Nat.add_zero] at hcall ⊢
  obtain ⟨fn, hf, hpar, hbody⟩ := hU _ _ _ hcall
  obtain ⟨fn', hf', hps', hb'⟩ := hfn
  rw [hf] at hf'
  cases hf'
  rw [hps'] at hpar
  rw [hb'] at hbody
  set σ' := V (osQueriesName lvl lv) [σ (.n lam), σ (.n bp.2.1), σ (.n (k + 1))]
    [σ (.n r), σ (.n (r + 1)), σ (.n (r + 2)), σ (.n (r + 3))]
  set q := lv.queries
  set base := if lvl = 0 then 1 else 0
  set N0 := q / (1 + base)
  obtain ⟨hargs, hrets, hcapc, hoq, hpw, hkv, hkey⟩ := level_queries_frameK hpar hbody hdig
    (by rw [iters_eq]; exact hb6) hS2 hS3
  simp only [List.cons.injEq, and_true] at hargs hrets
  obtain ⟨a0, a1, a2⟩ := hargs
  obtain ⟨r0, r1, r2, r3⟩ := hrets
  rw [iters_eq] at hkv
  have er0 := loadHolds_unique hs0 hr0
  have er1 := loadHolds_unique hs1 hr1
  have hroot : (σ' (.n 46), σ' (.n 47)) = digestHalves root := by rw [← r0, ← r1, er0, er1]
  obtain ⟨-, rs, hrsl, hrs, hlo, hhi⟩ := hRW _ _ (hle _ _ _ hrw)
  have hrsf : rs = lf := by
    apply List.ext_getElem (by rw [hrsl, hlf])
    intro j h1 h2
    have a := hrs j h1
    rw [efp, loadHolds_mul_gen_pow] at a
    have b := hfch j (by rw [← hrsl]; exact h1)
    rw [List.getD_eq_getElem _ _ h2] at b
    exact loadHolds_unique a b
  subst hrsf
  have hbits : ∀ k' < q, ∃ bpv, LoadHolds rd (σ' (.n 1)) k' bpv ∧
      FrameRun rd bpv (qwN lv.depth lv.capDepth)
        fun i ↦ gen ^ qwVal lv.depth lv.capDepth (qs.getD k' 0) i := by
    intro k' hk'
    obtain ⟨bpv, h1, h2⟩ := hpos k' hk'
    exact ⟨bpv, by rw [← a1, ebp, loadHolds_mul_gen_pow]; exact h1, h2⟩
  have hqb : ∀ N, gen ^ N0 = gen ^ N → N < ordG → QueryWinsOk rd (σ' (.n 1))
      (oqCount (q % 2 * base) base N) lv.depth lv.capDepth := by
    intro N hN hNo k' hk' bpv hbpv
    have hNN : N = N0 := gen_pow_inj hNo hb5 hN.symm
    rw [hNN, oqCount_q] at hk'
    obtain ⟨bpv', h1, h2⟩ := hbits k' hk'
    rw [loadHolds_unique hbpv h1]
    exact ⟨_, hqlt k' hk', h2⟩
  have hm := hQW _ _ hoq hkv hb5 hcdd (fun N hN hNo ↦ hqb N (hkv.symm.trans hN) hNo) S hkey
  have hlc : lqCallK lvl lv = (oqNameOf lvl lv, [.n 4, .n 45, .n 0,
      .n (osPowSteps 0 (osPowDigits q) 0 48).2, .n 1, .n 2, .n (48 + osPowLen q)],
      [.n (48 + osPowLen q + 1)]) := rfl
  obtain ⟨hol, hop, hsum, hidx⟩ := queries_open_wK (q := q) (N0 := N0) (cap0 := σ' (.n 4))
    rfl hm (hCap _ _ (hle _ _ _ hcapc)) hkey hroot hcd hcd8 hcdd hkv hb5 (oqCount_q _ _)
    (by split_ifs <;> simp; omega) (by by_cases h : lvl = 0 <;> simp [h]) qs hqsl hqlt hbits
    hpw
    (width := if lvl = 0 then lv.interleave else 3 * lv.interleave) (width_eq lvl lv.interleave)
    (specRow lvl) rs (fun row w hrow hw ↦ rowDot_spec hs hrsl hlo hhi row w
      (hrow.trans (width_eq lvl lv.interleave).symm) (by rw [a2]; exact hw))
  refine ⟨σ (.n (r + 4)), σ (.n (r + 5)), ?_, ?_, ?_, ?_, ?_, rfl, rfl, hi1, hmq, ?_⟩
  · simp only [lvOpenings, hlc]; exact hol
  · simp only [lvOpenings, hlc]; exact hop
  · simp only [lvOpenings, hlc]
    rw [show powers (σ (.n lam)) q = powers (σ' (.n 0)) q by rw [a0]]
    exact r2.trans hsum
  · rw [r3, ← a0]
  · intro i hi
    rcases i with _ | _ | i
    · exact load_cur (by simpa using hi0)
    · exact load_cur hi2
    · simp at hi
  · simp only [lvOpenings, hlc]; exact hidx

end
end LeanVM.SaltedGuest.B1.Whir
