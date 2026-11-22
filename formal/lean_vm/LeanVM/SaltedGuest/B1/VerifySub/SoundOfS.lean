/-
  LeanVM.SaltedGuest.B1.VerifySub.SoundOfS

  **The salted `verify_sub` is sound**, given its terminal's obligation: a run of its body gives a
  child proof, read off its valuation, the memory and the frame map, that the deferring verifier
  with a second public digest accepts at the keyed hash.
-/

module

public import LeanVM.SaltedGuest.B1.VerifySub.AssembleLib
public import LeanVM.SaltedGuest.B1.Main.SoundVK
public import LeanVM.Guest.B1.Tables.HoldsC

/-!
# The salted `verify_sub` is sound

`verify_sub_sound_wK`: given the salted `check_opening_terminal`'s obligation on memory images of
at most `2^32` words (`check_opening_terminal_SpecK`), `B1.Main.SubSoundWK vsPiOfK`: the deployed
`verify_sub_sound_w_of` for the salted body: the front (`vs_frontS`), the seed's claims
(`vsSeedClaimsS_holds`), the Keccak reduction (`vsCalls2S_holds`, `verify_keccak` an unchanged
function), the back over the `170` claims (`vs_backS`: `verify_tables`' claims and the second
digest's, `claimAt_readsS`), the stack (`vs_stackS`), the lanes (`vs_lanesS`), the ring switch's
target (unchanged), the opening at the keyed hash of the seed in memory words `2` and `3`
(`vs_dispatchS`, `osSoundWK_of`), the terminal (the hypothesis), the tables' segment with the
second digest's claims (`runsTo_tablesSeg₂`), the stream (`vs_streamS`) and the acceptance
(`deferred_accepts₂`).
-/

namespace LeanVM.SaltedGuest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.VerifySub LeanVM.SaltedGuest.B1 Recursion.SecondDigest
open LeanVM.Protocol.EndToEnd.Front Recursion.Salted

@[expose] public section

/-- The announced words are the memory's log, the rows and the rate, as integer words. -/
theorem vsWordsS_eq {bytecode : List K} {C : CallRel} {rd : Reader} {σ : Val}
    (F : VsFrontS bytecode C rd σ) :
    vsWordsS σ = eOfNat F.logMem :: F.rowsN.map eOfNat ++ [eOfNat F.lir] := by
  have hr : [σ (.n 41), σ (.n 51), σ (.n 61), σ (.n 84), σ (.n 94), σ (.n 104)] =
      F.rowsN.map eOfNat := by
    refine readsAt_ext (by simp [F.hrowsL]) (fun k hk ↦ ?_) F.hrows
    simp only [List.length_cons, List.length_nil] at hk
    have := F.hrw k hk
    interval_cases k <;> exact this
  rw [vsWordsS, ← hr, ← F.e29, ← F.e112]
  rfl

/-- **The salted `verify_sub` is sound**, given its terminal's obligation. -/
theorem verify_sub_sound_wK
    (hterm : ∀ {κ : ℕ}, κ ≤ 32 → ∀ (L : MemoryImage κ), check_opening_terminal_SpecK L.read) :
    B1.Main.SubSoundWK vsPiOfK := by
  intro κ L hκ C V hU hLe σ rets hb hpre hsw
  have hbl : SaltedGuest.End.bytecode.length = 2 ^ 23 := SaltedGuest.End.bytecode_length
  have hexp : ExpTables L.read (σ (.n 4)) := by
    simpa [VerifySubPre, core18_paramsS] using hpre
  have hsw' : LoadHolds L.read 1 2 (σ (.n 2)) ∧ LoadHolds L.read 1 3 (σ (.n 3)) := by
    simpa [B1.Main.SeedAtWords, core18_paramsS] using hsw
  replace hb := (congrArg (fun b ↦ Stmt.HoldsList C L.read σ b False (fun rs ↦ rs = rets))
    core18_bodyS).mp hb
  rw [vsTS_split, holdsList_append] at hb
  obtain ⟨hF0, hR⟩ := (holdsList_noRet vsFrontPartS vsFrontPartS_noRet _ _).1 hb
  have hz := hF0
  simp only [vsFrontPartS, holdsList_append] at hz
  obtain ⟨-, -, -, -, h12, h13, h14, h15, -, -⟩ := vsHeadT_holdsS hz
  rw [holdsList_append] at hR
  obtain ⟨hSC, hR⟩ := (holdsList_noRet vsSeedClaimsS vsSeedClaimsS_noRet _ _).1 hR
  rw [holdsList_append] at hR
  obtain ⟨hC2, hR⟩ := (holdsList_noRet vsCalls2S vsCalls2S_noRet _ _).1 hR
  -- the memory holds at least `64` words (the coefficients' table)
  have hκ6 : 6 ≤ κ := by
    have hR' := hR
    rw [holdsList_append, holdsList_append] at hR'
    obtain ⟨-, hmR, hR'⟩ := vsMapsS_holds h12 h13 h14 h15 hR'
    obtain ⟨hct, -⟩ := vsCtabS_holds (chs := σ (.n 685) :: vsChsS σ) rfl hmR hR'
    have := mem_size hκ L (n := 64) (by norm_num) (fun j hj ↦
      ⟨_, hct j (by simp [ringCoefficients, kBits]; omega)⟩)
    by_contra hlt
    have : 2 ^ κ ≤ 2 ^ 5 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hgkr : Tables.verify_bus_gkr_SpecC L.read C :=
    fun args rets hne hc ↦ Tables.verify_bus_gkr_holdsC hκ L
      (onlyS_le (f := "verify_bus_gkr") (by decide +kernel) (by decide +kernel)) args rets hne
      ⟨rfl, hLe _ _ _ hc⟩
  have htab : Tables.verify_tables_SpecC SaltedGuest.End.bytecode L.read C :=
    fun pi logMem alphas point values args rets hpre hc ↦ Tables.verify_tables_holdsC hκ L _
      hbl (onlyS_le (f := "verify_tables") (by decide +kernel) (by decide +kernel))
      pi logMem alphas point values args rets hpre ⟨rfl, hLe _ _ _ hc⟩
  obtain ⟨⟨F⟩, -⟩ := vs_frontS hκ hκ6 L hLe SaltedGuest.End.bytecode hgkr htab hexp hF0
  obtain ⟨-, -, l167, l168, l169, -⟩ := vsSeedClaimsS_holds hSC
  obtain ⟨l673, e677, hkc, hcopy, -⟩ := vsCalls2S_holds hC2
  have hctx := F.hctx
  simp only [Tables.TCtx] at hctx
  obtain ⟨chis0, hbp, hgmu, -, -, -, hcl, hcol, -⟩ := hctx
  -- the batched claims: `verify_tables`' and the second digest's
  set layout := Tables.layoutOf SaltedGuest.End.bytecode F.logMem F.rowsN with hlayout
  set second := secondClaims layout F.seed (σ (.n 654)) with hsec
  have e2 : (digestHalves F.seed).1 = σ (.n 2) := by rw [← F.hseed]
  have e3 : (digestHalves F.seed).2 = σ (.n 3) := by rw [← F.hseed]
  have l167' : LoadHolds L.read (σ (.n 6)) 167 (pubLimb F.seed (σ (.n 654)) 0) := by
    simp only [pubLimb, e2, e3]; exact l167
  have l168' : LoadHolds L.read (σ (.n 6)) 168 (pubLimb F.seed (σ (.n 654)) 1) := by
    simp only [pubLimb, e2, e3]; exact l168
  have hcolS : (F.claims ++ second).map (·.column) = claimColumnsS := by
    rw [List.map_append, hcol, hsec, secondClaims_columns]; rfl
  have hval := claimAt_readsS (layout := layout) hcl F.hpool F.hcew F.hpoolPI l167' l168' l169
  obtain ⟨hmaps, hchR, hct, hrstC, hlam, -, h1720, hcp, hl2, e1725, r1, hdisp, hterm', hd1, hd2,
    hd3, hkret⟩ := vs_backS h12 h13 h14 h15 hcolS hval hR
  refine ⟨hkret.symm, ?_⟩
  -- the stack
  obtain ⟨hμ19, hμ30, hsize, hP, hKB⟩ :=
    vs_stackS hκ hκ6 L hLe (Tables.certify_placement_holds hκ L) hbl F hexp hcp hl2 e1725 r1
  have hμ30' : layout.stackLog ≤ 30 := hμ30
  have hμ19' : Guest.B1.Whir.minOpenLog ≤ layout.stackLog := hμ19
  -- the output lanes
  obtain ⟨chis, hchiR, hτc, hlcol, hlpt, hout, hl25⟩ := vs_lanesS hbl F
  have hτ9 := tau_ge F.hrowsL
  have hsL := tableHeights_length _ F.hrowsL
  have hτ28 : vsTau F.rowsN ≤ 28 := by
    have := tau_le_of_kappasBelow hsL hKB
    show (Tables.tableHeightsOf F.rowsN).getD 5 0 ≤ 28
    omega
  have htg : σ (.n 673) = gen ^ vsTau F.rowsN := by
    refine loadHolds_unique l673 ?_
    have h6 := F.hdims 6 (by simp [hsL])
    have e6 : (gen ^ F.logMem :: (Tables.tableHeightsOf F.rowsN).map (gen ^ ·))[6]'(by simp [hsL]) =
        gen ^ vsTau F.rowsN := by
      simp only [List.getElem_cons_succ, List.getElem_map, vsTau]
      rw [List.getD_eq_getElem _ _ (by rw [hsL]; omega)]
    rw [e6] at h6
    exact h6
  -- `verify_keccak`
  have hk := verify_keccak_holds L.read _ _
    (toDRel (by decide +kernel) (by decide +kernel) (hLe _ _ _ hkc))
  simp only [MeaningVerifyKeccak] at hk
  obtain ⟨xsK, op, point, slices, capK, word, m0, hxsK, hrunK, hop, hpoint, hsl, hopL, hpointL,
    hslL, hretK⟩ :=
    hk (vsTau F.rowsN) chis ((lanesOf F.claims).map (·.value)) hτ9 hτ28 htg hτc hchiR
      (by simp [hl25]) (by rw [e677]; exact hout)
  have hretK' : [σ (.n 678), σ (.n 679), σ (.n 680), σ (.n 681), σ (.n 682)] ++
      [σ (.n 683), σ (.n 684), σ (.n 685)] = capK ++ [σ (.n 651) * gen ^ xsK.length, word, m0] :=
    hretK
  obtain ⟨hcapK, hK3⟩ := List.append_inj' hretK' rfl
  simp only [List.cons.injEq, and_true] at hK3
  obtain ⟨e683, e684, e685⟩ := hK3
  -- the ring switch's target
  have hrt := ring_switch_target_holds L.read _ _
    (toDRel (by decide +kernel) (by decide +kernel) (hLe _ _ _ hrstC))
  simp only [MeaningRingTarget] at hrt
  obtain ⟨s', ch', hs'L, hch'L, hs'R, hch'R, hr1118⟩ := hrt
  have ech' : ch' = σ (.n 685) :: vsChsS σ := readsAt_ext (by rw [hch'L]; rfl) hch'R hchR
  simp only [List.cons.injEq, and_true] at hr1118
  -- the opening at the keyed hash
  have h126 : σ (.n 126) = Guest.B1.Whir.rateSel F.lir := by rw [F.e124, gen_pow_eq_ofK]; rfl
  obtain ⟨root, hroot⟩ := digest_of_canonical F.hc537 F.hc547
  have hS2 : LoadHolds L.read 1 2 (digestHalves F.seed).1 := by rw [e2]; exact hsw'.1
  have hS3 : LoadHolds L.read 1 3 (digestHalves F.seed).2 := by rw [e3]; exact hsw'.2
  obtain ⟨w, s10, roots', hxsW, hrunW, hwL, pt, pt1, hretsW, hptR, hpt1R⟩ :=
    vs_dispatchS (osSoundWK_of hκ hU hLe hS2 hS3) hμ19 hμ30 F.hl1 F.hl4 hsize h126 hdisp hroot
  simp only [vsOsRetsS, List.cons.injEq, and_true] at hretsW
  obtain ⟨e1730, e1731, e1732, e1733, e1734⟩ := hretsW
  -- the bus point
  have hbpL : F.bus.point.length ≤ 40 := by
    have hle := mem_size_le hκ L hbp
    have := gen_pow_inj (by omega) (lt_trans F.hdep (by norm_num)) (hgmu.symm.trans F.e522)
    have := F.hdep
    omega
  -- the terminal
  obtain ⟨-, hTacc⟩ := hterm hκ L _ _ (hLe _ _ _ hterm')
  have hacc := hTacc layout F.bus F.claims ⟨qkeccak, op, word⟩ (σ (.n 1138)) point
    (ringCoefficients (σ (.n 685) :: vsChsS σ)) w.point F.seed (by
      simp only [TermPre]
      refine ⟨termCtx_of_tctx F.hctx, hP, hKB, layoutOf_placements hbl _ _,
        layoutOf_stackLog hbl _ _, by omega, le_trans (by norm_num) F.hlm1, F.hm32, hbpL, hsL,
        F.hh33, F.e130, htg, F.hkb, gTabs_of_exp hexp, trivial, trivial, hopL, hop, hpointL,
        hpoint, by simp [ringCoefficients, kBits], hct, hwL, ?_, ?_⟩
      · rw [padPoint, hwL, e1731]; exact hptR
      · rw [padPoint, hwL, List.map_append, List.map_replicate, add_zero, e1732]; exact hpt1R)
    F.hlm1
  simp only [List.getD_cons_succ, List.getD_cons_zero] at hacc
  -- the terminal's check, as `whirOpen`'s acceptance
  have hAcc : w.Accepts fun x ↦ dot (powers (σ (.n 1138))
      (stackClaims layout (F.claims ++ second) [⟨qkeccak, op, word⟩] point slices
        (m0 :: vsChsS σ)).length)
      ((stackClaims layout (F.claims ++ second) [⟨qkeccak, op, word⟩] point slices
        (m0 :: vsChsS σ)).map fun c ↦ c.1 x) := by
    unfold Guest.B1.Whir.WhirEnd.Accepts
    beta_reduce
    rw [stackClaims_weight, ← e685, ← e1733, ← e1734, ← e1730]
    exact hacc
  -- the batched target
  have es' : s' = slices := readsAt_ext (by rw [hs'L, hslL]; rfl) hs'R hsl
  have htarget : σ (.n 1720) = dot (powers (σ (.n 1138))
      (stackClaims layout (F.claims ++ second) [⟨qkeccak, op, word⟩] point slices
        (m0 :: vsChsS σ)).length)
      ((stackClaims layout (F.claims ++ second) [⟨qkeccak, op, word⟩] point slices
        (m0 :: vsChsS σ)).map (·.2)) := by
    rw [stackClaims_values, stackClaims_length, h1720, hr1118, es', ech', ← e685, ← e684]
  -- the runs
  obtain ⟨level, rest, hcfg⟩ := cfg_cons hμ19 hμ30 F.hl1 F.hl4
  have h1 := readSizes_runsTo hbl (le_trans (by norm_num) F.hlm1) F.hm30 F.hrowsL F.hh31 F.hl1
    F.hl4 hμ30 (⟨[σ (.n 24), σ (.n 25), σ (.n 26), σ (.n 27), σ (.n 28)], []⟩ : Fs)
  rw [← vsWordsS_eq F, F.hab8] at h1
  have hroot' : digestFromHalves (σ (.n 334), σ (.n 344)) = some root := by
    rw [hroot]; exact digestOfScalars_digestScalars root
  have h3 : (((⟨[σ (.n 79), σ (.n 80), σ (.n 81), σ (.n 82), σ (.n 83)],
      [(σ (.n 84), dsObserve), (σ (.n 94), dsObserve), (σ (.n 104), dsObserve),
        (σ (.n 114), dsObserve)]⟩ : Fs).absorb (σ (.n 334)) dsObserve).absorb (σ (.n 344))
        dsObserve).squeezeN busBits =
      (vsAlphaVals σ, ⟨[σ (.n 425), σ (.n 426), σ (.n 427), σ (.n 428), σ (.n 429)], []⟩) := by
    rw [F.habR]; exact F.halpha
  have h5 := F.hrunG
  rw [F.capG_eq, show log2Ceil (pushTotal F.logMem (Tables.tableHeightsOf F.rowsN)) =
    (busLayout [0, F.logMem, layout.logBytecode] layout.push).depth from
    (pushDepth_eq hbl F.logMem F.rowsN F.hrowsL).symm] at h5
  have h6 := F.hrunT (claimedBytecodeValue (vsFixedS σ F.r.2.1)) (by
    rw [logBytecode_eq hbl]; exact bytecodeAt_claimed SaltedGuest.End.bytecode _ _)
  rw [← F.hcapT] at h6
  have h6' := runsTo_tablesSeg₂ (memFour hbl F.hrowsL F.hlm1) (second := F.seed) h6
  rw [pubChallengeOf_tctx F.hctx] at h6'
  have hne : lanesOf F.claims ≠ [] := by intro h; rw [h] at hl25; simp at hl25
  have hhd : ((lanesOf F.claims).headD default).point = chis.take (vsTau F.rowsN) := by
    obtain ⟨c, cs, hcs⟩ := List.exists_cons_of_ne_nil hne
    have hc : c ∈ lanesOf F.claims := by rw [hcs]; exact List.mem_cons_self
    rw [hcs]
    exact hlpt c hc
  have h7 : (lanesOf (F.claims ++ second)).map (·.column) = keccakOutputColumns ∧
      ∀ c ∈ lanesOf (F.claims ++ second),
        c.point = ((lanesOf (F.claims ++ second)).headD default).point := by
    rw [hsec, lanesOf_append_second]
    exact ⟨hlcol, fun c hc ↦ by rw [hlpt c hc, hhd]⟩
  have h8 : RunsTo (keccakSeg (layout.tableLogHeights.getD opKeccak 0)
      ((lanesOf (F.claims ++ second)).headD default).point
      ((lanesOf (F.claims ++ second)).map (·.value)))
      ⟨[σ (.n 646), σ (.n 647), σ (.n 648), σ (.n 649), σ (.n 650)], []⟩ xsK
      (([⟨qkeccak, op, word⟩], point, slices), m0) ⟨capK, []⟩ := by
    rw [hsec, lanesOf_append_second, hhd]; exact hrunK
  have hcopy' : [σ (.n 678), σ (.n 679), σ (.n 680), σ (.n 681), σ (.n 682)] =
      [σ (.n 686), σ (.n 687), σ (.n 688), σ (.n 689), σ (.n 690)] := by
    rw [hcopy 0 (by omega), hcopy 1 (by omega), hcopy 2 (by omega), hcopy 3 (by omega),
      hcopy 4 (by omega)]
  have h9 : (⟨capK, []⟩ : Fs).squeezeN 5 =
      (vsChsS σ, ⟨[σ (.n 781), σ (.n 782), σ (.n 783), σ (.n 784), σ (.n 785)], []⟩) := by
    rw [← hcapK, hcopy']; exact hmaps
  have h11 : RunsWithH (keyedHash F.seed) (Guest.B1.Whir.whirOpen layout.stackLog F.lir
      (dot (powers (σ (.n 1138)) (stackClaims layout (F.claims ++ second) [⟨qkeccak, op, word⟩]
        point slices (m0 :: vsChsS σ)).length)
        ((stackClaims layout (F.claims ++ second) [⟨qkeccak, op, word⟩] point slices
          (m0 :: vsChsS σ)).map (·.2))))
      ⟨[σ (.n 1127), σ (.n 1128), σ (.n 1129), σ (.n 1130), σ (.n 1131)], []⟩
      (vsOsWK L.read V (layout.stackLog - Guest.B1.Whir.minOpenLog) F.lir (vsOsArgsS σ)
        (vsOsRetsS σ)).1
      (vsOsWK L.read V (layout.stackLog - Guest.B1.Whir.minOpenLog) F.lir (vsOsArgsS σ)
        (vsOsRetsS σ)).2
      [(root, Guest.B1.Whir.stackShape layout.stackLog F.lir)] w s10 roots' := by
    rw [← htarget]; exact hrunW
  have hacc' := deferred_accepts₂ (c := vsFixedS σ F.r.2.1)
    (s0 := ⟨[σ (.n 24), σ (.n 25), σ (.n 26), σ (.n 27), σ (.n 28)], []⟩) ⟨F.hcap0.symm, rfl⟩
    h1 hcfg hroot' h3 F.hbeta h5 h6' h7 h8 h9 hlam h11 hAcc
  -- the decoded proof
  have hidx : dispatchIdx (σ (.n 1725)) = layout.stackLog - Guest.B1.Whir.minOpenLog :=
    dispatchIdx_eq (by unfold Guest.B1.Whir.minOpenLog; omega) (by rw [hsize, gen_pow_eq_ofK])
  have hrate : rateOf (σ (.n 126)) = F.lir := by rw [h126]; exact rateOf_eq F.hl1 F.hl4
  have hπ : vsPiOfK L.read σ V = ⟨vsWordsS σ ++ [σ (.n 334), σ (.n 344)] ++ F.xsG ++ F.xsT ++
      xsK ++ (vsOsWK L.read V (layout.stackLog - Guest.B1.Whir.minOpenLog) F.lir (vsOsArgsS σ)
        (vsOsRetsS σ)).1,
      (vsOsWK L.read V (layout.stackLog - Guest.B1.Whir.minOpenLog) F.lir (vsOsArgsS σ)
        (vsOsRetsS σ)).2⟩ := by
    simp only [vsPiOfK, piOfWS, hidx, hrate]
    rw [vs_streamS hκ L F hxsK e683]
  -- the statement
  refine ⟨σ (.n 0), σ (.n 1), σ (.n 2), σ (.n 3), σ (.n 4), σ (.n 5), rfl, F.seed, F.pi,
    vsFixedS σ F.r.2.1, F.hseed, F.hpi, ?_, ?_, ?_⟩
  · have := F.hptL
    have := depth_ge (logMem := F.logMem) hsL
    show (F.r.2.1.take 19 ++ vsAlphaVals σ).length = 23
    rw [List.length_append, List.length_take, min_eq_left (by omega)]
    rfl
  · have hd20 := depth_ge (logMem := F.logMem) hsL
    have hrl := F.hptL
    simp only [Node.DeferredClaim.cells, vsFixedS]
    rw [readsAt_append, readsAt_append, List.length_take, min_eq_left (by omega)]
    refine ⟨⟨fun k hk ↦ ?_, fun k hk ↦ ?_⟩, fun k hk ↦ ?_⟩
    · have hk' : k < 19 := by simp at hk; omega
      obtain ⟨v, h523, h6⟩ := hd1 k hk'
      rw [loadHolds_unique h523 (F.hzeta k (by omega))] at h6
      simpa using h6
    · rw [loadHolds_mul_gen_pow]
      obtain ⟨v, h559, h6⟩ := hd2 k (by simpa [vsAlphaVals] using hk)
      rw [loadHolds_unique h559 (F.halphaR k hk)] at h6
      exact h6
    · simp only [List.length_cons, List.length_nil] at hk
      obtain rfl : k = 0 := by omega
      rw [List.length_append, List.length_take, min_eq_left (by omega),
        show (vsAlphaVals σ).length = 4 from rfl, loadHolds_mul_gen_pow]
      exact hd3
  · rw [hπ]
    simp only [vsOsWK, vsOsArgsS, vsOsRetsS]
    exact hacc'

end
end LeanVM.SaltedGuest.B1.VerifySub
