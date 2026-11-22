/-
  LeanVM.SaltedGuest.B1.VerifySub.AssembleLib

  What the salted `verify_sub`'s assembly reads besides its sections: the body's split, the Keccak
  reduction's call, the batched claims' values, the second digest's claims among them, and the
  terminal's obligation.
-/

module

public import LeanVM.SaltedGuest.B1.VerifySub.BackS
public import LeanVM.SaltedGuest.B1.VerifySub.StackS
public import LeanVM.SaltedGuest.B1.VerifySub.LanesS
public import LeanVM.SaltedGuest.B1.VerifySub.TablesS
public import LeanVM.SaltedGuest.B1.VerifySub.Accept2
public import LeanVM.SaltedGuest.B1.VerifySub.DispatchS
public import LeanVM.SaltedGuest.B1.VerifySub.StreamS
public import LeanVM.Guest.B1.VerifySub.SoundOf

/-!
# The salted `verify_sub`'s assembly: its library

* `core18_bodyS`, `vsTS_split`: the body is the template, as the front, the seed's claims, the Keccak
  reduction and the back.
* `vsCalls2S_holds`: the Keccak reduction's statements (`verify_keccak`'s call and its capacity's
  copy).
* `claimAt_readsS`: the `170` batched claims' values where the batching reads them (`vsClaimAtS`):
  `verify_tables`' claims as the deployed `claimAt_reads`, the second digest's claims (the seed's
  lines at the public challenge, `pubLimb`) at the pool's slots `167 .. 169`.
* `lanesOf_append_second`, `notLanes_append_second`, `pubChallengeOf_tctx`, `memFour`: the second
  claims are on the memory's columns, no lanes; the public challenge is the tables' last claim's
  point's first coordinate; the memory has four words.
* `MeaningTerminalK`, `check_opening_terminal_SpecK`: the salted `check_opening_terminal`'s
  obligation, the deployed `MeaningTerminal` with the stack's weight over the claims and the second
  digest's claims at the public challenge (`rm`, its argument `3`).
-/

namespace LeanVM.SaltedGuest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.VerifySub LeanVM.SaltedGuest.B1 Recursion.SecondDigest
open LeanVM.Protocol.EndToEnd.Front

@[expose] public section

/-! ## The body -/

set_option maxRecDepth 100000 in
kernel_rfl core18_bodyS : LeanVM.SaltedGuest.Data.core18.body = vsTS

theorem core18_paramsS : LeanVM.SaltedGuest.Data.core18.params = [.n 0, .n 1, .n 2, .n 3, .n 4, .n 5] :=
  rfl

/-- The salted front, up to `verify_tables`. -/
abbrev vsFrontPartS : List Stmt :=
  vsHeadS ++ vsReadsS ++ vsSizesS ++ vsPushS ++ vsRootsS ++ vsAlphasS ++ vsFpwS ++ vsCalls1S

theorem vsTS_split : vsTS = vsFrontPartS ++ (vsSeedClaimsS ++ (vsCalls2S ++
    (vsMapsS ++ (vsCtabS ++ (vsLamS ++ vsTailS))))) := by
  simp only [vsTS, vsFrontPartS, List.append_assoc]

theorem vsFrontPartS_noRet : Stmt.noRetList vsFrontPartS = true := by decide +kernel

theorem vsSeedClaimsS_noRet : Stmt.noRetList vsSeedClaimsS = true := by decide +kernel

theorem vsCalls2S_noRet : Stmt.noRetList vsCalls2S = true := by decide +kernel

section Calls2

variable {C : CallRel} {rd : Reader} {σ : Val} {next : Prop} {kret : List E → Prop}

/-- **The Keccak reduction**: `gτ` read, `col_eval_words·g^107`, the call of `verify_keccak`, its
capacity copied. -/
theorem vsCalls2S_holds (h : Stmt.HoldsList C rd σ vsCalls2S next kret) :
    LoadHolds rd (σ (.n 131)) 6 (σ (.n 673)) ∧ σ (.n 677) = σ (.n 655) * gen ^ 107 ∧
    C "verify_keccak" [σ (.n 646), σ (.n 647), σ (.n 648), σ (.n 649), σ (.n 650), σ (.n 651),
      σ (.n 673), σ (.n 645), σ (.n 677), σ (.n 674), σ (.n 675)]
      [σ (.n 678), σ (.n 679), σ (.n 680), σ (.n 681), σ (.n 682), σ (.n 683), σ (.n 684),
        σ (.n 685)] ∧
    (∀ i < 5, σ (.n (686 + i)) = σ (.n (678 + i))) ∧ next := by
  simp only [vsCalls2S, vsLd, vsAlloc, vsConst, vsMul, vsCall, List.range_succ, List.range_zero,
    List.map_cons, List.map_nil, List.nil_append, List.cons_append, Stmt.HoldsList, Stmt.Holds,
    Atom.Holds] at h
  obtain ⟨l673, -, -, c676, m677, hk, p0, p1, p2, p3, p4, hn⟩ := h
  refine ⟨l673, by rw [m677, c676, word_g107], hk, fun i hi ↦ ?_, hn⟩
  interval_cases i
  · exact p0
  · exact p1
  · exact p2
  · exact p3
  · exact p4

end Calls2

/-! ## The second digest's claims -/

theorem secondClaims_columns (layout : Layout) (second : Digest) (r : E) :
    (secondClaims layout second r).map (·.column) = [memory0, memory1, memory2] := rfl

theorem secondClaims_values (layout : Layout) (second : Digest) (r : E) :
    (secondClaims layout second r).map (·.value) =
      [pubLimb second r 0, pubLimb second r 1, pubLimb second r 2] := rfl

theorem notLanes_secondClaims (layout : Layout) (second : Digest) (r : E) :
    notLanes (secondClaims layout second r) = secondClaims layout second r := by
  simp [notLanes, secondClaims, keccakOutputColumns, memory0, memory1, memory2]
  decide

theorem lanesOf_secondClaims (layout : Layout) (second : Digest) (r : E) :
    lanesOf (secondClaims layout second r) = [] := by
  simp [lanesOf, secondClaims, keccakOutputColumns, memory0, memory1, memory2]
  decide

theorem lanesOf_append_second (claims : List ColumnClaim) (layout : Layout) (second : Digest)
    (r : E) : lanesOf (claims ++ secondClaims layout second r) = lanesOf claims := by
  rw [lanesOf, List.filter_append, ← lanesOf, ← lanesOf, lanesOf_secondClaims, List.append_nil]

theorem notLanes_append_second (claims : List ColumnClaim) (layout : Layout) (second : Digest)
    (r : E) : notLanes (claims ++ secondClaims layout second r) =
      notLanes claims ++ secondClaims layout second r := by
  rw [notLanes, List.filter_append, ← notLanes, ← notLanes, notLanes_secondClaims]

theorem pubLimb_two (second : Digest) (r : E) : pubLimb second r 2 = 0 := by
  rw [pubLimb_eq]
  have h1 : ((digestHalves second).1).limb 2 = 0 := rfl
  have h2 : ((digestHalves second).2).limb 2 = 0 := rfl
  rw [show ((2 : Fin 3) : Fin 3) = 2 from rfl, h1, h2]
  simp

/-- **The public challenge** is the tables' last claim's point's first coordinate. -/
theorem pubChallengeOf_tctx {rd : Reader} {layout : Layout} {bus : BusResult}
    {claims : List ColumnClaim} {zeta chi rm gmu gzcn : E}
    (h : Tables.TCtx rd layout bus claims [zeta, chi, rm, gmu, gzcn]) : pubChallengeOf claims = rm := by
  simp only [Tables.TCtx] at h
  obtain ⟨chis, -, -, -, -, -, hl, -, hp⟩ := h
  have hl' : claims.length = 167 := hl
  have hlast : claims.getLastD default = claims[166]'(by omega) := by
    rw [List.getLastD_eq_getLast?]
    simp [List.getLast?_eq_getElem?, hl']
  have hq := hp 166 (claims[166]'(by omega)).point (by simp [hl'])
  rw [pubChallengeOf, hlast, (hq.2.2.2 (by decide))]
  rfl

/-- **The memory has four words** when its log is at least `2`. -/
theorem memFour {bytecode : List K} (hbl : bytecode.length = 2 ^ 23) {logMem : ℕ}
    {rowsN : List ℕ} (hl : rowsN.length = 6) (h2 : 2 ≤ logMem) :
    MemoryHasFourWords (Tables.layoutOf bytecode logMem rowsN) := by
  unfold MemoryHasFourWords
  have hsL := tableHeights_length _ hl
  have hkap : (columnKappas logMem 19 (Tables.tableHeightsOf rowsN)).length = 165 :=
    Tables.columnKappas_length _ _ _
  have := placement_committed hkap (layoutOf_placements hbl logMem rowsN) (cc := 0) (by decide)
  rw [committedCols_getD (by decide)] at this
  rw [show memory0 = colOfCommitted 0 from rfl, this]
  have hKC := Tables.committedKappas_columnKappas logMem (Tables.tableHeightsOf rowsN) hsL
  rw [hKC]
  simp [Tables.colKappaSrc, Tables.colKappaAdj]
  omega

/-! ## The batched claims' values -/

theorem claimAt_readsS {rd : Reader} {σ : Val} {claims : List ColumnClaim}
    (hl : claims.length = Tables.nClaims)
    (hp : ReadsAt rd (σ (.n 6)) ((claims.take Tables.nBusClaims).map (·.value)))
    (hc : ReadsAt rd (σ (.n 655))
      (((claims.drop Tables.nBusClaims).take Tables.nColEvals).map (·.value)))
    (hq : ReadsAt rd (σ (.n 6) * gen ^ Tables.nPooled) ((claims.drop Tables.nPooled).map (·.value)))
    {layout : Layout} {second : Digest} {r : E}
    (h167 : LoadHolds rd (σ (.n 6)) 167 (pubLimb second r 0))
    (h168 : LoadHolds rd (σ (.n 6)) 168 (pubLimb second r 1))
    (h169 : LoadHolds rd (σ (.n 6)) 169 0) :
    ∀ j < nClaimsS, LoadHolds rd (σ (.n (vsClaimAtS j).1)) (vsClaimAtS j).2
      (((claims ++ secondClaims layout second r).map (·.value)).getD j 0) := by
  have e1 : Tables.nClaims = 167 := rfl
  have e2 : Tables.nBusClaims = 5 := rfl
  have e3 : Tables.nColEvals = 159 := rfl
  have e4 : Tables.nPooled = 164 := rfl
  rw [e1] at hl
  rw [e2, e3] at hc
  rw [e2] at hp
  rw [e4] at hq
  intro j hj
  have hjS : j < 170 := hj
  rw [List.map_append]
  by_cases hj7 : j < 167
  · rw [List.getD_append _ _ _ _ (by simpa [hl] using hj7)]
    have hj' : j < claims.length := by rw [hl]; exact hj7
    rw [List.getD_eq_getElem _ _ (by simpa using hj'), List.getElem_map]
    unfold vsClaimAtS
    split_ifs with h
    · have := hc (j - 5) (by simp only [List.length_map, List.length_take, List.length_drop, hl]; omega)
      simp only [List.getElem_map, List.getElem_take, List.getElem_drop] at this
      have e : claims[5 + (j - 5)]'(by omega) = claims[j] := by congr 1; omega
      rwa [e] at this
    · by_cases h5 : j < 5
      · have := hp j (by simp only [List.length_map, List.length_take, hl]; omega)
        simpa only [List.getElem_map, List.getElem_take] using this
      · obtain ⟨k, rfl⟩ : ∃ k, j = 164 + k := ⟨j - 164, by omega⟩
        have := hq k (by simp only [List.length_map, List.length_drop, hl]; omega)
        rw [loadHolds_mul_gen_pow] at this
        simpa only [List.getElem_map, List.getElem_drop, show 164 + k - 164 = k by omega] using this
  · rw [List.getD_append_right _ _ _ _ (by simp [hl]; omega), List.length_map, hl,
      secondClaims_values]
    have hv : vsClaimAtS j = (6, j) := by unfold vsClaimAtS; split_ifs with h <;> [omega; rfl]
    rw [hv]
    obtain ⟨k, rfl⟩ : ∃ k, j = 167 + k := ⟨j - 167, by omega⟩
    rw [show 167 + k - 167 = k by omega]
    rcases (show k = 0 ∨ k = 1 ∨ k = 2 by omega) with rfl | rfl | rfl
    · exact h167
    · exact h168
    · simpa [pubLimb_two] using h169

/-! ## The terminal's obligation -/

/-- **The salted `check_opening_terminal`'s outcome**: it returns nothing, and for every reading
of its arguments that the deployed `TermPre` allows, the WHIR terminal holds with the stack's
weight over the claims and the second digest's claims at the public challenge (`rm`, argument `3`),
for any second digest. -/
def MeaningTerminalK (rd : Reader) (args rets : List E) : Prop :=
  rets = [] ∧ ∀ (layout : Layout) (bus : BusResult) (claims : List ColumnClaim) (out : ColumnClaim)
    (lam : E) (ringPoint coeffs x : List E) (second : Digest),
    TermPre rd layout bus claims out lam ringPoint coeffs x args → 2 ≤ layout.logMemory →
      (args.getD 15 0 + stackWeight layout (openedClaims
        (claims ++ secondClaims layout second (args.getD 3 0)) [out]) ringPoint coeffs lam x) *
        args.getD 16 0 = args.getD 17 0

/-- **The salted `check_opening_terminal` is sound.** -/
def check_opening_terminal_SpecK (rd : Reader) : Prop :=
  ∀ args rets, SaltedGuest.coreProgram.Rel rd "check_opening_terminal" args rets →
    MeaningTerminalK rd args rets

end
end LeanVM.SaltedGuest.B1.VerifySub
