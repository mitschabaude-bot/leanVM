/-
  LeanVM.SaltedGuest.B1.Main.AggK

  B1 for the salted `aggregate_claims`: the batching of the children from the batching's seed
  call under the seed.
-/

module

public import LeanVM.SaltedGuest.B1.Da.VerifyK
public import LeanVM.Guest.B1.Main.Aggregate
public import LeanVM.Guest.B1.VerifySub.Front

/-!
# The salted `aggregate_claims`

`aggregate_claims(seed_0, seed_1, n_children_g, child_pi, child_fresh, child_carried, defer_stmt)`
(`core35`) is the deployed one (`Main.aggOk`, `Main.aggregate_claims_val`) with the seed's two cells
new and its transcript started at the batching's seed call under the seed: one `KECCAK` of the
seed's cells and the batching label's digest (`VerifySub.vsSeedAtom` renamed by `aggSeedR`, so the
deployed `VerifySub.vs_seed` reads it) whose capacity, copied into `.n 31 … .n 35`, is row `0`'s
capacity, where the deployed guest bakes `Node.batchSeed`'s. Its values are the deployed ones
moved by two below `9` and by `22` from `9` on (the deployed seed constants `9 … 13` are the
copies). Its loops `__loop34`, `__loop35`, `__loop36` are the deployed `__loop33`, `__loop34`,
`__loop35` (unchanged functions: their deployed steps hold of the salted calls through
`Same.rel_same`), and so is `batch_sumcheck__L23`.

The batching from an initial state `S` (`batchFrom S`, `Node.batch`'s transcript run from `S`) on
the carried sponge (`aggS0K S`, `aggAbsK`, `aggLamK`, `aggRunK`, `batch_fsK`), as the deployed
`Main.batch_fs` from `Node.batchSeed`. `aggregate_claims_valK`: at a valuation, for the seed `s` of
its first two arguments, the claim written at `defer_stmt` is `batchFrom (batchingSeed s)` of the
children whose words the memory holds, with the hints `aggHintsS rd σ`.
-/

namespace LeanVM.SaltedGuest.B1.Main

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Guest.Value.Keccak LeanVM.Guest.B1 LeanVM.Guest.B1.Digest
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Node LeanVM.Guest.B1.Main LeanVM.SaltedGuest.B1 Recursion.Salted LeanVM.Guest.B1.Da

@[expose] public section

/-! ## The batching from an initial state -/

/-- **The batching from the initial state `S`**: `Node.batch`'s transcript, run from `S`. -/
def batchFrom (S : KeccakState) (children : List ChildClaims) (h : BatchingHints) :
    Option DeferredClaim :=
  (batch.go children h).run' ⟨S, []⟩

theorem batchFrom_eq (S : KeccakState) (cs : List ChildClaims) (h : BatchingHints) :
    batchFrom S cs h =
      let L := Batch.sqL cs.length (Batch.obsAll ⟨S, []⟩ (Batch.cellsBeforeChallenge cs))
      let R := Batch.rsRun h.sumcheckMessages (Batch.batchedClaim cs L.1) L.2
      if R.1.2 = h.finalBytecodeValue * Batch.batchedBytecodeWeight cs L.1 R.1.1 then
        some ⟨R.1.1, h.finalBytecodeValue⟩
      else none := by
  simp only [batchFrom, batch.go, StateT.run'_eq, StateT.run_bind, Batch.forIn_observe_run,
    Batch.forIn_children_run, Batch.sample_run, Batch.batchRounds_run]
  rw [show Batch.obsAll ⟨S, []⟩ (Batch.cellsBeforeChallenge cs) =
    Batch.obsAll (Batch.obsAll ⟨S, []⟩ (Batch.childCountCells cs.length))
      (cs.flatMap Batch.childCells) from Batch.obsAll_append _ _ _]
  simp only [Batch.id_bind, Batch.id_map, Batch.id_pure, Batch.ite_run, StateT.run_pure, apply_ite Prod.fst,
    Batch.childCountCells]
  rfl

/-- The batching's initial sponge from `S`, carried: its capacity, nothing waiting. -/
def aggS0K (S : KeccakState) : Fs := ⟨capOf S, []⟩

/-- The sponge after the batching's words. -/
def aggAbsK (S : KeccakState) (cs : List ChildClaims) : Fs :=
  (aggS0K S).absorbAll (Batch.cellsBeforeChallenge cs) dsObserve

/-- The lambdas and the sponge after them. -/
def aggLamK (S : KeccakState) (cs : List ChildClaims) : List (E × E) × Fs :=
  sqLF cs.length (aggAbsK S cs)

/-- The sumcheck's run: its challenges and final claim, and the sponge after it. -/
def aggRunK (S : KeccakState) (cs : List ChildClaims) (h : BatchingHints) : (List E × E) × Fs :=
  bsRun h.sumcheckMessages (Batch.batchedClaim cs (aggLamK S cs).1) (aggLamK S cs).2

/-- **The batching from `S` on the carried sponge.** -/
theorem batch_fsK (S : KeccakState) (cs : List ChildClaims) (h : BatchingHints) :
    batchFrom S cs h =
      if (aggRunK S cs h).1.2 =
          h.finalBytecodeValue * Batch.batchedBytecodeWeight cs (aggLamK S cs).1 (aggRunK S cs h).1.1
      then some ⟨(aggRunK S cs h).1.1, h.finalBytecodeValue⟩ else none := by
  rw [batchFrom_eq]
  have hc := carries_obsAll (Batch.cellsBeforeChallenge cs) (s := aggS0K S) (sp := ⟨S, []⟩) ⟨rfl, rfl⟩
  obtain ⟨e1, h1⟩ := carries_sqL cs.length hc
  obtain ⟨sp', -, hr⟩ := B1.batchRounds_run h.sumcheckMessages
    (Batch.batchedClaim cs (aggLamK S cs).1) (aggLamK S cs).2 _ h1
  rw [Batch.batchRounds_run] at hr
  have e1' : (Batch.sqL cs.length (Batch.obsAll ⟨S, []⟩ (Batch.cellsBeforeChallenge cs))).1 =
      (aggLamK S cs).1 := e1
  have hr' : (Batch.rsRun h.sumcheckMessages (Batch.batchedClaim cs (aggLamK S cs).1)
      (Batch.sqL cs.length (Batch.obsAll ⟨S, []⟩ (Batch.cellsBeforeChallenge cs))).2).1 =
      (aggRunK S cs h).1 := congrArg Prod.fst hr
  simp only [e1', hr']

theorem absorb_headK (S : KeccakState) (m : ℕ) :
    (aggS0K S).absorbAll (Batch.childCountCells m) dsObserve =
      ⟨capOf S, [gen ^ m, 0, 0, 0].map (·, dsObserve)⟩ := by
  rw [headCells_eq, absorbAll_short (aggS0K S) _ dsObserve (by simp [aggS0K])]
  rfl

variable {rd : Reader}

/-- **The absorbing rows**, from any initial sponge (`Main.absorb_rows`). -/
theorem absorb_rowsK {absorb cpi cfresh lfT ccarried lcT : E} {m : ℕ} {cs : List ChildClaims}
    {s0 : Fs} (hcl : cs.length = m)
    (hcw : ∀ c (hc : c < cs.length), ChildWordsAt rd cpi cfresh ccarried c cs[c])
    (L25 : ∀ c < m, L25Step rd absorb cfresh lfT ccarried lcT cpi (gen ^ c))
    (h0 : RowRel rd absorb (s0.absorbAll (Batch.childCountCells m) dsObserve))
    (hp0 : (s0.absorbAll (Batch.childCountCells m) dsObserve).pend.length = 4) :
    ∀ c ≤ m, RowRel rd (absorb * (gen ^ c) ^ 13)
      (s0.absorbAll (Batch.childCountCells m ++ (cs.take c).flatMap Batch.childCells) dsObserve) ∧
      (s0.absorbAll (Batch.childCountCells m ++ (cs.take c).flatMap Batch.childCells)
        dsObserve).pend.length = 4 := by
  intro c
  induction c with
  | zero => intro _; simpa using ⟨h0, hp0⟩
  | succ c ih =>
    intro hc
    obtain ⟨hr, hp⟩ := ih (by omega)
    have hcc : c < cs.length := by omega
    obtain ⟨-, -, -, -, hw⟩ := kid_words (hcw c hcc)
    obtain ⟨-, -, hstep⟩ := L25 c (by omega)
    rw [List.take_succ_eq_append_getElem hcc, List.flatMap_append, List.flatMap_singleton,
      ← List.append_assoc, absorbAll_append, ← hw]
    refine ⟨?_, ?_⟩
    · have := hstep _ hp hr
      rwa [show absorb * (gen ^ c) ^ 13 * gen ^ 13 = absorb * (gen ^ (c + 1)) ^ 13 by ring]
        at this
    · rw [pend_absorbAll, hp]
      · simp [l25Words]
      · omega
      · omega

/-! ## The body -/

/-- The salted `aggregate_claims`' block: its body without the final `ret []`. -/
noncomputable def aggPS : List Stmt := (Fn.body LeanVM.SaltedGuest.Data.core35).dropLast

set_option maxRecDepth 100000 in
theorem agg_shapeS : Fn.body LeanVM.SaltedGuest.Data.core35 = aggPS ++ [Stmt.ret []] :=
  stmtsEqb_sound (by decide +kernel)

/-- The seed call's values: the deployed `verify_sub`'s seed atom's, renamed (its four input cells
the seed's and the label digest's, its zeros `14 … 17`, its outputs `18 … 30`). -/
def aggSeedR (v : V) : V :=
  ⟨v.path, v.tag, match v.idx with | 0 => 11 | 1 => 12 | 2 => 0 | 3 => 1 | k => k + 6⟩

/-- The permutation of the last absorbing row: its rate cells, then its capacity. -/
def aggKiS : List V := [.n 97, .n 98, .n 99, .n 100, .n 105, .n 106, .n 107, .n 108, .n 92, .n 93,
  .n 94, .n 95, .n 96]

/-- The permutation's outputs. -/
def aggKoS : List V := (List.range 13).map fun i => .n (109 + i)

/-- **The salted `aggregate_claims`' block, checked.** -/
noncomputable def aggOkS : Bool :=
  let P := aggPS
  let A := atomsIn P
  P.all Stmt.flat && decide (LeanVM.SaltedGuest.Data.core35.params = [.n 0, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6]) &&
  hasAtom A (.const (.n 11) (digestHalves batchLabelDigest).1) &&
  hasAtom A (.const (.n 12) (digestHalves batchLabelDigest).2) &&
  hasAtom A (.const (.n 14) (word 0 0 0)) && hasAtom A (.const (.n 15) (word 0 0 0)) &&
  hasAtom A (.const (.n 16) (word 0 0 0)) && hasAtom A (.const (.n 17) (word 0 0 0)) &&
  hasAtom A (VerifySub.vsSeedAtom.rename aggSeedR) &&
  (List.range 5).all (fun i => A.any (isCopyAt (.n (31 + i)) (.n (26 + i))) &&
    A.any (isLoadAt (.n (31 + i)) (.n 82) i)) &&
  packIn A (.n 2) 36 && A.any (isConstAt (.n 45) 0 0) && packIn A (.n 45) 46 &&
  A.any (isConstAt (.n 55) 0 0) && packIn A (.n 55) 56 &&
  A.any (isConstAt (.n 65) 0 0) && packIn A (.n 65) 66 &&
  (List.range 4).all (fun j => A.any (isLoadAt (.n (42 + 10 * j)) (.n 82) (5 + 2 * j)) &&
    A.any (isLoadAt (.n (44 + 10 * j)) (.n 82) (6 + 2 * j))) &&
  guardOk P (.n 84) "__loop34" (.n 85) (.n 2) [.n 82, .n 4, .n 9, .n 5, .n 10, .n 3] &&
  monoIs A (.n 91) (.n 82) (.n 2) 13 &&
  A.any (isKeccakAt aggKiS aggKoS false false) && rowInOk A (.n 91) aggKiS &&
  allIn A (challA (.n 109) (.n 110) 122) && isMul A (.n 129) (.n 128) (.n 128) &&
  A.any (isConstAt (.n 134) 1 0) && A.any (isLoadAt (.n 134) (.n 133) 0) &&
  A.any (isConstAt (.n 135) 0 0) && A.any (isLoadAt (.n 135) (.n 133) 1) &&
  guardOk P (.n 137) "__loop35" (.n 138) (.n 2) [.n 133, .n 9, .n 10, .n 129, .n 128] &&
  monoIs A (.n 140) (.n 133) (.n 2) 2 && A.any (isLoadAt (.n 141) (.n 140) 1) &&
  hasCall P "batch_sumcheck__L23" [.n 117, .n 118, .n 119, .n 120, .n 121, .n 7, .n 141, .n 142]
    [.n 143, .n 144, .n 145, .n 146, .n 147, .n 148] &&
  (List.range 23).all (fun k => A.any (isConstAt (.n (150 + 3 * k)) 1 0) &&
    A.any (isLoadAt (.n (151 + 3 * k)) (.n 142) k) &&
    A.any (isAddAt (.n (152 + 3 * k)) (.n (150 + 3 * k)) (.n (151 + 3 * k))) &&
    A.any (isLoadAt (.n (152 + 3 * k)) (.n 149) k)) &&
  A.any (isConstAt (.n 222) 0 0) && A.any (isLoadAt (.n 222) (.n 221) 0) &&
  guardOk P (.n 224) "__loop36" (.n 225) (.n 2) [.n 9, .n 10, .n 149, .n 133, .n 221, .n 128] &&
  isMul A (.n 226) (.n 221) (.n 2) && A.any (isLoadAt (.n 227) (.n 226) 0) &&
  isMul A (.n 228) (.n 8) (.n 227) && A.any (isAssertEqAt (.n 148) (.n 228)) &&
  (List.range 23).all (fun k => A.any (isLoadAt (.n (229 + k)) (.n 142) k) &&
    A.any (isLoadAt (.n (229 + k)) (.n 6) k)) &&
  A.any (isLoadAt (.n 8) (.n 6) 23)

set_option maxRecDepth 100000 in
theorem aggS_ok : aggOkS = true := by decide +kernel

/-- The sumcheck's rounds the salted `aggregate_claims` hints, read off the memory at
`bc_sumcheck_msgs`. -/
noncomputable def aggRoundsS (rd : Reader) (σ : Val) : List (E × E) :=
  (List.range 23).map fun k => (memAt rd (σ (.n 7)) (2 * k), memAt rd (σ (.n 7)) (2 * k + 1))

/-- **The salted `aggregate_claims`' hints**: the rounds at `bc_sumcheck_msgs`, the bytecode's
value `bc_star_hint`. -/
noncomputable def aggHintsS (rd : Reader) (σ : Val) : BatchingHints := ⟨aggRoundsS rd σ, σ (.n 8)⟩

/-- **The salted `aggregate_claims`, its hints named**: for the seed of its first two words, the
batching from the batching's seed call under it. -/
def MeaningAggregateClaimsWK (rd : Reader) (h : BatchingHints) : List E → List E → Prop
  | [s0, s1, ncg, cpi, cfresh, ccarried, dst], rets => ∀ s : Digest, (s0, s1) = digestHalves s →
      ∀ m, 1 ≤ m → m ≤ 16 → ncg = gen ^ m →
      rets = [] ∧ ∃ out : DeferredClaim,
        out.bytecodePoint.length = bytecodeVars ∧ ReadsAt rd dst out.cells ∧
        ∀ cs : List ChildClaims, cs.length = m →
          (∀ c (hc : c < cs.length), ChildWordsAt rd cpi cfresh ccarried c cs[c]) →
          batchFrom (batchingSeed s) cs h = some out
  | _, _ => False

/-- A salted call of an unchanged loop is the deployed loop's call. -/
theorem loopToD {f g : String} {args : List E} (hf : Same.inS f = true) (hr : Same.rho f = g)
    (h : SaltedGuest.coreProgram.Rel rd f args []) : Guest.coreProgram.Rel rd g args [] := by
  have := (Same.rel_same rd hf args []).mp h
  rwa [hr] at this

theorem aggregate_claims_valK {C : CallRel} {rd : Reader}
    (hle : CallRel.Le C (SaltedGuest.coreProgram.Rel rd)) {σ : Val} {args rets : List E}
    (hpar : LeanVM.SaltedGuest.Data.core35.params.map σ = args)
    (hbC : Stmt.HoldsList C rd σ (Fn.body LeanVM.SaltedGuest.Data.core35) False (fun rs => rs = rets)) :
    MeaningAggregateClaimsWK rd (aggHintsS rd σ) args rets := by
  have hb := holdsList_mono hle _ id (fun _ h => h) hbC
  have hok := aggS_ok
  simp only [aggOkS, Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hflat, hparams⟩, hs11⟩, hs12⟩, hs14⟩, hs15⟩, hs16⟩, hs17⟩, hsk⟩, hseed⟩, hp0⟩, hc23⟩, hp23⟩, hc33⟩,
    hp33⟩, hc43⟩, hp43⟩, hrate⟩, hg25⟩, hm69⟩, hk⟩, hrin⟩, hch⟩, hm107⟩, hc112⟩, hl112⟩, hc113⟩,
    hl113⟩, hg26⟩, hm118⟩, hl119⟩, hbs⟩, hpt1⟩, hc200⟩, hl200⟩, hg27⟩, hm204⟩, hl205⟩, hm206⟩,
    hae⟩, hout⟩, hl6⟩ := hok
  rw [hparams] at hpar
  subst hpar
  rw [agg_shapeS, holdsList_append] at hb
  obtain ⟨hall, hret⟩ := holdsList_flat aggPS hflat _ _ hb
  have hr : rets = [] := by
    simp only [Stmt.HoldsList, Stmt.Holds, List.map_nil] at hret
    exact hret.symm
  subst hr
  have hat := atoms_of_flat hall
  simp only [List.map_cons, List.map_nil, MeaningAggregateClaimsWK]
  intro s hs m hm1 hm16 hN
  refine ⟨trivial, ?_⟩
  simp only [List.all_eq_true, List.mem_range, Bool.and_eq_true] at hseed hrate hpt1 hout
  -- the absorbing loop
  have L25 : ∀ c < m, L25Step rd (σ (.n 82)) (σ (.n 4)) (σ (.n 9)) (σ (.n 5)) (σ (.n 10))
      (σ (.n 3)) (gen ^ c) :=
    loop_sound (f := "__loop33")
      (ps := [σ (.n 2), σ (.n 82), σ (.n 4), σ (.n 9), σ (.n 5), σ (.n 10), σ (.n 3)])
      (by unfold ordG; omega) hN
      (fun y hy => by
        obtain ⟨h1, h2⟩ := l25_step hy
        exact ⟨h1 _ _ _ _ _ _ _ rfl, h2⟩)
      (fun hne => loopToD (f := "__loop34") (by decide +kernel) (by decide +kernel)
        (by simpa using Da.guardK_soundC hg25 hall hne))
  -- the sumcheck
  have hbsm := (batch_sumcheck_holds rd _ _).mp
    (toD (by decide +kernel) (by decide +kernel) (call_of_flat hall hbs))
  simp only [List.map_cons, List.map_nil] at hbsm
  obtain ⟨-, rounds, hrl, hrd, hpt, hrets⟩ := hbsm
  have hrnd : rounds = aggRoundsS rd σ := rounds_of_reads hrl hrd
  have h126 : σ (.n 148) = (bsRun rounds (σ (.n 141)) ⟨[σ (.n 117), σ (.n 118), σ (.n 119),
      σ (.n 120), σ (.n 121)], []⟩).1.2 := by
    have := congrArg List.getLast? hrets
    simpa using this
  have hptl : (bsRun rounds (σ (.n 141)) ⟨[σ (.n 117), σ (.n 118), σ (.n 119), σ (.n 120),
      σ (.n 121)], []⟩).1.1.length = 23 := by rw [bsRun_len, hrl]
  refine ⟨⟨(bsRun rounds (σ (.n 141)) ⟨[σ (.n 117), σ (.n 118), σ (.n 119),
    σ (.n 120), σ (.n 121)], []⟩).1.1, σ (.n 8)⟩, hptl, ?_, ?_⟩
  · -- the claim written
    intro k hk
    simp only [DeferredClaim.cells, List.length_append, List.length_cons, List.length_nil,
      hptl] at hk
    by_cases hk23 : k < 23
    · rw [show (DeferredClaim.cells ⟨(bsRun rounds (σ (.n 141)) ⟨[σ (.n 117), σ (.n 118),
        σ (.n 119), σ (.n 120), σ (.n 121)], []⟩).1.1, σ (.n 8)⟩)[k] = _ from
        List.getElem_append_left (by rw [hptl]; exact hk23)]
      obtain ⟨h1, h2⟩ := hout k hk23
      have e := loadHolds_unique (load_sound h1 hat) (hpt k (by rw [hptl]; exact hk23))
      rw [← e]
      exact load_sound h2 hat
    · have hk' : k = 23 := by omega
      subst hk'
      rw [show (DeferredClaim.cells ⟨(bsRun rounds (σ (.n 141)) ⟨[σ (.n 117), σ (.n 118),
        σ (.n 119), σ (.n 120), σ (.n 121)], []⟩).1.1, σ (.n 8)⟩)[23] = σ (.n 8) by
          simp [DeferredClaim.cells, List.getElem_append_right, hptl]]
      exact load_sound hl6 hat
  -- the batching
  intro cs hcl hcw
  have hp60 := hp0
  -- row 0
  -- the batching's seed call under `s`
  have hseedcap : [σ (.n 26), σ (.n 27), σ (.n 28), σ (.n 29), σ (.n 30)] =
      capOf (batchingSeed s) := by
    have hk := hasAtom_sound hsk hat
    rw [Atom.holds_rename] at hk
    have z14 := hasAtom_sound hs14 hat
    have z15 := hasAtom_sound hs15 hat
    have z16 := hasAtom_sound hs16 hat
    have z17 := hasAtom_sound hs17 hat
    simp only [Atom.Holds, word_zero] at z14 z15 z16 z17
    obtain ⟨seed, pi, es, ep, hc⟩ := VerifySub.vs_seed hk z14 z15 z16 z17
    have e11 := hasAtom_sound hs11 hat
    have e12 := hasAtom_sound hs12 hat
    simp only [Atom.Holds] at e11 e12
    have hseed' : seed = s := digestScalars_inj (es.symm.trans hs)
    have hpi : pi = batchLabelDigest := by
      refine digestScalars_inj (ep.symm.trans ?_)
      show (σ (.n 11), σ (.n 12)) = _
      rw [e11, e12]
    subst hseed' hpi
    rw [batchingSeed, keccak256_batchLabel]
    exact hc
  have hcap0 : rowCap rd (σ (.n 82)) = capOf (batchingSeed s) := by
    rw [← hseedcap]
    refine list_eq_of_getD (n := 5) (by simp [rowCap]) (by simp) fun i hi => ?_
    obtain ⟨hcp, hld⟩ := hseed i hi
    have e1 := memAt_of_load (load_sound hld hat)
    have e2 := copy_sound hcp hat
    simp only [rowCap, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi,
      Option.map_some, Option.getD_some]
    rw [e1, e2]
    interval_cases i <;> rfl
  have hrow0 : RowRel rd (σ (.n 82)) ((aggS0K (batchingSeed s)).absorbAll (Batch.childCountCells m) dsObserve) := by
    rw [absorb_headK, ← hcap0]
    refine rowRel_full (by simp) fun j hj => ?_
    obtain ⟨r1, r2⟩ := hrate j hj
    rw [memAt_of_load (load_sound r1 hat), memAt_of_load (load_sound r2 hat)]
    rcases (show j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 by omega) with rfl | rfl | rfl | rfl
    · have := packOf_of (packIn_sound hp60 hat)
      rw [hN] at this
      exact this
    · have := packOf_of (packIn_sound hp23 hat)
      rw [const_sound hc23 hat, word_zero] at this
      exact this
    · have := packOf_of (packIn_sound hp33 hat)
      rw [const_sound hc33 hat, word_zero] at this
      exact this
    · have := packOf_of (packIn_sound hp43 hat)
      rw [const_sound hc43 hat, word_zero] at this
      exact this
  have hpend0 : ((aggS0K (batchingSeed s)).absorbAll (Batch.childCountCells m) dsObserve).pend.length = 4 := by
    rw [absorb_headK]; rfl
  -- the absorbing rows
  obtain ⟨hrowm, -⟩ := absorb_rowsK hcl hcw L25 hrow0 hpend0 m le_rfl
  rw [List.take_of_length_le (by omega), show Batch.childCountCells m ++ cs.flatMap Batch.childCells =
    Batch.cellsBeforeChallenge cs by rw [Batch.cellsBeforeChallenge, hcl]] at hrowm
  have hrow69 : RowRel rd (σ (.n 91)) (aggAbsK (batchingSeed s) cs) := by
    rw [monoIs_sound hm69 hat, hN]
    exact hrowm
  -- the permutation and `λ`
  have hin := rowIn_sound hrin hat
  obtain ⟨hcan, hout1⟩ := DupSpec.keccak_facts (keccak_sound hk hat)
  rw [hin] at hcan hout1
  have hperm := rowRel_perm hrow69 (fun c hc => hcan c (List.mem_append_left _ hc))
  rw [← hperm] at hout1
  have o : ∀ c (hc : c < 13), σ (.n (109 + c)) = cellsOfState (aggAbsK (batchingSeed s) cs).perm false ⟨c, hc⟩ :=
    fun c hc => by
      have := hout1 c hc
      rwa [show aggKoS.getD c default = .n (109 + c) by
        simp [aggKoS, List.getD_eq_getElem?_getD, hc]] at this
  have hlam : σ (.n 128) = (aggAbsK (batchingSeed s) cs).squeeze.1 :=
    challengeT_value (chal_sound hch hat) (o 0 (by omega)) (o 1 (by omega))
  have hsq : (aggAbsK (batchingSeed s) cs).squeeze.2 =
      ⟨[σ (.n 117), σ (.n 118), σ (.n 119), σ (.n 120), σ (.n 121)], []⟩ := by
    have o8 : σ (.n 117) = cellsOfState (aggAbsK (batchingSeed s) cs).perm false 8 := o 8 (by omega)
    have o9 : σ (.n 118) = cellsOfState (aggAbsK (batchingSeed s) cs).perm false 9 := o 9 (by omega)
    have o10 : σ (.n 119) = cellsOfState (aggAbsK (batchingSeed s) cs).perm false 10 := o 10 (by omega)
    have o11 : σ (.n 120) = cellsOfState (aggAbsK (batchingSeed s) cs).perm false 11 := o 11 (by omega)
    have o12 : σ (.n 121) = cellsOfState (aggAbsK (batchingSeed s) cs).perm false 12 := o 12 (by omega)
    show (⟨capOf (aggAbsK (batchingSeed s) cs).perm, []⟩ : Fs) = _
    rw [o8, o9, o10, o11, o12]
    rfl
  have hagg : aggLamK (batchingSeed s) cs = (Batch.lambdaPowers (σ (.n 128)) m,
      ⟨[σ (.n 117), σ (.n 118), σ (.n 119), σ (.n 120), σ (.n 121)], []⟩) := by
    simp only [aggLamK, sqLF, hcl, hlam, hsq]
  -- the records
  have L26 : ∀ c < m, L26Step rd (σ (.n 133)) (σ (.n 9)) (σ (.n 10)) (σ (.n 128) * σ (.n 128))
      (σ (.n 128)) (gen ^ c) := by
    have h := loop_sound (f := "__loop34")
      (ps := [σ (.n 2), σ (.n 133), σ (.n 9), σ (.n 10), σ (.n 129), σ (.n 128)])
      (B := fun x => L26Step rd (σ (.n 133)) (σ (.n 9)) (σ (.n 10)) (σ (.n 129)) (σ (.n 128)) x)
      (by unfold ordG; omega) hN
      (fun y hy => by
        obtain ⟨h1, h2⟩ := l26_step hy
        exact ⟨h1 _ _ _ _ _ _ rfl, h2⟩)
      (fun hne => loopToD (f := "__loop35") (by decide +kernel) (by decide +kernel)
        (by simpa using Da.guardK_soundC hg26 hall hne))
    rwa [isMul_sound hm107 hat] at h
  have h111 : memAt rd (σ (.n 133)) 0 = 1 := by
    rw [memAt_of_load (load_sound hl112 hat), const_sound hc112 hat, word_one]
  have h111z : memAt rd (σ (.n 133)) 1 = 0 := by
    rw [memAt_of_load (load_sound hl113 hat), const_sound hc113 hat, word_zero]
  have CH := chain_rows hcl hcw L25 L26 h111 h111z
  have p118 : σ (.n 140) = σ (.n 133) * (gen ^ m) ^ 2 := by
    rw [monoIs_sound hm118 hat, hN]
  have hclaim : Batch.batchedClaim cs (aggLamK (batchingSeed s) cs).1 = σ (.n 141) := by
    obtain ⟨-, hacc⟩ := CH m le_rfl
    rw [List.take_of_length_le (by omega)] at hacc
    rw [hagg, ← memAt_of_load (load_sound hl119 hat), p118, hacc]
    rfl
  have hrun : aggRunK (batchingSeed s) cs ⟨rounds, σ (.n 8)⟩ = bsRun rounds (σ (.n 141))
      ⟨[σ (.n 117), σ (.n 118), σ (.n 119), σ (.n 120), σ (.n 121)], []⟩ := by
    rw [aggRunK, hclaim, hagg]
  -- the weight
  have L27 : ∀ c < m, L27Step rd (σ (.n 9)) (σ (.n 10)) (σ (.n 149)) (σ (.n 133)) (σ (.n 221))
      (σ (.n 128)) (gen ^ c) :=
    loop_sound (f := "__loop35")
      (ps := [σ (.n 2), σ (.n 9), σ (.n 10), σ (.n 149), σ (.n 133), σ (.n 221), σ (.n 128)])
      (by unfold ordG; omega) hN
      (fun y hy => by
        obtain ⟨h1, h2⟩ := l27_step hy
        exact ⟨h1 _ _ _ _ _ _ _ rfl, h2⟩)
      (fun hne => loopToD (f := "__loop36") (by decide +kernel) (by decide +kernel)
        (by simpa using Da.guardK_soundC hg27 hall hne))
  have hptr : (memRun rd (σ (.n 149)) 23).map (1 + ·) = (bsRun rounds (σ (.n 141))
      ⟨[σ (.n 117), σ (.n 118), σ (.n 119), σ (.n 120), σ (.n 121)], []⟩).1.1 := by
    rw [readsAt_memRun hpt, hptl]
    refine map_one_add_memRun fun k hk => ?_
    obtain ⟨⟨⟨c1, l1⟩, a1⟩, s1⟩ := hpt1 k hk
    rw [memAt_of_load (load_sound s1 hat), add_sound a1 hat, const_sound c1 hat, word_one,
      memAt_of_load (load_sound l1 hat)]
  have hz199 : memAt rd (σ (.n 221)) 0 = 0 := by
    rw [memAt_of_load (load_sound hl200 hat), const_sound hc200 hat, word_zero]
  have W := weight_rows hcl hcw L25 L27 (fun c hc => (CH c hc.le).1) hptr hz199 m le_rfl
  rw [List.take_of_length_le (by omega)] at W
  have hw : Batch.batchedBytecodeWeight cs (aggLamK (batchingSeed s) cs).1 (bsRun rounds (σ (.n 141))
      ⟨[σ (.n 117), σ (.n 118), σ (.n 119), σ (.n 120), σ (.n 121)], []⟩).1.1 =
      σ (.n 227) := by
    rw [hagg, ← memAt_of_load (load_sound hl205 hat), isMul_sound hm204 hat, hN, W]
    rfl
  -- the check
  rw [show aggHintsS rd σ = ⟨rounds, σ (.n 8)⟩ by rw [hrnd]; rfl, batch_fsK, hrun, hw, ← h126,
    assertEq_sound hae hat, isMul_sound hm206 hat]
  exact ite_pos' rfl

end
end LeanVM.SaltedGuest.B1.Main
