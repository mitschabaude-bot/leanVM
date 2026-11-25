/-
  LeanVM.SaltedGuest.B1.Main.LoopsK

  The salted children's loop `__loop4`: a child's statement rebuilt under the key, and its proof's
  check.
-/

module

public import LeanVM.SaltedGuest.B1.Main.BodyK
public import LeanVM.SaltedGuest.B1.Digest.StatementK

/-!
# The salted children's loop

`__loop4` is the deployed one (`Main.l5Ok`, `Main.l5_stepC`) with the key as its argument `.n 3`,
its two `child_claim_list_digest` calls taking it, and the child's node count: four hinted digits
`g^e₃, g^e₂, g^e₁, g^e₀`, each range checked below `2^15` (`.n 39` to `.n 42`), composed by
squarings into `g^n`, `n = 2^45 e₃ + 2^30 e₂ + 2^15 e₁ + e₀ < 2^60` (`.n 106`), stored at
`child_count · x`, multiplied into the running count (`count_run · x` to `count_run · x · g`) and
passed to the salted `statement_digest`. `KidStepCK`: the deployed `KidStepC` with the child's
claim lists rebuilt by the salted `child_claim_list_digest` under the key and the child's count;
`l5_stepCK`.
-/

namespace LeanVM.SaltedGuest.B1.Main

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Guest.Value.Keccak LeanVM.Guest.B1 LeanVM.Guest.B1.Digest
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Node LeanVM.Guest.B1.Main LeanVM.SaltedGuest.B1 Recursion.Salted

@[expose] public section

/-- `g^(2^15 - 1)`, the bound cell of a count digit's range check. -/
theorem word_g32767 : word 36029349141217455 0 0 = gen ^ 32767 := by
  rw [word_eOfNat, gen_pow_eq_ofK]
  show ofK (K.ofBits 36029349141217455) = ofK (Parameters.addressOfIndex 32767)
  rw [show K.ofBits 36029349141217455 = Parameters.addressOfIndex 32767 by decide +kernel]

/-- **`n` squarings**: the cells `c` to `c + n - 1`, the first the square of `x` and each next the
square of the one before, hold `x ^ 2 ^ 1` to `x ^ 2 ^ n`. -/
theorem sq_chainN {rd : Reader} {σ : Val} {A : List Atom} {x : V} {c n : ℕ}
    (h0 : isMul A (.n c) x x = true)
    (hs : ∀ i < n, isMul A (.n (c + 1 + i)) (.n (c + i)) (.n (c + i)) = true)
    (hat : ∀ a ∈ A, a.Holds rd σ) : σ (.n (c + n)) = σ x ^ 2 ^ (n + 1) := by
  induction n with
  | zero => rw [Nat.add_zero, isMul_sound h0 hat, ← pow_two, zero_add, pow_one]
  | succ n ih =>
    rw [show c + (n + 1) = c + 1 + n by omega, isMul_sound (hs n (by omega)) hat,
      ih (fun i hi => hs i (by omega)), ← pow_two, ← pow_mul, ← pow_succ]

/-- **A node count's four digits**: `((g^a)^(2^15) g^b)^(2^15) g^c)^(2^15) g^d` is
`g^(2^45 a + 2^30 b + 2^15 c + d)`. -/
theorem gen_pow_digits4 (a b c d : ℕ) :
    ((((gen ^ a) ^ 2 ^ 15 * gen ^ b) ^ 2 ^ 15 * gen ^ c) ^ 2 ^ 15) * gen ^ d =
      gen ^ (2 ^ 45 * a + 2 ^ 30 * b + 2 ^ 15 * c + d) := by
  simp only [← pow_mul, ← pow_add]
  congr 1
  ring

/-- A call of a flat block, from its check. -/
theorem call_of_hasCall {C : CallRel} {rd : Reader} {σ : Val} {P : List Stmt}
    {kret : List E → Prop} (h : ∀ s ∈ P, Stmt.Holds C rd σ s True kret) {f : String}
    {args rets : List V} (hm : hasCall P f args rets = true) : C f (args.map σ) (rets.map σ) :=
  call_of_flat h hm

def l5OkS (fn : Fn) : Bool :=
  let P := loopPre fn
  let A := atomsIn P
  loopShapeF fn "__loop4" &&
  decide (fn.params.length = 19) &&
  isMul A (.n 19) (.n 2) (.n 0) &&
  isLoad A (.n 20) (.n 19) 0 &&
  isTouch A (.n 23) (.n 21) &&
  isTouch A (.n 24) (.n 22) &&
  isMul A (.n 25) (.n 21) (.n 22) &&
  hasCall P "child_claim_list_digest" [.n 3, .n 4, .n 5, .n 20, .n 6, .n 21] [.n 26, .n 27] &&
  isMul A (.n 28) (.n 20) (.n 21) &&
  hasCall P "child_claim_list_digest" [.n 3, .n 7, .n 8, .n 28, .n 9, .n 22] [.n 29, .n 30] &&
  monoIs A (.n 36) (.n 10) (.n 0) 24 &&
  monoIs A (.n 38) (.n 11) (.n 0) 2 &&
  rcConstOk A (.n 39) 36029349141217455 && rcConstOk A (.n 40) 36029349141217455 &&
  rcConstOk A (.n 41) 36029349141217455 && rcConstOk A (.n 42) 36029349141217455 &&
  isMul A (.n 59) (.n 39) (.n 39) &&
  ((List.range 14).all fun i => isMul A (.n (59 + 1 + i)) (.n (59 + i)) (.n (59 + i))) &&
  isMul A (.n 74) (.n 73) (.n 40) &&
  isMul A (.n 75) (.n 74) (.n 74) &&
  ((List.range 14).all fun i => isMul A (.n (75 + 1 + i)) (.n (75 + i)) (.n (75 + i))) &&
  isMul A (.n 90) (.n 89) (.n 41) &&
  isMul A (.n 91) (.n 90) (.n 90) &&
  ((List.range 14).all fun i => isMul A (.n (91 + 1 + i)) (.n (91 + i)) (.n (91 + i))) &&
  isMul A (.n 106) (.n 105) (.n 42) &&
  isMul A (.n 107) (.n 12) (.n 0) &&
  isLoad A (.n 106) (.n 107) 0 &&
  isMul A (.n 108) (.n 13) (.n 0) &&
  isLoad A (.n 109) (.n 108) 0 &&
  isMul A (.n 110) (.n 109) (.n 106) &&
  isMul A (.n 111) (.n 13) (.n 0) &&
  isLoad A (.n 110) (.n 111) 1 &&
  isLoad A (.n 112) (.n 38) 0 &&
  isLoad A (.n 113) (.n 38) 1 &&
  hasCall P "statement_digest" [.n 14, .n 15, .n 26, .n 27, .n 29, .n 30, .n 112, .n 113, .n 36,
    .n 106] [.n 114, .n 115] &&
  monoIs A (.n 117) (.n 16) (.n 0) 2 &&
  isLoad A (.n 114) (.n 117) 0 &&
  monoIs A (.n 118) (.n 16) (.n 0) 2 &&
  isLoad A (.n 115) (.n 118) 1 &&
  monoIs A (.n 124) (.n 18) (.n 0) 24 &&
  hasCall P "verify_sub" [.n 114, .n 115, .n 14, .n 15, .n 17, .n 124] [] &&
  isMul A (.n 125) (.n 20) (.n 25) &&
  isMul A (.n 126) (.n 2) (.n 0) &&
  isLoad A (.n 125) (.n 126) 1

set_option maxRecDepth 100000 in
theorem l5_okS : l5OkS (SaltedGuest.coreProgram.getD 40 default) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem l5_nameS : Da.nameS 40 = "__loop4" := by decide +kernel

theorem find_l5S : SaltedGuest.coreProgram.find? "__loop4" =
    some (SaltedGuest.coreProgram.getD 40 default) :=
  Da.find_getD (by rw [SaltedGuest.coreProgram_length]; omega) l5_nameS

/-- **Child `x`'s facts**, salted (`Main.KidStepC` with the claim lists under the key `key` and
the child's node count `n < 2^60`, stored at `ccount · x` and multiplied into the running count
at `crun · x`). -/
def KidStepCK (C : CallRel) (rd : Reader) (written key lxt cover lxs lst spc lss carried dadig
    ccount crun s0 s1 cpi gsq cfresh x : E) : Prop :=
  ∃ (base cx0 cx1 cs0 cs1 d0 d1 p0 p1 r : E) (ex es n : ℕ),
    LoadHolds rd (written * x) 0 base ∧ ex < 2 ^ 32 ∧ es < 2 ^ 32 ∧
    SaltedGuest.coreProgram.Rel rd "child_claim_list_digest" [key, lxt, cover, base, lxs, gen ^ ex]
      [cx0, cx1] ∧
    SaltedGuest.coreProgram.Rel rd "child_claim_list_digest"
      [key, lst, spc, base * gen ^ ex, lss, gen ^ es] [cs0, cs1] ∧
    LoadHolds rd (dadig * x ^ 2) 0 d0 ∧ LoadHolds rd (dadig * x ^ 2) 1 d1 ∧
    n < 2 ^ 60 ∧ LoadHolds rd (ccount * x) 0 (gen ^ n) ∧
    LoadHolds rd (crun * x) 0 r ∧ LoadHolds rd (crun * x) 1 (r * gen ^ n) ∧
    SaltedGuest.coreProgram.Rel rd "statement_digest"
      [s0, s1, cx0, cx1, cs0, cs1, d0, d1, carried * x ^ 24, gen ^ n] [p0, p1] ∧
    LoadHolds rd (cpi * x ^ 2) 0 p0 ∧ LoadHolds rd (cpi * x ^ 2) 1 p1 ∧
    C "verify_sub" [p0, p1, s0, s1, gsq, cfresh * x ^ 24] [] ∧
    LoadHolds rd (written * x) 1 (base * (gen ^ ex * gen ^ es))

theorem l5_stepCK {rd : Reader} {C : CallRel} {Vm : End.FrameMap} (hVm : End.UnfoldsV rd C Vm)
    (hle : CallRel.Le C (SaltedGuest.coreProgram.Rel rd)) (hm : End.MemOk rd) {x : E} {ps : List E}
    (h : C "__loop4" (x :: ps) []) :
    (∀ N written key lxt cover lxs lst spc lss carried dadig ccount crun s0 s1 cpi gsq cfresh,
      ps = [N, written, key, lxt, cover, lxs, lst, spc, lss, carried, dadig, ccount, crun, s0, s1,
        cpi, gsq, cfresh] →
      KidStepCK C rd written key lxt cover lxs lst spc lss carried dadig ccount crun s0 s1 cpi gsq
        cfresh x) ∧
      (x * gen + ps.headD 0 ≠ 0 → C "__loop4" (x * gen :: ps) []) := by
  have hok := l5_okS
  simp only [l5OkS, Bool.and_eq_true, decide_eq_true_eq, and_assoc, List.all_eq_true,
    List.mem_range] at hok
  obtain ⟨hshape, hlen, hm16, hl17, hg18, hg19, hm28, hcx, hm31, hcs, hm39, hm41, hr39, hr40,
    hr41, hr42, hq0, hqs0, hq74, hq1, hqs1, hq90, hq2, hqs2, hq106, hm107, hl106, hm108, hl109,
    hm110, hm111, hl110, hl42, hl43, hsd, hm47, hl44, hm48, hl45, hm54, hvs, hm55, hm56,
    hl55⟩ := hok
  obtain ⟨hx, hps, hall, hnext⟩ := loop_stepVS hVm find_l5S hshape h
  set σ := Vm "__loop4" (x :: ps) [] with hσ
  refine ⟨fun N written key lxt cover lxs lst spc lss carried dadig ccount crun s0 s1 cpi gsq
    cfresh hN => ?_, hnext⟩
  have hat := atoms_of_flat hall
  have hpar : (SaltedGuest.coreProgram.getD 40 default).params = (List.range 19).map V.n := by
    have hs := hshape
    simp only [loopShapeF, Bool.and_eq_true, decide_eq_true_eq] at hs
    rw [hs.1.2, hlen]
  rw [hpar, hN] at hps
  simp only [List.range_succ, List.range_zero, List.nil_append, List.map_cons,
    List.map_nil, List.cons_append, List.tail_cons, List.cons.injEq, and_true] at hps
  obtain ⟨-, hwr, hkey, hlxt, hcov, hlxs, hlst, hspc, hlss, hcar, hdad, hcc, hcr, hs0, hs1, hcpi,
    hgsq, hcf⟩ := hps
  obtain ⟨ex, hex, hnx⟩ := load_gpow hm (touch_sound hg18 hat)
  obtain ⟨es, hes, hns⟩ := load_gpow hm (touch_sound hg19 hat)
  have h16 : σ (.n 19) = written * x := by rw [isMul_sound hm16 hat, hwr, hx]
  have h28 : σ (.n 25) = gen ^ ex * gen ^ es := by rw [isMul_sound hm28 hat, hnx, hns]
  -- the child's count
  obtain ⟨e3, he3, h39⟩ := rcConst_sound hm (by norm_num) word_g32767 hr39 hat
  obtain ⟨e2, he2, h40⟩ := rcConst_sound hm (by norm_num) word_g32767 hr40 hat
  obtain ⟨e1, he1, h41⟩ := rcConst_sound hm (by norm_num) word_g32767 hr41 hat
  obtain ⟨e0, he0, h42⟩ := rcConst_sound hm (by norm_num) word_g32767 hr42 hat
  have q73 : σ (.n 73) = σ (.n 39) ^ 2 ^ 15 := sq_chainN (c := 59) (n := 14) hq0 hqs0 hat
  have q89 : σ (.n 89) = σ (.n 74) ^ 2 ^ 15 := sq_chainN (c := 75) (n := 14) hq1 hqs1 hat
  have q105 : σ (.n 105) = σ (.n 90) ^ 2 ^ 15 := sq_chainN (c := 91) (n := 14) hq2 hqs2 hat
  have h106 : σ (.n 106) = gen ^ (2 ^ 45 * e3 + 2 ^ 30 * e2 + 2 ^ 15 * e1 + e0) := by
    rw [isMul_sound hq106 hat, q105, isMul_sound hq90 hat, q89, isMul_sound hq74 hat, q73, h39,
      h40, h41, h42, gen_pow_digits4]
  refine ⟨σ (.n 20), σ (.n 26), σ (.n 27), σ (.n 29), σ (.n 30), σ (.n 112), σ (.n 113),
    σ (.n 114), σ (.n 115), σ (.n 109), ex, es, 2 ^ 45 * e3 + 2 ^ 30 * e2 + 2 ^ 15 * e1 + e0, ?_,
    hex, hes, ?_, ?_, ?_, ?_, by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have := load_sound hl17 hat; rwa [h16] at this
  · have := hle _ _ _ (call_of_hasCall hall hcx)
    simp only [List.map_cons, List.map_nil] at this
    rwa [hkey, hlxt, hcov, hlxs, hnx] at this
  · have := hle _ _ _ (call_of_hasCall hall hcs)
    simp only [List.map_cons, List.map_nil] at this
    rwa [isMul_sound hm31 hat, hkey, hlst, hspc, hlss, hnx, hns] at this
  · have := load_sound hl42 hat; rwa [monoIs_sound hm41 hat, hdad, hx] at this
  · have := load_sound hl43 hat; rwa [monoIs_sound hm41 hat, hdad, hx] at this
  · have := load_sound hl106 hat; rwa [isMul_sound hm107 hat, hcc, hx, h106] at this
  · have := load_sound hl109 hat; rwa [isMul_sound hm108 hat, hcr, hx] at this
  · have := load_sound hl110 hat
    rwa [isMul_sound hm111 hat, isMul_sound hm110 hat, hcr, hx, h106] at this
  · have := hle _ _ _ (call_of_hasCall hall hsd)
    simp only [List.map_cons, List.map_nil] at this
    rwa [monoIs_sound hm39 hat, hs0, hs1, hcar, hx, h106] at this
  · have := load_sound hl44 hat; rwa [monoIs_sound hm47 hat, hcpi, hx] at this
  · have := load_sound hl45 hat; rwa [monoIs_sound hm48 hat, hcpi, hx] at this
  · have := call_of_hasCall hall hvs
    simp only [List.map_cons, List.map_nil] at this
    rwa [monoIs_sound hm54 hat, hs0, hs1, hgsq, hcf, hx] at this
  · have := load_sound hl55 hat
    rwa [isMul_sound hm56 hat, isMul_sound hm55 hat, h28, hwr, hx] at this

end
end LeanVM.SaltedGuest.B1.Main
