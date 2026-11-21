/-
  LeanVM.SaltedGuest.B1.Main.LoopsK

  The salted children's loop `__loop4`: a child's statement rebuilt under the key, and its proof's
  check.
-/

module

public import LeanVM.SaltedGuest.B1.Main.BodyK

/-!
# The salted children's loop

`__loop4` is the deployed one (`Main.l5Ok`, `Main.l5_stepC`) with the key as its argument `.n 3`
(the deployed values from `3` on moved by one) and its two `child_claim_list_digest` calls taking
it. `KidStepCK`: the deployed `KidStepC` with the child's claim lists rebuilt by the salted
`child_claim_list_digest` under the key; `l5_stepCK`.
-/

namespace LeanVM.SaltedGuest.B1.Main

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Guest.Value.Keccak LeanVM.Guest.B1 LeanVM.Guest.B1.Digest
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Node LeanVM.Guest.B1.Main LeanVM.SaltedGuest.B1 Recursion.Salted

@[expose] public section

def l5OkS (fn : Fn) : Bool :=
  let P := loopPre fn
  let A := atomsIn P
  loopShapeF fn "__loop4" &&
  decide (fn.params.length = 17) &&
  isMul A (.n 17) (.n 2) (.n 0) &&
  isLoad A (.n 18) (.n 17) 0 &&
  isTouch A (.n 21) (.n 19) &&
  isTouch A (.n 22) (.n 20) &&
  isMul A (.n 23) (.n 19) (.n 20) &&
  hasCall P "child_claim_list_digest" [.n 3, .n 4, .n 5, .n 18, .n 6, .n 19] [.n 24, .n 25] &&
  isMul A (.n 26) (.n 18) (.n 19) &&
  hasCall P "child_claim_list_digest" [.n 3, .n 7, .n 8, .n 26, .n 9, .n 20] [.n 27, .n 28] &&
  monoIs A (.n 34) (.n 10) (.n 0) 24 &&
  monoIs A (.n 36) (.n 11) (.n 0) 2 &&
  isLoad A (.n 37) (.n 36) 0 &&
  isLoad A (.n 38) (.n 36) 1 &&
  hasCall P "statement_digest" [.n 12, .n 13, .n 24, .n 25, .n 27, .n 28, .n 37, .n 38, .n 34]
    [.n 39, .n 40] &&
  monoIs A (.n 42) (.n 14) (.n 0) 2 &&
  isLoad A (.n 39) (.n 42) 0 &&
  monoIs A (.n 43) (.n 14) (.n 0) 2 &&
  isLoad A (.n 40) (.n 43) 1 &&
  monoIs A (.n 49) (.n 16) (.n 0) 24 &&
  hasCall P "verify_sub" [.n 39, .n 40, .n 12, .n 13, .n 15, .n 49] [] &&
  isMul A (.n 50) (.n 18) (.n 23) &&
  isMul A (.n 51) (.n 2) (.n 0) &&
  isLoad A (.n 50) (.n 51) 1

set_option maxRecDepth 100000 in
theorem l5_okS : l5OkS (SaltedGuest.coreProgram.getD 40 default) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem l5_nameS : Da.nameS 40 = "__loop4" := by decide +kernel

theorem find_l5S : SaltedGuest.coreProgram.find? "__loop4" =
    some (SaltedGuest.coreProgram.getD 40 default) :=
  Da.find_getD (by rw [SaltedGuest.coreProgram_length]; omega) l5_nameS

/-- **Child `x`'s facts**, salted (`Main.KidStepC` with the claim lists under the key `key`). -/
def KidStepCK (C : CallRel) (rd : Reader) (written key lxt cover lxs lst spc lss carried dadig s0 s1
    cpi gsq cfresh x : E) : Prop :=
  ∃ (base cx0 cx1 cs0 cs1 d0 d1 p0 p1 : E) (ex es : ℕ),
    LoadHolds rd (written * x) 0 base ∧ ex < 2 ^ 32 ∧ es < 2 ^ 32 ∧
    SaltedGuest.coreProgram.Rel rd "child_claim_list_digest" [key, lxt, cover, base, lxs, gen ^ ex]
      [cx0, cx1] ∧
    SaltedGuest.coreProgram.Rel rd "child_claim_list_digest"
      [key, lst, spc, base * gen ^ ex, lss, gen ^ es] [cs0, cs1] ∧
    LoadHolds rd (dadig * x ^ 2) 0 d0 ∧ LoadHolds rd (dadig * x ^ 2) 1 d1 ∧
    SaltedGuest.coreProgram.Rel rd "statement_digest"
      [s0, s1, cx0, cx1, cs0, cs1, d0, d1, carried * x ^ 24] [p0, p1] ∧
    LoadHolds rd (cpi * x ^ 2) 0 p0 ∧ LoadHolds rd (cpi * x ^ 2) 1 p1 ∧
    C "verify_sub" [p0, p1, s0, s1, gsq, cfresh * x ^ 24] [] ∧
    LoadHolds rd (written * x) 1 (base * (gen ^ ex * gen ^ es))

theorem l5_stepCK {rd : Reader} {C : CallRel} {Vm : End.FrameMap} (hVm : End.UnfoldsV rd C Vm)
    (hle : CallRel.Le C (SaltedGuest.coreProgram.Rel rd)) (hm : End.MemOk rd) {x : E} {ps : List E}
    (h : C "__loop4" (x :: ps) []) :
    (∀ N written key lxt cover lxs lst spc lss carried dadig s0 s1 cpi gsq cfresh,
      ps = [N, written, key, lxt, cover, lxs, lst, spc, lss, carried, dadig, s0, s1, cpi, gsq,
        cfresh] →
      KidStepCK C rd written key lxt cover lxs lst spc lss carried dadig s0 s1 cpi gsq cfresh x) ∧
      (x * gen + ps.headD 0 ≠ 0 → C "__loop4" (x * gen :: ps) []) := by
  have hok := l5_okS
  simp only [l5OkS, Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hshape, hlen⟩, hm16⟩, hl17⟩, hg18⟩, hg19⟩, hm28⟩, hcx⟩,
    hm31⟩, hcs⟩, hm39⟩, hm41⟩, hl42⟩, hl43⟩, hsd⟩, hm47⟩, hl44⟩, hm48⟩, hl45⟩, hm54⟩, hvs⟩,
    hm55⟩, hm56⟩, hl55⟩ := hok
  obtain ⟨hx, hps, hall, hnext⟩ := loop_stepVS hVm find_l5S hshape h
  set σ := Vm "__loop4" (x :: ps) [] with hσ
  refine ⟨fun N written key lxt cover lxs lst spc lss carried dadig s0 s1 cpi gsq cfresh hN
    => ?_, hnext⟩
  have hat := atoms_of_flat hall
  have hpar : (SaltedGuest.coreProgram.getD 40 default).params = (List.range 17).map V.n := by
    have hs := hshape
    simp only [loopShapeF, Bool.and_eq_true, decide_eq_true_eq] at hs
    rw [hs.1.2, hlen]
  rw [hpar, hN] at hps
  simp only [List.range_succ, List.range_zero, List.nil_append, List.map_cons,
    List.map_nil, List.cons_append, List.tail_cons, List.cons.injEq, and_true] at hps
  obtain ⟨-, hwr, hkey, hlxt, hcov, hlxs, hlst, hspc, hlss, hcar, hdad, hs0, hs1, hcpi, hgsq,
    hcf⟩ := hps
  obtain ⟨ex, hex, hnx⟩ := load_gpow hm (touch_sound hg18 hat)
  obtain ⟨es, hes, hns⟩ := load_gpow hm (touch_sound hg19 hat)
  have h16 : σ (.n 17) = written * x := by rw [isMul_sound hm16 hat, hwr, hx]
  have h28 : σ (.n 23) = gen ^ ex * gen ^ es := by rw [isMul_sound hm28 hat, hnx, hns]
  refine ⟨σ (.n 18), σ (.n 24), σ (.n 25), σ (.n 27), σ (.n 28), σ (.n 37), σ (.n 38),
    σ (.n 39), σ (.n 40), ex, es, ?_, hex, hes, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have := load_sound hl17 hat; rwa [h16] at this
  · have := hle _ _ _ (call_of_flat hall hcx)
    simpa [hkey, hlxt, hcov, hlxs, hnx] using this
  · have := hle _ _ _ (call_of_flat hall hcs)
    simpa [isMul_sound hm31 hat, hkey, hlst, hspc, hlss, hnx, hns] using this
  · have := load_sound hl42 hat; rwa [monoIs_sound hm41 hat, hdad, hx] at this
  · have := load_sound hl43 hat; rwa [monoIs_sound hm41 hat, hdad, hx] at this
  · have := hle _ _ _ (call_of_flat hall hsd)
    simpa [monoIs_sound hm39 hat, hs0, hs1, hcar, hx] using this
  · have := load_sound hl44 hat; rwa [monoIs_sound hm47 hat, hcpi, hx] at this
  · have := load_sound hl45 hat; rwa [monoIs_sound hm48 hat, hcpi, hx] at this
  · have := call_of_flat hall hvs
    simpa [monoIs_sound hm54 hat, hs0, hs1, hgsq, hcf, hx] using this
  · have := load_sound hl55 hat
    rwa [isMul_sound hm56 hat, isMul_sound hm55 hat, h28, hwr, hx] at this

end
end LeanVM.SaltedGuest.B1.Main
