/-
  LeanVM.SaltedGuest.Bounds.V.Xmss

  Deployed decoder bounds with their value hypotheses for indices below `2^64`: `Cost/Bounds/Guest/Xmss.lean`.
-/

module

public import LeanVM.Cost.Bounds.Guest.Xmss
public import LeanVM.SaltedGuest.Bounds.V.Signatures

/-!
Deployed decoder bounds with their value hypotheses for indices below `2^64`: `Cost/Bounds/Guest/Xmss.lean`.

Each lemma is the deployed one of the name without `K`, stated with its hypotheses on a valuation or frame closure `∀ v, v.idx < 2^64 → …`: the salted frame cells are read by the value's index (`cellAtK`), whose price is the index's limbs.
-/

namespace LeanVM.SaltedGuest.Bounds

open LeanVM.Cost.Bounds.Guest LeanVM.Cost LeanVM.Cost.Bounds LeanVM.Cost.Library LeanVM.Parameters
open LeanVM.Guest.Core LeanVM.Guest.B1 LeanVM.Guest.Fast

public section

variable (P : MachineProgram)

section Val

variable {σ : Val} {σV : MachineValue}
  (hσ : ∀ v : V, RunsApp P σV [encodeValue v] (encodeValue (σ v)))
  {S : ℕ} (hS : ∀ v : V, v.idx < 2 ^ 64 → appCost P σV [encodeValue v] ≤ S)
include hσ hS

/-- A layer's dispatches' exponents (`lxArmsTakenC`), its digit words from `dg < 2^20`. -/
theorem lxArmsTaken_costK (hP : Includes P Decoder.lxArmsTakenC.costDeps) (lanes : List ℕ)
    (hl : ∀ x ∈ lanes, x < 2 ^ 64) (dg : ℕ) (hdg : dg < 2 ^ 20) :
    machineCost P Decoder.lxArmsTakenC.costIdx [encodeValue lanes, σV, encodeValue dg] ≤
      (S + 5960) * 15 + 30 := by
  rw [Decoder.lxArmsTakenC.costEq P hP lanes σ σV hσ dg]
  have := rangeMap_le P (by includes) (by includes) _
    (.closure Decoder.lxArmsTakenC.lam0.costIdx [encodeValue lanes, σV, encodeValue dg])
    (fun p ↦ RunsApp.of_spec (Decoder.lxArmsTakenC.lam0.costSpec P (by includes) lanes σ σV hσ dg p))
    (S + 5932) 15 15 le_rfl (by norm_num) (fun p hp ↦ by
      rw [appCost_fn, List.cons_append, List.cons_append, List.cons_append, List.nil_append,
        Decoder.lxArmsTakenC.lam0.costEq P (by includes) lanes σ σV hσ dg p, List.length_cons,
        List.length_cons, List.length_cons, List.length_nil]
      have := hS (.n (dg + p)) (by show dg + p < 2 ^ 64; omega)
      have := logGTWith_cost P (by includes) lanes hl (σ (.n (dg + p))) 256 (by norm_num)
      limbs_one
      omega)
  omega

/-- **A layer's signature, off the tables `T`** (`xPartNC`, `xPartA`), the windows' arms `kw`
(at most `4`, each at most `256`) given: at most `xPartPrice S`. -/
theorem xPartA_costK (hP : Includes P Decoder.xPartNC.costDeps) (T : XmssTabs) (hT : XmssTabsOK T)
    (kw : List ℕ) (hkw : kw.length ≤ 4) (hk : ∀ x ∈ kw, x ≤ 256) (layer : ℕ) (hlay : layer ≤ 1) :
    machineCost P Decoder.xPartNC.costIdx [encodeValue T, encodeValue kw, encodeValue layer, σV] ≤
      xPartPrice S := by
  rw [Decoder.xPartNC.costEq P hP T kw layer σ σV hσ, ofFnFrom_length, ofFnFrom_length]
  have hdg : lxDigitBase layer ≤ 107774 := by unfold lxDigitBase; split_ifs <;> omega
  have hd := Decoder.lxDigitBaseC.costEq P (by includes) layer
  have hr := Decoder.lxRhoCellC.costEq P (by includes) layer
  simp only [ite_self, limbs_of_lt (by omega : layer < 2 ^ 64)] at hd hr
  have ha := lxArmsTaken_costK P hσ hS (by includes) T.lanes hT.lanes (lxDigitBase layer) (by omega)
  have hks := lxArmsTaken_le (σ := σ) T.lanes (lxDigitBase layer)
  have hc := cellNat_cost P (by includes) (σ (.n (lxRhoCell layer)))
  have := hS (.n (lxRhoCell layer))
    (by show lxRhoCell layer < 2 ^ 64; unfold lxRhoCell; split_ifs <;> omega)
  have m0 := ofFnFrom_cost P (by includes) (n := LeanXmss.chainCount) (by decide) _
    (.closure Decoder.xPartNC.lam0.costIdx [encodeValue T, encodeValue layer, σV,
      encodeValue (lxArmsTaken T.lanes σ (lxDigitBase layer))])
    (fun i ↦ RunsApp.of_spec (Decoder.xPartNC.lam0.costSpec P (by includes) T layer σ σV hσ _ i))
    (S + 360) (fun i ↦ by
      rw [appCost_fn, List.cons_append, List.cons_append, List.cons_append, List.cons_append,
        List.nil_append, Decoder.xPartNC.lam0.costEq P (by includes) T layer σ σV hσ,
        List.length_cons, List.length_cons, List.length_cons, List.length_cons, List.length_nil]
      have hi := i.isLt
      simp only [LeanXmss.chainCount] at hi
      have := lxChainCell_cost P (by includes) T hT _ hks.1 hks.2 (lxDigitBase layer + 70)
        (by omega) i.val hi
      have := cellNat_cost P (by includes)
        (σ (.n (lxChainCell T (lxArmsTaken T.lanes σ (lxDigitBase layer)) (lxDigitBase layer + 70)
          i.val)))
      have := hS (.n (lxChainCell T (lxArmsTaken T.lanes σ (lxDigitBase layer))
        (lxDigitBase layer + 70) i.val))
        (by
          show lxChainCell T _ _ i.val < 2 ^ 64
          unfold lxChainCell lxGroupBase
          have := lxGroupTab_lt hT (i.val / 4) (i.val % 4)
            ((lxArmsTaken T.lanes σ (lxDigitBase layer)).getD (i.val / 4) 0)
          split_ifs <;> omega)
      limbs_one
      omega) 0 (Nat.zero_le _)
  have m1 := ofFnFrom_cost P (by includes) (n := LeanXmss.layerHeight) (by decide) _
    (.closure Decoder.xPartNC.lam1.costIdx [encodeValue kw, encodeValue layer, σV])
    (fun l ↦ RunsApp.of_spec (Decoder.xPartNC.lam1.costSpec P (by includes) kw layer σ σV hσ l))
    (S + 200) (fun l ↦ by
      rw [appCost_fn, List.cons_append, List.cons_append, List.cons_append, List.nil_append,
        Decoder.xPartNC.lam1.costEq P (by includes) kw layer σ σV hσ, List.length_cons,
        List.length_cons, List.length_cons, List.length_nil]
      have hl := l.isLt
      simp only [LeanXmss.layerHeight] at hl
      have hkd : kw.getD (2 * layer + l.val / 8) 0 ≤ 256 := by
        rw [List.getD_eq_getElem?_getD]
        cases h : kw[2 * layer + l.val / 8]? with
        | none => simp
        | some x => exact hk x (List.mem_of_getElem? h)
      have hg := getD_cost P (by includes) kw (2 * layer + l.val / 8) 0 (by omega)
      have := lxSibAt_cost P (by includes) (2 * layer + l.val / 8)
        (kw.getD (2 * layer + l.val / 8) 0) (l.val % 8) (by omega) hkd (by omega)
      have := cellNat_cost P (by includes) (σ (.n (lxSibAt (2 * layer + l.val / 8)
        (kw.getD (2 * layer + l.val / 8) 0) (l.val % 8))))
      have := hS (.n (lxSibAt (2 * layer + l.val / 8) (kw.getD (2 * layer + l.val / 8) 0)
        (l.val % 8))) (lt_trans (lxSibAt_lt _ _ _ hkd (by omega)) (by norm_num))
      have := Nat.mul_le_mul_left 15 hkw
      limbs_one
      omega) 0 (Nat.zero_le _)
  simp only [LeanXmss.chainCount, LeanXmss.layerHeight, Nat.sub_zero] at m0 m1 ⊢
  unfold xPartPrice
  omega

/-- **A leanXMSS signature, off the tables `T`** (`xmssSigOfNC`, `xmssSigOfA`): at most
`xmssPrice S`. -/
theorem xmssSigOfN_costK (hP : Includes P Decoder.xmssSigOfNC.costDeps) (T : XmssTabs)
    (hT : XmssTabsOK T) :
    machineCost P Decoder.xmssSigOfNC.costIdx [encodeValue T, σV] ≤ xmssPrice S := by
  rw [Decoder.xmssSigOfNC.costEq P hP T σ σV hσ, ofFnFrom_length]
  have hw := rangeMap_le P (by includes) (by includes) _
    (.closure Decoder.xmssSigOfNC.lam0.costIdx [encodeValue T, σV])
    (fun w ↦ RunsApp.of_spec (Decoder.xmssSigOfNC.lam0.costSpec P (by includes) T σ σV hσ w))
    (S + 5933) 4 4 le_rfl (by norm_num) (fun w hw ↦ by
      rw [appCost_fn, List.cons_append, List.cons_append, List.nil_append,
        Decoder.xmssSigOfNC.lam0.costEq P (by includes) T σ σV hσ w, List.length_cons,
        List.length_cons, List.length_nil]
      have := hS (.n (71 + w)) (by show 71 + w < 2 ^ 64; omega)
      have := logGTWith_cost P (by includes) T.lanes hT.lanes (σ (.n (71 + w))) 256 (by norm_num)
      limbs_one
      omega)
  have hkw : ((List.range 4).map fun w ↦ logGTWith T.lanes (σ (.n (71 + w))) 256).length ≤ 4 ∧
      ∀ x ∈ (List.range 4).map (fun w ↦ logGTWith T.lanes (σ (.n (71 + w))) 256), x ≤ 256 := by
    refine ⟨by simp, fun x hx ↦ ?_⟩
    obtain ⟨w, -, rfl⟩ := List.mem_map.1 hx
    exact logGTWith_le _ _ _
  have hleaf := lxLeafOf_cost P (by includes) _ hkw.1 hkw.2
  have m := ofFnFrom_cost P (by includes) (n := LeanXmss.layerCount) (by decide) _
    (.closure Decoder.xmssSigOfNC.lam1.costIdx [encodeValue T, σV,
      encodeValue ((List.range 4).map fun w ↦ logGTWith T.lanes (σ (.n (71 + w))) 256)])
    (fun l ↦ RunsApp.of_spec (Decoder.xmssSigOfNC.lam1.costSpec P (by includes) T σ σV hσ _ l))
    (xPartPrice S + 10) (fun l ↦ by
      rw [appCost_fn, List.cons_append, List.cons_append, List.cons_append, List.nil_append,
        Decoder.xmssSigOfNC.lam1.costEq P (by includes) T σ σV hσ, List.length_cons,
        List.length_cons, List.length_cons, List.length_nil]
      have hl := l.isLt
      simp only [LeanXmss.layerCount] at hl
      have := xPartA_costK P hσ hS (by includes) T hT _ hkw.1 hkw.2 l.val (by omega)
      omega) 0 (Nat.zero_le _)
  simp only [LeanXmss.layerCount, Nat.sub_zero] at m ⊢
  unfold xmssPrice
  omega

end Val

end

end LeanVM.SaltedGuest.Bounds
