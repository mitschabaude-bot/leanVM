/-
  LeanVM.SaltedGuest.Bounds.V.Signatures

  Deployed decoder bounds with their value hypotheses for indices below `2^64`: `Cost/Bounds/Guest/Signatures.lean`.
-/

module

public import LeanVM.Cost.Bounds.Guest.Signatures
public import LeanVM.SaltedGuest.Bounds.V.Readers

/-!
Deployed decoder bounds with their value hypotheses for indices below `2^64`: `Cost/Bounds/Guest/Signatures.lean`.

Each lemma is the deployed one of the name without `K`, stated with its hypotheses on a valuation or frame closure `∀ v, v.idx < 2^64 → …`: the salted frame cells are read by the value's index (`cellAtK`), whose price is the index's limbs.
-/

namespace LeanVM.SaltedGuest.Bounds

open LeanVM.Cost.Bounds.Guest LeanVM.Cost LeanVM.Cost.Bounds LeanVM.Cost.Library LeanVM.Parameters
open LeanVM.Guest.Core LeanVM.Guest.B1 LeanVM.Guest.Fast

public section

variable (P : MachineProgram)

instance (M : ℕ) (tab : List (List ℕ)) : Decidable (RowsOK M tab) := by
  unfold RowsOK; infer_instance

instance (M : ℕ) (l : List ℕ) : Decidable (ListOK M l) := by
  unfold ListOK; infer_instance

section Val

variable {σ : Val} {σV : MachineValue}
  (hσ : ∀ v : V, RunsApp P σV [encodeValue v] (encodeValue (σ v)))
  {S : ℕ} (hS : ∀ v : V, v.idx < 2 ^ 64 → appCost P σV [encodeValue v] ≤ S)
include hσ hS

/-- A path level's sibling (`sibNC`): at most `4·S + 71`. -/
theorem sibN_costK (hP : Includes P Decoder.sibNC.costDeps) (bit b : ℕ)
    (hb : b + 1 < 2 ^ 64) (hbit : bit < 2 ^ 64) :
    machineCost P Decoder.sibNC.costIdx [σV, encodeValue bit, encodeValue b] ≤
      4 * S + 71 := by
  rw [Decoder.sibNC.costEq P hP σ σV hσ, limbs_of_lt hb, limbs_of_lt (by omega : b < 2 ^ 64)]
  have := hS (.n bit) hbit; have := hS (.n b) (by show b < 2 ^ 64; omega)
  have := hS (.n (b + 1)) hb
  split_ifs <;> omega

omit hσ hS in
/-- A chain's start cell is below `2^21`, the selectors and the tables' entries below `2^20`. -/
theorem cwCellA_lt {lanes : List ℕ} {G : ℕ} {sel : Array ℕ} {first rest last : Array (Array ℕ)}
    (hsel : ∀ k, sel.getD k 0 < 2 ^ 20) (hf : ∀ r k, offAtA first r k < 2 ^ 20)
    (hr : ∀ r k, offAtA rest r k < 2 ^ 20) (hl : ∀ r k, offAtA last r k < 2 ^ 20) (σ : Val)
    (i : ℕ) : (V.n (cwCellA lanes G sel first rest last σ i)).idx < 2 ^ 64 := by
  show cwCellA lanes G sel first rest last σ i < 2 ^ 64
  unfold cwCellA
  have := hsel (i / 3)
  dsimp only
  split_ifs
  · have := hf (i % 3) (logGTWith lanes (σ (.n (sel.getD (i / 3) 0))) 64); omega
  · have := hr (i % 3) (logGTWith lanes (σ (.n (sel.getD (i / 3) 0))) 64); omega
  · have := hl (i % 3) (logGTWith lanes (σ (.n (sel.getD (i / 3) 0))) 4); omega

/-- **A chain's start cell, off arrays** (`cwCellC`, `cwCellA`): the lanes below `2^64`, the
selectors and the tables' entries below `2^20`: at most `S + 1543`. -/
theorem cwCellA_costK (hP : Includes P Decoder.cwCellC.costDeps) (lanes : List ℕ)
    (hlanes : ∀ x ∈ lanes, x < 2 ^ 64) (G : ℕ) (sel : Array ℕ) (first rest last : Array (Array ℕ))
    (hsel : ∀ k, sel.getD k 0 < 2 ^ 20) (hf : ∀ r k, offAtA first r k < 2 ^ 20)
    (hr : ∀ r k, offAtA rest r k < 2 ^ 20) (hl : ∀ r k, offAtA last r k < 2 ^ 20)
    (hG : G < 2 ^ 20) (i : ℕ) (hi : i < 2 ^ 20) :
    machineCost P Decoder.cwCellC.costIdx [encodeValue lanes, encodeValue G, encodeValue sel,
      encodeValue first, encodeValue rest, encodeValue last, σV, encodeValue i] ≤ S + 1543 := by
  rw [Decoder.cwCellC.costEq P hP _ _ _ _ _ _ σ σV hσ]
  have hsl := hsel (i / 3)
  rw [limbs_of_lt (by omega : i < 2 ^ 64), limbs_of_lt (by omega : i / 3 < 2 ^ 64),
    limbs_of_lt (by omega : G < 2 ^ 64), limbs_of_lt (by omega : sel.getD (i / 3) 0 < 2 ^ 64)]
  have := hS (.n (sel.getD (i / 3) 0)) (by show sel.getD (i / 3) 0 < 2 ^ 64; omega)
  have := logGTWith_cost P (by includes) lanes hlanes (σ (.n (sel.getD (i / 3) 0))) 64
    (by norm_num)
  have := logGTWith_cost P (by includes) lanes hlanes (σ (.n (sel.getD (i / 3) 0))) 4
    (by norm_num)
  rw [Decoder.offAtAC.costEq P (by includes), Decoder.offAtAC.costEq P (by includes)]
  have h1 := hf (i % 3) (logGTWith lanes (σ (.n (sel.getD (i / 3) 0))) 64)
  have h2 := hr (i % 3) (logGTWith lanes (σ (.n (sel.getD (i / 3) 0))) 64)
  have h3 := hl (i % 3) (logGTWith lanes (σ (.n (sel.getD (i / 3) 0))) 4)
  split_ifs with c1 c2
  · rw [limbs_of_lt (by omega : offAtA first (i % 3)
      (logGTWith lanes (σ (.n (sel.getD (i / 3) 0))) 64) < 2 ^ 64),
      limbs_of_lt (by omega : sel.getD (i / 3) 0 + offAtA first (i % 3)
      (logGTWith lanes (σ (.n (sel.getD (i / 3) 0))) 64) < 2 ^ 64)]
    omega
  · rw [limbs_of_lt (by omega : offAtA rest (i % 3)
      (logGTWith lanes (σ (.n (sel.getD (i / 3) 0))) 64) < 2 ^ 64),
      limbs_of_lt (by omega : sel.getD (i / 3) 0 + offAtA rest (i % 3)
      (logGTWith lanes (σ (.n (sel.getD (i / 3) 0))) 64) < 2 ^ 64)]
    omega
  · rw [limbs_of_lt (by omega : offAtA last (i % 3)
      (logGTWith lanes (σ (.n (sel.getD (i / 3) 0))) 4) < 2 ^ 64),
      limbs_of_lt (by omega : sel.getD (i / 3) 0 + offAtA last (i % 3)
      (logGTWith lanes (σ (.n (sel.getD (i / 3) 0))) 4) < 2 ^ 64)]
    omega

/-- **FORS tree `c`'s opening** (`forsOpeningAC`), `c < 24`, the tables `T` small: its secret and
ten siblings, at most `41·S + 1500`. -/
theorem forsOpeningA_costK (hP : Includes P Decoder.forsOpeningAC.costDeps) (T : SpTabs)
    (hT : SpTabsOK T) (c : ℕ) (hc : c < 24) :
    machineCost P Decoder.forsOpeningAC.costIdx [encodeValue T, σV, encodeValue c] ≤
      41 * S + 1500 := by
  rw [Decoder.forsOpeningAC.costEq P hP T σ σV hσ, ofFnFrom_length]
  have := spForsBase_cost P (by includes) c hc
  have := hS (.n (spForsBase c)) (by show spForsBase c < 2 ^ 64; unfold spForsBase; split_ifs <;> omega)
  have := cellNat_cost P (by includes) (σ (.n (spForsBase c)))
  have m := ofFnFrom_cost P (by includes) (n := Sphincs.forsTreeHeight) (by decide) _
    (.closure Decoder.forsOpeningAC.lam0.costIdx [encodeValue T, σV, encodeValue c])
    (fun z ↦ RunsApp.of_spec (Decoder.forsOpeningAC.lam0.costSpec P (by includes) T σ σV hσ c z))
    (4 * S + 120) (fun z ↦ by
      rw [appCost_fn, List.cons_append, List.cons_append, List.cons_append, List.nil_append,
        Decoder.forsOpeningAC.lam0.costEq P (by includes) T σ σV hσ]
      simp only [List.length_cons, List.length_nil]
      have hb := hT.forsBit c z.val
      have hk := hT.forsKid c z.val
      have := sibN_costK P hσ hS (by includes) (offAtA T.forsBit c z.val) (offAtA T.forsKid c z.val)
        (by omega) (by omega)
      have := cellNat_cost P (by includes)
        (sibN σ (offAtA T.forsBit c z.val) (offAtA T.forsKid c z.val))
      rw [Decoder.offAtAC.costEq P (by includes), Decoder.offAtAC.costEq P (by includes)]
      omega) 0 (Nat.zero_le _)
  simp only [Sphincs.forsTreeHeight, Nat.sub_zero] at m ⊢
  omega

/-- **A layer's signature** (`layerAC`), row `l < 3` of the tables `T`, its chains off the
`sp_wots` frame `w` (a valuation of price at most `S`, like `σ`): at most `169·S + 104600`. -/
theorem layerA_costK (hP : Includes P Decoder.layerAC.costDeps) (T : SpTabs) (hT : SpTabsOK T)
    {w : Val} {wV : MachineValue} (hw : ∀ v : V, RunsApp P wV [encodeValue v] (encodeValue (w v)))
    (hW : ∀ v : V, v.idx < 2 ^ 64 → appCost P wV [encodeValue v] ≤ S) (l : ℕ) (hl : l < 3)
    (layer : Sphincs.Layer) :
    machineCost P Decoder.layerAC.costIdx [encodeValue T, σV, wV, encodeValue l,
      encodeValue layer] ≤ 169 * S + 104600 := by
  rw [Decoder.layerAC.costEq P hP T σ σV hσ w wV hw, ofFnFrom_length, ofFnFrom_length,
    Auto.Sphincs.layerHeight.c847.costEq P (by includes)]
  have := spCtr_cost P (by includes) l hl
  have := hS (.n (spCtr l)) (by have := spLayerBase_lt l; show spCtr l < 2 ^ 64; unfold spCtr; omega)
  have := cellNat_cost P (by includes) (σ (.n (spCtr l)))
  have := beWordAt_cost P (by includes) _ (Decoder.cellNat_lt (σ (.n (spCtr l))))
  have hbe := limbs_of_lt (lt_trans (beWordAt_lt (Sig.cellNat (σ (.n (spCtr l))))) (by norm_num))
  rw [limbs_of_lt (by norm_num : 2 ^ 32 - 1 < 2 ^ 64), hbe]
  have hlay := layer.isLt
  simp only [Sphincs.layerCount] at hlay
  rw [limbs_of_lt (by omega : layer.val < 2 ^ 64)]
  have hh : Sphincs.layerHeight layer ≤ 10 := by unfold Sphincs.layerHeight; split <;> omega
  have m0 := ofFnFrom_cost P (by includes) (n := Sphincs.chainCount) (by decide) _
    (.closure Decoder.layerAC.lam0.costIdx [encodeValue T, wV])
    (fun i ↦ RunsApp.of_spec (Decoder.layerAC.lam0.costSpec P (by includes) T w wV hw i))
    (2 * S + 1580) (fun i ↦ by
      rw [appCost_fn, List.cons_append, List.cons_append, List.nil_append,
        Decoder.layerAC.lam0.costEq P (by includes) T w wV hw]
      simp only [List.length_cons, List.length_nil]
      have := cwCellA_costK P hw hW (by includes) T.lanes hT.lanes 21 T.sel T.first T.rest T.last
        hT.sel hT.first hT.rest hT.last (by norm_num) i.val
        (by have := i.isLt; simp only [Sphincs.chainCount] at this; omega)
      have := cellNat_cost P (by includes)
        (w (.n (cwCellA T.lanes 21 T.sel T.first T.rest T.last w i.val)))
      have := hW (.n (cwCellA T.lanes 21 T.sel T.first T.rest T.last w i.val))
        (cwCellA_lt hT.sel hT.first hT.rest hT.last w i.val)
      omega) 0 (Nat.zero_le _)
  have m1 := ofFnFrom_cost P (by includes) (n := Sphincs.layerHeight layer) (by omega) _
    (.closure Decoder.layerAC.lam1.costIdx [encodeValue T, σV, encodeValue l, encodeValue layer])
    (fun j ↦ RunsApp.of_spec (Decoder.layerAC.lam1.costSpec P (by includes) T σ σV hσ l layer j))
    (4 * S + 120) (fun j ↦ by
      rw [appCost_fn, List.cons_append, List.cons_append, List.cons_append, List.cons_append,
        List.nil_append, Decoder.layerAC.lam1.costEq P (by includes) T σ σV hσ]
      simp only [List.length_cons, List.length_nil]
      have hb := hT.pathBit l j.val
      have hk := hT.pathKid l j.val
      have := sibN_costK P hσ hS (by includes) (offAtA T.pathBit l j.val) (offAtA T.pathKid l j.val)
        (by omega) (by omega)
      have := cellNat_cost P (by includes)
        (sibN σ (offAtA T.pathBit l j.val) (offAtA T.pathKid l j.val))
      rw [Decoder.offAtAC.costEq P (by includes), Decoder.offAtAC.costEq P (by includes)]
      omega) 0 (Nat.zero_le _)
  have hm1 : (4 * S + 120 + 16) * (Sphincs.layerHeight layer - 0) ≤ (4 * S + 136) * 10 := by
    rw [Nat.sub_zero]; exact Nat.mul_le_mul_left _ hh
  simp only [Sphincs.chainCount, Nat.sub_zero, ite_self] at m0 ⊢
  omega

/-- **A leanSPHINCS signature, off the tables `T`** (`sphincsSigOfNC`, `sphincsSigOfA`):
`verify_sig_lean_sphincs`' valuation `σ` and the three `sp_wots` frames `w0`, `w1`, `w2`, each a
valuation of price at most `S`: at most `1492·S + 350800`. -/
theorem sphincsSigOfA_costK (hP : Includes P Decoder.sphincsSigOfNC.costDeps) (T : SpTabs)
    (hT : SpTabsOK T) {w0 w1 w2 : Val} {w0V w1V w2V : MachineValue}
    (hw0 : ∀ v : V, RunsApp P w0V [encodeValue v] (encodeValue (w0 v)))
    (hW0 : ∀ v : V, v.idx < 2 ^ 64 → appCost P w0V [encodeValue v] ≤ S)
    (hw1 : ∀ v : V, RunsApp P w1V [encodeValue v] (encodeValue (w1 v)))
    (hW1 : ∀ v : V, v.idx < 2 ^ 64 → appCost P w1V [encodeValue v] ≤ S)
    (hw2 : ∀ v : V, RunsApp P w2V [encodeValue v] (encodeValue (w2 v)))
    (hW2 : ∀ v : V, v.idx < 2 ^ 64 → appCost P w2V [encodeValue v] ≤ S) :
    machineCost P Decoder.sphincsSigOfNC.costIdx [encodeValue T, σV, w0V, w1V, w2V] ≤
      1492 * S + 350800 := by
  rw [Decoder.sphincsSigOfNC.costEq P hP T σ σV hσ w0 w0V hw0 w1 w1V hw1 w2 w2V hw2,
    ofFnFrom_length]
  have := hS (.n 6) (by idx_lt)
  have := cellNat_cost P (by includes) (σ (.n 6))
  have m0 := ofFnFrom_cost P (by includes) (n := Sphincs.forsTreeCount) (by decide) _
    (.closure Decoder.sphincsSigOfNC.lam0.costIdx [encodeValue T, σV])
    (fun c ↦ RunsApp.of_spec (Decoder.sphincsSigOfNC.lam0.costSpec P (by includes) T σ σV hσ c))
    (41 * S + 1520) (fun c ↦ by
      rw [appCost_fn, List.cons_append, List.cons_append, List.nil_append,
        Decoder.sphincsSigOfNC.lam0.costEq P (by includes) T σ σV hσ]
      simp only [List.length_cons, List.length_nil]
      have := forsOpeningA_costK P hσ hS (by includes) T hT c.val
        (by have := c.isLt; simp only [Sphincs.forsTreeCount] at this; omega)
      omega) 0 (Nat.zero_le _)
  have l0 := layerA_costK P hσ hS (by includes) T hT hw0 hW0 0 (by norm_num) 0
  have l1 := layerA_costK P hσ hS (by includes) T hT hw1 hW1 1 (by norm_num) 1
  have l2 := layerA_costK P hσ hS (by includes) T hT hw2 hW2 2 (by norm_num) 2
  rw [Auto.Fin.ofNat.c850.costEq P (by includes), Auto.Fin.ofNat.c850.costEq P (by includes),
    Auto.Fin.ofNat.c850.costEq P (by includes)]
  simp only [Sphincs.forsTreeCount, Sphincs.layerCount, Nat.sub_zero] at m0 ⊢
  limbs_one
  omega

/-- **A layer's call of `sp_wots`, its arguments** (`spWotsArgsC`), `l < 3`: four words, at most
`4·S + 90`. -/
theorem spWotsArgs_costK (hP : Includes P Decoder.spWotsArgsC.costDeps) (l : ℕ) (hl : l < 3) :
    machineCost P Decoder.spWotsArgsC.costIdx [σV, encodeValue l] ≤ 4 * S + 90 := by
  rw [Decoder.spWotsArgsC.costEq P hP σ σV hσ, Decoder.spA0C.costEq P (by includes),
    Decoder.spA1C.costEq P (by includes), Decoder.spEncC.costEq P (by includes)]
  have := spLayerBase_cost P (by includes) l hl
  have := spLayerBase_lt l
  have := hS (.n 2) (by idx_lt); have := hS (.n (spA0 l)) (by show spA0 l < 2 ^ 64; unfold spA0; split_ifs <;> omega)
  have := hS (.n (spA1 l)) (by show spA1 l < 2 ^ 64; unfold spA1; split_ifs <;> omega)
  have := hS (.n (spEnc l)) (by show spEnc l < 2 ^ 64; unfold spEnc; omega)
  limbs_one
  split_ifs <;> omega

/-- **A layer's call of `sp_wots`, its return** (`spWotsRetsC`), `l < 3`: at most `S + 40`. -/
theorem spWotsRets_costK (hP : Includes P Decoder.spWotsRetsC.costDeps) (l : ℕ) (hl : l < 3) :
    machineCost P Decoder.spWotsRetsC.costIdx [σV, encodeValue l] ≤ S + 40 := by
  rw [Decoder.spWotsRetsC.costEq P hP σ σV hσ, Decoder.spLeafC.costEq P (by includes)]
  have := spLayerBase_cost P (by includes) l hl
  have := spLayerBase_lt l
  have := hS (.n (spLeaf l)) (by show spLeaf l < 2 ^ 64; unfold spLeaf; omega)
  limbs_one
  omega

end Val

end

end LeanVM.SaltedGuest.Bounds
