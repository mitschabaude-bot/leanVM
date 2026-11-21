/-
  LeanVM.SaltedGuest.B1.Da.Cell

  B1 for the salted `da_verify_cell`: a cell's keyed digest and its dot product with the weights.
-/

module

public import LeanVM.SaltedGuest.B1.Da.Common
public import LeanVM.Guest.B1.Da.CellSound

/-!
# The salted `da_verify_cell`

`da_verify_cell(lvals, key)` (`core31`) is the deployed one (`Da.cellOk`) with the key's argument
`.n 1` new: its hint and the packing and dot product's `1279` atoms are the deployed template
`tmplA` renamed by `shiftV 1 1`, so the deployed `blk_sound` and `acc_sum` hold at the shifted
valuation; the key's thirteen cells are loaded into `.n 1409 …` and the `128` packed cells are
hashed continuing from them (`ChainSpec` with `init`, `chain_final` after the key's prefix). The
returned words are the keyed digest's two cells and the sum.

`da_verify_cell_valK`: at a valuation, with the symbols `cellSymsOfS σ`; `da_verify_cell_soundK`.
-/

namespace LeanVM.SaltedGuest.B1.Da

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Guest.Value.Keccak LeanVM.Guest.B1 LeanVM.Guest.B1.Digest
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Node LeanVM.Guest.B1.Da LeanVM.SaltedGuest.B1 Recursion.Salted

@[expose] public section

/-- **The salted `da_verify_cell(lvals, key)`**: some `256` symbols of `K` and the `256` weights at
`lvals`; under every seed whose key is at `key`, the returned words are the symbols' keyed digest's
two cells and their dot product with the weights. -/
def MeaningDaVerifyCellK (rd : Reader) : List E → List E → Prop
  | [lv, key], rets => ∃ (syms : List K) (ws : List E), syms.length = LeanDa.cellSymbols ∧
      ReadsAt rd lv ws ∧ ws.length = LeanDa.cellSymbols ∧ ∀ s : Digest, KeyIs rd key s →
      rets = digestCells (keyedHash s (syms.flatMap K.toBytes)) ++
        [((List.range LeanDa.cellSymbols).map fun e ↦ ws.getD e 0 * ofK (syms.getD e 0)).sum]
  | _, _ => False

/-! ## The check -/

/-- The key's cells, loaded into `.n 1409 …`. -/
def cellKeyVs : List V := (List.range 13).map fun c ↦ .n (1409 + c)

/-- The digest's chain: the `128` packed cells, `2048` bytes, from the key's cells. -/
def cellSpecS (atoms : List Atom) : ChainSpec :=
  ⟨(List.range 128).map fun e => some (.n (packV e + 1)), 2048, true, some cellKeyVs,
    keccakBlocks atoms⟩

/-- **The salted `da_verify_cell`'s body, checked**: the hint, the deployed template renamed, the
key's loads, the chain, the copies and `ret`. -/
noncomputable def cellOkS : Bool :=
  decide (LeanVM.SaltedGuest.Data.core31.params = [.n 0, .n 1]) &&
  match splitBody (Fn.body LeanVM.SaltedGuest.Data.core31) with
  | some (A, vs) =>
    decide (vs = [.n 1763, .n 1764, .n 1765]) && decide (1280 ≤ A.length) &&
    atomsEqb ((A.drop 1).take 1279) (tmplA.map (Atom.rename (shiftV 1 1))) &&
    stLoadsOk (A.drop 1280) (.n 1) cellKeyVs 0 &&
    (cellSpecS (A.drop 1280)).check (A.drop 1280) &&
    retOk (A.drop 1280) (cellSpecS (A.drop 1280)) (.n 1763) (.n 1764) &&
    (A.drop 1280).any (isCopyAt (.n 1765) (.n 1408))
  | none => false

set_option maxRecDepth 100000 in
theorem cellS_ok : cellOkS = true := by decide +kernel

set_option maxRecDepth 100000 in
kernel_rfl cell_idxS : SaltedGuest.coreProgram[31]? = some LeanVM.SaltedGuest.Data.core31

theorem find_da_verify_cellS :
    SaltedGuest.coreProgram.find? "da_verify_cell" = some LeanVM.SaltedGuest.Data.core31 :=
  find_of_getElem? cell_idxS

/-! ## The body -/

/-- The symbols the salted `da_verify_cell` hints, read off its valuation. -/
def cellSymsOfS (σ : Val) : List K := cellSymsOf (σ ∘ shiftV 1 1)

/-- **The salted `da_verify_cell`'s body, at a valuation**: under any call relation (it calls
nothing), the meaning holds with the symbols `cellSymsOfS σ` and the weights read at its first
argument. -/
theorem da_verify_cell_valK {C : CallRel} {rd : Reader} {σ : Val} {args rets : List E}
    (hpar : LeanVM.SaltedGuest.Data.core31.params.map σ = args)
    (hb : Stmt.HoldsList C rd σ (Fn.body LeanVM.SaltedGuest.Data.core31) False
      (fun rs => rs = rets)) :
    ∃ lv key, args = [lv, key] ∧ (cellSymsOfS σ).length = LeanDa.cellSymbols ∧
      ReadsAt rd lv (memRun rd lv 256) ∧ (memRun rd lv 256).length = LeanDa.cellSymbols ∧
      ∀ s : Digest, KeyIs rd key s →
      rets = digestCells (keyedHash s ((cellSymsOfS σ).flatMap K.toBytes)) ++
        [((List.range LeanDa.cellSymbols).map fun e ↦
          (memRun rd lv 256).getD e 0 * ofK ((cellSymsOfS σ).getD e 0)).sum] := by
  have hok := cellS_ok
  unfold cellOkS at hok
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨hparams, hok⟩ := hok
  split at hok
  · rename_i A vs hsp
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
    obtain ⟨⟨⟨⟨⟨⟨rfl, -⟩, htm⟩, hld⟩, hchk⟩, hret⟩, hcp⟩ := hok
    rw [splitBody_eq hsp, holdsList_atoms_ret] at hb
    obtain ⟨hat, hrets⟩ := hb
    rw [hparams] at hpar
    subst hpar
    set σ' : Val := σ ∘ shiftV 1 1 with hσ'
    have htmpl : ∀ a ∈ tmplA, a.Holds rd σ' := holds_of_rename fun a ha => by
      rw [← atomsEqb_sound htm] at ha
      exact hat a (List.mem_of_mem_drop (List.mem_of_mem_take ha))
    have hC : ∀ a ∈ A.drop 1280, a.Holds rd σ := fun a ha => hat a (List.mem_of_mem_drop ha)
    have e0 : σ' (.n 0) = σ (.n 0) := by simp [hσ', shiftV_lt]
    have es : ∀ k, 1 ≤ k → σ' (.n k) = σ (.n (k + 1)) := fun k hk => by
      simp [hσ', shiftV_ge hk]
    have hsym : ∀ j < 256, IsInK (σ' (.n (j + 1))) := by
      intro j hj
      obtain ⟨h1, h2, -⟩ := blk_sound (show j / 2 < 128 by omega) htmpl
      rcases Nat.even_or_odd j with ⟨i, hi⟩ | ⟨i, hi⟩
      · rw [show j + 1 = 2 * (j / 2) + 1 by omega]; exact h1
      · rw [show j + 1 = 2 * (j / 2) + 2 by omega]; exact h2
    have hloads : ∀ j < 256, LoadHolds rd (σ (.n 0)) j (memAt rd (σ (.n 0)) j) := by
      intro j hj
      obtain ⟨-, -, -, l0, l1, -⟩ := blk_sound (show j / 2 < 128 by omega) htmpl
      rw [e0] at l0 l1
      rcases Nat.even_or_odd j with ⟨i, hi⟩ | ⟨i, hi⟩
      · rw [show j = 2 * (j / 2) by omega]; exact l0
      · rw [show j = 2 * (j / 2) + 1 by omega]; exact l1
    have hsum := acc_sum htmpl 127 (by norm_num)
    rw [show accV 127 = 1407 from rfl, es 1407 (by norm_num), e0] at hsum
    refine ⟨σ (.n 0), σ (.n 1), rfl, by simp [LeanDa.cellSymbols, cellSymsOfS, cellSymsOf],
      fun j hj => ?_, by simp [LeanDa.cellSymbols], fun s hk => ?_⟩
    · simp only [length_memRun] at hj
      simp only [memRun, List.getElem_map, List.getElem_range]
      exact hloads j hj
    · have hkl := stLoads_sound hld hC
      obtain ⟨hd, -⟩ := chain_final hchk rfl hC (pre := keyPrefix s) (n := 2) (keyPrefix_length s)
        (fun c => by
          simp only [ChainSpec.initCell, cellSpecS]
          have := hkl c
          rw [Nat.zero_add] at this
          rw [hk.load this]
          simp [keyCells, keyState])
      have hr : [σ (.n 1763), σ (.n 1764), σ (.n 1765)] = rets := hrets
      simp only [retOk, Bool.and_eq_true] at hret
      rw [← hr, copy_sound hret.1 hC, copy_sound hret.2 hC, copy_sound hcp hC, hsum]
      have hv : ((cellSpecS (A.drop 1280)).vals σ).take ((cellSpecS (A.drop 1280)).len / 16) =
          (List.range 128).map fun e => σ' (.n (packV e)) := by
        simp only [cellSpecS, ChainSpec.vals, List.map_map]
        rw [List.take_of_length_le (by simp)]
        refine List.map_congr_left fun e he => ?_
        simp only [Function.comp_apply, srcVal]
        rw [es _ (by unfold packV; split <;> omega)]
      rw [hv] at hd
      have hb : cellsBytes ((List.range 128).map fun e => σ' (.n (packV e))) =
          (cellSymsOfS σ).flatMap K.toBytes := by
        rw [cellSymsOfS, cellSymsOf, show (256 : ℕ) = 2 * 128 from rfl, flatMap_pairs, cellsBytes,
          List.flatMap_map]
        refine List.flatMap_congr fun e he => ?_
        have hp := (blk_sound (List.mem_range.mp he) htmpl).2.2.1
        rw [cellBytes, hp, ofLimbs_limb0, ofLimbs_limb1]
      rw [hb, ← keyedHash_eq] at hd
      have hs : ((List.range (2 * 127 + 2)).map fun j => memAt rd (σ (V.n 0)) j * σ' (V.n (j + 1))).sum =
          ((List.range LeanDa.cellSymbols).map fun e ↦
            (memRun rd (σ (.n 0)) 256).getD e 0 * ofK ((cellSymsOfS σ).getD e 0)).sum := by
        simp only [LeanDa.cellSymbols]
        refine congrArg List.sum (List.map_congr_left fun j hj => ?_)
        have hj' := List.mem_range.mp hj
        have h1 : j < (memRun rd (σ (.n 0)) 256).length := by rw [length_memRun]; exact hj'
        have h2 : j < (cellSymsOfS σ).length := by
          rw [cellSymsOfS, cellSymsOf, List.length_map, List.length_range]; exact hj'
        rw [List.getD_eq_getElem _ _ h1, List.getD_eq_getElem _ _ h2]
        simp only [memRun, cellSymsOfS, cellSymsOf, List.getElem_map, List.getElem_range]
        rw [← eq_ofK_limb (hsym j hj')]
      rw [hs, digestCells, ← hd]
      rfl
  · exact absurd hok (by simp)

/-- **The salted `da_verify_cell` computes its meaning.** -/
theorem da_verify_cell_soundK (rd : Reader) (args rets : List E)
    (h : SaltedGuest.coreProgram.Rel rd "da_verify_cell" args rets) :
    MeaningDaVerifyCellK rd args rets := by
  obtain ⟨σ, hpar, hb⟩ := (rel_iff_sem find_da_verify_cellS _ _).mp h
  obtain ⟨lv, key, rfl, hsl, hrd, hwl, hrets⟩ := da_verify_cell_valK hpar hb
  exact ⟨cellSymsOfS σ, memRun rd lv 256, hsl, hrd, hwl, hrets⟩

end
end LeanVM.SaltedGuest.B1.Da
