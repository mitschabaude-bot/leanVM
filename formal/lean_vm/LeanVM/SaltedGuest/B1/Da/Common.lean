/-
  LeanVM.SaltedGuest.B1.Da.Common

  What the salted LeanDA proofs share: value shifts, a node key's run, and the frame map's
  valuation of a salted call.
-/

module

public import LeanVM.SaltedGuest.B1.Keyed
public import LeanVM.SaltedGuest.B1.Callee
public import LeanVM.SaltedGuest.KernelRfl
public import LeanVM.SaltedGuest.B1.Merkle.CapAll
public import LeanVM.SaltedGuest.EndKnow
public import LeanVM.Guest.Renumber
public import LeanVM.Guest.B1.Main.LoopsC

/-!
# Shared salted vocabulary

* `shiftV b d`: the value `.n k` moved to `.n (k + d)` from `k = b` on, the numbering of a salted
  body that has `d` more values from `b` on than the deployed one (a new argument). A salted block
  that is a deployed block renamed by it holds at `σ` exactly when the deployed one holds at
  `σ ∘ shiftV b d` (`Stmt.holdsList_rename`, `Atom.holds_rename`).
* `nodeKey s`: the thirteen cells `node_key` writes (the key's cells, the padding's first byte in
  cell `4` and its last bit in cell `8`); `keyed_node_kr`: one `KECCAK` on them with the message
  XORed into cells `0` to `3` is `HashesPairK` (`keyed_node`).
* `loop_stepVS`, `body_ofVS`: a salted call under a relation that unfolds at a frame map, read at
  the frame map's valuation (`End.UnfoldsV`), as `Main.loop_stepV`, `Main.body_ofV` read a deployed
  one.
-/

namespace LeanVM.SaltedGuest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Guest.Value.Keccak LeanVM.Guest.B1 LeanVM.Guest.B1.Digest
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Node

@[expose] public section

/-! ## Shifts -/

/-- The value `.n k` as `.n (k + d)` from `k = b` on. -/
def shiftV (b d : ℕ) (v : V) : V := ⟨v.path, v.tag, if v.idx < b then v.idx else v.idx + d⟩

theorem shiftV_lt {b d k : ℕ} (h : k < b) : shiftV b d (.n k) = .n k := by
  simp [shiftV, V.n, h]

theorem shiftV_ge {b d k : ℕ} (h : b ≤ k) : shiftV b d (.n k) = .n (k + d) := by
  simp [shiftV, V.n, show ¬ k < b by omega]

/-- An atom of a deployed list renamed into a salted one holds at the shifted valuation. -/
theorem holds_of_rename {rd : Reader} {σ : Val} {r : V → V} {as : List Atom}
    (hat : ∀ a ∈ as.map (Atom.rename r), a.Holds rd σ) : ∀ a ∈ as, a.Holds rd (σ ∘ r) :=
  fun a ha ↦ by rw [← Atom.holds_rename]; exact hat _ (List.mem_map_of_mem ha)

/-! ## A node key -/

/-- **`node_key`'s cells** under `s`: the key's, with the padding's first byte in cell `4` and its
last bit in cell `8`. -/
def nodeKey (s : Digest) (c : Fin 13) : E :=
  if c.val = 4 then keyCells s 4 + word 1 0 0 else if c.val = 8 then keyCells s 8 + w63
  else keyCells s c

/-- **A keyed node over `node_key`'s cells**: one `KECCAK` on `nodeKey s` with the four message cells
added to cells `0` to `3` hashes them under the key. -/
theorem keyed_node_kr {s : Digest} {kr : Fin 13 → E} (hk : kr = nodeKey s) {a0 a1 b0 b1 : E}
    {O : Fin 13 → E}
    (hK : KeccakCellsRelation (cells13 [kr 0 + a0, kr 1 + a1, kr 2 + b0, kr 3 + b1, kr 4, kr 5,
      kr 6, kr 7, kr 8, kr 9, kr 10, kr 11, kr 12]) false O false .all) :
    HashesPairK s a0 a1 b0 b1 (O 0) (O 1) := by
  subst hk
  have e : [nodeKey s 0 + a0, nodeKey s 1 + a1, nodeKey s 2 + b0, nodeKey s 3 + b1, nodeKey s 4,
      nodeKey s 5, nodeKey s 6, nodeKey s 7, nodeKey s 8, nodeKey s 9, nodeKey s 10, nodeKey s 11,
      nodeKey s 12] = nodeIn s a0 a1 b0 b1 := by
    simp only [nodeKey, nodeIn, Fin.isValue, Fin.val_zero, Fin.val_one, Fin.val_two]
    norm_num
  rw [e] at hK
  exact keyed_node hK

/-- **`node_key`'s run, checked**: the thirteen key cells loaded from `p` into `vl`, cell `4` plus
one into `v4` (the constant `c4`), cell `8` plus `2^63` into `v8` (the constant `c8`). -/
def nodeKeyOk (A : List Atom) (p : V) (vl : List V) (v4 c4 v8 c8 : V) : Bool :=
  stLoadsOk A p vl 0 && A.any (isAddAt v4 (vl.getD 4 default) c4) && A.any (isConstAt c4 1 0) &&
    A.any (isAddAt v8 (vl.getD 8 default) c8) && A.any (isConstAt c8 9223372036854775808 0)

/-- The run's thirteen values: the loads, with cells `4` and `8` the adjusted ones. -/
def nodeKeyVs (vl : List V) (v4 v8 : V) : List V := (vl.set 4 v4).set 8 v8

/-- **`node_key`'s run holds the node key** of every seed whose key is at `p`. -/
theorem nodeKey_sound {rd : Reader} {σ : Val} {A : List Atom} {p : V} {vl : List V}
    {v4 c4 v8 c8 : V} (h : nodeKeyOk A p vl v4 c4 v8 c8 = true) (hat : ∀ a ∈ A, a.Holds rd σ)
    {s : Digest} (hk : KeyIs rd (σ p) s) (hl : vl.length = 13) :
    ∀ c : Fin 13, σ ((nodeKeyVs vl v4 v8).getD c default) = nodeKey s c := by
  simp only [nodeKeyOk, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨hld, ha4⟩, hc4⟩, ha8⟩, hc8⟩ := h
  have hload : ∀ c : Fin 13, σ (vl.getD c default) = keyCells s c := fun c ↦ by
    have := stLoads_sound hld hat c
    rw [Nat.zero_add] at this
    exact hk.load this
  intro c
  by_cases h4 : c.val = 4
  · obtain rfl : c = 4 := Fin.ext h4
    have e : (nodeKeyVs vl v4 v8).getD (4 : Fin 13) default = v4 := by
      simp [nodeKeyVs, List.getD_eq_getElem?_getD, hl]
    rw [e, add_sound ha4 hat, const_sound hc4 hat, show σ (vl.getD 4 default) = keyCells s 4 from hload 4]
    rfl
  · by_cases h8 : c.val = 8
    · obtain rfl : c = 8 := Fin.ext h8
      have e : (nodeKeyVs vl v4 v8).getD (8 : Fin 13) default = v8 := by
        simp [nodeKeyVs, List.getD_eq_getElem?_getD, hl]
      rw [e, add_sound ha8 hat, const_sound hc8 hat,
        show σ (vl.getD 8 default) = keyCells s 8 from hload 8]
      rfl
    · have e : (nodeKeyVs vl v4 v8).getD c default = vl.getD c default := by
        simp [nodeKeyVs, List.getD_eq_getElem?_getD, Ne.symm h4, Ne.symm h8]
      rw [e, hload c]
      simp [nodeKey, h4, h8]

/-! ## Calls at the frame map -/

variable {rd : Reader} {C : CallRel}

theorem loop_stepVS {Vm : End.FrameMap} (hVm : End.UnfoldsV rd C Vm) {f : String} {fn : Fn}
    (hf : SaltedGuest.coreProgram.find? f = some fn) (hok : LeanVM.Guest.B1.Digest.loopShapeF fn f = true) {x : E}
    {ps : List E} (h : C f (x :: ps) []) :
    Vm f (x :: ps) [] (V.n 0) = x ∧ fn.params.tail.map (Vm f (x :: ps) []) = ps ∧
      (∀ s ∈ LeanVM.Guest.B1.Digest.loopPre fn, Stmt.Holds C rd (Vm f (x :: ps) []) s True (fun rs => rs = [])) ∧
      (x * gen + ps.headD 0 ≠ 0 → C f (x * gen :: ps) []) := by
  obtain ⟨fn', hf', hp, hb⟩ := hVm _ _ _ h
  obtain rfl : fn = fn' := Option.some.inj (hf.symm.trans hf')
  exact Main.loop_of_body hok hp hb

theorem body_ofVS {Vm : End.FrameMap} (hVm : End.UnfoldsV rd C Vm) {f : String} {fn : Fn}
    (hf : SaltedGuest.coreProgram.find? f = some fn) {args rets : List E} (h : C f args rets) :
    fn.params.map (Vm f args rets) = args ∧
      Stmt.HoldsList C rd (Vm f args rets) fn.body False (fun rs => rs = rets) := by
  obtain ⟨fn', hf', hp, hb⟩ := hVm _ _ _ h
  obtain rfl : fn = fn' := Option.some.inj (hf.symm.trans hf')
  exact ⟨hp, hb⟩

end
end LeanVM.SaltedGuest.B1
