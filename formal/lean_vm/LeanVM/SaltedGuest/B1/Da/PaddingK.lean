/-
  LeanVM.SaltedGuest.B1.Da.PaddingK

  B1 for `da_padding_root`: the root of the zero codeword's tree under the key.
-/

module

public import LeanVM.SaltedGuest.B1.Da.TreeK

/-!
# `da_padding_root`

`da_padding_root(key)` (`core28`) loads the key's run (`.n 1 … .n 13`) and `node_key`'s
(`nodeKeyOk`, `.n 14 …`), hashes the zero cell (`128` zero packed cells, `2048` bytes) continuing
from the key (sixteen `KECCAK`s, a `ChainSpec` with `init`), then hashes the node with itself seven
times (`keyed_node`): the root of the tree whose `128` leaves are the zero cell's keyed digest.

`padRootK s`: that root (`padUpK s 7`); `toBytes_padRootK`: it is LeanDA's padding blob root under
the keyed hash (`LeanDa.paddingBlobRootWithHash`). `da_padding_root_soundK`.
-/

namespace LeanVM.SaltedGuest.B1.Da

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Guest.Value.Keccak LeanVM.Guest.B1 LeanVM.Guest.B1.Digest
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Node LeanVM.Guest.B1.Da LeanVM.SaltedGuest.B1 Recursion.Salted

@[expose] public section

/-! ## The padding root -/

/-- The zero cell's keyed digest, then each level's node hashed with itself. -/
def padUpK (s : Digest) : ℕ → Digest
  | 0 => keyedHash s ((List.replicate LeanDa.cellSymbols (0 : K)).flatMap K.toBytes)
  | n + 1 => keyedHash s (digestBytes (padUpK s n) ++ digestBytes (padUpK s n))

/-- **The zero codeword's blob root under the key.** -/
def padRootK (s : Digest) : Digest := padUpK s 7

theorem merkleRoot_const (s : Digest) : ∀ (d n : ℕ),
    LeanDa.merkleRootWithHash (keyedBytes s) d (fun _ ↦ LeanVM.Protocol.Digest.toBytes (padUpK s n)) =
      LeanVM.Protocol.Digest.toBytes (padUpK s (n + d))
  | 0, n => rfl
  | d + 1, n => by
    rw [LeanDa.merkleRootWithHash]
    have : LeanDa.upWithHash (keyedBytes s) (fun _ ↦ LeanVM.Protocol.Digest.toBytes (padUpK s n)) =
        fun _ ↦ LeanVM.Protocol.Digest.toBytes (padUpK s (n + 1)) := by
      funext i
      simp only [LeanDa.upWithHash, keyedBytes, LeanDa.pairBytes, toList_toBytes, padUpK]
    rw [this, merkleRoot_const s d (n + 1), show n + 1 + d = n + (d + 1) by ring]

/-- **The padding root is LeanDA's padding blob root under the keyed hash.** -/
theorem toBytes_padRootK (s : Digest) :
    LeanVM.Protocol.Digest.toBytes (padRootK s) = LeanDa.paddingBlobRootWithHash (keyedBytes s) := by
  rw [LeanDa.paddingBlobRootWithHash, show LeanDa.cellsPerRow = 2 ^ 7 from rfl,
    show List.replicate (2 ^ 7) (LeanDa.paddingCellWithHash (keyedBytes s)) =
      (List.range (2 ^ 7)).map fun _ ↦ LeanDa.paddingCellWithHash (keyedBytes s) by simp,
    treeRoot_range]
  have := merkleRoot_const s 7 0
  rw [Nat.zero_add] at this
  rw [padRootK, ← this]
  rfl

/-! ## The check -/

/-- The key's cells, loaded into `.n 1 …`. -/
def prVl : List V := (List.range 13).map fun c ↦ .n (1 + c)

/-- The key's cells as `node_key` loads them. -/
def prKl : List V :=
  [.n 14, .n 15, .n 16, .n 17, .n 18, .n 21, .n 22, .n 23, .n 24, .n 27, .n 28, .n 29, .n 30]

/-- `node_key`'s run. -/
def prKr : List V := nodeKeyVs prKl (.n 20) (.n 26)

/-- The zero cell's chain: `128` zero cells, `2048` bytes, from the key. -/
def prSpec (A : List Atom) : ChainSpec :=
  ⟨List.replicate 128 none, 2048, true, some prVl, (keccakBlocks A).take 16⟩

/-- Level `l`'s node, from the node at `.n (234 + 6l)`, `.n (235 + 6l)`: hashed with itself into
`.n (240 + 6l)`, `.n (241 + 6l)`. -/
def prNodeOk (A : List Atom) (l : ℕ) : Bool :=
  (List.range 4).all (fun i => A.any (isAddAt (.n (236 + 6 * l + i)) (prKr.getD i default)
    (.n (234 + 6 * l + i % 2)))) &&
  A.any (isKeccakAt ((List.range 4).map (fun i => V.n (236 + 6 * l + i)) ++ prKr.drop 4)
    [.n (240 + 6 * l), .n (241 + 6 * l)] false false)

/-- **`da_padding_root`'s body, checked.** -/
noncomputable def prOk : Bool :=
  decide (LeanVM.SaltedGuest.Data.core28.params = [.n 0]) &&
  match splitBody (Fn.body LeanVM.SaltedGuest.Data.core28) with
  | some (A, vs) =>
    decide (vs = [.n 278, .n 279]) && stLoadsOk A (.n 0) prVl 0 &&
    nodeKeyOk A (.n 0) prKl (.n 20) (.n 19) (.n 26) (.n 25) && (prSpec A).check A &&
    decide ((prSpec A).outV ((prSpec A).nb - 1) 0 = .n 234) &&
    decide ((prSpec A).outV ((prSpec A).nb - 1) 1 = .n 235) &&
    (List.range 7).all (prNodeOk A) &&
    A.any (isCopyAt (.n 278) (.n 276)) && A.any (isCopyAt (.n 279) (.n 277))
  | none => false

set_option maxRecDepth 100000 in
theorem pr_ok : prOk = true := by decide +kernel

set_option maxRecDepth 100000 in
kernel_rfl pr_idx : SaltedGuest.coreProgram[28]? = some LeanVM.SaltedGuest.Data.core28

theorem find_da_padding_root :
    SaltedGuest.coreProgram.find? "da_padding_root" = some LeanVM.SaltedGuest.Data.core28 :=
  find_of_getElem? pr_idx

/-! ## The meaning -/

/-- **`da_padding_root(key)`**: under every seed whose key is at `key`, the padding root's cells. -/
def MeaningDaPaddingRoot (rd : Reader) : List E → List E → Prop
  | [key], rets => ∀ s : Digest, KeyIs rd key s → rets = digestCells (padRootK s)
  | _, _ => False

set_option maxRecDepth 100000 in
theorem zeroCell_bytes : (List.replicate LeanDa.cellSymbols (0 : K)).flatMap K.toBytes =
    cellsBytes (List.replicate 128 0) := by
  rw [cellsBytes_replicate_zero]
  decide +kernel

/-- **`da_padding_root` returns the padding root's cells.** -/
theorem da_padding_root_soundK (rd : Reader) (args rets : List E)
    (h : SaltedGuest.coreProgram.Rel rd "da_padding_root" args rets) :
    MeaningDaPaddingRoot rd args rets := by
  obtain ⟨σ, hpar, hb⟩ := (rel_iff_sem find_da_padding_root _ _).mp h
  have hok := pr_ok
  unfold prOk at hok
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨hparams, hok⟩ := hok
  split at hok
  · rename_i A vs hsp
    simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range] at hok
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨rfl, hld⟩, hkey⟩, hchk⟩, ho0⟩, ho1⟩, hnodes⟩, hc0⟩, hc1⟩ := hok
    rw [splitBody_eq hsp, holdsList_atoms_ret] at hb
    obtain ⟨hat, hrets⟩ := hb
    rw [hparams] at hpar
    subst hpar
    intro s hks
    have hkl := stLoads_sound hld hat
    have hkr := nodeKey_sound hkey hat hks rfl
    -- the zero cell
    obtain ⟨hd, -⟩ := chain_final hchk rfl hat (pre := keyPrefix s) (n := 2) (keyPrefix_length s)
      (fun c => by
        simp only [ChainSpec.initCell, prSpec]
        have := hkl c
        rw [Nat.zero_add] at this
        rw [hks.load this]
        simp [keyCells, keyState])
    rw [ho0, ho1] at hd
    have hv : ((prSpec A).vals σ).take ((prSpec A).len / 16) = List.replicate 128 0 := by
      simp [prSpec, ChainSpec.vals, srcVal]
    rw [hv, ← zeroCell_bytes, ← keyedHash_eq] at hd
    -- the levels
    have hlev : ∀ l ≤ 7, (σ (.n (234 + 6 * l)), σ (.n (235 + 6 * l))) = digestHalves (padUpK s l) := by
      intro l
      induction l with
      | zero => intro _; exact hd
      | succ l ih =>
        intro hl
        have hn := hnodes l (by omega)
        simp only [prNodeOk, Bool.and_eq_true, List.all_eq_true, List.mem_range] at hn
        obtain ⟨hadd, hkc⟩ := hn
        obtain ⟨-, -, O, hKC, hw⟩ := keccak_holds_full (keccak_sound hkc hat)
        have k0 : σ (.n 14) = nodeKey s 0 := hkr 0
        have k1 : σ (.n 15) = nodeKey s 1 := hkr 1
        have k2 : σ (.n 16) = nodeKey s 2 := hkr 2
        have k3 : σ (.n 17) = nodeKey s 3 := hkr 3
        have k4 : σ (.n 20) = nodeKey s 4 := hkr 4
        have k5 : σ (.n 21) = nodeKey s 5 := hkr 5
        have k6 : σ (.n 22) = nodeKey s 6 := hkr 6
        have k7 : σ (.n 23) = nodeKey s 7 := hkr 7
        have k8 : σ (.n 26) = nodeKey s 8 := hkr 8
        have k9 : σ (.n 27) = nodeKey s 9 := hkr 9
        have k10 : σ (.n 28) = nodeKey s 10 := hkr 10
        have k11 : σ (.n 29) = nodeKey s 11 := hkr 11
        have k12 : σ (.n 30) = nodeKey s 12 := hkr 12
        have x0 := add_sound (hadd 0 (by omega)) hat
        have x1 := add_sound (hadd 1 (by omega)) hat
        have x2 := add_sound (hadd 2 (by omega)) hat
        have x3 := add_sound (hadd 3 (by omega)) hat
        simp only [prKr, nodeKeyVs, prKl, List.set_cons_succ, List.set_cons_zero, List.getD_cons_zero,
          List.getD_cons_succ, Nat.add_zero, Nat.zero_mod, Nat.one_mod, Nat.reduceMod] at x0 x1 x2 x3
        have hin : ((List.range 4).map (fun i => V.n (236 + 6 * l + i)) ++ prKr.drop 4).map σ =
            [nodeKey s 0 + σ (.n (234 + 6 * l)), nodeKey s 1 + σ (.n (235 + 6 * l)),
              nodeKey s 2 + σ (.n (234 + 6 * l)), nodeKey s 3 + σ (.n (235 + 6 * l)), nodeKey s 4,
              nodeKey s 5, nodeKey s 6, nodeKey s 7, nodeKey s 8, nodeKey s 9, nodeKey s 10,
              nodeKey s 11, nodeKey s 12] := by
          simp only [prKr, nodeKeyVs, prKl, List.set_cons_succ, List.set_cons_zero, List.drop,
            List.range_succ, List.range_zero, List.nil_append, List.map_cons, List.map_nil,
            List.cons_append, Nat.add_zero]
          rw [x0, x1, x2, x3, k0, k1, k2, k3, k4, k5, k6, k7, k8, k9, k10, k11, k12]
          simp only [show 234 + 6 * l + 1 = 235 + 6 * l by ring]
        rw [hin] at hKC
        obtain ⟨-, hdig⟩ := keyed_node_kr (kr := nodeKey s) rfl hKC
        have e0 : σ (.n (240 + 6 * l)) = O 0 := hw 0 (by simp)
        have e1 : σ (.n (241 + 6 * l)) = O 1 := hw 1 (by simp)
        have hp := ih (by omega)
        have hp1 : σ (.n (234 + 6 * l)) = (digestHalves (padUpK s l)).1 := congrArg Prod.fst hp
        have hp2 : σ (.n (235 + 6 * l)) = (digestHalves (padUpK s l)).2 := congrArg Prod.snd hp
        rw [show 234 + 6 * (l + 1) = 240 + 6 * l by ring, show 235 + 6 * (l + 1) = 241 + 6 * l by ring,
          e0, e1, hdig, hp1, hp2, padUpK, Main.digestBytes_eq_cells]
        simp [cellsBytes]
    have h7 := hlev 7 le_rfl
    have hr : [σ (.n 278), σ (.n 279)] = rets := hrets
    rw [← hr, copy_sound hc0 hat, copy_sound hc1 hat, digestCells, padRootK, ← h7]
  · exact absurd hok (by simp)

end
end LeanVM.SaltedGuest.B1.Da
