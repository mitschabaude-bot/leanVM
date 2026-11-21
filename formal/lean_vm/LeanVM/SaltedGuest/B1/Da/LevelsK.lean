/-
  LeanVM.SaltedGuest.B1.Da.LevelsK

  B1 for the salted `da_levels`: the root of a tree of cell pairs whose nodes are hashed under the
  key.
-/

module

public import LeanVM.SaltedGuest.B1.Da.TreeK
public import LeanVM.Guest.B1.Da.LevelsSound

/-!
# The salted `da_levels`

`da_levels(tree, key, 2^k, k)` (`core381` … `core391`) loads the key's run at `key` and writes
`node_key`'s thirteen cells (`nodeKeyOk`, values `2 … 18`, cells `4` and `8` adjusted into `8` and
`14`); level `lvl`'s loop takes them as its arguments `3 … 15` and hashes nodes `2p`, `2p + 1` of
the level into node `p` of the next under the key (`keyed_node`: the four cells added to the run's
first four, one `KECCAK`), at the deployed offsets (`off`, `ptrOk`). The deployed proof
(`Da.dl_sound`, `Da.levels_root`) carries over with `nodeCellsK` for `nodeCells`; the values are the
deployed ones from `5·lvl + 21` on.

`MeaningDaLevelsK k`: the `2^k` leaves at `tree`, and under every seed whose key is at `key` they are
read, canonical (`0 < k`) and the returned cells are their keyed root `cellRootK`. `da_levels_soundK`.
-/

namespace LeanVM.SaltedGuest.B1.Da

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Guest.Value.Keccak LeanVM.Guest.B1 LeanVM.Guest.B1.Digest
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Node LeanVM.Guest.B1.Da LeanVM.Guest.B1.Main LeanVM.SaltedGuest.B1 Recursion.Salted

@[expose] public section

/-- **The salted `da_levels(tree, key, 2^k, k)`**: the `2^k` leaves at `tree` (two cells each); under
every seed whose key is at `key`, canonical when hashed and the returned cells their keyed root. -/
def MeaningDaLevelsK (k : ℕ) (rd : Reader) : List E → List E → Prop
  | [tree, key], rets => ∃ leaves : List (E × E), leaves.length = 2 ^ k ∧
      ∀ s : Digest, KeyIs rd key s → ReadsAt rd tree (pairCells leaves) ∧
        (0 < k → AllCanonical (pairCells leaves)) ∧
        rets = [(cellRootK s k leaves).1, (cellRootK s k leaves).2]
  | _, _ => False

/-! ## Finding a function -/

theorem find_getD {j : ℕ} {f : String} (hj : j < SaltedGuest.coreProgram.length)
    (hn : (SaltedGuest.coreProgram.getD j default).name = f) :
    SaltedGuest.coreProgram.find? f = some (SaltedGuest.coreProgram.getD j default) := by
  have h := SaltedGuest.coreProgram_find_getElem hj
  rw [List.getD_eq_getElem _ _ hj] at hn ⊢
  rw [← hn]
  exact h

/-! ## A level loop -/

/-- **A salted level loop's body, checked**: the four cells loaded through `tree·g^offA·x^4`, added
to the node key's first four cells (arguments `3 … 6`), hashed with the run's other nine
(arguments `7 … 15`), the digest written through `tree·g^offB·x^2`. -/
def lvlOkS (fn : Fn) (f : String) (offA offB : ℕ) : Bool :=
  let A := atomsIn (loopPre fn)
  let pa := if offA = 0 then 18 else 20
  let pb := pa + 4
  let c0 := pb + 1
  loopShapeF fn f && decide (fn.params.length = 16) &&
  (List.range 4).all (fun i => A.any (isLoadAt (.n (c0 + i)) (.n pa) i)) &&
  ptrOk A (.n pa) (.n 2) (.n 0) offA 4 && ptrOk A (.n pb) (.n 2) (.n 0) offB 2 &&
  (List.range 4).all (fun i => A.any (isAddAt (.n (c0 + 4 + i)) (.n (3 + i)) (.n (c0 + i)))) &&
  A.any (isKeccakAt ((List.range 4).map (fun i => V.n (c0 + 4 + i)) ++
    (List.range 9).map (fun i => V.n (7 + i))) [.n (c0 + 8), .n (c0 + 9)] false false) &&
  A.any (isLoadAt (.n (c0 + 8)) (.n pb) 0) && A.any (isLoadAt (.n (c0 + 9)) (.n pb) 1)

/-- **One node of the next level, under the key**: the four cells at `tree·g^offA·x^4` read,
canonical, and their keyed digest's cells at `tree·g^offB·x^2`. -/
def LvlStepK (rd : Reader) (s : Digest) (tree : E) (offA offB : ℕ) (x : E) : Prop :=
  (∀ i < 4, LoadHolds rd (tree * gen ^ offA * x ^ 4) i (memAt rd (tree * gen ^ offA * x ^ 4) i)) ∧
  AllCanonical ((List.range 4).map (memAt rd (tree * gen ^ offA * x ^ 4))) ∧
  LoadHolds rd (tree * gen ^ offB * x ^ 2) 0
    (nodeCellsK s (memAt rd (tree * gen ^ offA * x ^ 4) 0, memAt rd (tree * gen ^ offA * x ^ 4) 1)
      (memAt rd (tree * gen ^ offA * x ^ 4) 2, memAt rd (tree * gen ^ offA * x ^ 4) 3)).1 ∧
  LoadHolds rd (tree * gen ^ offB * x ^ 2) 1
    (nodeCellsK s (memAt rd (tree * gen ^ offA * x ^ 4) 0, memAt rd (tree * gen ^ offA * x ^ 4) 1)
      (memAt rd (tree * gen ^ offA * x ^ 4) 2, memAt rd (tree * gen ^ offA * x ^ 4) 3)).2

theorem lvl_stepK {rd : Reader} {f : String} {fn : Fn}
    (hf : SaltedGuest.coreProgram.find? f = some fn) {offA offB : ℕ}
    (hok : lvlOkS fn f offA offB = true) (hA : offA < 2 ^ 64) (hB : offB < 2 ^ 64) {x : E}
    {ps : List E} (h : SaltedGuest.coreProgram.Rel rd f (x :: ps) []) :
    (∀ N tree (kr : List E) (s : Digest), ps = N :: tree :: kr →
      (∀ c : Fin 13, kr.getD c 0 = nodeKey s c) → LvlStepK rd s tree offA offB x) ∧
      (x * gen + ps.headD 0 ≠ 0 → SaltedGuest.coreProgram.Rel rd f (x * gen :: ps) []) := by
  simp only [lvlOkS, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range] at hok
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hshape, hlen⟩, hld⟩, hpa⟩, hpb⟩, hadd⟩, hkc⟩, ho0⟩, ho1⟩ := hok
  obtain ⟨σ, hp, hb⟩ := (rel_iff_sem hf _ _).mp h
  obtain ⟨hx, hps, hall, hnext⟩ := loop_of_body hshape hp hb
  refine ⟨fun N tree kr s hN hkr => ?_, hnext⟩
  have hat := atoms_of_flat hall
  have hpar : fn.params = (List.range 16).map V.n := by
    have hs := hshape
    simp only [loopShapeF, Bool.and_eq_true, decide_eq_true_eq] at hs
    rw [hs.1.2, hlen]
  rw [hpar, hN] at hps
  simp only [List.range_succ, List.range_zero, List.nil_append, List.map_cons, List.map_nil,
    List.cons_append, List.tail_cons, List.cons.injEq] at hps
  obtain ⟨-, h2, hkr'⟩ := hps
  have hk : ∀ c : Fin 13, σ (.n (3 + c)) = nodeKey s c := fun c ↦ by
    rw [← hkr c, ← hkr']
    fin_cases c <;> rfl
  set pa := if offA = 0 then 18 else 20 with hpaD
  set c0 := pa + 4 + 1 with hc0
  have ea := ptr_sound hpa hat hA
  have eb := ptr_sound hpb hat hB
  rw [h2, hx] at ea eb
  have hl : ∀ i < 4, LoadHolds rd (tree * gen ^ offA * x ^ 4) i (σ (.n (c0 + i))) := fun i hi => by
    have := load_sound (hld i hi) hat
    rwa [ea] at this
  have hm : ∀ i < 4, memAt rd (tree * gen ^ offA * x ^ 4) i = σ (.n (c0 + i)) :=
    fun i hi => memAt_of_load (hl i hi)
  have hx' : ∀ i < 4, σ (.n (c0 + 4 + i)) = σ (.n (3 + i)) + σ (.n (c0 + i)) :=
    fun i hi => add_sound (hadd i hi) hat
  obtain ⟨-, -, O, hKC, hw⟩ := keccak_holds_full (keccak_sound hkc hat)
  have hin : ((List.range 4).map (fun i => V.n (c0 + 4 + i)) ++
      (List.range 9).map (fun i => V.n (7 + i))).map σ =
      [nodeKey s 0 + σ (.n c0), nodeKey s 1 + σ (.n (c0 + 1)), nodeKey s 2 + σ (.n (c0 + 2)),
        nodeKey s 3 + σ (.n (c0 + 3)), nodeKey s 4, nodeKey s 5, nodeKey s 6, nodeKey s 7,
        nodeKey s 8, nodeKey s 9, nodeKey s 10, nodeKey s 11, nodeKey s 12] := by
    simp only [List.range_succ, List.range_zero, List.nil_append, List.map_cons, List.map_nil,
      List.cons_append]
    rw [hx' 0 (by omega), hx' 1 (by omega), hx' 2 (by omega), hx' 3 (by omega),
      ← hk 0, ← hk 1, ← hk 2, ← hk 3, ← hk 4, ← hk 5, ← hk 6, ← hk 7, ← hk 8, ← hk 9, ← hk 10,
      ← hk 11, ← hk 12]
    rfl
  rw [hin] at hKC
  have hH := keyed_node_kr (kr := nodeKey s) rfl hKC
  obtain ⟨hcan, hd⟩ := hH
  have e0 : σ (.n (c0 + 8)) = O 0 := hw 0 (by simp)
  have e1 : σ (.n (c0 + 9)) = O 1 := hw 1 (by simp)
  have l0 := load_sound ho0 hat
  have l1 := load_sound ho1 hat
  rw [eb] at l0 l1
  refine ⟨fun i hi => by rw [hm i hi]; exact hl i hi, ?_, ?_, ?_⟩
  · simp only [List.range_succ, List.range_zero, List.nil_append, List.map_cons, List.map_nil,
      List.cons_append]
    rw [hm 0 (by omega), hm 1 (by omega), hm 2 (by omega), hm 3 (by omega)]
    simpa using hcan
  · rw [hm 0 (by omega), hm 1 (by omega), hm 2 (by omega), hm 3 (by omega), nodeCellsK, ← hd, ← e0]
    exact l0
  · rw [hm 0 (by omega), hm 1 (by omega), hm 2 (by omega), hm 3 (by omega), nodeCellsK, ← hd, ← e1]
    exact l1

/-! ## A specialization's body -/

/-- The key's cells, as `da_levels` loads them. -/
def dlKeyVl : List V := [.n 2, .n 3, .n 4, .n 5, .n 6, .n 9, .n 10, .n 11, .n 12, .n 15, .n 16, .n 17,
  .n 18]

/-- `node_key`'s run, as `da_levels` passes it to its level loops. -/
def dlKr : List V := nodeKeyVs dlKeyVl (.n 8) (.n 14)

/-- **A guarded loop on a constant bound** `g^k`, under any call relation (`Da.guardPow_sound`). -/
theorem guardPow_soundC {C : CallRel} {rd : Reader} {σ : Val} {P : List Stmt} {gc : V} {f : String}
    {one N : V} {rest : List V} {k : ℕ} (h : guardPowOk P gc f one N rest k = true)
    {kret : List E → Prop} (hall : ∀ s ∈ P, Stmt.Holds C rd σ s True kret) (hk : k < 2 ^ 64) :
    1 + gen ^ k ≠ 0 → C f (1 :: gen ^ k :: rest.map σ) [] := by
  simp only [guardPowOk, Bool.and_eq_true] at h
  obtain ⟨⟨⟨hc, ha⟩, h1⟩, hN⟩ := h
  have hat := atoms_of_flat hall
  have hcall := callIf_of_flat hall hc
  split at ha
  · rename_i p q hpq
    simp only [Bool.and_eq_true] at ha
    intro hne
    have hgc : σ gc = 1 + gen ^ k := by
      rw [addOf_sound hpq hat, const_sound ha.1 hat, word_one, constPow_sound ha.2 hat hk]
    have := hcall.2 (by rw [hgc]; exact hne)
    rwa [List.map_cons, List.map_cons, const_sound h1 hat, word_one, constPow_sound hN hat hk]
      at this
  · exact absurd ha (by simp)

/-- **The salted `da_levels__L{2^k}_L{k}`'s body, checked**, its level loops `loops`. -/
def dlOkS (fn : Fn) (k : ℕ) (loops : List String) : Bool :=
  decide (fn.params = [.n 0, .n 1]) && decide (loops.length = k) &&
  match splitRet fn.body with
  | some (P, vs) =>
    decide (vs = [.n (5 * k + 19), .n (5 * k + 20)]) && P.all Stmt.flat &&
    nodeKeyOk (atomsIn P) (.n 1) dlKeyVl (.n 8) (.n 7) (.n 14) (.n 13) &&
    (List.range k).all (fun lvl => guardPowOk P (.n (5 * lvl + 21)) (loops.getD lvl "")
      (.n (5 * lvl + 22)) (.n (5 * lvl + 23)) (.n 0 :: dlKr) (2 ^ (k - lvl - 1))) &&
    (atomsIn P).any (isLoadAt (.n (5 * k + 19)) (.n 0) (4 * 2 ^ k - 4)) &&
    (atomsIn P).any (isLoadAt (.n (5 * k + 20)) (.n 0) (4 * 2 ^ k - 3))
  | none => false

/-- The specializations: `k`, the name, the core function, its level loops' core functions. -/
def dlTabS : List (ℕ × String × ℕ × List ℕ) :=
  (List.range 11).map fun k ↦
    (k, daLevelsName k, 381 + k, (List.range k).map fun l ↦ 920 + k * (k - 1) / 2 + l)

/-- The name of a core function of the salted guest. -/
noncomputable def nameS (j : ℕ) : String := (SaltedGuest.coreProgram.getD j default).name

/-- A level loop, found and checked. -/
noncomputable def loopOkS (j offA offB : ℕ) : Bool :=
  decide (j < SaltedGuest.coreProgram.length) &&
    lvlOkS (SaltedGuest.coreProgram.getD j default) (nameS j) offA offB

/-- **Entry `k` of `dlTabS`, checked.** -/
noncomputable def dlEntryOkS (k : ℕ) : Bool :=
  let e := dlTabS.getD k (0, "", 0, [])
  decide (nameS e.2.2.1 = e.2.1) && decide (e.2.2.1 < SaltedGuest.coreProgram.length) &&
  dlOkS (SaltedGuest.coreProgram.getD e.2.2.1 default) k (e.2.2.2.map nameS) &&
  (List.range k).all fun lvl => loopOkS (e.2.2.2.getD lvl 0) (off k lvl) (off k (lvl + 1))

/-! ## The root -/

/-- **A checked salted specialization computes its meaning.** -/
theorem dl_soundK {k : ℕ} (hk : k ≤ 10) (hok : dlEntryOkS k = true) :
    ∀ (rd : Reader) (args rets : List E),
      SaltedGuest.coreProgram.Rel rd (daLevelsName k) args rets →
        MeaningDaLevelsK k rd args rets := by
  have he : (dlTabS.getD k (0, "", 0, [])) =
      (k, daLevelsName k, 381 + k, (List.range k).map fun l ↦ 920 + k * (k - 1) / 2 + l) := by
    simp [dlTabS, List.getD_eq_getElem?_getD, show k < 11 by omega]
  unfold dlEntryOkS at hok
  rw [he] at hok
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range] at hok
  obtain ⟨⟨⟨hname, hlen⟩, hdl⟩, hloops⟩ := hok
  intro rd args rets hrel
  obtain ⟨σ, hpar, hb⟩ := (rel_iff_sem (find_getD hlen hname) _ _).mp hrel
  unfold dlOkS at hdl
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hdl
  obtain ⟨⟨hparams, -⟩, hdl⟩ := hdl
  split at hdl
  · rename_i P vs hsr
    simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range] at hdl
    obtain ⟨⟨⟨⟨⟨rfl, hflat⟩, hkey⟩, hguards⟩, hr0⟩, hr1⟩ := hdl
    rw [splitRet_eq hsr, holdsList_append] at hb
    obtain ⟨hall, hret⟩ := holdsList_flat P (List.all_eq_true.mpr hflat) _ _ hb
    simp only [Stmt.HoldsList, Stmt.Holds, List.map_cons, List.map_nil] at hret
    rw [hparams] at hpar
    subst hpar
    have hat := atoms_of_flat hall
    have h2k : 2 ^ k ≤ 2 ^ 10 := Nat.pow_le_pow_right (by norm_num) hk
    -- the levels
    have hlvl : ∀ s : Digest, KeyIs rd (σ (.n 1)) s → ∀ lvl < k, ∀ p < 2 ^ (k - lvl - 1),
        LvlStepK rd s (σ (.n 0)) (off k lvl) (off k (lvl + 1)) (gen ^ p) := by
      intro s hks lvl hl
      have hkr := nodeKey_sound hkey hat hks rfl
      have hlo := hloops lvl hl
      unfold loopOkS at hlo
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hlo
      have hm : 2 ^ (k - lvl - 1) ≤ 2 ^ 10 := Nat.pow_le_pow_right (by norm_num) (by omega)
      have hg := hguards lvl hl
      have hnm : (((List.range k).map (fun l ↦ 920 + k * (k - 1) / 2 + l)).map nameS).getD lvl "" =
          nameS (((List.range k).map (fun l ↦ 920 + k * (k - 1) / 2 + l)).getD lvl 0) := by
        simp [List.getD_eq_getElem?_getD, hl]
      rw [hnm] at hg
      exact loop_soundC (C := SaltedGuest.coreProgram.Rel rd)
        (ps := gen ^ 2 ^ (k - lvl - 1) :: σ (.n 0) :: dlKr.map σ)
        (N := gen ^ 2 ^ (k - lvl - 1)) (m := 2 ^ (k - lvl - 1)) (by unfold ordG; omega) rfl
        (fun y hy => by
          obtain ⟨h1, h2⟩ := lvl_stepK (find_getD hlo.1 rfl) hlo.2 (off_lt hk) (off_lt hk) hy
          exact ⟨h1 _ _ _ s rfl fun c ↦ by
            rw [← hkr c, List.getD_eq_getElem?_getD, List.getElem?_map]
            simp [dlKr, nodeKeyVs, dlKeyVl, List.getD_eq_getElem?_getD], h2⟩)
        (fun hne => by simpa [nameS] using guardPow_soundC hg hall (by omega) hne)
    -- the nodes
    have hnode : ∀ s : Digest, KeyIs rd (σ (.n 1)) s → ∀ j < k, ∀ p < 2 ^ (k - j - 1),
        node rd (σ (.n 0)) k (j + 1) p =
          nodeCellsK s (node rd (σ (.n 0)) k j (2 * p)) (node rd (σ (.n 0)) k j (2 * p + 1)) := by
      intro s hks j hj p hp
      obtain ⟨hld, -, h0, h1⟩ := hlvl s hks j hj p hp
      rw [ptr_pow] at hld h0 h1
      rw [ptr_pow] at h0 h1
      have m : ∀ i < 4, memAt rd (σ (.n 0) * gen ^ (off k j + 4 * p)) i =
          memAt rd (σ (.n 0)) (off k j + 4 * p + i) := fun i hi => by
        obtain ⟨-, e1, e2⟩ := shift_load (hld i hi)
        rw [e2, ← e1]
      obtain ⟨-, e0, -⟩ := shift_load h0
      obtain ⟨-, e1, -⟩ := shift_load h1
      rw [m 0 (by omega), m 1 (by omega), m 2 (by omega), m 3 (by omega)] at e0 e1
      simp only [add_zero] at e0
      simp only [node]
      rw [e0, e1]
      have a0 : off k j + 2 * (2 * p) = off k j + 4 * p + 0 := by ring
      have a1 : off k j + 2 * (2 * p) + 1 = off k j + 4 * p + 1 := by ring
      have a2 : off k j + 2 * (2 * p + 1) = off k j + 4 * p + 2 := by ring
      have a3 : off k j + 2 * (2 * p + 1) + 1 = off k j + 4 * p + 3 := by ring
      rw [a1, a3, a0, a2]
      simp only [add_zero]
    -- the leaves
    have hleaves : (List.range (2 ^ k)).map (node rd (σ (.n 0)) k 0) =
        (List.range (2 ^ k)).map fun i =>
          (memAt rd (σ (.n 0)) (2 * i), memAt rd (σ (.n 0)) (2 * i + 1)) := by
      simp [node, off_zero]
    have hread : ∀ s : Digest, KeyIs rd (σ (.n 1)) s → ∀ c < 2 * 2 ^ k,
        LoadHolds rd (σ (.n 0)) c (memAt rd (σ (.n 0)) c) ∧
          (0 < k → IsCanonical128 (memAt rd (σ (.n 0)) c)) := by
      intro s hks c hc
      rcases Nat.eq_zero_or_pos k with rfl | hk0
      · have l0 := load_sound hr0 hat
        have l1 := load_sound hr1 hat
        simp only [pow_zero, mul_one] at l0 l1
        refine ⟨?_, fun h => absurd h (by omega)⟩
        rcases (show c = 0 ∨ c = 1 by omega) with rfl | rfl
        · rw [memAt_of_load l0]; exact l0
        · rw [memAt_of_load l1]; exact l1
      · obtain ⟨hld, hcan, -, -⟩ := hlvl s hks 0 hk0 (c / 4) (by
          have : 2 ^ k = 2 * 2 ^ (k - 0 - 1) := by rw [← pow_succ']; congr 1; omega
          omega)
        rw [ptr_pow, off_zero, zero_add] at hld
        rw [ptr_pow, off_zero, zero_add] at hcan
        obtain ⟨hl, e1, e2⟩ := shift_load (hld (c % 4) (by omega))
        rw [show 4 * (c / 4) + c % 4 = c by omega] at hl e1
        refine ⟨by rw [e1]; exact hl, fun _ => ?_⟩
        have := hcan _ (List.mem_map.mpr ⟨c % 4, List.mem_range.mpr (by omega), rfl⟩)
        rw [← e1] at this
        exact this
    refine ⟨(List.range (2 ^ k)).map (node rd (σ (.n 0)) k 0), by simp, fun s hks => ⟨?_, ?_, ?_⟩⟩
    · rw [hleaves, pairCells_range (memAt rd (σ (.n 0)))]
      intro c hc
      simp only [List.length_map, List.length_range] at hc
      rw [List.getElem_map, List.getElem_range]
      exact (hread s hks c hc).1
    · intro hk0 x hx
      rw [hleaves, pairCells_range (memAt rd (σ (.n 0)))] at hx
      obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hx
      exact (hread s hks c (List.mem_range.mp hc)).2 hk0
    · rw [← hret, levels_rootK (hnode s hks)]
      simp only [node, off_self, mul_zero, add_zero]
      rw [show 4 * 2 ^ k - 4 + 1 = 4 * 2 ^ k - 3 by have := Nat.one_le_two_pow (n := k); omega,
        memAt_of_load (load_sound hr0 hat), memAt_of_load (load_sound hr1 hat)]
  · exact absurd hdl (by simp)

end
end LeanVM.SaltedGuest.B1.Da
