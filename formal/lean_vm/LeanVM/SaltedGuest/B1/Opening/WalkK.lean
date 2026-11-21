/-
  LeanVM.SaltedGuest.B1.Opening.WalkK

  The salted `walk_path`: from a node and a position's windows, the path climbs by hinted siblings
  under the key into the cap leaf, whose parent it flags; its template and its soundness.
-/

module

public import LeanVM.SaltedGuest.B1.Merkle.ClimbK
public import LeanVM.Guest.B1.Opening.WalkPath

/-!
# `walk_path` under the key

`walk_path__L{pd}_L{cd}(n0, n1, wins, cap, flags)` of the salted guest is the deployed one with
every level hashed under the key: it first loads the key's state from the cap's buffer after its
`4·2^cd` cells into the run `kr` (`node_key`, values `5 .. 21`, `wkKeyT`), and each level
(`walk_window`'s `keyed_node`) XORs the running node and the sibling into the run's first four
cells (four `add`s) before its `KECCAK`. So its expansion is the deployed template's with the
children at `22` (`wkCh`) in place of `5`, six values a level in place of three (`wkStepT`), and
the key run in front (`wpBodyK`); the window words, the dispatch, the padding constants it no
longer reads and the cap leaf are as deployed.

`WalkOpensK rd s pd cd wins cap flags q leaf`: the windows read, and for some siblings the cap
leaf's cells hold `climbK s leaf q sibs` and the parent's flag is `1`. `WalkSoundK walk pd cd`: a
call of `walk` on the leaf's halves, its windows (when read) the position's, with the key of `s`
in the cap's buffer, gives `WalkOpensK`. `WalkFnK.sound`: a function whose body is `wpBodyK` is
`WalkSoundK`.
-/

namespace LeanVM.SaltedGuest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Guest.B1 LeanVM.Guest.B1.Oq LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Guest.Value.Keccak LeanVM.Protocol.Verifier

@[expose] public section

variable {rd : Reader} {σ : Val}

/-! ## The template -/

/-- The key run's values, in the order a level's `KECCAK` reads them after its four message
cells: cells `4` and `8` with the padding added. -/
def wkKr : List ℕ := [11, 12, 13, 14, 17, 18, 19, 20, 21]

/-- The value the key's cell `c` is loaded into. -/
def wkKl : List ℕ := [5, 6, 7, 8, 9, 12, 13, 14, 15, 18, 19, 20, 21]

/-- The key run (`node_key`): the key's thirteen cells loaded from `cap` at `4·2^cd + c`, `1` added
to cell `4`, `0x80 << 56` to cell `8`. -/
def wkKeyT (cd : ℕ) : List Stmt :=
  let o := 4 * 2 ^ cd
  [.atom (.load (.n 5) (.n 3) o), .atom (.load (.n 6) (.n 3) (o + 1)),
    .atom (.load (.n 7) (.n 3) (o + 2)), .atom (.load (.n 8) (.n 3) (o + 3)),
    .atom (.load (.n 9) (.n 3) (o + 4)), .atom (.const (.n 10) (word 1 0 0)),
    .atom (.add (.n 11) (.n 9) (.n 10)), .atom (.load (.n 12) (.n 3) (o + 5)),
    .atom (.load (.n 13) (.n 3) (o + 6)), .atom (.load (.n 14) (.n 3) (o + 7)),
    .atom (.load (.n 15) (.n 3) (o + 8)), .atom (.const (.n 16) w63),
    .atom (.add (.n 17) (.n 15) (.n 16)), .atom (.load (.n 18) (.n 3) (o + 9)),
    .atom (.load (.n 19) (.n 3) (o + 10)), .atom (.load (.n 20) (.n 3) (o + 11)),
    .atom (.load (.n 21) (.n 3) (o + 12))]

/-- Window `i`'s first value: its window word, then (window `0`) the padding run, then the hoisted
`0x80`, then the arms, six values a level. The children hinted at `ch .. ch + 4pd - 1` come
first. -/
def wkWk (s : Oq) (ch : ℕ) : ℕ → ℕ
  | 0 => ch + 4 * s.pd
  | i + 1 => wkWk s ch i + 4 + oqWo i + 6 * oqWw s i * 2 ^ oqWw s i

/-- The match targets of window `i`: the node after its levels. -/
def wkWT (s : Oq) (ch i : ℕ) : ℕ := wkWk s ch i + 2 + oqWo i + 6 * oqWw s i

/-- Cell `c` of the node window `i` starts from: the node the walk is given at `kL, kL + 1`, then
the previous window's targets; window `oqNpw` is the cap leaf. -/
def wkNd (s : Oq) (kL ch i c : ℕ) : ℕ :=
  if i = 0 then kL + c else wkWT s ch (i - 1) + c

/-- Arm `a`'s first value in window `i` (the first arm's targets follow it). -/
def wkArmK (s : Oq) (ch i a : ℕ) : ℕ :=
  if a = 0 then wkWk s ch i + 2 + oqWo i else wkWk s ch i + 4 + oqWo i + 6 * oqWw s i * a

/-- One level `l` of an arm from `K` (`keyed_node`): the key run's first four cells plus the
running node `n0, n1` and its sibling on the side the bit leaves, then their `KECCAK` with the
rest of the key run. -/
def wkStepT (ch l K n0 n1 : ℕ) (bit : Bool) : List Stmt :=
  [.atom (.add (.n K) (.n 5) (.n (if bit then ch + 4 * l else n0))),
    .atom (.add (.n (K + 1)) (.n 6) (.n (if bit then ch + 4 * l + 1 else n1))),
    .atom (.add (.n (K + 2)) (.n 7) (.n (if bit then n0 else ch + 4 * l + 2))),
    .atom (.add (.n (K + 3)) (.n 8) (.n (if bit then n1 else ch + 4 * l + 3))),
    .atom (.keccak [.n K, .n (K + 1), .n (K + 2), .n (K + 3), .n 11, .n 12, .n 13, .n 14, .n 17,
      .n 18, .n 19, .n 20, .n 21] [.n (K + 4), .n (K + 5)] false false)]

/-- The node before level `r` of arm `a` of window `i`. -/
def wkArmN (s : Oq) (kL ch i a r c : ℕ) : ℕ :=
  if r = 0 then wkNd s kL ch i c else wkArmK s ch i a + 6 * (r - 1) + 4 + c

/-- Arm `a` of window `i` (`walk_window`): its levels, the order bits `a`'s, then the node copied
into the match's targets. -/
def wkArmT (s : Oq) (kL ch i a : ℕ) : List Stmt :=
  ((List.range (oqWw s i)).map fun r ↦ wkStepT ch (6 * i + r) (wkArmK s ch i a + 6 * r)
      (wkArmN s kL ch i a r 0) (wkArmN s kL ch i a r 1) (a.testBit r)).flatten ++
    [.atom (.copy (.n (wkWT s ch i)) (.n (wkArmN s kL ch i a (oqWw s i) 0))),
      .atom (.copy (.n (wkWT s ch i + 1)) (.n (wkArmN s kL ch i a (oqWw s i) 1)))]

/-- Window `i`: its word read, (window `0`) the padding run at `pr`, the hoisted `0x80`, the
dispatch on the word's log. -/
def wkWinT (s : Oq) (bp : V) (pr kL ch i : ℕ) : List Stmt :=
  [.atom (.load (.n (wkWk s ch i)) bp i)] ++ (if i = 0 then oqPadT pr else []) ++
    [.atom (.const (.n (wkWk s ch i + 1 + oqWo i)) (word (2 ^ 63) 0 0)),
      .match_ (.n (wkWk s ch i)) ((List.range (2 ^ oqWw s i)).map (wkArmT s kL ch i))]

/-- The path: the children hinted, the windows. -/
def wkPathT (s : Oq) (bp : V) (pr kL ch : ℕ) : List Stmt :=
  [.atom (.hint (.witness "merkle_children" (.stack ((List.range (4 * s.pd)).map fun j ↦ .n (ch + j)))))] ++
    ((List.range (oqNpw s)).map (wkWinT s bp pr kL ch)).flatten

/-- The cap section's first value. -/
def wkCq (s : Oq) (ch : ℕ) : ℕ := wkWk s ch (oqNpw s)

/-- The cap leaf (`cd ≥ 2`): as deployed (`oqCapT`), from `wkCq`. -/
def wkCapT (s : Oq) (bp cap flags : V) (kL ch : ℕ) : List Stmt :=
  let k := wkCq s ch
  [.atom (.load (.n k) bp (oqNpw s)), .atom (.load (.n (k + 1)) bp (oqNpw s + 1)),
    .atom (.mul (.n (k + 2)) flags (.n (k + 1))), .atom (.const (.n (k + 3)) (word 1 0 0)),
    .atom (.load (.n (k + 3)) (.n (k + 2)) (2 ^ (s.cd - 1))),
    .atom (.mul (.n (k + 4)) (.n (k + 1)) (.n (k + 1))), .atom (.mul (.n (k + 5)) cap (.n (k + 4))),
    .atom (.mul (.n (k + 6)) (.n (k + 5)) (.n (k + 4))), .atom (.mul (.n (k + 7)) (.n k) (.n k)),
    .atom (.mul (.n (k + 8)) (.n (k + 6)) (.n (k + 7))),
    .atom (.load (.n (wkNd s kL ch (oqNpw s) 0)) (.n (k + 8)) (2 ^ (s.cd + 1))),
    .atom (.load (.n (wkNd s kL ch (oqNpw s) 1)) (.n (k + 8)) (2 ^ (s.cd + 1) + 1))]

/-- `walk_path`'s children: after its parameters and the key run. -/
def wkCh : ℕ := 22

/-- `walk_path`'s padding run: after its children and its first window's word. -/
def wkPr (s : Oq) : ℕ := wkCh + 4 * s.pd + 1

/-- **The salted `walk_path__L{pd}_L{cd}`'s body**: the key run, the path from the node `n0, n1`
(`.n 0`, `.n 1`) by the windows at `wins` (`.n 2`), the cap leaf into `cap` (`.n 3`), the flag into
`flags` (`.n 4`). -/
def wpBodyK (s : Oq) : List Stmt :=
  wkKeyT s.cd ++ wkPathT s (.n 2) (wkPr s) 0 wkCh ++ wkCapT s (.n 2) (.n 3) (.n 4) 0 wkCh ++
    [.ret []]

/-! ## Flat pieces -/

theorem wkStepT_atoms (ch l K n0 n1 : ℕ) (bit : Bool) : AllAtoms (wkStepT ch l K n0 n1 bit) := by
  unfold wkStepT; atoms_lit

theorem wkArmT_atoms (s : Oq) (kL ch i a : ℕ) : AllAtoms (wkArmT s kL ch i a) := by
  unfold wkArmT
  exact allAtoms_append (allAtoms_map_flatten fun _ _ => wkStepT_atoms _ _ _ _ _ _) (by atoms_lit)

theorem wkWinT_flat (s : Oq) (bp : V) (pr kL ch i : ℕ) : Flat (wkWinT s bp pr kL ch i) := by
  unfold wkWinT
  refine flat_append (flat_append (flat_of_atoms (by atoms_lit)) ?_) ?_
  · split
    · exact flat_of_atoms (oqPadT_atoms _)
    · exact flat_of_atoms allAtoms_nil
  · intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    · exact Or.inl ⟨_, rfl⟩
    · refine Or.inr ⟨_, _, rfl, fun arm h ↦ ?_⟩
      obtain ⟨a, -, rfl⟩ := List.mem_map.mp h
      exact wkArmT_atoms _ _ _ _ _

theorem wkPathT_flat (s : Oq) (bp : V) (pr kL ch : ℕ) : Flat (wkPathT s bp pr kL ch) :=
  flat_append (flat_of_atoms (by atoms_lit)) (flat_map_flatten fun _ _ => wkWinT_flat _ _ _ _ _ _)

theorem wkCapT_atoms (s : Oq) (bp cap flags : V) (kL ch : ℕ) :
    AllAtoms (wkCapT s bp cap flags kL ch) := by
  unfold wkCapT; atoms_lit

theorem wkKeyT_atoms (cd : ℕ) : AllAtoms (wkKeyT cd) := by
  unfold wkKeyT; atoms_lit

/-! ## The key run -/

/-- The key's cells as the key run loads them. -/
def wkKc (σ : Val) : Fin 13 → E := fun c ↦ σ (.n (wkKl.getD c.val 0))

/-- The key run's values, the key's cells those of `s`. -/
def KeyRun (σ : Val) (s : Digest) : Prop :=
  σ (.n 5) = keyCells s 0 ∧ σ (.n 6) = keyCells s 1 ∧ σ (.n 7) = keyCells s 2 ∧
    σ (.n 8) = keyCells s 3 ∧ σ (.n 11) = keyCells s 4 + word 1 0 0 ∧
    σ (.n 12) = keyCells s 5 ∧ σ (.n 13) = keyCells s 6 ∧ σ (.n 14) = keyCells s 7 ∧
    σ (.n 17) = keyCells s 8 + w63 ∧ σ (.n 18) = keyCells s 9 ∧ σ (.n 19) = keyCells s 10 ∧
    σ (.n 20) = keyCells s 11 ∧ σ (.n 21) = keyCells s 12

/-- **The key run** loads the key's cells from the cap's buffer; with the key of `s` there, its
values are `s`'s key run. -/
theorem wkKey_sound {cd : ℕ} (hA : ∀ a, Stmt.atom a ∈ wkKeyT cd → a.Holds rd σ) {s : Digest}
    (hkey : ∀ c : Fin 13, LoadHolds rd (σ (.n 3)) (4 * 2 ^ cd + c.val) (keyCells s c)) :
    KeyRun σ s := by
  have l (v c : ℕ) (hc : c < 13)
      (h : Stmt.atom (.load (.n v) (.n 3) (4 * 2 ^ cd + c)) ∈ wkKeyT cd) :
      σ (.n v) = keyCells s ⟨c, hc⟩ :=
    loadHolds_unique (hA _ h) (hkey ⟨c, hc⟩)
  have c10 := hA _ (by simp [wkKeyT] : Stmt.atom (.const (.n 10) (word 1 0 0)) ∈ _)
  have c16 := hA _ (by simp [wkKeyT] : Stmt.atom (.const (.n 16) w63) ∈ _)
  have a11 := hA _ (by simp [wkKeyT] : Stmt.atom (.add (.n 11) (.n 9) (.n 10)) ∈ _)
  have a17 := hA _ (by simp [wkKeyT] : Stmt.atom (.add (.n 17) (.n 15) (.n 16)) ∈ _)
  simp only [Atom.Holds] at c10 c16 a11 a17
  refine ⟨l 5 0 (by omega) (by simp [wkKeyT]), l 6 1 (by omega) (by simp [wkKeyT]),
    l 7 2 (by omega) (by simp [wkKeyT]), l 8 3 (by omega) (by simp [wkKeyT]), ?_,
    l 12 5 (by omega) (by simp [wkKeyT]), l 13 6 (by omega) (by simp [wkKeyT]),
    l 14 7 (by omega) (by simp [wkKeyT]), ?_, l 18 9 (by omega) (by simp [wkKeyT]),
    l 19 10 (by omega) (by simp [wkKeyT]), l 20 11 (by omega) (by simp [wkKeyT]),
    l 21 12 (by omega) (by simp [wkKeyT])⟩
  · rw [a11, c10, l 9 4 (by omega) (by simp [wkKeyT])]; rfl
  · rw [a17, c16, l 15 8 (by omega) (by simp [wkKeyT])]; rfl

/-! ## One level -/

/-- **One level of an arm under the key**: the running node `node` at `n0, n1` hashed with the
hinted pair on the other side of the order bit, the pair a digest's cells, the next node at
`K + 4, K + 5`. -/
theorem wkStep_sound {ch l K n0 n1 : ℕ} {bit : Bool} {s : Digest}
    (hA : ∀ a, Stmt.atom a ∈ wkStepT ch l K n0 n1 bit → a.Holds rd σ) (hk : KeyRun σ s)
    {node : Digest} (hnode : (σ (.n n0), σ (.n n1)) = digestHalves node) :
    ∃ sib : Digest,
      (σ (.n (ch + 4 * l + (if bit then 0 else 2))),
        σ (.n (ch + 4 * l + (if bit then 0 else 2) + 1))) = digestHalves sib ∧
      (σ (.n (K + 4)), σ (.n (K + 5))) =
        digestHalves (if bit then hashPairK s sib node else hashPairK s node sib) := by
  obtain ⟨k0, k1, k2, k3, k4, k5, k6, k7, k8, k9, k10, k11, k12⟩ := hk
  have x0 := hA _ (by simp [wkStepT] : Stmt.atom (.add (.n K) (.n 5)
    (.n (if bit then ch + 4 * l else n0))) ∈ _)
  have x1 := hA _ (by simp [wkStepT] : Stmt.atom (.add (.n (K + 1)) (.n 6)
    (.n (if bit then ch + 4 * l + 1 else n1))) ∈ _)
  have x2 := hA _ (by simp [wkStepT] : Stmt.atom (.add (.n (K + 2)) (.n 7)
    (.n (if bit then n0 else ch + 4 * l + 2))) ∈ _)
  have x3 := hA _ (by simp [wkStepT] : Stmt.atom (.add (.n (K + 3)) (.n 8)
    (.n (if bit then n1 else ch + 4 * l + 3))) ∈ _)
  have hK := hA _ (by simp [wkStepT] : Stmt.atom (.keccak [.n K, .n (K + 1), .n (K + 2),
    .n (K + 3), .n 11, .n 12, .n 13, .n 14, .n 17, .n 18, .n 19, .n 20, .n 21]
    [.n (K + 4), .n (K + 5)] false false) ∈ _)
  simp only [Atom.Holds] at x0 x1 x2 x3
  obtain ⟨-, -, O, hKC, hw⟩ := keccak_holds_full hK
  set a0 := σ (.n (if bit then ch + 4 * l else n0))
  set a1 := σ (.n (if bit then ch + 4 * l + 1 else n1))
  set b0 := σ (.n (if bit then n0 else ch + 4 * l + 2))
  set b1 := σ (.n (if bit then n1 else ch + 4 * l + 3))
  have hin : [V.n K, .n (K + 1), .n (K + 2), .n (K + 3), .n 11, .n 12, .n 13, .n 14, .n 17, .n 18,
      .n 19, .n 20, .n 21].map σ = nodeIn s a0 a1 b0 b1 := by
    simp only [List.map_cons, List.map_nil, nodeIn, x0, x1, x2, x3, k0, k1, k2, k3, k4, k5, k6, k7,
      k8, k9, k10, k11, k12]
  rw [hin] at hKC
  have e0 : σ (.n (K + 4)) = O 0 := hw 0 (by simp)
  have e1 : σ (.n (K + 5)) = O 1 := hw 1 (by simp)
  obtain ⟨dl, dr, hl, hr, hp⟩ := hashesPairK_digests (keyed_node hKC)
  rw [← e0, ← e1] at hp
  cases bit
  · simp only [Bool.false_eq_true, ↓reduceIte, a0, a1, b0, b1] at hl hr hp ⊢
    have hdl : dl = node := capDigestScalars_injective (by rw [← hl, ← hnode])
    subst hdl
    exact ⟨dr, by simpa using hr, hp⟩
  · simp only [↓reduceIte, a0, a1, b0, b1] at hl hr hp ⊢
    have hdr : dr = node := capDigestScalars_injective (by rw [← hr, ← hnode])
    subst hdr
    exact ⟨dl, by simpa using hl, hp⟩

/-! ## An arm, a window, the path -/

theorem wkArmT_mem_step {s : Oq} {kL ch i a r : ℕ} (hr : r < oqWw s i) {x : Atom}
    (hx : Stmt.atom x ∈ wkStepT ch (6 * i + r) (wkArmK s ch i a + 6 * r)
      (wkArmN s kL ch i a r 0) (wkArmN s kL ch i a r 1) (a.testBit r)) :
    Stmt.atom x ∈ wkArmT s kL ch i a := by
  unfold wkArmT
  exact List.mem_append_left _
    (List.mem_flatten.mpr ⟨_, List.mem_map.mpr ⟨r, List.mem_range.mpr hr, rfl⟩, hx⟩)

theorem climbK_step {s leaf : Digest} {q : ℕ} {cs : List Digest} {sib : Digest} :
    climbK s leaf q (cs ++ [sib]) = if q.testBit cs.length then hashPairK s sib (climbK s leaf q cs)
      else hashPairK s (climbK s leaf q cs) sib := by
  rw [climbK_snoc, Nat.testBit_eq_decide_div_mod_eq]
  by_cases h : q / 2 ^ cs.length % 2 = 1
  · simp [h]
  · simp [show q / 2 ^ cs.length % 2 = 0 by omega]

/-- **An arm under the key** (`walk_window`): with its order bits the position's from level `6i`
and the node it starts from `climbK s leaf q sibs0` (`6i` siblings), its levels' pairs off the
walk's side hold siblings `sibs` and the node copied into the match's targets is
`climbK s leaf q (sibs0 ++ sibs)`. -/
theorem wkArm_sound {s : Oq} {kL ch i a : ℕ} {sd : Digest}
    (hA : ∀ x, Stmt.atom x ∈ wkArmT s kL ch i a → x.Holds rd σ) (hk : KeyRun σ sd) {q : ℕ}
    (hbits : ∀ r < oqWw s i, a.testBit r = q.testBit (6 * i + r)) {leaf : Digest}
    {sibs0 : List Digest} (hl0 : sibs0.length = 6 * i)
    (hnode : (σ (.n (wkNd s kL ch i 0)), σ (.n (wkNd s kL ch i 1))) =
      digestHalves (climbK sd leaf q sibs0)) :
    ∃ sibs : List Digest, sibs.length = oqWw s i ∧
      (∀ r < oqWw s i, SibAt σ ch q (6 * i + r) (sibs.getD r default)) ∧
      (σ (.n (wkWT s ch i)), σ (.n (wkWT s ch i + 1))) =
        digestHalves (climbK sd leaf q (sibs0 ++ sibs)) := by
  suffices h : ∀ m ≤ oqWw s i, ∃ sibs : List Digest, sibs.length = m ∧
      (∀ r < m, SibAt σ ch q (6 * i + r) (sibs.getD r default)) ∧
      (σ (.n (wkArmN s kL ch i a m 0)), σ (.n (wkArmN s kL ch i a m 1))) =
        digestHalves (climbK sd leaf q (sibs0 ++ sibs)) by
    obtain ⟨sibs, hl, hs, hn⟩ := h _ le_rfl
    have c0 := hA _ (by simp [wkArmT] : Stmt.atom (.copy (.n (wkWT s ch i))
      (.n (wkArmN s kL ch i a (oqWw s i) 0))) ∈ _)
    have c1 := hA _ (by simp [wkArmT] : Stmt.atom (.copy (.n (wkWT s ch i + 1))
      (.n (wkArmN s kL ch i a (oqWw s i) 1))) ∈ _)
    simp only [Atom.Holds] at c0 c1
    exact ⟨sibs, hl, hs, by rw [c0, c1, hn]⟩
  intro m hm
  induction m with
  | zero => exact ⟨[], rfl, fun r hr ↦ absurd hr (by omega), by simpa [wkArmN] using hnode⟩
  | succ m ih =>
    obtain ⟨sibs, hl, hs, hn⟩ := ih (by omega)
    obtain ⟨sib, hsib, hnext⟩ := wkStep_sound (fun x hx ↦ hA x (wkArmT_mem_step (by omega) hx))
      hk hn
    have hb := hbits m (by omega)
    refine ⟨sibs ++ [sib], by simp [hl], fun r hr ↦ ?_, ?_⟩
    · by_cases hr' : r < m
      · have := hs r hr'
        rwa [List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega),
          ← List.getD_eq_getElem?_getD]
      · obtain rfl : r = m := by omega
        have e : (sibs ++ [sib]).getD r default = sib := by
          simp [List.getD_eq_getElem?_getD, hl]
        rw [e, SibAt, sibOff, ← hb]
        exact hsib
    · have e0 : wkArmN s kL ch i a (m + 1) 0 = wkArmK s ch i a + 6 * m + 4 := by
        simp [wkArmN]
      have e1 : wkArmN s kL ch i a (m + 1) 1 = wkArmK s ch i a + 6 * m + 5 := by
        simp [wkArmN]
      rw [e0, e1, hnext, ← List.append_assoc, climbK_step, List.length_append, hl0, hl, ← hb]

/-- **Window `i` under the key**: its word `g^v`, `v` below its arms' count, with `v`'s bits the
position's from level `6i`: arm `v` climbs. -/
theorem wkWin_sound {s : Oq} {bp : V} {pr kL ch i : ℕ} {sd : Digest}
    (hA : BlockOk rd σ (wkWinT s bp pr kL ch i)) (hk : KeyRun σ sd) {q v : ℕ}
    (hw : σ (.n (wkWk s ch i)) = gen ^ v) (hv : v < 2 ^ oqWw s i)
    (hbits : ∀ r < oqWw s i, v.testBit r = q.testBit (6 * i + r)) {leaf : Digest}
    {sibs0 : List Digest} (hl0 : sibs0.length = 6 * i)
    (hnode : (σ (.n (wkNd s kL ch i 0)), σ (.n (wkNd s kL ch i 1))) =
      digestHalves (climbK sd leaf q sibs0)) :
    ∃ sibs : List Digest, sibs.length = oqWw s i ∧
      (∀ r < oqWw s i, SibAt σ ch q (6 * i + r) (sibs.getD r default)) ∧
      (σ (.n (wkWT s ch i)), σ (.n (wkWT s ch i + 1))) =
        digestHalves (climbK sd leaf q (sibs0 ++ sibs)) := by
  have hm := hA _ (by simp [wkWinT] : Stmt.match_ (.n (wkWk s ch i))
    ((List.range (2 ^ oqWw s i)).map (wkArmT s kL ch i)) ∈ _)
  obtain ⟨j, hj, hx, harm⟩ := hm
  have h64 : 2 ^ oqWw s i ≤ 2 ^ 6 := Nat.pow_le_pow_right (by norm_num) (oqWw_le s i)
  simp only [List.length_map, List.length_range] at hj
  have hjv : j = v := match_arm_of_gen_pow (by omega) (by omega) hx hw
  subst hjv
  simp only [List.getElem_map, List.getElem_range] at harm
  exact wkArm_sound harm hk hbits hl0 hnode

theorem wkPathT_mem_win {s : Oq} {bp : V} {pr kL ch i : ℕ} (hi : i < oqNpw s) {x : Stmt}
    (hx : x ∈ wkWinT s bp pr kL ch i) : x ∈ wkPathT s bp pr kL ch := by
  unfold wkPathT
  exact List.mem_append_right _
    (List.mem_flatten.mpr ⟨_, List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩, hx⟩)

theorem wkNd_succ (s : Oq) (kL ch i c : ℕ) : wkNd s kL ch (i + 1) c = wkWT s ch i + c := by
  simp [wkNd]

/-- **The path below the cap under the key**: with each window's word `g^v`, `v`'s bits the
position's from level `6i`, and the leaf's digest the first node, the hinted pairs off the walk's
side hold siblings `sibs` and the node reached is `climbK s leaf q sibs`. -/
theorem wkPath_sound {s : Oq} {bp : V} {pr kL ch q : ℕ} {sd leaf : Digest}
    (hA : BlockOk rd σ (wkPathT s bp pr kL ch)) (hk : KeyRun σ sd)
    (hwin : ∀ i < oqNpw s, ∃ v < 2 ^ oqWw s i, σ (.n (wkWk s ch i)) = gen ^ v ∧
      ∀ r < oqWw s i, v.testBit r = q.testBit (6 * i + r))
    (hleaf : (σ (.n (wkNd s kL ch 0 0)), σ (.n (wkNd s kL ch 0 1))) = digestHalves leaf) :
    ∃ sibs : List Digest, sibs.length = s.pd ∧
      (∀ l < s.pd, SibAt σ ch q l (sibs.getD l default)) ∧
      (σ (.n (wkNd s kL ch (oqNpw s) 0)), σ (.n (wkNd s kL ch (oqNpw s) 1))) =
        digestHalves (climbK sd leaf q sibs) := by
  suffices h : ∀ m ≤ oqNpw s, ∃ sibs : List Digest, sibs.length = min (6 * m) s.pd ∧
      (∀ l < min (6 * m) s.pd, SibAt σ ch q l (sibs.getD l default)) ∧
      (σ (.n (wkNd s kL ch m 0)), σ (.n (wkNd s kL ch m 1))) =
        digestHalves (climbK sd leaf q sibs) by
    obtain ⟨sibs, hl, hs, hn⟩ := h _ le_rfl
    have e : min (6 * oqNpw s) s.pd = s.pd := by unfold oqNpw; omega
    rw [e] at hl hs
    exact ⟨sibs, hl, hs, hn⟩
  intro m hm
  induction m with
  | zero => exact ⟨[], by simp, fun l hl ↦ absurd hl (by omega), by rw [climbK_nil]; exact hleaf⟩
  | succ m ih =>
    obtain ⟨sibs, hl, hs, hn⟩ := ih (by omega)
    have hm6 : min (6 * m) s.pd = 6 * m := by unfold oqNpw at hm; omega
    rw [hm6] at hl hs
    obtain ⟨v, hv, hw, hb⟩ := hwin m (by omega)
    obtain ⟨sw, hsl, hss, hsn⟩ := wkWin_sound (hA.mono fun x hx ↦ wkPathT_mem_win (by omega) hx)
      hk hw hv hb hl hn
    have hww : 6 * m + oqWw s m = min (6 * (m + 1)) s.pd := by
      unfold oqWw; unfold oqNpw at hm ⊢; split <;> omega
    refine ⟨sibs ++ sw, by simp [hl, hsl, hww], fun l hl' ↦ ?_, ?_⟩
    · by_cases h : l < 6 * m
      · have := hs l h
        rwa [List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega),
          ← List.getD_eq_getElem?_getD]
      · have := hss (l - 6 * m) (by omega)
        rw [show 6 * m + (l - 6 * m) = l by omega] at this
        rwa [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega), hl,
          ← List.getD_eq_getElem?_getD]
    · rw [wkNd_succ, wkNd_succ, Nat.add_zero]; exact hsn

/-! ## The cap leaf -/

/-- **The cap leaf** (`walk_path`'s end): as deployed (`oqCap_sound`). -/
theorem wkCap_sound {s : Oq} (hcd : 1 ≤ s.cd) {bp cap flags : V} {kL ch q : ℕ}
    (hA : ∀ a, Stmt.atom a ∈ wkCapT s bp cap flags kL ch → a.Holds rd σ)
    (hq : q < 2 ^ (s.pd + s.cd))
    (hwin : ∀ i v, LoadHolds rd (σ bp) i v → i < qwN (s.pd + s.cd) s.cd →
      v = gen ^ qwVal (s.pd + s.cd) s.cd q i) :
    LoadHolds rd (σ flags) (2 ^ (s.cd - 1) + q / 2 ^ (s.pd + 1)) 1 ∧
      LoadHolds rd (σ cap) (2 * (2 ^ s.cd + q / 2 ^ s.pd)) (σ (.n (wkNd s kL ch (oqNpw s) 0))) ∧
      LoadHolds rd (σ cap) (2 * (2 ^ s.cd + q / 2 ^ s.pd) + 1)
        (σ (.n (wkNd s kL ch (oqNpw s) 1))) := by
  set k := wkCq s ch with hk
  have hN : oqNpw s + 1 < qwN (s.pd + s.cd) s.cd := by
    simp [qwN, qwNp, oqNpw]
  have c0 := hA _ (by simp [wkCapT, ← hk] : Stmt.atom (.load (.n k) bp (oqNpw s)) ∈ _)
  have c1 := hA _ (by simp [wkCapT, ← hk] : Stmt.atom (.load (.n (k + 1)) bp (oqNpw s + 1)) ∈ _)
  have c2 := hA _ (by simp [wkCapT, ← hk] : Stmt.atom (.mul (.n (k + 2)) flags (.n (k + 1))) ∈ _)
  have c3 := hA _ (by simp [wkCapT, ← hk] : Stmt.atom (.const (.n (k + 3)) (word 1 0 0)) ∈ _)
  have c4 := hA _ (by simp [wkCapT, ← hk] :
    Stmt.atom (.load (.n (k + 3)) (.n (k + 2)) (2 ^ (s.cd - 1))) ∈ _)
  have c5 := hA _ (by simp [wkCapT, ← hk] :
    Stmt.atom (.mul (.n (k + 4)) (.n (k + 1)) (.n (k + 1))) ∈ _)
  have c6 := hA _ (by simp [wkCapT, ← hk] : Stmt.atom (.mul (.n (k + 5)) cap (.n (k + 4))) ∈ _)
  have c7 := hA _ (by simp [wkCapT, ← hk] :
    Stmt.atom (.mul (.n (k + 6)) (.n (k + 5)) (.n (k + 4))) ∈ _)
  have c8 := hA _ (by simp [wkCapT, ← hk] : Stmt.atom (.mul (.n (k + 7)) (.n k) (.n k)) ∈ _)
  have c9 := hA _ (by simp [wkCapT, ← hk] :
    Stmt.atom (.mul (.n (k + 8)) (.n (k + 6)) (.n (k + 7))) ∈ _)
  have c10 := hA _ (by simp [wkCapT, ← hk] :
    Stmt.atom (.load (.n (wkNd s kL ch (oqNpw s) 0)) (.n (k + 8)) (2 ^ (s.cd + 1))) ∈ _)
  have c11 := hA _ (by simp [wkCapT, ← hk] :
    Stmt.atom (.load (.n (wkNd s kL ch (oqNpw s) 1)) (.n (k + 8)) (2 ^ (s.cd + 1) + 1)) ∈ _)
  simp only [Atom.Holds] at c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11
  set Q := q / 2 ^ (s.pd + 1) with hQdef
  set b : ℕ := if q.testBit s.pd then 1 else 0 with hbdef
  have hwb : σ (.n k) = gen ^ b := by
    rw [hwin _ _ c0 (by omega), oqNpw_eq, qwVal_capBit]
  have hwq : σ (.n (k + 1)) = gen ^ Q := by
    rw [hwin _ _ c1 hN, oqNpw_eq, qwVal_capIdx hcd hq]
  have hz8 : σ (.n (k + 8)) = σ cap * gen ^ (4 * Q + 2 * b) := by
    rw [c9, c7, c6, c5, c8, hwb, hwq, ← pow_add, ← pow_add, mul_assoc, ← pow_add, mul_assoc,
      ← pow_add]
    congr 2; ring
  have hsplit : q / 2 ^ s.pd = 2 * Q + b := by
    rw [hQdef, hbdef, Nat.testBit_eq_decide_div_mod_eq, pow_succ, ← Nat.div_div_eq_div_mul]
    by_cases h : q / 2 ^ s.pd % 2 = 1
    · simp [h]; omega
    · simp [h]; omega
  refine ⟨?_, ?_, ?_⟩
  · rw [c2, hwq, c3, word_one, loadHolds_mul_gen_pow, add_comm] at c4
    exact c4
  · rw [hz8, loadHolds_mul_gen_pow] at c10
    rw [hsplit, show 2 * (2 ^ s.cd + (2 * Q + b)) = 4 * Q + 2 * b + 2 ^ (s.cd + 1) by
      rw [pow_succ]; ring]
    exact c10
  · rw [hz8, loadHolds_mul_gen_pow] at c11
    rw [hsplit, show 2 * (2 ^ s.cd + (2 * Q + b)) + 1 = 4 * Q + 2 * b + (2 ^ (s.cd + 1) + 1) by
      rw [pow_succ]; ring]
    exact c11

/-! ## The walk -/

theorem wkPathT_mem_load {s : Oq} {bp : V} {pr kL ch i : ℕ} (hi : i < oqNpw s) :
    Stmt.atom (.load (.n (wkWk s ch i)) bp i) ∈ wkPathT s bp pr kL ch :=
  wkPathT_mem_win hi (by simp [wkWinT])

/-- **The walk under the key reads each of its position's windows.** -/
theorem wkWalk_winLoads {s : Oq} {bp cap flags : V} {pr kL ch : ℕ}
    (hPa : BlockOk rd σ (wkPathT s bp pr kL ch))
    (hC : ∀ a, Stmt.atom a ∈ wkCapT s bp cap flags kL ch → a.Holds rd σ) :
    ∀ i < qwN (s.pd + s.cd) s.cd, ∃ v, LoadHolds rd (σ bp) i v := by
  intro i hi
  rw [qwN_eq] at hi
  by_cases h1 : i < oqNpw s
  · exact ⟨_, hPa.atom (wkPathT_mem_load h1)⟩
  by_cases h2 : i = oqNpw s
  · subst h2
    exact ⟨_, hC _ (by simp [wkCapT] : Stmt.atom (.load (.n (wkCq s ch)) bp (oqNpw s)) ∈ _)⟩
  obtain rfl : i = oqNpw s + 1 := by omega
  exact ⟨_, hC _ (by simp [wkCapT] :
    Stmt.atom (.load (.n (wkCq s ch + 1)) bp (oqNpw s + 1)) ∈ _)⟩

/-- **What a walk under the key gives** at the position `q` from the node `leaf`: its windows
read, and for some `pd` siblings the parent's flag set and the cap leaf's cells holding the node
reached by the keyed climb. -/
def WalkOpensK (rd : Reader) (sd : Digest) (pd cd : ℕ) (wins cap flags : E) (q : ℕ)
    (leaf : Digest) : Prop :=
  (∀ i < qwN (pd + cd) cd, LoadHolds rd wins i (gen ^ qwVal (pd + cd) cd q i)) ∧
    ∃ sibs : List Digest, sibs.length = pd ∧
      LoadHolds rd flags (2 ^ (cd - 1) + q / 2 ^ (pd + 1)) 1 ∧
      LoadHolds rd cap (2 * (2 ^ cd + q / 2 ^ pd)) (digestHalves (climbK sd leaf q sibs)).1 ∧
      LoadHolds rd cap (2 * (2 ^ cd + q / 2 ^ pd) + 1) (digestHalves (climbK sd leaf q sibs)).2

/-- **`walk` is a sound walk under the key of `pd` levels below a cap of depth `cd`**: a call on
the halves of `leaf`, its windows (when read) those of `q < 2^(pd + cd)`, the key of `sd` in the
cap's buffer after its `4·2^cd` cells, returns nothing and opens. -/
def WalkSoundK (walk : String) (pd cd : ℕ) : Prop :=
  ∀ (rd : Reader) (n0 n1 wins cap flags : E) (rets : List E),
    SaltedGuest.coreProgram.Rel rd walk [n0, n1, wins, cap, flags] rets →
    ∀ (sd leaf : Digest) (q : ℕ), (n0, n1) = digestHalves leaf → q < 2 ^ (pd + cd) →
      (∀ i v, LoadHolds rd wins i v → i < qwN (pd + cd) cd → v = gen ^ qwVal (pd + cd) cd q i) →
      (∀ c : Fin 13, LoadHolds rd cap (4 * 2 ^ cd + c.val) (keyCells sd c)) →
      rets = [] ∧ WalkOpensK rd sd pd cd wins cap flags q leaf

theorem wpBodyK_eq (s : Oq) :
    wpBodyK s = (wkKeyT s.cd ++ wkPathT s (.n 2) (wkPr s) 0 wkCh ++
      wkCapT s (.n 2) (.n 3) (.n 4) 0 wkCh) ++ [.ret []] := by
  simp [wpBodyK]

/-- **A frame of a walk under the key**: on the halves of `leaf`, its windows (when read) those of
`q < 2^(pd + cd)`, the key of `sd` in the cap's buffer, it returns nothing, reads the windows, its
children cells off the walk's side hold siblings, and the cap leaf and the flag are written. -/
theorem wpK_frame_sound {s : Oq} (hcd : 1 ≤ s.cd) {C : CallRel} {τ : Val}
    {n0 n1 wins cap flags : E} {rets : List E}
    (hpar : [V.n 0, .n 1, .n 2, .n 3, .n 4].map τ = [n0, n1, wins, cap, flags])
    (h : Stmt.HoldsList C rd τ (wpBodyK s) False (fun rs ↦ rs = rets))
    {sd leaf : Digest} {q : ℕ} (hleaf : (n0, n1) = digestHalves leaf) (hq : q < 2 ^ (s.pd + s.cd))
    (hwin : ∀ i v, LoadHolds rd wins i v → i < qwN (s.pd + s.cd) s.cd →
      v = gen ^ qwVal (s.pd + s.cd) s.cd q i)
    (hkey : ∀ c : Fin 13, LoadHolds rd cap (4 * 2 ^ s.cd + c.val) (keyCells sd c)) :
    rets = [] ∧ (∀ i < qwN (s.pd + s.cd) s.cd, LoadHolds rd wins i (gen ^ qwVal (s.pd + s.cd) s.cd q i)) ∧
      ∃ sibs : List Digest, sibs.length = s.pd ∧ (∀ l < s.pd, SibAt τ wkCh q l (sibs.getD l default)) ∧
        LoadHolds rd flags (2 ^ (s.cd - 1) + q / 2 ^ (s.pd + 1)) 1 ∧
        LoadHolds rd cap (2 * (2 ^ s.cd + q / 2 ^ s.pd)) (digestHalves (climbK sd leaf q sibs)).1 ∧
        LoadHolds rd cap (2 * (2 ^ s.cd + q / 2 ^ s.pd) + 1)
          (digestHalves (climbK sd leaf q sibs)).2 := by
  simp only [List.map_cons, List.map_nil, List.cons.injEq] at hpar
  obtain ⟨rfl, rfl, rfl, rfl, rfl, -⟩ := hpar
  rw [wpBodyK_eq, holdsList_append, holdsList_flat (flat_append (flat_append
    (flat_of_atoms (wkKeyT_atoms _)) (wkPathT_flat _ _ _ _ _))
    (flat_of_atoms (wkCapT_atoms _ _ _ _ _ _)))] at h
  obtain ⟨hA, hret⟩ := h
  simp only [Stmt.HoldsList, Stmt.Holds, List.map_nil] at hret
  have hKy : ∀ a, Stmt.atom a ∈ wkKeyT s.cd → a.Holds rd τ :=
    fun a ha ↦ BlockOk.atom hA (List.mem_append_left _ (List.mem_append_left _ ha))
  have hPa : BlockOk rd τ (wkPathT s (.n 2) (wkPr s) 0 wkCh) :=
    BlockOk.mono hA fun x hx ↦ List.mem_append_left _ (List.mem_append_right _ hx)
  have hC : ∀ a, Stmt.atom a ∈ wkCapT s (.n 2) (.n 3) (.n 4) 0 wkCh → a.Holds rd τ :=
    fun a ha ↦ BlockOk.atom hA (List.mem_append_right _ ha)
  have hk := wkKey_sound hKy hkey
  obtain ⟨sibs, hsl, hsib, hnd⟩ := wkPath_sound hPa hk (q := q) (fun i hi ↦
    ⟨_, (qwVal_path hi q).1, hwin _ _ (hPa.atom (wkPathT_mem_load hi)) (by rw [qwN_eq]; omega),
      (qwVal_path hi q).2⟩) (by simpa [wkNd] using hleaf)
  obtain ⟨hflag, hc0, hc1⟩ := wkCap_sound hcd hC hq hwin
  rw [show τ (.n (wkNd s 0 wkCh (oqNpw s) 0)) = (digestHalves (climbK sd leaf q sibs)).1 by
    rw [← hnd]] at hc0
  rw [show τ (.n (wkNd s 0 wkCh (oqNpw s) 1)) = (digestHalves (climbK sd leaf q sibs)).2 by
    rw [← hnd]] at hc1
  refine ⟨hret.symm, fun i hi ↦ ?_, sibs, hsl, hsib, hflag, hc0, hc1⟩
  obtain ⟨v, hv⟩ := wkWalk_winLoads hPa hC i hi
  rw [← hwin i v hv hi]
  exact hv

/-- **`walk` is the salted `walk_path__L{pd}_L{cd}`**: a function of five parameters whose body is
the keyed template. -/
def WalkFnK (walk : String) (pd cd : ℕ) : Prop :=
  ∃ fn : Fn, SaltedGuest.coreProgram.find? walk = some fn ∧
    fn.params = [.n 0, .n 1, .n 2, .n 3, .n 4] ∧ fn.body = wpBodyK ⟨0, 0, pd, cd⟩

/-- **A salted `walk_path` specialization is a sound walk under the key.** -/
theorem WalkFnK.sound {walk : String} {pd cd : ℕ} (hcd : 1 ≤ cd)
    (hW : WalkFnK walk pd cd) : WalkSoundK walk pd cd := by
  intro rd n0 n1 wins cap flags rets h sd leaf q hleaf hq hwin hkey
  obtain ⟨fn, hf, hp, hb⟩ := hW
  rw [rel_iff_sem hf, hb, hp] at h
  obtain ⟨τ, hpar, h⟩ := h
  obtain ⟨hr, hl, sibs, hsl, -, hfl, h0, h1⟩ :=
    wpK_frame_sound (s := ⟨0, 0, pd, cd⟩) hcd hpar h hleaf hq hwin hkey
  exact ⟨hr, hl, sibs, hsl, hfl, h0, h1⟩

end
end LeanVM.SaltedGuest.B1
