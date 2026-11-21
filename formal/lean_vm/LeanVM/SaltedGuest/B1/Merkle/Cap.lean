/-
  LeanVM.SaltedGuest.B1.Merkle.Cap

  B1 for the salted `verify_merkle_cap`: the template of its expansion at every cap depth, and its
  meaning under the key, soundly.
-/

module

public import LeanVM.SaltedGuest.B1.Keyed
public import LeanVM.SaltedGuest.CoreNames

/-!
# `verify_merkle_cap` under the key

`verify_merkle_cap(cap, flags, depth)` of the salted guest hashes every node of the cap with the
keyed hash: the key's state sits in the cap's buffer after its `4L` cells (`L = 2^depth` leaves),
where `level_queries` computes it, and `node_key` loads it into the run `kr` (cell `4` plus the
padding's first byte, cell `8` plus its last bit), on which each node's `KECCAK` XORs its
children's four cells (`keyed_node`). With `L` leaves the expansion of `verify_merkle_cap__L{D}`
is `mcBodyS L`:

* the key run, values `2 .. 18` (`mcKeyT`): the key's thirteen cells loaded from the cap at
  `4L + c`, `1` added to cell `4` (values `6`, `7`, `8`) and `0x80 << 56` to cell `8` (values `12`,
  `13`, `14`);
* the cap's cells `2 .. 4L - 1` loaded into the values `19 ..` (node `k`'s cells are the values
  `17 + 2k`, `18 + 2k`);
* the root's message cells (`mcXs`: the key's first four cells plus its children's) and its
  `KECCAK` (`mcInsS`, `mcOutsS`);
* node `k = 2 .. L - 1` (`mcNodeS`, its values from `mcBaseS L k`): its message cells, its flag
  loaded, then on a zero flag its children's flags pinned to zero (when its children are internal,
  `2k < L`), else its `KECCAK`;
* the root's cells returned.

`MeaningCapK L`: the key's cells, the cap's cells and the flags are in memory, and under every seed
`s` whose key's cells they are (`keyCells s`), the root and every flagged internal node hash their
children (`HashesPairK s`); `verify_merkle_cap_sound_holds`: the seven deployed depths' relation
gives it.
-/

namespace LeanVM.SaltedGuest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Guest.B1 LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Guest.Value.Keccak

@[expose] public section

variable {C : CallRel} {rd : Reader} {σ : Val}

/-! ## The meaning -/

/-- **`verify_merkle_cap(cap, flags, D)` under the key**, `L = 2^D` leaves: the key's cells
`kc c` at `4L + c` of the cap, the cap's cells `cell k`, `2 ≤ k < 4L`, the flags `fl k` of the
internal nodes `2 ≤ k < L`, in memory and in `K`; under every seed whose key's cells `kc` are, the
root and every flagged internal node hash their children; an unflagged internal node whose children
are internal has their flags zero; the function returns the root's cells. -/
def MeaningCapK (L : ℕ) (rd : Reader) : List E → List E → Prop
  | [cap, flags], rets =>
      ∃ (kc : Fin 13 → E) (cell fl : ℕ → E),
        (∀ c : Fin 13, LoadHolds rd cap (4 * L + c.val) (kc c)) ∧
        (∀ k, 2 ≤ k → k < 4 * L → LoadHolds rd cap k (cell k)) ∧
        (∀ k, 2 ≤ k → k < L → LoadHolds rd flags k (fl k) ∧ IsInK (fl k)) ∧
        (∀ s : Digest, kc = keyCells s → ∀ k, 1 ≤ k → k < L → (k = 1 ∨ fl k ≠ 0) →
          HashesPairK s (cell (4 * k)) (cell (4 * k + 1)) (cell (4 * k + 2)) (cell (4 * k + 3))
            (cell (2 * k)) (cell (2 * k + 1))) ∧
        (∀ k, 2 ≤ k → 2 * k < L → fl k = 0 →
          LoadHolds rd flags (2 * k) 0 ∧ LoadHolds rd flags (2 * k + 1) 0) ∧
        rets = [cell 2, cell 3]
  | _, _ => False

/-- The salted core IR's `verify_merkle_cap__L{D}` gives its meaning, `2 ≤ D ≤ 8`. -/
def verify_merkle_cap_sound_Spec : Prop :=
  ∀ p ∈ merkleCapNames, ∀ (rd : Reader) (args rets : List E),
    SaltedGuest.coreProgram.Rel rd p.1 args rets → MeaningCapK (2 ^ p.2) rd args rets

/-! ## The template -/

/-- The value of the key run holding the key's cell `c`, as a node's `KECCAK` reads it: cells `4`
and `8` with the padding added. -/
def mcKr : List ℕ := [2, 3, 4, 5, 8, 9, 10, 11, 14, 15, 16, 17, 18]

/-- The value the key's cell `c` is loaded into. -/
def mcKl : List ℕ := [2, 3, 4, 5, 6, 9, 10, 11, 12, 15, 16, 17, 18]

/-- The key run at `4L` of the cap. -/
def mcKeyT (L : ℕ) : List Stmt :=
  [.atom (.load (.n 2) (.n 0) (4 * L)), .atom (.load (.n 3) (.n 0) (4 * L + 1)),
    .atom (.load (.n 4) (.n 0) (4 * L + 2)), .atom (.load (.n 5) (.n 0) (4 * L + 3)),
    .atom (.load (.n 6) (.n 0) (4 * L + 4)), .atom (.const (.n 7) (word 1 0 0)),
    .atom (.add (.n 8) (.n 6) (.n 7)), .atom (.load (.n 9) (.n 0) (4 * L + 5)),
    .atom (.load (.n 10) (.n 0) (4 * L + 6)), .atom (.load (.n 11) (.n 0) (4 * L + 7)),
    .atom (.load (.n 12) (.n 0) (4 * L + 8)), .atom (.const (.n 13) w63),
    .atom (.add (.n 14) (.n 12) (.n 13)), .atom (.load (.n 15) (.n 0) (4 * L + 9)),
    .atom (.load (.n 16) (.n 0) (4 * L + 10)), .atom (.load (.n 17) (.n 0) (4 * L + 11)),
    .atom (.load (.n 18) (.n 0) (4 * L + 12))]

/-- Node `k`'s message cells from the value `b`: the key's first four cells plus its children's. -/
def mcXs (k b : ℕ) : List Stmt :=
  [.atom (.add (.n b) (.n 2) (.n (17 + 4 * k))), .atom (.add (.n (b + 1)) (.n 3) (.n (18 + 4 * k))),
    .atom (.add (.n (b + 2)) (.n 4) (.n (19 + 4 * k))),
    .atom (.add (.n (b + 3)) (.n 5) (.n (20 + 4 * k)))]

/-- A node's `KECCAK` inputs: its message cells, then the key run's other cells. -/
def mcInsS (b : ℕ) : List V :=
  [.n b, .n (b + 1), .n (b + 2), .n (b + 3), .n 8, .n 9, .n 10, .n 11, .n 14, .n 15, .n 16,
    .n 17, .n 18]

/-- Node `k`'s `KECCAK` outputs: its two cells. -/
def mcOutsS (k : ℕ) : List V := [.n (17 + 2 * k), .n (18 + 2 * k)]

/-- Node `k`'s first value, `2 ≤ k ≤ L` (at `k = L`, the return's). -/
def mcBaseS (L k : ℕ) : ℕ :=
  if k ≤ L / 2 then 4 * L + 21 + 7 * (k - 2) else 4 * L + 21 + 7 * (L / 2 - 2) + 5 * (k - L / 2)

/-- Node `k`'s statements from the value `b`. -/
def mcNodeS (L k b : ℕ) : List Stmt :=
  mcXs k b ++
    [.atom (.load (.n (b + 4)) (.n 1) k),
      .ite (.n (b + 4))
        (if 2 * k < L then
          [.atom (.const (.n (b + 5)) (word 0 0 0)), .atom (.load (.n (b + 5)) (.n 1) (2 * k)),
            .atom (.const (.n (b + 6)) (word 0 0 0)),
            .atom (.load (.n (b + 6)) (.n 1) (2 * k + 1))]
        else [])
        [keccakA (mcInsS b) (mcOutsS k)]]

/-- The expansion of the salted `verify_merkle_cap` at `L` leaves. -/
def mcBodyS (L : ℕ) : List Stmt :=
  mcKeyT L ++
  ((List.range (4 * L - 2)).map fun i ↦ [.atom (.load (.n (i + 19)) (.n 0) (i + 2))]).flatten ++
  mcXs 1 (4 * L + 17) ++ [keccakA (mcInsS (4 * L + 17)) (mcOutsS 1)] ++
  ((List.range (L - 2)).map fun j ↦ mcNodeS L (j + 2) (mcBaseS L (j + 2))).flatten ++
  [.atom (.copy (.n (mcBaseS L L)) (.n 19)), .atom (.copy (.n (mcBaseS L L + 1)) (.n 20)),
    .ret [.n (mcBaseS L L), .n (mcBaseS L L + 1)]]

theorem noRet_mcNodeS (L k b : ℕ) : Stmt.noRetList (mcNodeS L k b) = true := by
  unfold mcNodeS; split <;> rfl

/-! ## One node -/

/-- The key's cells as the key run loads them. -/
def mcKc (σ : Val) : Fin 13 → E := fun c ↦ σ (.n (mcKl.getD c.val 0))

/-- What the key run asks: its loads, and cells `4` and `8` with the padding added. -/
def McKeyOk (rd : Reader) (σ : Val) (L : ℕ) : Prop :=
  LoadHolds rd (σ (.n 0)) (4 * L) (σ (.n 2)) ∧ LoadHolds rd (σ (.n 0)) (4 * L + 1) (σ (.n 3)) ∧
    LoadHolds rd (σ (.n 0)) (4 * L + 2) (σ (.n 4)) ∧ LoadHolds rd (σ (.n 0)) (4 * L + 3) (σ (.n 5)) ∧
    LoadHolds rd (σ (.n 0)) (4 * L + 4) (σ (.n 6)) ∧ LoadHolds rd (σ (.n 0)) (4 * L + 5) (σ (.n 9)) ∧
    LoadHolds rd (σ (.n 0)) (4 * L + 6) (σ (.n 10)) ∧
    LoadHolds rd (σ (.n 0)) (4 * L + 7) (σ (.n 11)) ∧
    LoadHolds rd (σ (.n 0)) (4 * L + 8) (σ (.n 12)) ∧
    LoadHolds rd (σ (.n 0)) (4 * L + 9) (σ (.n 15)) ∧
    LoadHolds rd (σ (.n 0)) (4 * L + 10) (σ (.n 16)) ∧
    LoadHolds rd (σ (.n 0)) (4 * L + 11) (σ (.n 17)) ∧
    LoadHolds rd (σ (.n 0)) (4 * L + 12) (σ (.n 18)) ∧
    σ (.n 8) = σ (.n 6) + word 1 0 0 ∧ σ (.n 14) = σ (.n 12) + w63

/-- The key's loads, by cell. -/
theorem McKeyOk.loads {L : ℕ} (h : McKeyOk rd σ L) :
    ∀ c : Fin 13, LoadHolds rd (σ (.n 0)) (4 * L + c.val) (mcKc σ c) := by
  obtain ⟨l0, l1, l2, l3, l4, l5, l6, l7, l8, l9, l10, l11, l12, -⟩ := h
  intro c
  match c with
  | ⟨0, _⟩ => exact l0
  | ⟨1, _⟩ => exact l1
  | ⟨2, _⟩ => exact l2
  | ⟨3, _⟩ => exact l3
  | ⟨4, _⟩ => exact l4
  | ⟨5, _⟩ => exact l5
  | ⟨6, _⟩ => exact l6
  | ⟨7, _⟩ => exact l7
  | ⟨8, _⟩ => exact l8
  | ⟨9, _⟩ => exact l9
  | ⟨10, _⟩ => exact l10
  | ⟨11, _⟩ => exact l11
  | ⟨12, _⟩ => exact l12

/-- What a node's message cells ask. -/
def McXsOk (σ : Val) (k b : ℕ) : Prop :=
  σ (.n b) = σ (.n 2) + σ (.n (17 + 4 * k)) ∧ σ (.n (b + 1)) = σ (.n 3) + σ (.n (18 + 4 * k)) ∧
    σ (.n (b + 2)) = σ (.n 4) + σ (.n (19 + 4 * k)) ∧ σ (.n (b + 3)) = σ (.n 5) + σ (.n (20 + 4 * k))

/-- **A node's `KECCAK`** hashes its children's cells into its own under the key. -/
theorem mcS_keccak_hash {L k b : ℕ} {s : Digest} (hkey : McKeyOk rd σ L) (hs : mcKc σ = keyCells s)
    (hx : McXsOk σ k b) (hK : (Atom.keccak (mcInsS b) (mcOutsS k) false false).Holds rd σ) :
    HashesPairK s (σ (.n (17 + 4 * k))) (σ (.n (18 + 4 * k))) (σ (.n (19 + 4 * k)))
      (σ (.n (20 + 4 * k))) (σ (.n (17 + 2 * k))) (σ (.n (18 + 2 * k))) := by
  obtain ⟨-, -, O, hKC, hw⟩ := keccak_holds_full hK
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, h8, h14⟩ := hkey
  obtain ⟨x0, x1, x2, x3⟩ := hx
  have k0 : σ (.n 2) = keyCells s 0 := congrFun hs 0
  have k1 : σ (.n 3) = keyCells s 1 := congrFun hs 1
  have k2 : σ (.n 4) = keyCells s 2 := congrFun hs 2
  have k3 : σ (.n 5) = keyCells s 3 := congrFun hs 3
  have k4 : σ (.n 6) = keyCells s 4 := congrFun hs 4
  have k5 : σ (.n 9) = keyCells s 5 := congrFun hs 5
  have k6 : σ (.n 10) = keyCells s 6 := congrFun hs 6
  have k7 : σ (.n 11) = keyCells s 7 := congrFun hs 7
  have k8 : σ (.n 12) = keyCells s 8 := congrFun hs 8
  have k9 : σ (.n 15) = keyCells s 9 := congrFun hs 9
  have k10 : σ (.n 16) = keyCells s 10 := congrFun hs 10
  have k11 : σ (.n 17) = keyCells s 11 := congrFun hs 11
  have k12 : σ (.n 18) = keyCells s 12 := congrFun hs 12
  have hin : (mcInsS b).map σ = nodeIn s (σ (.n (17 + 4 * k))) (σ (.n (18 + 4 * k)))
      (σ (.n (19 + 4 * k))) (σ (.n (20 + 4 * k))) := by
    simp only [mcInsS, nodeIn, List.map_cons, List.map_nil, x0, x1, x2, x3, h8, h14, k0, k1, k2,
      k3, k4, k5, k6, k7, k8, k9, k10, k11, k12]
  rw [hin] at hKC
  have h := keyed_node hKC
  have e0 : σ (.n (17 + 2 * k)) = O 0 := hw 0 (by simp [mcOutsS])
  have e1 : σ (.n (18 + 2 * k)) = O 1 := hw 1 (by simp [mcOutsS])
  rw [e0, e1]
  exact h

/-- What node `k`'s statements ask, from the value `b`. -/
def McNodeOkS (rd : Reader) (σ : Val) (L k b : ℕ) : Prop :=
  McXsOk σ k b ∧ LoadHolds rd (σ (.n 1)) k (σ (.n (b + 4))) ∧ IsInK (σ (.n (b + 4))) ∧
    (σ (.n (b + 4)) = 0 → 2 * k < L → σ (.n (b + 5)) = word 0 0 0 ∧
      LoadHolds rd (σ (.n 1)) (2 * k) (σ (.n (b + 5))) ∧ σ (.n (b + 6)) = word 0 0 0 ∧
      LoadHolds rd (σ (.n 1)) (2 * k + 1) (σ (.n (b + 6)))) ∧
    (σ (.n (b + 4)) ≠ 0 → (Atom.keccak (mcInsS b) (mcOutsS k) false false).Holds rd σ)

theorem holds_mcXs (k b : ℕ) (next : Prop) (kret : List E → Prop) :
    Stmt.HoldsList C rd σ (mcXs k b) next kret ↔ McXsOk σ k b ∧ next := by
  simp only [mcXs, McXsOk, Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_assoc]

theorem holds_mcNodeS (L k b : ℕ) (kret : List E → Prop) :
    Stmt.HoldsList C rd σ (mcNodeS L k b) True kret → McNodeOkS rd σ L k b := by
  unfold mcNodeS McNodeOkS
  rw [holdsList_append, holds_mcXs]
  by_cases h : 2 * k < L
  · simp only [h, ↓reduceIte, Stmt.HoldsList, Stmt.Holds, Atom.Holds, keccakA, and_true,
      true_implies]
    exact fun ⟨hx, hl, hK, hz, hn⟩ ↦ ⟨hx, hl, hK, hz, hn⟩
  · simp only [h, ↓reduceIte, Stmt.HoldsList, Stmt.Holds, Atom.Holds, keccakA, and_true,
      false_implies, implies_true, true_and]
    exact fun ⟨hx, hl, hK, hn⟩ ↦ ⟨hx, hl, hK, hn⟩

theorem holds_mcKeyT (L : ℕ) (next : Prop) (kret : List E → Prop) :
    Stmt.HoldsList C rd σ (mcKeyT L) next kret → McKeyOk rd σ L ∧ next := by
  simp only [mcKeyT, Stmt.HoldsList, Stmt.Holds, Atom.Holds]
  rintro ⟨l0, l1, l2, l3, l4, c7, a8, l5, l6, l7, l8, c13, a14, l9, l10, l11, l12, hn⟩
  exact ⟨⟨l0, l1, l2, l3, l4, l5, l6, l7, l8, l9, l10, l11, l12, by rw [a8, c7], by rw [a14, c13]⟩,
    hn⟩

/-! ## The meaning, soundly -/

/-- **`verify_merkle_cap` at `L` leaves, soundly**, for a function of the salted core IR whose
body is `mcBodyS L`. -/
theorem merkle_cap_soundL {name : String} {f : Fn} (L : ℕ) (hL : 4 ≤ L)
    (hfind : SaltedGuest.coreProgram.find? name = some f) (hparams : f.params = [.n 0, .n 1])
    (hbody : f.body = mcBodyS L) (rd : Reader) (args rets : List E) :
    SaltedGuest.coreProgram.Rel rd name args rets → MeaningCapK L rd args rets := by
  rw [rel_iff_sem hfind, hbody, hparams]
  rintro ⟨σ, hp, hb⟩
  rw [mcBodyS, holdsList_append, holdsList_append, holdsList_append, holdsList_append,
    holdsList_append] at hb
  obtain ⟨hkey, hb⟩ := holds_mcKeyT L _ _ hb
  rw [holdsList_range_flatten _ _ (fun _ ↦ rfl)] at hb
  obtain ⟨hld, hb⟩ := hb
  rw [holds_mcXs] at hb
  obtain ⟨hx1, hb⟩ := hb
  simp only [Stmt.HoldsList, Stmt.Holds, keccakA] at hb
  obtain ⟨hroot, hb⟩ := hb
  rw [holdsList_range_flatten _ _ (fun j ↦ noRet_mcNodeS L (j + 2) _)] at hb
  obtain ⟨hnodes, hb⟩ := hb
  simp only [Atom.Holds, List.map_cons, List.map_nil] at hb
  obtain ⟨hR0, hR1, hret⟩ := hb
  have hnodes' : ∀ k, 2 ≤ k → k < L → McNodeOkS rd σ L k (mcBaseS L k) := fun k h2 hk ↦ by
    have := holds_mcNodeS L (k - 2 + 2) _ _ (hnodes (k - 2) (by omega))
    rwa [Nat.sub_add_cancel h2] at this
  simp only [List.map_cons, List.map_nil] at hp
  subst hp
  refine ⟨mcKc σ, fun k ↦ σ (.n (k + 17)), fun k ↦ σ (.n (mcBaseS L k + 4)), hkey.loads, ?_, ?_,
    ?_, ?_, ?_⟩
  · intro k hk2 hk
    have := hld (k - 2) (by omega)
    simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true] at this
    rwa [show k - 2 + 19 = k + 17 by omega, Nat.sub_add_cancel hk2] at this
  · intro k hk2 hk
    obtain ⟨-, hl, hK, -⟩ := hnodes' k hk2 hk
    exact ⟨hl, hK⟩
  · intro s hs k hk1 hk hfl
    have e (i : ℕ) : 4 * k + i + 17 = 17 + 4 * k + i := by omega
    have e' (i : ℕ) : 2 * k + i + 17 = 17 + 2 * k + i := by omega
    simp only [e, e']
    rw [show 2 * k + 17 = 17 + 2 * k by omega, show 4 * k + 17 = 17 + 4 * k by omega]
    rw [show 17 + 4 * k + 1 = 18 + 4 * k by omega, show 17 + 4 * k + 2 = 19 + 4 * k by omega,
      show 17 + 4 * k + 3 = 20 + 4 * k by omega, show 17 + 2 * k + 1 = 18 + 2 * k by omega]
    rcases Nat.lt_or_ge k 2 with hk' | hk'
    · obtain rfl : k = 1 := by omega
      exact mcS_keccak_hash hkey hs hx1 hroot
    · have hfl' : σ (.n (mcBaseS L k + 4)) ≠ 0 := by
        rcases hfl with h | h
        · omega
        · exact h
      obtain ⟨hx, -, -, -, hnz⟩ := hnodes' k hk' hk
      exact mcS_keccak_hash hkey hs hx (hnz hfl')
  · intro k hk2 hk hfl
    obtain ⟨-, -, -, hz, -⟩ := hnodes' k hk2 (by omega)
    obtain ⟨e1, l1, e2, l2⟩ := hz hfl hk
    rw [e1, word_zero] at l1
    rw [e2, word_zero] at l2
    exact ⟨l1, l2⟩
  · rw [← hret, hR0, hR1]

end
end LeanVM.SaltedGuest.B1
