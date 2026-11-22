/-
  LeanVM.SaltedGuest.B1.Whir.LqK

  The salted `level_queries`: its template, and its frame with the key of the seed in memory
  words 2 and 3 written after the cap's cells.
-/

module

public import LeanVM.Guest.B1.Whir.QueriesBlk
public import LeanVM.SaltedGuest.B1.Main.KeyOfSeed

/-!
# The salted `level_queries`

`lqBodyK q base il leaf d cd`: the deployed `lqBody` with the cap's buffer `13` cells longer, and
after the cap's hint the key run (`lqKeyT`): the seed's cells loaded from memory words `2` and `3`,
the key computed by two `KECCAK`s (`key_of_seed`'s), its cells asserted in the cap's buffer after
the cap's `4·2^cd` cells; the values from `5` on moved by `39`.

`level_queries_frameK`: the deployed `level_queries_frame` for the salted body, and with the seed
`S` whose cells are memory words `2` and `3`, the key of `S` in the cap's buffer (`lqKey_sound`).
-/

namespace LeanVM.SaltedGuest.B1.Whir

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest LeanVM.Guest.B1
open LeanVM.Guest.Value LeanVM.Guest.Value.Keccak LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Whir LeanVM.SaltedGuest.B1 Recursion.Salted

@[expose] public section

/-- A function of the salted core IR, found by its name, with the parameters and the body. -/
def FnIsK (name : String) (ps : List V) (body : List Stmt) : Prop :=
  ∃ fn, SaltedGuest.coreProgram.find? name = some fn ∧ fn.params = ps ∧ fn.body = body

/-- Size `m`'s salted `open_stacked` is its template, the deployed one. -/
def OsDataK (m : Nat) : Prop :=
  FnIsK ("open_stacked__L" ++ natStr m) (osParams 10) (osBody (osCfg m))

/-- The seed's loads and the key's two `KECCAK`s of the salted `level_queries`. -/
def lqKeyA : List Stmt :=
  [.atom (.const (.n 5) (word 1 0 0)), .atom (.const (.n 6) (word 4 0 0)),
    .atom (.mul (.n 7) (.n 5) (.n 6)), .atom (.load (.n 8) (.n 7) 0),
    .atom (.const (.n 9) (word 1 0 0)), .atom (.const (.n 10) (word 8 0 0)),
    .atom (.mul (.n 11) (.n 9) (.n 10)), .atom (.load (.n 12) (.n 11) 0),
    .atom (.const (.n 13) (word 1 0 0)), .atom (.const (.n 14) (word 0 0 0)),
    .atom (.const (.n 15) (word 0 0 0)), .atom (.const (.n 16) (word 0 0 0)),
    .atom (.const (.n 17) (word 0 0 0)),
    .atom (.keccak [.n 8, .n 12, .n 14, .n 14, .n 14, .n 15, .n 16, .n 17, .n 14, .n 14, .n 15,
      .n 16, .n 17] (ksRun 18) false true),
    .atom (.keccak (ksRun 18) (ksRun 31) true false)]

/-- The key run of the salted `level_queries`: the seed's cells from memory words `2` and `3`, the
key's two `KECCAK`s (`lqKeyA`), its cells asserted after the cap's `4·2^cd` cells. -/
def lqKeyT (cd : ℕ) : List Stmt :=
  lqKeyA ++ (List.range 13).map fun c ↦ .atom (.load (.n (31 + c)) (.n 4) (4 * 2 ^ cd + c))

/-- The salted `level_queries`' body before its `ret`. -/
def lqAK (q base il leaf d cd : ℕ) : List Stmt :=
  let pw := osPowSteps 0 (osPowDigits q) 0 48
  let k := 48 + osPowLen q
  let iters := if base = 1 then q / 2 else q
  osHeap (4 * 2 ^ cd + 13) 3 ++
    [.atom (.hint (.witness "merkle_caps" (.heap (.n 4) 0 (4 * 2 ^ cd))))] ++
    lqKeyT cd ++ osHeap (2 ^ cd) 44 ++
    [.atom (.hint (.witness "merkle_cap_active" (.heap (.n 45) 0 (2 ^ cd)))),
      .call ("verify_merkle_cap__L" ++ natStr cd) [.n 4, .n 45] [.n 46, .n 47]] ++
    pw.1 ++
    [.atom (.const (.n k) (gw iters)),
      .call (oqName q base il leaf d cd) [.n 4, .n 45, .n 0, .n pw.2, .n 1, .n 2, .n k] [.n (k + 1)],
      .atom (.copy (.n (k + 2)) (.n 46)), .atom (.copy (.n (k + 3)) (.n 47)),
      .atom (.copy (.n (k + 4)) (.n (k + 1))), .atom (.copy (.n (k + 5)) (.n pw.2))]

/-- **The salted `level_queries`' body.** -/
def lqBodyK (q base il leaf d cd : ℕ) : List Stmt :=
  lqAK q base il leaf d cd ++ [.ret [.n (48 + osPowLen q + 2), .n (48 + osPowLen q + 3),
    .n (48 + osPowLen q + 4), .n (48 + osPowLen q + 5)]]

theorem lqAK_flat (q base il leaf d cd : ℕ) : (lqAK q base il leaf d cd).all Stmt.flat = true := by
  simp [lqAK, lqKeyT, lqKeyA, osHeap, osPowSteps_allFlat, Stmt.flat]

/-- **The key run** writes the key of the seed whose cells are memory words `2` and `3` after the
cap's cells. -/
theorem lqKey_sound {C : CallRel} {rd : Reader} {σ : Val} {cd : ℕ} (h : AllOk C rd σ (lqKeyT cd))
    {S : Digest} (hS2 : LoadHolds rd 1 2 (digestHalves S).1)
    (hS3 : LoadHolds rd 1 3 (digestHalves S).2) :
    ∀ c : Fin 13, LoadHolds rd (σ (.n 4)) (4 * 2 ^ cd + c.val) (keyCells S c) := by
  have A : ∀ a : Atom, Stmt.atom a ∈ lqKeyA → a.Holds rd σ :=
    fun a ha ↦ h _ (List.mem_append_left _ ha)
  have c5 : σ (.n 5) = word 1 0 0 := A (.const (.n 5) _) (by simp [lqKeyA])
  have c6 : σ (.n 6) = word 4 0 0 := A (.const (.n 6) _) (by simp [lqKeyA])
  have m7 : σ (.n 7) = σ (.n 5) * σ (.n 6) := A (.mul (.n 7) (.n 5) (.n 6)) (by simp [lqKeyA])
  have l8 : LoadHolds rd (σ (.n 7)) 0 (σ (.n 8)) := A (.load (.n 8) (.n 7) 0) (by simp [lqKeyA])
  have c9 : σ (.n 9) = word 1 0 0 := A (.const (.n 9) _) (by simp [lqKeyA])
  have c10 : σ (.n 10) = word 8 0 0 := A (.const (.n 10) _) (by simp [lqKeyA])
  have m11 : σ (.n 11) = σ (.n 9) * σ (.n 10) := A (.mul (.n 11) (.n 9) (.n 10)) (by simp [lqKeyA])
  have l12 : LoadHolds rd (σ (.n 11)) 0 (σ (.n 12)) := A (.load (.n 12) (.n 11) 0) (by simp [lqKeyA])
  have z3 : σ (.n 14) = 0 := by rw [← word_zero]; exact A (.const (.n 14) _) (by simp [lqKeyA])
  have z4 : σ (.n 15) = 0 := by rw [← word_zero]; exact A (.const (.n 15) _) (by simp [lqKeyA])
  have z5 : σ (.n 16) = 0 := by rw [← word_zero]; exact A (.const (.n 16) _) (by simp [lqKeyA])
  have z6 : σ (.n 17) = 0 := by rw [← word_zero]; exact A (.const (.n 17) _) (by simp [lqKeyA])
  have k0 := A (.keccak [.n 8, .n 12, .n 14, .n 14, .n 14, .n 15, .n 16, .n 17, .n 14, .n 14,
    .n 15, .n 16, .n 17] (ksRun 18) false true) (by simp [lqKeyA])
  have k1 := A (.keccak (ksRun 18) (ksRun 31) true false) (by simp [lqKeyA])
  have hs0 : σ (.n 8) = (digestHalves S).1 := by
    rw [m7, c5, c6, word_one, show word 4 0 0 = gen ^ 2 from word_two_pow (a := 2) (by norm_num)]
      at l8
    exact loadHolds_unique ((loadHolds_mul_gen_pow rd 1 2 0 _).mp l8) hS2
  have hs1 : σ (.n 12) = (digestHalves S).2 := by
    rw [m11, c9, c10, word_one, show word 8 0 0 = gen ^ 3 from word_two_pow (a := 3) (by norm_num)]
      at l12
    exact loadHolds_unique ((loadHolds_mul_gen_pow rd 1 3 0 _).mp l12) hS3
  obtain ⟨-, -, O0, hK0, hw0⟩ := keccak_holds_full (rd := rd) k0
  obtain ⟨-, -, O1, hK1, hw1⟩ := keccak_holds_full (rd := rd) k1
  let I : ℕ → Fin 13 → E := fun k ↦ if k = 0 then cells13 ([V.n 8, .n 12, .n 14, .n 14, .n 14,
    .n 15, .n 16, .n 17, .n 14, .n 14, .n 15, .n 16, .n 17].map σ) else cells13 ((ksRun 18).map σ)
  let O : ℕ → Fin 13 → E := fun k ↦ if k = 0 then 0 else if k = 1 then O0 else O1
  have e0 : ∀ c : Fin 13, O0 c = σ (.n (18 + c)) := fun c ↦ by
    rw [← hw0 c (by simp [ksRun])]; simp [ksRun]
  have e1 : ∀ c : Fin 13, O1 c = σ (.n (31 + c)) := fun c ↦ by
    rw [← hw1 c (by simp [ksRun])]; simp [ksRun]
  have hk := key_whole (s := S) (I := I) (O := O) (fun c ↦ rfl)
    (fun k hk c hc ↦ by
      interval_cases k
      · fin_cases c <;> simp [I, O, keyInput, cells13, z3, z4, z5, z6, hs0, hs1]
      · fin_cases c <;> simp [I, O, keyInput, cells13_ksRun, e0])
    (fun k hk c hc ↦ by
      interval_cases k
      · fin_cases c <;> simp [I, O, cells13, z3, z4, z5, z6] at hc ⊢
      · fin_cases c <;> simp [I, O, cells13_ksRun, e0] at hc ⊢)
    (fun k hk ↦ by
      interval_cases k
      · exact hK0
      · simp only [I, O, one_ne_zero, ↓reduceIte]
        have : cells13 ((ksRun 18).map σ) = O0 := funext fun c ↦ by rw [cells13_ksRun, e0]
        rw [this]
        show KeccakCellsRelation O0 true O1 false .all
        rw [this] at hK1
        exact hK1)
  intro c
  have hl : LoadHolds rd (σ (.n 4)) (4 * 2 ^ cd + c.val) (σ (.n (31 + c.val))) :=
    h (.atom (.load (.n (31 + c.val)) (.n 4) (4 * 2 ^ cd + c.val)))
      (List.mem_append_right _ (List.mem_map.2 ⟨c.val, List.mem_range.2 c.2, rfl⟩))
  rw [← e1 c, show O1 = O 2 from rfl, hk] at hl
  exact hl

/-- **The salted `level_queries`' frame**: the deployed frame's facts at the salted values, and the
key of the seed in memory words `2` and `3` after the cap's cells. -/
theorem level_queries_frameK {C : CallRel} {rd : Reader} {q base il leaf d cd : ℕ} {σ' : Val}
    {args rets : List E}
    (hp : (osParams 3).map σ' = args)
    (hh : Stmt.HoldsList C rd σ' (lqBodyK q base il leaf d cd) False (fun rs ↦ rs = rets))
    (hdig : digitsVal (osPowDigits q) 1 = q)
    (hit : (if base = 1 then q / 2 else q) < u128Bound)
    {S : Digest} (hS2 : LoadHolds rd 1 2 (digestHalves S).1)
    (hS3 : LoadHolds rd 1 3 (digestHalves S).2) :
    args = [σ' (.n 0), σ' (.n 1), σ' (.n 2)] ∧
    rets = [σ' (.n 46), σ' (.n 47), σ' (.n (48 + osPowLen q + 1)), σ' (.n 0) ^ q] ∧
    C ("verify_merkle_cap__L" ++ natStr cd) [σ' (.n 4), σ' (.n 45)] [σ' (.n 46), σ' (.n 47)] ∧
    C (oqName q base il leaf d cd)
      [σ' (.n 4), σ' (.n 45), σ' (.n 0), σ' (.n (osPowSteps 0 (osPowDigits q) 0 48).2), σ' (.n 1),
        σ' (.n 2), σ' (.n (48 + osPowLen q))] [σ' (.n (48 + osPowLen q + 1))] ∧
    σ' (.n (osPowSteps 0 (osPowDigits q) 0 48).2) = σ' (.n 0) ^ q ∧
    σ' (.n (48 + osPowLen q)) = gen ^ (if base = 1 then q / 2 else q) ∧
    ∀ c : Fin 13, LoadHolds rd (σ' (.n 4)) (4 * 2 ^ cd + c.val) (keyCells S c) := by
  rw [lqBodyK, holdsList_flat_ret _ (lqAK_flat _ _ _ _ _ _)] at hh
  obtain ⟨hok, hret⟩ := hh
  have hkey : AllOk C rd σ' (lqKeyT cd) := fun s hs ↦ hok s (by
    simp only [lqAK, List.mem_append]; exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr hs)))))
  have hk := lqKey_sound hkey hS2 hS3
  simp only [lqAK, osHeap, allOk_append, allOk_cons, allOk_nil, and_true, true_and, Whir.StmtOk,
    Atom.Holds, and_assoc] at hok
  obtain ⟨-, -, -, hcap, hpw, hk', hoq, e2, e3, e4, e5⟩ := hok
  have hpv := osPowSteps_val (C := C) (rd := rd) (σ := σ') 0 (osPowDigits q) 0 48 1
    (by rw [pow_one]) hpw
  rw [hdig] at hpv
  simp only [List.map_cons, List.map_nil] at hcap hoq hret
  simp only [osParams, List.range_succ, List.range_zero, List.map_cons, List.map_nil,
    List.nil_append, List.cons_append] at hp
  refine ⟨hp.symm, ?_, hcap, hoq, hpv, by rw [hk', gw_eq hit], hk⟩
  rw [← hret, e2, e3, e4, e5, hpv]

end
end LeanVM.SaltedGuest.B1.Whir
