/-
  LeanVM.SaltedGuest.B1.Main.KeyOfSeed

  B1 for `key_of_seed`: the address of the key's state under the seed of its two cells.
-/

module

public import LeanVM.SaltedGuest.B1.Keyed
public import LeanVM.SaltedGuest.B1.Merkle.CapAll

/-!
# `key_of_seed`

`key_of_seed(seed_0, seed_1)` absorbs the seed's two cells and fifteen zero cells in two `KECCAK`s
from the zero state (`keyed_state`, `final=0`) into a frame run and returns its address (`addr`).
`key_of_seed_sound`: for the seed `S` whose cells the arguments are, the returned address holds
the key of `S` (`KeyIs`, `key_whole`).
-/

namespace LeanVM.SaltedGuest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Guest.Value.Keccak LeanVM.Guest.B1 LeanVM.Protocol LeanVM.Protocol.KeccakHash

@[expose] public section

/-- **`key_of_seed(seed_0, seed_1)`**: for the seed of its two cells, the key's run at the returned
pointer. -/
def MeaningKeyOfSeed (rd : Reader) : List E → List E → Prop
  | [s0, s1], [p] => ∀ S : Digest, (s0, s1) = digestHalves S → KeyIs rd p S
  | _, _ => False

/-- The thirteen output values of block `b` of `key_of_seed` (`7 ..`, `20 ..`). -/
def ksRun (b : ℕ) : List V := (List.range 13).map fun c ↦ .n (b + c)

/-- `key_of_seed`'s body. -/
def ksBody : List Stmt :=
  [.atom (.const (.n 2) (word 1 0 0)), .atom (.const (.n 3) (word 0 0 0)),
    .atom (.const (.n 4) (word 0 0 0)), .atom (.const (.n 5) (word 0 0 0)),
    .atom (.const (.n 6) (word 0 0 0)),
    .atom (.keccak [.n 0, .n 1, .n 3, .n 3, .n 3, .n 4, .n 5, .n 6, .n 3, .n 3, .n 4, .n 5, .n 6]
      (ksRun 7) false true),
    .atom (.keccak (ksRun 7) (ksRun 20) true false),
    .atom (.frameAddr (.n 33) (ksRun 20)), .atom (.copy (.n 34) (.n 33)), .ret [.n 34]]

set_option maxRecDepth 100000 in
kernel_rfl ks_idx : SaltedGuest.coreProgram[34]? = some LeanVM.SaltedGuest.Data.core34

set_option maxRecDepth 100000 in
kernel_rfl ks_body : LeanVM.SaltedGuest.Data.core34.body = ksBody

theorem cells13_ksRun (σ : Val) (b : ℕ) (c : Fin 13) :
    cells13 ((ksRun b).map σ) c = σ (.n (b + c)) := by
  simp [cells13, ksRun, List.getD_eq_getElem?_getD]

/-- **`key_of_seed` returns the key's address.** -/
theorem key_of_seed_sound (rd : Reader) (args rets : List E)
    (h : SaltedGuest.coreProgram.Rel rd "key_of_seed" args rets) : MeaningKeyOfSeed rd args rets := by
  obtain ⟨σ, hp, hb⟩ := (rel_iff_sem (find_of_getElem? ks_idx) args rets).mp h
  replace hb : Stmt.HoldsList (SaltedGuest.coreProgram.Rel rd) rd σ ksBody False (fun rs ↦ rs = rets) := by
    rw [← ks_body]; exact hb
  have hp' : args = [σ (.n 0), σ (.n 1)] := by rw [← hp]; rfl
  subst hp'
  simp only [ksBody, Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hb
  obtain ⟨-, z3, z4, z5, z6, k0, k1, ⟨hK, hrun⟩, cp, hret⟩ := hb
  simp only [List.map_cons, List.map_nil] at hret
  subst hret
  intro S hS
  rw [word_zero] at z3 z4 z5 z6
  obtain ⟨-, -, O0, hK0, hw0⟩ := keccak_holds_full (rd := rd) k0
  obtain ⟨-, -, O1, hK1, hw1⟩ := keccak_holds_full (rd := rd) k1
  let I : ℕ → Fin 13 → E := fun k ↦ if k = 0 then cells13 ([V.n 0, .n 1, .n 3, .n 3, .n 3, .n 4,
    .n 5, .n 6, .n 3, .n 3, .n 4, .n 5, .n 6].map σ) else cells13 ((ksRun 7).map σ)
  let O : ℕ → Fin 13 → E := fun k ↦ if k = 0 then 0 else if k = 1 then O0 else O1
  have e0 : ∀ c : Fin 13, O0 c = σ (.n (7 + c)) := fun c ↦ by
    rw [← hw0 c (by simp [ksRun])]; simp [ksRun]
  have e1 : ∀ c : Fin 13, O1 c = σ (.n (20 + c)) := fun c ↦ by
    rw [← hw1 c (by simp [ksRun])]; simp [ksRun]
  have hk := key_whole (s := S) (I := I) (O := O) (fun c ↦ rfl)
    (fun k hk c hc ↦ by
      have h1 : (σ (.n 0), σ (.n 1)) = ((digestHalves S).1, (digestHalves S).2) := hS
      simp only [Prod.mk.injEq] at h1
      obtain ⟨h1a, h1b⟩ := h1
      interval_cases k
      · fin_cases c <;> simp [I, O, keyInput, cells13, z3, z4, z5, z6, h1a, h1b]
      · fin_cases c <;> simp [I, O, keyInput, cells13_ksRun, e0])
    (fun k hk c hc ↦ by
      interval_cases k
      · fin_cases c <;> simp [I, O, cells13, z3, z4, z5, z6] at hc ⊢
      · fin_cases c <;> simp [I, O, cells13_ksRun, e0] at hc ⊢)
    (fun k hk ↦ by
      interval_cases k
      · exact hK0
      · simp only [I, O, one_ne_zero, ↓reduceIte]
        have : cells13 ((ksRun 7).map σ) = O0 := funext fun c ↦ by rw [cells13_ksRun, e0]
        rw [this]
        show KeccakCellsRelation O0 true O1 false .all
        rw [this] at hK1
        exact hK1)
  have hO2 : O 2 = O1 := rfl
  refine ⟨by rw [cp]; exact hK, fun c w hw ↦ ?_⟩
  rw [cp] at hw
  have := hrun c (by simp [ksRun]) w hw
  rw [this, ← congrFun hk c, hO2, e1 c]
  simp [ksRun]

end
end LeanVM.SaltedGuest.B1
