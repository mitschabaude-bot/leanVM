/-
  LeanVM.SaltedGuest.B1.Opening.QueriesMainWK

  The salted `opening_queries` is sound with its queries named, under every seed whose key the
  cap's buffer holds.
-/

module

public import LeanVM.SaltedGuest.B1.Opening.QueriesWK
public import LeanVM.Guest.B1.Opening.QueriesMainW

/-!
# The salted `opening_queries`, its queries named

The deployed `oqMain1_sound_w`, `oqMain0_sound_w` for the salted templates: the key's cells loaded
from the cap's buffer (`9 .. 21`, of `S` when the buffer holds the key of `S`) and handed to the
loop (its parameters `5 .. 17`), each query `QueryOpensSK S`.

* `oqLoopArgsK`, `oqIterOfK`, `oqsOfK`: the queries' witness, as the deployed `oqsOf`, off the
  salted frames (the salted loop's arguments, the salted queries' `oqQueryWK`).
* `opening_queries_sound_w_SpecK name loop s odd`: the deployed `opening_queries_sound_w_Spec` over
  the salted core IR, under every seed `S` whose key the cap's buffer holds after its `4·2^cd`
  cells, `MeaningOpeningQueriesWK S` at `oqsOfK`.
-/

namespace LeanVM.SaltedGuest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Guest.B1 LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile
open LeanVM.Protocol.Verifier LeanVM.SaltedGuest.B1.Whir Recursion.Salted

@[expose] public section

variable {rd : Reader} {σ : Val}

/-! ## The witness -/

/-- The salted loop's arguments after its counter: `N, qptrs, cap, flags`, the key's cells, `wp,
chain, μ`. -/
def oqLoopArgsK (σ : Val) : List E :=
  [σ (.n 6), σ (.n 4), σ (.n 0), σ (.n 1)] ++ (oqKeyV 9).map σ ++ [σ (.n 5), σ (.n 24), σ (.n 8)]

/-- A salted loop iteration's queries, from its frame. -/
def oqIterOfK (s : Oq) (rd : Reader) (σ : Val) (V : SaltedGuest.End.FrameMap) : List QW :=
  if s.base = 1 then
    [oqQueryWK s rd (σ (.n 23)) (σ (.n 3)) (σ (.n 4)) 24 true σ V,
      oqQueryWK s rd (σ (.n (oqE1K s))) (σ (.n 3)) (σ (.n 4)) (oqE1K s + 1) false σ V]
  else [oqQueryWK s rd (σ (.n 22)) (σ (.n 3)) (σ (.n 4)) 23 true σ V]

/-- **The queries of the salted `opening_queries`**, from its frame `σ` and its `N` iterations'
frames. -/
def oqsOfK (s : Oq) (odd : ℕ) (loop : String) (N : ℕ) (rd : Reader) (σ : Val)
    (V : SaltedGuest.End.FrameMap) : List QW :=
  (if odd = 1 then [oqQueryWK s rd (σ (.n 25)) (σ (.n 0)) (σ (.n 1)) 26 true σ V] else []) ++
    (List.range N).flatMap fun j ↦ oqIterOfK s rd (V loop (gen ^ j :: oqLoopArgsK σ) []) V

/-- **The salted `opening_queries` is sound with its queries named** at the specialization `name`
(loop helper `loop`, shape `s`, `odd`), under every seed whose key the cap's buffer holds. -/
def opening_queries_sound_w_SpecK (name loop : String) (s : Oq) (odd : ℕ) : Prop :=
  ∀ (rd : Reader) (C : CallRel) (V : SaltedGuest.End.FrameMap), SaltedGuest.End.UnfoldsV rd C V →
    CallRel.Le C (SaltedGuest.coreProgram.Rel rd) →
    ∀ (fm : Fn) (σ : Val) (args rets : List E) (N : ℕ), SaltedGuest.coreProgram.find? name = some fm →
      fm.params.map σ = args → Stmt.HoldsList C rd σ fm.body False (fun rs ↦ rs = rets) →
      args.getD 6 0 = gen ^ N → N < ordG →
      QueryWinsOk rd (args.getD 4 0) (oqCount odd s.base N) (s.pd + s.cd) s.cd →
      ∀ S : Digest, (∀ c : Fin 13, LoadHolds rd (args.getD 0 0) (4 * 2 ^ s.cd + c.val)
        (keyCells S c)) →
      MeaningOpeningQueriesWK S odd s.base s.I (s.pd + s.cd) s.cd rd (oqsOfK s odd loop N rd σ V)
        args rets

/-! ## The templates are flat -/

theorem oqXorTK_atoms (s : Oq) (emit : Bool) (b pr kc kL k c : ℕ) :
    AllAtoms (oqXorTK s emit b pr kc kL k c) := by
  unfold oqXorTK
  dsimp only
  split
  · exact allAtoms_cons allAtoms_nil
  · split
    · exact allAtoms_append (by split <;> first | exact oqPadT_atoms _ | exact allAtoms_nil)
        (allAtoms_cons allAtoms_nil)
    · exact allAtoms_cons (allAtoms_cons allAtoms_nil)

theorem oqBlockTK_atoms (s : Oq) (emit : Bool) (b pr kc kL k : ℕ) :
    AllAtoms (oqBlockTK s emit b pr kc kL k) :=
  allAtoms_append (allAtoms_map_flatten fun _ _ => oqXorTK_atoms _ _ _ _ _ _ _ _)
    (allAtoms_cons allAtoms_nil)

theorem oqLeafTK_atoms (s : Oq) (emit : Bool) (b pr kc kL : ℕ) :
    AllAtoms (oqLeafTK s emit b pr kc kL) :=
  allAtoms_map_flatten fun _ _ => oqBlockTK_atoms _ _ _ _ _ _ _

theorem oqQueryTK_flatC (s : Oq) (bp cap flags wp : V) (b : ℕ) (emit : Bool) (pr kc : ℕ)
    (walk : String) : FlatC (oqQueryTK s bp cap flags wp b emit pr kc walk) := by
  unfold oqQueryTK
  exact flatC_append (flatC_of_flat (flat_of_atoms (allAtoms_append (allAtoms_append
    (allAtoms_append (oqRowT_atoms _ _) (oqPacksT_atoms _ _)) (oqDotT_atoms _ _ _))
    (oqLeafTK_atoms _ _ _ _ _ _)))) (flatC_call _ _ _)

theorem oqLoop1AK_flatC (s : Oq) (odd : ℕ) (walk : String) : FlatC (oqLoop1AK s odd walk) := by
  unfold oqLoop1AK
  dsimp only
  refine flatC_append (flatC_append (flatC_append (flatC_append (flatC_atoms ?_)
    (oqQueryTK_flatC _ _ _ _ _ _ _ _ _ _)) (flatC_atoms ?_)) (oqQueryTK_flatC _ _ _ _ _ _ _ _ _ _))
    (flatC_atoms ?_)
  all_goals atoms_lit

theorem oqLoop0AK_flatC (s : Oq) (walk : String) : FlatC (oqLoop0AK s walk) := by
  unfold oqLoop0AK
  dsimp only
  refine flatC_append (flatC_append (flatC_atoms ?_) (oqQueryTK_flatC _ _ _ _ _ _ _ _ _ _))
    (flatC_atoms ?_)
  all_goals atoms_lit

theorem oqMainAK_flatC (s : Oq) (odd : ℕ) (walk : String) : FlatC (oqMainAK s odd walk) := by
  unfold oqMainAK
  dsimp only
  refine flatC_append (flatC_append (flatC_append (flatC_append (flatC_atoms ?_) (flatC_atoms ?_))
    (flatC_atoms ?_)) ?_) (flatC_atoms ?_)
  · atoms_lit
  · intro x hx
    obtain ⟨c, -, rfl⟩ := List.mem_map.1 hx
    exact ⟨_, rfl⟩
  · atoms_lit
  · split
    · exact flatC_append (flatC_append (flatC_atoms (allAtoms_cons allAtoms_nil))
        (oqQueryTK_flatC _ _ _ _ _ _ _ _ _ _)) (flatC_atoms (allAtoms_cons (allAtoms_cons allAtoms_nil)))
    · exact flatC_atoms (allAtoms_cons (allAtoms_cons allAtoms_nil))
  · exact allAtoms_cons (allAtoms_cons (allAtoms_cons allAtoms_nil))

/-! ## The loops' guards and parameters -/

theorem oqLoop1_hcK {C : CallRel} {s : Oq} {odd : ℕ} {walk : String} {fl : Fn}
    (hpl : fl.params = oqLoopParamsK) {Nv : E} {rest : List E} (τ : Val) (x : E)
    (hp : fl.params.map τ = x :: Nv :: rest) (hA : BlockOkC C rd τ (oqLoop1AK s odd walk)) :
    τ (.n (oqC1K s + 9)) = x * gen + Nv ∧
      ((.n (oqC1K s + 11) :: (List.range 20).map fun i ↦ V.n (i + 1)) : List V).map τ =
        x * gen :: Nv :: rest := by
  rw [hpl] at hp
  simp only [oqLoopParamsK, List.range_succ, List.range_zero, List.map_cons, List.map_nil,
    List.nil_append, List.cons_append] at hp
  set c := oqC1K s with hc
  have a7 := hA.atom (by simp [oqLoop1AK, ← hc] : Stmt.atom (.const (.n (c + 7)) (word 2 0 0)) ∈ _)
  have a8 := hA.atom (by simp [oqLoop1AK, ← hc] :
    Stmt.atom (.mul (.n (c + 8)) (.n 0) (.n (c + 7))) ∈ _)
  have a9 := hA.atom (by simp [oqLoop1AK, ← hc] :
    Stmt.atom (.add (.n (c + 9)) (.n (c + 8)) (.n 1)) ∈ _)
  have a10 := hA.atom (by simp [oqLoop1AK, ← hc] : Stmt.atom (.const (.n (c + 10)) (word 2 0 0)) ∈ _)
  have a11 := hA.atom (by simp [oqLoop1AK, ← hc] :
    Stmt.atom (.mul (.n (c + 11)) (.n 0) (.n (c + 10))) ∈ _)
  simp only [Atom.Holds] at a7 a8 a9 a10 a11
  simp only [List.cons.injEq] at hp
  obtain ⟨h0, h1, hr⟩ := hp
  subst hr
  refine ⟨by rw [a9, a8, a7, word_gen, h0, h1], ?_⟩
  simp [a11, a10, word_gen, h0, h1, List.range_succ]

theorem oqLoop0_hcK {C : CallRel} {s : Oq} {walk : String} {fl : Fn}
    (hpl : fl.params = oqLoopParamsK) {Nv : E} {rest : List E} (τ : Val) (x : E)
    (hp : fl.params.map τ = x :: Nv :: rest) (hA : BlockOkC C rd τ (oqLoop0AK s walk)) :
    τ (.n (oqC0K s + 7)) = x * gen + Nv ∧
      ((.n (oqC0K s + 9) :: (List.range 20).map fun i ↦ V.n (i + 1)) : List V).map τ =
        x * gen :: Nv :: rest := by
  rw [hpl] at hp
  simp only [oqLoopParamsK, List.range_succ, List.range_zero, List.map_cons, List.map_nil,
    List.nil_append, List.cons_append] at hp
  set c := oqC0K s with hc
  have a5 := hA.atom (by simp [oqLoop0AK, ← hc] : Stmt.atom (.const (.n (c + 5)) (word 2 0 0)) ∈ _)
  have a6 := hA.atom (by simp [oqLoop0AK, ← hc] :
    Stmt.atom (.mul (.n (c + 6)) (.n 0) (.n (c + 5))) ∈ _)
  have a7 := hA.atom (by simp [oqLoop0AK, ← hc] :
    Stmt.atom (.add (.n (c + 7)) (.n (c + 6)) (.n 1)) ∈ _)
  have a8 := hA.atom (by simp [oqLoop0AK, ← hc] : Stmt.atom (.const (.n (c + 8)) (word 2 0 0)) ∈ _)
  have a9 := hA.atom (by simp [oqLoop0AK, ← hc] :
    Stmt.atom (.mul (.n (c + 9)) (.n 0) (.n (c + 8))) ∈ _)
  simp only [Atom.Holds] at a5 a6 a7 a8 a9
  simp only [List.cons.injEq] at hp
  obtain ⟨h0, h1, hr⟩ := hp
  subst hr
  refine ⟨by rw [a7, a6, a5, word_gen, h0, h1], ?_⟩
  simp [a9, a8, word_gen, h0, h1, List.range_succ]

/-- A salted iteration's frame at the loop's arguments: its parameters those of the salted
function's frame `σ`. -/
theorem loop_paramsK {fl : Fn} (hpl : fl.params = oqLoopParamsK) {τ : Val} {x : E}
    (hp : fl.params.map τ = x :: oqLoopArgsK σ) :
    τ (.n 0) = x ∧ τ (.n 1) = σ (.n 6) ∧ τ (.n 2) = σ (.n 4) ∧ τ (.n 3) = σ (.n 0) ∧
      τ (.n 4) = σ (.n 1) ∧ (∀ c : Fin 13, τ (.n (5 + c.val)) = σ (.n (9 + c.val))) ∧
      τ (.n 18) = σ (.n 5) ∧ τ (.n 19) = σ (.n 24) ∧ τ (.n 20) = σ (.n 8) := by
  rw [hpl] at hp
  simp only [oqLoopParamsK, oqLoopArgsK, oqKeyV, List.range_succ, List.range_zero, List.map_cons,
    List.map_nil, List.nil_append, List.cons_append, List.cons.injEq] at hp
  obtain ⟨e0, e1, e2, e3, e4, k0, k1, k2, k3, k4, k5, k6, k7, k8, k9, k10, k11, k12, e18, e19, e20,
    -⟩ := hp
  refine ⟨e0, e1, e2, e3, e4, fun c ↦ ?_, e18, e19, e20⟩
  fin_cases c <;> assumption

/-! ## The function's start -/

theorem oqMainA_basicK {C : CallRel} {s : Oq} {odd : ℕ} {walk : String} {σ : Val}
    (hA : BlockOkC C rd σ (oqMainAK s odd walk)) :
    σ (.n 8) * σ (.n 2) = 1 ∧ σ (.n (oqMKK s odd + 1)) = 1 + σ (.n 6) ∧
      σ (.n (oqMKK s odd + 2)) = 1 ∧ (odd ≠ 1 → LoadHolds rd (σ (.n 24)) 0 0) := by
  set k := oqMKK s odd with hk
  have m0 := hA.atom (by simp [oqMainAK] : Stmt.atom (.const (.n 7) (word 1 0 0)) ∈ _)
  have m1 := hA.atom (by simp [oqMainAK] : Stmt.atom (.mul (.n 7) (.n 8) (.n 2)) ∈ _)
  have m2 := hA.atom (by simp [oqMainAK, ← hk] : Stmt.atom (.const (.n k) (word 1 0 0)) ∈ _)
  have m3 := hA.atom (by simp [oqMainAK, ← hk] : Stmt.atom (.add (.n (k + 1)) (.n k) (.n 6)) ∈ _)
  have m4 := hA.atom (by simp [oqMainAK, ← hk] :
    Stmt.atom (.const (.n (k + 2)) (word 1 0 0)) ∈ _)
  simp only [Atom.Holds] at m0 m1 m2 m3 m4
  refine ⟨by rw [← m1, m0, word_one], by rw [m3, m2, word_one], by rw [m4, word_one], fun h1 => ?_⟩
  have c1 := hA.atom (by simp [oqMainAK, h1] : Stmt.atom (.const (.n 25) (word 0 0 0)) ∈ _)
  have c2 := hA.atom (by simp [oqMainAK, h1] : Stmt.atom (.load (.n 25) (.n 24) 0) ∈ _)
  simp only [Atom.Holds] at c1 c2
  rw [c1, word_zero] at c2
  exact c2

/-- The key's loads of the salted function's start: with the key of `S` in the cap's buffer, the
key's cells of `S`. -/
theorem oqMainA_keyK {C : CallRel} {s : Oq} {odd : ℕ} {walk : String} {σ : Val}
    (hA : BlockOkC C rd σ (oqMainAK s odd walk)) {S : Digest}
    (hkeyC : ∀ c : Fin 13, LoadHolds rd (σ (.n 0)) (4 * 2 ^ s.cd + c.val) (keyCells S c)) :
    ∀ c : Fin 13, σ (.n (9 + c.val)) = keyCells S c := fun c ↦ by
  have l := hA.atom (a := .load (.n (9 + c.val)) (.n 0) (4 * 2 ^ s.cd + c.val)) (by
    simp only [oqMainAK, List.mem_append, List.mem_map, List.mem_range]
    exact Or.inl (Or.inl (Or.inl (Or.inr ⟨c.val, c.isLt, rfl⟩))))
  exact loadHolds_unique l (hkeyC c)

theorem oqMainA_odd_wK {C : CallRel} {V : SaltedGuest.End.FrameMap}
    (hU : SaltedGuest.End.UnfoldsV rd C V) {s : Oq} (hs : s.RowShape) (hcd : 2 ≤ s.cd)
    (hcd8 : s.cd ≤ 8) (hW : WalkFnK (oqWalkOf s) s.pd s.cd)
    (hA : BlockOkC C rd σ (oqMainAK s 1 (oqWalkOf s))) {S : Digest}
    (hkeyC : ∀ c : Fin 13, LoadHolds rd (σ (.n 0)) (4 * 2 ^ s.cd + c.val) (keyCells S c))
    (hbool : ∀ bp, LoadHolds rd (σ (.n 4)) 0 bp → WinRun rd bp (s.pd + s.cd) s.cd) :
    LoadHolds rd (σ (.n 4)) 0 (σ (.n 25)) ∧
      QueryWK S rd s (σ (.n 0)) (σ (.n 1)) (σ (.n 5)) (σ (.n 25))
        (oqQueryWK s rd (σ (.n 25)) (σ (.n 0)) (σ (.n 1)) 26 true σ V) (σ (.n (oqDot s 26))) ∧
      LoadHolds rd (σ (.n 24)) 0 (σ (.n (oqDot s 26)) * σ (.n 8)) := by
  have mem : BlockOkC C rd σ (oqQueryTK s (.n 25) (.n 0) (.n 1) (.n 5) 26 true 0 9 (oqWalkOf s)) :=
    hA.mono fun a ha => by simp only [oqMainAK, ↓reduceIte, List.mem_append]; simp_all
  have l25 := hA.atom (by simp [oqMainAK] : Stmt.atom (.load (.n 25) (.n 4) 0) ∈ _)
  have c1 := hA.atom (by simp [oqMainAK] :
    Stmt.atom (.mul (.n (oqMKK s 1 - 1)) (.n (oqDot s 26)) (.n 8)) ∈ _)
  have c2 := hA.atom (by simp [oqMainAK] : Stmt.atom (.load (.n (oqMKK s 1 - 1)) (.n 24) 0) ∈ _)
  simp only [Atom.Holds] at c1 l25
  refine ⟨l25, oqQuery_sound_wK hU hs hcd hcd8 hW mem (by simp) (oqMainA_keyK hA hkeyC) hkeyC
    (hbool _ l25), ?_⟩
  have := c2
  simp only [Atom.Holds, c1] at this
  exact this

theorem oqsOfK_length_one {s : Oq} (hb1 : s.base = 1) {odd : ℕ} (hodd : odd ≤ 1) (loop : String)
    (N : ℕ) (rd : Reader) (σ : Val) (V : SaltedGuest.End.FrameMap) :
    (oqsOfK s odd loop N rd σ V).length = odd + 2 * N := by
  unfold oqsOfK
  rw [List.length_append, oqLength_flatMap_range _ 2 (fun j => by simp [oqIterOfK, hb1])]
  split_ifs with h <;> simp <;> omega

theorem oqsOfK_length_zero {s : Oq} (hb0 : s.base = 0) (loop : String) (N : ℕ) (rd : Reader)
    (σ : Val) (V : SaltedGuest.End.FrameMap) : (oqsOfK s 0 loop N rd σ V).length = N := by
  unfold oqsOfK
  rw [List.length_append, oqLength_flatMap_range _ 1 (fun j => by simp [oqIterOfK, hb0])]
  simp

/-! ## The function -/

/-- The salted function's loop arguments after its counter, as the loop's frames read them. -/
theorem oqLoopArgsK_cons (σ : Val) : oqLoopArgsK σ =
    σ (.n 6) :: ([σ (.n 4), σ (.n 0), σ (.n 1)] ++ (oqKeyV 9).map σ ++ [σ (.n 5), σ (.n 24), σ (.n 8)]) :=
  rfl

/-- **The salted `opening_queries` at level 0 is sound with its queries named.** -/
theorem oqMain1_sound_wK {s : Oq} (hs : s.RowShape) (hb1 : s.base = 1)
    (hcd : 2 ≤ s.cd) (hcd8 : s.cd ≤ 8) {odd : ℕ} (hodd : odd ≤ 1) {name loop : String}
    (hW : WalkFnK (oqWalkOf s) s.pd s.cd) {fm fl : Fn}
    (hfm : SaltedGuest.coreProgram.find? name = some fm)
    (hpm : fm.params = [.n 0, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6])
    (hbm : fm.body = oqMainTK s odd (oqWalkOf s) loop)
    (hfl : SaltedGuest.coreProgram.find? loop = some fl) (hpl : fl.params = oqLoopParamsK)
    (hbl : fl.body = oqLoop1TK s odd (oqWalkOf s) loop) :
    opening_queries_sound_w_SpecK name loop s odd := by
  intro rd C V hU _ fm' σ args rets N hfm' hp hh hN hNo hbits S hS
  rw [hfm] at hfm'
  cases hfm'
  rw [hpm] at hp
  simp only [List.map_cons, List.map_nil] at hp
  subst hp
  simp only [List.getD_cons_succ, List.getD_cons_zero] at hN hbits hS
  rw [hbm, oqMainTK, holdsList_append, holdsList_flatC (oqMainAK_flatC s odd (oqWalkOf s))] at hh
  obtain ⟨hA, h⟩ := hh
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, List.map_cons, List.map_nil] at h
  obtain ⟨-, hcall, e3, e4, e5, hret⟩ := h
  obtain ⟨hmu, hg, hst, h0even⟩ := oqMainA_basicK hA
  have hkey := oqMainA_keyK hA hS
  have hlam : σ (.n 2) ≠ 0 := fun h0 => by rw [h0, mul_zero] at hmu; exact zero_ne_one hmu
  have hmuinv : σ (.n 8) = (σ (.n 2))⁻¹ := eq_inv_of_mul_eq_one_left hmu
  rw [hb1] at hbits
  simp only [oqCount, ↓reduceIte] at hbits
  -- the iterations' frames
  have hfr := loopV_framesK (rd := rd) hU hfl (by rw [hbl]; rfl)
    (oqLoop1AK_flatC s odd (oqWalkOf s)) (Nv := σ (.n 6))
    (rest := [σ (.n 4), σ (.n 0), σ (.n 1)] ++ (oqKeyV 9).map σ ++ [σ (.n 5), σ (.n 24), σ (.n 8)])
    (fun τ x hp hA => oqLoop1_hcK hpl τ x hp hA) hN hNo (fun hN0 => by
      have hne : σ (.n (oqMKK s odd + 1)) ≠ 0 := by
        rw [hg, hN]
        intro h0
        have := (gen_pow_eq_one_iff hNo).mp (e_add_eq_zero_iff.mp h0).symm
        omega
      have := hcall hne
      rw [show ([.n (oqMKK s odd + 2), .n 6, .n 4, .n 0, .n 1] ++ oqKeyV 9 ++
          [.n 5, .n 24, .n 8] : List Core.V).map σ = σ (.n (oqMKK s odd + 2)) :: σ (.n 6) ::
          ([σ (.n 4), σ (.n 0), σ (.n 1)] ++ (oqKeyV 9).map σ ++
            [σ (.n 5), σ (.n 24), σ (.n 8)]) by simp, hst] at this
      exact this)
  set τ : ℕ → Val := fun j => V loop (gen ^ j :: oqLoopArgsK σ) [] with hτ
  have hit : ∀ j < N, ∃ v : E,
      LoadHolds rd (σ (.n 4)) (2 * j + odd) (τ j (.n 23)) ∧
      QueryWK S rd s (σ (.n 0)) (σ (.n 1)) (σ (.n 5)) (τ j (.n 23))
        (oqQueryWK s rd (τ j (.n 23)) (τ j (.n 3)) (τ j (.n 4)) 24 true (τ j) V)
        (τ j (.n (oqDot s 24))) ∧
      LoadHolds rd (σ (.n 4)) (2 * j + odd + 1) (τ j (.n (oqE1K s))) ∧
      QueryWK S rd s (σ (.n 0)) (σ (.n 1)) (σ (.n 5)) (τ j (.n (oqE1K s)))
        (oqQueryWK s rd (τ j (.n (oqE1K s))) (τ j (.n 3)) (τ j (.n 4)) (oqE1K s + 1) false (τ j) V)
        (τ j (.n (oqDot s (oqE1K s + 1)))) ∧
      LoadHolds rd (σ (.n 24)) j v ∧
      LoadHolds rd (σ (.n 24)) (j + 1) (((v + τ j (.n (oqDot s 24))) * σ (.n 8) +
        τ j (.n (oqDot s (oqE1K s + 1)))) * σ (.n 8)) := by
    intro j hj
    obtain ⟨hp, hA⟩ := hfr j hj
    rw [← oqLoopArgsK_cons] at hp hA
    obtain ⟨t0, -, t2, t3, t4, tk, t18, t19, t20⟩ := loop_paramsK hpl hp
    have := oqIter1_sound_wK hU hs hcd hcd8 hW (odd := odd) (i := j) hA t0 (S := S)
      (fun c ↦ (tk c).trans (hkey c)) (by rw [t3]; exact hS) (fun k hk bp hbp => by
        rw [t2] at hbp
        exact hbits k (by omega) bp hbp)
    obtain ⟨v, a1, a2, a3, a4, a5, a6⟩ := this
    rw [t2] at a1 a3
    rw [t19] at a5 a6
    rw [t20] at a6
    refine ⟨v, a1, ?_, a3, ?_, a5, a6⟩
    · rw [← t3, ← t4, ← t18]; exact a2
    · rw [← t3, ← t4, ← t18]; exact a4
  choose! v hit using hit
  -- the main query
  have hM : odd = 1 → LoadHolds rd (σ (.n 4)) 0 (σ (.n 25)) ∧
      QueryWK S rd s (σ (.n 0)) (σ (.n 1)) (σ (.n 5)) (σ (.n 25))
        (oqQueryWK s rd (σ (.n 25)) (σ (.n 0)) (σ (.n 1)) 26 true σ V) (σ (.n (oqDot s 26))) ∧
      LoadHolds rd (σ (.n 24)) 0 (σ (.n (oqDot s 26)) * σ (.n 8)) := by
    intro h1
    subst h1
    exact oqMainA_odd_wK hU hs hcd hcd8 hW hA hS (fun bp hbp => hbits 0 (by omega) bp hbp)
  -- the queries' functions
  let fsel : ∀ {α : Type}, α → (ℕ → α) → (ℕ → α) → ℕ → α := fun a f g k =>
    if k < odd then a else if (k - odd) % 2 = 0 then f ((k - odd) / 2) else g ((k - odd) / 2)
  have fsel0 : ∀ {α : Type} (a : α) (f g : ℕ → α) (j : ℕ), fsel a f g (odd + 2 * j) = f j :=
    fun a f g j => by simp [fsel]
  have fsel1 : ∀ {α : Type} (a : α) (f g : ℕ → α) (j : ℕ), fsel a f g (odd + 2 * j + 1) = g j :=
    fun a f g j => by
      simp [fsel, show ¬ odd + 2 * j + 1 < odd by omega,
        show (odd + 2 * j + 1 - odd) % 2 = 1 by omega, show (odd + 2 * j + 1 - odd) / 2 = j by omega]
  have fselM : ∀ {α : Type} (a : α) (f g : ℕ → α), odd = 1 → fsel a f g 0 = a :=
    fun a f g h => by simp [fsel, h]
  set D0 : ℕ → E := fun j => τ j (.n (oqDot s 24)) with hD0
  set D1 : ℕ → E := fun j => τ j (.n (oqDot s (oqE1K s + 1))) with hD1
  set B0 : ℕ → E := fun j => τ j (.n 23) with hB0
  set B1 : ℕ → E := fun j => τ j (.n (oqE1K s)) with hB1
  set ds := fsel (σ (.n (oqDot s 26))) D0 D1 with hds
  set ws := oqsOfK s odd loop N rd σ V with hws
  have hwsM : odd = 1 → ws.getD 0 default =
      oqQueryWK s rd (σ (.n 25)) (σ (.n 0)) (σ (.n 1)) 26 true σ V := by
    intro h1; subst h1; simp [hws, oqsOfK]
  have hwsI : ∀ j < N, ∀ e < 2, ws.getD (odd + (2 * j + e)) default =
      (oqIterOfK s rd (τ j) V).getD e default := by
    intro j hj e he
    have hl : (if odd = 1 then [oqQueryWK s rd (σ (.n 25)) (σ (.n 0)) (σ (.n 1)) 26 true σ V]
        else []).length = odd := by
      split_ifs with h <;> simp <;> omega
    simp only [hws, oqsOfK]
    rw [List.getD_append_right _ _ _ _ (by omega), hl, Nat.add_sub_cancel_left]
    exact oqGetD_flatMap_range _ 2 (fun j => by simp [oqIterOfK, hb1]) default N j e hj he
  -- the chain
  have hchain : ∀ i ≤ N, LoadHolds rd (σ (.n 24)) i (oqChain odd s.base (σ (.n 2))⁻¹ ds i) := by
    intro i hi
    induction i with
    | zero =>
      by_cases h1 : odd = 1
      · have := (hM h1).2.2
        simp only [oqChain, h1, ↓reduceIte]
        rw [hds, fselM (α := E) (σ (.n (oqDot s 26))) D0 D1 h1, ← hmuinv]
        exact this
      · simp only [oqChain, h1, ↓reduceIte]
        exact h0even h1
    | succ i ih =>
      obtain ⟨-, -, -, -, hv, hv1⟩ := hit i (by omega)
      have e := loadHolds_unique hv (ih (by omega))
      rw [e] at hv1
      have q0 : ds (odd + 2 * i) = τ i (.n (oqDot s 24)) := fsel0 (α := E) _ D0 D1 i
      have q1 : ds (odd + 2 * i + 1) = τ i (.n (oqDot s (oqE1K s + 1))) := fsel1 (α := E) _ D0 D1 i
      rw [oqChain_succ_one hb1, q0, q1]
      rw [hmuinv] at hv1
      exact hv1
  have hlast := e4
  rw [e3, hN, loadHolds_mul_gen_pow, Nat.add_zero] at hlast
  have hv := loadHolds_unique hlast (hchain N le_rfl)
  refine ⟨N, hNo, hN, hlam, by rw [hws, oqsOfK_length_one hb1 hodd, hb1]; simp [oqCount],
    fsel (σ (.n 25)) B0 B1, ds, fun k hk => ?_, σ (.n 24), hchain, ?_⟩
  · simp only [oqCount, hb1, ↓reduceIte] at hk
    by_cases hk0 : k < odd
    · have h1 : odd = 1 := by omega
      obtain rfl : k = 0 := by omega
      obtain ⟨a1, a2, -⟩ := hM h1
      rw [fselM (α := E) (σ (.n 25)) B0 B1 h1, hds, fselM (α := E) (σ (.n (oqDot s 26))) D0 D1 h1,
        hwsM h1]
      exact ⟨a1, a2⟩
    · obtain ⟨j, hj, hk'⟩ : ∃ j < N, k = odd + 2 * j ∨ k = odd + 2 * j + 1 :=
        ⟨(k - odd) / 2, by omega, by omega⟩
      obtain ⟨a1, a2, a3, a4, -⟩ := hit j hj
      have hI : oqIterOfK s rd (τ j) V =
          [oqQueryWK s rd (τ j (.n 23)) (τ j (.n 3)) (τ j (.n 4)) 24 true (τ j) V,
            oqQueryWK s rd (τ j (.n (oqE1K s))) (τ j (.n 3)) (τ j (.n 4)) (oqE1K s + 1) false
              (τ j) V] := by simp [oqIterOfK, hb1]
      rcases hk' with rfl | rfl
      · rw [fsel0 (α := E) (σ (.n 25)) B0 B1 j, hds, fsel0 (α := E) (σ (.n (oqDot s 26))) D0 D1 j,
          show odd + 2 * j = odd + (2 * j + 0) by omega, hwsI j hj 0 (by omega), hI,
          List.getD_cons_zero, show odd + (2 * j + 0) = 2 * j + odd by omega]
        exact ⟨a1, a2⟩
      · rw [fsel1 (α := E) (σ (.n 25)) B0 B1 j, hds, fsel1 (α := E) (σ (.n (oqDot s 26))) D0 D1 j,
          show odd + 2 * j + 1 = odd + (2 * j + 1) by omega, hwsI j hj 1 (by omega), hI,
          List.getD_cons_succ, List.getD_cons_zero, show odd + (2 * j + 1) = 2 * j + odd + 1 by omega]
        exact ⟨a3, a4⟩
  · rw [← hret, e5, hv]

/-- **The salted `opening_queries` deeper is sound with its queries named.** -/
theorem oqMain0_sound_wK {s : Oq} (hs : s.RowShape) (hb0 : s.base = 0)
    (hcd : 2 ≤ s.cd) (hcd8 : s.cd ≤ 8) {name loop : String}
    (hW : WalkFnK (oqWalkOf s) s.pd s.cd) {fm fl : Fn}
    (hfm : SaltedGuest.coreProgram.find? name = some fm)
    (hpm : fm.params = [.n 0, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6])
    (hbm : fm.body = oqMainTK s 0 (oqWalkOf s) loop)
    (hfl : SaltedGuest.coreProgram.find? loop = some fl) (hpl : fl.params = oqLoopParamsK)
    (hbl : fl.body = oqLoop0TK s (oqWalkOf s) loop) :
    opening_queries_sound_w_SpecK name loop s 0 := by
  intro rd C V hU _ fm' σ args rets N hfm' hp hh hN hNo hbits S hS
  rw [hfm] at hfm'
  cases hfm'
  rw [hpm] at hp
  simp only [List.map_cons, List.map_nil] at hp
  subst hp
  simp only [List.getD_cons_succ, List.getD_cons_zero] at hN hbits hS
  rw [hbm, oqMainTK, holdsList_append, holdsList_flatC (oqMainAK_flatC s 0 (oqWalkOf s))] at hh
  obtain ⟨hA, h⟩ := hh
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, List.map_cons, List.map_nil] at h
  obtain ⟨-, hcall, e3, e4, e5, hret⟩ := h
  obtain ⟨hmu, hg, hst, h0even⟩ := oqMainA_basicK hA
  have hkey := oqMainA_keyK hA hS
  have hlam : σ (.n 2) ≠ 0 := fun h0 => by rw [h0, mul_zero] at hmu; exact zero_ne_one hmu
  have hmuinv : σ (.n 8) = (σ (.n 2))⁻¹ := eq_inv_of_mul_eq_one_left hmu
  rw [hb0] at hbits
  simp only [oqCount, show (0 : ℕ) ≠ 1 by decide, ↓reduceIte] at hbits
  have hfr := loopV_framesK (rd := rd) hU hfl (by rw [hbl]; rfl) (oqLoop0AK_flatC s (oqWalkOf s))
    (Nv := σ (.n 6))
    (rest := [σ (.n 4), σ (.n 0), σ (.n 1)] ++ (oqKeyV 9).map σ ++ [σ (.n 5), σ (.n 24), σ (.n 8)])
    (fun τ x hp hA => oqLoop0_hcK hpl τ x hp hA) hN hNo (fun hN0 => by
      have hne : σ (.n (oqMKK s 0 + 1)) ≠ 0 := by
        rw [hg, hN]
        intro h0
        have := (gen_pow_eq_one_iff hNo).mp (e_add_eq_zero_iff.mp h0).symm
        omega
      have := hcall hne
      rw [show ([.n (oqMKK s 0 + 2), .n 6, .n 4, .n 0, .n 1] ++ oqKeyV 9 ++
          [.n 5, .n 24, .n 8] : List Core.V).map σ = σ (.n (oqMKK s 0 + 2)) :: σ (.n 6) ::
          ([σ (.n 4), σ (.n 0), σ (.n 1)] ++ (oqKeyV 9).map σ ++
            [σ (.n 5), σ (.n 24), σ (.n 8)]) by simp, hst] at this
      exact this)
  set τ : ℕ → Val := fun j => V loop (gen ^ j :: oqLoopArgsK σ) [] with hτ
  have hit : ∀ j < N, ∃ v : E,
      LoadHolds rd (σ (.n 4)) j (τ j (.n 22)) ∧
      QueryWK S rd s (σ (.n 0)) (σ (.n 1)) (σ (.n 5)) (τ j (.n 22))
        (oqQueryWK s rd (τ j (.n 22)) (τ j (.n 3)) (τ j (.n 4)) 23 true (τ j) V)
        (τ j (.n (oqDot s 23))) ∧
      LoadHolds rd (σ (.n 24)) j v ∧
      LoadHolds rd (σ (.n 24)) (j + 1) ((v + τ j (.n (oqDot s 23))) * σ (.n 8)) := by
    intro j hj
    obtain ⟨hp, hA⟩ := hfr j hj
    rw [← oqLoopArgsK_cons] at hp hA
    obtain ⟨t0, -, t2, t3, t4, tk, t18, t19, t20⟩ := loop_paramsK hpl hp
    have := oqIter0_sound_wK hU hs hcd hcd8 hW (i := j) hA t0 (S := S)
      (fun c ↦ (tk c).trans (hkey c)) (by rw [t3]; exact hS) (fun bp hbp => by
        rw [t2] at hbp
        exact hbits j hj bp hbp)
    obtain ⟨v, a1, a2, a3, a4⟩ := this
    rw [t2] at a1
    rw [t19] at a3 a4
    rw [t20] at a4
    refine ⟨v, a1, ?_, a3, a4⟩
    rw [← t3, ← t4, ← t18]; exact a2
  choose! v hit using hit
  set ds := fun j => τ j (.n (oqDot s 23)) with hds
  set ws := oqsOfK s 0 loop N rd σ V with hws
  have hwsI : ∀ j < N, ws.getD j default =
      oqQueryWK s rd (τ j (.n 22)) (τ j (.n 3)) (τ j (.n 4)) 23 true (τ j) V := by
    intro j hj
    simp only [hws, oqsOfK, show (0 : ℕ) ≠ 1 by decide, ↓reduceIte, List.nil_append]
    have := oqGetD_flatMap_range (fun j => oqIterOfK s rd (V loop (gen ^ j :: oqLoopArgsK σ) []) V)
      1 (fun j => by simp [oqIterOfK, hb0]) default N j 0 hj (by omega)
    rw [Nat.one_mul, Nat.add_zero] at this
    rw [this]
    simp [oqIterOfK, hb0, hτ]
  have hchain : ∀ i ≤ N, LoadHolds rd (σ (.n 24)) i (oqChain 0 s.base (σ (.n 2))⁻¹ ds i) := by
    intro i hi
    induction i with
    | zero =>
      simp only [oqChain, show (0 : ℕ) ≠ 1 by decide, ↓reduceIte]
      exact h0even (by decide)
    | succ i ih =>
      obtain ⟨-, -, hv, hv1⟩ := hit i (by omega)
      have e := loadHolds_unique hv (ih (by omega))
      rw [e] at hv1
      rw [oqChain_succ_zero hb0]
      rw [hmuinv] at hv1
      exact hv1
  have hlast := e4
  rw [e3, hN, loadHolds_mul_gen_pow, Nat.add_zero] at hlast
  have hv := loadHolds_unique hlast (hchain N le_rfl)
  refine ⟨N, hNo, hN, hlam, by rw [hws, oqsOfK_length_zero hb0, hb0]; simp [oqCount],
    fun j => τ j (.n 22), ds, fun k hk => ?_, σ (.n 24), hchain, ?_⟩
  · simp only [oqCount, hb0, show (0 : ℕ) ≠ 1 by decide, ↓reduceIte] at hk
    obtain ⟨a1, a2, -⟩ := hit k hk
    rw [hwsI k hk]
    exact ⟨a1, a2⟩
  · rw [← hret, e5, hv]

end
end LeanVM.SaltedGuest.B1
