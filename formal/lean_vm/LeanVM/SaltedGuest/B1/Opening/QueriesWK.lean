/-
  LeanVM.SaltedGuest.B1.Opening.QueriesWK

  A salted query and a salted loop iteration, sound at their witnesses: the leaf hashed and climbed
  under the key.
-/

module

public import LeanVM.SaltedGuest.B1.Opening.QueriesLeafK
public import LeanVM.SaltedGuest.B1.Opening.WalkFnsK
public import LeanVM.SaltedGuest.B1.Whir.QueriesOpenWK
public import LeanVM.SaltedGuest.EndKnow
public import LeanVM.Guest.B1.Opening.QueriesW

/-!
# A salted query, at its witness

The deployed `oqQuery_sound_s`, `oqQuery_sound_w`, `oqIter1_sound_w`, `oqIter0_sound_w` and
`loopV_frames` for the salted templates (`QueriesTK`) and the salted core IR: the leaf is the keyed
digest of the row (`oqLeaf_soundK`, the key's cells of `S` the query's `kc ..` values), the walk is
the salted `walk_path` (`WalkFnK`, the key of `S` in the cap's buffer, its children cells from
`wkCh`), each query `QueryOpensSK S`. A query's witness `oqQueryWK` reads its siblings off the salted
walk's frame.
-/

namespace LeanVM.SaltedGuest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Guest.B1 LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile
open LeanVM.Protocol.Verifier LeanVM.SaltedGuest.B1.Whir Recursion.Salted

@[expose] public section

variable {rd : Reader} {σ : Val}

/-! ## A query's pieces -/

theorem oqQuery_piecesK {C : CallRel} {s : Oq} {bp cap flags wp : V} {b : ℕ} {emit : Bool}
    {pr kc : ℕ} {walk : String} (hA : BlockOkC C rd σ (oqQueryTK s bp cap flags wp b emit pr kc walk)) :
    (∀ a, Stmt.atom a ∈ oqPacksT b s.R → a.Holds rd σ) ∧
      (∀ a, Stmt.atom a ∈ oqDotT s wp b → a.Holds rd σ) ∧
      (∀ a, Stmt.atom a ∈ oqLeafTK s emit b pr kc (oqKLK s b) → a.Holds rd σ) ∧
      C walk [σ (.n (oqOutK s emit (oqKLK s b) (s.B - 1) 0)),
        σ (.n (oqOutK s emit (oqKLK s b) (s.B - 1) 1)), σ bp, σ cap, σ flags] [] := by
  refine ⟨fun a h => hA.atom ?_, fun a h => hA.atom ?_, fun a h => hA.atom ?_, ?_⟩
  · simp only [oqQueryTK, List.mem_append]; simp_all
  · simp only [oqQueryTK, List.mem_append]; simp_all
  · simp only [oqQueryTK, List.mem_append]; simp_all
  · have := hA.call (f := walk) (args := [.n (oqOutK s emit (oqKLK s b) (s.B - 1) 0),
      .n (oqOutK s emit (oqKLK s b) (s.B - 1) 1), bp, cap, flags]) (rets := [])
      (by simp [oqQueryTK])
    simpa using this

/-- **A salted query's leaf** is the keyed digest of its row. -/
theorem oqQuery_leafK {C : CallRel} {s : Oq} (hs : s.RowShape) {bp cap flags wp : V} {b : ℕ}
    {emit : Bool} {pr kc : ℕ} {walk : String}
    (hA : BlockOkC C rd σ (oqQueryTK s bp cap flags wp b emit pr kc walk))
    (hpad : emit = false → σ (.n pr) = word 1 0 0)
    {S : Digest} (hkey : ∀ c : Fin 13, σ (.n (kc + c.val)) = keyCells S c) :
    (σ (.n (oqOutK s emit (oqKLK s b) (s.B - 1) 0)),
      σ (.n (oqOutK s emit (oqKLK s b) (s.B - 1) 1))) =
      digestHalves (keyedHash S ((oqRow b s.R σ).flatMap K.toBytes)) := by
  obtain ⟨hP, -, hL, -⟩ := oqQuery_piecesK hA
  have hR2 : s.R % 2 = 0 := by rcases hs with ⟨hb, hI⟩ | ⟨hb, hI⟩ <;> simp [Oq.R, hb, hI]
  have hpk : ∀ j < s.ncells, σ (.n (oqPk b s.R j)) =
      E.ofLimbs ((oqRow b s.R σ).getD (2 * j) 0) ((oqRow b s.R σ).getD (2 * j + 1) 0) 0 :=
    fun j hj => by
      have hj' : j < s.R / 2 := hj
      rw [(oqPack_sound hP hj').2.2, getD_oqRow (by omega), getD_oqRow (by omega)]
      rfl
  exact oqLeaf_soundK hs hL hpad hkey (by simp [oqRow, Oq.ncells]; omega) hpk

/-- **The padding run a query emits** is its leaf's `0x01` cell's: `1` at `oqPadPosK`. -/
theorem oqPad_memK {s : Oq} (hs : s.RowShape) {bp cap flags wp : V} {b pr kc : ℕ} {walk : String} :
    Stmt.atom (.const (.n (oqPadPosK s b)) (word 1 0 0)) ∈
      oqQueryTK s bp cap flags wp b true pr kc walk := by
  have hL := leafShape_of s hs
  have key : (s.ncells = 32 ∧ s.B = 4) ∨ (s.ncells = 24 ∧ s.B = 3) := by
    rcases hs with ⟨hb, hI⟩ | ⟨hb, hI⟩
    · left; simp [Oq.B, Oq.ncells, Oq.R, hb, hI, rate]
    · right; simp [Oq.B, Oq.ncells, Oq.R, hb, hI, rate]
  have hm : 17 * (s.B - 1) / 2 + (s.ncells - 17 * (s.B - 1) / 2) = s.ncells := by
    rcases key with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2]
  have hc : s.ncells - 17 * (s.B - 1) / 2 < 9 := by
    rcases key with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2] <;> norm_num
  have hB : s.B - 1 < s.B := by have := hL.B2; omega
  simp only [oqQueryTK, List.mem_append]
  refine Or.inl (Or.inr (mem_oqLeafTK hB (mem_oqBlockTK_xor hc ?_)))
  simp [oqXorTK, hm, oqPadT, oqPadPosK]

/-! ## A query at its witness -/

/-- The arguments of a salted query's `walk_path` call. -/
def oqWalkArgsK (s : Oq) (b : ℕ) (emit : Bool) (bp cap flags : E) (σ : Val) : List E :=
  [σ (.n (oqOutK s emit (oqKLK s b) (s.B - 1) 0)), σ (.n (oqOutK s emit (oqKLK s b) (s.B - 1) 1)),
    bp, cap, flags]

/-- **The salted query hinted at `b`**: its position, its row and its siblings off its salted
walk's frame. -/
def oqQueryWK (s : Oq) (rd : Reader) (bp cap flags : E) (b : ℕ) (emit : Bool) (σ : Val)
    (V : SaltedGuest.End.FrameMap) : QW :=
  (winPosOf rd bp (s.pd + s.cd) s.cd, oqRow b s.R σ,
    oqSibsOf s.pd wkCh (winPosOf rd bp (s.pd + s.cd) s.cd)
      (V (oqWalkOf s) (oqWalkArgsK s b emit bp cap flags σ) []))

/-- What a salted query establishes of its witness `w` under the seed `S`. -/
def QueryWK (S : Digest) (rd : Reader) (s : Oq) (cap flags wp bp : E) (w : QW) (d : E) : Prop :=
  w.1 < 2 ^ (s.pd + s.cd) ∧
    (∀ i < qwN (s.pd + s.cd) s.cd, LoadHolds rd bp i (gen ^ qwVal (s.pd + s.cd) s.cd w.1 i)) ∧
    QueryOpensSK S rd s.base s.I (s.pd + s.cd) s.cd cap flags wp w.1 w.2.1 w.2.2 d

/-- **A salted query is `QueryOpensSK S`** at its row and the siblings its walk's frame holds. -/
theorem oqQuery_sound_sK {C : CallRel} {V : SaltedGuest.End.FrameMap}
    (hU : SaltedGuest.End.UnfoldsV rd C V) {s : Oq} (hs : s.RowShape) (hcd : 1 ≤ s.cd)
    (hW : WalkFnK (oqWalkOf s) s.pd s.cd) {bp cap flags wp : Core.V} {b : ℕ} {emit : Bool}
    {pr kc : ℕ} (hA : BlockOkC C rd σ (oqQueryTK s bp cap flags wp b emit pr kc (oqWalkOf s)))
    (hpad : emit = false → σ (.n pr) = word 1 0 0)
    {S : Digest} (hkey : ∀ c : Fin 13, σ (.n (kc + c.val)) = keyCells S c)
    (hkeyC : ∀ c : Fin 13, LoadHolds rd (σ cap) (4 * 2 ^ s.cd + c.val) (keyCells S c))
    {q : ℕ} (hq : q < 2 ^ (s.pd + s.cd))
    (hwin : ∀ i v, LoadHolds rd (σ bp) i v → i < qwN (s.pd + s.cd) s.cd →
      v = gen ^ qwVal (s.pd + s.cd) s.cd q i) :
    (∀ i < qwN (s.pd + s.cd) s.cd, LoadHolds rd (σ bp) i (gen ^ qwVal (s.pd + s.cd) s.cd q i)) ∧
    QueryOpensSK S rd s.base s.I (s.pd + s.cd) s.cd (σ cap) (σ flags) (σ wp) q (oqRow b s.R σ)
      (oqSibsOf s.pd wkCh q (V (oqWalkOf s) (oqWalkArgsK s b emit (σ bp) (σ cap) (σ flags) σ) []))
      (σ (.n (oqDot s b))) := by
  obtain ⟨hP, hD, -, hcall⟩ := oqQuery_piecesK hA
  obtain ⟨fn, hf, hp, hb⟩ := hW
  obtain ⟨fn', hf', hpar, hh⟩ := hU _ _ _ hcall
  rw [hf] at hf'
  cases hf'
  rw [hp] at hpar
  rw [hb] at hh
  obtain ⟨-, hwl, sibs, hsl, hsib, hflag, hc0, hc1⟩ :=
    wpK_frame_sound (s := ⟨0, 0, s.pd, s.cd⟩) hcd hpar hh (oqQuery_leafK hs hA hpad hkey) hq hwin
      hkeyC
  have hrl : (oqRow b s.R σ).length = s.R := by simp [oqRow]
  have hWd := oqWord_sound hs hP hD
  obtain ⟨hw, hdot⟩ := oqDot_sound hs hD hWd
  refine ⟨hwl, ?_⟩
  rw [show oqWalkArgsK s b emit (σ bp) (σ cap) (σ flags) σ =
    [σ (.n (oqOutK s emit (oqKLK s b) (s.B - 1) 0)), σ (.n (oqOutK s emit (oqKLK s b) (s.B - 1) 1)),
      σ bp, σ cap, σ flags] from rfl, oqSibsOf_eq hsl hsib]
  unfold QueryOpensSK
  rw [show s.pd + s.cd - s.cd = s.pd by omega]
  refine ⟨by rw [hrl]; rfl, hsl, oqW s b σ, fun l hl => hw l (by simpa [Oq.lo] using hl),
    hc0, hc1, hflag, ?_⟩
  rw [hdot, rowDot_eq]
  congr 1

/-- **A salted query whose window pointer names a position's windows** is sound at its witness
`oqQueryWK`. -/
theorem oqQuery_sound_wK {C : CallRel} {V : SaltedGuest.End.FrameMap}
    (hU : SaltedGuest.End.UnfoldsV rd C V) {s : Oq} (hs : s.RowShape) (hcd : 2 ≤ s.cd)
    (hcd8 : s.cd ≤ 8) (hW : WalkFnK (oqWalkOf s) s.pd s.cd) {bp cap flags wp : Core.V} {b : ℕ}
    {emit : Bool} {pr kc : ℕ}
    (hA : BlockOkC C rd σ (oqQueryTK s bp cap flags wp b emit pr kc (oqWalkOf s)))
    (hpad : emit = false → σ (.n pr) = word 1 0 0)
    {S : Digest} (hkey : ∀ c : Fin 13, σ (.n (kc + c.val)) = keyCells S c)
    (hkeyC : ∀ c : Fin 13, LoadHolds rd (σ cap) (4 * 2 ^ s.cd + c.val) (keyCells S c))
    (hrun : WinRun rd (σ bp) (s.pd + s.cd) s.cd) :
    QueryWK S rd s (σ cap) (σ flags) (σ wp) (σ bp)
      (oqQueryWK s rd (σ bp) (σ cap) (σ flags) b emit σ V) (σ (.n (oqDot s b))) := by
  obtain ⟨q, hq, -, hfr⟩ := hrun
  have hwin : ∀ i v, LoadHolds rd (σ bp) i v → i < qwN (s.pd + s.cd) s.cd →
      v = gen ^ qwVal (s.pd + s.cd) s.cd q i := fun i v hv hi ↦ hfr i hi v hv.2
  obtain ⟨hl, ho⟩ := oqQuery_sound_sK hU hs (by omega) hW hA hpad hkey hkeyC hq hwin
  have e : winPosOf rd (σ bp) (s.pd + s.cd) s.cd = q := winPosOf_eq hcd8 hq hl
  unfold oqQueryWK
  rw [e]
  exact ⟨hq, hl, ho⟩

/-! ## The iterations -/

/-- The key's cells of `S` are the loop's parameters `5 .. 17`. -/
def KeyParams (σ : Val) (S : Digest) : Prop := ∀ c : Fin 13, σ (.n (5 + c.val)) = keyCells S c

/-- **A salted level-0 iteration** at `x = g^i`, its two queries at their witnesses. -/
theorem oqIter1_sound_wK {C : CallRel} {V : SaltedGuest.End.FrameMap}
    (hU : SaltedGuest.End.UnfoldsV rd C V) {s : Oq} (hs : s.RowShape) (hcd : 2 ≤ s.cd)
    (hcd8 : s.cd ≤ 8) (hW : WalkFnK (oqWalkOf s) s.pd s.cd) {odd i : ℕ}
    (hA : BlockOkC C rd σ (oqLoop1AK s odd (oqWalkOf s))) (hx : σ (.n 0) = gen ^ i)
    {S : Digest} (hkey : KeyParams σ S)
    (hkeyC : ∀ c : Fin 13, LoadHolds rd (σ (.n 3)) (4 * 2 ^ s.cd + c.val) (keyCells S c))
    (hbool : ∀ k, k = 2 * i + odd ∨ k = 2 * i + odd + 1 → ∀ bp, LoadHolds rd (σ (.n 2)) k bp →
      WinRun rd bp (s.pd + s.cd) s.cd) :
    ∃ v : E,
      LoadHolds rd (σ (.n 2)) (2 * i + odd) (σ (.n 23)) ∧
      QueryWK S rd s (σ (.n 3)) (σ (.n 4)) (σ (.n 18)) (σ (.n 23))
        (oqQueryWK s rd (σ (.n 23)) (σ (.n 3)) (σ (.n 4)) 24 true σ V) (σ (.n (oqDot s 24))) ∧
      LoadHolds rd (σ (.n 2)) (2 * i + odd + 1) (σ (.n (oqE1K s))) ∧
      QueryWK S rd s (σ (.n 3)) (σ (.n 4)) (σ (.n 18)) (σ (.n (oqE1K s)))
        (oqQueryWK s rd (σ (.n (oqE1K s))) (σ (.n 3)) (σ (.n 4)) (oqE1K s + 1) false σ V)
        (σ (.n (oqDot s (oqE1K s + 1)))) ∧
      LoadHolds rd (σ (.n 19)) i v ∧
      LoadHolds rd (σ (.n 19)) (i + 1) (((v + σ (.n (oqDot s 24))) * σ (.n 20) +
        σ (.n (oqDot s (oqE1K s + 1)))) * σ (.n 20)) := by
  have p8 := hA.atom (by simp [oqLoop1AK] : Stmt.atom (.mul (.n 21) (.n 2) (.n 0)) ∈ _)
  have p9 := hA.atom (by simp [oqLoop1AK] : Stmt.atom (.mul (.n 22) (.n 21) (.n 0)) ∈ _)
  have p10 := hA.atom (by simp [oqLoop1AK] : Stmt.atom (.load (.n 23) (.n 22) odd) ∈ _)
  have pe1 := hA.atom (by simp [oqLoop1AK] : Stmt.atom (.load (.n (oqE1K s)) (.n 22) (odd + 1)) ∈ _)
  simp only [Atom.Holds] at p8 p9 p10 pe1
  have h9 : σ (.n 22) = σ (.n 2) * gen ^ (2 * i) := by rw [p9, p8, hx, mul_assoc, ← pow_add]; ring_nf
  rw [h9, loadHolds_mul_gen_pow] at p10 pe1
  have hq1 : BlockOkC C rd σ (oqQueryTK s (.n 23) (.n 3) (.n 4) (.n 18) 24 true 0 5 (oqWalkOf s)) :=
    hA.mono fun a h => by simp only [oqLoop1AK, List.mem_append]; simp_all
  have hq2 : BlockOkC C rd σ (oqQueryTK s (.n (oqE1K s)) (.n 3) (.n 4) (.n 18) (oqE1K s + 1) false
      (oqPadPosK s 24) 5 (oqWalkOf s)) :=
    hA.mono fun a h => by simp only [oqLoop1AK, List.mem_append]; simp_all
  have e1 : σ (.n (oqPadPosK s 24)) = word 1 0 0 := hq1.atom (oqPad_memK hs)
  have pe1' : LoadHolds rd (σ (.n 2)) (2 * i + odd + 1) (σ (.n (oqE1K s))) := by
    rw [show 2 * i + odd + 1 = 2 * i + (odd + 1) by omega]; exact pe1
  have w1 := oqQuery_sound_wK hU hs hcd hcd8 hW hq1 (by simp) hkey hkeyC (hbool _ (Or.inl rfl) _ p10)
  have w2 := oqQuery_sound_wK hU hs hcd hcd8 hW hq2 (fun _ ↦ e1) hkey hkeyC
    (hbool _ (Or.inr rfl) _ pe1')
  set c := oqC1K s with hc
  have c0 := hA.atom (by simp [oqLoop1AK, ← hc] : Stmt.atom (.mul (.n c) (.n 19) (.n 0)) ∈ _)
  have c1 := hA.atom (by simp [oqLoop1AK, ← hc] : Stmt.atom (.load (.n (c + 1)) (.n c) 0) ∈ _)
  have c2 := hA.atom (by simp [oqLoop1AK, ← hc] :
    Stmt.atom (.add (.n (c + 2)) (.n (c + 1)) (.n (oqDot s 24))) ∈ _)
  have c3 := hA.atom (by simp [oqLoop1AK, ← hc] :
    Stmt.atom (.mul (.n (c + 3)) (.n (c + 2)) (.n 20)) ∈ _)
  have c4 := hA.atom (by simp [oqLoop1AK, ← hc] :
    Stmt.atom (.add (.n (c + 4)) (.n (c + 3)) (.n (oqDot s (oqE1K s + 1)))) ∈ _)
  have c5 := hA.atom (by simp [oqLoop1AK, ← hc] :
    Stmt.atom (.mul (.n (c + 5)) (.n (c + 4)) (.n 20)) ∈ _)
  have c6 := hA.atom (by simp [oqLoop1AK, ← hc] : Stmt.atom (.mul (.n (c + 6)) (.n 19) (.n 0)) ∈ _)
  have c7 := hA.atom (by simp [oqLoop1AK, ← hc] :
    Stmt.atom (.load (.n (c + 5)) (.n (c + 6)) 1) ∈ _)
  simp only [Atom.Holds] at c0 c1 c2 c3 c4 c5 c6 c7
  rw [c0, hx, loadHolds_mul_gen_pow, Nat.add_zero] at c1
  rw [c6, hx, loadHolds_mul_gen_pow, c5, c4, c3, c2] at c7
  exact ⟨_, p10, w1, pe1', w2, c1, c7⟩

/-- **A salted deeper iteration** at `x = g^i`, its query at its witness. -/
theorem oqIter0_sound_wK {C : CallRel} {V : SaltedGuest.End.FrameMap}
    (hU : SaltedGuest.End.UnfoldsV rd C V) {s : Oq} (hs : s.RowShape) (hcd : 2 ≤ s.cd)
    (hcd8 : s.cd ≤ 8) (hW : WalkFnK (oqWalkOf s) s.pd s.cd) {i : ℕ}
    (hA : BlockOkC C rd σ (oqLoop0AK s (oqWalkOf s))) (hx : σ (.n 0) = gen ^ i)
    {S : Digest} (hkey : KeyParams σ S)
    (hkeyC : ∀ c : Fin 13, LoadHolds rd (σ (.n 3)) (4 * 2 ^ s.cd + c.val) (keyCells S c))
    (hbool : ∀ bp, LoadHolds rd (σ (.n 2)) i bp → WinRun rd bp (s.pd + s.cd) s.cd) :
    ∃ v : E, LoadHolds rd (σ (.n 2)) i (σ (.n 22)) ∧
      QueryWK S rd s (σ (.n 3)) (σ (.n 4)) (σ (.n 18)) (σ (.n 22))
        (oqQueryWK s rd (σ (.n 22)) (σ (.n 3)) (σ (.n 4)) 23 true σ V) (σ (.n (oqDot s 23))) ∧
      LoadHolds rd (σ (.n 19)) i v ∧
      LoadHolds rd (σ (.n 19)) (i + 1) ((v + σ (.n (oqDot s 23))) * σ (.n 20)) := by
  have p8 := hA.atom (by simp [oqLoop0AK] : Stmt.atom (.mul (.n 21) (.n 2) (.n 0)) ∈ _)
  have p9 := hA.atom (by simp [oqLoop0AK] : Stmt.atom (.load (.n 22) (.n 21) 0) ∈ _)
  simp only [Atom.Holds] at p8 p9
  rw [p8, hx, loadHolds_mul_gen_pow, Nat.add_zero] at p9
  have hq : BlockOkC C rd σ (oqQueryTK s (.n 22) (.n 3) (.n 4) (.n 18) 23 true 0 5 (oqWalkOf s)) :=
    hA.mono fun a h => by simp only [oqLoop0AK, List.mem_append]; simp_all
  have w1 := oqQuery_sound_wK hU hs hcd hcd8 hW hq (by simp) hkey hkeyC (hbool _ p9)
  set c := oqC0K s with hc
  have c0 := hA.atom (by simp [oqLoop0AK, ← hc] : Stmt.atom (.mul (.n c) (.n 19) (.n 0)) ∈ _)
  have c1 := hA.atom (by simp [oqLoop0AK, ← hc] : Stmt.atom (.load (.n (c + 1)) (.n c) 0) ∈ _)
  have c2 := hA.atom (by simp [oqLoop0AK, ← hc] :
    Stmt.atom (.add (.n (c + 2)) (.n (c + 1)) (.n (oqDot s 23))) ∈ _)
  have c3 := hA.atom (by simp [oqLoop0AK, ← hc] :
    Stmt.atom (.mul (.n (c + 3)) (.n (c + 2)) (.n 20)) ∈ _)
  have c4 := hA.atom (by simp [oqLoop0AK, ← hc] : Stmt.atom (.mul (.n (c + 4)) (.n 19) (.n 0)) ∈ _)
  have c5 := hA.atom (by simp [oqLoop0AK, ← hc] :
    Stmt.atom (.load (.n (c + 3)) (.n (c + 4)) 1) ∈ _)
  simp only [Atom.Holds] at c0 c1 c2 c3 c4 c5
  rw [c0, hx, loadHolds_mul_gen_pow, Nat.add_zero] at c1
  rw [c4, hx, loadHolds_mul_gen_pow, c3, c2] at c5
  exact ⟨_, p9, w1, c1, c5⟩

/-! ## A guarded loop's frames -/

/-- **A guarded loop's iterations hold at their frames** (the deployed `loopV_frames` over the
salted core IR). -/
theorem loopV_framesK {C : CallRel} {V : SaltedGuest.End.FrameMap}
    (hU : SaltedGuest.End.UnfoldsV rd C V) {f : String} {fn : Fn}
    (hf : SaltedGuest.coreProgram.find? f = some fn) {A : List Stmt} {c : ℕ} {args : List Core.V}
    (hb : fn.body = A ++ [.callIf (.n c) f args, .ret []]) (hA : FlatC A) {Nv : E}
    {rest : List E}
    (hc : ∀ (τ : Val) (x : E), fn.params.map τ = x :: Nv :: rest → BlockOkC C rd τ A →
      τ (.n c) = x * gen + Nv ∧ args.map τ = x * gen :: Nv :: rest)
    {N : ℕ} (hN : Nv = gen ^ N) (hNo : N < ordG) (h0 : 0 < N → C f (1 :: Nv :: rest) []) :
    ∀ j < N, fn.params.map (V f (gen ^ j :: Nv :: rest) []) = gen ^ j :: Nv :: rest ∧
      BlockOkC C rd (V f (gen ^ j :: Nv :: rest) []) A := by
  have unf : ∀ j, C f (gen ^ j :: Nv :: rest) [] →
      fn.params.map (V f (gen ^ j :: Nv :: rest) []) = gen ^ j :: Nv :: rest ∧
      BlockOkC C rd (V f (gen ^ j :: Nv :: rest) []) A ∧
      (V f (gen ^ j :: Nv :: rest) [] (.n c) ≠ 0 →
        C f (args.map (V f (gen ^ j :: Nv :: rest) [])) []) := by
    intro j hC
    obtain ⟨fn', hf', hp, hh⟩ := hU _ _ _ hC
    rw [hf] at hf'
    cases hf'
    rw [hb, holdsList_append, holdsList_flatC hA] at hh
    obtain ⟨hall, h⟩ := hh
    simp only [Stmt.HoldsList, Stmt.Holds] at h
    exact ⟨hp, hall, h.2.1⟩
  have calls : ∀ j < N, C f (gen ^ j :: Nv :: rest) [] := by
    intro j hj
    induction j with
    | zero => rw [pow_zero]; exact h0 hj
    | succ j ih =>
      obtain ⟨hp, hall, hcall⟩ := unf j (ih (by omega))
      obtain ⟨e1, e2⟩ := hc _ _ hp hall
      have := hcall (by
        rw [e1, hN, ← pow_succ]
        intro h
        have := gen_pow_inj (lt_trans (show j + 1 < N by omega) hNo) hNo (e_add_eq_zero_iff.mp h)
        omega)
      rwa [e2, ← pow_succ] at this
  intro j hj
  obtain ⟨hp, hall, -⟩ := unf j (calls j hj)
  exact ⟨hp, hall⟩

end
end LeanVM.SaltedGuest.B1
