/-
  LeanVM.SaltedGuest.Bounds.WhirK

  The price of the salted decoder's child proof reader.
-/

module

public import LeanVM.SaltedGuest.Bounds.V.Signatures
public import LeanVM.Cost.Bounds.Guest.Whir
public import LeanVM.SaltedGuest.Decoder.Proof

/-!
# The price of a salted child proof

The deployed `Cost/Bounds/Guest/Whir.lean` for the salted reader (`Decoder/Proof.lean`): the salted
`opening_queries`' cells (its first query at `25`, a loop iteration's at `22` and `23`, the
loop's other arguments `oqLoopArgsSK`, twenty words), each query's salted `walk_path` call
(`oqWalkArgsSK`, the siblings from the chain's `22`), `open_stacked`'s salted dispatch (function
`310 + m`, the selectors at `126` and `1725`, the cursor from `29` to `683`) and the table of the
salted `level_queries` dispatches (`osCallsTabK`). The valuations and the frame map are priced for
values of index below `2^64`, the frame map for calls of at most `24` words. Each lemma is the
deployed one of the name without `K`; the salted shapes (`OqOKK`, `CallOKK`, `WhirTabsOKK`) are the
deployed ones with the salted queries' last value and the dispatch's argument cells below `2^20`.
-/

namespace LeanVM.SaltedGuest.Bounds

open LeanVM.Cost.Bounds.Guest LeanVM.SaltedGuest.Decoder LeanVM.Cost LeanVM.Cost.Bounds
open LeanVM.Cost.Library LeanVM.Parameters LeanVM.Guest.Core LeanVM.Guest.B1 LeanVM.Guest.Fast
open LeanVM.SaltedGuest.B1 (oqE1K oqKLK oqBsK oqPadN oqOutK oqEndK oqKeyV)

public section

variable (P : MachineProgram)

/-! ## The salted levels' shapes -/

/-- A salted level's shape: the deployed `OqOK` and the salted queries' last value below `2^20`. -/
@[expose] def OqOKK (s : Oq) : Prop := OqOK s ∧ oqE1K s < 2 ^ 20

instance (s : Oq) : Decidable (OqOKK s) := by unfold OqOKK; infer_instance

/-- A salted `level_queries` dispatch: the deployed `CallOK`, the salted queries' last value and
the dispatch's argument cells below `2^20`. -/
@[expose] def CallOKK (c : OsCall) : Prop :=
  CallOK c ∧ oqE1K ⟨c.base, c.I, c.pd, c.cd⟩ < 2 ^ 20 ∧ ∀ k ∈ c.args, k < 2 ^ 20

instance (c : OsCall) : Decidable (CallOKK c) := by unfold CallOKK; infer_instance

theorem callOKK_osCallsTabK : osCallsTabK.length = 44 ∧ (∀ cs ∈ osCallsTabK, cs.length ≤ 7) ∧
    ∀ cs ∈ osCallsTabK, ∀ c ∈ cs, CallOKK c := by decide +kernel

theorem CallOKK.shape {c : OsCall} (hc : CallOKK c) : OqOKK ⟨c.base, c.I, c.pd, c.cd⟩ :=
  ⟨hc.1.1, hc.2.1⟩

/-- The salted `open_stacked`'s tables as arrays (`whirTabsK_ok`). -/
structure WhirTabsOKK (T : WhirTabs) : Prop where
  lanes : ∀ x ∈ T.lanes, x < 2 ^ 64
  words : ∀ m, T.words.getD m 0 ≤ 137
  calls : ∀ m, (T.calls.getD m []).length ≤ 7 ∧ ∀ c ∈ T.calls.getD m [], CallOKK c

theorem callOKK_getD (m : ℕ) :
    (osCallsTabK.getD m []).length ≤ 7 ∧ ∀ c ∈ osCallsTabK.getD m [], CallOKK c := by
  rw [List.getD_eq_getElem?_getD]
  cases hk : osCallsTabK[m]? with
  | none => simp
  | some cs =>
    have := List.mem_of_getElem? hk
    exact ⟨callOKK_osCallsTabK.2.1 cs this, callOKK_osCallsTabK.2.2 cs this⟩

theorem whirTabsK_ok : WhirTabsOKK whirTabsK := by
  refine ⟨gLanes_ok.2, fun m ↦ ?_, fun m ↦ ?_⟩
  · show osWordsTab.toArray.getD m 0 ≤ 137
    rw [getD_toArray, List.getD_eq_getElem?_getD]
    cases hk : osWordsTab[m]? with
    | none => simp
    | some x => exact osWordsTab_ok.2 x (List.mem_of_getElem? hk)
  · show (osCallsTabK.toArray.getD m []).length ≤ 7 ∧
      ∀ c ∈ osCallsTabK.toArray.getD m [], CallOKK c
    rw [getD_toArray]
    exact callOKK_getD m

/-- **The salted `open_stacked`'s tables, built** (`whirTabsKC`). -/
theorem whirTabsK_cost (hP : Includes P whirTabsKC.costDeps) :
    machineCost P whirTabsKC.costIdx [] ≤ 11134 := by
  rw [whirTabsKC.costEq P hP, Decoder.gLanesC.costEq P (by includes),
    Decoder.osWordsTabC.costEq P (by includes), osCallsTabKC.costEq P (by includes),
    osWordsTab_ok.1, callOKK_osCallsTabK.1]

theorem qargsK_lt {c : OsCall} (hpw : c.pw < 2 ^ 20) : ∀ k ∈ c.qargsK, k < 2 ^ 64 := by
  intro k hk
  simp only [OsCall.qargsK, List.mem_cons, List.not_mem_nil, or_false] at hk
  omega

theorem rets_lt {c : OsCall} (hr : c.ret0 < 2 ^ 20) : ∀ k ∈ c.rets, k < 2 ^ 64 := by
  intro k hk
  simp only [OsCall.rets, List.mem_cons, List.not_mem_nil, or_false] at hk
  omega

/-! ## The salted shape's numbers -/

section Shape

variable {s : Oq} (hs : OqOKK s)
include hs

theorem oqE1K_lt : oqE1K s < 2 ^ 20 := hs.2

theorem oqK1_lt (b : ℕ) (hb : b < 2 ^ 21) : oqK1 b s.R < 2 ^ 22 := by
  obtain ⟨⟨h1, h2, h3, h4, h5, -⟩, -⟩ := hs
  unfold oqK1; omega

theorem oqKLK_lt (b : ℕ) (hb : b < 2 ^ 21) : oqKLK s b < 2 ^ 23 := by
  have := oqK1_lt hs b hb
  obtain ⟨⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, -⟩, -⟩ := hs
  unfold oqKLK; omega

theorem oqKLK_cost (hP : Includes P oqKLKC.costDeps) (b : ℕ) (hb : b < 2 ^ 21) :
    machineCost P oqKLKC.costIdx [encodeValue s, encodeValue b] ≤ 124 := by
  have hr := Oq_R_cost P hs.1 (by includes)
  have hk := oqK1_cost P hs.1 (by includes) b hb
  have hd := Oq_D_cost P hs.1 (by includes)
  have := oqK1_lt hs b hb
  have := oqKLK_lt hs b hb
  have h11 := hs.1.2.2.2.2.2.2.2.2.2.2.1
  rw [oqKLKC.costEq P hP]
  unfold oqKLK at *
  cost_simp
  omega

theorem oqBsK_lt (kL : ℕ) (hkL : kL < 2 ^ 23) : oqBsK kL (s.B - 1) < 2 ^ 26 := by
  have h14 := hs.1.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  unfold oqBsK; omega

theorem oqBsK_cost (hP : Includes P oqBsKC.costDeps) (kL : ℕ) (hkL : kL < 2 ^ 23) :
    machineCost P oqBsKC.costIdx [encodeValue kL, encodeValue (s.B - 1)] ≤ 13 := by
  have h14 := hs.1.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  rw [oqBsKC.costEq P hP]
  cost_simp
  omega

omit hs in
theorem oqPadN_le (emit : Bool) (k : ℕ) : oqPadN s emit k ≤ 5 := by
  unfold oqPadN; split_ifs <;> omega

theorem oqPadN_cost (hP : Includes P oqPadNC.costDeps) (emit : Bool) :
    machineCost P oqPadNC.costIdx [encodeValue s, encodeValue emit, encodeValue (s.B - 1)] ≤ 40 := by
  have hB := Oq_B_cost P hs.1 (by includes)
  have h14 := hs.1.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  rw [oqPadNC.costEq P hP]
  cost_simp
  split_ifs <;> omega

theorem oqOutK_lt (emit : Bool) (kL : ℕ) (hkL : kL < 2 ^ 23) (c : ℕ) (hc : c ≤ 2) :
    oqOutK s emit kL (s.B - 1) c < 2 ^ 27 := by
  have := oqBsK_lt hs kL hkL
  have := oqPadN_le (s := s) emit (s.B - 1)
  unfold oqOutK; split_ifs <;> omega

theorem oqOutK_cost (hP : Includes P oqOutKC.costDeps) (emit : Bool) (kL : ℕ) (hkL : kL < 2 ^ 23)
    (c : ℕ) (hc : c ≤ 2) :
    machineCost P oqOutKC.costIdx
      [encodeValue s, encodeValue emit, encodeValue kL, encodeValue (s.B - 1), encodeValue c] ≤
        120 := by
  have hb := oqBsK_cost P hs (by includes) kL hkL
  have hbl := oqBsK_lt hs kL hkL
  have hB := Oq_B_cost P hs.1 (by includes)
  have hpd := oqPadN_cost P hs (by includes) emit
  have hpl := oqPadN_le (s := s) emit (s.B - 1)
  have h14 := hs.1.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  rw [oqOutKC.costEq P hP]
  cost_simp
  split_ifs <;> omega

theorem oqEndK_cost (hP : Includes P oqEndKC.costDeps) (b : ℕ) (hb : b < 2 ^ 21) (emit : Bool) :
    machineCost P oqEndKC.costIdx [encodeValue s, encodeValue b, encodeValue emit] ≤ 300 := by
  have hkl := oqKLK_cost P hs (by includes) b hb
  have hkl' := oqKLK_lt hs b hb
  have hB := Oq_B_cost P hs.1 (by includes)
  have ho := oqOutK_cost P hs (by includes) emit (oqKLK s b) hkl' 2 le_rfl
  have h14 := hs.1.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  rw [oqEndKC.costEq P hP]
  cost_simp
  omega

theorem oqE1K_cost (hP : Includes P oqE1KC.costDeps) :
    machineCost P oqE1KC.costIdx [encodeValue s] ≤ 304 := by
  have := oqEndK_cost P hs (by includes) 24 (by norm_num) true
  rw [oqE1KC.costEq P hP]
  omega

end Shape

/-! ## The salted queries' values -/

section Facts

variable {rd : Reader}

theorem length_oqIterAK (s : Oq) (lanes : List ℕ) (walk : ℕ) (rd : Reader) (σ : Val)
    (Vn : NFrames) : (oqIterAK s lanes walk rd σ Vn).length ≤ 2 := by
  unfold oqIterAK; split_ifs <;> simp

theorem oqQueryAK_facts (s : Oq) (lanes : List ℕ) (walk : ℕ) (bp cap flags : E) (b : ℕ)
    (emit : Bool) (σ : Val) (Vn : NFrames) :
    (oqQueryAK s lanes walk rd bp cap flags b emit σ Vn).1 < 2 ^ (s.pd + s.cd) ∧
      (oqQueryAK s lanes walk rd bp cap flags b emit σ Vn).2.2.length = s.pd := by
  unfold oqQueryAK oqQueryAtK oqSibsOf winPosOfW
  exact ⟨winPosAt_lt _ _ _, by simp⟩

theorem mem_oqItersFromK {s : Oq} {lanes : List ℕ} {loop walk : ℕ} {Vn : NFrames} {la : List E}
    {w : QW} : ∀ {N : ℕ} {x : E}, w ∈ oqItersFromK s lanes loop walk rd Vn la N x →
      w.1 < 2 ^ (s.pd + s.cd) ∧ w.2.2.length = s.pd
  | 0, _, h => by simp [oqItersFromK] at h
  | N + 1, x, h => by
    rw [oqItersFromK, List.mem_append] at h
    rcases h with h | h
    · unfold oqIterAK at h
      split_ifs at h
      · rcases List.mem_pair.1 h with rfl | rfl <;> exact oqQueryAK_facts _ _ _ _ _ _ _ _ _ _
      · rw [List.mem_singleton] at h; subst h; exact oqQueryAK_facts _ _ _ _ _ _ _ _ _ _
    · exact mem_oqItersFromK h

theorem mem_oqsOfAK {s : Oq} {lanes : List ℕ} {odd loop walk N : ℕ} {σ : Val} {Vn : NFrames}
    {w : QW} (h : w ∈ oqsOfAK s lanes odd loop walk N rd σ Vn) :
    w.1 < 2 ^ (s.pd + s.cd) ∧ w.2.2.length = s.pd := by
  unfold oqsOfAK at h
  rcases List.mem_append.1 h with h | h
  · split_ifs at h
    · rw [List.mem_singleton] at h; subst h; exact oqQueryAK_facts _ _ _ _ _ _ _ _ _ _
    · simp at h
  · exact mem_oqItersFromK h

theorem length_oqItersFromK (s : Oq) (lanes : List ℕ) (loop walk : ℕ) (Vn : NFrames)
    (la : List E) :
    ∀ (N : ℕ) (x : E), (oqItersFromK s lanes loop walk rd Vn la N x).length ≤ 2 * N
  | 0, _ => by simp [oqItersFromK]
  | N + 1, x => by
    rw [oqItersFromK, List.length_append]
    have := length_oqIterAK s lanes walk rd (Vn loop (x :: la) []) Vn
    have := length_oqItersFromK s lanes loop walk Vn la N (x * LeanVM.Protocol.Verifier.gen)
    omega

theorem length_oqsOfAK (s : Oq) (lanes : List ℕ) (odd loop walk N : ℕ) (σ : Val) (Vn : NFrames) :
    (oqsOfAK s lanes odd loop walk N rd σ Vn).length ≤ 1 + 2 * N := by
  unfold oqsOfAK
  rw [List.length_append]
  have := length_oqItersFromK (rd := rd) s lanes loop walk Vn (oqLoopArgsSK σ) N 1
  split_ifs <;> simp only [List.length_cons, List.length_nil] <;> omega

end Facts

section Reader

variable {rd : Reader} {rdV : MachineValue}
  (hrd : ∀ a : K, RunsApp P rdV [encodeValue a] (encodeValue (rd a)))
  {R : ℕ} (hR : ∀ a : K, appCost P rdV [encodeValue a] ≤ R)
include hrd hR

/-! ## A query -/

section Val

variable {σ : Val} {σV : MachineValue}
  (hσ : ∀ v : V, RunsApp P σV [encodeValue v] (encodeValue (σ v)))
  {S : ℕ} (hS : ∀ v : V, v.idx < 2 ^ 64 → appCost P σV [encodeValue v] ≤ S)
include hσ hS

omit hrd hR in
/-- A query's row (`oqRowC`), `R ≤ 192` words: `(S + 42)·192 + 17`. -/
theorem oqRow_costK (hP : Includes P Decoder.oqRowC.costDeps) (b Rw : ℕ)
    (hb : b < 2 ^ 21) (hRw : Rw ≤ 192) :
    machineCost P Decoder.oqRowC.costIdx [encodeValue b, encodeValue Rw, σV] ≤
      (S + 14 + 28) * 192 + 17 := by
  rw [Decoder.oqRowC.costEq P hP b Rw σ σV hσ]
  have := rangeMap_le P (by includes) (by includes) _
    (.closure Decoder.oqRowC.lam0.costIdx [encodeValue b, σV])
    (fun i ↦ RunsApp.of_spec (Decoder.oqRowC.lam0.costSpec P (by includes) b σ σV
      hσ i))
    (S + 14) Rw 192 hRw (by norm_num) (fun i hi ↦ by
      rw [appCost_fn, List.cons_append, List.cons_append, List.nil_append,
        Decoder.oqRowC.lam0.costEq P (by includes) b σ σV hσ, List.length_cons, List.length_cons, List.length_nil]
      have := hS (.n (b + i)) (by show b + i < 2 ^ 64; omega)
      limbs_one
      omega)
  omega

omit hrd hR in
/-- A query's siblings (`oqSibsOfC`), `pd ≤ 24` levels: `(2·S + 120 + 28)·24 + 19`. -/
theorem oqSibsOf_costK (hP : Includes P Decoder.oqSibsOfC.costDeps) (pd ch q : ℕ)
    (hpd : pd ≤ 24) (hch : ch < 2 ^ 24) (hq : q < 2 ^ 64) :
    machineCost P Decoder.oqSibsOfC.costIdx
      [encodeValue pd, encodeValue ch, encodeValue q, σV] ≤ (2 * S + 120 + 28) * 24 + 19 := by
  rw [Decoder.oqSibsOfC.costEq P hP pd ch q σ σV hσ]
  have := rangeMap_le P (by includes) (by includes) _
    (.closure Decoder.oqSibsOfC.lam0.costIdx [encodeValue ch, encodeValue q, σV])
    (fun l ↦ RunsApp.of_spec (Decoder.oqSibsOfC.lam0.costSpec P (by includes) ch q
      σ σV hσ l))
    (2 * S + 120) pd 24 hpd (by norm_num) (fun l hl ↦ by
      rw [appCost_fn, List.cons_append, List.cons_append, List.cons_append, List.nil_append,
        Decoder.oqSibsOfC.lam0.costEq P (by includes) ch q σ σV hσ, List.length_cons, List.length_cons, List.length_cons, List.length_nil]
      have := LeanVM.Cost.Bounds.Guest.testBit_cost P (by includes) q l hq (by omega)
      have hS' : ∀ k : ℕ, k < 2 ^ 64 → appCost P σV [encodeValue (V.n k)] ≤ S := fun k hk ↦ hS (.n k) hk
      split_ifs <;> limbs_one <;> cost_facts [digestOfCells640_cost P, hS'] <;> omega)
  omega

omit hrd hR in
/-- A query's `walk_path` call's words (`oqWalkArgsC`): the leaf digest's two cells, the window
pointer, the cap and the flags: `2·S + 500`. -/
theorem oqWalkArgs_costK (hP : Includes P oqWalkArgsSKC.costDeps) (s : Oq) (hs : OqOKK s)
    (b : ℕ) (hb : b < 2 ^ 21) (emit : Bool) (bp cap flags : E) :
    machineCost P oqWalkArgsSKC.costIdx [encodeValue s, encodeValue b, encodeValue emit,
      encodeValue bp, encodeValue cap, encodeValue flags, σV] ≤ 2 * S + 700 := by
  rw [oqWalkArgsSKC.costEq P hP s b emit bp cap flags σ σV hσ]
  have hkl := oqKLK_cost P hs (by includes) b hb
  have hkl' := oqKLK_lt hs b hb
  have hB := Oq_B_cost P hs.1 (by includes)
  have h0 := oqOutK_cost P hs (by includes) emit (oqKLK s b) hkl' 0 (by norm_num)
  have h1 := oqOutK_cost P hs (by includes) emit (oqKLK s b) hkl' 1 (by norm_num)
  have := hS (.n (oqOutK s emit (oqKLK s b) (s.B - 1) 0))
    (lt_trans (oqOutK_lt hs emit (oqKLK s b) hkl' 0 (by norm_num)) (by norm_num))
  have := hS (.n (oqOutK s emit (oqKLK s b) (s.B - 1) 1))
    (lt_trans (oqOutK_lt hs emit (oqKLK s b) hkl' 1 (by norm_num)) (by norm_num))
  have o0 := oqOutK_lt hs emit (oqKLK s b) hkl' 0 (by norm_num)
  have o1 := oqOutK_lt hs emit (oqKLK s b) hkl' 1 (by norm_num)
  have h14 := hs.1.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  cost_simp
  omega

omit hrd hR in
/-- The salted loop's arguments (`oqLoopArgsSKC`): twenty words, the key's thirteen by a map:
`20·S + 1000`. -/
theorem oqLoopArgs_costK (hP : Includes P oqLoopArgsSKC.costDeps) :
    machineCost P oqLoopArgsSKC.costIdx [σV] ≤ 20 * S + 1200 := by
  rw [oqLoopArgsSKC.costEq P hP σ σV hσ, oqKeyVC.costEq P (by includes)]
  have hr := rangeLoop_cost P (by includes) 13 [] (by norm_num)
  have hk := map_cost P (by includes) _ (.closure oqKeyVC.lam0.costIdx [encodeValue 9])
    (fun c ↦ RunsApp.of_spec (oqKeyVC.lam0.costSpec P (by includes) 9 c)) 10 (List.range 13)
    (fun c hc ↦ by
      rw [List.mem_range] at hc
      rw [appCost_fn, List.cons_append, List.nil_append, oqKeyVC.lam0.costEq P (by includes)]
      cost_simp
      omega)
  have hm := map_cost P (by includes) σ σV hσ S (oqKeyV 9) (fun v hv ↦ by
    simp only [oqKeyV, List.mem_map, List.mem_range] at hv
    obtain ⟨c, hc, rfl⟩ := hv
    exact hS _ (by show 9 + c < 2 ^ 64; omega))
  have ha1 := append_cost P (by includes) [σ (.n 6), σ (.n 4), σ (.n 0), σ (.n 1)]
    (List.map σ (oqKeyV 9))
  have ha2 := append_cost P (by includes)
    ([σ (.n 6), σ (.n 4), σ (.n 0), σ (.n 1)] ++ List.map σ (oqKeyV 9))
    [σ (.n 5), σ (.n 24), σ (.n 8)]
  have := hS (.n 6) (by idx_lt); have := hS (.n 4) (by idx_lt); have := hS (.n 0) (by idx_lt)
  have := hS (.n 1) (by idx_lt); have := hS (.n 5) (by idx_lt); have := hS (.n 24) (by idx_lt)
  have := hS (.n 8) (by idx_lt)
  have hlen : (oqKeyV 9).length = 13 := by simp [oqKeyV]
  simp only [hlen, List.length_append, List.length_map, List.length_range,
    List.length_cons, List.length_nil] at hk hm ha1 ha2
  omega

end Val

section Frames

variable {Vn : NFrames} {VnV : MachineValue}
  (hVn : ∀ (k : ℕ) (a r : List E) (v : V),
    RunsApp P VnV [encodeValue k, encodeValue a, encodeValue r, encodeValue v]
      (encodeValue (Vn k a r v)))
  {F : ℕ} (hF : ∀ (k : ℕ) (a r : List E) (v : V), k < 2 ^ 64 → v.idx < 2 ^ 64 → a.length + r.length ≤ 24 →
    appCost P VnV [encodeValue k, encodeValue a, encodeValue r, encodeValue v] ≤ F)
include hVn hF

omit hrd hR in
/-- **A frame of the map, read a cell at a time**: at most `F + 10` a cell. -/
theorem frameAt_costK (hP : Includes P Decoder.oqQueryAtC.lam0.costDeps) (k : ℕ) (hk : k < 2 ^ 64) (a r : List E) (ha : a.length + r.length ≤ 24)
    (v : V) (hv : v.idx < 2 ^ 64) :
    appCost P (.closure Decoder.oqQueryAtC.lam0.costIdx [encodeValue k, VnV, encodeValue a,
      encodeValue r]) [encodeValue v] ≤ F + 10 := by
  rw [appCost_fn, List.cons_append, List.cons_append, List.cons_append, List.cons_append,
    List.nil_append, Decoder.oqQueryAtC.lam0.costEq P hP k Vn VnV hVn, List.length_cons,
    List.length_cons, List.length_cons, List.length_cons, List.length_nil]
  have := hF k a r v hk hv ha
  omega

section Val

variable {σ : Val} {σV : MachineValue}
  (hσ : ∀ v : V, RunsApp P σV [encodeValue v] (encodeValue (σ v)))
  {S : ℕ} (hS : ∀ v : V, v.idx < 2 ^ 64 → appCost P σV [encodeValue v] ≤ S)
include hσ hS

/-- A query's price, its position given: its row off its frame, its siblings off its walk's. -/
@[expose] def queryAtPriceK (S F : ℕ) : ℕ :=
  9 + ((S + 14 + 28) * 192 + 17) + 1 + (2 * S + 700) + ((2 * (F + 10) + 120 + 28) * 24 + 19) + 33

omit hrd hR in
/-- **A query, its position `pos < 2^32` given** (`oqQueryAtC`), of a level's shape, from a value
below `2^21`, its walk `walk < 2^64`: at most `queryAtPriceK S F`. -/
theorem oqQueryAt_costK (hP : Includes P oqQueryAtKC.costDeps) (s : Oq) (hs : OqOKK s)
    (walk : ℕ) (hw : walk < 2 ^ 64) (bp cap flags : E) (b : ℕ) (hb : b < 2 ^ 21) (emit : Bool)
    (pos : ℕ) (hpos : pos < 2 ^ 32) :
    machineCost P oqQueryAtKC.costIdx
      [encodeValue s, encodeValue walk, encodeValue bp, encodeValue cap, encodeValue flags, σV, VnV,
        encodeValue b, encodeValue emit, encodeValue pos] ≤ queryAtPriceK S F := by
  rw [oqQueryAtKC.costEq P hP s walk bp cap flags σ σV hσ Vn VnV hVn]
  have hR' := Oq_R_cost P hs.1 (by includes)
  have hrow := oqRow_costK P hσ hS (by includes) b s.R hb hs.1.2.2.2.2.1
  have hwa := oqWalkArgs_costK P hσ hS (by includes) s hs b hb emit bp cap flags
  have hsib := oqSibsOf_costK P (frameAt_runs P hVn (by includes) walk (oqWalkArgsSK s b emit bp cap flags σ) [])
    (frameAt_costK P hVn hF (by includes) walk hw (oqWalkArgsSK s b emit bp cap flags σ) [] (by simp [oqWalkArgsSK]))
    (by includes) s.pd 22 pos hs.1.2.2.1 (by norm_num) (by omega)
  unfold queryAtPriceK
  omega

/-- A query's price. -/
@[expose] def queryPriceK (R S F : ℕ) : ℕ := posPrice R + queryAtPriceK S F + 40

/-- **A query** (`oqQueryAC`), its position read once off its windows: at most
`queryPriceK R S F`. -/
theorem oqQueryA_costK (hP : Includes P oqQueryAKC.costDeps) (s : Oq) (hs : OqOKK s)
    (lanes : List ℕ) (hl : ∀ x ∈ lanes, x < 2 ^ 64) (walk : ℕ) (hw : walk < 2 ^ 64)
    (bp cap flags : E) (b : ℕ) (hb : b < 2 ^ 21) (emit : Bool) :
    machineCost P oqQueryAKC.costIdx
      [encodeValue s, encodeValue lanes, encodeValue walk, rdV, encodeValue bp, encodeValue cap,
        encodeValue flags, encodeValue b, encodeValue emit, σV, VnV] ≤ queryPriceK R S F := by
  rw [oqQueryAKC.costEq P hP s lanes walk rd rdV hrd bp cap flags b emit σ σV hσ Vn VnV hVn]
  have h3 : s.pd ≤ 24 := hs.1.2.2.1
  have h4 : s.cd ≤ 8 := hs.1.2.2.2.1
  have hw' : qwN (s.pd + s.cd) s.cd ≤ 6 := by unfold qwN qwNp; omega
  have hp := winPosOfW_cost P hrd hR (by includes) lanes hl bp (s.pd + s.cd) s.cd (by omega) h4 hw'
  have hlt := winPosAt_lt (winLogsFrom lanes rd (bp.limb 0) (qwN (s.pd + s.cd) s.cd))
    (s.pd + s.cd) s.cd
  have : 2 ^ (s.pd + s.cd) ≤ 2 ^ 32 := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hq := oqQueryAt_costK P hVn hF hσ hS (by includes) s hs walk hw bp cap flags b hb emit
    (winPosOfW lanes rd bp (s.pd + s.cd) s.cd) (by unfold winPosOfW; omega)
  rw [limbs_of_lt (by omega : s.pd < 2 ^ 64), limbs_of_lt (by omega : s.cd < 2 ^ 64),
    limbs_of_lt (by omega : s.pd + s.cd < 2 ^ 64)]
  unfold queryPriceK
  omega

/-- An iteration's price. -/
@[expose] def iterPriceK (R S F : ℕ) : ℕ := 2 * queryPriceK R S F + 6 * S + 2080

/-- **A loop iteration's queries** (`oqIterAC`): at most `iterPriceK R S F`. -/
theorem oqIterA_costK (hP : Includes P oqIterAKC.costDeps) (s : Oq) (hs : OqOKK s)
    (lanes : List ℕ) (hl : ∀ x ∈ lanes, x < 2 ^ 64) (walk : ℕ) (hw : walk < 2 ^ 64) :
    machineCost P oqIterAKC.costIdx
      [encodeValue s, encodeValue lanes, encodeValue walk, rdV, σV, VnV] ≤ iterPriceK R S F := by
  rw [oqIterAKC.costEq P hP s lanes walk rd rdV hrd σ σV hσ Vn VnV hVn]
  have hE := oqE1K_lt hs
  have q1 := oqQueryA_costK P hrd hR hVn hF hσ hS (by includes) s hs lanes hl walk hw (σ (.n 23))
    (σ (.n 3)) (σ (.n 4)) 24 (by norm_num) true
  have q2 := oqQueryA_costK P hrd hR hVn hF hσ hS (by includes) s hs lanes hl walk hw
    (σ (.n (oqE1K s))) (σ (.n 3)) (σ (.n 4)) (oqE1K s + 1) (by omega) false
  have q3 := oqQueryA_costK P hrd hR hVn hF hσ hS (by includes) s hs lanes hl walk hw (σ (.n 22))
    (σ (.n 3)) (σ (.n 4)) 23 (by norm_num) true
  have e1 := oqE1K_cost P hs (by includes)
  have := hS (.n 23) (by idx_lt); have := hS (.n 22) (by idx_lt); have := hS (.n (oqE1K s)) (by show oqE1K s < 2 ^ 64; omega); have := hS (.n 3) (by idx_lt)
  have := hS (.n 4) (by idx_lt)
  have hb := hs.1.1
  unfold iterPriceK
  limbs_one
  split_ifs <;> omega

end Val

/-- An iteration of the loop, its frame stepped: its price. -/
@[expose] def stepPriceK (R F : ℕ) : ℕ := iterPriceK R (F + 10) F + 420

/-- **The loop's `N` iterations from the frame at `x`** (`oqItersFromC`), each the next at
`x·g`: at most `stepPriceK R F · N + 5`. -/
theorem oqItersFrom_costK (hP : Includes P oqItersFromKC.costDeps) (s : Oq) (hs : OqOKK s)
    (lanes : List ℕ) (hl : ∀ x ∈ lanes, x < 2 ^ 64)
    (loop : ℕ) (hloop : loop < 2 ^ 64) (walk : ℕ) (hw : walk < 2 ^ 64) (la : List E)
    (hla : la.length ≤ 20) :
    ∀ (N : ℕ) (x : E), N < 2 ^ 64 →
      machineCost P oqItersFromKC.costIdx [encodeValue s, encodeValue lanes,
        encodeValue loop, encodeValue walk, rdV, VnV, encodeValue la, encodeValue N, encodeValue x] ≤
          stepPriceK R F * N + 5
  | 0, x, _ => by
    rw [oqItersFromKC.costEq_zero P hP s lanes loop walk rd rdV hrd Vn VnV hVn]; omega
  | N + 1, x, hN => by
    rw [oqItersFromKC.costEq_succ P hP s lanes loop walk rd rdV hrd Vn VnV hVn,
      limbs_of_lt hN]
    have hi := oqIterA_costK P hrd hR hVn hF (frameAt_runs P hVn (by includes) loop (x :: la) [])
      (frameAt_costK P hVn hF (by includes) loop hloop (x :: la) [] (by simp; omega)) (by includes) s hs lanes hl
      walk hw
    have := oqItersFrom_costK hP s hs lanes hl loop hloop walk hw la hla N
      (x * LeanVM.Protocol.Verifier.gen) (by omega)
    have ha := append_cost P (by includes) (oqIterAK s lanes walk rd (Vn loop (x :: la) []) Vn)
      (oqItersFromK s lanes loop walk rd Vn la N (x * LeanVM.Protocol.Verifier.gen))
    have := length_oqIterAK s lanes walk rd (Vn loop (x :: la) []) Vn
    unfold stepPriceK at *
    rw [Nat.mul_succ]
    omega

section Val

variable {σ : Val} {σV : MachineValue}
  (hσ : ∀ v : V, RunsApp P σV [encodeValue v] (encodeValue (σ v)))
  {S : ℕ} (hS : ∀ v : V, v.idx < 2 ^ 64 → appCost P σV [encodeValue v] ≤ S)
include hσ hS

/-- The queries' price. -/
@[expose] def oqsPriceK (R S F : ℕ) : ℕ :=
  1 + (3 * S + queryPriceK R S F + 19) + (20 * S + 1200) + (stepPriceK R F * 113 + 5) + 14 + 140

/-- **The queries of `opening_queries`** (`oqsOfNC`, `oqsOfAK`), its odd query and `N ≤ 113`
iterations: at most `oqsPriceK R S F`. -/
theorem oqsOfA_costK (hP : Includes P oqsOfAKC.costDeps) (s : Oq) (hs : OqOKK s)
    (lanes : List ℕ) (hl : ∀ x ∈ lanes, x < 2 ^ 64)
    (odd loop walk N : ℕ) (hodd : odd ≤ 1) (hN : N ≤ 113) (hloop : loop < 2 ^ 64)
    (hw : walk < 2 ^ 64) :
    machineCost P oqsOfAKC.costIdx [encodeValue s, encodeValue lanes, encodeValue odd,
      encodeValue loop, encodeValue walk, encodeValue N, rdV, σV, VnV] ≤ oqsPriceK R S F := by
  rw [oqsOfAKC.costEq P hP s lanes odd loop walk N rd rdV hrd σ σV hσ Vn VnV hVn]
  have q := oqQueryA_costK P hrd hR hVn hF hσ hS (by includes) s hs lanes hl walk hw (σ (.n 25))
    (σ (.n 0)) (σ (.n 1)) 26 (by norm_num) true
  have := hS (.n 25) (by idx_lt); have := hS (.n 0) (by idx_lt); have := hS (.n 1) (by idx_lt)
  have := oqLoopArgs_costK P hσ hS (by includes)
  have hi := oqItersFrom_costK P hrd hR hVn hF (by includes) s hs lanes hl loop hloop walk hw
    (oqLoopArgsSK σ)
    (by simp [oqLoopArgsSK, oqKeyV]) N 1 (by omega)
  have := Nat.mul_le_mul_left (stepPriceK R F) hN
  unfold oqsPriceK
  rw [limbs_of_lt (by omega : odd < 2 ^ 64)]
  split_ifs
  · have ha := append_cost P (by includes)
      [oqQueryAK s lanes walk rd (σ (.n 25)) (σ (.n 0)) (σ (.n 1)) 26 true σ Vn]
      (oqItersFromK s lanes loop walk rd Vn (oqLoopArgsSK σ) N 1)
    simp only [List.length_cons, List.length_nil] at ha
    omega
  · have ha := append_cost P (by includes) ([] : List QW)
      (oqItersFromK s lanes loop walk rd Vn (oqLoopArgsSK σ) N 1)
    simp only [List.length_nil] at ha
    omega

end Val

end Frames

/-! ## The queries' values -/

/-! ## A query's opening -/

section Val2

variable {σ : Val} {σV : MachineValue}
  (hσ : ∀ v : V, RunsApp P σV [encodeValue v] (encodeValue (σ v)))
  {S : ℕ} (hS : ∀ v : V, v.idx < 2 ^ 64 → appCost P σV [encodeValue v] ≤ S)
  {Vn : NFrames} {VnV : MachineValue}
  (hVn : ∀ (k : ℕ) (a r : List E) (v : V),
    RunsApp P VnV [encodeValue k, encodeValue a, encodeValue r, encodeValue v]
      (encodeValue (Vn k a r v)))
  {F : ℕ} (hF : ∀ (k : ℕ) (a r : List E) (v : V), k < 2 ^ 64 → v.idx < 2 ^ 64 → a.length + r.length ≤ 24 →
    appCost P VnV [encodeValue k, encodeValue a, encodeValue r, encodeValue v] ≤ F)
include hσ hS hVn hF

/-- A level's price, the `level_queries` callee's frame (at most `S` a word) and its
`opening_queries` call's argument words given. -/
@[expose] def levelAtPriceK (R S F : ℕ) : ℕ :=
  7 + 1 + S + oqsPriceK R (F + 10) F + ((openingPrice R + 10 + 13) * 227 + 3) + 62

/-- **A level's openings, the `level_queries` callee's frame `fr` and its `opening_queries`
call's words `a` given** (`levelOsAtC`), from a dispatch of the table: at most
`levelAtPriceK R S F`. -/
theorem levelOsAt_costK (hP : Includes P levelOsAtKC.costDeps) (lanes : List ℕ)
    (hl : ∀ x ∈ lanes, x < 2 ^ 64) (c : OsCall) (hc : CallOKK c) (a : List E) (ha : a.length ≤ 15) :
    machineCost P levelOsAtKC.costIdx
      [encodeValue lanes, rdV, σV, VnV, encodeValue c, encodeValue a] ≤ levelAtPriceK R S F := by
  have hs := hc.shape
  obtain ⟨⟨-, hodd, hN, hfn, hloop, hwalk, hdepth, -, -, -, hpw⟩, -, -⟩ := hc
  rw [levelOsAtKC.costEq P hP lanes rd rdV hrd σ σV hσ Vn VnV hVn]
  have hpw2 := hS (.n (c.pw + 2)) (by show c.pw + 2 < 2 ^ 64; omega)
  have hσ'' : ∀ v : V, RunsApp P (.closure Decoder.levelOsAtC.lam1.costIdx
      [VnV, encodeValue a, encodeValue [σ (.n (c.pw + 2))], encodeValue c.fn])
      [encodeValue v] (encodeValue (Vn c.fn a [σ (.n (c.pw + 2))] v)) :=
    fun v ↦ RunsApp.of_spec (Decoder.levelOsAtC.lam1.costSpec P (by includes) Vn VnV hVn _ _ _ v)
  have hS'' : ∀ v : V, v.idx < 2 ^ 64 → appCost P (.closure Decoder.levelOsAtC.lam1.costIdx
      [VnV, encodeValue a, encodeValue [σ (.n (c.pw + 2))], encodeValue c.fn])
      [encodeValue v] ≤ F + 10 := fun v hv ↦ by
    rw [appCost_fn, List.cons_append, List.cons_append, List.cons_append, List.cons_append,
      List.nil_append, Decoder.levelOsAtC.lam1.costEq P (by includes) Vn VnV hVn, List.length_cons,
      List.length_cons, List.length_cons, List.length_cons, List.length_nil]
    have := hF c.fn a [σ (.n (c.pw + 2))] v (by omega) hv (by simp; omega)
    omega
  have ho := oqsOfA_costK P hrd hR hVn hF hσ'' hS'' (by includes) _ hs lanes hl c.odd c.loop c.walk
    c.N hodd hN (by omega) (by omega)
  have hlen := length_oqsOfAK (rd := rd) ⟨c.base, c.I, c.pd, c.cd⟩ lanes c.odd c.loop c.walk c.N
    (Vn c.fn a [σ (.n (c.pw + 2))]) Vn
  have m3 := map_cost P (by includes) _
    (.closure Decoder.levelOsAtC.lam0.costIdx [rdV, encodeValue (a.headD 0), encodeValue c.depth,
      encodeValue c.cd])
    (fun w ↦ RunsApp.of_spec (Decoder.levelOsAtC.lam0.costSpec P (by includes) rd rdV hrd _ _ _ w))
    (openingPrice R + 10) (oqsOfAK ⟨c.base, c.I, c.pd, c.cd⟩ lanes c.odd c.loop c.walk c.N rd
      (Vn c.fn a [σ (.n (c.pw + 2))]) Vn) (fun w hw ↦ by
      rw [appCost_fn, List.cons_append, List.cons_append, List.cons_append, List.cons_append,
        List.nil_append, Decoder.levelOsAtC.lam0.costEq P (by includes) rd rdV hrd, List.length_cons,
        List.length_cons, List.length_cons, List.length_cons, List.length_nil]
      obtain ⟨hw1, hw2⟩ := mem_oqsOfAK hw
      have h4 : c.cd ≤ 8 := hs.1.2.2.2.1
      have h3 : c.pd ≤ 24 := hs.1.2.2.1
      have : 2 ^ (c.pd + c.cd) ≤ 2 ^ 32 := Nat.pow_le_pow_right (by norm_num) (by omega)
      have := toOpening_cost P hrd hR (by includes) (a.headD 0) c.cd c.depth w h4 hdepth
        (lt_of_lt_of_le hw1 this) (by rw [hw2]; exact h3)
      omega)
  have := Nat.mul_le_mul_left (openingPrice R + 10 + 13) (hlen.trans (by omega : 1 + 2 * c.N ≤ 227))
  unfold levelAtPriceK
  have := listCasesOn_le a 7 (fun _ _ ↦ 3) (by intros; omega)
  rw [limbs_of_lt (by omega : c.pw + 2 < 2 ^ 64), limbs_of_lt (by omega : c.pw < 2 ^ 64)]
  omega

/-- A level's price, the `level_queries` callee's frame given (at most `S` a word). -/
@[expose] def levelQPriceK (R S F : ℕ) : ℕ := 33 + ((S + 10 + 13) * 7 + 3) + levelAtPriceK R S F + 12

/-- **A level's openings, the `level_queries` callee's frame `fr` given** (`levelOsQC`): the
`opening_queries` call's seven words read once, then `levelOsAtC`: at most `levelQPriceK R S F`. -/
theorem levelOsQ_costK (hP : Includes P levelOsQKC.costDeps) (lanes : List ℕ)
    (hl : ∀ x ∈ lanes, x < 2 ^ 64) (c : OsCall) (hc : CallOKK c) :
    machineCost P levelOsQKC.costIdx [encodeValue lanes, rdV, σV, VnV, encodeValue c] ≤
      levelQPriceK R S F := by
  rw [levelOsQKC.costEq P hP lanes rd rdV hrd σ σV hσ Vn VnV hVn]
  have hpw : c.pw < 2 ^ 20 := hc.1.2.2.2.2.2.2.2.2.2.2
  have hq : machineCost P OsCallQargsKC.costIdx [encodeValue c] ≤ 33 := by
    rw [OsCallQargsKC.costEq P (by includes)]
    rw [limbs_of_lt (by omega : c.pw + 1 < 2 ^ 64), limbs_of_lt (by omega : c.pw < 2 ^ 64)]
    omega
  have hl0 : ∀ k : ℕ, k < 2 ^ 64 → appCost P (.closure Decoder.levelOsQC.lam0.costIdx [σV]) [encodeValue k] ≤
      S + 10 := fun k hk ↦ by
    rw [appCost_fn, List.cons_append, List.nil_append,
      Decoder.levelOsQC.lam0.costEq P (by includes) σ σV hσ, List.length_cons, List.length_nil]
    have := hS (.n k) hk; omega
  have hr0 : ∀ k : ℕ, RunsApp P (.closure Decoder.levelOsQC.lam0.costIdx [σV]) [encodeValue k]
      (encodeValue (σ (.n k))) :=
    fun k ↦ RunsApp.of_spec (Decoder.levelOsQC.lam0.costSpec P (by includes) σ σV hσ k)
  have m := map_cost P (by includes) _ _ hr0 (S + 10) c.qargsK (fun k hk ↦ hl0 k (qargsK_lt hpw k hk))
  have hql : c.qargsK.length = 7 := rfl
  rw [hql] at m
  have := levelOsAt_costK P hrd hR hσ hS hVn hF (by includes) lanes hl c hc
    (c.qargsK.map fun k ↦ σ (.n k)) (by rw [List.length_map, hql]; omega)
  unfold levelQPriceK
  omega

/-- A level's price. -/
@[expose] def levelPriceK (R S F : ℕ) : ℕ :=
  27 + ((S + 10 + 13) * 4 + 3) + ((S + 10 + 13) * 3 + 3) + levelQPriceK R (F + 10) F + 25

/-- **A level's openings** (`levelOsNC`, `levelOsAK`), its `level_queries` dispatch's frame read
once: at most `levelPriceK R S F`. -/
theorem levelOsA_costK (hP : Includes P levelOsAKC.costDeps) (lanes : List ℕ)
    (hl : ∀ x ∈ lanes, x < 2 ^ 64) (c : OsCall) (hc : CallOKK c) :
    machineCost P levelOsAKC.costIdx [encodeValue lanes, rdV, σV, VnV, encodeValue c] ≤
      levelPriceK R S F := by
  rw [levelOsAKC.costEq P hP lanes rd rdV hrd σ σV hσ Vn VnV hVn]
  have hargs : c.args.length ≤ 3 := hc.1.2.2.2.2.2.2.2.1
  have hlq : c.lq < 2 ^ 20 := hc.1.2.2.2.2.2.2.2.2.1
  have hr0 : c.ret0 < 2 ^ 20 := hc.1.2.2.2.2.2.2.2.2.2.1
  have hrt : machineCost P Decoder.OsCallRetsC.costIdx [encodeValue c] ≤ 27 := by
    rw [Decoder.OsCallRetsC.costEq P (by includes)]
    rw [limbs_of_lt (by omega : c.ret0 + 1 < 2 ^ 64), limbs_of_lt (by omega : c.ret0 + 2 < 2 ^ 64),
      limbs_of_lt (by omega : c.ret0 + 3 < 2 ^ 64), limbs_of_lt (by omega : c.ret0 < 2 ^ 64)]
    omega
  have hl0 : ∀ k : ℕ, k < 2 ^ 64 → appCost P (.closure Decoder.levelOsQC.lam0.costIdx [σV]) [encodeValue k] ≤
      S + 10 := fun k hk ↦ by
    rw [appCost_fn, List.cons_append, List.nil_append,
      Decoder.levelOsQC.lam0.costEq P (by includes) σ σV hσ, List.length_cons, List.length_nil]
    have := hS (.n k) hk; omega
  have hr0' : ∀ k : ℕ, RunsApp P (.closure Decoder.levelOsQC.lam0.costIdx [σV]) [encodeValue k]
      (encodeValue (σ (.n k))) :=
    fun k ↦ RunsApp.of_spec (Decoder.levelOsQC.lam0.costSpec P (by includes) σ σV hσ k)
  have m1 := map_cost P (by includes) _ _ hr0' (S + 10) c.rets (fun k hk ↦ hl0 k (rets_lt hr0 k hk))
  have m2 := map_cost P (by includes) _ _ hr0' (S + 10) c.args (fun k hk ↦ hl0 k (hc.2.2 k hk |>.trans (by norm_num)))
  have hrl : c.rets.length = 4 := rfl
  rw [hrl] at m1
  have := Nat.mul_le_mul_left (S + 10 + 13) hargs
  have hfr : ∀ v : V, RunsApp P (.closure Decoder.levelOsNC.lam0.costIdx
      [VnV, encodeValue (c.rets.map fun k ↦ σ (.n k)), encodeValue (c.args.map fun k ↦ σ (.n k)),
        encodeValue c.lq]) [encodeValue v]
      (encodeValue (Vn c.lq (c.args.map fun k ↦ σ (.n k)) (c.rets.map fun k ↦ σ (.n k)) v)) :=
    fun v ↦ RunsApp.of_spec (Decoder.levelOsNC.lam0.costSpec P (by includes) Vn VnV hVn _ _ _ v)
  have hfrS : ∀ v : V, v.idx < 2 ^ 64 → appCost P (.closure Decoder.levelOsNC.lam0.costIdx
      [VnV, encodeValue (c.rets.map fun k ↦ σ (.n k)), encodeValue (c.args.map fun k ↦ σ (.n k)),
        encodeValue c.lq]) [encodeValue v] ≤ F + 10 := fun v hv ↦ by
    rw [appCost_fn, List.cons_append, List.cons_append, List.cons_append, List.cons_append,
      List.nil_append, Decoder.levelOsNC.lam0.costEq P (by includes) Vn VnV hVn, List.length_cons,
      List.length_cons, List.length_cons, List.length_cons, List.length_nil]
    have := hF c.lq (c.args.map fun k ↦ σ (.n k)) (c.rets.map fun k ↦ σ (.n k)) v (by omega) hv
      (by simp only [List.length_map]; omega)
    omega
  have := levelOsQ_costK P hrd hR hfr hfrS hVn hF (by includes) lanes hl c hc
  unfold levelPriceK
  omega

end Val2

section Proof

variable {σ : Val} {σV : MachineValue}
  (hσ : ∀ v : V, RunsApp P σV [encodeValue v] (encodeValue (σ v)))
  {S : ℕ} (hS : ∀ v : V, v.idx < 2 ^ 64 → appCost P σV [encodeValue v] ≤ S)
  {Vn : NFrames} {VnV : MachineValue}
  (hVn : ∀ (k : ℕ) (a r : List E) (v : V),
    RunsApp P VnV [encodeValue k, encodeValue a, encodeValue r, encodeValue v]
      (encodeValue (Vn k a r v)))
  {F : ℕ} (hF : ∀ (k : ℕ) (a r : List E) (v : V), k < 2 ^ 64 → v.idx < 2 ^ 64 → a.length + r.length ≤ 24 →
    appCost P VnV [encodeValue k, encodeValue a, encodeValue r, encodeValue v] ≤ F)
  {cl : E → E → ℕ} {clV : MachineValue}
  (hcl : ∀ a b : E, RunsApp P clV [encodeValue a, encodeValue b] (encodeValue (cl a b)))
  {C : ℕ} (hC : ∀ a b : E, appCost P clV [encodeValue a, encodeValue b] ≤ C)
  {L : ℕ} (hL : cl (σ (.n 29)) (σ (.n 683)) ≤ L) (hL32 : L ≤ 2 ^ 32)
include hσ hS hVn hF hcl hC hL hL32

omit hrd hR hVn hF hcl hC hL hL32 in
theorem vsOsArgs_costK (hP : Includes P vsOsArgsSKC.costDeps) :
    machineCost P vsOsArgsSKC.costIdx [σV] ≤ 10 * S + 121 := by
  rw [vsOsArgsSKC.costEq P hP σ σV hσ]
  cost_facts [hS]
  omega

omit hrd hR hVn hF hcl hC hL hL32 in
theorem vsOsRets_costK (hP : Includes P vsOsRetsSKC.costDeps) :
    machineCost P vsOsRetsSKC.costIdx [σV] ≤ 5 * S + 61 := by
  rw [vsOsRetsSKC.costEq P hP σ σV hσ]
  cost_facts [hS]
  omega

/-- A child proof's price, its size and rate and `open_stacked`'s frame given. -/
@[expose] def vsAtPriceK (R S F C L : ℕ) : ℕ :=
  3 * S + C + ((R + 56) * L + 5) + (F + 10) + ((R + 56) * 137 + 5) + (11 * L + 3) +
    ((levelPriceK R (F + 10) F + 20 + 13) * 7 + 3) + 69

/-- **A child's proof, the index `j` of its size and rate and the frame `fr` of its
`open_stacked` call given** (`vsPiOfAtC`), the frame of price at most `F + 10`: at most
`vsAtPriceK R S F C L`. -/
theorem vsPiOfAt_costK (hP : Includes P vsPiOfAtKC.costDeps) (T : WhirTabs)
    (hT : WhirTabsOKK T) (j : ℕ) {fr : Val} {frV : MachineValue}
    (hfr : ∀ v : V, RunsApp P frV [encodeValue v] (encodeValue (fr v)))
    (hfrS : ∀ v : V, v.idx < 2 ^ 64 → appCost P frV [encodeValue v] ≤ F + 10) :
    machineCost P vsPiOfAtKC.costIdx
      [encodeValue T, rdV, σV, VnV, clV, encodeValue j, frV] ≤ vsAtPriceK R S F C L := by
  rw [vsPiOfAtKC.costEq P hP T rd rdV hrd σ σV hσ Vn VnV hVn cl clV hcl j fr frV hfr]
  have := hS (.n 29) (by idx_lt); have := hS (.n 683) (by idx_lt); have := hfrS (.n 9) (by idx_lt)
  have := hC (σ (.n 29)) (σ (.n 683))
  have hl := hL
  have hw1 := wordsFrom_cost P hrd hR (by includes) (cl (σ (.n 29)) (σ (.n 683)))
    ((σ (.n 29)).limb 0) (by omega)
  have := Nat.mul_le_mul_left (R + 56) hl
  have hwd := hT.words j
  have hw2 := wordsFrom_cost P hrd hR (by includes) (T.words.getD j 0) ((fr (.n 9)).limb 0)
    (by omega)
  have := Nat.mul_le_mul_left (R + 56) hwd
  have ha := append_cost P (by includes)
    (wordsFrom rd ((σ (.n 29)).limb 0) (cl (σ (.n 29)) (σ (.n 683))))
    (wordsFrom rd ((fr (.n 9)).limb 0) (T.words.getD j 0))
  rw [length_wordsFrom] at ha
  obtain ⟨hcl7, hcok⟩ := hT.calls j
  have hm := map_cost P (by includes) _
    (.closure vsPiOfAtKC.lam0.costIdx [rdV, VnV, frV, encodeValue T.lanes])
    (fun c ↦ RunsApp.of_spec (vsPiOfAtKC.lam0.costSpec P (by includes) rd rdV hrd Vn VnV hVn
      fr frV hfr T.lanes c))
    (levelPriceK R (F + 10) F + 20) (T.calls.getD j []) (fun c hc ↦ by
      rw [appCost_fn, List.cons_append, List.cons_append, List.cons_append, List.cons_append,
        List.nil_append, vsPiOfAtKC.lam0.costEq P (by includes) rd rdV hrd Vn VnV hVn fr frV
        hfr, List.length_cons, List.length_cons, List.length_cons, List.length_cons, List.length_nil]
      have := levelOsA_costK P hrd hR hfr hfrS hVn hF (by includes) T.lanes hT.lanes c (hcok c hc)
      omega)
  have := Nat.mul_le_mul_left (levelPriceK R (F + 10) F + 20 + 13) hcl7
  unfold vsAtPriceK
  omega

/-- A child proof's price, its size and the index of its size and rate given. -/
@[expose] def vsMPriceK (R S F C L : ℕ) : ℕ :=
  (5 * S + 61) + 1 + (10 * S + 121) + vsAtPriceK R S F C L + 19

/-- **A child's proof, its size `m` and the index `j` of its size and rate given**
(`vsPiOfMC`): the frame of `open_stacked__L{m}`'s call read once: at most
`vsMPriceK R S F C L`. -/
theorem vsPiOfM_costK (hP : Includes P vsPiOfMKC.costDeps) (T : WhirTabs)
    (hT : WhirTabsOKK T) (m j : ℕ) (hm : m < 2 ^ 32) :
    machineCost P vsPiOfMKC.costIdx [encodeValue T, rdV, σV, VnV, clV, encodeValue m,
      encodeValue j] ≤ vsMPriceK R S F C L := by
  rw [vsPiOfMKC.costEq P hP T rd rdV hrd σ σV hσ Vn VnV hVn cl clV hcl m j,
    limbs_of_lt (by omega : m < 2 ^ 64), limbs_of_lt (by omega : 310 + m < 2 ^ 64)]
  have hfr : ∀ v : V, RunsApp P (.closure vsPiOfMKC.lam0.costIdx
      [VnV, encodeValue (310 + m), encodeValue (vsOsRetsSK σ),
        encodeValue (vsOsArgsSK σ)]) [encodeValue v]
      (encodeValue (Vn ((310 + m)) (vsOsArgsSK σ) (vsOsRetsSK σ) v)) :=
    fun v ↦ RunsApp.of_spec (vsPiOfMKC.lam0.costSpec P (by includes) Vn VnV hVn _ _ _ v)
  have hfrS : ∀ v : V, v.idx < 2 ^ 64 → appCost P (.closure vsPiOfMKC.lam0.costIdx
      [VnV, encodeValue (310 + m), encodeValue (vsOsRetsSK σ),
        encodeValue (vsOsArgsSK σ)]) [encodeValue v] ≤ F + 10 := fun v hv ↦ by
    rw [appCost_fn, List.cons_append, List.cons_append, List.cons_append, List.cons_append,
      List.nil_append, vsPiOfMKC.lam0.costEq P (by includes) Vn VnV hVn, List.length_cons,
      List.length_cons, List.length_cons, List.length_cons, List.length_nil]
    have := hF ((310 + m)) (vsOsArgsSK σ) (vsOsRetsSK σ) v
      (by omega) hv (by simp [vsOsArgsSK, vsOsRetsSK])
    omega
  have := vsPiOfAt_costK P hrd hR hσ hS hVn hF hcl hC hL hL32 (by includes) T hT j hfr hfrS
  have := vsOsArgs_costK P hσ hS (by includes)
  have := vsOsRets_costK P hσ hS (by includes)
  unfold vsMPriceK
  omega

/-- A child proof's price, its size given. -/
@[expose] def vsSPriceK (R S F C L : ℕ) : ℕ := S + 117 + 2 + vsMPriceK R S F C L + 22

/-- **A child's proof, its size `m < 2^32` given** (`vsPiOfSC`): the rate read once, then
`vsPiOfMC` at the index of the size and rate: at most `vsSPriceK R S F C L`. -/
theorem vsPiOfS_costK (hP : Includes P vsPiOfSKC.costDeps) (T : WhirTabs)
    (hT : WhirTabsOKK T) (m : ℕ) (hm : m < 2 ^ 32) :
    machineCost P vsPiOfSKC.costIdx [encodeValue T, rdV, σV, VnV, clV, encodeValue m] ≤
      vsSPriceK R S F C L := by
  rw [vsPiOfSKC.costEq P hP T rd rdV hrd σ σV hσ Vn VnV hVn cl clV hcl m]
  have := hS (.n 126) (by idx_lt)
  have := logGTWith_cost P (by includes) T.lanes hT.lanes (σ (.n 126)) 4 (by norm_num)
  have hr := logGTWith_le T.lanes (σ (.n 126)) 4
  have := vsPiOfM_costK P hrd hR hσ hS hVn hF hcl hC hL hL32 (by includes) T hT m
    (logGTWith T.lanes (σ (.n 126)) 4 * 11 + m) hm
  rw [limbs_of_lt (by omega : logGTWith T.lanes (σ (.n 126)) 4 * 11 < 2 ^ 64),
    limbs_of_lt (by omega : logGTWith T.lanes (σ (.n 126)) 4 < 2 ^ 64),
    limbs_of_lt (by omega : logGTWith T.lanes (σ (.n 126)) 4 * 11 + m < 2 ^ 64),
    limbs_of_lt (by omega : m < 2 ^ 64)]
  unfold vsSPriceK
  omega

/-- A child proof's price. -/
@[expose] def vsPiPriceK (R S F C L : ℕ) : ℕ := S + 347 + vsSPriceK R S F C L + 19

/-- **A child's proof** (`vsPiOfNC`, `vsPiOfA`) at `verify_sub`'s valuation, off `open_stacked`'s
tables `T`: its stream (the cursor's length at most `L`), the opening's words, the selected size
and rate's levels' openings: at most `vsPiPriceK R S F C L`. -/
theorem vsPiOfN_costK (hP : Includes P vsPiOfAKC.costDeps) (T : WhirTabs)
    (hT : WhirTabsOKK T) :
    machineCost P vsPiOfAKC.costIdx [encodeValue T, rdV, σV, VnV, clV] ≤
      vsPiPriceK R S F C L := by
  rw [vsPiOfAKC.costEq P hP T rd rdV hrd σ σV hσ Vn VnV hVn cl clV hcl]
  have := hS (.n 1725) (by idx_lt)
  have := logGTWith_cost P (by includes) T.lanes hT.lanes (σ (.n 1725)) 11 (by norm_num)
  have := logGTWith_le T.lanes (σ (.n 1725)) 11
  have := vsPiOfS_costK P hrd hR hσ hS hVn hF hcl hC hL hL32 (by includes) T hT
    (logGTWith T.lanes (σ (.n 1725)) 11) (by omega)
  unfold vsPiPriceK
  omega

end Proof

end Reader

end

end LeanVM.SaltedGuest.Bounds
