/-
  LeanVM.SaltedGuest.WalkKnown

  The walks' cut obligations (`CutsKnown`) of the salted guest, from decided checks of its
  certificates and facts on prefixes of its core IR.
-/

module

public import LeanVM.SaltedGuest.Sound
public import LeanVM.Guest.WalkTags
public import LeanVM.Guest.B1.Opening.QueriesWalk

/-!
# The walks' obligations

The deployed guest's checks of the walks' certificates (`winTripOk`, `loopOk`, `mainOk`, `wpOk`,
`lqOk`, on any certificate) and their lemmas at the salted guest's `glob` and `certOf`:

* `loop_cutsKnown`: a loop's cut obligations from its certificate's check and two facts on the
  prefixes of its body, that its window pointers name windows and that its tail passes the walk on;
* `main_cutsKnownG`: a specialization of `opening_queries`'s, from its check, the window pointer of
  an odd count's first query and the walk its loop call starts;
* `wp_cutsKnown` (`walk_path`) and `lq_cutsKnown` (`level_queries`): from the checks alone.

The prefixes' facts are the statements the deployed templates name, read off the salted core IR by
index (`WalkOqK.lean`).
-/

namespace LeanVM.SaltedGuest.End

open LeanVM.SaltedGuest LeanVM.Guest

open LeanVM.Parameters LeanVM.Semantics LeanVM.SaltedGuest LeanVM.Guest LeanVM.Guest.Core LeanVM.SaltedGuest.Check LeanVM.Guest.Check
open LeanVM.Guest.B1

@[expose] public section


/-- A window bound the walk hands on: on the cell of a window pointer `v` the prefix has loaded
(`v.2` statements suffice), window `m.2.1 < qwN`, bound at least its width's. -/
def winTripOk (C : Cert) (d cd : ℕ) (src : List (ℕ × ℕ)) (start : ℕ) (m : ℕ × ℕ × ℕ) : Bool :=
  src.any fun v ↦ m.1 == C.locs.getD v.1 0 && Nat.ble v.2 start && Nat.blt m.2.1 (qwN d cd) &&
    Nat.ble (2 ^ (qwWin d cd m.2.1).2) m.2.2

/-- A tuple a cut hands to a call of `walk_path`: `WinsAt` (`winsTag d cd`) on the cell of a window
pointer `v` the prefix has loaded (`v.2` statements suffice). -/
def winSemOk (C : Cert) (d cd : ℕ) (src : List (ℕ × ℕ)) (start : ℕ) (t : ℕ × List ℕ) : Bool :=
  src.any fun v ↦ t == (winsTag d cd, [C.locs.getD v.1 0]) && Nat.ble v.2 start

/-- A loop's cut: no plain bound, its window bounds and `walk_path`'s tuples of the loaded pointers
`src`, its other tuples the walk's tail `[2, xv, 1]` once `tl` statements hold. -/
def loopCutOk (C : Cert) (tag d cd : ℕ) (src : List (ℕ × ℕ)) (xv tl : ℕ) (c : Cut) : Bool :=
  c.known.isEmpty && c.knownIf.all (winTripOk C d cd src c.start) &&
    c.sems.all fun t ↦ (t == (tag, [C.locs.getD 2 0, C.locs.getD xv 0, C.locs.getD 1 0]) &&
      Nat.ble tl c.start) || winSemOk C d cd src c.start t

/-- A loop's certificate: the walk `tag` on `[2, 0, 1]` and `0 ≠ 1` assumed, every cut a
`loopCutOk`. -/
def loopOk (C : Cert) (tag d cd : ℕ) (src : List (ℕ × ℕ)) (xv tl : ℕ) : Bool :=
  C.sem == [(tag, [C.locs.getD 2 0, C.locs.getD 0 0, C.locs.getD 1 0]),
    (tagNe, [C.locs.getD 0 0, C.locs.getD 1 0])] && C.cuts.all (loopCutOk C tag d cd src xv tl)

/-- A specialization's cut: no plain bound, its window bounds and `walk_path`'s tuple of an odd
count's first query (`src`), its other tuples the loop call's walk `tagW` on `[4, x, 6]`, conditional
on `x = 1`. -/
def mainCutOk (C : Cert) (tagW d cd : ℕ) (src : List (ℕ × ℕ)) (c : Cut) : Bool :=
  c.known.isEmpty && c.knownIf.all (winTripOk C d cd src c.start) &&
    c.sems.all fun t ↦ (t.1 == impTag tagW 1 1 && t.2.length == 3 &&
      t.2.getD 0 0 == C.locs.getD 4 0 && t.2.getD 2 0 == C.locs.getD 6 0) ||
      winSemOk C d cd src c.start t

/-- A specialization's certificate: `OqMainWins` (`tagM`) on `[4, 6]` assumed, every cut a
`mainCutOk`. -/
def mainOk (C : Cert) (tagM tagW d cd : ℕ) (src : List (ℕ × ℕ)) : Bool :=
  C.sem == [(tagM, [C.locs.getD 4 0, C.locs.getD 6 0])] && C.cuts.all (mainCutOk C tagW d cd src)

/-- A cut of `walk_path`: no plain bound, no tuple, its window bounds those of its argument `wins`
(value `2`, from the function's start). -/
def wpCutOk (C : Cert) (d cd : ℕ) (c : Cut) : Bool :=
  c.known.isEmpty && c.knownIf.all (winTripOk C d cd [(2, 0)] c.start) && c.sems.isEmpty

/-- `walk_path`'s certificate: `WinsAt` (`winsTag d cd`) on `wins` (value `2`) assumed, every cut a
`wpCutOk`. -/
def wpOk (C : Cert) (d cd : ℕ) : Bool :=
  C.sem == [(winsTag d cd, [C.locs.getD 2 0])] && C.cuts.all (wpCutOk C d cd)

/-- A cut of `level_queries`: no bound, its tuples the walk `tW` (`OqMainWins`) of its call of
`opening_queries` on the window pointers' cell `3` and `n_iters_g`'s, conditional on the latter
holding the one-limb word `g^n` (`impTag tW 1 l`). -/
def lqCutOk (tW n : ℕ) (c : Cut) : Bool :=
  c.known.isEmpty && c.knownIf.isEmpty && c.sems.all fun t ↦
    t.1 == impTag tW 1 (impImm t.1) && decide (K.ofBits (impImm t.1) = gpowK n) &&
      t.2.length == 2 && t.2.getD 0 0 == 3

/-- `level_queries`' certificate: its windows (`lqTag`) on `win_ptrs` (cell `3`) assumed, every cut
an `lqCutOk`. -/
def lqOk (C : Cert) (n odd base d cd : ℕ) : Bool :=
  C.sem == [(lqTag n odd base d cd, [3])] && C.cuts.all (lqCutOk (walkTag (2 + base) odd d cd) n)



/-! ## The tags -/

theorem walkTag_ge (kind odd d cd : ℕ) : 2 ≤ walkTag kind odd d cd := by
  unfold walkTag; omega

theorem semRel_lt {t : ℕ} (ht : t < 2 ^ 21) (rd : Reader) (ws : List E) :
    SemRel glob t rd ws ↔ SemRel0 glob t rd ws := by
  unfold SemRel
  rw [ite_eq_right_of_eq_false _ _ (eq_false (by omega)),
    ite_eq_right_of_eq_false _ _ (eq_false (by omega))]

/-- A walk tag of a kind but `2` is not `tagGkr` (`2^20`, a multiple of `4`). -/
theorem walkTag_ne_gkr {kind odd d cd : ℕ} (hk : kind < 4) (h2 : kind ≠ 2) :
    walkTag kind odd d cd ≠ tagGkr := by
  rw [show tagGkr = 4 * 262144 from rfl]
  unfold walkTag
  omega

theorem semRel0_walk {t : ℕ} (ht : 2 ≤ t) (hg : t ≠ tagGkr) (hl : t < 2 ^ 21) (rd : Reader)
    (ws : List E) : SemRel0 glob t rd ws ↔ walkSem t rd ws := by
  unfold SemRel0
  rw [ite_eq_right_of_eq_false _ _ (eq_false (by unfold tagNe; omega))]
  obtain ⟨n, rfl⟩ : ∃ n, t = n + 2 := ⟨t - 2, by omega⟩
  change (if n + 2 = tagGkr then GkrPar rd (ws.getD 0 0) (ws.getD 1 0) (ws.getD 2 0) (ws.getD 3 0)
    (ws.getD 4 0) else if 2 ^ 21 ≤ n + 2 then lqSem (n + 2) rd ws else walkSem (n + 2) rd ws) ↔ _
  rw [ite_eq_right_of_eq_false _ _ (eq_false hg), ite_eq_right_of_eq_false _ _ (eq_false (by omega))]

theorem semRel_ne (rd : Reader) (ws : List E) : SemRel glob tagNe rd ws ↔ ws.getD 0 0 ≠ ws.getD 1 0 := by
  rw [semRel_lt (by unfold tagNe; norm_num)]
  unfold SemRel0
  rw [ite_eq_left_of_eq_true _ _ (eq_true rfl)]

theorem semRel0_w0 {d cd : ℕ} (hc : cd < 64) (hl : walkTag 0 0 d cd < 2 ^ 21) (rd : Reader) (ws : List E) :
    SemRel0 glob (walkTag 0 0 d cd) rd ws ↔ WinWalk rd d cd (ws.getD 0 0) (ws.getD 1 0) (ws.getD 2 0) := by
  rw [semRel0_walk (walkTag_ge _ _ _ _) (walkTag_ne_gkr (by omega) (by omega)) hl]
  obtain ⟨h1, h2, h3, h4⟩ := walkTag_decode (d := d) (by decide : 0 < 4) (by decide : 0 < 2) hc
  simp only [walkSem, h1, h2, h3, h4]
  rfl

theorem semRel_w0 {d cd : ℕ} (hc : cd < 64) (hlt : walkTag 0 0 d cd < 2 ^ 21)
    (rd : Reader) (ws : List E) :
    SemRel glob (walkTag 0 0 d cd) rd ws ↔ WinWalk rd d cd (ws.getD 0 0) (ws.getD 1 0) (ws.getD 2 0) := by
  rw [semRel_lt hlt, semRel0_w0 hc hlt]

/-- **`walk_path`'s tag**: its windows at the tuple's one word. -/
theorem semRel_wins {d cd : ℕ} (hc : cd < 64) (hlt : winsTag d cd < 2 ^ 21) (rd : Reader)
    (ws : List E) : SemRel glob (winsTag d cd) rd ws ↔ WinsAt rd d cd (ws.getD 0 0) := by
  unfold winsTag at hlt ⊢
  rw [semRel_lt hlt, semRel0_walk (walkTag_ge _ _ _ _) (walkTag_ne_gkr (by omega) (by omega)) hlt]
  obtain ⟨h1, h2, h3, h4⟩ := walkTag_decode (d := d) (by decide : 0 < 4) (by decide : 1 < 2) hc
  simp only [walkSem, h1, h2, h3, h4]
  rfl

theorem semRel0_w1 {odd d cd : ℕ} (ho : odd < 2) (hc : cd < 64) (hl : walkTag 1 odd d cd < 2 ^ 21)
    (rd : Reader) (ws : List E) :
    SemRel0 glob (walkTag 1 odd d cd) rd ws ↔
      WinWalk2 rd d cd odd (ws.getD 0 0) (ws.getD 1 0) (ws.getD 2 0) := by
  rw [semRel0_walk (walkTag_ge _ _ _ _) (walkTag_ne_gkr (by omega) (by omega)) hl]
  obtain ⟨h1, h2, h3, h4⟩ := walkTag_decode (d := d) (by decide : 1 < 4) ho hc
  simp only [walkSem, h1, h2, h3, h4]

theorem semRel_w1 {odd d cd : ℕ} (ho : odd < 2) (hc : cd < 64) (hlt : walkTag 1 odd d cd < 2 ^ 21)
    (rd : Reader) (ws : List E) :
    SemRel glob (walkTag 1 odd d cd) rd ws ↔
      WinWalk2 rd d cd odd (ws.getD 0 0) (ws.getD 1 0) (ws.getD 2 0) := by
  rw [semRel_lt hlt, semRel0_w1 ho hc hlt]

theorem semRel_main {odd d cd base : ℕ} (ho : odd < 2) (hc : cd < 64) (hb : base < 2)
    (hlt : walkTag (2 + base) odd d cd < tagGkr) (rd : Reader) (ws : List E) :
    SemRel glob (walkTag (2 + base) odd d cd) rd ws ↔
      OqMainWins rd d cd odd base (ws.getD 0 0) (ws.getD 1 0) := by
  have hl : walkTag (2 + base) odd d cd < 2 ^ 21 := lt_trans hlt (by unfold tagGkr; norm_num)
  rw [semRel_lt hl, semRel0_walk (walkTag_ge _ _ _ _) hlt.ne hl]
  obtain ⟨h1, h2, h3, h4⟩ := walkTag_decode (d := d) (by omega : 2 + base < 4) ho hc
  obtain rfl | rfl : base = 0 ∨ base = 1 := by omega
  · simp only [walkSem, h1, h2, h3, h4]
  · simp only [walkSem, h1, h2, h3, h4]

/-- A conditional tag on the immediate `1` at position `1`: the relation holds if the second word
is `1`. -/
theorem semRel_imp {t : ℕ} (ht : t < 2 ^ 21) (rd : Reader) (ws : List E) :
    SemRel glob (impTag t 1 1) rd ws ↔ (ws.getD 1 0 = 1 → SemRel0 glob t rd ws) := by
  have ht : t < 2 ^ 32 := by omega
  have e1 : impPos (impTag t 1 1) = 1 := by
    unfold impPos impTag
    rw [Nat.add_mul_div_left _ _ (by positivity), Nat.div_eq_of_lt ht]
  have e2 : impImm (impTag t 1 1) = 1 := by
    unfold impImm impTag
    rw [Nat.add_mul_div_left _ _ (by positivity), Nat.div_eq_of_lt ht]
  have e3 : impBase (impTag t 1 1) = t := by
    unfold impBase impTag
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt ht]
  have hone : OffsetInstruction.immediateWord 1 0 0 = 1 := (Exec.imm_of_ofBits rfl).trans Exec.ofK_one
  unfold SemRel
  rw [ite_eq_left_of_eq_true _ _ (eq_true (by unfold impTag; omega)), e1, e2, e3, hone]

/-- **`level_queries`' tag**: `OqMainWins` of its walk on the tuple's one word, at `g^n`. -/
theorem semRel_lq {n odd base d cd : ℕ} (ho : odd < 2) (hb : base < 2) (hc : cd < 64) (hd : d < 64)
    (hn : n < 992) (rd : Reader) (ws : List E) :
    SemRel glob (lqTag n odd base d cd) rd ws ↔
      OqMainWins rd d cd odd base (ws.getD 0 0) (Protocol.Verifier.gen ^ n) := by
  have hw := walkTag_lt (kind := 2 + base) (by omega) ho hc hd
  have hlt : lqTag n odd base d cd < 2 ^ 26 := by unfold lqTag; omega
  have hge : 2 ^ 21 ≤ lqTag n odd base d cd := by unfold lqTag; omega
  unfold SemRel SemRel0
  rw [ite_eq_right_of_eq_false _ _ (eq_false (by omega)),
    ite_eq_right_of_eq_false _ _ (eq_false (by omega)),
    ite_eq_right_of_eq_false _ _ (eq_false (by unfold tagNe; omega))]
  obtain ⟨m, hm⟩ : ∃ m, lqTag n odd base d cd = m + 2 := ⟨lqTag n odd base d cd - 2, by omega⟩
  change globSem (lqTag n odd base d cd) rd ws ↔ _
  rw [hm]
  change (if m + 2 = tagGkr then GkrPar rd (ws.getD 0 0) (ws.getD 1 0) (ws.getD 2 0) (ws.getD 3 0)
    (ws.getD 4 0) else if 2 ^ 21 ≤ m + 2 then lqSem (m + 2) rd ws else walkSem (m + 2) rd ws) ↔ _
  rw [ite_eq_right_of_eq_false _ _ (eq_false (by unfold tagGkr; omega)),
    ite_eq_left_of_eq_true _ _ (eq_true (by omega)), ← hm]
  obtain ⟨e1, e2⟩ := lqTag_decode (n := n) hb ho hc hd
  obtain ⟨h1, h2, h3, h4⟩ := walkTag_decode (d := d) (by omega : 2 + base < 4) ho hc
  simp only [lqSem, e1, e2, h1, h2, h3, h4, Nat.add_sub_cancel_left]

/-! ## The certificates' cells -/

theorem valG_n {κ : ℕ} (L : MemoryImage κ) (fp : K) (C : Cert) (v : ℕ) :
    valG L fp C (.n v) = wd L fp (C.locs.getD v 0) := rfl

theorem getD_map_lt {f : ℕ → E} {l : List ℕ} {i : ℕ} (h : i < l.length) :
    (l.map f).getD i 0 = f (l.getD i 0) := by
  rw [List.getD_eq_getElem _ _ (by simpa using h), List.getD_eq_getElem _ _ h, List.getElem_map]

theorem cutAt_mem {C : Cert} {i : ℕ} (hi : i ≤ C.cuts.length) (h0 : 0 < i) : C.cutAt i ∈ C.cuts := by
  obtain ⟨i, rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
  have hc : C.cutAt (i + 1) = C.cuts[i]'(by omega) := by
    simp only [Cert.cutAt]
    exact nth_eq _
  rw [hc]
  exact List.getElem_mem _

theorem memIf_of_wins {κ : ℕ} {L : MemoryImage κ} {fp : K} {C : Cert} {d cd start : ℕ}
    {src : List (ℕ × ℕ)} {knownIf : List (ℕ × ℕ × ℕ)}
    (hok : knownIf.all (winTripOk C d cd src start) = true)
    (hw : ∀ v ∈ src, v.2 ≤ start → WinsAt L.read d cd (valG L fp C (.n v.1))) :
    MemIf L fp knownIf := by
  intro m hm val hv
  have h := List.all_eq_true.mp hok m hm
  simp only [winTripOk, List.any_eq_true, Bool.and_eq_true, beq_iff_eq, Nat.ble_eq,
    Nat.blt_eq] at h
  obtain ⟨v, hv', ⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  have hW := hw v hv' h2
  rw [valG_n, ← h1] at hW
  obtain ⟨e, he, rfl⟩ := hW m.2.1 h3 val hv
  exact ⟨e, lt_of_lt_of_le he h4, rfl⟩

/-- A tuple `winSemOk` accepts holds: `WinsAt` of a loaded window pointer. -/
theorem semRel_of_winSem {κ : ℕ} {L : MemoryImage κ} {fp : K} {C : Cert} {d cd start : ℕ}
    {src : List (ℕ × ℕ)} {t : ℕ × List ℕ} (hc : cd < 64) (hlt : winsTag d cd < 2 ^ 21)
    (hok : winSemOk C d cd src start t = true)
    (hw : ∀ v ∈ src, v.2 ≤ start → WinsAt L.read d cd (valG L fp C (.n v.1))) :
    SemRel glob t.1 L.read (t.2.map (wd L fp)) := by
  simp only [winSemOk, List.any_eq_true, Bool.and_eq_true, beq_iff_eq, Nat.ble_eq] at hok
  obtain ⟨v, hv, rfl, hle⟩ := hok
  rw [semRel_wins hc hlt]
  exact hw v hv hle

/-! ## The loops -/

/-- **A loop's cut obligations**, from its certificate's check (`loopOk`) and the walk's facts on
the prefixes of its body: the window pointers `src` name windows, the tail passes the walk on. -/
theorem loop_cutsKnown {j tag d cd xv tl : ℕ} {src : List (ℕ × ℕ)} (hc : cd < 64)
    (hltw : winsTag d cd < 2 ^ 21)
    (hok : loopOk (certOf j) tag d cd src xv tl = true) (W : Reader → E → E → E → Prop)
    (hsem : ∀ rd ws, SemRel glob tag rd ws ↔ W rd (ws.getD 0 0) (ws.getD 1 0) (ws.getD 2 0))
    (hwins : ∀ {κ : ℕ} (L : MemoryImage κ) (σ : Val) (n : ℕ),
      Stmt.HoldsList (coreProgram.Rel L.read) L.read σ ((coreOf j).body.take n) True (fun _ ↦ True) →
      W L.read (σ (.n 2)) (σ (.n 0)) (σ (.n 1)) → σ (.n 0) ≠ σ (.n 1) →
      ∀ v ∈ src, v.2 ≤ n → WinsAt L.read d cd (σ (.n v.1)))
    (htail : ∀ {κ : ℕ} (L : MemoryImage κ) (σ : Val) (n : ℕ), tl ≤ n →
      Stmt.HoldsList (coreProgram.Rel L.read) L.read σ ((coreOf j).body.take n) True (fun _ ↦ True) →
      W L.read (σ (.n 2)) (σ (.n 0)) (σ (.n 1)) → σ (.n 0) ≠ σ (.n 1) →
      W L.read (σ (.n 2)) (σ (.n xv)) (σ (.n 1))) :
    CutsKnown j := by
  intro κ L _ _ fp _ hsem' i hi h0 hl
  simp only [loopOk, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at hok
  obtain ⟨hs, hcuts⟩ := hok
  rw [hs] at hsem'
  have hW : W L.read (valG L fp (certOf j) (.n 2)) (valG L fp (certOf j) (.n 0))
      (valG L fp (certOf j) (.n 1)) :=
    (hsem _ _).mp (hsem' _ (List.mem_cons_self ..))
  have hne : valG L fp (certOf j) (.n 0) ≠ valG L fp (certOf j) (.n 1) :=
    (semRel_ne _ _).mp (hsem' _ (List.mem_cons_of_mem _ (List.mem_singleton_self _)))
  have hcut := hcuts _ (cutAt_mem hi h0)
  simp only [loopCutOk, Bool.and_eq_true, List.isEmpty_iff, List.all_eq_true] at hcut
  obtain ⟨⟨hkn, hki⟩, hsm⟩ := hcut
  have hwv := fun v hv hle ↦ hwins L _ _ hl hW hne v hv hle
  refine ⟨by rw [hkn]; intro _ h; simp at h, memIf_of_wins (by simpa using hki) hwv,
    fun t ht ↦ ?_⟩
  rcases Bool.or_eq_true_iff.mp (hsm t ht) with h | h
  · simp only [Bool.and_eq_true, beq_iff_eq, Nat.ble_eq] at h
    obtain ⟨rfl, hle⟩ := h
    exact (hsem _ _).mpr (htail L _ _ hle hl hW hne)
  · exact semRel_of_winSem hc hltw h hwv

/-! ## The specializations -/

/-- **A specialization's cut obligations**, from its certificate's check (`mainOk`): its
precondition `OqMainWins`, the window pointers `src` an odd count's first query loads (a fact on
the prefixes of its body), and the walk from `1` its loop call starts (`OqMainWins`' second half). -/
theorem main_cutsKnownG {j o d cd base : ℕ} {src : List (ℕ × ℕ)} (ho : o < 2)
    (hodd : o = 1 → base = 1) (hc : cd < 64) (hbase : base < 2)
    (hlt : walkTag (2 + base) o d cd < tagGkr)
    (hltW : walkTag (if base = 1 then 1 else 0) o d cd < 2 ^ 21)
    (hltw : winsTag d cd < 2 ^ 21)
    (hok : mainOk (certOf j) (walkTag (2 + base) o d cd) (walkTag (if base = 1 then 1 else 0) o d cd)
      d cd src = true)
    (hwins : ∀ {κ : ℕ} (L : MemoryImage κ) (σ : Val) (n : ℕ),
      Stmt.HoldsList (coreProgram.Rel L.read) L.read σ ((coreOf j).body.take n) True (fun _ ↦ True) →
      OqMainWins L.read d cd o base (σ (.n 4)) (σ (.n 6)) →
      ∀ v ∈ src, v.2 ≤ n → WinsAt L.read d cd (σ (.n v.1))) :
    CutsKnown j := by
  intro κ L _ _ fp _ hsem' i hi h0 hl
  simp only [mainOk, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at hok
  obtain ⟨hs, hcuts⟩ := hok
  rw [hs] at hsem'
  have hW : OqMainWins L.read d cd o base (valG L fp (certOf j) (.n 4))
      (valG L fp (certOf j) (.n 6)) :=
    (semRel_main ho hc hbase hlt _ _).mp (hsem' _ (List.mem_singleton_self _))
  have hcut := hcuts _ (cutAt_mem hi h0)
  simp only [mainCutOk, Bool.and_eq_true, List.isEmpty_iff, List.all_eq_true] at hcut
  obtain ⟨⟨hkn, hki⟩, hsm⟩ := hcut
  have hwv := fun v hv hle ↦ hwins L _ _ hl hW v hv hle
  refine ⟨by rw [hkn]; intro _ h; simp at h, memIf_of_wins (by simpa using hki) hwv,
    fun t ht ↦ ?_⟩
  rcases Bool.or_eq_true_iff.mp (hsm t ht) with ht' | ht'
  swap
  · exact semRel_of_winSem hc hltw ht' hwv
  · simp only [Bool.and_eq_true, beq_iff_eq] at ht'
    obtain ⟨⟨⟨ht1, hlen⟩, ha⟩, hb'⟩ := ht'
    rw [ht1, semRel_imp hltW]
    intro hx
    rw [getD_map_lt (by omega)] at hx
    have h2 := hW.2
    split at h2
    · rename_i h1
      rw [ite_eq_left_of_eq_true _ _ (eq_true h1), semRel0_w1 ho hc (by simpa [h1] using hltW),
        getD_map_lt (by omega),
        getD_map_lt (by omega), getD_map_lt (by omega), hx, ha, hb']
      exact h2
    · rename_i h1
      obtain rfl : o = 0 := by have := mt hodd h1; omega
      rw [ite_eq_right_of_eq_false _ _ (eq_false h1), semRel0_w0 hc (by simpa [h1] using hltW),
        getD_map_lt (by omega),
        getD_map_lt (by omega), getD_map_lt (by omega), hx, ha, hb']
      exact h2

/-! ## `walk_path` -/

/-- **`walk_path`'s cut obligations**: its precondition `WinsAt` on `wins` (value `2`), every
window bound one of its windows'. -/
theorem wp_cutsKnown {j d cd : ℕ} (hc : cd < 64) (hltw : winsTag d cd < 2 ^ 21)
    (hok : wpOk (certOf j) d cd = true) : CutsKnown j := by
  intro κ L _ _ fp _ hsem' i hi h0 _
  simp only [wpOk, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at hok
  obtain ⟨hs, hcuts⟩ := hok
  rw [hs] at hsem'
  have hW : WinsAt L.read d cd (valG L fp (certOf j) (.n 2)) := by
    have := (semRel_wins hc hltw _ _).mp (hsem' _ (List.mem_singleton_self _))
    simpa [valG_n] using this
  have hcut := hcuts _ (cutAt_mem hi h0)
  simp only [wpCutOk, Bool.and_eq_true, List.isEmpty_iff] at hcut
  obtain ⟨⟨hkn, hki⟩, hsm⟩ := hcut
  refine ⟨by rw [hkn]; intro _ h; simp at h, memIf_of_wins hki fun v hv _ ↦ ?_,
    by rw [hsm]; intro _ h; simp at h⟩
  simp only [List.mem_singleton] at hv
  subst hv
  exact hW



/-- A conditional tag on the immediate `l` at position `1`: the relation holds if the second
word is `l`'s. -/
theorem semRel_impL {t : ℕ} (ht : t < 2 ^ 32) (l : ℕ) (rd : Reader) (ws : List E) :
    SemRel glob (impTag t 1 l) rd ws ↔
      (ws.getD 1 0 = OffsetInstruction.immediateWord l 0 0 → SemRel0 glob t rd ws) := by
  have e0 : impTag t 1 l / 2 ^ 32 = 1 + 1 + 8 * l := by
    unfold impTag
    rw [Nat.add_mul_div_left _ _ (by positivity), Nat.div_eq_of_lt ht, Nat.zero_add]
  have e1 : impPos (impTag t 1 l) = 1 := by unfold impPos; rw [e0]; omega
  have e2 : impImm (impTag t 1 l) = l := by unfold impImm; rw [e0]; omega
  have e3 : impBase (impTag t 1 l) = t := by
    unfold impBase impTag
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt ht]
  unfold SemRel
  rw [ite_eq_left_of_eq_true _ _ (eq_true (by unfold impTag; omega)), e1, e2, e3]

/-- **`level_queries`' cut obligations**, from its certificate's check: its precondition's
windows are the call's walk at `g^n`. -/
theorem lq_cutsKnown {j n odd base d cd : ℕ} (ho : odd < 2) (hb : base < 2) (hc : cd < 64)
    (hd : d < 64) (hn : n < 992) (hok : lqOk (certOf j) n odd base d cd = true) : CutsKnown j := by
  intro κ L _ _ fp _ hsem' i hi h0 _
  simp only [lqOk, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at hok
  obtain ⟨hs, hcuts⟩ := hok
  rw [hs] at hsem'
  have hW := (semRel_lq ho hb hc hd hn _ _).mp (hsem' _ (List.mem_singleton_self _))
  simp only [List.map_cons, List.map_nil, List.getD_cons_zero] at hW
  have hcut := hcuts _ (cutAt_mem hi h0)
  simp only [lqCutOk, Bool.and_eq_true, List.isEmpty_iff, List.all_eq_true] at hcut
  obtain ⟨⟨hkn, hki⟩, hsm⟩ := hcut
  refine ⟨by rw [hkn]; intro _ h; simp at h, by rw [hki]; intro _ h; simp at h, fun t ht ↦ ?_⟩
  have h1 := hsm t ht
  simp only [beq_iff_eq, decide_eq_true_eq] at h1
  obtain ⟨⟨⟨ht1, hl0⟩, hlen⟩, h3⟩ := h1
  have hw := walkTag_lt (kind := 2 + base) (by omega) ho hc hd
  have hgk : walkTag (2 + base) odd d cd < tagGkr := by unfold tagGkr; omega
  rw [ht1, semRel_impL (by omega), ← semRel_lt (by omega), semRel_main ho hc hb hgk]
  intro hx
  rw [getD_map_lt (by omega)] at hx
  rw [getD_map_lt (by omega), getD_map_lt (by omega), hx, h3, Exec.imm_of_ofBits hl0,
    gpowK_eq (lt_trans hn (by unfold u128Bound; norm_num)), ← Value.gen_pow_eq_ofK]
  exact hW

end
end LeanVM.SaltedGuest.End
