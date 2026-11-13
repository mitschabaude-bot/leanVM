/-
  LeanVM.Guest.SoundFacts

  The certificate facts B2's soundness reads off the deployed bytecode's checks, semantics-free:
  the checked windows, the functions' names and their windows' hand-overs.
-/

module

public import LeanVM.Guest.Checked
public import LeanVM.Guest.CoreNames
public import LeanVM.Guest.JumpTable
public import LeanVM.Guest.CertName

/-!
# The checks' facts

What `Sound.lean` reads off the certificates and the kernel's checks (`Checked.all_ok`), none of
it about the semantics of `KECCAK`: every window of every function passes (`winOk_of`), the jump
table the checks read is the one `__jump_tables` writes (`jtHolds_of`), the windows hand nothing
on but in `main` (after `exponent_tables`, `main_cut`), `verify_sub` (function `19`, from its calls
of `verify_tables`, `vs_cut1`, and `check_opening_terminal`, `vs_cut`) and the walks
(`Checked.oblFns`), and `main`'s certificate (`main_facts`).
-/

namespace LeanVM.Guest.End

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Check
open LeanVM.Guest.Exec

@[expose] public section

theorem certOf_pows (j : ℕ) : (certOf j).facts.pows = Data.powTree := by
  unfold certOf
  split
  rfl

theorem certOf_pows_ok (j : ℕ) : (certOf j).facts.pows.Ok := by
  rw [certOf_pows]
  exact PowTree.ok_of_okW Checked.powTree_ok

theorem functions_length : Data.functions.length = nFns := by decide +kernel

theorem coreProgram_length' : coreProgram.length + 1 = nFns := by
  rw [coreProgram_length]; rfl

theorem fnOf_mem {j : ℕ} (h : j < nFns) : fnOf j ∈ Data.functions := by
  unfold fnOf
  rw [nth_eq (functions_length ▸ h)]
  exact List.getElem_mem _

theorem coreOf_find {j : ℕ} (h1 : 1 ≤ j) (h2 : j < nFns) :
    coreProgram.find? (coreOf j).name = some (coreOf j) := by
  have h : j - 1 < coreProgram.length := by have := coreProgram_length'; omega
  unfold coreOf
  rw [nth_eq h]
  exact coreProgram_find_getElem h

theorem winOk_of {j : ℕ} (h1 : 1 ≤ j) (h2 : j < nFns) :
    ∀ i ≤ (certOf j).cuts.length, checkWin glob (fnOf j) (coreOf j) (certOf j) (j == 1) i = true :=
  Checked.all_ok j h1 h2

theorem jtHolds_of {κ : ℕ} {L : MemoryImage κ} (h : JumpTables L) : JTHolds glob L :=
  JumpTable.jt_of_jumpTables h (PowTree.ok_of_okW Checked.powTree_ok)

/-- A function's cuts hand nothing on (`Checked.Plain`): every cut's memory bounds, conditional
memory bounds and semantic tuples hold, vacuously. -/
theorem known_of_plain {j : ℕ} (hp : Checked.Plain j) {κ : ℕ} {L : MemoryImage κ} {fp : K} {i : ℕ}
    (hi : i ≤ (certOf j).cuts.length) (h0 : 0 < i) :
    MemKnown L fp ((certOf j).cutAt i).known ∧ MemIf L fp ((certOf j).cutAt i).knownIf ∧
      SemHolds glob L fp ((certOf j).cutAt i).sems := by
  obtain ⟨i, rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
  have hall := List.all_eq_true.mp hp ((certOf j).cuts[i]'(by omega)) (List.getElem_mem _)
  simp only [Bool.and_eq_true, List.isEmpty_iff] at hall
  have hc : (certOf j).cutAt (i + 1) = (certOf j).cuts[i]'(by omega) := by
    simp only [Cert.cutAt]
    exact nth_eq _
  rw [hc, hall.1.1, hall.1.2, hall.2]
  exact ⟨fun _ h ↦ by simp at h, fun _ h ↦ by simp at h, fun _ h ↦ by simp at h⟩

/-- **The exponent table's tag**: tag `0` of `glob` on one word is `B1.ExpTables`. -/
theorem semRel_exp (rd : Reader) (ws : List E) :
    SemRel glob 0 rd ws ↔ B1.ExpTables rd (ws.getD 0 0) := by
  simp [SemRel, SemRel0, tagNe, glob, globSem]

/-- The semantic tuples of the functions `a ..< a + n` are on their argument cells
`2 ..< 2 + nargs`, decided. -/
noncomputable def sigSemArgsB (a n : ℕ) : Bool :=
  (List.range' a n).all fun j ↦ (glob.sig j).sem.all fun s ↦ s.2.all fun o ↦
    Nat.ble 2 o && Nat.blt o (2 + (glob.sig j).nargs)

/-! The functions in twelve runs of `128`, each its own kernel check and one at a time: one check
of all `nFns` holds every function's data at once. -/

set_option Elab.async false in
theorem sigSemArgsB_0 : sigSemArgsB 0 128 = true := by decide +kernel

set_option Elab.async false in
theorem sigSemArgsB_128 : sigSemArgsB 128 128 = true := by decide +kernel

set_option Elab.async false in
theorem sigSemArgsB_256 : sigSemArgsB 256 128 = true := by decide +kernel

set_option Elab.async false in
theorem sigSemArgsB_384 : sigSemArgsB 384 128 = true := by decide +kernel

set_option Elab.async false in
theorem sigSemArgsB_512 : sigSemArgsB 512 128 = true := by decide +kernel

set_option Elab.async false in
theorem sigSemArgsB_640 : sigSemArgsB 640 128 = true := by decide +kernel

set_option Elab.async false in
theorem sigSemArgsB_768 : sigSemArgsB 768 128 = true := by decide +kernel

set_option Elab.async false in
theorem sigSemArgsB_896 : sigSemArgsB 896 128 = true := by decide +kernel

set_option Elab.async false in
theorem sigSemArgsB_1024 : sigSemArgsB 1024 128 = true := by decide +kernel

set_option Elab.async false in
theorem sigSemArgsB_1152 : sigSemArgsB 1152 128 = true := by decide +kernel

set_option Elab.async false in
theorem sigSemArgsB_1280 : sigSemArgsB 1280 128 = true := by decide +kernel

set_option Elab.async false in
theorem sigSemArgsB_1408 : sigSemArgsB 1408 128 = true := by decide +kernel

theorem sigSemArgsB_eq : ∀ q < 12, sigSemArgsB (128 * q) 128 = true := by
  intro q hq
  interval_cases q
  exacts [sigSemArgsB_0, sigSemArgsB_128, sigSemArgsB_256, sigSemArgsB_384, sigSemArgsB_512,
    sigSemArgsB_640, sigSemArgsB_768, sigSemArgsB_896, sigSemArgsB_1024, sigSemArgsB_1152,
    sigSemArgsB_1280, sigSemArgsB_1408]

/-- **Every function's semantic tuples read only its argument words**: their cells are argument
cells (and a tuple's relation, `SemRel glob t rd ws`, reads only the memory and the words). -/
theorem sigSem_args {j : ℕ} (hj : j < nFns) :
    ∀ s ∈ (glob.sig j).sem, ∀ o ∈ s.2, 2 ≤ o ∧ o < 2 + (glob.sig j).nargs := by
  intro s hs o ho
  have hq : j / 128 < 12 := by simp only [nFns] at hj; omega
  have h := List.all_eq_true.mp (sigSemArgsB_eq (j / 128) hq) j (by rw [List.mem_range'_1]; omega)
  have h' := List.all_eq_true.mp (List.all_eq_true.mp h s hs) o ho
  simp only [Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq] at h'
  exact h'

theorem nameIndex_coreOf {j : ℕ} (h1 : 1 ≤ j) (h2 : j < nFns) : nameIndex (coreOf j).name = j := by
  have hl : j - 1 < coreProgram.length := by
    have : coreProgram.length = 1535 := coreProgram_length
    simp only [nFns] at h2
    omega
  unfold nameIndex coreOf
  rw [nth_eq hl, findIdx_name_of_nodup coreProgram_names_nodup hl]
  omega

/-- Two functions of one name are one (`coreProgram_names_nodup`). -/
theorem sig_name_inj {j j' : ℕ} (h1 : 1 ≤ j) (h2 : j < nFns) (h1' : 1 ≤ j') (h2' : j' < nFns)
    (h : (glob.sig j).name = (glob.sig j').name) : j = j' := by
  have e : (coreOf j).name = (coreOf j').name := h
  rw [← nameIndex_coreOf h1 h2, ← nameIndex_coreOf h1' h2', e]

/-! ## `verify_sub`'s window -/

theorem vs_cuts : (certOf 19).cuts.length = 2 := by decide +kernel

/-- The bound of entry `c` of `kappa_base` (`lean_ethereum.py:3255-3263`): `kb[0] = g^0`, the
memory's log and the six tables' heights `kb[1..6]` below `g^31`, and `kb[7]`, keccak's `τ`,
below `g^25` (`τ + 6` is a column's log, at most `30`). -/
def vsKbBound (c : ℕ) : ℕ := [1, 31, 31, 31, 31, 31, 31, 25].getD c 0

/-- `verify_sub`'s bound of the memory's log: entry `0` of `dims_g` (the value `127`) among `g^e`,
`e < 34`, which `verify_tables` dispatches on (the tables' logs, entries `1` to `6`, are range
checked in `verify_tables` itself, `lean_ethereum.py:2189`). -/
def vsDimsKnown (c : ℕ) : List (ℕ × ℕ × ℕ) := [(c, 0, 34)]

/-- `verify_sub`'s second window starts at its call of `verify_tables` (statement `552`) and takes
the bound of entry `0` of `dims_g` (the value `127`). -/
theorem vs_cut1 : ((certOf 19).cutAt 1).start = 552 ∧
    ((certOf 19).cutAt 1).known = vsDimsKnown ((certOf 19).locs.getD 127 0) ∧
    ((certOf 19).cutAt 1).knownIf = [] ∧ ((certOf 19).cutAt 1).sems = [] := by decide +kernel

/-- `verify_sub`'s third window starts at its call of `check_opening_terminal` (statement
`1593`) and takes, beside `dims_g`'s, the bound of each of the `8` entries of `kappa_base` (the
value `139`). -/
theorem vs_cut : ((certOf 19).cutAt 2).start = 1593 ∧
    ((certOf 19).cutAt 2).known = vsDimsKnown ((certOf 19).locs.getD 127 0) ++
      (List.range 8).map (fun c ↦ ((certOf 19).locs.getD 139 0, c, vsKbBound c)) ∧
    ((certOf 19).cutAt 2).knownIf = [] ∧ ((certOf 19).cutAt 2).sems = [] := by decide +kernel

theorem vs_cells : (certOf 19).locs.getD 4 0 = 6 := by decide +kernel

theorem vs_sem : (certOf 19).sem = [(0, [6])] := by decide +kernel

theorem coreOf_19 : coreOf 19 = Data.core18 := rfl

/-! ## `main`'s window -/

/-- `main`'s one cut, after its call of `exponent_tables` (`main_call`), takes the exponent
table's relation (tag `0`) on that call's return cell. -/
theorem main_cut : (certOf 1).cuts.length = 1 ∧ ((certOf 1).cutAt 1).known = [] ∧
    ((certOf 1).cutAt 1).knownIf = [] ∧
    ((certOf 1).cutAt 1).sems = [(0, [(certOf 1).locs.getD 28 0])] := by
  decide +kernel

/-- `main`'s statement `16` is its call of `exponent_tables`, before its cut, after no `ret`. -/
theorem main_exp : (coreOf 1).body[16]? = some (.call "exponent_tables" [] [.n 28]) := rfl

theorem main_exp_lt : 16 < ((certOf 1).cutAt 1).start := by decide +kernel

theorem main_exp_noRet : Stmt.noRetList ((coreOf 1).body.take 16) = true := by decide +kernel

/-- The statements before `main`'s cut, at its call of `exponent_tables` (wherever the cut is). -/
theorem main_call : (coreOf 1).body.take ((certOf 1).cutAt 1).start =
    (coreOf 1).body.take 16 ++ .call "exponent_tables" [] [.n 28] ::
      ((coreOf 1).body.take ((certOf 1).cutAt 1).start).drop 17 := by
  have h1 := main_exp
  have h2 := main_exp_lt
  generalize (coreOf 1).body = l at h1 ⊢
  generalize ((certOf 1).cutAt 1).start = n at h2 ⊢
  have h : (l.take n)[16]? = some (.call "exponent_tables" [] [.n 28]) := by
    rw [List.getElem?_take_of_lt h2, h1]
  have hl : 16 < (l.take n).length := (List.getElem?_eq_some_iff.mp h).1
  conv_lhs => rw [← List.take_append_drop 16 (l.take n)]
  rw [List.take_take, Nat.min_eq_left h2.le, List.drop_eq_getElem_cons hl]
  congr 2
  exact (List.getElem?_eq_some_iff.mp h).2

theorem main_facts : (certOf 1).facts.env = [] ∧ (certOf 1).pre = [] ∧ (certOf 1).mem = [] ∧
    (certOf 1).sem = [] ∧ (certOf 1).nret = 0 ∧ (coreOf 1).params = [] ∧ (coreOf 1).name = "main" := by
  decide +kernel

theorem fnOf_1 : (fnOf 1).entryPc = mainEntry := rfl

end
end LeanVM.Guest.End
