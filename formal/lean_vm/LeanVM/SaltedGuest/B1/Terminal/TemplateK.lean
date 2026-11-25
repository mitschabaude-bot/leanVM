/-
  LeanVM.SaltedGuest.B1.Terminal.TemplateK

  The salted `check_opening_terminal`: the deployed template renamed, with the second claims'
  point and their three terms; its loop `__loop15`.
-/

module

public import LeanVM.Guest.B1.Terminal.HoldsOf
public import LeanVM.Guest.Renumber
public import LeanVM.SaltedGuest.B1.Whir.OsSame
public import LeanVM.SaltedGuest.B1.Merkle.CapAll

/-!
# The salted `check_opening_terminal`, as a template

The salted body (`core17`) is the deployed `termT` with its values from `33` on moved by `9`
(`termR`; the tail's by `termR2`, which reads the sum and the power after the inserted terms) and
two insertions:

* after the public input's chain (`termIns1`): the second claims' chain, `chain2[2] =
  pi_chain[1]·point[1]` and `__loop15` (the deployed `__loop14`'s body) writing
  `chain2[k + 1] = chain2[k]·point1[k]`, its value at `g_log_mem` read into `41`;
* after the claims' blocks (`termIns2`): the three second claims' terms, the memory columns'
  selectors (`54`, `58`, `62`, the deployed `selV 0 .. 2` moved) times `41` at the running power
  of `λ`, and the power after them.

`termFoundK`: the function, found by name, has the deployed parameters and the template `termTK`
(the kernel's evaluation of `stmtsEqb`). `loop16Found`, `loop16_step`: `__loop15`'s body is the
deployed loop's, named `__loop15`. `termSame`: the terminal's unchanged callees are in the closed
set and kept by the renaming, so their deployed meanings apply (`Same.rel_same'`).
-/

namespace LeanVM.SaltedGuest.B1.Terminal

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Guest.B1 LeanVM.Guest.B1.VerifySub LeanVM.Protocol LeanVM.Protocol.Verifier

@[expose] public section

/-- The salted terminal's value of the deployed value `k`, in the head, selectors and claims. -/
def termRi (k : ℕ) : ℕ := if k < 33 then k else k + 9

/-- The salted terminal's value of the deployed value `k`, in the tail. -/
def termR2i (k : ℕ) : ℕ :=
  if k < 33 then k else if k = 1764 then 1785 else if k = 1765 then 1786
  else if k < 1766 then k + 9 else k + 21

def termR (v : V) : V := ⟨v.path, v.tag, termRi v.idx⟩

def termR2 (v : V) : V := ⟨v.path, v.tag, termR2i v.idx⟩

/-- The second claims' chain: `chain2` at `33`, its word `2` the product of the public input's
chain's word `1` and the point's coordinate `1`, `__loop15` from `g^2` to `g_log_mem`, its value
at `g_log_mem` in `41`. -/
def termIns1 : List Stmt :=
  [.atom (.hint (.alloc (.n 33) 35)), .atom (.load (.n 34) (.n 24) 1),
    .atom (.load (.n 35) (.n 13) 1), .atom (.mul (.n 36) (.n 34) (.n 35)),
    .atom (.load (.n 36) (.n 33) 2), .atom (.const (.n 37) (word 4 0 0)),
    .atom (.add (.n 38) (.n 37) (.n 6)), .atom (.const (.n 39) (word 4 0 0)),
    .callIf (.n 38) "__loop15" [.n 39, .n 6, .n 33, .n 14],
    .atom (.mul (.n 40) (.n 33) (.n 6)), .atom (.load (.n 41) (.n 40) 0)]

/-- The second claims' terms: the claims' sum at `1773`, the power at `1774`; the sum after them
at `1785`, the power at `1786`. -/
def termIns2 : List Stmt :=
  [.atom (.mul (.n 1775) (.n 1774) (.n 41)), .atom (.mul (.n 1776) (.n 1775) (.n 54)),
    .atom (.add (.n 1777) (.n 1773) (.n 1776)), .atom (.mul (.n 1778) (.n 1774) (.n 9)),
    .atom (.mul (.n 1779) (.n 1778) (.n 41)), .atom (.mul (.n 1780) (.n 1779) (.n 58)),
    .atom (.add (.n 1781) (.n 1777) (.n 1780)), .atom (.mul (.n 1782) (.n 1778) (.n 9)),
    .atom (.mul (.n 1783) (.n 1782) (.n 41)), .atom (.mul (.n 1784) (.n 1783) (.n 62)),
    .atom (.add (.n 1785) (.n 1781) (.n 1784)), .atom (.mul (.n 1786) (.n 1782) (.n 9))]

/-- The deployed head after the public input's chain, the selectors and the claims. -/
def termMidT : List Stmt := termHeadT.drop 20 ++ selsT ++ termClaims.1

/-- **The salted `check_opening_terminal`'s body.** -/
def termTK : List Stmt :=
  termHeadT.take 20 ++ termIns1 ++ Stmt.renameList termR termMidT ++ termIns2 ++
    Stmt.renameList termR2 (termTailT 1766 1764 1765)

set_option maxRecDepth 100000 in
kernel_rfl term_idx17 : SaltedGuest.coreProgram[17]? = some LeanVM.SaltedGuest.Data.core17

set_option maxRecDepth 100000 in
theorem term_bodyK : LeanVM.SaltedGuest.Data.core17.body = termTK :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem termFoundK : ∃ fn : Fn, SaltedGuest.coreProgram.find? "check_opening_terminal" = some fn ∧
    fn.params = termParams ∧ fn.body = termTK :=
  ⟨_, find_of_getElem? term_idx17, rfl, term_bodyK⟩

/-! ## `__loop15` -/

/-- `__loop15`'s body: the deployed loop's, calling itself. -/
def loop16T : List Stmt :=
  [.atom (.mul (.n 4) (.n 2) (.n 0)), .atom (.load (.n 5) (.n 4) 0),
    .atom (.mul (.n 6) (.n 3) (.n 0)), .atom (.load (.n 7) (.n 6) 0),
    .atom (.mul (.n 8) (.n 5) (.n 7)), .atom (.mul (.n 9) (.n 2) (.n 0)),
    .atom (.load (.n 8) (.n 9) 1), .atom (.const (.n 10) (word 2 0 0)),
    .atom (.mul (.n 11) (.n 0) (.n 10)), .atom (.add (.n 12) (.n 11) (.n 1)),
    .atom (.const (.n 13) (word 2 0 0)), .atom (.mul (.n 14) (.n 0) (.n 13)),
    .callIf (.n 12) "__loop15" [.n 14, .n 1, .n 2, .n 3], .ret []]

set_option maxRecDepth 100000 in
kernel_rfl loop16_idx : SaltedGuest.coreProgram[275]? = some LeanVM.SaltedGuest.Data.core275

set_option maxRecDepth 100000 in
theorem loop16_body : LeanVM.SaltedGuest.Data.core275.body = loop16T :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem loop16Found : ∃ fn : Fn, SaltedGuest.coreProgram.find? "__loop15" = some fn ∧
    fn.params = [.n 0, .n 1, .n 2, .n 3] ∧ fn.body = loop16T :=
  ⟨_, find_of_getElem? loop16_idx, rfl, loop16_body⟩

/-- **`__loop15`'s step.** -/
theorem loop16_step {rd : Reader} (d : ℕ) (x N chain p1 : E)
    (h : SaltedGuest.coreProgram.relN rd (d + 1) "__loop15" [x, N, chain, p1] []) :
    PiStep rd chain p1 x ∧
      (x * gen + N ≠ 0 → SaltedGuest.coreProgram.relN rd d "__loop15" [x * gen, N, chain, p1] []) := by
  obtain ⟨fn, hf, σ, hpar, hb⟩ := h
  obtain ⟨fn', hf', hp', hb'⟩ := loop16Found
  rw [hf'] at hf
  cases hf
  rw [hp'] at hpar
  rw [hb'] at hb
  simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hpar
  obtain ⟨rfl, rfl, rfl, rfl⟩ := hpar
  simp only [loop16T, Stmt.HoldsList, Stmt.Holds, Atom.Holds, List.map_cons, List.map_nil] at hb
  obtain ⟨e4, l5, e6, l7, e8, e9, l8, e10, e11, e12, e13, e14, ⟨-, hcall, -⟩⟩ := hb
  refine ⟨⟨σ (.n 5), σ (.n 7), by rw [← e4]; exact l5, by rw [← e6]; exact l7, ?_⟩, fun hne ↦ ?_⟩
  · rw [← e8, ← e9]; exact l8
  · have e : σ (.n 12) = σ (.n 0) * gen + σ (.n 1) := by rw [e12, e11, e10, word_gen]
    have := hcall (by rw [e]; exact hne)
    rw [e14, e13, word_gen] at this
    exact this

/-! ## The unchanged callees -/

set_option maxRecDepth 100000

kernel_rfl tcl_4 : Same.closed[4]? = some ("eq_prefix_chain", 5, 5)
kernel_rfl tdg_5 : Guest.coreProgram[5]? = some LeanVM.Guest.Data.core5
kernel_rfl tcl_13 : Same.closed[13]? = some ("ring_switch_weight", 14, 14)
kernel_rfl tdg_14 : Guest.coreProgram[14]? = some LeanVM.Guest.Data.core14
kernel_rfl tcl_15 : Same.closed[15]? = some ("selector_tables", 16, 16)
kernel_rfl tdg_16 : Guest.coreProgram[16]? = some LeanVM.Guest.Data.core16
kernel_rfl tcl_259 : Same.closed[259]? = some ("__loop14", 274, 272)
kernel_rfl tdg_272 : Guest.coreProgram[272]? = some LeanVM.Guest.Data.core272

theorem same_eq_prefix_chain :
    Same.inS "eq_prefix_chain" = true ∧ Same.rho "eq_prefix_chain" = "eq_prefix_chain" :=
  Whir.sameOf tcl_4 tdg_5 rfl

theorem same_ring_switch_weight :
    Same.inS "ring_switch_weight" = true ∧ Same.rho "ring_switch_weight" = "ring_switch_weight" :=
  Whir.sameOf tcl_13 tdg_14 rfl

theorem same_selector_tables :
    Same.inS "selector_tables" = true ∧ Same.rho "selector_tables" = "selector_tables" :=
  Whir.sameOf tcl_15 tdg_16 rfl

theorem same_loop14 : Same.inS "__loop14" = true ∧ Same.rho "__loop14" = "__loop14" :=
  Whir.sameOf tcl_259 tdg_272 rfl

kernel_rfl tcl_260 : Same.closed[260]? = some ("column_selector__L0", 276, 273)
kernel_rfl tdg_273 : Guest.coreProgram[273]? = some LeanVM.Guest.Data.core273
kernel_rfl tcl_261 : Same.closed[261]? = some ("column_selector__L1", 277, 274)
kernel_rfl tdg_274 : Guest.coreProgram[274]? = some LeanVM.Guest.Data.core274
kernel_rfl tcl_262 : Same.closed[262]? = some ("column_selector__L2", 278, 275)
kernel_rfl tdg_275 : Guest.coreProgram[275]? = some LeanVM.Guest.Data.core275
kernel_rfl tcl_263 : Same.closed[263]? = some ("column_selector__L3", 279, 276)
kernel_rfl tdg_276 : Guest.coreProgram[276]? = some LeanVM.Guest.Data.core276
kernel_rfl tcl_264 : Same.closed[264]? = some ("column_selector__L4", 280, 277)
kernel_rfl tdg_277 : Guest.coreProgram[277]? = some LeanVM.Guest.Data.core277
kernel_rfl tcl_265 : Same.closed[265]? = some ("column_selector__L5", 281, 278)
kernel_rfl tdg_278 : Guest.coreProgram[278]? = some LeanVM.Guest.Data.core278
kernel_rfl tcl_266 : Same.closed[266]? = some ("column_selector__L6", 282, 279)
kernel_rfl tdg_279 : Guest.coreProgram[279]? = some LeanVM.Guest.Data.core279
kernel_rfl tcl_267 : Same.closed[267]? = some ("column_selector__L7", 283, 280)
kernel_rfl tdg_280 : Guest.coreProgram[280]? = some LeanVM.Guest.Data.core280
kernel_rfl tcl_268 : Same.closed[268]? = some ("column_selector__L8", 284, 281)
kernel_rfl tdg_281 : Guest.coreProgram[281]? = some LeanVM.Guest.Data.core281
kernel_rfl tcl_269 : Same.closed[269]? = some ("column_selector__L9", 285, 282)
kernel_rfl tdg_282 : Guest.coreProgram[282]? = some LeanVM.Guest.Data.core282
kernel_rfl tcl_270 : Same.closed[270]? = some ("column_selector__L10", 286, 283)
kernel_rfl tdg_283 : Guest.coreProgram[283]? = some LeanVM.Guest.Data.core283
kernel_rfl tcl_271 : Same.closed[271]? = some ("column_selector__L11", 287, 284)
kernel_rfl tdg_284 : Guest.coreProgram[284]? = some LeanVM.Guest.Data.core284
kernel_rfl tcl_272 : Same.closed[272]? = some ("column_selector__L12", 288, 285)
kernel_rfl tdg_285 : Guest.coreProgram[285]? = some LeanVM.Guest.Data.core285
kernel_rfl tcl_273 : Same.closed[273]? = some ("column_selector__L13", 289, 286)
kernel_rfl tdg_286 : Guest.coreProgram[286]? = some LeanVM.Guest.Data.core286
kernel_rfl tcl_274 : Same.closed[274]? = some ("column_selector__L14", 290, 287)
kernel_rfl tdg_287 : Guest.coreProgram[287]? = some LeanVM.Guest.Data.core287
kernel_rfl tcl_275 : Same.closed[275]? = some ("column_selector__L15", 291, 288)
kernel_rfl tdg_288 : Guest.coreProgram[288]? = some LeanVM.Guest.Data.core288
kernel_rfl tcl_276 : Same.closed[276]? = some ("column_selector__L16", 292, 289)
kernel_rfl tdg_289 : Guest.coreProgram[289]? = some LeanVM.Guest.Data.core289
kernel_rfl tcl_277 : Same.closed[277]? = some ("column_selector__L17", 293, 290)
kernel_rfl tdg_290 : Guest.coreProgram[290]? = some LeanVM.Guest.Data.core290
kernel_rfl tcl_278 : Same.closed[278]? = some ("column_selector__L18", 294, 291)
kernel_rfl tdg_291 : Guest.coreProgram[291]? = some LeanVM.Guest.Data.core291
kernel_rfl tcl_279 : Same.closed[279]? = some ("column_selector__L19", 295, 292)
kernel_rfl tdg_292 : Guest.coreProgram[292]? = some LeanVM.Guest.Data.core292
kernel_rfl tcl_280 : Same.closed[280]? = some ("column_selector__L20", 296, 293)
kernel_rfl tdg_293 : Guest.coreProgram[293]? = some LeanVM.Guest.Data.core293
kernel_rfl tcl_281 : Same.closed[281]? = some ("column_selector__L21", 297, 294)
kernel_rfl tdg_294 : Guest.coreProgram[294]? = some LeanVM.Guest.Data.core294
kernel_rfl tcl_282 : Same.closed[282]? = some ("column_selector__L22", 298, 295)
kernel_rfl tdg_295 : Guest.coreProgram[295]? = some LeanVM.Guest.Data.core295
kernel_rfl tcl_283 : Same.closed[283]? = some ("column_selector__L23", 299, 296)
kernel_rfl tdg_296 : Guest.coreProgram[296]? = some LeanVM.Guest.Data.core296
kernel_rfl tcl_284 : Same.closed[284]? = some ("column_selector__L24", 300, 297)
kernel_rfl tdg_297 : Guest.coreProgram[297]? = some LeanVM.Guest.Data.core297
kernel_rfl tcl_285 : Same.closed[285]? = some ("column_selector__L25", 301, 298)
kernel_rfl tdg_298 : Guest.coreProgram[298]? = some LeanVM.Guest.Data.core298
kernel_rfl tcl_286 : Same.closed[286]? = some ("column_selector__L26", 302, 299)
kernel_rfl tdg_299 : Guest.coreProgram[299]? = some LeanVM.Guest.Data.core299
kernel_rfl tcl_287 : Same.closed[287]? = some ("column_selector__L27", 303, 300)
kernel_rfl tdg_300 : Guest.coreProgram[300]? = some LeanVM.Guest.Data.core300
kernel_rfl tcl_288 : Same.closed[288]? = some ("column_selector__L28", 304, 301)
kernel_rfl tdg_301 : Guest.coreProgram[301]? = some LeanVM.Guest.Data.core301
kernel_rfl tcl_289 : Same.closed[289]? = some ("column_selector__L29", 305, 302)
kernel_rfl tdg_302 : Guest.coreProgram[302]? = some LeanVM.Guest.Data.core302
kernel_rfl tcl_290 : Same.closed[290]? = some ("column_selector__L30", 306, 303)
kernel_rfl tdg_303 : Guest.coreProgram[303]? = some LeanVM.Guest.Data.core303

/-- The selectors' specializations are in the closed set and kept by the renaming. -/
theorem colSel_same : ∀ κ < 31, Same.inS (Tables.lName "column_selector" κ) = true ∧
    Same.rho (Tables.lName "column_selector" κ) = Tables.lName "column_selector" κ := by
  intro κ hκ
  interval_cases κ
  · rw [show Tables.lName "column_selector" 0 = "column_selector__L0" by decide +kernel]
    exact Whir.sameOf tcl_260 tdg_273 rfl
  · rw [show Tables.lName "column_selector" 1 = "column_selector__L1" by decide +kernel]
    exact Whir.sameOf tcl_261 tdg_274 rfl
  · rw [show Tables.lName "column_selector" 2 = "column_selector__L2" by decide +kernel]
    exact Whir.sameOf tcl_262 tdg_275 rfl
  · rw [show Tables.lName "column_selector" 3 = "column_selector__L3" by decide +kernel]
    exact Whir.sameOf tcl_263 tdg_276 rfl
  · rw [show Tables.lName "column_selector" 4 = "column_selector__L4" by decide +kernel]
    exact Whir.sameOf tcl_264 tdg_277 rfl
  · rw [show Tables.lName "column_selector" 5 = "column_selector__L5" by decide +kernel]
    exact Whir.sameOf tcl_265 tdg_278 rfl
  · rw [show Tables.lName "column_selector" 6 = "column_selector__L6" by decide +kernel]
    exact Whir.sameOf tcl_266 tdg_279 rfl
  · rw [show Tables.lName "column_selector" 7 = "column_selector__L7" by decide +kernel]
    exact Whir.sameOf tcl_267 tdg_280 rfl
  · rw [show Tables.lName "column_selector" 8 = "column_selector__L8" by decide +kernel]
    exact Whir.sameOf tcl_268 tdg_281 rfl
  · rw [show Tables.lName "column_selector" 9 = "column_selector__L9" by decide +kernel]
    exact Whir.sameOf tcl_269 tdg_282 rfl
  · rw [show Tables.lName "column_selector" 10 = "column_selector__L10" by decide +kernel]
    exact Whir.sameOf tcl_270 tdg_283 rfl
  · rw [show Tables.lName "column_selector" 11 = "column_selector__L11" by decide +kernel]
    exact Whir.sameOf tcl_271 tdg_284 rfl
  · rw [show Tables.lName "column_selector" 12 = "column_selector__L12" by decide +kernel]
    exact Whir.sameOf tcl_272 tdg_285 rfl
  · rw [show Tables.lName "column_selector" 13 = "column_selector__L13" by decide +kernel]
    exact Whir.sameOf tcl_273 tdg_286 rfl
  · rw [show Tables.lName "column_selector" 14 = "column_selector__L14" by decide +kernel]
    exact Whir.sameOf tcl_274 tdg_287 rfl
  · rw [show Tables.lName "column_selector" 15 = "column_selector__L15" by decide +kernel]
    exact Whir.sameOf tcl_275 tdg_288 rfl
  · rw [show Tables.lName "column_selector" 16 = "column_selector__L16" by decide +kernel]
    exact Whir.sameOf tcl_276 tdg_289 rfl
  · rw [show Tables.lName "column_selector" 17 = "column_selector__L17" by decide +kernel]
    exact Whir.sameOf tcl_277 tdg_290 rfl
  · rw [show Tables.lName "column_selector" 18 = "column_selector__L18" by decide +kernel]
    exact Whir.sameOf tcl_278 tdg_291 rfl
  · rw [show Tables.lName "column_selector" 19 = "column_selector__L19" by decide +kernel]
    exact Whir.sameOf tcl_279 tdg_292 rfl
  · rw [show Tables.lName "column_selector" 20 = "column_selector__L20" by decide +kernel]
    exact Whir.sameOf tcl_280 tdg_293 rfl
  · rw [show Tables.lName "column_selector" 21 = "column_selector__L21" by decide +kernel]
    exact Whir.sameOf tcl_281 tdg_294 rfl
  · rw [show Tables.lName "column_selector" 22 = "column_selector__L22" by decide +kernel]
    exact Whir.sameOf tcl_282 tdg_295 rfl
  · rw [show Tables.lName "column_selector" 23 = "column_selector__L23" by decide +kernel]
    exact Whir.sameOf tcl_283 tdg_296 rfl
  · rw [show Tables.lName "column_selector" 24 = "column_selector__L24" by decide +kernel]
    exact Whir.sameOf tcl_284 tdg_297 rfl
  · rw [show Tables.lName "column_selector" 25 = "column_selector__L25" by decide +kernel]
    exact Whir.sameOf tcl_285 tdg_298 rfl
  · rw [show Tables.lName "column_selector" 26 = "column_selector__L26" by decide +kernel]
    exact Whir.sameOf tcl_286 tdg_299 rfl
  · rw [show Tables.lName "column_selector" 27 = "column_selector__L27" by decide +kernel]
    exact Whir.sameOf tcl_287 tdg_300 rfl
  · rw [show Tables.lName "column_selector" 28 = "column_selector__L28" by decide +kernel]
    exact Whir.sameOf tcl_288 tdg_301 rfl
  · rw [show Tables.lName "column_selector" 29 = "column_selector__L29" by decide +kernel]
    exact Whir.sameOf tcl_289 tdg_302 rfl
  · rw [show Tables.lName "column_selector" 30 = "column_selector__L30" by decide +kernel]
    exact Whir.sameOf tcl_290 tdg_303 rfl

end

end LeanVM.SaltedGuest.B1.Terminal
