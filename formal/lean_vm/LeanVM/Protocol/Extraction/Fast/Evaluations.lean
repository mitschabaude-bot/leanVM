module

public import LeanVM.Protocol.Extraction.Fast.Compiled

/-!
# The extractor on a list of evaluations

`extractorTop` (`Fast/Compiled.lean`) reads the hash through the permutation queries of a
transcript: it replays them into the transcript's evaluations of at most `512` bytes
(`transcriptIndex`), then indexes their preimages. `extractorEvaluations` is the same extractor
entered after that replay: its input is a list of evaluations `(x, H(x))`, indexed the same way
(`evaluationsIndex`: their first answers, then the preimage index). Every other step is
`extractorTop`'s (`afterRootLite`, `subtreeLeavesWith`, `runFromLeaves`), so the cost compiler
reuses their compiled bodies (`Cost/Extractor/Evaluations.lean`).

* `shortEvaluations answers keys`: the answered keys of at most `512` bytes with their answers, the
  evaluations `Extraction.extract answers keys` reads (a committed node is `64` bytes and a leaf
  `8·64`: the stack's root has leaves of `64` words);
* `extractorEvaluations_eq_full`: `extractorEvaluations` written in one `do` block on the full
  layout, as `extractorTopFull` is `extractorTop`.
-/

namespace LeanVM.Extraction.Fast

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Compile
open LeanVM.Protocol.Verifier LeanVM.Protocol.KeccakHash LeanVM.Extraction LeanVM

public section

attribute [local instance] lexOrd

/-- **The preimage index of a list of evaluations**: their first answers, then the index, as
`transcriptIndex` indexes the transcript's evaluations. -/
@[expose] def evaluationsIndex (P : List (Bytes × Digest)) : SortedMap (List UInt64 × ℕ) Hits :=
  preimageIndex (answerPairs (firstAnswers P).get? (P.map (·.1)))

/-- The committed leaves from a list of evaluations: the index, then the subtree under the
root. -/
@[expose] def leavesOfEvaluations (P : List (Bytes × Digest)) (w h : ℕ) (root : Digest) :
    Array (List K) :=
  subtreeLeavesWith (preimageIn (evaluationsIndex P)) w h root

/-- The runs at a root `t = (root, height, width)`, from a list of evaluations. -/
@[expose] def stageE (prog : LeanIsaProgram) (input : PublicInput) (layout : LayoutLite) (R : ℕ)
    (P : List (Bytes × Digest)) (t : Digest × ℕ × ℕ) : Option (Execution prog) :=
  runFromLeaves prog input layout R (leavesOfEvaluations P t.2.2 t.2.1 t.1) t.2.1 t.2.2

/-- After the replay: the first root, then `stageE` at it. -/
@[expose] def afterRootStageE (prog : LeanIsaProgram) (input : PublicInput)
    (P : List (Bytes × Digest)) (r : (LayoutLite × ℕ) × VerifierProgramState) :
    Option (Execution prog) :=
  r.2.roots.head?.bind (stageE prog input r.1.1 r.1.2 P)

/-- **The extractor on a list of evaluations**: `extractorTop` with the preimages read off the
evaluations `P` instead of the transcript's. -/
@[expose] def extractorEvaluations (prog : LeanIsaProgram) (input : PublicInput)
    (P : List (Bytes × Digest)) (π : Proof) : Option (Execution prog) :=
  (afterRootLite (bytecodeWords prog) π).bind (afterRootStageE prog input P)

/-- **The evaluations `extract answers keys` reads**: the answered keys of at most `512` bytes
with their answers. -/
@[expose] def shortEvaluations (answers : Bytes → Option Digest) (keys : List Bytes) :
    List (Bytes × Digest) :=
  answerPairs answers (keys.filter fun x ↦ decide (x.length ≤ 512))

/-- `extractorEvaluations` on the full layout, in one `do` block. -/
@[expose] def extractorEvaluationsFull (prog : LeanIsaProgram) (input : PublicInput)
    (P : List (Bytes × Digest)) (π : Proof) : Option (Execution prog) := do
  let ((layout, logInverseRate), state) ← afterRootDirect (bytecodeWords prog) π
  let (root, height, width) ← state.roots.head?
  let leaves := subtreeLeavesWith (preimageIn (evaluationsIndex P)) width height root
  let word := leafAt leaves height width
  let execution := candidateRunner prog input (layoutLite layout)
  (fastStacksFast layout.stackLog logInverseRate word).findSome? execution <|>
    (decodeStacksFast layout.stackLog logInverseRate word).findSome? execution

theorem extractorEvaluations_eq_full (prog : LeanIsaProgram) (input : PublicInput)
    (P : List (Bytes × Digest)) (π : Proof) :
    extractorEvaluations prog input P π = extractorEvaluationsFull prog input P π := by
  unfold extractorEvaluations extractorEvaluationsFull afterRootStageE stageE runFromLeaves
    leavesOfEvaluations runBoth fastOf decOf
  simp only [Option.bind_eq_bind]
  rw [afterRootLite_eq, ← afterRootDirect_eq, Option.bind_map]
  refine Option.bind_congr fun r h ↦ ?_
  obtain ⟨⟨layout, R⟩, st⟩ := r
  have hadm : Whir.Admissible layout.stackLog R := admissible_of_afterRootDirect h
  simp only [Function.comp_apply, liteResult]
  simp only [layoutLite_stackLog, decodeStacksDistinctPM_eq_fast hadm, runWithTables_runnerTables]

/-- `extractorEvaluationsFull` is `extractWith` with the evaluations' index. -/
theorem extractorEvaluationsFull_eq_extractWith (prog : LeanIsaProgram) (input : PublicInput)
    (P : List (Bytes × Digest)) (π : Proof) :
    extractorEvaluationsFull prog input P π =
      extractWith prog input (bytecodeWords prog) (fun _ ↦ evaluationsIndex P) preimageIn π := by
  rw [extractorEvaluationsFull, extractWith, afterRootDirect_eq_afterRoot]
  simp only [candidateRunner_eq, fastStacksFast_eq]
  rfl

end

end LeanVM.Extraction.Fast
