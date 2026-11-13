module

public import LeanVM.Cost.ExtractorProgram
public import LeanVM.Cost.Extractor.Evaluations

/-!
# The program of the extractor on a list of evaluations

`compiledEvaluationsExtractor`: function `0` is the entry `entryBody j` (`Cost/ExtractorProgram.lean`),
which destructures the input `encodeEvaluationsExtractorInput prog input Ev proof` (a constructor of
four fields), calls function `j = extractorEvaluationsC.costIdx` (the compiled
`extractorEvaluations`, `Cost/Extractor/Evaluations.lean`) on them and unwraps its optional output;
the other functions are the bodies the compiled extractor on evaluations needs
(`extractorEvaluationsC.costDeps`, sorted by index, all past `0`). Its size is evaluated in
`Cost/EvaluationsSize.lean`.
-/

namespace LeanVM.Cost

open LeanVM.Cost.Extractor LeanVM.Protocol.Compile

public section

/-- **The input of the extractor on evaluations**: the program, the public input, the evaluations
and the proof. -/
@[expose] def encodeEvaluationsExtractorInput (prog : Semantics.LeanIsaProgram)
    (input : Semantics.PublicInput) (Ev : List (Bytes × LeanVM.Protocol.Digest)) (proof : Proof) :
    MachineValue :=
  .constructor 0 [encodeValue prog, encodeValue input, encodeValue Ev, encodeValue proof]

/-- The program's bodies: the entry at `0`, then the compiled extractor's on evaluations. -/
@[expose] def evaluationsProgramBodies : List (ℕ × Term) :=
  (0, entryBody extractorEvaluationsC.costIdx) :: extractorEvaluationsC.costDeps

theorem evaluationsProgramBodies_eq :
    evaluationsProgramBodies =
      (0, entryBody extractorEvaluationsC.costIdx) :: extractorEvaluationsC.costDeps := by
  unfold evaluationsProgramBodies; rfl

/-- **The program of the extractor on evaluations.** -/
@[expose] def compiledEvaluationsExtractor : MachineProgram :=
  MachineProgram.ofList evaluationsProgramBodies

end

end LeanVM.Cost
