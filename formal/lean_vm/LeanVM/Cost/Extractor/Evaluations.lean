module

public import LeanVM.Cost.Extractor.Top
public import LeanVM.Protocol.Extraction.Fast.Evaluations
import all LeanVM.Protocol.Extraction.Fast.Evaluations
import all LeanVM.Protocol.Extraction.Fast.Compiled
import all LeanVM.Protocol.Extraction.Extractor
import all Statement.LeanIsa

/-!
# The extractor on a list of evaluations, compiled

`extractorEvaluations` (`Fast/Evaluations.lean`), compiled on top of the compiled extractor
(`Cost/Extractor/Top.lean`), whose functions it reuses: the replay (`afterRootLite`), the committed
leaves' subtree (`subtreeLeavesWith`), the first answers and the preimage index, the candidate
runs (`runFromLeavesC`). Compiled here: the evaluations' index (`evaluationsIndexC`), the leaves
(`leavesOfEvaluationsC`), the stage (`stageEC`, `afterRootStageEC`) and the top body
(`extractorEvaluationsC`).
-/

namespace LeanVM.Cost.Extractor

open LeanVM.Cost LeanVM.Parameters LeanVM.Extraction LeanVM.Extraction.Fast LeanVM.Cost.FastLib

public section

attribute [local instance] lexOrd

cost_compile evaluationsIndexC := evaluationsIndex
cost_compile leavesOfEvaluationsC := leavesOfEvaluations
cost_compile stageEC := stageE
cost_compile afterRootStageEC := afterRootStageE
cost_compile extractorEvaluationsC := extractorEvaluations

end

end LeanVM.Cost.Extractor
