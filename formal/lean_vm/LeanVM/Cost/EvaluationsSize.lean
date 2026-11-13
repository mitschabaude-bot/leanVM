module

public import LeanVM.Cost.EvaluationsProgram

/-!
# The program of the extractor on evaluations: its indices and its size, by evaluation

A firewall (`AGENTS.md`), as `Cost/ExtractorSize.lean` is for the extractor's program: the kernel
evaluations over `compiledEvaluationsExtractor`, in a module of their own that imports only the
program's definition.

* `evaluationsProgram_indices_increasing`: the bodies' indices are distinct;
* **`evaluationsProgram_size_le_measured`**: the program's size is at most `13721`, its exact size:
  the bodies' sizes (`13603`: `661` compiled bodies and the entry) and `59` indices without a body,
  a literal `0` of size `2` each, `721` indices in all.
-/

namespace LeanVM.Cost

open LeanVM.Cost.Extractor

public section

/-- The bodies' indices increase: the entry's `0`, then the compiled extractor's on evaluations. -/
theorem evaluationsProgram_indices_increasing :
    increasingFrom 0 (extractorEvaluationsC.costDeps.map (·.1)) = true := by
  decide +kernel

/-- **The program's size**, from its bodies, each count evaluated: exactly `13721`. -/
theorem evaluationsProgram_size_le_measured : compiledEvaluationsExtractor.size ≤ 13721 := by
  have h := size_ofList_add_length evaluationsProgramBodies (by
    rw [evaluationsProgramBodies, List.map_cons]
    exact nodup_of_increasing evaluationsProgram_indices_increasing)
  have h1 : (evaluationsProgramBodies.map fun p ↦ p.2.size).sum = 13603 := by decide +kernel
  have h2 : (evaluationsProgramBodies.map (·.1)).foldr max 0 = 720 := by decide +kernel
  have h3 : evaluationsProgramBodies.length = 662 := by decide +kernel
  unfold compiledEvaluationsExtractor
  omega

end

end LeanVM.Cost
