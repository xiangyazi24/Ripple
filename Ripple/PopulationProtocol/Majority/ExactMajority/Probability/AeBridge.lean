import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.Probability.Kernel.Basic

namespace ExactMajority

open MeasureTheory ProbabilityTheory

/-- 
  If the bad set (where the property fails) is a subset of `{c | φ c > 0}`, 
  then its measure is bounded by the measure of `{c | φ c > 0}`.
  (This is a direct application of `MeasureTheory.measure_mono`).
-/
theorem measure_le_of_subset {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    (bad : Set Ω) (phi_pos : Set Ω) (h_sub : bad ⊆ phi_pos) :
    μ bad ≤ μ phi_pos := by
  exact measure_mono h_sub

-- ae_of_measure_compl_le DELETED (2026-05-23 brainstorm).
-- It was mathematically false: Doty's bounds give μ{¬P} ≤ 1/n² (not = 0),
-- so ∀ᵐ (which requires μ{¬P} = 0) is unprovable.
-- All probability theorems now use measure ≤ form directly.

end ExactMajority
