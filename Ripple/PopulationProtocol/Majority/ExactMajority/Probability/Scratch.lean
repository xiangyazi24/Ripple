import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.PhaseConvergence
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.Supermartingale
import Ripple.PopulationProtocol.Majority.PopProtoCommon.Convergence.GeometricDrift

namespace ExactMajority
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]
variable (P : Protocol Λ) (c : Config Λ)
variable (Post : Config Λ → Prop)

lemma test_compl [IsMarkovKernel P.transitionKernel] (h1 : P.transitionKernel c {y | Post y} = 1) :
    P.transitionKernel c {y | ¬Post y} = 0 := by
  calc P.transitionKernel c {y | ¬Post y}
      = P.transitionKernel c Set.univ - P.transitionKernel c {y | Post y} := by
        have h_meas : MeasurableSet {y | Post y} := DiscreteMeasurableSpace.forall_measurableSet _
        have h_ne_top : P.transitionKernel c {y | Post y} ≠ ∞ := by
          rw [h1]; exact ENNReal.one_ne_top
        have heq : {y | ¬Post y} = {y | Post y}ᶜ := rfl
        rw [heq, measure_compl h_meas h_ne_top]
    _ = 1 - 1 := by rw [h1, measure_univ]
    _ = 0 := by simp

end ExactMajority
