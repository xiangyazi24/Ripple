import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.SignMatch
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.BackupEntry
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.ReachableLadder
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.Phase2Convergence
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.EliminatorMargins

namespace ExactMajority
namespace SmallSweepProbe
variable {L K : ℕ}
open Phase10Drop

-- Atom 2 probe: concrete union algebra by decide
example : Phase2Convergence.singleSign (4 : Fin 8) := by decide
example : Phase2Convergence.singleSign (0 : Fin 8) := by decide
example : opinionsUnion (0 : Fin 8) (4 : Fin 8) = (4 : Fin 8) := by decide
example : opinionsUnion (4 : Fin 8) (0 : Fin 8) = (4 : Fin 8) := by decide
example : opinionsUnion (0 : Fin 8) (0 : Fin 8) = (0 : Fin 8) := by decide
example : opinionsUnion (4 : Fin 8) (4 : Fin 8) = (4 : Fin 8) := by decide
example : (4 : Fin 8) ≠ (0 : Fin 8) := by decide

-- Atom 4 probe: activity propagation along Reachable
example (init c : Config (AgentState L K))
    (hreach : (NonuniformMajority L K).Reachable init c)
    (hAllinit : ∀ a ∈ init, a.phase.val = 10)
    (hactinit : hasActiveAgent init) :
    hasActiveAgent c ∧ (∀ a ∈ c, a.phase.val = 10) := by
  induction hreach with
  | refl => exact ⟨hactinit, hAllinit⟩
  | tail hstep_rt hstep ih =>
      exact ⟨phase10_hasActiveAgent_preserved_by_step _ _ ih.2 ih.1 hstep,
        phase10_phase_preserved_by_step _ _ ih.2 hstep⟩

-- Atom 1 probe: extremeU counts BOTH ends; +3 witness present → extremeU > 0
example (c : Config (AgentState L K))
    (h : 1 ≤ (DrainThreading.extremePosSet L K).sum c.count) :
    1 ≤ Phase1Convergence.extremeU c := by
  sorry

end SmallSweepProbe
end ExactMajority
