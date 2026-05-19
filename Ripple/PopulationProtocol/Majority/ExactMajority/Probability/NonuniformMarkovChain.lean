/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Markov Chain for the Nonuniform Exact Majority Protocol

This file specializes the generic scheduler/kernel infrastructure to the
Doty et al. nonuniform exact-majority protocol `NonuniformMajority L K`.
-/

import Ripple.PopulationProtocol.Majority.ExactMajority.Protocol.Transition
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.MarkovChain

namespace ExactMajority

variable (L K : ℕ)

/-- One-step distribution for the concrete nonuniform majority protocol, with a
point-mass fallback on populations of size less than two. -/
noncomputable def nonuniformStepDistOrSelf (c : Config (AgentState L K)) :
    PMF (Config (AgentState L K)) :=
  (NonuniformMajority L K).stepDistOrSelf c

/-- Markov transition kernel for the concrete nonuniform majority protocol. -/
noncomputable def nonuniformTransitionKernel :
    ProbabilityTheory.Kernel (Config (AgentState L K)) (Config (AgentState L K)) :=
  (NonuniformMajority L K).transitionKernel

/-- Every support point of the concrete one-step distribution is reachable by
the nonuniform majority protocol. -/
theorem nonuniformStepDistOrSelf_support_reachable
    (c c' : Config (AgentState L K)) :
    c' ∈ (nonuniformStepDistOrSelf L K c).support →
      (NonuniformMajority L K).Reachable c c' := by
  exact Protocol.stepDistOrSelf_support_reachable (NonuniformMajority L K) c c'

/-- Every support point of the concrete one-step distribution preserves
population size. -/
theorem nonuniformStepDistOrSelf_support_card_eq
    (c c' : Config (AgentState L K)) :
    c' ∈ (nonuniformStepDistOrSelf L K c).support → c'.card = c.card := by
  exact Protocol.stepDistOrSelf_support_card_eq (NonuniformMajority L K) c c'

end ExactMajority
