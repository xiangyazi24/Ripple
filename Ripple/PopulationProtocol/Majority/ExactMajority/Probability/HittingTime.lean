/-
# Hitting Time for Traces

Generic first hitting time of a target predicate under a discrete trace.
-/

import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.MarkovChain

open scoped ENNReal

namespace ExactMajority

/-- The first hitting time of `Goal` under `trace`.
Returns `⊤` if the goal is never reached. -/
noncomputable def hittingTime {α : Type*}
    (trace : ℕ → α) (Goal : α → Prop) : ENNReal :=
  ⨅ t ∈ {t : ℕ | Goal (trace t)}, (t : ENNReal)

end ExactMajority
