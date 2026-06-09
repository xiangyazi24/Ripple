/-
# Descent Potential for Population Protocol Markov Chains

A deterministic descent argument: if a potential φ never increases and
some support point always decreases it, the potential eventually reaches 0.

The key observation: any property Q that (1) holds at C₀, (2) is preserved
by every support point, and (3) implies Goal when φ = 0, can be used with
`ae_of_stepDistOrSelf_support_preserved` to get Goal a.e.

The trick: define Q c = "Goal c ∨ (Inv c ∧ φ c ≤ k)" for decreasing k.
Q₀ holds (Inv C₀ with φ ≤ φ C₀). Q is preserved (Goal absorbs, Inv+φ≤k
is preserved by nonincrease). At k=0, Q gives Goal.
-/

import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.MarkovChain

namespace ExactMajority

open MeasureTheory ProbabilityTheory

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]

/-- If Goal is absorbing and "Goal ∨ Inv" is preserved, then
"Goal ∨ Inv" holds a.e. for all t. This is the stepping stone. -/
theorem ae_goal_or_inv_of_absorbing_preserved
    (P : Protocol Λ)
    (C₀ : Config Λ)
    (Goal : Config Λ → Prop)
    (Inv : Config Λ → Prop)
    (hInit : Goal C₀ ∨ Inv C₀)
    (hStep : ∀ C, (Goal C ∨ Inv C) →
      ∀ c' ∈ (P.stepDistOrSelf C).support, Goal c' ∨ Inv c')
    (t : ℕ) :
    ∀ᵐ c ∂((P.transitionKernel ^ t) C₀), Goal c ∨ Inv c :=
  ae_of_stepDistOrSelf_support_preserved P
    (fun c => Goal c ∨ Inv c) hStep C₀ hInit t

end ExactMajority
