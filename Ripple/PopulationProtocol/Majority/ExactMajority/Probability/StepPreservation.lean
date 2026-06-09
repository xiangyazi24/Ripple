import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.MarkovChain

namespace ExactMajority

open MeasureTheory ProbabilityTheory

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]

/-- If Q is preserved by stepDistOrSelf and holds at c₀, then Q holds a.e.
This is just ae_of_stepDistOrSelf_support_preserved re-exported. -/
theorem ae_of_pointwise_preserved
    (P : Protocol Λ) (Q : Config Λ → Prop)
    (hStep : ∀ c c', c' ∈ (P.stepDistOrSelf c).support → Q c → Q c')
    (c₀ : Config Λ) (h₀ : Q c₀) (t : ℕ) :
    ∀ᵐ c ∂((P.transitionKernel ^ t) c₀), Q c :=
  ae_of_stepDistOrSelf_support_preserved P Q hStep c₀ h₀ t

/-- Multiset membership after a step: any agent in
`c - {r₁, r₂} + {out₁, out₂}` is either from `c` or is an output. -/
theorem mem_step_config {c : Multiset Λ} {r₁ r₂ out₁ out₂ : Λ}
    {a : Λ} (ha : a ∈ c - {r₁, r₂} + {out₁, out₂}) :
    a ∈ c ∨ a = out₁ ∨ a = out₂ := by
  rw [Multiset.mem_add] at ha
  rcases ha with ha_res | ha_out
  · left; exact Multiset.mem_of_le (Multiset.tsub_le_self) ha_res
  · right
    simp only [Multiset.insert_eq_cons, Multiset.mem_cons,
      Multiset.mem_singleton] at ha_out
    exact ha_out

end ExactMajority
