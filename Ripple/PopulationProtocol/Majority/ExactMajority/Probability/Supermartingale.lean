/-
Supermartingale convergence-time bound (Theorem 4.2 of Doty et al.).

Generic tool: if X₀, X₁, ... is a nonneg supermartingale with X₀ = x₀ and
multiplicative drift E[X_{t+1} | X_t] ≤ (1−γ) X_t, then the hitting time to
some threshold has exponential tail. Used throughout the paper to bound phase
durations.

This file re-exports `PopProtoCommon`'s `lintegral_geometric_decay`, which
proves the kernel-level multiplicative-decay bound and is independent of any
specific population protocol. We expose it under the `ExactMajority`
namespace for convenience here, and prove the kernel-version Markov tail
bound below.

Reference: Doty et al., Theorem 4.2; PopProtoCommon/Convergence/GeometricDrift.lean
(originally extracted from PP-Proof).
-/

import Mathlib.Probability.Martingale.Basic
import Mathlib.Probability.Kernel.Defs
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Ripple.PopulationProtocol.Majority.PopProtoCommon.Convergence.GeometricDrift

open scoped ENNReal
open MeasureTheory ProbabilityTheory

namespace ExactMajority

/-- Re-export of `PopProtoCommon`'s kernel multiplicative-decay theorem.

If `K : Kernel α α` is a Markov kernel, `Φ : α → ℝ≥0∞` is measurable, and the
one-step expectation satisfies `∫⁻ Φ dK(x) ≤ r·Φ(x)` for all `x`, then the
`t`-step expectation satisfies `∫⁻ Φ d(K^t)(x) ≤ r^t · Φ(x)`.

This is the analytic engine behind any "multiplicative drift" / geometric
supermartingale bound, and is reusable across population-protocol proofs. -/
abbrev lintegral_geometric_decay := @PopProtoCommon.lintegral_geometric_decay

/-- Re-export of `PopProtoCommon`'s `measure_potential_ge_one` (Markov
inequality specialization for the geometric-decay regime). -/
abbrev measure_potential_ge_one := @PopProtoCommon.measure_potential_ge_one

/-- **Geometric-drift tail bound** (Theorem 4.2, kernel version).

If a Markov kernel `K` satisfies the multiplicative drift condition
`∫⁻ Φ dK(x) ≤ r · Φ(x)` for all `x`, then for any threshold `θ`,
`θ · (K ^ t) x {y | θ ≤ Φ y} ≤ r ^ t · Φ(x)`.

This is a direct consequence of Markov's inequality (`mul_meas_ge_le_lintegral₀`)
followed by the geometric-decay lemma (`lintegral_geometric_decay`).

TODO (DeepSeek): derive the real-valued hitting-time corollary
  `P[X_t ≥ θ] ≤ x₀ · (1-γ)^t / θ`
from this kernel version once the probability-space wrapper is written. -/
theorem geometric_drift_tail_kernel {α : Type*} [MeasurableSpace α]
    (K : Kernel α α) [IsMarkovKernel K]
    (Φ : α → ℝ≥0∞) (hΦ : Measurable Φ)
    (r : ℝ≥0∞)
    (hdrift : ∀ x, ∫⁻ y, Φ y ∂(K x) ≤ r * Φ x)
    (t : ℕ) (x : α) (θ : ℝ≥0∞) :
    θ * (K ^ t) x {y | θ ≤ Φ y} ≤ r ^ t * Φ x := by
  calc
    θ * (K ^ t) x {y | θ ≤ Φ y} ≤ ∫⁻ y, Φ y ∂((K ^ t) x) :=
      mul_meas_ge_le_lintegral₀ (hf := hΦ.aemeasurable) (ε := θ)
    _ ≤ r ^ t * Φ x := lintegral_geometric_decay K Φ hΦ r hdrift t x

/-- **Geometric-drift tail bound, division form** (Theorem 4.2 corollary).

Under the same drift condition as `geometric_drift_tail_kernel`, for a finite
non-zero threshold `θ` (i.e., `θ ≠ 0` and `θ ≠ ∞`), the measure of the
super-level set `{θ ≤ Φ}` after `t` steps is bounded by `r^t · Φ(x) / θ`.

This follows immediately from the multiplicative form by dividing both sides
by `θ` (using `ENNReal.inv_mul_cancel` when `θ` is finite and non-zero). -/
theorem geometric_drift_tail {α : Type*} [MeasurableSpace α]
    (K : Kernel α α) [IsMarkovKernel K]
    (Φ : α → ℝ≥0∞) (hΦ : Measurable Φ)
    (r : ℝ≥0∞)
    (hdrift : ∀ x, ∫⁻ y, Φ y ∂(K x) ≤ r * Φ x)
    (t : ℕ) (x : α) (θ : ℝ≥0∞) (hθ0 : θ ≠ 0) (hθ_top : θ ≠ ∞) :
    (K ^ t) x {y | θ ≤ Φ y} ≤ r ^ t * Φ x / θ := by
  have h := geometric_drift_tail_kernel K Φ hΦ r hdrift t x θ
  -- h: θ * μ ≤ r^t * Φ x  where μ = (K^t) x {θ ≤ Φ}
  calc
    (K ^ t) x {y | θ ≤ Φ y} = (θ⁻¹ * θ) * (K ^ t) x {y | θ ≤ Φ y} := by
      simp [ENNReal.inv_mul_cancel hθ0 hθ_top]
    _ = θ⁻¹ * (θ * (K ^ t) x {y | θ ≤ Φ y}) := by
      simp [mul_assoc]
    _ ≤ θ⁻¹ * (r ^ t * Φ x) := by gcongr
    _ = r ^ t * Φ x * θ⁻¹ := by
      simp [mul_comm, mul_assoc, mul_left_comm]
    _ = r ^ t * Φ x / θ := rfl

end ExactMajority
