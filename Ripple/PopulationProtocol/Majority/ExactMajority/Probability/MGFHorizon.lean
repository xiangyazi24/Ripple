import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.EarlyDripBound
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.Supermartingale

/-!
# MGFHorizon — the early-drip MGF tail (engine for Doty Lemma 6.3)

Composing the proven one-step MGF contraction `EarlyDrip.earlyDrip_mgf_one_step`
(`∫ exp(s·N') dK(c) ≤ (1+q(e^s−1))·exp(s·N c)`) with the generic geometric-drift horizon tail
`geometric_drift_tail` gives the early-drip count tail:

  `(K^t) c₀ {c | a ≤ earlyDripCount T c} ≤ (1+q(e^s−1))^t · exp(s·earlyDripCount T c₀) / exp(s·a)`,

for any `s > 0`, GIVEN the per-step increment probability is `≤ q` at every config (the explicit `hrate`
hypothesis — the UNGATED engine).  The next brick (the genuine §6 coupling) discharges `hrate` via the
bulk-arrival gate: the early-drip rate `q ≈ (feeder/n)²` is small only while the bulk has not arrived at the
level, so `hrate` holds on a gate, and the gated horizon (killed/stopped walk) is what makes this
unconditional.  This lemma isolates the clean, true, reusable MGF→tail engine.
-/

namespace ExactMajority

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Real BigOperators

namespace EarlyDrip

open ClockTime

variable {L₀ : ℕ}

/-- **The early-drip MGF tail** (ungated engine).  For `s > 0`, `q ≥ 0`, and the per-step increment
probability of the early-drip count `≤ q` at every config (`hrate`), the `t`-step probability that the
early-drip count at level `T` reaches `a` is at most `(1+q(e^s−1))^t · exp(s·N₀) / exp(s·a)`
(`N₀ = earlyDripCount T c₀`).  GENUINE: `earlyDrip_mgf_one_step` (one-step factor) fed into
`geometric_drift_tail` (horizon), with the exp super-level set identified with the count super-level set
(`s > 0`). -/
theorem earlyDrip_mgf_tail (s : ℝ) (hs : 0 < s) (T : ℕ) (q : ℝ) (hq0 : 0 ≤ q)
    (hrate : ∀ c : Config (Minute L₀),
      (clockProto L₀).transitionKernel c
        {c' | earlyDripCount T c < earlyDripCount T c'} ≤ ENNReal.ofReal q)
    (t : ℕ) (c₀ : Config (Minute L₀)) (a : ℕ) :
    (((clockProto L₀).transitionKernel) ^ t) c₀ {c | a ≤ earlyDripCount T c} ≤
      ENNReal.ofReal ((1 + q * (Real.exp s - 1)) ^ t
        * expCount s (earlyDripCount T) c₀ / Real.exp (s * (a : ℝ))) := by
  classical
  set K := (clockProto L₀).transitionKernel with hK
  set N : Config (Minute L₀) → ℕ := earlyDripCount T with hN
  set Φ : Config (Minute L₀) → ℝ≥0∞ := fun c => ENNReal.ofReal (expCount s N c) with hΦdef
  have hΦ_meas : Measurable Φ := Measurable.of_discrete
  set r : ℝ≥0∞ := ENNReal.ofReal (1 + q * (Real.exp s - 1)) with hr
  have hexp1 : (0 : ℝ) ≤ Real.exp s - 1 := by have := Real.one_le_exp hs.le; linarith
  have hr_base : (0 : ℝ) ≤ 1 + q * (Real.exp s - 1) := by positivity
  -- One-step multiplicative drift `∫⁻ Φ ∂(K x) ≤ r * Φ x`, from `earlyDrip_mgf_one_step`.
  have hdrift : ∀ x, ∫⁻ y, Φ y ∂(K x) ≤ r * Φ x := by
    intro x
    have hstep : ∀ c', c' ∈ ((clockProto L₀).stepDistOrSelf x).support → N c' ≤ N x + 1 := by
      intro c' hc'; exact earlyDripCount_le_succ_on_support T x c' hc'
    have hone := earlyDrip_mgf_one_step s hs.le N x hstep q hq0 (hrate x)
    -- `r * Φ x = ofReal((1+q(e^s−1)) · expCount s N x)`.
    have hfac : r * Φ x
        = ENNReal.ofReal ((1 + q * (Real.exp s - 1)) * expCount s N x) := by
      rw [hr, hΦdef, ← ENNReal.ofReal_mul hr_base]
    rw [hfac]; exact hone
  -- Apply the geometric-drift tail at threshold `θ = ofReal(exp(s·a))`.
  set θ : ℝ≥0∞ := ENNReal.ofReal (Real.exp (s * (a : ℝ))) with hθ
  have hθ0 : θ ≠ 0 := by rw [hθ]; simp [ENNReal.ofReal_eq_zero, not_le, Real.exp_pos]
  have hθtop : θ ≠ ∞ := by rw [hθ]; exact ENNReal.ofReal_ne_top
  have htail := geometric_drift_tail K Φ hΦ_meas r hdrift t c₀ θ hθ0 hθtop
  -- Identify the super-level set `{θ ≤ Φ}` with the count set `{a ≤ N}` (uses `s > 0`).
  have hset : {y | θ ≤ Φ y} = {c | a ≤ N c} := by
    ext y
    simp only [Set.mem_setOf_eq, hθ, hΦdef, expCount]
    rw [ENNReal.ofReal_le_ofReal_iff (Real.exp_pos _).le, Real.exp_le_exp]
    constructor
    · intro h
      have : (a : ℝ) ≤ (N y : ℝ) := le_of_mul_le_mul_left h hs
      exact_mod_cast this
    · intro h
      have : (a : ℝ) ≤ (N y : ℝ) := by exact_mod_cast h
      exact mul_le_mul_of_nonneg_left this hs.le
  rw [hset] at htail
  -- Rewrite the ENNReal RHS `r^t * Φ c₀ / θ` as a single `ofReal`.
  refine htail.trans (le_of_eq ?_)
  rw [hr, hΦdef, hθ, ← ENNReal.ofReal_pow hr_base,
    ← ENNReal.ofReal_mul (by positivity),
    ENNReal.ofReal_div_of_pos (Real.exp_pos _)]

end EarlyDrip

end ExactMajority
