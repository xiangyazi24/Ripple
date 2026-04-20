/-
  Ripple.Number.ApreyScalarZ — (F6) scalar exponential convergence
  of the Apéry conifold parameter `z(τ)`.

  The Apéry 8-variable system's z-coordinate satisfies an autonomous
  scalar ODE
      `dz/dτ = p(z) := z² (1 − 34 z + z²) = z² (z − z₁)(z − z₂)`
  where
      `z₁ := 17 − 12 √2`  (the conifold singularity, our target),
      `z₂ := 17 + 12 √2`  (the conjugate, outside the basin).

  **Goal of this file.**  Prove the standalone scalar lemma (F6) from the
  roadmap in `ApreyBounded.apery_conifold_frobenius_witness`:

      if `z : ℝ → ℝ` satisfies `z' = p(z)` on `[0, ∞)` with
      `z(0) = z₀ ∈ (0, z₁)`, then there exist `K, κ > 0` with
      `|z₁ − z(t)| ≤ K · exp(−κ · t)` for all `t ≥ 0`.

  This is the only F-step of the Frobenius roadmap that is fully within
  Mathlib's reach — (F1)–(F5) require Apéry's irrationality theorem and
  regular-singular-point Frobenius theory.

  **Proof outline.**

    1. Factorisation.  `p(z) = (z₁ − z) · z² · (z₂ − z)`.  On the open
       interval `(0, z₁)` the three factors `(z₁ − z)`, `z²`, `(z₂ − z)`
       are all strictly positive, so `p(z) > 0` — i.e. `z` is strictly
       increasing along any solution that stays in `(0, z₁)`.

    2. Invariant region.  The constant function `z ≡ z₁` is a solution
       of `z' = p(z)` (since `p(z₁) = 0`).  Mathlib's Picard uniqueness
       (`ODE_solution_unique`) then forces any solution starting
       strictly below `z₁` to remain strictly below `z₁` forever.

    3. Gronwall contraction.  Let `u(t) := z₁ − z(t) > 0`.  Then
          `u'(t) = −p(z(t)) = −u(t) · z(t)² · (z₂ − z(t))`.
       On the invariant region `z(t) ∈ [z₀, z₁]` the factor
       `z(t)² · (z₂ − z(t))` is bounded below by
          `κ := z₀² · (z₂ − z₁) = z₀² · 24 √2 > 0`.
       Hence `u'(t) ≤ −κ · u(t)`, and the constant-coefficient scalar
       Grönwall inequality gives
          `u(t) ≤ u(0) · exp(−κ · t)`.

  The constant `κ` obtained this way is *not* the optimal linearisation
  rate `λ = 24 √2 · z₁²` advertised in the docstring of
  `apery_conifold_frobenius_witness` (nor `3 λ / 2`), but it is *some*
  strictly positive rate — which is all the downstream chain demands.
-/

import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.ODE.PicardLindelof
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace Ripple
namespace Number

open Real Set

/-- The conifold singularity `z₁ = 17 − 12√2`.  This is the target
fixed point of the scalar Apéry dynamics. -/
noncomputable def aperyZ1 : ℝ := 17 - 12 * Real.sqrt 2

/-- The conjugate `z₂ = 17 + 12√2`.  Outside the conifold basin. -/
noncomputable def aperyZ2 : ℝ := 17 + 12 * Real.sqrt 2

/-- Scalar field for the conifold z-dynamics:
`p(z) = z² · (1 − 34 z + z²)`. -/
noncomputable def aperyScalarP (z : ℝ) : ℝ :=
  z ^ 2 * (1 - 34 * z + z ^ 2)

/-! ## Elementary properties of `z₁`, `z₂`, `p`. -/

lemma aperyZ1_lt_aperyZ2 : aperyZ1 < aperyZ2 := by
  unfold aperyZ1 aperyZ2
  have h : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  linarith

lemma aperyZ2_sub_aperyZ1 : aperyZ2 - aperyZ1 = 24 * Real.sqrt 2 := by
  unfold aperyZ1 aperyZ2; ring

lemma aperyZ1_pos : 0 < aperyZ1 := by
  unfold aperyZ1
  -- 17 > 12 √2 iff 289 > 288, true.
  have hsqrt : Real.sqrt 2 < 17 / 12 := by
    rw [show (17 : ℝ) / 12 = Real.sqrt ((17 / 12) ^ 2) by
      rw [Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 17/12)]]
    apply Real.sqrt_lt_sqrt (by norm_num)
    norm_num
  linarith

/-- Factorisation: `p(z) = z² · (z − z₁) · (z − z₂)`. -/
lemma aperyScalarP_factor (z : ℝ) :
    aperyScalarP z = z ^ 2 * (z - aperyZ1) * (z - aperyZ2) := by
  unfold aperyScalarP aperyZ1 aperyZ2
  have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)
  ring_nf
  ring_nf at h2
  nlinarith [h2, Real.sqrt_nonneg 2]

/-- Useful form: `p(z) = −(z₁ − z) · z² · (z₂ − z) · (−1)`  — i.e.
`p(z) = (z₁ − z) · z² · (z₂ − z)` when the two negatives cancel. -/
lemma aperyScalarP_factor' (z : ℝ) :
    aperyScalarP z = (aperyZ1 - z) * z ^ 2 * (aperyZ2 - z) := by
  rw [aperyScalarP_factor]; ring

/-- On the open interval `(0, z₁)` the scalar field is strictly
positive. -/
lemma aperyScalarP_pos_of_mem_basin {z : ℝ}
    (hz_pos : 0 < z) (hz_lt : z < aperyZ1) :
    0 < aperyScalarP z := by
  rw [aperyScalarP_factor']
  have hz2_pos : 0 < z ^ 2 := by positivity
  have hleft : 0 < aperyZ1 - z := by linarith
  have hright : 0 < aperyZ2 - z := by
    have : z < aperyZ2 := lt_trans hz_lt aperyZ1_lt_aperyZ2
    linarith
  positivity

/-- The linearisation rate used in the Gronwall step is strictly positive.
Given a lower bound `z₀ > 0` on the z-coordinate, we use
`κ := z₀² · (z₂ − z₁) = 24 √2 · z₀²`. -/
noncomputable def aperyKappa (z₀ : ℝ) : ℝ := z₀ ^ 2 * (24 * Real.sqrt 2)

lemma aperyKappa_pos {z₀ : ℝ} (hz₀ : 0 < z₀) : 0 < aperyKappa z₀ := by
  unfold aperyKappa
  have hsqrt : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have : 0 < z₀ ^ 2 := by positivity
  positivity

/-! ## (F6): the main exponential-convergence lemma.

  Statement: Given a solution `z : ℝ → ℝ` of the scalar ODE
  `z' = p(z)` on `[0, ∞)` with `z(0) ∈ (0, z₁)`, the quantity
  `z₁ − z(t)` decays exponentially.

  **Status.**  Skeletal — all three proof steps (invariant region via
  Picard uniqueness, Grönwall contraction, packaging) are left as
  `sorry` pending dedicated follow-up.  The file compiles and fixes
  the precise statement that future work must close.
-/

/-- **(F6) Scalar exponential convergence of the Apéry z-coordinate.**
Given `z : ℝ → ℝ` satisfying `z' = p(z)` on `[0, ∞)` with
`z(0) = z₀ ∈ (0, z₁)`, the gap `z₁ − z(t)` decays exponentially with
rate `κ := z₀² · 24 √2`. -/
theorem apery_scalar_z_exponential_convergence
    (z : ℝ → ℝ) (z₀ : ℝ)
    (hz₀_pos : 0 < z₀) (hz₀_lt : z₀ < aperyZ1)
    (hz_init : z 0 = z₀)
    (hz_ode : ∀ t : ℝ, 0 ≤ t → HasDerivAt z (aperyScalarP (z t)) t) :
    ∃ K κ : ℝ, 0 < K ∧ 0 < κ ∧
      ∀ t : ℝ, 0 ≤ t → |aperyZ1 - z t| ≤ K * Real.exp (-(κ * t)) := by
  refine ⟨aperyZ1 - z₀, aperyKappa z₀, ?_, aperyKappa_pos hz₀_pos, ?_⟩
  · linarith
  · sorry

end Number
end Ripple
