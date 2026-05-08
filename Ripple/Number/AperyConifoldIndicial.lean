import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Analysis.SpecialFunctions.Sqrt

namespace Ripple
namespace Number

/-- The Apéry conifold singularity `z₁ = 17 - 12√2`. -/
noncomputable def aperyConifoldZ1Poly : ℝ := 17 - 12 * Real.sqrt 2

/-- Real-coefficient version of the leading polynomial `p(z) = z² - 34 z³ + z⁴`. -/
noncomputable def aperyPconifold : Polynomial ℝ :=
  Polynomial.monomial 2 1 + Polynomial.monomial 3 (-34 : ℝ) + Polynomial.monomial 4 1

/-- Real-coefficient version of `q(z) = 3z - 153 z² + 6 z³`. -/
noncomputable def aperyQconifold : Polynomial ℝ :=
  Polynomial.monomial 1 3 + Polynomial.monomial 2 (-153 : ℝ) + Polynomial.monomial 3 6

/-- The simple-root relation for the conifold point. -/
lemma aperyConifoldZ1Poly_quad :
    aperyConifoldZ1Poly ^ 2 - 34 * aperyConifoldZ1Poly + 1 = 0 := by
  unfold aperyConifoldZ1Poly
  have h2 : Real.sqrt 2 ^ 2 = 2 := by
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  nlinarith

lemma aperyConifoldZ1Poly_sq :
    aperyConifoldZ1Poly ^ 2 = 34 * aperyConifoldZ1Poly - 1 := by
  nlinarith [aperyConifoldZ1Poly_quad]

/-- `p(z₁) = 0`. -/
lemma aperyPconifold_eval_z1 :
    Polynomial.eval aperyConifoldZ1Poly aperyPconifold = 0 := by
  unfold aperyPconifold
  rw [Polynomial.eval_add, Polynomial.eval_add, Polynomial.eval_monomial,
    Polynomial.eval_monomial, Polynomial.eval_monomial]
  have hquad := aperyConifoldZ1Poly_quad
  ring_nf
  have hfac :
      aperyConifoldZ1Poly ^ 2 - aperyConifoldZ1Poly ^ 3 * 34 + aperyConifoldZ1Poly ^ 4 =
        aperyConifoldZ1Poly ^ 2 * (aperyConifoldZ1Poly ^ 2 - 34 * aperyConifoldZ1Poly + 1) := by
    ring
  rw [hfac, hquad]
  ring

/-- `p'(z₁)` in closed form. -/
lemma aperyPconifold_deriv_eval_z1 :
    Polynomial.eval aperyConifoldZ1Poly (Polynomial.derivative aperyPconifold) =
      19584 - 13848 * Real.sqrt 2 := by
  unfold aperyPconifold aperyConifoldZ1Poly
  simp [Polynomial.derivative_add]
  have h2 : Real.sqrt 2 ^ 2 = 2 := by
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  nlinarith

/-- `q(z₁)` in closed form. -/
lemma aperyQconifold_eval_z1 :
    Polynomial.eval aperyConifoldZ1Poly aperyQconifold =
      29376 - 20772 * Real.sqrt 2 := by
  unfold aperyQconifold aperyConifoldZ1Poly
  simp [Polynomial.eval_add, Polynomial.eval_monomial]
  have h2 : Real.sqrt 2 ^ 2 = 2 := by
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  nlinarith

/-- `q'(z₁)` in closed form. From `q'(z) = 3 − 306z + 18z²` and the
quadratic relation `z₁² = 34z₁ − 1`, simplifies to `5187 − 3672√2`. -/
lemma aperyQconifold_deriv_eval_z1 :
    Polynomial.eval aperyConifoldZ1Poly (Polynomial.derivative aperyQconifold) =
      5187 - 3672 * Real.sqrt 2 := by
  unfold aperyQconifold aperyConifoldZ1Poly
  simp [Polynomial.derivative_add]
  have h2 : Real.sqrt 2 ^ 2 = 2 := by
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  nlinarith

/-- `q'(z₁) < 0`. From `5187² = 26904969 < 26967168 = 3672²·2`. -/
lemma aperyQconifold_deriv_eval_z1_neg :
    Polynomial.eval aperyConifoldZ1Poly (Polynomial.derivative aperyQconifold) < 0 := by
  rw [aperyQconifold_deriv_eval_z1]
  have h2_nn : (0 : ℝ) ≤ 2 := by norm_num
  have hsq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt h2_nn
  have hsqrt_pos : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)
  nlinarith [sq_nonneg (3672 * Real.sqrt 2 - 5187), hsq, hsqrt_pos]

/-- `|q'(z₁)| = 3672·√2 − 5187`. -/
lemma aperyQconifold_deriv_eval_z1_abs :
    |Polynomial.eval aperyConifoldZ1Poly (Polynomial.derivative aperyQconifold)| =
      3672 * Real.sqrt 2 - 5187 := by
  rw [abs_of_neg aperyQconifold_deriv_eval_z1_neg, aperyQconifold_deriv_eval_z1]
  ring

/-- `q''(z₁)` in closed form. From `q''(z) = −306 + 36z`, direct
substitution gives `306 − 432√2`. -/
lemma aperyQconifold_deriv2_eval_z1 :
    Polynomial.eval aperyConifoldZ1Poly
        (Polynomial.derivative (Polynomial.derivative aperyQconifold)) =
      306 - 432 * Real.sqrt 2 := by
  unfold aperyQconifold aperyConifoldZ1Poly
  simp [Polynomial.derivative_add]
  have h2 : Real.sqrt 2 ^ 2 = 2 := by
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  nlinarith

/-- `q''(z₁) < 0`. From `306² = 93636 < 373248 = 432²·2`. -/
lemma aperyQconifold_deriv2_eval_z1_neg :
    Polynomial.eval aperyConifoldZ1Poly
        (Polynomial.derivative (Polynomial.derivative aperyQconifold)) < 0 := by
  rw [aperyQconifold_deriv2_eval_z1]
  have h2_nn : (0 : ℝ) ≤ 2 := by norm_num
  have hsq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt h2_nn
  have hsqrt_pos : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)
  nlinarith [sq_nonneg (432 * Real.sqrt 2 - 306), hsq, hsqrt_pos]

/-- `|q''(z₁)| = 432·√2 − 306`. -/
lemma aperyQconifold_deriv2_eval_z1_abs :
    |Polynomial.eval aperyConifoldZ1Poly
        (Polynomial.derivative (Polynomial.derivative aperyQconifold))| =
      432 * Real.sqrt 2 - 306 := by
  rw [abs_of_neg aperyQconifold_deriv2_eval_z1_neg, aperyQconifold_deriv2_eval_z1]
  ring

/-- `p''(z₁)` in closed form. From `p''(z) = 2 − 204z + 12z²` and the
quadratic relation `z₁² = 34z₁ − 1`, simplifies to `3458 − 2448√2`. -/
lemma aperyPconifold_deriv2_eval_z1 :
    Polynomial.eval aperyConifoldZ1Poly
        (Polynomial.derivative (Polynomial.derivative aperyPconifold)) =
      3458 - 2448 * Real.sqrt 2 := by
  unfold aperyPconifold aperyConifoldZ1Poly
  simp [Polynomial.derivative_add]
  have h2 : Real.sqrt 2 ^ 2 = 2 := by
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  nlinarith

/-- `p''(z₁) < 0`. From `3458² = 11957764 < 11985408 = 2448²·2`. -/
lemma aperyPconifold_deriv2_eval_z1_neg :
    Polynomial.eval aperyConifoldZ1Poly
        (Polynomial.derivative (Polynomial.derivative aperyPconifold)) < 0 := by
  rw [aperyPconifold_deriv2_eval_z1]
  have h2_nn : (0 : ℝ) ≤ 2 := by norm_num
  have hsq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt h2_nn
  have hsqrt_pos : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)
  nlinarith [sq_nonneg (2448 * Real.sqrt 2 - 3458), hsq, hsqrt_pos]

/-- `|p''(z₁)| = 2448·√2 − 3458`. -/
lemma aperyPconifold_deriv2_eval_z1_abs :
    |Polynomial.eval aperyConifoldZ1Poly
        (Polynomial.derivative (Polynomial.derivative aperyPconifold))| =
      2448 * Real.sqrt 2 - 3458 := by
  rw [abs_of_neg aperyPconifold_deriv2_eval_z1_neg, aperyPconifold_deriv2_eval_z1]
  ring

/-- `p'''(z₁)` in closed form. From `p'''(z) = −204 + 24z`, direct
substitution gives `204 − 288√2`. -/
lemma aperyPconifold_deriv3_eval_z1 :
    Polynomial.eval aperyConifoldZ1Poly
        (Polynomial.derivative (Polynomial.derivative
            (Polynomial.derivative aperyPconifold))) =
      204 - 288 * Real.sqrt 2 := by
  unfold aperyPconifold aperyConifoldZ1Poly
  simp [Polynomial.derivative_add]
  have h2 : Real.sqrt 2 ^ 2 = 2 := by
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  nlinarith

/-- `p'''(z₁) < 0`. From `204² = 41616 < 165888 = 288²·2`. -/
lemma aperyPconifold_deriv3_eval_z1_neg :
    Polynomial.eval aperyConifoldZ1Poly
        (Polynomial.derivative (Polynomial.derivative
            (Polynomial.derivative aperyPconifold))) < 0 := by
  rw [aperyPconifold_deriv3_eval_z1]
  have h2_nn : (0 : ℝ) ≤ 2 := by norm_num
  have hsq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt h2_nn
  have hsqrt_pos : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)
  nlinarith [sq_nonneg (288 * Real.sqrt 2 - 204), hsq, hsqrt_pos]

/-- `|p'''(z₁)| = 288·√2 − 204`. -/
lemma aperyPconifold_deriv3_eval_z1_abs :
    |Polynomial.eval aperyConifoldZ1Poly
        (Polynomial.derivative (Polynomial.derivative
            (Polynomial.derivative aperyPconifold)))| =
      288 * Real.sqrt 2 - 204 := by
  rw [abs_of_neg aperyPconifold_deriv3_eval_z1_neg, aperyPconifold_deriv3_eval_z1]
  ring

/-- `p''''(z₁) = 24`. The fourth derivative of
`p(z) = z² − 34z³ + z⁴` is the constant `24`. -/
lemma aperyPconifold_deriv4_eval_z1 :
    Polynomial.eval aperyConifoldZ1Poly
        (Polynomial.derivative (Polynomial.derivative
            (Polynomial.derivative (Polynomial.derivative aperyPconifold)))) =
      24 := by
  unfold aperyPconifold
  simp [Polynomial.derivative_add]
  norm_num

/-- `|p''''(z₁)| = 24`. -/
lemma aperyPconifold_deriv4_eval_z1_abs :
    |Polynomial.eval aperyConifoldZ1Poly
        (Polynomial.derivative (Polynomial.derivative
            (Polynomial.derivative (Polynomial.derivative aperyPconifold))))| =
      24 := by
  rw [aperyPconifold_deriv4_eval_z1]
  norm_num

/-- `q'''(z₁) = 36`. The third derivative of `q(z) = 3z − 153z² + 6z³` is
the constant `36`. -/
lemma aperyQconifold_deriv3_eval_z1 :
    Polynomial.eval aperyConifoldZ1Poly
        (Polynomial.derivative (Polynomial.derivative
            (Polynomial.derivative aperyQconifold))) = 36 := by
  unfold aperyQconifold
  simp [Polynomial.derivative_add]
  norm_num

/-- `|q'''(z₁)| = 36`. -/
lemma aperyQconifold_deriv3_eval_z1_abs :
    |Polynomial.eval aperyConifoldZ1Poly
        (Polynomial.derivative (Polynomial.derivative
            (Polynomial.derivative aperyQconifold)))| = 36 := by
  rw [aperyQconifold_deriv3_eval_z1]
  norm_num

/-- The key algebraic identity behind the conifold indicial polynomial:
`q(z₁) = (3/2) p'(z₁)`. -/
lemma aperyQconifold_eval_eq_three_halves_pderiv :
    Polynomial.eval aperyConifoldZ1Poly aperyQconifold =
      (3 / 2 : ℝ) * Polynomial.eval aperyConifoldZ1Poly
        (Polynomial.derivative aperyPconifold) := by
  rw [aperyQconifold_eval_z1, aperyPconifold_deriv_eval_z1]
  ring

/-- The algebraic indicial polynomial obtained from the simple-zero term of `p`
and the value of `q` at the conifold. -/
noncomputable def aperyConifoldIndicial (ρ : ℝ) : ℝ :=
  Polynomial.eval aperyConifoldZ1Poly (Polynomial.derivative aperyPconifold) *
      ρ * (ρ - 1) * (ρ - 2)
    + Polynomial.eval aperyConifoldZ1Poly aperyQconifold * ρ * (ρ - 1)

/-- The conifold indicial polynomial factors as a nonzero constant times
`ρ(ρ-1)(2ρ-1)`. This isolates the algebraic content of the claimed
Frobenius exponents `{0, 1/2, 1}`. -/
lemma aperyConifoldIndicial_factor (ρ : ℝ) :
    aperyConifoldIndicial ρ =
      Polynomial.eval aperyConifoldZ1Poly (Polynomial.derivative aperyPconifold) *
        ρ * (ρ - 1) * (2 * ρ - 1) / 2 := by
  unfold aperyConifoldIndicial
  rw [aperyQconifold_eval_eq_three_halves_pderiv]
  ring

/-- The scalar prefactor in the indicial polynomial is nonzero, so the
algebraic indicial roots are exactly `0`, `1/2`, `1`. -/
lemma aperyPconifold_deriv_eval_z1_ne_zero :
    Polynomial.eval aperyConifoldZ1Poly (Polynomial.derivative aperyPconifold) ≠ 0 := by
  rw [aperyPconifold_deriv_eval_z1]
  intro h
  have hs : Real.sqrt 2 = 1632 / 1154 := by
    linarith
  have hsq := congrArg (fun x : ℝ => x ^ 2) hs
  norm_num at hsq

/-- `q(z₁) < 0`. From `q(z₁) = 29376 - 20772·√2` and `(20772)²·2 = 862951968 >
862949376 = 29376²`. -/
lemma aperyQconifold_eval_z1_neg :
    Polynomial.eval aperyConifoldZ1Poly aperyQconifold < 0 := by
  rw [aperyQconifold_eval_z1]
  have h2_nn : (0 : ℝ) ≤ 2 := by norm_num
  have hsq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt h2_nn
  have hsqrt_pos : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)
  nlinarith [sq_nonneg (20772 * Real.sqrt 2 - 29376), hsq, hsqrt_pos]

/-- `p'(z₁) < 0`. From `p'(z₁) = 19584 - 13848·√2` and `(13848)²·2 = 383534208 >
383533056 = 19584²`. -/
lemma aperyPconifold_deriv_eval_z1_neg :
    Polynomial.eval aperyConifoldZ1Poly (Polynomial.derivative aperyPconifold) < 0 := by
  rw [aperyPconifold_deriv_eval_z1]
  have h2_nn : (0 : ℝ) ≤ 2 := by norm_num
  have hsq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt h2_nn
  have hsqrt_pos : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)
  nlinarith [sq_nonneg (13848 * Real.sqrt 2 - 19584), hsq, hsqrt_pos]

/-- `|q(z₁)| = 20772·√2 - 29376`. -/
lemma aperyQconifold_eval_z1_abs :
    |Polynomial.eval aperyConifoldZ1Poly aperyQconifold| =
      20772 * Real.sqrt 2 - 29376 := by
  rw [abs_of_neg aperyQconifold_eval_z1_neg, aperyQconifold_eval_z1]
  ring

/-- `|p'(z₁)| = 13848·√2 - 19584`. -/
lemma aperyPconifold_deriv_eval_z1_abs :
    |Polynomial.eval aperyConifoldZ1Poly (Polynomial.derivative aperyPconifold)| =
      13848 * Real.sqrt 2 - 19584 := by
  rw [abs_of_neg aperyPconifold_deriv_eval_z1_neg, aperyPconifold_deriv_eval_z1]
  ring

/-- `|p'(z₁)| > 0`. Direct consequence of `aperyPconifold_deriv_eval_z1_neg`. -/
lemma aperyPconifold_deriv_eval_z1_abs_pos :
    0 < |Polynomial.eval aperyConifoldZ1Poly (Polynomial.derivative aperyPconifold)| :=
  abs_pos.mpr aperyPconifold_deriv_eval_z1_ne_zero

/-- Reciprocal in rationalised form: `1/|p'(z₁)| = (13848·√2 + 19584)/1152`.
Numerically `≈ 34.0`. Used to make the convergence threshold
`M_eps · (1 + 64B/|p'(z₁)|) < 1` legible. -/
lemma one_div_aperyPconifold_deriv_eval_z1_abs :
    1 / |Polynomial.eval aperyConifoldZ1Poly
        (Polynomial.derivative aperyPconifold)|
      = (13848 * Real.sqrt 2 + 19584) / 1152 := by
  rw [aperyPconifold_deriv_eval_z1_abs]
  have hsq : Real.sqrt 2 ^ 2 = 2 :=
    Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)
  have hsqrt_pos : 0 < Real.sqrt 2 :=
    Real.sqrt_pos.mpr (by norm_num : (0:ℝ) < 2)
  have hdenom_ne : (13848 * Real.sqrt 2 - 19584 : ℝ) ≠ 0 := by
    intro h
    have h' : 13848 * Real.sqrt 2 = 19584 := by linarith
    have hsq' : (13848 * Real.sqrt 2) ^ 2 = 19584 ^ 2 := by rw [h']
    rw [mul_pow, hsq] at hsq'
    norm_num at hsq'
  field_simp
  nlinarith [hsq, hsqrt_pos]

/-- **Numerical upper bound on `1/|p'(z₁)|`.** From the closed form
`(13848√2 + 19584)/1152` and `√2 < 20736/13848`, we get the strict
estimate `1/|p'(z₁)| < 35`. Equivalently `|p'(z₁)| > 1/35`. This
quantifies the small-denominator obstruction at the conifold: the
Frobenius contraction constant `K = (n+2)·B·2^{n+1}/|p'(z₁)|`
inherits a `~34×` blow-up from this reciprocal. -/
lemma aperyPconifold_inv_deriv_eval_z1_abs_lt_35 :
    1 / |Polynomial.eval aperyConifoldZ1Poly
            (Polynomial.derivative aperyPconifold)| < 35 := by
  rw [one_div_aperyPconifold_deriv_eval_z1_abs]
  have hsq : Real.sqrt 2 ^ 2 = 2 :=
    Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)
  have hsqrt_pos : 0 < Real.sqrt 2 :=
    Real.sqrt_pos.mpr (by norm_num : (0:ℝ) < 2)
  have h_sq_lt : (13848 * Real.sqrt 2)^2 < (20736 : ℝ)^2 := by
    rw [mul_pow, hsq]; norm_num
  have h_sum_pos : 0 < 20736 + 13848 * Real.sqrt 2 := by positivity
  have h_lt : 13848 * Real.sqrt 2 < 20736 := by
    nlinarith [h_sq_lt, h_sum_pos, hsqrt_pos]
  rw [div_lt_iff₀ (by norm_num : (0:ℝ) < 1152)]
  linarith

/-- **Numerical lower bound on `1/|p'(z₁)|`.** Companion to
`aperyPconifold_inv_deriv_eval_z1_abs_lt_35`: from `√2 > 19584/13848`,
`1/|p'(z₁)| > 34`. Combined with the upper bound, the reciprocal lies
in `(34, 35)`. -/
lemma aperyPconifold_inv_deriv_eval_z1_abs_gt_34 :
    34 < 1 / |Polynomial.eval aperyConifoldZ1Poly
                (Polynomial.derivative aperyPconifold)| := by
  rw [one_div_aperyPconifold_deriv_eval_z1_abs]
  have hsq : Real.sqrt 2 ^ 2 = 2 :=
    Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)
  have hsqrt_pos : 0 < Real.sqrt 2 :=
    Real.sqrt_pos.mpr (by norm_num : (0:ℝ) < 2)
  have h_sq_gt : (19584 : ℝ)^2 < (13848 * Real.sqrt 2)^2 := by
    rw [mul_pow, hsq]; norm_num
  have h_sum_pos : 0 < 19584 + 13848 * Real.sqrt 2 := by positivity
  have h_gt : (19584 : ℝ) < 13848 * Real.sqrt 2 := by
    nlinarith [h_sq_gt, h_sum_pos, hsqrt_pos]
  rw [lt_div_iff₀ (by norm_num : (0:ℝ) < 1152)]
  linarith

/-- **Quantitative lower bound on the Frobenius contraction at Apéry.**
For the uniform-`B` Frobenius bound at the Apéry conifold with
`(n+2)·2^{n+1} = 32` and `B = 153`, the contraction constant
`K = 32·B/|p'(z₁)|` exceeds `166464`. Combined with the ratio-test
threshold `M_eps · (1 + K) < 1`, this forces `M_eps < 1/166465`,
roughly `6·10⁻⁶`. The standard probe `M_eps = 3z₁/4 ≈ 0.022` exceeds
this by `3.5` orders of magnitude — the formal expression of the
"4-orders gap" between the uniform-`B` Gronwall route and the
empirical convergence corridor for ζ(3). -/
lemma aperyConifold_K_uniform_gt_166464 :
    (166464 : ℝ) <
      32 * 153 / |Polynomial.eval aperyConifoldZ1Poly
        (Polynomial.derivative aperyPconifold)| := by
  have h_inv : (34 : ℝ) <
      1 / |Polynomial.eval aperyConifoldZ1Poly
        (Polynomial.derivative aperyPconifold)| :=
    aperyPconifold_inv_deriv_eval_z1_abs_gt_34
  calc (166464 : ℝ)
      = 4896 * 34 := by norm_num
    _ < 4896 * (1 / |Polynomial.eval aperyConifoldZ1Poly
                (Polynomial.derivative aperyPconifold)|) :=
        mul_lt_mul_of_pos_left h_inv (by norm_num : (0:ℝ) < 4896)
    _ = 32 * 153 / |Polynomial.eval aperyConifoldZ1Poly
                (Polynomial.derivative aperyPconifold)| := by
        rw [mul_one_div]; ring

/-- **Key threshold ratio.** From the algebraic identity
`q(z₁) = (3/2) p'(z₁)` and the shared sign of `q(z₁)` and `p'(z₁)`,
the absolute values satisfy `|q(z₁)| = (3/2)|p'(z₁)|`. Equivalently,
`2|q(z₁)| = 3|p'(z₁)|`, which collapses the per-branch threshold
inequality `2|q| ≤ |p'|·((m+1) − |ρ| − 2)` to `3 ≤ (m+1) − |ρ| − 2`,
i.e., `m ≥ |ρ| + 4`. -/
lemma aperyQconifold_eval_z1_abs_eq_three_halves_deriv :
    |Polynomial.eval aperyConifoldZ1Poly aperyQconifold| =
      (3 / 2 : ℝ) *
        |Polynomial.eval aperyConifoldZ1Poly (Polynomial.derivative aperyPconifold)| := by
  rw [aperyQconifold_eval_z1_abs, aperyPconifold_deriv_eval_z1_abs]
  ring

/-- Convenient form: `2|q(z₁)| = 3|p'(z₁)|`. -/
lemma two_aperyQconifold_eval_z1_abs_eq_three_deriv :
    2 * |Polynomial.eval aperyConifoldZ1Poly aperyQconifold| =
      3 * |Polynomial.eval aperyConifoldZ1Poly (Polynomial.derivative aperyPconifold)| := by
  have := aperyQconifold_eval_z1_abs_eq_three_halves_deriv
  linarith

/-- **Threshold for ρ = 0 (Z branch).** For `m' ≥ 4`,
`2|q(z₁)| ≤ |p'(z₁)|·((m'+1) − 0 − 2)`. Uses `2|q| = 3|p'|` and
`|p'| > 0`. -/
lemma aperyConifold_threshold_Z (m' : ℕ) (hm' : 4 ≤ m') :
    2 * |Polynomial.eval aperyConifoldZ1Poly aperyQconifold| ≤
      |Polynomial.eval aperyConifoldZ1Poly (Polynomial.derivative aperyPconifold)| *
        (((m' + 1 : ℕ) : ℝ) - |(0 : ℝ)| - (2 : ℝ)) := by
  have hP_nn : 0 ≤
      |Polynomial.eval aperyConifoldZ1Poly (Polynomial.derivative aperyPconifold)| :=
    aperyPconifold_deriv_eval_z1_abs_pos.le
  rw [two_aperyQconifold_eval_z1_abs_eq_three_deriv]
  have hcast : (3 : ℝ) ≤ (((m' + 1 : ℕ) : ℝ) - |(0 : ℝ)| - (2 : ℝ)) := by
    have hm'R : (4 : ℝ) ≤ (m' : ℝ) := by exact_mod_cast hm'
    push_cast
    rw [abs_zero]
    linarith
  calc 3 * |Polynomial.eval aperyConifoldZ1Poly
            (Polynomial.derivative aperyPconifold)|
      = |Polynomial.eval aperyConifoldZ1Poly (Polynomial.derivative aperyPconifold)| * 3 := by
        ring
    _ ≤ |Polynomial.eval aperyConifoldZ1Poly (Polynomial.derivative aperyPconifold)| *
          (((m' + 1 : ℕ) : ℝ) - |(0 : ℝ)| - (2 : ℝ)) :=
        mul_le_mul_of_nonneg_left hcast hP_nn

/-- **Threshold for ρ = 1/2 (H branch).** For `m' ≥ 5`,
`2|q(z₁)| ≤ |p'(z₁)|·((m'+1) − 1/2 − 2)`. -/
lemma aperyConifold_threshold_H (m' : ℕ) (hm' : 5 ≤ m') :
    2 * |Polynomial.eval aperyConifoldZ1Poly aperyQconifold| ≤
      |Polynomial.eval aperyConifoldZ1Poly (Polynomial.derivative aperyPconifold)| *
        (((m' + 1 : ℕ) : ℝ) - |(1 / 2 : ℝ)| - (2 : ℝ)) := by
  have hP_nn : 0 ≤
      |Polynomial.eval aperyConifoldZ1Poly (Polynomial.derivative aperyPconifold)| :=
    aperyPconifold_deriv_eval_z1_abs_pos.le
  rw [two_aperyQconifold_eval_z1_abs_eq_three_deriv]
  have hcast : (3 : ℝ) ≤ (((m' + 1 : ℕ) : ℝ) - |(1 / 2 : ℝ)| - (2 : ℝ)) := by
    have hm'R : (5 : ℝ) ≤ (m' : ℝ) := by exact_mod_cast hm'
    have habs : |(1 / 2 : ℝ)| = 1 / 2 := by
      rw [abs_of_pos]; norm_num
    push_cast
    rw [habs]
    linarith
  calc 3 * |Polynomial.eval aperyConifoldZ1Poly
            (Polynomial.derivative aperyPconifold)|
      = |Polynomial.eval aperyConifoldZ1Poly (Polynomial.derivative aperyPconifold)| * 3 := by
        ring
    _ ≤ |Polynomial.eval aperyConifoldZ1Poly (Polynomial.derivative aperyPconifold)| *
          (((m' + 1 : ℕ) : ℝ) - |(1 / 2 : ℝ)| - (2 : ℝ)) :=
        mul_le_mul_of_nonneg_left hcast hP_nn

/-- **Threshold for ρ = 1 (O branch).** For `m' ≥ 5`,
`2|q(z₁)| ≤ |p'(z₁)|·((m'+1) − 1 − 2)`. -/
lemma aperyConifold_threshold_O (m' : ℕ) (hm' : 5 ≤ m') :
    2 * |Polynomial.eval aperyConifoldZ1Poly aperyQconifold| ≤
      |Polynomial.eval aperyConifoldZ1Poly (Polynomial.derivative aperyPconifold)| *
        (((m' + 1 : ℕ) : ℝ) - |(1 : ℝ)| - (2 : ℝ)) := by
  have hP_nn : 0 ≤
      |Polynomial.eval aperyConifoldZ1Poly (Polynomial.derivative aperyPconifold)| :=
    aperyPconifold_deriv_eval_z1_abs_pos.le
  rw [two_aperyQconifold_eval_z1_abs_eq_three_deriv]
  have hcast : (3 : ℝ) ≤ (((m' + 1 : ℕ) : ℝ) - |(1 : ℝ)| - (2 : ℝ)) := by
    have hm'R : (5 : ℝ) ≤ (m' : ℝ) := by exact_mod_cast hm'
    push_cast
    rw [abs_one]
    linarith
  calc 3 * |Polynomial.eval aperyConifoldZ1Poly
            (Polynomial.derivative aperyPconifold)|
      = |Polynomial.eval aperyConifoldZ1Poly (Polynomial.derivative aperyPconifold)| * 3 := by
        ring
    _ ≤ |Polynomial.eval aperyConifoldZ1Poly (Polynomial.derivative aperyPconifold)| *
          (((m' + 1 : ℕ) : ℝ) - |(1 : ℝ)| - (2 : ℝ)) :=
        mul_le_mul_of_nonneg_left hcast hP_nn

/-- **Small-side bound for Z branch (ρ = 0).** For `m ≥ 6`,
`|0| + 2 < (m+1 : ℕ)`. -/
lemma aperyConifold_small_Z (m : ℕ) (hm : 6 ≤ m) :
    (|(0 : ℝ)| + (2 : ℝ)) < ((m + 1 : ℕ) : ℝ) := by
  have hmR : (6 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  push_cast
  rw [abs_zero]
  linarith

/-- **Large-side bound for Z branch (ρ = 0).** For `m ≥ 6`,
`3·|0| + 3·2 ≤ m`. -/
lemma aperyConifold_large_Z (m : ℕ) (hm : 6 ≤ m) :
    3 * |(0 : ℝ)| + 3 * (2 : ℝ) ≤ (m : ℝ) := by
  have hmR : (6 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  rw [abs_zero]
  linarith

/-- **Small-side bound for H branch (ρ = 1/2).** For `m ≥ 8`,
`|1/2| + 2 < (m+1 : ℕ)`. -/
lemma aperyConifold_small_H (m : ℕ) (hm : 8 ≤ m) :
    (|(1 / 2 : ℝ)| + (2 : ℝ)) < ((m + 1 : ℕ) : ℝ) := by
  have hmR : (8 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have habs : |(1 / 2 : ℝ)| = 1 / 2 := by rw [abs_of_pos]; norm_num
  push_cast
  rw [habs]
  linarith

/-- **Large-side bound for H branch (ρ = 1/2).** For `m ≥ 8`,
`3·|1/2| + 3·2 ≤ m`. -/
lemma aperyConifold_large_H (m : ℕ) (hm : 8 ≤ m) :
    3 * |(1 / 2 : ℝ)| + 3 * (2 : ℝ) ≤ (m : ℝ) := by
  have hmR : (8 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have habs : |(1 / 2 : ℝ)| = 1 / 2 := by rw [abs_of_pos]; norm_num
  rw [habs]
  linarith

/-- **Small-side bound for O branch (ρ = 1).** For `m ≥ 9`,
`|1| + 2 < (m+1 : ℕ)`. -/
lemma aperyConifold_small_O (m : ℕ) (hm : 9 ≤ m) :
    (|(1 : ℝ)| + (2 : ℝ)) < ((m + 1 : ℕ) : ℝ) := by
  have hmR : (9 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  push_cast
  rw [abs_one]
  linarith

/-- **Large-side bound for O branch (ρ = 1).** For `m ≥ 9`,
`3·|1| + 3·2 ≤ m`. -/
lemma aperyConifold_large_O (m : ℕ) (hm : 9 ≤ m) :
    3 * |(1 : ℝ)| + 3 * (2 : ℝ) ≤ (m : ℝ) := by
  have hmR : (9 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  rw [abs_one]
  linarith

/-- The indicial polynomial vanishes exactly at the three algebraic roots
`0`, `1/2`, `1`. -/
lemma aperyConifoldIndicial_eq_zero_iff (ρ : ℝ) :
    aperyConifoldIndicial ρ = 0 ↔ ρ = 0 ∨ ρ = (1 / 2 : ℝ) ∨ ρ = 1 := by
  constructor
  · intro hρ
    have hfac := aperyConifoldIndicial_factor ρ
    have hsplit :
        aperyConifoldIndicial ρ =
          (Polynomial.eval aperyConifoldZ1Poly (Polynomial.derivative aperyPconifold) / 2) *
            (ρ * (ρ - 1) * (2 * ρ - 1)) := by
      rw [hfac]
      ring
    have hzero :
        (Polynomial.eval aperyConifoldZ1Poly (Polynomial.derivative aperyPconifold) / 2) *
          (ρ * (ρ - 1) * (2 * ρ - 1)) = 0 := by
      rw [← hsplit]
      exact hρ
    have hcoef :
        Polynomial.eval aperyConifoldZ1Poly (Polynomial.derivative aperyPconifold) / 2 ≠ 0 := by
      exact div_ne_zero aperyPconifold_deriv_eval_z1_ne_zero (by norm_num)
    have hprod : ρ * (ρ - 1) * (2 * ρ - 1) = 0 := by
      exact (mul_eq_zero.mp hzero).resolve_left hcoef
    rcases mul_eq_zero.mp hprod with hzero | hhalf
    · rcases mul_eq_zero.mp hzero with hzero' | hone
      · exact Or.inl hzero'
      · exact Or.inr <| Or.inr (by linarith)
    · exact Or.inr <| Or.inl (by linarith)
  · intro hρ
    rcases hρ with rfl | rfl | rfl
    · rw [aperyConifoldIndicial_factor]
      ring
    · rw [aperyConifoldIndicial_factor]
      ring
    · rw [aperyConifoldIndicial_factor]
      ring

/-- Lightweight interface for a local Frobenius exponent at the Apéry
conifold. The analytic content of the expansion is deferred; this
predicate only records the indicial relation that such an exponent must
satisfy. -/
structure IsAperyConifoldFrobeniusExponent (_A : ℝ → ℝ) (ρ : ℝ) : Prop where
  indicial_eq_zero : aperyConifoldIndicial ρ = 0

/-- **(F3)** Any local Frobenius exponent at the Apéry conifold must be one
of the three indicial roots `0`, `1/2`, `1`. -/
theorem aperyConifold_indicial_exponents_are_roots
    {A : ℝ → ℝ} {ρ : ℝ}
    (hρ : IsAperyConifoldFrobeniusExponent A ρ) :
    ρ = 0 ∨ ρ = (1 / 2 : ℝ) ∨ ρ = 1 := by
  exact (aperyConifoldIndicial_eq_zero_iff ρ).mp hρ.indicial_eq_zero

/-! ## Taylor shift coefficients

The Taylor shift of a polynomial `p` at `z₁` has coefficients
`taylorShift(p, z₁)_k = (-1)^k · p^{(k)}(z₁) / k!`.
We compute these for `k = 2, 3, 4` (P) and `k = 2, 3` (Q). -/

/-- `taylorShift(P, z₁)₂ = P''(z₁)/2! = 1729 - 1224√2`. -/
lemma aperyPconifold_taylorShift_coeff_2 :
    Polynomial.eval aperyConifoldZ1Poly
        (Polynomial.derivative (Polynomial.derivative aperyPconifold)) / 2 =
      1729 - 1224 * Real.sqrt 2 := by
  rw [aperyPconifold_deriv2_eval_z1]
  ring

/-- `taylorShift(P, z₁)₃ = -P'''(z₁)/3! = -34 + 48√2`. -/
lemma aperyPconifold_taylorShift_coeff_3 :
    -(Polynomial.eval aperyConifoldZ1Poly
        (Polynomial.derivative (Polynomial.derivative
            (Polynomial.derivative aperyPconifold)))) / 6 =
      -34 + 48 * Real.sqrt 2 := by
  rw [aperyPconifold_deriv3_eval_z1]
  ring

/-- `taylorShift(P, z₁)₄ = P⁴(z₁)/4! = 1`. -/
lemma aperyPconifold_taylorShift_coeff_4 :
    Polynomial.eval aperyConifoldZ1Poly
        (Polynomial.derivative (Polynomial.derivative
            (Polynomial.derivative (Polynomial.derivative aperyPconifold)))) / 24 =
      1 := by
  rw [aperyPconifold_deriv4_eval_z1]
  norm_num

/-- `taylorShift(Q, z₁)₂ = Q''(z₁)/2! = 153 - 216√2`. -/
lemma aperyQconifold_taylorShift_coeff_2 :
    Polynomial.eval aperyConifoldZ1Poly
        (Polynomial.derivative (Polynomial.derivative aperyQconifold)) / 2 =
      153 - 216 * Real.sqrt 2 := by
  rw [aperyQconifold_deriv2_eval_z1]
  ring

/-- `taylorShift(Q, z₁)₃ = -Q'''(z₁)/3! = -6`. -/
lemma aperyQconifold_taylorShift_coeff_3 :
    -(Polynomial.eval aperyConifoldZ1Poly
        (Polynomial.derivative (Polynomial.derivative
            (Polynomial.derivative aperyQconifold)))) / 6 =
      -6 := by
  rw [aperyQconifold_deriv3_eval_z1]
  norm_num

end Number
end Ripple
