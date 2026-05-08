/-
  Ripple.Number.Frobenius.AperyG2Bounded

  Phase 2 (sub-sorry piece (1)): the differentiated numerator
  `B''(z) − ζ(3)·A''(z)` is bounded on a neighborhood of `z = z₁`.

  Mathematical idea:
    - Define `g(z) := B(z) − ζ(3)·A(z) = ∑ g_n z^n` with `g_n := b_n − ζ(3)·a_n`.
    - Phase 1 gave: `|g_n| · z₁^n` summable, so `g(z)` analytic on `|z| < α`.
    - Therefore `g''(z) = ∑ (n+2)(n+1) g_{n+2} z^n` is also analytic on
      `|z| < α`, in particular continuous on `|z| ≤ z₁` (closed disk).
    - Continuous on compact ⇒ bounded.

  Phase 2 deliverable: `Summable (fun n ↦ (n+2)(n+1) · |g_{n+2}| · z₁^n)`,
  which gives `g''(z₁)` well-defined; combined with continuity (via M-test
  on `|z| ≤ b < z₁` for any `b > 0`) yields boundedness near `z₁`.
-/

import Ripple.Number.Frobenius.AperyAbsConvergentAtZ1

namespace Ripple.Number

open Filter

/-- Comparator for the second-derivative series: `K · (n+1)(n+2)(n+6) /
((1-r)² · α^(2n+3))`. This is poly degree 3 × geometric, summable. -/
noncomputable def aperyG2Comparator (K : ℝ) (n : ℕ) : ℝ :=
  K * ((n : ℝ) + 1) * ((n : ℝ) + 2) * ((n : ℝ) + 6) /
    ((1 - aperyR) ^ 2 * aperyAlpha ^ (2 * n + 3))

/-- The second-derivative comparator is summable. -/
lemma aperyG2Comparator_summable (K : ℝ) :
    Summable (aperyG2Comparator K) := by
  -- Decompose: aperyG2Comparator K n = (K / ((1-r)²·α³)) · (n+1)(n+2)(n+6) · r^n
  -- where r = 1/α². Then poly·geom is summable.
  have hr_pos : 0 < aperyR := aperyR_pos
  have hr_lt : aperyR < 1 := aperyR_lt_one
  have hr_norm : ‖aperyR‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_pos hr_pos]; exact hr_lt
  have h1mr_pos : 0 < 1 - aperyR := by linarith
  have h1mr_sq_pos : 0 < (1 - aperyR) ^ 2 := by positivity
  have hα_pos : 0 < aperyAlpha := aperyAlpha_pos
  have hα_ne : aperyAlpha ≠ 0 := aperyAlpha_ne_zero
  -- Polynomial Summable for degrees 0,1,2,3:
  have hsum0 : Summable (fun n : ℕ => ((n : ℝ) ^ 0) * aperyR ^ n) :=
    summable_pow_mul_geometric_of_norm_lt_one 0 hr_norm
  have hsum1 : Summable (fun n : ℕ => ((n : ℝ) ^ 1) * aperyR ^ n) :=
    summable_pow_mul_geometric_of_norm_lt_one 1 hr_norm
  have hsum2 : Summable (fun n : ℕ => ((n : ℝ) ^ 2) * aperyR ^ n) :=
    summable_pow_mul_geometric_of_norm_lt_one 2 hr_norm
  have hsum3 : Summable (fun n : ℕ => ((n : ℝ) ^ 3) * aperyR ^ n) :=
    summable_pow_mul_geometric_of_norm_lt_one 3 hr_norm
  -- (n+1)(n+2)(n+6) = n³ + 9n² + 20n + 12
  have hpoly : Summable (fun n : ℕ =>
      ((n : ℝ) + 1) * ((n : ℝ) + 2) * ((n : ℝ) + 6) * aperyR ^ n) := by
    convert (hsum3.add ((hsum2.mul_left 9).add ((hsum1.mul_left 20).add
      (hsum0.mul_left 12)))) using 1
    ext n; ring
  -- aperyG2Comparator K n = const · poly_n · r^n
  -- where const = K / ((1-r)² · α³).
  have heq : aperyG2Comparator K = fun n : ℕ =>
      (K / ((1 - aperyR) ^ 2 * aperyAlpha ^ 3)) *
        (((n : ℝ) + 1) * ((n : ℝ) + 2) * ((n : ℝ) + 6) * aperyR ^ n) := by
    funext n
    unfold aperyG2Comparator aperyR
    have hα_pow_combine : aperyAlpha ^ (2 * n + 3) = aperyAlpha ^ 3 * (aperyAlpha ^ 2) ^ n := by
      rw [show 2 * n + 3 = 3 + 2 * n from by omega, pow_add, pow_mul]
    rw [hα_pow_combine]
    have h_inv_pow : (1 / aperyAlpha ^ 2) ^ n = (1 : ℝ) / (aperyAlpha ^ 2) ^ n := by
      rw [div_pow, one_pow]
    rw [h_inv_pow]
    field_simp
  rw [heq]
  exact hpoly.mul_left _

/-- For `n ≥ M₀`, the second-derivative term is bounded by the comparator. -/
lemma aperyG2_term_le_comparator :
    ∃ M₀ : ℕ, 1 ≤ M₀ ∧ ∃ K : ℝ, 0 < K ∧
      ∀ n : ℕ, M₀ ≤ n →
        ((n : ℝ) + 2) * ((n : ℝ) + 1) *
          |((aperyB (n + 2) : ℝ) - (∑' k : ℕ, 1 / ((k + 1 : ℝ) ^ 3)) *
             (aperyA (n + 2) : ℝ))|
          * aperyConifoldZ1Inv ^ n
        ≤ aperyG2Comparator K n := by
  obtain ⟨M₀, hM₀, K, hK, hbound⟩ := aperyZetaTail_geom_bound
  refine ⟨M₀, hM₀, K, hK, ?_⟩
  intro n hn
  -- Phase 1 pointwise: |g_{n+2}| · z₁^{n+2} ≤ aperyZetaTail (n+2)
  -- Phase 1 tail: aperyZetaTail (n+2) ≤ K(n+6)/((1-r)²·α^(2n+5))
  -- Multiply by (n+2)(n+1) · z₁^{-2} = (n+2)(n+1) · α²:
  -- (n+2)(n+1)·|g_{n+2}|·z₁^n = (n+2)(n+1)·α²·|g_{n+2}|·z₁^{n+2}
  --                          ≤ (n+2)(n+1)·α²·aperyZetaTail (n+2)
  --                          ≤ (n+2)(n+1)·α²·K(n+6)/((1-r)²·α^(2(n+2)+1))
  --                          = K(n+1)(n+2)(n+6) / ((1-r)²·α^(2n+3))
  --                          = aperyG2Comparator K n
  have hα_pos : 0 < aperyAlpha := aperyAlpha_pos
  have hα_ne : aperyAlpha ≠ 0 := aperyAlpha_ne_zero
  have h1mr_pos : 0 < 1 - aperyR := by
    have := aperyR_lt_one; linarith
  have h1mr_sq_pos : 0 < (1 - aperyR) ^ 2 := by positivity
  have h1mr_sq_ne : (1 - aperyR) ^ 2 ≠ 0 := h1mr_sq_pos.ne'
  -- Need n+2 ≥ M₀ for tail bound at index n+2.
  have hn2_ge : M₀ ≤ n + 2 := le_trans hn (by omega)
  -- Apply Phase 1 pointwise bound at n+2
  have h_pointwise := absDiff_mul_z1_pow_le_tail (n + 2)
  -- Apply Phase 1 tail bound at n+2
  have h_tail := hbound (n + 2) hn2_ge
  have hcast2 : ((n + 2 : ℕ) : ℝ) + 4 = (n : ℝ) + 6 := by push_cast; ring
  rw [hcast2] at h_tail
  have hcast2' : 2 * (n + 2) + 1 = 2 * n + 5 := by omega
  rw [hcast2'] at h_tail
  -- Combine: |g_{n+2}|·z₁^{n+2} ≤ K(n+6)/((1-r)²·α^(2n+5))
  have hbound1 : |((aperyB (n + 2) : ℝ) -
        (∑' k : ℕ, 1 / ((k + 1 : ℝ) ^ 3)) * (aperyA (n + 2) : ℝ))|
        * aperyConifoldZ1Inv ^ (n + 2) ≤
        K * ((n : ℝ) + 6) / ((1 - aperyR) ^ 2 * aperyAlpha ^ (2 * n + 5)) := by
    calc _ ≤ aperyZetaTail (n + 2) := h_pointwise
      _ ≤ _ := by
        have h := h_tail
        -- h : aperyZetaTail (n+2) ≤ K(n+6)/((1-r)²·α^(2n+5))
        have hα_form : (1 - aperyR) ^ 2 * aperyAlpha ^ (2 * n + 5)
            = (1 - aperyR) ^ 2 * aperyAlpha ^ (2 * n + 5) := rfl
        linarith
  -- Now z₁^{n+2} = z₁^n · z₁², so z₁^n = z₁^{n+2} / z₁² = α² · z₁^{n+2}.
  have hz1_pow : aperyConifoldZ1Inv ^ (n + 2) = aperyConifoldZ1Inv ^ n * aperyConifoldZ1Inv ^ 2 := by ring
  have hz1_sq_pos : 0 < aperyConifoldZ1Inv ^ 2 := pow_pos aperyConifoldZ1Inv_pos 2
  have hz1_sq_eq_inv : aperyConifoldZ1Inv ^ 2 = 1 / aperyAlpha ^ 2 := by
    unfold aperyConifoldZ1Inv
    rw [div_pow, one_pow]
  -- Multiply by (n+2)(n+1) and rearrange.
  have hα2_pos : 0 < aperyAlpha ^ 2 := pow_pos hα_pos 2
  have habs_nn := abs_nonneg ((aperyB (n + 2) : ℝ) -
    (∑' k : ℕ, 1 / ((k + 1 : ℝ) ^ 3)) * (aperyA (n + 2) : ℝ))
  have hz1_n_nn : 0 ≤ aperyConifoldZ1Inv ^ n := pow_nonneg aperyConifoldZ1Inv_pos.le n
  have hcoef_nn : 0 ≤ ((n : ℝ) + 2) * ((n : ℝ) + 1) := by positivity
  -- LHS · α²·z₁² ≤ (n+2)(n+1)·α²·K(n+6)/((1-r)²·α^(2n+5)) · z₁²
  -- but α²·z₁² = 1, so LHS ≤ (n+2)(n+1)·K(n+6)·α²/((1-r)²·α^(2n+5)) ·1
  --                    = K(n+1)(n+2)(n+6) / ((1-r)²·α^(2n+3))
  --                    = aperyG2Comparator K n
  unfold aperyG2Comparator
  -- Step: bound (n+2)(n+1)·|g_{n+2}|·z₁^n by K(n+1)(n+2)(n+6)/((1-r)²·α^(2n+3))
  have hα_pow_split : aperyAlpha ^ (2 * n + 5) = aperyAlpha ^ (2 * n + 3) * aperyAlpha ^ 2 := by
    rw [show 2 * n + 5 = (2 * n + 3) + 2 from by omega, pow_add]
  have hz1_n_eq : aperyConifoldZ1Inv ^ n = 1 / aperyAlpha ^ n := by
    unfold aperyConifoldZ1Inv
    rw [div_pow, one_pow]
  have hz1_pow_simplify : aperyConifoldZ1Inv ^ (n + 2) = 1 / aperyAlpha ^ (n + 2) := by
    unfold aperyConifoldZ1Inv
    rw [div_pow, one_pow]
  -- Easier: let c := aperyConifoldZ1Inv, then c² = 1/α², c^(n+2) = c^n · c² = c^n / α².
  -- (n+2)(n+1)·|g|·c^n = (n+2)(n+1)·|g|·c^(n+2)·α²
  -- ≤ (n+2)(n+1)·α²·K(n+6)/((1-r)²·α^(2n+5))
  -- = K(n+1)(n+2)(n+6)·α² / ((1-r)²·α^(2n+5))
  -- = K(n+1)(n+2)(n+6) / ((1-r)²·α^(2n+3))  via α²·α^(2n+3) = α^(2n+5)
  have hgoal_aux :
      ((n : ℝ) + 2) * ((n : ℝ) + 1) *
        |((aperyB (n + 2) : ℝ) -
          (∑' k : ℕ, 1 / ((k + 1 : ℝ) ^ 3)) * (aperyA (n + 2) : ℝ))|
        * aperyConifoldZ1Inv ^ n
        ≤ ((n : ℝ) + 2) * ((n : ℝ) + 1) * aperyAlpha ^ 2 *
          (K * ((n : ℝ) + 6) / ((1 - aperyR) ^ 2 * aperyAlpha ^ (2 * n + 5))) := by
    have hexpand : ((n : ℝ) + 2) * ((n : ℝ) + 1) *
        |((aperyB (n + 2) : ℝ) -
          (∑' k : ℕ, 1 / ((k + 1 : ℝ) ^ 3)) * (aperyA (n + 2) : ℝ))|
        * aperyConifoldZ1Inv ^ n
      = ((n : ℝ) + 2) * ((n : ℝ) + 1) * aperyAlpha ^ 2 *
        (|((aperyB (n + 2) : ℝ) -
          (∑' k : ℕ, 1 / ((k + 1 : ℝ) ^ 3)) * (aperyA (n + 2) : ℝ))|
          * aperyConifoldZ1Inv ^ (n + 2)) := by
      rw [hz1_pow_simplify, hz1_n_eq]
      have hα_pow_simp : aperyAlpha ^ (n + 2) = aperyAlpha ^ n * aperyAlpha ^ 2 := by
        rw [pow_add]
      rw [hα_pow_simp]
      have hα_pow_n_pos : 0 < aperyAlpha ^ n := pow_pos hα_pos n
      have hα_pow_2_pos : 0 < aperyAlpha ^ 2 := hα2_pos
      field_simp
    rw [hexpand]
    have hcoef_α_nn : 0 ≤ ((n : ℝ) + 2) * ((n : ℝ) + 1) * aperyAlpha ^ 2 := by
      have := hα2_pos; positivity
    exact mul_le_mul_of_nonneg_left hbound1 hcoef_α_nn
  -- Now simplify the RHS:
  -- (n+2)(n+1)·α²·K(n+6) / ((1-r)²·α^(2n+5))
  -- = K(n+1)(n+2)(n+6)·α² / ((1-r)²·α^(2n+5))
  -- = K(n+1)(n+2)(n+6) / ((1-r)²·α^(2n+3))  via α² cancels with α^(2n+5)→α^(2n+3)
  have hrhs_simplify :
      ((n : ℝ) + 2) * ((n : ℝ) + 1) * aperyAlpha ^ 2 *
        (K * ((n : ℝ) + 6) / ((1 - aperyR) ^ 2 * aperyAlpha ^ (2 * n + 5)))
      = K * ((n : ℝ) + 1) * ((n : ℝ) + 2) * ((n : ℝ) + 6) /
          ((1 - aperyR) ^ 2 * aperyAlpha ^ (2 * n + 3)) := by
    rw [hα_pow_split]
    have hα2n3_pos : 0 < aperyAlpha ^ (2 * n + 3) := pow_pos hα_pos _
    field_simp
  rw [hrhs_simplify] at hgoal_aux
  exact hgoal_aux

/-- The differentiated numerator series is summable at `z = z₁`. -/
theorem aperyG2_summable_at_z1 :
    Summable (fun n : ℕ =>
      ((n : ℝ) + 2) * ((n : ℝ) + 1) *
        |((aperyB (n + 2) : ℝ) -
          (∑' k : ℕ, 1 / ((k + 1 : ℝ) ^ 3)) * (aperyA (n + 2) : ℝ))|
        * aperyConifoldZ1Inv ^ n) := by
  obtain ⟨M₀, _, K, hK, hbound⟩ := aperyG2_term_le_comparator
  refine Summable.of_norm_bounded_eventually
    (g := aperyG2Comparator K) (aperyG2Comparator_summable K) ?_
  rw [Nat.cofinite_eq_atTop]
  refine Filter.eventually_atTop.mpr ⟨M₀, ?_⟩
  intro n hn
  rw [Real.norm_eq_abs]
  have hf_nn :
      0 ≤ ((n : ℝ) + 2) * ((n : ℝ) + 1) *
        |((aperyB (n + 2) : ℝ) -
          (∑' k : ℕ, 1 / ((k + 1 : ℝ) ^ 3)) * (aperyA (n + 2) : ℝ))|
        * aperyConifoldZ1Inv ^ n := by
    have h1 : 0 ≤ ((n : ℝ) + 2) * ((n : ℝ) + 1) := by positivity
    have h2 : 0 ≤ |((aperyB (n + 2) : ℝ) -
      (∑' k : ℕ, 1 / ((k + 1 : ℝ) ^ 3)) * (aperyA (n + 2) : ℝ))| := abs_nonneg _
    have h3 : 0 ≤ aperyConifoldZ1Inv ^ n := pow_nonneg aperyConifoldZ1Inv_pos.le n
    positivity
  rw [abs_of_nonneg hf_nn]
  exact hbound n hn

end Ripple.Number
