/-
  Ripple.Number.Frobenius.AperyAbsConvergentAtZ1

  Phase 1.4 wrapper: ∑ (b_n − ζ(3)·a_n) · z^n converges absolutely at
  `z = z₁`. This makes the formal series for `B(z) − ζ(3)·A(z)` converge
  on the closed disk `|z| ≤ z₁`, the first analytic continuation result
  past the conifold (Apéry's "regular and vanishes at z₁" of vdPoorten p203).

  Strategy:
    - pointwise bound |b_n − ζ(3)·a_n| · z₁^n ≤ aperyZetaTail n   (Phase 1.4a)
    - tail bound aperyZetaTail n ≤ K(n+4) / ((1-r)²·α^(2n+1))      (Phase 1.4b)
    - the comparator is poly × geometric, summable in n
    - ⇒ Summable n ↦ |b_n − ζ(3)·a_n| · z₁^n
-/

import Ripple.Number.Frobenius.AperyTailGeometric

namespace Ripple.Number

open Filter

/-- The summable comparator for `aperyZetaTail`, with the `(1-r)²` factor:
    `K · (n+4) / ((1-r)² · α^(2n+1))`. -/
noncomputable def aperyZetaTailComparator (K : ℝ) (n : ℕ) : ℝ :=
  K * ((n : ℝ) + 4) / ((1 - aperyR) ^ 2 * aperyAlpha ^ (2 * n + 1))

/-- The comparator is summable. Just a constant multiple of
`aperyZetaUpperBound K n` (which we already proved summable). -/
lemma aperyZetaTailComparator_summable (K : ℝ) :
    Summable (aperyZetaTailComparator K) := by
  have hr_pos : 0 < aperyR := aperyR_pos
  have hr_lt : aperyR < 1 := aperyR_lt_one
  have h1mr_pos : 0 < 1 - aperyR := by linarith
  have h1mr_sq_pos : 0 < (1 - aperyR) ^ 2 := by positivity
  have h1mr_sq_ne : (1 - aperyR) ^ 2 ≠ 0 := h1mr_sq_pos.ne'
  -- aperyZetaTailComparator K n = aperyZetaUpperBound K n / (1-r)²
  have heq : aperyZetaTailComparator K
      = fun n => aperyZetaUpperBound K n / (1 - aperyR) ^ 2 := by
    funext n
    unfold aperyZetaTailComparator aperyZetaUpperBound
    field_simp
  rw [heq]
  exact (aperyZetaUpperBound_summable K).div_const _

/-- |b_n − ζ(3)·a_n| · z₁^n is summable: the formal series for
`B(z) − ζ(3)·A(z)` converges absolutely at `z = z₁`. -/
theorem aperyB_minus_zeta3_aperyA_absSummable_at_z1 :
    Summable (fun n : ℕ =>
      |((aperyB n : ℝ) - (∑' k : ℕ, 1 / ((k + 1 : ℝ) ^ 3)) * (aperyA n : ℝ))|
        * aperyConifoldZ1Inv ^ n) := by
  obtain ⟨M₀, _, K, hK, hbound⟩ := aperyZetaTail_geom_bound
  -- Comparator: aperyZetaTailComparator K
  refine Summable.of_norm_bounded_eventually
    (g := aperyZetaTailComparator K) (aperyZetaTailComparator_summable K) ?_
  -- For ℕ, cofinite = atTop.
  rw [Nat.cofinite_eq_atTop]
  refine Filter.eventually_atTop.mpr ⟨M₀, ?_⟩
  intro n hn
  -- f n = |b_n - ζ(3)·a_n| · z₁^n
  -- ≤ aperyZetaTail n  (pointwise bound)
  -- ≤ K(n+4)/((1-r)²·α^(2n+1)) = aperyZetaTailComparator K n  (tail bound)
  have h1 := absDiff_mul_z1_pow_le_tail n
  have h2 := hbound n hn
  have hf_nn :
      0 ≤ |((aperyB n : ℝ) - (∑' k : ℕ, 1 / ((k + 1 : ℝ) ^ 3)) * (aperyA n : ℝ))|
        * aperyConifoldZ1Inv ^ n :=
    mul_nonneg (abs_nonneg _) (pow_nonneg aperyConifoldZ1Inv_pos.le n)
  rw [Real.norm_eq_abs, abs_of_nonneg hf_nn]
  unfold aperyZetaTailComparator
  linarith

end Ripple.Number
