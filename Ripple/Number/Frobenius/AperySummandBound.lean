/-
  Ripple.Number.Frobenius.AperySummandBound

  Phase 1.3b: per-term geometric bound for `aperyZetaSummand`.

  Using `aperyA_asymptotic_lower_bound` (a_n ≥ C·α^n/(n+1)^2 for n ≥ M₀,
  with α = (1+√2)^4), we derive:

      ∀ m ≥ M₀,  aperyZetaSummand m  ≤  (6 / C^2) * (m + 4) / α^(2m + 1)

  This is a per-term bound; tail summation in `AperyTailGeometric.lean`
  (next file) sums it geometrically.
-/

import Ripple.Number.Frobenius.AperyTailBound

namespace Ripple.Number

open Filter

/-- The Apéry conifold conjugate ratio `α = (1+√2)^4 = 17 + 12√2`. -/
noncomputable def aperyAlpha : ℝ := (1 + Real.sqrt 2) ^ 4

lemma aperyAlpha_pos : 0 < aperyAlpha := by
  unfold aperyAlpha; positivity

lemma aperyAlpha_ne_zero : aperyAlpha ≠ 0 := aperyAlpha_pos.ne'

lemma aperyAlpha_ge_one : 1 ≤ aperyAlpha := by
  unfold aperyAlpha
  have h : (0 : ℝ) ≤ Real.sqrt 2 := Real.sqrt_nonneg _
  have h1 : 1 ≤ 1 + Real.sqrt 2 := by linarith
  exact one_le_pow₀ h1

/-- Repackage `aperyA_asymptotic_lower_bound` with `aperyAlpha^n` instead
of `(1+√2)^(4n)`. -/
lemma aperyA_lower_bound_alpha :
    ∃ M₀ : ℕ, 1 ≤ M₀ ∧ ∃ C : ℝ, 0 < C ∧ ∀ n, M₀ ≤ n →
      (aperyA n : ℝ) ≥ C * aperyAlpha ^ n / (((n : ℝ) + 1) ^ 2) := by
  obtain ⟨M₀, hM₀, C, hC_pos, hbound⟩ := aperyA_asymptotic_lower_bound
  refine ⟨M₀, hM₀, C, hC_pos, ?_⟩
  intro n hn
  have h := hbound n hn
  have hpow : (1 + Real.sqrt 2 : ℝ) ^ (4 * n) = aperyAlpha ^ n := by
    unfold aperyAlpha
    rw [← pow_mul, mul_comm]
  rw [hpow] at h
  exact h

/-- Per-term geometric bound: for sufficiently large `m`,

    `aperyZetaSummand m ≤ (6 / C^2) · (m+4) / α^{2m+1}`.

This converts the polynomial-growth lower bound on `aperyA` into a
quantitative geometric upper bound on each summand of the Apéry zeta
series. -/
theorem aperyZetaSummand_geom_bound :
    ∃ M₀ : ℕ, 1 ≤ M₀ ∧ ∃ K : ℝ, 0 < K ∧
      ∀ m : ℕ, M₀ ≤ m →
        aperyZetaSummand m ≤ K * ((m : ℝ) + 4) / aperyAlpha ^ (2 * m + 1) := by
  obtain ⟨M₀, hM₀, C, hC, hAbound⟩ := aperyA_lower_bound_alpha
  refine ⟨M₀, hM₀, 6 / C ^ 2, by positivity, ?_⟩
  intro m hm
  unfold aperyZetaSummand
  have hα_pos : 0 < aperyAlpha := aperyAlpha_pos
  have hα_pow_pos : ∀ k : ℕ, 0 < aperyAlpha ^ k := fun k => pow_pos hα_pos k
  -- a_m and a_{m+1} lower bounds.
  have hAm_pos : 0 < (aperyA m : ℝ) := by exact_mod_cast aperyA_pos m
  have hAm1_pos : 0 < (aperyA (m + 1) : ℝ) := by exact_mod_cast aperyA_pos (m + 1)
  have hm_succ_ge_M0 : M₀ ≤ m + 1 := le_trans hm (Nat.le_succ m)
  have hAm_lower : (aperyA m : ℝ) ≥ C * aperyAlpha ^ m / (((m : ℝ) + 1) ^ 2) :=
    hAbound m hm
  have hAm1_lower : (aperyA (m + 1) : ℝ) ≥
      C * aperyAlpha ^ (m + 1) / ((((m + 1 : ℕ) : ℝ) + 1) ^ 2) :=
    hAbound (m + 1) hm_succ_ge_M0
  have hcast : ((m + 1 : ℕ) : ℝ) + 1 = (m : ℝ) + 2 := by push_cast; ring
  rw [hcast] at hAm1_lower
  -- Helper positives.
  have hm_pos : (0 : ℝ) ≤ (m : ℝ) := by exact_mod_cast Nat.zero_le m
  have hm1_pos : (0 : ℝ) < (m : ℝ) + 1 := by linarith
  have hm2_pos : (0 : ℝ) < (m : ℝ) + 2 := by linarith
  have hm1_sq_pos : (0 : ℝ) < ((m : ℝ) + 1) ^ 2 := by positivity
  have hm2_sq_pos : (0 : ℝ) < ((m : ℝ) + 2) ^ 2 := by positivity
  -- Combine: a_m * a_{m+1} ≥ C^2 * α^{2m+1} / ((m+1)^2 (m+2)^2).
  have hprod_lower : (aperyA m : ℝ) * (aperyA (m + 1) : ℝ) ≥
      C ^ 2 * aperyAlpha ^ (2 * m + 1) / (((m : ℝ) + 1) ^ 2 * ((m : ℝ) + 2) ^ 2) := by
    have hLeft : C * aperyAlpha ^ m / (((m : ℝ) + 1) ^ 2) *
        (C * aperyAlpha ^ (m + 1) / (((m : ℝ) + 2) ^ 2))
      = C ^ 2 * aperyAlpha ^ (2 * m + 1) /
          (((m : ℝ) + 1) ^ 2 * ((m : ℝ) + 2) ^ 2) := by
      have hpow_combine : aperyAlpha ^ m * aperyAlpha ^ (m + 1) = aperyAlpha ^ (2 * m + 1) := by
        rw [← pow_add]
        congr 1
        ring
      field_simp
      linear_combination (((m : ℝ) + 1)^2 * ((m : ℝ) + 2)^2) * hpow_combine
    rw [← hLeft]
    have hpos' : 0 ≤ C * aperyAlpha ^ (m + 1) / (((m : ℝ) + 2) ^ 2) :=
      div_nonneg (mul_nonneg hC.le (hα_pow_pos (m + 1)).le) hm2_sq_pos.le
    exact mul_le_mul hAm_lower hAm1_lower hpos' hAm_pos.le
  -- Bound 6 / ((m+1)^3 · a_m · a_{m+1}).
  -- ≤ 6 · ((m+1)^2 (m+2)^2) / ((m+1)^3 · C^2 · α^{2m+1})
  -- = 6 · (m+2)^2 / ((m+1) · C^2 · α^{2m+1})
  -- ≤ 6 · (m+4) / (C^2 · α^{2m+1})  using (m+2)^2 ≤ (m+1)(m+4) for m ≥ 0
  have hα_pow_pos' : 0 < aperyAlpha ^ (2 * m + 1) := hα_pow_pos _
  have hC_sq_pos : 0 < C ^ 2 := by positivity
  have hm1_cube_pos : (0 : ℝ) < ((m : ℝ) + 1) ^ 3 := by positivity
  -- denom_RHS lower bound:
  have hdenom_lower : ((m : ℝ) + 1) ^ 3 * ((aperyA m : ℝ) * (aperyA (m + 1) : ℝ)) ≥
      ((m : ℝ) + 1) ^ 3 * (C ^ 2 * aperyAlpha ^ (2 * m + 1) /
        (((m : ℝ) + 1) ^ 2 * ((m : ℝ) + 2) ^ 2)) := by
    exact mul_le_mul_of_nonneg_left hprod_lower hm1_cube_pos.le
  have hsimp_denom : ((m : ℝ) + 1) ^ 3 * (C ^ 2 * aperyAlpha ^ (2 * m + 1) /
        (((m : ℝ) + 1) ^ 2 * ((m : ℝ) + 2) ^ 2))
      = ((m : ℝ) + 1) * C ^ 2 * aperyAlpha ^ (2 * m + 1) / ((m : ℝ) + 2) ^ 2 := by
    field_simp
  rw [hsimp_denom] at hdenom_lower
  -- Now have: (m+1)^3 · A_m · A_{m+1} ≥ (m+1) · C² · α^{2m+1} / (m+2)²
  -- ⇒ 6 / ((m+1)^3 · A_m · A_{m+1}) ≤ 6 · (m+2)² / ((m+1) · C² · α^{2m+1})
  have hLHS_pos : 0 < ((m : ℝ) + 1) ^ 3 * ((aperyA m : ℝ) * (aperyA (m + 1) : ℝ)) := by
    positivity
  have hRHS_lower_pos : 0 < ((m : ℝ) + 1) * C ^ 2 * aperyAlpha ^ (2 * m + 1) /
      ((m : ℝ) + 2) ^ 2 := by positivity
  have hbound1 : 6 / (((m : ℝ) + 1) ^ 3 * ((aperyA m : ℝ) * (aperyA (m + 1) : ℝ))) ≤
      6 / (((m : ℝ) + 1) * C ^ 2 * aperyAlpha ^ (2 * m + 1) / ((m : ℝ) + 2) ^ 2) :=
    div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 6) hRHS_lower_pos hdenom_lower
  -- Simplify RHS:
  have hsimp_rhs : 6 / (((m : ℝ) + 1) * C ^ 2 * aperyAlpha ^ (2 * m + 1) / ((m : ℝ) + 2) ^ 2)
      = 6 * ((m : ℝ) + 2) ^ 2 / (((m : ℝ) + 1) * C ^ 2 * aperyAlpha ^ (2 * m + 1)) := by
    field_simp
  rw [hsimp_rhs] at hbound1
  -- Now bound (m+2)² / (m+1) ≤ (m+4):  (m+2)² ≤ (m+1)(m+4) iff m² + 4m + 4 ≤ m² + 5m + 4
  -- iff 0 ≤ m, always true.
  have hmsq : ((m : ℝ) + 2) ^ 2 ≤ ((m : ℝ) + 1) * ((m : ℝ) + 4) := by nlinarith [hm_pos]
  have hbound2 : 6 * ((m : ℝ) + 2) ^ 2 / (((m : ℝ) + 1) * C ^ 2 * aperyAlpha ^ (2 * m + 1)) ≤
      6 * (((m : ℝ) + 1) * ((m : ℝ) + 4)) /
        (((m : ℝ) + 1) * C ^ 2 * aperyAlpha ^ (2 * m + 1)) := by
    apply div_le_div_of_nonneg_right
    · linarith [hmsq]
    · positivity
  -- Final: 6·(m+1)(m+4) / ((m+1) C² α^{2m+1}) = 6·(m+4) / (C² α^{2m+1}) = (6/C²)·(m+4)/α^{2m+1}
  have hsimp_final : 6 * (((m : ℝ) + 1) * ((m : ℝ) + 4)) /
        (((m : ℝ) + 1) * C ^ 2 * aperyAlpha ^ (2 * m + 1))
      = 6 / C ^ 2 * ((m : ℝ) + 4) / aperyAlpha ^ (2 * m + 1) := by
    field_simp
  rw [hsimp_final] at hbound2
  -- combine the chain. Need to align casts: ↑(m+1) vs (↑m + 1).
  have hcast_eq : ((m + 1 : ℕ) : ℝ) = (m : ℝ) + 1 := by push_cast; ring
  have hgroup : (((m + 1 : ℕ) : ℝ) ^ 3 * (aperyA (m + 1) : ℝ) * (aperyA m : ℝ))
      = (((m : ℝ) + 1) ^ 3 * ((aperyA m : ℝ) * (aperyA (m + 1) : ℝ))) := by
    rw [hcast_eq]; ring
  rw [hgroup]
  exact le_trans hbound1 hbound2

end Ripple.Number
