import Ripple.Number.Frobenius.AperySummandBound

namespace Ripple.Number

/-- `aperyAlpha = (1 + sqrt 2)^4` in the closed conifold form. -/
lemma aperyAlpha_eq_conifold :
    aperyAlpha = 17 + 12 * Real.sqrt 2 := by
  simpa [aperyAlpha] using aperyA_dominant_lambda_eq

/-- Characteristic equation for the dominant Apéry growth rate. -/
private lemma aperyAlpha_sq : aperyAlpha ^ 2 = 34 * aperyAlpha - 1 := by
  rw [aperyAlpha_eq_conifold]
  have hsq : Real.sqrt 2 ^ 2 = 2 :=
    Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  nlinarith [hsq]

private lemma five_le_aperyAlpha : (5 : ℝ) ≤ aperyAlpha := by
  rw [aperyAlpha_eq_conifold]
  linarith [Real.sqrt_nonneg 2]

/-- One-step ratio bound for the Apéry numbers: `a_{n+1} ≤ α a_n`. -/
private lemma aperyA_ratio_le_aperyAlpha (n : ℕ) :
    (aperyA (n + 1) : ℝ) ≤ aperyAlpha * (aperyA n : ℝ) := by
  match n with
  | 0 =>
      simp [aperyA_zero, aperyA_one]
      exact five_le_aperyAlpha
  | n + 1 =>
      have h_rec := aperyA_recurrence (n + 1) (by omega)
      have h_sub_simp : (n + 1 : ℕ) - 1 = n := by omega
      rw [h_sub_simp] at h_rec
      have h_rec_real : ((n + 2 : ℝ)) ^ 3 * (aperyA (n + 2) : ℝ)
          = (2 * ((n : ℝ) + 1) + 1) * (17 * ((n : ℝ) + 1) ^ 2
            + 17 * ((n : ℝ) + 1) + 5) * (aperyA (n + 1) : ℝ)
            - ((n : ℝ) + 1) ^ 3 * (aperyA n : ℝ) := by
        exact_mod_cast h_rec
      have h_ih := aperyA_ratio_le_aperyAlpha n
      have h_lower : (aperyA (n + 1) : ℝ) / aperyAlpha ≤
          (aperyA n : ℝ) := by
        rw [div_le_iff₀ aperyAlpha_pos]
        linarith [h_ih]
      set m := n + 1
      set coeff : ℝ :=
        (2 * (m : ℝ) + 1) * (17 * (m : ℝ) ^ 2 + 17 * m + 5)
        with hcoeff_def
      have h_key : coeff * (aperyA m : ℝ) - (m : ℝ) ^ 3 *
          ((aperyA m : ℝ) / aperyAlpha) ≤
          ((m : ℝ) + 1) ^ 3 * (aperyAlpha * (aperyA m : ℝ)) := by
        have h_am_pos : (0 : ℝ) < (aperyA m : ℝ) := by
          exact_mod_cast aperyA_pos m
        rw [show ((m : ℝ) + 1) ^ 3 * (aperyAlpha * (aperyA m : ℝ)) =
          (aperyA m : ℝ) * (((m : ℝ) + 1) ^ 3 * aperyAlpha) from by ring]
        rw [show coeff * (aperyA m : ℝ) - (m : ℝ) ^ 3 *
          ((aperyA m : ℝ) / aperyAlpha) =
          (aperyA m : ℝ) * (coeff - (m : ℝ) ^ 3 / aperyAlpha) from by
            rw [mul_div_assoc']; ring]
        refine mul_le_mul_of_nonneg_left ?_ h_am_pos.le
        rw [sub_div' aperyAlpha_ne_zero]
        rw [div_le_iff₀ aperyAlpha_pos]
        have : (↑m + 1) ^ 3 * aperyAlpha * aperyAlpha =
            (↑m + 1) ^ 3 * (34 * aperyAlpha - 1) := by
          rw [← aperyAlpha_sq]
          ring
        rw [this]
        nlinarith [aperyAlpha_ge_one, sq_nonneg (m : ℝ)]
      have h_upper : ((m : ℝ) + 1) ^ 3 * (aperyA (m + 1) : ℝ) ≤
          ((m : ℝ) + 1) ^ 3 * (aperyAlpha * (aperyA m : ℝ)) := by
        calc
          ((m : ℝ) + 1) ^ 3 * (aperyA (m + 1) : ℝ)
              = coeff * (aperyA m : ℝ) - (m : ℝ) ^ 3 * (aperyA n : ℝ) := by
                have h_m_eq : (↑m : ℝ) + 1 = ↑n + 2 := by
                  show (↑(n + 1) : ℝ) + 1 = ↑n + 2
                  push_cast
                  ring
                have h_m_eq_nat : m + 1 = n + 2 := by
                  show (n + 1) + 1 = n + 2
                  omega
                rw [h_m_eq, h_m_eq_nat]
                rw [hcoeff_def]
                show (↑n + 2) ^ 3 * (aperyA (n + 2) : ℝ) =
                  (2 * ↑m + 1) * (17 * ↑m ^ 2 + 17 * ↑m + 5) *
                    (aperyA m : ℝ) - ↑m ^ 3 * (aperyA n : ℝ)
                have hm_eq_real : (↑m : ℝ) = ↑n + 1 := by
                  show (↑(n + 1) : ℝ) = ↑n + 1
                  push_cast
                  ring
                rw [hm_eq_real]
                exact h_rec_real
          _ ≤ coeff * (aperyA m : ℝ) - (m : ℝ) ^ 3 *
              ((aperyA m : ℝ) / aperyAlpha) := by
                refine sub_le_sub_left ?_ _
                refine mul_le_mul_of_nonneg_left h_lower ?_
                positivity
          _ ≤ ((m : ℝ) + 1) ^ 3 * (aperyAlpha * (aperyA m : ℝ)) := h_key
      have h_pos_cube : (0 : ℝ) < ((m : ℝ) + 1) ^ 3 := by positivity
      exact le_of_mul_le_mul_left h_upper h_pos_cube

/-- Sharp geometric upper bound for Apéry's `a_n` sequence. -/
theorem aperyA_le_aperyAlpha_pow (n : ℕ) :
    (aperyA n : ℝ) ≤ aperyAlpha ^ n := by
  induction n with
  | zero =>
      simp [aperyA_zero]
  | succ n ih =>
      calc
        (aperyA (n + 1) : ℝ)
            ≤ aperyAlpha * (aperyA n : ℝ) := aperyA_ratio_le_aperyAlpha n
        _ ≤ aperyAlpha * aperyAlpha ^ n :=
            mul_le_mul_of_nonneg_left ih aperyAlpha_pos.le
        _ = aperyAlpha ^ (n + 1) := by
            rw [pow_succ]
            ring

end Ripple.Number
