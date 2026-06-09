import Mathlib.Tactic

namespace ExactMajority

/-- 
  Arithmetic Helper: For n ≥ 8, n * (n - 1) > 0 in ℝ. 
  Used to prove strict positivity of DescentKernel interaction probabilities.
-/
lemma mul_sub_one_pos_of_ge_eight (n : ℕ) (hn : 8 ≤ n) : 
    (0 : ℝ) < (n : ℝ) * ((n : ℝ) - 1) := by
  have h_n_pos : (0 : ℝ) < ↑n := by
    exact_mod_cast lt_of_lt_of_le (by decide : 0 < 8) hn
  have h_n_sub_pos : (0 : ℝ) < ↑n - 1 := by
    apply sub_pos.mpr
    exact_mod_cast lt_of_lt_of_le (by decide : 1 < 8) hn
  exact mul_pos h_n_pos h_n_sub_pos

/-- 
  Arithmetic Helper: For n ≥ 8, 2 / (n * (n - 1)) > 0 in ℝ. 
  Used to close the `hp_pos` strict positivity requirement in DescentKernel.
-/
lemma div_mul_sub_one_pos_of_ge_eight (n : ℕ) (hn : 8 ≤ n) : 
    (0 : ℝ) < 2 / ((n : ℝ) * ((n : ℝ) - 1)) := by
  exact div_pos zero_lt_two (mul_sub_one_pos_of_ge_eight n hn)

/-- 
  Arithmetic Helper: For n ≥ 8, 2 / (n * (n - 1)) ≥ 0 in ℝ. 
  Used to satisfy the non-negativity constraint when coercing to `ℝ≥0`.
-/
lemma div_mul_sub_one_nonneg_of_ge_eight (n : ℕ) (hn : 8 ≤ n) : 
    (0 : ℝ) ≤ 2 / ((n : ℝ) * ((n : ℝ) - 1)) := by
  exact (div_mul_sub_one_pos_of_ge_eight n hn).le

end ExactMajority
