/-
  Ripple.Number.Frobenius.AperyZetaSum

  Telescoping consequences of the Apéry cross-product identity.

  Phase 1.2 of the F5 connection-coefficient discharge.

  Main results:

  * `aperyB_aperyA_ratio_diff` : the consecutive ratio difference equals
      `b_n / a_n − b_{n−1} / a_{n−1} = 6 / (n^3 · a_n · a_{n−1})`.

  * `aperyB_div_aperyA_eq_partial_sum` : the partial sum is the ratio
      `b_n / a_n = ∑_{m = 1}^{n} 6 / (m^3 · a_m · a_{m−1})`.

  * `aperyZeta3_eq_tsum` : Apéry's classical series representation
      `ζ(3) = ∑_{m = 1}^{∞} 6 / (m^3 · a_m · a_{m−1})`.

  Phase 1.3 (next file) uses this to bound `|b_n − ζ(3) · a_n|` and
  derive analytic continuation of `B(z) − ζ(3) · A(z)` past `z = z₁`.
-/

import Ripple.Number.Frobenius.AperyCrossProduct

namespace Ripple.Number

open Finset

/-- Step 1: dividing the cross-product identity by `a_n · a_{n-1}` gives
    the ratio difference. -/
lemma aperyB_aperyA_ratio_diff (n : ℕ) (hn : 1 ≤ n) :
    aperyB n / (aperyA n : ℚ) - aperyB (n - 1) / (aperyA (n - 1) : ℚ)
      = 6 / ((n : ℚ) ^ 3 * (aperyA n : ℚ) * (aperyA (n - 1) : ℚ)) := by
  have hAn_pos : 0 < (aperyA n : ℚ) := by exact_mod_cast aperyA_pos n
  have hAn1_pos : 0 < (aperyA (n - 1) : ℚ) := by exact_mod_cast aperyA_pos (n - 1)
  have hn_pos : (0 : ℚ) < (n : ℚ) := by exact_mod_cast hn
  have hn3_pos : (0 : ℚ) < (n : ℚ) ^ 3 := by positivity
  have hAn_ne : (aperyA n : ℚ) ≠ 0 := hAn_pos.ne'
  have hAn1_ne : (aperyA (n - 1) : ℚ) ≠ 0 := hAn1_pos.ne'
  have hn3_ne : (n : ℚ) ^ 3 ≠ 0 := hn3_pos.ne'
  -- Cross-product identity:
  --   n³ · (a_{n-1} · b_n − a_n · b_{n-1}) = 6
  have hcross := aperyAB_cross_product n hn
  -- Combine into ratio form.
  field_simp
  linarith [hcross]

/-- Step 2: `b_n / a_n = b_0 / a_0 + ∑_{m = 1}^n 6 / (m^3 · a_m · a_{m-1})`,
    and since `b_0 = 0`, this gives the partial-sum form. -/
lemma aperyB_div_aperyA_eq_partial_sum (n : ℕ) :
    aperyB n / (aperyA n : ℚ)
      = ∑ m ∈ range n,
          6 / (((m + 1 : ℕ) : ℚ) ^ 3 *
            (aperyA (m + 1) : ℚ) * (aperyA m : ℚ)) := by
  induction n with
  | zero =>
      simp [aperyB_zero]
  | succ n ih =>
      rw [Finset.sum_range_succ]
      have hcurrent : aperyB n / (aperyA n : ℚ)
          = ∑ m ∈ range n,
              6 / (((m + 1 : ℕ) : ℚ) ^ 3 *
                (aperyA (m + 1) : ℚ) * (aperyA m : ℚ)) := ih
      have hdiff := aperyB_aperyA_ratio_diff (n + 1) (by omega)
      have hsimp : (n + 1 : ℕ) - 1 = n := by omega
      rw [hsimp] at hdiff
      have hpush : ((n + 1 : ℕ) : ℚ) = (n : ℚ) + 1 := by push_cast; ring
      have hpush' : ((n + 1 : ℕ) : ℚ) ^ 3 = ((n : ℚ) + 1) ^ 3 := by rw [hpush]
      -- Goal: B(n+1)/A(n+1) = sum + 6/((n+1)^3 · A(n+1) · A(n))
      linarith [hdiff]

/-- The summand of the Apéry telescoped series. -/
noncomputable def aperyZetaSummand (m : ℕ) : ℝ :=
  6 / (((m + 1 : ℕ) : ℝ) ^ 3 *
    (aperyA (m + 1) : ℝ) * (aperyA m : ℝ))

/-- Each summand is non-negative. -/
lemma aperyZetaSummand_nonneg (m : ℕ) : 0 ≤ aperyZetaSummand m := by
  unfold aperyZetaSummand
  have h1 : 0 < (((m + 1 : ℕ) : ℝ) ^ 3) := by positivity
  have h2 : 0 < (aperyA (m + 1) : ℝ) := by exact_mod_cast aperyA_pos (m + 1)
  have h3 : 0 < (aperyA m : ℝ) := by exact_mod_cast aperyA_pos m
  positivity

/-- Real version of the partial-sum identity. -/
lemma aperyB_div_aperyA_real_eq_partial_sum (n : ℕ) :
    (aperyB n : ℝ) / (aperyA n : ℝ)
      = ∑ m ∈ range n, aperyZetaSummand m := by
  have hQ := aperyB_div_aperyA_eq_partial_sum n
  have hcast :
      ((aperyB n / (aperyA n : ℚ) : ℚ) : ℝ)
        = (aperyB n : ℝ) / (aperyA n : ℝ) := by
    push_cast; rfl
  have hQR : (aperyB n : ℝ) / (aperyA n : ℝ)
      = ((∑ m ∈ range n,
          6 / (((m + 1 : ℕ) : ℚ) ^ 3 *
            (aperyA (m + 1) : ℚ) * (aperyA m : ℚ)) : ℚ) : ℝ) := by
    rw [← hcast, hQ]
  rw [hQR]
  push_cast
  apply Finset.sum_congr rfl
  intro m _
  unfold aperyZetaSummand
  push_cast
  ring

/-- Apéry's series representation as a partial-sum convergence.

    Partial sums `∑_{m=0}^{n-1} 6 / ((m+1)^3 · a_{m+1} · a_m)` converge to
    `ζ(3) = ∑'(1/(k+1)^3)`.  This is the tendsto-form of the classical
    Apéry telescoping identity, derived from
    `aperyB_div_aperyA_tendsto_zeta3` (sequence-level, AperySequences.lean). -/
theorem aperyZeta3_partial_sum_tendsto :
    Filter.Tendsto (fun n : ℕ => ∑ m ∈ range n, aperyZetaSummand m)
      Filter.atTop
      (nhds (∑' k : ℕ, 1 / ((k + 1 : ℝ) ^ 3))) := by
  have htend := aperyB_div_aperyA_tendsto_zeta3
  have heq : ∀ n : ℕ, ∑ m ∈ range n, aperyZetaSummand m
      = (aperyB n : ℝ) / (aperyA n : ℝ) := by
    intro n
    exact (aperyB_div_aperyA_real_eq_partial_sum n).symm
  simp_rw [heq]
  exact htend

end Ripple.Number
