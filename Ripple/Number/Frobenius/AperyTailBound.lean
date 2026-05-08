/-
  Ripple.Number.Frobenius.AperyTailBound

  Phase 1.3a: exact identity for the difference `b_n − ζ(3) · a_n`.

  From the telescoped Apéry series:

      ζ(3) − b_n / a_n = ∑'_{m ≥ n}  aperyZetaSummand m

  Multiplying both sides by `a_n` gives the exact identity

      ζ(3) · a_n − b_n = a_n · ∑'_{m ≥ n}  aperyZetaSummand m

  This is Phase 1.3a; Phase 1.3b will bound the tail sum geometrically using
  `aperyA_asymptotic_lower_bound` to derive `|b_n − ζ(3) a_n| ≤ K n / α^n`.
-/

import Ripple.Number.Frobenius.AperyZetaSum

namespace Ripple.Number

open Filter Finset

/-- The summand sequence has sum equal to `ζ(3)` (HasSum form). -/
theorem aperyZetaSummand_hasSum :
    HasSum aperyZetaSummand (∑' k : ℕ, 1 / ((k + 1 : ℝ) ^ 3)) :=
  (hasSum_iff_tendsto_nat_of_nonneg aperyZetaSummand_nonneg _).mpr
    aperyZeta3_partial_sum_tendsto

/-- The summand sequence is summable. -/
lemma aperyZetaSummand_summable : Summable aperyZetaSummand :=
  aperyZetaSummand_hasSum.summable

/-- The tsum equals ζ(3). -/
theorem aperyZetaSummand_tsum :
    (∑' m : ℕ, aperyZetaSummand m) = (∑' k : ℕ, 1 / ((k + 1 : ℝ) ^ 3)) :=
  aperyZetaSummand_hasSum.tsum_eq

/-- Tail of the Apéry zeta series starting at index `n`. -/
noncomputable def aperyZetaTail (n : ℕ) : ℝ :=
  ∑' m : ℕ, aperyZetaSummand (m + n)

/-- The tail is non-negative. -/
lemma aperyZetaTail_nonneg (n : ℕ) : 0 ≤ aperyZetaTail n := by
  unfold aperyZetaTail
  exact tsum_nonneg (fun m => aperyZetaSummand_nonneg _)

/-- Splitting the tsum at `n`: `ζ(3) = ∑_{m<n} + tail`. -/
lemma aperyZeta3_split (n : ℕ) :
    (∑' k : ℕ, 1 / ((k + 1 : ℝ) ^ 3))
      = (∑ m ∈ range n, aperyZetaSummand m) + aperyZetaTail n := by
  rw [← aperyZetaSummand_tsum]
  rw [← (aperyZetaSummand_summable.sum_add_tsum_nat_add n)]
  unfold aperyZetaTail
  rfl

/-- The exact identity: `ζ(3) − b_n / a_n = aperyZetaTail n`. -/
lemma aperyZeta3_minus_aperyB_div_aperyA (n : ℕ) :
    (∑' k : ℕ, 1 / ((k + 1 : ℝ) ^ 3)) - (aperyB n : ℝ) / (aperyA n : ℝ)
      = aperyZetaTail n := by
  rw [aperyB_div_aperyA_real_eq_partial_sum]
  rw [aperyZeta3_split n]
  ring

/-- Multiplying by `a_n` gives the difference identity:
    `ζ(3) · a_n − b_n = a_n · aperyZetaTail n`. -/
theorem aperyZeta3_aperyA_minus_aperyB (n : ℕ) :
    (∑' k : ℕ, 1 / ((k + 1 : ℝ) ^ 3)) * (aperyA n : ℝ) - (aperyB n : ℝ)
      = (aperyA n : ℝ) * aperyZetaTail n := by
  have hA_pos : 0 < (aperyA n : ℝ) := by exact_mod_cast aperyA_pos n
  have hA_ne : (aperyA n : ℝ) ≠ 0 := hA_pos.ne'
  have h := aperyZeta3_minus_aperyB_div_aperyA n
  field_simp at h
  linarith

end Ripple.Number
