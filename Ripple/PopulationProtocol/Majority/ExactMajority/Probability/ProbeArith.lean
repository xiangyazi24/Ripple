import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.SeamEpidemics
open scoped ENNReal
example (n : ℕ) (x : ℝ) (hn : 0 < (n:ℝ)) (hx : (1:ℝ)/n ≤ x) (hxpos : 0 < x) :
    (ENNReal.ofReal x)⁻¹ ≤ (n : ℝ≥0∞) := by
  have h1 : ENNReal.ofReal (1/n) ≤ ENNReal.ofReal x := ENNReal.ofReal_le_ofReal hx
  have h2 : (ENNReal.ofReal x)⁻¹ ≤ (ENNReal.ofReal (1/n))⁻¹ := ENNReal.inv_le_inv.mpr h1
  refine le_trans h2 ?_
  rw [one_div, ENNReal.ofReal_inv_of_pos hn, inv_inv, ENNReal.ofReal_natCast]
