/-
  Ripple.Core.BoundedTime — Bounded-Time Computability

  Defines time modulus and bounded-time complexity classes
  for bounded PIVPs.

  Key definition (from [BAC] Def 2.4):
    A bounded PIVP computes α with time modulus μ : ℕ → ℝ≥0 if
      |x(t) - α| < e^{-r}   whenever  t > μ(r).

  The time complexity of the computation is the asymptotic growth of μ(r).

  Hierarchy (from [BAC] §5):
    Floor 0 (real-time):  μ(r) = Θ(r)        — e.g., e, π
    Floor 1:              μ(r) = Θ(r²)       — quadratic
    Floor n:              μ(r) = Θ(rⁿ)       — degree-n polynomial
    Lambert W:            μ(r) = Θ(r log r)
    Tower k:              μ(r) = Θ(exp^(k+1)(r))
-/

import Ripple.Core.PIVP
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

namespace Ripple

/-- A time modulus is a function μ : ℕ → ℝ such that μ(r) bounds the time
  needed to achieve r bits of precision. -/
def TimeModulus := ℕ → ℝ

/-- A bounded PIVP computes α with time modulus μ if:
  for all r, for all t > μ(r), |x_output(t) - α| < e^{-r}. -/
structure BoundedTimeComputable (d : ℕ) (α : ℝ) where
  /-- The underlying PIVP. -/
  pivp : PIVP d
  /-- The solution to the PIVP. -/
  sol : PIVP.Solution pivp
  /-- The time modulus. -/
  modulus : TimeModulus
  /-- The PIVP is bounded. -/
  bounded : pivp.IsBounded sol.trajectory
  /-- Convergence with the given time modulus. -/
  convergence : ∀ r : ℕ, ∀ t : ℝ, t > modulus r →
    |sol.trajectory t pivp.output - α| < Real.exp (-(r : ℝ))

/-- A real number is CRN-computable if it is computable by some bounded PIVP. -/
def IsCRNComputable (α : ℝ) : Prop :=
  ∃ d : ℕ, ∃ _ : BoundedTimeComputable d α, True

/-- A real number is real-time CRN-computable (floor 0) if it has
  a linear time modulus: μ(r) = O(r), i.e., μ(r) ≤ C(r+1) for some C > 0. -/
def IsRealTimeComputable (α : ℝ) : Prop :=
  ∃ d : ℕ, ∃ btc : BoundedTimeComputable d α,
    ∃ C : ℝ, 0 < C ∧ ∀ r : ℕ, btc.modulus r ≤ C * (↑r + 1)

/-- A real number is polynomial-time CRN-computable (floor n) if it has
  time modulus μ(r) = O(r^n). -/
def IsPolyTimeComputable (α : ℝ) (n : ℕ) : Prop :=
  ∃ d : ℕ, ∃ btc : BoundedTimeComputable d α,
    ∃ C : ℝ, 0 < C ∧ ∀ r : ℕ, btc.modulus r ≤ C * (↑r + 1) ^ n

/-- Addition closure for real-time computable numbers (from [RTCRN2]).
  Constructs a combined (d₁+d₂+1)-dimensional PIVP that runs both sub-PIVPs in
  parallel with a sum-tracking output variable.
  Convergence uses triangle inequality + 2e^{-(r+1)} ≤ e^{-r} (since 2 ≤ e). -/
theorem realtime_field_add {α β : ℝ} :
    IsRealTimeComputable α → IsRealTimeComputable β → IsRealTimeComputable (α + β) := by
  intro ⟨d₁, btc₁, C₁, hC₁, hmod₁⟩ ⟨d₂, btc₂, C₂, hC₂, hmod₂⟩
  -- Combined PIVP: first d₁ components run PIVP₁, next d₂ run PIVP₂,
  -- last component tracks x₁_output + x₂_output.
  refine ⟨(d₁ + d₂) + 1, {
    pivp := {
      field := fun v =>
        let v₁ : Fin d₁ → ℝ := fun j => v (Fin.castSucc (Fin.castAdd d₂ j))
        let v₂ : Fin d₂ → ℝ := fun j => v (Fin.castSucc (Fin.natAdd d₁ j))
        Fin.snoc (Fin.append (btc₁.pivp.field v₁) (btc₂.pivp.field v₂))
          (btc₁.pivp.field v₁ btc₁.pivp.output + btc₂.pivp.field v₂ btc₂.pivp.output)
      init := Fin.snoc (Fin.append btc₁.pivp.init btc₂.pivp.init)
          (btc₁.pivp.init btc₁.pivp.output + btc₂.pivp.init btc₂.pivp.output)
      output := Fin.last (d₁ + d₂) }
    sol := {
      trajectory := fun t =>
        Fin.snoc (Fin.append (btc₁.sol.trajectory t) (btc₂.sol.trajectory t))
          (btc₁.sol.trajectory t btc₁.pivp.output + btc₂.sol.trajectory t btc₂.pivp.output)
      init_cond := by simp only [btc₁.sol.init_cond, btc₂.sol.init_cond]
      is_solution := fun t ht => by
        have hd₁ := btc₁.sol.is_solution t ht
        have hd₂ := btc₂.sol.is_solution t ht
        rw [hasDerivAt_pi] at hd₁ hd₂ ⊢
        refine Fin.lastCases ?_ (fun j => ?_)
        · -- Last component (sum tracker): d/dt (x₁_o₁ + x₂_o₂)
          simp only [Fin.snoc_last, Fin.snoc_castSucc, Fin.append_left, Fin.append_right]
          exact (hd₁ btc₁.pivp.output).add (hd₂ btc₂.pivp.output)
        · -- Sub-PIVP components
          refine Fin.addCases (fun j₁ => ?_) (fun j₂ => ?_) j
          · simp only [Fin.snoc_castSucc, Fin.append_left]
            exact hd₁ j₁
          · simp only [Fin.snoc_castSucc, Fin.append_right]
            exact hd₂ j₂ }
    modulus := fun r => max (btc₁.modulus (r + 1)) (btc₂.modulus (r + 1))
    bounded := ?_
    convergence := ?_ }, 2 * max C₁ C₂, by positivity, ?_⟩
  · -- Bounded: all components bounded by M₁ + M₂
    obtain ⟨M₁, hM₁, hb₁⟩ := btc₁.bounded
    obtain ⟨M₂, hM₂, hb₂⟩ := btc₂.bounded
    refine ⟨M₁ + M₂, by linarith, fun t ht => ?_⟩
    rw [pi_norm_le_iff_of_nonneg (by linarith)]
    refine Fin.lastCases ?_ (fun j => ?_)
    · -- Sum component
      simp only [Fin.snoc_last]
      rw [Real.norm_eq_abs]
      have h₁ : |btc₁.sol.trajectory t btc₁.pivp.output| ≤ M₁ := by
        have hcomp := norm_le_pi_norm (btc₁.sol.trajectory t) btc₁.pivp.output
        rw [Real.norm_eq_abs] at hcomp; linarith [hb₁ t ht]
      have h₂ : |btc₂.sol.trajectory t btc₂.pivp.output| ≤ M₂ := by
        have hcomp := norm_le_pi_norm (btc₂.sol.trajectory t) btc₂.pivp.output
        rw [Real.norm_eq_abs] at hcomp; linarith [hb₂ t ht]
      linarith [abs_add_le (btc₁.sol.trajectory t btc₁.pivp.output)
                           (btc₂.sol.trajectory t btc₂.pivp.output)]
    · -- Sub-PIVP components
      refine Fin.addCases (fun j₁ => ?_) (fun j₂ => ?_) j
      · simp only [Fin.snoc_castSucc, Fin.append_left]
        calc ‖btc₁.sol.trajectory t j₁‖
            ≤ ‖btc₁.sol.trajectory t‖ := norm_le_pi_norm _ _
          _ ≤ M₁ := hb₁ t ht
          _ ≤ M₁ + M₂ := le_add_of_nonneg_right (le_of_lt hM₂)
      · simp only [Fin.snoc_castSucc, Fin.append_right]
        calc ‖btc₂.sol.trajectory t j₂‖
            ≤ ‖btc₂.sol.trajectory t‖ := norm_le_pi_norm _ _
          _ ≤ M₂ := hb₂ t ht
          _ ≤ M₁ + M₂ := le_add_of_nonneg_left (le_of_lt hM₁)
  · -- Convergence: triangle inequality + 2e^{-(r+1)} ≤ e^{-r}
    intro r t ht
    simp only [Fin.snoc_last]
    have ht₁ : t > btc₁.modulus (r + 1) := lt_of_le_of_lt (le_max_left _ _) ht
    have ht₂ : t > btc₂.modulus (r + 1) := lt_of_le_of_lt (le_max_right _ _) ht
    have hc₁ := btc₁.convergence (r + 1) t ht₁
    have hc₂ := btc₂.convergence (r + 1) t ht₂
    have htri : |btc₁.sol.trajectory t btc₁.pivp.output +
        btc₂.sol.trajectory t btc₂.pivp.output - (α + β)|
      ≤ |btc₁.sol.trajectory t btc₁.pivp.output - α| +
        |btc₂.sol.trajectory t btc₂.pivp.output - β| := by
      have : btc₁.sol.trajectory t btc₁.pivp.output +
          btc₂.sol.trajectory t btc₂.pivp.output - (α + β) =
          (btc₁.sol.trajectory t btc₁.pivp.output - α) +
          (btc₂.sol.trajectory t btc₂.pivp.output - β) := by ring
      rw [this]; exact abs_add_le _ _
    have hexp : 2 * Real.exp (-(↑(r + 1) : ℝ)) ≤ Real.exp (-(↑r : ℝ)) := by
      have hcast : (-(↑(r + 1) : ℝ)) = -(↑r : ℝ) + (-1 : ℝ) := by push_cast; ring
      rw [hcast, Real.exp_add]
      have h2e : 2 * Real.exp (-1 : ℝ) ≤ 1 := by
        rw [Real.exp_neg, ← div_eq_mul_inv, div_le_one (Real.exp_pos 1)]
        linarith [Real.add_one_le_exp (1 : ℝ)]
      calc 2 * (Real.exp (-(↑r : ℝ)) * Real.exp (-1))
          = Real.exp (-(↑r : ℝ)) * (2 * Real.exp (-1)) := by ring
        _ ≤ Real.exp (-(↑r : ℝ)) * 1 :=
            mul_le_mul_of_nonneg_left h2e (le_of_lt (Real.exp_pos _))
        _ = Real.exp (-(↑r : ℝ)) := mul_one _
    linarith
  · -- Linear modulus: max(μ₁(r+1), μ₂(r+1)) ≤ 2·max(C₁,C₂)·(r+1)
    intro r
    have h₁ : btc₁.modulus (r + 1) ≤ max C₁ C₂ * (↑r + 2) := by
      calc btc₁.modulus (r + 1)
          ≤ C₁ * (↑(r + 1) + 1) := hmod₁ (r + 1)
        _ = C₁ * (↑r + 2) := by push_cast; ring
        _ ≤ max C₁ C₂ * (↑r + 2) :=
            mul_le_mul_of_nonneg_right (le_max_left C₁ C₂)
              (by positivity)
    have h₂ : btc₂.modulus (r + 1) ≤ max C₁ C₂ * (↑r + 2) := by
      calc btc₂.modulus (r + 1)
          ≤ C₂ * (↑(r + 1) + 1) := hmod₂ (r + 1)
        _ = C₂ * (↑r + 2) := by push_cast; ring
        _ ≤ max C₁ C₂ * (↑r + 2) :=
            mul_le_mul_of_nonneg_right (le_max_right C₁ C₂)
              (by positivity)
    calc max (btc₁.modulus (r + 1)) (btc₂.modulus (r + 1))
        ≤ max C₁ C₂ * (↑r + 2) := max_le h₁ h₂
      _ ≤ max C₁ C₂ * (2 * (↑r + 1)) := by
          apply mul_le_mul_of_nonneg_left
          · have : (0 : ℝ) ≤ ↑r := Nat.cast_nonneg r; linarith
          · exact le_of_lt (lt_of_lt_of_le hC₁ (le_max_left C₁ C₂))
      _ = 2 * max C₁ C₂ * (↑r + 1) := by ring

/-- Multiplication closure for real-time computable numbers (from [RTCRN2]).
  Constructs a combined (d₁+d₂+1)-dimensional PIVP that runs both sub-PIVPs in
  parallel with a product-tracking output variable (using the product rule).
  Convergence uses the three-term decomposition
  x₁x₂-αβ = x₁(x₂-β) + (x₁-α)x₂ - (x₁-α)(x₂-β) with a
  modulus shift by K = ⌈M₁+M₂+1⌉ to absorb the constant factor. -/
theorem realtime_field_mul {α β : ℝ} :
    IsRealTimeComputable α → IsRealTimeComputable β → IsRealTimeComputable (α * β) := by
  intro ⟨d₁, btc₁, C₁, hC₁, hmod₁⟩ ⟨d₂, btc₂, C₂, hC₂, hmod₂⟩
  obtain ⟨M₁, hM₁, hb₁⟩ := btc₁.bounded
  obtain ⟨M₂, hM₂, hb₂⟩ := btc₂.bounded
  -- K : ℕ with e^K > M₁+M₂+1 (via 1+x ≤ e^x)
  set K := Nat.ceil (M₁ + M₂ + 1) with hK_def
  have hK : M₁ + M₂ + 1 ≤ (↑K : ℝ) := Nat.le_ceil _
  have hexp_K : M₁ + M₂ + 1 < Real.exp (↑K : ℝ) :=
    calc M₁ + M₂ + 1 ≤ (↑K : ℝ) := hK
      _ < (↑K : ℝ) + 1 := by linarith
      _ ≤ Real.exp (↑K : ℝ) := Real.add_one_le_exp _
  -- Component bound helpers
  have hx₁_bound : ∀ t, 0 ≤ t → |btc₁.sol.trajectory t btc₁.pivp.output| ≤ M₁ := by
    intro t ht
    have := norm_le_pi_norm (btc₁.sol.trajectory t) btc₁.pivp.output
    rw [Real.norm_eq_abs] at this; linarith [hb₁ t ht]
  have hx₂_bound : ∀ t, 0 ≤ t → |btc₂.sol.trajectory t btc₂.pivp.output| ≤ M₂ := by
    intro t ht
    have := norm_le_pi_norm (btc₂.sol.trajectory t) btc₂.pivp.output
    rw [Real.norm_eq_abs] at this; linarith [hb₂ t ht]
  -- Combined PIVP: first d₁ run PIVP₁, next d₂ run PIVP₂, last = product tracker
  refine ⟨(d₁ + d₂) + 1, {
    pivp := {
      field := fun v =>
        let v₁ : Fin d₁ → ℝ := fun j => v (Fin.castSucc (Fin.castAdd d₂ j))
        let v₂ : Fin d₂ → ℝ := fun j => v (Fin.castSucc (Fin.natAdd d₁ j))
        Fin.snoc (Fin.append (btc₁.pivp.field v₁) (btc₂.pivp.field v₂))
          (btc₁.pivp.field v₁ btc₁.pivp.output * v₂ btc₂.pivp.output +
           v₁ btc₁.pivp.output * btc₂.pivp.field v₂ btc₂.pivp.output)
      init := Fin.snoc (Fin.append btc₁.pivp.init btc₂.pivp.init)
          (btc₁.pivp.init btc₁.pivp.output * btc₂.pivp.init btc₂.pivp.output)
      output := Fin.last (d₁ + d₂) }
    sol := {
      trajectory := fun t =>
        Fin.snoc (Fin.append (btc₁.sol.trajectory t) (btc₂.sol.trajectory t))
          (btc₁.sol.trajectory t btc₁.pivp.output * btc₂.sol.trajectory t btc₂.pivp.output)
      init_cond := by simp only [btc₁.sol.init_cond, btc₂.sol.init_cond]
      is_solution := fun t ht => by
        have hd₁ := btc₁.sol.is_solution t ht
        have hd₂ := btc₂.sol.is_solution t ht
        rw [hasDerivAt_pi] at hd₁ hd₂ ⊢
        refine Fin.lastCases ?_ (fun j => ?_)
        · -- Product tracker: d/dt (x₁ * x₂) = x₁' * x₂ + x₁ * x₂'
          simp only [Fin.snoc_last, Fin.snoc_castSucc, Fin.append_left, Fin.append_right]
          exact (hd₁ btc₁.pivp.output).mul (hd₂ btc₂.pivp.output)
        · refine Fin.addCases (fun j₁ => ?_) (fun j₂ => ?_) j
          · simp only [Fin.snoc_castSucc, Fin.append_left]
            exact hd₁ j₁
          · simp only [Fin.snoc_castSucc, Fin.append_right]
            exact hd₂ j₂ }
    modulus := fun r => max 0 (max (btc₁.modulus (r + K)) (btc₂.modulus (r + K)))
    bounded := ?_
    convergence := ?_ }, max C₁ C₂ * (↑K + 1), by positivity, ?_⟩
  · -- Bounded
    refine ⟨M₁ * M₂ + M₁ + M₂, by positivity, fun t ht => ?_⟩
    rw [pi_norm_le_iff_of_nonneg (by positivity)]
    refine Fin.lastCases ?_ (fun j => ?_)
    · -- Product component
      simp only [Fin.snoc_last]
      rw [Real.norm_eq_abs, abs_mul]
      calc |btc₁.sol.trajectory t btc₁.pivp.output| *
            |btc₂.sol.trajectory t btc₂.pivp.output|
          ≤ M₁ * M₂ := mul_le_mul (hx₁_bound t ht) (hx₂_bound t ht)
              (abs_nonneg _) (le_of_lt hM₁)
        _ ≤ M₁ * M₂ + M₁ + M₂ := by linarith [hM₁, hM₂]
    · -- Sub-PIVP components
      refine Fin.addCases (fun j₁ => ?_) (fun j₂ => ?_) j
      · simp only [Fin.snoc_castSucc, Fin.append_left]
        calc ‖btc₁.sol.trajectory t j₁‖
            ≤ ‖btc₁.sol.trajectory t‖ := norm_le_pi_norm _ _
          _ ≤ M₁ := hb₁ t ht
          _ ≤ M₁ * M₂ + M₁ + M₂ := by nlinarith [hM₂]
      · simp only [Fin.snoc_castSucc, Fin.append_right]
        calc ‖btc₂.sol.trajectory t j₂‖
            ≤ ‖btc₂.sol.trajectory t‖ := norm_le_pi_norm _ _
          _ ≤ M₂ := hb₂ t ht
          _ ≤ M₁ * M₂ + M₁ + M₂ := by nlinarith [hM₁]
  · -- Convergence: three-term decomposition + modulus shift by K
    intro r t ht
    simp only [Fin.snoc_last]
    have ht_pos : 0 < t := lt_of_le_of_lt (le_max_left 0 _) ht
    have ht₁ : t > btc₁.modulus (r + K) :=
      lt_of_le_of_lt (le_trans (le_max_left _ _) (le_max_right 0 _)) ht
    have ht₂ : t > btc₂.modulus (r + K) :=
      lt_of_le_of_lt (le_trans (le_max_right _ _) (le_max_right 0 _)) ht
    -- Abbreviations
    set x₁ := btc₁.sol.trajectory t btc₁.pivp.output
    set x₂ := btc₂.sol.trajectory t btc₂.pivp.output
    set e_rK := Real.exp (-(↑(r + K) : ℝ))
    have hc₁ : |x₁ - α| < e_rK := btc₁.convergence (r + K) t ht₁
    have hc₂ : |x₂ - β| < e_rK := btc₂.convergence (r + K) t ht₂
    have hx₁ : |x₁| ≤ M₁ := hx₁_bound t (le_of_lt ht_pos)
    have hx₂ : |x₂| ≤ M₂ := hx₂_bound t (le_of_lt ht_pos)
    -- Triangle: x₁x₂-αβ = x₁(x₂-β)+(x₁-α)x₂-(x₁-α)(x₂-β)
    have htri : |x₁ * x₂ - α * β| ≤
        |x₁| * |x₂ - β| + |x₁ - α| * |x₂| + |x₁ - α| * |x₂ - β| := by
      have heq : x₁ * x₂ - α * β =
        (x₁ * (x₂ - β) + (x₁ - α) * x₂) + (-(x₁ - α) * (x₂ - β)) := by ring
      calc |x₁ * x₂ - α * β|
          = |(x₁ * (x₂ - β) + (x₁ - α) * x₂) + (-(x₁ - α) * (x₂ - β))| := by rw [heq]
        _ ≤ |x₁ * (x₂ - β) + (x₁ - α) * x₂| + |-(x₁ - α) * (x₂ - β)| :=
            abs_add_le _ _
        _ ≤ (|x₁ * (x₂ - β)| + |(x₁ - α) * x₂|) + |-(x₁ - α) * (x₂ - β)| := by
            linarith [abs_add_le (x₁ * (x₂ - β)) ((x₁ - α) * x₂)]
        _ = |x₁| * |x₂ - β| + |x₁ - α| * |x₂| + |x₁ - α| * |x₂ - β| := by
            simp only [abs_mul, neg_mul, abs_neg]
    -- Bound each term
    have hb1 : |x₁| * |x₂ - β| ≤ M₁ * e_rK :=
      mul_le_mul hx₁ (le_of_lt hc₂) (abs_nonneg _) (le_of_lt hM₁)
    have hb2 : |x₁ - α| * |x₂| ≤ e_rK * M₂ :=
      mul_le_mul (le_of_lt hc₁) hx₂ (abs_nonneg _) (le_of_lt (Real.exp_pos _))
    have h_le_1 : e_rK ≤ 1 := by
      calc e_rK ≤ Real.exp 0 :=
            Real.exp_le_exp.mpr (neg_nonpos.mpr (by positivity))
        _ = 1 := Real.exp_zero
    have hb3 : |x₁ - α| * |x₂ - β| ≤ e_rK := by
      calc |x₁ - α| * |x₂ - β|
          ≤ e_rK * e_rK :=
            mul_le_mul (le_of_lt hc₁) (le_of_lt hc₂) (abs_nonneg _)
              (le_of_lt (Real.exp_pos _))
        _ ≤ 1 * e_rK :=
            mul_le_mul_of_nonneg_right h_le_1 (le_of_lt (Real.exp_pos _))
        _ = e_rK := one_mul _
    -- Sum: ≤ (M₁+M₂+1)·e_rK
    have hsum : |x₁ * x₂ - α * β| ≤ (M₁ + M₂ + 1) * e_rK := by linarith
    -- Rate: (M₁+M₂+1)·e_rK < exp(-r) via e^K > M₁+M₂+1
    have hrate : (M₁ + M₂ + 1) * e_rK < Real.exp (-(↑r : ℝ)) := by
      have hfactor : e_rK = Real.exp (-(↑r : ℝ)) * Real.exp (-(↑K : ℝ)) := by
        change Real.exp (-(↑(r + K) : ℝ)) = _
        rw [show (-(↑(r + K) : ℝ)) = -(↑r : ℝ) + (-(↑K : ℝ)) from by push_cast; ring,
            Real.exp_add]
      rw [hfactor, show (M₁ + M₂ + 1) * (Real.exp (-(↑r : ℝ)) * Real.exp (-(↑K : ℝ))) =
        Real.exp (-(↑r : ℝ)) * ((M₁ + M₂ + 1) * Real.exp (-(↑K : ℝ))) from by ring]
      have hfrac : (M₁ + M₂ + 1) * Real.exp (-(↑K : ℝ)) < 1 := by
        rw [Real.exp_neg, ← div_eq_mul_inv, div_lt_one (Real.exp_pos _)]
        exact hexp_K
      calc Real.exp (-(↑r : ℝ)) * ((M₁ + M₂ + 1) * Real.exp (-(↑K : ℝ)))
          < Real.exp (-(↑r : ℝ)) * 1 :=
            mul_lt_mul_of_pos_left hfrac (Real.exp_pos _)
        _ = Real.exp (-(↑r : ℝ)) := mul_one _
    linarith
  · -- Linear modulus: max 0 (max(μ₁(r+K),μ₂(r+K))) ≤ max(C₁,C₂)·(K+1)·(r+1)
    intro r
    have hcast : (↑(r + K) : ℝ) + 1 = ↑r + ↑K + 1 := by push_cast; ring
    have h₁ : btc₁.modulus (r + K) ≤ max C₁ C₂ * (↑r + ↑K + 1) := by
      have := hmod₁ (r + K); rw [hcast] at this
      exact le_trans this (mul_le_mul_of_nonneg_right (le_max_left C₁ C₂) (by positivity))
    have h₂ : btc₂.modulus (r + K) ≤ max C₁ C₂ * (↑r + ↑K + 1) := by
      have := hmod₂ (r + K); rw [hcast] at this
      exact le_trans this (mul_le_mul_of_nonneg_right (le_max_right C₁ C₂) (by positivity))
    have h_factor : (↑r : ℝ) + ↑K + 1 ≤ (↑K + 1) * (↑r + 1) := by
      have : (↑K + 1) * (↑r + 1) = ↑K * ↑r + ↑K + ↑r + 1 := by ring
      linarith [show (0 : ℝ) ≤ ↑K * ↑r from by positivity]
    calc max 0 (max (btc₁.modulus (r + K)) (btc₂.modulus (r + K)))
        ≤ max C₁ C₂ * (↑r + ↑K + 1) := max_le (by positivity) (max_le h₁ h₂)
      _ ≤ max C₁ C₂ * ((↑K + 1) * (↑r + 1)) :=
          mul_le_mul_of_nonneg_left h_factor
            (le_of_lt (lt_of_lt_of_le hC₁ (le_max_left C₁ C₂)))
      _ = max C₁ C₂ * (↑K + 1) * (↑r + 1) := by ring

/-- Any integer (or rational with integer PIVP embedding) is real-time computable.
  Proof: constant PIVP x' = 0, x(0) = c has solution x(t) = c,
  so |x(t) - c| = 0 < e^{-r} for all t.
  Note: our PIVP definition allows real ICs; in the full theory,
  ICs must be rational ([RTCRN2] Thm 3.2.10). -/
theorem realtime_const (c : ℝ) : IsRealTimeComputable c := by
  refine ⟨1, ?_, ?_⟩
  · exact {
      pivp := { field := fun _ => ![0], init := ![c], output := 0 }
      sol := {
        trajectory := fun _ => ![c]
        init_cond := by ext i; fin_cases i; simp
        is_solution := fun t _ => by
          convert hasDerivAt_const t (![c] : Fin 1 → ℝ) using 1
          ext i; fin_cases i; simp
      }
      modulus := fun _ => 0
      bounded := ⟨|c| + 1, by positivity, fun t _ => by
        rw [pi_norm_le_iff_of_nonneg (by positivity)]
        intro i; fin_cases i
        change ‖c‖ ≤ |c| + 1
        rw [Real.norm_eq_abs]
        linarith⟩
      convergence := by
        intro r t _
        simp only [Matrix.cons_val_zero, sub_self, abs_zero]
        exact Real.exp_pos _
    }
  · exact ⟨1, one_pos, fun _ => by positivity⟩

/-- Negation closure: derived from mul and const. -α = (-1) * α. -/
theorem realtime_field_neg {α : ℝ} (ha : IsRealTimeComputable α) :
    IsRealTimeComputable (-α) := by
  have : -α = (-1) * α := by ring
  rw [this]
  exact realtime_field_mul (realtime_const (-1)) ha

/-- Reciprocal closure (positive case): from [RTCRN2] Lemma 4.
  Extend a PIVP computing α > 0 with a variable x satisfying
  x' = 1 - f_out(t)·x, x(0) = 0. The integrating factor solution
  x(t) = e^{-F(t)} · ∫₀ᵗ e^{F(s)} ds converges to 1/α exponentially. -/
private theorem realtime_field_inv_pos {α : ℝ} (hα_pos : 0 < α)
    (ha : IsRealTimeComputable α) : IsRealTimeComputable α⁻¹ := by
  obtain ⟨d, btc, C, hC, hmod⟩ := ha
  obtain ⟨M, hM, hbound⟩ := btc.bounded
  -- f(t) = trajectory output; g = continuous extension to all of ℝ
  set f : ℝ → ℝ := fun t => btc.sol.trajectory t btc.pivp.output with hf_def
  set g : ℝ → ℝ := fun t => f (max t 0) with hg_def
  have hg_cont : Continuous g := continuous_iff_continuousAt.mpr fun t => by
    have h1 : ContinuousAt f (max t 0) :=
      ((hasDerivAt_pi.mp (btc.sol.is_solution (max t 0) (le_max_right t 0)))
        btc.pivp.output).continuousAt
    have h2 : ContinuousAt (fun s => max s (0:ℝ)) t :=
      (continuous_id.max continuous_const).continuousAt
    exact ContinuousAt.comp (g := f) (f := fun s => max s (0:ℝ)) h1 h2
  have hg_eq : ∀ t, 0 ≤ t → g t = f t := fun t ht => by simp [hg_def, max_eq_left ht]
  have hf_bound : ∀ t, 0 ≤ t → |f t| ≤ M := fun t ht => by
    have := norm_le_pi_norm (btc.sol.trajectory t) btc.pivp.output
    rw [Real.norm_eq_abs] at this; linarith [hbound t ht]
  -- G(t) = ∫₀ᵗ g(s) ds (integrating factor)
  set G : ℝ → ℝ := fun t => ∫ s in (0:ℝ)..t, g s with hG_def
  have hG_hd : ∀ t, HasDerivAt G (g t) t := fun t =>
    intervalIntegral.integral_hasDerivAt_right (hg_cont.intervalIntegrable 0 t)
      (hg_cont.stronglyMeasurableAtFilter _ _) hg_cont.continuousAt
  have hG_cont : Continuous G :=
    continuous_iff_continuousAt.mpr fun t => (hG_hd t).continuousAt
  have hexpG : Continuous (fun s => Real.exp (G s)) := Real.continuous_exp.comp hG_cont
  -- x(t) = e^{-G(t)} · ∫₀ᵗ e^{G(s)} ds (reciprocal trajectory)
  set x : ℝ → ℝ := fun t => Real.exp (-G t) * ∫ s in (0:ℝ)..t, Real.exp (G s) with hx_def
  have hx_zero : x 0 = 0 := by
    simp [hx_def, hG_def, intervalIntegral.integral_same]
  -- HasDerivAt x (1 - g(t)·x(t)) at each t
  have hx_hd : ∀ t, HasDerivAt x (1 - g t * x t) t := by
    intro t
    have h2 := (hG_hd t).neg.exp  -- d/dt exp(-G(t))
    have h3 := intervalIntegral.integral_hasDerivAt_right (hexpG.intervalIntegrable 0 t)
      (hexpG.stronglyMeasurableAtFilter _ _) hexpG.continuousAt
    have h4 := h2.mul h3
    -- Convert Pi.mul function form to x
    have hfun : (fun t => Real.exp ((-G) t)) * (fun u => ∫ s in (0:ℝ)..u, Real.exp (G s)) = x := by
      ext s; simp [hx_def, Pi.mul_apply]
    rw [hfun] at h4
    -- Now h4 : HasDerivAt x (...) t; fix derivative value
    convert h4 using 1
    simp only [hx_def, Pi.neg_apply]
    rw [show Real.exp (-G t) * Real.exp (G t) = 1 from by
      rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]]
    ring
  -- Build (d+1)-dimensional PIVP
  refine ⟨d + 1, {
    pivp := {
      field := fun v =>
        Fin.snoc (btc.pivp.field (fun j => v (Fin.castSucc j)))
          (1 - v (Fin.castSucc btc.pivp.output) * v (Fin.last d))
      init := Fin.snoc btc.pivp.init 0
      output := Fin.last d }
    sol := {
      trajectory := fun t => Fin.snoc (btc.sol.trajectory t) (x t)
      init_cond := by
        ext i; refine Fin.lastCases ?_ (fun j => ?_) i
        · simp only [Fin.snoc_last]; exact hx_zero
        · simp only [Fin.snoc_castSucc]; exact congr_fun btc.sol.init_cond j
      is_solution := fun t ht => by
        rw [hasDerivAt_pi]
        refine Fin.lastCases ?_ (fun j => ?_)
        · -- Last component: d/dt x(t) = 1 - f(t)·x(t)
          simp only [Fin.snoc_last, Fin.snoc_castSucc]
          have := hx_hd t; rw [hg_eq t ht] at this; exact this
        · -- Original PIVP components
          simp only [Fin.snoc_castSucc]
          exact (hasDerivAt_pi.mp (btc.sol.is_solution t ht)) j }
    modulus := fun r => sorry
    bounded := sorry
    convergence := sorry }, sorry, sorry, sorry⟩

/-- Reciprocal closure for real-time computable numbers.
  When α ≠ 0 and α ∈ ℝ_RTCRN, then α⁻¹ ∈ ℝ_RTCRN.
  For α > 0: extend PIVP with x' = 1 - f(t)·x (integrating factor).
  For α < 0: reduce via 1/α = -(1/(-α)). -/
theorem realtime_field_inv {α : ℝ} (hα : α ≠ 0)
    (ha : IsRealTimeComputable α) : IsRealTimeComputable α⁻¹ := by
  by_cases hpos : 0 < α
  · exact realtime_field_inv_pos hpos ha
  · push Not at hpos
    have hneg : α < 0 := lt_of_le_of_ne hpos hα
    have h1 := realtime_field_inv_pos (neg_pos.mpr hneg) (realtime_field_neg ha)
    convert realtime_field_neg h1 using 1
    rw [inv_neg, neg_neg]

/-- Division closure: α / β = α · β⁻¹. -/
theorem realtime_field_div {α β : ℝ} (hβ : β ≠ 0)
    (ha : IsRealTimeComputable α) (hb : IsRealTimeComputable β) :
    IsRealTimeComputable (α / β) := by
  rw [div_eq_mul_inv]
  exact realtime_field_mul ha (realtime_field_inv hβ hb)

/-- Subtraction closure: derived from add and neg. -/
theorem realtime_field_sub {α β : ℝ} (ha : IsRealTimeComputable α)
    (hb : IsRealTimeComputable β) : IsRealTimeComputable (α - β) := by
  have : α - β = α + (-β) := sub_eq_add_neg α β
  rw [this]
  exact realtime_field_add ha (realtime_field_neg hb)

end Ripple
