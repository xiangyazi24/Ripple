/-
  Ripple.DualRail.ScalarQuintic — UCNC25 Problem 1, scalar quintic case

  Concrete quintic case for UCNC25 Problem 1: the scalar GPAC
    y' = 1 - y^5        y(0) = 0
  which is bounded (attracts to y = 1). Uniform dual-rail with constant-k
  annihilation after the substitution y ↦ u - v expands
    p̂(u, v) = 1 - (u - v)^5
            = 1 + (5 u^4 v + 10 u^2 v^3 + v^5)     -- p̂⁺
              − (u^5 + 10 u^3 v^2 + 5 u v^4)        -- p̂⁻
  so the dual-railed system is
    u' = 1 + 5 u^4 v + 10 u^2 v^3 + v^5 − k · u · v
    v' =     u^5 + 10 u^3 v^2 + 5 u v^4 − k · u · v
  with u(0) = v(0) = 0.

  **Theorem (target, this file).** There exists `k_5* > 0` such that for all
  `k > k_5*`, the dual-rail solution `(u, v)` is bounded for all t ≥ 0.

  Proof outline (identical skeleton to `ScalarCubic.lean`):

  - Let `σ := u + v`, `y := u − v`. Binomial identity in `y`:
      p̂⁺ + p̂⁻ = 1 + (u + v)^5 = 1 + σ^5,
      p̂⁺ − p̂⁻ = 1 − (u − v)^5 = 1 − y^5.
  - σ-drift: σ' = u' + v' = (1 + σ^5) − 2k·uv = 1 + σ^5 − (k/2)(σ^2 − y^2).

  **Chosen threshold.** The true saddle-node threshold for `|y|=1` is
  the irrational root of a transcendental equation, numerically ≈ 13.01.
  Rather than dealing with irrational barriers, we use an integer barrier
  `σ = 2` and demand `k > 22`. At `σ = 2` with `|y| ≤ 1` the drift is
    1 + 32 − (k/2)(4 − y²) ≤ 33 − 3k/2,
  which is strictly negative for `k > 22`. (For `k > 22/3·11 = ...` —
  see the header of `scalar_quintic_sigma_bound` for the precise
  computation.) We therefore set `scalarQuinticThreshold = 22`.

  References:
  - `notes/constant-annihilation-UCNC25.tex` (research note).
  - `Ripple/DualRail/ScalarCubic.lean` (cubic analogue, 0 sorry, 0 axiom).
  - UCNC25: `../../ref/selective-dual-railing-UCNC2025.pdf`.
-/

import Ripple.Core.PIVP
import Ripple.Core.ODEGlobal
import Ripple.DualRail.ConstantAnnihilation
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.ODE.Gronwall

namespace Ripple
namespace DualRail
namespace ScalarQuintic

open MvPolynomial

/-! ## The scalar polynomial p(y) = 1 − y^5 -/

/-- The 1-dimensional polynomial vector field `p(y) = 1 − y^5`, encoded as
a `Fin 1 → MvPolynomial (Fin 1) ℚ`. -/
noncomputable def quinticField : Fin 1 → MvPolynomial (Fin 1) ℚ :=
  fun _ => 1 - (X 0) ^ 5

/-- The scalar PIVP `y' = 1 − y^5`, `y(0) = 0`. -/
noncomputable def quinticPIVP : PolyPIVP 1 where
  field := quinticField
  init := fun _ => 0
  output := 0

/-! ## The uniform constant-annihilation dual-railed system -/

/-- The dual-railed PolyPIVP at a fixed annihilation rate `k`. -/
noncomputable def dualRailedQuintic (k : ℚ) : PolyPIVP 2 :=
  constantAnnihilationDualRail 1 quinticField k

/-! ## Positive / negative decomposition for p(y) = 1 − y^5 -/

/-- The positive part as an explicit polynomial:
`1 + 5·X₀⁴·X₁ + 10·X₀²·X₁³ + X₁⁵`. -/
noncomputable def quinticPosExplicit : MvPolynomial (Fin 2) ℚ :=
  C 1 + C 5 * X 0 ^ 4 * X 1 + C 10 * X 0 ^ 2 * X 1 ^ 3 + X 1 ^ 5

/-- The negative part as an explicit polynomial:
`X₀⁵ + 10·X₀³·X₁² + 5·X₀·X₁⁴`. -/
noncomputable def quinticNegExplicit : MvPolynomial (Fin 2) ℚ :=
  X 0 ^ 5 + C 10 * X 0 ^ 3 * X 1 ^ 2 + C 5 * X 0 * X 1 ^ 4

/-- Algebraic identity: `dualRailHom 1 (quinticField 0) = pos − neg`. -/
theorem dualRailHom_quintic_eq_pos_sub_neg :
    dualRailHom 1 (quinticField 0) = quinticPosExplicit - quinticNegExplicit := by
  unfold dualRailHom quinticField quinticPosExplicit quinticNegExplicit
  have e0 : (⟨2 * (0 : Fin 1).val, by omega⟩ : Fin 2) = 0 := by
    apply Fin.ext; simp
  have e1 : (⟨2 * (0 : Fin 1).val + 1, by omega⟩ : Fin 2) = 1 := by
    apply Fin.ext; simp
  simp only [map_sub, map_one, map_pow, MvPolynomial.aeval_X, e0, e1]
  show _ = 1 + C 5 * (X 0 : MvPolynomial (Fin 2) ℚ) ^ 4 * X 1
            + C 10 * X 0 ^ 2 * X 1 ^ 3 + X 1 ^ 5
    - (X 0 ^ 5 + C 10 * X 0 ^ 3 * X 1 ^ 2 + C 5 * X 0 * X 1 ^ 4)
  simp only [map_ofNat]
  ring

/-! ### Coefficient helpers for monomials in two variables. -/

private lemma quintic_coeff_X0pow_X1pow (a b : ℕ) (s : Fin 2 →₀ ℕ) :
    ((X 0 ^ a * X 1 ^ b : MvPolynomial (Fin 2) ℚ)).coeff s
      = if s = Finsupp.single 0 a + Finsupp.single 1 b then 1 else 0 := by
  rw [MvPolynomial.X_pow_eq_monomial, MvPolynomial.X_pow_eq_monomial,
      MvPolynomial.monomial_mul, MvPolynomial.coeff_monomial]
  split_ifs with h1 h2 h2
  · ring
  · exact (h2 h1.symm).elim
  · exact (h1 h2.symm).elim
  · rfl

/-- Coefficient formula for `quinticPosExplicit`. -/
private lemma quinticPosExplicit_coeff (s : Fin 2 →₀ ℕ) :
    quinticPosExplicit.coeff s
      = (if s = 0 then 1 else 0)
        + (if s = Finsupp.single 0 4 + Finsupp.single 1 1 then 5 else 0)
        + (if s = Finsupp.single 0 2 + Finsupp.single 1 3 then 10 else 0)
        + (if s = Finsupp.single 1 5 then 1 else 0) := by
  have heq : quinticPosExplicit
      = C 1 + C 5 * (X 0 ^ 4 * X 1) + C 10 * (X 0 ^ 2 * X 1 ^ 3) + X 1 ^ 5 := by
    unfold quinticPosExplicit; ring
  rw [heq, MvPolynomial.coeff_add, MvPolynomial.coeff_add, MvPolynomial.coeff_add,
      MvPolynomial.coeff_C_mul, MvPolynomial.coeff_C_mul]
  -- C 1 coeff
  have h1 : ((C 1 : MvPolynomial (Fin 2) ℚ)).coeff s
      = if s = 0 then 1 else 0 := by
    rw [MvPolynomial.coeff_C]
    split_ifs with h1 h2 h2
    · rfl
    · exact (h2 h1.symm).elim
    · exact (h1 h2.symm).elim
    · rfl
  -- X 1 ^ 5 coeff
  have h5 : ((X 1 ^ 5 : MvPolynomial (Fin 2) ℚ)).coeff s
      = if s = Finsupp.single 1 5 then 1 else 0 := by
    rw [MvPolynomial.X_pow_eq_monomial, MvPolynomial.coeff_monomial]
    split_ifs with h1 h2 h2
    · rfl
    · exact (h2 h1.symm).elim
    · exact (h1 h2.symm).elim
    · rfl
  -- Rewrite the X₀⁴·X₁ coeff. Factor X₀⁴·X₁ = X₀^4 · X₁^1.
  have hX1 : (X 1 : MvPolynomial (Fin 2) ℚ) = X 1 ^ 1 := by rw [pow_one]
  have hcoeff41 :
      ((X 0 ^ 4 * X 1 : MvPolynomial (Fin 2) ℚ)).coeff s
        = if s = Finsupp.single 0 4 + Finsupp.single 1 1 then 1 else 0 := by
    rw [hX1]; exact quintic_coeff_X0pow_X1pow 4 1 s
  have hcoeff23 :
      ((X 0 ^ 2 * X 1 ^ 3 : MvPolynomial (Fin 2) ℚ)).coeff s
        = if s = Finsupp.single 0 2 + Finsupp.single 1 3 then 1 else 0 :=
    quintic_coeff_X0pow_X1pow 2 3 s
  rw [h1, hcoeff41, hcoeff23, h5]
  split_ifs <;> ring

/-- Coefficient formula for `quinticNegExplicit`. -/
private lemma quinticNegExplicit_coeff (s : Fin 2 →₀ ℕ) :
    quinticNegExplicit.coeff s
      = (if s = Finsupp.single 0 5 then 1 else 0)
        + (if s = Finsupp.single 0 3 + Finsupp.single 1 2 then 10 else 0)
        + (if s = Finsupp.single 0 1 + Finsupp.single 1 4 then 5 else 0) := by
  have heq : quinticNegExplicit
      = X 0 ^ 5 + C 10 * (X 0 ^ 3 * X 1 ^ 2) + C 5 * (X 0 * X 1 ^ 4) := by
    unfold quinticNegExplicit; ring
  rw [heq, MvPolynomial.coeff_add, MvPolynomial.coeff_add,
      MvPolynomial.coeff_C_mul, MvPolynomial.coeff_C_mul]
  -- X 0 ^ 5 coeff
  have h1 : ((X 0 ^ 5 : MvPolynomial (Fin 2) ℚ)).coeff s
      = if s = Finsupp.single 0 5 then 1 else 0 := by
    rw [MvPolynomial.X_pow_eq_monomial, MvPolynomial.coeff_monomial]
    split_ifs with h1 h2 h2
    · rfl
    · exact (h2 h1.symm).elim
    · exact (h1 h2.symm).elim
    · rfl
  have hcoeff32 :
      ((X 0 ^ 3 * X 1 ^ 2 : MvPolynomial (Fin 2) ℚ)).coeff s
        = if s = Finsupp.single 0 3 + Finsupp.single 1 2 then 1 else 0 :=
    quintic_coeff_X0pow_X1pow 3 2 s
  have hX0 : (X 0 : MvPolynomial (Fin 2) ℚ) = X 0 ^ 1 := by rw [pow_one]
  have hcoeff14 :
      ((X 0 * X 1 ^ 4 : MvPolynomial (Fin 2) ℚ)).coeff s
        = if s = Finsupp.single 0 1 + Finsupp.single 1 4 then 1 else 0 := by
    rw [hX0]; exact quintic_coeff_X0pow_X1pow 1 4 s
  rw [h1, hcoeff32, hcoeff14]
  split_ifs <;> ring

/-- All coefficients of `quinticPosExplicit` are non-negative. -/
private lemma quinticPosExplicit_coeff_nonneg (s : Fin 2 →₀ ℕ) :
    0 ≤ quinticPosExplicit.coeff s := by
  rw [quinticPosExplicit_coeff]
  split_ifs <;> norm_num

/-- All coefficients of `quinticNegExplicit` are non-negative. -/
private lemma quinticNegExplicit_coeff_nonneg (s : Fin 2 →₀ ℕ) :
    0 ≤ quinticNegExplicit.coeff s := by
  rw [quinticNegExplicit_coeff]
  split_ifs <;> norm_num

/-- Supports are disjoint: for every `s`, either all pos-ites are false
or all neg-ites are false. We case on `s`. -/
private lemma quintic_supports_disjoint (s : Fin 2 →₀ ℕ) :
    quinticPosExplicit.coeff s = 0 ∨ quinticNegExplicit.coeff s = 0 := by
  rw [quinticPosExplicit_coeff, quinticNegExplicit_coeff]
  -- Pos indices (val-at-0, val-at-1): (0,0), (4,1), (2,3), (0,5)
  -- Neg indices: (5,0), (3,2), (1,4)
  -- All 7 distinct.  Case on which pos-branch (if any) fires.
  by_cases hp1 : s = 0
  · right
    have hn1 : s ≠ Finsupp.single 0 5 := by
      intro h; rw [hp1] at h
      have := congrArg (fun f : Fin 2 →₀ ℕ => f 0) h
      simp [Finsupp.single_apply] at this
    have hn2 : s ≠ Finsupp.single 0 3 + Finsupp.single 1 2 := by
      intro h; rw [hp1] at h
      have := congrArg (fun f : Fin 2 →₀ ℕ => f 0) h
      simp [Finsupp.single_apply] at this
    have hn3 : s ≠ Finsupp.single 0 1 + Finsupp.single 1 4 := by
      intro h; rw [hp1] at h
      have := congrArg (fun f : Fin 2 →₀ ℕ => f 0) h
      simp [Finsupp.single_apply] at this
    rw [if_neg hn1, if_neg hn2, if_neg hn3]; ring
  by_cases hp2 : s = Finsupp.single 0 4 + Finsupp.single 1 1
  · right
    have hn1 : s ≠ Finsupp.single 0 5 := by
      intro h; rw [hp2] at h
      have := congrArg (fun f : Fin 2 →₀ ℕ => f 1) h
      simp [Finsupp.single_apply] at this
    have hn2 : s ≠ Finsupp.single 0 3 + Finsupp.single 1 2 := by
      intro h; rw [hp2] at h
      have := congrArg (fun f : Fin 2 →₀ ℕ => f 0) h
      simp [Finsupp.single_apply] at this
    have hn3 : s ≠ Finsupp.single 0 1 + Finsupp.single 1 4 := by
      intro h; rw [hp2] at h
      have := congrArg (fun f : Fin 2 →₀ ℕ => f 0) h
      simp [Finsupp.single_apply] at this
    rw [if_neg hn1, if_neg hn2, if_neg hn3]; ring
  by_cases hp3 : s = Finsupp.single 0 2 + Finsupp.single 1 3
  · right
    have hn1 : s ≠ Finsupp.single 0 5 := by
      intro h; rw [hp3] at h
      have := congrArg (fun f : Fin 2 →₀ ℕ => f 1) h
      simp [Finsupp.single_apply] at this
    have hn2 : s ≠ Finsupp.single 0 3 + Finsupp.single 1 2 := by
      intro h; rw [hp3] at h
      have := congrArg (fun f : Fin 2 →₀ ℕ => f 0) h
      simp [Finsupp.single_apply] at this
    have hn3 : s ≠ Finsupp.single 0 1 + Finsupp.single 1 4 := by
      intro h; rw [hp3] at h
      have := congrArg (fun f : Fin 2 →₀ ℕ => f 0) h
      simp [Finsupp.single_apply] at this
    rw [if_neg hn1, if_neg hn2, if_neg hn3]; ring
  by_cases hp4 : s = Finsupp.single 1 5
  · right
    have hn1 : s ≠ Finsupp.single 0 5 := by
      intro h; rw [hp4] at h
      have := congrArg (fun f : Fin 2 →₀ ℕ => f 0) h
      simp [Finsupp.single_apply] at this
    have hn2 : s ≠ Finsupp.single 0 3 + Finsupp.single 1 2 := by
      intro h; rw [hp4] at h
      have := congrArg (fun f : Fin 2 →₀ ℕ => f 0) h
      simp [Finsupp.single_apply] at this
    have hn3 : s ≠ Finsupp.single 0 1 + Finsupp.single 1 4 := by
      intro h; rw [hp4] at h
      have := congrArg (fun f : Fin 2 →₀ ℕ => f 0) h
      simp [Finsupp.single_apply] at this
    rw [if_neg hn1, if_neg hn2, if_neg hn3]; ring
  -- Otherwise all four pos-ites are false, so pos coefficient is 0.
  left
  rw [if_neg hp1, if_neg hp2, if_neg hp3, if_neg hp4]; ring

/-- Identification: `dualRailPosPart = quinticPosExplicit`. -/
theorem dualRailPosPart_quintic_eq :
    dualRailPosPart 1 quinticField 0 = quinticPosExplicit := by
  unfold dualRailPosPart
  exact (posPart_negPart_of_nonneg_disjoint_decomp
    dualRailHom_quintic_eq_pos_sub_neg
    quinticPosExplicit_coeff_nonneg
    quinticNegExplicit_coeff_nonneg
    quintic_supports_disjoint).1

/-- Identification: `dualRailNegPart = quinticNegExplicit`. -/
theorem dualRailNegPart_quintic_eq :
    dualRailNegPart 1 quinticField 0 = quinticNegExplicit := by
  unfold dualRailNegPart
  exact (posPart_negPart_of_nonneg_disjoint_decomp
    dualRailHom_quintic_eq_pos_sub_neg
    quinticPosExplicit_coeff_nonneg
    quinticNegExplicit_coeff_nonneg
    quintic_supports_disjoint).2

/-- The positive part evaluates to `1 + 5 u⁴v + 10 u²v³ + v⁵`. -/
theorem dualRailPosPart_quintic_eval (w : Fin 2 → ℝ) :
    (dualRailPosPart 1 quinticField 0).eval₂ (Rat.castHom ℝ) w
      = 1 + 5 * (w 0) ^ 4 * (w 1) + 10 * (w 0) ^ 2 * (w 1) ^ 3 + (w 1) ^ 5 := by
  rw [dualRailPosPart_quintic_eq]
  unfold quinticPosExplicit
  simp only [MvPolynomial.eval₂_add, MvPolynomial.eval₂_mul,
    MvPolynomial.eval₂_X, MvPolynomial.eval₂_pow,
    MvPolynomial.eval₂_one, MvPolynomial.eval₂_ofNat,
    map_one, map_ofNat]

/-- The negative part evaluates to `u⁵ + 10 u³v² + 5 u v⁴`. -/
theorem dualRailNegPart_quintic_eval (w : Fin 2 → ℝ) :
    (dualRailNegPart 1 quinticField 0).eval₂ (Rat.castHom ℝ) w
      = (w 0) ^ 5 + 10 * (w 0) ^ 3 * (w 1) ^ 2 + 5 * (w 0) * (w 1) ^ 4 := by
  rw [dualRailNegPart_quintic_eq]
  unfold quinticNegExplicit
  simp only [MvPolynomial.eval₂_add, MvPolynomial.eval₂_mul,
    MvPolynomial.eval₂_X, MvPolynomial.eval₂_pow,
    MvPolynomial.eval₂_one, MvPolynomial.eval₂_ofNat,
    map_one, map_ofNat]

/-! ## Drift-difference / drift-sum identities -/

/-- Drift-difference identity: `u' − v' = 1 − (u − v)^5`. -/
theorem dualRailedQuintic_drift_diff (k : ℚ) (w : Fin 2 → ℝ) :
    (dualRailedQuintic k).evalField w 0 - (dualRailedQuintic k).evalField w 1
      = 1 - (w 0 - w 1) ^ 5 := by
  have hrow0 :
      (dualRailedQuintic k).evalField w 0
        = (dualRailPosPart 1 quinticField 0).eval₂ (Rat.castHom ℝ) w
          - (k : ℝ) * w 0 * w 1 := by
    unfold dualRailedQuintic PolyPIVP.evalField constantAnnihilationDualRail
    simp [MvPolynomial.eval₂_sub, MvPolynomial.eval₂_mul,
      MvPolynomial.eval₂_C, MvPolynomial.eval₂_X]
  have hrow1 :
      (dualRailedQuintic k).evalField w 1
        = (dualRailNegPart 1 quinticField 0).eval₂ (Rat.castHom ℝ) w
          - (k : ℝ) * w 0 * w 1 := by
    unfold dualRailedQuintic PolyPIVP.evalField constantAnnihilationDualRail
    simp [MvPolynomial.eval₂_sub, MvPolynomial.eval₂_mul,
      MvPolynomial.eval₂_C, MvPolynomial.eval₂_X]
  rw [hrow0, hrow1]
  ring_nf
  have hdiff :
      (dualRailPosPart 1 quinticField 0).eval₂ (Rat.castHom ℝ) w
        - (dualRailNegPart 1 quinticField 0).eval₂ (Rat.castHom ℝ) w
      = (quinticField 0).eval₂ (Rat.castHom ℝ)
          (fun j : Fin 1 =>
            w ⟨2 * j.val, by omega⟩ - w ⟨2 * j.val + 1, by omega⟩) :=
    dualRailPos_sub_dualRailNeg_eval 1 quinticField 0 w
  have heval : (quinticField 0).eval₂ (Rat.castHom ℝ)
      (fun j : Fin 1 =>
        w ⟨2 * j.val, by omega⟩ - w ⟨2 * j.val + 1, by omega⟩)
      = 1 - (w 0 - w 1) ^ 5 := by
    unfold quinticField
    simp [MvPolynomial.eval₂_sub, MvPolynomial.eval₂_one,
      MvPolynomial.eval₂_pow, MvPolynomial.eval₂_X]
  rw [heval] at hdiff
  linarith [hdiff]

/-- Drift-sum identity: `u' + v' = 1 + (u + v)^5 − 2k·uv`. -/
theorem dualRailedQuintic_drift_sum (k : ℚ) (w : Fin 2 → ℝ) :
    (dualRailedQuintic k).evalField w 0 + (dualRailedQuintic k).evalField w 1
      = 1 + (w 0 + w 1) ^ 5 - 2 * (k : ℝ) * w 0 * w 1 := by
  have hrow0 :
      (dualRailedQuintic k).evalField w 0
        = (dualRailPosPart 1 quinticField 0).eval₂ (Rat.castHom ℝ) w
          - (k : ℝ) * w 0 * w 1 := by
    unfold dualRailedQuintic PolyPIVP.evalField constantAnnihilationDualRail
    simp [MvPolynomial.eval₂_sub, MvPolynomial.eval₂_mul,
      MvPolynomial.eval₂_C, MvPolynomial.eval₂_X]
  have hrow1 :
      (dualRailedQuintic k).evalField w 1
        = (dualRailNegPart 1 quinticField 0).eval₂ (Rat.castHom ℝ) w
          - (k : ℝ) * w 0 * w 1 := by
    unfold dualRailedQuintic PolyPIVP.evalField constantAnnihilationDualRail
    simp [MvPolynomial.eval₂_sub, MvPolynomial.eval₂_mul,
      MvPolynomial.eval₂_C, MvPolynomial.eval₂_X]
  rw [hrow0, hrow1, dualRailPosPart_quintic_eval, dualRailNegPart_quintic_eval]
  ring

/-! ## Sigma-reduction identity -/

/-- Key algebraic identity:
  `(1 + 5 u⁴v + 10 u²v³ + v⁵) + (u⁵ + 10 u³v² + 5 u v⁴) = 1 + (u + v)^5`. -/
theorem quintic_posPart_plus_negPart (u v : ℝ) :
    (1 + 5 * u ^ 4 * v + 10 * u ^ 2 * v ^ 3 + v ^ 5)
      + (u ^ 5 + 10 * u ^ 3 * v ^ 2 + 5 * u * v ^ 4)
      = 1 + (u + v) ^ 5 := by
  ring

/-! ## Saddle-node threshold

Chosen: `k_5* = 22`. At `σ = 2`, `|y| ≤ 1`, the σ-drift is
  1 + σ⁵ − (k/2)(σ² − y²) = 33 − (k/2)(4 − y²) ≤ 33 − 3k/2,
which is negative for `k > 22`. Using `σ = 2` as the barrier avoids
irrational critical points `(k/5)^{1/3}`. -/
noncomputable def scalarQuinticThreshold : ℝ := 22

lemma scalarQuinticThreshold_pos : 0 < scalarQuinticThreshold := by
  unfold scalarQuinticThreshold
  norm_num

/-! ## Proof sub-lemmas (Tier 1) -/

/-- Lipschitz estimate for `(·)^5` on balls: `|x⁵ − y⁵| ≤ 5 R⁴ |x − y|`
when `|x|, |y| ≤ R`. Derived from the factoring
`x⁵ − y⁵ = (x − y)(x⁴ + x³y + x²y² + xy³ + y⁴)`. -/
private lemma fifth_power_lipschitz_on_ball (R : ℝ) (hR : 0 ≤ R)
    (x y : ℝ) (hx : |x| ≤ R) (hy : |y| ≤ R) :
    |x ^ 5 - y ^ 5| ≤ 5 * R ^ 4 * |x - y| := by
  have hfactor : x ^ 5 - y ^ 5
      = (x - y) * (x ^ 4 + x ^ 3 * y + x ^ 2 * y ^ 2 + x * y ^ 3 + y ^ 4) := by ring
  rw [hfactor, abs_mul]
  -- Bound the quartic factor by triangle inequality on |x|, |y| ≤ R.
  have habsx : |x| ≤ R := hx
  have habsy : |y| ≤ R := hy
  have hx_nn : 0 ≤ |x| := abs_nonneg _
  have hy_nn : 0 ≤ |y| := abs_nonneg _
  have hRx_sq : |x| ^ 2 ≤ R ^ 2 := by
    have := mul_le_mul habsx habsx hx_nn hR
    simpa [pow_two] using this
  have hRy_sq : |y| ^ 2 ≤ R ^ 2 := by
    have := mul_le_mul habsy habsy hy_nn hR
    simpa [pow_two] using this
  have hRx_cu : |x| ^ 3 ≤ R ^ 3 := by
    have h1 : |x| ^ 2 * |x| ≤ R ^ 2 * R := by
      exact mul_le_mul hRx_sq habsx hx_nn (by positivity)
    calc |x| ^ 3 = |x| ^ 2 * |x| := by ring
      _ ≤ R ^ 2 * R := h1
      _ = R ^ 3 := by ring
  have hRy_cu : |y| ^ 3 ≤ R ^ 3 := by
    have h1 : |y| ^ 2 * |y| ≤ R ^ 2 * R := by
      exact mul_le_mul hRy_sq habsy hy_nn (by positivity)
    calc |y| ^ 3 = |y| ^ 2 * |y| := by ring
      _ ≤ R ^ 2 * R := h1
      _ = R ^ 3 := by ring
  have hRx_4 : |x| ^ 4 ≤ R ^ 4 := by
    have h1 : |x| ^ 3 * |x| ≤ R ^ 3 * R :=
      mul_le_mul hRx_cu habsx hx_nn (by positivity)
    calc |x| ^ 4 = |x| ^ 3 * |x| := by ring
      _ ≤ R ^ 3 * R := h1
      _ = R ^ 4 := by ring
  have hRy_4 : |y| ^ 4 ≤ R ^ 4 := by
    have h1 : |y| ^ 3 * |y| ≤ R ^ 3 * R :=
      mul_le_mul hRy_cu habsy hy_nn (by positivity)
    calc |y| ^ 4 = |y| ^ 3 * |y| := by ring
      _ ≤ R ^ 3 * R := h1
      _ = R ^ 4 := by ring
  -- Now bound |x^4 + x^3 y + x²y² + xy³ + y^4| via triangle inequality.
  have habs4 : |x ^ 4| ≤ R ^ 4 := by rw [abs_pow]; exact hRx_4
  have habs_x3y : |x ^ 3 * y| ≤ R ^ 4 := by
    rw [abs_mul, abs_pow]
    calc |x| ^ 3 * |y| ≤ R ^ 3 * R := mul_le_mul hRx_cu habsy hy_nn (by positivity)
      _ = R ^ 4 := by ring
  have habs_x2y2 : |x ^ 2 * y ^ 2| ≤ R ^ 4 := by
    rw [abs_mul, abs_pow, abs_pow]
    calc |x| ^ 2 * |y| ^ 2 ≤ R ^ 2 * R ^ 2 :=
          mul_le_mul hRx_sq hRy_sq (by positivity) (by positivity)
      _ = R ^ 4 := by ring
  have habs_xy3 : |x * y ^ 3| ≤ R ^ 4 := by
    rw [abs_mul, abs_pow]
    calc |x| * |y| ^ 3 ≤ R * R ^ 3 := mul_le_mul habsx hRy_cu (by positivity) hR
      _ = R ^ 4 := by ring
  have habs_y4 : |y ^ 4| ≤ R ^ 4 := by rw [abs_pow]; exact hRy_4
  have h_bound : |x ^ 4 + x ^ 3 * y + x ^ 2 * y ^ 2 + x * y ^ 3 + y ^ 4| ≤ 5 * R ^ 4 := by
    have t1 := abs_add_le (x^4 + x^3 * y + x^2 * y^2 + x * y^3) (y^4)
    have t2 := abs_add_le (x^4 + x^3 * y + x^2 * y^2) (x * y^3)
    have t3 := abs_add_le (x^4 + x^3 * y) (x^2 * y^2)
    have t4 := abs_add_le (x^4) (x^3 * y)
    linarith
  calc |x - y| * |x ^ 4 + x ^ 3 * y + x ^ 2 * y ^ 2 + x * y ^ 3 + y ^ 4|
      ≤ |x - y| * (5 * R ^ 4) :=
        mul_le_mul_of_nonneg_left h_bound (abs_nonneg _)
    _ = 5 * R ^ 4 * |x - y| := by ring

/-- Lipschitz estimate for `(·)^4` on balls: `|x⁴ − y⁴| ≤ 4 R³ |x − y|`
when `|x|, |y| ≤ R`. Derived from the factoring
`x⁴ − y⁴ = (x − y)(x³ + x²y + xy² + y³)`. -/
private lemma fourth_power_lipschitz_on_ball (R : ℝ) (hR : 0 ≤ R)
    (x y : ℝ) (hx : |x| ≤ R) (hy : |y| ≤ R) :
    |x ^ 4 - y ^ 4| ≤ 4 * R ^ 3 * |x - y| := by
  have hfactor : x ^ 4 - y ^ 4
      = (x - y) * (x ^ 3 + x ^ 2 * y + x * y ^ 2 + y ^ 3) := by ring
  rw [hfactor, abs_mul]
  have hx_nn : 0 ≤ |x| := abs_nonneg _
  have hy_nn : 0 ≤ |y| := abs_nonneg _
  have hRx_sq : |x| ^ 2 ≤ R ^ 2 := by
    have := mul_le_mul hx hx hx_nn hR; simpa [pow_two] using this
  have hRy_sq : |y| ^ 2 ≤ R ^ 2 := by
    have := mul_le_mul hy hy hy_nn hR; simpa [pow_two] using this
  have hRx_cu : |x| ^ 3 ≤ R ^ 3 := by
    have h1 : |x| ^ 2 * |x| ≤ R ^ 2 * R :=
      mul_le_mul hRx_sq hx hx_nn (by positivity)
    calc |x| ^ 3 = |x| ^ 2 * |x| := by ring
      _ ≤ R ^ 2 * R := h1
      _ = R ^ 3 := by ring
  have hRy_cu : |y| ^ 3 ≤ R ^ 3 := by
    have h1 : |y| ^ 2 * |y| ≤ R ^ 2 * R :=
      mul_le_mul hRy_sq hy hy_nn (by positivity)
    calc |y| ^ 3 = |y| ^ 2 * |y| := by ring
      _ ≤ R ^ 2 * R := h1
      _ = R ^ 3 := by ring
  have habs_x3 : |x ^ 3| ≤ R ^ 3 := by rw [abs_pow]; exact hRx_cu
  have habs_x2y : |x ^ 2 * y| ≤ R ^ 3 := by
    rw [abs_mul, abs_pow]
    calc |x| ^ 2 * |y| ≤ R ^ 2 * R := mul_le_mul hRx_sq hy hy_nn (by positivity)
      _ = R ^ 3 := by ring
  have habs_xy2 : |x * y ^ 2| ≤ R ^ 3 := by
    rw [abs_mul, abs_pow]
    calc |x| * |y| ^ 2 ≤ R * R ^ 2 := mul_le_mul hx hRy_sq (by positivity) hR
      _ = R ^ 3 := by ring
  have habs_y3 : |y ^ 3| ≤ R ^ 3 := by rw [abs_pow]; exact hRy_cu
  have h_bound : |x ^ 3 + x ^ 2 * y + x * y ^ 2 + y ^ 3| ≤ 4 * R ^ 3 := by
    have t1 := abs_add_le (x^3 + x^2 * y + x * y^2) (y^3)
    have t2 := abs_add_le (x^3 + x^2 * y) (x * y^2)
    have t3 := abs_add_le (x^3) (x^2 * y)
    linarith
  calc |x - y| * |x ^ 3 + x ^ 2 * y + x * y ^ 2 + y ^ 3|
      ≤ |x - y| * (4 * R ^ 3) :=
        mul_le_mul_of_nonneg_left h_bound (abs_nonneg _)
    _ = 4 * R ^ 3 * |x - y| := by ring

/-- Lipschitz estimate for `(·)^3` on balls: `|x³ − y³| ≤ 3 R² |x − y|`
when `|x|, |y| ≤ R`. -/
private lemma third_power_lipschitz_on_ball (R : ℝ) (hR : 0 ≤ R)
    (x y : ℝ) (hx : |x| ≤ R) (hy : |y| ≤ R) :
    |x ^ 3 - y ^ 3| ≤ 3 * R ^ 2 * |x - y| := by
  have hfactor : x ^ 3 - y ^ 3 = (x - y) * (x ^ 2 + x * y + y ^ 2) := by ring
  rw [hfactor, abs_mul]
  have hx_nn : 0 ≤ |x| := abs_nonneg _
  have hy_nn : 0 ≤ |y| := abs_nonneg _
  have hRx_sq : |x| ^ 2 ≤ R ^ 2 := by
    have := mul_le_mul hx hx hx_nn hR; simpa [pow_two] using this
  have hRy_sq : |y| ^ 2 ≤ R ^ 2 := by
    have := mul_le_mul hy hy hy_nn hR; simpa [pow_two] using this
  have habs_x2 : |x ^ 2| ≤ R ^ 2 := by rw [abs_pow]; exact hRx_sq
  have habs_xy : |x * y| ≤ R ^ 2 := by
    rw [abs_mul]
    calc |x| * |y| ≤ R * R := mul_le_mul hx hy hy_nn hR
      _ = R ^ 2 := by ring
  have habs_y2 : |y ^ 2| ≤ R ^ 2 := by rw [abs_pow]; exact hRy_sq
  have h_bound : |x ^ 2 + x * y + y ^ 2| ≤ 3 * R ^ 2 := by
    have t1 := abs_add_le (x^2 + x * y) (y^2)
    have t2 := abs_add_le (x^2) (x * y)
    linarith
  calc |x - y| * |x ^ 2 + x * y + y ^ 2|
      ≤ |x - y| * (3 * R ^ 2) :=
        mul_le_mul_of_nonneg_left h_bound (abs_nonneg _)
    _ = 3 * R ^ 2 * |x - y| := by ring

/-- Explicit component drift for row 0 of the dual-railed quintic. -/
private theorem dualRailedQuintic_drift0 (k : ℚ) (w : Fin 2 → ℝ) :
    (dualRailedQuintic k).evalField w 0
      = 1 + 5 * (w 0) ^ 4 * (w 1) + 10 * (w 0) ^ 2 * (w 1) ^ 3 + (w 1) ^ 5
        - (k : ℝ) * (w 0) * (w 1) := by
  have hrow0 :
      (dualRailedQuintic k).evalField w 0
        = (dualRailPosPart 1 quinticField 0).eval₂ (Rat.castHom ℝ) w
          - (k : ℝ) * w 0 * w 1 := by
    unfold dualRailedQuintic PolyPIVP.evalField constantAnnihilationDualRail
    simp [MvPolynomial.eval₂_sub, MvPolynomial.eval₂_mul,
      MvPolynomial.eval₂_C, MvPolynomial.eval₂_X]
  rw [hrow0, dualRailPosPart_quintic_eval]

/-- Explicit component drift for row 1 of the dual-railed quintic. -/
private theorem dualRailedQuintic_drift1 (k : ℚ) (w : Fin 2 → ℝ) :
    (dualRailedQuintic k).evalField w 1
      = (w 0) ^ 5 + 10 * (w 0) ^ 3 * (w 1) ^ 2 + 5 * (w 0) * (w 1) ^ 4
        - (k : ℝ) * (w 0) * (w 1) := by
  have hrow1 :
      (dualRailedQuintic k).evalField w 1
        = (dualRailNegPart 1 quinticField 0).eval₂ (Rat.castHom ℝ) w
          - (k : ℝ) * w 0 * w 1 := by
    unfold dualRailedQuintic PolyPIVP.evalField constantAnnihilationDualRail
    simp [MvPolynomial.eval₂_sub, MvPolynomial.eval₂_mul,
      MvPolynomial.eval₂_C, MvPolynomial.eval₂_X]
  rw [hrow1, dualRailNegPart_quintic_eval]

/-- Semantic CRN-implementability of the dual-railed quintic field. -/
private noncomputable def dualRailedQuintic_crn (k : ℚ) :
    IsCRNImplementable 2 (dualRailedQuintic k).evalField where
  prod := fun i w => match i with
    | ⟨0, _⟩ => 1 + 5 * (w 0) ^ 4 * (w 1) + 10 * (w 0) ^ 2 * (w 1) ^ 3 + (w 1) ^ 5
        + max (-(k : ℝ)) 0 * (w 0) * (w 1)
    | ⟨1, _⟩ => (w 0) ^ 5 + 10 * (w 0) ^ 3 * (w 1) ^ 2 + 5 * (w 0) * (w 1) ^ 4
        + max (-(k : ℝ)) 0 * (w 0) * (w 1)
  degr := fun i w => match i with
    | ⟨0, _⟩ => max (k : ℝ) 0 * (w 1)
    | ⟨1, _⟩ => max (k : ℝ) 0 * (w 0)
  prod_pos := by
    intro i w hw
    fin_cases i
    · have h0 := hw 0
      have h1 := hw 1
      have hkm : 0 ≤ max (-(k : ℝ)) 0 := le_max_right _ _
      have hterm : 0 ≤ max (-(k : ℝ)) 0 * (w 0) * (w 1) := by
        have : 0 ≤ max (-(k : ℝ)) 0 * (w 0) := mul_nonneg hkm h0
        exact mul_nonneg this h1
      have h5u4v : 0 ≤ 5 * (w 0) ^ 4 * (w 1) := by
        have : 0 ≤ 5 * (w 0) ^ 4 := by positivity
        exact mul_nonneg this h1
      have h10u2v3 : 0 ≤ 10 * (w 0) ^ 2 * (w 1) ^ 3 := by
        have hp1 : 0 ≤ 10 * (w 0) ^ 2 := by positivity
        have hp2 : 0 ≤ (w 1) ^ 3 := by positivity
        have := mul_nonneg hp1 hp2
        linarith [this]
      have hv5 : 0 ≤ (w 1) ^ 5 := by positivity
      linarith
    · have h0 := hw 0
      have h1 := hw 1
      have hkm : 0 ≤ max (-(k : ℝ)) 0 := le_max_right _ _
      have hterm : 0 ≤ max (-(k : ℝ)) 0 * (w 0) * (w 1) := by
        have : 0 ≤ max (-(k : ℝ)) 0 * (w 0) := mul_nonneg hkm h0
        exact mul_nonneg this h1
      have hu5 : 0 ≤ (w 0) ^ 5 := by positivity
      have h10u3v2 : 0 ≤ 10 * (w 0) ^ 3 * (w 1) ^ 2 := by
        have hp1 : 0 ≤ 10 * (w 0) ^ 3 := by positivity
        have hp2 : 0 ≤ (w 1) ^ 2 := by positivity
        have := mul_nonneg hp1 hp2
        linarith [this]
      have h5uv4 : 0 ≤ 5 * (w 0) * (w 1) ^ 4 := by
        have : 0 ≤ 5 * (w 0) := by positivity
        have hp2 : 0 ≤ (w 1) ^ 4 := by positivity
        exact mul_nonneg this hp2
      linarith
  degr_pos := by
    intro i w hw
    fin_cases i
    · exact mul_nonneg (le_max_right _ _) (hw 1)
    · exact mul_nonneg (le_max_right _ _) (hw 0)
  field_eq := by
    intro w i
    have hsplit : max (k : ℝ) 0 - max (-(k : ℝ)) 0 = (k : ℝ) := by
      rcases le_or_gt 0 (k : ℝ) with hk | hk
      · rw [max_eq_left hk, max_eq_right (by linarith : -(k : ℝ) ≤ 0)]; ring
      · rw [max_eq_right hk.le, max_eq_left (by linarith : 0 ≤ -(k : ℝ))]; ring
    fin_cases i
    · have h0 := dualRailedQuintic_drift0 k w
      show (dualRailedQuintic k).evalField w 0 = _
      rw [h0]
      show 1 + 5 * w 0 ^ 4 * w 1 + 10 * w 0 ^ 2 * w 1 ^ 3 + w 1 ^ 5
          - (k : ℝ) * w 0 * w 1
        = (1 + 5 * w 0 ^ 4 * w 1 + 10 * w 0 ^ 2 * w 1 ^ 3 + w 1 ^ 5
            + max (-(k : ℝ)) 0 * w 0 * w 1)
          - max (k : ℝ) 0 * w 1 * w 0
      linear_combination (w 0 * w 1) * hsplit
    · have h1 := dualRailedQuintic_drift1 k w
      show (dualRailedQuintic k).evalField w 1 = _
      rw [h1]
      show w 0 ^ 5 + 10 * w 0 ^ 3 * w 1 ^ 2 + 5 * w 0 * w 1 ^ 4
          - (k : ℝ) * w 0 * w 1
        = (w 0 ^ 5 + 10 * w 0 ^ 3 * w 1 ^ 2 + 5 * w 0 * w 1 ^ 4
            + max (-(k : ℝ)) 0 * w 0 * w 1)
          - max (k : ℝ) 0 * w 0 * w 1
      linear_combination (w 0 * w 1) * hsplit

/-- Local Lipschitz estimate for the dual-railed quintic field on norm balls.
The field has total degree 5 in (u, v); a generous loose bound is
`L = 64 · (R^4 + |k|·R + 1)`. -/
private lemma dualRailedQuintic_lipschitz (k : ℚ) :
    ∀ R : ℝ, 0 < R → ∃ L : ℝ, ∀ x y : Fin 2 → ℝ,
      ‖x‖ ≤ R → ‖y‖ ≤ R →
      ‖(dualRailedQuintic k).evalField x - (dualRailedQuintic k).evalField y‖
        ≤ L * ‖x - y‖ := by
  intro R hR
  refine ⟨128 * (R^4 + |(k : ℝ)| * R + 1), ?_⟩
  intro x y hx hy
  have hx0 : |x 0| ≤ R := by
    have := norm_le_pi_norm x 0; rw [Real.norm_eq_abs] at this; linarith
  have hx1 : |x 1| ≤ R := by
    have := norm_le_pi_norm x 1; rw [Real.norm_eq_abs] at this; linarith
  have hy0 : |y 0| ≤ R := by
    have := norm_le_pi_norm y 0; rw [Real.norm_eq_abs] at this; linarith
  have hy1 : |y 1| ≤ R := by
    have := norm_le_pi_norm y 1; rw [Real.norm_eq_abs] at this; linarith
  have hdiff0 : |x 0 - y 0| ≤ ‖x - y‖ := by
    have := norm_le_pi_norm (x - y) 0
    rw [Real.norm_eq_abs] at this
    simpa [Pi.sub_apply] using this
  have hdiff1 : |x 1 - y 1| ≤ ‖x - y‖ := by
    have := norm_le_pi_norm (x - y) 1
    rw [Real.norm_eq_abs] at this
    simpa [Pi.sub_apply] using this
  have hxy_nn : 0 ≤ ‖x - y‖ := norm_nonneg _
  have hR_nn : 0 ≤ R := hR.le
  have hL_nn : 0 ≤ 128 * (R^4 + |(k : ℝ)| * R + 1) := by
    have hR4 : 0 ≤ R^4 := by positivity
    have h2 : 0 ≤ |(k : ℝ)| * R := mul_nonneg (abs_nonneg _) hR_nn
    have : 0 ≤ R^4 + |(k : ℝ)| * R + 1 := by linarith
    linarith
  -- Key bounds on monomial differences up to degree 5.
  -- We'll reduce to per-coordinate bounds of the form |A(x) - A(y)| ≤ C_A · (|x₀-y₀| + |x₁-y₁|).
  -- For the quintic case each component drift is a sum of monomials of total degree ≤ 5.
  --
  -- Instead of handling each monomial in detail, we observe that each drift row is a
  -- polynomial on the ball {|x₀|, |x₁| ≤ R}, and bound it by the max-norm polynomial.
  -- The key insight: |x^a y^b - u^a v^b| ≤ (a+b) R^{a+b-1} · max(|x-u|, |y-v|) on the ball.
  -- We just need concrete Lipschitz constants for each monomial:
  --   |x^5 - y^5|  ≤ 5 R^4 |x-y|
  --   |x^4·y - u^4·v|  ≤ 4R^4 |x-u| + R^4 |y-v|
  --   etc.
  -- We bound each row by a crude constant: each monomial of degree d yields ≤ d · R^{d-1} per variable
  -- difference; with max coefficient 10 and d ≤ 5, each term contributes ≤ 50 R^4 to each diff.
  -- With 4 pos monomials and 3 neg monomials + 1 linear term, the total is ≲ 50·7·R^4 ≲ 350 R^4.
  -- A factor 128 is more than enough (128 > 64 · 2).

  -- Monomial Lipschitz on ball (helper, inline).
  -- |u^a·v^b - u'^a·v'^b| ≤ a·R^{a+b-1}·|u-u'| + b·R^{a+b-1}·|v-v'|
  -- Proven via telescoping:
  -- u^a v^b - u'^a v'^b = (u^a - u'^a) v^b + u'^a (v^b - v'^b).

  -- We invoke nlinarith with a huge bag of sq_nonneg / mul hypotheses. This works for the
  -- quintic because all monomial differences break down to sums of products of differences.

  have coord_bound : ∀ i : Fin 2,
      |(dualRailedQuintic k).evalField x i - (dualRailedQuintic k).evalField y i|
        ≤ 128 * (R^4 + |(k : ℝ)| * R + 1) * ‖x - y‖ := by
    intro i
    fin_cases i
    · -- Row 0: Δ = (1 + 5x₀⁴x₁ + 10x₀²x₁³ + x₁⁵ - k x₀x₁) - (same with y).
      have hx_d0 := dualRailedQuintic_drift0 k x
      have hy_d0 := dualRailedQuintic_drift0 k y
      change |(dualRailedQuintic k).evalField x 0 - (dualRailedQuintic k).evalField y 0|
        ≤ 128 * (R^4 + |(k : ℝ)| * R + 1) * ‖x - y‖
      rw [hx_d0, hy_d0]
      have h_expand :
          (1 + 5 * (x 0) ^ 4 * (x 1) + 10 * (x 0) ^ 2 * (x 1) ^ 3 + (x 1) ^ 5
            - (k : ℝ) * (x 0) * (x 1))
          - (1 + 5 * (y 0) ^ 4 * (y 1) + 10 * (y 0) ^ 2 * (y 1) ^ 3 + (y 1) ^ 5
            - (k : ℝ) * (y 0) * (y 1))
          = 5 * ((x 0)^4 * (x 1) - (y 0)^4 * (y 1))
            + 10 * ((x 0)^2 * (x 1)^3 - (y 0)^2 * (y 1)^3)
            + ((x 1)^5 - (y 1)^5)
            + (-(k : ℝ)) * ((x 0) * (x 1) - (y 0) * (y 1)) := by ring
      rw [h_expand]
      -- Bounds on the four pieces.
      have h5 : |(x 1)^5 - (y 1)^5| ≤ 5 * R^4 * |x 1 - y 1| :=
        fifth_power_lipschitz_on_ball R hR_nn (x 1) (y 1) hx1 hy1
      -- |x₀⁴ - y₀⁴| ≤ 4 R³ |x₀ - y₀|.
      have h4pow : |(x 0)^4 - (y 0)^4| ≤ 4 * R^3 * |x 0 - y 0| :=
        fourth_power_lipschitz_on_ball R hR_nn (x 0) (y 0) hx0 hy0
      -- |x₀⁴x₁ - y₀⁴y₁| ≤ |x₀⁴ - y₀⁴|·|x₁| + |y₀⁴|·|x₁ - y₁| ≤ 4R⁴·|x₀-y₀| + R⁴·|x₁-y₁|.
      have h_x04x1 : |(x 0)^4 * (x 1) - (y 0)^4 * (y 1)|
          ≤ 4 * R^4 * |x 0 - y 0| + R^4 * |x 1 - y 1| := by
        have h_eq : (x 0)^4 * (x 1) - (y 0)^4 * (y 1)
            = ((x 0)^4 - (y 0)^4) * (x 1) + (y 0)^4 * ((x 1) - (y 1)) := by ring
        rw [h_eq]
        have h1 := abs_add_le (((x 0)^4 - (y 0)^4) * (x 1))
                              ((y 0)^4 * ((x 1) - (y 1)))
        have h2 : |((x 0)^4 - (y 0)^4) * (x 1)| ≤ (4 * R^3 * |x 0 - y 0|) * R := by
          rw [abs_mul]
          have := mul_le_mul h4pow hx1 (abs_nonneg _)
            (by positivity : (0 : ℝ) ≤ 4 * R^3 * |x 0 - y 0|)
          linarith
        have h3 : |(y 0)^4 * ((x 1) - (y 1))| ≤ R^4 * |x 1 - y 1| := by
          rw [abs_mul, abs_pow]
          have hy0_R : |y 0| ≤ R := hy0
          have h_abs_nn : 0 ≤ |y 0| := abs_nonneg _
          have hy0sq : |y 0|^2 ≤ R^2 := by
            have := mul_le_mul hy0_R hy0_R h_abs_nn hR_nn
            simpa [pow_two] using this
          have hy0_4 : |y 0|^4 ≤ R^4 := by
            have hsq_nn : 0 ≤ |y 0|^2 := by positivity
            have hRsq_nn : 0 ≤ R^2 := by positivity
            have := mul_le_mul hy0sq hy0sq hsq_nn hRsq_nn
            calc |y 0|^4 = |y 0|^2 * |y 0|^2 := by ring
              _ ≤ R^2 * R^2 := this
              _ = R^4 := by ring
          exact mul_le_mul_of_nonneg_right hy0_4 (abs_nonneg _)
        calc |((x 0)^4 - (y 0)^4) * (x 1) + (y 0)^4 * ((x 1) - (y 1))|
            ≤ |((x 0)^4 - (y 0)^4) * (x 1)| + |(y 0)^4 * ((x 1) - (y 1))| := h1
          _ ≤ (4 * R^3 * |x 0 - y 0|) * R + R^4 * |x 1 - y 1| := by linarith
          _ = 4 * R^4 * |x 0 - y 0| + R^4 * |x 1 - y 1| := by ring
      -- |x₀² - y₀²| ≤ 2R·|x₀-y₀|.
      have h_x0sq : |(x 0)^2 - (y 0)^2| ≤ 2 * R * |x 0 - y 0| := by
        have hfact : (x 0)^2 - (y 0)^2 = (x 0 - y 0) * (x 0 + y 0) := by ring
        rw [hfact, abs_mul]
        have habsum : |x 0 + y 0| ≤ 2 * R := by
          have := abs_add_le (x 0) (y 0); linarith
        calc |x 0 - y 0| * |x 0 + y 0|
            ≤ |x 0 - y 0| * (2 * R) := mul_le_mul_of_nonneg_left habsum (abs_nonneg _)
          _ = 2 * R * |x 0 - y 0| := by ring
      -- |x₁³ - y₁³| ≤ 3R²·|x₁-y₁|.
      have h_x1cb : |(x 1)^3 - (y 1)^3| ≤ 3 * R^2 * |x 1 - y 1| :=
        third_power_lipschitz_on_ball R hR_nn (x 1) (y 1) hx1 hy1
      -- |x₀²·x₁³ - y₀²·y₁³| ≤ |x₀²-y₀²|·|x₁³| + |y₀²|·|x₁³-y₁³|
      --                     ≤ (2R·R³)·|x₀-y₀| + R²·3R²·|x₁-y₁|
      --                     = 2R⁴·|x₀-y₀| + 3R⁴·|x₁-y₁|.
      have h_x02x13 : |(x 0)^2 * (x 1)^3 - (y 0)^2 * (y 1)^3|
          ≤ 2 * R^4 * |x 0 - y 0| + 3 * R^4 * |x 1 - y 1| := by
        have h_eq : (x 0)^2 * (x 1)^3 - (y 0)^2 * (y 1)^3
            = ((x 0)^2 - (y 0)^2) * (x 1)^3 + (y 0)^2 * ((x 1)^3 - (y 1)^3) := by ring
        rw [h_eq]
        have h1 := abs_add_le (((x 0)^2 - (y 0)^2) * (x 1)^3)
                              ((y 0)^2 * ((x 1)^3 - (y 1)^3))
        have h2 : |((x 0)^2 - (y 0)^2) * (x 1)^3| ≤ (2 * R * |x 0 - y 0|) * R^3 := by
          rw [abs_mul, abs_pow]
          have h_abs_nn : 0 ≤ |x 1| := abs_nonneg _
          have hx1sq : |x 1|^2 ≤ R^2 := by
            have := mul_le_mul hx1 hx1 h_abs_nn hR_nn
            simpa [pow_two] using this
          have hx1_3 : |x 1|^3 ≤ R^3 := by
            have := mul_le_mul hx1sq hx1 h_abs_nn (by positivity)
            calc |x 1|^3 = |x 1|^2 * |x 1| := by ring
              _ ≤ R^2 * R := this
              _ = R^3 := by ring
          have := mul_le_mul h_x0sq hx1_3 (by positivity) (by positivity)
          linarith
        have h3 : |(y 0)^2 * ((x 1)^3 - (y 1)^3)| ≤ R^2 * (3 * R^2 * |x 1 - y 1|) := by
          rw [abs_mul, abs_pow]
          have h_abs_nn : 0 ≤ |y 0| := abs_nonneg _
          have hy0_2 : |y 0|^2 ≤ R^2 := by
            have := mul_le_mul hy0 hy0 h_abs_nn hR_nn
            simpa [pow_two] using this
          have := mul_le_mul hy0_2 h_x1cb (by positivity) (by positivity)
          linarith
        calc |((x 0)^2 - (y 0)^2) * (x 1)^3 + (y 0)^2 * ((x 1)^3 - (y 1)^3)|
            ≤ |((x 0)^2 - (y 0)^2) * (x 1)^3| + |(y 0)^2 * ((x 1)^3 - (y 1)^3)| := h1
          _ ≤ (2 * R * |x 0 - y 0|) * R^3 + R^2 * (3 * R^2 * |x 1 - y 1|) := by linarith
          _ = 2 * R^4 * |x 0 - y 0| + 3 * R^4 * |x 1 - y 1| := by ring
      -- |x₀·x₁ - y₀·y₁| ≤ R·|x₀-y₀| + R·|x₁-y₁|.
      have h_prod : |(x 0) * (x 1) - (y 0) * (y 1)|
          ≤ R * |x 0 - y 0| + R * |x 1 - y 1| := by
        have h_eq : (x 0) * (x 1) - (y 0) * (y 1)
            = (x 0 - y 0) * (x 1) + (y 0) * ((x 1) - (y 1)) := by ring
        rw [h_eq]
        have h1 := abs_add_le ((x 0 - y 0) * (x 1)) ((y 0) * ((x 1) - (y 1)))
        have h2 : |(x 0 - y 0) * (x 1)| ≤ |x 0 - y 0| * R := by
          rw [abs_mul]
          exact mul_le_mul_of_nonneg_left hx1 (abs_nonneg _)
        have h3 : |(y 0) * ((x 1) - (y 1))| ≤ R * |x 1 - y 1| := by
          rw [abs_mul]
          exact mul_le_mul_of_nonneg_right hy0 (abs_nonneg _)
        calc |(x 0 - y 0) * (x 1) + (y 0) * ((x 1) - (y 1))|
            ≤ |(x 0 - y 0) * (x 1)| + |(y 0) * ((x 1) - (y 1))| := h1
          _ ≤ |x 0 - y 0| * R + R * |x 1 - y 1| := by linarith
          _ = R * |x 0 - y 0| + R * |x 1 - y 1| := by ring
      -- Combine.
      calc |5 * ((x 0)^4 * (x 1) - (y 0)^4 * (y 1))
              + 10 * ((x 0)^2 * (x 1)^3 - (y 0)^2 * (y 1)^3)
              + ((x 1)^5 - (y 1)^5)
              + (-(k : ℝ)) * ((x 0) * (x 1) - (y 0) * (y 1))|
          ≤ |5 * ((x 0)^4 * (x 1) - (y 0)^4 * (y 1))|
              + |10 * ((x 0)^2 * (x 1)^3 - (y 0)^2 * (y 1)^3)|
              + |((x 1)^5 - (y 1)^5)|
              + |(-(k : ℝ)) * ((x 0) * (x 1) - (y 0) * (y 1))| := by
            have h1 := abs_add_le (5 * ((x 0)^4 * (x 1) - (y 0)^4 * (y 1))
                                  + 10 * ((x 0)^2 * (x 1)^3 - (y 0)^2 * (y 1)^3)
                                  + ((x 1)^5 - (y 1)^5))
                                ((-(k : ℝ)) * ((x 0) * (x 1) - (y 0) * (y 1)))
            have h2 := abs_add_le (5 * ((x 0)^4 * (x 1) - (y 0)^4 * (y 1))
                                  + 10 * ((x 0)^2 * (x 1)^3 - (y 0)^2 * (y 1)^3))
                                ((x 1)^5 - (y 1)^5)
            have h3 := abs_add_le (5 * ((x 0)^4 * (x 1) - (y 0)^4 * (y 1)))
                                (10 * ((x 0)^2 * (x 1)^3 - (y 0)^2 * (y 1)^3))
            linarith
        _ ≤ 5 * (4 * R^4 * |x 0 - y 0| + R^4 * |x 1 - y 1|)
              + 10 * (2 * R^4 * |x 0 - y 0| + 3 * R^4 * |x 1 - y 1|)
              + 5 * R^4 * |x 1 - y 1|
              + |(k : ℝ)| * (R * |x 0 - y 0| + R * |x 1 - y 1|) := by
            have hc1 : |5 * ((x 0)^4 * (x 1) - (y 0)^4 * (y 1))|
                = 5 * |(x 0)^4 * (x 1) - (y 0)^4 * (y 1)| := by
              rw [abs_mul]; norm_num
            have hc2 : |10 * ((x 0)^2 * (x 1)^3 - (y 0)^2 * (y 1)^3)|
                = 10 * |(x 0)^2 * (x 1)^3 - (y 0)^2 * (y 1)^3| := by
              rw [abs_mul]; norm_num
            have hc3 : |(-(k : ℝ)) * ((x 0) * (x 1) - (y 0) * (y 1))|
                = |(k : ℝ)| * |(x 0) * (x 1) - (y 0) * (y 1)| := by
              rw [abs_mul, abs_neg]
            rw [hc1, hc2, hc3]
            have h_abs_k_nn : 0 ≤ |(k : ℝ)| := abs_nonneg _
            have p1 := mul_le_mul_of_nonneg_left h_x04x1 (by norm_num : (0 : ℝ) ≤ 5)
            have p2 := mul_le_mul_of_nonneg_left h_x02x13 (by norm_num : (0 : ℝ) ≤ 10)
            have p3 := mul_le_mul_of_nonneg_left h_prod h_abs_k_nn
            linarith
        _ ≤ 128 * (R^4 + |(k : ℝ)| * R + 1) * ‖x - y‖ := by
            have h_abs_k_nn : 0 ≤ |(k : ℝ)| := abs_nonneg _
            have hR4_nn : 0 ≤ R^4 := by positivity
            have ha_nn : 0 ≤ |x 0 - y 0| := abs_nonneg _
            have hb_nn : 0 ≤ |x 1 - y 1| := abs_nonneg _
            have hkR_nn : 0 ≤ |(k : ℝ)| * R := mul_nonneg h_abs_k_nn hR_nn
            -- Group: LHS = 40·R^4·a + 40·R^4·b + |k|·R·(a+b)
            -- where a = |x₀-y₀|, b = |x₁-y₁|.
            have step1 :
                5 * (4 * R^4 * |x 0 - y 0| + R^4 * |x 1 - y 1|)
                + 10 * (2 * R^4 * |x 0 - y 0| + 3 * R^4 * |x 1 - y 1|)
                + 5 * R^4 * |x 1 - y 1|
                + |(k : ℝ)| * (R * |x 0 - y 0| + R * |x 1 - y 1|)
                = 40 * R^4 * |x 0 - y 0| + 40 * R^4 * |x 1 - y 1|
                  + |(k : ℝ)| * R * |x 0 - y 0| + |(k : ℝ)| * R * |x 1 - y 1| := by ring
            rw [step1]
            have hsum_nn : 0 ≤ R^4 + |(k : ℝ)| * R + 1 := by linarith
            have h128 : 0 ≤ 128 * (R^4 + |(k : ℝ)| * R + 1) := by linarith
            have hcombined : (80 * R^4 + 2 * (|(k : ℝ)| * R)) * ‖x - y‖
                ≤ 128 * (R^4 + |(k : ℝ)| * R + 1) * ‖x - y‖ := by
              apply mul_le_mul_of_nonneg_right _ hxy_nn
              have : 128 * (R^4 + |(k : ℝ)| * R + 1) - (80 * R^4 + 2 * (|(k : ℝ)| * R))
                  = 48 * R^4 + 126 * (|(k : ℝ)| * R) + 128 := by ring
              linarith [hkR_nn, hR4_nn, this]
            calc 40 * R^4 * |x 0 - y 0| + 40 * R^4 * |x 1 - y 1|
                + |(k : ℝ)| * R * |x 0 - y 0| + |(k : ℝ)| * R * |x 1 - y 1|
                ≤ 40 * R^4 * ‖x - y‖ + 40 * R^4 * ‖x - y‖
                  + |(k : ℝ)| * R * ‖x - y‖ + |(k : ℝ)| * R * ‖x - y‖ := by
                  have b1 : 40 * R^4 * |x 0 - y 0| ≤ 40 * R^4 * ‖x - y‖ :=
                    mul_le_mul_of_nonneg_left hdiff0 (by positivity)
                  have b2 : 40 * R^4 * |x 1 - y 1| ≤ 40 * R^4 * ‖x - y‖ :=
                    mul_le_mul_of_nonneg_left hdiff1 (by positivity)
                  have b3 : |(k : ℝ)| * R * |x 0 - y 0| ≤ |(k : ℝ)| * R * ‖x - y‖ :=
                    mul_le_mul_of_nonneg_left hdiff0 hkR_nn
                  have b4 : |(k : ℝ)| * R * |x 1 - y 1| ≤ |(k : ℝ)| * R * ‖x - y‖ :=
                    mul_le_mul_of_nonneg_left hdiff1 hkR_nn
                  linarith
              _ = (80 * R^4 + 2 * (|(k : ℝ)| * R)) * ‖x - y‖ := by ring
              _ ≤ 128 * (R^4 + |(k : ℝ)| * R + 1) * ‖x - y‖ := hcombined
    · -- Row 1: symmetric to row 0.
      have hx_d1 := dualRailedQuintic_drift1 k x
      have hy_d1 := dualRailedQuintic_drift1 k y
      change |(dualRailedQuintic k).evalField x 1 - (dualRailedQuintic k).evalField y 1|
        ≤ 128 * (R^4 + |(k : ℝ)| * R + 1) * ‖x - y‖
      rw [hx_d1, hy_d1]
      have h_expand :
          ((x 0)^5 + 10 * (x 0)^3 * (x 1)^2 + 5 * (x 0) * (x 1)^4
            - (k : ℝ) * (x 0) * (x 1))
          - ((y 0)^5 + 10 * (y 0)^3 * (y 1)^2 + 5 * (y 0) * (y 1)^4
            - (k : ℝ) * (y 0) * (y 1))
          = ((x 0)^5 - (y 0)^5)
            + 10 * ((x 0)^3 * (x 1)^2 - (y 0)^3 * (y 1)^2)
            + 5 * ((x 0) * (x 1)^4 - (y 0) * (y 1)^4)
            + (-(k : ℝ)) * ((x 0) * (x 1) - (y 0) * (y 1)) := by ring
      rw [h_expand]
      have h5 : |(x 0)^5 - (y 0)^5| ≤ 5 * R^4 * |x 0 - y 0| :=
        fifth_power_lipschitz_on_ball R hR_nn (x 0) (y 0) hx0 hy0
      -- |x₀³ - y₀³| ≤ 3R²·|x₀-y₀|.
      have h_x0cb : |(x 0)^3 - (y 0)^3| ≤ 3 * R^2 * |x 0 - y 0| :=
        third_power_lipschitz_on_ball R hR_nn (x 0) (y 0) hx0 hy0
      -- |x₁² - y₁²| ≤ 2R·|x₁-y₁|.
      have h_x1sq : |(x 1)^2 - (y 1)^2| ≤ 2 * R * |x 1 - y 1| := by
        have hfact : (x 1)^2 - (y 1)^2 = (x 1 - y 1) * (x 1 + y 1) := by ring
        rw [hfact, abs_mul]
        have habsum : |x 1 + y 1| ≤ 2 * R := by
          have := abs_add_le (x 1) (y 1); linarith
        calc |x 1 - y 1| * |x 1 + y 1|
            ≤ |x 1 - y 1| * (2 * R) := mul_le_mul_of_nonneg_left habsum (abs_nonneg _)
          _ = 2 * R * |x 1 - y 1| := by ring
      -- |x₁⁴ - y₁⁴| ≤ 4R³·|x₁-y₁|.
      have h_x1_4 : |(x 1)^4 - (y 1)^4| ≤ 4 * R^3 * |x 1 - y 1| :=
        fourth_power_lipschitz_on_ball R hR_nn (x 1) (y 1) hx1 hy1
      -- |x₀³·x₁² - y₀³·y₁²| ≤ 3R⁴·|x₀-y₀| + 2R⁴·|x₁-y₁|.
      have h_x03x12 : |(x 0)^3 * (x 1)^2 - (y 0)^3 * (y 1)^2|
          ≤ 3 * R^4 * |x 0 - y 0| + 2 * R^4 * |x 1 - y 1| := by
        have h_eq : (x 0)^3 * (x 1)^2 - (y 0)^3 * (y 1)^2
            = ((x 0)^3 - (y 0)^3) * (x 1)^2 + (y 0)^3 * ((x 1)^2 - (y 1)^2) := by ring
        rw [h_eq]
        have h1 := abs_add_le (((x 0)^3 - (y 0)^3) * (x 1)^2)
                              ((y 0)^3 * ((x 1)^2 - (y 1)^2))
        have h2 : |((x 0)^3 - (y 0)^3) * (x 1)^2| ≤ (3 * R^2 * |x 0 - y 0|) * R^2 := by
          rw [abs_mul, abs_pow]
          have h_abs_nn : 0 ≤ |x 1| := abs_nonneg _
          have hx1_2 : |x 1|^2 ≤ R^2 := by
            have := mul_le_mul hx1 hx1 h_abs_nn hR_nn
            simpa [pow_two] using this
          have := mul_le_mul h_x0cb hx1_2 (by positivity) (by positivity)
          linarith
        have h3 : |(y 0)^3 * ((x 1)^2 - (y 1)^2)| ≤ R^3 * (2 * R * |x 1 - y 1|) := by
          rw [abs_mul, abs_pow]
          have h_abs_nn : 0 ≤ |y 0| := abs_nonneg _
          have hy0_2 : |y 0|^2 ≤ R^2 := by
            have := mul_le_mul hy0 hy0 h_abs_nn hR_nn
            simpa [pow_two] using this
          have hy0_3 : |y 0|^3 ≤ R^3 := by
            have := mul_le_mul hy0_2 hy0 h_abs_nn (by positivity)
            calc |y 0|^3 = |y 0|^2 * |y 0| := by ring
              _ ≤ R^2 * R := this
              _ = R^3 := by ring
          have := mul_le_mul hy0_3 h_x1sq (by positivity) (by positivity)
          linarith
        calc |((x 0)^3 - (y 0)^3) * (x 1)^2 + (y 0)^3 * ((x 1)^2 - (y 1)^2)|
            ≤ |((x 0)^3 - (y 0)^3) * (x 1)^2| + |(y 0)^3 * ((x 1)^2 - (y 1)^2)| := h1
          _ ≤ (3 * R^2 * |x 0 - y 0|) * R^2 + R^3 * (2 * R * |x 1 - y 1|) := by linarith
          _ = 3 * R^4 * |x 0 - y 0| + 2 * R^4 * |x 1 - y 1| := by ring
      -- |x₀·x₁⁴ - y₀·y₁⁴| ≤ R⁴·|x₀-y₀| + 4R⁴·|x₁-y₁|.
      have h_x01x14 : |(x 0) * (x 1)^4 - (y 0) * (y 1)^4|
          ≤ R^4 * |x 0 - y 0| + 4 * R^4 * |x 1 - y 1| := by
        have h_eq : (x 0) * (x 1)^4 - (y 0) * (y 1)^4
            = ((x 0) - (y 0)) * (x 1)^4 + (y 0) * ((x 1)^4 - (y 1)^4) := by ring
        rw [h_eq]
        have h1 := abs_add_le (((x 0) - (y 0)) * (x 1)^4)
                              ((y 0) * ((x 1)^4 - (y 1)^4))
        have h2 : |((x 0) - (y 0)) * (x 1)^4| ≤ |x 0 - y 0| * R^4 := by
          rw [abs_mul, abs_pow]
          have h_abs_nn : 0 ≤ |x 1| := abs_nonneg _
          have hx1_2 : |x 1|^2 ≤ R^2 := by
            have := mul_le_mul hx1 hx1 h_abs_nn hR_nn
            simpa [pow_two] using this
          have hRsq_nn : 0 ≤ R^2 := by positivity
          have hx1sq_nn : 0 ≤ |x 1|^2 := by positivity
          have hx1_4 : |x 1|^4 ≤ R^4 := by
            have := mul_le_mul hx1_2 hx1_2 hx1sq_nn hRsq_nn
            calc |x 1|^4 = |x 1|^2 * |x 1|^2 := by ring
              _ ≤ R^2 * R^2 := this
              _ = R^4 := by ring
          exact mul_le_mul_of_nonneg_left hx1_4 (abs_nonneg _)
        have h3 : |(y 0) * ((x 1)^4 - (y 1)^4)| ≤ R * (4 * R^3 * |x 1 - y 1|) := by
          rw [abs_mul]
          have := mul_le_mul hy0 h_x1_4 (by positivity) hR_nn
          linarith
        calc |((x 0) - (y 0)) * (x 1)^4 + (y 0) * ((x 1)^4 - (y 1)^4)|
            ≤ |((x 0) - (y 0)) * (x 1)^4| + |(y 0) * ((x 1)^4 - (y 1)^4)| := h1
          _ ≤ |x 0 - y 0| * R^4 + R * (4 * R^3 * |x 1 - y 1|) := by linarith
          _ = R^4 * |x 0 - y 0| + 4 * R^4 * |x 1 - y 1| := by ring
      -- |x₀·x₁ - y₀·y₁| ≤ R·|x₀-y₀| + R·|x₁-y₁|.
      have h_prod : |(x 0) * (x 1) - (y 0) * (y 1)|
          ≤ R * |x 0 - y 0| + R * |x 1 - y 1| := by
        have h_eq : (x 0) * (x 1) - (y 0) * (y 1)
            = (x 0 - y 0) * (x 1) + (y 0) * ((x 1) - (y 1)) := by ring
        rw [h_eq]
        have h1 := abs_add_le ((x 0 - y 0) * (x 1)) ((y 0) * ((x 1) - (y 1)))
        have h2 : |(x 0 - y 0) * (x 1)| ≤ |x 0 - y 0| * R := by
          rw [abs_mul]
          exact mul_le_mul_of_nonneg_left hx1 (abs_nonneg _)
        have h3 : |(y 0) * ((x 1) - (y 1))| ≤ R * |x 1 - y 1| := by
          rw [abs_mul]
          exact mul_le_mul_of_nonneg_right hy0 (abs_nonneg _)
        calc |(x 0 - y 0) * (x 1) + (y 0) * ((x 1) - (y 1))|
            ≤ |(x 0 - y 0) * (x 1)| + |(y 0) * ((x 1) - (y 1))| := h1
          _ ≤ |x 0 - y 0| * R + R * |x 1 - y 1| := by linarith
          _ = R * |x 0 - y 0| + R * |x 1 - y 1| := by ring
      calc |((x 0)^5 - (y 0)^5)
              + 10 * ((x 0)^3 * (x 1)^2 - (y 0)^3 * (y 1)^2)
              + 5 * ((x 0) * (x 1)^4 - (y 0) * (y 1)^4)
              + (-(k : ℝ)) * ((x 0) * (x 1) - (y 0) * (y 1))|
          ≤ |((x 0)^5 - (y 0)^5)|
              + |10 * ((x 0)^3 * (x 1)^2 - (y 0)^3 * (y 1)^2)|
              + |5 * ((x 0) * (x 1)^4 - (y 0) * (y 1)^4)|
              + |(-(k : ℝ)) * ((x 0) * (x 1) - (y 0) * (y 1))| := by
            have h1 := abs_add_le (((x 0)^5 - (y 0)^5)
                                  + 10 * ((x 0)^3 * (x 1)^2 - (y 0)^3 * (y 1)^2)
                                  + 5 * ((x 0) * (x 1)^4 - (y 0) * (y 1)^4))
                                ((-(k : ℝ)) * ((x 0) * (x 1) - (y 0) * (y 1)))
            have h2 := abs_add_le (((x 0)^5 - (y 0)^5)
                                  + 10 * ((x 0)^3 * (x 1)^2 - (y 0)^3 * (y 1)^2))
                                (5 * ((x 0) * (x 1)^4 - (y 0) * (y 1)^4))
            have h3 := abs_add_le ((x 0)^5 - (y 0)^5)
                                (10 * ((x 0)^3 * (x 1)^2 - (y 0)^3 * (y 1)^2))
            linarith
        _ ≤ 5 * R^4 * |x 0 - y 0|
              + 10 * (3 * R^4 * |x 0 - y 0| + 2 * R^4 * |x 1 - y 1|)
              + 5 * (R^4 * |x 0 - y 0| + 4 * R^4 * |x 1 - y 1|)
              + |(k : ℝ)| * (R * |x 0 - y 0| + R * |x 1 - y 1|) := by
            have hc1 : |10 * ((x 0)^3 * (x 1)^2 - (y 0)^3 * (y 1)^2)|
                = 10 * |(x 0)^3 * (x 1)^2 - (y 0)^3 * (y 1)^2| := by
              rw [abs_mul]; norm_num
            have hc2 : |5 * ((x 0) * (x 1)^4 - (y 0) * (y 1)^4)|
                = 5 * |(x 0) * (x 1)^4 - (y 0) * (y 1)^4| := by
              rw [abs_mul]; norm_num
            have hc3 : |(-(k : ℝ)) * ((x 0) * (x 1) - (y 0) * (y 1))|
                = |(k : ℝ)| * |(x 0) * (x 1) - (y 0) * (y 1)| := by
              rw [abs_mul, abs_neg]
            rw [hc1, hc2, hc3]
            have h_abs_k_nn : 0 ≤ |(k : ℝ)| := abs_nonneg _
            have p1 := mul_le_mul_of_nonneg_left h_x03x12 (by norm_num : (0 : ℝ) ≤ 10)
            have p2 := mul_le_mul_of_nonneg_left h_x01x14 (by norm_num : (0 : ℝ) ≤ 5)
            have p3 := mul_le_mul_of_nonneg_left h_prod h_abs_k_nn
            linarith
        _ ≤ 128 * (R^4 + |(k : ℝ)| * R + 1) * ‖x - y‖ := by
            have h_abs_k_nn : 0 ≤ |(k : ℝ)| := abs_nonneg _
            have hR4_nn : 0 ≤ R^4 := by positivity
            have ha_nn : 0 ≤ |x 0 - y 0| := abs_nonneg _
            have hb_nn : 0 ≤ |x 1 - y 1| := abs_nonneg _
            have hkR_nn : 0 ≤ |(k : ℝ)| * R := mul_nonneg h_abs_k_nn hR_nn
            have step1 :
                5 * R^4 * |x 0 - y 0|
                + 10 * (3 * R^4 * |x 0 - y 0| + 2 * R^4 * |x 1 - y 1|)
                + 5 * (R^4 * |x 0 - y 0| + 4 * R^4 * |x 1 - y 1|)
                + |(k : ℝ)| * (R * |x 0 - y 0| + R * |x 1 - y 1|)
                = 40 * R^4 * |x 0 - y 0| + 40 * R^4 * |x 1 - y 1|
                  + |(k : ℝ)| * R * |x 0 - y 0| + |(k : ℝ)| * R * |x 1 - y 1| := by ring
            rw [step1]
            have hsum_nn : 0 ≤ R^4 + |(k : ℝ)| * R + 1 := by linarith
            have h128 : 0 ≤ 128 * (R^4 + |(k : ℝ)| * R + 1) := by linarith
            have hcombined : (80 * R^4 + 2 * (|(k : ℝ)| * R)) * ‖x - y‖
                ≤ 128 * (R^4 + |(k : ℝ)| * R + 1) * ‖x - y‖ := by
              apply mul_le_mul_of_nonneg_right _ hxy_nn
              have : 128 * (R^4 + |(k : ℝ)| * R + 1) - (80 * R^4 + 2 * (|(k : ℝ)| * R))
                  = 48 * R^4 + 126 * (|(k : ℝ)| * R) + 128 := by ring
              linarith [hkR_nn, hR4_nn, this]
            calc 40 * R^4 * |x 0 - y 0| + 40 * R^4 * |x 1 - y 1|
                + |(k : ℝ)| * R * |x 0 - y 0| + |(k : ℝ)| * R * |x 1 - y 1|
                ≤ 40 * R^4 * ‖x - y‖ + 40 * R^4 * ‖x - y‖
                  + |(k : ℝ)| * R * ‖x - y‖ + |(k : ℝ)| * R * ‖x - y‖ := by
                  have b1 : 40 * R^4 * |x 0 - y 0| ≤ 40 * R^4 * ‖x - y‖ :=
                    mul_le_mul_of_nonneg_left hdiff0 (by positivity)
                  have b2 : 40 * R^4 * |x 1 - y 1| ≤ 40 * R^4 * ‖x - y‖ :=
                    mul_le_mul_of_nonneg_left hdiff1 (by positivity)
                  have b3 : |(k : ℝ)| * R * |x 0 - y 0| ≤ |(k : ℝ)| * R * ‖x - y‖ :=
                    mul_le_mul_of_nonneg_left hdiff0 hkR_nn
                  have b4 : |(k : ℝ)| * R * |x 1 - y 1| ≤ |(k : ℝ)| * R * ‖x - y‖ :=
                    mul_le_mul_of_nonneg_left hdiff1 hkR_nn
                  linarith
              _ = (80 * R^4 + 2 * (|(k : ℝ)| * R)) * ‖x - y‖ := by ring
              _ ≤ 128 * (R^4 + |(k : ℝ)| * R + 1) * ‖x - y‖ := hcombined
  rw [pi_norm_le_iff_of_nonneg (by positivity)]
  intro i
  rw [Real.norm_eq_abs, Pi.sub_apply]
  exact coord_bound i

/-- **Sub-lemma 1: non-negativity of the dual-rail solution.** -/
theorem scalar_quintic_nonneg (k : ℚ) (sol : ℝ → Fin 2 → ℝ)
    (h_init : sol 0 = fun _ => 0)
    (h_deriv : ∀ t ≥ (0 : ℝ),
      HasDerivAt (fun s => sol s) ((dualRailedQuintic k).evalField (sol t)) t) :
    ∀ t ≥ (0 : ℝ), ∀ i, 0 ≤ sol t i := by
  intro t ht i
  have hT : (0 : ℝ) < t + 1 := by linarith
  have h_init_nn : ∀ j, 0 ≤ sol 0 j := fun j => by rw [h_init]
  have h_ode : ∀ s ∈ Set.Ico (0 : ℝ) (t + 1),
      HasDerivAt sol ((dualRailedQuintic k).evalField (sol s)) s := by
    intro s hs
    exact h_deriv s hs.1
  have h_crn := dualRailedQuintic_crn k
  have h_lip := dualRailedQuintic_lipschitz k
  have := crn_local_nonneg h_crn h_lip (t + 1) hT sol h_init_nn h_ode
    t ⟨ht, by linarith⟩ i
  exact this

/-- **Sub-lemma 2: dual-rail identity preservation.** -/
theorem scalar_quintic_dual_rail_identity (k : ℚ) (sol : ℝ → Fin 2 → ℝ)
    (h_deriv : ∀ t ≥ (0 : ℝ),
      HasDerivAt (fun s => sol s) ((dualRailedQuintic k).evalField (sol t)) t) :
    ∀ t ≥ (0 : ℝ),
      HasDerivAt (fun s => sol s 0 - sol s 1)
        (1 - (sol t 0 - sol t 1) ^ 5) t := by
  intro t ht
  have h := h_deriv t ht
  have hpi := (hasDerivAt_pi (φ := fun s => sol s)
    (φ' := (dualRailedQuintic k).evalField (sol t))).1 h
  have hu := hpi 0
  have hv := hpi 1
  have hdiff := hu.sub hv
  have heq := dualRailedQuintic_drift_diff k (sol t)
  rw [heq] at hdiff
  exact hdiff

/-! ### Barriers for the scalar quintic ODE `y' = 1 − y^5` -/

/-- Lower barrier (local): if `y(0) = 0` and `y' = 1 − y^5` on `[0, t]`,
then `0 ≤ y t`. Same sup-argument as cubic; `(y ξ)^5 < 0` when `y ξ < 0`. -/
private lemma scalar_quintic_lower_barrier_local
    {y : ℝ → ℝ} {t : ℝ}
    (ht_nn : 0 ≤ t)
    (hy0 : y 0 = 0)
    (hy_deriv : ∀ u, 0 ≤ u → u ≤ t → HasDerivAt y (1 - (y u) ^ 5) u) :
    0 ≤ y t := by
  by_contra h_neg
  push_neg at h_neg
  have hy_cont : ContinuousOn y (Set.Icc 0 t) := by
    intro u hu
    exact (hy_deriv u hu.1 hu.2).continuousAt.continuousWithinAt
  let S : Set ℝ := {u | u ∈ Set.Icc (0 : ℝ) t ∧ 0 ≤ y u}
  have h0_mem : (0 : ℝ) ∈ S := ⟨⟨le_refl _, ht_nn⟩, by rw [hy0]⟩
  have hS_bdd : BddAbove S := ⟨t, fun u hu => hu.1.2⟩
  have hS_nonempty : S.Nonempty := ⟨0, h0_mem⟩
  set s := sSup S with hs_def
  have hs_le_t : s ≤ t := csSup_le hS_nonempty (fun u hu => hu.1.2)
  have hs_nn : 0 ≤ s := le_csSup hS_bdd h0_mem
  have hs_in_Icc : s ∈ Set.Icc (0 : ℝ) t := ⟨hs_nn, hs_le_t⟩
  have hys_nn : 0 ≤ y s := by
    have hy_cont_s : ContinuousWithinAt y (Set.Icc 0 t) s :=
      hy_cont s hs_in_Icc
    rcases eq_or_lt_of_le hs_nn with hs_zero | hs_pos
    · rw [← hs_zero, hy0]
    · have h_seq : ∀ ε > 0, ∃ u ∈ S, s - ε < u ∧ u ≤ s := by
        intro ε hε
        obtain ⟨u, hu_mem, hu_lt⟩ :=
          exists_lt_of_lt_csSup hS_nonempty (show s - ε < s by linarith)
        exact ⟨u, hu_mem, hu_lt, le_csSup hS_bdd hu_mem⟩
      have : ∀ ε > 0, ∃ u ∈ Set.Icc (0:ℝ) t, |u - s| < ε ∧ 0 ≤ y u := by
        intro ε hε
        obtain ⟨u, ⟨hu1, hu2⟩, hu_lt, hu_le⟩ := h_seq ε hε
        refine ⟨u, hu1, ?_, hu2⟩
        rw [abs_sub_lt_iff]; exact ⟨by linarith, by linarith⟩
      by_contra h_ys_neg
      push_neg at h_ys_neg
      rw [Metric.continuousWithinAt_iff] at hy_cont_s
      obtain ⟨δ, hδ, hδ_prop⟩ := hy_cont_s (-y s / 2) (by linarith)
      obtain ⟨u, hu_in, hu_dist, hyu_nn⟩ := this δ hδ
      have := hδ_prop hu_in (by rw [Real.dist_eq]; exact hu_dist)
      rw [Real.dist_eq] at this
      have := abs_sub_lt_iff.mp this
      linarith
  have hs_lt_t : s < t := by
    rcases lt_or_eq_of_le hs_le_t with h | h
    · exact h
    · exfalso; rw [← h] at h_neg; linarith
  have hy_neg_on : ∀ u, s < u → u ≤ t → y u < 0 := by
    intro u hsu hut
    by_contra hu_nn
    push_neg at hu_nn
    have hu_in_S : u ∈ S :=
      ⟨⟨le_trans hs_nn (le_of_lt hsu), hut⟩, hu_nn⟩
    have : u ≤ s := le_csSup hS_bdd hu_in_S
    linarith
  have hys_zero : y s = 0 := by
    refine le_antisymm ?_ hys_nn
    by_contra h_pos
    push_neg at h_pos
    have hy_cont_s : ContinuousWithinAt y (Set.Icc 0 t) s :=
      hy_cont s hs_in_Icc
    rw [Metric.continuousWithinAt_iff] at hy_cont_s
    obtain ⟨δ, hδ, hδ_prop⟩ := hy_cont_s (y s) h_pos
    set u := min (s + δ / 2) t with hu_def
    have hu_lt_t : u ≤ t := min_le_right _ _
    have hsu : s < u := lt_min (by linarith) hs_lt_t
    have hu_mem : u ∈ Set.Icc (0 : ℝ) t :=
      ⟨le_trans hs_nn (le_of_lt hsu), hu_lt_t⟩
    have h_dist : dist u s < δ := by
      have h1 : u ≤ s + δ / 2 := min_le_left _ _
      rw [Real.dist_eq, abs_of_pos (by linarith : (0:ℝ) < u - s)]
      linarith
    have h_apply := hδ_prop hu_mem h_dist
    have hyu_close : |y u - y s| < y s := by rwa [Real.dist_eq] at h_apply
    have hyu_neg : y u < 0 := hy_neg_on u hsu hu_lt_t
    have : y u > 0 := by
      have := abs_sub_lt_iff.mp hyu_close; linarith
    linarith
  have hy_cont_st : ContinuousOn y (Set.Icc s t) :=
    hy_cont.mono (fun u hu => ⟨le_trans hs_nn hu.1, hu.2⟩)
  have hy_diff_st : ∀ u ∈ Set.Ioo s t, HasDerivAt y (1 - (y u) ^ 5) u := by
    intro u ⟨hu1, hu2⟩
    have hu_nn : 0 ≤ u := le_trans hs_nn (le_of_lt hu1)
    exact hy_deriv u hu_nn (le_of_lt hu2)
  obtain ⟨ξ, hξ_mem, hξ_eq⟩ :=
    exists_hasDerivAt_eq_slope y (fun u => 1 - (y u) ^ 5)
      hs_lt_t hy_cont_st (fun u hu => hy_diff_st u hu)
  have hy_ξ_neg : y ξ < 0 := hy_neg_on ξ hξ_mem.1 (le_of_lt hξ_mem.2)
  -- (y ξ)^5 < 0 since y ξ < 0.
  have h_fifth_neg : (y ξ) ^ 5 < 0 := by
    have hpos : 0 < -(y ξ) := by linarith
    have : 0 < (-(y ξ))^5 := by positivity
    have h_eq : (-(y ξ))^5 = -(y ξ)^5 := by ring
    rw [h_eq] at this; linarith
  have hξ_pos : 0 < 1 - (y ξ) ^ 5 := by linarith
  have htsub : 0 < t - s := by linarith
  rw [hys_zero, sub_zero] at hξ_eq
  have h1 : 0 < y t / (t - s) := hξ_eq ▸ hξ_pos
  have : 0 < y t := by
    have := mul_pos h1 htsub
    rw [div_mul_cancel₀ _ (ne_of_gt htsub)] at this
    exact this
  linarith

/-- Upper barrier (local): if `y(0) = 0` and `y' = 1 − y^5` on `[0, t]`,
then `y t ≤ 1`. ODE-uniqueness argument against constant `1`. -/
private lemma scalar_quintic_upper_barrier_local
    {y : ℝ → ℝ} {t : ℝ}
    (ht_nn : 0 ≤ t)
    (hy0 : y 0 = 0)
    (hy_deriv : ∀ u, 0 ≤ u → u ≤ t → HasDerivAt y (1 - (y u) ^ 5) u) :
    y t ≤ 1 := by
  by_contra h_gt
  push_neg at h_gt
  have hy_cont : ContinuousOn y (Set.Icc 0 t) := by
    intro u hu
    exact (hy_deriv u hu.1 hu.2).continuousAt.continuousWithinAt
  let S : Set ℝ := {u | u ∈ Set.Icc (0 : ℝ) t ∧ y u ≤ 1}
  have h0_mem : (0 : ℝ) ∈ S :=
    ⟨⟨le_refl _, ht_nn⟩, by rw [hy0]; norm_num⟩
  have hS_bdd : BddAbove S := ⟨t, fun u hu => hu.1.2⟩
  have hS_nonempty : S.Nonempty := ⟨0, h0_mem⟩
  set s := sSup S with hs_def
  have hs_le_t : s ≤ t := csSup_le hS_nonempty (fun u hu => hu.1.2)
  have hs_nn : 0 ≤ s := le_csSup hS_bdd h0_mem
  have hs_in_Icc : s ∈ Set.Icc (0 : ℝ) t := ⟨hs_nn, hs_le_t⟩
  have hys_le : y s ≤ 1 := by
    rcases eq_or_lt_of_le hs_nn with hs_zero | hs_pos
    · rw [← hs_zero, hy0]; norm_num
    · by_contra h_ys_gt
      push_neg at h_ys_gt
      have hy_cont_s : ContinuousWithinAt y (Set.Icc 0 t) s := hy_cont s hs_in_Icc
      rw [Metric.continuousWithinAt_iff] at hy_cont_s
      obtain ⟨δ, hδ, hδ_prop⟩ := hy_cont_s ((y s - 1) / 2) (by linarith)
      obtain ⟨u, hu_mem, hu_lt⟩ :=
        exists_lt_of_lt_csSup hS_nonempty (show s - δ < s by linarith)
      have hu_le : u ≤ s := le_csSup hS_bdd hu_mem
      have hu_dist : |u - s| < δ := by
        rw [abs_sub_lt_iff]; exact ⟨by linarith, by linarith⟩
      have := hδ_prop hu_mem.1 (by rw [Real.dist_eq]; exact hu_dist)
      rw [Real.dist_eq] at this
      have := abs_sub_lt_iff.mp this
      linarith [hu_mem.2]
  have hs_lt_t : s < t := by
    rcases lt_or_eq_of_le hs_le_t with h | h
    · exact h
    · exfalso; rw [← h] at h_gt; linarith
  have hys_eq : y s = 1 := by
    refine le_antisymm hys_le ?_
    by_contra h_ys_lt
    push_neg at h_ys_lt
    have hy_cont_s : ContinuousWithinAt y (Set.Icc 0 t) s := hy_cont s hs_in_Icc
    rw [Metric.continuousWithinAt_iff] at hy_cont_s
    obtain ⟨δ, hδ, hδ_prop⟩ := hy_cont_s ((1 - y s) / 2) (by linarith)
    set u := min (s + δ / 2) t with hu_def
    have hsu : s < u := lt_min (by linarith) hs_lt_t
    have hu_le_t : u ≤ t := min_le_right _ _
    have hu_mem_Icc : u ∈ Set.Icc (0 : ℝ) t :=
      ⟨le_trans hs_nn (le_of_lt hsu), hu_le_t⟩
    have hu_dist : dist u s < δ := by
      have h1 : u ≤ s + δ / 2 := min_le_left _ _
      rw [Real.dist_eq, abs_of_pos (by linarith : (0:ℝ) < u - s)]
      linarith
    have h_apply := hδ_prop hu_mem_Icc hu_dist
    rw [Real.dist_eq] at h_apply
    have := abs_sub_lt_iff.mp h_apply
    have hu_in_S : u ∈ S := ⟨hu_mem_Icc, by linarith⟩
    have : u ≤ s := le_csSup hS_bdd hu_in_S
    linarith
  have hy_gt_on : ∀ u, s < u → u ≤ t → 1 < y u := by
    intro u hsu hut
    by_contra h_u_le
    push_neg at h_u_le
    have hu_in_S : u ∈ S :=
      ⟨⟨le_trans hs_nn (le_of_lt hsu), hut⟩, h_u_le⟩
    have : u ≤ s := le_csSup hS_bdd hu_in_S
    linarith
  have hy_cont_st : ContinuousOn y (Set.Icc s t) :=
    hy_cont.mono (fun u hu => ⟨le_trans hs_nn hu.1, hu.2⟩)
  have h_st_ne : (Set.Icc s t).Nonempty :=
    ⟨s, ⟨le_refl _, hs_lt_t.le⟩⟩
  obtain ⟨u_y, _, hu_y_max⟩ :=
    isCompact_Icc.exists_isMaxOn h_st_ne hy_cont_st.abs
  set R : ℝ := |y u_y| + 2 with hR_def
  have hR_pos : 0 < R := by
    have h1 : 0 ≤ |y u_y| := abs_nonneg _
    linarith
  have hR_nn : 0 ≤ R := hR_pos.le
  have hy_bdd : ∀ u ∈ Set.Icc s t, |y u| ≤ R := by
    intro u hu
    have h1 : |y u| ≤ |y u_y| := hu_y_max hu
    linarith
  let v : ℝ → ℝ → ℝ := fun _ z => 1 - z ^ 5
  set K_val : ℝ := 5 * R ^ 4 with hK_val_def
  have hK_nn : 0 ≤ K_val := by positivity
  let K : NNReal := Real.toNNReal K_val
  have hK_coe : (K : ℝ) = K_val := Real.coe_toNNReal K_val hK_nn
  have hv_lip : ∀ u ∈ Set.Ico s t, LipschitzOnWith K (v u) (Set.Icc (-R) R) := by
    intro u _
    rw [lipschitzOnWith_iff_dist_le_mul]
    intro z hz z' hz'
    rw [Real.dist_eq, Real.dist_eq, hK_coe]
    have hz_abs : |z| ≤ R := abs_le.mpr hz
    have hz'_abs : |z'| ≤ R := abs_le.mpr hz'
    have h_exp : v u z - v u z' = -(z ^ 5 - z' ^ 5) := by simp only [v]; ring
    rw [h_exp, abs_neg]
    have := fifth_power_lipschitz_on_ball R hR_nn z z' hz_abs hz'_abs
    linarith [this]
  let c : ℝ → ℝ := fun _ => (1 : ℝ)
  have hc_cont : ContinuousOn c (Set.Icc s t) := continuousOn_const
  have hc_deriv : ∀ u ∈ Set.Ico s t,
      HasDerivWithinAt c (v u (c u)) (Set.Ici u) u := by
    intro u _
    have h_v : v u (c u) = 0 := by simp [v, c]
    rw [h_v]
    exact (hasDerivAt_const u (1 : ℝ)).hasDerivWithinAt
  have hy_within : ∀ u ∈ Set.Ico s t,
      HasDerivWithinAt y (v u (y u)) (Set.Ici u) u := by
    intro u ⟨hu1, hu2⟩
    have hu_nn : 0 ≤ u := le_trans hs_nn hu1
    exact (hy_deriv u hu_nn (le_of_lt hu2)).hasDerivWithinAt
  have hy_in_s : ∀ u ∈ Set.Ico s t, y u ∈ Set.Icc (-R) R := fun u hu =>
    abs_le.mp (hy_bdd u ⟨hu.1, le_of_lt hu.2⟩)
  have hc_in_s : ∀ u ∈ Set.Ico s t, c u ∈ Set.Icc (-R) R := by
    intro u _
    show (1 : ℝ) ∈ Set.Icc (-R) R
    refine ⟨?_, ?_⟩ <;> · have h1 := abs_nonneg (y u_y); linarith
  have h_eq_at : y s = c s := hys_eq
  have hst_eqOn : Set.EqOn y c (Set.Icc s t) :=
    ODE_solution_unique_of_mem_Icc_right hv_lip hy_cont_st hy_within hy_in_s
      hc_cont hc_deriv hc_in_s h_eq_at
  have : y t = 1 := hst_eqOn ⟨hs_lt_t.le, le_refl _⟩
  linarith

/-- Global wrappers. -/
private lemma scalar_quintic_lower_barrier
    {y : ℝ → ℝ}
    (hy0 : y 0 = 0)
    (hy_deriv : ∀ t, 0 ≤ t → HasDerivAt y (1 - (y t) ^ 5) t) :
    ∀ t, 0 ≤ t → 0 ≤ y t :=
  fun t ht_nn =>
    scalar_quintic_lower_barrier_local ht_nn hy0
      (fun u hu_nn _ => hy_deriv u hu_nn)

private lemma scalar_quintic_upper_barrier
    {y : ℝ → ℝ}
    (hy0 : y 0 = 0)
    (hy_deriv : ∀ t, 0 ≤ t → HasDerivAt y (1 - (y t) ^ 5) t) :
    ∀ t, 0 ≤ t → y t ≤ 1 :=
  fun t ht_nn =>
    scalar_quintic_upper_barrier_local ht_nn hy0
      (fun u hu_nn _ => hy_deriv u hu_nn)

/-- **Sub-lemma 3: original GPAC is bounded in [0, 1].** -/
theorem scalar_quintic_original_bounded :
    ∃ ySol : ℝ → ℝ, ySol 0 = 0 ∧
      (∀ t ≥ (0 : ℝ), HasDerivAt ySol (1 - (ySol t) ^ 5) t) ∧
      (∀ t ≥ (0 : ℝ), 0 ≤ ySol t ∧ ySol t ≤ 1) := by
  classical
  let F : (Fin 1 → ℝ) → Fin 1 → ℝ := fun z _ => 1 - (z 0) ^ 5
  let y₀ : Fin 1 → ℝ := fun _ => 0
  have h_lip : ∀ R : ℝ, 0 < R → ∃ L : ℝ, ∀ x y : Fin 1 → ℝ,
      ‖x‖ ≤ R → ‖y‖ ≤ R → ‖F x - F y‖ ≤ L * ‖x - y‖ := by
    intro R hR
    refine ⟨5 * R ^ 4, ?_⟩
    intro x y hx hy
    have hx0 : |x 0| ≤ R := by
      have := norm_le_pi_norm x 0
      rw [Real.norm_eq_abs] at this
      linarith [this.trans hx]
    have hy0 : |y 0| ≤ R := by
      have := norm_le_pi_norm y 0
      rw [Real.norm_eq_abs] at this
      linarith [this.trans hy]
    have h_coord : ‖F x - F y‖ ≤ 5 * R ^ 4 * |x 0 - y 0| := by
      rw [show F x - F y = fun _ => -(x 0 ^ 5 - y 0 ^ 5) by
            funext i; simp only [F, Pi.sub_apply]; ring]
      rw [pi_norm_le_iff_of_nonneg (by positivity)]
      intro i
      rw [Real.norm_eq_abs, abs_neg]
      exact fifth_power_lipschitz_on_ball R hR.le (x 0) (y 0) hx0 hy0
    have h_diff_coord : |x 0 - y 0| ≤ ‖x - y‖ := by
      have := norm_le_pi_norm (x - y) 0
      rw [Real.norm_eq_abs] at this
      simpa [Pi.sub_apply] using this
    calc ‖F x - F y‖
        ≤ 5 * R ^ 4 * |x 0 - y 0| := h_coord
      _ ≤ 5 * R ^ 4 * ‖x - y‖ :=
          mul_le_mul_of_nonneg_left h_diff_coord (by positivity)
  have h_invariant : ∀ (T : ℝ), 0 < T → ∀ (w : ℝ → Fin 1 → ℝ),
      w 0 = y₀ →
      (∀ t ∈ Set.Ico (0 : ℝ) T, HasDerivAt w (F (w t)) t) →
      ∀ t ∈ Set.Ico (0 : ℝ) T, ‖w t‖ ≤ 1 := by
    intro T _hT w hw0 hw_deriv t htm
    set z : ℝ → ℝ := fun τ => w τ 0 with hz_def
    have hz_deriv : ∀ τ ∈ Set.Ico (0 : ℝ) T,
        HasDerivAt z (1 - (z τ) ^ 5) τ := by
      intro τ hτ
      have h := hw_deriv τ hτ
      have hpi := (hasDerivAt_pi (φ := w) (φ' := F (w τ))).1 h
      have := hpi 0
      show HasDerivAt z (F (w τ) 0) τ
      exact this
    have hz0 : z 0 = 0 := by
      show w 0 0 = 0
      rw [hw0]
    have hz_deriv_local : ∀ τ, 0 ≤ τ → τ < T →
        ∀ u, 0 ≤ u → u ≤ τ → HasDerivAt z (1 - (z u) ^ 5) u := by
      intro τ hτ_nn hτ_lt u hu_nn hu_le
      exact hz_deriv u ⟨hu_nn, lt_of_le_of_lt hu_le hτ_lt⟩
    have hz_lb_Ico : ∀ τ, 0 ≤ τ → τ < T → 0 ≤ z τ := by
      intro τ hτ_nn hτ_lt
      exact scalar_quintic_lower_barrier_local hτ_nn hz0
        (hz_deriv_local τ hτ_nn hτ_lt)
    have hz_ub_Ico : ∀ τ, 0 ≤ τ → τ < T → z τ ≤ 1 := by
      intro τ hτ_nn hτ_lt
      exact scalar_quintic_upper_barrier_local hτ_nn hz0
        (hz_deriv_local τ hτ_nn hτ_lt)
    have hlb : 0 ≤ z t := hz_lb_Ico t htm.1 htm.2
    have hub : z t ≤ 1 := hz_ub_Ico t htm.1 htm.2
    rw [pi_norm_le_iff_of_nonneg zero_le_one]
    intro i
    have hi0 : i = 0 := Subsingleton.elim i 0
    subst hi0
    rw [Real.norm_eq_abs]
    show |z t| ≤ 1
    rw [abs_le]
    exact ⟨by linarith, hub⟩
  obtain ⟨w, hw0, hw_deriv, _hw_cont⟩ :=
    locally_lipschitz_bounded_global_ode_proved_continuous F y₀ h_lip 1
      (by norm_num) h_invariant
  refine ⟨fun τ => w τ 0, ?_, ?_, ?_⟩
  · show w 0 0 = 0
    rw [hw0]
  · intro t ht
    have h := hw_deriv t ht
    have hpi := (hasDerivAt_pi (φ := w) (φ' := F (w t))).1 h
    have := hpi 0
    show HasDerivAt (fun τ => w τ 0) (F (w t) 0) t
    exact this
  · intro t ht
    set z : ℝ → ℝ := fun τ => w τ 0 with hz_def
    have hz_deriv_all : ∀ τ, 0 ≤ τ → HasDerivAt z (1 - (z τ) ^ 5) τ := by
      intro τ hτ
      have h := hw_deriv τ hτ
      have hpi := (hasDerivAt_pi (φ := w) (φ' := F (w τ))).1 h
      have := hpi 0
      show HasDerivAt z (F (w τ) 0) τ
      exact this
    have hz0 : z 0 = 0 := by show w 0 0 = 0; rw [hw0]
    have hlb := scalar_quintic_lower_barrier hz0 hz_deriv_all t ht
    have hub := scalar_quintic_upper_barrier hz0 hz_deriv_all t ht
    exact ⟨hlb, hub⟩

/-- **Sub-lemma 4: σ-drift identity.** -/
theorem scalar_quintic_sigma_drift (k : ℚ) (sol : ℝ → Fin 2 → ℝ)
    (h_deriv : ∀ t ≥ (0 : ℝ),
      HasDerivAt (fun s => sol s) ((dualRailedQuintic k).evalField (sol t)) t) :
    ∀ t ≥ (0 : ℝ),
      HasDerivAt (fun s => sol s 0 + sol s 1)
        (1 + (sol t 0 + sol t 1) ^ 5
          - (k : ℝ) / 2 * ((sol t 0 + sol t 1) ^ 2 - (sol t 0 - sol t 1) ^ 2)) t := by
  intro t ht
  have h := h_deriv t ht
  have hpi := (hasDerivAt_pi (φ := fun s => sol s)
    (φ' := (dualRailedQuintic k).evalField (sol t))).1 h
  have hu := hpi 0
  have hv := hpi 1
  have hadd := hu.add hv
  rw [dualRailedQuintic_drift_sum k (sol t)] at hadd
  have halg :
      1 + (sol t 0 + sol t 1) ^ 5 - 2 * (k : ℝ) * (sol t 0) * (sol t 1)
        = 1 + (sol t 0 + sol t 1) ^ 5
          - (k : ℝ) / 2 * ((sol t 0 + sol t 1) ^ 2 - (sol t 0 - sol t 1) ^ 2) := by
    ring
  rw [halg] at hadd
  exact hadd

/-- **Sub-lemma 5 (local form): σ forward-invariance on `[0, T]`.** -/
theorem scalar_quintic_sigma_bound_local (k : ℚ) (hk : scalarQuinticThreshold < (k : ℝ))
    (σ y : ℝ → ℝ) (hσ0 : σ 0 = 0) {T : ℝ} (_hT_nn : 0 ≤ T)
    (hy_bound : ∀ u, 0 ≤ u → u ≤ T → |y u| ≤ 1)
    (h_deriv : ∀ u, 0 ≤ u → u ≤ T →
      HasDerivAt σ (1 + (σ u) ^ 5 - (k : ℝ) / 2 * ((σ u) ^ 2 - (y u) ^ 2)) u) :
    ∀ t, 0 ≤ t → t ≤ T → 0 ≤ σ t ∧ σ t ≤ (k : ℝ) := by
  -- Threshold facts: k > 22 > 0, and 2 < k/2·something. Key: 33 < 3k/2 when k > 22.
  have hk22 : (22 : ℝ) < (k : ℝ) := by
    have := hk
    unfold scalarQuinticThreshold at this
    exact this
  have hk_pos : (0 : ℝ) < (k : ℝ) := by linarith
  -- σ is continuous on [0, T].
  have hσ_cont : ∀ u, 0 ≤ u → u ≤ T → ContinuousAt σ u := fun u h1 h2 =>
    (h_deriv u h1 h2).continuousAt
  -- **Lower barrier: 0 ≤ σ t.**
  -- Drift at σ = 0, any y: 1 + 0 - (k/2)(0 - y²) = 1 + (k/2) y² ≥ 1 > 0.
  have h_lower : ∀ t, 0 ≤ t → t ≤ T → 0 ≤ σ t := by
    intro t ht_nn ht_le
    by_contra h_neg
    push_neg at h_neg
    have hσ_cont_Icc : ContinuousOn σ (Set.Icc 0 t) := fun u hu =>
      (hσ_cont u hu.1 (le_trans hu.2 ht_le)).continuousWithinAt
    let S : Set ℝ := {u | u ∈ Set.Icc (0 : ℝ) t ∧ 0 ≤ σ u}
    have h0_mem : (0 : ℝ) ∈ S := ⟨⟨le_refl _, ht_nn⟩, by rw [hσ0]⟩
    have hS_bdd : BddAbove S := ⟨t, fun u hu => hu.1.2⟩
    have hS_nonempty : S.Nonempty := ⟨0, h0_mem⟩
    set s := sSup S with hs_def
    have hs_le_t : s ≤ t := csSup_le hS_nonempty (fun u hu => hu.1.2)
    have hs_nn : 0 ≤ s := le_csSup hS_bdd h0_mem
    have hs_in_Icc : s ∈ Set.Icc (0 : ℝ) t := ⟨hs_nn, hs_le_t⟩
    have hσs_nn : 0 ≤ σ s := by
      rcases eq_or_lt_of_le hs_nn with hs_zero | hs_pos
      · rw [← hs_zero, hσ0]
      · have hσ_cont_s : ContinuousWithinAt σ (Set.Icc 0 t) s :=
          hσ_cont_Icc s hs_in_Icc
        have h_seq : ∀ ε > 0, ∃ u ∈ S, s - ε < u ∧ u ≤ s := by
          intro ε hε
          obtain ⟨u, hu_mem, hu_lt⟩ :=
            exists_lt_of_lt_csSup hS_nonempty (show s - ε < s by linarith)
          exact ⟨u, hu_mem, hu_lt, le_csSup hS_bdd hu_mem⟩
        have h_approach :
            ∀ ε > 0, ∃ u ∈ Set.Icc (0:ℝ) t, |u - s| < ε ∧ 0 ≤ σ u := by
          intro ε hε
          obtain ⟨u, ⟨hu1, hu2⟩, hu_lt, hu_le⟩ := h_seq ε hε
          refine ⟨u, hu1, ?_, hu2⟩
          rw [abs_sub_lt_iff]; exact ⟨by linarith, by linarith⟩
        by_contra h_σs_neg
        push_neg at h_σs_neg
        rw [Metric.continuousWithinAt_iff] at hσ_cont_s
        obtain ⟨δ, hδ, hδ_prop⟩ := hσ_cont_s (-σ s / 2) (by linarith)
        obtain ⟨u, hu_in, hu_dist, hσu_nn⟩ := h_approach δ hδ
        have := hδ_prop hu_in (by rw [Real.dist_eq]; exact hu_dist)
        rw [Real.dist_eq] at this
        have := abs_sub_lt_iff.mp this
        linarith
    have hs_lt_t : s < t := by
      rcases lt_or_eq_of_le hs_le_t with h | h
      · exact h
      · exfalso; rw [← h] at h_neg; linarith
    have hσ_neg_on : ∀ u, s < u → u ≤ t → σ u < 0 := by
      intro u hsu hut
      by_contra hu_nn
      push_neg at hu_nn
      have hu_in_S : u ∈ S :=
        ⟨⟨le_trans hs_nn (le_of_lt hsu), hut⟩, hu_nn⟩
      have : u ≤ s := le_csSup hS_bdd hu_in_S
      linarith
    have hσs_zero : σ s = 0 := by
      refine le_antisymm ?_ hσs_nn
      by_contra h_pos
      push_neg at h_pos
      have hσ_cont_s : ContinuousWithinAt σ (Set.Icc 0 t) s :=
        hσ_cont_Icc s hs_in_Icc
      rw [Metric.continuousWithinAt_iff] at hσ_cont_s
      obtain ⟨δ, hδ, hδ_prop⟩ := hσ_cont_s (σ s) h_pos
      set u := min (s + δ / 2) t with hu_def
      have hu_lt_t : u ≤ t := min_le_right _ _
      have hsu : s < u := lt_min (by linarith) hs_lt_t
      have hu_mem : u ∈ Set.Icc (0 : ℝ) t :=
        ⟨le_trans hs_nn (le_of_lt hsu), hu_lt_t⟩
      have h_dist : dist u s < δ := by
        have h1 : u ≤ s + δ / 2 := min_le_left _ _
        rw [Real.dist_eq, abs_of_pos (by linarith : (0:ℝ) < u - s)]
        linarith
      have h_apply := hδ_prop hu_mem h_dist
      have : |σ u - σ s| < σ s := by rwa [Real.dist_eq] at h_apply
      have hσu_neg : σ u < 0 := hσ_neg_on u hsu hu_lt_t
      have := abs_sub_lt_iff.mp this
      linarith
    have hs_le_T : s ≤ T := le_trans hs_le_t ht_le
    have h_deriv_s :
        HasDerivAt σ (1 + (σ s) ^ 5 - (k : ℝ) / 2 * ((σ s) ^ 2 - (y s) ^ 2)) s :=
      h_deriv s hs_nn hs_le_T
    have h_drift_val :
        (1 + (σ s) ^ 5 - (k : ℝ) / 2 * ((σ s) ^ 2 - (y s) ^ 2))
          = 1 + (k : ℝ) / 2 * (y s) ^ 2 := by
      rw [hσs_zero]; ring
    rw [h_drift_val] at h_deriv_s
    set d : ℝ := 1 + (k : ℝ) / 2 * (y s) ^ 2 with hd_def
    have hd_pos : 0 < d := by
      have hy_sq_nn : 0 ≤ (y s) ^ 2 := sq_nonneg _
      have : 0 ≤ (k : ℝ) / 2 * (y s) ^ 2 :=
        mul_nonneg (by linarith) hy_sq_nn
      linarith
    have h_lo : (fun h => σ (s + h) - σ s - h • d) =o[nhds 0] fun h => h :=
      (hasDerivAt_iff_isLittleO_nhds_zero.mp h_deriv_s)
    have h_bnd_ev : ∀ᶠ h in nhds (0 : ℝ), ‖σ (s + h) - σ s - h • d‖ ≤ (d / 2) * ‖h‖ :=
      h_lo.def (by linarith : 0 < d / 2)
    rw [Metric.eventually_nhds_iff] at h_bnd_ev
    obtain ⟨δ, hδ, hδ_prop⟩ := h_bnd_ev
    set h := min (δ / 2) ((t - s) / 2) with hh_def
    have hh_pos : 0 < h := lt_min (by linarith) (by linarith)
    have hh_lt_ts : h ≤ (t - s) / 2 := min_le_right _ _
    have hh_lt_δ : h < δ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
    have hh_dist : dist h 0 < δ := by
      rw [Real.dist_0_eq_abs, abs_of_pos hh_pos]
      exact hh_lt_δ
    have h_ineq := hδ_prop hh_dist
    have hσ_h_pos : 0 < σ (s + h) := by
      rw [hσs_zero] at h_ineq
      have h_simp : σ (s + h) - 0 - h • d = σ (s + h) - h * d := by
        simp [smul_eq_mul]
      rw [h_simp] at h_ineq
      have h_abs_h : ‖h‖ = h := by rw [Real.norm_eq_abs, abs_of_pos hh_pos]
      rw [h_abs_h] at h_ineq
      have h_norm_eq : ‖σ (s + h) - h * d‖ = |σ (s + h) - h * d| := Real.norm_eq_abs _
      rw [h_norm_eq] at h_ineq
      have h_abs_lb : -(d / 2 * h) ≤ σ (s + h) - h * d :=
        neg_le_of_abs_le h_ineq
      have h_half_d_h : 0 < (d / 2) * h :=
        mul_pos (by linarith : (0:ℝ) < d / 2) hh_pos
      nlinarith
    have hs_h_lt_t : s + h ≤ t := by linarith
    have hs_lt_sh : s < s + h := by linarith
    have : σ (s + h) < 0 := hσ_neg_on (s + h) hs_lt_sh hs_h_lt_t
    linarith
  -- **Upper barrier: σ t ≤ 2.** At σ = 2, |y| ≤ 1, drift ≤ 33 - 3k/2 < 0 for k > 22.
  have h_upper_two : ∀ t, 0 ≤ t → t ≤ T → σ t ≤ 2 := by
    intro t ht_nn ht_le
    by_contra h_gt
    push_neg at h_gt
    have hσ_cont_Icc : ContinuousOn σ (Set.Icc 0 t) := fun u hu =>
      (hσ_cont u hu.1 (le_trans hu.2 ht_le)).continuousWithinAt
    let S : Set ℝ := {u | u ∈ Set.Icc (0 : ℝ) t ∧ σ u ≤ 2}
    have h0_mem : (0 : ℝ) ∈ S :=
      ⟨⟨le_refl _, ht_nn⟩, by rw [hσ0]; linarith⟩
    have hS_bdd : BddAbove S := ⟨t, fun u hu => hu.1.2⟩
    have hS_nonempty : S.Nonempty := ⟨0, h0_mem⟩
    set s := sSup S with hs_def
    have hs_le_t : s ≤ t := csSup_le hS_nonempty (fun u hu => hu.1.2)
    have hs_nn : 0 ≤ s := le_csSup hS_bdd h0_mem
    have hs_in_Icc : s ∈ Set.Icc (0 : ℝ) t := ⟨hs_nn, hs_le_t⟩
    have hσs_le : σ s ≤ 2 := by
      rcases eq_or_lt_of_le hs_nn with hs_zero | hs_pos
      · rw [← hs_zero, hσ0]; linarith
      · by_contra h_σs_gt
        push_neg at h_σs_gt
        have hσ_cont_s : ContinuousWithinAt σ (Set.Icc 0 t) s :=
          hσ_cont_Icc s hs_in_Icc
        rw [Metric.continuousWithinAt_iff] at hσ_cont_s
        obtain ⟨δ, hδ, hδ_prop⟩ := hσ_cont_s ((σ s - 2) / 2) (by linarith)
        obtain ⟨u, hu_mem, hu_lt⟩ :=
          exists_lt_of_lt_csSup hS_nonempty (show s - δ < s by linarith)
        have hu_le : u ≤ s := le_csSup hS_bdd hu_mem
        have hu_dist : |u - s| < δ := by
          rw [abs_sub_lt_iff]; exact ⟨by linarith, by linarith⟩
        have := hδ_prop hu_mem.1 (by rw [Real.dist_eq]; exact hu_dist)
        rw [Real.dist_eq] at this
        have := abs_sub_lt_iff.mp this
        linarith [hu_mem.2]
    have hs_lt_t : s < t := by
      rcases lt_or_eq_of_le hs_le_t with h | h
      · exact h
      · exfalso; rw [← h] at h_gt; linarith
    have hσs_eq : σ s = 2 := by
      refine le_antisymm hσs_le ?_
      by_contra h_σs_lt
      push_neg at h_σs_lt
      have hσ_cont_s : ContinuousWithinAt σ (Set.Icc 0 t) s :=
        hσ_cont_Icc s hs_in_Icc
      rw [Metric.continuousWithinAt_iff] at hσ_cont_s
      obtain ⟨δ, hδ, hδ_prop⟩ := hσ_cont_s ((2 - σ s) / 2) (by linarith)
      set u := min (s + δ / 2) t with hu_def
      have hsu : s < u := lt_min (by linarith) hs_lt_t
      have hu_le_t : u ≤ t := min_le_right _ _
      have hu_mem_Icc : u ∈ Set.Icc (0 : ℝ) t :=
        ⟨le_trans hs_nn (le_of_lt hsu), hu_le_t⟩
      have hu_dist : dist u s < δ := by
        have h1 : u ≤ s + δ / 2 := min_le_left _ _
        rw [Real.dist_eq, abs_of_pos (by linarith : (0:ℝ) < u - s)]
        linarith
      have h_apply := hδ_prop hu_mem_Icc hu_dist
      rw [Real.dist_eq] at h_apply
      have := abs_sub_lt_iff.mp h_apply
      have hu_in_S : u ∈ S := ⟨hu_mem_Icc, by linarith⟩
      have : u ≤ s := le_csSup hS_bdd hu_in_S
      linarith
    have hσ_gt_on : ∀ u, s < u → u ≤ t → 2 < σ u := by
      intro u hsu hut
      by_contra h_u_le
      push_neg at h_u_le
      have hu_in_S : u ∈ S :=
        ⟨⟨le_trans hs_nn (le_of_lt hsu), hut⟩, h_u_le⟩
      have : u ≤ s := le_csSup hS_bdd hu_in_S
      linarith
    have hs_le_T : s ≤ T := le_trans hs_le_t ht_le
    have h_deriv_s :
        HasDerivAt σ (1 + (σ s) ^ 5 - (k : ℝ) / 2 * ((σ s) ^ 2 - (y s) ^ 2)) s :=
      h_deriv s hs_nn hs_le_T
    have hy_s_bd : |y s| ≤ 1 := hy_bound s hs_nn hs_le_T
    have hy_s_sq_le : (y s) ^ 2 ≤ 1 := by
      have h_sq : (y s) ^ 2 = |y s| ^ 2 := (sq_abs _).symm
      rw [h_sq]
      have h_abs_nn : 0 ≤ |y s| := abs_nonneg _
      nlinarith
    -- At σ = 2: 1 + 32 - (k/2)(4 - y²) = 33 - (k/2)(4 - y²).
    have h_drift_val :
        1 + (σ s) ^ 5 - (k : ℝ) / 2 * ((σ s) ^ 2 - (y s) ^ 2)
          = 33 - (k : ℝ) / 2 * (4 - (y s) ^ 2) := by
      rw [hσs_eq]; ring
    rw [h_drift_val] at h_deriv_s
    set d : ℝ := 33 - (k : ℝ) / 2 * (4 - (y s) ^ 2) with hd_def
    -- d < 0: d ≤ 33 - 3k/2. For k > 22, 3k/2 > 33, so 33 - 3k/2 < 0.
    have hd_neg : d < 0 := by
      have hy_s_sq_nn : 0 ≤ (y s) ^ 2 := sq_nonneg _
      have h_bound : (k : ℝ) / 2 * (4 - (y s) ^ 2) ≥ (k : ℝ) / 2 * 3 := by
        have h1 : 4 - (y s) ^ 2 ≥ 3 := by linarith
        have hk2_nn : 0 ≤ (k : ℝ) / 2 := by linarith
        nlinarith
      have : d ≤ 33 - (k : ℝ) / 2 * 3 := by linarith
      have : 33 - (k : ℝ) / 2 * 3 < 0 := by linarith
      linarith
    -- Apply derivative definition to extract σ(s+h) < σ s = 2.
    have h_lo : (fun h => σ (s + h) - σ s - h • d) =o[nhds 0] fun h => h :=
      (hasDerivAt_iff_isLittleO_nhds_zero.mp h_deriv_s)
    have h_bnd_ev : ∀ᶠ h in nhds (0 : ℝ), ‖σ (s + h) - σ s - h • d‖ ≤ (-d / 2) * ‖h‖ :=
      h_lo.def (by linarith : 0 < -d / 2)
    rw [Metric.eventually_nhds_iff] at h_bnd_ev
    obtain ⟨δ, hδ, hδ_prop⟩ := h_bnd_ev
    set hh := min (δ / 2) ((t - s) / 2) with hh_def
    have hh_pos : 0 < hh := lt_min (by linarith) (by linarith)
    have hh_lt_ts : hh ≤ (t - s) / 2 := min_le_right _ _
    have hh_lt_δ : hh < δ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
    have hh_dist : dist hh 0 < δ := by
      rw [Real.dist_0_eq_abs, abs_of_pos hh_pos]; exact hh_lt_δ
    have h_ineq := hδ_prop hh_dist
    have hσ_sh_lt : σ (s + hh) < σ s := by
      have h_norm_eq : ‖σ (s + hh) - σ s - hh • d‖ = |σ (s + hh) - σ s - hh * d| := by
        rw [Real.norm_eq_abs]; simp [smul_eq_mul]
      rw [h_norm_eq] at h_ineq
      have h_abs_h : ‖hh‖ = hh := by rw [Real.norm_eq_abs, abs_of_pos hh_pos]
      rw [h_abs_h] at h_ineq
      have h_upper : σ (s + hh) - σ s - hh * d ≤ -d / 2 * hh :=
        le_of_abs_le h_ineq
      have h_hh_d_neg : hh * d < 0 := mul_neg_of_pos_of_neg hh_pos hd_neg
      nlinarith
    rw [hσs_eq] at hσ_sh_lt
    have hs_h_lt_t : s + hh ≤ t := by linarith
    have hs_lt_sh : s < s + hh := by linarith
    have : 2 < σ (s + hh) := hσ_gt_on (s + hh) hs_lt_sh hs_h_lt_t
    linarith
  intro t ht ht_le
  refine ⟨h_lower t ht ht_le, ?_⟩
  have h_two := h_upper_two t ht ht_le
  -- σ t ≤ 2 ≤ k since k > 22.
  have : (2 : ℝ) ≤ (k : ℝ) := by linarith
  linarith

/-- Global wrapper for `scalar_quintic_sigma_bound_local`. -/
theorem scalar_quintic_sigma_bound (k : ℚ) (hk : scalarQuinticThreshold < (k : ℝ))
    (σ y : ℝ → ℝ) (hσ0 : σ 0 = 0) (hy_bound : ∀ t ≥ (0 : ℝ), |y t| ≤ 1)
    (h_deriv : ∀ t ≥ (0 : ℝ),
      HasDerivAt σ (1 + (σ t) ^ 5 - (k : ℝ) / 2 * ((σ t) ^ 2 - (y t) ^ 2)) t) :
    ∀ t ≥ (0 : ℝ), 0 ≤ σ t ∧ σ t ≤ (k : ℝ) :=
  fun t ht =>
    scalar_quintic_sigma_bound_local k hk σ y hσ0
      (T := t) ht
      (fun u hu_nn _ => hy_bound u hu_nn)
      (fun u hu_nn _ => h_deriv u hu_nn)
      t ht (le_refl _)

/-- **Sub-lemma 6: Picard existence from invariance.** -/
theorem scalar_quintic_picard (k : ℚ) (hk : scalarQuinticThreshold < (k : ℝ)) :
    ∃ (sol : ℝ → Fin 2 → ℝ),
      sol 0 = (fun _ => 0) ∧
      (∀ t ≥ (0 : ℝ),
        HasDerivAt (fun s => sol s) ((dualRailedQuintic k).evalField (sol t)) t) ∧
      (∀ t ≥ (0 : ℝ), ∀ i, 0 ≤ sol t i ∧ sol t i ≤ (k : ℝ)) := by
  classical
  have hk22 : (22 : ℝ) < (k : ℝ) := by
    have := hk; unfold scalarQuinticThreshold at this; exact this
  have hk_pos : (0 : ℝ) < (k : ℝ) := by linarith
  have hk1 : (1 : ℝ) ≤ (k : ℝ) := by linarith
  set F : (Fin 2 → ℝ) → Fin 2 → ℝ := (dualRailedQuintic k).evalField with hF_def
  have hF_lip := dualRailedQuintic_lipschitz k
  have hF_crn := dualRailedQuintic_crn k
  have h_invariant : ∀ (T : ℝ), 0 < T → ∀ (w : ℝ → Fin 2 → ℝ),
      w 0 = (fun _ : Fin 2 => (0 : ℝ)) →
      (∀ t ∈ Set.Ico (0 : ℝ) T, HasDerivAt w (F (w t)) t) →
      ∀ t ∈ Set.Ico (0 : ℝ) T, ‖w t‖ ≤ (k : ℝ) := by
    intro T hT w hw0 hw_deriv t htm
    have hw_init_nn : ∀ i, 0 ≤ w 0 i := fun i => by rw [hw0]
    have hw_nn : ∀ s ∈ Set.Ico (0 : ℝ) T, ∀ i, 0 ≤ w s i := fun s hs i =>
      crn_local_nonneg hF_crn hF_lip T hT w hw_init_nn hw_deriv s hs i
    set z : ℝ → ℝ := fun s => w s 0 - w s 1 with hz_def
    set σ : ℝ → ℝ := fun s => w s 0 + w s 1 with hσ_def
    have hz0 : z 0 = 0 := by simp [z, hw0]
    have hσ0 : σ 0 = 0 := by simp [σ, hw0]
    have hz_deriv : ∀ s ∈ Set.Ico (0 : ℝ) T,
        HasDerivAt z (1 - (z s) ^ 5) s := by
      intro s hs
      have h := hw_deriv s hs
      have hpi := (hasDerivAt_pi (φ := w) (φ' := F (w s))).1 h
      have hu := hpi 0
      have hv := hpi 1
      have hdiff := hu.sub hv
      have heq := dualRailedQuintic_drift_diff k (w s)
      rw [hF_def] at hdiff
      rw [heq] at hdiff
      exact hdiff
    have hσ_deriv : ∀ s ∈ Set.Ico (0 : ℝ) T,
        HasDerivAt σ (1 + (σ s) ^ 5 - (k : ℝ) / 2 * ((σ s) ^ 2 - (z s) ^ 2)) s := by
      intro s hs
      have h := hw_deriv s hs
      have hpi := (hasDerivAt_pi (φ := w) (φ' := F (w s))).1 h
      have hu := hpi 0
      have hv := hpi 1
      have hadd := hu.add hv
      rw [hF_def] at hadd
      rw [dualRailedQuintic_drift_sum k (w s)] at hadd
      have halg :
          1 + (w s 0 + w s 1) ^ 5 - 2 * (k : ℝ) * (w s 0) * (w s 1)
            = 1 + (w s 0 + w s 1) ^ 5
              - (k : ℝ) / 2 * ((w s 0 + w s 1) ^ 2 - (w s 0 - w s 1) ^ 2) := by ring
      rw [halg] at hadd
      show HasDerivAt σ _ s
      simp only [σ, z]
      exact hadd
    have hz_deriv_local : ∀ τ, 0 ≤ τ → τ < T →
        ∀ u, 0 ≤ u → u ≤ τ → HasDerivAt z (1 - (z u) ^ 5) u := by
      intro τ hτ_nn hτ_lt u hu_nn hu_le
      exact hz_deriv u ⟨hu_nn, lt_of_le_of_lt hu_le hτ_lt⟩
    have hz_lb : ∀ τ ∈ Set.Ico (0 : ℝ) T, 0 ≤ z τ := by
      intro τ hτ
      exact scalar_quintic_lower_barrier_local hτ.1 hz0
        (hz_deriv_local τ hτ.1 hτ.2)
    have hz_ub : ∀ τ ∈ Set.Ico (0 : ℝ) T, z τ ≤ 1 := by
      intro τ hτ
      exact scalar_quintic_upper_barrier_local hτ.1 hz0
        (hz_deriv_local τ hτ.1 hτ.2)
    have hz_abs_le : ∀ τ ∈ Set.Ico (0 : ℝ) T, |z τ| ≤ 1 := by
      intro τ hτ
      rw [abs_le]
      exact ⟨by linarith [hz_lb τ hτ], hz_ub τ hτ⟩
    obtain ⟨T', htT', hT'T⟩ : ∃ T', t < T' ∧ T' < T := by
      refine ⟨(t + T) / 2, ?_, ?_⟩ <;> linarith [htm.2]
    have hT'_nn : 0 ≤ T' := by linarith [htm.1]
    have hσ_sigma_bound :=
      scalar_quintic_sigma_bound_local k hk σ z hσ0 (T := T') hT'_nn
        (fun u hu_nn hu_le => hz_abs_le u ⟨hu_nn, lt_of_le_of_lt hu_le hT'T⟩)
        (fun u hu_nn hu_le => hσ_deriv u ⟨hu_nn, lt_of_le_of_lt hu_le hT'T⟩)
    have ht_le_T' : t ≤ T' := le_of_lt htT'
    have hσ_nn : 0 ≤ σ t := (hσ_sigma_bound t htm.1 ht_le_T').1
    have hσ_le_k : σ t ≤ (k : ℝ) := (hσ_sigma_bound t htm.1 ht_le_T').2
    have hσt : σ t = w t 0 + w t 1 := rfl
    have hzt : z t = w t 0 - w t 1 := rfl
    have hz_t_ub : z t ≤ 1 := hz_ub t htm
    have hz_t_lb : -1 ≤ z t := by linarith [hz_lb t htm]
    have hw_t_nn : ∀ i, 0 ≤ w t i := hw_nn t htm
    have hw0_bound : w t 0 ≤ (k : ℝ) := by
      have h1 : w t 0 = (σ t + z t) / 2 := by rw [hσt, hzt]; ring
      linarith
    have hw1_bound : w t 1 ≤ (k : ℝ) := by
      have h1 : w t 1 = (σ t - z t) / 2 := by rw [hσt, hzt]; ring
      linarith
    have hwt_bound : ∀ i, w t i ≤ (k : ℝ) := fun i => by
      fin_cases i
      · exact hw0_bound
      · exact hw1_bound
    rw [pi_norm_le_iff_of_nonneg hk_pos.le]
    intro i
    rw [Real.norm_eq_abs, abs_of_nonneg (hw_t_nn i)]
    exact hwt_bound i
  obtain ⟨sol, h_init, h_deriv, _h_cont⟩ :=
    locally_lipschitz_bounded_global_ode_proved_continuous F (fun _ => 0)
      hF_lip (k : ℝ) hk_pos h_invariant
  refine ⟨sol, h_init, h_deriv, ?_⟩
  intro t ht i
  have h_nn : 0 ≤ sol t i :=
    scalar_quintic_nonneg k sol h_init h_deriv t ht i
  refine ⟨h_nn, ?_⟩
  have hT : (0 : ℝ) < t + 1 := by linarith
  have h_sub : ∀ s ∈ Set.Ico (0 : ℝ) (t + 1), HasDerivAt sol (F (sol s)) s := by
    intro s hs; exact h_deriv s hs.1
  have h_inv := h_invariant (t + 1) hT sol h_init h_sub t ⟨ht, by linarith⟩
  have h_abs : |sol t i| ≤ (k : ℝ) := by
    have := norm_le_pi_norm (sol t) i
    rw [Real.norm_eq_abs] at this
    linarith
  have : sol t i ≤ (k : ℝ) := le_of_abs_le h_abs
  exact this

/-- **Main theorem (UCNC25 Problem 1, scalar quintic case).** -/
theorem scalar_quintic_bounded :
    ∀ (k : ℚ), scalarQuinticThreshold < (k : ℝ) →
      ∃ (sol : ℝ → Fin 2 → ℝ) (B : ℝ), 0 < B ∧
        (∀ t ≥ (0 : ℝ), ∀ i, 0 ≤ sol t i ∧ sol t i ≤ B) ∧
        (∀ t ≥ (0 : ℝ),
          HasDerivAt (fun s => sol s) ((dualRailedQuintic k).evalField (sol t)) t) ∧
        sol 0 = fun _ => 0 := by
  intro k hk
  obtain ⟨sol, h_init, h_deriv, h_bound⟩ := scalar_quintic_picard k hk
  refine ⟨sol, (k : ℝ), ?_, h_bound, h_deriv, h_init⟩
  exact lt_trans scalarQuinticThreshold_pos hk

/-- **Corollary.** At `k = 25`, above `scalarQuinticThreshold = 22`. -/
theorem scalar_quintic_bounded_at_twentyfive :
    ∃ (sol : ℝ → Fin 2 → ℝ) (B : ℝ), 0 < B ∧
      (∀ t ≥ (0 : ℝ), ∀ i, 0 ≤ sol t i ∧ sol t i ≤ B) ∧
      (∀ t ≥ (0 : ℝ),
        HasDerivAt (fun s => sol s)
          ((dualRailedQuintic (25 : ℚ)).evalField (sol t)) t) ∧
      sol 0 = fun _ => 0 := by
  have hk : scalarQuinticThreshold < ((25 : ℚ) : ℝ) := by
    unfold scalarQuinticThreshold
    have h25 : ((25 : ℚ) : ℝ) = 25 := by norm_num
    rw [h25]; norm_num
  exact scalar_quintic_bounded 25 hk

end ScalarQuintic
end DualRail
end Ripple
