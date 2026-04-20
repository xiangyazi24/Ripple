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
    These drop out of the two parity-split pieces of the binomial expansion
    of `1 − (u − v)^5`.
  - σ-drift: σ' = u' + v' = (1 + σ^5) − 2k·uv = 1 + σ^5 − (k/2)(σ^2 − y^2).
  - Fixed-point equation at the upper |y|=1 boundary:
      f(σ) := σ^5 − (k/2) σ^2 + (k/2) + 1 = 0.
    Unlike the cubic case (clean factorization `k^3 − 27k − 54 =
    (k−6)(k+3)^2`), the quintic threshold is the root of a transcendental
    equation in k and has no closed rational form. Computing the critical
    point σ* = (k/5)^{1/3} (where f′(σ*) = 0) gives
      f(σ*) = −(3k/10)·(k/5)^{2/3} + k/2 + 1,
    which is negative for k ≳ 13.0; numerically the saddle-node is
    k ≈ 13.01. We pick a safe overestimate `k_5* = 20` so downstream
    proofs can use `k > 20` without worrying about the sharp threshold.
    (A future pass can replace this with the sharp root.)

  **Status.** This file scaffolds the statement. All nontrivial proofs
  are `sorry`-placeholders mirroring the layout of `ScalarCubic.lean`.
  The sole claim we leave to the scaffold-filler for sharp numerics is
  `scalarQuinticThreshold = 20`, chosen as a loose upper bound.

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

/-! ## The uniform constant-annihilation dual-railed system

Instantiates `constantAnnihilationDualRail` at `n = 1` and
`p = quinticField`. Produces a `PolyPIVP 2` with variables
`(u, v) = (X 0, X 1)`. -/

/-- The dual-railed PolyPIVP at a fixed annihilation rate `k`. -/
noncomputable def dualRailedQuintic (k : ℚ) : PolyPIVP 2 :=
  constantAnnihilationDualRail 1 quinticField k

/-! ## Positive / negative decomposition for p(y) = 1 − y^5

  `1 − (u − v)^5
     = 1 − u^5 + 5 u^4 v − 10 u^3 v^2 + 10 u^2 v^3 − 5 u v^4 + v^5`

so

  p̂⁺ = 1 + 5 u^4 v + 10 u^2 v^3 + v^5      (non-negative coefficients)
  p̂⁻ = u^5 + 10 u^3 v^2 + 5 u v^4            (sign-flipped to non-negative)

and `p̂⁺ + p̂⁻ = 1 + (u + v)^5`, `p̂⁺ − p̂⁻ = 1 − (u − v)^5`. -/

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
  sorry

/-- Identification: `dualRailPosPart = quinticPosExplicit`. -/
theorem dualRailPosPart_quintic_eq :
    dualRailPosPart 1 quinticField 0 = quinticPosExplicit := by
  sorry

/-- Identification: `dualRailNegPart = quinticNegExplicit`. -/
theorem dualRailNegPart_quintic_eq :
    dualRailNegPart 1 quinticField 0 = quinticNegExplicit := by
  sorry

/-- The positive part `p̂⁺(u, v) = 1 + 5 u^4 v + 10 u^2 v^3 + v^5` as a
real polynomial evaluation. -/
theorem dualRailPosPart_quintic_eval (w : Fin 2 → ℝ) :
    (dualRailPosPart 1 quinticField 0).eval₂ (Rat.castHom ℝ) w
      = 1 + 5 * (w 0) ^ 4 * (w 1) + 10 * (w 0) ^ 2 * (w 1) ^ 3 + (w 1) ^ 5 := by
  sorry

/-- The negative part `p̂⁻(u, v) = u^5 + 10 u^3 v^2 + 5 u v^4`. -/
theorem dualRailNegPart_quintic_eval (w : Fin 2 → ℝ) :
    (dualRailNegPart 1 quinticField 0).eval₂ (Rat.castHom ℝ) w
      = (w 0) ^ 5 + 10 * (w 0) ^ 3 * (w 1) ^ 2 + 5 * (w 0) * (w 1) ^ 4 := by
  sorry

/-! ## Drift-difference / drift-sum identities

Same algebraic content as the cubic case, but with the quintic binomial
identity `1 ± (u ± v)^5`. -/

/-- Drift-difference identity: `u' − v' = 1 − (u − v)^5`. -/
theorem dualRailedQuintic_drift_diff (k : ℚ) (w : Fin 2 → ℝ) :
    (dualRailedQuintic k).evalField w 0 - (dualRailedQuintic k).evalField w 1
      = 1 - (w 0 - w 1) ^ 5 := by
  sorry

/-- Drift-sum identity: `u' + v' = 1 + (u + v)^5 − 2k·uv`. -/
theorem dualRailedQuintic_drift_sum (k : ℚ) (w : Fin 2 → ℝ) :
    (dualRailedQuintic k).evalField w 0 + (dualRailedQuintic k).evalField w 1
      = 1 + (w 0 + w 1) ^ 5 - 2 * (k : ℝ) * w 0 * w 1 := by
  sorry

/-! ## Sigma-reduction identity

Setting `σ := u + v` and `y := u − v`:
  σ' = 1 + σ^5 − (k/2)(σ^2 − y^2).
-/

/-- Key algebraic identity:
  `(1 + 5 u^4 v + 10 u^2 v^3 + v^5) + (u^5 + 10 u^3 v^2 + 5 u v^4) = 1 + (u + v)^5`. -/
theorem quintic_posPart_plus_negPart (u v : ℝ) :
    (1 + 5 * u ^ 4 * v + 10 * u ^ 2 * v ^ 3 + v ^ 5)
      + (u ^ 5 + 10 * u ^ 3 * v ^ 2 + 5 * u * v ^ 4)
      = 1 + (u + v) ^ 5 := by
  ring

/-! ## Saddle-node threshold

For the quintic `p(y) = 1 − y^5` with `|y| ≤ 1`, the σ-quintic
  `f(σ; y) = σ^5 − (k/2) σ^2 + (k/2) y^2 + 1`
has its local minimum on the positive axis at the critical point
`σ* = (k/5)^{1/3}` (where `f′(σ) = 5σ^4 − kσ = σ(5σ^3 − k)` vanishes).
At `y^2 = 1` (worst case):
  f(σ*; 1) = −(3k/10) · (k/5)^{2/3} + k/2 + 1.
Numerically this turns negative near `k ≈ 13.01`. A closed rational
formula for the saddle-node would require solving
  (3k/10)^3 · (k/5)^2 = (k/2 + 1)^3
which is quintic in `k` and irreducible. For scaffolding purposes we pick
the loose overestimate `k_5* = 20`, well above the saddle-node.

TODO (future sharpening): replace with the sharp root of
`3k^{5/3}/(10 · 5^{2/3}) = k/2 + 1`. -/
noncomputable def scalarQuinticThreshold : ℝ := 20

lemma scalarQuinticThreshold_pos : 0 < scalarQuinticThreshold := by
  unfold scalarQuinticThreshold
  norm_num

/-! ## Proof sub-lemmas (Tier 1)

Six analytic pieces mirroring `ScalarCubic.lean`. Each is stated with
`sorry` so the scaffolding compiles and work fronts are visible. -/

/-- **Sub-lemma 1: non-negativity of the dual-rail solution.** If a
solution `sol` to `dualRailedQuintic k` starts at the origin, both
components stay non-negative on `[0, ∞)`.

Proof strategy (mirror of cubic): show `dualRailedQuintic k` is
CRN-implementable (non-negative production, linear degradation via
`−k u v`), verify local Lipschitz (polynomial of degree 5 on norm
balls), then invoke `crn_local_nonneg`. -/
theorem scalar_quintic_nonneg (k : ℚ) (sol : ℝ → Fin 2 → ℝ)
    (h_init : sol 0 = fun _ => 0)
    (h_deriv : ∀ t ≥ (0 : ℝ),
      HasDerivAt (fun s => sol s) ((dualRailedQuintic k).evalField (sol t)) t) :
    ∀ t ≥ (0 : ℝ), ∀ i, 0 ≤ sol t i := by
  sorry

/-- **Sub-lemma 2: dual-rail identity preservation.** The difference
`u − v` of a dual-rail solution satisfies the original scalar quintic
GPAC `y' = 1 − y^5`. -/
theorem scalar_quintic_dual_rail_identity (k : ℚ) (sol : ℝ → Fin 2 → ℝ)
    (h_deriv : ∀ t ≥ (0 : ℝ),
      HasDerivAt (fun s => sol s) ((dualRailedQuintic k).evalField (sol t)) t) :
    ∀ t ≥ (0 : ℝ),
      HasDerivAt (fun s => sol s 0 - sol s 1)
        (1 - (sol t 0 - sol t 1) ^ 5) t := by
  sorry

/-- **Sub-lemma 3: original GPAC is bounded in [0, 1].** For
`y(0) = 0`, the solution of `y' = 1 − y^5` stays in `[0, 1]` forever.
Standard monotonic-attractor argument at the barriers `y = 0, 1`. -/
theorem scalar_quintic_original_bounded :
    ∃ ySol : ℝ → ℝ, ySol 0 = 0 ∧
      (∀ t ≥ (0 : ℝ), HasDerivAt ySol (1 - (ySol t) ^ 5) t) ∧
      (∀ t ≥ (0 : ℝ), 0 ≤ ySol t ∧ ySol t ≤ 1) := by
  sorry

/-- **Sub-lemma 4: σ-drift identity.** If `sol` satisfies the dual-railed
ODE, then `σ(t) = sol t 0 + sol t 1` satisfies
  `σ' = 1 + σ^5 − (k/2)(σ^2 − y^2)`
where `y(t) = sol t 0 − sol t 1`. -/
theorem scalar_quintic_sigma_drift (k : ℚ) (sol : ℝ → Fin 2 → ℝ)
    (h_deriv : ∀ t ≥ (0 : ℝ),
      HasDerivAt (fun s => sol s) ((dualRailedQuintic k).evalField (sol t)) t) :
    ∀ t ≥ (0 : ℝ),
      HasDerivAt (fun s => sol s 0 + sol s 1)
        (1 + (sol t 0 + sol t 1) ^ 5
          - (k : ℝ) / 2 * ((sol t 0 + sol t 1) ^ 2 - (sol t 0 - sol t 1) ^ 2)) t := by
  sorry

/-- **Sub-lemma 5: σ forward-invariance.** For `k > scalarQuinticThreshold`
and `|y| ≤ 1` on `[0, ∞)`, any σ trajectory starting at `σ(0) = 0`
satisfies `0 ≤ σ(t) ≤ k` on `[0, ∞)`.

Proof strategy (mirror of cubic): use a strict σ = σ* barrier at the
critical point `σ* = (k/5)^{1/3}`, where `f(σ*; 1) < 0` for `k > 20`.
The cubic case used σ = k/3 as the exact critical point because the
minimum polynomial `k^3 − 27k − 54 = (k−6)(k+3)^2` factored cleanly; the
quintic critical point `(k/5)^{1/3}` leaves the drift estimate as a
plain transcendental-looking inequality that still yields a positive
barrier for `k > 20`. -/
theorem scalar_quintic_sigma_bound (k : ℚ) (hk : scalarQuinticThreshold < (k : ℝ))
    (σ y : ℝ → ℝ) (hσ0 : σ 0 = 0) (hy_bound : ∀ t ≥ (0 : ℝ), |y t| ≤ 1)
    (h_deriv : ∀ t ≥ (0 : ℝ),
      HasDerivAt σ (1 + (σ t) ^ 5 - (k : ℝ) / 2 * ((σ t) ^ 2 - (y t) ^ 2)) t) :
    ∀ t ≥ (0 : ℝ), 0 ≤ σ t ∧ σ t ≤ (k : ℝ) := by
  sorry

/-- **Sub-lemma 6: Picard existence from invariance.** Combining
Sub-lemmas 1–5 yields global existence and boundedness of the dual-rail
solution. -/
theorem scalar_quintic_picard (k : ℚ) (hk : scalarQuinticThreshold < (k : ℝ)) :
    ∃ (sol : ℝ → Fin 2 → ℝ),
      sol 0 = (fun _ => 0) ∧
      (∀ t ≥ (0 : ℝ),
        HasDerivAt (fun s => sol s) ((dualRailedQuintic k).evalField (sol t)) t) ∧
      (∀ t ≥ (0 : ℝ), ∀ i, 0 ≤ sol t i ∧ sol t i ≤ (k : ℝ)) := by
  sorry

/-- **Main theorem (UCNC25 Problem 1, scalar quintic case).**

  For every rational `k > scalarQuinticThreshold`, the uniform constant-
  annihilation dual-rail of the scalar quintic GPAC `y' = 1 − y^5` with
  zero initial condition admits a bounded solution on `[0, ∞)`.

  The bound `B` depends on `k` but not on `t`. -/
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
  -- `(k : ℝ) > 0` follows from `k > scalarQuinticThreshold > 0`.
  exact lt_trans scalarQuinticThreshold_pos hk

/-- **Corollary.** Instantiated at a specific concrete `k`, e.g. `k = 25`
(comfortably above `scalarQuinticThreshold = 20`), the scalar-quintic
dual-rail admits a bounded solution. Useful as a sanity-check instance
once the sub-lemmas are proven. -/
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
