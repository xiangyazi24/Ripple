/-
  Ripple.Core.PIVP — Polynomial Initial Value Problems

  Formalizes the GPAC/PIVP model:
    y'(t) = p(y(t)),   y(0) = y₀ ∈ ℚ^d

  where p : ℝ^d → ℝ^d is a vector of polynomials with rational coefficients.

  References:
  - Shannon (1941): GPAC = PIVP
  - Bournez-Graça-Pouly (2017): computability and complexity via trajectory length
  - [BAC] §2: Preliminaries
-/

import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Topology.MetricSpace.Basic

namespace Ripple

/-- A polynomial initial value problem (PIVP) in dimension d.

  The vector field `p` maps ℝ^d → ℝ^d via polynomials with rational coefficients.
  The initial condition `y₀` is a rational vector.
  The designated output is the component at index `output`. -/
structure PIVP (d : ℕ) where
  /-- The polynomial vector field. -/
  field : (Fin d → ℝ) → (Fin d → ℝ)
  /-- Initial condition. -/
  init : Fin d → ℝ
  /-- Index of the designated output variable. -/
  output : Fin d

/-- A PIVP is bounded if there exists M > 0 such that ‖y(t)‖ ≤ M for all t ≥ 0
  along the maximal solution. -/
def PIVP.IsBounded (P : PIVP d) (sol : ℝ → Fin d → ℝ) : Prop :=
  ∃ M : ℝ, 0 < M ∧ ∀ t : ℝ, 0 ≤ t → ‖sol t‖ ≤ M

/-- A solution to a PIVP: y'(t) = p(y(t)), y(0) = y₀. -/
structure PIVP.Solution (P : PIVP d) where
  /-- The trajectory. -/
  trajectory : ℝ → Fin d → ℝ
  /-- Satisfies initial condition. -/
  init_cond : trajectory 0 = P.init
  /-- Satisfies the ODE (pointwise). -/
  -- For now, this is stated informally; rigorous ODE solution
  -- will use Mathlib's ODE framework.
  is_solution : True  -- placeholder

/-- A PIVP computes a real number α if the output variable converges to α. -/
def PIVP.Computes (P : PIVP d) (sol : PIVP.Solution P) (α : ℝ) : Prop :=
  Filter.Tendsto (fun t => sol.trajectory t P.output) Filter.atTop (nhds α)

end Ripple
