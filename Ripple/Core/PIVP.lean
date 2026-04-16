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
import Mathlib.RingTheory.MvPolynomial.Basic
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

/-- A syntactic PIVP whose vector field is explicitly given by multivariate
polynomials over `ℚ`, and whose initial condition is rational.

This is the non-vacuous layer needed for compilation-style theorems from the
paper: unlike `PIVP`, it does not allow arbitrary real constants to be hidden
in the field or in the initial condition. -/
structure PolyPIVP (d : ℕ) where
  /-- Each component of the vector field is a polynomial in the state
  variables with rational coefficients. -/
  field : Fin d → MvPolynomial (Fin d) ℚ
  /-- Rational initial condition. -/
  init : Fin d → ℚ
  /-- Designated output component. -/
  output : Fin d

namespace PolyPIVP

/-- Evaluate the polynomial vector field on a real state vector. -/
noncomputable def evalField (P : PolyPIVP d) (x : Fin d → ℝ) : Fin d → ℝ :=
  fun i => (P.field i).eval₂ (Rat.castHom ℝ) x

/-- Forget the syntactic certification and obtain the semantic `PIVP`. -/
noncomputable def toPIVP (P : PolyPIVP d) : PIVP d where
  field := P.evalField
  init := fun i => (P.init i : ℝ)
  output := P.output

@[simp] theorem toPIVP_output (P : PolyPIVP d) :
    P.toPIVP.output = P.output := rfl

@[simp] theorem toPIVP_init (P : PolyPIVP d) (i : Fin d) :
    P.toPIVP.init i = (P.init i : ℝ) := rfl

/-- The semantic initial condition extracted from a `PolyPIVP` is rational,
in the explicit sense that each component is the cast of a rational number. -/
theorem init_is_rational (P : PolyPIVP d) (i : Fin d) :
    ∃ q : ℚ, P.toPIVP.init i = (q : ℝ) := ⟨P.init i, rfl⟩

end PolyPIVP

/-- A PIVP is bounded if there exists M > 0 such that ‖y(t)‖ ≤ M for all t ≥ 0
  along the maximal solution. -/
def PIVP.IsBounded (_P : PIVP d) (sol : ℝ → Fin d → ℝ) : Prop :=
  ∃ M : ℝ, 0 < M ∧ ∀ t : ℝ, 0 ≤ t → ‖sol t‖ ≤ M

/-- A solution to a PIVP: y'(t) = p(y(t)), y(0) = y₀. -/
structure PIVP.Solution (P : PIVP d) where
  /-- The trajectory. -/
  trajectory : ℝ → Fin d → ℝ
  /-- Satisfies initial condition. -/
  init_cond : trajectory 0 = P.init
  /-- Satisfies the ODE y'(t) = p(y(t)) for all t ≥ 0. -/
  is_solution : ∀ t : ℝ, 0 ≤ t → HasDerivAt trajectory (P.field (trajectory t)) t

/-- A PIVP computes a real number α if the output variable converges to α. -/
def PIVP.Computes (P : PIVP d) (sol : PIVP.Solution P) (α : ℝ) : Prop :=
  Filter.Tendsto (fun t => sol.trajectory t P.output) Filter.atTop (nhds α)

end Ripple
