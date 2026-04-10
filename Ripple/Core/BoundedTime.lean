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
  a linear time modulus: μ(r) = O(r). -/
def IsRealTimeComputable (α : ℝ) : Prop :=
  ∃ d : ℕ, ∃ btc : BoundedTimeComputable d α,
    ∃ C : ℝ, 0 < C ∧ ∀ r : ℕ, btc.modulus r ≤ C * r

/-- A real number is polynomial-time CRN-computable (floor n) if it has
  time modulus μ(r) = O(r^n). -/
def IsPolyTimeComputable (α : ℝ) (n : ℕ) : Prop :=
  ∃ d : ℕ, ∃ btc : BoundedTimeComputable d α,
    ∃ C : ℝ, 0 < C ∧ ∀ r : ℕ, btc.modulus r ≤ C * (r : ℝ) ^ n

/-- Real-time computable numbers form a field (from [RTCRN2]).
  This is stated as an axiom for now; the proof requires constructing
  the arithmetic ODE modules. -/
axiom realtime_field_add {α β : ℝ} :
  IsRealTimeComputable α → IsRealTimeComputable β → IsRealTimeComputable (α + β)

axiom realtime_field_mul {α β : ℝ} :
  IsRealTimeComputable α → IsRealTimeComputable β → IsRealTimeComputable (α * β)

end Ripple
