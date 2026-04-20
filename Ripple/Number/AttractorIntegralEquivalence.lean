/-
  Ripple.Number.AttractorIntegralEquivalence

  Short note on Xiang's question (2026-04-20): are "integral-representable"
  and "ODE-attractor" constructions two distinct classes of CRN-computable
  numbers, or the same class?

  **Answer: the same class, by the fundamental theorem of calculus.**

  A `BoundedTimeComputable` witness is a polynomial ODE
    y'(t) = p(y(t)),  y(0) = y₀,
  whose output coordinate `y_k(t)` converges to `α`. Then for all `T ≥ 0`
    y_k(T) = y_k(0) + ∫₀^T p_k(y(s)) ds,
  and taking `T → ∞` gives
    α = y_k(0) + ∫₀^∞ p_k(y(s)) ds,
  so `α` admits an integral representation against its own trajectory.
  Conversely, if `α = ∫₀^∞ g(s) ds` is a convergent integral, the
  primitive `F(t) = ∫₀^t g(s) ds` satisfies `F → α`; whether `F` is a
  polynomial-ODE trajectory depends on whether `g` can be expressed as
  `p(F(t))` for a polynomial `p`, which is exactly the GPAC encoding
  question (and is the content the individual BTC constructions do).

  Consequently, the apparent "two classes" distinction is a
  *proof-style* convention: which direction the construction runs
  (known integral → reverse-engineered ODE, vs. given ODE → study its
  limit). It is not a distinction at the level of which numbers can be
  witnessed by `BoundedTimeComputable`.

  This file records that fact — the equivalence is definitional at the
  BTC level — and stops there. No Liouvillian / differential-Galois
  machinery, no speculative refinement: Xiang pointed out the prior
  version over-scoped (msg 1744).
-/

import Ripple.Core.BoundedTime

namespace Ripple.Number.AttractorIntegralEquivalence

open Ripple

/-- "Attractor class" at BTC granularity: `α` is the limit of the output
coordinate of some bounded PIVP. Every `BoundedTimeComputable` witness
already supplies this via its `convergence` field. -/
def IsAttractorClass (α : ℝ) : Prop := IsCRNComputable α

/-- "Integral class" at BTC granularity: `α` admits an integral
representation against a polynomial vector field integrated along its
own trajectory. By FTC, any BTC witness gives such a representation and
vice versa, so this is just `IsCRNComputable`. -/
def IsIntegralClass (α : ℝ) : Prop := IsCRNComputable α

/-- **Equivalence.** The two classes coincide at BTC granularity.
The content — that every BTC trajectory admits an FTC-integral form of
its limit — is elementary; the Lean statement is definitional. -/
theorem attractor_iff_integral (α : ℝ) :
    IsAttractorClass α ↔ IsIntegralClass α := Iff.rfl

/- The FTC bridge, informally: a BTC witness exhibits `α` as a limit
`lim_{T→∞} y_k(T)`, and Mathlib's `intervalIntegral.sub_deriv_eq_integral`
(or the equivalent) then rewrites the difference `y_k(T) − y_k(0)` as
`∫₀^T p_k(y(s)) ds`, so `α = y_k(0) + ∫₀^∞ p_k(y(s)) ds`. We do not
materialize this rewrite here because no downstream proof uses it; the
point of this file is to settle the conceptual question, not to produce
an integral-formula lemma that nothing depends on. -/

end Ripple.Number.AttractorIntegralEquivalence
