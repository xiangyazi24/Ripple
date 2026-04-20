/-
  Ripple.Core.CRNPipeline — GPAC-to-CRN Pipeline

  Formalizes the pipeline from [BAC] §7:
    Bounded GPAC → Dual-rail encoding → Readout subtraction → CRN

  Key results:
  - Dual-rail encoding is exact (from [RTCRN2], [Fages 2017])
  - Readout subtraction acts as a low-pass filter
  - Time complexity is preserved through the full pipeline

  The low-pass filter analysis ([BAC] §7.2):
    δ̇ + α·δ = α·ε(t)
  where ε is the input error and δ is the readout error.

  Two regimes:
  - Input-limited: ε decays slower than e^{-αt} → δ(t) ~ ε(t)
  - Module-limited: ε decays faster than e^{-αt} → δ(t) ~ Ce^{-αt}
-/

import Ripple.Core.Compilation
import Ripple.DualRail.Tier1Composition
import Ripple.LPP.Stages
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace Ripple

/-- A CRN (Chemical Reaction Network) is a bounded PIVP where all
  variables represent non-negative species concentrations and the
  dynamics follow mass-action kinetics. -/
structure CRN (d : ℕ) extends PIVP d where
  /-- All species concentrations are non-negative. -/
  nonneg : ∀ i : Fin d, 0 ≤ init i

/-- **CRN readout closure** (honest version).

From a `BoundedTimeComputable` for `α ∈ [0, 1]` whose underlying PIVP
has a polynomial-field presentation with zero initial conditions, one
obtains a `CertifiedBoundedTimeComputable` with an accompanying
`PolyCRNDecomposition` — i.e., a concrete mass-action CRN witness for
the same real number.

This is the [BAC] §7 readout content: the dual-rail + subtraction
readout (DNA25 annihilation + Lemma 8) is CRN-implementable. The
induced modulus is the explicit chain of Stage A + Stage B composed
with the input modulus (see `Ripple.DualRail.btc_to_cbtc_pcd_of_unit_interval`).

The previous "modulus ≤ input + C" signature was vacuously satisfied
by the identity witness (C = 0) and carried no CRN content; it has been
replaced by this honest CBTC + PCD statement. The sharpened modulus
bound of [BAC] Thm 7.3 (asymptotic low-pass filter regimes) is a
follow-up quantitative refinement, not part of the structural closure. -/
theorem crn_readout_preserves_complexity {d : ℕ} [NeZero d] {α : ℝ}
    (btc : BoundedTimeComputable d α)
    (p : Fin d → MvPolynomial (Fin d) ℚ)
    (h_field : ∀ y : Fin d → ℝ, ∀ i : Fin d,
        btc.pivp.field y i = (p i).eval₂ (Rat.castHom ℝ) y)
    (h_zero : ∀ j : Fin d, btc.pivp.init j = 0)
    (hα_lo : 0 ≤ α) (hα_hi : α ≤ 1) :
    ∃ (d' : ℕ) (cbtc' : CertifiedBoundedTimeComputable d' α)
      (_ : PolyCRNDecomposition d' cbtc'.pivp), True :=
  Ripple.DualRail.btc_to_cbtc_pcd_of_unit_interval btc p h_field h_zero hα_lo hα_hi

/-- **Exponentiation closure** ([BAC] Thm 6.1), structural reduction.

Given CRN-computability of `α, β`, closure of the CRN-computable reals
under the real exponential (`h_exp`) and under the real logarithm on
positive reals (`h_log`), the rpow `α^β = exp(log α · β)` is
CRN-computable. Multiplication closure is discharged internally via
`crn_computable_mul`.

This replaces the prior placeholder which invoked `realtime_const` on
the exact value `α^β` — a vacuous witness that presupposes the
computation it claims to deliver. The present statement honestly
exposes the two missing sub-closures (`exp`, `log`) as explicit
hypotheses: when they are discharged (via the [BAC] §6 dual-rail
construction for `exp` and the reciprocal-tracker construction for
`log`), rpow closure follows purely by composition. -/
theorem closure_exponentiation_via_exp_log {α β : ℝ} (hα : 0 < α)
    (ha : IsCRNComputable α) (hb : IsCRNComputable β)
    (h_exp : ∀ γ : ℝ, IsCRNComputable γ → IsCRNComputable (Real.exp γ))
    (h_log : ∀ γ : ℝ, 0 < γ → IsCRNComputable γ → IsCRNComputable (Real.log γ)) :
    IsCRNComputable (Real.rpow α β) := by
  change IsCRNComputable (α ^ β)
  rw [Real.rpow_def_of_pos hα β]
  exact h_exp _ (crn_computable_mul (h_log α hα ha) hb)

end Ripple
