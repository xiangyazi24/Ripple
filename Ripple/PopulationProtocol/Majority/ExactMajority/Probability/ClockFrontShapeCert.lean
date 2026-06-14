/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# `ClockFrontShapeCert` — the deterministic Layer-D certificate (ShapeGood ⟹ FrontSync).

The Layer-D first-exit transfer needs a DETERMINISTIC certificate that turns the per-config
"shape-good" data — the mixed windowed squaring (`ClockWindowedFrontProfile`, the Layer-B Lemma-6.3
output), the sub-floor climb bound (`ClockClimbBound`, the sparse-pioneer output), and the bulk
position (the `0.1`-clock-bulk is BELOW the top band) — into `FrontSync` (no clock at the cap).
This is the deterministic spine of `front_shape_exit_prob`: whatever whp event the Layer-B/C
concentrations establish, THIS lemma converts it pointwise to `FrontSync`, so the first-exit union
of `¬ FrontSync` is bounded by the union of the shape-good failures.

`frontSync_of_windowed_climb_bulk_mixed` composes the two proven mixed-geometry lemmas
(`ClockFrontMixed.clockGoodFrontWidth_of_windowed_profile_and_climb_mixed` ⟹
`ClockGoodFrontWidth`, then `ClockFrontMixed.frontSync_of_clockGoodWidth_of_bulk_below` ⟹
`FrontSync`) at the moving-frame width `W = frontWidthBound C₀ + W₂`.  Purely deterministic; the
probabilistic content (that the three antecedents HOLD whp along the trajectory) is the Layer-B/C
concentration, NOT touched here.

NEW file; no existing file edited; no sorry/admit/axiom/native_decide.
Reference: Doty et al. (arXiv:2106.10201v2) Theorem 6.5; `DOCTRINE_THM69_CA.md` Layer D.
-/

import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.ClockFrontMixed

namespace ExactMajority

namespace ClockFrontShapeCert

open ClockFrontMixed ClockRealKernel ClockRealMixed ClockFrontShape FrontTail

variable {L K : ℕ}

/-- **The deterministic Layer-D certificate: shape-good ⟹ `FrontSync`.**
Given the mixed clock window (`clockCount = C₀`, `2 ≤ C₀`, floor `θ ≥ 1/C₀`), the windowed squaring
recurrence `ClockWindowedFrontProfile` and the sub-floor climb bound `ClockClimbBound` collapse the
clock profile to the moving-frame width `W = frontWidthBound C₀ + W₂` (the mixed Theorem-6.5
reduction).  If additionally the `0.1`-clock-bulk has NOT reached within `W` minutes of the cap
(`10·rBeyond(capMinute − W) < C₀`), the cap is empty: `FrontSync c`. -/
theorem frontSync_of_windowed_climb_bulk_mixed
    (C₀ : ℕ) (θ : ℝ) (W₂ : ℕ) (c : Config (AgentState L K))
    (hC₀card : clockCount (L := L) (K := K) c = C₀) (hC₀ : 2 ≤ C₀)
    (hθ : 1 / (C₀ : ℝ) ≤ θ)
    (hwp : ClockWindowedFrontProfile (L := L) (K := K) C₀ θ c)
    (hcb : ClockClimbBound (L := L) (K := K) C₀ θ W₂ c)
    (hbulk : 10 * rBeyond (L := L) (K := K)
        (capMinute (L := L) (K := K) - (FrontTail.frontWidthBound C₀ + W₂)) c < C₀) :
    FrontSync (L := L) (K := K) c := by
  have hwidth :=
    clockGoodFrontWidth_of_windowed_profile_and_climb_mixed
      C₀ θ W₂ c hC₀card hC₀ hθ hwp hcb
  exact frontSync_of_clockGoodWidth_of_bulk_below
    C₀ (FrontTail.frontWidthBound C₀ + W₂) c hwidth hbulk

end ClockFrontShapeCert

end ExactMajority
