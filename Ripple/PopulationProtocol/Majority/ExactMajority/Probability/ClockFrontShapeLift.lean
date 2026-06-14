/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# `ClockFrontShapeLift` — the measure lift G1a (real FrontSync-exit ≤ marked ShapeGood-fail).

The Layer-D first-exit needs the REAL-kernel FrontSync-exit mass `(realκ^τ) (erase mc₀) {¬ FrontSync}`
bounded by marked-kernel events.  This file supplies the FIRST half of that lift (independent of the
stopped→markedK gate-exit transfer): transport the real-kernel exit to the MARKED kernel via
`EarlyDripMarked.markedK_pow_erase` (the marked chain projects EXACTLY to the real chain at every
horizon), then apply the contrapositive of the deterministic certificate
`ClockShapeGood.frontSync_of_shapeGood` (`ShapeGood ∧ clockCount(erase)=C₀ ⟹ FrontSync(erase)`):

  `(realκ^τ) (erase mc₀) {¬ FrontSync}
     ≤ (markedK^τ) mc₀ {¬ ShapeGood}  +  (markedK^τ) mc₀ {clockCount(erase) ≠ C₀}`.

The first term is closed by Layer-B (`¬ ShapeGood` = a mesoscopic `Lemma63Bad` ∨ ghost-large ∨ climb
∨ bulk failure) routed through `ClockLayerD.windowBadMass` once the stopped→markedK gate-exit lands;
the second is the conserved-quantity invariant (`clockCount` preserved, ≈ 0 — the start-structure
escape).  `2 ≤ C₀` and `1/C₀ ≤ θ` are global constants (carried hypotheses, not per-config events).

NEW file; no existing file edited; no sorry/admit/axiom/native_decide.
Reference: `DOCTRINE_THM69_CA.md` Layer D (the first-exit transfer); Doty et al. (arXiv:2106.10201v2).
-/

import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.ClockShapeGood

namespace ExactMajority

namespace ClockFrontShapeLift

open MeasureTheory ProbabilityTheory
open ClockShapeGood ClockLayerB ClockRealKernel ClockRealMixed ClockFrontShape EarlyDripMarked
open scoped ENNReal NNReal

variable {L K : ℕ}

/-- **The measure lift G1a.**  Via `markedK_pow_erase` (marked → real projection) and the
contrapositive of `frontSync_of_shapeGood`, the real-kernel FrontSync-exit mass is bounded by the
marked-kernel `¬ ShapeGood` mass plus the `clockCount`-invariant escape.  `T θn` are the marking
level/threshold (the erased real chain is the same for any choice). -/
theorem frontSyncExit_le_shapeGoodFail
    (T θn C₀ : ℕ) (θ p : ℝ) (W₂ τ : ℕ) (mc₀ : MCfg L K)
    (hp1 : p ≤ 1) (hC₀ : 2 ≤ C₀) (hθ : 1 / (C₀ : ℝ) ≤ θ) :
    ((NonuniformMajority L K).transitionKernel ^ τ)
        (eraseConfig (L := L) (K := K) mc₀)
        {c | ¬ FrontSync (L := L) (K := K) c}
      ≤ ((markedK (L := L) (K := K) T θn) ^ τ) mc₀
          {mc | ¬ ShapeGood (L := L) (K := K) C₀ θ p W₂ mc}
        + ((markedK (L := L) (K := K) T θn) ^ τ) mc₀
          {mc | clockCount (L := L) (K := K) (eraseConfig (L := L) (K := K) mc) ≠ C₀} := by
  classical
  rw [← markedK_pow_erase (L := L) (K := K) T θn τ mc₀ {c | ¬ FrontSync (L := L) (K := K) c}]
  refine le_trans (measure_mono ?_) (measure_union_le _ _)
  intro mc hmc
  have hmc' : ¬ FrontSync (L := L) (K := K) (eraseConfig (L := L) (K := K) mc) := hmc
  by_cases hcard : clockCount (L := L) (K := K) (eraseConfig (L := L) (K := K) mc) = C₀
  · left
    intro hSG
    exact hmc' (frontSync_of_shapeGood (L := L) (K := K) C₀ θ p W₂ mc hp1 hcard hC₀ hθ hSG)
  · right
    exact hcard

end ClockFrontShapeLift

end ExactMajority
