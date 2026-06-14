/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# `ClockShapeGood` — the deterministic `ShapeGood ⟹ FrontSync` certificate (marked config).

This assembles the deterministic spine of the Layer-D first-exit certificate into ONE per-config
implication on the MARKED kernel.  A marked config is `ShapeGood` when, on its erased projection:

* at every mesoscopic level (`θ ≤ X_T ≤ 1/10`) the Layer-B endpoint succeeds (`¬ Lemma63Bad`) and the
  ghost is negligible (`D_T/C₀ ≤ (1/10)·X_T²`) — the per-level clean-step inputs (`ClockCleanStep`);
* the sub-floor climb bound holds (`ClockClimbBound`) — the sparse-pioneer output;
* the `0.1`-clock-bulk is below the top band (`10·rBeyond(cap − W) < C₀`) — the bulk position.

Then `ClockCleanStep.lemma65_clean_step_from_ghost` supplies the squaring at every mesoscopic level,
i.e. `ClockFrontMixed.ClockWindowedFrontProfile` on the erased config, and
`ClockFrontShapeCert.frontSync_of_windowed_climb_bulk_mixed` concludes `FrontSync (eraseConfig mc)`.

This is the DETERMINISTIC half of Layer D (`front_shape_exit`): whatever whp event the Layer-B window
transfer (`ClockLayerD.windowBad…`) + GhostSmall (`GhostSmallConc`) + sparse establish, THIS lemma
converts it pointwise to `FrontSync`, so the first-exit union `{¬FrontSync}` is bounded by the
`¬ ShapeGood` union.  The probabilistic lift (`{¬FrontSync at τ} ≤ ¬ShapeGood union`, and the
`markedK_pow_erase` transfer to the real kernel) is the remaining Layer-D measure step.

NEW file; no existing file edited; no sorry/admit/axiom/native_decide.
Reference: `DOCTRINE_THM69_CA.md` Layer D + Round 5/6; Doty et al. (arXiv:2106.10201v2) Theorem 6.5.
-/

import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.ClockCleanStep
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.ClockFrontShapeCert

namespace ExactMajority

namespace ClockShapeGood

open ClockLayerB ClockCleanStep ClockFrontShapeCert ClockFrontMixed
open ClockRealKernel ClockRealMixed ClockFrontShape FrontTail EarlyDripMarked

variable {L K : ℕ}

/-- **The per-config `ShapeGood` predicate** (marked, evaluated on the erased projection).  The
deterministic certificate's hypothesis: mesoscopic clean-steps + climb + bulk-below-cap. -/
def ShapeGood (C₀ : ℕ) (θ p : ℝ) (W₂ : ℕ) (mc : MCfg L K) : Prop :=
  (∀ T : ℕ, θ ≤ X (L := L) (K := K) C₀ T mc → X (L := L) (K := K) C₀ T mc ≤ 1 / 10 →
      ¬ Lemma63Bad (L := L) (K := K) C₀ T p mc ∧
        Dfrac (L := L) (K := K) C₀ T mc
          ≤ (1 / 10 : ℝ) * (X (L := L) (K := K) C₀ T mc) ^ 2) ∧
    ClockClimbBound (L := L) (K := K) C₀ θ W₂ (eraseConfig (L := L) (K := K) mc) ∧
    10 * rBeyond (L := L) (K := K)
        (capMinute (L := L) (K := K) - (FrontTail.frontWidthBound C₀ + W₂))
        (eraseConfig (L := L) (K := K) mc) < C₀

/-- **The mesoscopic clean-steps give the windowed squaring** on the erased config.  Each level with
`θ ≤ X_T ≤ 1/10` squares (`X_{T+1} ≤ X_T²`) by `lemma65_clean_step_from_ghost`, i.e. exactly
`ClockWindowedFrontProfile` (since `X C₀ T mc = ClockFrac C₀ T (eraseConfig mc)` definitionally). -/
theorem windowedProfile_of_shapeGood (C₀ : ℕ) (θ p : ℝ) (W₂ : ℕ) (mc : MCfg L K)
    (hp1 : p ≤ 1) (hShape : ShapeGood (L := L) (K := K) C₀ θ p W₂ mc) :
    ClockWindowedFrontProfile (L := L) (K := K) C₀ θ (eraseConfig (L := L) (K := K) mc) := by
  intro T hlo hhi
  obtain ⟨hsteps, _, _⟩ := hShape
  obtain ⟨hbad, hghost⟩ := hsteps T hlo hhi
  exact lemma65_clean_step_from_ghost (L := L) (K := K) C₀ T p mc hp1 hbad hghost

/-- **`frontSync_of_shapeGood` — the deterministic Layer-D certificate.**  On the mixed clock window
(`clockCount (erase mc) = C₀`, `2 ≤ C₀`, `1/C₀ ≤ θ`), `ShapeGood ⟹ FrontSync (eraseConfig mc)`: the
mesoscopic clean-steps give the windowed squaring, and the climb + bulk-below-cap conjuncts feed
`ClockFrontShapeCert.frontSync_of_windowed_climb_bulk_mixed`. -/
theorem frontSync_of_shapeGood (C₀ : ℕ) (θ p : ℝ) (W₂ : ℕ) (mc : MCfg L K)
    (hp1 : p ≤ 1)
    (hcard : clockCount (L := L) (K := K) (eraseConfig (L := L) (K := K) mc) = C₀)
    (hC₀ : 2 ≤ C₀) (hθ : 1 / (C₀ : ℝ) ≤ θ)
    (hShape : ShapeGood (L := L) (K := K) C₀ θ p W₂ mc) :
    FrontSync (L := L) (K := K) (eraseConfig (L := L) (K := K) mc) := by
  have hwp := windowedProfile_of_shapeGood (L := L) (K := K) C₀ θ p W₂ mc hp1 hShape
  obtain ⟨_, hclimb, hbulk⟩ := hShape
  exact frontSync_of_windowed_climb_bulk_mixed C₀ θ W₂
    (eraseConfig (L := L) (K := K) mc) hcard hC₀ hθ hwp hclimb hbulk

end ClockShapeGood

end ExactMajority
