/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# `ClockCleanStep` — the deterministic clean-step bridge (Layer-B ⟹ squaring).

The Layer-B forward window transfer (`ClockLayerB.lemma63_window_transfer_forward`) controls the
endpoint event `¬ Lemma63Bad`, i.e. `X_{T+1} ≤ 0.9·p·X_T² + D_T/C₀` (clean squaring plus the ghost
immigration term `D/C₀`).  The mixed Theorem-6.5 geometry (`ClockFrontMixed.ClockWindowedFrontProfile`,
consumed by `ClockFrontShapeCert.frontSync_of_windowed_climb_bulk_mixed`) needs the GHOST-FREE squaring
`X_{T+1} ≤ X_T²`.  `lemma65_clean_step_from_ghost` is the deterministic algebra that closes the gap:
once GhostSmall makes `D_T/C₀ ≤ (1/10)·X_T²` (the negligible-ghost regime, `X_T ≥ n^{−0.4}` so
`D/C₀ ≤ η = n^{−0.85} ≤ 0.1·X_T²`), the `0.9·p·X_T²` clean term (with `p ≤ 1`) plus the `≤ 0.1·X_T²`
ghost is `≤ X_T²`.  Pure real algebra; no probability.

This is the load-bearing link between `ClockLayerB` (Layer-B output) and `ClockFrontShapeCert`
(deterministic FrontSync certificate): `¬ Lemma63Bad ∧ GhostSmall ⟹ ClockWindowedFrontProfile`-style
per-level squaring at the erased config.

NEW file; no existing file edited; no sorry/admit/axiom/native_decide.
Reference: `DOCTRINE_THM69_CA.md` Round 5 (`lemma65_clean_step_from_ghost`); Doty et al.
(arXiv:2106.10201v2) Lemma 6.5.
-/

import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.ClockLayerB

namespace ExactMajority

namespace ClockCleanStep

open ClockLayerB

variable {L K : ℕ}

/-- **`lemma65_clean_step_from_ghost` — the deterministic clean step.**  On the negligible-ghost
regime (`D_T/C₀ ≤ (1/10)·X_T²`), the Layer-B endpoint bound `¬ Lemma63Bad`
(`X_{T+1} ≤ 0.9·p·X_T² + D_T/C₀`) collapses to the ghost-free squaring `X_{T+1} ≤ X_T²` for any
`0 ≤ p ≤ 1`.  Pure algebra: `0.9·p·X² + 0.1·X² ≤ 0.9·X² + 0.1·X² = X²` (using `p ≤ 1`, `X² ≥ 0`). -/
theorem lemma65_clean_step_from_ghost (C₀ T : ℕ) (p : ℝ) (mc : MCfg L K)
    (hp1 : p ≤ 1)
    (hbad : ¬ Lemma63Bad (L := L) (K := K) C₀ T p mc)
    (hghost : Dfrac (L := L) (K := K) C₀ T mc
      ≤ (1 / 10 : ℝ) * (X (L := L) (K := K) C₀ T mc) ^ 2) :
    X (L := L) (K := K) C₀ (T + 1) mc ≤ (X (L := L) (K := K) C₀ T mc) ^ 2 := by
  unfold Lemma63Bad at hbad
  push Not at hbad
  -- hbad : X_{T+1} ≤ 0.9·p·X² + D/C₀
  have hXsq : (0 : ℝ) ≤ (X (L := L) (K := K) C₀ T mc) ^ 2 := sq_nonneg _
  have hp1' : (0 : ℝ) ≤ 1 - p := by linarith
  nlinarith [hbad, hghost, hXsq, mul_nonneg hp1' hXsq]

end ClockCleanStep

end ExactMajority
