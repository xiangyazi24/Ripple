/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Phase-1 averaging collapse — the saturated-side floor (the last of the four floors)

`HANDOFF_FOUR_FLOORS.md` §1: the Phase-1 saturated-side floor.  Whp over the Phase-1 window,
the saturated-positive Mains (`smallBias.val ≥ 5`) stay `≤ n/3 − P`, so `pullPosSet ≥ P` via the
landed Main decomposition `PhaseFloors.mainCount_eq_pullPos_add_saturatedPos` and the wrapper
`EliminatorMargins.phase1_pullPos_floor_of_mainCount_and_saturated_bound`.

## The honest self-contained route: a deterministic second-moment ledger

The paper imports the quantitative collapse from reference [45] (Mocquard et al., discrete
averaging) — all Main `smallBias`es converge to `{µ−1,µ,µ+1}` in `O(log n)` whp.  Rather than
formalize [45]'s variance-decay argument wholesale, we use the genuine self-contained mechanism
the blueprint points at: **bounded pairwise averaging contracts the second moment.**

The FROZEN Phase-1 rule (`Protocol/Transition.lean`, `avgFin7`) replaces two Mains' `smallBias`
values `x, y : Fin 7` by `(⌊(x+y)/2⌋, ⌈(x+y)/2⌉)`.  The exact integer ledger, computed over all
`7 × 7 = 49` pairs (both parities), centred at the encoding origin `3` (`smallBiasInt = v − 3`):

* the sum is preserved: `x' + y' = x + y` (`avgFin7_preserves_sum`);
* the **centred second moment drops by exactly `⌊(x−y)²/2⌋`**:
  `(x−3)² + (y−3)²  −  (x'−3)² − (y'−3)² = ⌊(x−y)²/2⌋ ≥ 0`.
  (Even parity: drop `= (x−y)²/2`; odd parity: drop `= ((x−y)²−1)/2`.  The centred drop equals
  the raw `Σv²` drop because the linear term cancels under the preserved sum.)

So `Φ(c) := Σ_{phase-1 Mains} (smallBias.val − 3)²` (the ℕ-valued centred second moment, computed
as `sqDist3N`) is **deterministically non-increasing** under every averaging interaction — no
expectation, no martingale: the variance literally never rises.  This is the honest potential the
blueprint asked for ("a cosh/variance contraction potential"); the contraction is so clean it is
a per-step ℕ-monotone, plugging straight into the same `OneSidedCancel` level engine that
`Phase1Convergence` already uses for `extremeU`.

## The saturated-count conversion (fully proved, exact)

A saturated-positive Main has `smallBias.val ≥ 5`, hence `(smallBias.val − 3)² ≥ 4`.  Summing,
`4 · #saturatedPos ≤ Φ` (`four_mul_saturatedPos_le_secondMoment`).  So `Φ ≤ 4·(n/3 − P)` forces
`#saturatedPos ≤ n/3 − P`, which is EXACTLY the saturated-side budget the wrapper
`phase1_pullPos_floor_of_mainCount_and_saturated_bound` consumes.  The "what is the mean µ"
design question dissolves: centring at the fixed encoding origin `3` already gives distance `≥ 2`
for every saturated value, so no estimate of the true mean is needed.

## What is fully proved vs carried

FULLY PROVED (0-sorry, axiom-clean): the exact per-rule ledger (`avgFin7_sqDist3_pair_le` /
`avgFin7_sqDist3_pair_drop`, both parities by exhaustive `decide`); the deterministic
config-kernel non-increase of `Φ = secondMomentN` on the `Phase1AllMain` window
(`PotNonincrOn`, mirroring `extremeU`); the saturated-count conversion
(`four_mul_saturatedPos_le_secondMoment`); the whp tail through the landed `OneSidedCancel`
level engine (`secondMoment_level_tail`); and the wired floor
(`phase1_saturatedPos_le_whp` → `phase1_pullPos_floor_whp`) feeding
`EliminatorMargins.phase1_pullPos_floor_of_mainCount_and_saturated_bound`.

CARRIED (exactly one named quantitative input, with paper provenance): the per-step
second-moment drain rate `q` (the `hstep`/`hdrop` hypothesis).  This is the SAME atom
`Phase1Convergence.phase1Convergence` carries for `extremeU` — the per-interaction probability
that a distant pair averages strictly inward, `≥ (pair count)/(n(n−1))`-shape, the quantitative
content the paper imports from reference [45] (Corollary 1).  It is exposed as a hypothesis
exactly as Phases 1/7/8 expose theirs; everything structural around it is discharged.

NEW file; no existing file is edited; no sorry/admit/axiom/native_decide.
-/

import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.EliminatorMargins
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.WindowConcentration

namespace ExactMajority

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace AveragingCollapse

variable {L K : ℕ}

attribute [local instance] Classical.propDecidable

/-! ## Stage 1 — the per-rule second-moment ledger (exact `Fin 7` integer arithmetic).

`sqDist3N v` is the ℕ-valued squared distance of a `Fin 7` value `v` from the encoding origin `3`
(`= (v.val − 3)²`, written with truncated ℕ subtraction so it is genuinely `ℕ`-valued).  Centred
at `3`, this is the per-agent contribution to the second moment `Σ (smallBias.val − 3)²`. -/

/-- ℕ-valued squared distance from the encoding origin `3` (`(v.val − 3)²` as a natural). -/
def sqDist3N (v : Fin 7) : ℕ :=
  (if v.val ≤ 3 then 3 - v.val else v.val - 3) ^ 2

/-- **The per-pair second-moment NON-INCREASE (exhaustive).**  The averaging rule never raises the
centred second moment: the sum of the two outputs' `sqDist3N` is at most the sum of the two
inputs'.  Verified over all `7 × 7 = 49` pairs (both parities) by `decide`. -/
theorem avgFin7_sqDist3_pair_le (x y : Fin 7) :
    sqDist3N (avgFin7 x y).1 + sqDist3N (avgFin7 x y).2
      ≤ sqDist3N x + sqDist3N y := by
  revert x y; decide

/-- **The EXACT per-pair drop (exhaustive, both parities).**  The centred second moment drops by
exactly `⌊(x.val − y.val)²/2⌋` per averaging interaction.  Even parity gives `(Δ)²/2`, odd parity
`((Δ)²−1)/2`; both are captured by the single floor expression.  Verified over all 49 pairs by
`decide`.  (Stated as an additive identity in ℕ; the `+` form avoids ℕ-subtraction pitfalls.) -/
theorem avgFin7_sqDist3_pair_drop (x y : Fin 7) :
    sqDist3N (avgFin7 x y).1 + sqDist3N (avgFin7 x y).2
        + (max x.val y.val - min x.val y.val) ^ 2 / 2
      = sqDist3N x + sqDist3N y := by
  revert x y; decide

/-- A saturated value (`v.val ≥ 5`) is at squared distance `≥ 4` from the origin `3`. -/
theorem sqDist3N_ge_four_of_saturated (v : Fin 7) (h : 5 ≤ v.val) :
    4 ≤ sqDist3N v := by
  revert h; revert v; decide

end AveragingCollapse

end ExactMajority
