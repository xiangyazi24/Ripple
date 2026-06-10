/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Conditional phase progress — Phase E brick E3 (Doty exact majority)

From any configuration with a FIXED clock count `mC = |Clock| ≥ 2` (the clock count
is determined after Phase 0 and never changes), every *counter-timed* phase finishes
within expected `O((counterMax · mC) · n(n−1) / (mC(mC−1)))` interactions: the clock
counters always tick down, because a clock-clock meeting (probability
`≥ mC(mC−1)/(n(n−1))` per interaction) strictly decrements the combined counter while
it is positive.

This single **parameterized** bound yields BOTH of Phase E's regimes from one lemma:

* **bad-but-big-clock** (`mC ≥ n/5`, Lemma 5.2 floor): the rate is
  `mC(mC−1)/(n(n−1)) ≥ Θ(1)`, so the expected time is `O(counterMax · n)` — linear,
  matching the paper's "`O(log n)` parallel rounds" once `counterMax = O(n log n)`;
* **tiny-clock** (`mC ≥ 2`, the deterministic floor of Lemma 5.2): the rate is
  `≥ 2/(n(n−1))`, so the expected time is `O(counterMax · n²)` — polynomial, the
  negligible-probability fallback regime.

## Engine

The combined clock-counter potential `Φ` (the *sum* of all clock counters) is
non-increasing along `K` (`PotNonincr K Φ`) and drops by `≥ 1` whenever a clock-clock
pair meets, which happens with probability `≥ p := mC(mC−1)/(n(n−1))` **independently
of the current level** (any positive-counter clock pair fires the decrement).  This is
the *uniform-rate* special case of the level-split coupon engine of
`Phase10ExpectedTime.lean`: with `q m = 1 − p` for every level, the per-level waiting
time is `(1 − q m)⁻¹ = p⁻¹`, and `coupon_expectedHitting_le_uniform` gives

    expectedHitting K c (potBelow Φ 1) ≤ (Φ c) · p⁻¹  ≤  (counterMax · mC) · p⁻¹.

`potBelow Φ 1 = {Φ < 1} = {Φ = 0}` is the phase-advance trigger ("all clock counters
hit `0`").

This file is the **generic / parameterized** layer of E3 (cf. how E1/E2 separated the
generic hitting engine from the protocol instantiation in `RoleSplitConcentration` /
`Phase10Backup`).  It is abstract over `K : Kernel α α`, the potential `Φ`, and the
uniform per-step drop probability `p`; the protocol-level discharge of the
clock-clock meeting mass `≥ mC(mC−1)/(n(n−1))` is the consuming brick's obligation
(its rectangle aggregation route is the clock-clock analogue of E2's
`activeABPairs` / `sum_interactionProb_presentActiveAB`).

ZERO sorry, zero axiom (beyond `propext`/`Classical.choice`/`Quot.sound`),
zero `native_decide`.
-/

import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.Phase10ExpectedTime

namespace ExactMajority

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

set_option linter.unusedSectionVars false

namespace ConditionalPhaseProgress

/-! ## Part 1 — The uniform per-step drop rate arithmetic

The clock-clock meeting rate is `p = mC(mC−1)/(n(n−1))`.  We package the rate as an
`ℝ≥0∞` and record its reciprocal (= the per-level waiting time) in the two regimes. -/

/-- The clock-clock meeting probability per interaction at clock count `mC` in a
population of `n` agents: `mC(mC−1)` ordered clock pairs out of `n(n−1)` ordered
pairs. -/
noncomputable def clockPairRate (mC n : ℕ) : ℝ≥0∞ :=
  (mC * (mC - 1) : ℕ) / (n * (n - 1) : ℕ)

/-- The per-step counter-progress mass is at most `1` (it is a probability): a clock
pair is one event among the `n(n−1)` ordered pairs.  Needed so `1 − (1 − p) = p`
does not underflow in `ℝ≥0∞`. -/
theorem clockPairRate_le_one (mC n : ℕ) (hmC : mC ≤ n) :
    clockPairRate mC n ≤ 1 := by
  unfold clockPairRate
  have hnum : mC * (mC - 1) ≤ n * (n - 1) := Nat.mul_le_mul hmC (by omega)
  calc ((mC * (mC - 1) : ℕ) : ℝ≥0∞) / (n * (n - 1) : ℕ)
      ≤ ((n * (n - 1) : ℕ) : ℝ≥0∞) / (n * (n - 1) : ℕ) := by
        apply ENNReal.div_le_div_right
        exact_mod_cast hnum
    _ ≤ 1 := ENNReal.div_self_le_one

end ConditionalPhaseProgress

end ExactMajority
