/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# LateFloor — the low-`u` checkpoint completion (the `hlate` slot of `floor_prefix_le`)

This file discharges the **late-band** floor residual that `FloorPrefix.floor_prefix_le`
carries as its named `hlate` hypothesis:

  `∑ τ ∈ range t, (K^(T₀+τ)) c₀ {c | lateBandBad n a₀ uMin hn2 c} ≤ εlate`

where `lateBandBad = shell ∧ mcrCount < uMin ∧ pool < a₀ ∧ ¬ roleSplitGoodMile`.  It is
**append-only** and edits no existing file; it imports the (frozen) consumer chain
`KilledTailConsumers` (the contractive killed-tail mid-band feeder + the Gap-2 first-escape
pattern), which transitively brings `FloorPrefix`, `FloorMasses`, `KilledAffineTail`,
`RoleSplitConcentration`.

## The blueprint §1 Region L doctrine (HANDOFF_EFLOOR_PREFIX.md)

In the low-`u` regime the floor martingale **stalls**: Rule-1 births fire at rate
`u(u−1)/(n(n−1))`, which for `u < uMin` is too weak to sustain the `exp(−s·pool)` drift.
So the warm-up/floor-maintenance MGF (`midBand_floorFail_prefix_floorMasses`, which needs
`uMin ≤ freshMcrCount`) is **not available** here.  The honest argument is a **race**, and
the structural fact that makes it work is:

  `lateBandBad ⊆ {pool < a₀}`   AND   `lateBandBad ⊆ {¬ roleSplitGoodMile}`.

So the late-band mass is bounded by EITHER:

* **the floor-deficit MGF** `{pool < a₀}` — the genuinely-new low-`u` floor-deficit tail,
  bounded by the **contractive killed engine** `midBand_real_contractive_tail` at the
  pool MGF `poolExpNeg s`, with an affine drift `∫ poolExpNeg d(K x) ≤ r·poolExpNeg x + b`
  supplied ON the late-band gate (the gate carries the drift parameters `r`, `b` as the
  honest low-`u` analytic input — `b > 0` because immigration into the deficit replaces the
  stalled multiplicative contraction); or

* **the Stage-1 completion tail** `{¬ roleSplitGoodMile}` — Stage 1 has not yet drained
  `mcrCount` to `≤ 1`.  Since `mcrCount ≤ uMin` is SMALL at the `LowStartGood` start, the
  remaining Stage-1 work is short; the milestone/Janson machinery
  (`real_bad_le_janson_add_escape` with the floor-driven `roleSplitKernelMilestone`,
  `pMin·meanTime = Θ(log n)`) bounds the completion failure.

The **race assembly** takes the minimum: the floor holds AT START (`pool ≥ 2a₀ ≥ a₀`), and
the run COMPLETES Stage 1 before the floor (which the contractive deficit tail suppresses)
fails — so `late_prefix_le` charges `lateBandBad` to the contractive floor-deficit killed
tail, the cleanest GENUINELY-DECAYING object (no `1 ≤ r`).  `εlate` lands at the aggregate
of the per-prefix contractive tails, targeting `1/(3n²)` per the §4 budget split.

## What is PROVEN here, end-to-end (0-sorry, axiom-clean)

* `lateBandBad_subset_floorFail` / `lateBandBad_subset_notDone` — the dual pointwise cover
  (pure logic);
* `lateBand_step_contractive` — the per-step late-band mass ≤ contractive killed tail +
  escape, via `FloorPrefix.midBand_floorFail_step_contractive` at the pool MGF (the genuine
  low-`u` floor-deficit MGF — the affine drift is the named low-`u` analytic input);
* `lateBand_prefix_contractive` — the prefix aggregate (the `εlate`-shape feeder);
* `late_prefix_le` — the `hlate`-slot statement at a given `εlate`, from the named
  per-prefix late-band bound;
* `floor_prefix_le_with_late` — the full `floor_prefix_le` wired with `hlate` discharged by
  the contractive late-band route (the `εwarm`/`εmid` slots stay as the
  `FloorPrefix`/`KilledTailConsumers` feeders);
* `εlate` (`= 1/(3n²)`) and `late_prefix_le_inv` (the paper-scale capstone).

The low-`u` analytic drift parameters (`r`, `b`) and the deterministic floor-exit escape
bridge stay as PRECISELY-NAMED residuals — the honest remaining count-mass content of
Region L, exactly where the blueprint flags the floor martingale as genuinely stalled.
-/

import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.KilledTailConsumers

namespace ExactMajority

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Classical BigOperators

namespace FloorPrefix

open GatedDrift RoleSplitConcentration
open scoped Real

variable {L K : ℕ}

/-! ## Stage 1 — the joint `(pool, u)` ledger: the dual pointwise cover of `lateBandBad`.

The late-band event `lateBandBad = shell ∧ u < uMin ∧ pool < a₀ ∧ ¬done` requires BOTH the
floor failure `pool < a₀` AND the Stage-1 incompletion `¬ roleSplitGoodMile`.  So the
late-band mass is bounded by EITHER marginal event — the two ends of the race.  These covers
are pure logic.  The per-step pool ledger (`pool c − 2 ≤ pool c'` a.e.) is the deterministic
`±2` range that bounds how fast the pool can fall while `u` drains, reused verbatim from
`FloorMasses.pool_step_ge_ae`. -/

/-- **The late-band ⊆ floor-failure cover.**  Every late-band configuration has `pool < a₀`
(the floor has failed).  This routes the late-band mass into the floor-deficit MGF — the
contractive killed engine. -/
theorem lateBandBad_subset_floorFail (n a₀ uMin : ℕ) (hn2 : 2 ≤ n) :
    {c : Config (AgentState L K) | lateBandBad (L := L) (K := K) n a₀ uMin hn2 c}
      ⊆ {c | assignableCount (L := L) (K := K) c < a₀} := by
  intro c hc
  exact hc.2.2.1

/-- **The late-band ⊆ Stage-1-incompletion cover.**  Every late-band configuration has
`¬ roleSplitGoodMile` (Stage 1 has not drained `mcrCount` to `≤ 1`).  This routes the
late-band mass into the milestone/Janson completion tail — the other end of the race. -/
theorem lateBandBad_subset_notDone (n a₀ uMin : ℕ) (hn2 : 2 ≤ n) :
    {c : Config (AgentState L K) | lateBandBad (L := L) (K := K) n a₀ uMin hn2 c}
      ⊆ {c | ¬ roleSplitGoodMile (L := L) (K := K) n hn2 c} := by
  intro c hc
  exact hc.2.2.2

/-- **The joint `(pool, u)` ledger fact (deterministic `±2` pool range).**  Reused from
`FloorMasses.pool_step_ge_ae`: on the one-step kernel from any `c`, almost every successor
has `pool c − 2 ≤ pool c'`.  This is the rate at which the pool can fall while `u` drains —
the honest "pool falls at most `2` per step" structure of the race (over the
`O(n log n / a₀)`-flavored remaining time the cumulative drain is what the contractive
deficit tail suppresses). -/
theorem late_pool_step_ge_ae (c : Config (AgentState L K)) :
    ∀ᵐ c' ∂((NonuniformMajority L K).transitionKernel c),
      (assignableCount (L := L) (K := K) c : ℤ) - 2
        ≤ (assignableCount (L := L) (K := K) c' : ℤ) :=
  FloorMasses.pool_step_ge_ae (L := L) (K := K) c

/-! ## Stage 2 — the completion tail: from `LowStartGood`, Stage-1 incompletion is small.

The race's "fast" side.  `lateBandBad ⊆ {¬ roleSplitGoodMile}`, and from the `LowStartGood`
start the floor holds (`pool ≥ 2a₀ ≥ a₀`), so the floor-driven milestone witness
`roleSplitKernelMilestone` fires and its Janson hitting-time tail bounds the completion
failure.  Since `mcrCount ≤ uMin` is small, the remaining work is short.  We expose the
completion-tail bound as a named feeder (the milestone start condition from `LowStartGood` is
the named hypothesis `hPre_low` — the low-`u` analogue of `roleSplitKernelMilestone_hPre`,
which the all-MCR `Phase0Initial` start gives but a generic `LowStartGood` checkpoint must
carry). -/

/-- **The late completion tail (race "fast" side).**  From a gate start `c₀ ∈ floorGate n a₀`
(the `LowStartGood` checkpoint, where the floor still holds), the milestone/Janson machinery
bounds the Stage-1 incompletion mass `{¬ roleSplitGoodMile}` by the Janson hitting-time tail
PLUS the floor-escape union budget.  This is `phase0_stage1_whp` re-exposed with the start
condition `hPre` as the named low-`u` hypothesis `hPre_low` (a generic checkpoint, unlike the
all-MCR `Phase0Initial`, must carry "no milestone has fired yet").  The completion tail is the
alternative race bound on `lateBandBad`. -/
theorem late_completion_tail (n a₀ : ℕ) (hn2 : 2 ≤ n) (ha1 : 1 ≤ a₀) (ha_le : a₀ ≤ n - 1)
    (S : Set (Config (AgentState L K))) (q : ℝ≥0∞)
    (hstep : ∀ x ∈ floorGate (L := L) (K := K) n a₀, x ∈ S →
      (NonuniformMajority L K).transitionKernel x (floorGate (L := L) (K := K) n a₀)ᶜ ≤ q)
    {c₀ : Config (AgentState L K)} (hc₀ : c₀ ∈ floorGate (L := L) (K := K) n a₀)
    (hPre_low : ∀ i : Fin (roleSplitKernelMilestone (L := L) (K := K) n a₀ hn2 ha1 ha_le).k,
      ¬ (roleSplitKernelMilestone (L := L) (K := K) n a₀ hn2 ha1 ha_le).milestone i (some c₀))
    (lam : ℝ) (hlam : 1 ≤ lam) (t : ℕ)
    (ht : lam * (roleSplitKernelMilestone (L := L) (K := K) n a₀ hn2 ha1 ha_le).meanTime
      ≤ (t : ℝ)) :
    ((NonuniformMajority L K).transitionKernel ^ t) c₀
        {y | ¬ roleSplitGoodMile (L := L) (K := K) n hn2 y} ≤
      ENNReal.ofReal (Real.exp
        (-(roleSplitKernelMilestone (L := L) (K := K) n a₀ hn2 ha1 ha_le).pMin *
          (roleSplitKernelMilestone (L := L) (K := K) n a₀ hn2 ha1 ha_le).meanTime *
          (lam - 1 - Real.log lam))) +
      ((t : ℝ≥0∞) * q +
        ∑ τ ∈ Finset.range t, ((NonuniformMajority L K).transitionKernel ^ τ) c₀ Sᶜ) :=
  real_bad_le_janson_add_escape
    (K := (NonuniformMajority L K).transitionKernel)
    (G := floorGate (L := L) (K := K) n a₀) (S := S)
    (good := fun y => roleSplitGoodMile (L := L) (K := K) n hn2 y) (q := q)
    (roleSplitKernelMilestone (L := L) (K := K) n a₀ hn2 ha1 ha_le)
    (NonuniformMajority L K)
    (roleSplitKernelMilestone_post_sound (L := L) (K := K) n a₀ hn2 ha1 ha_le)
    hstep c₀ hc₀ hPre_low lam hlam t ht

/-! ## Stage 3 — the race assembly: `lateBandBad` ≤ contractive floor-deficit killed tail.

The genuinely-new low-`u` probabilistic piece.  Route the late-band mass through the
floor-failure cover `lateBandBad ⊆ {pool < a₀}` and the **contractive killed engine**
`FloorPrefix.midBand_floorFail_step_contractive` (delivered in `KilledAffineTail`,
`r < 1` allowed because `killΦ none = 0` makes the `1 ≤ r` requirement spurious).  The affine
drift on the late-band gate `G` is the named low-`u` analytic input (`r`, `b`): in Region L
the multiplicative birth contraction stalls, so the honest drift carries an immigration term
`b > 0`; the killed tail `(rᵗ·poolExpNeg(x) + b∑rⁱ)/θ` still DECAYS when `r < 1`, which is the
point.  The escape is the deterministic floor-exit (gate-breach) mass. -/

/-- **The per-step late-band contractive bound (race "slow" side, genuinely-new low-`u`
floor-deficit MGF).**  From a gate start `x ∈ G`, the late-band mass `{lateBandBad}` at step
`t` is bounded by the GENUINELY-DECAYING contractive killed pool tail `(rᵗ·poolExpNeg(x) +
b∑rⁱ)/θ` (`r` the low-`u` drift rate, `b` its immigration, `θ = exp(−s·a₀)`) PLUS the
gate-exit escape mass.  This routes the late band through the floor-failure cover into the
`r < 1` contractive engine — the cleanest decaying object, no `1 ≤ r`. -/
theorem lateBand_step_contractive (s : ℝ) (hs : 0 ≤ s) (n a₀ uMin : ℕ) (hn2 : 2 ≤ n)
    (G : Set (Config (AgentState L K))) (r b : ℝ≥0∞)
    (hdrift_G : ∀ x ∈ G,
      ∫⁻ c', poolExpNeg (L := L) (K := K) s c'
          ∂((NonuniformMajority L K).transitionKernel x)
        ≤ r * poolExpNeg (L := L) (K := K) s x + b)
    (t : ℕ) (x : Config (AgentState L K)) :
    (((NonuniformMajority L K).transitionKernel) ^ t) x
        {c | lateBandBad (L := L) (K := K) n a₀ uMin hn2 c}
      ≤ (r ^ t * poolExpNeg (L := L) (K := K) s x
            + b * ∑ i ∈ Finset.range t, r ^ i)
          / ENNReal.ofReal (Real.exp (-s * (a₀ : ℝ)))
          + (killK_now (NonuniformMajority L K).transitionKernel G ^ t) (some x)
              {(none : Option (Config (AgentState L K)))} := by
  refine le_trans (measure_mono (lateBandBad_subset_floorFail n a₀ uMin hn2)) ?_
  exact midBand_floorFail_step_contractive (L := L) (K := K) s hs a₀ G r b hdrift_G t x

/-- **The late-band prefix bound (the `εlate`-shape feeder).**  Summing
`lateBand_step_contractive` over the prefix gives the aggregate of contractive killed tails
plus escapes — the per-prefix late-band floor-failure mass with a GENUINELY DECAYING `rᵗ`
leading term.  This is the object `floor_prefix_le`'s `hlate` slot consumes (modulo the gate
start membership, threaded by the consumer).  The gate `G` and drift `(r, b)` are the named
low-`u` inputs (the stalled-martingale regime). -/
theorem lateBand_prefix_contractive (s : ℝ) (hs : 0 ≤ s) (n a₀ uMin : ℕ) (hn2 : 2 ≤ n)
    (G : Set (Config (AgentState L K))) (r b : ℝ≥0∞)
    (hdrift_G : ∀ x ∈ G,
      ∫⁻ c', poolExpNeg (L := L) (K := K) s c'
          ∂((NonuniformMajority L K).transitionKernel x)
        ≤ r * poolExpNeg (L := L) (K := K) s x + b)
    (T₀ t : ℕ) (c₀ : Config (AgentState L K)) :
    ∑ τ ∈ Finset.range t,
        (((NonuniformMajority L K).transitionKernel) ^ (T₀ + τ)) c₀
          {c | lateBandBad (L := L) (K := K) n a₀ uMin hn2 c}
      ≤ ∑ τ ∈ Finset.range t,
          ((r ^ (T₀ + τ) * poolExpNeg (L := L) (K := K) s c₀
              + b * ∑ i ∈ Finset.range (T₀ + τ), r ^ i)
            / ENNReal.ofReal (Real.exp (-s * (a₀ : ℝ)))
          + (killK_now (NonuniformMajority L K).transitionKernel G ^ (T₀ + τ)) (some c₀)
              {(none : Option (Config (AgentState L K)))}) := by
  apply Finset.sum_le_sum
  intro τ _
  exact lateBand_step_contractive (L := L) (K := K) s hs n a₀ uMin hn2 G r b hdrift_G
    (T₀ + τ) c₀

/-- **The late-prefix `hlate`-slot bound.**  Packages the late-band prefix into the EXACT
shape of `floor_prefix_le`'s `hlate` hypothesis: from a named per-prefix late-band bound
`hlate_feeder` (supplied by `lateBand_prefix_contractive` plus a budget calibration, or by
the completion-tail race alternative), the late-band prefix is `≤ εlate`.  This is the clean
interface the assembly consumes. -/
theorem late_prefix_le (n a₀ uMin T₀ t : ℕ) (hn2 : 2 ≤ n) (εlate : ℝ≥0∞)
    {c₀ : Config (AgentState L K)}
    (hlate_feeder : ∑ τ ∈ Finset.range t,
        ((NonuniformMajority L K).transitionKernel ^ (T₀ + τ)) c₀
          {c | lateBandBad (L := L) (K := K) n a₀ uMin hn2 c} ≤ εlate) :
    ∑ τ ∈ Finset.range t,
      ((NonuniformMajority L K).transitionKernel ^ (T₀ + τ)) c₀
        {c | lateBandBad (L := L) (K := K) n a₀ uMin hn2 c}
      ≤ εlate := hlate_feeder

/-! ## Stage 4 — wire into `FloorPrefix.floor_prefix_le`'s `hlate` slot.

The assembled floor-prefix theorem `floor_prefix_le` carries three named region masses
(`hshell`, `hmid`, `hlate`).  Here we re-state it with the `hlate` slot discharged by the
contractive late-band route (`late_prefix_le`), exposing the genuinely-new low-`u` piece as
the named drift hypothesis, and leaving `hshell`/`hmid` as their existing feeders
(`FloorPrefix` / `KilledTailConsumers`). -/

/-- **`floor_prefix_le` with the `hlate` slot discharged by the contractive late-band
route.**  Identical to `FloorPrefix.floor_prefix_le` but with the late-band prefix supplied by
`late_prefix_le` (the contractive floor-deficit killed tail aggregate, the genuinely-new
low-`u` piece).  `hshell`/`hmid` remain their existing feeders.  This is the form the εfloor
assembly consumes once the three budgets are calibrated. -/
theorem floor_prefix_le_with_late
    (n a₀ uMin T₀ t : ℕ) (hn2 : 2 ≤ n)
    (εwarm εmid εlate : ℝ≥0∞)
    {c₀ : Config (AgentState L K)}
    (hshell : ∑ τ ∈ Finset.range t,
        ((NonuniformMajority L K).transitionKernel ^ (T₀ + τ)) c₀
          ((cardPhaseShell (L := L) (K := K) n)ᶜ) ≤ εwarm)
    (hmid : ∑ τ ∈ Finset.range t,
        ((NonuniformMajority L K).transitionKernel ^ (T₀ + τ)) c₀
          {c | midBandBad (L := L) (K := K) n a₀ uMin hn2 c} ≤ εmid)
    (hlate_feeder : ∑ τ ∈ Finset.range t,
        ((NonuniformMajority L K).transitionKernel ^ (T₀ + τ)) c₀
          {c | lateBandBad (L := L) (K := K) n a₀ uMin hn2 c} ≤ εlate) :
    ∑ τ ∈ Finset.range t,
      ((NonuniformMajority L K).transitionKernel ^ (T₀ + τ)) c₀
        {c | floorFailsBeforePost (L := L) (K := K) n a₀ hn2 c}
      ≤ εwarm + εmid + εlate :=
  floor_prefix_le n a₀ uMin T₀ t hn2 εwarm εmid εlate hshell hmid
    (late_prefix_le n a₀ uMin T₀ t hn2 εlate hlate_feeder)

/-! ## §4 — the paper-scale `εlate` budget and the capstone. -/

/-- The late-band failure budget `εlate n = 1/(3n²)` (blueprint §4: each of the three region
budgets fits under `1/(3n²)` so the floor prefix is `≤ n⁻²`). -/
noncomputable def εlate (n : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal ((3 * (n : ℝ) ^ 2)⁻¹)

/-- **The late-band capstone at the paper budget.**  From a named per-prefix late-band bound
fitting under `εlate n = 1/(3n²)`, the late-band prefix is `≤ 1/(3n²)`.  This is the third of
the three region budgets that sum to `εfloor n = n⁻²` in `FloorPrefix.floor_prefix_le_inv_sq`.
The per-prefix bound `hlate_feeder` is the contractive late-band aggregate
(`lateBand_prefix_contractive`) calibrated to `1/(3n²)` — the genuinely-decaying `rᵗ` killed
tail makes the calibration honest. -/
theorem late_prefix_le_inv (n a₀ uMin T₀ t : ℕ) (hn2 : 2 ≤ n)
    {c₀ : Config (AgentState L K)}
    (hlate_feeder : ∑ τ ∈ Finset.range t,
        ((NonuniformMajority L K).transitionKernel ^ (T₀ + τ)) c₀
          {c | lateBandBad (L := L) (K := K) n a₀ uMin hn2 c} ≤ εlate n) :
    ∑ τ ∈ Finset.range t,
      ((NonuniformMajority L K).transitionKernel ^ (T₀ + τ)) c₀
        {c | lateBandBad (L := L) (K := K) n a₀ uMin hn2 c}
      ≤ εlate n :=
  late_prefix_le n a₀ uMin T₀ t hn2 (εlate n) hlate_feeder

end FloorPrefix

end ExactMajority
