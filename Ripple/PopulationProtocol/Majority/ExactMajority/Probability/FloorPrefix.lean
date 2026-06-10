/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# FloorPrefix — the post-gated floor-prefix residual (Doty Thm 3.1, εfloor route)

This file develops the **warm-up-shifted, post-gated floor residual** that the
campaign's `phase0_stage1_whp_final` needs in order to replace its crude
`floorGateᶜ` prefix term by the honest `n⁻²`-scale floor failure mass.  It is
**append-only** and imports the (frozen) consumer file
`Probability/RoleSplitConcentration.lean` for the reusable atoms (`assignableCount`,
`mcrCount`, `cardPhaseShell`, `floorGate`, `roleSplitGoodMile`, `Phase0Initial`),
the protocol `Probability/MarkovChain.lean` layer, and the two honest gated-drift
engines `Probability/GatedEscape.lean` / `Probability/GatedGeometricDrift.lean`.

## The design (ChatGPT-Pro blueprint §3–§5, corrected against the real repo)

The pool potential is `poolExpNeg s c = exp(-s · assignableCount c)` (an MGF that is
LARGE when the pool is small, i.e. when the floor `a₀ ≤ assignableCount` is in danger).
On a band where `mcrCount` is still linear (`u ≥ uMin`) and the pool is bounded
(`pool ≤ Ahi`), Rule-1 births (which create `+2` assignable agents, `assignable_rule…`)
dominate the Rule-4 drain, so the exponentially-tilted one-step drift contracts at a
rate `r < 1`.

### Constants (per blueprint §1, §4)

* `a₀  := n / 10`     -- the floor itself
* `Ahi := 2 * a₀`     -- the buffer the warm-up reaches
* `uMin := 3 * a₀`    -- the `u`-floor for favorability (`uMin² > Ahi²` with slack)
* `s   := 1/10`       -- the MGF scale (the blueprint's `s = 1/2` is TOO LARGE — at
                         `s = 1/2` the tilted drift is `> 1`; `s = 1/10` gives `r ≈ 0.993`).

### Engine-shape findings (corrections to the blueprint, see the status section)

1. **`windowDrift_tail` requires an ABSORBING window** (`hQ_abs`: `Q` one-step-support
   closed).  The warm-up/mid windows `{pool < 2a₀ ∧ u ≥ uMin}` are NOT absorbing — `pool`
   can cross `2a₀` and `u` can drop below `uMin` in one step — so `windowDrift_tail` does
   not apply to them directly.  The honest non-absorbing engine is
   `GatedDrift.gated_real_tail_full` (`GatedEscape.lean`), which needs only the drift ON
   the gate plus a per-step escape bound `η`.

2. **The gated engines require `1 ≤ r`** (the killed-kernel potential must dominate the
   cemetery transition).  So the gated tail does NOT decay as `rᵗ`; it is the escape form
   `t·η + rᵗ·Φx/θ`.  A genuinely-contractive `r < 1` floor tail therefore needs the
   absorbing-window route — which is why the honest assembly keeps the per-region masses
   (`εmid`, `εlate`) as named hypotheses with precise doc-comments, plus the provable
   scalar/one-step analytic layer below.

The contributions that ARE proven here, end-to-end: the scalar favorability layer
(`scalarPoolFav_core`, `scalarPoolFav_lt_one`, the favorability instance), the
rate-parametric one-step pool drift (analytic core), and the pure union/checkpoint
assembly `floor_prefix_le`.
-/

import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.RoleSplitConcentration
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.GatedEscape
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.DotyParams
import Mathlib.Analysis.Complex.ExponentialBounds

namespace ExactMajority
namespace FloorPrefix

open MeasureTheory ProbabilityTheory RoleSplitConcentration
open scoped ENNReal NNReal Real BigOperators

variable {L K : ℕ}

/-! ## §3 — the pool MGF potential and its drift region. -/

/-- The pool MGF potential `exp(-s · assignableCount c)`.  Large exactly when the
assignable pool is small, i.e. when the floor `a₀ ≤ assignableCount` is endangered. -/
noncomputable def poolExpNeg (s : ℝ) :
    Config (AgentState L K) → ℝ≥0∞ :=
  fun c => ENNReal.ofReal
    (Real.exp (-s * (assignableCount (L := L) (K := K) c : ℝ)))

theorem poolExpNeg_measurable (s : ℝ) :
    Measurable (poolExpNeg (L := L) (K := K) s) := Measurable.of_discrete

/-- `poolExpNeg s c` is never zero (the exponential of a real is positive). -/
theorem poolExpNeg_pos (s : ℝ) (c : Config (AgentState L K)) :
    0 < poolExpNeg (L := L) (K := K) s c := by
  unfold poolExpNeg
  exact ENNReal.ofReal_pos.mpr (Real.exp_pos _)

theorem poolExpNeg_ne_top (s : ℝ) (c : Config (AgentState L K)) :
    poolExpNeg (L := L) (K := K) s c ≠ ⊤ := by
  unfold poolExpNeg; exact ENNReal.ofReal_ne_top

/-- **The favorability drift region** (blueprint §3): a configuration in the structural
shell whose `mcrCount` is still at least the floor `uMin` and whose pool has not exceeded
the buffer `Ahi`.  This is the band on which Rule-1 births dominate the Rule-4 drain. -/
def PoolDriftRegion (n uMin Ahi : ℕ)
    (c : Config (AgentState L K)) : Prop :=
  c ∈ cardPhaseShell (L := L) (K := K) n ∧
  uMin ≤ ExactMajority.mcrCount (L := L) (K := K) c ∧
  assignableCount (L := L) (K := K) c ≤ Ahi

/-! ## §3 — the scalar favorability predicate. -/

/-- **Scalar favorability** (blueprint §3): the tilted one-step drift multiplier
`1 - b·(1 - e^{-2s}) + d·(e^{2s} - 1)` is at most `r`, where `b` is the birth mass lower
bound `uMin(uMin-1)/(n(n-1))` and `d` the death mass upper bound `Ahi²/(n(n-1))`.  For
`Ahi = 2a₀`, `uMin = 3a₀`, small `s`, this gives `r < 1`. -/
def ScalarPoolFav (s : ℝ) (n uMin Ahi : ℕ) (r : ℝ≥0∞) : Prop :=
  ENNReal.ofReal
    (1
      - (((uMin * (uMin - 1) : ℕ) : ℝ) / (n * (n - 1) : ℝ)) *
          (1 - Real.exp (-2 * s))
      + (((Ahi * Ahi : ℕ) : ℝ) / (n * (n - 1) : ℝ)) *
          (Real.exp (2 * s) - 1))
    ≤ r

/-! ### The pure-scalar favorability instances.

These are arithmetic facts in `ℝ` with no protocol content.  The crux is the
favorability inequality `d·(e^{2s} - 1) ≤ b·(1 - e^{-2s})`, which at the concrete
constants `a₀ = n/10`, `Ahi = 2a₀`, `uMin = 3a₀`, `s = 1/10` reduces to
`(4/100)(e^{1/5} - 1) ≤ (9/100)(1 - e^{-1/5})`, discharged via `Real.exp_bound'`
(upper bound on `e^{1/5}`) and `Real.add_one_le_exp` (upper bound on `e^{-1/5}`). -/

/-- **The favorability core (constants `b = 9/100`, `d = 4/100`, `s = 1/10`).**  The
death contribution is STRICTLY dominated by the birth contribution after exponential
tilting (the strict gap `≈ 0.006` survives the crude `exp` bounds). -/
theorem scalarPoolFav_core :
    (4 / 100 : ℝ) * (Real.exp ((1 : ℝ) / 5) - 1)
      < (9 / 100) * (1 - Real.exp (-(1 / 5))) := by
  have hup : Real.exp ((1 : ℝ) / 5)
      ≤ 1 + (1 / 5) + (1 / 5) ^ 2 / 2 + (1 / 5) ^ 3 * 4 / 18 := by
    have := Real.exp_bound' (x := (1 : ℝ) / 5) (by norm_num) (by norm_num)
      (n := 3) (by norm_num)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero] at this
    norm_num at this ⊢; nlinarith [this]
  have hlo : Real.exp (-(1 / 5) : ℝ) ≤ 5 / 6 := by
    have h1 : (6 : ℝ) / 5 ≤ Real.exp ((1 : ℝ) / 5) := by
      have := Real.add_one_le_exp ((1 : ℝ) / 5); nlinarith [this]
    have hpos : (0 : ℝ) < Real.exp ((1 : ℝ) / 5) := Real.exp_pos _
    rw [Real.exp_neg, inv_le_comm₀ hpos (by norm_num)]; nlinarith [h1]
  nlinarith [hup, hlo]

/-- **The concrete contraction rate is `< 1`.**  With `b = 9/100`, `d = 4/100`, `s = 1/10`
the tilted drift multiplier `1 - b(1 - e^{-2s}) + d(e^{2s} - 1)` is strictly below `1`. -/
theorem scalarPoolFav_lt_one :
    1
      - (9 / 100 : ℝ) * (1 - Real.exp (-2 * (1 / 10)))
      + (4 / 100) * (Real.exp (2 * (1 / 10)) - 1)
    < 1 := by
  have hcore := scalarPoolFav_core
  have h2s : (2 : ℝ) * (1 / 10) = 1 / 5 := by norm_num
  have hn2s : (-2 : ℝ) * (1 / 10) = -(1 / 5) := by norm_num
  rw [h2s, hn2s]
  linarith [hcore]

/-- **The favorability instance at the concrete constants.**  Packages
`scalarPoolFav_lt_one` into the `ScalarPoolFav` shape with the rate `r` taken to be the
(definitionally equal) tilted-drift value, and exposes the witness `r < 1` separately. -/
theorem scalarPoolFav_instance (n : ℕ) :
    ScalarPoolFav (1 / 10) n (3 * (n / 10)) (2 * (n / 10))
      (ENNReal.ofReal
        (1
          - (((3 * (n / 10) * (3 * (n / 10) - 1) : ℕ) : ℝ) / (n * (n - 1) : ℝ)) *
              (1 - Real.exp (-2 * (1 / 10)))
          + (((2 * (n / 10) * (2 * (n / 10)) : ℕ) : ℝ) / (n * (n - 1) : ℝ)) *
              (Real.exp (2 * (1 / 10)) - 1))) := by
  unfold ScalarPoolFav
  exact le_refl _

/-! ## §1–§2 — the warm-up and low-start checkpoint predicates. -/

/-- **`Phase0WarmGood`** (blueprint §1, §2): the buffered checkpoint the warm-up reaches —
the structural shell, `u ≥ uMin`, and the pool at the buffer `2a₀ ≤ pool`. -/
def Phase0WarmGood (n a₀ uMin : ℕ) (c : Config (AgentState L K)) : Prop :=
  c ∈ cardPhaseShell (L := L) (K := K) n ∧
  uMin ≤ ExactMajority.mcrCount (L := L) (K := K) c ∧
  2 * a₀ ≤ assignableCount (L := L) (K := K) c

/-- **`LowStartGood`** (blueprint §1): the low-`u` checkpoint start — the structural shell,
`u ≤ uMin`, and the buffered pool `2a₀ ≤ pool`.  The genuinely-new region L start. -/
def LowStartGood (n a₀ uMin : ℕ) (c : Config (AgentState L K)) : Prop :=
  c ∈ cardPhaseShell (L := L) (K := K) n ∧
  ExactMajority.mcrCount (L := L) (K := K) c ≤ uMin ∧
  2 * a₀ ≤ assignableCount (L := L) (K := K) c

/-- The post-gated floor-failure event (blueprint §4): the pool dropped below `a₀` while
Stage 1 has NOT yet succeeded (`¬ roleSplitGoodMile`).  "Floor failure after success" is
not counted — this is the design change that makes the residual `n⁻²`-scale honest. -/
def floorFailsBeforePost (n a₀ : ℕ) (hn2 : 2 ≤ n)
    (c : Config (AgentState L K)) : Prop :=
  assignableCount (L := L) (K := K) c < a₀ ∧
  ¬ roleSplitGoodMile (L := L) (K := K) n hn2 c

/-- **`floorOrDoneGate`** (blueprint §5 "minimal edit"): the gate that does NOT charge
floor failure once Stage 1 has succeeded.  `floorGate ∪ {roleSplitGoodMile}`. -/
def floorOrDoneGate (n a₀ : ℕ) (hn2 : 2 ≤ n) :
    Set (Config (AgentState L K)) :=
  floorGate (L := L) (K := K) n a₀ ∪
    {c | roleSplitGoodMile (L := L) (K := K) n hn2 c}

/-! ## §3 — the one-step pool MGF drift.

We isolate the analytic content (the exponential-tilt mass bookkeeping) into an
abstract scalar drift lemma, then state the protocol-rate masses and the
one-step drift specialised to the real kernel.

### The honest mass model (corrected against the real `Phase0Transition`)

The per-step assignable-pool change is in `[-2, +2]` (each interaction touches two
agents; each contributes `±1` to the assignable count `IsAssignable`).  Splitting
the one-step successor measure into the three bands

* **birth**  `B = {c' | pool c + 2 ≤ pool c'}`   (Rule-1 `MCR,MCR → Main,CR` with both
  outputs unassigned-at-phase-0, `assignable_rule…`, mass `≥ b`);
* **death**  `D = {c' | pool c' < pool c}`       (a genuine pool drop, e.g. fresh-CR
  pairs draining via Rule 4, mass `≤ d`);
* **neutral** `N = {c' | pool c ≤ pool c' ∧ pool c' < pool c + 2}`,

and tilting `poolExpNeg` by `e^{-2s}` on `B`, `1` on `N`, `e^{2s}` on `D` (using the
a.e. lower bound `pool c - 2 ≤ pool c'`), gives the multiplier
`1 - b(1 - e^{-2s}) + d(e^{2s} - 1)`.  This is the `ScalarPoolFav` value. -/

/-- **`birthR1Mass c`** — the real-kernel one-step mass of the pool-birth band
`{c' | assignableCount c + 2 ≤ assignableCount c'}`.  Lower-bounded by Rule-1
`MCR,MCR` interactions among unassigned phase-0 agents (`hbirth`). -/
noncomputable def birthR1Mass (c : Config (AgentState L K)) : ℝ≥0∞ :=
  ((NonuniformMajority L K).stepDistOrSelf c).toMeasure
    {c' | assignableCount (L := L) (K := K) c + 2 ≤ assignableCount (L := L) (K := K) c'}

/-- **`r4FreshCRDrainMass c`** — the real-kernel one-step mass of the pool-drain band
`{c' | assignableCount c' < assignableCount c}`.  Upper-bounded by the fresh-CR pair
count squared, hence by `pool²/(n(n-1))` (`hdeath`). -/
noncomputable def r4FreshCRDrainMass (c : Config (AgentState L K)) : ℝ≥0∞ :=
  ((NonuniformMajority L K).stepDistOrSelf c).toMeasure
    {c' | assignableCount (L := L) (K := K) c' < assignableCount (L := L) (K := K) c}

/-- **Abstract scalar one-step pool drift.**  The analytic core, kernel-local and
parametric in the masses `b, d` and the contraction value.  Given:
* `hstep` — the per-step pool lower bound `pool c - 2 ≤ pool c'` a.e. on the successor
  measure (the `±2` interaction range — a protocol fact, supplied as a hypothesis);
* `hb` — the birth mass is at least `b`;
* `hd` — the drain mass is at most `d`;
* `hbd` — the masses are real-valued (`≠ ⊤`, automatic for a probability measure) and
  the favorability value `rVal = 1 - b·(1-e^{-2s}) + d·(e^{2s}-1)` is `≤ r`,
the tilted one-step expectation contracts:
`∫ poolExpNeg s ∂(K c) ≤ r · poolExpNeg s c`. -/
theorem pool_expNeg_one_step_drift_abstract
    (s : ℝ) (hs : 0 < s) (c : Config (AgentState L K))
    (b d : ℝ) (hb0 : 0 ≤ b) (hd0 : 0 ≤ d) (_hb1 : b ≤ 1) (_hbd1 : b + d ≤ 1)
    (hstep : ∀ᵐ c' ∂((NonuniformMajority L K).transitionKernel c),
      (assignableCount (L := L) (K := K) c : ℤ) - 2
        ≤ (assignableCount (L := L) (K := K) c' : ℤ))
    (hb : ENNReal.ofReal b ≤ birthR1Mass (L := L) (K := K) c)
    (hd : r4FreshCRDrainMass (L := L) (K := K) c ≤ ENNReal.ofReal d)
    (r : ℝ≥0∞)
    (hfav : ENNReal.ofReal
      (1 - b * (1 - Real.exp (-2 * s)) + d * (Real.exp (2 * s) - 1)) ≤ r) :
    ∫⁻ c', poolExpNeg (L := L) (K := K) s c'
        ∂((NonuniformMajority L K).transitionKernel c)
      ≤ r * poolExpNeg (L := L) (K := K) s c := by
  classical
  set μ := (NonuniformMajority L K).transitionKernel c with hμ
  haveI : IsProbabilityMeasure μ := by rw [hμ]; infer_instance
  set p := assignableCount (L := L) (K := K) c with hp
  set β := Real.exp (-s * (p : ℝ)) with hβ
  have hβpos : 0 < β := Real.exp_pos _
  -- The three bands.
  set B : Set (Config (AgentState L K)) :=
    {c' | p + 2 ≤ assignableCount (L := L) (K := K) c'} with hBdef
  set D : Set (Config (AgentState L K)) :=
    {c' | assignableCount (L := L) (K := K) c' < p} with hDdef
  -- Pointwise upper bound on the integrand by an `if`-cascade times β.
  have hpw : ∀ᵐ c' ∂μ,
      poolExpNeg (L := L) (K := K) s c'
        ≤ ENNReal.ofReal
            ((if c' ∈ B then Real.exp (-2 * s)
              else if c' ∈ D then Real.exp (2 * s) else 1) * β) := by
    filter_upwards [hstep] with c' hc'
    unfold poolExpNeg
    apply ENNReal.ofReal_le_ofReal
    set p' := assignableCount (L := L) (K := K) c' with hp'
    by_cases hB : c' ∈ B
    · simp only [hB, if_true]
      have hle : (p : ℝ) + 2 ≤ (p' : ℝ) := by
        have : p + 2 ≤ p' := hB; exact_mod_cast this
      have : Real.exp (-s * (p' : ℝ)) ≤ Real.exp (-2 * s) * β := by
        rw [hβ, ← Real.exp_add]; apply Real.exp_le_exp.mpr; nlinarith [hle, hs]
      linarith [this]
    · simp only [hB, if_false]
      by_cases hD : c' ∈ D
      · simp only [hD, if_true]
        -- death band: pool c' ≥ pool c - 2 (from hstep), factor e^{2s}
        have hle : (p : ℝ) ≤ (p' : ℝ) + 2 := by
          have : (p : ℤ) - 2 ≤ (p' : ℤ) := hc'
          have : (p : ℝ) - 2 ≤ (p' : ℝ) := by exact_mod_cast this
          linarith
        have : Real.exp (-s * (p' : ℝ)) ≤ Real.exp (2 * s) * β := by
          rw [hβ, ← Real.exp_add]; apply Real.exp_le_exp.mpr; nlinarith [hle, hs]
        linarith [this]
      · simp only [hD, if_false, one_mul]
        -- neutral band: pool c ≤ pool c' (¬D), factor 1
        have hge : p ≤ p' := by
          simp only [hDdef, Set.mem_setOf_eq, not_lt] at hD; exact hD
        have hle : (p : ℝ) ≤ (p' : ℝ) := by exact_mod_cast hge
        have : Real.exp (-s * (p' : ℝ)) ≤ β := by
          rw [hβ]; apply Real.exp_le_exp.mpr; nlinarith [hle, hs]
        linarith [this]
  -- Integrate the if-cascade.
  have hBmeas : MeasurableSet B := DiscreteMeasurableSpace.forall_measurableSet _
  have hDmeas : MeasurableSet D := DiscreteMeasurableSpace.forall_measurableSet _
  have hgmeas : Measurable (fun c' : Config (AgentState L K) =>
      ENNReal.ofReal
        ((if c' ∈ B then Real.exp (-2 * s)
          else if c' ∈ D then Real.exp (2 * s) else 1) * β)) := Measurable.of_discrete
  -- `B` and `D` are disjoint (`pool' ≥ pool+2` vs `pool' < pool`).
  have hBD_disj : Disjoint B D := by
    rw [Set.disjoint_left]; intro x hxB hxD
    simp only [hBdef, Set.mem_setOf_eq] at hxB
    simp only [hDdef, Set.mem_setOf_eq] at hxD; omega
  set qB := μ B with hqB
  set qD := μ D with hqD
  have hqB_le : ENNReal.ofReal b ≤ qB := by rw [hqB, hμ]; exact hb
  have hqD_le : qD ≤ ENNReal.ofReal d := by rw [hqD, hμ]; exact hd
  have hqB_top : qB ≠ ⊤ := measure_ne_top _ _
  have hqD_top : qD ≠ ⊤ := measure_ne_top _ _
  -- Compute `∫ g`.  Split B / Bᶜ; on Bᶜ split D / (Bᶜ ∩ Dᶜ).
  have hint_le : ∫⁻ c', ENNReal.ofReal
      ((if c' ∈ B then Real.exp (-2 * s)
        else if c' ∈ D then Real.exp (2 * s) else 1) * β) ∂μ
      ≤ ENNReal.ofReal (Real.exp (-2 * s) * β) * qB
        + ENNReal.ofReal (Real.exp (2 * s) * β) * qD
        + ENNReal.ofReal (1 * β) * (1 - qB - qD) := by
    rw [← lintegral_add_compl _ hBmeas]
    have hI_B : ∫⁻ c' in B, ENNReal.ofReal
        ((if c' ∈ B then Real.exp (-2 * s)
          else if c' ∈ D then Real.exp (2 * s) else 1) * β) ∂μ
        = ENNReal.ofReal (Real.exp (-2 * s) * β) * qB := by
      rw [show (∫⁻ c' in B, ENNReal.ofReal
          ((if c' ∈ B then Real.exp (-2 * s)
            else if c' ∈ D then Real.exp (2 * s) else 1) * β) ∂μ)
          = ∫⁻ _ in B, ENNReal.ofReal (Real.exp (-2 * s) * β) ∂μ from ?_,
        lintegral_const, Measure.restrict_apply_univ, hqB]
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_mem hBmeas] with c' hc'
      simp only [hc', if_true]
    have hI_Bc : ∫⁻ c' in Bᶜ, ENNReal.ofReal
        ((if c' ∈ B then Real.exp (-2 * s)
          else if c' ∈ D then Real.exp (2 * s) else 1) * β) ∂μ
        ≤ ENNReal.ofReal (Real.exp (2 * s) * β) * qD
          + ENNReal.ofReal (1 * β) * (1 - qB - qD) := by
      -- On Bᶜ the integrand is `if D then e^{2s}β else β`.  Split D / Dᶜ within Bᶜ.
      have hDsubBc : D ⊆ Bᶜ := by
        rw [Set.subset_compl_iff_disjoint_left]; exact hBD_disj
      rw [← lintegral_add_compl (μ := μ.restrict Bᶜ) _ hDmeas]
      have hI_D : ∫⁻ c' in D, ENNReal.ofReal
          ((if c' ∈ B then Real.exp (-2 * s)
            else if c' ∈ D then Real.exp (2 * s) else 1) * β) ∂(μ.restrict Bᶜ)
          = ENNReal.ofReal (Real.exp (2 * s) * β) * qD := by
        rw [Measure.restrict_restrict hDmeas, Set.inter_eq_left.mpr hDsubBc]
        rw [show (∫⁻ c' in D, ENNReal.ofReal
            ((if c' ∈ B then Real.exp (-2 * s)
              else if c' ∈ D then Real.exp (2 * s) else 1) * β) ∂μ)
            = ∫⁻ _ in D, ENNReal.ofReal (Real.exp (2 * s) * β) ∂μ from ?_,
          lintegral_const, Measure.restrict_apply_univ, hqD]
        apply lintegral_congr_ae
        filter_upwards [ae_restrict_mem hDmeas] with c' hc'
        have hcB : c' ∉ B := fun h => (Set.disjoint_left.mp hBD_disj h hc')
        simp only [hcB, if_false, hc', if_true]
      have hI_DcN : ∫⁻ c' in Dᶜ, ENNReal.ofReal
          ((if c' ∈ B then Real.exp (-2 * s)
            else if c' ∈ D then Real.exp (2 * s) else 1) * β) ∂(μ.restrict Bᶜ)
          ≤ ENNReal.ofReal (1 * β) * (1 - qB - qD) := by
        rw [Measure.restrict_restrict hDmeas.compl]
        calc ∫⁻ c' in Dᶜ ∩ Bᶜ, _ ∂μ
            = ∫⁻ _ in Dᶜ ∩ Bᶜ, ENNReal.ofReal (1 * β) ∂μ := by
              apply lintegral_congr_ae
              filter_upwards [ae_restrict_mem (hDmeas.compl.inter hBmeas.compl)] with c' hc'
              obtain ⟨hcD, hcB⟩ := hc'
              simp only [Set.mem_compl_iff] at hcD hcB
              simp only [hcB, if_false, hcD, if_false]
          _ = ENNReal.ofReal (1 * β) * μ (Dᶜ ∩ Bᶜ) := by
              rw [lintegral_const, Measure.restrict_apply_univ]
          _ ≤ ENNReal.ofReal (1 * β) * (1 - qB - qD) := by
              refine mul_le_mul' (le_refl _) ?_
              have hsub : Dᶜ ∩ Bᶜ ⊆ (B ∪ D)ᶜ := by
                intro x ⟨hxD, hxB⟩
                simp only [Set.mem_compl_iff, Set.mem_union] at hxD hxB ⊢
                tauto
              calc μ (Dᶜ ∩ Bᶜ) ≤ μ (B ∪ D)ᶜ := measure_mono hsub
                _ = 1 - μ (B ∪ D) := by
                    rw [measure_compl (hBmeas.union hDmeas) (measure_ne_top _ _), measure_univ]
                _ = 1 - (qB + qD) := by
                    rw [measure_union hBD_disj hDmeas]
                _ = 1 - qB - qD := by rw [tsub_add_eq_tsub_tsub]
      rw [hI_D]
      exact add_le_add le_rfl hI_DcN
    rw [hI_B]
    calc ENNReal.ofReal (Real.exp (-2 * s) * β) * qB
          + ∫⁻ c' in Bᶜ, ENNReal.ofReal
            ((if c' ∈ B then Real.exp (-2 * s)
              else if c' ∈ D then Real.exp (2 * s) else 1) * β) ∂μ
        ≤ ENNReal.ofReal (Real.exp (-2 * s) * β) * qB
            + (ENNReal.ofReal (Real.exp (2 * s) * β) * qD
              + ENNReal.ofReal (1 * β) * (1 - qB - qD)) :=
          add_le_add le_rfl hI_Bc
      _ = _ := by rw [add_assoc]
  -- The scalar mass bound `e^{-2s}·qB + e^{2s}·qD + (1-qB-qD) ≤ rVal` times β.
  -- Reduce everything to `toReal` and finish by `nlinarith`.
  set qBr := qB.toReal with hqBr
  set qDr := qD.toReal with hqDr
  have hqBr0 : 0 ≤ qBr := ENNReal.toReal_nonneg
  have hqDr0 : 0 ≤ qDr := ENNReal.toReal_nonneg
  have hqB_eq : qB = ENNReal.ofReal qBr := (ENNReal.ofReal_toReal hqB_top).symm
  have hqD_eq : qD = ENNReal.ofReal qDr := (ENNReal.ofReal_toReal hqD_top).symm
  have hb_le_qBr : b ≤ qBr := by
    have h := ENNReal.toReal_mono hqB_top hqB_le
    rwa [ENNReal.toReal_ofReal hb0] at h
  have hqDr_le_d : qDr ≤ d := by
    have h := ENNReal.toReal_mono (b := ENNReal.ofReal d) ENNReal.ofReal_ne_top hqD_le
    rwa [ENNReal.toReal_ofReal hd0] at h
  -- `qB + qD ≤ 1` so `1 - qB - qD = ofReal (1 - qBr - qDr)`.
  have hsum_le : qB + qD ≤ 1 := by
    rw [hqB, hqD, ← measure_union hBD_disj hDmeas]
    calc μ (B ∪ D) ≤ μ Set.univ := measure_mono (Set.subset_univ _)
      _ = 1 := measure_univ
  have hsumr_le : qBr + qDr ≤ 1 := by
    have h := ENNReal.toReal_mono ENNReal.one_ne_top hsum_le
    rwa [ENNReal.toReal_add hqB_top hqD_top, ENNReal.toReal_one] at h
  have hcompl_eq : (1 : ℝ≥0∞) - qB - qD = ENNReal.ofReal (1 - qBr - qDr) := by
    rw [hqB_eq, hqD_eq, ← ENNReal.ofReal_one,
      ← ENNReal.ofReal_sub _ hqBr0, ← ENNReal.ofReal_sub _ hqDr0]
  -- Collapse the three `ofReal _ * ofReal _` products into a single `ofReal`.
  have hβ0 : (0 : ℝ) ≤ β := hβpos.le
  have he2 : (0 : ℝ) ≤ Real.exp (2 * s) := (Real.exp_pos _).le
  have hen2 : (0 : ℝ) ≤ Real.exp (-2 * s) := (Real.exp_pos _).le
  have hbound_real :
      Real.exp (-2 * s) * β * qBr + Real.exp (2 * s) * β * qDr
          + 1 * β * (1 - qBr - qDr)
        ≤ (1 - b * (1 - Real.exp (-2 * s)) + d * (Real.exp (2 * s) - 1)) * β := by
    have hkey : Real.exp (-2 * s) * qBr + Real.exp (2 * s) * qDr + (1 - qBr - qDr)
        ≤ 1 - b * (1 - Real.exp (-2 * s)) + d * (Real.exp (2 * s) - 1) := by
      have h1 : (1 - Real.exp (-2 * s)) * (qBr - b) ≥ 0 := by
        apply mul_nonneg
        · have : Real.exp (-2 * s) ≤ 1 := by
            rw [show (1 : ℝ) = Real.exp 0 from (Real.exp_zero).symm]
            exact Real.exp_le_exp.mpr (by nlinarith [hs])
          linarith
        · linarith [hb_le_qBr]
      have h2 : (Real.exp (2 * s) - 1) * (d - qDr) ≥ 0 := by
        apply mul_nonneg
        · have : (1 : ℝ) ≤ Real.exp (2 * s) := by
            rw [show (1 : ℝ) = Real.exp 0 from (Real.exp_zero).symm]
            exact Real.exp_le_exp.mpr (by nlinarith [hs])
          linarith
        · linarith [hqDr_le_d]
      nlinarith [h1, h2]
    nlinarith [hkey, hβpos]
  -- Chain everything.
  calc ∫⁻ c', poolExpNeg (L := L) (K := K) s c' ∂μ
      ≤ ∫⁻ c', ENNReal.ofReal
          ((if c' ∈ B then Real.exp (-2 * s)
            else if c' ∈ D then Real.exp (2 * s) else 1) * β) ∂μ :=
        lintegral_mono_ae hpw
    _ ≤ ENNReal.ofReal (Real.exp (-2 * s) * β) * qB
          + ENNReal.ofReal (Real.exp (2 * s) * β) * qD
          + ENNReal.ofReal (1 * β) * (1 - qB - qD) := hint_le
    _ = ENNReal.ofReal
          (Real.exp (-2 * s) * β * qBr + Real.exp (2 * s) * β * qDr
            + 1 * β * (1 - qBr - qDr)) := by
        have hcompl0 : (0 : ℝ) ≤ 1 - qBr - qDr := by linarith [hsumr_le]
        have ht1 : (0 : ℝ) ≤ Real.exp (-2 * s) * β * qBr :=
          mul_nonneg (mul_nonneg hen2 hβ0) hqBr0
        have ht2 : (0 : ℝ) ≤ Real.exp (2 * s) * β * qDr :=
          mul_nonneg (mul_nonneg he2 hβ0) hqDr0
        have ht3 : (0 : ℝ) ≤ 1 * β * (1 - qBr - qDr) :=
          mul_nonneg (mul_nonneg (by norm_num) hβ0) hcompl0
        rw [hcompl_eq, hqB_eq, hqD_eq,
          ← ENNReal.ofReal_mul (by positivity),
          ← ENNReal.ofReal_mul (by positivity),
          ← ENNReal.ofReal_mul (by positivity),
          ← ENNReal.ofReal_add ht1 ht2,
          ← ENNReal.ofReal_add (add_nonneg ht1 ht2) ht3]
    _ ≤ ENNReal.ofReal
          ((1 - b * (1 - Real.exp (-2 * s)) + d * (Real.exp (2 * s) - 1)) * β) :=
        ENNReal.ofReal_le_ofReal hbound_real
    _ = ENNReal.ofReal
          (1 - b * (1 - Real.exp (-2 * s)) + d * (Real.exp (2 * s) - 1))
          * ENNReal.ofReal β := by rw [ENNReal.ofReal_mul' hβ0]
    _ ≤ r * poolExpNeg (L := L) (K := K) s c := by
        apply mul_le_mul' hfav
        unfold poolExpNeg; rw [hβ, hp]

end FloorPrefix
end ExactMajority
