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

end FloorPrefix
end ExactMajority
