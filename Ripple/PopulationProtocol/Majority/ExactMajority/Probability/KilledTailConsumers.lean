/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# `KilledTailConsumers` — the FINAL whp instantiations against the killed engine.

`Probability/KilledAffineTail.lean` built the generic affine-immigration killed-tail
engine (`killed_now_affine_tail`, `real_le_killed_affine_tail_add_escape`,
`escape_le_threshold_prefix`, `real_window_killed_affine`) and the three consumer
ADAPTERS (`top_killed_cosh_tail` + `topGate_exit_bridge` for Consumer 2,
`phase0_clock_zero_killed_affine` for Consumer 1/Gap-2, `midBand_real_contractive_tail`
for Consumer 3).  Its "Honest residual" doc-section flagged the remaining MECHANICAL
re-cut: instantiate the FINAL whp statements of those consumers against the killed engine,
replacing the old `windowDrift_tail` / `gated_real_tail` call-site shapes.

This file (append-only; no existing file is edited) performs that re-cut.  Three deliverables.

## Deliverable 1 — Consumer 2 final form (top-split tail).

`real_le_killed_affine_tail_add_escape` at `Φ := coshPot s`, `a := ofReal(cosh s)`, `b := 0`,
gate `G := topGate n`, threshold `θ := ofReal(cosh(s·δn))`, combined with the threshold link
`coshPot_ge_thresh_of_not_window` (`{¬TopSplitWindow} ⊆ {θ ≤ coshPot}`), the b=0 killed cosh
tail (`top_killed_cosh_tail`), the deterministic gate-exit bridge (`topGate_exit_bridge` ⟹
`escape_le_threshold_prefix` at the CLOCK-potential exit threshold), and the balanced-start
fact `coshPot_init_one`, gives the FINAL Lemma-5.1 top-split tail:

  `(K^T) c₀ {¬TopSplitWindow δ n} ≤ (cosh s)^T / cosh(s·δn)
       + ∑_{σ<T} (K^σ) c₀ {1 ≤ Φ_clock}`,

with hypothesis surface = `Phase0Initial n c₀` + `NoAssignedMcrConfig c₀` + arithmetic.  The
gate `topGate` (= `allPhase0 ∩ {card=n} ∩ NoAssignedMcr ∩ LedgerInv`) is supplied internally;
`LedgerInv c₀` from `LedgerInv_init`, the four conjuncts one-step preserved.  NO absorbing `Q`.
The remaining `∑_σ {1 ≤ Φ_clock}` term is exactly the Phase-0 clock-zero escape prefix that
Gap-2 (Consumer 1) handles.

## Deliverable 2 — Gap-2 assembly attempt (Phase-0 clock-zero / allPhase0 window).

`allPhase0_window_whp` (Phase0Window) consumes a uniform per-τ bound `hτ` for
`(K^τ) c₀ {¬noClockAtZero}`.  We attack the named missing reachability/gate-membership piece:
the killed object `phase0_killed_clock_zero_tail` gives the CLEAN decaying budget for the
killed (surviving) clock-zero mass with NO self-reference and NO absorbing `Q`.  We show the
honest decomposition `real ≤ killed-clean + escape` (Consumer-1 `real ≤ killed + escape` at
the clock threshold) and isolate the EXACT residual: the escape mass
`(killK_now^τ)(some c₀){none}`, whose `escape_le_threshold_prefix` bound is the
SELF-REFERENTIAL `∑_{σ<τ} {1 ≤ Φ_clock}` (since `{¬noClockAtZero} ⊆ {1 ≤ Φ_clock}`).  We state
the precise reachability lemma whose proof would close Gap-2 and record what genuinely resists
(see the doc on `gap2_real_clock_zero_le_killed_clean_add_escape`).

## Deliverable 3 — Consumer 3 final form (εmid).

`midBand_real_contractive_tail` at the pool-MGF, instantiated with FloorMasses' fully
discharged one-step drift `pool_expNeg_one_step_drift_floorMasses` (rate the proven-`<1`
favorability multiplier, immigration `b = 0`), gives the strongest hypothesis-free εmid-shape
statement: a GENUINELY decaying `rᵗ` leading term plus the floor escape — the contractive
mid-band tail FloorPrefix's finding 3 was blocked on (no `1 ≤ r`).  `FloorMasses`' region
hypothesis (`hfresh : uMin ≤ freshMcrCount` on `PoolDriftRegion`, the documented honest
hbirth feeder) is kept as the documented region hypothesis.

Everything here is 0-`sorry` / 0-`axiom` (only `propext`, `Classical.choice`, `Quot.sound`) /
no `native_decide`.

Reference: `Probability/KilledAffineTail.lean` (engine + adapters);
`Probability/TopSplitDrift.lean`, `Probability/TopSplitInward.lean`,
`Probability/RectangleResidualProof.lean` (Consumer-2 chain);
`Probability/Phase0Window.lean` (`allPhase0_window_whp`, the Gap-2 assembler);
`Probability/FloorPrefix.lean`, `Probability/FloorMasses.lean` (Consumer-3 chain).
-/

import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.KilledAffineTail
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.FloorMasses

namespace ExactMajority

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Classical BigOperators

/-! ## Deliverable 1 — Consumer 2 final form (top-split tail). -/

namespace RoleSplitConcentration

open GatedDrift

variable {L K : ℕ}

/-- **The Consumer-2 gate contains the balanced start.**  At `Phase0Initial n c₀`, with the
honest `NoAssignedMcrConfig c₀` side-hypothesis, `c₀ ∈ topGate n`: `allPhase0` and `card = n`
are immediate from `Phase0Initial`, `NoAssignedMcrConfig` is the carried hypothesis, and
`LedgerInv` holds at the balanced start (`LedgerInv_init`). -/
theorem topGate_mem_of_phase0Initial {n : ℕ} {c₀ : Config (AgentState L K)}
    (hinit : Phase0Initial (L := L) (K := K) n c₀)
    (hnomcr : NoAssignedMcrConfig (L := L) (K := K) c₀) :
    c₀ ∈ topGate (L := L) (K := K) n := by
  refine ⟨?_, hinit.1, hnomcr, LedgerInv_init hinit⟩
  intro a ha; exact (hinit.2 a ha).1

/-- **Consumer 2 — the FINAL Lemma-5.1 top-split tail (killed engine, no absorbing `Q`).**

From the Phase-0 balanced start `Phase0Initial n c₀` plus the honest start side-condition
`NoAssignedMcrConfig c₀`, the probability that the top-split window `TopSplitWindow δ n` fails
after `T` steps is at most the boundary-clean cosh (Chernoff) tail PLUS the Phase-0 clock-zero
escape prefix:

  `(K^T) c₀ {¬TopSplitWindow δ n}
     ≤ (cosh s)^T / cosh(s·δn) + ∑_{σ<T} (K^σ) c₀ {1 ≤ Φ_clock}`.

This closes the §5.1 probabilistic chain: the absorbing-`Q` requirement of
`topSplitWindow_whp_rectFree` / `topSplitWindow_whp_cosh_clean` is REMOVED — the killed kernel
on the gate `topGate n` substitutes for it, the in-gate tail is the b=0 killed cosh tail
(`top_killed_cosh_tail`), and the gate's only exit is the (killed, deterministic) `allPhase0`
breach, bounded via `topGate_exit_bridge` by the clock-potential threshold prefix.  The
remaining `∑_σ {1 ≤ Φ_clock}` term is exactly the Phase-0 clock-zero escape (Consumer 1 /
Gap-2).  Hypothesis surface: `Phase0Initial n c₀` + `NoAssignedMcrConfig c₀` + arithmetic. -/
theorem topSplitWindow_whp_killed
    (s : ℝ) (hs : 0 ≤ s) (sc : ℝ) (δ : ℝ) (n : ℕ) (hn2 : 2 ≤ n)
    (c₀ : Config (AgentState L K))
    (hinit : Phase0Initial (L := L) (K := K) n c₀)
    (hnomcr : NoAssignedMcrConfig (L := L) (K := K) c₀)
    (T : ℕ) (hδn : 0 < s * (δ * n)) :
    ((NonuniformMajority L K).transitionKernel ^ T) c₀
        {c | ¬ TopSplitWindow (L := L) (K := K) δ n c}
      ≤ ENNReal.ofReal (Real.cosh s) ^ T
            / ENNReal.ofReal (Real.cosh (s * (δ * n)))
        + ∑ σ ∈ Finset.range T,
            ((NonuniformMajority L K).transitionKernel ^ σ) c₀
              {c | (1 : ℝ≥0∞) ≤ Phase0Window.clockCounterPotential (L := L) (K := K) sc c} := by
  classical
  set Kk := (NonuniformMajority L K).transitionKernel with hKk
  set G := topGate (L := L) (K := K) n with hGdef
  set Φ := coshPot (L := L) (K := K) s with hΦdef
  set θ := ENNReal.ofReal (Real.cosh (s * (δ * n))) with hθdef
  -- threshold θ ≠ 0, θ ≠ ⊤.
  have hone_le_cosh : ∀ x : ℝ, 1 ≤ Real.cosh x := by
    intro x; rw [Real.cosh_eq]
    nlinarith [Real.add_one_le_exp x, Real.add_one_le_exp (-x),
      Real.exp_pos x, Real.exp_pos (-x)]
  have hθpos : (0 : ℝ) < Real.cosh (s * (δ * n)) :=
    lt_of_lt_of_le zero_lt_one (hone_le_cosh _)
  have hθ0 : θ ≠ 0 := by rw [hθdef, ne_eq, ENNReal.ofReal_eq_zero, not_le]; exact hθpos
  have hθtop : θ ≠ ∞ := by rw [hθdef]; exact ENNReal.ofReal_ne_top
  have hδnpos : 0 ≤ δ * n := by
    by_contra h; push Not at h
    exact absurd (mul_nonpos_of_nonneg_of_nonpos hs (le_of_lt h)) (not_le.2 hδn)
  -- the b=0 multiplicative cosh drift on the gate G.
  have hdrift_G : ∀ x ∈ G, ∫⁻ y, Φ y ∂(Kk x) ≤ ENNReal.ofReal (Real.cosh s) * Φ x + 0 := by
    intro x hx
    obtain ⟨hall, hcard, _hnomcr, hled⟩ := hx
    rw [add_zero]
    have hc2 : 2 ≤ Multiset.card x := hcard ▸ hn2
    have hrect := rectangleResidual_of_allPhase0 x hc2 hall
    have hinw := inwardResidual_of_ledger s hs x hc2 hall hled hrect
    exact coshPot_drift s hs x hc2 hall hinw
  -- Step 1: real ≤ killed-tail + escape, at Φ = coshPot, θ = cosh(s·δn) threshold.
  -- {¬TopSplitWindow} ⊆ {θ ≤ Φ}.
  have hlink : {c | ¬ TopSplitWindow (L := L) (K := K) δ n c} ⊆ {c | θ ≤ Φ c} := by
    intro c hc
    exact coshPot_ge_thresh_of_not_window s hs hδnpos c hc
  refine le_trans (measure_mono hlink) ?_
  refine le_trans
    (real_le_killed_affine_tail_add_escape (K := Kk) (G := G) Φ (ENNReal.ofReal (Real.cosh s)) 0
      hdrift_G T c₀ θ hθ0 hθtop) ?_
  -- the killed-tail summand: (cosh s)^T·Φ(c₀)/θ; at the balanced start Φ(c₀) = 1.
  have hΦinit : Φ c₀ = 1 := coshPot_init_one s hinit
  -- rewrite the killed-tail summand as (cosh s)^T / θ.
  have htail_eq : (ENNReal.ofReal (Real.cosh s) ^ T * Φ c₀
        + (0 : ℝ≥0∞) * ∑ i ∈ Finset.range T, ENNReal.ofReal (Real.cosh s) ^ i) / θ
      = ENNReal.ofReal (Real.cosh s) ^ T / ENNReal.ofReal (Real.cosh (s * (δ * n))) := by
    rw [hΦinit, mul_one, zero_mul, add_zero, hθdef]
  rw [htail_eq]
  refine add_le_add le_rfl ?_
  -- the escape summand: (killK_now Kk G ^ T)(some c₀){none} ≤ ∑_{σ<T} (Kk^σ) c₀ {1 ≤ Φ_clock}.
  have hc₀G : c₀ ∈ G := topGate_mem_of_phase0Initial hinit hnomcr
  -- the deterministic exit bridge at the CLOCK-potential threshold θ' = 1.
  have hbridge : ∀ x ∈ G, Phase0Window.clockCounterPotential (L := L) (K := K) sc x < 1 →
      Kk x Gᶜ = 0 := by
    intro x hx hxΦ
    exact topGate_exit_bridge sc n x hx hxΦ
  exact escape_le_threshold_prefix (K := Kk) (G := G)
    (Phase0Window.clockCounterPotential (L := L) (K := K) sc) 1 hbridge T c₀ hc₀G

end RoleSplitConcentration

end ExactMajority
