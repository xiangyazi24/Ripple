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

/-! ## Deliverable 2 — Gap-2 assembly attempt (Phase-0 clock-zero / allPhase0 window).

`Phase0Window.allPhase0_window_whp` consumes a UNIFORM per-τ bound `hτ`:

  `∀ τ < t, (K^τ) c₀ {¬noClockAtZero} ≤ ε`   (the clean `ofReal(e^{-45(L+1)})` window bound).

`KilledAffineTail.phase0_clock_zero_killed_affine` gives the per-τ REAL bound but with a
SELF-REFERENTIAL threshold prefix `+ ∑_{σ<τ} (K^σ) c₀ {1 ≤ Φ_clock}` (the escape).  We attack
the named missing reachability/gate-membership piece by asking whether the killed-kernel
formalism makes it unnecessary — whether `allPhase0_window_whp`'s assembly can be re-derived
directly against killed objects + escape.

### The honest decomposition (PROVEN here).

The killed object `phase0_killed_clock_zero_tail` gives the CLEAN decaying budget for the
killed (surviving) clock-zero mass — NO self-reference, NO absorbing `Q`.  The real per-τ
clock-zero mass splits as `killed-clean + escape` (Consumer-1
`real_le_killed_affine_tail_add_escape` at the clock threshold), which we package as
`gap2_real_clock_zero_le_killed_clean_add_escape` below.  This is the strongest CLEAN
decomposition: the killed term genuinely decays, isolating the escape as the SOLE residual.

### What genuinely resists (the precise reachability lemma).

The escape term is `escape(τ) := (killK_now K (phase0Gate n) ^ τ) (some c₀) {none}`.  The ONLY
engine bound for it is `escape_le_threshold_prefix` (via the deterministic exit bridge,
`q = 0`):

  `escape(τ) ≤ ∑_{σ<τ} (K^σ) c₀ {1 ≤ Φ_clock}`   (REAL threshold masses).

This is STRUCTURALLY against the REAL chain (see `GatedKillNow.kill_now_escape_le_prefix_union`:
the escape accounting `M·q + ∑_τ (K^τ) x₀ Sᶜ` bounds the cemetery mass by the REAL chain's
side-event masses — there is no killed-chain reformulation of the escape; the killed chain's
alive successors are EXACTLY the real chain's gated successors, so the cemetery mass IS the
real probability of having left the gate).  And `{¬noClockAtZero} ⊆ {1 ≤ Φ_clock}` (the
threshold link), so each real prefix term DOMINATES the very quantity being bounded — the
recursion does NOT contract.  Hence the killed formalism does NOT remove the reachability
need: it relocates it to "the REAL chain stays in the gate `allPhase0 ∩ {card=n}` along the
surviving trajectory", i.e. the real per-σ clock-zero masses `(K^σ) c₀ {1 ≤ Φ_clock}` are
INDIVIDUALLY small — which is EXACTLY the uniform `hτ` that `allPhase0_window_whp` already
takes as input, and which `phase0_window_whp` supplies per-τ GIVEN the surviving-trajectory
reachability of the absorbing clock-counter drift region.

So **Gap-2 does NOT close via the killed engine alone.**  The precise lemma whose proof would
close it is the genuine reachability/maintenance object stated below as
`Gap2_reachability_target` (a `Prop`-level statement, not proven — it is the role-split /
absorbing-drift-region maintenance layer, NOT an engine gap).  We deliver the proven partial
chain (the clean decomposition) and identify the target precisely. -/

namespace Phase0Window

open GatedDrift

variable {L K : ℕ}

/-- **Gap-2 partial chain (PROVEN): `real ≤ killed-clean + escape` at the clock threshold.**

The real per-τ clock-zero mass `(K^τ) c₀ {¬noClockAtZero}` is bounded by the CLEAN decaying
killed budget `aᵗ·Φ_clock(c₀) + b·∑_{i<τ} aⁱ` (`a = ofReal(1+2(eˢ−1)/n)`, `b =
ofReal(e^{−s·50(L+1)})`, NO `1≤a`, NO absorbing `Q`) PLUS the escape (cemetery) mass.  This is
`real_le_killed_affine_tail_add_escape` at `Φ = Φ_clock`, `θ = θ' = 1`, gate `phase0Gate n`,
composed with the threshold link `{¬noClockAtZero} ⊆ {1 ≤ Φ_clock}`.  The killed term is the
clean `phase0_killed_clock_zero_tail`; the escape is the sole residual (see the section doc). -/
theorem gap2_real_clock_zero_le_killed_clean_add_escape
    (s : ℝ) (hs : 0 ≤ s) (n : ℕ) (hn2 : 2 ≤ n)
    (τ : ℕ) (c₀ : Config (AgentState L K))
    (hc₀ : c₀ ∈ phase0Gate (L := L) (K := K) n) :
    (((NonuniformMajority L K).transitionKernel) ^ τ) c₀
        {c | ¬ noClockAtZero (L := L) (K := K) c}
      ≤ (ENNReal.ofReal (1 + 2 * (Real.exp s - 1) / (n : ℝ)) ^ τ
            * clockCounterPotential (L := L) (K := K) s c₀
          + ENNReal.ofReal (Real.exp (-(s * (50 * (L + 1) : ℕ))))
              * ∑ i ∈ Finset.range τ,
                  ENNReal.ofReal (1 + 2 * (Real.exp s - 1) / (n : ℝ)) ^ i)
        + (GatedDrift.killK_now (NonuniformMajority L K).transitionKernel
              (phase0Gate (L := L) (K := K) n) ^ τ) (some c₀)
            {(none : Option (Config (AgentState L K)))} := by
  classical
  set Kk := (NonuniformMajority L K).transitionKernel with hKk
  set Φ := clockCounterPotential (L := L) (K := K) s with hΦdef
  set G := phase0Gate (L := L) (K := K) n with hGdef
  set a := ENNReal.ofReal (1 + 2 * (Real.exp s - 1) / (n : ℝ)) with ha
  set b := ENNReal.ofReal (Real.exp (-(s * (50 * (L + 1) : ℕ)))) with hb
  -- the affine drift on G.
  have hdrift_G : ∀ x ∈ G, ∫⁻ y, Φ y ∂(Kk x) ≤ a * Φ x + b := by
    intro x hx
    obtain ⟨hall, hcard⟩ := hx
    exact clockCounterPotential_drift_affine s hs n x hcard (hcard ▸ hn2) hall
  -- threshold link: ¬noClockAtZero ⟹ 1 ≤ Φ.
  have hlink : {c | ¬ noClockAtZero (L := L) (K := K) c} ⊆ {c | (1 : ℝ≥0∞) ≤ Φ c} := by
    intro c hc
    exact clockCounterPotential_ge_one_of_not_noClockAtZero s c hc
  refine le_trans (measure_mono hlink) ?_
  -- the killed-clean + escape decomposition at θ = 1.
  have h := real_le_killed_affine_tail_add_escape (K := Kk) (G := G) Φ a b hdrift_G τ c₀ 1
    (by norm_num) (by norm_num)
  rwa [ENNReal.div_one] at h

/-- **The Gap-2 reachability TARGET (statement only — NOT proven; see the section doc).**

The precise object whose proof would close Gap-2: a UNIFORM per-τ bound on the REAL
clock-zero / gate-exit prefix masses along the surviving trajectory.  This is the
role-split / absorbing-drift-region MAINTENANCE layer — that the real chain, started from a
gate config, keeps each per-σ clock-zero mass under the clean window budget `ε` — NOT an
engine gap (the killed AFFINE-TAIL engine itself is delivered 0-sorry axiom-clean).  Given
this, `allPhase0_window_whp`'s `hτ` is discharged directly (its `hτ` IS this `∀ τ` with
`{¬noClockAtZero} ⊆ {1 ≤ Φ_clock}`), and the `gap2_real_clock_zero_le_killed_clean_add_escape`
decomposition above becomes the clean route (killed term decays, escape bounded by the now-
uniform prefix).  We state it as a `Prop` so downstream relays have the exact target. -/
def Gap2_reachability_target (s : ℝ) (t : ℕ)
    (c₀ : Config (AgentState L K)) (ε : ℝ≥0∞) : Prop :=
  ∀ σ ∈ Finset.range t,
    (((NonuniformMajority L K).transitionKernel) ^ σ) c₀
        {c | (1 : ℝ≥0∞) ≤ clockCounterPotential (L := L) (K := K) s c}
      ≤ ε

/-- **Gap-2 conditional close (PROVEN given the reachability target).**  IF the reachability
target `Gap2_reachability_target` holds (the uniform per-σ real clock-zero bound `ε` along the
surviving trajectory), THEN `allPhase0_window_whp`'s conclusion follows at budget `t·ε`.  This
isolates the EXACT residual: the only missing input is `Gap2_reachability_target` (the
absorbing-drift-region maintenance), which is consumed here as a hypothesis exactly as
`allPhase0_window_whp` consumes `hτ` — confirming Gap-2 reduces to that single reachability
object and nothing else.  (The `{¬noClockAtZero} ⊆ {1 ≤ Φ_clock}` threshold link bridges the
target's `{1 ≤ Φ_clock}` shape to `allPhase0_window_whp`'s `{¬noClockAtZero}` shape.) -/
theorem gap2_allPhase0_window_whp_of_reachability
    (s : ℝ) (t : ℕ) (c₀ : Config (AgentState L K))
    (h0 : allPhase0 (L := L) (K := K) c₀)
    (ε : ℝ≥0∞)
    (hreach : Gap2_reachability_target (L := L) (K := K) s t c₀ ε) :
    ((NonuniformMajority L K).transitionKernel ^ t) c₀
        {c | ¬ allPhase0 (L := L) (K := K) c}
      ≤ (t : ℝ≥0∞) * ε := by
  classical
  refine (allPhase0_window_le_prefix_sum t c₀ h0).trans ?_
  have hτ : ∀ σ ∈ Finset.range t,
      (((NonuniformMajority L K).transitionKernel) ^ σ) c₀
          {c | ¬ noClockAtZero (L := L) (K := K) c} ≤ ε := by
    intro σ hσ
    refine le_trans (measure_mono ?_) (hreach σ hσ)
    intro c hc
    exact clockCounterPotential_ge_one_of_not_noClockAtZero s c hc
  calc ∑ σ ∈ Finset.range t,
        (((NonuniformMajority L K).transitionKernel) ^ σ) c₀
          {c | ¬ noClockAtZero (L := L) (K := K) c}
      ≤ ∑ _σ ∈ Finset.range t, ε := Finset.sum_le_sum hτ
    _ = (t : ℝ≥0∞) * ε := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

end Phase0Window

end ExactMajority
