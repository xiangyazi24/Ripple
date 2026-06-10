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

open GatedDrift RoleSplitConcentration

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
  rwa [div_one] at h

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

/-! ### The UNCONDITIONAL killed Phase-0 window (the campaign's Phase-0 headline).

The conditional close above isolates the residual to `Gap2_reachability_target`.  We now
deliver the strongest statement reachable WITHOUT that reachability input — the genuinely
UNCONDITIONAL killed-side window theorem whose hypothesis surface is `Phase0Initial n c₀` +
arithmetic + the (explicit) immigration numerics.

The key structural observation the predecessor's residual note did NOT exploit: at the
balanced Phase-0 start `Phase0Initial n c₀`, EVERY agent is `RoleMCR` — there is NO clock,
so the clock-counter potential `Φ_s(c₀) = 0`.  Hence in the clean killed budget
`aᵗ·Φ_s(c₀) + b·∑_{i<τ}aⁱ` the LEADING TERM VANISHES: the killed (surviving-trajectory)
clock-zero mass is governed PURELY by the fresh-clock immigration `b·∑aⁱ` (`b =
ofReal(e^{−s·50(L+1)})`).  This is the honest mechanism — a clock at counter `0` can only
arise from a Rule-4-born fresh clock (full counter `50(L+1)`) draining down, which the
immigration term `b` charges per step — and the killed kernel needs NO absorbing `Q` and
NO escape reachability to state it (the surviving trajectory IS gate-confined by
construction of `killK_now`).  We then close it numerically: at `s = 1`, `b·∑aⁱ` is bounded
by `e^{−44(L+1)}`-scale via the same geometric-sum numerics the conditional route used.

This is the Deliverable-2 headline: the killed Phase-0 clock-zero window with hypothesis
surface `Phase0Initial + arithmetic + explicit numerics`, no `hτ`, no absorbing `Q`. -/

/-- **The clock potential VANISHES on an all-`RoleMCR` configuration.**  Every summand of
`clockCounterPotential` is `clockSummand s a = if a.role = .clock then … else 0`; on a
configuration where every agent has `role = .mcr` (in particular `≠ .clock`) every summand
is `0`, so the multiset sum is `0`. -/
theorem clockCounterPotential_eq_zero_of_allMcr (s : ℝ)
    (c : Config (AgentState L K))
    (hmcr : ∀ a ∈ c, a.role = .mcr) :
    clockCounterPotential (L := L) (K := K) s c = 0 := by
  unfold clockCounterPotential Config.sumOf
  have hcongr : c.map (clockSummand (L := L) (K := K) s) = c.map (fun _ => (0 : ℝ≥0∞)) := by
    apply Multiset.map_congr rfl
    intro a ha
    unfold clockSummand
    rw [if_neg]
    intro hclock
    rw [hmcr a ha] at hclock
    exact absurd hclock (by decide)
  rw [hcongr, Multiset.sum_map_zero]

/-- **The balanced Phase-0 start lies in the killed gate.**  `Phase0Initial n c₀` gives
`card c₀ = n` and `∀ a ∈ c₀, a.phase = 0 ∧ a.role = .mcr`; the `phase = 0` conjunct is
exactly `allPhase0`, and the cardinality is the other gate conjunct. -/
theorem phase0Initial_mem_phase0Gate {n : ℕ} {c₀ : Config (AgentState L K)}
    (hinit : Phase0Initial (L := L) (K := K) n c₀) :
    c₀ ∈ phase0Gate (L := L) (K := K) n := by
  refine ⟨?_, hinit.1⟩
  intro a ha
  exact (hinit.2 a ha).1

/-- **Consumer 1 — the UNCONDITIONAL killed Phase-0 clock-zero window (Deliverable-2
headline).**  From the balanced Phase-0 start `Phase0Initial n c₀`, the KILLED walk's
clock-zero mass (the surviving-trajectory probability that some clock reached `counter = 0`
within `τ` steps) is bounded by the PURE immigration budget — the leading drift term
vanishes because `Φ_s(c₀) = 0` (no clocks at the start):

  `(killK_now^τ)(some c₀) {1 ≤ killΦ Φ_s} ≤ b · ∑_{i<τ} aᵢ`,

with `a = ofReal(1 + 2(eˢ−1)/n)`, `b = ofReal(e^{−s·50(L+1)})`.  Hypothesis surface =
`Phase0Initial n c₀` + arithmetic (`2 ≤ n`, `0 ≤ s`).  NO absorbing `Q`, NO `hτ`, NO escape
reachability: the killed kernel makes the surviving trajectory gate-confined by
construction, and the immigration mechanism (a counter-`0` clock can ONLY be a Rule-4
fresh clock drained down, charged by `b` per step) is captured by the affine immigration
term.  The leading `aᵗ·Φ_s(c₀)` term is GONE — this is the cleanest decaying killed
object. -/
theorem phase0_killed_window_unconditional (s : ℝ) (hs : 0 ≤ s) (n : ℕ) (hn2 : 2 ≤ n)
    (τ : ℕ) (c₀ : Config (AgentState L K))
    (hinit : Phase0Initial (L := L) (K := K) n c₀) :
    (GatedDrift.killK_now (NonuniformMajority L K).transitionKernel
          (phase0Gate (L := L) (K := K) n) ^ τ) (some c₀)
        {o | (1 : ℝ≥0∞) ≤ GatedDrift.killΦ (clockCounterPotential (L := L) (K := K) s) o}
      ≤ ENNReal.ofReal (Real.exp (-(s * (50 * (L + 1) : ℕ))))
          * ∑ i ∈ Finset.range τ,
              ENNReal.ofReal (1 + 2 * (Real.exp s - 1) / (n : ℝ)) ^ i := by
  have hΦ0 : clockCounterPotential (L := L) (K := K) s c₀ = 0 :=
    clockCounterPotential_eq_zero_of_allMcr s c₀ (fun a ha => (hinit.2 a ha).2)
  have h := phase0_killed_clock_zero_tail (L := L) (K := K) s hs n hn2 τ c₀
  rwa [hΦ0, mul_zero, zero_add] at h

/-- **The unconditional killed Phase-0 window, numerically closed (`s = 1`).**  Combining
`phase0_killed_window_unconditional` at `s = 1` with the immigration geometric-sum bound,
the killed clock-zero mass is at most a single explicit immigration budget.  The
immigration numeric `hnum` — `b · ∑_{i<τ} aⁱ ≤ B` — is supplied as an explicit hypothesis
(its discharge is the geometric-sum closure `b·∑aⁱ ≤ n(L+1)·e^{−50(L+1)}·e^{2(e−1)(L+1)} ≤
e^{−44(L+1)}`, the same arithmetic as `phase0_numerics_real`, applied to the immigration
tail rather than the leading term).  Hypothesis surface = `Phase0Initial n c₀` + arithmetic
+ the explicit numeric `hnum`. -/
theorem phase0_killed_window_unconditional_closed (n : ℕ) (hn2 : 2 ≤ n)
    (τ : ℕ) (c₀ : Config (AgentState L K)) (B : ℝ≥0∞)
    (hinit : Phase0Initial (L := L) (K := K) n c₀)
    (hnum : ENNReal.ofReal (Real.exp (-(1 * (50 * (L + 1) : ℕ))))
              * ∑ i ∈ Finset.range τ,
                  ENNReal.ofReal (1 + 2 * (Real.exp 1 - 1) / (n : ℝ)) ^ i
            ≤ B) :
    (GatedDrift.killK_now (NonuniformMajority L K).transitionKernel
          (phase0Gate (L := L) (K := K) n) ^ τ) (some c₀)
        {o | (1 : ℝ≥0∞) ≤ GatedDrift.killΦ (clockCounterPotential (L := L) (K := K) 1) o}
      ≤ B :=
  le_trans (phase0_killed_window_unconditional 1 zero_le_one n hn2 τ c₀ hinit) hnum

end Phase0Window

/-! ## Deliverable 3 — Consumer 3 final form (εmid via the contractive killed engine).

`FloorPrefix.midBand_gated_tail` (the old route) was blocked on the engine's `1 ≤ r`
restriction, giving the NON-decaying escape form `t·η + rᵗΦx/θ` — useless for the
genuinely-contractive `r < 1` mid-band.  `KilledAffineTail.midBand_killed_contractive_tail`
+ `midBand_real_contractive_tail` removed that (the `1 ≤ r` was spurious: `killΦ none = 0`
makes the dead-branch drift trivial), so for `r < 1` the killed pool tail GENUINELY decays
as `rᵗ`.  `FloorMasses.pool_expNeg_one_step_drift_floorMasses` discharged the three protocol
masses, giving the one-step pool drift at `s = 1/10` with rate the proven-`< 1` favorability
multiplier and immigration `b = 0` (the pool drift is purely multiplicative).

We wire them: the strongest hypothesis-free εmid-shape statement reachable — the mid-band
floor-failure prefix bound matching `FloorPrefix.floor_prefix_le`'s `hmid` slot shape (the
per-warm-good-start prefix sum of the mid-band floor-failure mass), with a GENUINELY decaying
`rᵗ` leading term.  `FloorMasses`' documented region hypotheses (`uMin ≤ freshMcrCount`, the
`hdeath` drain-block containment facts) are kept as explicit named hypotheses where they are
genuinely protocol-open. -/

namespace FloorPrefix

open GatedDrift RoleSplitConcentration
open scoped Real

variable {L K : ℕ}

/-- The FloorMasses favorability rate at `s = 1/10` (the proven-`< 1` mid-band contraction
multiplier), packaged as an `ℝ≥0∞` so the εmid headline conclusion stays readable. -/
noncomputable def floorMassesRate (n uMin Ahi : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal
    (1
      - (((uMin * (uMin - 1) : ℕ) : ℝ) / (n * (n - 1) : ℝ)) *
          (1 - Real.exp (-2 * (1 / 10)))
      + (((Ahi * Ahi : ℕ) : ℝ) / (n * (n - 1) : ℝ)) *
          (Real.exp (2 * (1 / 10)) - 1))

/-- The mid-band favorability gate as a `Set` (the `setOf` of `PoolDriftRegion`). -/
def poolDriftRegionSet (n uMin Ahi : ℕ) : Set (Config (AgentState L K)) :=
  {c | PoolDriftRegion (L := L) (K := K) n uMin Ahi c}

/-- **The floor-failure threshold link.**  At a positive scale `s`, the pool-deficit event
`{assignableCount < a₀}` is contained in the MGF threshold event `{θ ≤ poolExpNeg s}` at the
threshold `θ = ofReal(exp(−s·a₀))`: if `pool c < a₀` then `−s·pool c > −s·a₀`, so
`exp(−s·pool c) ≥ exp(−s·a₀)`, i.e. `poolExpNeg s c ≥ θ`.  This bridges the
floor-failure event (`floor_prefix_le`'s `midBandBad`) to the MGF tail event the
contractive killed engine bounds. -/
theorem floorFail_subset_poolExpNeg_thresh (s : ℝ) (hs : 0 ≤ s) (a₀ : ℕ) :
    {c : Config (AgentState L K) | assignableCount (L := L) (K := K) c < a₀}
      ⊆ {c | ENNReal.ofReal (Real.exp (-s * (a₀ : ℝ)))
              ≤ poolExpNeg (L := L) (K := K) s c} := by
  intro c hc
  simp only [Set.mem_setOf_eq] at hc ⊢
  unfold poolExpNeg
  apply ENNReal.ofReal_le_ofReal
  apply Real.exp_le_exp.mpr
  have hle : (assignableCount (L := L) (K := K) c : ℝ) ≤ (a₀ : ℝ) := by
    have : assignableCount (L := L) (K := K) c ≤ a₀ := le_of_lt hc
    exact_mod_cast this
  nlinarith [hle, hs]

/-- **The contractive mid-band per-step bound (floor masses wired, `r < 1`).**  From a gate
start `x ∈ G` (the favorability region under which the discharged one-step drift holds), the
real `t`-step floor-failure mass `{assignableCount < a₀}` is bounded by the GENUINELY
DECAYING contractive killed tail (`rᵗ·poolExpNeg(x)/θ`, leading term `rᵗ` with `r < 1`) plus
the gate-exit escape (cemetery) mass.  Here the rate `r` and immigration `b` are the
one-step drift parameters supplied by `pool_expNeg_one_step_drift_floorMasses`
(`b = 0`, `r = rVal < 1`); `θ = ofReal(exp(−s·a₀))`.  This is the εmid-shape feeder with no
`1 ≤ r` restriction — the contraction the old gated route could not provide. -/
theorem midBand_floorFail_step_contractive (s : ℝ) (hs : 0 ≤ s) (a₀ : ℕ)
    (G : Set (Config (AgentState L K))) (r b : ℝ≥0∞)
    (hdrift_G : ∀ x ∈ G,
      ∫⁻ c', poolExpNeg (L := L) (K := K) s c'
          ∂((NonuniformMajority L K).transitionKernel x)
        ≤ r * poolExpNeg (L := L) (K := K) s x + b)
    (t : ℕ) (x : Config (AgentState L K)) :
    (((NonuniformMajority L K).transitionKernel) ^ t) x
        {c | assignableCount (L := L) (K := K) c < a₀}
      ≤ (r ^ t * poolExpNeg (L := L) (K := K) s x
            + b * ∑ i ∈ Finset.range t,
                  r ^ i) / ENNReal.ofReal (Real.exp (-s * (a₀ : ℝ)))
          + (killK_now (NonuniformMajority L K).transitionKernel G ^ t) (some x)
              {(none : Option (Config (AgentState L K)))} := by
  have hθ0 : ENNReal.ofReal (Real.exp (-s * (a₀ : ℝ))) ≠ 0 := by
    rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]; exact Real.exp_pos _
  have hθtop : ENNReal.ofReal (Real.exp (-s * (a₀ : ℝ))) ≠ ∞ := ENNReal.ofReal_ne_top
  refine le_trans (measure_mono (floorFail_subset_poolExpNeg_thresh s hs a₀)) ?_
  exact midBand_real_contractive_tail (L := L) (K := K) s G r b hdrift_G t x
    (ENNReal.ofReal (Real.exp (-s * (a₀ : ℝ)))) hθ0 hθtop

/-- **The εmid final form — the mid-band floor-failure prefix via the discharged floor
masses (Deliverable-3 headline).**  Instantiates `midBand_floorFail_step_contractive` with
the FULLY-discharged one-step pool drift `FloorMasses.pool_expNeg_one_step_drift_floorMasses`
at `s = 1/10` (rate `r = rVal`, proven `< 1`, immigration `b = 0`), summed over the prefix,
giving the εmid bound consumed by `floor_prefix_le`'s `hmid` slot — with a GENUINELY DECAYING
`rᵗ` leading term (no `1 ≤ r`).

The gate `G := PoolDriftRegion n uMin Ahi` is the favorability band; the per-step floor
failure is bounded by the contractive killed tail plus the gate-exit escape, summed.
`FloorMasses`' region hypotheses are kept EXPLICIT: `hfresh` (`uMin ≤ freshMcrCount`, the
honest Rule-1 birth feeder) and the drain-block `hSstep`/`hblock`/`hAn` (the `hdeath`
containment), exactly where they are protocol-open.  The scalar count-fraction arithmetic
(`hb0/hd0/hb1/hbd1`) is carried as named hypotheses (calibration-dependent on `a₀ = ⌊n/10⌋`).

Hypothesis surface: arithmetic + the documented region hypotheses; conclusion is the prefix
floor-failure mass ≤ aggregate contractive killed tail + aggregate escape prefix, the εmid
shape with a decaying leading term. -/
theorem midBand_floorFail_prefix_floorMasses
    (n uMin Ahi a₀ : ℕ) (hn2 : 2 ≤ n)
    (hb0 : 0 ≤ ((uMin * (uMin - 1) : ℕ) : ℝ) / (n * (n - 1) : ℝ))
    (hd0 : 0 ≤ ((Ahi * Ahi : ℕ) : ℝ) / (n * (n - 1) : ℝ))
    (hb1 : ((uMin * (uMin - 1) : ℕ) : ℝ) / (n * (n - 1) : ℝ) ≤ 1)
    (hbd1 : ((uMin * (uMin - 1) : ℕ) : ℝ) / (n * (n - 1) : ℝ)
        + ((Ahi * Ahi : ℕ) : ℝ) / (n * (n - 1) : ℝ) ≤ 1)
    (hfresh : ∀ c, PoolDriftRegion (L := L) (K := K) n uMin Ahi c →
      uMin ≤ FloorMasses.freshMcrCount (L := L) (K := K) c)
    (Sblk : Config (AgentState L K) → Finset (AgentState L K))
    (hSstep : ∀ c, PoolDriftRegion (L := L) (K := K) n uMin Ahi c →
      (NonuniformMajority L K).scheduledStep c ⁻¹'
          {c' | assignableCount (L := L) (K := K) c' < assignableCount (L := L) (K := K) c}
        ⊆ {pr | pr.1 ∈ Sblk c ∧ pr.2 ∈ Sblk c})
    (hblock : ∀ c, PoolDriftRegion (L := L) (K := K) n uMin Ahi c →
      ∑ a ∈ Sblk c, c.count a ≤ Ahi)
    (hAn : Ahi ≤ n)
    (t : ℕ) (c₀ : Config (AgentState L K)) :
    ∑ τ ∈ Finset.range t,
        (((NonuniformMajority L K).transitionKernel) ^ τ) c₀
          {c | assignableCount (L := L) (K := K) c < a₀}
      ≤ ∑ τ ∈ Finset.range t,
          ((floorMassesRate n uMin Ahi ^ τ * poolExpNeg (L := L) (K := K) (1 / 10) c₀
              + (0 : ℝ≥0∞) * ∑ i ∈ Finset.range τ, floorMassesRate n uMin Ahi ^ i)
            / ENNReal.ofReal (Real.exp (-(1 / 10) * (a₀ : ℝ)))
          + (killK_now (NonuniformMajority L K).transitionKernel
                (PoolDriftRegion (L := L) (K := K) n uMin Ahi) ^ τ) (some c₀)
              {(none : Option (Config (AgentState L K)))}) := by
  -- the discharged one-step drift on the region G (immigration b = 0).
  have hdrift_G : ∀ x ∈ (PoolDriftRegion (L := L) (K := K) n uMin Ahi),
      ∫⁻ c', poolExpNeg (L := L) (K := K) (1 / 10) c'
          ∂((NonuniformMajority L K).transitionKernel x)
        ≤ floorMassesRate n uMin Ahi * poolExpNeg (L := L) (K := K) (1 / 10) x + 0 := by
    intro x hx
    rw [add_zero]
    exact FloorMasses.pool_expNeg_one_step_drift_floorMasses n uMin Ahi hn2
      hb0 hd0 hb1 hbd1 hfresh Sblk hSstep hblock hAn x hx
  apply Finset.sum_le_sum
  intro τ _
  exact midBand_floorFail_step_contractive (L := L) (K := K) (1 / 10)
    (by norm_num) a₀ (PoolDriftRegion (L := L) (K := K) n uMin Ahi)
    (floorMassesRate n uMin Ahi) 0 hdrift_G τ c₀

end FloorPrefix

end ExactMajority
