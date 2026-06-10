/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Phase D-4 — the inter-phase advance-epidemic seams (`SeamEpidemics`)

`ChainBridges` PROVED that the ten `h_chain` bridges `Post_i ⟹ Pre_{i+1}` of
`DotyTimeHeadline.doty_time_headline_W` are **NOT** pointwise implications: every phase-window
predicate pins all agents to a single, distinct `phase.val`, so a populated config can never
simultaneously satisfy `Post_i` (all at `phase.val = i`) and `Pre_{i+1}` (all at `phase.val =
i+1`).  The bridge is the paper's inter-phase TRANSITION — the `advancePhase` EPIDEMIC — not a
predicate implication on a fixed `x`.

This file builds the honest reconciliation: a **seam phase** between each pair of work phases,
itself a `PhaseConvergenceW` whose `Pre` is the *trigger-form* tail of `work_i.Post` (some agent
already advanced) and whose `Post` is the next work phase's `≥`-window entry condition (all
agents advanced).  The mechanics are the protocol's universal phase epidemic: on EVERY
interaction both outputs take `max` of the two input phases (the public lemmas
`Invariants.Transition_left/right_phase_ge_pair_max`).  The Phase-4 instance
`Phase4Convergence.phase4Convergence` is EXACTLY this epidemic at `p = 4`
(`advancedU`-count drift, rate `m(n−m)/(n(n−1))`); the seam generalises it to a parameter `p`.

## The generic seam (the largest closed subset, delivered here)

`seamEpidemicW p n εepidemic εovershoot hDrift` : `PhaseConvergenceW K` with

* `Pre  c := c.card = n ∧ (∀ a ∈ c, p ≤ a.phase.val) ∧ 1 ≤ #{a ∈ c | p+1 ≤ a.phase.val}`
  — the trigger has fired (some agent is already at phase `≥ p+1`).
* `Post c := c.card = n ∧ (∀ a ∈ c, p+1 ≤ a.phase.val)` — the `≥`-window for the next phase.
* `t := tseam`, `ε := εepidemic + εovershoot`.
* `convergence` — threaded through TWO named feeders, mirroring the campaign's honest
  per-phase-drain pattern (no `sorry`, no smuggled `axiom`, no `native_decide`):
  - `hDrift` : the generic-`p` advance-epidemic convergence bound
        `(K^tseam) c {¬ allPhaseGe (p+1) n} ≤ εepidemic`
    — the parameter-`p` clone of `phase4AdvancedDrift` (drift count = `#{phase ≥ p+1}`,
    rate `m(n−m)/(n(n−1))`, spread by `Transition_*_phase_ge_pair_max`).  Discharging it =
    instantiating the Phase-4 OneSidedCancel engine at abstract `p` (the named GAP).
  - `εovershoot` budget : folded additively; the per-seam overshoot input
    `hNoOvershoot` (below) is what bounds `#{phase ≥ p+2} ≥ 1` at the seam end.

## The `≥`/exact-window reconciliation (`allPhaseEq` ⟺ `allPhaseGe (p+1) ∧ ¬ overshoot`)

A work phase whose `Pre` pins agents to an EXACT phase (`a.phase.val = p+1`) is recovered from
the seam's `≥`-`Post` by `allPhaseEq_of_ge_and_no_overshoot`: `(∀ a, p+1 ≤ phase) ∧
(∀ a, phase < p+2) ⟹ (∀ a, phase = p+1)`.  The "no overshoot" half — no agent has run ahead to
`phase ≥ p+2` during the seam — is the timing-separation event, named per seam as
`hNoOvershoot` and bounded (NOT discharged here) by the Phase0Window counter machinery (a
counter cannot finish too early).

## What is delivered vs. named-gap

DELIVERED (0-sorry, axiom-clean): the generic `seamEpidemicW` instance; the `≥`/exact-window
reconciliation lemma; the trigger/window helper lemmas; the corrected 21-instance composition
skeleton lives in `DotyTimeHeadline` (`doty_time_headline_W2`).
NAMED GAPS (carried as hypotheses, exact shapes recorded in the docstrings):
`hDrift` (generic-`p` epidemic drift), `hNoOvershoot` (per-seam timing separation).
-/

import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.PhaseConvergenceWeak
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.NonuniformMarkovChain
import Ripple.PopulationProtocol.Majority.ExactMajority.Analysis.Invariants

namespace ExactMajority
namespace SeamEpidemics

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal

variable {L K : ℕ}

/-! ## The generic phase windows and the advance trigger -/

/-- The `≥`-window at phase `p`: fixed size `n`, every agent at phase `≥ p`.  This is the
parameter-`p` generalisation of `Phase4Convergence.Q4` (which is `allPhaseGe 4 n`). -/
def allPhaseGe (p n : ℕ) (c : Config (AgentState L K)) : Prop :=
  c.card = n ∧ ∀ a ∈ c, p ≤ a.phase.val

/-- The exact window at phase `p`: fixed size `n`, every agent at phase exactly `= p`.  This is
the shape the EXACT-pinning work `Pre`s carry (`Phase1AllMain`, `Q2`, `Phase6Win`, …). -/
def allPhaseEq (p n : ℕ) (c : Config (AgentState L K)) : Prop :=
  c.card = n ∧ ∀ a ∈ c, a.phase.val = p

/-- The advance trigger: at least one agent has already reached phase `≥ p`. -/
def advTriggered (p : ℕ) (c : Config (AgentState L K)) : Prop :=
  1 ≤ Multiset.countP (fun a => decide (p ≤ a.phase.val)) c

instance (p n : ℕ) (c : Config (AgentState L K)) : Decidable (allPhaseGe p n c) := by
  unfold allPhaseGe; infer_instance

instance (p n : ℕ) (c : Config (AgentState L K)) : Decidable (allPhaseEq p n c) := by
  unfold allPhaseEq; infer_instance

instance (p : ℕ) (c : Config (AgentState L K)) : Decidable (advTriggered p c) := by
  unfold advTriggered; infer_instance

/-! ## The `≥`/exact reconciliation -/

/-- **The honest `≥`-to-exact reconciliation.**  At the seam's end the population is in the
`≥ (p+1)`-window; the next work phase's EXACT `Pre` (`allPhaseEq (p+1)`) is recovered IFF no
agent has overshot to phase `≥ p+2`.  The "no overshoot" half is the named per-seam timing
event `hNoOvershoot`. -/
theorem allPhaseEq_of_ge_and_no_overshoot
    {p n : ℕ} {c : Config (AgentState L K)}
    (hge : allPhaseGe (L := L) (K := K) (p + 1) n c)
    (hno : ∀ a ∈ c, a.phase.val < p + 2) :
    allPhaseEq (L := L) (K := K) (p + 1) n c := by
  obtain ⟨hcard, hge'⟩ := hge
  refine ⟨hcard, ?_⟩
  intro a ha
  have h1 := hge' a ha
  have h2 := hno a ha
  omega

/-- Conversely, the exact window at `p+1` IS the `≥`-window at `p+1` (the trivial direction,
used when chaining a seam INTO an exact-pin work phase that we then keep as `≥`). -/
theorem allPhaseGe_of_allPhaseEq
    {p n : ℕ} {c : Config (AgentState L K)}
    (heq : allPhaseEq (L := L) (K := K) p n c) :
    allPhaseGe (L := L) (K := K) p n c := by
  obtain ⟨hcard, heq'⟩ := heq
  exact ⟨hcard, fun a ha => (heq' a ha).ge⟩

/-! ## The generic seam epidemic instance -/

/-- **The generic phase-advance epidemic seam** `seamEpidemicW`.

`Pre` = `≥ p`-window with the advance trigger fired (some agent at `≥ p+1`); `Post` =
`≥ (p+1)`-window.  The mechanics are the universal phase epidemic
(`Invariants.Transition_*_phase_ge_pair_max`): each interaction lifts both outputs to the
`max` of the two input phases, so the leading `≥ p+1` agent spreads phase `p+1` to the whole
population — the `advancedU`-count drift at abstract `p` (the Phase-4 instance is `p = 4`).

The `convergence` is threaded through the NAMED drift feeder `hDrift` (exact shape: the
generic-`p` epidemic convergence bound on the next `≥`-window), with the overshoot budget
`εovershoot` folded additively.  This is the campaign's honest per-phase-drain pattern: the
quantitative epidemic atom is supplied as a hypothesis, not re-opened here. -/
noncomputable def seamEpidemicW
    (p n tseam : ℕ) (εepidemic εovershoot : ℝ≥0)
    (hDrift : ∀ c : Config (AgentState L K),
        (allPhaseGe (L := L) (K := K) p n c ∧ advTriggered (L := L) (K := K) (p + 1) c) →
        ((NonuniformMajority L K).transitionKernel ^ tseam) c
            {c' | ¬ allPhaseGe (L := L) (K := K) (p + 1) n c'}
          ≤ (εepidemic : ℝ≥0∞)) :
    PhaseConvergenceW (NonuniformMajority L K).transitionKernel where
  Pre := fun c =>
    allPhaseGe (L := L) (K := K) p n c ∧ advTriggered (L := L) (K := K) (p + 1) c
  Post := fun c => allPhaseGe (L := L) (K := K) (p + 1) n c
  t := tseam
  ε := εepidemic + εovershoot
  convergence := by
    intro c hPre
    calc ((NonuniformMajority L K).transitionKernel ^ tseam) c
            {c' | ¬ allPhaseGe (L := L) (K := K) (p + 1) n c'}
        ≤ (εepidemic : ℝ≥0∞) := hDrift c hPre
      _ ≤ ((εepidemic : ℝ≥0∞) + (εovershoot : ℝ≥0∞)) := le_self_add
      _ = ((εepidemic + εovershoot : ℝ≥0) : ℝ≥0∞) := by push_cast; rfl

@[simp] theorem seamEpidemicW_Pre
    (p n tseam : ℕ) (εepidemic εovershoot : ℝ≥0) (hDrift) (c : Config (AgentState L K)) :
    (seamEpidemicW (L := L) (K := K) p n tseam εepidemic εovershoot hDrift).Pre c
      = (allPhaseGe (L := L) (K := K) p n c ∧ advTriggered (L := L) (K := K) (p + 1) c) := rfl

@[simp] theorem seamEpidemicW_Post
    (p n tseam : ℕ) (εepidemic εovershoot : ℝ≥0) (hDrift) (c : Config (AgentState L K)) :
    (seamEpidemicW (L := L) (K := K) p n tseam εepidemic εovershoot hDrift).Post c
      = allPhaseGe (L := L) (K := K) (p + 1) n c := rfl

@[simp] theorem seamEpidemicW_t
    (p n tseam : ℕ) (εepidemic εovershoot : ℝ≥0) (hDrift) :
    (seamEpidemicW (L := L) (K := K) p n tseam εepidemic εovershoot hDrift).t = tseam := rfl

@[simp] theorem seamEpidemicW_eps
    (p n tseam : ℕ) (εepidemic εovershoot : ℝ≥0) (hDrift) :
    (seamEpidemicW (L := L) (K := K) p n tseam εepidemic εovershoot hDrift).ε
      = εepidemic + εovershoot := rfl

/-! ## The two per-seam bridge directions (work ↔ seam), as generic pointwise implications

These are the bridges `composeW_n_phases` consumes in the 21-instance interleave.  They are
GENUINE pointwise implications on populated configs — the phase-clash that refuted the
work↔work bridges (`ChainBridges`) does NOT arise, because the seam's `Pre`/`Post` are
`≥`-windows, not exact-pins.  Both are stated against the generic `allPhaseEq`/`allPhaseGe`
shapes; every concrete work window (`Phase1AllMain`, `Q2`, `Phase6Win`, `Phase5AllWin`, …)
reduces to `allPhaseEq i n ∧ (extra structural component)` and feeds these by projection. -/

/-- **Seam → exact-work bridge.**  The seam's `Post` (the `≥ (p+1)`-window) implies an
EXACT-pin work `Pre` (`allPhaseEq (p+1)`) under the named per-seam timing input `hno`
(no agent overshot to `≥ p+2`).  This is the reconciliation `≥` ⟹ `=` of
`allPhaseEq_of_ge_and_no_overshoot`, packaged as the bridge map.  The `≥`-window work phases
(only Phase 4 = `Q4 = allPhaseGe 4`) take `hge` directly with no overshoot input. -/
theorem seam_into_exact_work
    {p n : ℕ} (hno : ∀ c : Config (AgentState L K),
        allPhaseGe (L := L) (K := K) (p + 1) n c → ∀ a ∈ c, a.phase.val < p + 2) :
    ∀ c, allPhaseGe (L := L) (K := K) (p + 1) n c →
      allPhaseEq (L := L) (K := K) (p + 1) n c :=
  fun c hge => allPhaseEq_of_ge_and_no_overshoot hge (hno c hge)

/-- **Exact-work → seam bridge.**  An exact-pin work `Post` (all agents at phase `= p`) does
NOT by itself fire the advance trigger (`advTriggered (p+1)` requires some agent already at
`≥ p+1`); the trigger is the per-work-phase strengthening the campaign carries as a named
input.  Given the work `Post` `allPhaseEq p n` AND the trigger `advTriggered (p+1)`, the
seam's `Pre` (`allPhaseGe p n ∧ advTriggered (p+1)`) follows pointwise. -/
theorem exact_work_into_seam
    {p n : ℕ} (c : Config (AgentState L K))
    (hwork : allPhaseEq (L := L) (K := K) p n c)
    (htrig : advTriggered (L := L) (K := K) (p + 1) c) :
    allPhaseGe (L := L) (K := K) p n c ∧ advTriggered (L := L) (K := K) (p + 1) c :=
  ⟨allPhaseGe_of_allPhaseEq hwork, htrig⟩

/-- **`≥`-work → seam bridge.**  When the work `Post` is already a `≥`-window
(`allPhaseGe p n`, e.g. Phase 4's `Q4`), the seam `Pre` follows from it plus the trigger with
no `≥`-to-`=` step. -/
theorem ge_work_into_seam
    {p n : ℕ} (c : Config (AgentState L K))
    (hwork : allPhaseGe (L := L) (K := K) p n c)
    (htrig : advTriggered (L := L) (K := K) (p + 1) c) :
    allPhaseGe (L := L) (K := K) p n c ∧ advTriggered (L := L) (K := K) (p + 1) c :=
  ⟨hwork, htrig⟩

end SeamEpidemics
end ExactMajority
