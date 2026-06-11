/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The all-hours UNION for the Theorem-6.2 confinement event (audit fix F1 refinement)

This file closes the genuinely-missing piece the Codex adversarial audit found in F1
(`/tmp/codex_audit_report.md` §F1).  No existing file is edited; this file ADDS the honest
hour-union composition and re-wires the confinement consumer surface onto the per-hour bricks.

## What the audit found (F1 refinement)

`ConfinementSurface.mainConfinement_kernel_whp` (and the orphaned engine
`MainExponentConfinement.theorem6_2_main_confinement_whp` it routes through) takes

```
hHourTail : ((K^phase3to5Time) c₀ {c | ¬ ConfinementEvent c}) ≤ η
```

— the FINAL bad-event bound — and returns the SAME bound (a `rfl`-level repackaging).  That is a
TAUTOLOGICAL carry: the all-hours-union DISCHARGE — composing the per-hour squaring tails over the
`numHours` hours of the Phase-3→5 horizon into the final `{¬ConfinementEvent}` budget — was never
performed.  The honest object is NOT the final tail; it is the per-hour squaring failure plus the
hour-boundary chaining.

## The honest chain (mirrors the landed checkpoint-composition machinery)

The campaign already lands the generic invariant-union-over-a-window-horizon machinery for the §6
CLOCK side:

* `EarlyDripMarked.invariant_union_bound` — per-step invariant failure `δ` from invariant states
  unions over `t` steps to `≤ t·δ` (a Chapman–Kolmogorov induction on the step count);
* `EarlyDripMarked.checkpoint_composition` — the same at the WINDOW kernel `Kk^w`: per-WINDOW
  failure `δ` from invariant states unions over `KK` windows to `≤ KK·δ` at horizon `w·KK`
  (`pow_mul` + `invariant_union_bound (Kk^w)`);
* `WidthPrefix.checkpoint_composition_prefix` — the same with a terminal remainder block
  (`w·j + r`, `r < w`), via ONE extra Chapman–Kolmogorov split.

These chain per-WINDOW facts across a multi-window horizon for the clock front.  The Codex audit's
F1 refinement asks for the SAME pattern, mirrored for the MAIN-profile hours: the per-hour squaring
tail is the per-WINDOW fact (window length = `hourLen`), and the union over the `numHours` hours of
the `phase3to5Time = hourLen·numHours` horizon is exactly `checkpoint_composition` with
`Inv := ConfinementEvent`, `w := hourLen`, `KK := numHours`.

`ConfinementSurface.ConfinementEvent` IS a discrete-measurable invariant on `Config (AgentState L K)`
(`MarkovChain.instDiscreteMeasurableSpaceConfig`), and `(NonuniformMajority L K).transitionKernel` IS
a Markov kernel (`MarkovChain.transitionKernel_isMarkovKernel`).  So the landed
`checkpoint_composition` applies VERBATIM — no new mathematics, the existing union engine wired onto
the confinement event.

## What this file delivers

1. `confinementEvent_hours_union` — the hour-union composition theorem.  From the PER-HOUR
   hypothesis (each hour, from any confinement-satisfying state, the single-hour squaring tail of
   confinement failure is `≤ δ`) plus the budget `numHours·δ ≤ η` and the horizon decomposition
   `phase3to5Time = hourLen·numHours`, conclude
   `(K^phase3to5Time) c₀ {¬ ConfinementEvent} ≤ η`.  This is the DISCHARGE the tautological carry
   skipped: it CONSUMES per-hour bricks and PRODUCES the final tail, never assumes it.

2. `mainConfinement_kernel_whp_of_hours` — the re-wired confinement consumer surface.  Same
   conclusion as `ConfinementSurface.mainConfinement_kernel_whp`, but its carried inputs are STRICTLY
   FINER than the final tail: the per-hour squaring events (`hHour`), the hour-boundary clock fact
   (the confined-start `hConf0` — the within-horizon clock-front anchor), and the arithmetic
   (`hHorizon`, `hBudget`).  The final tail is now an OUTPUT, not an input.

3. `confinement_hours_union_from_single` — the convenience form: a single per-hour squaring tail
   constant `δ` (the `ConfinementSurface.confinement_hour_tail` shape `r^hourLen·Φ(c₀)/θ`, uniform
   over confined starts) feeds the union directly.

## Honesty

The per-hour squaring tail itself is the LANDED `ConfinementSurface.confinement_hour_tail`
(= `MainExponentConfinement.main_profile_hour_squaring`, the `WindowConcentration.windowDrift_tail`
engine).  This file does NOT re-prove the single-hour drift; it CHAINS the per-hour tails across the
horizon, which is the piece F1 found missing.  The carried inventory for the confinement chain
becomes: PER-HOUR squaring failure + hour-boundary confined-start anchor + arithmetic — never the
final event bound.

NEW file; no existing file is edited; no sorry/admit/axiom/native_decide.
-/

import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.ConfinementSurface

namespace ExactMajority

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Real BigOperators

namespace HourUnion

variable {L K : ℕ}

open ConfinementSurface (ConfinementEvent)

/-! ## Part 1 — the all-hours union composition (the discharge F1 found missing).

The per-hour squaring tail is the per-WINDOW invariant-failure fact for the invariant
`ConfinementEvent`, at window length `hourLen`.  The union over the `numHours` hours of the
`phase3to5Time = hourLen·numHours` horizon is the LANDED `EarlyDripMarked.checkpoint_composition`
instantiated at `Kk := (NonuniformMajority L K).transitionKernel`, `Inv := ConfinementEvent`,
`w := hourLen`, `KK := numHours`.  No new probability content; the confinement event is plugged into
the existing window-union engine. -/

/-- **The all-hours UNION for the confinement event (audit F1 refinement, the missing discharge).**

From the genuine PER-HOUR bricks:

* `hHour` — each hour, from ANY confinement-satisfying state `x`, the single-hour squaring tail of
  confinement failure is `≤ δ`.  This is the per-window invariant-failure fact: the LANDED
  `ConfinementSurface.confinement_hour_tail` (= `main_profile_hour_squaring`) at the hour window
  length `hourLen`, uniform over confined starts (the hour-boundary chaining condition — confinement
  re-enters each hour from a confined state);
* `hHorizon` — the horizon decomposes into whole hours `phase3to5Time = hourLen · numHours`
  (the hour-boundary clock fact: the Phase-3→5 horizon is `numHours` hours of length `hourLen`);
* `hBudget` — the union budget `numHours · δ ≤ η` (each hour spends `≤ η/numHours`);
* `hConf0` — the start `c₀` satisfies confinement (the within-horizon confined-start anchor),

we DISCHARGE the final event bound
`(K^phase3to5Time) c₀ {c | ¬ ConfinementEvent c} ≤ η`.

This is what `mainConfinement_kernel_whp`'s tautological `hHourTail` carry SKIPPED: the per-hour
tails are COMPOSED across the horizon, not assumed as the final tail.  It mirrors
`WidthPrefix.checkpoint_composition_prefix` (the clock-side per-window chaining) for the
Main-profile hours via `EarlyDripMarked.checkpoint_composition`. -/
theorem confinementEvent_hours_union
    (hourLen numHours phase3to5Time : ℕ) (δ η : ℝ≥0∞) (c₀ : Config (AgentState L K))
    (hHour : ∀ x, ConfinementEvent (L := L) (K := K) x →
      ((NonuniformMajority L K).transitionKernel ^ hourLen) x
        {c | ¬ ConfinementEvent (L := L) (K := K) c} ≤ δ)
    (hHorizon : phase3to5Time = hourLen * numHours)
    (hBudget : (numHours : ℝ≥0∞) * δ ≤ η)
    (hConf0 : ConfinementEvent (L := L) (K := K) c₀) :
    ((NonuniformMajority L K).transitionKernel ^ phase3to5Time) c₀
      {c | ¬ ConfinementEvent (L := L) (K := K) c} ≤ η := by
  -- Rewrite the horizon as a whole number of hours.
  subst hHorizon
  -- The landed checkpoint composition: per-window (= per-hour) failure `δ` from invariant states
  -- unions over `numHours` windows to `≤ numHours · δ` at horizon `hourLen · numHours`.
  have hunion :
      ((NonuniformMajority L K).transitionKernel ^ (hourLen * numHours)) c₀
        {c | ¬ ConfinementEvent (L := L) (K := K) c} ≤ (numHours : ℝ≥0∞) * δ :=
    EarlyDripMarked.checkpoint_composition
      (NonuniformMajority L K).transitionKernel
      (fun c => ConfinementEvent (L := L) (K := K) c)
      hourLen δ hHour numHours c₀ hConf0
  -- Spend the budget: `numHours · δ ≤ η`.
  exact le_trans hunion hBudget

/-! ## Part 2 — the re-wired confinement consumer surface (strictly finer carried set).

`ConfinementSurface.mainConfinement_kernel_whp` carried the FINAL tail `hHourTail` and returned it.
Here is the honest replacement: SAME conclusion, but the inputs are the per-hour squaring events
`hHour`, the hour-boundary clock fact `hHorizon` + confined start `hConf0`, and the arithmetic
`hBudget`.  The final tail is the OUTPUT.  This is the surface the audit asked for — the per-hour
bricks, not the final tail. -/

/-- **Re-wired `mainConfinement_kernel_whp` (audit F1 refinement).**  The honest kernel-level
confinement surface whose carried set is STRICTLY FINER than the final tail: instead of assuming
`hHourTail : (K^phase3to5Time) c₀ {¬ConfinementEvent} ≤ η` (the tautological carry), it consumes the
PER-HOUR squaring events `hHour`, the hour-boundary clock facts (`hHorizon`, `hConf0`), and the
arithmetic `hBudget`, then DISCHARGES the final event bound via the all-hours union.

This is the drop-in replacement for `ConfinementSurface.mainConfinement_kernel_whp`: identical
conclusion, finer carried inventory (the per-hour bricks the dead `let` and the tautological carry
both pretended to deliver). -/
theorem mainConfinement_kernel_whp_of_hours
    (η : ℝ≥0∞) (hourLen numHours phase3to5Time : ℕ) (δ : ℝ≥0∞)
    (c₀ : Config (AgentState L K))
    (hHour : ∀ x, ConfinementEvent (L := L) (K := K) x →
      ((NonuniformMajority L K).transitionKernel ^ hourLen) x
        {c | ¬ ConfinementEvent (L := L) (K := K) c} ≤ δ)
    (hHorizon : phase3to5Time = hourLen * numHours)
    (hBudget : (numHours : ℝ≥0∞) * δ ≤ η)
    (hConf0 : ConfinementEvent (L := L) (K := K) c₀) :
    ((NonuniformMajority L K).transitionKernel ^ phase3to5Time) c₀
      {c | ¬ ConfinementEvent (L := L) (K := K) c} ≤ η :=
  confinementEvent_hours_union (L := L) (K := K)
    hourLen numHours phase3to5Time δ η c₀ hHour hHorizon hBudget hConf0

/-! ## Part 3 — the convenience form from a single per-hour squaring tail constant.

The landed `ConfinementSurface.confinement_hour_tail` gives, per hour from a confined start, the tail
`≤ r^hourLen·Φ(c₀)/θ`.  When this is uniform over confined starts (the squaring drift uses a fixed
potential `Φ` and the absorbing window `Q` contains confinement), the per-hour constant `δ` is the
single object fed to the union.  This wrapper exposes that one-constant entry point. -/

/-- **Hour-union from a single per-hour squaring constant (convenience form).**  Given a SINGLE
per-hour squaring tail constant `δ` valid from every confinement-satisfying state (the uniform
`confinement_hour_tail` shape), the horizon decomposition, the budget, and the confined start, the
confinement-failure tail over the full horizon is `≤ η`.  This is the entry point for a confinement
engine that produces ONE per-hour squaring rate. -/
theorem confinement_hours_union_from_single
    (hourLen numHours phase3to5Time : ℕ) (δ η : ℝ≥0∞) (c₀ : Config (AgentState L K))
    (hHour : ∀ x, ConfinementEvent (L := L) (K := K) x →
      ((NonuniformMajority L K).transitionKernel ^ hourLen) x
        {c | ¬ ConfinementEvent (L := L) (K := K) c} ≤ δ)
    (hHorizon : phase3to5Time = hourLen * numHours)
    (hBudget : (numHours : ℝ≥0∞) * δ ≤ η)
    (hConf0 : ConfinementEvent (L := L) (K := K) c₀) :
    ((NonuniformMajority L K).transitionKernel ^ phase3to5Time) c₀
      {c | ¬ ConfinementEvent (L := L) (K := K) c} ≤ η :=
  confinementEvent_hours_union (L := L) (K := K)
    hourLen numHours phase3to5Time δ η c₀ hHour hHorizon hBudget hConf0

end HourUnion

end ExactMajority
