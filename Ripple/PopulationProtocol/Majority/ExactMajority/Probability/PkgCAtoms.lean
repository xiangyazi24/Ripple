/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Package C atoms — Theorem 6.2 slot-5 entry and A-profile feeder

This file is append-only and edits no existing file.

Deliverables:

* `hmain5_on_confinement_event`: the honest event-conditioned adapter.  On a concrete Phase-5
  config, the phase-3 squaring success event
  `MainExponentConfinement.MainProfileConfinedToUseful` plus the Lemma-5.2 Main-role floor yields
  the exact slot-5 floor `P5 ≤ usefulMains.sum b.count`.
* `hmain5_of_pointwise_confinement`: the exact `WorkInputsV51.hmain5` shape, but explicitly from a
  pointwise success hypothesis on every Phase-5-window config.  This is the sharp pointwise form:
  the landed Theorem-6.2 chain is WHP/event-level, not a proof of universal pointwise confinement.
* `hmain5_bad_event_whp_from_phase3_hours`: the honest WHP production.  The per-hour confinement
  bricks union through `HourUnion.confinementEvent_hours_union`; the bad event for the slot-5
  floor, restricted to configs where the Phase-5 window and Main-role floor hold, is contained in
  the confinement-failure event.
* `mainConfinementProfile_feeder_of_paper`: the package-B feeder
  `MarginLedgers.MainConfinementProfile σ n b` from the paper-faithful `Theorem62Paper` object.

Remainder statement: the exact V51 field
`∀ b, Phase5AllWin n b → P5 ≤ usefulMains.sum b.count` cannot be derived from the landed WHP
kernel event alone without an additional conditioning/success hypothesis at `b`; the WHP theorem
bounds mass of failing configurations, while `FinalAssemblyV2.slot5Honest` consumes a deterministic
per-config floor.
-/

import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.HourUnion
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.TimelineReconciliation
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.PaperRegime

namespace ExactMajority

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace PkgCAtoms

variable {L K : ℕ}

/-- **Package C / field `WorkInputsV51.hmain5`, event-conditioned adapter.**

This is the pointwise consumer adapter for a single Phase-5-window configuration.  It runs the
landed deterministic tail of the phase-3 chain:

`TimelineReconciliation.confine3_served_by_phase3_squaring`
`→ UsefulMainFloor.theorem6_2_usefulMains_floor`.

It does not claim that the WHP confinement event holds at every `b`; it consumes the success event
at this `b`. -/
theorem hmain5_on_confinement_event {n P5 : ℕ}
    (hP5 : (P5 : ℝ) ≤ (23 : ℝ) * (n : ℝ) / 75)
    (b : Config (AgentState L K))
    (hPhase5 : ReserveSampling.Phase5AllWin (L := L) (K := K) n b)
    (hMainFloor : (n : ℝ) / 3 ≤ (RoleSplitConcentration.mainCount (L := L) (K := K) b : ℝ))
    (hConf : MainExponentConfinement.MainProfileConfinedToUseful (L := L) (K := K) b) :
    P5 ≤ (Phase5Convergence.usefulMains (L := L) (K := K)).sum b.count :=
  UsefulMainFloor.theorem6_2_usefulMains_floor
    (TimelineReconciliation.confine3_served_by_phase3_squaring (L := L) (K := K)
      hPhase5 hMainFloor hConf) P5 hP5

/-- **Package C / exact field producer for `WorkInputsV51.hmain5`.**

This theorem produces the exact field shape

`∀ b, Phase5AllWin n b → P5 ≤ usefulMains.sum b.count`.

The required extra input is exactly the pointwise form missing from the WHP confinement theorem:
every Phase-5-window config must satisfy the phase-3 squaring success event. -/
theorem hmain5_of_pointwise_confinement {n P5 : ℕ}
    (hP5 : (P5 : ℝ) ≤ (23 : ℝ) * (n : ℝ) / 75)
    (hMainFloor : ∀ b : Config (AgentState L K),
      ReserveSampling.Phase5AllWin (L := L) (K := K) n b →
        (n : ℝ) / 3 ≤ (RoleSplitConcentration.mainCount (L := L) (K := K) b : ℝ))
    (hConf : ∀ b : Config (AgentState L K),
      ReserveSampling.Phase5AllWin (L := L) (K := K) n b →
        MainExponentConfinement.MainProfileConfinedToUseful (L := L) (K := K) b) :
    ∀ b : Config (AgentState L K), ReserveSampling.Phase5AllWin (L := L) (K := K) n b →
      P5 ≤ (Phase5Convergence.usefulMains (L := L) (K := K)).sum b.count := by
  intro b hb
  exact hmain5_on_confinement_event (L := L) (K := K) hP5 b hb (hMainFloor b hb) (hConf b hb)

/-- The event whose mass is honestly controlled by the phase-3 confinement WHP theorem when slot 5
needs the deterministic `hmain5` floor.  The event is restricted to configs where the deterministic
side conditions available to the slot are true; on those configs, failure of the `P5` floor implies
failure of the phase-3 confinement event. -/
def Slot5MainFloorBad (n P5 : ℕ) : Set (Config (AgentState L K)) :=
  {b |
    ReserveSampling.Phase5AllWin (L := L) (K := K) n b ∧
    (n : ℝ) / 3 ≤ (RoleSplitConcentration.mainCount (L := L) (K := K) b : ℝ) ∧
    ¬ P5 ≤ (Phase5Convergence.usefulMains (L := L) (K := K)).sum b.count}

/-- **Package C / WHP event-conditioned slot-5 floor.**

If the phase-3 confinement failure event has kernel mass at most `η`, then the bad event for the
slot-5 `hmain5` floor, restricted to the Phase-5 window plus Main-role floor, also has mass at most
`η`.  This is the honest kernel-level replacement for trying to manufacture a universal pointwise
`hmain5` from a WHP statement. -/
theorem hmain5_bad_event_whp_from_confinement {n P5 phase3to5Time : ℕ}
    {η : ℝ≥0∞} {c₀ : Config (AgentState L K)}
    (hP5 : (P5 : ℝ) ≤ (23 : ℝ) * (n : ℝ) / 75)
    (hTail :
      ((NonuniformMajority L K).transitionKernel ^ phase3to5Time) c₀
        {b | ¬ MainExponentConfinement.MainProfileConfinedToUseful (L := L) (K := K) b} ≤ η) :
    ((NonuniformMajority L K).transitionKernel ^ phase3to5Time) c₀
      (Slot5MainFloorBad (L := L) (K := K) n P5) ≤ η := by
  refine le_trans (measure_mono ?_) hTail
  intro b hb
  simp only [Slot5MainFloorBad, Set.mem_setOf_eq] at hb
  simp only [Set.mem_setOf_eq]
  intro hConf
  exact hb.2.2 (hmain5_on_confinement_event (L := L) (K := K) hP5 b hb.1 hb.2.1 hConf)

/-- **Package C / full hour-union WHP route to the slot-5 bad-event bound.**

This wires the landed phase-3 chain at the event level:

`HourUnion.confinementEvent_hours_union`
`→ hmain5_bad_event_whp_from_confinement`.

The per-hour hypothesis `hHour` is the output shape fed by the single-hour squaring bricks
(`MainExponentConfinement.main_profile_hour_squaring` /
`ConfinementSurface.confinement_hour_tail`). -/
theorem hmain5_bad_event_whp_from_phase3_hours {n P5 hourLen numHours phase3to5Time : ℕ}
    {δ η : ℝ≥0∞} {c₀ : Config (AgentState L K)}
    (hP5 : (P5 : ℝ) ≤ (23 : ℝ) * (n : ℝ) / 75)
    (hHour : ∀ x, ConfinementSurface.ConfinementEvent (L := L) (K := K) x →
      ((NonuniformMajority L K).transitionKernel ^ hourLen) x
        {b | ¬ ConfinementSurface.ConfinementEvent (L := L) (K := K) b} ≤ δ)
    (hHorizon : phase3to5Time = hourLen * numHours)
    (hBudget : (numHours : ℝ≥0∞) * δ ≤ η)
    (hConf0 : ConfinementSurface.ConfinementEvent (L := L) (K := K) c₀) :
    ((NonuniformMajority L K).transitionKernel ^ phase3to5Time) c₀
      (Slot5MainFloorBad (L := L) (K := K) n P5) ≤ η := by
  have hTail :
      ((NonuniformMajority L K).transitionKernel ^ phase3to5Time) c₀
        {b | ¬ MainExponentConfinement.MainProfileConfinedToUseful (L := L) (K := K) b} ≤ η := by
    simpa [ConfinementSurface.ConfinementEvent] using
      HourUnion.confinementEvent_hours_union (L := L) (K := K)
        hourLen numHours phase3to5Time δ η c₀ hHour hHorizon hBudget hConf0
  exact hmain5_bad_event_whp_from_confinement (L := L) (K := K) hP5 hTail

/-- **Package C / package-B feeder: `MainConfinementProfile σ n b`.**

This is the A-shape profile (`hMainFloor`, `hUseful`, `hMinoritySmall`) consumed downstream.  It is
produced from the paper-faithful Theorem-6.2 object, which carries the sign-specific majority band
and minority-small facts that the broad useful-Main confinement event alone does not contain. -/
theorem mainConfinementProfile_feeder_of_paper {σ : Sign} {l n : ℕ}
    (hl : l + 2 < L + 1) {b : Config (AgentState L K)}
    (hP : PaperRegime.Theorem62Paper (L := L) (K := K) σ l hl n b) :
    MarginLedgers.MainConfinementProfile (L := L) (K := K) σ n b :=
  PaperRegime.mainConfinementProfile_of_paper (L := L) (K := K) hl hP

end PkgCAtoms

end ExactMajority
