/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# `ClockSidePrefix` — the deterministic side-prefix backbone (Holes 4/5 of the C-A route).

`ClockUnconditional.clock_real_faithful_O_log_n_unconditional` (the capstone) leaves the per-minute
side prefixes `∑_τ (realκ^τ) c₀ (Sgood n mC T)ᶜ` UN-bounded; `ClockUnconditional.sidePrefix_le`
reduces each to `εQ + εfloor + εsync + εphase` from four named feeders.  This file supplies the
DETERMINISTIC backbone that routes three of those feeders to a SINGLE genuine probabilistic input —
the structural first-exit mass `(realκ^τ) c₀ {¬ HabsGood} ≤ εH` (the front-shape / FrontSync
concentration, discharged by the Layer-B window transfer + ghost concentrations).

* `sync_phase_le_of_habsGood_exit` — `{SyncFail} ∪ {PhaseGateFail} = {¬ HabsGood}` exactly
  (`HabsGood` is the five structural conjuncts), so BOTH the `hsync` and `hphase` feeders are bounded
  by the one structural-exit mass.  PURE LOGIC; no probabilistic content; zero coupling to Layer-B.
* `habsGood_step_closed_or_syncFail` — the DETERMINISTIC one-step closure: on a `Q_mix` window,
  `HabsGood` is one-step closed UNLESS `FrontSync` fails at the successor.  This is the deterministic
  half of `FrontSyncConc.frontSync_union_horizon`'s `hstep` (Good = `HabsGood`, W carries `Q_mix`);
  it reuses the three proven closures (`allPhaseGE3_closed`, `noPhaseAbove3_closed_of_frontSync`,
  `counterPos_closed_of_frontSync`).  The per-step exit RATE (the union lemma's `qE` / `hseed`)
  is the genuine probabilistic input, NOT proven here.
* `qmixFail_subset` — `QmixFail ⊆ {card≠n} ∪ {clockCount≠mC} ∪ {¬crossedT} ∪ {¬ HabsGood}`: the
  `Q_mix` window failure splits into the two conserved-quantity invariants (deterministic from the
  start), the seed/width `crossedT` 0.9-floor (the FloorFail-class progress), and the structural
  exit (shared with sync/phase, via `clockPhase3 ⟸ allPhaseGE3 ∧ noPhaseAbove3`).

NO false ∀c: every statement is either pure set logic or a one-step closure on the actual support.
NEW file; no existing file edited; no sorry/admit/axiom/native_decide.
Reference: Doty et al. (arXiv:2106.10201v2) §6; `DOCTRINE_THM69_CA.md` Holes 4/5, Round 6.
-/

import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.ClockUnconditional
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.PhaseGatesPrefix

namespace ExactMajority

namespace ClockSidePrefix

open ClockUnconditional ClockRealKernel ClockRealMixed HabsDischarge ClockFrontShape
open PhaseGatesPrefix ClockKilledMinute
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

variable {L K : ℕ}

/-! ## Part 1 — the structural-exit feeder for `hsync` and `hphase` (pure logic). -/

/-- **`SyncFail ⊆ {¬ HabsGood}`.**  `FrontSync` is the fourth `HabsGood` conjunct. -/
theorem syncFail_subset_not_habsGood :
    SyncFail (L := L) (K := K) ⊆ {c | ¬ HabsGood (L := L) (K := K) c} := by
  intro c hc hG
  exact hc hG.2.2.2.1

/-- **`{PhaseGateFail} ⊆ {¬ HabsGood}`.**  Each phase-gate disjunct contradicts the corresponding
`HabsGood` conjunct. -/
theorem phaseGateFail_subset_not_habsGood :
    {c | PhaseGateFail (L := L) (K := K) c} ⊆ {c | ¬ HabsGood (L := L) (K := K) c} := by
  intro c hc hG
  rcases hc with h | h | h | h
  · exact h hG.1
  · exact h hG.2.1
  · exact h hG.2.2.1
  · exact h hG.2.2.2.2

/-- **`hsync` and `hphase` from the single structural first-exit mass.**  Given the per-`τ`
structural-exit bound `(realκ^τ) c₀ {¬ HabsGood} ≤ εH`, BOTH `sidePrefix_le` feeders are `≤ εH`.
This collapses the SyncFail and PhaseGateFail obligations to ONE genuine probabilistic input. -/
theorem sync_phase_le_of_habsGood_exit (τ : ℕ) (c₀ : Config (AgentState L K)) (εH : ℝ≥0∞)
    (hH : (realκ L K ^ τ) c₀ {c | ¬ HabsGood (L := L) (K := K) c} ≤ εH) :
    (realκ L K ^ τ) c₀ (SyncFail (L := L) (K := K)) ≤ εH ∧
      (realκ L K ^ τ) c₀ {c | PhaseGateFail (L := L) (K := K) c} ≤ εH :=
  ⟨le_trans (measure_mono syncFail_subset_not_habsGood) hH,
   le_trans (measure_mono phaseGateFail_subset_not_habsGood) hH⟩

/-! ## Part 2 — the deterministic one-step closure (the `hstep` core). -/

/-- **`HabsGood` is one-step closed on a `Q_mix` window, unless `FrontSync` fails at the successor.**
This is the DETERMINISTIC half of `frontSync_union_horizon`'s `hstep` with `Good = HabsGood`,
`W ⊇ Q_mix`.  Reuses `allPhaseGE3_closed` (unconditional), `noPhaseAbove3_closed_of_frontSync`,
and `counterPos_closed_of_frontSync` (the `Q_mix` slot is supplied by `W`).  Whenever the produced
config is still `FrontSync`, every gate closes and `HabsGood` is maintained; otherwise the produced
config is a `FrontSync` first-exit (`¬ HabsGood` via its `FrontSync` conjunct). -/
theorem habsGood_step_closed_or_syncFail {n mC T : ℕ} (c c' : Config (AgentState L K))
    (hG : HabsGood (L := L) (K := K) c) (hQ : Q_mix (L := L) (K := K) n mC T c)
    (hc' : c' ∈ ((NonuniformMajority L K).stepDistOrSelf c).support) :
    HabsGood (L := L) (K := K) c' ∨ ¬ FrontSync (L := L) (K := K) c' := by
  obtain ⟨hge, hno, hpos, hsync, _hsucc⟩ := hG
  by_cases hs' : FrontSync (L := L) (K := K) c'
  · left
    have hge' := allPhaseGE3_closed (L := L) (K := K) c c' hge hc'
    have hno' := noPhaseAbove3_closed_of_frontSync (L := L) (K := K) c c' hge hno hsync hc'
    have hpos' := counterPos_closed_of_frontSync (L := L) (K := K) n mC T c c'
      hQ hge hno hpos hsync hc'
    refine ⟨hge', hno', hpos', hs', ?_⟩
    intro c'' hc''
    exact noPhaseAbove3_closed_of_frontSync (L := L) (K := K) c' c'' hge' hno' hs' hc''
  · exact Or.inr hs'

/-! ## Part 3 — the `QmixFail` deterministic decomposition (the `hQ` feeder). -/

/-- **`QmixFail ⊆ {card≠n} ∪ {clockCount≠mC} ∪ {¬crossedT} ∪ {¬ HabsGood}`.**  The `Q_mix` window
failure splits into the two conserved-quantity invariants (`card`, `clockSize` — deterministic from
the start), the seed/width 0.9-floor `crossedT` (the FloorFail-class progress at level `T`), and the
structural exit (`clockPhase3 ⟸ allPhaseGE3 ∧ noPhaseAbove3`, i.e. every clock at phase exactly 3).
So `εQ ≤ εcard + εclockSize + εcrossedT + εH`, with `εcard = εclockSize = 0` from the invariants and
`εH` shared with the sync/phase feeders. -/
theorem qmixFail_subset {n mC T : ℕ} :
    QmixFail (L := L) (K := K) n mC T ⊆
      ((({c : Config (AgentState L K) | c.card ≠ n}
          ∪ {c | clockCount (L := L) (K := K) c ≠ mC})
        ∪ {c | ¬ (9 * mC / 10 ≤ rBeyond (L := L) (K := K) T c)})
        ∪ {c | ¬ HabsGood (L := L) (K := K) c}) := by
  intro c hc
  by_contra hnin
  simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_not] at hnin
  obtain ⟨⟨⟨hcard, hclk⟩, hcross⟩, hG⟩ := hnin
  -- Reconstruct `Q_mix` from the four un-failed pieces: `clockPhase3` comes from `HabsGood`.
  exact hc
    { card := hcard
      clockPhase3 := fun a ha hrole => le_antisymm (hG.2.1 a ha) (hG.1 a ha)
      clockSize := hclk
      crossedT := hcross }

/-! ## Part 4 — the side-prefix SUM (the capstone's per-minute side cost). -/

/-- **`sidePrefix_sum_le` — the summed side-prefix bound.**  The capstone
`ClockUnconditional.clock_real_faithful_O_log_n_unconditional` leaves per-minute side costs
`∑_{τ} (realκ^τ) c₀ (Sgood n mC T)ᶜ`.  Summing `ClockUnconditional.sidePrefix_le` over the prefix
`Finset` bounds it by the summed four feeders.  The per-`τ` feeders are: `εfloor` from
`FloorFailAdapter.FloorFail_horizon_le`; `εsync`/`εphase` BOTH from the structural first-exit via
`sync_phase_le_of_habsGood_exit`; `εQ` from `qmixFail_subset` (invariants + `crossedT` + structural).
This is the mechanical item-6 assembly step; the only genuine probabilistic inputs are the per-`τ`
feeder values, supplied by the seed engine (`εfloor`, `εQ`-`crossedT`) and Layer-B/Layer-D
(`εsync`/`εphase` structural exit). -/
theorem sidePrefix_sum_le (n mC T : ℕ) (c₀ : Config (AgentState L K))
    (S : Finset ℕ) (εQ εfloor εsync εphase : ℕ → ℝ≥0∞)
    (hQ : ∀ τ ∈ S, (realκ L K ^ τ) c₀ (QmixFail (L := L) (K := K) n mC T) ≤ εQ τ)
    (hfloor : ∀ τ ∈ S, (realκ L K ^ τ) c₀ (FloorFail (L := L) (K := K) mC T) ≤ εfloor τ)
    (hsync : ∀ τ ∈ S, (realκ L K ^ τ) c₀ (SyncFail (L := L) (K := K)) ≤ εsync τ)
    (hphase : ∀ τ ∈ S,
      (realκ L K ^ τ) c₀ {c | PhaseGateFail (L := L) (K := K) c} ≤ εphase τ) :
    ∑ τ ∈ S, (realκ L K ^ τ) c₀ (Sgood (L := L) (K := K) n mC T)ᶜ
      ≤ ∑ τ ∈ S, (εQ τ + εfloor τ + εsync τ + εphase τ) :=
  Finset.sum_le_sum (fun τ hτ =>
    ClockUnconditional.sidePrefix_le (L := L) (K := K) n mC T τ c₀
      (εQ τ) (εfloor τ) (εsync τ) (εphase τ)
      (hQ τ hτ) (hfloor τ hτ) (hsync τ hτ) (hphase τ hτ))

end ClockSidePrefix

end ExactMajority
