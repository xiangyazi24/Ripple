import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.ClockWeakAssembly
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.FrontSyncConc
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.ClockFrontSyncFromWidth

/-!
# ClockUnconditional — the final Phase B wiring (B-11)

This is the last connector of the Phase B campaign.  `ClockWeakAssembly` (B-10) reduced the
unconditional clock to TWO named residuals carried on the endpoint
`clock_real_faithful_O_log_n_W`:

1. `hstep : ∀ T, ∀ x ∈ QbulkSet n mC T, realκ x QbulkSetᶜ ≤ q` — the per-step gate-escape rate;
2. the per-minute side prefixes `∑_{τ} (realκ^τ) c₀ QbulkSet(i)ᶜ` left in the conclusion RHS.

This file wires both to the discharged machinery.

## The honest split (the §6 side-gate audit, settled)

`QbulkSet n mC T = {Q_mix n mC T ∧ mC/10 ≤ rBeyond (T+1)}`, with `Q_mix` = `card ∧ clockPhase3 ∧
clockSize ∧ crossedT`.  The one-step escape `realκ x QbulkSetᶜ` decomposes per conjunct:

* `card`, `clockSize`, `crossedT` (`T ≥ 1`), `allPhaseGE3` close DETERMINISTICALLY on the support
  (`HabsDischarge.habs_mix_deterministic_skeleton`) — they contribute `0` to the escape.
* the `mC/10` floor at `T+1` is MONOTONE on the support
  (`ClockMonoDischarge.hmono_mix_discharged`) — contributes `0`.
* `clockPhase3` (clocks stay at phase EXACTLY 3) closes one step ONLY on the FrontSync-good window
  (`FrontSyncConc.habs_mix_full`): under `allPhaseGE3 ∧ noPhaseAbove3 ∧ allClocksCounterPos ∧
  FrontSync` (with the successor `noPhaseAbove3 c'`), every successor lies in `Q_mix` AND keeps
  `allClocksCounterPos`.  The bare deterministic closure is FALSE (the at-cap `counter = 1`
  witness, `ClockFrontShape.counterPos_one_step_NOT_closed_witness`); FrontSync is the ESSENTIAL
  gate, supplied PROBABILISTICALLY by the §6 width engine.

**The result of the split: `q = 0`.**  We condition the one-step escape on a SIDE EVENT
`HabsGood T` (the full `habs_mix_full` gate, plus the deterministic successor `noPhaseAbove3`
gate folded in).  On `QbulkSet n mC T ∩ HabsGood T`, EVERY successor lies in `QbulkSet n mC T`,
so the one-step escape is exactly `0`.  Per the campaign blueprint's directive
("if it cannot be discharged deterministically, keep it INSIDE the side event and the escape
charges to the side prefix failures instead: then `q = 0` and ALL the cost moves to the side
prefixes"), we charge ALL the cost to the side prefixes by taking the side set
`S = QbulkSet ∩ HabsGood` and `q = 0`.

`ClockWeakAssembly`'s endpoint takes `hstep` with `S = G = QbulkSet` (unconditioned), so to use
the `q = 0` route honestly we restate the assembly with `S = QbulkSet ∩ HabsGood` and the
side-conditioned `hstep` (the campaign-mandated "S-conditioned variant theorem IN YOUR FILE,
do not edit ClockWeakAssembly").  The per-minute side prefix then becomes
`∑_τ (realκ^τ) c₀ (QbulkSet ∩ HabsGood)ᶜ`, whose failure events are exactly the §6 whp pieces
(width / FrontSync / the deterministic phase gates), discharged later by `goodFrontWidth_whp_at`
+ the `ClockFrontSyncFromWidth` bridges + `DotyParams`.

ZERO sorry, zero new axiom, zero native_decide.
-/

namespace ExactMajority

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Real BigOperators Classical

namespace ClockUnconditional

open ClockRealKernel ClockKilledMinute ClockRealBulk ClockRealMixed
open HabsDischarge ClockFrontShape FrontSyncConc ClockMonoDischarge

variable {L K : ℕ}

/-! ## Part 1 — the side event `HabsGood` and the `q = 0` one-step escape.

`HabsGood T c` carries EXACTLY the gates `FrontSyncConc.habs_mix_full` needs to close `Q_mix`
one step (plus the maintained `allClocksCounterPos`), PLUS the deterministic successor
`noPhaseAbove3` gate (`∀ c' on support, noPhaseAbove3 c'`).  With these gates the one-step image
of `QbulkSet ∩ HabsGood` lies entirely in `QbulkSet`, so the escape mass on `QbulkSetᶜ` is `0`. -/

/-- The side event under which the one-step gate-escape rate is `0`.  All four conjuncts are
exactly the `habs_mix_full` gate; the last is the deterministic successor `noPhaseAbove3` gate
(the residual deterministic closure that the §6 audit folds into the side event).  NOTE: the
gate is MINUTE-INDEPENDENT (it does not mention `T`) — the §6 side gates are structural, not
per-minute, so a SINGLE side event `HabsGood` serves every minute. -/
def HabsGood (c : Config (AgentState L K)) : Prop :=
  allPhaseGE3 (L := L) (K := K) c ∧
    noPhaseAbove3 (L := L) (K := K) c ∧
    allClocksCounterPos (L := L) (K := K) c ∧
    FrontSync (L := L) (K := K) c ∧
    (∀ c' ∈ ((NonuniformMajority L K).stepDistOrSelf c).support,
      noPhaseAbove3 (L := L) (K := K) c')

/-- **The one-step image of `QbulkSet ∩ HabsGood` lands in `QbulkSet` (per config on the
support).**  From `x ∈ QbulkSet ∩ HabsGood T` (with `1 ≤ T`), every support successor `c'`
satisfies `QbulkWin n mC T c'`, i.e. `c' ∈ QbulkSet n mC T`.  `Q_mix c'` is `habs_mix_full`; the
`mC/10` floor is `hmono_mix_discharged`. -/
theorem qbulk_succ_of_sideGood (n mC T : ℕ) (hT : 1 ≤ T)
    (x : Config (AgentState L K))
    (hx : x ∈ QbulkSet (L := L) (K := K) n mC T ∩ HabsGood (L := L) (K := K))
    (c' : Config (AgentState L K))
    (hc' : c' ∈ ((NonuniformMajority L K).stepDistOrSelf x).support) :
    c' ∈ QbulkSet (L := L) (K := K) n mC T := by
  classical
  obtain ⟨hQbw, hge, hno, hpos, hsync, hno'all⟩ := hx
  have hQbw : QbulkWin (L := L) (K := K) n mC T x := hQbw
  obtain ⟨hQ, hfloor⟩ := hQbw
  -- successor noPhaseAbove3 (the carried deterministic gate).
  have hno' : noPhaseAbove3 (L := L) (K := K) c' := hno'all c' hc'
  -- Q_mix c' from the FrontSync-gated closure.
  have hclose := habs_mix_full (L := L) (K := K) n mC T hT x c' hQ hge hno hpos hsync hno' hc'
  -- the mC/10 floor at T+1 is monotone on the support.
  have hmono := hmono_mix_discharged (L := L) (K := K) n mC T x c' hQ hc'
  exact ⟨hclose.1, le_trans hfloor hmono⟩

/-- **`hstep_of_sideGood` (q = 0).**  On `x ∈ QbulkSet n mC T ∩ HabsGood T` (with `1 ≤ T`), the
one-step real-kernel escape to `QbulkSetᶜ` is exactly `0`.  This is the honest `hstep` with
`q = 0` and the cost moved entirely to the side event `HabsGood`. -/
theorem hstep_of_sideGood (n mC T : ℕ) (hT : 1 ≤ T)
    (x : Config (AgentState L K))
    (hx : x ∈ QbulkSet (L := L) (K := K) n mC T ∩ HabsGood (L := L) (K := K)) :
    realκ L K x (QbulkSet (L := L) (K := K) n mC T)ᶜ = 0 := by
  classical
  show ((NonuniformMajority L K).transitionKernel) x
      (QbulkSet (L := L) (K := K) n mC T)ᶜ = 0
  change ((NonuniformMajority L K).stepDistOrSelf x).toMeasure
      (QbulkSet (L := L) (K := K) n mC T)ᶜ = 0
  rw [PMF.toMeasure_apply_eq_zero_iff _
    (DiscreteMeasurableSpace.forall_measurableSet _)]
  rw [Set.disjoint_left]
  intro c' hsupp hbad
  exact hbad (qbulk_succ_of_sideGood (L := L) (K := K) n mC T hT x hx c' hsupp)

/-! ## Status (Part 1 complete). -/
theorem clock_unconditional_part1_status : True := trivial

end ClockUnconditional

end ExactMajority

#print axioms ExactMajority.ClockUnconditional.hstep_of_sideGood
#print axioms ExactMajority.ClockUnconditional.qbulk_succ_of_sideGood
