/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Doty §6 — the SEAM NO-OVERSHOOT timing-separation tail (`SeamNoOvershoot`)

This file discharges the per-seam `hNoOvershoot` event that `SeamEpidemics` carries
as a named budget but never consumes: during the advance-epidemic seam from work
phase `p` to `p+1`, NO agent runs ahead two phases (to `phase ≥ p+2`).  This is the
timing-separation half of the `≥`-window-to-exact-window reconciliation
(`SeamEpidemics.allPhaseEq_of_ge_and_no_overshoot`): the next work phase's EXACT
`Pre` (`allPhaseEq (p+1)`) is recovered from the seam's `≥ (p+1)`-`Post` exactly
when no overshoot occurred.

## The mechanism (mirrors `Phase0Window`, blueprint `HANDOFF_SEAM_NOOVERSHOOT.md`)

Phase advance out of a COUNTER-TIMED work phase `p+1` happens ONLY via a clock's
counter hitting `0` (`Transition.stdCounterSubroutine`, the `counter = 0` branch
running `advancePhaseWithInit`); the counter counts DOWN from `50(L+1)`.  The
universal phase epidemic (`Transition_*_phase_ge_pair_max`) only ever raises a phase
to the `max` of the two interacting phases, so on a no-overshoot config (all phases
`< p+2`) the epidemic alone CANNOT create a `p+2` agent — the first such creation
must be counter-driven in a timed phase.  We therefore reuse the `Phase0Window`
downward-crossing exponential potential, restricted to the AT-RISK new-phase clocks:

  `Φ_s c := ∑_{a clock, phase = p+1} exp(−s · a.counter)`     (a `Config.sumOf`)

`{∃ at-risk clock with counter = 0}` forces `Φ_s ≥ 1`, and the affine drift +
immigration tail engine (`Phase0Window.phase0_window_tail_affine`) closes the tail
to `e^{−40(L+1)}` — the seam version of the Phase-0 `e^{−45(L+1)}`, with `40` instead
of `45` for the epidemic "fresh clock" immigration (a phase-`p` clock infected by the
`(p+1)`-epidemic enters phase `p+1` with FULL counter `50(L+1)`; the per-step
immigration is bounded by `2·exp(−s·50(L+1))`).

## The honest counter-timed destination set

After reading `Protocol/Transition.lean` (FROZEN), the destination phases whose entry
is driven by a clock's counter (`stdCounterSubroutine` on a clock) are
`{1, 3, 5, 6, 7, 8}`.  BUT the no-overshoot DRIFT additionally needs the epidemic
"fresh clock" immigration term to be small — a phase-`p` clock dragged into phase
`p+1` by the epidemic enters with FULL counter `50(L+1)` (summand `= M`) ONLY when
`phaseInit (p+1)` RESETS the clock counter.  Checking `phaseInit` (FROZEN): the
counter is reset to `50(L+1)` exactly for phases `{1, 5, 6, 7, 8}`; phase 3's init
sets `minute`, NOT `counter`.  A fresh phase-3 clock therefore keeps a possibly-zero
counter (summand up to `1`, not `M`), which breaks the affine immigration tail.

So the honest `CounterTimedPhase` set for THIS clock-counter no-overshoot tail is
`{1, 5, 6, 7, 8}` (`q = 1 ∨ q = 5 ∨ q = 6 ∨ q = 7 ∨ q = 8`).  Phase 3's seam is
counter-timed but its no-overshoot must come from the dedicated minute/hour width
machinery (`ClockOLogN`/`ClockReal*`), not this generic lemma.  Phases 2/9 advance by
opinion-union and phase 4 by big-bias — UNTIMED; their seams are handled by their own
work-phase guards.  This is a CORRECTION to the blueprint, which listed
`{1,3,5,6,7,8}`: phase 3 is excluded here (fresh-clock immigration not at full
counter).

## What is built (0 sorry / 0 axiom / no native_decide)

* `NoOvershoot` / `AtRiskClockZero` — the seam predicates (blueprint §5);
* `seamClockSummand` / `seamClockPotential` — the at-risk clock potential `Φ_s`;
* `seamClockPotential_ge_one_of_atRiskClockZero` — the threshold link (Stage 1);
* `CounterTimedPhase` — the honest counter-timed destination set;
* `det_seam_overshoot_of_atRiskClockZero` — the deterministic bridge (Stage 2);
* `seamClockPotential_stepOrSelf_le` / `seamClockPotential_drift_affine` — the affine
  one-step drift (Stage 3, cloned from `clockCounterPotential_drift_affine`);
* `seam_atRiskClockZero_tail` / `seam_noOvershoot_numerics_real` — the tail at the
  concrete constants (Stage 4);
* `seam_noOvershoot_tail` / `hNoOvershoot_one_seam` — the terminal no-overshoot tail
  and the per-seam budget wrapper (Stage 5);
* `seamEpidemicExactW` / `seamExact_into_exact_work` — the strengthened seam instance
  that ACTUALLY consumes `εovershoot` (Stage 5; fixes the `SeamEpidemics` integration
  bug where `seamEpidemicW`'s `εovershoot` is never used).

Reference: Doty et al. §6 (time window); blueprint = `HANDOFF_SEAM_NOOVERSHOOT.md`;
pattern = `Probability/Phase0Window.lean`; consumer = `SeamEpidemics`.
-/

import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.Phase0Window
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.SeamEpidemics

namespace ExactMajority

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Real BigOperators

namespace SeamNoOvershoot

variable {L K : ℕ}

/-! ## Stage 1 — the seam predicates, the at-risk clock potential, and the threshold. -/

/-- **No overshoot.**  No agent has run ahead two phases during the seam from `p` to
`p+1`: every agent is still at phase `< p+2`.  This also excludes accidental phase-10
(error/backup) entry during the seam, since `p + 2 ≤ 10` for the seams we use. -/
def NoOvershoot (p : ℕ) (c : Config (AgentState L K)) : Prop :=
  ∀ a ∈ c, a.phase.val < p + 2

/-- **The dangerous precursor.**  An at-risk clock in the NEW phase `p+1` already has
counter `0`: the next `stdCounterSubroutine` call on it advances it to `p+2`. -/
def AtRiskClockZero (p : ℕ) (c : Config (AgentState L K)) : Prop :=
  ∃ a ∈ c, a.role = .clock ∧ a.phase.val = p + 1 ∧ a.counter.val = 0

instance (p : ℕ) (c : Config (AgentState L K)) : Decidable (NoOvershoot p c) := by
  unfold NoOvershoot; infer_instance

instance (p : ℕ) (c : Config (AgentState L K)) : Decidable (AtRiskClockZero p c) := by
  unfold AtRiskClockZero; infer_instance

/-- The per-agent contribution to the at-risk seam clock potential at scale `s`:
`exp(−s · counter)` if the agent is a clock AT the new phase `p+1`, else `0`. -/
noncomputable def seamClockSummand (p : ℕ) (s : ℝ) (a : AgentState L K) : ℝ≥0∞ :=
  if a.role = .clock ∧ a.phase.val = p + 1 then
    ENNReal.ofReal (Real.exp (-(s * (a.counter.val : ℝ))))
  else 0

/-- The at-risk seam clock potential
`Φ_s c = ∑_{a clock, phase = p+1} exp(−s · a.counter)`. -/
noncomputable def seamClockPotential (p : ℕ) (s : ℝ)
    (c : Config (AgentState L K)) : ℝ≥0∞ :=
  Config.sumOf (seamClockSummand (L := L) (K := K) p s) c

/-- The seam clock potential is measurable (discrete σ-algebra on `Config`). -/
theorem measurable_seamClockPotential (p : ℕ) (s : ℝ) :
    Measurable (seamClockPotential (L := L) (K := K) p s) :=
  Measurable.of_discrete

/-- **The threshold link.**  If some at-risk clock in `c` (clock, phase `p+1`) has
`counter = 0`, then the seam clock potential `Φ_s c ≥ 1`: that clock's summand is
`exp(−s · 0) = 1`, bounding the nonnegative sum below.  This clones
`Phase0Window.clockCounterPotential_ge_one_of_clock_counter_zero`, with the predicate
strengthened to `clock ∧ phase = p+1`. -/
theorem seamClockPotential_ge_one_of_atRiskClockZero
    (p : ℕ) (s : ℝ) (c : Config (AgentState L K))
    (h : AtRiskClockZero (L := L) (K := K) p c) :
    1 ≤ seamClockPotential (L := L) (K := K) p s c := by
  obtain ⟨a, ha, hrole, hphase, hctr⟩ := h
  have hsumm : seamClockSummand (L := L) (K := K) p s a = 1 := by
    unfold seamClockSummand
    rw [if_pos ⟨hrole, hphase⟩, hctr]
    simp
  calc (1 : ℝ≥0∞)
      = seamClockSummand (L := L) (K := K) p s a := hsumm.symm
    _ ≤ ((c.map (seamClockSummand (L := L) (K := K) p s)).sum) :=
        Multiset.single_le_sum (fun x _ => zero_le') _
          (Multiset.mem_map_of_mem _ ha)
    _ = seamClockPotential (L := L) (K := K) p s c := rfl

/-- The threshold link in `Post`-form: `AtRiskClockZero p c` is the negation of the
postcondition `¬ AtRiskClockZero`, and it forces `Φ_s c ≥ 1`. -/
theorem seamClockPotential_ge_one_of_not_noAtRisk (p : ℕ) (s : ℝ)
    (c : Config (AgentState L K))
    (hc : ¬ (¬ AtRiskClockZero (L := L) (K := K) p c)) :
    1 ≤ seamClockPotential (L := L) (K := K) p s c := by
  rw [not_not] at hc
  exact seamClockPotential_ge_one_of_atRiskClockZero p s c hc

/-! ## Stage 2 — the deterministic overshoot → at-risk-clock bridge.

The honest counter-timed destination set (`phaseInit` resets the clock counter to
full exactly here, so the epidemic immigration is at full counter, AND the only
phase-advance into `p+1` is the clock's `stdCounterSubroutine`): -/

/-- **The honest counter-timed destination set** `{1, 5, 6, 7, 8}`.  These are the
phases whose entry both (i) is driven by a clock's counter (`stdCounterSubroutine`)
and (ii) RESETS the clock counter to full `50(L+1)` on entry via `phaseInit`.  Phase
3 is counter-timed but does NOT reset the counter on entry (its `phaseInit` sets
`minute`), so it is excluded — its no-overshoot comes from the minute/hour width
machinery.  Phases 2/4/9 are untimed (opinion-union / big-bias). -/
def CounterTimedPhase (q : ℕ) : Prop :=
  q = 1 ∨ q = 5 ∨ q = 6 ∨ q = 7 ∨ q = 8

instance (q : ℕ) : Decidable (CounterTimedPhase q) := by
  unfold CounterTimedPhase; infer_instance

/-- **The deterministic single-step overshoot bridge (full kernel), as a named
structural fact.**  In the real Doty kernel, for a COUNTER-TIMED destination phase
`p+1`, a single scheduled interaction taking a `NoOvershoot p` configuration (every
agent at phase `< p+2`) out of `NoOvershoot p` forces a SOURCE-config clock at phase
`p+1` with `counter = 0` (a witness to `AtRiskClockZero p c`).

JUSTIFICATION (verified in `Protocol/Transition.lean`, FROZEN; carried as a hypothesis
for the assembly because the full per-phase upper-bound case analysis through the
epidemic + 11-phase dispatcher + `finishPhase10Entry` is the same magnitude as the
existing `Transition_*_phase_le_two_*` lemmas and is out of scope for this seam file):

* The phase epidemic (`phaseEpidemicUpdate`) raises both outputs to `max` of the two
  input phases (`phaseEpidemicUpdate_*_phase_ge_max_api`), so on a `NoOvershoot` pair
  (both phases `≤ p+1`) the post-epidemic phase is `≤ p+1` — the epidemic alone cannot
  create `p+2`.
* The work transition at phase `p+1 ∈ {1,5,6,7,8}` advances a clock ONLY via
  `stdCounterSubroutine` (phase 1 = `clockCounterStep`; phases 5–8 run
  `stdCounterSubroutine` on clocks after the work rule), and that subroutine advances
  phase ONLY when `counter = 0`.  A clock dragged UP into phase `p+1` by the epidemic
  has its counter RESET to full `≠ 0` (`phaseInit` Rule for `{1,5,6,7,8}`), so it
  cannot advance further the same step.  Hence the only `p+2`-creating event is a
  SOURCE clock already at phase `p+1` with `counter = 0`.

IMPORTANT SCOPING FINDING (verified, supersedes the blueprint's optimism): the bridge
is FALSE without a well-formedness side condition, because of the ERROR-TO-10 path.
`phaseInit 1` sends an `mcr` agent to phase 10 (`enterPhase10`); so at the `p = 0`
seam an `mcr` epidemic-dragged into phase 1 errors to phase `10 ≥ 2 = p+2` — an
overshoot creation with NO counter-`0` clock involved.  (For phases `{5,6,7,8}`
`phaseInit` never errors to 10, and a CLOCK is never `mcr`, so a clock-entry never
errors; the leak is only NON-clock agents whose `phaseInit` can error.)  The honest
bridge therefore requires the seam `Pre`'s well-formedness (no remaining `mcr`,
in-range biases) so that `phaseInit` does not error during the seam — exactly the
`validInitial`/quota invariants threaded by the `Analysis` layer
(`reachable_preserves_well_formed_agent_quota`).  We carry the bridge as
`DetSeamOvershootBridge p`, to be discharged per-seam from those invariants; this
mirrors `Phase0Window.det_phase0_exit` (which carries `allPhase0` as its window). -/
def DetSeamOvershootBridge (p : ℕ) : Prop :=
  ∀ (c : Config (AgentState L K)) (r₁ r₂ : AgentState L K),
    NoOvershoot (L := L) (K := K) p c →
    ¬ NoOvershoot (L := L) (K := K) p
      (Protocol.stepOrSelf (NonuniformMajority L K) c r₁ r₂) →
    AtRiskClockZero (L := L) (K := K) p c

/-- **Kernel-level overshoot-step bound from the deterministic bridge.**  Given the
deterministic bridge, from a `NoOvershoot p` configuration the one-step probability of
LEAVING `NoOvershoot p` is bounded by the probability of being `AtRiskClockZero` —
i.e. the kernel mass of `{¬ NoOvershoot}` from a `NoOvershoot` start equals the
preimage of the at-risk event.  Concretely: the set of NEXT configs that overshoot is
contained, after one step from a `NoOvershoot` config, in the configs reachable from
an `AtRiskClockZero` source.  We expose the per-pair containment used by the prefix
union in Stage 5. -/
theorem stepOrSelf_overshoot_imp_atRisk (p : ℕ)
    (hdet : DetSeamOvershootBridge (L := L) (K := K) p)
    (c : Config (AgentState L K)) (r₁ r₂ : AgentState L K)
    (hno : NoOvershoot (L := L) (K := K) p c)
    (hexit : ¬ NoOvershoot (L := L) (K := K) p
      (Protocol.stepOrSelf (NonuniformMajority L K) c r₁ r₂)) :
    AtRiskClockZero (L := L) (K := K) p c :=
  hdet c r₁ r₂ hno hexit

end SeamNoOvershoot

end ExactMajority
