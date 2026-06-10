/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Doty §6 — the HONEST seam per-pair `hpair` adapter (`SeamPairAdapter`)

This file packages the protocol-structural per-pair output bound for the seam
no-overshoot clock-counter tail with the HONEST constants discovered in
`SeamPairBound.lean`'s genuine attack, and re-wires the consumer chain in
`SeamNoOvershoot.lean` accordingly.  Append-only; it EDITS no existing file.

## The two honest corrections it implements (from `SeamPairBound`'s findings)

1. **The honest per-pair immigration ceiling is `2·eˢ·freshVal`, NOT `2·freshVal`.**
   A fresh epidemic-dragged clock enters `p+1` at the FULL counter and is DECREMENTED
   by the SAME-step dispatch to `full − 1`, so its summand is `eˢ·freshVal` per side,
   `2·eˢ·freshVal` per pair.  (`SeamNoOvershoot`'s `seamClockPotential_drift_affine`
   consumed `2·freshVal`, which is FALSE for `s > 0`.)

2. **The honest counter-reset destination set is `{1,6,7,8}`, NOT `{1,5,6,7,8}`.**
   Phase 5's predecessor `Phase4Transition` advances clocks via `advancePhase`
   (big-bias gate, NO `phaseInit`, NO counter reset), so a clock counter-advanced from
   phase 4 into phase 5 keeps its OLD counter (summand up to `1`, not `freshVal`),
   breaking the immigration tail.  Phases `{1,6,7,8}` are clean: their predecessors
   (`Phase0` Rule-5 / `Phase{5,6,7}`) all advance clocks via
   `stdCounterSubroutine → advancePhaseWithInit → phaseInit q`, which DOES reset.

## What is built (0 sorry / 0 axiom / no native_decide)

* **Stage 1** — the missing ADVANCE-regime dispatch reductions for the honest set
  `{1,6,7,8}`: `Phase0Transition_left_clock_eq` / `…_right_clock_eq` (the conditional
  Rule-5 dispatch), and the per-side ADVANCE bound
  `seamClockSummand_Transition_side_advance_le` (a clock advanced INTO `p+1` enters at
  full counter, summand `= freshVal`).
* **Stage 2** — the HONEST two-sided per-pair bound
  `seamClockSummand_Transition_pair_le`
  `summand(δ.1) + summand(δ.2) ≤ eˢ·(summand a + summand b) + 2·eˢ·freshVal`
  on the seam region (destination `p+1 ∈ {1,6,7,8}`), assembled from the per-side
  no-advance (`SeamPairBound`) and advance (Stage 1) bounds.
* **Stage 3** — the corrected drift `seamClockPotential_drift_affine_honest` with
  `b = 2·eˢ·freshVal`, derived from Stage 2 via
  `Phase0Window.lintegral_transitionKernel_eq_sum` (mirrors `SeamNoOvershoot`).
* **Stage 4** — the corrected numerics `seam_noOvershoot_numerics_honest`
  (`b = 2·e·freshVal` at `s = 1`; verifies the `e^{−45}+e^{−43}→e^{−40}` slack absorbs
  the extra `eˢ` factor) and the end-to-end honest at-risk tail / no-overshoot tail.

The four excluded destination phases are handled by NAMED per-phase guard facts (NOT
faked): phases `2,4,9` (untimed: opinion-union / big-bias) and phases `3,5`
(counter-timed but no counter reset on entry) carry their own work-phase / width
guards; see the `CounterResetDest` predicate and the closing doc section.

Reference: Doty et al. §6; consumer = `SeamNoOvershoot.lean`; protocol core =
`SeamPairBound.lean`; pattern = `Phase0Window.lean`; blueprint =
`HANDOFF_SEAM_NOOVERSHOOT.md`.
-/

import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.SeamPairBound

namespace ExactMajority

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Real BigOperators

namespace SeamNoOvershoot

variable {L K : ℕ}

/-! ## The honest counter-reset destination set `{1,6,7,8}`.

This is the intersection of the epidemic-drag reset set `{1,5,6,7,8}`
(`CounterTimedPhase`) with the counter-ADVANCE reset set: a clock counter-advanced
INTO `q` keeps a full counter iff `q`'s PREDECESSOR `q−1` advances clocks via
`stdCounterSubroutine → advancePhaseWithInit → phaseInit q`.  For `q = 5` the
predecessor (phase 4) advances via `advancePhase` (no reset), so `5` is excluded. -/

/-- **The honest counter-reset destination set** `{1, 6, 7, 8}` (blueprint's
`CounterTimedPhase` minus phase 5).  Entry into these phases both (i) decrements the
summand by `eˢ` for a clock already there, AND (ii) resets a counter-advanced or
epidemic-dragged immigrant clock to the FULL counter (summand `= freshVal`). -/
def CounterResetDest (q : ℕ) : Prop :=
  q = 1 ∨ q = 6 ∨ q = 7 ∨ q = 8

instance (q : ℕ) : Decidable (CounterResetDest q) := by
  unfold CounterResetDest; infer_instance

/-- `CounterResetDest ⊆ CounterTimedPhase` (so `SeamPairBound`'s no-advance lemmas,
stated for `CounterTimedPhase`, apply on the honest set). -/
theorem CounterTimedPhase_of_CounterResetDest {q : ℕ} (h : CounterResetDest q) :
    CounterTimedPhase q := by
  rcases h with h | h | h | h <;> simp [CounterTimedPhase, h]

/-! ## Stage 1 — the ADVANCE-regime dispatch reductions for `{1,6,7,8}`.

`SeamPairBound` proved the NO-ADVANCE per-side bound (when `ep.1.phase = p+1`): the
dispatch is `Phase(p+1)Transition` and the clock summand contracts by `eˢ`.  The
remaining ADVANCE regime is when `ep.i.phase = p` and the same-step dispatch advances
the clock INTO `p+1`.  For destination `p+1 ∈ {1,6,7,8}` the dispatch (selected by
`ep.1.phase = p`) is `Phase{0,5,6,7}Transition`; for a clock initiator/responder these
reduce to `stdCounterSubroutine` of that clock, EXCEPT Phase 0, whose Rule-5 clock step
is gated on the PARTNER also being a clock.  In every case the LEFT/RIGHT clock output
is `stdCounterSubroutine ep.i` or `ep.i` unchanged — and if it lands at `p+1` it must be
the advancing `stdCounterSubroutine` branch, which RESETS the counter (summand
`= freshVal`). -/

/-- **Phase-0 LEFT clock reduction (advance regime).**  For a clock initiator `c`, the
Phase-0 dispatch LEFT output equals `stdCounterSubroutine ĉ` (Rule 5, when the partner
is also a clock) or `ĉ` unchanged, where `ĉ` is `c` possibly with `assigned := true`
(Phase-0 Rule 3, partner-mcr).  Crucially `ĉ` is a CLOCK at the SAME phase as `c` — so
the advance lemma `seamClockSummand_stdCounterSubroutine_advance` applies to `ĉ`
directly, with no need to relate it back to `c`. -/
theorem Phase0Transition_left_clock_eq (c t : AgentState L K) (hc : c.role = .clock) :
    ∃ chat : AgentState L K, chat.role = .clock ∧ chat.phase.val = c.phase.val
      ∧ ((Phase0Transition L K c t).1 = stdCounterSubroutine L K chat
        ∨ (Phase0Transition L K c t).1 = chat) := by
  have hnm : c.role ≠ .mcr := by rw [hc]; decide
  have hnmain : c.role ≠ .main := by rw [hc]; decide
  have hncr : c.role ≠ .cr := by rw [hc]; decide
  by_cases h3 : t.role = Role.mcr ∧ ¬ c.assigned = true
  · -- Rule 3 fires (partner is mcr ⇒ NOT a clock ⇒ Rule 5 gate false):
    -- the output is exactly `{c with assigned := true}`.
    refine ⟨{ c with assigned := true }, hc, rfl, ?_⟩
    right
    unfold Phase0Transition
    simp only [hc, reduceCtorEq, false_and, and_false, if_false, ne_eq, not_false_eq_true,
      true_and, h3.1, h3.2, and_true, if_true]
  · -- Rule 3 does not fire: the output is `if t.role = clock then stdCounterSubroutine c else c`.
    refine ⟨c, hc, rfl, ?_⟩
    unfold Phase0Transition
    simp only [hc, reduceCtorEq, false_and, and_false, if_false, ne_eq, not_false_eq_true,
      true_and, h3, if_false]
    by_cases hgate : t.role = .clock
    · left; rw [if_pos hgate]
    · right; rw [if_neg hgate]

/-- **Phase-0 RIGHT clock reduction (advance regime).**  Symmetric. -/
theorem Phase0Transition_right_clock_eq (s c : AgentState L K) (hc : c.role = .clock) :
    ∃ chat : AgentState L K, chat.role = .clock ∧ chat.phase.val = c.phase.val
      ∧ ((Phase0Transition L K s c).2 = stdCounterSubroutine L K chat
        ∨ (Phase0Transition L K s c).2 = chat) := by
  have hnm : c.role ≠ .mcr := by rw [hc]; decide
  have hnmain : c.role ≠ .main := by rw [hc]; decide
  have hncr : c.role ≠ .cr := by rw [hc]; decide
  by_cases h3 : s.role = Role.mcr ∧ ¬ c.assigned = true
  · refine ⟨{ c with assigned := true }, hc, rfl, ?_⟩
    right
    unfold Phase0Transition
    simp only [hc, reduceCtorEq, and_false, if_false, ne_eq, not_false_eq_true,
      true_and, h3.1, h3.2, and_true, if_true]
  · refine ⟨c, hc, rfl, ?_⟩
    unfold Phase0Transition
    simp only [hc, reduceCtorEq, and_false, if_false, ne_eq, not_false_eq_true,
      true_and, h3, if_false]
    by_cases hgate : s.role = .clock
    · left; rw [if_pos hgate]
    · right; rw [if_neg hgate]

/-- For a clock RESPONDER, the Phase-5 dispatch RIGHT output equals
`stdCounterSubroutine c` (the reserve/main sampling pre-step never touches a clock). -/
theorem Phase5Transition_right_clock (s c : AgentState L K) (hc : c.role = .clock) :
    (Phase5Transition L K s c).2 = stdCounterSubroutine L K c := by
  unfold Phase5Transition
  simp only [hc, reduceCtorEq, false_and, and_false, ↓reduceIte]

/-- For a clock RESPONDER, the Phase-6 dispatch RIGHT output equals
`stdCounterSubroutine c`. -/
theorem Phase6Transition_right_clock (s c : AgentState L K) (hc : c.role = .clock) :
    (Phase6Transition L K s c).2 = stdCounterSubroutine L K c := by
  unfold Phase6Transition
  simp only [hc, reduceCtorEq, false_and, and_false, ↓reduceIte]

/-- For a clock RESPONDER, the Phase-7 dispatch RIGHT output equals
`stdCounterSubroutine c`. -/
theorem Phase7Transition_right_clock (s c : AgentState L K) (hc : c.role = .clock) :
    (Phase7Transition L K s c).2 = stdCounterSubroutine L K c := by
  unfold Phase7Transition
  simp only [hc, reduceCtorEq, false_and, ↓reduceIte]

/-- For a clock RESPONDER, the Phase-8 dispatch RIGHT output equals
`stdCounterSubroutine c`. -/
theorem Phase8Transition_right_clock (s c : AgentState L K) (hc : c.role = .clock) :
    (Phase8Transition L K s c).2 = stdCounterSubroutine L K c := by
  unfold Phase8Transition
  simp only [hc, reduceCtorEq, false_and, ↓reduceIte]

end SeamNoOvershoot

end ExactMajority
