/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# `RolePreservation` — the role field is preserved by the work-phase dynamics.

Foundational layer toward `mainCount` conservation at phase `≥ 3` (the prerequisite for the Lemma
6.10 supermartingale `Φ = m_{>h} − 1.1·c_{>h}`, which needs fixed role-size denominators `|M|`,`|C|`).

The `role` field is written ONLY in the role-assignment phases 0–1 (`RoleMCR → Main/Clock/Reserve`,
`RoleCR → Reserve`); every transition entering a phase `≥ 2` leaves `role` untouched.  This file
proves the helper-level role-equalities (`advancePhase`, `phaseInit` for phase `≥ 2`,
`advancePhaseWithInit` / `stdCounterSubroutine` for phase `≥ 2`).  The per-phase
`PhaseNTransition` role-equalities (N = 3..10) and the assembled `Transition` role-eq at phase `≥ 3`
build on these.  NO sorry / admit / axiom / native_decide.
-/

import Ripple.PopulationProtocol.Majority.ExactMajority.Protocol.Transition

namespace ExactMajority

namespace RolePreservation

variable {L K : ℕ}

/-- `advancePhase` only bumps the `phase` field — `role` is preserved. -/
theorem advancePhase_role_eq (a : AgentState L K) :
    (advancePhase L K a).role = a.role := by
  unfold advancePhase; split_ifs <;> rfl

set_option maxHeartbeats 4000000 in
/-- `phaseInit` preserves `role` when entering any phase `≥ 2`.  (The only role-changing branch is
the phase-1 cleanup `RoleCR → Reserve`; every phase-`≥2` branch modifies only non-role fields, and
the `enterPhase10` error branch preserves `role` via `enterPhase10_role`.) -/
theorem phaseInit_role_eq (p : Fin 11) (hp : 2 ≤ p.val) (a : AgentState L K) :
    (phaseInit L K p a).role = a.role := by
  obtain ⟨pv, hpv⟩ := p
  cases hrole : a.role <;> interval_cases pv <;>
    simp [phaseInit, hrole, enterPhase10_role, apply_ite AgentState.role, ite_self]

/-- `advancePhaseWithInit` (= `phaseInit` after `advancePhase`) preserves `role` from phase `≥ 2`
(the advanced phase is then `≥ 3 ≥ 2`, where `phaseInit` preserves role). -/
theorem advancePhaseWithInit_role_eq (a : AgentState L K) (ha : 2 ≤ a.phase.val) :
    (advancePhaseWithInit L K a).role = a.role := by
  unfold advancePhaseWithInit
  have hadv : 2 ≤ (advancePhase L K a).phase.val := by
    unfold advancePhase; split_ifs with h
    · dsimp only; omega
    · exact ha
  rw [phaseInit_role_eq _ hadv, advancePhase_role_eq]

/-- `stdCounterSubroutine` (decrement, or `advancePhaseWithInit` on counter `0`) preserves `role`
from phase `≥ 2`. -/
theorem stdCounterSubroutine_role_eq (a : AgentState L K) (ha : 2 ≤ a.phase.val) :
    (stdCounterSubroutine L K a).role = a.role := by
  unfold stdCounterSubroutine
  split_ifs with h
  · exact advancePhaseWithInit_role_eq a ha
  · rfl

/-! ## Per-phase role-equalities — Phase 3 (the clock minute-counting phase). -/

/-- `phase3CancelSplit` (the same-exponent cancel) preserves the first agent's `role`. -/
theorem phase3CancelSplit_first_role_eq (s t : AgentState L K) :
    (phase3CancelSplit L K s t).1.role = s.role := by
  unfold phase3CancelSplit; split <;> (try split_ifs) <;> rfl

/-- `phase3CancelSplit` preserves the second agent's `role`. -/
theorem phase3CancelSplit_second_role_eq (s t : AgentState L K) :
    (phase3CancelSplit L K s t).2.role = t.role := by
  unfold phase3CancelSplit; split <;> (try split_ifs) <;> rfl

set_option maxHeartbeats 2000000 in
/-- `Phase3Transition` preserves the first agent's `role` (phase-3 input).  Clock-clock drip/sync/
counter all keep role (`stdCounterSubroutine_role_eq`), the Main-hour-set keeps role, and
`phase3CancelSplit` keeps role. -/
theorem Phase3Transition_first_role_eq (s t : AgentState L K) (hs : s.phase.val = 3) :
    (Phase3Transition L K s t).1.role = s.role := by
  have h2 : 2 ≤ s.phase.val := by omega
  have hstd := stdCounterSubroutine_role_eq s h2
  unfold Phase3Transition; simp only
  split_ifs <;> simp_all [phase3CancelSplit_first_role_eq]

set_option maxHeartbeats 2000000 in
/-- `Phase3Transition` preserves the second agent's `role` (phase-3 input). -/
theorem Phase3Transition_second_role_eq (s t : AgentState L K) (ht : t.phase.val = 3) :
    (Phase3Transition L K s t).2.role = t.role := by
  have h2 : 2 ≤ t.phase.val := by omega
  have hstd := stdCounterSubroutine_role_eq t h2
  unfold Phase3Transition; simp only
  split_ifs <;> simp_all [phase3CancelSplit_second_role_eq]

end RolePreservation

end ExactMajority
