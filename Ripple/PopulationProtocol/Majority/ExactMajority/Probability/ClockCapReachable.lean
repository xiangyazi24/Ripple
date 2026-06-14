/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# `ClockCapReachable` — the clock-count cap on the reachable trajectory (DETERMINISTIC),
# decoupling the clock per-`τ` depletion cap from the §6 FrontSync front-shape concentration.

`ReachableClockTail.mgf_depletion_tail_reachable` closes the clock per-`τ` depletion from the
reachable cap `hcap_reach : ∀ c, Reachable c₀ c → c.count sc ≤ m`.  We supply `hcap_reach`
DETERMINISTICALLY from the phase-3 ENTRY invariant `clockCount c₀ = mC ∧ allPhaseGE3 c₀`:

* (a) clock-count is conserved by every transition whose interacting pair is at phase `≥ 3`
  (`HabsDischarge.clockCount_pair_eq` — roles are never created or destroyed once all phases `≥ 3`);
* (b) `allPhaseGE3` is one-step closed (phase non-decrease, `Transition_phase_nondec_local`), so the
  invariant propagates along the WHOLE reachable trajectory (`ReflTransGen` induction); and
* (c) `count sc ≤ clockCount` for any single clock-role state `sc` (`count_filter_of_pos`).

This uses NEITHER `Q_mix` NOR `FrontSync`: the clock COUNT cap is independent of the §6 front-shape
concentration (which is needed only for the clock TIMING / phase-advance, not the count).  Hence the
contracting slots' clock-depletion cap is regime-CLOSED to the bare phase-3 entry invariant.

NEW file; no existing file is edited; no sorry / admit / axiom / native_decide.
-/

import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.HabsDischarge
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.CascadeConservation
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.ReachableClockTail
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.RoleSplitConcentration

namespace ExactMajority

namespace ClockCapReachable

open ClockRealKernel ClockRealMixed HabsDischarge
open scoped ENNReal NNReal Real

variable {L K : ℕ}

/-! ## Part 1 — the two `StepRel`-closed fields. -/

/-- **Per-`StepRel` clock-count conservation, from an `allPhaseGE3` source.**  Roles cannot be
created or destroyed when both interacting agents are at phase `≥ 3` (`clockCount_pair_eq`), so the
clock count is exactly preserved by a single applicable step.  (Mirrors the applicable branch of
`HabsDischarge.qmix_clockSize_closed`, but needs ONLY `allPhaseGE3`, not the full `Q_mix`.) -/
theorem clockCount_stepRel {c c' : Config (AgentState L K)}
    (hge : allPhaseGE3 (L := L) (K := K) c)
    (h : (NonuniformMajority L K).StepRel c c') :
    clockCount (L := L) (K := K) c' = clockCount (L := L) (K := K) c := by
  obtain ⟨r₁, r₂, happ, hc'⟩ := CascadeConservation.stepRel_eq_stepOrSelf h
  have hmem1 : r₁ ∈ c := mem_of_applicable_left happ
  have hmem2 : r₂ ∈ c := mem_of_applicable_right happ
  have h1ge : 3 ≤ r₁.phase.val := hge r₁ hmem1
  have h2ge : 3 ≤ r₂.phase.val := hge r₂ hmem2
  have hsub : ({r₁, r₂} : Multiset (AgentState L K)) ≤ c := happ
  have hc'eq : Protocol.stepOrSelf (NonuniformMajority L K) c r₁ r₂
      = c - {r₁, r₂} + {(Transition L K r₁ r₂).1, (Transition L K r₁ r₂).2} := by
    unfold Protocol.stepOrSelf; rw [if_pos happ]; rfl
  rw [hc', hc'eq]
  unfold clockCount
  rw [Multiset.countP_add, Multiset.countP_sub hsub, clockCount_pair_eq r₁ r₂ h1ge h2ge]
  have hle : Multiset.countP (fun a => a.role = .clock)
      ({r₁, r₂} : Multiset (AgentState L K))
      ≤ Multiset.countP (fun a => a.role = .clock) c :=
    Multiset.countP_le_of_le _ hsub
  omega

/-- **Per-`StepRel` `allPhaseGE3` closure.**  Every per-phase transition is phase-non-decreasing
(`Transition_phase_nondec_local`), so a config all of whose agents are at phase `≥ 3` maps under one
applicable step to one all of whose agents are at phase `≥ 3`. -/
theorem allPhaseGE3_stepRel {c c' : Config (AgentState L K)}
    (hge : allPhaseGE3 (L := L) (K := K) c)
    (h : (NonuniformMajority L K).StepRel c c') :
    allPhaseGE3 (L := L) (K := K) c' := by
  obtain ⟨r₁, r₂, happ, hc'⟩ := CascadeConservation.stepRel_eq_stepOrSelf h
  have h1ge : 3 ≤ r₁.phase.val := hge r₁ (mem_of_applicable_left happ)
  have h2ge : 3 ≤ r₂.phase.val := hge r₂ (mem_of_applicable_right happ)
  have hc'eq : Protocol.stepOrSelf (NonuniformMajority L K) c r₁ r₂
      = c - {r₁, r₂} + {(Transition L K r₁ r₂).1, (Transition L K r₁ r₂).2} := by
    unfold Protocol.stepOrSelf; rw [if_pos happ]; rfl
  rw [hc', hc'eq]
  intro a ha
  rw [Multiset.mem_add] at ha
  rcases ha with ha | ha
  · -- a ∈ c - {r₁,r₂} ⊆ c
    exact hge a (Multiset.mem_of_le (Multiset.sub_le_self c _) ha)
  · -- a is a transition output: phase ≥ its input phase ≥ 3
    obtain ⟨hnd1, hnd2⟩ := Transition_phase_nondec_local (L := L) (K := K) r₁ r₂
    simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at ha
    rcases ha with rfl | rfl
    · omega
    · omega

/-! ## Part 2 — the invariant and its reachable propagation. -/

/-- The deterministic clock-structure invariant: a fixed clock count `mC` and all phases `≥ 3`. -/
def ClockGE3Inv (mC : ℕ) (c : Config (AgentState L K)) : Prop :=
  clockCount (L := L) (K := K) c = mC ∧ allPhaseGE3 (L := L) (K := K) c

/-- `ClockGE3Inv mC` is `StepRel`-closed. -/
theorem clockGE3Inv_stepRel {mC : ℕ} {c c' : Config (AgentState L K)}
    (hInv : ClockGE3Inv (L := L) (K := K) mC c)
    (h : (NonuniformMajority L K).StepRel c c') :
    ClockGE3Inv (L := L) (K := K) mC c' :=
  ⟨(clockCount_stepRel hInv.2 h).trans hInv.1, allPhaseGE3_stepRel hInv.2 h⟩

/-- **The invariant propagates along the whole reachable trajectory** (`ReflTransGen` induction). -/
theorem clockGE3Inv_reachable {mC : ℕ} {c₀ c : Config (AgentState L K)}
    (hInv : ClockGE3Inv (L := L) (K := K) mC c₀)
    (hreach : (NonuniformMajority L K).Reachable c₀ c) :
    ClockGE3Inv (L := L) (K := K) mC c := by
  induction hreach with
  | refl => exact hInv
  | tail _ hstep ih => exact clockGE3Inv_stepRel ih hstep

/-- The clock count is exactly `mC` on every config reachable from a `ClockGE3Inv mC` entry. -/
theorem clockCount_eq_on_reachable {mC : ℕ} {c₀ c : Config (AgentState L K)}
    (hInv : ClockGE3Inv (L := L) (K := K) mC c₀)
    (hreach : (NonuniformMajority L K).Reachable c₀ c) :
    clockCount (L := L) (K := K) c = mC :=
  (clockGE3Inv_reachable hInv hreach).1

/-! ## Part 3 — the count bridge and the deterministic `hcap_reach`. -/

/-- For any single clock-role state `sc`, `count sc ≤ clockCount` (`count_filter_of_pos`). -/
theorem count_le_clockCount (sc : AgentState L K) (hsc : sc.role = .clock)
    (c : Config (AgentState L K)) :
    c.count sc ≤ clockCount (L := L) (K := K) c := by
  rw [Config.count, clockCount, Multiset.countP_eq_card_filter]
  have hfp : Multiset.count sc (Multiset.filter (fun a => a.role = Role.clock) c)
      = Multiset.count sc c :=
    Multiset.count_filter_of_pos (p := fun a => a.role = Role.clock) (a := sc) hsc
  calc Multiset.count sc c
      = Multiset.count sc (Multiset.filter (fun a => a.role = Role.clock) c) := hfp.symm
    _ ≤ Multiset.card (Multiset.filter (fun a => a.role = Role.clock) c) :=
        Multiset.count_le_card sc _

/-- **The reachable clock cap (the `mgf_depletion_tail_reachable` input), DETERMINISTIC.**
Given the phase-3 entry invariant `ClockGE3Inv mC c₀`, every config reachable from `c₀` has
`count sc ≤ mC` for any clock-role state `sc`.  This is the honest `hcap_reach` — supplied with NO
front-shape concentration (only role conservation + `allPhaseGE3`).  It instantiates
`ReachableClockTail.mgf_depletion_tail_reachable`'s `hcap_reach` at `m := mC`, closing the clock
per-`τ` depletion cap to the bare phase-3 entry invariant. -/
theorem hcap_reach_of_entry {mC : ℕ} (sc : AgentState L K) (hsc : sc.role = .clock)
    {c₀ : Config (AgentState L K)} (hInv : ClockGE3Inv (L := L) (K := K) mC c₀)
    (c : Config (AgentState L K)) (hreach : (NonuniformMajority L K).Reachable c₀ c) :
    c.count sc ≤ mC := by
  rw [← clockCount_eq_on_reachable hInv hreach]
  exact count_le_clockCount sc hsc c

/-! ## Part 4 — the fully-instantiated clock depletion tail (both caps deterministic). -/

/-- **The clock depletion tail from the phase-3 entry invariant (fully instantiated).**
Bundling the two reachable caps — card conservation (`FaithfulDischargeTierA.card_eq_on_reachable`)
and the clock-count cap (`hcap_reach_of_entry`) — with the small-config self-loop
(`FaithfulDischargeTierA.hsmall_self_loop`), this instantiates
`ReachableClockTail.mgf_depletion_tail_reachable` for the ExactMajority clock species `sc` at the
clock rate `m := mC`.  Hence the clock per-`τ` depletion bound

  `(K^H) c₀ {count sc ≤ N − R}  ≤  (1 + (2mC/n)(e^{2s}−1))^H · expPot sc s N c₀ / e^{sR}`

holds with ONLY the deterministic phase-3 entry invariant `ClockGE3Inv mC c₀` (+ `card c₀ = n`) —
NO front-shape / FrontSync concentration.  This is the regime-closed clock-depletion input the
contracting slots consume. -/
theorem clock_depletion_tail_from_entry
    (sc : AgentState L K) (hsc : sc.role = .clock) (s : ℝ) (hs : 0 < s)
    (N R n mC : ℕ) {c₀ : Config (AgentState L K)}
    (hcard0 : c₀.card = n) (hInv : ClockGE3Inv (L := L) (K := K) mC c₀) (H : ℕ) :
    ((NonuniformMajority L K).transitionKernel ^ H) c₀
        {c : Config (AgentState L K) | (c.count sc : ℝ) ≤ (N : ℝ) - R}
      ≤ (1 + (2 * (mC : ℝ≥0∞) / (n : ℝ≥0∞)) * ENNReal.ofReal (Real.exp (2 * s) - 1)) ^ H
          * ClockDepletionCoupling.expPot sc s N c₀
          / ENNReal.ofReal (Real.exp (s * R)) :=
  ReachableClockTail.mgf_depletion_tail_reachable (NonuniformMajority L K) sc s hs N R n mC c₀
    (fun c hreach _ => FaithfulDischargeTierA.card_eq_on_reachable n c₀ c hreach hcard0)
    (FaithfulDischargeTierA.hsmall_self_loop sc)
    (fun c hreach => hcap_reach_of_entry sc hsc hInv c hreach)
    H

/-- **The uniform per-`τ` clock bound from the phase-3 entry invariant — the
`ClockStructGateDischarge.clock_prefix_fit` input.**  For every `τ ≤ T` the forward-trajectory term
`(K^τ) c₀ {count sc ≤ N − R}` is bounded by the single `ε := Q^T · expPot / e^{sR}`
(`Q = 1 + (2mC/n)(e^{2s}−1)`), supplied with ONLY the deterministic entry invariant `ClockGE3Inv mC c₀`
(+ `card c₀ = n`).  This is EXACTLY the `hClockPerτ` per-`τ` hypothesis the contracting slots' clock
budget consumes (`clock_prefix_fit` then gives the `∑_{τ<T} ≤ T·ε ≤ η_clock` prefix bound).  Hence the
contracting slots' clock-depletion input is regime-CLOSED to the entry invariant, NO front-shape. -/
theorem clock_perτ_from_entry
    (sc : AgentState L K) (hsc : sc.role = .clock) (s : ℝ) (hs : 0 < s)
    (N R n mC : ℕ) {c₀ : Config (AgentState L K)}
    (hcard0 : c₀.card = n) (hInv : ClockGE3Inv (L := L) (K := K) mC c₀)
    (T τ : ℕ) (hτ : τ ≤ T) :
    ((NonuniformMajority L K).transitionKernel ^ τ) c₀
        {c : Config (AgentState L K) | (c.count sc : ℝ) ≤ (N : ℝ) - R}
      ≤ (1 + (2 * (mC : ℝ≥0∞) / (n : ℝ≥0∞)) * ENNReal.ofReal (Real.exp (2 * s) - 1)) ^ T
          * ClockDepletionCoupling.expPot sc s N c₀
          / ENNReal.ofReal (Real.exp (s * R)) :=
  ReachableClockTail.clock_perτ_uniform_reachable (NonuniformMajority L K) sc s hs N R n mC c₀
    (fun c hreach _ => FaithfulDischargeTierA.card_eq_on_reachable n c₀ c hreach hcard0)
    (FaithfulDischargeTierA.hsmall_self_loop sc)
    (fun c hreach => hcap_reach_of_entry sc hsc hInv c hreach)
    T τ hτ

/-! ## Part 5 — establishing the entry invariant at the Phase-3 seam (the whp content). -/

/-- **The entry invariant from the role-split good event + the Phase-3 seam.**  Clock agents are
created ONLY in Phase 0 (`RoleCR,RoleCR → Clock,Reserve`) and the count FREEZES at Phase-1
initialization (remaining `RoleCR → Reserve`); so the realized clock count `mC := clockCount c` is a
deterministic conserved quantity from the Phase-3 entry on, and `allPhaseGE3` first holds at the
Phase-3 seam (after Phase 2 advances the population to phase 3).  Hence from the role-split good
event `RoleSplitGood η n c` (the Phase-0 whp event — roles assigned, `|Clock| ≥ n/5`) and
`allPhaseGE3 c` (the Phase-3 seam postcondition), the entry invariant `ClockGE3Inv mC c` holds at the
realized `mC = clockCount c`, with the floor `mC ≥ n/5`.  This is the MINIMAL whp content feeding the
deterministic propagation `clockGE3Inv_reachable`; `mC` is realized (existential), NOT hardwired. -/
theorem clockGE3_entry_of_roleSplitGood {η : ℝ} (hη : η ≤ 1 / 25) {n : ℕ}
    {c : Config (AgentState L K)}
    (hgood : RoleSplitConcentration.RoleSplitGood (L := L) (K := K) η n c)
    (hge3 : allPhaseGE3 (L := L) (K := K) c) :
    ∃ mC : ℕ, ClockGE3Inv (L := L) (K := K) mC c ∧ (n : ℝ) / 5 ≤ (mC : ℝ) :=
  ⟨clockCount (L := L) (K := K) c, ⟨rfl, hge3⟩,
    RoleSplitConcentration.clockCount_linear_of_RoleSplitGood (L := L) (K := K) hη hgood⟩

end ClockCapReachable

end ExactMajority
