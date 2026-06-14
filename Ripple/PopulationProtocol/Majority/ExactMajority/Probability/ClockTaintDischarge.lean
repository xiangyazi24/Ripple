/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# `ClockTaintDischarge` — discharging `ClockTaintedRiseSubset` on the hour-coupling window.

`ClockTaintMixed.clockTainted_rise_prob_le_of_subset` reduces the mixed clock-filtered early-drip
ghost rate to a single deterministic obligation,

  `ClockTaintMixed.ClockTaintedRiseSubset T θn Aux`

(a marked step raises the clock-filtered taint count only on a same-minute-`T` pair or a pair with a
tainted member), parametrized by an auxiliary gate `Aux`.  The blocker that the previous agent
isolated (`ClockTaintMixed` module docstring) is that the original `EarlyDripMarked.tainted_rise_subset`
feeds `AllClockP3` to BOTH sampled pair members in order to invoke
`ClimbTail.transition_p3_minute_le_succ_max` (the per-pair minute cap `outputs ≤ max(inputs)+1`),
which needs both members to be phase-3 CLOCKS.  Under the weakened `ClockP3`, a sampled pair may
contain a Main/Reserve agent, and the minute cap is unavailable.

## What this file does

We supply the MIXED per-pair minute cap and use it to discharge `ClockTaintedRiseSubset` with the
EXPLICIT auxiliary gate

  `Aux mc := HourCoupling.HourWindow (eraseConfig mc)`

— the established hour-coupling window "every agent is a Main or a Clock, at phase 3, with unbiased
Mains" (`HourCoupling.HourWindow`).  On this window EVERY applicable pair `(s,t)` satisfies the
hypotheses of `HourCoupling.phase3_out_phase_ne_ten`, so `Transition = Phase3Transition` and the
minute is bounded in all four role cases:

* Main×Clock / Clock×Main (Rule-2 hour-drag): `Phase3Transition` only rewrites `hour`, so each
  output's minute EQUALS its input's minute (`HourCoupling.phase3_drag_left/right`);
* Main×Main (Rules 3/4 `phase3CancelSplit`, identity on unbiased Mains): outputs `= (s,t)`, minutes
  unchanged;
* Clock×Clock (Rule 1): the proven `ClimbTail.transition_p3_minute_le_succ_max` gives `≤ max+1`.

`transition_minute_le_succ_max_of_hourWindow` packages these into `outputs ≤ max(inputs)+1`, the exact
shape the rise-subset argument consumes.  Replaying `EarlyDripMarked.tainted_rise_subset` verbatim with
this mixed cap (and `clockTaintedCount ≤ taintedCount` for the count step) discharges
`ClockTaintedRiseSubset`.

### Where the gate comes from (honest accounting)

The phase-3 part of `HourWindow` is EXACTLY `PhaseGatesPrefix.phaseGates_of_prefix_frontSync`'s
`allPhaseGE3 ∧ noPhaseAbove3` conclusion (`allPhaseGE3 ∧ noPhaseAbove3 ⟹ phase = 3`).  The remaining
two conjuncts — every agent is Main-or-Clock, and every Main is unbiased — are the SEPARATE role/bias
window invariants of the hour-coupling regime (the same `HourWindow` already carried by
`HourCoupling`/`HourCouplingV2`).  We therefore discharge against the FULL `HourWindow` rather than
faking a `ClockP3`-only proof: `ClockP3` alone genuinely does not bound a Main×Clock minute, as the
`ClockTaintMixed` docstring records.  `phaseGates_supplies_hourWindow_phase3` makes the phase-3 half of
the supply explicit.

NEW file; no existing file is edited; no sorry/admit/axiom/native_decide.
Reference: Doty et al. (arXiv:2106.10201v2) §6; `DOCTRINE_THM69_CA.md` ROUND 6.
-/

import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.ClockTaintMixed
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.PhaseGatesPrefix

namespace ExactMajority

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace ClockTaintDischarge

open ClockRealKernel EarlyDripMarked ClockTaintMixed

variable {L K : ℕ}

/-! ## Part 1 — the MIXED per-pair minute cap on the hour-coupling window. -/

/-- **Mixed per-pair minute upper bound.**  For a pair `(s,t)` both at phase exactly 3, each agent a
Main or a Clock, every Main unbiased, BOTH `Transition` outputs have minute at most `max(inputs)+1`.

This is the `HourWindow`-faithful analogue of `ClimbTail.transition_p3_minute_le_succ_max` (which
needs both members to be phase-3 *clocks*).  The four role cases:
the Rule-2 hour-drag (Main×Clock, Clock×Main) and the Rule-3/4 cancel-split (Main×Main, identity on
unbiased Mains) all leave each output's minute EQUAL to its input's, and the Clock×Clock case is the
existing `≤ max+1` cap. -/
theorem transition_minute_le_succ_max_of_hourWindow (s t : AgentState L K)
    (hs3 : s.phase.val = 3) (ht3 : t.phase.val = 3)
    (hsr : s.role = .main ∨ s.role = .clock) (htr : t.role = .main ∨ t.role = .clock)
    (hsu : s.role = .main → s.bias = .zero) (htu : t.role = .main → t.bias = .zero) :
    (Transition L K s t).1.minute.val ≤ max s.minute.val t.minute.val + 1 ∧
      (Transition L K s t).2.minute.val ≤ max s.minute.val t.minute.val + 1 := by
  classical
  rcases hsr with hsm | hsc
  · rcases htr with htm | htc
    · -- Main × Main: `phase3CancelSplit` is the identity (unbiased), so minutes are unchanged.
      obtain ⟨h1, h2⟩ := HourCoupling.phase3_out_phase_ne_ten (L := L) (K := K) s t hs3 ht3
        (Or.inl hsm) (Or.inl htm) hsu htu
      rw [HourCoupling.transition_eq_phase3 (L := L) (K := K) s t hs3 ht3 h1 h2]
      have hP3 : Phase3Transition L K s t = (s, t) := by
        unfold Phase3Transition
        have hsc' : s.role ≠ .clock := by rw [hsm]; decide
        have htc' : t.role ≠ .clock := by rw [htm]; decide
        simp only [hsm, htm, hsu hsm, htu htm, and_false,
          if_false, if_true, and_self, reduceCtorEq, ite_self]
        exact HourCoupling.phase3CancelSplit_id_of_unbiased (L := L) (K := K) s t hsu htu ⟨hsm, htm⟩
      rw [hP3]
      exact ⟨Nat.le_succ_of_le (le_max_left _ _), Nat.le_succ_of_le (le_max_right _ _)⟩
    · -- Main × Clock: Rule-2 drag rewrites only `hour`; minutes equal the inputs'.
      obtain ⟨h1, h2⟩ := HourCoupling.phase3_out_phase_ne_ten (L := L) (K := K) s t hs3 ht3
        (Or.inl hsm) (Or.inr htc) hsu htu
      rw [HourCoupling.transition_eq_phase3 (L := L) (K := K) s t hs3 ht3 h1 h2]
      rw [HourCoupling.phase3_drag_left (L := L) (K := K) s t hsm (hsu hsm) htc]
      refine ⟨?_, Nat.le_succ_of_le (le_max_right _ _)⟩
      show s.minute.val ≤ max s.minute.val t.minute.val + 1
      exact Nat.le_succ_of_le (le_max_left _ _)
  · rcases htr with htm | htc
    · -- Clock × Main: symmetric Rule-2 drag; minutes equal the inputs'.
      obtain ⟨h1, h2⟩ := HourCoupling.phase3_out_phase_ne_ten (L := L) (K := K) s t hs3 ht3
        (Or.inr hsc) (Or.inl htm) hsu htu
      rw [HourCoupling.transition_eq_phase3 (L := L) (K := K) s t hs3 ht3 h1 h2]
      rw [HourCoupling.phase3_drag_right (L := L) (K := K) s t hsc htm (htu htm)]
      refine ⟨Nat.le_succ_of_le (le_max_left _ _), ?_⟩
      show t.minute.val ≤ max s.minute.val t.minute.val + 1
      exact Nat.le_succ_of_le (le_max_right _ _)
    · -- Clock × Clock: the existing per-pair cap (on the full `Transition`).
      exact ClimbTail.transition_p3_minute_le_succ_max (L := L) (K := K) s t hsc htc hs3 ht3

/-! ## Part 2 — the discharge of `ClockTaintedRiseSubset`. -/

/-- **The hour-coupling auxiliary gate.**  Discharging the mixed rise-subset uses the established
hour-coupling window on the erased configuration: every agent is a Main or a Clock, at phase exactly
3, with unbiased Mains (`HourCoupling.HourWindow`).  Its phase-3 conjunct is exactly what
`PhaseGatesPrefix.phaseGates_of_prefix_frontSync` supplies; the role/bias conjuncts are the separate
hour-window invariants. -/
def HourWindowAux (mc : Config (MarkedAgent L K)) : Prop :=
  HourCoupling.HourWindow (L := L) (K := K) (eraseConfig (L := L) (K := K) mc)

/-- **`ClockTaintedRiseSubset` is discharged on the hour-coupling window.**  The marked taint-rise
event is contained in the two scheduler events (a same-minute-`T` pair or a pair with a tainted
member), under `ClockP3` together with the hour-coupling auxiliary gate `HourWindowAux`.  This is the
mixed analogue of `EarlyDripMarked.tainted_rise_subset`, replayed with the mixed minute cap
`transition_minute_le_succ_max_of_hourWindow` in place of the all-clock cap. -/
theorem clockTaintedRiseSubset_of_hourWindow (T θn : ℕ) :
    ClockTaintedRiseSubset (L := L) (K := K) T θn (HourWindowAux (L := L) (K := K)) := by
  classical
  intro mc _hP3 hAux pr hpr
  rw [Set.mem_preimage, Set.mem_setOf_eq] at hpr
  by_contra hnot
  rw [Set.mem_union, Set.mem_setOf_eq, Set.mem_setOf_eq] at hnot
  push Not at hnot
  obtain ⟨hnotT, hm₁false, hm₂false⟩ := hnot
  -- the step cannot raise the clock-filtered count: refute hpr.
  unfold markedStep at hpr
  by_cases happ : ({pr.1, pr.2} : Multiset (MarkedAgent L K)) ≤ mc
  · rw [if_pos happ] at hpr
    have hmem1 : pr.1 ∈ mc := Multiset.mem_of_le happ (Multiset.mem_cons_self _ _)
    have hmem2 : pr.2 ∈ mc := Multiset.mem_of_le happ
      (Multiset.mem_cons_of_mem (Multiset.mem_singleton_self _))
    -- both pair states are in the erased window.
    have he1 : pr.1.1 ∈ eraseConfig (L := L) (K := K) mc := Multiset.mem_map_of_mem Prod.fst hmem1
    have he2 : pr.2.1 ∈ eraseConfig (L := L) (K := K) mc := Multiset.mem_map_of_mem Prod.fst hmem2
    obtain ⟨h1r, h1p, h1u⟩ := hAux pr.1.1 he1
    obtain ⟨h2r, h2p, h2u⟩ := hAux pr.2.1 he2
    -- the mixed per-pair minute cap.
    have hminute := transition_minute_le_succ_max_of_hourWindow (L := L) (K := K)
      pr.1.1 pr.2.1 h1p h2p h1r h2r h1u h2u
    set g := preBulkGate (L := L) (K := K) T θn mc with hg
    set o₁ := (markedOut (L := L) (K := K) T g pr.1 pr.2).1 with ho₁
    set o₂ := (markedOut (L := L) (K := K) T g pr.1 pr.2).2 with ho₂
    have hmark₁ : o₁.2 = markFor (L := L) (K := K) T g pr.1 pr.2
        (Transition L K pr.1.1 pr.2.1).1 := rfl
    have hmark₂ : o₂.2 = markFor (L := L) (K := K) T g pr.2 pr.1
        (Transition L K pr.1.1 pr.2.1).2 := rfl
    -- neither output is freshly tainted.
    have hno₁ : ¬ (o₁.2 = true) := by
      intro hm
      rw [hmark₁] at hm
      rcases markFor_true_crossing_cases (L := L) (K := K) T g pr.1 pr.2 _ hm with
        ⟨_, hin⟩ | ⟨hlo, hhi, hvia⟩
      · exact hm₁false hin
      · rcases hvia with ⟨hsame, _⟩ | hpart
        · -- gated drip seed: both pair minutes are exactly T.
          have hsame' : pr.1.1.minute.val = pr.2.1.minute.val := by rw [hsame]
          have hmax : max pr.1.1.minute.val pr.2.1.minute.val = pr.1.1.minute.val := by
            rw [← hsame']
            exact max_self _
          have h1T : pr.1.1.minute.val = T := by
            have := hminute.1
            rw [hmax] at this
            omega
          exact hnotT h1T (by omega)
        · exact hm₂false hpart
    have hno₂ : ¬ (o₂.2 = true) := by
      intro hm
      rw [hmark₂] at hm
      rcases markFor_true_crossing_cases (L := L) (K := K) T g pr.2 pr.1 _ hm with
        ⟨_, hin⟩ | ⟨hlo, hhi, hvia⟩
      · exact hm₂false hin
      · rcases hvia with ⟨hsame, _⟩ | hpart
        · have hsame' : pr.2.1.minute.val = pr.1.1.minute.val := by rw [hsame]
          have hmax : max pr.1.1.minute.val pr.2.1.minute.val = pr.2.1.minute.val := by
            rw [hsame']
            exact max_self _
          have h2T : pr.2.1.minute.val = T := by
            have := hminute.2
            rw [hmax] at this
            omega
          exact hnotT (by omega) h2T
        · exact hm₁false hpart
    -- the produced pair carries no tainted member.
    have houts : Multiset.countP (fun m : MarkedAgent L K => m.2 = true)
        ({o₁, o₂} : Multiset (MarkedAgent L K)) = 0 := by
      rw [Multiset.countP_eq_zero]
      intro m hm
      rw [show ({o₁, o₂} : Multiset (MarkedAgent L K)) = o₁ ::ₘ {o₂} from rfl] at hm
      rcases Multiset.mem_cons.mp hm with hm | hm
      · rw [hm]; exact hno₁
      · rw [Multiset.mem_singleton.mp hm]; exact hno₂
    -- hence the clock-filtered taint count cannot rise: the produced pair has no tainted member, so
    -- its `clockTaintedCount` contribution is `0` (a clock-filtered tainted agent is tainted), and
    -- the surviving part is dominated by `mc`.
    have houtsC : clockTaintedCount (L := L) (K := K) T ({o₁, o₂} : Multiset (MarkedAgent L K))
        = 0 := by
      unfold clockTaintedCount
      rw [Multiset.countP_eq_zero]
      intro m hm hmp
      have hcontra : ¬ (m.2 = true) := by
        have := (Multiset.countP_eq_zero
          (p := fun m : MarkedAgent L K => m.2 = true)
          (s := ({o₁, o₂} : Multiset (MarkedAgent L K)))).mp houts
        exact this m hm
      exact hcontra hmp.2.2
    have hle : clockTaintedCount (L := L) (K := K) T
        (mc - {pr.1, pr.2} + ({o₁, o₂} : Multiset (MarkedAgent L K)))
        ≤ clockTaintedCount (L := L) (K := K) T mc := by
      unfold clockTaintedCount
      unfold clockTaintedCount at houtsC
      rw [Multiset.countP_add, houtsC, add_zero]
      exact Multiset.countP_le_of_le _ (tsub_le_self (a := mc))
    omega
  · rw [if_neg happ] at hpr
    omega

/-! ## Part 3 — the phase-3 supply from the FrontSync prefix gate. -/

/-- **`phaseGates` supplies the phase-3 conjunct of `HourWindow`.**  The
`allPhaseGE3 ∧ noPhaseAbove3` conclusion of `PhaseGatesPrefix.phaseGates_of_prefix_frontSync`
pins every agent to phase EXACTLY 3, which is precisely the phase-3 requirement of
`HourCoupling.HourWindow`.  The remaining role/bias conjuncts of `HourWindow` are the separate
hour-coupling window invariants (not produced by the phase-gate induction). -/
theorem phaseGates_supply_phase3 (c : Config (AgentState L K))
    (hge : HabsDischarge.allPhaseGE3 (L := L) (K := K) c)
    (hno : HabsDischarge.noPhaseAbove3 (L := L) (K := K) c) :
    ∀ a ∈ c, a.phase.val = 3 :=
  fun a ha => le_antisymm (hno a ha) (hge a ha)

/-- **The KEY adapter on the hour-coupling window (clock-filtered ghost rate).**  Instantiating
`ClockTaintMixed.clockTainted_rise_prob_le_of_subset` with the discharged subset
`clockTaintedRiseSubset_of_hourWindow` gives the mixed clock-filtered early-drip rate

  `P[clockTaintedCount rises] ≤ (count@T / n)² + 2·taintedCount/n`

under `ClockP3` plus the hour-coupling window `HourWindowAux` — with NO residual obligation. -/
theorem clockTainted_rise_prob_le_on_hourWindow
    (T θn : ℕ) (mc : Config (MarkedAgent L K)) (h : 2 ≤ mc.card)
    (hP3 : ClockFrontMixed.ClockP3 (L := L) (K := K) (eraseConfig (L := L) (K := K) mc))
    (hAux : HourWindowAux (L := L) (K := K) mc) :
    markedK (L := L) (K := K) T θn mc
        {mc' | clockTaintedCount (L := L) (K := K) T mc
          < clockTaintedCount (L := L) (K := K) T mc'} ≤
      ENNReal.ofReal
        (((Multiset.countP (fun m : MarkedAgent L K => m.1.minute.val = T) mc : ℝ)
          / (mc.card : ℝ)) ^ 2)
      + ENNReal.ofReal
          (2 * ((taintedCount (L := L) (K := K) mc : ℝ) / (mc.card : ℝ))) :=
  clockTainted_rise_prob_le_of_subset (L := L) (K := K) T θn
    (HourWindowAux (L := L) (K := K))
    (clockTaintedRiseSubset_of_hourWindow (L := L) (K := K) T θn) mc h hP3 hAux

end ClockTaintDischarge

end ExactMajority
