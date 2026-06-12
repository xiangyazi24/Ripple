/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Package F: opaque slots, start/end pins, and seam guards for the V5.1 residual bundle.

This file is append-only.  It provides exact-shape producers or adapters for:

* `WorkInputsV51.work0`, `work2`, `work3`, `work9`;
* `DotyResidualAtomsV51.hWork0PreOfStart`;
* `DotyResidualAtomsV51.hPhase10Sign`;
* the counter-reset no-overshoot field and the five named non-reset guard fields;
* `DotyResidualAtomsV51.hSeedStep` from the remaining per-seam seed event.
-/

import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.FinalAssemblyV51
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.EndpointWiring
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.SmallSweep
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.ClockZeroTail

namespace ExactMajority
namespace PkgFAtoms

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators NNReal

variable {L K : ℕ}

/-! ## WorkInputsV51 work-slot producers -/

/-- Produces the `WorkInputsV51.work0` field from the landed role-split composition constructor. -/
noncomputable def work0_of_two_stage
    (stage1 stage15 stage2 :
      PhaseConvergenceW (NonuniformMajority L K).transitionKernel)
    (h_chain1 : ∀ x, stage1.Post x → stage15.Pre x)
    (h_chain2 : ∀ x, stage15.Post x → stage2.Pre x) :
    PhaseConvergenceW (NonuniformMajority L K).transitionKernel :=
  EndpointWiring.roleSplitW_of_two_stage (L := L) (K := K)
    stage1 stage15 stage2 h_chain1 h_chain2

/-- Produces the `WorkInputsV51.work2` field from the calibrated phase-2 union constructor. -/
noncomputable def work2_calibratedUnion (n : ℕ) (hn : 2 ≤ n) (s : ℝ) (hs : 0 < s)
    (t : ℕ) (ε : ℝ≥0)
    (hε : ENNReal.ofReal
        (1 - (((n - 1 : ℕ) : ℝ) / ((n : ℝ) * ((n : ℝ) - 1))) * (1 - Real.exp (-s))) ^ t *
        ENNReal.ofReal (Real.exp (s * ((n : ℝ) - 1))) / 1 ≤ (ε : ℝ≥0∞)) :
    PhaseConvergenceW (NonuniformMajority L K).transitionKernel :=
  SmallSweep.calibratedUnionW (L := L) (K := K) n hn s hs t ε hε

/-- Produces the `WorkInputsV51.work3` field from the bounded-horizon clock-side constructor. -/
noncomputable def work3_phase3_bounded (n mC : ℕ) (hn : 2 ≤ n) (hmC : 2 ≤ mC)
    (hLK : 0 < K * (L + 1)) (hLK1 : 0 < K * (L + 1) - 1)
    (tseed tbulk : ℕ) (htbulk : 0 < tbulk) (εbulk : ℝ≥0)
    (hεb : ClockKilledMinute.minuteRate n mC ^ tbulk *
        ENNReal.ofReal (Real.exp (Real.log 2 * (ClockRealBulk.bulkHi mC : ℝ))) / 1
          ≤ (εbulk : ℝ≥0∞))
    (c₀ : Config (AgentState L K)) (εside : ℝ≥0∞)
    (hside : ∀ T τ, τ < (L + 1) *
        EarlyDripMarked.Mhour (L := L) (K := K) tseed tbulk →
      (ClockKilledMinute.realκ L K ^ τ) c₀
        (ClockUnconditional.Sgood (L := L) (K := K) n mC T)ᶜ ≤ εside)
    (εtot : ℝ≥0)
    (hεtot : ClockBudgets.εclock L K tbulk (εbulk : ℝ≥0∞) εside ≤
      (εtot : ℝ≥0∞)) :
    PhaseConvergenceW (NonuniformMajority L K).transitionKernel :=
  EndpointWiring.phase3Convergence_bounded (L := L) (K := K)
    n mC hn hmC hLK hLK1 tseed tbulk htbulk εbulk hεb c₀ εside hside εtot hεtot

/-- Produces the `WorkInputsV51.work9` field; it is the same calibrated union constructor as slot 2. -/
noncomputable def work9_calibratedUnion (n : ℕ) (hn : 2 ≤ n) (s : ℝ) (hs : 0 < s)
    (t : ℕ) (ε : ℝ≥0)
    (hε : ENNReal.ofReal
        (1 - (((n - 1 : ℕ) : ℝ) / ((n : ℝ) * ((n : ℝ) - 1))) * (1 - Real.exp (-s))) ^ t *
        ENNReal.ofReal (Real.exp (s * ((n : ℝ) - 1))) / 1 ≤ (ε : ℝ≥0∞)) :
    PhaseConvergenceW (NonuniformMajority L K).transitionKernel :=
  SmallSweep.calibratedUnionW (L := L) (K := K) n hn s hs t ε hε

/-! ## Start and sign fields -/

/-- Exact adapter for `WorkInputsV51.hWork0PreOfStart` when `work0` is the package-F role-split slot. -/
theorem hWork0PreOfStart_of_work0_eq {n : ℕ} {c₀ : Config (AgentState L K)}
    {wi : FinalAssemblyV51.WorkInputsV51 (L := L) (K := K) n}
    (stage1 stage15 stage2 :
      PhaseConvergenceW (NonuniformMajority L K).transitionKernel)
    (h_chain1 : ∀ x, stage1.Post x → stage15.Pre x)
    (h_chain2 : ∀ x, stage15.Post x → stage2.Pre x)
    (hwork0 : wi.work0 = work0_of_two_stage (L := L) (K := K)
      stage1 stage15 stage2 h_chain1 h_chain2)
    (hPre0 : RoleSplitConcentration.Phase0Initial (L := L) (K := K) n c₀ →
      stage1.Pre c₀) :
    RoleSplitConcentration.Phase0Initial (L := L) (K := K) n c₀ →
      (wi.work0).Pre c₀ := by
  intro hstart
  rw [hwork0]
  exact hPre0 hstart

/-- The V5.1 slot-0 pin consumes the produced `hWork0PreOfStart` and the primitive start. -/
theorem hStart_to_phase0_pre_v51 {n C0 : ℕ}
    (ra : FinalAssemblyV51.DotyResidualAtomsV51 (L := L) (K := K) n C0) :
    (FinalAssemblyV51.phases'V51 (L := L) (K := K) ra ⟨0, by omega⟩).Pre ra.c₀ :=
  FinalAssemblyV51.hx₀_of_start_v51 (L := L) (K := K) ra

/-- Produces the `DotyResidualAtomsV51.hPhase10Sign` field from the rooted phase-10 entry data. -/
theorem hPhase10Sign_of_rooted {init : Config (AgentState L K)}
    (hinit : validInitial init)
    (hAllRoot : ∀ a ∈ init, a.phase.val = 10) (hactRoot : hasActiveAgent init)
    (hreach : ∀ c, Phase10Drop.Phase10Post (L := L) (K := K) c →
      (NonuniformMajority L K).Reachable init c) :
    AtomsV2.Phase10SignMatch (L := L) (K := K) init :=
  SmallSweep.phase10SignMatch_of_rooted (L := L) (K := K)
    hinit hAllRoot hactRoot hreach

/-! ## No-overshoot field and the five non-reset guards -/

/-- The exact V51 no-overshoot seam-field shape for one seam phase `p`. -/
abbrev NoOvershootField (p n tseam : ℕ) (εovershoot : ℝ≥0) : Prop :=
  ∀ c : Config (AgentState L K),
    (SeamEpidemics.allPhaseGe (L := L) (K := K) p n c ∧
      SeamEpidemics.advTriggered (L := L) (K := K) (p + 1) c) →
    ((NonuniformMajority L K).transitionKernel ^ tseam) c
        {c' | ¬ SeamNoOvershoot.NoOvershoot (L := L) (K := K) p c'}
      ≤ (εovershoot : ℝ≥0∞)

/-- Produces the no-overshoot field for counter-reset destinations `{1,6,7,8}`. -/
theorem hNoOvershoot_counterReset_field (p n tseam : ℕ) (εovershoot : ℝ≥0)
    (hq : SeamNoOvershoot.CounterResetDest (p + 1))
    (hdisp : SeamNoOvershoot.SeamRegimeDispatch (L := L) (K := K) p)
    (hWf : ∀ c : Config (AgentState L K), SeamNoOvershoot.Wf (L := L) (K := K) c)
    (hn : 1 ≤ n) (hn2 : 2 ≤ n)
    (hlog : Real.log (n : ℝ) ≤ (L + 1 : ℕ))
    (ht : tseam ≤ n * (L + 1))
    (hcard : ∀ c : Config (AgentState L K),
      (SeamEpidemics.allPhaseGe (L := L) (K := K) p n c ∧
        SeamEpidemics.advTriggered (L := L) (K := K) (p + 1) c) →
      Multiset.card c = n)
    (hStartNoOver : ∀ c : Config (AgentState L K),
      (SeamEpidemics.allPhaseGe (L := L) (K := K) p n c ∧
        SeamEpidemics.advTriggered (L := L) (K := K) (p + 1) c) →
      SeamNoOvershoot.NoOvershoot (L := L) (K := K) p c)
    (hEntry : ∀ c : Config (AgentState L K),
      (SeamEpidemics.allPhaseGe (L := L) (K := K) p n c ∧
        SeamEpidemics.advTriggered (L := L) (K := K) (p + 1) c) →
      SeamNoOvershoot.SeamEntryFullCounter (L := L) (K := K) p c)
    (hε : (tseam : ℝ≥0∞) * ENNReal.ofReal (Real.exp (-(40 * (L + 1) : ℕ)))
        ≤ (εovershoot : ℝ≥0∞)) :
    NoOvershootField (L := L) (K := K) p n tseam εovershoot :=
  SeamNoOvershoot.hNoOvershoot_field_of_entry (L := L) (K := K)
    p n tseam εovershoot hq hdisp hWf hn hn2 hlog ht hcard hStartNoOver hEntry hε

/-- Destination phase 2 guard: untimed opinion-union advance, carried as this exact field. -/
theorem hNoOvershoot_phase2_guard {n tseam : ℕ} {εovershoot : ℝ≥0}
    (h : NoOvershootField (L := L) (K := K) 1 n tseam εovershoot) :
    NoOvershootField (L := L) (K := K) 1 n tseam εovershoot :=
  h

/-- Destination phase 3 guard: minute machinery, carried as this exact field. -/
theorem hNoOvershoot_phase3_guard {n tseam : ℕ} {εovershoot : ℝ≥0}
    (h : NoOvershootField (L := L) (K := K) 2 n tseam εovershoot) :
    NoOvershootField (L := L) (K := K) 2 n tseam εovershoot :=
  h

/-- Destination phase 4 guard: untimed big-bias advance, carried as this exact field. -/
theorem hNoOvershoot_phase4_guard {n tseam : ℕ} {εovershoot : ℝ≥0}
    (h : NoOvershootField (L := L) (K := K) 3 n tseam εovershoot) :
    NoOvershootField (L := L) (K := K) 3 n tseam εovershoot :=
  h

/-- Destination phase 5 guard: hour machinery without counter reset, carried as this exact field. -/
theorem hNoOvershoot_phase5_guard {n tseam : ℕ} {εovershoot : ℝ≥0}
    (h : NoOvershootField (L := L) (K := K) 4 n tseam εovershoot) :
    NoOvershootField (L := L) (K := K) 4 n tseam εovershoot :=
  h

/-- Destination phase 9 guard: untimed pre-phase-10 union, carried as this exact field. -/
theorem hNoOvershoot_phase9_guard {n tseam : ℕ} {εovershoot : ℝ≥0}
    (h : NoOvershootField (L := L) (K := K) 8 n tseam εovershoot) :
    NoOvershootField (L := L) (K := K) 8 n tseam εovershoot :=
  h

/-- The five package-F guard seams are exactly outside the counter-reset producer. -/
theorem guarded_noOvershoot_not_counterReset {q : ℕ}
    (h : q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 8) :
    ¬ SeamNoOvershoot.CounterResetDest (q + 1) :=
  SeamNoOvershoot.not_counterResetDest_of_guarded h

/-! ## Drain-seam one-step seed field -/

/-- The exact V51 one-step seed field shape for a work family and seam map. -/
abbrev SeedStepField
    (work : Fin 11 → PhaseConvergenceW (NonuniformMajority L K).transitionKernel)
    (seamP : Fin 10 → ℕ) : Prop :=
  ∀ (k : Fin 10) (c : Config (AgentState L K)),
    (work ⟨k.val, by omega⟩).Post c →
    ((NonuniformMajority L K).transitionKernel ^ 1) c
        {c' | ¬ SeamEpidemics.advTriggered (L := L) (K := K) (seamP k + 1) c'} = 0

/-- Produces the V51 `hSeedStep` field from the still-needed per-seam seed event family. -/
theorem hSeedStep_v51_of_event {n : ℕ}
    (wi : FinalAssemblyV51.WorkInputsV51 (L := L) (K := K) n)
    (seamP : Fin 10 → ℕ)
    (hEvent : ∀ k : Fin 10,
      SmallSweep.SeedStepEvent (L := L) (K := K) (seamP k)
        ((FinalAssemblyV51.dotyWorkSurvivalV51 (L := L) (K := K) wi
          ⟨k.val, by omega⟩).Post)) :
    SeedStepField (L := L) (K := K)
      (FinalAssemblyV51.dotyWorkSurvivalV51 (L := L) (K := K) wi) seamP :=
  SmallSweep.hSeedStep_of_event (L := L) (K := K)
    (FinalAssemblyV51.dotyWorkSurvivalV51 (L := L) (K := K) wi) seamP hEvent

/-- The timed seed applies once the drained all-clock unseeded state is supplied explicitly. -/
theorem seedStepEvent_of_drained_state (p n : ℕ)
    (workPost : Config (AgentState L K) → Prop)
    (hp : p ∈ ({0, 1, 5, 6, 7, 8} : Finset ℕ))
    (hn : 2 ≤ n)
    (hdrained : ∀ c, workPost c →
      ConditionalPhaseProgress.AllClockGEpCard (L := L) (K := K) p n c ∧
      ConditionalPhaseProgress.clockCounterSumAt (L := L) (K := K) p c = 0 ∧
      SeamEpidemics.geCount (L := L) (K := K) (p + 1) c = 0) :
    SmallSweep.SeedStepEvent (L := L) (K := K) p workPost :=
  SmallSweep.seedStepEvent_needs_drained_state (L := L) (K := K)
    p n workPost hp hn hdrained

end PkgFAtoms
end ExactMajority
