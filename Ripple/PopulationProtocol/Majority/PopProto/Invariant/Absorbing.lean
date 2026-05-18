/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Absorbing States

Configurations where all agents agree are absorbing: once the population
reaches all-X, all-Y, or all-B, it stays there forever.

Additionally, the all-B configuration is unreachable from any configuration
that has at least one opinionated agent, because `hasOpinion` is preserved
by every step.
-/

import Ripple.PopulationProtocol.Majority.PopProto.Probability.MarkovChain
import Mathlib.Probability.Kernel.Composition.Comp
import Mathlib.Probability.ProbabilityMassFunction.Monad

namespace PopProto

open State MeasureTheory ProbabilityTheory

namespace Config

variable {n : ℕ}

set_option linter.unnecessarySeqFocus false in
/-- If all agents hold state X, every interaction is a no-op. -/
theorem allX_step_eq (c : Config n) (hx : c.allX) (i r : State) :
    c.stepOrSelf i r = c := by
  unfold allX at hx
  obtain ⟨hxn, hb0, hy0⟩ := hx
  unfold stepOrSelf step
  have hs := c.sum_eq
  cases i <;> cases r <;> simp_all <;> split_ifs <;> simp_all

set_option linter.unnecessarySeqFocus false in
/-- If all agents hold state Y, every interaction is a no-op. -/
theorem allY_step_eq (c : Config n) (hy : c.allY) (i r : State) :
    c.stepOrSelf i r = c := by
  unfold allY at hy
  obtain ⟨hx0, hb0, hyn⟩ := hy
  unfold stepOrSelf step
  have hs := c.sum_eq
  cases i <;> cases r <;> simp_all <;> split_ifs <;> simp_all

set_option linter.unnecessarySeqFocus false in
/-- If all agents are blank, every interaction is a no-op. -/
theorem allB_step_eq (c : Config n) (hb : c.allB) (i r : State) :
    c.stepOrSelf i r = c := by
  unfold allB at hb
  obtain ⟨hx0, hbn, hy0⟩ := hb
  unfold stepOrSelf step
  have hs := c.sum_eq
  cases i <;> cases r <;> simp_all <;> split_ifs <;> simp_all

private theorem interactionPMF_sum_eq_one (c : Config n) (hn : n ≥ 2) :
    (Finset.univ.sum fun p : State × State => c.interactionPMF hn p) = 1 := by
  simpa using (c.interactionPMF hn).tsum_coe

/-- At all-X consensus, the one-step random transition distribution is a
point mass at the same configuration. -/
theorem allX_stepDist_eq_pure (c : Config n) (hn : n ≥ 2) (hx : c.allX) :
    c.stepDist hn = PMF.pure c := by
  ext c'
  by_cases h : c' = c
  · simp [stepDist, allX_step_eq c hx, h, interactionPMF_sum_eq_one c hn]
  · simp [stepDist, allX_step_eq c hx, h]

/-- At all-Y consensus, the one-step random transition distribution is a
point mass at the same configuration. -/
theorem allY_stepDist_eq_pure (c : Config n) (hn : n ≥ 2) (hy : c.allY) :
    c.stepDist hn = PMF.pure c := by
  ext c'
  by_cases h : c' = c
  · simp [stepDist, allY_step_eq c hy, h, interactionPMF_sum_eq_one c hn]
  · simp [stepDist, allY_step_eq c hy, h]

/-- At all-blank consensus, the one-step random transition distribution is a
point mass at the same configuration. -/
theorem allB_stepDist_eq_pure (c : Config n) (hn : n ≥ 2) (hb : c.allB) :
    c.stepDist hn = PMF.pure c := by
  ext c'
  by_cases h : c' = c
  · simp [stepDist, allB_step_eq c hb, h, interactionPMF_sum_eq_one c hn]
  · simp [stepDist, allB_step_eq c hb, h]

/-- At all-X consensus, the Markov kernel is the Dirac measure at the same
configuration. -/
theorem allX_transitionKernel_eq_dirac (c : Config n) (hn : n ≥ 2) (hx : c.allX) :
    transitionKernel hn c = MeasureTheory.Measure.dirac c := by
  rw [show transitionKernel hn c = (c.stepDist hn).toMeasure from rfl,
    allX_stepDist_eq_pure c hn hx]
  rw [PMF.toMeasure_pure]

/-- At all-Y consensus, the Markov kernel is the Dirac measure at the same
configuration. -/
theorem allY_transitionKernel_eq_dirac (c : Config n) (hn : n ≥ 2) (hy : c.allY) :
    transitionKernel hn c = MeasureTheory.Measure.dirac c := by
  rw [show transitionKernel hn c = (c.stepDist hn).toMeasure from rfl,
    allY_stepDist_eq_pure c hn hy]
  rw [PMF.toMeasure_pure]

/-- At all-blank consensus, the Markov kernel is the Dirac measure at the same
configuration. -/
theorem allB_transitionKernel_eq_dirac (c : Config n) (hn : n ≥ 2) (hb : c.allB) :
    transitionKernel hn c = MeasureTheory.Measure.dirac c := by
  rw [show transitionKernel hn c = (c.stepDist hn).toMeasure from rfl,
    allB_stepDist_eq_pure c hn hb]
  rw [PMF.toMeasure_pure]

/-- All-X configurations stay fixed under any finite number of Markov steps. -/
theorem allX_transitionKernel_pow_eq_dirac (c : Config n) (hn : n ≥ 2)
    (hx : c.allX) (t : ℕ) :
    (transitionKernel hn ^ t) c = Measure.dirac c := by
  induction t with
  | zero =>
      simp only [pow_zero]
      change Kernel.id c = Measure.dirac c
      exact Kernel.id_apply c
  | succ t ih =>
      exact Measure.ext (fun S hS => by
        rw [Kernel.pow_succ_apply_eq_lintegral _ _ _ hS, ih,
            MeasureTheory.lintegral_dirac' _
              (Kernel.measurable_coe _ hS),
            allX_transitionKernel_eq_dirac c hn hx])

/-- All-Y configurations stay fixed under any finite number of Markov steps. -/
theorem allY_transitionKernel_pow_eq_dirac (c : Config n) (hn : n ≥ 2)
    (hy : c.allY) (t : ℕ) :
    (transitionKernel hn ^ t) c = Measure.dirac c := by
  induction t with
  | zero =>
      simp only [pow_zero]
      change Kernel.id c = Measure.dirac c
      exact Kernel.id_apply c
  | succ t ih =>
      exact Measure.ext (fun S hS => by
        rw [Kernel.pow_succ_apply_eq_lintegral _ _ _ hS, ih,
            MeasureTheory.lintegral_dirac' _
              (Kernel.measurable_coe _ hS),
            allY_transitionKernel_eq_dirac c hn hy])

/-- All-blank configurations stay fixed under any finite number of Markov steps. -/
theorem allB_transitionKernel_pow_eq_dirac (c : Config n) (hn : n ≥ 2)
    (hb : c.allB) (t : ℕ) :
    (transitionKernel hn ^ t) c = Measure.dirac c := by
  induction t with
  | zero =>
      simp only [pow_zero]
      change Kernel.id c = Measure.dirac c
      exact Kernel.id_apply c
  | succ t ih =>
      exact Measure.ext (fun S hS => by
        rw [Kernel.pow_succ_apply_eq_lintegral _ _ _ hS, ih,
            MeasureTheory.lintegral_dirac' _
              (Kernel.measurable_coe _ hS),
            allB_transitionKernel_eq_dirac c hn hb])

/-- Consensus configurations are one-step absorbing. -/
theorem consensus_transitionKernel_eq_dirac (c : Config n) (hn : n ≥ 2)
    (hc : c.isConsensus) :
    transitionKernel hn c = Measure.dirac c := by
  rcases hc with hx | hy
  · exact allX_transitionKernel_eq_dirac c hn hx
  · exact allY_transitionKernel_eq_dirac c hn hy

/-- Consensus configurations stay fixed under any finite number of Markov steps. -/
theorem consensus_transitionKernel_pow_eq_dirac (c : Config n) (hn : n ≥ 2)
    (hc : c.isConsensus) (t : ℕ) :
    (transitionKernel hn ^ t) c = Measure.dirac c := by
  rcases hc with hx | hy
  · exact allX_transitionKernel_pow_eq_dirac c hn hx t
  · exact allY_transitionKernel_pow_eq_dirac c hn hy t

set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
/-- If we have at least one opinionated agent, this is preserved by any step.
    This is the key lemma: the "last non-blank agent" cannot be eliminated
    because when it interacts with a blank, it converts the blank. -/
theorem hasOpinion_preserved (c : Config n) (i r : State) (c' : Config n)
    (h : c.step i r = some c') (hop : c.hasOpinion) :
    c'.hasOpinion := by
  unfold hasOpinion opinionated at *
  simp only [step] at h
  cases i <;> cases r <;> simp_all <;>
    (try omega) <;>
    (first | (obtain ⟨_, rfl⟩ := h) | (obtain ⟨⟨_, _⟩, rfl⟩ := h)) <;>
    simp <;> omega

/-- If the initial configuration has at least one opinionated agent,
    then all-B is unreachable in one step. -/
theorem not_allB_of_opinionated_step (c : Config n) (i r : State) (c' : Config n)
    (h : c.step i r = some c') (hop : c.hasOpinion) :
    ¬c'.allB := by
  intro hb
  have hop' := hasOpinion_preserved c i r c' h hop
  unfold allB at hb
  unfold hasOpinion opinionated at hop'
  omega

end Config
end PopProto
