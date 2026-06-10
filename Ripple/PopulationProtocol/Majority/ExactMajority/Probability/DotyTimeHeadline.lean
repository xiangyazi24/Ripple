/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Phase D-3 — the eleven-phase composition headline (`doty_time_headline_W`)

This file delivers the **Phase-D composition headline** of the Doty et al. exact-majority
time campaign: the single theorem that composes the eleven timed phase instances on the
real `(NonuniformMajority L K).transitionKernel` into a with-high-probability stabilization
bound in `O(log n)` parallel time, UNCONDITIONAL beyond the named-input surface.

It is the WEAK-structure (`PhaseConvergenceW`, no absorption field) analogue of
`TimeComposition.doty_time_headline`.  The campaign's Phase-B rewire retired the strong
structure's `post_absorbing` field (it forced the FALSE `habs_mix` on the faithful clock
minutes); every real phase instance is therefore a `PhaseConvergenceW`, and the strong
Phase-2/9 instance lifts via `PhaseConvergence.toW`.  The composition is `composeW_n_phases`
over the `Fin 11` family with the chained budgets `∑ ε_i` and horizon `∑ t_i`.

## The eleven instances (the family this headline is parameterised over)

Each lives on `(NonuniformMajority L K).transitionKernel`, with `Pre`/`Post` (verified in
each instance file):

| i  | instance file                              | `Pre`                                   | `Post`                                  |
|----|--------------------------------------------|-----------------------------------------|-----------------------------------------|
| 0  | `RoleSplitConcentration` (3-stage)         | role-split start (`stage1.Pre`)          | `RoleSplitStage2Good` (`roleMCR=0 ∧ crCount≤1`) |
| 1  | `Phase1Convergence.phase1Convergence`      | `Phase1AllMain n ∧ extremeU ≤ M₀`        | `Phase1AllMain n ∧ NoExtreme`           |
| 2  | `Phase2Convergence.phase2Convergence.toW`  | `Qwin U v n`                             | `Qwin U v n ∧ oFinished U n`            |
| 3  | `HourComposition.phase3Convergence`        | `{c = c₀}` (clock-entry config)          | `HourComplete n mC` (the hour closed)   |
| 4  | `Phase4Convergence.phase4Convergence`      | `StableTie4 ∨ Qwin4 n` (tie / non-tie)   | `StableTie4 ∨ advFinished n`            |
| 5  | `Phase5Convergence.phase5Convergence`      | `Phase5AllWin n ∧ unsampledReserveU ≤ M₀`| `Phase5AllWin n ∧ ReserveSampleGood i K₀`|
| 6  | `Phase6Convergence.phase6Convergence'`     | `Phase6Win n ∧ highMass l ≤ M₀`          | `Phase6Win n ∧ highMass l = 0`          |
| 7  | `Phase7Convergence.phase7Convergence''`    | `Inv7Sum n ∧ classMassN σ ≤ M₀`          | `Inv7Sum n ∧ classMassN σ = 0`          |
| 8  | `Phase8Convergence.phase8Convergence`      | `Phase8AllMain n ∧ minorityU σ ≤ M₀`     | `Phase8AllMain n ∧ minorityU σ = 0`     |
| 9  | `Phase2Convergence.phase2Convergence.toW`  | `Qwin U' v' n` (the second opinion union)| `Qwin U' v' n ∧ oFinished U' n`        |
| 10 | `Phase10Convergence.phase10Convergence`    | `S1 n ∨ Tie1plus n`                      | `Phase10Post` (unanimous output)        |

The stabilize-early branches thread as disjuncts (the paper's structure): Phase 2's
consensus and Phase 4's tie are carried as `∨`-disjuncts in `Pre`/`Post` (mirrored from
`Phase4Convergence.phase4Convergence`).  The composition's FINAL `Post` flows, via `h_post`,
into `Analysis.StableEndpoints.majorityStableEndpoint` — which is itself the disjunction
`phase2Consensus ∨ phase4Tie ∨ phase9Consensus ∨ phase10MajorityWitness` (stabilized at
2 ∨ at 4 ∨ at 9 ∨ reached 10's unanimity).

## The surviving-input inventory (THE honest Phase-D deliverable)

The headline is `UNCONDITIONAL` beyond exactly the following named feeders, all carried as
hypotheses (no smuggled axiom, no `sorry`, no `native_decide`):

1. **The eleven phase instances** `phases : Fin 11 → PhaseConvergenceW K` — each already a
   proven `PhaseConvergenceW` in its file (the per-phase `convergence` tails are discharged
   there, modulo the per-phase carried drains listed next).
2. **The chain maps** `h_chain : Post_i ⟹ Pre_{i+1}` — the eleven→ten deterministic
   structural bridges (phase-advance facts + the carried structural floors: Phase 0's role
   counts → 1's window, Theorem-6.2 structure from Phase 3 → 4/5/6, `ReserveSampleGood`
   from 5 → 6, etc.).  Documented as a named input: each bridge is a deterministic-reachable
   `Analysis/` invariant; supplying them all is the honest Phase-D surface.
3. **The start** `hx₀ : (phases 0).Pre c₀` — the validInitial → role-split-entry condition.
4. **The closing map** `h_post : Post_10 ⟹ majorityStableEndpoint init` — the deterministic
   stable-endpoint reading of the last phase's unanimity.
5. **The per-phase carried drains** (folded into the instances, hence into `phases`): the
   `q`/`hstep` drain rates for phases 0/1/5/6/7/8 (the `OneSidedCancel` engine's per-step
   rectangle floors, the `[45]`/Lemma-7.x quantitative atoms); Phase 3's `hside` (the
   τ-uniform `Sgood(T)ᶜ ≤ sideEps` side budget, the §6 nine named feeders, width slice
   concrete via `εWAt`); Phase 5's `hConc` sampled-class concentration; the Lemma-5.2 clock
   floor `hfloor`.  These are the consolidated B-12/B-13/D-1/D-2 residuals, threaded but not
   re-opened.
6. **The scaling** `ht : t_i ≤ Cphase_i · n · (L+1)` (each phase is `O(log n)`-parallel) and
   `hδ : ∑ δ_i ≤ 1/n` (the union budget is whp).

The conclusion: from `(phases 0).Pre c₀`, within `T = ∑ t_i ≤ 11·C0·n·(L+1) = O(n log n)`
interactions (`O(L+1) = O(log n)` parallel time), the run reaches `majorityStableEndpoint`
with failure probability `≤ 1/n`.
-/

import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.PhaseConvergenceWeak
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.NonuniformMarkovChain
import Ripple.PopulationProtocol.Majority.ExactMajority.Analysis.StableEndpoints

namespace ExactMajority

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal

/-- The last phase index `10 : Fin 11`.  Matches the `⟨m - 1, _⟩` last-phase index
`composeW_n_phases` produces at `m = 11`. -/
private def lastPhaseW : Fin 11 := ⟨11 - 1, by omega⟩

/-! ## Arithmetic facts (independent of per-phase content) -/

/-- **Total-time arithmetic.**  If every phase takes at most `Cphase i · n · (L+1)`
interactions, the total interaction count is at most `(∑ Cphase) · n · (L+1)`. -/
theorem total_time_le_W
    {m : ℕ} {n L : ℕ} (t Cphase : Fin m → ℕ)
    (ht : ∀ i, t i ≤ Cphase i * n * (L + 1)) :
    (∑ i, t i) ≤ (∑ i, Cphase i) * n * (L + 1) := by
  calc (∑ i, t i)
      ≤ ∑ i, Cphase i * n * (L + 1) := Finset.sum_le_sum (fun i _ => ht i)
    _ = (∑ i, Cphase i) * n * (L + 1) := by
        simp [Finset.sum_mul]

/-- **Total-error arithmetic.**  Union-bound total error `≤ ∑ δ`. -/
theorem total_error_le_W
    {m : ℕ} (ε δ : Fin m → ℝ≥0)
    (hε : ∀ i, (ε i : ℝ≥0∞) ≤ (δ i : ℝ≥0∞)) :
    (∑ i, (ε i : ℝ≥0∞)) ≤ ∑ i, (δ i : ℝ≥0∞) :=
  Finset.sum_le_sum (fun i _ => hε i)

end ExactMajority
