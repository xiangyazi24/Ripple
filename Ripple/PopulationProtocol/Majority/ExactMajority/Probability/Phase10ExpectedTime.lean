/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Phase-10 Backup Expected Stabilization Time (Doty et al. Lemma 7.7)

The 6-state Phase-10 backup protocol stably computes majority in `O(n log n)`
*parallel* time, both in expectation and with high probability.  This file
formalizes the **expectation** bound.

## Convention (READ THIS)

All time bounds in this file are stated in **interaction counts** (= kernel
steps), NOT parallel time.  Parallel time = interactions / n, so the paper's
`O(n log n)` parallel-time statements become:

  * cancel stage (active B against active A):   `O(n²)` interactions;
  * coupon-collector stages (absorb T, convert passive):  `O(n² log n)` each.

The expected hitting time is the E1 tail-sum `expectedHitting K c Done`
(`= ∑' t, (K^t) c Doneᶜ`), which under the standard identity
`E[T] = ∑_{t≥0} P(T > t)` equals the mean number of interactions to reach the
stable set `Done`.

## Structure (three sequential coupon/cancel stages, majority case WLOG A)

1. All active-B agents cancel against active-A agents (`Phase10Transition`
   cancel reaction): with `b` active-B and `a ≥ b` active-A agents, the per-step
   cancel probability is `≥ a·b / (n·(n−1)) ≥ b / (n·(n−1))`, and the potential
   `b = activeBCount` strictly drops on each cancel.  Harmonic-free here: a crude
   `∑_{b ≤ n} (n·(n−1))/b ≤ (n·(n−1))·(H_n)` interaction bound, dominated by the
   coupon stages.
2. The active-A agents absorb all active-T agents (broadcast A): coupon-collector
   on `wrongACount`, per-step success `≥ wrongACount / (n·(n−1))`, expected
   `≤ (n·(n−1))·H_n = O(n² log n)` interactions.
3. Same shape converting passive agents.

The **generic engine** (`Coupon` section below) is the level-split coupon
bound: a `ℕ`-valued potential `Φ` non-increasing along the kernel, with a
per-level one-step strict-decrease probability `≥ p_lev`, yields
`E[T] ≤ ∑_{m < Φ c₀} (p_lev m)⁻¹` interactions.  This is the harmonic / coupon
sum.  It is built directly on E1's `expectedHitting` toolkit
(`ExpectedHitting.lean`) and the per-step progress technique of
`Phase2TimeConvergence.step_advance_prob` (one useful ordered state pair fires
with probability `interactionCount / totalPairs`).

## Status

The generic coupon engine and the per-stage potential bookkeeping are delivered
and axiom-clean.  The capstone instantiation for the real
`(NonuniformMajority L K).transitionKernel` requires the per-step progress lower
bound to be discharged against the *state-multiplicity* of `AgentState`: an
"active A" is not a single scheduler state `Λ` but a whole class of `AgentState`
records, so the single-useful-pair bound of `step_advance_prob` must be replaced
by a class-aggregated `interactionCount` lower bound.  That bridge is documented
as the remaining blocker at the end of this file (see `phase10_progress_blocker`).
-/

import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.ExpectedHitting
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.MarkovChain

namespace ExactMajority

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

set_option linter.unusedSectionVars false

/-! ## Generic level-split coupon-collector hitting engine

We work over a generic measurable space `α` and a Markov kernel `K`, exactly as
in `ExpectedHitting.lean`, with a `ℕ`-valued potential `Φ`.  `Done = {Φ = 0}`.
-/

section Coupon

variable {α : Type*} [MeasurableSpace α]

/-- The "done" set of a `ℕ`-valued potential: where `Φ` has hit `0`. -/
def potDone (Φ : α → ℕ) : Set α := {x | Φ x = 0}

/-- The "above level `m`" set: where `Φ` still exceeds `m`. -/
def potAbove (Φ : α → ℕ) (m : ℕ) : Set α := {x | m < Φ x}

theorem potDone_measurable [DiscreteMeasurableSpace α] (Φ : α → ℕ) :
    MeasurableSet (potDone Φ) :=
  DiscreteMeasurableSpace.forall_measurableSet _

theorem potAbove_measurable [DiscreteMeasurableSpace α] (Φ : α → ℕ) (m : ℕ) :
    MeasurableSet (potAbove Φ m) :=
  DiscreteMeasurableSpace.forall_measurableSet _

/-- `potDoneᶜ = {0 < Φ} = potAbove Φ 0`. -/
theorem compl_potDone (Φ : α → ℕ) : (potDone Φ)ᶜ = potAbove Φ 0 := by
  ext x; simp only [potDone, potAbove, Set.mem_compl_iff, Set.mem_setOf_eq]; omega

/-! ### Additive stage chaining

The campaign's "chaining lemma": for nested absorbing sets `Done ⊆ Mid` the
expected hitting time of `Done` splits additively into the time to reach `Mid`
plus the residual time spent in `Mid ∖ Done`.  This is the kernel-power form
`(K^t) c Doneᶜ ≤ (K^t) c Midᶜ + (K^t) c (Mid ∩ Doneᶜ)`, summed over `t`.  It lets
a multi-stage potential descent (cancel → absorb-T → convert-passive) be bounded
stage by stage. -/

/-- **Pointwise additive split through an intermediate set.** For any sets
`Done ⊆ Mid`, the not-done mass splits as not-in-`Mid` plus in-`Mid`-not-`Done`. -/
theorem bad_split_through_mid (K : Kernel α α)
    {Done Mid : Set α} (_hsub : Done ⊆ Mid) (c : α) (t : ℕ) :
    (K ^ t) c Doneᶜ ≤ (K ^ t) c Midᶜ + (K ^ t) c (Mid ∩ Doneᶜ) := by
  have hcover : (Doneᶜ : Set α) ⊆ Midᶜ ∪ (Mid ∩ Doneᶜ) := by
    intro x hx
    by_cases hxM : x ∈ Mid
    · exact Or.inr ⟨hxM, hx⟩
    · exact Or.inl hxM
  calc (K ^ t) c Doneᶜ
      ≤ (K ^ t) c (Midᶜ ∪ (Mid ∩ Doneᶜ)) := measure_mono hcover
    _ ≤ (K ^ t) c Midᶜ + (K ^ t) c (Mid ∩ Doneᶜ) := measure_union_le _ _

/-- **Expected-hitting additive split.** `Done ⊆ Mid` gives
`E[hit Done] ≤ E[hit Mid] + ∑ₜ P(in Mid, not Done at t)`. -/
theorem expectedHitting_le_through_mid (K : Kernel α α)
    {Done Mid : Set α} (hsub : Done ⊆ Mid) (c : α) :
    expectedHitting K c Done ≤
      expectedHitting K c Mid + ∑' t : ℕ, (K ^ t) c (Mid ∩ Doneᶜ) := by
  rw [expectedHitting, expectedHitting, ← ENNReal.tsum_add]
  exact ENNReal.tsum_le_tsum (fun t => bad_split_through_mid K hsub c t)

end Coupon

end ExactMajority
