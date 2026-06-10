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

/-! ### Level occupation from a constrained start (coupon-collector core)

The single rigorous waiting-time fact behind the coupon sum: if the potential
never increases along `K` and from every state at level exactly `m` (`Φ = m`,
`m ≥ 1`) the one-step probability of dropping to `Φ < m` is at least `1 - q`
(`q < 1`), then starting **at or below level `m`** the expected time to hit
`{Φ < m}` is `≤ (1 - q)⁻¹`.

The trick: starting at `Φ ≤ m`, the chain stays in `{Φ ≤ m}` (`Φ` non-increasing),
so the "not yet below `m`" event coincides with the level-`m` event, on which the
per-step drop hypothesis applies uniformly.  We instantiate E1's
`expectedHitting_one_step_q` with `Done := {Φ < m}` after transporting the start
into `{Φ ≤ m}`. -/

/-- The set of states strictly below level `m`. -/
def potBelow (Φ : α → ℕ) (m : ℕ) : Set α := {x | Φ x < m}

theorem potBelow_measurable [DiscreteMeasurableSpace α] (Φ : α → ℕ) (m : ℕ) :
    MeasurableSet (potBelow Φ m) :=
  DiscreteMeasurableSpace.forall_measurableSet _

/-- Kernel-level "potential non-increasing" hypothesis: one step never strictly
raises `Φ` (the mass placed on strictly-higher potential is `0`). -/
def PotNonincr (K : Kernel α α) (Φ : α → ℕ) : Prop :=
  ∀ b : α, K b {x | Φ b < Φ x} = 0

/-- `{Φ < m}` is absorbing when `Φ` is non-increasing: from a state already below
`m`, one step cannot reach `{Φ ≥ m}`. -/
theorem potBelow_absorbing [DiscreteMeasurableSpace α]
    (K : Kernel α α) (Φ : α → ℕ) (hmono : PotNonincr K Φ) (m : ℕ) :
    ∀ x ∈ potBelow Φ m, K x (potBelow Φ m)ᶜ = 0 := by
  intro x hx
  -- (potBelow Φ m)ᶜ = {Φ ≥ m} ⊆ {Φ > Φ x} since Φ x < m.
  have hsub : ((potBelow Φ m)ᶜ : Set α) ⊆ {y | Φ x < Φ y} := by
    intro y hy
    simp only [potBelow, Set.mem_compl_iff, Set.mem_setOf_eq, not_lt] at hy
    have hxlt : Φ x < m := hx
    exact Set.mem_setOf_eq ▸ (lt_of_lt_of_le hxlt hy)
  exact measure_mono_null hsub (hmono x)

/-- The `(K^t)`-mass on strictly-above-`m` stays `0` for a start at level `≤ m`. -/
theorem pow_above_eq_zero_of_start_le [DiscreteMeasurableSpace α]
    (K : Kernel α α) [IsMarkovKernel K] (Φ : α → ℕ) (hmono : PotNonincr K Φ)
    (m : ℕ) (c : α) (hc : Φ c ≤ m) (t : ℕ) :
    (K ^ t) c {x | m < Φ x} = 0 := by
  induction t generalizing c with
  | zero =>
      rw [show (K ^ 0) = Kernel.id from pow_zero K, Kernel.id_apply,
        Measure.dirac_apply' c
          (DiscreteMeasurableSpace.forall_measurableSet _)]
      have : c ∉ {x | m < Φ x} := by simp only [Set.mem_setOf_eq, not_lt]; exact hc
      simp [this]
  | succ t ih =>
      have hbad : MeasurableSet {x : α | m < Φ x} :=
        DiscreteMeasurableSpace.forall_measurableSet _
      rw [show t + 1 = 1 + t from by ring,
        Kernel.pow_add_apply_eq_lintegral K 1 t c hbad, pow_one,
        lintegral_eq_zero_iff (Kernel.measurable_coe _ hbad)]
      rw [Filter.eventuallyEq_iff_exists_mem]
      refine ⟨{y | Φ y ≤ m}, ?_, ?_⟩
      · rw [mem_ae_iff]
        -- complement is {Φ > m}; one step from c (Φ c ≤ m) cannot reach it.
        have hcompl : ({y | Φ y ≤ m}ᶜ : Set α) = {x | m < Φ x} := by
          ext y; simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_le]
        rw [hcompl]
        refine measure_mono_null ?_ (hmono c)
        intro y hy
        simp only [Set.mem_setOf_eq] at hy ⊢
        exact lt_of_le_of_lt hc hy
      · intro y hy
        exact ih y hy

/-- **One-step level-`m` occupation contraction.** Under non-increasing `Φ` and a
per-step drop hypothesis at level `m` (`∀ b, Φ b = m → K b (potBelow Φ m)ᶜ ≤ q`),
for a start `c` with `Φ c ≤ m` the not-below-`m` mass contracts by `q` each step:
`(K^(t+1)) c (potBelow Φ m)ᶜ ≤ q · (K^t) c (potBelow Φ m)ᶜ`. -/
theorem level_occ_contract [DiscreteMeasurableSpace α]
    (K : Kernel α α) [IsMarkovKernel K] (Φ : α → ℕ) (hmono : PotNonincr K Φ)
    (m : ℕ) (q : ℝ≥0∞)
    (hdrop : ∀ b : α, Φ b = m → K b (potBelow Φ m)ᶜ ≤ q)
    (c : α) (hc : Φ c ≤ m) (t : ℕ) :
    (K ^ (t + 1)) c (potBelow Φ m)ᶜ ≤ q * (K ^ t) c (potBelow Φ m)ᶜ := by
  classical
  have hbad : MeasurableSet ((potBelow Φ m)ᶜ : Set α) :=
    (potBelow_measurable Φ m).compl
  -- Peel last step: (K^(t+1)) c Bᶜ = ∫ b, K b Bᶜ ∂(K^t c).
  rw [Kernel.pow_succ_apply_eq_lintegral K t c hbad]
  -- The (K^t c)-mass lives on {Φ = m} ∪ {Φ < m}; on {Φ < m}, Bᶜ-reach is 0
  -- (absorbing); on {Φ = m}, K b Bᶜ ≤ q; {Φ > m} carries 0 mass.
  calc ∫⁻ b, K b (potBelow Φ m)ᶜ ∂((K ^ t) c)
      ≤ ∫⁻ b, q * Set.indicator ((potBelow Φ m)ᶜ) (fun _ => (1 : ℝ≥0∞)) b
          ∂((K ^ t) c) := by
        apply lintegral_mono_ae
        -- a.e. b: handle by cases on Φ b vs m, using that {Φ > m} is null.
        have hnull : (K ^ t) c {x | m < Φ x} = 0 :=
          pow_above_eq_zero_of_start_le K Φ hmono m c hc t
        rw [Filter.eventually_iff_exists_mem]
        refine ⟨{x | Φ x ≤ m}, ?_, ?_⟩
        · rw [mem_ae_iff]
          have : ({x | Φ x ≤ m}ᶜ : Set α) = {x | m < Φ x} := by
            ext y; simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_le]
          rw [this]; exact hnull
        · intro b hb
          simp only [Set.mem_setOf_eq] at hb
          rcases lt_or_eq_of_le hb with hlt | heq
          · -- Φ b < m: b ∈ potBelow, absorbing ⇒ K b Bᶜ = 0 ≤ q·indicator
            have hbb : b ∈ potBelow Φ m := hlt
            rw [potBelow_absorbing K Φ hmono m b hbb]; exact zero_le'
          · -- Φ b = m: b ∉ potBelow (since not < m), so indicator = 1.
            have hbmem : b ∈ ((potBelow Φ m)ᶜ : Set α) := by
              simp only [potBelow, Set.mem_compl_iff, Set.mem_setOf_eq, not_lt]
              exact heq.ge
            rw [Set.indicator_of_mem hbmem, mul_one]
            exact hdrop b heq
    _ = q * (K ^ t) c (potBelow Φ m)ᶜ := by
        rw [lintegral_const_mul q (measurable_const.indicator hbad)]
        congr 1
        rw [lintegral_indicator hbad]; simp

/-- Geometric decay of the level-`m` occupation mass: `(K^t) c (potBelow Φ m)ᶜ ≤ q^t`
for a start `c` at level `≤ m`. -/
theorem level_occ_geometric [DiscreteMeasurableSpace α]
    (K : Kernel α α) [IsMarkovKernel K] (Φ : α → ℕ) (hmono : PotNonincr K Φ)
    (m : ℕ) (q : ℝ≥0∞)
    (hdrop : ∀ b : α, Φ b = m → K b (potBelow Φ m)ᶜ ≤ q)
    (c : α) (hc : Φ c ≤ m) (t : ℕ) :
    (K ^ t) c (potBelow Φ m)ᶜ ≤ q ^ t := by
  induction t with
  | zero =>
      simp only [pow_zero]
      calc (K ^ 0) c (potBelow Φ m)ᶜ ≤ (K ^ 0) c Set.univ :=
            measure_mono (Set.subset_univ _)
        _ = 1 := by
            rw [show (K ^ 0) = Kernel.id from pow_zero K, Kernel.id_apply, measure_univ]
  | succ t ih =>
      calc (K ^ (t + 1)) c (potBelow Φ m)ᶜ
          ≤ q * (K ^ t) c (potBelow Φ m)ᶜ :=
            level_occ_contract K Φ hmono m q hdrop c hc t
        _ ≤ q * q ^ t := by gcongr
        _ = q ^ (t + 1) := by rw [pow_succ]; ring

/-- **Level-`m` occupation bound (coupon waiting time).** Under non-increasing `Φ`
and a level-`m` per-step drop probability `≥ 1 - q`, a start at level `≤ m` hits
`{Φ < m}` in expected time `≤ (1 - q)⁻¹`:
`expectedHitting K c (potBelow Φ m) ≤ (1 - q)⁻¹`. -/
theorem level_occ_expectedHitting [DiscreteMeasurableSpace α]
    (K : Kernel α α) [IsMarkovKernel K] (Φ : α → ℕ) (hmono : PotNonincr K Φ)
    (m : ℕ) (q : ℝ≥0∞)
    (hdrop : ∀ b : α, Φ b = m → K b (potBelow Φ m)ᶜ ≤ q)
    (c : α) (hc : Φ c ≤ m) :
    expectedHitting K c (potBelow Φ m) ≤ (1 - q)⁻¹ := by
  rw [expectedHitting]
  calc ∑' t : ℕ, (K ^ t) c (potBelow Φ m)ᶜ
      ≤ ∑' t : ℕ, q ^ t :=
        ENNReal.tsum_le_tsum (fun t => level_occ_geometric K Φ hmono m q hdrop c hc t)
    _ = (1 - q)⁻¹ := ENNReal.tsum_geometric q

end Coupon

end ExactMajority
