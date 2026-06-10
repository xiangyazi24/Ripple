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
import Ripple.PopulationProtocol.Majority.ExactMajority.Analysis.Phase10Backup
import Ripple.PopulationProtocol.Majority.ExactMajority.Analysis.Phase0Convergence
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.ClockRealMixed
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.HourCouplingV2

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

/-! ### Full coupon assembly (harmonic sum)

Chaining the per-level occupation bound down the potential ladder gives the total
expected hitting time of `Done = {Φ = 0}` as the sum of the per-level waiting
times `∑_{m=1}^{M} (1 - q_m)⁻¹`.  This is the harmonic / coupon sum: for the
Phase-10 coupon stages `q_m = 1 - m/(n(n−1))`, so `(1-q_m)⁻¹ = n(n−1)/m` and the
sum is `n(n−1)·H_M = O(n² log n)` interactions.

The chaining is downward induction on the level gap, peeling one level per step
via `expectedHitting_le_through_mid`: hitting `{Φ < m}` from a start at level
`≤ M` costs the level-`M` waiting time plus hitting `{Φ < m}` from the next level
down.  We package the per-level drop hypotheses as a single family `q : ℕ → ℝ≥0∞`
with `hdrop : ∀ m b, Φ b = m → K b (potBelow Φ m)ᶜ ≤ q m`. -/

/-- The level-`m` occupation along the chain from `c`:
`occLevel K Φ m c = ∑' t, P(Φ = m at time t)`. -/
noncomputable def occLevel (K : Kernel α α) (Φ : α → ℕ) (m : ℕ) (c : α) : ℝ≥0∞ :=
  ∑' t : ℕ, (K ^ t) c {x | Φ x = m}

/-- The expected hitting time of `Done = {Φ = 0}` decomposes as the sum of the
per-level occupations over the active levels `1, 2, …`:
`expectedHitting K c (potBelow Φ 1) = ∑' m, occLevel K Φ (m+1) c`.

This is the exact occupation decomposition (`{Φ ≥ 1} = ⨆ₘ {Φ = m+1}` disjointly),
the bookkeeping skeleton of the coupon sum.  Bounding each `occLevel K Φ m c` by
the per-level waiting time `(1 - q m)⁻¹` (the strong-Markov restart, see
`occLevel_le_blocker`) then yields the harmonic bound. -/
theorem expectedHitting_eq_tsum_occLevel [DiscreteMeasurableSpace α]
    (K : Kernel α α) [IsMarkovKernel K] (Φ : α → ℕ) (c : α) :
    expectedHitting K c (potBelow Φ 1) = ∑' m : ℕ, occLevel K Φ (m + 1) c := by
  simp only [expectedHitting, occLevel]
  -- ∑'_t (K^t)c (potBelow Φ 1)ᶜ  and  ∑'_m ∑'_t (K^t)c {Φ = m+1}
  rw [ENNReal.tsum_comm]
  refine tsum_congr (fun t => ?_)
  -- For each t: (K^t)c {Φ ≥ 1} = ∑'_m (K^t)c {Φ = m+1}.
  have hbiject : ((potBelow Φ 1)ᶜ : Set α) = ⋃ m : ℕ, {x | Φ x = m + 1} := by
    ext x
    simp only [potBelow, Set.mem_compl_iff, Set.mem_setOf_eq, not_lt,
      Set.mem_iUnion]
    constructor
    · intro hx; exact ⟨Φ x - 1, by omega⟩
    · rintro ⟨m, hm⟩; omega
  rw [hbiject]
  have hdisj : Pairwise (Function.onFun Disjoint (fun m : ℕ => {x | Φ x = m + 1})) := by
    intro i j hij
    rw [Function.onFun, Set.disjoint_iff]
    intro x hx
    simp only [Set.mem_inter_iff, Set.mem_setOf_eq] at hx
    exact hij (by omega)
  have hmeas : ∀ m : ℕ, MeasurableSet {x : α | Φ x = m + 1} :=
    fun m => DiscreteMeasurableSpace.forall_measurableSet _
  rw [measure_iUnion hdisj hmeas]

/-- **Coupon assembly (modulo the level-occupation bound).**  Given the
per-level occupation bound `hocc : ∀ m, 1 ≤ m → m ≤ M → occLevel K Φ m c ≤ (1-q m)⁻¹`
and that levels above `M` are unreached (`hhi : ∀ m, M < m → occLevel K Φ m c = 0`),
the expected hitting time of `Done` is `≤ ∑_{m=1}^{M} (1-q m)⁻¹`.

This is the pure bookkeeping step: it turns the occupation decomposition into the
finite harmonic sum.  Discharging `hocc` is the remaining strong-Markov restart
(documented as `occLevel_le_blocker`); `hhi` follows from `Φ c ≤ M` +
`pow_above_eq_zero_of_start_le`. -/
theorem coupon_expectedHitting_le_of_occBounds [DiscreteMeasurableSpace α]
    (K : Kernel α α) [IsMarkovKernel K] (Φ : α → ℕ)
    (q : ℕ → ℝ≥0∞) (M : ℕ) (c : α)
    (hocc : ∀ m : ℕ, 1 ≤ m → m ≤ M → occLevel K Φ m c ≤ (1 - q m)⁻¹)
    (hhi : ∀ m : ℕ, M < m → occLevel K Φ m c = 0) :
    expectedHitting K c (potBelow Φ 1) ≤ ∑ m ∈ Finset.Icc 1 M, (1 - q m)⁻¹ := by
  rw [expectedHitting_eq_tsum_occLevel K Φ c]
  -- ∑'_m occLevel (m+1) = ∑_{m=1}^{M} occLevel m  (tail vanishes by hhi)
  rw [tsum_eq_sum (s := Finset.range M) (fun m hm => by
    rw [Finset.mem_range, not_lt] at hm
    exact hhi (m + 1) (by omega))]
  -- reindex range M (m ↦ m+1) to Icc 1 M
  rw [show (∑ m ∈ Finset.range M, occLevel K Φ (m + 1) c)
      = ∑ m ∈ Finset.Icc 1 M, occLevel K Φ m c by
    rw [Finset.sum_bij (fun m _ => m + 1)]
    · intro a ha; rw [Finset.mem_range] at ha; rw [Finset.mem_Icc]; omega
    · intro a ha b hb hab; omega
    · intro b hb; rw [Finset.mem_Icc] at hb
      exact ⟨b - 1, by rw [Finset.mem_range]; omega, by omega⟩
    · intro a _; rfl]
  apply Finset.sum_le_sum
  intro m hm
  rw [Finset.mem_Icc] at hm
  exact hocc m hm.1 hm.2

/-! ### Arbitrary-start level occupation (the strong-Markov restart, formalized)

We now discharge the per-level occupation bound

  `occLevel K Φ m c ≤ (1 - q m)⁻¹`   for **arbitrary** start `c`  (∗)

required by `coupon_expectedHitting_le_of_occBounds`.

The constrained case `Φ c ≤ m` is immediate from `level_occ_geometric`
(`{Φ = m} ⊆ (potBelow Φ m)ᶜ`, geometric decay, geometric series).  The arbitrary
case is the **first-passage restart**: from a start `Φ c > m` the time-0 level-`m`
mass is `0`, and one Chapman-Kolmogorov step pushes the whole occupation onto the
one-step successors, where the bound holds by induction.  We avoid a pathwise
strong-Markov statement by inducting on a **time-truncated** occupation
`∑_{i<t} (K^i) c {Φ = m}` (a uniform-in-`c` bound for every truncation `t`), then
passing to the `tsum` limit.  No measure-theoretic first-passage σ-algebra is
needed — only the kernel Chapman-Kolmogorov identity and a Markov-kernel
`∫ const = const`. -/

/-- **Constrained-start level occupation.** For a start at level `≤ m`, the
level-`m` occupation is bounded by the per-level waiting time `(1 - q)⁻¹`.  Direct
from geometric decay: `{Φ = m} ⊆ (potBelow Φ m)ᶜ` and `(K^t) c (potBelow Φ m)ᶜ ≤ qᵗ`. -/
theorem occLevel_le_of_start_le [DiscreteMeasurableSpace α]
    (K : Kernel α α) [IsMarkovKernel K] (Φ : α → ℕ) (hmono : PotNonincr K Φ)
    (m : ℕ) (q : ℝ≥0∞)
    (hdrop : ∀ b : α, Φ b = m → K b (potBelow Φ m)ᶜ ≤ q)
    (c : α) (hc : Φ c ≤ m) :
    occLevel K Φ m c ≤ (1 - q)⁻¹ := by
  have hsub : ({x : α | Φ x = m} : Set α) ⊆ (potBelow Φ m)ᶜ := by
    intro x hx
    simp only [potBelow, Set.mem_compl_iff, Set.mem_setOf_eq, not_lt]
    exact (Set.mem_setOf_eq ▸ hx).ge
  rw [occLevel]
  calc ∑' t : ℕ, (K ^ t) c {x | Φ x = m}
      ≤ ∑' t : ℕ, (K ^ t) c (potBelow Φ m)ᶜ :=
        ENNReal.tsum_le_tsum (fun t => measure_mono hsub)
    _ ≤ ∑' t : ℕ, q ^ t :=
        ENNReal.tsum_le_tsum (fun t => level_occ_geometric K Φ hmono m q hdrop c hc t)
    _ = (1 - q)⁻¹ := ENNReal.tsum_geometric q

/-- The **time-truncated** level-`m` occupation: the partial sum of the level-`m`
masses over the first `t` steps. -/
noncomputable def occLevelUpTo (K : Kernel α α) (Φ : α → ℕ) (m : ℕ) (t : ℕ) (c : α) :
    ℝ≥0∞ :=
  ∑ i ∈ Finset.range t, (K ^ i) c {x | Φ x = m}

/-- **Uniform truncated bound (the strong-Markov restart, truncated form).** For
*every* truncation `t` and *every* start `c`, the truncated level-`m` occupation is
`≤ (1 - q)⁻¹`.  Proof by induction on `t`, splitting on `Φ c ≤ m` (constrained
bound, no IH) vs `Φ c > m` (the time-0 term vanishes, then one Chapman-Kolmogorov
step pushes the remaining sum onto successors where the IH applies, integrated
against the Markov kernel `K c`). -/
theorem occLevelUpTo_le [DiscreteMeasurableSpace α]
    (K : Kernel α α) [IsMarkovKernel K] (Φ : α → ℕ) (hmono : PotNonincr K Φ)
    (m : ℕ) (q : ℝ≥0∞)
    (hdrop : ∀ b : α, Φ b = m → K b (potBelow Φ m)ᶜ ≤ q)
    (t : ℕ) (c : α) :
    occLevelUpTo K Φ m t c ≤ (1 - q)⁻¹ := by
  induction t generalizing c with
  | zero => simp only [occLevelUpTo, Finset.range_zero, Finset.sum_empty]; exact zero_le'
  | succ t ih =>
      by_cases hc : Φ c ≤ m
      · -- Constrained start: truncated sum ≤ full occupation ≤ (1-q)⁻¹.
        calc occLevelUpTo K Φ m (t + 1) c
            ≤ occLevel K Φ m c := by
              rw [occLevelUpTo, occLevel]; exact ENNReal.sum_le_tsum _
          _ ≤ (1 - q)⁻¹ := occLevel_le_of_start_le K Φ hmono m q hdrop c hc
      · -- Φ c > m: the i = 0 term is 0; peel it and reindex i ↦ j+1.
        rw [not_le] at hc  -- m < Φ c
        have hmeasm : MeasurableSet {x : α | Φ x = m} :=
          DiscreteMeasurableSpace.forall_measurableSet _
        -- (K^0) c {Φ = m} = 0 since Φ c ≠ m.
        have hzero : (K ^ 0) c {x | Φ x = m} = 0 := by
          rw [show (K ^ 0) = Kernel.id from pow_zero K, Kernel.id_apply,
            Measure.dirac_apply' c hmeasm]
          have : c ∉ {x : α | Φ x = m} := by
            simp only [Set.mem_setOf_eq]; omega
          simp [this]
        -- Truncated sum over range (t+1): drop i=0, reindex i = j+1.
        have hsplit : occLevelUpTo K Φ m (t + 1) c
            = ∑ j ∈ Finset.range t, (K ^ (j + 1)) c {x | Φ x = m} := by
          rw [occLevelUpTo, Finset.sum_range_succ']
          simp only [hzero, add_zero]
        rw [hsplit]
        -- Chapman-Kolmogorov per term: (K^(j+1)) c S = ∫ b, (K^j) b S ∂(K c).
        have hCK : ∀ j : ℕ, (K ^ (j + 1)) c {x | Φ x = m}
            = ∫⁻ b, (K ^ j) b {x | Φ x = m} ∂(K c) := by
          intro j
          rw [show j + 1 = 1 + j from by ring,
            Kernel.pow_add_apply_eq_lintegral K 1 j c hmeasm, pow_one]
        simp only [hCK]
        -- Pull the finite sum inside the integral: ∑_j ∫ f_j = ∫ ∑_j f_j.
        rw [← lintegral_finsetSum (Finset.range t)
          (fun j _ => Kernel.measurable_coe (K ^ j) hmeasm)]
        -- The integrand ∑_{j<t} (K^j) b {Φ = m} = occLevelUpTo … t b ≤ (1-q)⁻¹ (IH),
        -- so the integral is ≤ (1-q)⁻¹ · (K c)(univ) = (1-q)⁻¹ (Markov kernel).
        calc ∫⁻ b, (∑ j ∈ Finset.range t, (K ^ j) b {x | Φ x = m}) ∂(K c)
            ≤ ∫⁻ _ : α, (1 - q)⁻¹ ∂(K c) := by
              apply lintegral_mono
              intro b
              simpa only [occLevelUpTo] using ih b
          _ = (1 - q)⁻¹ := by
              rw [lintegral_const, measure_univ, mul_one]

/-- **Arbitrary-start level occupation bound (∗).** For *any* start `c`, the
level-`m` occupation is bounded by the per-level waiting time `(1 - q)⁻¹`.  The
truncated occupations `occLevelUpTo … t c` are uniformly `≤ (1-q)⁻¹`
(`occLevelUpTo_le`) and increase to `occLevel … c` (partial sums of a nonnegative
series), so their `tsum` limit inherits the bound.  This is the strong-Markov
first-passage restart, discharged via the time-truncation + Chapman-Kolmogorov
route, and closes the last brick of the coupon engine. -/
theorem occLevel_le [DiscreteMeasurableSpace α]
    (K : Kernel α α) [IsMarkovKernel K] (Φ : α → ℕ) (hmono : PotNonincr K Φ)
    (m : ℕ) (q : ℝ≥0∞)
    (hdrop : ∀ b : α, Φ b = m → K b (potBelow Φ m)ᶜ ≤ q)
    (c : α) :
    occLevel K Φ m c ≤ (1 - q)⁻¹ := by
  -- occLevel = tsum = ⨆ truncations; each truncation ≤ (1-q)⁻¹.
  rw [occLevel, ENNReal.tsum_eq_iSup_nat]
  refine iSup_le (fun t => ?_)
  exact occLevelUpTo_le K Φ hmono m q hdrop t c

/-- High levels carry no occupation from a start at level `≤ M`: for `M < m`,
`occLevel K Φ m c = 0`.  Immediate from `pow_above_eq_zero_of_start_le`
(`{Φ = m} ⊆ {M < Φ}` is null at every time for a start with `Φ c ≤ M`). -/
theorem occLevel_eq_zero_of_high [DiscreteMeasurableSpace α]
    (K : Kernel α α) [IsMarkovKernel K] (Φ : α → ℕ) (hmono : PotNonincr K Φ)
    (M : ℕ) (c : α) (hc : Φ c ≤ M) (m : ℕ) (hm : M < m) :
    occLevel K Φ m c = 0 := by
  rw [occLevel, ENNReal.tsum_eq_zero]
  intro t
  refine measure_mono_null ?_ (pow_above_eq_zero_of_start_le K Φ hmono M c hc t)
  intro x hx
  simp only [Set.mem_setOf_eq] at hx ⊢
  omega

/-- **Generic coupon capstone (fully discharged).** Under non-increasing `Φ`, a
per-level drop family `q : ℕ → ℝ≥0∞` with `K b (potBelow Φ m)ᶜ ≤ q m` at every
level-`m` state, and a start `c` at level `≤ M`, the expected hitting time of
`Done = {Φ < 1} = {Φ = 0}` is bounded by the harmonic coupon sum
`∑_{m=1}^{M} (1 - q m)⁻¹`.

This is `coupon_expectedHitting_le_of_occBounds` with both hypotheses discharged:
`hocc` by the arbitrary-start `occLevel_le` and `hhi` by `occLevel_eq_zero_of_high`.
It is the protocol-agnostic `O(coupon sum)` interaction-count bound; the Phase-10
stages instantiate it with `q m = 1 - m/(n(n-1))`. -/
theorem coupon_expectedHitting_le [DiscreteMeasurableSpace α]
    (K : Kernel α α) [IsMarkovKernel K] (Φ : α → ℕ) (hmono : PotNonincr K Φ)
    (q : ℕ → ℝ≥0∞)
    (hdrop : ∀ m : ℕ, ∀ b : α, Φ b = m → K b (potBelow Φ m)ᶜ ≤ q m)
    (M : ℕ) (c : α) (hc : Φ c ≤ M) :
    expectedHitting K c (potBelow Φ 1) ≤ ∑ m ∈ Finset.Icc 1 M, (1 - q m)⁻¹ :=
  coupon_expectedHitting_le_of_occBounds K Φ q M c
    (fun m _ _ => occLevel_le K Φ hmono m (q m) (hdrop m) c)
    (fun m hm => occLevel_eq_zero_of_high K Φ hmono M c hc m hm)

/-! ### Harmonic / coupon-sum evaluation (generic bookkeeping)

The capstone RHS is the coupon sum `∑_{m=1}^{M} (1 - q m)⁻¹`.  For the Phase-10
shape `(1 - q m)⁻¹ = n(n-1)/m`, the exact value is `n(n-1)·H_M`, but the engine
only needs an upper bound.  We record the crude per-level-uniform bound: if every
active level's waiting time is `≤ r`, the sum is `≤ M·r` (here `r = n(n-1)` since
`n(n-1)/m ≤ n(n-1)` for `m ≥ 1`), which already gives the `O(n²·M)` interaction
count; for the coupon stages `M = O(n)`, i.e. `O(n³)`, dominated by — and in the
paper sharpened to — the `n(n-1)·H_n = O(n² log n)` harmonic form.  The crude
bound is what the chained stage argument consumes; recorded here so the harmonic
constant is not on the critical path. -/

/-- **Crude coupon-sum bound.** If every active-level waiting time `(1 - q m)⁻¹`
(`1 ≤ m ≤ M`) is bounded by a common `r`, then the coupon sum is `≤ M · r`.  Feeds
the capstone RHS with `r = (per-level waiting-time ceiling) = n(n-1)`. -/
theorem coupon_sum_le_of_uniform (q : ℕ → ℝ≥0∞) (M : ℕ) (r : ℝ≥0∞)
    (hq : ∀ m : ℕ, 1 ≤ m → m ≤ M → (1 - q m)⁻¹ ≤ r) :
    ∑ m ∈ Finset.Icc 1 M, (1 - q m)⁻¹ ≤ (M : ℝ≥0∞) * r := by
  calc ∑ m ∈ Finset.Icc 1 M, (1 - q m)⁻¹
      ≤ ∑ _m ∈ Finset.Icc 1 M, r := by
        apply Finset.sum_le_sum
        intro m hm
        rw [Finset.mem_Icc] at hm
        exact hq m hm.1 hm.2
    _ = (M : ℝ≥0∞) * r := by
        rw [Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]

/-- **Generic coupon capstone with crude harmonic evaluation.** Combines
`coupon_expectedHitting_le` with `coupon_sum_le_of_uniform`: under the engine
hypotheses plus a uniform per-level waiting-time ceiling `r`, the expected hitting
time of `Done = {Φ = 0}` is `≤ M · r` interactions.  For the Phase-10 coupon
stages (`M = O(n)`, `r = n(n-1)`) this is the `O(n³)` crude form; the harmonic
`O(n² log n)` is a constant sharpening orthogonal to the engine. -/
theorem coupon_expectedHitting_le_uniform [DiscreteMeasurableSpace α]
    (K : Kernel α α) [IsMarkovKernel K] (Φ : α → ℕ) (hmono : PotNonincr K Φ)
    (q : ℕ → ℝ≥0∞)
    (hdrop : ∀ m : ℕ, ∀ b : α, Φ b = m → K b (potBelow Φ m)ᶜ ≤ q m)
    (M : ℕ) (c : α) (hc : Φ c ≤ M) (r : ℝ≥0∞)
    (hq : ∀ m : ℕ, 1 ≤ m → m ≤ M → (1 - q m)⁻¹ ≤ r) :
    expectedHitting K c (potBelow Φ 1) ≤ (M : ℝ≥0∞) * r :=
  le_trans (coupon_expectedHitting_le K Φ hmono q hdrop M c hc)
    (coupon_sum_le_of_uniform q M r hq)

/-! ## Invariant-relative coupon engine (Brick B1 generic infrastructure)

The Phase-10 stage potentials (`activeBCount`, `wrongACount`) are **not**
non-increasing on the full `NonuniformMajority` kernel: a pre-phase-10 reaction
(`enterPhase10`, epidemic entry) can create active-B agents or un-A an A.  The
per-pair non-increase holds only when both interacting agents are already in phase
10, i.e. on the **all-phase-10 subdynamics**.

We thread an abstract invariant `Inv : α → Prop` through the engine.  Two abstract
hypotheses suffice and are both discharged for `Inv = Phase10EpidemicPost` by the
existing support-closure machinery:

* **`InvClosed K Inv`** — `Inv` is `K`-support-closed: from an `Inv`-state, one step
  almost surely stays in `Inv` (`K b {¬ Inv} = 0`).  (For the protocol kernel this
  is `Phase10EpidemicPost` preservation: phases only increase and 10 is the max.)
* **`PotNonincrOn Inv K Φ`** — `Φ` is non-increasing from every `Inv`-state:
  `K b {Φ b < Φ x} = 0` for all `b` with `Inv b`.  (The per-pair bound on the
  phase-10-restricted transition.)

Carrying `Inv` a.e. along the kernel powers (every reachable state from an
`Inv`-start satisfies `Inv`), the level-occupation contraction goes through with the
drop hypothesis only required at `Inv`-states.  All engine theorems below mirror
their unconditional counterparts; the proofs differ only by intersecting the
relevant null sets with `{¬ Inv}` (which is itself null). -/

/-- `Inv` is closed under one kernel step: from an `Inv`-state the next-step mass on
`¬ Inv` is `0`. -/
def InvClosed (K : Kernel α α) (Inv : α → Prop) : Prop :=
  ∀ b : α, Inv b → K b {x | ¬ Inv x} = 0

/-- `Φ` is non-increasing along `K` **from every `Inv`-state**: one step from an
`Inv`-state never strictly raises `Φ`. -/
def PotNonincrOn (Inv : α → Prop) (K : Kernel α α) (Φ : α → ℕ) : Prop :=
  ∀ b : α, Inv b → K b {x | Φ b < Φ x} = 0

/-- From an `Inv`-start the `(K^t)`-mass on `¬ Inv` stays `0` (the invariant holds
a.e. at every time). -/
theorem pow_not_inv_eq_zero [DiscreteMeasurableSpace α]
    (K : Kernel α α) [IsMarkovKernel K] (Inv : α → Prop)
    (hClosed : InvClosed K Inv) (c : α) (hc : Inv c) (t : ℕ) :
    (K ^ t) c {x | ¬ Inv x} = 0 := by
  induction t generalizing c with
  | zero =>
      rw [show (K ^ 0) = Kernel.id from pow_zero K, Kernel.id_apply,
        Measure.dirac_apply' c (DiscreteMeasurableSpace.forall_measurableSet _)]
      have : c ∉ {x | ¬ Inv x} := by simp only [Set.mem_setOf_eq, not_not]; exact hc
      simp [this]
  | succ t ih =>
      have hbad : MeasurableSet {x : α | ¬ Inv x} :=
        DiscreteMeasurableSpace.forall_measurableSet _
      rw [show t + 1 = 1 + t from by ring,
        Kernel.pow_add_apply_eq_lintegral K 1 t c hbad, pow_one,
        lintegral_eq_zero_iff (Kernel.measurable_coe _ hbad)]
      rw [Filter.eventuallyEq_iff_exists_mem]
      refine ⟨{y | Inv y}, ?_, ?_⟩
      · rw [mem_ae_iff]
        have hcompl : ({y | Inv y}ᶜ : Set α) = {x | ¬ Inv x} := by
          ext y; simp only [Set.mem_compl_iff, Set.mem_setOf_eq]
        rw [hcompl]; exact hClosed c hc
      · intro y hy; exact ih y hy

/-- **Invariant-relative absorption of `{Φ < m}`.** From an `Inv`-state below level
`m`, one step cannot reach `{Φ ≥ m}` (using the drop hypothesis at that state). -/
theorem potBelow_absorbing_on [DiscreteMeasurableSpace α]
    (K : Kernel α α) (Inv : α → Prop) (Φ : α → ℕ)
    (hmono : PotNonincrOn Inv K Φ) (m : ℕ) :
    ∀ x ∈ potBelow Φ m, Inv x → K x (potBelow Φ m)ᶜ = 0 := by
  intro x hx hInv
  have hsub : ((potBelow Φ m)ᶜ : Set α) ⊆ {y | Φ x < Φ y} := by
    intro y hy
    simp only [potBelow, Set.mem_compl_iff, Set.mem_setOf_eq, not_lt] at hy
    have hxlt : Φ x < m := hx
    exact Set.mem_setOf_eq ▸ (lt_of_lt_of_le hxlt hy)
  exact measure_mono_null hsub (hmono x hInv)

/-- The `(K^t)`-mass on strictly-above-`m` stays `0` for an `Inv`-start at level
`≤ m` (invariant-relative). -/
theorem pow_above_eq_zero_of_start_le_on [DiscreteMeasurableSpace α]
    (K : Kernel α α) [IsMarkovKernel K] (Inv : α → Prop)
    (hClosed : InvClosed K Inv) (Φ : α → ℕ) (hmono : PotNonincrOn Inv K Φ)
    (m : ℕ) (c : α) (hc : Φ c ≤ m) (hInvc : Inv c) (t : ℕ) :
    (K ^ t) c {x | m < Φ x} = 0 := by
  induction t generalizing c with
  | zero =>
      rw [show (K ^ 0) = Kernel.id from pow_zero K, Kernel.id_apply,
        Measure.dirac_apply' c (DiscreteMeasurableSpace.forall_measurableSet _)]
      have : c ∉ {x | m < Φ x} := by simp only [Set.mem_setOf_eq, not_lt]; exact hc
      simp [this]
  | succ t ih =>
      have hbad : MeasurableSet {x : α | m < Φ x} :=
        DiscreteMeasurableSpace.forall_measurableSet _
      rw [show t + 1 = 1 + t from by ring,
        Kernel.pow_add_apply_eq_lintegral K 1 t c hbad, pow_one,
        lintegral_eq_zero_iff (Kernel.measurable_coe _ hbad)]
      rw [Filter.eventuallyEq_iff_exists_mem]
      -- Stay in {Φ ≤ m} ∩ Inv: one step from an Inv-state at level ≤ m.
      refine ⟨{y | Φ y ≤ m} ∩ {y | Inv y}, ?_, ?_⟩
      · rw [mem_ae_iff]
        have hcompl : (({y | Φ y ≤ m} ∩ {y | Inv y})ᶜ : Set α)
            ⊆ {x | m < Φ x} ∪ {x | ¬ Inv x} := by
          intro y hy
          simp only [Set.mem_compl_iff, Set.mem_inter_iff, Set.mem_setOf_eq,
            not_and_or, not_le] at hy
          rcases hy with hy | hy
          · exact Or.inl hy
          · exact Or.inr hy
        refine measure_mono_null hcompl ?_
        rw [measure_union_null_iff]
        have hinv1 : (K c) {x | ¬ Inv x} = 0 := by
          have := pow_not_inv_eq_zero K Inv hClosed c hInvc 1
          rwa [pow_one] at this
        refine ⟨?_, hinv1⟩
        -- one step from c (Inv c, Φ c ≤ m) cannot reach {Φ > m}
        refine measure_mono_null ?_ (hmono c hInvc)
        intro y hy
        simp only [Set.mem_setOf_eq] at hy ⊢
        exact lt_of_le_of_lt hc hy
      · intro y hy
        simp only [Set.mem_inter_iff, Set.mem_setOf_eq] at hy
        exact ih y hy.1 hy.2

/-- **Invariant-relative one-step level-`m` occupation contraction.** Mirrors
`level_occ_contract`, but the drop hypothesis is only needed at `Inv`-level-`m`
states, and the start must satisfy `Inv`.  The `(K^t c)`-mass lives a.e. on
`{Φ ≤ m} ∩ Inv`: on `{Φ < m} ∩ Inv` the reach of `(potBelow Φ m)ᶜ` is `0`
(invariant-relative absorption); on `{Φ = m} ∩ Inv` it is `≤ q`; the rest
(`{Φ > m}` and `¬ Inv`) carries `0` mass. -/
theorem level_occ_contract_on [DiscreteMeasurableSpace α]
    (K : Kernel α α) [IsMarkovKernel K] (Inv : α → Prop)
    (hClosed : InvClosed K Inv) (Φ : α → ℕ) (hmono : PotNonincrOn Inv K Φ)
    (m : ℕ) (q : ℝ≥0∞)
    (hdrop : ∀ b : α, Inv b → Φ b = m → K b (potBelow Φ m)ᶜ ≤ q)
    (c : α) (hc : Φ c ≤ m) (hInvc : Inv c) (t : ℕ) :
    (K ^ (t + 1)) c (potBelow Φ m)ᶜ ≤ q * (K ^ t) c (potBelow Φ m)ᶜ := by
  classical
  have hbad : MeasurableSet ((potBelow Φ m)ᶜ : Set α) :=
    (potBelow_measurable Φ m).compl
  rw [Kernel.pow_succ_apply_eq_lintegral K t c hbad]
  calc ∫⁻ b, K b (potBelow Φ m)ᶜ ∂((K ^ t) c)
      ≤ ∫⁻ b, q * Set.indicator ((potBelow Φ m)ᶜ) (fun _ => (1 : ℝ≥0∞)) b
          ∂((K ^ t) c) := by
        apply lintegral_mono_ae
        -- a.e. b lives in {Φ ≤ m} ∩ Inv.
        have hnull_above : (K ^ t) c {x | m < Φ x} = 0 :=
          pow_above_eq_zero_of_start_le_on K Inv hClosed Φ hmono m c hc hInvc t
        have hnull_inv : (K ^ t) c {x | ¬ Inv x} = 0 :=
          pow_not_inv_eq_zero K Inv hClosed c hInvc t
        rw [Filter.eventually_iff_exists_mem]
        refine ⟨{x | Φ x ≤ m} ∩ {x | Inv x}, ?_, ?_⟩
        · rw [mem_ae_iff]
          have hcompl : (({x | Φ x ≤ m} ∩ {x | Inv x})ᶜ : Set α)
              ⊆ {x | m < Φ x} ∪ {x | ¬ Inv x} := by
            intro y hy
            simp only [Set.mem_compl_iff, Set.mem_inter_iff, Set.mem_setOf_eq,
              not_and_or, not_le] at hy
            rcases hy with hy | hy
            · exact Or.inl hy
            · exact Or.inr hy
          refine measure_mono_null hcompl ?_
          rw [measure_union_null_iff]
          exact ⟨hnull_above, hnull_inv⟩
        · intro b hb
          simp only [Set.mem_inter_iff, Set.mem_setOf_eq] at hb
          obtain ⟨hbm, hbInv⟩ := hb
          rcases lt_or_eq_of_le hbm with hlt | heq
          · -- Φ b < m: b ∈ potBelow, Inv b, absorbing ⇒ K b Bᶜ = 0
            have hbb : b ∈ potBelow Φ m := hlt
            rw [potBelow_absorbing_on K Inv Φ hmono m b hbb hbInv]; exact zero_le'
          · -- Φ b = m: b ∉ potBelow, so indicator = 1, and K b Bᶜ ≤ q.
            have hbmem : b ∈ ((potBelow Φ m)ᶜ : Set α) := by
              simp only [potBelow, Set.mem_compl_iff, Set.mem_setOf_eq, not_lt]
              exact heq.ge
            rw [Set.indicator_of_mem hbmem, mul_one]
            exact hdrop b hbInv heq
    _ = q * (K ^ t) c (potBelow Φ m)ᶜ := by
        rw [lintegral_const_mul q (measurable_const.indicator hbad)]
        congr 1
        rw [lintegral_indicator hbad]; simp

/-- **Invariant-relative geometric decay** of the level-`m` occupation mass. -/
theorem level_occ_geometric_on [DiscreteMeasurableSpace α]
    (K : Kernel α α) [IsMarkovKernel K] (Inv : α → Prop)
    (hClosed : InvClosed K Inv) (Φ : α → ℕ) (hmono : PotNonincrOn Inv K Φ)
    (m : ℕ) (q : ℝ≥0∞)
    (hdrop : ∀ b : α, Inv b → Φ b = m → K b (potBelow Φ m)ᶜ ≤ q)
    (c : α) (hc : Φ c ≤ m) (hInvc : Inv c) (t : ℕ) :
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
            level_occ_contract_on K Inv hClosed Φ hmono m q hdrop c hc hInvc t
        _ ≤ q * q ^ t := by gcongr
        _ = q ^ (t + 1) := by rw [pow_succ]; ring

/-- **Invariant-relative constrained-start level occupation.** For an `Inv`-start at
level `≤ m`, the level-`m` occupation is `≤ (1 - q)⁻¹`. -/
theorem occLevel_le_of_start_le_on [DiscreteMeasurableSpace α]
    (K : Kernel α α) [IsMarkovKernel K] (Inv : α → Prop)
    (hClosed : InvClosed K Inv) (Φ : α → ℕ) (hmono : PotNonincrOn Inv K Φ)
    (m : ℕ) (q : ℝ≥0∞)
    (hdrop : ∀ b : α, Inv b → Φ b = m → K b (potBelow Φ m)ᶜ ≤ q)
    (c : α) (hc : Φ c ≤ m) (hInvc : Inv c) :
    occLevel K Φ m c ≤ (1 - q)⁻¹ := by
  have hsub : ({x : α | Φ x = m} : Set α) ⊆ (potBelow Φ m)ᶜ := by
    intro x hx
    simp only [potBelow, Set.mem_compl_iff, Set.mem_setOf_eq, not_lt]
    exact (Set.mem_setOf_eq ▸ hx).ge
  rw [occLevel]
  calc ∑' t : ℕ, (K ^ t) c {x | Φ x = m}
      ≤ ∑' t : ℕ, (K ^ t) c (potBelow Φ m)ᶜ :=
        ENNReal.tsum_le_tsum (fun t => measure_mono hsub)
    _ ≤ ∑' t : ℕ, q ^ t :=
        ENNReal.tsum_le_tsum
          (fun t => level_occ_geometric_on K Inv hClosed Φ hmono m q hdrop c hc hInvc t)
    _ = (1 - q)⁻¹ := ENNReal.tsum_geometric q

/-- **Invariant-relative uniform truncated occupation bound.** For *every* truncation
`t` and *every* `Inv`-start `c`, the truncated level-`m` occupation is `≤ (1 - q)⁻¹`.
Mirrors `occLevelUpTo_le`: split on `Φ c ≤ m` (constrained, no IH) vs `Φ c > m`
(time-0 term vanishes, then one Chapman-Kolmogorov step pushes onto successors —
which satisfy `Inv` a.e. by `InvClosed`, so the IH applies under the integral). -/
theorem occLevelUpTo_le_on [DiscreteMeasurableSpace α]
    (K : Kernel α α) [IsMarkovKernel K] (Inv : α → Prop)
    (hClosed : InvClosed K Inv) (Φ : α → ℕ) (hmono : PotNonincrOn Inv K Φ)
    (m : ℕ) (q : ℝ≥0∞)
    (hdrop : ∀ b : α, Inv b → Φ b = m → K b (potBelow Φ m)ᶜ ≤ q)
    (t : ℕ) (c : α) (hInvc : Inv c) :
    occLevelUpTo K Φ m t c ≤ (1 - q)⁻¹ := by
  induction t generalizing c with
  | zero => simp only [occLevelUpTo, Finset.range_zero, Finset.sum_empty]; exact zero_le'
  | succ t ih =>
      by_cases hc : Φ c ≤ m
      · calc occLevelUpTo K Φ m (t + 1) c
            ≤ occLevel K Φ m c := by
              rw [occLevelUpTo, occLevel]; exact ENNReal.sum_le_tsum _
          _ ≤ (1 - q)⁻¹ :=
              occLevel_le_of_start_le_on K Inv hClosed Φ hmono m q hdrop c hc hInvc
      · rw [not_le] at hc
        have hmeasm : MeasurableSet {x : α | Φ x = m} :=
          DiscreteMeasurableSpace.forall_measurableSet _
        have hzero : (K ^ 0) c {x | Φ x = m} = 0 := by
          rw [show (K ^ 0) = Kernel.id from pow_zero K, Kernel.id_apply,
            Measure.dirac_apply' c hmeasm]
          have : c ∉ {x : α | Φ x = m} := by
            simp only [Set.mem_setOf_eq]; omega
          simp [this]
        have hsplit : occLevelUpTo K Φ m (t + 1) c
            = ∑ j ∈ Finset.range t, (K ^ (j + 1)) c {x | Φ x = m} := by
          rw [occLevelUpTo, Finset.sum_range_succ']
          simp only [hzero, add_zero]
        rw [hsplit]
        have hCK : ∀ j : ℕ, (K ^ (j + 1)) c {x | Φ x = m}
            = ∫⁻ b, (K ^ j) b {x | Φ x = m} ∂(K c) := by
          intro j
          rw [show j + 1 = 1 + j from by ring,
            Kernel.pow_add_apply_eq_lintegral K 1 j c hmeasm, pow_one]
        simp only [hCK]
        rw [← lintegral_finsetSum (Finset.range t)
          (fun j _ => Kernel.measurable_coe (K ^ j) hmeasm)]
        -- a.e. b under (K c) satisfies Inv (InvClosed); on those the IH applies.
        have hinv_ae : (K c) {x | ¬ Inv x} = 0 := hClosed c hInvc
        calc ∫⁻ b, (∑ j ∈ Finset.range t, (K ^ j) b {x | Φ x = m}) ∂(K c)
            ≤ ∫⁻ _ : α, (1 - q)⁻¹ ∂(K c) := by
              apply lintegral_mono_ae
              rw [Filter.eventually_iff_exists_mem]
              refine ⟨{x | Inv x}, ?_, ?_⟩
              · rw [mem_ae_iff]
                have : ({x | Inv x}ᶜ : Set α) = {x | ¬ Inv x} := by
                  ext y; simp only [Set.mem_compl_iff, Set.mem_setOf_eq]
                rw [this]; exact hinv_ae
              · intro b hb
                simp only [Set.mem_setOf_eq] at hb
                simpa only [occLevelUpTo] using ih b hb
          _ = (1 - q)⁻¹ := by
              rw [lintegral_const, measure_univ, mul_one]

/-- **Invariant-relative arbitrary-start level occupation bound.** For any `Inv`-start
`c`, the level-`m` occupation is `≤ (1 - q)⁻¹`.  The truncated occupations are
uniformly bounded and increase to `occLevel`. -/
theorem occLevel_le_on [DiscreteMeasurableSpace α]
    (K : Kernel α α) [IsMarkovKernel K] (Inv : α → Prop)
    (hClosed : InvClosed K Inv) (Φ : α → ℕ) (hmono : PotNonincrOn Inv K Φ)
    (m : ℕ) (q : ℝ≥0∞)
    (hdrop : ∀ b : α, Inv b → Φ b = m → K b (potBelow Φ m)ᶜ ≤ q)
    (c : α) (hInvc : Inv c) :
    occLevel K Φ m c ≤ (1 - q)⁻¹ := by
  rw [occLevel, ENNReal.tsum_eq_iSup_nat]
  refine iSup_le (fun t => ?_)
  exact occLevelUpTo_le_on K Inv hClosed Φ hmono m q hdrop t c hInvc

/-- **Invariant-relative high-level vanishing.** For an `Inv`-start at level `≤ M`,
levels above `M` carry no occupation. -/
theorem occLevel_eq_zero_of_high_on [DiscreteMeasurableSpace α]
    (K : Kernel α α) [IsMarkovKernel K] (Inv : α → Prop)
    (hClosed : InvClosed K Inv) (Φ : α → ℕ) (hmono : PotNonincrOn Inv K Φ)
    (M : ℕ) (c : α) (hc : Φ c ≤ M) (hInvc : Inv c) (m : ℕ) (hm : M < m) :
    occLevel K Φ m c = 0 := by
  rw [occLevel, ENNReal.tsum_eq_zero]
  intro t
  refine measure_mono_null ?_
    (pow_above_eq_zero_of_start_le_on K Inv hClosed Φ hmono M c hc hInvc t)
  intro x hx
  simp only [Set.mem_setOf_eq] at hx ⊢
  omega

/-- **Invariant-relative coupon capstone (fully discharged).** The all-phase-10
analogue of `coupon_expectedHitting_le`: under `InvClosed K Inv`, `PotNonincrOn Inv
K Φ`, a per-level drop family `q` (required only at `Inv`-states), an `Inv`-start `c`
at level `≤ M`, the expected hitting time of `Done = {Φ = 0}` is `≤
∑_{m=1}^{M} (1 - q m)⁻¹`. -/
theorem coupon_expectedHitting_le_on [DiscreteMeasurableSpace α]
    (K : Kernel α α) [IsMarkovKernel K] (Inv : α → Prop)
    (hClosed : InvClosed K Inv) (Φ : α → ℕ) (hmono : PotNonincrOn Inv K Φ)
    (q : ℕ → ℝ≥0∞)
    (hdrop : ∀ m : ℕ, ∀ b : α, Inv b → Φ b = m → K b (potBelow Φ m)ᶜ ≤ q m)
    (M : ℕ) (c : α) (hc : Φ c ≤ M) (hInvc : Inv c) :
    expectedHitting K c (potBelow Φ 1) ≤ ∑ m ∈ Finset.Icc 1 M, (1 - q m)⁻¹ :=
  coupon_expectedHitting_le_of_occBounds K Φ q M c
    (fun m _ _ => occLevel_le_on K Inv hClosed Φ hmono m (q m) (hdrop m) c hInvc)
    (fun m hm => occLevel_eq_zero_of_high_on K Inv hClosed Φ hmono M c hc hInvc m hm)

/-- **Invariant-relative coupon capstone with crude harmonic evaluation.** The
`_on` analogue of `coupon_expectedHitting_le_uniform`: under the invariant-relative
engine hypotheses plus a uniform per-level ceiling `r`, the expected hitting time of
`Done = {Φ = 0}` is `≤ M · r`. -/
theorem coupon_expectedHitting_le_uniform_on [DiscreteMeasurableSpace α]
    (K : Kernel α α) [IsMarkovKernel K] (Inv : α → Prop)
    (hClosed : InvClosed K Inv) (Φ : α → ℕ) (hmono : PotNonincrOn Inv K Φ)
    (q : ℕ → ℝ≥0∞)
    (hdrop : ∀ m : ℕ, ∀ b : α, Inv b → Φ b = m → K b (potBelow Φ m)ᶜ ≤ q m)
    (M : ℕ) (c : α) (hc : Φ c ≤ M) (hInvc : Inv c) (r : ℝ≥0∞)
    (hq : ∀ m : ℕ, 1 ≤ m → m ≤ M → (1 - q m)⁻¹ ≤ r) :
    expectedHitting K c (potBelow Φ 1) ≤ (M : ℝ≥0∞) * r :=
  le_trans (coupon_expectedHitting_le_on K Inv hClosed Φ hmono q hdrop M c hc hInvc)
    (coupon_sum_le_of_uniform q M r hq)

/-! ### Phase-10 instantiation target

For the real protocol `K := (NonuniformMajority L K).transitionKernel` and the
stage potentials of `Analysis/Phase10Backup.lean`:

* **cancel stage** `Φ := activeBCount` (majority A case): `Done = {activeBCount = 0}`;
* **absorb-T stage** `Φ := wrongACount` after `activeBCount = 0`;
* **convert-passive stage** `Φ := wrongACount` (passive recount).

**Generic engine: fully closed (E2-6/7/8).**  `coupon_expectedHitting_le_uniform`
takes exactly `(PotNonincr K Φ)`, `(hdrop : ∀ m b, Φ b = m → K b (potBelow Φ m)ᶜ ≤
q m)`, `(Φ c ≤ M)`, and a uniform per-level ceiling `r` (`(1 - q m)⁻¹ ≤ r`), and
returns `expectedHitting K c (potBelow Φ 1) ≤ M·r` — no residual hypotheses.  Only
the THREE protocol facts below remain, all in `Analysis/Phase10Backup.lean` land:

1. `PotNonincr K Φ`, i.e. `∀ c, K c {c' | Φ c < Φ c'} = 0`.  Via the established
   support template (`Phase0Convergence.phaseBelowCount_step_le` / `mcrCount_step_le`):
   `c' ∈ (stepDistOrSelf c).support` ⇒ `Protocol.stepDist_support` peels a pair
   `(r₁,r₂)`, `Φ c' = Φ(c-{r₁,r₂}) + Φ{Transition r₁ r₂}` (countP additivity,
   `Multiset.countP_add`), so it reduces to the **per-pair bound**
   `Φ{Transition r₁ r₂} ≤ Φ{r₁,r₂}` (a `Transition_activeBCount_le` /
   `Transition_wrongACount_le`, the analogue of `Transition_phaseBelowCount_le`).
   **SCOPING CAVEAT (precise):** this per-pair bound is FALSE for the *full*
   `NonuniformMajority` kernel — pre-phase-10 reactions (`enterPhase10`, epidemic
   entry) DO create active-B / un-A an A.  So `PotNonincr` holds only on the
   **phase-10-restricted** subdynamics.  The honest discharge is either (a) run the
   stages on the absorbed/restricted kernel where every reachable config satisfies
   the all-phase-10 invariant (`backupSignal_of_all_phase10` regime), proving the
   per-pair bound under `IsActiveX`-typed hypotheses on `r₁,r₂`; or (b) thread an
   all-phase-10 invariant `J` through a `PotNonincr`-relative-to-`J` variant of the
   engine.  This invariant-threading is the first genuine instantiation brick.
2. the per-level drop `K c (potBelow Φ m)ᶜ ≤ q m` with `q m = 1 - m/(n(n−1))`.  The
   useful-interaction probability is `≥ (class interactionCount)/(n(n−1))`; with `m`
   active-B and `≥ 1` active-A (from `exists_activeA_of_phase10ActiveSignedSum_pos`
   in the majority-A case), the class count is `≥ m`.  **State-multiplicity subtlety
   (precise):** `step_advance_prob` is proven over `Bool` for a single fixed pair
   `(true,false)`; here "active A" / "active B" are *classes* of `AgentState`
   records, so the single-pair mass bound must be aggregated over the
   active-A × active-B class.  This needs (i) the real-kernel analogue of
   `step_advance_prob` (the `interactionPMF (r₁,r₂)` mass lower bound for an
   applicable `AgentState` pair, following the `stepDist = map scheduledStep
   interactionPMF` route used in `ClockOLogN`/`ClockFaithful`), and (ii) summing
   that mass over the `Finset` of present useful pairs via `interactionPMF`/`countP`
   additivity to reach `≥ m/(n(n−1))`.  This is the second (largest) brick.
3. the harmonic evaluation — DONE generically: `coupon_sum_le_of_uniform` gives the
   crude `M·r = O(n³)`; the sharp `n(n−1)·H_n = O(n² log n)` is a constant
   refinement of the same Icc sum (`∑ 1/m`), orthogonal to the engine.

The three stages are then chained by `expectedHitting_le_through_mid`
(majority/tie case split via `Phase10Backup.backupSignal` sign), giving the
Lemma 7.7 expectation bound in interaction counts.  Remaining work = bricks 1 and 2
above (invariant-threading + class-aggregated probability), both PURELY protocol
instantiation; the probability/coupon engine carries no further obligation. -/

end Coupon

/-! ## Phase-10 per-level drop probability (Brick B2)

We instantiate the per-level drop hypothesis of the invariant-relative engine for
the real kernel `K = (NonuniformMajority L K).transitionKernel` and `Φ =
activeBCount` on the all-phase-10 invariant `Inv = Phase10EpidemicPost`.

The route is the one used by `Invariants.phase10_descent_prob`: the public helper
`Phase0Convergence.stepDistOrSelf_toMeasure_ge` reduces a kernel-mass lower bound on
a target set to the `interactionPMF` mass of a `good` Finset of ordered pairs that
land in the target.  Each ordered pair `(a, b)` with `a` active-A and `b` active-B
fires the Phase-10 cancel reaction, which strictly lowers `activeBCount` (so it
lands in the drop target).  Aggregating over the `m` distinct active-B agents
(paired with one fixed active-A) gives mass `≥ m / (n(n−1))`. -/

namespace Phase10Drop

open MeasureTheory ProbabilityTheory

variable {L K : ℕ}

/-- The drop target set for a potential `Φ` at a base configuration `c`:
configurations whose `Φ`-value is strictly smaller than `Φ c`. -/
def dropTarget (Φ : Config (AgentState L K) → ℕ) (c : Config (AgentState L K)) :
    Set (Config (AgentState L K)) :=
  {c' | Φ c' < Φ c}

/-- Re-derivation of applicability from membership + distinctness (the public
analogue of the `Analysis`-private `applicable_of_mem_ne'`). -/
theorem applicable_of_mem_ne {c : Config (AgentState L K)} {a b : AgentState L K}
    (ha : a ∈ c) (hb : b ∈ c) (hne : a ≠ b) :
    Protocol.Applicable c a b := by
  have hnot : a ∉ ({b} : Multiset (AgentState L K)) := by simp [hne]
  change a ::ₘ ({b} : Multiset (AgentState L K)) ≤ c
  rw [Multiset.cons_le_of_notMem hnot]
  exact ⟨ha, Multiset.singleton_le.2 hb⟩

/-- The `activeBCount` of the post-cancel configuration is strictly below the base
`activeBCount`, for an active-A / active-B ordered pair on an all-phase-10 config.
Re-derived in-file from the public output characterization
`Phase10Transition_activeA_activeB_outputs_T`. -/
theorem activeBCount_post_cancel_lt
    (c : Config (AgentState L K))
    (hphase : ∀ x ∈ c, x.phase.val = 10)
    {a b : AgentState L K} (ha_mem : a ∈ c) (hb_mem : b ∈ c)
    (ha : IsActiveA a) (hb : IsActiveB b) :
    activeBCount
        (c - ({a, b} : Multiset (AgentState L K)) +
          ({(Transition L K a b).1, (Transition L K a b).2} :
            Multiset (AgentState L K))) <
      activeBCount c := by
  have hne : a ≠ b := by
    intro h; subst h
    have : a.output = .B := hb.2
    rw [ha.2] at this; exact absurd this (by decide)
  have happ : ({a, b} : Multiset (AgentState L K)) ≤ c :=
    applicable_of_mem_ne ha_mem hb_mem hne
  have htransition : Transition L K a b = Phase10Transition L K a b :=
    Transition_eq_Phase10Transition_of_phase10
      (L := L) (K := K) a b (hphase a ha_mem) (hphase b hb_mem)
  -- activeBCount {a,b} = 1 (only b is active-B).
  have hpair_before :
      Multiset.countP IsActiveB ({a, b} : Multiset (AgentState L K)) = 1 := by
    change Multiset.countP IsActiveB (a ::ₘ ({b} : Multiset (AgentState L K))) = 1
    rw [Multiset.countP_cons_of_neg]
    · change Multiset.countP IsActiveB (b ::ₘ (0 : Multiset (AgentState L K))) = 1
      rw [Multiset.countP_cons_of_pos]
      · simp
      · exact hb
    · intro hbad
      have : a.output = .B := hbad.2
      rw [ha.2] at this; exact absurd this (by decide)
  -- both outputs become T after cancel, so activeBCount of the pair becomes 0.
  have hlocal :=
    Phase10Transition_activeA_activeB_outputs_T
      (L := L) (K := K) a b ha.1 hb.1 ha.2 hb.2
  have hpair_after :
      Multiset.countP IsActiveB
        ({(Transition L K a b).1, (Transition L K a b).2} :
          Multiset (AgentState L K)) = 0 := by
    rw [htransition]
    rcases hlocal with ⟨h1out, h2out, _h1full, _h2full⟩
    change Multiset.countP IsActiveB
      ((Phase10Transition L K a b).1 ::ₘ
        ({(Phase10Transition L K a b).2} : Multiset (AgentState L K))) = 0
    rw [Multiset.countP_cons_of_neg]
    · change Multiset.countP IsActiveB
        ((Phase10Transition L K a b).2 ::ₘ (0 : Multiset (AgentState L K))) = 0
      rw [Multiset.countP_cons_of_neg]
      · simp
      · intro hbad
        have : (Phase10Transition L K a b).2.output = .B := hbad.2
        rw [h2out] at this; exact absurd this (by decide)
    · intro hbad
      have : (Phase10Transition L K a b).1.output = .B := hbad.2
      rw [h1out] at this; exact absurd this (by decide)
  have hres :
      Multiset.countP IsActiveB (c - ({a, b} : Multiset (AgentState L K))) =
        Multiset.countP IsActiveB c - 1 := by
    have hsub := Multiset.countP_sub
      (s := c) (t := ({a, b} : Multiset (AgentState L K))) happ IsActiveB
    rw [hsub, hpair_before]
  have hpos_old : 0 < Multiset.countP IsActiveB c :=
    Multiset.countP_pos_of_mem (s := c) hb_mem hb
  unfold activeBCount
  rw [Multiset.countP_add, hpair_after, hres]
  omega

/-- A single active-A / active-B ordered pair, scheduled on an all-phase-10
configuration, lands in the `activeBCount`-drop target. -/
theorem scheduledStep_activeA_activeB_in_drop
    (c : Config (AgentState L K))
    (hphase : ∀ x ∈ c, x.phase.val = 10)
    {a b : AgentState L K} (ha_mem : a ∈ c) (hb_mem : b ∈ c)
    (ha : IsActiveA a) (hb : IsActiveB b) :
    (NonuniformMajority L K).scheduledStep c (a, b) ∈
      dropTarget (activeBCount (L := L) (K := K)) c := by
  have hne : a ≠ b := by
    intro h; subst h
    have : a.output = .B := hb.2
    rw [ha.2] at this; exact absurd this (by decide)
  have happ : Protocol.Applicable c a b := applicable_of_mem_ne ha_mem hb_mem hne
  simp only [dropTarget, Set.mem_setOf_eq, Protocol.scheduledStep]
  have hstep : Protocol.stepOrSelf (NonuniformMajority L K) c a b =
      c - {a, b} + {(Transition L K a b).1, (Transition L K a b).2} := by
    unfold Protocol.stepOrSelf NonuniformMajority
    simp only [if_pos happ]
  rw [hstep]
  exact activeBCount_post_cancel_lt c hphase ha_mem hb_mem ha hb

/-- The active-A × active-B rectangle of ordered pairs. -/
def activeABPairs (c : Config (AgentState L K)) :
    Finset (AgentState L K × AgentState L K) :=
  (Finset.univ.filter (fun a : AgentState L K => IsActiveA a)) ×ˢ
    (Finset.univ.filter (fun a : AgentState L K => IsActiveB a))

/-- The total `interactionCount` over the active-A × active-B rectangle equals
`activeACount c · activeBCount c`.  Active-A and active-B states are disjoint
classes, so the cross-rectangle identity `sum_interactionCount_cross_disjoint`
applies, and each row/column sum of `count` is the respective `countP`. -/
theorem sum_interactionCount_activeAB (c : Config (AgentState L K)) :
    (∑ p ∈ activeABPairs (L := L) (K := K) c, c.interactionCount p.1 p.2)
      = activeACount c * activeBCount c := by
  classical
  have hdisj : ∀ a ∈ Finset.univ.filter (fun a : AgentState L K => IsActiveA a),
      ∀ b ∈ Finset.univ.filter (fun a : AgentState L K => IsActiveB a), a ≠ b := by
    intro a ha b hb hab
    rw [Finset.mem_filter] at ha hb
    subst hab
    have : a.output = .B := hb.2.2
    rw [ha.2.2] at this; exact absurd this (by decide)
  rw [activeABPairs,
    ClockRealMixed.sum_interactionCount_cross_disjoint c _ _ hdisj]
  rw [show (∑ a ∈ Finset.univ.filter (fun a : AgentState L K => IsActiveA a), c.count a)
      = Multiset.countP IsActiveA c from
    (HourCouplingV2.countP_eq_sum_count IsActiveA c).symm]
  rw [show (∑ b ∈ Finset.univ.filter (fun a : AgentState L K => IsActiveB a), c.count b)
      = Multiset.countP IsActiveB c from
    (HourCouplingV2.countP_eq_sum_count IsActiveB c).symm]
  rfl

/-- The present active-A × active-B pairs (those with both states actually present
in `c`). -/
def presentActiveABPairs (c : Config (AgentState L K)) :
    Finset (AgentState L K × AgentState L K) :=
  (activeABPairs (L := L) (K := K) c).filter
    (fun p => 1 ≤ c.count p.1 ∧ 1 ≤ c.count p.2)

/-- The `interactionProb`-sum over the present active-A × active-B pairs equals the
full-rectangle sum (absent pairs have `interactionCount = 0`), which by
`sum_interactionCount_activeAB` is `activeACount · activeBCount / totalPairs`. -/
theorem sum_interactionProb_presentActiveAB (c : Config (AgentState L K)) :
    (∑ p ∈ presentActiveABPairs (L := L) (K := K) c,
        c.interactionProb p.1 p.2)
      = (↑(activeACount c * activeBCount c) : ℝ≥0∞) / (c.totalPairs : ℝ≥0∞) := by
  classical
  -- present-pair sum = full rectangle sum (drop absent pairs: interactionProb 0)
  have hpresent : (∑ p ∈ presentActiveABPairs (L := L) (K := K) c,
        c.interactionProb p.1 p.2)
      = ∑ p ∈ activeABPairs (L := L) (K := K) c, c.interactionProb p.1 p.2 := by
    rw [presentActiveABPairs]
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro p _ hpnot
    simp only [Finset.mem_filter, not_and, not_le, Nat.lt_one_iff] at hpnot
    have hzero : c.interactionCount p.1 p.2 = 0 := by
      unfold Config.interactionCount
      by_cases hpp : p.1 = p.2
      · rw [if_pos hpp]
        rcases Nat.eq_zero_or_pos (c.count p.1) with h1 | h1
        · rw [h1, Nat.zero_mul]
        · have := hpnot h1; omega
      · rw [if_neg hpp]
        rcases Nat.eq_zero_or_pos (c.count p.1) with h1 | h1
        · rw [h1, Nat.zero_mul]
        · rw [hpnot h1, Nat.mul_zero]
    unfold Config.interactionProb; rw [hzero]; simp
  rw [hpresent]
  -- full-rectangle interactionProb sum = (∑ interactionCount) / totalPairs
  have heqterm : ∀ p : AgentState L K × AgentState L K,
      c.interactionProb p.1 p.2
        = (↑(c.interactionCount p.1 p.2) : ℝ≥0∞) * (↑c.totalPairs)⁻¹ := by
    intro p; unfold Config.interactionProb; rw [div_eq_mul_inv]
  rw [Finset.sum_congr rfl (fun p _ => heqterm p), ← Finset.sum_mul, ← Nat.cast_sum,
    sum_interactionCount_activeAB, ← div_eq_mul_inv]

/-- **Cancel-stage per-level drop probability.** On an all-phase-10 configuration
with at least one active-A agent (the majority-A regime), the transition kernel
maps into the `activeBCount`-drop set with probability `≥ activeBCount c /
(n·(n−1))`.  This is the per-level drop lower bound consumed by the
invariant-relative engine with `q m = 1 − m/(n(n−1))`. -/
theorem activeBCount_drop_prob (c : Config (AgentState L K))
    (hc : 2 ≤ c.card)
    (hphase : ∀ x ∈ c, x.phase.val = 10)
    (hA : 1 ≤ activeACount c) :
    (NonuniformMajority L K).transitionKernel c
        (dropTarget (activeBCount (L := L) (K := K)) c) ≥
      (↑(activeBCount c) : ℝ≥0∞) / (c.totalPairs : ℝ≥0∞) := by
  classical
  -- every present active-A × active-B pair lands in the drop target
  have hgood : ∀ pair ∈ presentActiveABPairs (L := L) (K := K) c,
      (NonuniformMajority L K).scheduledStep c pair ∈
        dropTarget (activeBCount (L := L) (K := K)) c := by
    intro pair hpair
    rw [presentActiveABPairs, activeABPairs, Finset.mem_filter, Finset.mem_product,
      Finset.mem_filter, Finset.mem_filter] at hpair
    obtain ⟨⟨⟨_, hA1⟩, ⟨_, hB2⟩⟩, h1, h2⟩ := hpair
    have ha_mem : pair.1 ∈ c := Multiset.count_pos.mp h1
    have hb_mem : pair.2 ∈ c := Multiset.count_pos.mp h2
    have := scheduledStep_activeA_activeB_in_drop c hphase ha_mem hb_mem hA1 hB2
    simpa using this
  -- kernel mass ≥ interactionPMF mass of the good Finset
  have hge := Phase0Convergence.stepDistOrSelf_toMeasure_ge c hc
    (dropTarget (activeBCount (L := L) (K := K)) c)
    (↑(presentActiveABPairs (L := L) (K := K) c) :
      Set (AgentState L K × AgentState L K))
    (fun pair hpair => hgood pair (by simpa using hpair))
  -- the interactionPMF mass of the Finset = the interactionProb sum
  have hSmeasure : (c.interactionPMF hc).toMeasure
      (↑(presentActiveABPairs (L := L) (K := K) c) :
        Set (AgentState L K × AgentState L K))
      = ∑ p ∈ presentActiveABPairs (L := L) (K := K) c, c.interactionProb p.1 p.2 := by
    rw [PMF.toMeasure_apply_finset]; rfl
  rw [sum_interactionProb_presentActiveAB] at hSmeasure
  change (NonuniformMajority L K).transitionKernel c _ ≥ _
  change ((NonuniformMajority L K).stepDistOrSelf c).toMeasure _ ≥ _
  rw [hSmeasure] at hge
  refine le_trans ?_ hge
  -- activeBCount / totalPairs ≤ activeACount·activeBCount / totalPairs (activeACount ≥ 1)
  apply ENNReal.div_le_div_right
  have : activeBCount c ≤ activeACount c * activeBCount c := by
    calc activeBCount c = 1 * activeBCount c := (Nat.one_mul _).symm
      _ ≤ activeACount c * activeBCount c := Nat.mul_le_mul_right _ hA
  exact_mod_cast this

end Phase10Drop

end ExactMajority
