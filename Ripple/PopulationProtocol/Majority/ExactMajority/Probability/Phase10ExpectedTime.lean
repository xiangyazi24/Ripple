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

/-! ### Phase-10 instantiation target

For the real protocol `K := (NonuniformMajority L K).transitionKernel` and the
stage potentials of `Analysis/Phase10Backup.lean`:

* **cancel stage** `Φ := activeBCount` (majority A case): `Done = {activeBCount = 0}`;
* **absorb-T stage** `Φ := wrongACount` after `activeBCount = 0`;
* **convert-passive stage** `Φ := wrongACount` (passive recount).

Each needs three protocol facts to feed the generic engine:
1. `PotNonincr K Φ` — one scheduler step never increases the potential.  Follows
   from the per-pair non-increase lemmas (`activeBCount_cancel_A_B_lt` /
   `wrongACount_activeA_nonActiveB_lt` give *strict* decrease on the useful pair;
   the support-wide non-increase is the easy direction: no Phase-10 reaction
   creates active B / un-A's an A).
2. the per-level drop `∀ b, Φ b = m → K b (potBelow Φ m)ᶜ ≤ q m` with
   `q m = 1 - (lower bound on useful-pair interaction probability)`.  The useful
   probability is `≥ (class interactionCount) / (n(n−1))`; with `m` active-B (or
   `m` wrong-A) agents and `≥ 1` active-A, the class count is `≥ m` (one active-A
   times `m` partners), so `q m = 1 - m / (n(n−1))` and
   `(1 - q m)⁻¹ = n(n−1)/m`.  Establishing this lower bound is where the
   **state-multiplicity** subtlety lives: "active A" is a *class* of `AgentState`
   records, so the single-pair technique of
   `Phase2TimeConvergence.step_advance_prob` must be aggregated over the class via
   `interactionCount`'s additivity (a `Finset.sum` over the active-A / wrong-A
   states present), rather than instantiated at one fixed `Λ` value.
3. the harmonic evaluation `∑_{m=1}^{n} n(n−1)/m = n(n−1) H_n = O(n² log n)`.

The three stages are then chained by `expectedHitting_le_through_mid`
(majority/tie case split via `Phase10Backup.backupSignal` sign), giving the
Lemma 7.7 expectation bound in interaction counts. -/

end Coupon

end ExactMajority
