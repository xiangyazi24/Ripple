/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Conditional phase progress — Phase E brick E3 (Doty exact majority)

From any configuration with a FIXED clock count `mC = |Clock| ≥ 2` (the clock count
is determined after Phase 0 and never changes), every *counter-timed* phase finishes
within expected `O((counterMax · mC) · n(n−1) / (mC(mC−1)))` interactions: the clock
counters always tick down, because a clock-clock meeting (probability
`≥ mC(mC−1)/(n(n−1))` per interaction) strictly decrements the combined counter while
it is positive.

This single **parameterized** bound yields BOTH of Phase E's regimes from one lemma:

* **bad-but-big-clock** (`mC ≥ n/5`, Lemma 5.2 floor): the rate is
  `mC(mC−1)/(n(n−1)) ≥ Θ(1)`, so the expected time is `O(counterMax · n)` — linear,
  matching the paper's "`O(log n)` parallel rounds" once `counterMax = O(n log n)`;
* **tiny-clock** (`mC ≥ 2`, the deterministic floor of Lemma 5.2): the rate is
  `≥ 2/(n(n−1))`, so the expected time is `O(counterMax · n²)` — polynomial, the
  negligible-probability fallback regime.

## Engine

The combined clock-counter potential `Φ` (the *sum* of all clock counters) is
non-increasing along `K` (`PotNonincr K Φ`) and drops by `≥ 1` whenever a clock-clock
pair meets, which happens with probability `≥ p := mC(mC−1)/(n(n−1))` **independently
of the current level** (any positive-counter clock pair fires the decrement).  This is
the *uniform-rate* special case of the level-split coupon engine of
`Phase10ExpectedTime.lean`: with `q m = 1 − p` for every level, the per-level waiting
time is `(1 − q m)⁻¹ = p⁻¹`, and `coupon_expectedHitting_le_uniform` gives

    expectedHitting K c (potBelow Φ 1) ≤ (Φ c) · p⁻¹  ≤  (counterMax · mC) · p⁻¹.

`potBelow Φ 1 = {Φ < 1} = {Φ = 0}` is the phase-advance trigger ("all clock counters
hit `0`").

This file is the **generic / parameterized** layer of E3 (cf. how E1/E2 separated the
generic hitting engine from the protocol instantiation in `RoleSplitConcentration` /
`Phase10Backup`).  It is abstract over `K : Kernel α α`, the potential `Φ`, and the
uniform per-step drop probability `p`; the protocol-level discharge of the
clock-clock meeting mass `≥ mC(mC−1)/(n(n−1))` is the consuming brick's obligation
(its rectangle aggregation route is the clock-clock analogue of E2's
`activeABPairs` / `sum_interactionProb_presentActiveAB`).

ZERO sorry, zero axiom (beyond `propext`/`Classical.choice`/`Quot.sound`),
zero `native_decide`.
-/

import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.ExpectedHitting

namespace ExactMajority

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

set_option linter.unusedSectionVars false

namespace ConditionalPhaseProgress

/-! ## Part 0 — Lifted generic coupon-collector hitting engine

The level-split coupon engine lives in `Probability/Phase10ExpectedTime.lean`
(`PotNonincr`, `potBelow`, `coupon_expectedHitting_le_uniform`, …), but that file is
mid-edit by a concurrent agent and its `.olean` is not in the build cache, so it
cannot be imported here.  We therefore **lift** the self-contained generic chain (it
depends only on `ExpectedHitting` + Mathlib) into a private `Engine` namespace.  Each
lemma is verbatim the generic version; no protocol content.  When the campaign closes
and `Phase10ExpectedTime` is built, these can be deduplicated by re-pointing the
E3 headline at the original `coupon_expectedHitting_le_uniform`. -/

namespace Engine

variable {α : Type*} [MeasurableSpace α]

/-- The set of states strictly below level `m`. -/
def potBelow (Φ : α → ℕ) (m : ℕ) : Set α := {x | Φ x < m}

theorem potBelow_measurable [DiscreteMeasurableSpace α] (Φ : α → ℕ) (m : ℕ) :
    MeasurableSet (potBelow Φ m) :=
  DiscreteMeasurableSpace.forall_measurableSet _

/-- Kernel-level "potential non-increasing" hypothesis: one step never strictly
raises `Φ`. -/
def PotNonincr (K : Kernel α α) (Φ : α → ℕ) : Prop :=
  ∀ b : α, K b {x | Φ b < Φ x} = 0

theorem potBelow_absorbing [DiscreteMeasurableSpace α]
    (K : Kernel α α) (Φ : α → ℕ) (hmono : PotNonincr K Φ) (m : ℕ) :
    ∀ x ∈ potBelow Φ m, K x (potBelow Φ m)ᶜ = 0 := by
  intro x hx
  have hsub : ((potBelow Φ m)ᶜ : Set α) ⊆ {y | Φ x < Φ y} := by
    intro y hy
    simp only [potBelow, Set.mem_compl_iff, Set.mem_setOf_eq, not_lt] at hy
    have hxlt : Φ x < m := hx
    exact Set.mem_setOf_eq ▸ (lt_of_lt_of_le hxlt hy)
  exact measure_mono_null hsub (hmono x)

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
        have hcompl : ({y | Φ y ≤ m}ᶜ : Set α) = {x | m < Φ x} := by
          ext y; simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_le]
        rw [hcompl]
        refine measure_mono_null ?_ (hmono c)
        intro y hy
        simp only [Set.mem_setOf_eq] at hy ⊢
        exact lt_of_le_of_lt hc hy
      · intro y hy
        exact ih y hy

theorem level_occ_contract [DiscreteMeasurableSpace α]
    (K : Kernel α α) [IsMarkovKernel K] (Φ : α → ℕ) (hmono : PotNonincr K Φ)
    (m : ℕ) (q : ℝ≥0∞)
    (hdrop : ∀ b : α, Φ b = m → K b (potBelow Φ m)ᶜ ≤ q)
    (c : α) (hc : Φ c ≤ m) (t : ℕ) :
    (K ^ (t + 1)) c (potBelow Φ m)ᶜ ≤ q * (K ^ t) c (potBelow Φ m)ᶜ := by
  classical
  have hbad : MeasurableSet ((potBelow Φ m)ᶜ : Set α) :=
    (potBelow_measurable Φ m).compl
  rw [Kernel.pow_succ_apply_eq_lintegral K t c hbad]
  calc ∫⁻ b, K b (potBelow Φ m)ᶜ ∂((K ^ t) c)
      ≤ ∫⁻ b, q * Set.indicator ((potBelow Φ m)ᶜ) (fun _ => (1 : ℝ≥0∞)) b
          ∂((K ^ t) c) := by
        apply lintegral_mono_ae
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
          · have hbb : b ∈ potBelow Φ m := hlt
            rw [potBelow_absorbing K Φ hmono m b hbb]; exact zero_le'
          · have hbmem : b ∈ ((potBelow Φ m)ᶜ : Set α) := by
              simp only [potBelow, Set.mem_compl_iff, Set.mem_setOf_eq, not_lt]
              exact heq.ge
            rw [Set.indicator_of_mem hbmem, mul_one]
            exact hdrop b heq
    _ = q * (K ^ t) c (potBelow Φ m)ᶜ := by
        rw [lintegral_const_mul q (measurable_const.indicator hbad)]
        congr 1
        rw [lintegral_indicator hbad]; simp

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

/-- The level-`m` occupation along the chain from `c`. -/
noncomputable def occLevel (K : Kernel α α) (Φ : α → ℕ) (m : ℕ) (c : α) : ℝ≥0∞ :=
  ∑' t : ℕ, (K ^ t) c {x | Φ x = m}

theorem expectedHitting_eq_tsum_occLevel [DiscreteMeasurableSpace α]
    (K : Kernel α α) [IsMarkovKernel K] (Φ : α → ℕ) (c : α) :
    expectedHitting K c (potBelow Φ 1) = ∑' m : ℕ, occLevel K Φ (m + 1) c := by
  simp only [expectedHitting, occLevel]
  rw [ENNReal.tsum_comm]
  refine tsum_congr (fun t => ?_)
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

theorem coupon_expectedHitting_le_of_occBounds [DiscreteMeasurableSpace α]
    (K : Kernel α α) [IsMarkovKernel K] (Φ : α → ℕ)
    (q : ℕ → ℝ≥0∞) (M : ℕ) (c : α)
    (hocc : ∀ m : ℕ, 1 ≤ m → m ≤ M → occLevel K Φ m c ≤ (1 - q m)⁻¹)
    (hhi : ∀ m : ℕ, M < m → occLevel K Φ m c = 0) :
    expectedHitting K c (potBelow Φ 1) ≤ ∑ m ∈ Finset.Icc 1 M, (1 - q m)⁻¹ := by
  rw [expectedHitting_eq_tsum_occLevel K Φ c]
  rw [tsum_eq_sum (s := Finset.range M) (fun m hm => by
    rw [Finset.mem_range, not_lt] at hm
    exact hhi (m + 1) (by omega))]
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

noncomputable def occLevelUpTo (K : Kernel α α) (Φ : α → ℕ) (m : ℕ) (t : ℕ) (c : α) :
    ℝ≥0∞ :=
  ∑ i ∈ Finset.range t, (K ^ i) c {x | Φ x = m}

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
      · calc occLevelUpTo K Φ m (t + 1) c
            ≤ occLevel K Φ m c := by
              rw [occLevelUpTo, occLevel]; exact ENNReal.sum_le_tsum _
          _ ≤ (1 - q)⁻¹ := occLevel_le_of_start_le K Φ hmono m q hdrop c hc
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
        calc ∫⁻ b, (∑ j ∈ Finset.range t, (K ^ j) b {x | Φ x = m}) ∂(K c)
            ≤ ∫⁻ _ : α, (1 - q)⁻¹ ∂(K c) := by
              apply lintegral_mono
              intro b
              simpa only [occLevelUpTo] using ih b
          _ = (1 - q)⁻¹ := by
              rw [lintegral_const, measure_univ, mul_one]

theorem occLevel_le [DiscreteMeasurableSpace α]
    (K : Kernel α α) [IsMarkovKernel K] (Φ : α → ℕ) (hmono : PotNonincr K Φ)
    (m : ℕ) (q : ℝ≥0∞)
    (hdrop : ∀ b : α, Φ b = m → K b (potBelow Φ m)ᶜ ≤ q)
    (c : α) :
    occLevel K Φ m c ≤ (1 - q)⁻¹ := by
  rw [occLevel, ENNReal.tsum_eq_iSup_nat]
  refine iSup_le (fun t => ?_)
  exact occLevelUpTo_le K Φ hmono m q hdrop t c

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

theorem coupon_expectedHitting_le [DiscreteMeasurableSpace α]
    (K : Kernel α α) [IsMarkovKernel K] (Φ : α → ℕ) (hmono : PotNonincr K Φ)
    (q : ℕ → ℝ≥0∞)
    (hdrop : ∀ m : ℕ, ∀ b : α, Φ b = m → K b (potBelow Φ m)ᶜ ≤ q m)
    (M : ℕ) (c : α) (hc : Φ c ≤ M) :
    expectedHitting K c (potBelow Φ 1) ≤ ∑ m ∈ Finset.Icc 1 M, (1 - q m)⁻¹ :=
  coupon_expectedHitting_le_of_occBounds K Φ q M c
    (fun m _ _ => occLevel_le K Φ hmono m (q m) (hdrop m) c)
    (fun m hm => occLevel_eq_zero_of_high K Φ hmono M c hc m hm)

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

/-- **Generic coupon capstone with crude uniform evaluation.** Under non-increasing
`Φ`, a per-level drop family `q`, a start `c` at level `≤ M`, and a uniform per-level
waiting-time ceiling `r`, the expected hitting time of `{Φ = 0}` is `≤ M · r`. -/
theorem coupon_expectedHitting_le_uniform [DiscreteMeasurableSpace α]
    (K : Kernel α α) [IsMarkovKernel K] (Φ : α → ℕ) (hmono : PotNonincr K Φ)
    (q : ℕ → ℝ≥0∞)
    (hdrop : ∀ m : ℕ, ∀ b : α, Φ b = m → K b (potBelow Φ m)ᶜ ≤ q m)
    (M : ℕ) (c : α) (hc : Φ c ≤ M) (r : ℝ≥0∞)
    (hq : ∀ m : ℕ, 1 ≤ m → m ≤ M → (1 - q m)⁻¹ ≤ r) :
    expectedHitting K c (potBelow Φ 1) ≤ (M : ℝ≥0∞) * r :=
  le_trans (coupon_expectedHitting_le K Φ hmono q hdrop M c hc)
    (coupon_sum_le_of_uniform q M r hq)

end Engine

/-! ## Part 1 — The uniform per-step drop rate arithmetic

The clock-clock meeting rate is `p = mC(mC−1)/(n(n−1))`.  We package the rate as an
`ℝ≥0∞` and record its reciprocal (= the per-level waiting time) in the two regimes. -/

/-- The clock-clock meeting probability per interaction at clock count `mC` in a
population of `n` agents: `mC(mC−1)` ordered clock pairs out of `n(n−1)` ordered
pairs. -/
noncomputable def clockPairRate (mC n : ℕ) : ℝ≥0∞ :=
  (mC * (mC - 1) : ℕ) / (n * (n - 1) : ℕ)

/-- The per-step counter-progress mass is at most `1` (it is a probability): a clock
pair is one event among the `n(n−1)` ordered pairs.  Needed so `1 − (1 − p) = p`
does not underflow in `ℝ≥0∞`. -/
theorem clockPairRate_le_one (mC n : ℕ) (hmC : mC ≤ n) :
    clockPairRate mC n ≤ 1 := by
  unfold clockPairRate
  have hnum : mC * (mC - 1) ≤ n * (n - 1) := Nat.mul_le_mul hmC (by omega)
  calc ((mC * (mC - 1) : ℕ) : ℝ≥0∞) / (n * (n - 1) : ℕ)
      ≤ ((n * (n - 1) : ℕ) : ℝ≥0∞) / (n * (n - 1) : ℕ) := by
        apply ENNReal.div_le_div_right
        exact_mod_cast hnum
    _ ≤ 1 := ENNReal.div_self_le_one

/-- The per-level waiting time `(1 - (1 - p))⁻¹ = p⁻¹` for the uniform drop
`q m = 1 - p`, where `p = clockPairRate mC n ≤ 1`.  This is the reciprocal of the
clock-clock meeting rate: `n(n−1)/(mC(mC−1))` interactions per counter tick. -/
theorem one_sub_one_sub_clockPairRate_inv (mC n : ℕ) (hmC : mC ≤ n) :
    (1 - (1 - clockPairRate mC n))⁻¹ = (clockPairRate mC n)⁻¹ := by
  rw [ENNReal.sub_sub_cancel (by norm_num) (clockPairRate_le_one mC n hmC)]

/-- The clock-clock waiting-time reciprocal in closed form:
`(clockPairRate mC n)⁻¹ = (n(n−1)) / (mC(mC−1))` interactions per counter decrement.
Valid whenever there are at least two clocks (`2 ≤ mC`), so the denominator
`mC(mC−1)` is positive and the division is genuine. -/
theorem clockPairRate_inv_eq (mC n : ℕ) (hmC : 2 ≤ mC) (hn : 2 ≤ n) :
    (clockPairRate mC n)⁻¹ = (n * (n - 1) : ℕ) / (mC * (mC - 1) : ℕ) := by
  unfold clockPairRate
  have hnum0 : ((mC * (mC - 1) : ℕ) : ℝ≥0∞) ≠ 0 := by
    simp only [ne_eq, Nat.cast_eq_zero, Nat.mul_eq_zero]; omega
  have hden0 : ((n * (n - 1) : ℕ) : ℝ≥0∞) ≠ 0 := by
    simp only [ne_eq, Nat.cast_eq_zero, Nat.mul_eq_zero]; omega
  rw [ENNReal.inv_div (Or.inl (ENNReal.natCast_ne_top _)) (Or.inl hden0)]

/-! ## Part 2 — The parameterized headline

The combined clock-counter potential `Φ` (the *sum* of the clock counters, picked
because it is `PotNonincr`-friendly: each clock-clock decrement lowers the sum by
`≥ 1` while it is positive, and non-clock interactions leave it untouched) descends
to `0` at the uniform per-step rate `clockPairRate mC n = mC(mC−1)/(n(n−1))`,
independent of the current level.  Starting from `Φ c ≤ counterMax · mC`, the
expected time to hit `{Φ = 0}` (phase advanced — all clock counters at `0`) is
`≤ (counterMax · mC) · (clockPairRate mC n)⁻¹` interactions.

This is the **single parameterized bound** that yields both Phase-E regimes
(Part 3).  It is abstract over the kernel and the drop rate; the protocol-level
discharge of (i) `PotNonincr K Φ` for the clock-counter sum and (ii) the per-level
drop `≥ clockPairRate mC n` (the clock-clock rectangle aggregation) is the consuming
brick's obligation — the clock-clock analogue of E2's
`activeABPairs`/`sum_interactionProb_presentActiveAB` machinery. -/

variable {α : Type*} [MeasurableSpace α]

/-- **Headline: counter-timed phase expected progress.**  Let `Φ : α → ℕ` be the
combined clock-counter potential, non-increasing along `K` (`hmono`), and suppose
from every state at level exactly `m ≥ 1` a single interaction drops `Φ` below `m`
with probability at least `clockPairRate mC n` (a clock-clock meeting fires the
decrement), i.e. the not-yet-dropped mass is `≤ 1 - clockPairRate mC n` (`hdrop`).
Then from a start `c` with `Φ c ≤ counterMax · mC` the expected number of
interactions to all-counters-zero is

    expectedHitting K c {Φ = 0} ≤ (counterMax · mC) · (clockPairRate mC n)⁻¹.

(`Engine.potBelow Φ 1 = {Φ < 1} = {Φ = 0}` is the phase-advance trigger.) -/
theorem timed_phase_expected_progress [DiscreteMeasurableSpace α]
    (K : Kernel α α) [IsMarkovKernel K] (Φ : α → ℕ)
    (hmono : Engine.PotNonincr K Φ)
    (mC n counterMax : ℕ) (hmC : mC ≤ n)
    (hdrop : ∀ m : ℕ, ∀ b : α, Φ b = m →
      K b (Engine.potBelow Φ m)ᶜ ≤ 1 - clockPairRate mC n)
    (c : α) (hc : Φ c ≤ counterMax * mC) :
    expectedHitting K c (Engine.potBelow Φ 1)
      ≤ ((counterMax * mC : ℕ) : ℝ≥0∞) * (clockPairRate mC n)⁻¹ := by
  apply Engine.coupon_expectedHitting_le_uniform K Φ hmono
    (fun _ => 1 - clockPairRate mC n) (fun m => hdrop m)
    (counterMax * mC) c hc
  -- per-level ceiling: `(1 - (1 - clockPairRate))⁻¹ = (clockPairRate)⁻¹ ≤ r` (with equality).
  intro m _ _
  rw [one_sub_one_sub_clockPairRate_inv mC n hmC]

/-! ## Part 3 — The two regime instantiations

One headline, two regimes, separated only by the lower bound carried on the (fixed,
post-Phase-0) clock count `mC`.  The whole difference is an upper bound on the
waiting-time reciprocal `(clockPairRate mC n)⁻¹ = n(n−1)/(mC(mC−1))`. -/

/-- **Waiting-time reciprocal, closed form, bounded by the clock floor.**  Using the
closed form `(clockPairRate mC n)⁻¹ = n(n−1)/(mC(mC−1))` and a floor `d ≤ mC(mC−1)`
on the clock-pair count (`d ≥ 1`), the waiting time is `≤ n(n−1)/d`.  Both regime
corollaries are this with the appropriate `d`. -/
theorem clockPairRate_inv_le_div (mC n d : ℕ) (hmC : 2 ≤ mC) (hn : 2 ≤ n)
    (hfloor : d ≤ mC * (mC - 1)) :
    (clockPairRate mC n)⁻¹ ≤ (n * (n - 1) : ℕ) / (d : ℕ) := by
  rw [clockPairRate_inv_eq mC n hmC hn]
  apply ENNReal.div_le_div_left
  exact_mod_cast hfloor

/-- **Headline product, simplified by the `mC`-cancellation.**  The headline RHS
`(counterMax · mC) · (clockPairRate mC n)⁻¹` equals `counterMax · n(n−1) / (mC − 1)`:
the `mC` factor in the prefactor cancels one of the two factors in the clock-pair
count `mC(mC−1)`.  This is the key algebraic identity for both regimes. -/
theorem headline_product_eq (counterMax mC n : ℕ) (hmC : 2 ≤ mC) (hn : 2 ≤ n) :
    ((counterMax * mC : ℕ) : ℝ≥0∞) * (clockPairRate mC n)⁻¹
      = ((counterMax : ℕ) : ℝ≥0∞) * ((n * (n - 1) : ℕ) : ℝ≥0∞) / ((mC - 1 : ℕ) : ℝ≥0∞) := by
  rw [clockPairRate_inv_eq mC n hmC hn]
  have hmc0 : ((mC : ℕ) : ℝ≥0∞) ≠ 0 := by simp; omega
  have hmctop : ((mC : ℕ) : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  have hcast1 : ((mC * (mC - 1) : ℕ) : ℝ≥0∞)
      = ((mC : ℕ) : ℝ≥0∞) * ((mC - 1 : ℕ) : ℝ≥0∞) := by push_cast; ring
  have hcast2 : ((counterMax * mC : ℕ) : ℝ≥0∞)
      = ((counterMax : ℕ) : ℝ≥0∞) * ((mC : ℕ) : ℝ≥0∞) := by push_cast; ring
  rw [hcast1, hcast2, ← mul_div_assoc]
  rw [show ((counterMax : ℕ) : ℝ≥0∞) * ((mC : ℕ) : ℝ≥0∞) * ((n * (n - 1) : ℕ) : ℝ≥0∞)
       = ((mC : ℕ) : ℝ≥0∞) * (((counterMax : ℕ) : ℝ≥0∞) * ((n * (n - 1) : ℕ) : ℝ≥0∞)) by ring]
  rw [ENNReal.mul_div_mul_left _ _ hmc0 hmctop]

/-- **Corollary (b): tiny-clock poly(n) fallback.**  With only the deterministic
floor `mC ≥ 2` (Lemma 5.2's deterministic part: at least two clocks always), the
expected time to advance a counter-timed phase is `≤ counterMax · n²` interactions —
the polynomial bound used for the super-polynomially-rare tiny-clock event.

Algebra: `(counterMax · mC) · rate⁻¹ = counterMax · n(n−1)/(mC−1) ≤ counterMax · n(n−1)
≤ counterMax · n²`, using `mC − 1 ≥ 1` and `n − 1 ≤ n`. -/
theorem timed_phase_progress_tinyClock [DiscreteMeasurableSpace α]
    (K : Kernel α α) [IsMarkovKernel K] (Φ : α → ℕ)
    (hmono : Engine.PotNonincr K Φ)
    (mC n counterMax : ℕ) (hmC : 2 ≤ mC) (hmCn : mC ≤ n) (hn : 2 ≤ n)
    (hdrop : ∀ m : ℕ, ∀ b : α, Φ b = m →
      K b (Engine.potBelow Φ m)ᶜ ≤ 1 - clockPairRate mC n)
    (c : α) (hc : Φ c ≤ counterMax * mC) :
    expectedHitting K c (Engine.potBelow Φ 1)
      ≤ ((counterMax : ℕ) : ℝ≥0∞) * ((n * n : ℕ) : ℝ≥0∞) := by
  refine le_trans
    (timed_phase_expected_progress K Φ hmono mC n counterMax hmCn hdrop c hc) ?_
  rw [headline_product_eq counterMax mC n hmC hn]
  -- counterMax·n(n−1)/(mC−1) ≤ counterMax·n(n−1)/1 = counterMax·n(n−1) ≤ counterMax·n²
  calc ((counterMax : ℕ) : ℝ≥0∞) * ((n * (n - 1) : ℕ) : ℝ≥0∞) / ((mC - 1 : ℕ) : ℝ≥0∞)
      ≤ ((counterMax : ℕ) : ℝ≥0∞) * ((n * (n - 1) : ℕ) : ℝ≥0∞) / ((1 : ℕ) : ℝ≥0∞) := by
        apply ENNReal.div_le_div_left
        exact_mod_cast (by omega : (1 : ℕ) ≤ mC - 1)
    _ = ((counterMax : ℕ) : ℝ≥0∞) * ((n * (n - 1) : ℕ) : ℝ≥0∞) := by
        rw [Nat.cast_one, div_one]
    _ ≤ ((counterMax : ℕ) : ℝ≥0∞) * ((n * n : ℕ) : ℝ≥0∞) := by
        gcongr
        · exact_mod_cast (by omega : n - 1 ≤ n)

/-- **Corollary (a): big-clock linear bound.**  Under the Lemma 5.2 carried floor
`n/5 ≤ mC` (the `RoleSplitConcentration.clockCount_linear_of_RoleSplitGood`
conclusion, supplied here as a hypothesis since that file is mid-edit and not
imported), the expected time to advance a counter-timed phase is `≤ counterMax · 11 n`
interactions — **linear** in `n` (the clock-clock rate is `Θ(1)`).  With
`counterMax = O(n log n)` this is the paper's `O(n² log n)` interactions = `O(n log n)`
parallel rounds for the bad-but-big-clock event.

Algebra: `(counterMax · mC) · rate⁻¹ = counterMax · n(n−1)/(mC−1) ≤ counterMax · 11 n`,
because `n/5 ≤ mC` (with `n ≥ 18`) gives `n − 1 ≤ 11(mC − 1)`, hence
`n(n−1) ≤ 11 n (mC − 1)`.  The constant `11` is not optimal (any `mC ≥ cn` gives a
constant); it is chosen to clear the `Nat`-floor slack uniformly for `n ≥ 18`. -/
theorem timed_phase_progress_bigClock [DiscreteMeasurableSpace α]
    (K : Kernel α α) [IsMarkovKernel K] (Φ : α → ℕ)
    (hmono : Engine.PotNonincr K Φ)
    (mC n counterMax : ℕ) (hfloor : n / 5 ≤ mC) (hmCn : mC ≤ n) (hn : 18 ≤ n)
    (hdrop : ∀ m : ℕ, ∀ b : α, Φ b = m →
      K b (Engine.potBelow Φ m)ᶜ ≤ 1 - clockPairRate mC n)
    (c : α) (hc : Φ c ≤ counterMax * mC) :
    expectedHitting K c (Engine.potBelow Φ 1)
      ≤ ((counterMax : ℕ) : ℝ≥0∞) * ((11 * n : ℕ) : ℝ≥0∞) := by
  have hmC : 2 ≤ mC := by omega
  refine le_trans
    (timed_phase_expected_progress K Φ hmono mC n counterMax hmCn hdrop c hc) ?_
  rw [headline_product_eq counterMax mC n hmC (by omega)]
  -- counterMax·n(n−1)/(mC−1) ≤ counterMax·(11n) via div_le_of_le_mul on the ℕ core.
  apply ENNReal.div_le_of_le_mul
  -- counterMax·n(n−1) ≤ (counterMax·11n)·(mC−1)
  have hcore : n * (n - 1) ≤ 11 * n * (mC - 1) := by
    have hkey : n - 1 ≤ 11 * (mC - 1) := by omega
    calc n * (n - 1) ≤ n * (11 * (mC - 1)) := Nat.mul_le_mul_left n hkey
      _ = 11 * n * (mC - 1) := by ring
  have hnat : counterMax * (n * (n - 1)) ≤ counterMax * (11 * n) * (mC - 1) := by
    calc counterMax * (n * (n - 1)) ≤ counterMax * (11 * n * (mC - 1)) :=
          Nat.mul_le_mul_left counterMax hcore
      _ = counterMax * (11 * n) * (mC - 1) := by ring
  calc ((counterMax : ℕ) : ℝ≥0∞) * ((n * (n - 1) : ℕ) : ℝ≥0∞)
      = ((counterMax * (n * (n - 1)) : ℕ) : ℝ≥0∞) := by push_cast; ring
    _ ≤ ((counterMax * (11 * n) * (mC - 1) : ℕ) : ℝ≥0∞) := by exact_mod_cast hnat
    _ = ((counterMax : ℕ) : ℝ≥0∞) * ((11 * n : ℕ) : ℝ≥0∞) * ((mC - 1 : ℕ) : ℝ≥0∞) := by
        push_cast; ring

end ConditionalPhaseProgress

end ExactMajority
