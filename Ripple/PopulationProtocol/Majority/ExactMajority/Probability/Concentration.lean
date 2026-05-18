/-
Concentration inequalities (Theorem 4.1 of Doty et al.).

These are standard multiplicative Chernoff bounds for sums of independent
[0,1]-valued random variables. Stated here in the `ProbabilityTheory` kernel
/ measure framework used by the rest of the development.

Mathlib provides a sub-Gaussian sum-of-independents bound
(`measure_sum_ge_le_of_iIndepFun`) which can be specialized to the
multiplicative Chernoff form once the correct variance-proxy lemma for
[0,1]-valued variables is proved. The proof is beyond our current scope;
the statements below give the exact Doty et al. Theorem 4.1 inequalities
with correct type signatures as hooks for downstream consumers.

Reference: Doty et al., Theorem 4.1.
-/

import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open Finset
open MeasureTheory ProbabilityTheory
open scoped Real BigOperators NNReal ENNReal

namespace ExactMajority

/-- **Hoeffding-form upper tail bound** (weaker than Doty et al. Theorem 4.1's
multiplicative form). For X = ∑ X_i a sum of independent [0,1]-valued RVs with
mean μS = E[X], for any δ > 0,
  P { (1+δ)·μS ≤ X } ≤ exp(−2·(δ·μS)²/k).
This is the additive Hoeffding bound; the multiplicative Doty form
exp(−δ²·μS/(2+δ)) requires Bernstein-style reasoning not yet in Mathlib. -/
theorem chernoff_upper {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (k : ℕ) (X : ℕ → Ω → ℝ) (h_indep : iIndepFun X P)
    (h_range : ∀ i, AEMeasurable (X i) P)
    (h_bound : ∀ i, ∀ᵐ ω ∂P, X i ω ∈ Set.Icc (0 : ℝ) 1)
    (_h_support : ∀ i ≥ k, ∀ᵐ ω ∂P, X i ω = 0)
    (S : Ω → ℝ) (μS : ℝ)
    (hS : S = fun ω => Finset.sum (range k) (fun i => X i ω))
    (hμS : μS = Finset.sum (range k) (fun i => ∫ x, X i x ∂P))
    (δ : ℝ) (hδ : 0 < δ) (hμS_nn : 0 ≤ μS) :
    P.real {ω | (1 + δ) * μS ≤ S ω} ≤ Real.exp (-2 * (δ * μS) ^ 2 / k) := by
  -- Centered variables Y_i := X_i - E[X_i]
  let Y : ℕ → Ω → ℝ := fun i ω => X i ω - ∫ x, X i x ∂P
  -- Each Y_i is sub-Gaussian with proxy 1/4 via Hoeffding's lemma for [0,1]-valued RVs.
  have h_subG : ∀ i, HasSubgaussianMGF (Y i) ((1 : ℝ≥0) / 4) P := by
    intro i
    have h := hasSubgaussianMGF_of_mem_Icc (μ := P) (h_range i) (h_bound i)
    have hproxy : ((‖(1 : ℝ) - 0‖₊ / 2) ^ 2 : ℝ≥0) = (1 : ℝ≥0) / 4 := by
      have : ‖(1 : ℝ) - 0‖₊ = 1 := by simp
      rw [this]; norm_num
    rw [hproxy] at h
    exact h
  -- Independence: Y_i = (· - μ_i) ∘ X_i and (· - μ_i) is measurable.
  have h_indep_Y : iIndepFun Y P := by
    have hg : ∀ i, Measurable (fun x : ℝ => x - ∫ x, X i x ∂P) := fun i =>
      measurable_id.sub_const _
    exact h_indep.comp _ hg
  -- ε := δ·μS ≥ 0 and apply Hoeffding sum inequality.
  have hε : (0 : ℝ) ≤ δ * μS := mul_nonneg hδ.le hμS_nn
  have h_tail :
      P.real {ω | δ * μS ≤ ∑ i ∈ Finset.range k, Y i ω} ≤
        Real.exp (-(δ * μS) ^ 2 / (2 * k * ((1 : ℝ≥0) / 4 : ℝ))) :=
    HasSubgaussianMGF.measure_sum_range_ge_le_of_iIndepFun
      h_indep_Y (fun i _ => h_subG i) hε
  -- Rewrite the event {δ·μS ≤ ∑Y} = {(1+δ)·μS ≤ S}.
  have h_event_eq : {ω | δ * μS ≤ ∑ i ∈ Finset.range k, Y i ω} =
      {ω | (1 + δ) * μS ≤ S ω} := by
    ext ω
    simp only [Set.mem_setOf_eq, Y]
    have hsum : ∑ i ∈ Finset.range k, (X i ω - ∫ x, X i x ∂P) = S ω - μS := by
      rw [Finset.sum_sub_distrib]
      simp [hS, hμS]
    rw [hsum]
    constructor <;> intro h <;> linarith
  rw [h_event_eq] at h_tail
  -- Simplify exponent: (2·k·(1/4)) = k/2; -(δ·μS)²/(k/2) = -2(δ·μS)²/k
  have h_exp_eq :
      Real.exp (-(δ * μS) ^ 2 / (2 * k * ((1 : ℝ≥0) / 4 : ℝ))) =
        Real.exp (-2 * (δ * μS) ^ 2 / k) := by
    congr 1
    have : ((1 : ℝ≥0) / 4 : ℝ) = 1 / 4 := by norm_num
    rw [this]
    by_cases hk : (k : ℝ) = 0
    · simp [hk]
    · field_simp
      ring
  rw [h_exp_eq] at h_tail
  exact h_tail

/-- **Hoeffding-form lower tail bound** (weaker than Doty et al. Theorem 4.1's
multiplicative form). For X = ∑ X_i a sum of independent [0,1]-valued RVs with
mean μS = E[X], for any δ ∈ (0, 1),
  P { X ≤ (1−δ)·μS } ≤ exp(−2·(δ·μS)²/k).
The negated centered variables -(X_i - μ_i) are still sub-Gaussian with proxy 1/4
(by `HasSubgaussianMGF.neg`); the rest mirrors `chernoff_upper`. -/
theorem chernoff_lower {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (k : ℕ) (X : ℕ → Ω → ℝ) (h_indep : iIndepFun X P)
    (h_range : ∀ i, AEMeasurable (X i) P)
    (h_bound : ∀ i, ∀ᵐ ω ∂P, X i ω ∈ Set.Icc (0 : ℝ) 1)
    (_h_support : ∀ i ≥ k, ∀ᵐ ω ∂P, X i ω = 0)
    (S : Ω → ℝ) (μS : ℝ)
    (hS : S = fun ω => Finset.sum (range k) (fun i => X i ω))
    (hμS : μS = Finset.sum (range k) (fun i => ∫ x, X i x ∂P))
    (δ : ℝ) (hδ : 0 < δ) (_hδ1 : δ < 1) (hμS_nn : 0 ≤ μS) :
    P.real {ω | S ω ≤ (1 - δ) * μS} ≤ Real.exp (-2 * (δ * μS) ^ 2 / k) := by
  -- Negated centered variables Z_i := -(X_i - E[X_i]) = E[X_i] - X_i.
  let Z : ℕ → Ω → ℝ := fun i ω => (∫ x, X i x ∂P) - X i ω
  have h_subG : ∀ i, HasSubgaussianMGF (Z i) ((1 : ℝ≥0) / 4) P := by
    intro i
    have h := hasSubgaussianMGF_of_mem_Icc (μ := P) (h_range i) (h_bound i)
    have hproxy : ((‖(1 : ℝ) - 0‖₊ / 2) ^ 2 : ℝ≥0) = (1 : ℝ≥0) / 4 := by
      have : ‖(1 : ℝ) - 0‖₊ = 1 := by simp
      rw [this]; norm_num
    rw [hproxy] at h
    -- h : HasSubgaussianMGF (X_i - μ[X_i]) (1/4) P; negate to get Z_i.
    have h_neg := h.neg
    -- Identify -(X_i - μ[X_i]) with Z_i.
    -- h_neg has form `HasSubgaussianMGF (-fun ω => X i ω - μ[X i]) (1/4) P`.
    -- Rewrite to identify with Z i.
    have h_eq : (-fun ω => X i ω - ∫ x, X i x ∂P) = Z i := by
      funext ω; simp [Z]
    rw [h_eq] at h_neg
    exact h_neg
  have h_indep_Z : iIndepFun Z P := by
    have hg : ∀ i, Measurable (fun x : ℝ => (∫ y, X i y ∂P) - x) := fun i =>
      measurable_const.sub measurable_id
    exact h_indep.comp _ hg
  have hε : (0 : ℝ) ≤ δ * μS := mul_nonneg hδ.le hμS_nn
  have h_tail :
      P.real {ω | δ * μS ≤ ∑ i ∈ Finset.range k, Z i ω} ≤
        Real.exp (-(δ * μS) ^ 2 / (2 * k * ((1 : ℝ≥0) / 4 : ℝ))) :=
    HasSubgaussianMGF.measure_sum_range_ge_le_of_iIndepFun
      h_indep_Z (fun i _ => h_subG i) hε
  have h_event_eq : {ω | δ * μS ≤ ∑ i ∈ Finset.range k, Z i ω} =
      {ω | S ω ≤ (1 - δ) * μS} := by
    ext ω
    simp only [Set.mem_setOf_eq, Z]
    have hsum : ∑ i ∈ Finset.range k, ((∫ x, X i x ∂P) - X i ω) = μS - S ω := by
      rw [Finset.sum_sub_distrib]
      simp [hS, hμS]
    rw [hsum]
    constructor <;> intro h <;> linarith
  rw [h_event_eq] at h_tail
  have h_exp_eq :
      Real.exp (-(δ * μS) ^ 2 / (2 * k * ((1 : ℝ≥0) / 4 : ℝ))) =
        Real.exp (-2 * (δ * μS) ^ 2 / k) := by
    congr 1
    have : ((1 : ℝ≥0) / 4 : ℝ) = 1 / 4 := by norm_num
    rw [this]
    by_cases hk : (k : ℝ) = 0
    · simp [hk]
    · field_simp
      ring
  rw [h_exp_eq] at h_tail
  exact h_tail

end ExactMajority
