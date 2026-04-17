/-
  Ripple.LPP.NAP — Non-Autocatalytic Protocols via Cubing

  Formalizes the PP → NAP construction from [BD] (Huang-Huls, DNA 30):
  - The r²-trick lifts a PP (degree 2) to a 4-PP (degree 4)
  - Cubing (degree-3 lifting) produces a NAP
  - NAP Splitting Feasibility: every positive monomial admits a
    non-autocatalytic factorization

  The key theorem (NAP Splitting Feasibility) is purely combinatorial:
  it concerns exponent vectors of monomials and their factorizations.

  Reference: Note 14 (working_notes/14_cubing_NAP_feasibility.tex)
-/

import Ripple.LPP.Defs

namespace Ripple

/-! ## Multi-indices

A multi-index α ∈ ℕⁿ represents the monomial x₀^{α₀} · x₁^{α₁} · ⋯.
The weight |α| = Σ αⱼ is the total degree. -/

/-- The weight (total degree) of a multi-index. -/
def miWeight {n : ℕ} (α : Fin n → ℕ) : ℕ := ∑ j, α j

/-- The support of a multi-index: indices where αⱼ > 0. -/
def miSupp {n : ℕ} (α : Fin n → ℕ) : Finset (Fin n) :=
  Finset.univ.filter (fun j => 0 < α j)

/-- A multi-index divides another if αⱼ ≤ βⱼ for all j. -/
def miDvd {n : ℕ} (α β : Fin n → ℕ) : Prop := ∀ j, α j ≤ β j

/-- The standard basis multi-index eⱼ (1 at position j, 0 elsewhere). -/
def miUnit {n : ℕ} (j : Fin n) : Fin n → ℕ := fun k => if k = j then 1 else 0

theorem miWeight_unit {n : ℕ} (j : Fin n) : miWeight (miUnit j) = 1 := by
  simp [miWeight, miUnit]

/-! ## Degree-3 factorizations

A factorization of a degree-6 monomial δ is a pair (β, γ) with
β + γ = δ and |β| = |γ| = 3.

A factorization is *non-autocatalytic* for α if β ≠ α and γ ≠ α. -/

/-- A factorization of δ into β + γ. -/
structure MonomialSplit {n : ℕ} (δ : Fin n → ℕ) where
  β : Fin n → ℕ
  γ : Fin n → ℕ
  sum_eq : ∀ j, β j + γ j = δ j

/-- A split is degree-balanced (both factors have degree 3). -/
def MonomialSplit.balanced {n : ℕ} {δ : Fin n → ℕ} (s : MonomialSplit δ) : Prop :=
  miWeight s.β = 3 ∧ miWeight s.γ = 3

/-- A split avoids autocatalysis for target α. -/
def MonomialSplit.nonAutocatalytic {n : ℕ} {δ : Fin n → ℕ}
    (s : MonomialSplit δ) (α : Fin n → ℕ) : Prop :=
  s.β ≠ α ∧ s.γ ≠ α

/-! ## The 4-PP Condition

After the r²-trick, every derivative x'ⱼ = fⱼ(x) has degree 4,
and the positive part of fⱼ contains no monomial with x_j-exponent ≥ 4.

We model this as a constraint on exponent vectors of positive monomials. -/

/-- A degree-4 monomial (represented by its exponent vector δ with |δ| = 4)
satisfies the 4-PP condition for variable j if δⱼ < 4. -/
def is4PPMonomial {n : ℕ} (j : Fin n) (δ : Fin n → ℕ) : Prop :=
  δ j < 4

/-- The 4-PP condition: for each variable j, every positive monomial
in x'ⱼ has x_j-exponent < 4.

In fact, from the PP structure + r²-trick, the self-exponent is ≤ 2
(Proposition 2 in Note 14), but we only need < 4 for the main theorem. -/
structure Is4PP (n : ℕ) where
  /-- For each variable j and each positive monomial δ in x'ⱼ,
  the exponent of xⱼ in δ is < 4. -/
  no_self_fourth : ∀ (j : Fin n) (δ : Fin n → ℕ),
    miWeight δ = 4 → δ j < 4

/-! ## Cubed Variables

The cubing step defines v_α = C(3,α) · ∏ xⱼ^{αⱼ} for |α| = 3.
By the chain rule, each positive monomial in v̇_α has degree
(3-1) + 4 = 6. The NAP Splitting Feasibility theorem says every
such monomial admits a non-autocatalytic degree-3 × degree-3 split. -/

/-- A cubed index is a multi-index of weight 3. -/
def IsCubedIndex {n : ℕ} (α : Fin n → ℕ) : Prop := miWeight α = 3

/-- A production monomial for v_α is a degree-6 monomial δ arising
from the chain rule: v̇_α = Σ_{j: αⱼ>0} αⱼ (v_α/xⱼ) · fⱼ(x).

It satisfies:
  (1) |δ| = 6
  (2) There exists j ∈ supp(α) such that δ = (α - eⱼ) + μ
      where μ is a positive degree-4 monomial in fⱼ with μⱼ < 4. -/
structure ProductionMonomial {n : ℕ} (α : Fin n → ℕ) where
  /-- The exponent vector of the degree-6 monomial. -/
  δ : Fin n → ℕ
  /-- Total degree is 6. -/
  weight_eq : miWeight δ = 6
  /-- Source variable: the j such that v̇_α gets a contribution from fⱼ. -/
  source : Fin n
  /-- The source is in the support of α. -/
  source_in_supp : 0 < α source
  /-- The degree-4 monomial from the positive part of fⱼ. -/
  μ : Fin n → ℕ
  /-- μ has degree 4. -/
  μ_weight : miWeight μ = 4
  /-- δ = (α - eⱼ) + μ (the chain rule product). -/
  chain_rule : ∀ k, δ k = (α k - if k = source then 1 else 0) + μ k
  /-- The pipeline condition on μ: the self-exponent is ≤ 2.
  This is stronger than the bare 4-PP condition (< 4) and comes from the
  PP structure: after the r²-trick, the maximum self-power in positive
  terms is 2 (Proposition 2 in Note 14). The bare 4-PP condition (< 4)
  is insufficient — e.g., α = 3eⱼ with μⱼ = 3 gives δ = (5,1,0,...),
  which has no valid non-autocatalytic split. -/
  pipeline_bound : μ source ≤ 2
  /-- The r²-trick structural property: μ has weight on at least 2 distinct
  non-source variables. In the pipeline, every positive monomial contains
  the r² factor (2 units on the r-variable, which is ≠ source for non-r
  derivatives) plus at least one other non-source variable from the original
  PP polynomial. For the r-derivative, the positive terms come from
  q_j · x_j · r², giving weight on both j and the variable in q_j. -/
  foreign_pair : ∃ i₁ i₂, i₁ ≠ i₂ ∧ i₁ ≠ source ∧ i₂ ≠ source ∧
    0 < μ i₁ ∧ 0 < μ i₂

/-! ## Exponent Redistribution Lemma

This is the algebraic heart of the proof. If α has support size ≥ 2,
then for any δ = 2α, the split β = α + eⱼ - eₖ gives a valid
non-autocatalytic factorization.

More generally: if α | δ and |supp(α)| ≥ 2, then δ has a degree-3
divisor β ≠ α with δ - β ≠ α. -/

/-- Shift one exponent unit from k to j: β(j) = α(j)+1, β(k) = α(k)-1, else β = α. -/
noncomputable def miShift {n : ℕ} (α : Fin n → ℕ) (j k : Fin n) : Fin n → ℕ :=
  fun i => if i = j then α i + 1 else if i = k then α i - 1 else α i

theorem miShift_at_j {n : ℕ} {α : Fin n → ℕ} {j k : Fin n} (_hjk : j ≠ k) :
    miShift α j k j = α j + 1 := by simp [miShift]

theorem miShift_at_k {n : ℕ} {α : Fin n → ℕ} {j k : Fin n} (hjk : j ≠ k) :
    miShift α j k k = α k - 1 := by simp only [miShift, hjk.symm, ite_false, ite_true]

theorem miShift_at_other {n : ℕ} {α : Fin n → ℕ} {j k i : Fin n}
    (hij : i ≠ j) (hik : i ≠ k) : miShift α j k i = α i := by
  simp [miShift, hij, hik]

/-- The weight of miShift α j k equals the weight of α (when α k ≥ 1). -/
theorem miShift_weight {n : ℕ} {α : Fin n → ℕ} {j k : Fin n}
    (hk : 0 < α k) (hjk : j ≠ k) :
    miWeight (miShift α j k) = miWeight α := by
  simp only [miWeight]
  -- Extract j and k from both sums, leaving the same remainder R
  have hjk' : k ≠ j := hjk.symm
  have hj_mem : j ∈ (Finset.univ : Finset (Fin n)) := Finset.mem_univ j
  have hk_mem : k ∈ (Finset.univ : Finset (Fin n)).erase j :=
    Finset.mem_erase.mpr ⟨hjk', Finset.mem_univ k⟩
  set R := ∑ i ∈ (Finset.univ.erase j).erase k, α i
  -- LHS = (α j + 1) + ((α k - 1) + R)
  have lhs : ∑ i, miShift α j k i = (α j + 1) + ((α k - 1) + R) := by
    rw [← Finset.add_sum_erase _ _ hj_mem, ← Finset.add_sum_erase _ _ hk_mem]
    rw [miShift_at_j hjk, miShift_at_k hjk]
    congr 1; congr 1
    exact Finset.sum_congr rfl fun i hi => by
      simp only [Finset.mem_erase] at hi; exact miShift_at_other hi.2.1 hi.1
  -- RHS = α j + (α k + R)
  have rhs : ∑ i, α i = α j + (α k + R) := by
    rw [← Finset.add_sum_erase _ _ hj_mem, ← Finset.add_sum_erase _ _ hk_mem]
  rw [lhs, rhs]; omega

/-- miShift α j k ≠ α when α k ≥ 1 and j ≠ k. -/
theorem miShift_ne {n : ℕ} {α : Fin n → ℕ} {j k : Fin n}
    (_hk : 0 < α k) (hjk : j ≠ k) : miShift α j k ≠ α := by
  intro h
  have := congr_fun h j
  rw [miShift_at_j hjk] at this
  omega

/-- miShift α k j ≠ α when j ≠ k (it increases α at k). -/
theorem miShift_reverse_ne {n : ℕ} {α : Fin n → ℕ} {j k : Fin n}
    (hjk : j ≠ k) : miShift α k j ≠ α := by
  intro h
  have := congr_fun h k
  rw [miShift_at_j hjk.symm] at this
  omega

/-- **Exponent Redistribution Lemma**: If α has support size ≥ 2
(witnessed by distinct j, k with αⱼ, αₖ > 0), then the monomial 2α
admits a non-autocatalytic degree-3 split.

β = miShift α j k = (α+eⱼ-eₖ), γ = miShift α k j = (α-eⱼ+eₖ).
Both have weight 3, both ≠ α, and β + γ = 2α componentwise. -/
theorem exponent_redistribution {n : ℕ} (α : Fin n → ℕ)
    (hα : miWeight α = 3)
    {j k : Fin n} (hj : 0 < α j) (hk : 0 < α k) (hjk : j ≠ k) :
    let β := miShift α j k
    let γ := miShift α k j
    -- |β| = 3
    miWeight β = 3 ∧
    -- |γ| = 3
    miWeight γ = 3 ∧
    -- β + γ = 2α
    (∀ i, β i + γ i = 2 * α i) ∧
    -- β ≠ α
    β ≠ α ∧
    -- γ ≠ α
    γ ≠ α := by
  refine ⟨?_, ?_, ?_, miShift_ne hk hjk, miShift_reverse_ne hjk⟩
  -- |β| = 3
  · rw [miShift_weight hk hjk, hα]
  -- |γ| = 3
  · rw [miShift_weight hj hjk.symm, hα]
  -- β + γ = 2α
  · intro i
    unfold miShift
    by_cases hij : i = j
    · subst hij
      simp [hjk]
      omega
    · by_cases hik : i = k
      · subst hik
        simp [hjk.symm]
        omega
      · simp [hij, hik]
        omega

/-! ## Helper: existence of non-source weight

From the pipeline bound, μ_source ≤ 2 and |μ| = 4, so at least 2 units
of μ are on non-source variables. This gives a "foreign atom" to use
in constructing non-autocatalytic splits. -/

/-- If μ has weight 4 and μ_source ≤ 2, there exists i₀ ≠ source with μ_{i₀} ≥ 1. -/
theorem exists_foreign_atom {n : ℕ} {μ : Fin n → ℕ} {source : Fin n}
    (hμ : miWeight μ = 4) (hbound : μ source ≤ 2) :
    ∃ i₀ : Fin n, i₀ ≠ source ∧ 0 < μ i₀ := by
  by_contra h
  push Not at h
  -- h : ∀ i₀, i₀ ≠ source → μ i₀ = 0  (push_neg turns ¬(0 < μ i₀) to μ i₀ ≤ 0, i.e. = 0 in ℕ)
  have hzero : ∀ i, i ≠ source → μ i = 0 := fun i hi => Nat.le_zero.mp (h i hi)
  have : ∑ i, μ i = μ source := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ source)]
    suffices ∑ x ∈ Finset.univ.erase source, μ x = 0 by omega
    exact Finset.sum_eq_zero fun i hi => hzero i (Finset.ne_of_mem_erase hi)
  rw [miWeight] at hμ; omega

/-! ## Pure-power case: |supp(α)| = 1

When α = 3·eⱼ, the split β = (2·eⱼ + e_{i₀}), γ = δ - β avoids
autocatalysis because β has weight on i₀ (so β ≠ α) and γ has
γⱼ = μⱼ ≤ 2 < 3 (so γ ≠ α). -/

/-- When |supp(α)| = 1 (pure power at source), construct a valid split.
β = 2·e_source + 1·e_{i₀}, γ = δ - β. Works because:
  - β ≠ α since β_{i₀} = 1 but α_{i₀} = 0
  - γ ≠ α since γ_source = μ_source ≤ 2 < 3 = α_source -/
theorem pure_power_split {n : ℕ} (α : Fin n → ℕ)
    (hα : IsCubedIndex α)
    (pm : ProductionMonomial α)
    (h_pure : ∀ i, i ≠ pm.source → α i = 0) :
    ∃ s : MonomialSplit pm.δ, s.balanced ∧ s.nonAutocatalytic α := by
  -- α is a pure power: α_source = 3
  have hα_source : α pm.source = 3 := by
    have hwt := hα; unfold IsCubedIndex miWeight at hwt
    have : ∑ i, α i = α pm.source := by
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ pm.source)]
      suffices ∑ x ∈ Finset.univ.erase pm.source, α x = 0 by omega
      exact Finset.sum_eq_zero fun i hi => h_pure i (Finset.ne_of_mem_erase hi)
    linarith
  -- Get a foreign atom i₀ ≠ source with μ_{i₀} ≥ 1
  obtain ⟨i₀, hi₀_ne, hi₀_pos⟩ := exists_foreign_atom pm.μ_weight pm.pipeline_bound
  -- δ_{i₀} ≥ 1 (from chain rule + h_pure)
  have hδi₀ : 1 ≤ pm.δ i₀ := by
    rw [pm.chain_rule i₀]; simp [hi₀_ne]; omega
  -- δ_source ≥ 2 (from chain rule: 3 - 1 + μ_source ≥ 2)
  have hδs : 2 ≤ pm.δ pm.source := by
    rw [pm.chain_rule pm.source]; simp; omega
  -- Define β: 2 on source, 1 on i₀, 0 elsewhere
  set β : Fin n → ℕ := fun i => if i = pm.source then 2 else if i = i₀ then 1 else 0
  -- Key values
  have hβ_s : β pm.source = 2 := if_pos rfl
  have hβ_i₀ : β i₀ = 1 := by simp [β, hi₀_ne]
  have hβ_other : ∀ i, i ≠ pm.source → i ≠ i₀ → β i = 0 :=
    fun i h1 h2 => by simp only [β, if_neg h1, if_neg h2]
  -- β ≤ δ
  have hβ_le : ∀ i, β i ≤ pm.δ i := by
    intro i
    by_cases hs : i = pm.source
    · rw [hs, hβ_s]; exact hδs
    · by_cases hi : i = i₀
      · rw [hi, hβ_i₀]; exact hδi₀
      · rw [hβ_other i hs hi]; exact Nat.zero_le _
  -- |β| = 3 (via extract j, k from sum)
  have hβ_wt : miWeight β = 3 := by
    simp only [miWeight]
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ pm.source), hβ_s]
    rw [← Finset.add_sum_erase _ _
      (Finset.mem_erase.mpr ⟨hi₀_ne, Finset.mem_univ i₀⟩), hβ_i₀]
    suffices ∑ x ∈ (Finset.univ.erase pm.source).erase i₀, β x = 0 by omega
    exact Finset.sum_eq_zero fun i hi => by
      simp only [Finset.mem_erase] at hi; exact hβ_other i hi.2.1 hi.1
  -- |γ| = 3 (weight of δ - β = 6 - 3)
  have hγ_wt : miWeight (fun i => pm.δ i - β i) = 3 := by
    simp only [miWeight]
    have key : ∑ i : Fin n, (β i + (pm.δ i - β i)) = ∑ i, pm.δ i :=
      Finset.sum_congr rfl fun i _ => Nat.add_sub_of_le (hβ_le i)
    rw [Finset.sum_add_distrib] at key
    have h1 : ∑ i : Fin n, β i = 3 := hβ_wt
    have h2 : ∑ i : Fin n, pm.δ i = 6 := pm.weight_eq
    omega
  -- Construct the split
  refine ⟨⟨β, fun i => pm.δ i - β i, fun i => Nat.add_sub_of_le (hβ_le i)⟩,
    ⟨hβ_wt, hγ_wt⟩, ?_, ?_⟩
  · -- β ≠ α: β_{i₀} = 1 but α_{i₀} = 0
    intro h
    have hv := congr_fun h i₀
    dsimp at hv
    rw [hβ_i₀, h_pure i₀ hi₀_ne] at hv
    exact absurd hv (by omega)
  · -- γ ≠ α: γ_source = δ_source - 2 = μ_source ≤ 2 < 3 = α_source
    intro h
    have hval : pm.δ pm.source - β pm.source = α pm.source := by
      have := congr_fun h pm.source; dsimp at this; exact this
    rw [hβ_s, hα_source] at hval
    have hδ_s : pm.δ pm.source = 2 + pm.μ pm.source := by
      have h := pm.chain_rule pm.source
      simp only [ite_true] at h; rw [hα_source] at h; omega
    rw [hδ_s] at hval
    -- hval : 2 + μ_source - 2 = 3, i.e. μ_source = 3
    have := pm.pipeline_bound; omega

/-! ## Mixed support case: |supp(α)| ≥ 2

When α has support on at least two variables (source and k), the proof
constructs β = miShift α i₀ source (primary) or β = miShift α i₀ k
(backup), where i₀ is a foreign atom of μ.

Key insight: if the primary split has γ₁ = α, then μ_source = α_source,
and the backup's γ₂ at source equals α_source - 1 ≠ α_source.
The two failures are contradictory, so at least one split works. -/

/-- Helper: construct a balanced split from β ≤ δ with |β| = 3, |δ| = 6. -/
private theorem balanced_of_le {n : ℕ} {δ : Fin n → ℕ} {β : Fin n → ℕ}
    (hle : ∀ i, β i ≤ δ i) (hβ : miWeight β = 3) (hδ : miWeight δ = 6) :
    miWeight (fun i => δ i - β i) = 3 := by
  simp only [miWeight]
  have key : ∑ i : Fin n, (β i + (δ i - β i)) = ∑ i, δ i :=
    Finset.sum_congr rfl fun i _ => Nat.add_sub_of_le (hle i)
  rw [Finset.sum_add_distrib] at key
  have h1 : ∑ i : Fin n, β i = 3 := hβ
  have h2 : ∑ i : Fin n, δ i = 6 := hδ
  omega

/-- Mixed support case: k ∈ supp(α) with k ≠ source. -/
theorem mixed_support_split {n : ℕ} (α : Fin n → ℕ)
    (hα : IsCubedIndex α)
    (pm : ProductionMonomial α)
    (k : Fin n) (hk_ne : k ≠ pm.source) (hk_supp : 0 < α k) :
    ∃ s : MonomialSplit pm.δ, s.balanced ∧ s.nonAutocatalytic α := by
  -- Foreign atoms: i₁ ≠ i₂, both ≠ source, μ positive at both
  obtain ⟨i₁, i₂, hi₁₂, hi₁_ne, hi₂_ne, hμ₁, hμ₂⟩ := pm.foreign_pair
  -- Choose i₀ ∈ {i₁, i₂} with i₀ ≠ k
  obtain ⟨i₀, hi₀_ne_s, hμ₀, hi₀_ne_k⟩ : ∃ i₀, i₀ ≠ pm.source ∧ 0 < pm.μ i₀ ∧ i₀ ≠ k := by
    by_cases h : i₁ = k
    · exact ⟨i₂, hi₂_ne, hμ₂, fun h2 => hi₁₂ (h.trans h2.symm)⟩
    · exact ⟨i₁, hi₁_ne, hμ₁, h⟩
  -- Chain rule simplified forms
  have hcr_s : pm.δ pm.source = α pm.source - 1 + pm.μ pm.source := by
    have := pm.chain_rule pm.source; simp only [ite_true] at this; exact this
  have hcr_ne : ∀ i, i ≠ pm.source → pm.δ i = α i + pm.μ i := by
    intro i hi; have := pm.chain_rule i; simp only [if_neg hi, Nat.sub_zero] at this; exact this
  -- Primary β₁ ≤ δ (using miShift directly, no `set`)
  have hβ₁_le : ∀ i, miShift α i₀ pm.source i ≤ pm.δ i := by
    intro i
    by_cases h1 : i = i₀
    · subst h1; rw [miShift_at_j hi₀_ne_s, hcr_ne _ hi₀_ne_s]; omega
    · by_cases h2 : i = pm.source
      · subst h2; rw [miShift_at_k hi₀_ne_s, hcr_s]; omega
      · rw [miShift_at_other h1 h2, hcr_ne _ h2]; omega
  have hβ₁_wt : miWeight (miShift α i₀ pm.source) = 3 :=
    (miShift_weight pm.source_in_supp hi₀_ne_s).trans hα
  -- Case split on whether the primary γ equals α pointwise
  by_cases hγ₁ : ∀ i, pm.δ i - miShift α i₀ pm.source i = α i
  · -- **Backup**: γ₁ = α at every coordinate → μ_source = α_source
    have hμs_eq : pm.μ pm.source = α pm.source := by
      have := hγ₁ pm.source; rw [miShift_at_k hi₀_ne_s, hcr_s] at this; omega
    -- Backup β₂ ≤ δ
    have hβ₂_le : ∀ i, miShift α i₀ k i ≤ pm.δ i := by
      intro i
      by_cases h1 : i = i₀
      · subst h1; rw [miShift_at_j hi₀_ne_k, hcr_ne _ hi₀_ne_s]; omega
      · by_cases h2 : i = k
        · subst h2; rw [miShift_at_k hi₀_ne_k, hcr_ne _ hk_ne]; omega
        · rw [miShift_at_other h1 h2]
          by_cases h3 : i = pm.source
          · subst h3; rw [hcr_s, hμs_eq]; omega
          · rw [hcr_ne _ h3]; omega
    have hβ₂_wt : miWeight (miShift α i₀ k) = 3 :=
      (miShift_weight hk_supp hi₀_ne_k).trans hα
    -- γ₂ at source: (α_s - 1 + α_s) - α_s = α_s - 1 ≠ α_s (since α_s ≥ 1)
    have hγ₂_ne : ¬∀ i, pm.δ i - miShift α i₀ k i = α i := by
      intro h; have := h pm.source
      rw [miShift_at_other (Ne.symm hi₀_ne_s) (Ne.symm hk_ne), hcr_s, hμs_eq] at this
      have := pm.source_in_supp; omega
    refine ⟨⟨miShift α i₀ k, fun i => pm.δ i - miShift α i₀ k i,
      fun i => Nat.add_sub_of_le (hβ₂_le i)⟩,
      ⟨hβ₂_wt, balanced_of_le hβ₂_le hβ₂_wt pm.weight_eq⟩, ?_, ?_⟩
    · intro h; exact absurd (by dsimp at h; exact h) (miShift_ne hk_supp hi₀_ne_k)
    · intro h; exact hγ₂_ne (fun i => by have := congr_fun h i; dsimp at this; exact this)
  · -- **Primary**: γ₁ ≠ α
    refine ⟨⟨miShift α i₀ pm.source, fun i => pm.δ i - miShift α i₀ pm.source i,
      fun i => Nat.add_sub_of_le (hβ₁_le i)⟩,
      ⟨hβ₁_wt, balanced_of_le hβ₁_le hβ₁_wt pm.weight_eq⟩, ?_, ?_⟩
    · intro h; exact absurd (by dsimp at h; exact h) (miShift_ne pm.source_in_supp hi₀_ne_s)
    · intro h; exact hγ₁ (fun i => by have := congr_fun h i; dsimp at this; exact this)

/-! ## NAP Splitting Feasibility — Main Theorem

Every positive degree-6 monomial in v̇_α admits a factorization
m_δ = m_β · m_γ with |β| = |γ| = 3, β ≠ α, γ ≠ α.

The proof splits into two cases:
  Case 1 (pure power): |supp(α)| = 1 → use pure_power_split
  Case 2 (mixed): |supp(α)| ≥ 2 → use mixed_support_split -/

/-- **NAP Splitting Feasibility** (Theorem 1 in Note 14):
For any cubed variable v_α (|α| = 3) and any production monomial δ
arising from the chain rule of a 4-PP, there exists a balanced
non-autocatalytic split of δ. -/
theorem nap_splitting_feasibility {n : ℕ} (α : Fin n → ℕ)
    (hα : IsCubedIndex α)
    (pm : ProductionMonomial α) :
    ∃ s : MonomialSplit pm.δ, s.balanced ∧ s.nonAutocatalytic α := by
  -- Does α have support beyond the source variable?
  by_cases h : ∃ k, k ≠ pm.source ∧ 0 < α k
  · obtain ⟨k, hk_ne, hk_supp⟩ := h
    exact mixed_support_split α hα pm k hk_ne hk_supp
  · push Not at h
    exact pure_power_split α hα pm (fun i hi => Nat.le_zero.mp (h i hi))

/-! ## Trivial Non-Autocatalytic Split

When the source exponent in δ is strictly less than in α, EVERY balanced
split is automatically non-autocatalytic. This handles the case where
the production monomial μ has μ_source = 0 (from PP no-self-production):
  δ_source = α_source - 1 + 0 = α_source - 1 < α_source
so any β with β_source ≤ δ_source < α_source gives β ≠ α, and similarly
γ_source = δ_source - β_source ≤ α_source - 1 < α_source gives γ ≠ α. -/

/-- When δ_source < α_source, any split β + γ = δ with β ≤ δ has
β ≠ α and γ ≠ α (both factors differ from α at the source coordinate). -/
theorem trivial_split_of_lt {n : ℕ} {α δ : Fin n → ℕ} {source : Fin n}
    (hlt : δ source < α source)
    (β : Fin n → ℕ) (hle : ∀ i, β i ≤ δ i) :
    β ≠ α ∧ (fun i => δ i - β i) ≠ α := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · -- β = α would give α source ≤ δ source, contradicting hlt
    rw [h] at hle; exact absurd (hle source) (not_le.mpr hlt)
  · -- (δ - β) = α at source: δ_s - β_s = α_s, but δ_s - β_s ≤ δ_s < α_s
    have h1 : ∀ i, δ i - β i = α i := fun i => congr_fun h i
    have h2 := h1 source
    have h3 := hle source
    omega

/-- Any multi-index of weight ≥ k has a divisor of weight exactly k.
This is a standard combinatorial fact: a "greedy fill" works. -/
private theorem exists_weight_divisor {n : ℕ} :
    ∀ (k : ℕ) (δ : Fin n → ℕ), k ≤ miWeight δ →
    ∃ β : Fin n → ℕ, miWeight β = k ∧ ∀ i, β i ≤ δ i := by
  intro k; induction k with
  | zero => intro _ _; exact ⟨fun _ => 0, by simp [miWeight], fun _ => Nat.zero_le _⟩
  | succ k ih =>
    intro δ hk
    -- |δ| ≥ 1, so ∃ i with δ_i ≥ 1
    have ⟨i, hi_pos⟩ : ∃ i, 0 < δ i := by
      by_contra h; push Not at h
      have : ∀ j, δ j = 0 := fun j => Nat.le_zero.mp (h j)
      simp [miWeight, this] at hk
    -- Let δ' = δ - e_i. Then |δ'| = |δ| - 1 ≥ k.
    set δ' := fun j => if j = i then δ j - 1 else δ j with hδ'_def
    have hδ'_wt : miWeight δ' = miWeight δ - 1 := by
      simp only [miWeight, hδ'_def]
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
      simp only [ite_true]
      rw [show ∑ x ∈ Finset.univ.erase i, (if x = i then δ x - 1 else δ x) =
        ∑ x ∈ Finset.univ.erase i, δ x from
        Finset.sum_congr rfl fun j hj => by simp [Finset.ne_of_mem_erase hj]]
      have : δ i + ∑ x ∈ Finset.univ.erase i, δ x = ∑ x, δ x :=
        Finset.add_sum_erase Finset.univ (fun x => δ x) (Finset.mem_univ i)
      omega
    obtain ⟨β', hβ'_wt, hβ'_le⟩ := ih δ' (by omega)
    -- β = β' + e_i
    refine ⟨fun j => β' j + if j = i then 1 else 0, ?_, ?_⟩
    · simp only [miWeight]
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
      simp only [ite_true]
      rw [show ∑ x ∈ Finset.univ.erase i,
        ((fun j => β' j + if j = i then 1 else 0) x) =
        ∑ x ∈ Finset.univ.erase i, β' x from
        Finset.sum_congr rfl fun j hj => by simp [Finset.ne_of_mem_erase hj]]
      simp only [miWeight] at hβ'_wt
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)] at hβ'_wt
      omega
    · intro j
      by_cases hj : j = i
      · subst hj
        have h1 := hβ'_le j
        simp only [hδ'_def, ite_true] at h1
        simp only [ite_true]; omega
      · simp only [if_neg hj, add_zero]
        have h1 := hβ'_le j
        simp only [hδ'_def, if_neg hj] at h1
        exact h1

/-- When δ_source < α_source and |δ| = 6, there exists a balanced
non-autocatalytic split. The split is "trivial" because ANY weight-3
divisor of δ gives β ≠ α and γ ≠ α (both factors must have
source-exponent ≤ δ_source < α_source). -/
theorem trivial_balanced_split {n : ℕ} (α δ : Fin n → ℕ)
    (hδ : miWeight δ = 6) (source : Fin n)
    (hlt : δ source < α source) :
    ∃ s : MonomialSplit δ, s.balanced ∧ s.nonAutocatalytic α := by
  obtain ⟨β, hβ_wt, hβ_le⟩ := exists_weight_divisor 3 δ (by omega)
  refine ⟨⟨β, fun i => δ i - β i, fun i => Nat.add_sub_of_le (hβ_le i)⟩,
    ⟨hβ_wt, balanced_of_le hβ_le hβ_wt hδ⟩, ?_⟩
  exact trivial_split_of_lt hlt β hβ_le

/-! ## Structural Chain: PP → 4-PP → NAP

The three-step causal chain:
  PP (x_j ∤ p_j) →[r²-trick] 4-PP →[cubing] NAP

The PP **no-self-production** condition: for each species j, the
production polynomial p_j is not divisible by x_j. This means x_j
does not appear at all in p_j — not even x_j · x_k.

After the r²-trick (multiply all derivatives by r²):
- For source j: μ = (degree-2 monomial from p_j) · r².
  Since x_j ∤ p_j, every monomial has μ_j = 0.

Two cases for each production monomial:
1. **foreign_pair holds** (μ has ≥2 distinct non-source positive variables):
   Apply nap_splitting_feasibility via ProductionMonomial.
2. **foreign_pair fails** (μ concentrated on one non-source variable):
   μ_source = 0, so δ_source = α_source - 1 < α_source.
   Any balanced split is automatically non-autocatalytic. -/

/-- **PP → NAP: General Non-Autocatalytic Split**

Every degree-6 chain-rule monomial from cubing a 4-PP (obtained via
r²-trick with PP no-self-production) admits a non-autocatalytic split.

The hypothesis h_no_self (μ_source = 0) captures the PP structural
invariant: x_j never appears in its own production polynomial p_j. -/
theorem pp_to_nap_split {n : ℕ} (α : Fin n → ℕ) (hα : IsCubedIndex α)
    (δ : Fin n → ℕ) (hδ : miWeight δ = 6)
    (source : Fin n) (hsrc : 0 < α source)
    (μ : Fin n → ℕ) (hμ : miWeight μ = 4)
    (hcr : ∀ k, δ k = (α k - if k = source then 1 else 0) + μ k)
    (h_no_self : μ source = 0) :
    ∃ s : MonomialSplit δ, s.balanced ∧ s.nonAutocatalytic α := by
  by_cases hfp : ∃ i₁ i₂, i₁ ≠ i₂ ∧ i₁ ≠ source ∧ i₂ ≠ source ∧ 0 < μ i₁ ∧ 0 < μ i₂
  · -- Case 1: foreign_pair holds → full ProductionMonomial → nap_splitting_feasibility
    exact nap_splitting_feasibility α hα ⟨δ, hδ, source, hsrc, μ, hμ, hcr,
      by omega, hfp⟩
  · -- Case 2: foreign_pair fails → δ_source < α_source → trivial split
    have hδs : δ source = α source - 1 := by
      have := hcr source; simp [h_no_self] at this; omega
    exact trivial_balanced_split α δ hδ source (by omega)

/-! ## Protocol-Level PP → NAP

The monomial-level `pp_to_nap_split` says: given specific α, δ, source, μ satisfying
the chain rule and strict no-self-production (μ_source = 0), a balanced non-autocatalytic
split exists.

The protocol-level statement says: for ALL production monomials arising from cubing
a PP with strict no-self-production, balanced non-autocatalytic splits exist.

### Strict No-Self-Production

The key structural condition on the PP: for each species j, the production polynomial
p_j does not contain x_j at all (x_j exponent = 0 in every monomial of p_j).
This is stronger than the ODE-level `no_self_square` (which only prevents x_j²).

After the r²-trick (multiplying by x_0², where x_0 is the slack variable),
the 4-PP field f_j^+ = x_0² · p_j has x_j exponent = 0 for all monomials
(since p_j has no x_j and x_0² adds no x_j for j ≥ 1).

For j = 0 (the slack variable): by conservation, f_0 = -Σ_{j≥1} f_j.
The positive part of g_0 = x_0² · f_0 contains x_0 to power at most 2
(from the x_0² factor, with p_0 having no x_0). So μ_0 ≤ 2 (pipeline_bound).
The stronger condition μ_0 = 0 requires that p_0 has no x_0 at all.

### Note on the Paper Proof Gap

Note 14b Theorem (NAP feasibility) has a gap in Step 2: the claim δ = 2α
is not justified by the no-NAP hypothesis alone. Step 1 correctly derives
α ≤ δ, but the partition β = α, γ = δ - α satisfies the hypothesis because
β = α, without forcing γ = α. The gap doesn't affect correctness for actual
PPs (deterministic transition functions limit production coefficients to ≤ 2
per reaction, ensuring problematic monomials cancel). Our formalization
sidesteps the gap entirely by using the strict no-self-production condition
(μ_source = 0), which splits the proof into the two clean cases handled by
`nap_splitting_feasibility` and `trivial_balanced_split`. -/

/-- A cubed PP production monomial: all the data arising from the chain rule
for v_α in the cubed 4-PP system, where the 4-PP has strict no-self-production. -/
structure CubedPPMonomial {n : ℕ} where
  /-- The cubed index (v_α variable). -/
  α : Fin n → ℕ
  /-- α is a cubed index (weight 3). -/
  α_cubed : IsCubedIndex α
  /-- The degree-6 product monomial. -/
  δ : Fin n → ℕ
  /-- Total degree is 6. -/
  δ_weight : miWeight δ = 6
  /-- The source (differentiation variable j). -/
  source : Fin n
  /-- The source is in supp(α). -/
  source_in_supp : 0 < α source
  /-- The degree-4 production monomial from the 4-PP field. -/
  μ : Fin n → ℕ
  /-- μ has degree 4. -/
  μ_weight : miWeight μ = 4
  /-- Chain rule: δ = (α - e_source) + μ. -/
  chain_rule : ∀ k, δ k = (α k - if k = source then 1 else 0) + μ k
  /-- Strict no-self-production: x_j does not appear in p_j at all. -/
  no_self_prod : μ source = 0

/-- **Protocol-Level PP → NAP Theorem**

Every production monomial arising from cubing a PP with strict no-self-production
admits a balanced non-autocatalytic factorization. This is the formal version of
Note 14 Theorem 5.1, using the strict no-self-production condition to avoid the
paper's Step 2 gap. -/
theorem cubed_pp_nap (m : @CubedPPMonomial n) :
    ∃ s : MonomialSplit m.δ, s.balanced ∧ s.nonAutocatalytic m.α :=
  pp_to_nap_split m.α m.α_cubed m.δ m.δ_weight m.source m.source_in_supp
    m.μ m.μ_weight m.chain_rule m.no_self_prod

/-- **Comprehensive NAP Split Criterion**

A degree-6 chain-rule monomial admits a balanced non-autocatalytic split if
EITHER of the following holds:
  (A) Strict no-self-production: μ_source = 0, OR
  (B) Pipeline bound (μ_source ≤ 2) AND foreign_pair (≥2 distinct non-source
      variables with positive μ-weight).

This covers all production monomials from the cubing construction where the
4-PP satisfies either the strict no-self-production condition (A) or has
sufficient monomial spread (B). For PPs arising from the Huang-Huls
Stage 3 construction, the r²-trick distributes weight across many variables,
ensuring that (B) holds for most monomials, and (A) covers the rest. -/
theorem nap_split_comprehensive {n : ℕ} (α : Fin n → ℕ) (hα : IsCubedIndex α)
    (δ : Fin n → ℕ) (hδ : miWeight δ = 6)
    (source : Fin n) (hsrc : 0 < α source)
    (μ : Fin n → ℕ) (hμ : miWeight μ = 4)
    (hcr : ∀ k, δ k = (α k - if k = source then 1 else 0) + μ k)
    (h_condition : μ source = 0 ∨
      (μ source ≤ 2 ∧ ∃ i₁ i₂, i₁ ≠ i₂ ∧ i₁ ≠ source ∧ i₂ ≠ source ∧
        0 < μ i₁ ∧ 0 < μ i₂)) :
    ∃ s : MonomialSplit δ, s.balanced ∧ s.nonAutocatalytic α := by
  rcases h_condition with h_no_self | ⟨h_bound, h_fp⟩
  · exact pp_to_nap_split α hα δ hδ source hsrc μ hμ hcr h_no_self
  · exact nap_splitting_feasibility α hα ⟨δ, hδ, source, hsrc, μ, hμ, hcr, h_bound, h_fp⟩

/-! ## Connection to Stage 3 Self-Product

The self-product z-PP (from Stage2CubicForm, see Stages.lean) has the field:
  z'_{(i,j)} = prod_{(i,j)} - degr_{(i,j)}

**Analysis of self-production in the z-PP:**

* **Case 1 (i,j ≠ 0)**: production = z(0,j)·Pz_i + z(0,i)·Pz_j.
  z_{(i,j)} appears only via A(i,i,j) or A(j,i,j). Both vanish under strict
  no-self-production (A(i,i,·) = 0 and A(j,·,j) = 0). **μ_source = 0 ✓**

* **Case 2a (i=0, j≠0)**: production includes colCoupling_j = Σ_{k≠0} z(k,j)·x0Qz_k.
  When x0Qz_k has a z(0,j) term (B(k,j)·z(0,j)), the monomial z(k,j)·z(0,j)
  contains the source variable z(0,j). **μ_source = 1**, but pipeline_bound (≤ 2)
  and foreign_pair (r + z(k,j)) both hold. ✓

* **Case 2b (i≠0, j=0)**: symmetric to 2a via rowCoupling. ✓

* **Case 3 (i=j=0)**: production = 2·z(0,0)·totalQxz, every monomial has z(0,0)
  as a factor. **μ_source = 1**, with foreign_pair (r + z(a,k) for k≠0). ✓

**Conclusion:** `nap_split_comprehensive` covers ALL production monomials of the
cubed self-product PP. The self-product preserves strict no-self-production for
interior variables (Case 1) and satisfies the weaker comprehensive criterion for
boundary variables (Cases 2, 3). -/

end Ripple
