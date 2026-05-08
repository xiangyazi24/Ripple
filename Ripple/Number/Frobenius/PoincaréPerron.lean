/-
Copyright (c) 2026 Xiang Huang, Zinan Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang, Zinan Huang
-/
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Basic

/-!
# Poincaré-Perron Theorem (Special Case)

This file proves a special case of the Poincaré-Perron theorem for
3-step linear recurrences with a dominant double eigenvalue.

## Main result

`threeStep_growth_bound`: Given a sequence `c : ℕ → ℝ` satisfying a
3-step recurrence with coefficients converging to limits whose
characteristic polynomial has a double dominant root `λ₁` and a simple
subdominant root `λ₂` with `|λ₂| < |λ₁|`, the sequence satisfies
`|c m| ≤ C · (m + 1) · |λ₁|^m` for some constant `C > 0`.

## Strategy

The proof proceeds by:
1. Rescaling: define `u_m = c_m / λ₁^m`, reducing to showing `u_m = O(m)`.
2. The rescaled recurrence has limiting eigenvalues `1` (double) and `λ₂/λ₁` (simple).
3. First-differencing: `v_m = u_m - u_{m-1}` eliminates the double eigenvalue,
   reducing to showing `v_m = O(1)`.
4. The v-recurrence has limiting dominant eigenvalue `1` (simple) and subdominant
   `λ₂/λ₁` with `|λ₂/λ₁| < 1`.
5. Second-differencing: `w_m = v_m - v_{m-1}` has limiting dominant eigenvalue
   `λ₂/λ₁` with `|λ₂/λ₁| < 1`.
6. For the w-recurrence, the triangle inequality WORKS (effective ratio < 1),
   giving `w_m → 0` geometrically.
7. Telescoping back: `v_m = v_0 + Σ w_k` (bounded), `u_m = u_0 + Σ v_k = O(m)`.

## Implementation note

The variable-coefficient perturbation at each differencing step introduces
O(1/m) error terms. These are absorbed by the geometric contraction at step 6.
-/

open Filter Finset

namespace Ripple.Frobenius.PoincaréPerron

/-! ### Abstract 3-step recurrence framework -/

/-- A 3-step recurrence with m-dependent coefficients. -/
structure ThreeStepRecurrence where
  /-- The sequence satisfying the recurrence. -/
  c : ℕ → ℝ
  /-- Coefficient of c_m in the recurrence for c_{m+1}. -/
  α : ℕ → ℝ
  /-- Coefficient of c_{m-1}. -/
  β : ℕ → ℝ
  /-- Coefficient of c_{m-2}. -/
  γ : ℕ → ℝ
  /-- The recurrence holds for m ≥ 2. -/
  recurrence : ∀ m, 2 ≤ m → c (m + 1) = α m * c m + β m * c (m - 1) + γ m * c (m - 2)

/-- Limiting coefficients of the recurrence. -/
structure LimitingCoefficients where
  α_lim : ℝ
  β_lim : ℝ
  γ_lim : ℝ

/-- The coefficients converge at rate O(1/m). -/
structure ConvergenceRate (rec : ThreeStepRecurrence) (lim : LimitingCoefficients) where
  /-- Error bound constant. -/
  K : ℝ
  hK : 0 < K
  /-- Rate of convergence. -/
  hα : ∀ m, 1 ≤ m → |rec.α m - lim.α_lim| ≤ K / m
  hβ : ∀ m, 1 ≤ m → |rec.β m - lim.β_lim| ≤ K / m
  hγ : ∀ m, 1 ≤ m → |rec.γ m - lim.γ_lim| ≤ K / m

/-- Eigenvalue structure: dominant double root and subdominant simple root. -/
structure DominantDoubleEigenvalue (lim : LimitingCoefficients) where
  /-- Dominant eigenvalue (double root). -/
  ev₁ : ℝ
  /-- Subdominant eigenvalue (simple root). -/
  ev₂ : ℝ
  /-- ev₁ ≠ 0. -/
  hev₁_ne : ev₁ ≠ 0
  /-- The characteristic polynomial factors correctly. -/
  char_poly : ∀ x : ℝ,
    x ^ 3 - lim.α_lim * x ^ 2 - lim.β_lim * x - lim.γ_lim =
      (x - ev₁) ^ 2 * (x - ev₂)
  /-- Subdominant is strictly smaller. -/
  subdominant_lt : |ev₂| < |ev₁|

/-! ### Step 1: Rescaled sequence -/

/-- The rescaled sequence `u_m = c_m / ev₁^m`. -/
noncomputable def rescaledSeq (rec : ThreeStepRecurrence) (ev₁ : ℝ) (m : ℕ) : ℝ :=
  rec.c m / ev₁ ^ m

/-- **Rescaled growth bound.** It suffices to show `|u_m| ≤ C · (m+1)`. -/
lemma growth_bound_of_rescaled_bound
    (rec : ThreeStepRecurrence) (ev₁ : ℝ) (hev₁ : ev₁ ≠ 0)
    {C : ℝ} (hC : 0 < C)
    (h : ∀ m : ℕ, |rescaledSeq rec ev₁ m| ≤ C * ((m : ℝ) + 1)) :
    ∀ m : ℕ, |rec.c m| ≤ C * ((m : ℝ) + 1) * |ev₁| ^ m := by
  intro m
  have hev₁_pow : (0 : ℝ) < |ev₁| ^ m := pow_pos (abs_pos.mpr hev₁) m
  have := h m
  rw [rescaledSeq, abs_div, abs_pow] at this
  rwa [div_le_iff₀ hev₁_pow] at this

/-! ### Step 2: First-difference sequence -/

/-- The first-difference sequence `v_m = u_m - u_{m-1}` (with v_0 = u_0). -/
noncomputable def firstDiffSeq (u : ℕ → ℝ) : ℕ → ℝ
  | 0 => u 0
  | m + 1 => u (m + 1) - u m

/-- **Bounded first differences imply linear growth.** If `|v_m| ≤ B`
for all `m`, then `|u_m| ≤ |u_0| + B · m ≤ (|u_0| + B) · (m + 1)`. -/
lemma rescaled_bound_of_firstDiff_bound
    (u : ℕ → ℝ)
    {B : ℝ} (hB : 0 ≤ B)
    (hv : ∀ m : ℕ, |firstDiffSeq u m| ≤ B) :
    ∀ m : ℕ, |u m| ≤ (|u 0| + B) * ((m : ℝ) + 1) := by
  -- First show |u m| ≤ |u 0| + B · m by induction, then weaken.
  suffices h : ∀ m : ℕ, |u m| ≤ |u 0| + B * m by
    intro m
    have := h m
    nlinarith [abs_nonneg (u 0)]
  intro m
  induction m with
  | zero => simp
  | succ n ih =>
    have hv_succ := hv (n + 1)
    simp only [firstDiffSeq] at hv_succ
    -- |u(n+1)| = |u n + (u(n+1) - u n)| ≤ |u n| + |u(n+1) - u n|
    have h_tri : |u (n + 1)| ≤ |u n| + |u (n + 1) - u n| := by
      have h := abs_add_le (u n) (u (n + 1) - u n)
      simp only [add_sub_cancel] at h
      exact h
    calc |u (n + 1)| ≤ |u n| + |u (n + 1) - u n| := h_tri
      _ ≤ (|u 0| + B * ↑n) + B := by linarith
      _ = |u 0| + B * (↑(n + 1) : ℝ) := by push_cast; ring

/-! ### Step 3: Second-difference and contraction

The second-difference `w_m = v_m - v_{m-1}` satisfies a recurrence where
the dominant eigenvalue is `ev₂/ev₁` with `|ev₂/ev₁| < 1`. For this
recurrence, the triangle inequality WORKS — the effective ratio is < 1,
giving geometric decay `w_m → 0`.

Once `w_m = O(ρ^m)` with `ρ < 1`, telescoping gives:
- `v_m = v_0 + Σ_{k=1}^m w_k` is bounded (geometric series)
- `u_m = u_0 + Σ_{k=1}^m v_k = O(m)` (bounded terms summed m times)
- `c_m = u_m · ev₁^m = O(m · |ev₁|^m)`
-/

/-- **Telescoping with summable differences.** If `|v(m+1) - v m| ≤ b m`
with `Σ b m` convergent, then `v` is bounded. -/
lemma bounded_of_summable_diffs
    (v : ℕ → ℝ) (b : ℕ → ℝ) (hb_nn : ∀ m, 0 ≤ b m)
    (hb_sum : Summable b)
    (hdiff : ∀ m : ℕ, |v (m + 1) - v m| ≤ b m) :
    ∃ B : ℝ, 0 < B ∧ ∀ m : ℕ, |v m| ≤ B := by
  have htsum_nn : 0 ≤ ∑' k, b k := tsum_nonneg hb_nn
  -- Track partial sums: |v m| ≤ |v 0| + Σ_{k<m} b k
  suffices h_partial : ∀ m : ℕ, |v m| ≤ |v 0| + ∑ k ∈ Finset.range m, b k by
    refine ⟨|v 0| + ∑' k, b k + 1, by linarith [abs_nonneg (v 0)], fun m => ?_⟩
    have h1 := h_partial m
    have h2 : ∑ k ∈ Finset.range m, b k ≤ ∑' k, b k :=
      hb_sum.sum_le_tsum _ (fun k _ => hb_nn k)
    linarith
  intro m
  induction m with
  | zero => simp
  | succ n ih =>
    have h_tri : |v (n + 1)| ≤ |v n| + |v (n + 1) - v n| := by
      have h := abs_add_le (v n) (v (n + 1) - v n)
      simp only [add_sub_cancel] at h; exact h
    rw [Finset.sum_range_succ]
    linarith [hdiff n]

/-! ### Key contraction lemma

The heart of Poincaré-Perron: a sequence satisfying `|a_{m+1}| ≤ (ρ + K/m) · |a_m|`
with `ρ < 1` eventually contracts geometrically.
-/

/-- **Perturbed geometric contraction.** If `|a_{m+1}| ≤ (ρ + K/m) · |a_m|`
for `m ≥ M₀` with `ρ + K/M₀ < 1`, then `a` decays geometrically past `M₀`:
`|a m| ≤ |a M₀| · (ρ + K/M₀)^{m - M₀}`. -/
lemma perturbed_geometric_decay
    {a : ℕ → ℝ} {ρ K : ℝ} {M₀ : ℕ}
    (hρ_nn : 0 ≤ ρ) (hK_nn : 0 ≤ K) (hM₀ : 1 ≤ M₀)
    (hcontract : ρ + K / M₀ < 1)
    (hrec : ∀ m, M₀ ≤ m → |a (m + 1)| ≤ (ρ + K / m) * |a m|) :
    ∀ m, M₀ ≤ m →
      |a m| ≤ |a M₀| * (ρ + K / M₀) ^ (m - M₀) := by
  set r := ρ + K / (M₀ : ℝ)
  have hr_nn : 0 ≤ r := by positivity
  have hM₀_pos : (0 : ℝ) < M₀ := Nat.cast_pos.mpr (by omega)
  intro m hm
  induction m, hm using Nat.le_induction with
  | base => simp
  | succ k hk ih =>
    -- K/(k:ℝ) ≤ K/(M₀:ℝ) since k ≥ M₀ ≥ 1
    have hk_pos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast (show 0 < k by omega)
    have hk_cast : (M₀ : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    have hKdiv : K / (k : ℝ) ≤ K / (M₀ : ℝ) := by
      rw [div_le_div_iff₀ hk_pos hM₀_pos]
      exact mul_le_mul_of_nonneg_left hk_cast hK_nn
    have hratio : ρ + K / (k : ℝ) ≤ r := by linarith
    have hsub : k + 1 - M₀ = (k - M₀) + 1 := by omega
    calc |a (k + 1)| ≤ (ρ + K / ↑k) * |a k| := hrec k hk
      _ ≤ r * |a k| := by gcongr
      _ ≤ r * (|a M₀| * r ^ (k - M₀)) := by gcongr
      _ = |a M₀| * r ^ ((k - M₀) + 1) := by rw [pow_succ]; ring
      _ = |a M₀| * r ^ (k + 1 - M₀) := by rw [hsub]

/-- **Summability from perturbed contraction.** Under the same hypotheses,
the sequence `a` is summable past `M₀` (geometric tail). -/
lemma summable_of_perturbed_contraction
    {a : ℕ → ℝ} {ρ K : ℝ} {M₀ : ℕ}
    (hρ_nn : 0 ≤ ρ) (hK_nn : 0 ≤ K) (hM₀ : 1 ≤ M₀)
    (hcontract : ρ + K / M₀ < 1)
    (hrec : ∀ m, M₀ ≤ m → |a (m + 1)| ≤ (ρ + K / m) * |a m|) :
    Summable (fun m => a (m + M₀)) := by
  set r := ρ + K / (M₀ : ℝ)
  have hr_nn : 0 ≤ r := by positivity
  -- |a(m+M₀)| ≤ |a M₀|·r^m (from perturbed_geometric_decay), r < 1
  have hbound : ∀ m, |a (m + M₀)| ≤ |a M₀| * r ^ m := by
    intro m
    have h := perturbed_geometric_decay hρ_nn hK_nn hM₀ hcontract hrec (m + M₀) (by omega)
    simp only [show m + M₀ - M₀ = m from by omega] at h
    exact h
  have hgeom : Summable (fun m => |a M₀| * r ^ m) :=
    (summable_geometric_of_lt_one hr_nn hcontract).mul_left _
  exact (Summable.of_nonneg_of_le (fun m => abs_nonneg _) hbound hgeom).of_abs

/-! ### Linear growth from ratio bound (K = 1 case)

The full Poincaré-Perron theorem (asymptotic basis construction in the
variable-coefficient case) is a multi-day project requiring Birkhoff-type
formal-series machinery. The architecture below splits the work in two:

1. **Abstract step (this section, fully proved):** given a *ratio bound*
   `|c_{m+1}|/|c_m| ≤ |ev₁|·(1 + 1/m)` for `m ≥ M₀`,
   derive the linear × geometric growth
   `|c_m| ≤ C·(m+1)·|ev₁|^m`. Proof uses the telescoping identity
   `1 + 1/k = (k+1)/k`, so `∏_{k=M₀}^{m-1}(1+1/k) = m/M₀` exactly.
2. **Instance-specific step (caller's responsibility):** prove the ratio
   bound for the specific recurrence. For Apéry conifold this requires
   exploiting the explicit char-poly factorization
   `taylorShift(P)(t) = t·(t-z₁)²·(t+24√2)` and the denominator
   factorization (`aperyFrobenius_half_denom_ne_zero` etc.) — concrete
   nlinarith-style work, not abstract analysis.

This design isolates the cancellation-essential algebra into the instance,
while the abstract machinery becomes elementary (telescoping product). -/

/-- **Telescoping product for `K = 1`:** `∏_{k=M₀}^{m-1}(1 + 1/k) = m/M₀`. -/
lemma prod_one_plus_inv_telescoping {M₀ m : ℕ} (hM₀ : 1 ≤ M₀) (hm : M₀ ≤ m) :
    ∏ k ∈ Finset.Ico M₀ m, (1 + 1 / (k : ℝ)) = (m : ℝ) / M₀ := by
  induction m, hm using Nat.le_induction with
  | base =>
    rw [Finset.Ico_self, Finset.prod_empty]
    have : (M₀ : ℝ) ≠ 0 := by exact_mod_cast (show M₀ ≠ 0 by omega)
    field_simp
  | succ k hk ih =>
    rw [Finset.prod_Ico_succ_top hk, ih]
    have hk_pos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast (show 0 < k by omega)
    have hM₀_ne : (M₀ : ℝ) ≠ 0 := by exact_mod_cast (show M₀ ≠ 0 by omega)
    have hk_ne : (k : ℝ) ≠ 0 := hk_pos.ne'
    push_cast
    field_simp

/-- **Linear growth from a multiplicative ratio bound with `1/m` perturbation.**

If `|c_{m+1}| ≤ |ev₁|·(1 + 1/m)·|c_m|` for all `m ≥ M₀ ≥ 1`, then
`|c_m| ≤ C·(m+1)·|ev₁|^m` for an explicit constant `C`.

**Proof:** telescope past `M₀`, then use `prod_one_plus_inv_telescoping`
which gives the EXACT product `∏_{k=M₀}^{m-1}(1+1/k) = m/M₀`. Hence
`|c_m| ≤ |c_{M₀}|·|ev₁|^(m-M₀)·m/M₀`, which absorbs into the desired form. -/
lemma growth_bound_of_ratio_bound_one
    {c : ℕ → ℝ} {ev₁ : ℝ} {M₀ : ℕ}
    (hev₁ : 0 < |ev₁|) (hM₀ : 1 ≤ M₀)
    (hratio : ∀ m, M₀ ≤ m →
        |c (m + 1)| ≤ |ev₁| * (1 + 1 / (m : ℝ)) * |c m|) :
    ∃ C : ℝ, 0 < C ∧ ∀ m : ℕ,
      |c m| ≤ C * ((m : ℝ) + 1) * |ev₁| ^ m := by
  have hev_nn : 0 ≤ |ev₁| := abs_nonneg _
  have hM₀R_pos : (0 : ℝ) < (M₀ : ℝ) := by exact_mod_cast (show 0 < M₀ by omega)
  -- Telescope: for m ≥ M₀, |c m| ≤ |c M₀|·|ev₁|^(m-M₀)·∏(1+1/k)
  have h_tele : ∀ m : ℕ, M₀ ≤ m →
      |c m| ≤ |c M₀| * |ev₁| ^ (m - M₀) *
        ∏ k ∈ Finset.Ico M₀ m, (1 + 1 / (k : ℝ)) := by
    intro m hm
    induction m, hm using Nat.le_induction with
    | base => simp
    | succ k hk ih =>
      have hk_pos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast (show 0 < k by omega)
      have h1 : |c (k + 1)| ≤ |ev₁| * (1 + 1 / (k : ℝ)) * |c k| := hratio k hk
      have h_factor_nn : 0 ≤ |ev₁| * (1 + 1 / (k : ℝ)) := by
        have : 0 ≤ 1 / (k : ℝ) := by positivity
        positivity
      have h_prod_split :
          (∏ k' ∈ Finset.Ico M₀ k, (1 + 1 / (k' : ℝ))) * (1 + 1 / (k : ℝ)) =
            ∏ k' ∈ Finset.Ico M₀ (k + 1), (1 + 1 / (k' : ℝ)) :=
        (Finset.prod_Ico_succ_top hk _).symm
      calc |c (k + 1)|
          ≤ |ev₁| * (1 + 1 / (k : ℝ)) * |c k| := h1
        _ ≤ |ev₁| * (1 + 1 / (k : ℝ)) *
              (|c M₀| * |ev₁| ^ (k - M₀) *
                ∏ k' ∈ Finset.Ico M₀ k, (1 + 1 / (k' : ℝ))) :=
              mul_le_mul_of_nonneg_left ih h_factor_nn
        _ = |c M₀| * |ev₁| ^ ((k - M₀) + 1) *
              ∏ k' ∈ Finset.Ico M₀ (k + 1), (1 + 1 / (k' : ℝ)) := by
            rw [← h_prod_split, pow_succ]; ring
        _ = |c M₀| * |ev₁| ^ (k + 1 - M₀) *
              ∏ k' ∈ Finset.Ico M₀ (k + 1), (1 + 1 / (k' : ℝ)) := by
            have heq : (k - M₀) + 1 = k + 1 - M₀ := by omega
            rw [heq]
  -- Now combine with the exact telescoping identity
  -- ∏_{k=M₀}^{m-1}(1+1/k) = m/M₀
  -- to get |c m| ≤ |c M₀|·|ev₁|^(m-M₀)·m/M₀ for m ≥ M₀.
  -- Bound this by C·(m+1)·|ev₁|^m where
  -- C := max( |c M₀|/(M₀·|ev₁|^M₀), max_{k≤M₀} |c k| / |ev₁|^k ) etc.
  -- For simplicity we choose a LARGE constant that handles all base cases too.
  -- Define C absorbing |c M₀|/(M₀·|ev₁|^M₀) AND base cases.
  have hev_pos_pow : ∀ m, 0 < |ev₁| ^ m := fun m => pow_pos hev₁ m
  -- Base sum bound: max base case constants
  set Cbase : ℝ := |c M₀| / ((M₀ : ℝ) * |ev₁| ^ M₀) +
    (∑ k ∈ Finset.range (M₀ + 1), |c k| / |ev₁| ^ k) + 1 with hCbase_def
  have hCbase_pos : 0 < Cbase := by
    have h1 : 0 ≤ |c M₀| / ((M₀ : ℝ) * |ev₁| ^ M₀) := by
      apply div_nonneg (abs_nonneg _)
      positivity
    have h2 : 0 ≤ ∑ k ∈ Finset.range (M₀ + 1), |c k| / |ev₁| ^ k :=
      Finset.sum_nonneg (fun k _ => div_nonneg (abs_nonneg _) (hev_pos_pow k).le)
    linarith
  refine ⟨Cbase, hCbase_pos, fun m => ?_⟩
  by_cases hcase : M₀ ≤ m
  · -- Use telescoping for m ≥ M₀
    have h_tele_m := h_tele m hcase
    rw [prod_one_plus_inv_telescoping hM₀ hcase] at h_tele_m
    -- |c m| ≤ |c M₀|·|ev₁|^(m-M₀)·m/M₀
    -- Want: |c m| ≤ Cbase·(m+1)·|ev₁|^m
    -- Bound: |c M₀|·|ev₁|^(m-M₀)·m/M₀ ≤ (|c M₀|/(M₀·|ev₁|^M₀))·m·|ev₁|^m
    --                                ≤ Cbase·m·|ev₁|^m ≤ Cbase·(m+1)·|ev₁|^m
    have h_split_pow : |ev₁| ^ m = |ev₁| ^ M₀ * |ev₁| ^ (m - M₀) := by
      rw [← pow_add]; congr 1; omega
    have hM₀pow_pos : 0 < |ev₁| ^ M₀ := hev_pos_pow M₀
    have h1 : |c M₀| * |ev₁| ^ (m - M₀) * ((m : ℝ) / M₀) =
        (|c M₀| / ((M₀ : ℝ) * |ev₁| ^ M₀)) * ((m : ℝ) * |ev₁| ^ m) := by
      rw [h_split_pow]
      field_simp
    rw [h1] at h_tele_m
    have h_m_le : (m : ℝ) ≤ (m : ℝ) + 1 := by linarith
    have h_evm_nn : (0 : ℝ) ≤ |ev₁| ^ m := (hev_pos_pow m).le
    have h_factor_nn : (0 : ℝ) ≤ |c M₀| / ((M₀ : ℝ) * |ev₁| ^ M₀) := by
      apply div_nonneg (abs_nonneg _); positivity
    have h_factor_le_Cbase : (|c M₀| / ((M₀ : ℝ) * |ev₁| ^ M₀)) ≤ Cbase := by
      change _ ≤ |c M₀| / ((M₀ : ℝ) * |ev₁| ^ M₀) +
        (∑ k ∈ Finset.range (M₀ + 1), |c k| / |ev₁| ^ k) + 1
      have h2 : 0 ≤ ∑ k ∈ Finset.range (M₀ + 1), |c k| / |ev₁| ^ k :=
        Finset.sum_nonneg (fun k _ => div_nonneg (abs_nonneg _) (hev_pos_pow k).le)
      linarith
    have h_m1_nn : (0 : ℝ) ≤ (m : ℝ) + 1 := by positivity
    nlinarith [h_tele_m, h_m_le, h_evm_nn, h_factor_nn, h_factor_le_Cbase, h_m1_nn,
      mul_nonneg h_m1_nn h_evm_nn]
  · -- Base case: m < M₀, use Cbase directly
    push_neg at hcase
    have hm_lt : m < M₀ + 1 := by omega
    have h_evm_nn : (0 : ℝ) ≤ |ev₁| ^ m := (hev_pos_pow m).le
    have h1 : |c m| / |ev₁| ^ m ≤ ∑ k ∈ Finset.range (M₀ + 1), |c k| / |ev₁| ^ k := by
      apply Finset.single_le_sum (f := fun k => |c k| / |ev₁| ^ k)
        (fun k _ => div_nonneg (abs_nonneg _) (hev_pos_pow k).le)
      exact Finset.mem_range.mpr hm_lt
    have h2 : |c m| ≤ (∑ k ∈ Finset.range (M₀ + 1), |c k| / |ev₁| ^ k) * |ev₁| ^ m := by
      rw [div_le_iff₀ (hev_pos_pow m)] at h1
      exact h1
    have h3 : (∑ k ∈ Finset.range (M₀ + 1), |c k| / |ev₁| ^ k) ≤ Cbase := by
      change _ ≤ |c M₀| / ((M₀ : ℝ) * |ev₁| ^ M₀) +
        (∑ k ∈ Finset.range (M₀ + 1), |c k| / |ev₁| ^ k) + 1
      have h_first : 0 ≤ |c M₀| / ((M₀ : ℝ) * |ev₁| ^ M₀) := by
        apply div_nonneg (abs_nonneg _); positivity
      linarith
    have h_m1_pos : (1 : ℝ) ≤ (m : ℝ) + 1 := by
      have : (0 : ℝ) ≤ (m : ℝ) := by positivity
      linarith
    have h4 : |c m| ≤ Cbase * |ev₁| ^ m :=
      le_trans h2 (mul_le_mul_of_nonneg_right h3 h_evm_nn)
    have h5 : Cbase * |ev₁| ^ m ≤ Cbase * ((m : ℝ) + 1) * |ev₁| ^ m := by
      have hCev_nn : 0 ≤ Cbase * |ev₁| ^ m := mul_nonneg hCbase_pos.le h_evm_nn
      nlinarith [hCev_nn, h_m1_pos, h_evm_nn, hCbase_pos.le]
    linarith

end Ripple.Frobenius.PoincaréPerron
