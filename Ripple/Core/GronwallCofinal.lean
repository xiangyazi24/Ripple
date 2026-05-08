/-
  Ripple.Core.GronwallCofinal — eventual-feed Grönwall lower bound.

  Pure analytic lemma underlying the no-collapse SCC induction step.
  Given an ODE `f' = g - D·f` on `[T_g, ∞)` where the forcing term `g` is
  eventually bounded below by `c > 0`, the solution `f` is also eventually
  bounded below by a positive constant `c'`.

  This fills the gap between Mathlib's constant-coefficient Grönwall
  (`le_gronwallBound_of_liminf_deriv_right_le`) and the downstream use case:
  in Mathlib's version the forcing is a constant `ε`; here it is a function
  `g` that is eventually ≥ `c`.
-/

import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Calculus.Deriv.Slope

namespace Ripple

open Set Real

/-- **Eventual-feed Grönwall lower bound.**

If `f` satisfies the one-sided ODE inequality `f' = g - D·f` on `[T_g, ∞)`
(as a right-derivative), `f` is nonnegative at `T_g`, and `g(t) ≥ c > 0`
for `t ≥ T_g`, then `f(t) ≥ α/2 := c / (2·(D+1))` for all `t` beyond a
threshold `T_g + T_thr`, where `T_thr := 1` if `D = 0` and
`T_thr := log 2 / D + 1` if `D > 0`.

Proof. Set `K := D + 1` and `α := c / K`. Define `φ := α - f`. A direct
calculation using `c ≤ g` gives `φ'(s) ≤ -D·φ(s) - α` on `[T_g, ∞)`, so
`φ(t) ≤ gronwallBound (α - f T_g) (-D) (-α) (t - T_g)` by Mathlib's
scalar Grönwall. Since `f(T_g) ≥ 0`, the δ parameter `α - f(T_g)` is
bounded above by `α`. Beyond the threshold the right-hand side is ≤ `α/2`,
so `f(t) = α - φ(t) ≥ α/2`. -/
theorem gronwall_eventual_lower_bound
    {c D : ℝ} (hc : 0 < c) (hD : 0 ≤ D)
    {f g : ℝ → ℝ} {T_g : ℝ}
    (hf_contOn : ContinuousOn f (Ici T_g))
    (hf_Tg_nn : 0 ≤ f T_g)
    (hf_hasDeriv : ∀ s, T_g ≤ s →
      HasDerivWithinAt f (g s - D * f s) (Ici s) s)
    (hg : ∀ t, T_g ≤ t → c ≤ g t) :
    ∃ T' c' : ℝ, T_g ≤ T' ∧ 0 < c' ∧ ∀ t, T' ≤ t → c' ≤ f t := by
  -- Setup constants: K := D + 1, α := c / K.
  set K : ℝ := D + 1 with hK_def
  have hK_pos : 0 < K := by rw [hK_def]; linarith
  set α : ℝ := c / K with hα_def
  have hα_pos : 0 < α := div_pos hc hK_pos
  -- Key algebraic fact: D · α + α = c (since K = D + 1 and K · α = c).
  have hDα_plus_α : D * α + α = c := by
    have : K * α = c := by rw [hα_def]; field_simp
    have hKexp : K * α = D * α + α := by rw [hK_def]; ring
    linarith
  -- Threshold T_thr: 1 if D = 0, log 2 / D + 1 otherwise.
  set T_thr : ℝ := if D = 0 then 1 else (Real.log 2) / D + 1 with hT_thr_def
  have hT_thr_ge_one : 1 ≤ T_thr := by
    rw [hT_thr_def]; split_ifs with hD0
    · exact le_refl _
    · have hD_pos : 0 < D := lt_of_le_of_ne hD (Ne.symm hD0)
      have hlog2_nn : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
      have : 0 ≤ Real.log 2 / D := div_nonneg hlog2_nn (le_of_lt hD_pos)
      linarith
  -- The final threshold time and lower bound.
  refine ⟨T_g + T_thr, α / 2, by linarith, by positivity, ?_⟩
  intro t ht_ge
  have ht_ge_Tg : T_g ≤ t := by linarith
  -- Define φ(s) := α - f(s).
  set φ : ℝ → ℝ := fun s => α - f s with hφ_def
  -- Continuity of φ on [T_g, t].
  have h_φ_contOn : ContinuousOn φ (Icc T_g t) := by
    apply ContinuousOn.sub continuousOn_const
    exact hf_contOn.mono Icc_subset_Ici_self
  -- Right-derivative of φ on [T_g, t).
  have h_φ_deriv : ∀ s ∈ Ico T_g t,
      HasDerivWithinAt φ (-(g s - D * f s)) (Ici s) s := by
    intro s hs
    have hfs := hf_hasDeriv s hs.1
    have h : HasDerivWithinAt φ (0 - (g s - D * f s)) (Ici s) s :=
      (hasDerivWithinAt_const _ _ α).sub hfs
    simpa using h
  -- Derivative bound: `-(g - D·f) ≤ -D·φ + (-α)` on `[T_g, t)`.
  have h_bound : ∀ s ∈ Ico T_g t,
      -(g s - D * f s) ≤ -D * φ s + (-α) := by
    intro s hs
    have hgs : c ≤ g s := hg s hs.1
    -- Goal: -(g s - D·f s) ≤ -D·(α - f s) + (-α)
    -- ⟺ -g s + D·f s ≤ -D·α + D·f s - α
    -- ⟺ -g s ≤ -(D·α + α) = -c ⟺ c ≤ g s ✓
    change -(g s - D * f s) ≤ -D * (α - f s) + (-α)
    have : D * α + α ≤ g s := hDα_plus_α ▸ hgs
    nlinarith
  -- Apply Mathlib's scalar Grönwall on [T_g, t].
  have h_gron : ∀ x ∈ Icc T_g t,
      φ x ≤ gronwallBound (α - f T_g) (-D) (-α) (x - T_g) := by
    apply le_gronwallBound_of_liminf_deriv_right_le h_φ_contOn
    · intro s hs rv hrv
      exact (h_φ_deriv s hs).liminf_right_slope_le hrv
    · simp [hφ_def]
    · intro s hs; exact h_bound s hs
  have h_gron_t : φ t ≤ gronwallBound (α - f T_g) (-D) (-α) (t - T_g) :=
    h_gron t ⟨ht_ge_Tg, le_refl _⟩
  -- Bound: α - f(T_g) ≤ α since f(T_g) ≥ 0.
  have hδ_le : α - f T_g ≤ α := by linarith
  -- Compute gronwallBound ≤ α/2 at (t - T_g) ≥ T_thr.
  have h_gron_form :
      gronwallBound (α - f T_g) (-D) (-α) (t - T_g) ≤ α / 2 := by
    by_cases hD0 : D = 0
    · -- K_gron = 0 case: gronwallBound δ 0 (-α) x = δ + (-α)·x.
      have hneg_eq : (-D : ℝ) = 0 := by rw [hD0]; ring
      rw [hneg_eq, gronwallBound_K0]
      have hT_thr_val : T_thr = 1 := by rw [hT_thr_def, if_pos hD0]
      have ht_minus : 1 ≤ t - T_g := by
        have := hT_thr_val ▸ ht_ge
        linarith
      -- Goal: α - f T_g + (-α) · (t - T_g) ≤ α/2
      -- δ ≤ α, (t - T_g) ≥ 1 ⇒ α + (-α)·(t - T_g) ≤ α - α = 0 ≤ α/2.
      have h_mono : (-α) * (t - T_g) ≤ (-α) * 1 :=
        mul_le_mul_of_nonpos_left ht_minus (by linarith)
      linarith
    · -- K_gron = -D ≠ 0.
      have hD_pos : 0 < D := lt_of_le_of_ne hD (Ne.symm hD0)
      have hKg_ne : (-D : ℝ) ≠ 0 := neg_ne_zero.mpr hD0
      rw [gronwallBound_of_K_ne_0 hKg_ne]
      -- Reduce form: δ · exp(-D(t-T_g)) + (-α)/(-D) · (exp(-D(t-T_g)) - 1)
      --            = δ · u + (α/D) · (u - 1)    where u = exp(-D(t-T_g)).
      have h_neg_div : ((-α) / (-D) : ℝ) = α / D := by rw [neg_div_neg_eq]
      -- Target inequality (after rewriting the `-α / -D` factor).
      change (α - f T_g) * Real.exp (-D * (t - T_g))
            + ((-α) / (-D)) * (Real.exp (-D * (t - T_g)) - 1) ≤ α / 2
      rw [h_neg_div]
      set u : ℝ := Real.exp (-D * (t - T_g)) with hu_def
      have hu_pos : 0 < u := Real.exp_pos _
      -- Threshold: t - T_g ≥ log 2 / D + 1.
      have hT_thr_val : T_thr = (Real.log 2) / D + 1 := by
        rw [hT_thr_def]; simp [hD0]
      have ht_minus : (Real.log 2) / D + 1 ≤ t - T_g := by
        linarith [hT_thr_val ▸ ht_ge]
      -- D · (t - T_g) ≥ log 2 + D.
      have h_Dt : Real.log 2 + D ≤ D * (t - T_g) := by
        have h1 : D * ((Real.log 2) / D + 1) ≤ D * (t - T_g) :=
          mul_le_mul_of_nonneg_left ht_minus (le_of_lt hD_pos)
        have h2 : D * ((Real.log 2) / D + 1) = Real.log 2 + D := by
          field_simp
        linarith
      -- u ≤ exp(-log 2) · exp(-D) ≤ 1/2 · 1 = 1/2.
      have hu_le_half : u ≤ 1 / 2 := by
        have h_arg_le : -D * (t - T_g) ≤ -Real.log 2 := by
          have h1 : -(D * (t - T_g)) ≤ -(Real.log 2 + D) := by linarith
          have h2 : -D * (t - T_g) = -(D * (t - T_g)) := by ring
          rw [h2]
          have hD_nn : 0 ≤ D := le_of_lt hD_pos
          linarith
        have h_exp_le : Real.exp (-D * (t - T_g)) ≤ Real.exp (-Real.log 2) :=
          Real.exp_le_exp.mpr h_arg_le
        have hval : Real.exp (-Real.log 2) = 1 / 2 := by
          rw [Real.exp_neg, Real.exp_log (by norm_num : (0:ℝ) < 2)]; norm_num
        rw [hu_def]; linarith
      -- (α - f T_g) · u + (α / D) · (u - 1)
      --   ≤ α · u + (α / D) · (u - 1)          [since α - f T_g ≤ α, u > 0]
      --   = (α / D) · (D · u + u - 1)
      --   = (α / D) · (K · u - 1)              [K := D + 1]
      --   ≤ (α / D) · (D / 2)                  [K·u ≤ K/2 ≤ (D+2)/2, so K·u - 1 ≤ D/2]
      --   = α / 2.
      have h_step1 : (α - f T_g) * u + (α / D) * (u - 1)
                    ≤ α * u + (α / D) * (u - 1) := by
        have h_δ_mono : (α - f T_g) * u ≤ α * u :=
          mul_le_mul_of_nonneg_right hδ_le (le_of_lt hu_pos)
        linarith
      -- Now bound α·u + (α/D)·(u-1) ≤ α/2.
      have h_step2 : α * u + (α / D) * (u - 1) ≤ α / 2 := by
        have hK_val : K = D + 1 := hK_def
        -- α/D · (D·u + u - 1) = α · u + (α/D) · (u - 1)
        have h_rewrite :
            α * u + (α / D) * (u - 1) = (α / D) * ((D + 1) * u - 1) := by
          field_simp
          ring
        rw [h_rewrite]
        -- (D + 1) · u ≤ (D + 1) · (1/2) = (D+1)/2
        have hKu_bound : (D + 1) * u ≤ (D + 1) / 2 := by
          have hKpos : 0 < D + 1 := by linarith
          have : (D + 1) * u ≤ (D + 1) * (1 / 2) :=
            mul_le_mul_of_nonneg_left hu_le_half (le_of_lt hKpos)
          linarith
        -- (D + 1) · u - 1 ≤ (D+1)/2 - 1 = (D - 1)/2 ≤ D/2
        have hKu_minus1 : (D + 1) * u - 1 ≤ D / 2 := by linarith
        -- α/D ≥ 0, multiply: (α/D)·((D+1)·u - 1) ≤ (α/D)·(D/2) = α/2
        have hα_D_nn : 0 ≤ α / D := div_nonneg (le_of_lt hα_pos) (le_of_lt hD_pos)
        have := mul_le_mul_of_nonneg_left hKu_minus1 hα_D_nn
        have hD_ne : D ≠ 0 := ne_of_gt hD_pos
        have h_final : (α / D) * (D / 2) = α / 2 := by field_simp
        linarith
      linarith
  -- Combine: f(t) = α - φ(t) ≥ α - gronwallBound ... ≥ α - α/2 = α/2.
  have : α - f t ≤ α / 2 := by
    have := h_gron_t
    have : φ t ≤ α / 2 := le_trans h_gron_t h_gron_form
    change α - f t ≤ α / 2
    have hφt : φ t = α - f t := rfl
    linarith
  linarith

/-- **Scalar exponential decay from a Lyapunov inequality.**

If `V` is continuous on `[0, T]`, has a right-derivative `V'(x)` on `[0, T)`
bounded above by `−α·V(x)`, and `α > 0`, then
`V(t) ≤ V(0)·exp(−α·t)` for all `t ∈ [0, T]`. -/
theorem scalar_exponential_decay
    {V V' : ℝ → ℝ} {α T : ℝ} (_hα : 0 < α) (_hT : 0 ≤ T)
    (hV_cont : ContinuousOn V (Set.Icc 0 T))
    (hV_deriv : ∀ x ∈ Set.Ico (0 : ℝ) T,
      HasDerivWithinAt V (V' x) (Set.Ici x) x)
    (h_bound : ∀ x ∈ Set.Ico (0 : ℝ) T, V' x ≤ -α * V x) :
    ∀ t ∈ Set.Icc (0 : ℝ) T, V t ≤ V 0 * Real.exp (-α * t) := by
  -- Integrating factor: φ(s) := V(s) · exp(α·s). Then φ' ≤ 0, so φ antitone.
  set φ : ℝ → ℝ := fun s => V s * Real.exp (α * s) with hφ_def
  -- Derivative of `s ↦ exp(α·s)` at `s` within `Ici s` (really, everywhere).
  have h_exp_deriv : ∀ s,
      HasDerivWithinAt (fun s => Real.exp (α * s)) (α * Real.exp (α * s)) (Ici s) s := by
    intro s
    have h1 : HasDerivAt (fun s : ℝ => α * s) α s := by
      simpa using (hasDerivAt_id s).const_mul α
    have h2 : HasDerivAt (fun s => Real.exp (α * s)) (Real.exp (α * s) * α) s :=
      h1.exp
    have h3 : HasDerivAt (fun s => Real.exp (α * s)) (α * Real.exp (α * s)) s := by
      have : Real.exp (α * s) * α = α * Real.exp (α * s) := by ring
      rw [this] at h2; exact h2
    exact h3.hasDerivWithinAt
  -- Continuity of `s ↦ exp(α·s)` on `Icc 0 T`.
  have h_exp_cont : ContinuousOn (fun s => Real.exp (α * s)) (Icc 0 T) :=
    (Real.continuous_exp.comp (continuous_const.mul continuous_id)).continuousOn
  -- Continuity of φ on `Icc 0 T`.
  have hφ_cont : ContinuousOn φ (Icc 0 T) := hV_cont.mul h_exp_cont
  -- Right-derivative of φ on `Ico 0 T`.
  -- φ'(x) = V'(x) · exp(α·x) + V(x) · α · exp(α·x) = (V'(x) + α·V(x)) · exp(α·x).
  set φ' : ℝ → ℝ := fun x => (V' x + α * V x) * Real.exp (α * x) with hφ'_def
  have hφ_deriv : ∀ x ∈ Ico (0:ℝ) T, HasDerivWithinAt φ (φ' x) (Ici x) x := by
    intro x hx
    have hV := hV_deriv x hx
    have hE := h_exp_deriv x
    -- Product rule: V · (exp ∘ (α·)) at x.
    have hprod : HasDerivWithinAt (fun s => V s * Real.exp (α * s))
        (V' x * Real.exp (α * x) + V x * (α * Real.exp (α * x))) (Ici x) x := hV.mul hE
    -- Rewrite the derivative expression to match φ' x.
    have h_eq : V' x * Real.exp (α * x) + V x * (α * Real.exp (α * x))
              = (V' x + α * V x) * Real.exp (α * x) := by ring
    rw [h_eq] at hprod
    exact hprod
  -- The derivative is nonpositive on `Ico 0 T`:
  -- `V' x + α · V x ≤ 0` by hypothesis, and `exp(α·x) > 0`.
  have hφ'_nonpos : ∀ x ∈ Ico (0:ℝ) T, φ' x ≤ 0 := by
    intro x hx
    have hbx : V' x ≤ -α * V x := h_bound x hx
    have h_sum_nonpos : V' x + α * V x ≤ 0 := by linarith
    have h_exp_pos : 0 < Real.exp (α * x) := Real.exp_pos _
    have : (V' x + α * V x) * Real.exp (α * x) ≤ 0 * Real.exp (α * x) :=
      mul_le_mul_of_nonneg_right h_sum_nonpos (le_of_lt h_exp_pos)
    simpa using this
  -- Apply Mathlib fencing: φ(t) ≤ φ(0) for t ∈ Icc 0 T.
  -- Use constant boundary B := fun _ => φ 0, with B' := 0.
  have h_antitone : ∀ t ∈ Icc (0:ℝ) T, φ t ≤ φ 0 := by
    have := image_le_of_deriv_right_le_deriv_boundary
      (f := φ) (f' := φ') (a := 0) (b := T)
      (B := fun _ => φ 0) (B' := fun _ => 0)
      hφ_cont hφ_deriv (le_refl _) continuousOn_const
      (fun x _ => (hasDerivWithinAt_const x (Ici x) (φ 0)))
      (fun x hx => by exact le_trans (hφ'_nonpos x hx) (le_refl 0))
    intro t ht; exact this ht
  -- Conclude: V(t) ≤ V(0) · exp(-α·t).
  intro t ht
  have hφt : φ t ≤ φ 0 := h_antitone t ht
  -- φ 0 = V 0 · exp 0 = V 0.
  have hφ0 : φ 0 = V 0 := by simp [hφ_def]
  -- φ t = V t · exp(α·t).
  have hφt_expand : φ t = V t * Real.exp (α * t) := rfl
  rw [hφ0, hφt_expand] at hφt
  -- V t · exp(α·t) ≤ V 0 ⇒ V t ≤ V 0 · exp(-α·t).
  have h_exp_pos : 0 < Real.exp (α * t) := Real.exp_pos _
  have h_exp_inv : Real.exp (α * t) * Real.exp (-α * t) = 1 := by
    rw [← Real.exp_add]
    have : α * t + -α * t = 0 := by ring
    rw [this, Real.exp_zero]
  -- Multiply both sides by exp(-α·t) > 0.
  have h_exp_neg_pos : 0 < Real.exp (-α * t) := Real.exp_pos _
  have hmul := mul_le_mul_of_nonneg_right hφt (le_of_lt h_exp_neg_pos)
  -- LHS = V t · (exp(α·t) · exp(-α·t)) = V t.
  -- RHS = V 0 · exp(-α·t).
  have hlhs : V t * Real.exp (α * t) * Real.exp (-α * t) = V t := by
    rw [mul_assoc, h_exp_inv, mul_one]
  rw [hlhs] at hmul
  exact hmul

end Ripple
