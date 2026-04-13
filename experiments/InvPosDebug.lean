import Ripple.Core.PIVP
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

namespace Ripple

def TimeModulus := ℕ → ℝ

structure BoundedTimeComputable (d : ℕ) (α : ℝ) where
  pivp : PIVP d
  sol : PIVP.Solution pivp
  modulus : TimeModulus
  bounded : pivp.IsBounded sol.trajectory
  convergence : ∀ r : ℕ, ∀ t : ℝ, t > modulus r →
    |sol.trajectory t pivp.output - α| < Real.exp (-(r : ℝ))

def IsRealTimeComputable (α : ℝ) : Prop :=
  ∃ d : ℕ, ∃ btc : BoundedTimeComputable d α,
    ∃ C : ℝ, 0 < C ∧ ∀ r : ℕ, btc.modulus r ≤ C * (↑r + 1)

/-- A one-sided exponential kernel has uniformly bounded mass. -/
private theorem integral_exp_decay_le_debug {λ T t : ℝ} (hλ : 0 < λ) (hTt : T ≤ t) :
    ∫ s in T..t, Real.exp (-λ * (t - s)) ≤ 1 / λ := by
  have hderiv :
      ∀ s ∈ Set.uIcc T t,
        HasDerivAt (fun u => (1 / λ) * Real.exp (-λ * (t - u)))
          (Real.exp (-λ * (t - s))) s := by
    intro s hs
    have hinner : HasDerivAt (fun u => -λ * (t - u)) λ s := by
      convert (((hasDerivAt_const s t).sub (hasDerivAt_id s)).const_mul (-λ)) using 1
      ring
    convert hinner.exp.const_mul (1 / λ) using 1
    field_simp [hλ.ne']
    ring
  have hint : IntervalIntegrable (fun s => Real.exp (-λ * (t - s))) volume T t := by
    apply Continuous.intervalIntegrable
    fun_prop
  have hcalc :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  calc
    ∫ s in T..t, Real.exp (-λ * (t - s))
        = (1 / λ) - (1 / λ) * Real.exp (-λ * (t - T)) := by
            simpa [hλ.ne'] using hcalc
    _ ≤ 1 / λ := by
      have hnonneg : 0 ≤ (1 / λ) * Real.exp (-λ * (t - T)) := by positivity
      linarith

theorem realtime_field_inv_pos_debug {α : ℝ} (hα_pos : 0 < α)
    (ha : IsRealTimeComputable α) : IsRealTimeComputable α⁻¹ := by
  have hα_ne : α ≠ 0 := ne_of_gt hα_pos
  obtain ⟨d, btc, C, hC, hmod⟩ := ha
  obtain ⟨M, hM, hbound⟩ := btc.bounded
  set f : ℝ → ℝ := fun t => btc.sol.trajectory t btc.pivp.output with hf_def
  set g : ℝ → ℝ := fun t => f (max t 0) with hg_def
  have hg_cont : Continuous g := continuous_iff_continuousAt.mpr fun t => by
    have h1 : ContinuousAt f (max t 0) :=
      ((hasDerivAt_pi.mp (btc.sol.is_solution (max t 0) (le_max_right t 0)))
        btc.pivp.output).continuousAt
    have h2 : ContinuousAt (fun s => max s (0 : ℝ)) t :=
      (continuous_id.max continuous_const).continuousAt
    exact ContinuousAt.comp (g := f) (f := fun s => max s (0 : ℝ)) h1 h2
  have hg_eq : ∀ t, 0 ≤ t → g t = f t := fun t ht => by simp [hg_def, max_eq_left ht]
  have hf_bound : ∀ t, 0 ≤ t → |f t| ≤ M := fun t ht => by
    have := norm_le_pi_norm (btc.sol.trajectory t) btc.pivp.output
    rw [Real.norm_eq_abs] at this
    linarith [hbound t ht]
  set G : ℝ → ℝ := fun t => ∫ s in (0 : ℝ)..t, g s with hG_def
  have hG_hd : ∀ t, HasDerivAt G (g t) t := fun t =>
    intervalIntegral.integral_hasDerivAt_right (hg_cont.intervalIntegrable 0 t)
      (hg_cont.stronglyMeasurableAtFilter _ _) hg_cont.continuousAt
  have hG_cont : Continuous G :=
    continuous_iff_continuousAt.mpr fun t => (hG_hd t).continuousAt
  have hexpG : Continuous (fun s => Real.exp (G s)) := Real.continuous_exp.comp hG_cont
  set x : ℝ → ℝ := fun t => Real.exp (-G t) * ∫ s in (0 : ℝ)..t, Real.exp (G s) with hx_def
  have hx_zero : x 0 = 0 := by
    simp [hx_def, hG_def, intervalIntegral.integral_same]
  have hx_hd : ∀ t, HasDerivAt x (1 - g t * x t) t := by
    intro t
    have h2 := (hG_hd t).neg.exp
    have h3 := intervalIntegral.integral_hasDerivAt_right (hexpG.intervalIntegrable 0 t)
      (hexpG.stronglyMeasurableAtFilter _ _) hexpG.continuousAt
    have h4 := h2.mul h3
    have hfun :
        (fun t => Real.exp ((-G) t)) * (fun u => ∫ s in (0 : ℝ)..u, Real.exp (G s)) = x := by
      ext s
      simp [hx_def, Pi.mul_apply]
    rw [hfun] at h4
    convert h4 using 1
    simp only [hx_def, Pi.neg_apply]
    rw [show Real.exp (-G t) * Real.exp (G t) = 1 from by
      rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]]
    ring
  set Npos : ℕ := Nat.ceil (2 / α) with hNpos_def
  set T0 : ℝ := C * (↑Npos + 1) + 1 with hT0_def
  set B0 : ℝ := Real.exp (M * T0) * (T0 * Real.exp (M * T0)) with hB0_def
  set Ninit : ℕ := Nat.ceil (B0 + 3 / α) with hNinit_def
  set Ntail : ℕ := Nat.ceil (2 / α ^ 2) with hNtail_def
  have hT0_pos : 0 < T0 := by
    rw [hT0_def]
    positivity
  have hNpos_ge : (2 / α : ℝ) ≤ Npos := Nat.le_ceil _
  have hNpos_exp : Real.exp (-(↑Npos : ℝ)) ≤ α / 2 := by
    have hplus : (↑Npos : ℝ) + 1 ≤ Real.exp (↑Npos : ℝ) := by
      simpa using Real.add_one_le_exp (↑Npos : ℝ)
    have hden_pos : 0 < (↑Npos : ℝ) + 1 := by positivity
    have h_inv : (1 : ℝ) / Real.exp (↑Npos : ℝ) ≤ 1 / ((↑Npos : ℝ) + 1) :=
      one_div_le_one_div_of_le hden_pos hplus
    have h_half : 1 / ((↑Npos : ℝ) + 1) ≤ α / 2 := by
      have htmp : (2 : ℝ) ≤ α * ((↑Npos : ℝ) + 1) := by
        have hmul := hNpos_ge
        field_simp [hα_ne] at hmul
        nlinarith [hmul, hα_pos]
      field_simp [hα_ne, hden_pos.ne']
      nlinarith
    simpa [Real.exp_neg] using le_trans h_inv h_half
  have hg_lower : ∀ t, T0 ≤ t → α / 2 ≤ g t := by
    intro t ht
    have ht0 : 0 ≤ t := le_trans hT0_pos.le ht
    have ht_mod : t > btc.modulus Npos := by
      have hlin := hmod Npos
      have : C * (↑Npos + 1) < t := by
        rw [hT0_def] at ht
        linarith
      exact lt_of_le_of_lt hlin this
    rw [hg_eq t ht0]
    have hconv := btc.convergence Npos t ht_mod
    have hclose : |f t - α| < α / 2 := lt_of_lt_of_le hconv hNpos_exp
    linarith [abs_lt.mp hclose]
  have hG_split : ∀ {s t : ℝ}, 0 ≤ s → s ≤ t → G t = G s + ∫ u in s..t, g u := by
    intro s t hs hst
    have hadd :
        (∫ u in (0 : ℝ)..s, g u) + ∫ u in s..t, g u = ∫ u in (0 : ℝ)..t, g u :=
      intervalIntegral.integral_add_adjacent_intervals
        (hg_cont.intervalIntegrable 0 s) (hg_cont.intervalIntegrable s t)
    simpa [hG_def] using hadd
  set k : ℝ → ℝ → ℝ := fun t s => Real.exp (-(∫ u in s..t, g u)) with hk_def
  have hk_hd : ∀ t s, HasDerivAt (fun u => k t u) (g s * k t s) s := by
    intro t s
    have hleft :=
      intervalIntegral.integral_hasDerivAt_left (hg_cont.intervalIntegrable s t)
        (hg_cont.stronglyMeasurableAtFilter _ _) hg_cont.continuousAt
    simpa [k, hk_def, mul_comm] using hleft.neg.exp
  have hk_cont : ∀ t, Continuous (fun s => k t s) := by
    intro t
    exact continuous_iff_continuousAt.mpr fun s => (hk_hd t s).continuousAt
  have hk_integral : ∀ {T t : ℝ}, T ≤ t → ∫ s in T..t, g s * k t s = 1 - k t T := by
    intro T t hTt
    have hderiv : ∀ s ∈ Set.uIcc T t, HasDerivAt (fun u => k t u) (g s * k t s) s := by
      intro s hs
      exact hk_hd t s
    have hint : IntervalIntegrable (fun s => g s * k t s) volume T t :=
      (hg_cont.mul (hk_cont t)).intervalIntegrable T t
    have hcalc := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
    simpa [k, hk_def] using hcalc
  have hk_exp : ∀ {s t : ℝ}, 0 ≤ s → s ≤ t → Real.exp (-G t) * Real.exp (G s) = k t s := by
    intro s t hs hst
    have hsplit := hG_split hs hst
    calc
      Real.exp (-G t) * Real.exp (G s)
          = (Real.exp (-G s) * Real.exp (-(∫ u in s..t, g u))) * Real.exp (G s) := by
              rw [hsplit, neg_add, Real.exp_add]
      _ = Real.exp (-(∫ u in s..t, g u)) * (Real.exp (-G s) * Real.exp (G s)) := by
              ac_rfl
      _ = Real.exp (-(∫ u in s..t, g u)) := by
              rw [show Real.exp (-G s) * Real.exp (G s) = 1 from by
                rw [← Real.exp_add, neg_add_cancel, Real.exp_zero], mul_one]
      _ = k t s := by simp [k, hk_def]
  have hx_restart : ∀ {T t : ℝ}, 0 ≤ T → T ≤ t →
      x t = k t T * x T + ∫ s in T..t, k t s := by
    intro T t hT0 hTt
    have hsplit :
        ∫ s in (0 : ℝ)..t, Real.exp (G s) =
          ∫ s in (0 : ℝ)..T, Real.exp (G s) + ∫ s in T..t, Real.exp (G s) := by
      symm
      exact intervalIntegral.integral_add_adjacent_intervals
        (hexpG.intervalIntegrable 0 T) (hexpG.intervalIntegrable T t)
    have hfac : Real.exp (-G t) = k t T * Real.exp (-G T) := by
      have hsplitG := hG_split hT0 hTt
      calc
        Real.exp (-G t) = Real.exp (-(G T + ∫ u in T..t, g u)) := by rw [hsplitG]
        _ = Real.exp (-G T) * Real.exp (-(∫ u in T..t, g u)) := by
              rw [neg_add, Real.exp_add]
        _ = k t T * Real.exp (-G T) := by
              simp [k, hk_def, mul_comm, mul_left_comm, mul_assoc]
    have htail :
        Real.exp (-G t) * ∫ s in T..t, Real.exp (G s) = ∫ s in T..t, k t s := by
      rw [← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr
      intro s hs
      have hsI : s ∈ Set.Icc T t := by simpa [Set.uIcc_of_le hTt] using hs
      have hs0 : 0 ≤ s := le_trans hT0 hsI.1
      have hst : s ≤ t := hsI.2
      simpa [k, hk_def] using hk_exp hs0 hst
    rw [hx_def, hsplit, mul_add, htail]
    calc
      Real.exp (-G t) * ∫ s in (0 : ℝ)..T, Real.exp (G s) + ∫ s in T..t, k t s
          = (k t T * Real.exp (-G T)) * ∫ s in (0 : ℝ)..T, Real.exp (G s) + ∫ s in T..t, k t s := by
              rw [hfac]
      _ = k t T * x T + ∫ s in T..t, k t s := by
              simp [hx_def, mul_assoc]
  have hx_nonneg : ∀ t, 0 ≤ t → 0 ≤ x t := by
    intro t ht
    rw [hx_def]
    apply mul_nonneg
    · exact le_of_lt (Real.exp_pos _)
    · exact intervalIntegral.integral_nonneg ht (fun s hs => le_of_lt (Real.exp_pos _))
  have hG_abs_le : ∀ t, 0 ≤ t → t ≤ T0 → |G t| ≤ M * T0 := by
    intro t ht0 htT
    rw [hG_def]
    have h_abs_mono : ∫ s in (0 : ℝ)..t, |g s| ≤ ∫ s in (0 : ℝ)..t, M := by
      apply intervalIntegral.integral_mono_on ht0
      · exact hg_cont.norm.intervalIntegrable 0 t
      · exact continuous_const.intervalIntegrable 0 t
      · intro s hs
        rw [hg_eq s hs.1]
        exact hf_bound s hs.1
    calc
      |∫ s in (0 : ℝ)..t, g s| ≤ ∫ s in (0 : ℝ)..t, |g s| :=
        intervalIntegral.abs_integral_le_integral_abs ht0
      _ ≤ ∫ s in (0 : ℝ)..t, M := h_abs_mono
      _ = M * t := by simp [ht0, mul_comm, mul_left_comm, mul_assoc]
      _ ≤ M * T0 := mul_le_mul_of_nonneg_left htT (le_of_lt hM)
  have hx_pre : ∀ t, 0 ≤ t → t ≤ T0 → x t ≤ B0 := by
    intro t ht0 htT
    have h_exp_le : Real.exp (-G t) ≤ Real.exp (M * T0) := by
      apply Real.exp_le_exp.mpr
      have hG := hG_abs_le t ht0 htT
      linarith
    have h_int_le : ∫ s in (0 : ℝ)..t, Real.exp (G s) ≤ T0 * Real.exp (M * T0) := by
      have h_exp_mono :
          ∫ s in (0 : ℝ)..t, Real.exp (G s) ≤ ∫ s in (0 : ℝ)..t, Real.exp (M * T0) := by
        apply intervalIntegral.integral_mono_on ht0
        · exact hexpG.intervalIntegrable 0 t
        · exact continuous_const.intervalIntegrable 0 t
        · intro s hs
          have hsT : s ≤ T0 := le_trans hs.2 htT
          have hG := hG_abs_le s hs.1 hsT
          apply Real.exp_le_exp.mpr
          linarith
      calc
        ∫ s in (0 : ℝ)..t, Real.exp (G s) ≤ ∫ s in (0 : ℝ)..t, Real.exp (M * T0) := h_exp_mono
        _ = t * Real.exp (M * T0) := by simp [ht0, mul_comm, mul_left_comm, mul_assoc]
        _ ≤ T0 * Real.exp (M * T0) :=
          mul_le_mul_of_nonneg_right htT (le_of_lt (Real.exp_pos _))
    have h_int_nonneg : 0 ≤ ∫ s in (0 : ℝ)..t, Real.exp (G s) :=
      intervalIntegral.integral_nonneg ht0 (fun s hs => le_of_lt (Real.exp_pos _))
    rw [hx_def, hB0_def]
    exact mul_le_mul h_exp_le h_int_le h_int_nonneg (le_of_lt (Real.exp_pos _))
  have hk_le_exp :
      ∀ {T t s : ℝ}, T0 ≤ T → s ∈ Set.Icc T t →
        k t s ≤ Real.exp (-(α / 2) * (t - s)) := by
    intro T t s hT0T hs
    have hmono : ∫ u in s..t, (α / 2 : ℝ) ≤ ∫ u in s..t, g u := by
      apply intervalIntegral.integral_mono_on hs.2
      · exact continuous_const.intervalIntegrable s t
      · exact hg_cont.intervalIntegrable s t
      · intro u hu
        exact hg_lower u (le_trans hT0T hu.1)
    have hconst : ∫ u in s..t, (α / 2 : ℝ) = (α / 2) * (t - s) := by
      simp [mul_comm, mul_left_comm, mul_assoc, sub_eq_add_neg]
    have hneg : -(∫ u in s..t, g u) ≤ -(α / 2) * (t - s) := by
      linarith
    calc
      k t s = Real.exp (-(∫ u in s..t, g u)) := by simp [k, hk_def]
      _ ≤ Real.exp (-(α / 2) * (t - s)) := Real.exp_le_exp.mpr hneg
  have hx_large : ∀ t, T0 ≤ t → x t ≤ B0 + 2 / α := by
    intro t htT
    have hrestart := hx_restart hT0_pos.le htT
    have hk_int : ∫ s in T0..t, k t s ≤ 2 / α := by
      have hint_expdec : IntervalIntegrable (fun s => Real.exp (-(α / 2) * (t - s))) volume T0 t := by
        apply Continuous.intervalIntegrable
        fun_prop
      calc
        ∫ s in T0..t, k t s ≤ ∫ s in T0..t, Real.exp (-(α / 2) * (t - s)) := by
          apply intervalIntegral.integral_mono_on htT
          · exact (hk_cont t).intervalIntegrable T0 t
          · exact hint_expdec
          · intro s hs
            exact hk_le_exp (le_rfl : T0 ≤ T0) hs
        _ ≤ 1 / (α / 2) := integral_exp_decay_le_debug (by positivity) htT
        _ = 2 / α := by field_simp [hα_ne]
    have hk_one : k t T0 ≤ 1 := by
      have h_int_nonneg : 0 ≤ ∫ u in T0..t, g u := by
        apply intervalIntegral.integral_nonneg htT
        intro u hu
        have hlow := hg_lower u hu.1
        linarith
      calc
        k t T0 = Real.exp (-(∫ u in T0..t, g u)) := by simp [k, hk_def]
        _ ≤ Real.exp 0 := Real.exp_le_exp.mpr (by linarith)
        _ = 1 := by simp
    have hxT0 : x T0 ≤ B0 := hx_pre T0 hT0_pos.le le_rfl
    have hxT0_nonneg : 0 ≤ x T0 := hx_nonneg T0 hT0_pos.le
    have hterm1 : k t T0 * x T0 ≤ B0 := by
      calc
        k t T0 * x T0 ≤ 1 * x T0 :=
          mul_le_mul_of_nonneg_right hk_one hxT0_nonneg
        _ ≤ 1 * B0 := by simpa using hxT0
        _ = B0 := by ring
    linarith
  have hB0_nonneg : 0 ≤ B0 := by
    rw [hB0_def]
    positivity
  have hA1_exp : B0 + 3 / α ≤ Real.exp (↑Ninit : ℝ) := by
    have hceil : B0 + 3 / α ≤ Ninit := Nat.le_ceil _
    have hnat : (↑Ninit : ℝ) ≤ Real.exp (↑Ninit : ℝ) := by
      have := Real.add_one_le_exp (↑Ninit : ℝ)
      linarith
    exact le_trans hceil hnat
  have hA2_exp : (2 / α ^ 2 : ℝ) ≤ Real.exp (↑Ntail : ℝ) := by
    have hceil : (2 / α ^ 2 : ℝ) ≤ Ntail := Nat.le_ceil _
    have hnat : (↑Ntail : ℝ) ≤ Real.exp (↑Ntail : ℝ) := by
      have := Real.add_one_le_exp (↑Ntail : ℝ)
      linarith
    exact le_trans hceil hnat
  refine ⟨d + 1, {
    pivp := {
      field := fun v =>
        Fin.snoc (btc.pivp.field (fun j => v (Fin.castSucc j)))
          (1 - v (Fin.castSucc btc.pivp.output) * v (Fin.last d))
      init := Fin.snoc btc.pivp.init 0
      output := Fin.last d }
    sol := {
      trajectory := fun t => Fin.snoc (btc.sol.trajectory t) (x t)
      init_cond := by
        ext i
        refine Fin.lastCases ?_ (fun j => ?_) i
        · simp only [Fin.snoc_last]
          exact hx_zero
        · simp only [Fin.snoc_castSucc]
          exact congr_fun btc.sol.init_cond j
      is_solution := fun t ht => by
        rw [hasDerivAt_pi]
        refine Fin.lastCases ?_ (fun j => ?_)
        · simp only [Fin.snoc_last, Fin.snoc_castSucc]
          have := hx_hd t
          rw [hg_eq t ht] at this
          exact this
        · simp only [Fin.snoc_castSucc]
          exact (hasDerivAt_pi.mp (btc.sol.is_solution t ht)) j }
    modulus := fun r =>
      max T0 (btc.modulus (r + Ntail + 1) + 1) + (2 / α) * (↑r + ↑Ninit + 1)
    bounded := by
      refine ⟨M + (B0 + 2 / α), by positivity, fun t ht => ?_⟩
      rw [pi_norm_le_iff_of_nonneg (by positivity)]
      refine Fin.lastCases ?_ (fun j => ?_)
      · simp only [Fin.snoc_last]
        rw [Real.norm_eq_abs]
        have hx_bound : x t ≤ B0 + 2 / α := by
          by_cases hcase : t ≤ T0
          · exact le_trans (hx_pre t ht hcase) (by positivity)
          · exact hx_large t (le_of_lt (lt_of_not_ge hcase))
        have hx_nn : 0 ≤ x t := hx_nonneg t ht
        rw [abs_of_nonneg hx_nn]
        exact hx_bound
      · simp only [Fin.snoc_castSucc]
        calc
          ‖btc.sol.trajectory t j‖ ≤ ‖btc.sol.trajectory t‖ := norm_le_pi_norm _ _
          _ ≤ M := hbound t ht
          _ ≤ M + (B0 + 2 / α) := by positivity
    convergence := by
      intro r t ht
      simp only [Fin.snoc_last]
      set T : ℝ := max T0 (btc.modulus (r + Ntail + 1) + 1) with hT_def
      have hT0T : T0 ≤ T := by
        rw [hT_def]
        exact le_max_left _ _
      have hT_ge0 : 0 ≤ T := le_trans hT0_pos.le hT0T
      have hTt : T ≤ t := by
        rw [hT_def] at ht
        linarith
      have hT_mod : btc.modulus (r + Ntail + 1) < T := by
        rw [hT_def]
        have : btc.modulus (r + Ntail + 1) < btc.modulus (r + Ntail + 1) + 1 := by linarith
        exact lt_of_lt_of_le this (le_max_right _ _)
      have hclose : ∀ s, T ≤ s → |g s - α| < Real.exp (-(↑(r + Ntail + 1) : ℝ)) := by
        intro s hs
        have hs0 : 0 ≤ s := le_trans hT_ge0 hs
        rw [hg_eq s hs0]
        exact btc.convergence (r + Ntail + 1) s (lt_of_lt_of_le hT_mod hs)
      have hrestart := hx_restart hT_ge0 hTt
      have hk_id := hk_integral hTt
      have hintk : IntervalIntegrable (fun s => k t s) volume T t := (hk_cont t).intervalIntegrable T t
      have hintgk : IntervalIntegrable (fun s => g s * k t s) volume T t :=
        (hg_cont.mul (hk_cont t)).intervalIntegrable T t
      have hcomb :
          (∫ s in T..t, k t s) - (1 / α) * ∫ s in T..t, g s * k t s =
            (1 / α) * ∫ s in T..t, (α - g s) * k t s := by
        have hintscaled : IntervalIntegrable (fun s => (1 / α) * (g s * k t s)) volume T t :=
          hintgk.const_mul _
        have hconstmul :
            (1 / α) * ∫ s in T..t, g s * k t s = ∫ s in T..t, (1 / α) * (g s * k t s) := by
          rw [← intervalIntegral.integral_const_mul]
        calc
          (∫ s in T..t, k t s) - (1 / α) * ∫ s in T..t, g s * k t s
              = ∫ s in T..t, k t s - ∫ s in T..t, (1 / α) * (g s * k t s) := by
                  rw [hconstmul]
          _ = ∫ s in T..t, (k t s - (1 / α) * (g s * k t s)) := by
                  rw [← intervalIntegral.integral_sub hintk hintscaled]
          _ = ∫ s in T..t, (1 / α) * ((α - g s) * k t s) := by
                  apply intervalIntegral.integral_congr
                  intro s hs
                  ring
          _ = (1 / α) * ∫ s in T..t, (α - g s) * k t s := by
                  rw [intervalIntegral.integral_const_mul]
      have herr :
          x t - α⁻¹ =
            k t T * (x T - α⁻¹) + (1 / α) * ∫ s in T..t, (α - g s) * k t s := by
        have hconst : α⁻¹ = k t T * α⁻¹ + (1 / α) * ∫ s in T..t, g s * k t s := by
          calc
            α⁻¹ = (1 / α : ℝ) := by simp
            _ = (1 / α) * (k t T + ∫ s in T..t, g s * k t s) := by
                  rw [hk_id]
                  ring
            _ = k t T * α⁻¹ + (1 / α) * ∫ s in T..t, g s * k t s := by ring
        rw [hrestart, hconst]
        rw [sub_eq_add_neg, hcomb]
        ring
      have herr_abs :
          |x t - α⁻¹| ≤
            k t T * |x T - α⁻¹| + (1 / α) * |∫ s in T..t, (α - g s) * k t s| := by
        have hkT_nonneg : 0 ≤ k t T := by
          simp [k, hk_def]
        have hαinv_nonneg : 0 ≤ (1 / α : ℝ) := by
          positivity
        rw [herr]
        calc
          |k t T * (x T - α⁻¹) + (1 / α) * ∫ s in T..t, (α - g s) * k t s|
              ≤ |k t T * (x T - α⁻¹)| + |(1 / α) * ∫ s in T..t, (α - g s) * k t s| :=
                abs_add_le _ _
          _ = k t T * |x T - α⁻¹| + (1 / α) * |∫ s in T..t, (α - g s) * k t s| := by
                rw [abs_mul, abs_of_nonneg hkT_nonneg, abs_mul, abs_of_nonneg hαinv_nonneg]
      have hkT_le : k t T ≤ Real.exp (-(α / 2) * (t - T)) := by
        exact hk_le_exp hT0T ⟨le_rfl, hTt⟩
      have hxT_bound : x T ≤ B0 + 2 / α := hx_large T hT0T
      have heT_bound : |x T - α⁻¹| ≤ B0 + 3 / α := by
        have hxT_nn : 0 ≤ x T := hx_nonneg T hT_ge0
        have h_inv_nn : 0 ≤ α⁻¹ := le_of_lt (inv_pos.mpr hα_pos)
        calc
          |x T - α⁻¹| ≤ |x T| + |α⁻¹| := by simpa using abs_sub_le (x T) (α⁻¹)
          _ = x T + α⁻¹ := by rw [abs_of_nonneg hxT_nn, abs_of_nonneg h_inv_nn]
          _ ≤ B0 + 2 / α + α⁻¹ := by linarith
          _ = B0 + 3 / α := by
                rw [show α⁻¹ = (1 / α : ℝ) by simp]
                ring
      have hdelay : (α / 2) * (t - T) > ↑r + ↑Ninit + 1 := by
        have : t - T > (2 / α) * (↑r + ↑Ninit + 1) := by
          rw [hT_def] at ht
          linarith
        nlinarith [this, hα_pos]
      have hfirst :
          k t T * |x T - α⁻¹| < Real.exp (-(↑(r + 1) : ℝ)) := by
        calc
          k t T * |x T - α⁻¹|
              ≤ Real.exp (-(α / 2) * (t - T)) * (B0 + 3 / α) :=
                mul_le_mul hkT_le heT_bound (by positivity) (by positivity)
          _ ≤ Real.exp (-(α / 2) * (t - T)) * Real.exp (↑Ninit : ℝ) :=
                mul_le_mul_of_nonneg_left hA1_exp (le_of_lt (Real.exp_pos _))
          _ = Real.exp (-(α / 2) * (t - T) + ↑Ninit) := by rw [← Real.exp_add]
          _ < Real.exp (-(↑(r + 1) : ℝ)) := by
                apply Real.exp_lt_exp.mpr
                nlinarith [hdelay]
      have hk_int : ∫ s in T..t, k t s ≤ 2 / α := by
        have hint_expdec : IntervalIntegrable (fun s => Real.exp (-(α / 2) * (t - s))) volume T t := by
          apply Continuous.intervalIntegrable
          fun_prop
        calc
          ∫ s in T..t, k t s ≤ ∫ s in T..t, Real.exp (-(α / 2) * (t - s)) := by
            apply intervalIntegral.integral_mono_on hTt
            · exact hintk
            · exact hint_expdec
            · intro s hs
              exact hk_le_exp hT0T hs
          _ ≤ 1 / (α / 2) := integral_exp_decay_le_debug (by positivity) hTt
          _ = 2 / α := by field_simp [hα_ne]
      have hforcing :
          |∫ s in T..t, (α - g s) * k t s|
            ≤ Real.exp (-(↑(r + Ntail + 1) : ℝ)) *
                ∫ s in T..t, Real.exp (-(α / 2) * (t - s)) := by
        have hint_abs :
            IntervalIntegrable (fun s => |(α - g s) * k t s|) volume T t := by
          exact ((continuous_const.sub hg_cont).mul (hk_cont t)).norm.intervalIntegrable T t
        have hint_bound :
            IntervalIntegrable
              (fun s =>
                Real.exp (-(↑(r + Ntail + 1) : ℝ)) * Real.exp (-(α / 2) * (t - s)))
              volume T t := by
          apply Continuous.intervalIntegrable
          fun_prop
        calc
          |∫ s in T..t, (α - g s) * k t s|
              ≤ ∫ s in T..t, |(α - g s) * k t s| :=
                intervalIntegral.abs_integral_le_integral_abs hTt
          _ ≤ ∫ s in T..t,
                Real.exp (-(↑(r + Ntail + 1) : ℝ)) * Real.exp (-(α / 2) * (t - s)) := by
                  apply intervalIntegral.integral_mono_on hTt
                  · exact hint_abs
                  · exact hint_bound
                  · intro s hs
                    have hclose_s : |α - g s| < Real.exp (-(↑(r + Ntail + 1) : ℝ)) := by
                      simpa [abs_sub_comm] using hclose s hs.1
                    have hk_s := hk_le_exp hT0T hs
                    have hk_nonneg : 0 ≤ k t s := by
                      simp [k, hk_def]
                    rw [abs_mul, abs_of_nonneg hk_nonneg]
                    exact mul_le_mul (le_of_lt hclose_s) hk_s hk_nonneg
                      (le_of_lt (Real.exp_pos _))
          _ = Real.exp (-(↑(r + Ntail + 1) : ℝ)) *
                ∫ s in T..t, Real.exp (-(α / 2) * (t - s)) := by
                  rw [← intervalIntegral.integral_const_mul]
      have hsecond :
          (1 / α) * |∫ s in T..t, (α - g s) * k t s|
            ≤ Real.exp (-(↑(r + 1) : ℝ)) := by
        calc
          (1 / α) * |∫ s in T..t, (α - g s) * k t s|
              ≤ (1 / α) *
                  (Real.exp (-(↑(r + Ntail + 1) : ℝ)) *
                    ∫ s in T..t, Real.exp (-(α / 2) * (t - s))) :=
                mul_le_mul_of_nonneg_left hforcing (by positivity)
          _ ≤ (1 / α) * (Real.exp (-(↑(r + Ntail + 1) : ℝ)) * (2 / α)) :=
                mul_le_mul_of_nonneg_left
                  (mul_le_mul_of_nonneg_left hk_int (le_of_lt (Real.exp_pos _))) (by positivity)
          _ = (2 / α ^ 2) * Real.exp (-(↑(r + Ntail + 1) : ℝ)) := by
                field_simp [hα_ne]
                ring
          _ ≤ Real.exp (↑Ntail : ℝ) * Real.exp (-(↑(r + Ntail + 1) : ℝ)) :=
                mul_le_mul_of_nonneg_right hA2_exp (le_of_lt (Real.exp_pos _))
          _ = Real.exp (-(↑(r + 1) : ℝ)) := by
                rw [← Real.exp_add]
                congr 1
                push_cast
                ring
      have hexp_two : 2 * Real.exp (-(↑(r + 1) : ℝ)) ≤ Real.exp (-(↑r : ℝ)) := by
        have hcast : (-(↑(r + 1) : ℝ)) = -(↑r : ℝ) + (-1 : ℝ) := by
          push_cast
          ring
        rw [hcast, Real.exp_add]
        have h2e : 2 * Real.exp (-1 : ℝ) ≤ 1 := by
          rw [Real.exp_neg, ← div_eq_mul_inv, div_le_one (Real.exp_pos 1)]
          linarith [Real.add_one_le_exp (1 : ℝ)]
        calc
          2 * (Real.exp (-(↑r : ℝ)) * Real.exp (-1))
              = Real.exp (-(↑r : ℝ)) * (2 * Real.exp (-1)) := by ring
          _ ≤ Real.exp (-(↑r : ℝ)) * 1 :=
                mul_le_mul_of_nonneg_left h2e (le_of_lt (Real.exp_pos _))
          _ = Real.exp (-(↑r : ℝ)) := by ring
      calc
        |x t - α⁻¹|
            ≤ k t T * |x T - α⁻¹| + (1 / α) * |∫ s in T..t, (α - g s) * k t s| := herr_abs
        _ < 2 * Real.exp (-(↑(r + 1) : ℝ)) := by linarith [hfirst, hsecond]
        _ ≤ Real.exp (-(↑r : ℝ)) := hexp_two },
    let Cinv : ℝ :=
      (C + 2 / α) +
        (T0 + (C * (↑Ntail + 2) + 1) + (2 / α) * (↑Ninit + 1))
    refine ⟨Cinv, by
      dsimp [Cinv]
      positivity, ?_⟩
    intro r
    have htail_mod : btc.modulus (r + Ntail + 1) + 1 ≤ C * (↑r + ↑Ntail + 2) + 1 := by
      have hlin := hmod (r + Ntail + 1)
      calc
        btc.modulus (r + Ntail + 1) + 1 ≤ C * ((↑(r + Ntail + 1) : ℝ) + 1) + 1 := by
          linarith
        _ = C * (↑r + ↑Ntail + 2) + 1 := by
          push_cast
          ring
    calc
      max T0 (btc.modulus (r + Ntail + 1) + 1) + (2 / α) * (↑r + ↑Ninit + 1)
          ≤ (T0 + (C * (↑r + ↑Ntail + 2) + 1)) + (2 / α) * (↑r + ↑Ninit + 1) := by
              have hmax :
                  max T0 (btc.modulus (r + Ntail + 1) + 1) ≤ T0 + (C * (↑r + ↑Ntail + 2) + 1) := by
                apply max_le
                · positivity
                · exact le_trans htail_mod (le_add_of_nonneg_left hT0_pos.le)
              linarith
      _ = (C + 2 / α) * ↑r +
            (T0 + (C * (↑Ntail + 2) + 1) + (2 / α) * (↑Ninit + 1)) := by
            ring
      _ ≤ Cinv * (↑r + 1) := by
            dsimp [Cinv]
            nlinarith [Nat.cast_nonneg r]

end Ripple
