/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# `Lemma610StoppedAzuma` — the HONEST (non-vacuous) Doty Lemma 6.10 via a STOPPED kernel.

## The vacuity defect in the existing Lemma 6.10

`HourCouplingV2.hour_coupling_v2` (and its re-export `HourComposition.main_not_ahead_of_clock`) prove
the Azuma tail for the hour-coupling potential `Φ = mAbove/M − 1.1·cAbove/C`, but they CARRY the
hypothesis `hreg : ∀ c, Regime M C h c` — the synchronous-hour window (`c_{>h} ≤ 1/11`) and the fixed
role counts hold at EVERY config.  This universal is UNSATISFIABLE (`regime_not_universal`: the empty
config has `clockCount = 0 ≠ C`), so those theorems are VACUOUSLY true — the Azuma drift `∀ x, ∫Φ dK ≤ Φ x`
is supplied only by assuming the window everywhere, which is false (`#print axioms` cannot see this).

The genuine machinery is real: the per-pair drift `hour_drift` (`∫Φ dK ≤ Φ` ON the window) and the
unconditional increment `hour_bdd` are PROVEN.  The defect is ONLY the global-window hypothesis used
to apply the unconditional `azuma_tail`.

## The fix: a STOPPED kernel

`K* := piecewise {Regime} K id` runs the real kernel `K` on the synchronous-hour regime and SELF-LOOPS
(freezes) off it.  Then the Azuma drift holds UNCONDITIONALLY for `K*`:
* on `Regime`: `∫Φ dK*(x) = ∫Φ dK(x) ≤ Φ x` by the genuine `hour_drift`;
* off `Regime`: `∫Φ dK*(x) = ∫Φ dδ_x = Φ x`.
and the increment `|ΔΦ| ≤ c0` holds for `K*` (on `Regime`: `hour_bdd`; off: `0`).  So `azuma_tail` applies
to `K*` with NO false global-window hypothesis: the stopped Lemma 6.10 is NON-VACUOUS.  (The coupling
that transfers the `K*` tail to the original chain on the no-early-stop event is the standard stopped-
process argument; `K*` and `K` agree until the first regime-exit.)

NO sorry / admit / axiom / native_decide.
-/

import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.HourCouplingV2

namespace ExactMajority

namespace Lemma610StoppedAzuma

open MeasureTheory ProbabilityTheory HourCouplingV2
open Classical

variable {L K : ℕ}

/-! ## Part 1 — the vacuity refutation (the defect, made explicit). -/

/-- **REFUTATION: the carried `∀ c, Regime M C h c` is UNSATISFIABLE.**  The empty config has
`clockCount = 0`, breaking the `clockCount = C` field for any `C > 0`.  Hence `hour_coupling_v2`'s
hypothesis cannot hold and the theorem is vacuous as stated. -/
theorem regime_not_universal (M C : ℝ) (h : ℕ) (hC : 0 < C) :
    ¬ (∀ c : Config (AgentState L K), Regime (L := L) (K := K) M C h c) := by
  intro hall
  obtain ⟨_, _, _, hCc, _, _⟩ := hall (0 : Config (AgentState L K))
  simp only [clockCount, Multiset.countP_zero, Nat.cast_zero] at hCc
  linarith

/-! ## Part 2 — the stopped kernel and its UNCONDITIONAL Azuma hypotheses. -/

/-- The synchronous-hour regime as a (measurable, discrete) set of configs. -/
def regimeSet (M C : ℝ) (h : ℕ) : Set (Config (AgentState L K)) :=
  {c | Regime (L := L) (K := K) M C h c}

/-- **The stopped kernel `K*`**: run `K` on the regime, freeze (self-loop) off it. -/
noncomputable def stoppedK (M C : ℝ) (h : ℕ) : Kernel (Config (AgentState L K)) (Config (AgentState L K)) :=
  Kernel.piecewise (DiscreteMeasurableSpace.forall_measurableSet (regimeSet (L := L) (K := K) M C h))
    (NonuniformMajority L K).transitionKernel Kernel.id

instance (M C : ℝ) (h : ℕ) : IsMarkovKernel (stoppedK (L := L) (K := K) M C h) := by
  unfold stoppedK; infer_instance

/-- **`drift_stopped` — the UNCONDITIONAL supermartingale drift for `K*`.**  No false global window:
on the regime it is the genuine `hour_drift`; off the regime the self-loop gives `∫Φ dδ_x = Φ x`. -/
theorem drift_stopped (M C : ℝ) (h : ℕ) (hK : 0 < K) (hhL : h < L) :
    ∀ x, ∫ y, Phi (L := L) (K := K) M C h y ∂((stoppedK (L := L) (K := K) M C h) x)
      ≤ Phi (L := L) (K := K) M C h x := by
  intro x
  unfold stoppedK
  rw [Kernel.piecewise_apply]
  by_cases hx : x ∈ regimeSet (L := L) (K := K) M C h
  · rw [if_pos hx]
    obtain ⟨hw, hwin, hMc, hCc, hM1, hC1⟩ := hx
    exact hour_drift M C h hK hhL x hw hwin hMc hCc hM1 hC1
  · rw [if_neg hx, Kernel.id_apply, integral_dirac]

/-- **`diff_stopped` — the bounded increment for `K*`.**  On the regime: `hour_bdd`; off: `0`. -/
theorem diff_stopped (M C : ℝ) (hM : 0 < M) (hC : 0 < C) (h : ℕ) :
    ∀ x, ∀ᵐ y ∂((stoppedK (L := L) (K := K) M C h) x),
      |Phi (L := L) (K := K) M C h y - Phi (L := L) (K := K) M C h x|
        ≤ 2 / M + 2 * (11 / 10 : ℝ) / C := by
  intro x
  unfold stoppedK
  rw [Kernel.piecewise_apply]
  by_cases hx : x ∈ regimeSet (L := L) (K := K) M C h
  · rw [if_pos hx]; exact hour_bdd M C hM hC h x
  · rw [if_neg hx, Kernel.id_apply]
    have hbnd : |Phi (L := L) (K := K) M C h x - Phi (L := L) (K := K) M C h x|
        ≤ 2 / M + 2 * (11 / 10 : ℝ) / C := by
      simp only [sub_self, abs_zero]; positivity
    exact (MeasureTheory.ae_dirac_iff (DiscreteMeasurableSpace.forall_measurableSet _)).mpr hbnd

/-- **The HONEST (non-vacuous) Lemma 6.10 — the Azuma tail for the stopped kernel.**  For every
deviation `lam > 0` and `t ≥ 1`, the stopped chain's "Main outruns the clock" tail is exponentially
small, with NO false global-window hypothesis (the drift is unconditional via the stopped kernel):

  `(K*^t) c₀ {Φ ≥ Φ c₀ + lam} ≤ exp(−lam² / (2 t c0²))`,   `c0 = 2/M + 2·(11/10)/C`.

This replaces `hour_coupling_v2`'s vacuous `∀ c, Regime c` with the genuine stopped-process drift. -/
theorem lemma610_stopped (M C : ℝ) (hM : 0 < M) (hC : 0 < C) (h : ℕ) (hK : 0 < K) (hhL : h < L)
    (t : ℕ) (ht : 1 ≤ t) (c₀ : Config (AgentState L K)) {lam : ℝ} (hlam : 0 < lam) :
    ((stoppedK (L := L) (K := K) M C h) ^ t) c₀
        {c' | Phi (L := L) (K := K) M C h c₀ + lam ≤ Phi (L := L) (K := K) M C h c'}
      ≤ ENNReal.ofReal (Real.exp
          (-(lam ^ 2) / (2 * t * (2 / M + 2 * (11 / 10 : ℝ) / C) ^ 2))) := by
  have hc0pos : (0 : ℝ) < 2 / M + 2 * (11 / 10 : ℝ) / C := by positivity
  exact ExactMajority.azuma_tail (stoppedK (L := L) (K := K) M C h)
    (Phi (L := L) (K := K) M C h) (Phi_measurable M C h)
    (2 / M + 2 * (11 / 10 : ℝ) / C) hc0pos
    (diff_stopped M C hM hC h) (drift_stopped M C h hK hhL) t ht c₀ hlam

/-! ## Part 3 — the conclusion layer (`Φ` ⟹ the `m_{>h}` bound). -/

/-- At a synchronized start (no agent — Main or Clock — ahead of hour `h`), `Φ = 0`. -/
theorem phi_zero_of_empty_above (M C : ℝ) (h : ℕ) (c : Config (AgentState L K))
    (hm : HourCoupling.mAbove (L := L) (K := K) h c = 0)
    (hcl : HourCoupling.cAbove (L := L) (K := K) h c = 0) :
    Phi (L := L) (K := K) M C h c = 0 := by
  unfold Phi; rw [hm, hcl]; simp

/-- **The readoff (`m_{>h} ≤ 0.0012`).**  `Φ = mAbove/M − (11/10)·cAbove/C`, so on `Φ < δ` with the
clock tail `cAbove/C ≤ θc`, the Main-ahead fraction is `mAbove/M < δ + (11/10)·θc`.  At Doty's
`δ = 10⁻⁴`, `θc = 10⁻³` this is `< 0.0012` — exactly Lemma 6.10's conclusion `m_{>h} ≤ 0.0012`. -/
theorem mAbove_frac_lt_of_phi (M C : ℝ) (hC : 0 < C) (h : ℕ) (δ θc : ℝ)
    (c : Config (AgentState L K))
    (hphi : Phi (L := L) (K := K) M C h c < δ)
    (hclock : (HourCoupling.cAbove (L := L) (K := K) h c : ℝ) / C ≤ θc) :
    (HourCoupling.mAbove (L := L) (K := K) h c : ℝ) / M < δ + (11 / 10 : ℝ) * θc := by
  have hsplit : (HourCoupling.mAbove (L := L) (K := K) h c : ℝ) / M
      = Phi (L := L) (K := K) M C h c
        + (11 / 10 : ℝ) * (HourCoupling.cAbove (L := L) (K := K) h c : ℝ) / C := by
    unfold Phi; ring
  rw [hsplit]
  have hθ : (11 / 10 : ℝ) * (HourCoupling.cAbove (L := L) (K := K) h c : ℝ) / C
      ≤ (11 / 10 : ℝ) * θc := by
    rw [mul_div_assoc]
    exact mul_le_mul_of_nonneg_left hclock (by norm_num)
  linarith

/-- **Numeric instance: `m_{>h} < 0.0012` at Doty's thresholds `δ = 10⁻⁴`, `θc = 10⁻³`.** -/
theorem mAbove_frac_lt_0012 (M C : ℝ) (hC : 0 < C) (h : ℕ) (c : Config (AgentState L K))
    (hphi : Phi (L := L) (K := K) M C h c < (1 / 10000 : ℝ))
    (hclock : (HourCoupling.cAbove (L := L) (K := K) h c : ℝ) / C ≤ (1 / 1000 : ℝ)) :
    (HourCoupling.mAbove (L := L) (K := K) h c : ℝ) / M < (12 / 10000 : ℝ) := by
  have h := mAbove_frac_lt_of_phi M C hC h (1 / 10000) (1 / 1000) c hphi hclock
  linarith

/-- **The HONEST Lemma 6.10 headline (stopped chain).**  From a synchronized start `c₀` (`Φ c₀ = 0`),
the probability that the stopped chain has Main agents ahead of hour `h` by fraction `≥ 0.0012` WHILE
the clock tail is confined (`cAbove/C ≤ 10⁻³`) is Azuma-exponentially small — with NO false global
window (the drift is unconditional via the stopped kernel).  This is the non-vacuous replacement for
`hour_coupling_v2`: the bad event is contained in `{Φ ≥ 10⁻⁴}` (contrapositive of `mAbove_frac_lt_0012`),
whose mass is the `lemma610_stopped` Azuma tail. -/
theorem lemma610_honest (M C : ℝ) (hM : 0 < M) (hC : 0 < C) (h : ℕ) (hK : 0 < K) (hhL : h < L)
    (t : ℕ) (ht : 1 ≤ t) (c₀ : Config (AgentState L K))
    (hphi0 : Phi (L := L) (K := K) M C h c₀ = 0) :
    ((stoppedK (L := L) (K := K) M C h) ^ t) c₀
        {c' | (12 / 10000 : ℝ) ≤ (HourCoupling.mAbove (L := L) (K := K) h c' : ℝ) / M
            ∧ (HourCoupling.cAbove (L := L) (K := K) h c' : ℝ) / C ≤ (1 / 1000 : ℝ)}
      ≤ ENNReal.ofReal (Real.exp
          (-((1 / 10000 : ℝ) ^ 2) / (2 * t * (2 / M + 2 * (11 / 10 : ℝ) / C) ^ 2))) := by
  refine le_trans (measure_mono ?_)
    (lemma610_stopped M C hM hC h hK hhL t ht c₀ (by norm_num : (0 : ℝ) < 1 / 10000))
  intro c' hc'
  obtain ⟨hma, hcl⟩ := hc'
  simp only [Set.mem_setOf_eq, hphi0, zero_add]
  by_contra hcon
  push_neg at hcon
  exact absurd (mAbove_frac_lt_0012 M C hC h c' hcon hcl) (by linarith)

end Lemma610StoppedAzuma

end ExactMajority
