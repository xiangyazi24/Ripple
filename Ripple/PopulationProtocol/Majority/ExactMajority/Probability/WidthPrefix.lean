/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# WidthPrefix — arbitrary-horizon prefixes of the §6 width engine (Phase B step 3)

The §6 coupled time-window engine (`EarlyDripMarked.lean`) lands its windowed-front recurrence at
checkpoint horizons `τ = w * KK` (a whole number `KK` of windows of length `w`).  Phase B's clock
rewire reads real-kernel prefix events off the SINGLE marked chain per clock run at ARBITRARY minute
boundaries `τ = w * j + r`, `r < w`.  This file supplies the horizon-flexibility layer:

1. `checkpoint_composition_prefix` — the generic invariant-union bound at a window kernel plus a
   terminal remainder block: from per-window failure `δ` and per-remainder failure `δr` (both from
   invariant states), the invariant fails by `w * j + r` with probability at most `j·δ + δr`.  This
   is `EarlyDripMarked.invariant_union_bound`'s split applied to `Kk ^ w` (= `checkpoint_composition`)
   followed by ONE Chapman–Kolmogorov remainder block.

2. `windowedFrontProfile_whp_checkpoint` — the `KK := j` wrapper of `windowedFrontProfile_whp`: the
   SAME theorem at `j ≤ KK` windows, with the scale hypothesis `hsmall` at `w·j` DERIVED from the one
   at `w·KK` (the base `1 + 4/n ≥ 1`, so `j ≤ KK ⟹ (·)^(w·j) ≤ (·)^(w·KK)`).

3. `windowedFrontProfile_whp_prefix` — the remainder version at `τ = w·j + r`, `r < w`, using (1)
   with the marked-kernel recurrence invariant `recInv`.  The `r`-horizon window bound is supplied as
   an INPUT hypothesis `δRem` (the §6 engine fixes the window length `w`; the `r`-horizon analog of
   `window_failure_le`'s `hB` input lives at power `r`, recorded in the campaign file as an input).

4. `goodFrontWidth_whp_at` — the per-`τ` width-bound family: combine (2)/(3) with `climbBound_whp`
   (already horizon-free, free `t`) via `goodFrontWidth_whp` at `t := τ`.

All statements are over the RAW parameters (`θn n cc w …` as in `EarlyDripMarked`), NOT the concrete
`DotyParams` choices (those are owned by a separate line; the concrete-parameter prefix family is a
follow-up there).

Reference: `DOTY_POST63_CAMPAIGN.md`, sections "Phase B step 3 — ARCHITECTURE SETTLED" and
"Phase B step 3 — horizon/start audit results".
-/

import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.EarlyDripMarked

namespace ExactMajority

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace EarlyDripMarked

open ClockRealKernel

variable {L K : ℕ}

/-! ## Deliverable 1 — the generic checkpoint composition with a remainder block.

`checkpoint_composition` bounds the invariant failure at `w * KK` (a whole number of windows).  A
mid-window horizon `τ = w * j + r` (`r < w`, `r` the remainder) needs ONE extra Chapman–Kolmogorov
block: from a `j`-window prefix landing on `{Inv}` w.p. `≥ 1 − j·δ`, the terminal `r`-block from
`{Inv}` fails by `δr`.  The Chapman–Kolmogorov split is the SAME shape as `invariant_union_bound`'s
successor step, with the outer measure `(Kk^(w*j)) x₀` and the inner `r`-block kernel. -/

/-- **The checkpoint composition with a remainder block.**  With per-window failure `δ` and
per-remainder failure `δr` (both from invariant states), the invariant fails by horizon `w * j + r`
with probability at most `j·δ + δr`.  Generic over a Markov kernel `Kk` and a (discrete-measurable)
invariant `Inv`. -/
theorem checkpoint_composition_prefix {α : Type*} [MeasurableSpace α] [DiscreteMeasurableSpace α]
    (Kk : Kernel α α) [IsMarkovKernel Kk] (Inv : α → Prop) (w r : ℕ) (δ δr : ℝ≥0∞)
    (hwindow : ∀ x, Inv x → (Kk ^ w) x {y | ¬ Inv y} ≤ δ)
    (hrem : ∀ x, Inv x → (Kk ^ r) x {y | ¬ Inv y} ≤ δr)
    (j : ℕ) (x₀ : α) (h0 : Inv x₀) :
    (Kk ^ (w * j + r)) x₀ {y | ¬ Inv y} ≤ (j : ℝ≥0∞) * δ + δr := by
  classical
  haveI : ∀ s : ℕ, IsMarkovKernel (Kk ^ s) := by
    intro s
    induction s with
    | zero =>
        rw [pow_zero]
        exact inferInstanceAs (IsMarkovKernel (Kernel.id : Kernel α α))
    | succ s ihs =>
        rw [pow_succ]
        exact inferInstanceAs (IsMarkovKernel ((Kk ^ s) ∘ₖ Kk))
  have hmeas : MeasurableSet {y : α | ¬ Inv y} :=
    DiscreteMeasurableSpace.forall_measurableSet _
  -- the `j`-window prefix failure bound (checkpoint_composition).
  have hprefix : (Kk ^ (w * j)) x₀ {y | ¬ Inv y} ≤ (j : ℝ≥0∞) * δ :=
    checkpoint_composition Kk Inv w δ hwindow j x₀ h0
  -- Chapman–Kolmogorov: split the horizon into the `w*j` prefix and the `r` remainder block.
  have hCK : (Kk ^ (w * j + r)) x₀ {y | ¬ Inv y}
      = ∫⁻ b, (Kk ^ r) b {y | ¬ Inv y} ∂((Kk ^ (w * j)) x₀) :=
    Kernel.pow_add_apply_eq_lintegral Kk (w * j) r x₀ hmeas
  rw [hCK]
  set E0 : Set α := {b | Inv b} with hE0
  have hE0_meas : MeasurableSet E0 := DiscreteMeasurableSpace.forall_measurableSet _
  have hE0c : E0ᶜ = {y : α | ¬ Inv y} := by
    ext b; simp [hE0]
  rw [← lintegral_add_compl _ hE0_meas]
  -- the `{Inv}` part: the remainder block fails by at most `δr`, integrated over a sub-probability.
  have hbound0 : (∫⁻ b in E0, (Kk ^ r) b {y | ¬ Inv y} ∂((Kk ^ (w * j)) x₀)) ≤ δr := by
    calc (∫⁻ b in E0, (Kk ^ r) b {y | ¬ Inv y} ∂((Kk ^ (w * j)) x₀))
        ≤ ∫⁻ _ in E0, δr ∂((Kk ^ (w * j)) x₀) := by
          apply lintegral_mono_ae
          filter_upwards [ae_restrict_mem hE0_meas] with b hb
          exact hrem b hb
      _ ≤ δr := by
          rw [lintegral_const, Measure.restrict_apply_univ]
          haveI : IsProbabilityMeasure ((Kk ^ (w * j)) x₀) :=
            (inferInstance : IsMarkovKernel (Kk ^ (w * j))).isProbabilityMeasure x₀
          calc δr * ((Kk ^ (w * j)) x₀) E0
              ≤ δr * 1 := by
                gcongr
                calc ((Kk ^ (w * j)) x₀) E0 ≤ ((Kk ^ (w * j)) x₀) Set.univ :=
                      measure_mono (Set.subset_univ _)
                  _ = 1 := measure_univ
            _ = δr := mul_one _
  -- the `{¬Inv}` part: the remainder block is at most `1`, integrated over the prefix-failure mass.
  have hbound1 : (∫⁻ b in E0ᶜ, (Kk ^ r) b {y | ¬ Inv y} ∂((Kk ^ (w * j)) x₀))
      ≤ (j : ℝ≥0∞) * δ := by
    calc (∫⁻ b in E0ᶜ, (Kk ^ r) b {y | ¬ Inv y} ∂((Kk ^ (w * j)) x₀))
        ≤ ∫⁻ _ in E0ᶜ, (1 : ℝ≥0∞) ∂((Kk ^ (w * j)) x₀) := by
          apply lintegral_mono_ae
          filter_upwards with b
          haveI : IsProbabilityMeasure ((Kk ^ r) b) :=
            (inferInstance : IsMarkovKernel (Kk ^ r)).isProbabilityMeasure b
          calc (Kk ^ r) b {y | ¬ Inv y}
              ≤ (Kk ^ r) b Set.univ := measure_mono (Set.subset_univ _)
            _ = 1 := measure_univ
      _ = ((Kk ^ (w * j)) x₀) E0ᶜ := by
          rw [lintegral_const, Measure.restrict_apply_univ, one_mul]
      _ = ((Kk ^ (w * j)) x₀) {y | ¬ Inv y} := by rw [hE0c]
      _ ≤ (j : ℝ≥0∞) * δ := hprefix
  calc (∫⁻ b in E0, (Kk ^ r) b {y | ¬ Inv y} ∂((Kk ^ (w * j)) x₀))
        + (∫⁻ b in E0ᶜ, (Kk ^ r) b {y | ¬ Inv y} ∂((Kk ^ (w * j)) x₀))
      ≤ δr + (j : ℝ≥0∞) * δ := add_le_add hbound0 hbound1
    _ = (j : ℝ≥0∞) * δ + δr := by rw [add_comm]

/-! ## Deliverable 2 — the `KK := j` checkpoint wrapper of `windowedFrontProfile_whp`.

`windowedFrontProfile_whp` is stated at a free `KK` (the number of windows); its horizon is `w * KK`.
For a prefix at `j ≤ KK` windows it is the SAME theorem with `KK := j`.  The only hypothesis that
depends on the window count is `hsmall : σ·(1+4/n)^(w·KK) ≤ 1/2`.  At `j ≤ KK` the LHS is SMALLER
(the base `1 + 4/n ≥ 1`, the exponent `w·j ≤ w·KK`), so `hsmall` at `w·j` is DERIVED from the one at
`w·KK`. -/

/-- **The pow-monotone bridge** for `hsmall`: with `0 ≤ σ` and `j ≤ KK`, the scale smallness
`σ·(1+4/n)^(w·KK) ≤ 1/2` implies `σ·(1+4/n)^(w·j) ≤ 1/2` (the base `1 + 4/n ≥ 1`). -/
theorem hsmall_mono (n : ℕ) (σ : ℝ) (hσ : 0 ≤ σ) (w j KK : ℕ) (hjKK : j ≤ KK)
    (hsmall : σ * (1 + 4 / (n : ℝ)) ^ (w * KK) ≤ 1 / 2) :
    σ * (1 + 4 / (n : ℝ)) ^ (w * j) ≤ 1 / 2 := by
  have hbase : (1 : ℝ) ≤ 1 + 4 / (n : ℝ) := by
    have : (0 : ℝ) ≤ 4 / (n : ℝ) := by positivity
    linarith
  have hpow : (1 + 4 / (n : ℝ)) ^ (w * j) ≤ (1 + 4 / (n : ℝ)) ^ (w * KK) :=
    pow_le_pow_right₀ hbase (Nat.mul_le_mul_left w hjKK)
  calc σ * (1 + 4 / (n : ℝ)) ^ (w * j)
      ≤ σ * (1 + 4 / (n : ℝ)) ^ (w * KK) := mul_le_mul_of_nonneg_left hpow hσ
    _ ≤ 1 / 2 := hsmall

open ClockFrontProfile in
/-- **STEP 4 capstone at a free window count `j ≤ KK`** — the `KK := j` checkpoint wrapper of
`windowedFrontProfile_whp`.  The horizon is `w * j`; the scale smallness at `w * j` is derived from
the one at `w * KK` via `hsmall_mono`.  Everything else is `windowedFrontProfile_whp` verbatim at
`KK := j`. -/
theorem windowedFrontProfile_whp_checkpoint (θn n : ℕ) (hn : 2 ≤ n) (cc : ℝ) (w : ℕ) (θ : ℝ)
    (hθpos : 0 < θ) (aM : ℕ → ℕ) (haM : ∀ T, n ≤ 10 * aM T) (δ : ℕ → ℝ≥0∞)
    (hB : ∀ T, ∀ mc₀, recInv (L := L) (K := K) T θn n cc mc₀ →
      AllClockP3 (L := L) (K := K) (eraseConfig (L := L) (K := K) mc₀) →
      10 * rBeyond (L := L) (K := K) T (eraseConfig (L := L) (K := K) mc₀) ≤ n →
      ((markedK (L := L) (K := K) T θn) ^ w) mc₀
          {mc | (cc * (rBeyond (L := L) (K := K) T
                (eraseConfig (L := L) (K := K) mc) : ℝ) ^ 2 / (n : ℝ)
              < (cleanAbove (L := L) (K := K) T mc : ℝ)) ∧
            rBeyond (L := L) (K := K) T (eraseConfig (L := L) (K := K) mc) ≤ aM T ∧
            mc.card = n ∧ AllClockP3 (L := L) (K := K) (eraseConfig (L := L) (K := K) mc)}
        ≤ δ T)
    (σ : ℝ) (hσ : 0 < σ) (j KK : ℕ) (hjKK : j ≤ KK)
    (hsmall : σ * (1 + 4 / (n : ℝ)) ^ (w * KK) ≤ 1 / 2)
    (tt : ℕ) (Tcap : ℕ) (hcap : ClockFrontShape.capMinute (L := L) (K := K) < Tcap)
    (mc₀ : Config (MarkedAgent L K))
    (h0 : ∀ T < Tcap, recInv (L := L) (K := K) T θn n cc mc₀)
    (hmark : ∀ T < Tcap, MarkInv (L := L) (K := K) T mc₀) :
    ((NonuniformMajority L K).transitionKernel ^ (w * j)) (eraseConfig (L := L) (K := K) mc₀)
        {c | (c.card = n ∧ AllClockP3 (L := L) (K := K) c ∧
            (∀ T, θ ≤ ClockFrontProfile.frac (L := L) (K := K) T c →
              cc * (rBeyond (L := L) (K := K) T c : ℝ) ^ 2 / (n : ℝ) + (tt : ℝ)
                ≤ (rBeyond (L := L) (K := K) T c : ℝ) ^ 2 / (n : ℝ)))
          ∧ ¬ WindowedFrontProfile (L := L) (K := K) θ c}
      ≤ ∑ T ∈ Finset.range Tcap,
          ((j : ℝ≥0∞) * δ T
            + ((GatedDrift.killK (markedK (L := L) (K := K) T θn)
                (taintedGate (L := L) (K := K) n) ^ (w * j)) (some mc₀) {none}
              + ENNReal.ofReal
                (Real.exp (σ * (1 + 4 / (n : ℝ)) ^ (w * j)
                    * (taintedCount (L := L) (K := K) mc₀ : ℝ)
                  + 2 * σ * (1 + 4 / (n : ℝ)) ^ (w * j) * ((θn : ℝ) / (n : ℝ)) ^ 2
                      * ((w * j : ℕ) : ℝ)
                  - σ * ((tt + 1 : ℕ) : ℝ))))) :=
  windowedFrontProfile_whp (L := L) (K := K) θn n hn cc w θ hθpos aM haM δ hB σ hσ j
    (hsmall_mono n σ hσ.le w j KK hjKK hsmall) tt Tcap hcap mc₀ h0 hmark

/-! ## Deliverable 3 — the remainder version at `τ = w·j + r`, `r < w`.

The §6 engine lands at whole-window horizons `w·KK`.  A mid-window minute boundary `τ = w·j + r`
needs the recurrence-checkpoint failure at `w·j + r`, which `checkpoint_composition_prefix` supplies
from the per-window failure (`window_failure_le` at power `w`, the existing engine) plus an
`r`-horizon remainder window bound.  The engine genuinely fixes the window length `w`, so the
`r`-horizon analog of `window_failure_le`'s `hB` lives at power `r` and is taken as an INPUT
hypothesis `δRem` (exactly as the campaign file's horizon/start audit records).  The taint tail
(`tainted_marked_tail_explicit`) and the MarkInv null (`markInv_ae_pow`) are already
horizon-parametric (free `t`), so they instantiate at `t := w·j + r` directly. -/

/-- **STEP 3 capstone at horizon `w·j + r`** — the marked-world per-level recurrence whp at a prefix
horizon.  Mirrors `front_squares_whp` but bounds the `{¬recInv}` mass with
`checkpoint_composition_prefix` (per-window `δ` via `window_failure_le`/`hB`, per-remainder `δRem` as
input).  The taint tail and the MarkInv null are at the prefix horizon `w·j + r`. -/
theorem front_squares_whp_prefix (T θn n : ℕ) (hn : 2 ≤ n) (cc : ℝ) (w r aM : ℕ)
    (haM : n ≤ 10 * aM) (δ δRem : ℝ≥0∞)
    (hB : ∀ mc₀, recInv (L := L) (K := K) T θn n cc mc₀ →
      AllClockP3 (L := L) (K := K) (eraseConfig (L := L) (K := K) mc₀) →
      10 * rBeyond (L := L) (K := K) T (eraseConfig (L := L) (K := K) mc₀) ≤ n →
      ((markedK (L := L) (K := K) T θn) ^ w) mc₀
          {mc | (cc * (rBeyond (L := L) (K := K) T
                (eraseConfig (L := L) (K := K) mc) : ℝ) ^ 2 / (n : ℝ)
              < (cleanAbove (L := L) (K := K) T mc : ℝ)) ∧
            rBeyond (L := L) (K := K) T (eraseConfig (L := L) (K := K) mc) ≤ aM ∧
            mc.card = n ∧ AllClockP3 (L := L) (K := K) (eraseConfig (L := L) (K := K) mc)}
        ≤ δ)
    -- the `r`-horizon remainder window bound (INPUT, per the campaign audit):
    (hRem : ∀ mc₀, recInv (L := L) (K := K) T θn n cc mc₀ →
      ((markedK (L := L) (K := K) T θn) ^ r) mc₀
          {mc | ¬ recInv (L := L) (K := K) T θn n cc mc} ≤ δRem)
    (σ : ℝ) (hσ : 0 < σ) (j : ℕ)
    (hsmall : σ * (1 + 4 / (n : ℝ)) ^ (w * j + r) ≤ 1 / 2)
    (tt : ℕ)
    (mc₀ : Config (MarkedAgent L K))
    (h0 : recInv (L := L) (K := K) T θn n cc mc₀)
    (hmark : MarkInv (L := L) (K := K) T mc₀) :
    ((markedK (L := L) (K := K) T θn) ^ (w * j + r)) mc₀
        {mc | (mc.card = n ∧
            AllClockP3 (L := L) (K := K) (eraseConfig (L := L) (K := K) mc) ∧
            10 * rBeyond (L := L) (K := K) T (eraseConfig (L := L) (K := K) mc) ≤ n ∧
            cc * (rBeyond (L := L) (K := K) T (eraseConfig (L := L) (K := K) mc) : ℝ) ^ 2 / (n : ℝ)
                + (tt : ℝ)
              ≤ (rBeyond (L := L) (K := K) T (eraseConfig (L := L) (K := K) mc) : ℝ) ^ 2 / (n : ℝ))
          ∧ ¬ ((rBeyond (L := L) (K := K) (T + 1) (eraseConfig (L := L) (K := K) mc) : ℝ) * (n : ℝ)
            ≤ (rBeyond (L := L) (K := K) T (eraseConfig (L := L) (K := K) mc) : ℝ) ^ 2)}
      ≤ ((j : ℝ≥0∞) * δ + δRem)
        + ((GatedDrift.killK (markedK (L := L) (K := K) T θn)
            (taintedGate (L := L) (K := K) n) ^ (w * j + r)) (some mc₀) {none}
          + ENNReal.ofReal
            (Real.exp (σ * (1 + 4 / (n : ℝ)) ^ (w * j + r)
                * (taintedCount (L := L) (K := K) mc₀ : ℝ)
              + 2 * σ * (1 + 4 / (n : ℝ)) ^ (w * j + r) * ((θn : ℝ) / (n : ℝ)) ^ 2
                  * ((w * j + r : ℕ) : ℝ)
              - σ * ((tt + 1 : ℕ) : ℝ)))) := by
  classical
  set bad : Set (Config (MarkedAgent L K)) :=
    {mc | (mc.card = n ∧
        AllClockP3 (L := L) (K := K) (eraseConfig (L := L) (K := K) mc) ∧
        10 * rBeyond (L := L) (K := K) T (eraseConfig (L := L) (K := K) mc) ≤ n ∧
        cc * (rBeyond (L := L) (K := K) T (eraseConfig (L := L) (K := K) mc) : ℝ) ^ 2 / (n : ℝ)
            + (tt : ℝ)
          ≤ (rBeyond (L := L) (K := K) T (eraseConfig (L := L) (K := K) mc) : ℝ) ^ 2 / (n : ℝ))
      ∧ ¬ ((rBeyond (L := L) (K := K) (T + 1) (eraseConfig (L := L) (K := K) mc) : ℝ) * (n : ℝ)
        ≤ (rBeyond (L := L) (K := K) T (eraseConfig (L := L) (K := K) mc) : ℝ) ^ 2)}
    with hbad
  have hsub : bad ⊆ {mc | ¬ recInv (L := L) (K := K) T θn n cc mc} ∪
      ({mc | tt + 1 ≤ taintedCount (L := L) (K := K) mc} ∪
        {mc | ¬ MarkInv (L := L) (K := K) T mc}) := by
    intro mc hmc
    rw [hbad, Set.mem_setOf_eq] at hmc
    obtain ⟨hwin, hns⟩ := hmc
    rcases front_bad_subset (L := L) (K := K) T θn n (by omega) cc tt mc hwin hns with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  refine le_trans (measure_mono hsub) ?_
  refine le_trans (measure_union_le _ _) ?_
  refine add_le_add ?_ ?_
  · -- the recurrence-checkpoint-prefix failure ≤ j·δ + δRem.
    exact checkpoint_composition_prefix (markedK (L := L) (K := K) T θn)
      (recInv (L := L) (K := K) T θn n cc) w r δ δRem
      (fun mc hmc => window_failure_le (L := L) (K := K) T θn n cc w aM haM δ mc hmc
        (fun hP3 hX => hB mc hmc hP3 hX))
      (fun mc hmc => hRem mc hmc)
      j mc₀ h0
  · refine le_trans (measure_union_le _ _) ?_
    have hmarknull : ((markedK (L := L) (K := K) T θn) ^ (w * j + r)) mc₀
        {mc | ¬ MarkInv (L := L) (K := K) T mc} = 0 := by
      have h := markInv_ae_pow (L := L) (K := K) T θn (w * j + r) mc₀ hmark
      rwa [MeasureTheory.ae_iff] at h
    rw [hmarknull, add_zero]
    exact tainted_marked_tail_explicit (L := L) (K := K) T θn n hn σ hσ (w * j + r)
      hsmall mc₀ (tt + 1)

/-- **STEP 4 — the real-kernel per-level transfer at horizon `w·j + r`.**  The `front_squares_whp_prefix`
bound transfers to the real kernel verbatim (the bad event is erase-measurable, via
`markedK_pow_erase`). -/
theorem real_front_squares_whp_prefix (T θn n : ℕ) (hn : 2 ≤ n) (cc : ℝ) (w r aM : ℕ)
    (haM : n ≤ 10 * aM) (δ δRem : ℝ≥0∞)
    (hB : ∀ mc₀, recInv (L := L) (K := K) T θn n cc mc₀ →
      AllClockP3 (L := L) (K := K) (eraseConfig (L := L) (K := K) mc₀) →
      10 * rBeyond (L := L) (K := K) T (eraseConfig (L := L) (K := K) mc₀) ≤ n →
      ((markedK (L := L) (K := K) T θn) ^ w) mc₀
          {mc | (cc * (rBeyond (L := L) (K := K) T
                (eraseConfig (L := L) (K := K) mc) : ℝ) ^ 2 / (n : ℝ)
              < (cleanAbove (L := L) (K := K) T mc : ℝ)) ∧
            rBeyond (L := L) (K := K) T (eraseConfig (L := L) (K := K) mc) ≤ aM ∧
            mc.card = n ∧ AllClockP3 (L := L) (K := K) (eraseConfig (L := L) (K := K) mc)}
        ≤ δ)
    (hRem : ∀ mc₀, recInv (L := L) (K := K) T θn n cc mc₀ →
      ((markedK (L := L) (K := K) T θn) ^ r) mc₀
          {mc | ¬ recInv (L := L) (K := K) T θn n cc mc} ≤ δRem)
    (σ : ℝ) (hσ : 0 < σ) (j : ℕ)
    (hsmall : σ * (1 + 4 / (n : ℝ)) ^ (w * j + r) ≤ 1 / 2)
    (tt : ℕ)
    (mc₀ : Config (MarkedAgent L K))
    (h0 : recInv (L := L) (K := K) T θn n cc mc₀)
    (hmark : MarkInv (L := L) (K := K) T mc₀) :
    ((NonuniformMajority L K).transitionKernel ^ (w * j + r))
        (eraseConfig (L := L) (K := K) mc₀)
        (realFrontBad (L := L) (K := K) T n cc tt)
      ≤ ((j : ℝ≥0∞) * δ + δRem)
        + ((GatedDrift.killK (markedK (L := L) (K := K) T θn)
            (taintedGate (L := L) (K := K) n) ^ (w * j + r)) (some mc₀) {none}
          + ENNReal.ofReal
            (Real.exp (σ * (1 + 4 / (n : ℝ)) ^ (w * j + r)
                * (taintedCount (L := L) (K := K) mc₀ : ℝ)
              + 2 * σ * (1 + 4 / (n : ℝ)) ^ (w * j + r) * ((θn : ℝ) / (n : ℝ)) ^ 2
                  * ((w * j + r : ℕ) : ℝ)
              - σ * ((tt + 1 : ℕ) : ℝ)))) := by
  rw [← markedK_pow_erase (L := L) (K := K) T θn (w * j + r) mc₀
    (realFrontBad (L := L) (K := K) T n cc tt),
    ← markedFrontBad_eq_preimage (L := L) (K := K) T n cc tt]
  exact front_squares_whp_prefix (L := L) (K := K) T θn n hn cc w r aM haM δ δRem hB hRem
    σ hσ j hsmall tt mc₀ h0 hmark

end EarlyDripMarked

end ExactMajority
