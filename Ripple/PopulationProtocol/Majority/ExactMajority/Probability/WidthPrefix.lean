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

end EarlyDripMarked

end ExactMajority
