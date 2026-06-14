/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# `ClockLayerBWindow` — the markedK per-window `WindowCleanGood`/`Lemma63Bad` composition.

Final-wiring step (mechanical): compose the verified pieces into the markedK per-window bound that
`ClockLayerD.windowBadMass_le` consumes as `hwin`.

* `windowClean_markedK_le` — `(markedK^Lwin) {¬ WindowCleanGood} ≤ εParent + εAmp`, from the
  contrapositive of `windowCleanGood_of_amp_budget` (item-1 subsumption: `WindowCleanGood` is witnessed
  by `immFrac = b·p·X(mc₀)²` once parent growth + amplification hold) — so `{¬WindowCleanGood}` splits
  into `{¬ParentGrowthGood}` (Janson, `parent_growth_forward`) and `AmpBadSetBudget` (item-2
  amplification on `markedK` via the gate-exit `amp_marked_tail_from_stopped_and_exit`).

The amplification allowance is fixed at `b·p·X(mc₀)² = (19/200)·p·X(mc₀)²` and the constants are the
verified w=0.09 set (`a=213/250, b=19/200, γ=6/5`), matching `lemma63_composition_algebra_w009`.

NEW file; no existing file edited; no sorry/admit/axiom/native_decide.
Reference: `DOCTRINE_THM69_CA.md` Round 3/4 (Layer-B composition); Doty et al. (arXiv:2106.10201v2).
-/

import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.ClockStoppedTransfer

namespace ExactMajority

namespace ClockLayerB

open MeasureTheory ProbabilityTheory
open ClockRealKernel EarlyDripMarked ClockFrontMixed ClockTaintMixed
open ClockStoppedTransfer
open scoped ENNReal NNReal Real BigOperators

variable {L K : ℕ}

/-- **`windowClean_markedK_le` — the markedK `¬ WindowCleanGood` bound.**  By the contrapositive of
`windowCleanGood_of_amp_budget` (with `a=213/250, b=19/200, γ=6/5`, `immFrac=(19/200)·p·X(mc₀)²`),
`{¬ WindowCleanGood}` is contained in `{¬ ParentGrowthGood} ∪ AmpBadSetBudget`; so the markedK mass is
bounded by the Janson parent-growth failure `εParent` plus the amplification-on-markedK failure `εAmp`
(supplied by `amp_marked_tail_from_stopped_and_exit` = item-2 stopped tail + gate-exit). -/
theorem windowClean_markedK_le (T θn C₀ Lwin : ℕ) (p : ℝ) (mc₀ : MCfg L K)
    (hp0 : 0 ≤ p) (εParent εAmp : ℝ≥0∞)
    (hParent :
      ((markedK (L := L) (K := K) T θn) ^ Lwin) mc₀
        {mc₁ | ¬ ParentGrowthGood (L := L) (K := K) C₀ T (213 / 250 : ℝ) mc₀ mc₁} ≤ εParent)
    (hAmp :
      ((markedK (L := L) (K := K) T θn) ^ Lwin) mc₀
        (AmpBadSetBudget (L := L) (K := K) C₀ T (6 / 5 : ℝ) mc₀
          ((19 / 200 : ℝ) * p * (X (L := L) (K := K) C₀ T mc₀) ^ 2)) ≤ εAmp) :
    ((markedK (L := L) (K := K) T θn) ^ Lwin) mc₀
      {mc₁ | ¬ WindowCleanGood (L := L) (K := K) C₀ T p (19 / 200 : ℝ) (6 / 5 : ℝ) mc₀ mc₁}
      ≤ εParent + εAmp := by
  classical
  refine le_trans (measure_mono ?_) (le_trans (measure_union_le _ _) (add_le_add hParent hAmp))
  intro mc₁ hbad
  by_cases hpar : ParentGrowthGood (L := L) (K := K) C₀ T (213 / 250 : ℝ) mc₀ mc₁
  · right
    intro hamp
    exact hbad
      (windowCleanGood_of_amp_budget (L := L) (K := K) C₀ T p
        (213 / 250 : ℝ) (19 / 200 : ℝ) (6 / 5 : ℝ) mc₀ mc₁
        hp0 (by norm_num) (by norm_num) (by norm_num) hpar hamp)
  · left
    exact hpar

/-- **`lemma63Bad_markedK_le` — the markedK per-window `Lemma63Bad` bound = ClockLayerD's `hwin`.**
Feeds `windowClean_markedK_le` (the `¬WindowCleanGood` bound) into the proven union shell
`lemma63_window_transfer_forward`, closing the per-active-start Layer-B endpoint failure on the REAL
marked kernel.  The amplification term `εAmp` is supplied by `amp_marked_tail_from_stopped_and_exit`
(item-2 stopped tail + gate-exit); `εParent` by `parent_growth_forward` (Janson). This is exactly the
shape `ClockLayerD.windowBadMass_le` consumes. -/
theorem lemma63Bad_markedK_le (T θn C₀ Lwin : ℕ) (p θ ρ η : ℝ) (Aux : MCfg L K → Prop)
    (mc₀ : MCfg L K)
    (hActive : Active63 (L := L) (K := K) C₀ T θ ρ η Aux mc₀)
    (hp : 0 ≤ p)
    (hclean₀ :
      CleanFrac (L := L) (K := K) C₀ T mc₀ ≤
        (9 / 10 : ℝ) * p * (X (L := L) (K := K) C₀ T mc₀) ^ 2)
    (εParent εAmp : ℝ≥0∞)
    (hParent :
      ((markedK (L := L) (K := K) T θn) ^ Lwin) mc₀
        {mc₁ | ¬ ParentGrowthGood (L := L) (K := K) C₀ T (213 / 250 : ℝ) mc₀ mc₁} ≤ εParent)
    (hAmp :
      ((markedK (L := L) (K := K) T θn) ^ Lwin) mc₀
        (AmpBadSetBudget (L := L) (K := K) C₀ T (6 / 5 : ℝ) mc₀
          ((19 / 200 : ℝ) * p * (X (L := L) (K := K) C₀ T mc₀) ^ 2)) ≤ εAmp) :
    ((markedK (L := L) (K := K) T θn) ^ Lwin) mc₀
      {mc₁ | Lemma63Bad (L := L) (K := K) C₀ T p mc₁}
      ≤ εParent + (εParent + εAmp) :=
  lemma63_window_transfer_forward (L := L) (K := K) T θn C₀ Lwin p θ ρ η Aux
    εParent (εParent + εAmp) (εParent + (εParent + εAmp)) mc₀ hActive hp hclean₀
    hParent
    (windowClean_markedK_le (L := L) (K := K) T θn C₀ Lwin p mc₀ hp εParent εAmp hParent hAmp)
    (le_refl _)

end ClockLayerB

end ExactMajority
