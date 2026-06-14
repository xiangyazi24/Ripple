/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# `ClockLayerD` — the Layer-D window-bad finite-union aggregation (DOCTRINE Round 4).

The front-shape first-exit is bounded by a FINITE UNION over `(level, window-start)` pairs of the
Layer-B window-bad mass — NOT a level-by-level stopping chain (painful in Lean: optionals/minimality
/overlap), per the Round-4 family2 resolution.  Each window-bad term is the mass of the Lemma-6.3
endpoint failure `Lemma63Bad` over a window of `Lwin` marked steps starting from an `Active63`
config, integrated over the chain up to the window start.  This file provides:

* `windowBadMass` — the per-`(level T, start s)` window-bad mass
  `∫ 1_{Active63}·((markedK T θn)^Lwin · {Lemma63Bad}) d((markedK T θn)^s mc₀)`;
* `windowBadMass_le` — each term `≤ εWindow`, from the carried per-active-state window bound
  (supplied by `ClockLayerB.lemma63_window_transfer_forward`, whose own probabilistic inputs are the
  Bennett immigration + MGF amplification);
* `windowBad_aggregate` / `windowBad_aggregate_levels` — the single- and double-sum union bound
  `∑ ≤ card · εWindow`, the Layer-D budget `leadingLevels.card · (H+1−Lwin) · εWindow`.

The carried `hwin` is EXACTLY `lemma63_window_transfer_forward`'s conclusion (per active start), so
this aggregation is interface-stable: whatever the Bennett/MGF discharge produces for the per-window
`εWindow`, the union budget is `(#levels)·(#starts)·εWindow`.  NO false ∀c — `hwin` is the proven
per-window transfer, quantified only over the `Active63` (state-local) start configs.

NEW file; no existing file edited; no sorry/admit/axiom/native_decide.
Reference: `DOCTRINE_THM69_CA.md` Round 4 (Layer D); Doty et al. (arXiv:2106.10201v2) §6.
-/

import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.ClockLayerB
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.ClockFrontShapeCert

namespace ExactMajority

namespace ClockLayerD

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators
open ClockRealKernel EarlyDripMarked ClockLayerB

variable {L K : ℕ}

/-- The Lemma-6.3 endpoint bad set at level `T`. -/
def Lemma63BadSet (C₀ T : ℕ) (p : ℝ) : Set (MCfg L K) :=
  {mc₁ | Lemma63Bad (L := L) (K := K) C₀ T p mc₁}

/-- The state-local active gate as a set. -/
def Active63Set (C₀ T : ℕ) (θ ρ η : ℝ) (Aux : MCfg L K → Prop) : Set (MCfg L K) :=
  {z | Active63 (L := L) (K := K) C₀ T θ ρ η Aux z}

/-- **The per-`(level T, start s)` window-bad mass.**  Integrate, over the chain run to the window
start `s`, the conditional Lemma-6.3 window failure: on an `Active63` start the `Lwin`-step
window-bad mass `((markedK T θn)^Lwin · {Lemma63Bad})`, and `0` off the gate. -/
noncomputable def windowBadMass (T θn C₀ Lwin : ℕ) (p θ ρ η : ℝ)
    (Aux : MCfg L K → Prop) (s : ℕ) (mc₀ : MCfg L K) : ℝ≥0∞ :=
  ∫⁻ z, (Active63Set (L := L) (K := K) C₀ T θ ρ η Aux).indicator
      (fun z => ((markedK (L := L) (K := K) T θn) ^ Lwin) z
        (Lemma63BadSet (L := L) (K := K) C₀ T p)) z
    ∂(((markedK (L := L) (K := K) T θn) ^ s) mc₀)

/-- **Each window-bad term is `≤ εWindow`.**  The integrand is `≤ εWindow` pointwise (on the gate by
the carried per-active-state window transfer `hwin`, off it `0 ≤ εWindow`); the start measure is a
probability measure (the marked kernel is Markov), so the integral is `≤ εWindow`. -/
theorem windowBadMass_le (T θn C₀ Lwin : ℕ) (p θ ρ η : ℝ)
    (Aux : MCfg L K → Prop) (εWindow : ℝ≥0∞)
    (hwin : ∀ z, Active63 (L := L) (K := K) C₀ T θ ρ η Aux z →
      ((markedK (L := L) (K := K) T θn) ^ Lwin) z
        (Lemma63BadSet (L := L) (K := K) C₀ T p) ≤ εWindow)
    (s : ℕ) (mc₀ : MCfg L K) :
    windowBadMass (L := L) (K := K) T θn C₀ Lwin p θ ρ η Aux s mc₀ ≤ εWindow := by
  classical
  unfold windowBadMass
  have hpt : ∀ z, (Active63Set (L := L) (K := K) C₀ T θ ρ η Aux).indicator
      (fun z => ((markedK (L := L) (K := K) T θn) ^ Lwin) z
        (Lemma63BadSet (L := L) (K := K) C₀ T p)) z ≤ εWindow := by
    intro z
    by_cases hz : z ∈ Active63Set (L := L) (K := K) C₀ T θ ρ η Aux
    · rw [Set.indicator_of_mem hz]
      exact hwin z hz
    · rw [Set.indicator_of_notMem hz]; exact zero_le'
  calc ∫⁻ z, (Active63Set (L := L) (K := K) C₀ T θ ρ η Aux).indicator
          (fun z => ((markedK (L := L) (K := K) T θn) ^ Lwin) z
            (Lemma63BadSet (L := L) (K := K) C₀ T p)) z
        ∂(((markedK (L := L) (K := K) T θn) ^ s) mc₀)
      ≤ ∫⁻ _, εWindow ∂(((markedK (L := L) (K := K) T θn) ^ s) mc₀) :=
        lintegral_mono hpt
    _ = εWindow := by
        rw [lintegral_const]
        haveI : IsMarkovKernel ((markedK (L := L) (K := K) T θn) ^ s) := by
          induction s with
          | zero =>
              rw [pow_zero]
              exact inferInstanceAs (IsMarkovKernel (Kernel.id : Kernel (MCfg L K) (MCfg L K)))
          | succ k ih =>
              haveI := ih; rw [pow_succ]
              exact inferInstanceAs (IsMarkovKernel
                ((markedK (L := L) (K := K) T θn ^ k) ∘ₖ markedK (L := L) (K := K) T θn))
        rw [measure_univ, mul_one]

/-- **Layer-D single-level union budget.**  Over a finite set of window-starts, the window-bad mass
sums to `≤ (#starts) · εWindow`. -/
theorem windowBad_aggregate (T θn C₀ Lwin : ℕ) (p θ ρ η : ℝ)
    (Aux : MCfg L K → Prop) (εWindow : ℝ≥0∞)
    (hwin : ∀ z, Active63 (L := L) (K := K) C₀ T θ ρ η Aux z →
      ((markedK (L := L) (K := K) T θn) ^ Lwin) z
        (Lemma63BadSet (L := L) (K := K) C₀ T p) ≤ εWindow)
    (starts : Finset ℕ) (mc₀ : MCfg L K) :
    ∑ s ∈ starts, windowBadMass (L := L) (K := K) T θn C₀ Lwin p θ ρ η Aux s mc₀
      ≤ (starts.card : ℝ≥0∞) * εWindow := by
  calc ∑ s ∈ starts, windowBadMass (L := L) (K := K) T θn C₀ Lwin p θ ρ η Aux s mc₀
      ≤ ∑ _s ∈ starts, εWindow :=
        Finset.sum_le_sum (fun s _ =>
          windowBadMass_le (L := L) (K := K) T θn C₀ Lwin p θ ρ η Aux εWindow hwin s mc₀)
    _ = (starts.card : ℝ≥0∞) * εWindow := by
        rw [Finset.sum_const, nsmul_eq_mul]

/-- **Layer-D full union budget (levels × starts).**  Over the leading levels and window-starts, the
total window-bad mass is `≤ (#levels)·(#starts)·εWindow` — the Round-4 Layer-D budget
`leadingLevels.card · (H+1−Lwin) · ε_window`.  The per-level window transfer `hwin` is the carried
Bennett/MGF-fed `lemma63_window_transfer_forward` conclusion, uniform over the leading levels. -/
theorem windowBad_aggregate_levels (θn C₀ Lwin : ℕ) (p θ ρ η : ℝ)
    (Aux : MCfg L K → Prop) (εWindow : ℝ≥0∞)
    (levels starts : Finset ℕ)
    (hwin : ∀ T ∈ levels, ∀ z, Active63 (L := L) (K := K) C₀ T θ ρ η Aux z →
      ((markedK (L := L) (K := K) T θn) ^ Lwin) z
        (Lemma63BadSet (L := L) (K := K) C₀ T p) ≤ εWindow)
    (mc₀ : MCfg L K) :
    ∑ T ∈ levels, ∑ s ∈ starts,
        windowBadMass (L := L) (K := K) T θn C₀ Lwin p θ ρ η Aux s mc₀
      ≤ (levels.card : ℝ≥0∞) * ((starts.card : ℝ≥0∞) * εWindow) := by
  calc ∑ T ∈ levels, ∑ s ∈ starts,
          windowBadMass (L := L) (K := K) T θn C₀ Lwin p θ ρ η Aux s mc₀
      ≤ ∑ _T ∈ levels, (starts.card : ℝ≥0∞) * εWindow :=
        Finset.sum_le_sum (fun T hT =>
          windowBad_aggregate (L := L) (K := K) T θn C₀ Lwin p θ ρ η Aux εWindow
            (hwin T hT) starts mc₀)
    _ = (levels.card : ℝ≥0∞) * ((starts.card : ℝ≥0∞) * εWindow) := by
        rw [Finset.sum_const, nsmul_eq_mul]

end ClockLayerD

end ExactMajority
