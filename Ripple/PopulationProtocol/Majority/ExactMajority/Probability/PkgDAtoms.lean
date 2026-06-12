/-
# Package D atoms — escape-budget adapters and padded Phase-6 drain rate.

Append-only package file for the V5.1 residual surface.  This file does not edit existing
campaign files.  It records the exact WorkInputsV51 field shapes that can be produced from
landed machinery, and names the honest carried remainders where the landed machinery is not
strong enough.

Delivered exact adapters:
* `hescW_of_tail_le`:
  if the at-risk tail layer supplies the exact one-step window-escape bound at a smaller
  budget `ηtail`, this produces the corresponding WorkInputsV51-shaped `hescW*` field at
  budget `η`.
* `hescε{1,6,7,8}_of_tail_fit`:
  the exact WorkInputsV51 escape-budget fields by the same arithmetic as
  `WindowSurvival.escape_budget_fits`.
* `q6D`, `hdrop6_padded_from_positive`, `hpt6_padded_from_positive`, `hq6zero_padded`:
  the padded phase-6 rate package.  The positive levels use any landed positive-level
  rate theorem (for example the Phase-6 chain rate); level `0` is padded to `1`, exactly
  matching the survival engine's filler need.

Honest carried remainders:
* the at-risk layer still has to provide the exact one-step `hescW*` hypotheses; the landed
  seam tail is multi-step and seam-indexed, not the V51 one-step window field.
* `hClosed5` remains carried.  Phase 5 is the documented exception: entry from phase 4 uses
  `advancePhase`, not `phaseInit`, so the counter-reset tail does not apply.
-/
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.Phase6Convergence
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.ReserveSampling

namespace ExactMajority
namespace PkgDAtoms

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators

variable {L K : ℕ}

/-! ## One-step escape-field adapter for WorkInputsV51.

These are deliberately adapters, not fake discharges.  The landed at-risk counter files give
seam-indexed multi-step tails; V51 asks for a one-step kernel escape field.  Once the at-risk
layer supplies that exact one-step field at `ηtail`, these theorems produce the exact V51
field at any larger `η`.
-/

/-- Produces any WorkInputsV51-shaped `hescW*` field from an exact one-step tail and
`ηtail ≤ η`.  Instantiate `Inv` with `Phase1Honest`, `Phase6Win`, `Phase7Honest`, or
`Phase8Honest` to recover the four field shapes. -/
theorem hescW_of_tail_le {α : Type*} [MeasurableSpace α] (Kern : Kernel α α)
    (Inv : α → Prop) {ηtail η : ℝ≥0∞}
    (hη : ηtail ≤ η)
    (htail : ∀ x, Inv x → Kern x {y | ¬ Inv y} ≤ ηtail) :
    ∀ x, Inv x → Kern x {y | ¬ Inv y} ≤ η := by
  intro x hx
  exact (htail x hx).trans hη

/-! ## Exact escape-budget fields.

Each theorem below produces the corresponding WorkInputsV51 `hescε*` field.  The only
slot-specific data is the window-length function name in the conclusion.
-/

/-- Produces WorkInputsV51 field `hescε1`. -/
theorem hescε1_of_tail_fit (c L0 M₀ : ℕ) (tWin1 : ℕ → ℕ) (η1 : ℝ≥0∞)
    (escapeε1 : ℝ≥0)
    (hηtail : η1 ≤ ENNReal.ofReal (Real.exp (-(c * (L0 + 1) : ℕ))))
    (hfit : ((((∑ m ∈ Finset.Icc 1 M₀, tWin1 m) : ℕ) : ℝ≥0∞) *
        ENNReal.ofReal (Real.exp (-(c * (L0 + 1) : ℕ)))) ≤ (escapeε1 : ℝ≥0∞)) :
    (((∑ m ∈ Finset.Icc 1 M₀, tWin1 m) : ℕ) : ℝ≥0∞) * η1 ≤
      (escapeε1 : ℝ≥0∞) :=
  le_trans (by gcongr) hfit

/-- Produces WorkInputsV51 field `hescε6`. -/
theorem hescε6_of_tail_fit (c L0 M₀ : ℕ) (tWin6 : ℕ → ℕ) (η6 : ℝ≥0∞)
    (escapeε6 : ℝ≥0)
    (hηtail : η6 ≤ ENNReal.ofReal (Real.exp (-(c * (L0 + 1) : ℕ))))
    (hfit : ((((∑ m ∈ Finset.Icc 1 M₀, tWin6 m) : ℕ) : ℝ≥0∞) *
        ENNReal.ofReal (Real.exp (-(c * (L0 + 1) : ℕ)))) ≤ (escapeε6 : ℝ≥0∞)) :
    (((∑ m ∈ Finset.Icc 1 M₀, tWin6 m) : ℕ) : ℝ≥0∞) * η6 ≤
      (escapeε6 : ℝ≥0∞) :=
  le_trans (by gcongr) hfit

/-- Produces WorkInputsV51 field `hescε7`. -/
theorem hescε7_of_tail_fit (c L0 M₀ : ℕ) (tWin7 : ℕ → ℕ) (η7 : ℝ≥0∞)
    (escapeε7 : ℝ≥0)
    (hηtail : η7 ≤ ENNReal.ofReal (Real.exp (-(c * (L0 + 1) : ℕ))))
    (hfit : ((((∑ m ∈ Finset.Icc 1 M₀, tWin7 m) : ℕ) : ℝ≥0∞) *
        ENNReal.ofReal (Real.exp (-(c * (L0 + 1) : ℕ)))) ≤ (escapeε7 : ℝ≥0∞)) :
    (((∑ m ∈ Finset.Icc 1 M₀, tWin7 m) : ℕ) : ℝ≥0∞) * η7 ≤
      (escapeε7 : ℝ≥0∞) :=
  le_trans (by gcongr) hfit

/-- Produces WorkInputsV51 field `hescε8`. -/
theorem hescε8_of_tail_fit (c L0 M₀ : ℕ) (tWin8 : ℕ → ℕ) (η8 : ℝ≥0∞)
    (escapeε8 : ℝ≥0)
    (hηtail : η8 ≤ ENNReal.ofReal (Real.exp (-(c * (L0 + 1) : ℕ))))
    (hfit : ((((∑ m ∈ Finset.Icc 1 M₀, tWin8 m) : ℕ) : ℝ≥0∞) *
        ENNReal.ofReal (Real.exp (-(c * (L0 + 1) : ℕ)))) ≤ (escapeε8 : ℝ≥0∞)) :
    (((∑ m ∈ Finset.Icc 1 M₀, tWin8 m) : ℕ) : ℝ≥0∞) * η8 ≤
      (escapeε8 : ℝ≥0∞) :=
  le_trans (by gcongr) hfit

/-! ## Phase-6 padded rate package.

The V51 survival engine additionally needs `1 ≤ q6 0`.  Padding only level `0` solves
that without changing any positive-level budget field.  The positive-level rate `qpos`
is intended to be instantiated with the landed Phase-6 chain rate.
-/

/-- Padded phase-6 rate: positive levels use `qpos`; level `0` is the filler `1`. -/
noncomputable def q6D (qpos : ℕ → ℝ≥0∞) : ℕ → ℝ≥0∞ :=
  fun m => if 1 ≤ m then qpos m else 1

@[simp] theorem q6D_zero (qpos : ℕ → ℝ≥0∞) : q6D qpos 0 = 1 := by
  unfold q6D
  simp

theorem q6D_eq_on_pos (qpos : ℕ → ℝ≥0∞) (m : ℕ) (hm : 1 ≤ m) :
    q6D qpos m = qpos m := by
  unfold q6D
  rw [if_pos hm]

/-- Produces WorkInputsV51 field `hq6zero` for `q6 := q6D qpos`. -/
theorem hq6zero_padded (qpos : ℕ → ℝ≥0∞) : (1 : ℝ≥0∞) ≤ q6D qpos 0 := by
  rw [q6D_zero]

/-- Produces WorkInputsV51 field `hdrop6` for `q6 := q6D qpos`.

The positive-level case is supplied by the landed chain rate; the level-`0` case is the
probability bound into the padded value `1`.
-/
theorem hdrop6_padded_from_positive {n : ℕ} (l : ℕ) (qpos : ℕ → ℝ≥0∞)
    (hdrop_pos : ∀ m, 1 ≤ m → ∀ b : Config (AgentState L K),
      Phase6Convergence.Phase6Win (L := L) (K := K) n b →
      Phase6Convergence.highMass (L := L) (K := K) l b = m →
      (NonuniformMajority L K).transitionKernel b
        (OneSidedCancel.potBelow
          (fun c => Phase6Convergence.highMass (L := L) (K := K) l c) m)ᶜ ≤ qpos m) :
    ∀ m, ∀ b : Config (AgentState L K),
      Phase6Convergence.Phase6Win (L := L) (K := K) n b →
      Phase6Convergence.highMass (L := L) (K := K) l b = m →
      (NonuniformMajority L K).transitionKernel b
        (OneSidedCancel.potBelow
          (fun c => Phase6Convergence.highMass (L := L) (K := K) l c) m)ᶜ ≤
          q6D qpos m := by
  intro m b hInv hbm
  rcases Nat.eq_zero_or_pos m with hm0 | hmpos
  · subst hm0
    rw [q6D_zero]
    exact prob_le_one
  · rw [q6D_eq_on_pos qpos m hmpos]
    exact hdrop_pos m hmpos b hInv hbm

/-- Produces WorkInputsV51-shaped field `hpt6` for `q6 := q6D qpos` from a positive-level
budget.  Instantiate `budget` with `DrainCalibration.budgetNN M₀ n` to recover the V51 field. -/
theorem hpt6_padded_from_positive {M₀ : ℕ} {qpos : ℕ → ℝ≥0∞} {tWin6 : ℕ → ℕ}
    {budget : ℝ≥0∞}
    (hpt : ∀ m ∈ Finset.Icc 1 M₀,
      (qpos m) ^ (tWin6 m) ≤ budget) :
    ∀ m ∈ Finset.Icc 1 M₀, (q6D qpos m) ^ (tWin6 m) ≤ budget := by
  intro m hm
  have hmpos : 1 ≤ m := (Finset.mem_Icc.mp hm).1
  rw [q6D_eq_on_pos qpos m hmpos]
  exact hpt m hm

/-! ## Slot-5 closure remainder.

This names the exact carried WorkInputsV51 field.  No theorem in the current landed machinery
produces this from the counter-tail mechanism: phase 5 is the documented non-reset exception.
-/

/-- Exact WorkInputsV51 field shape for the carried `hClosed5` remainder. -/
abbrev HClosed5Field (n : ℕ) : Prop :=
  OneSidedCancel.InvClosed (NonuniformMajority L K).transitionKernel
    (fun c => ReserveSampling.Phase5AllWin (L := L) (K := K) n c)

/-- Adapter for the carried WorkInputsV51 field `hClosed5`.

This is intentionally only an adapter: the Package-D survey found no landed width-based
replacement producing this exact `Phase5AllWin` closure.
-/
theorem hClosed5_carried {n : ℕ} (h : HClosed5Field (L := L) (K := K) n) :
    OneSidedCancel.InvClosed (NonuniformMajority L K).transitionKernel
      (fun c => ReserveSampling.Phase5AllWin (L := L) (K := K) n c) :=
  h

end PkgDAtoms
end ExactMajority
