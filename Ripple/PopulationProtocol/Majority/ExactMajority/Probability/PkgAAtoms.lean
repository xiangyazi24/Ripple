/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Package A atoms for `WorkInputsV51`

Append-only package file for the POST63 atom campaign.

Delivered surfaces:

* `hext1H_of_extremePos_witness_honest` produces the exact `WorkInputsV51.hext1H`
  field from the sharp carried witness `∀ b, Phase1Honest n b → ∃ a ∈ b, extremePos a`.
  The weaker `extremeU ≥ 1` route remains false-as-stated, by `SmallSweep`:
  `extremeU` is two-sided (`smallBias = 0 ∨ 6`) while `extremePosSet` is the `+3`
  side only.

* `hpull1H_of_entry_on_honest` produces the exact `WorkInputsV51.hpull1H` field at
  `P1 = (n - g + 3) / 4`, from the precise carried remainder
  `∀ b, Phase1Honest n b → PartnerMargin.EntrySumPinned n g b`.  This is the
  honest-window version of the landed `SlotAtoms.pullPos_floor_of_entry`; the
  current `Phase1Honest` predicate is phase-only, so the all-Main/gap entry fact is
  not derivable from it alone.

* `hpt1_of_rect_calibration` and `hpt1_of_rect_calibrated_window` produce the exact
  `WorkInputsV51.hpt1` field by `DrainCalibration.rect_pow_le_budget_enn`.
-/

import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.PartnerMargin
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.HonestWindows
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.FinalAssemblyV2

namespace ExactMajority

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace PkgAAtoms

variable {L K : ℕ}

attribute [local instance] Classical.propDecidable

/-! ## `hext1H` — exact field adapter from the sharp `+3` witness. -/

/-- A pointwise `+3`-extreme witness contributes one count to `extremePosSet`. -/
theorem extremePosSet_sum_pos_of_witness (c : Config (AgentState L K))
    (h : ∃ a ∈ c, DrainThreading.extremePos a) :
    1 ≤ (DrainThreading.extremePosSet L K).sum c.count := by
  classical
  obtain ⟨a, hac, haext⟩ := h
  have hamem : a ∈ DrainThreading.extremePosSet L K := by
    simp only [DrainThreading.extremePosSet, Finset.mem_filter]
    exact ⟨Finset.mem_univ a, haext⟩
  have hcount : 1 ≤ c.count a := Multiset.one_le_count_iff_mem.mpr hac
  exact le_trans hcount (Finset.single_le_sum (fun _ _ => Nat.zero_le _) hamem)

/-- **Produces `WorkInputsV51.hext1H`.**

Exact field shape:
`∀ b, Phase1Honest n b → 1 ≤ (DrainThreading.extremePosSet L K).sum b.count`.

Remainder: a sign-selected `+3` witness on the honest window.  This is strictly
stronger than `extremeU b ≥ 1`; see `SmallSweep.hext1_not_from_extremeU`. -/
theorem hext1H_of_extremePos_witness_honest (n : ℕ)
    (hwit : ∀ b : Config (AgentState L K),
      HonestWindows.Phase1Honest (L := L) (K := K) n b →
        ∃ a ∈ b, DrainThreading.extremePos a) :
    ∀ b : Config (AgentState L K),
      HonestWindows.Phase1Honest (L := L) (K := K) n b →
        1 ≤ (DrainThreading.extremePosSet L K).sum b.count :=
  fun b hb => extremePosSet_sum_pos_of_witness b (hwit b hb)

/-- The sharp landed verdict: `extremeU ≥ 1` only gives a saturated extreme on
one of the two ends (`0` or `6`), while `hext1H` needs the sign-selected `6` end.
This theorem is intentionally a compact re-export for Package A's remainder log. -/
theorem hext1H_not_produced_by_extremeU_verdict :
    (∀ c : Config (AgentState L K), 1 ≤ (DrainThreading.extremePosSet L K).sum c.count →
        1 ≤ Phase1Convergence.extremeU c) ∧
    (∀ a : AgentState L K, Phase1Convergence.extremeSt a →
        a.smallBias.val = 0 ∨ a.smallBias.val = 6) :=
  by
    constructor
    · intro c h
      classical
      have hne : (DrainThreading.extremePosSet L K).sum c.count ≠ 0 := by omega
      obtain ⟨a, ha, hca⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
      simp only [DrainThreading.extremePosSet, Finset.mem_filter] at ha
      have hmem : a ∈ c := Multiset.one_le_count_iff_mem.mp (Nat.one_le_iff_ne_zero.mpr hca)
      have hext : Phase1Convergence.extremeSt a := by
        obtain ⟨hm, hv⟩ := ha.2
        refine ⟨hm, ?_⟩
        unfold Phase1Convergence.extremeVal
        rw [hv]
        rfl
      unfold Phase1Convergence.extremeU
      exact Multiset.countP_pos_of_mem hmem hext
    · intro a h
      have hv : Phase1Convergence.extremeVal a.smallBias = true := h.2
      unfold Phase1Convergence.extremeVal at hv
      rcases Nat.lt_or_ge a.smallBias.val 1 with h0 | _
      · exact Or.inl (by omega)
      · rcases (by simpa using hv : a.smallBias.val = 0 ∨ a.smallBias.val = 6) with hzero | hsix
        · exact Or.inl hzero
        · exact Or.inr hsix

/-! ## `hpull1H` — exact field adapter at `P1 = (n - g + 3) / 4`. -/

/-- **Produces `WorkInputsV51.hpull1H` at `P1 = (n - g + 3) / 4`.**

Exact field shape:
`∀ b, Phase1Honest n b → (n - g + 3) / 4 ≤ pullPosSet.sum b.count`.

Remainder: `hentry`, the honest-window entry/gap predicate
`PartnerMargin.EntrySumPinned n g`.  This bundles the all-Main counting support and
the conserved gap bound `|centredBiasSum| ≤ g`; the current `Phase1Honest` is only
`card = n ∧ phase = 1`, so it does not imply this by itself. -/
theorem hpull1H_of_entry_on_honest (n g : ℕ)
    (hentry : ∀ b : Config (AgentState L K),
      HonestWindows.Phase1Honest (L := L) (K := K) n b →
        PartnerMargin.EntrySumPinned (L := L) (K := K) n g b) :
    ∀ b : Config (AgentState L K),
      HonestWindows.Phase1Honest (L := L) (K := K) n b →
        (n - g + 3) / 4 ≤ (DrainThreading.pullPosSet L K).sum b.count :=
  fun b hb =>
    le_trans (PartnerMargin.lowSet_floor_of_entry n g b (hentry b hb))
      (by
        exact Finset.sum_le_sum_of_subset (by
          intro a ha
          simp only [AveragingRate.lowSet, AveragingRate.low, DrainThreading.pullPosSet,
            DrainThreading.pullPos, Finset.mem_filter] at ha ⊢
          exact ⟨ha.1, ha.2.1, by omega⟩))

/-- A split version of `hpull1H_of_entry_on_honest` when the campaign carries the
all-Main support and the conserved gap as separate facts.  This also produces the
exact `WorkInputsV51.hpull1H` field at `P1 = (n - g + 3) / 4`. -/
theorem hpull1H_of_allMain_and_gap_on_honest (n g : ℕ)
    (hall : ∀ b : Config (AgentState L K),
      HonestWindows.Phase1Honest (L := L) (K := K) n b →
        Phase1Convergence.Phase1AllMain (L := L) (K := K) n b)
    (hgap : ∀ b : Config (AgentState L K),
      HonestWindows.Phase1Honest (L := L) (K := K) n b →
        |AveragingRate.centredBiasSum b| ≤ (g : ℤ)) :
    ∀ b : Config (AgentState L K),
      HonestWindows.Phase1Honest (L := L) (K := K) n b →
        (n - g + 3) / 4 ≤ (DrainThreading.pullPosSet L K).sum b.count :=
  hpull1H_of_entry_on_honest n g (fun b hb => ⟨hall b hb, hgap b hb⟩)

/-! ## `hpt1` — exact field via the rectangle calibration. -/

/-- The real rate corresponding to the constant rectangle floor `P1`. -/
noncomputable def qRectReal (P1 n : ℕ) : ℝ :=
  1 - ((P1 : ℝ) / ((n : ℝ) * ((n : ℝ) - 1)))

/-- On positive levels, `qHat P1 n` is exactly `ofReal (qRectReal P1 n)`. -/
theorem qHat_eq_ofReal_qRectReal {P1 n m : ℕ} (hn : 2 ≤ n) (hm : 1 ≤ m) :
    FinalAssemblyV2.qHat P1 n m = ENNReal.ofReal (qRectReal P1 n) := by
  rw [FinalAssemblyV2.qHat_eq_on_pos _ _ _ hm]
  unfold DrainRates.levelRate qRectReal
  have hnR : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hden : 0 ≤ (n : ℝ) * ((n : ℝ) - 1) := by nlinarith
  have hnonneg : 0 ≤ ((P1 : ℝ) / ((n : ℝ) * ((n : ℝ) - 1))) := div_nonneg (by positivity) hden
  rw [ENNReal.ofReal_sub 1 hnonneg]
  simp

/-- A calibrated per-level window.  With `α m` as the real rectangle fraction for
level `m`, this is the usual ceiling of `(3 / α) * (n / m) * log n`. -/
noncomputable def rectTWin (α : ℕ → ℝ) (n m : ℕ) : ℕ :=
  Nat.ceil ((3 / α m) * ((n : ℝ) / (m : ℝ)) * Real.log n)

/-- The calibrated window satisfies the lower-bound side condition required by
`DrainCalibration.rect_pow_le_budget_enn`. -/
theorem rectTWin_spec (α : ℕ → ℝ) (n m : ℕ) :
    (3 / α m) * ((n : ℝ) / (m : ℝ)) * Real.log n ≤
      (rectTWin α n m : ℝ) := by
  exact Nat.le_ceil _

/-- **Produces `WorkInputsV51.hpt1`.**

Exact field shape:
`∀ m ∈ Icc 1 M₀, (FinalAssemblyV2.qHat P1 n m) ^ (tWin1 m) ≤ budgetNN M₀ n`.

The assumptions are precisely the real rectangle-calibration obligations for each
level: `M₀ ≤ n`, `0 < α m ≤ 1`, nonnegative real rate, rate ceiling, and the
chosen window length lower bound. -/
theorem hpt1_of_rect_calibration {n M₀ P1 : ℕ} (tWin1 : ℕ → ℕ) (α : ℕ → ℝ)
    (hn : 2 ≤ n) (hM1 : 1 ≤ M₀) (hM₀ : (M₀ : ℝ) ≤ n)
    (hα0 : ∀ m ∈ Finset.Icc 1 M₀, 0 < α m)
    (hα1 : ∀ m ∈ Finset.Icc 1 M₀, α m ≤ 1)
    (hq0 : ∀ m ∈ Finset.Icc 1 M₀, 0 ≤ qRectReal P1 n)
    (hq : ∀ m ∈ Finset.Icc 1 M₀,
      qRectReal P1 n ≤ 1 - α m * (m : ℝ) / n)
    (hT : ∀ m ∈ Finset.Icc 1 M₀,
      (3 / α m) * ((n : ℝ) / (m : ℝ)) * Real.log n ≤ tWin1 m) :
    ∀ m ∈ Finset.Icc 1 M₀,
      (FinalAssemblyV2.qHat P1 n m) ^ (tWin1 m) ≤
        (DrainCalibration.budgetNN M₀ n : ℝ≥0∞) := by
  intro m hmI
  have hm : 1 ≤ m := (Finset.mem_Icc.mp hmI).1
  rw [qHat_eq_ofReal_qRectReal hn hm]
  exact DrainCalibration.rect_pow_le_budget_enn hn hm hM1 hM₀
    (hα0 m hmI) (hα1 m hmI) (hq0 m hmI) (hq m hmI) (hT m hmI)

/-- **Produces `WorkInputsV51.hpt1` for the calibrated choice**
`tWin1 m = rectTWin α n m`. -/
theorem hpt1_of_rect_calibrated_window {n M₀ P1 : ℕ} (α : ℕ → ℝ)
    (hn : 2 ≤ n) (hM1 : 1 ≤ M₀) (hM₀ : (M₀ : ℝ) ≤ n)
    (hα0 : ∀ m ∈ Finset.Icc 1 M₀, 0 < α m)
    (hα1 : ∀ m ∈ Finset.Icc 1 M₀, α m ≤ 1)
    (hq0 : ∀ m ∈ Finset.Icc 1 M₀, 0 ≤ qRectReal P1 n)
    (hq : ∀ m ∈ Finset.Icc 1 M₀,
      qRectReal P1 n ≤ 1 - α m * (m : ℝ) / n) :
    ∀ m ∈ Finset.Icc 1 M₀,
      (FinalAssemblyV2.qHat P1 n m) ^ (rectTWin α n m) ≤
        (DrainCalibration.budgetNN M₀ n : ℝ≥0∞) :=
  hpt1_of_rect_calibration (P1 := P1) (fun m => rectTWin α n m) α hn hM1 hM₀
    hα0 hα1 hq0 hq (fun m _ => rectTWin_spec α n m)

end PkgAAtoms

end ExactMajority
