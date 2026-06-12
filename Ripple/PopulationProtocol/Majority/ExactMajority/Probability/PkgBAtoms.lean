/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Package B atoms — Lemma 7.4 / 7.6 margins for `WorkInputsV51`

This file is append-only and produces adapters for the V51 fields
`hwit7`, `hwit8`, `hpt7`, and `hpt8`.

Honesty note.  The landed Lemma-7.4/7.6 adapters extract their minority witnesses through
`Phase7AllMain` / `Phase8AllMain`, while `WorkInputsV51` asks for witnesses under the weaker
phase-only windows `Phase7Honest` / `Phase8Honest`.  Since the per-level witness sets
`minorityAt7` and `minorityAt` are Main-role filtered, the phase-only hypothesis by itself does
not provide the role witness.  The exact V51 producers below therefore carry the precise missing
bridge:

* for slot 7, `Phase7Honest n b → Phase7AllMain n b` plus the Phase6→7 structure on that honest
  window (or, in the single-level adapter, the stronger `Phase7Honest n b → Inv7Sum n b`);
* for slot 8, `Phase8Honest n b → Phase8AllMain n b` plus the Phase7→8 structure on that honest
  window (or the survival-chain inputs producing it).

The budget fields are fully wired from the α-parametric rectangle calibration, at `α₇ = 4/15`
and the honest slot-8 re-cut `α₈' = 14/75`; the caller supplies the standard real rate comparison
and horizon for each level.
-/

import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.EliminatorMargins
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.HonestWindows
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.FinalAssemblyV2

namespace ExactMajority
namespace PkgBAtoms

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators

variable {L K : ℕ}

/-! ## Slot 7 witness field (`WorkInputsV51.hwit7`). -/

/-- Produces the exact `WorkInputsV51.hwit7` field from a Phase6→7 eliminator-margin structure
available on the honest window, plus the necessary role-window bridge.

Field produced: `WorkInputsV51.hwit7`.
Carried remainder: `Phase7Honest → Phase7AllMain`, because `minorityAt7` is Main-role filtered. -/
theorem hwit7_of_phase6To7Structure_honest {n E7 : ℕ} {σ : Sign}
    (hE7 : (E7 : ℝ) ≤ (4 : ℝ) * (n : ℝ) / 15)
    (hAll7 : ∀ b : Config (AgentState L K),
      HonestWindows.Phase7Honest (L := L) (K := K) n b →
      Phase7Convergence.Phase7AllMain (L := L) (K := K) n b)
    (hStruct7 : ∀ b : Config (AgentState L K),
      HonestWindows.Phase7Honest (L := L) (K := K) n b →
      EliminatorMargins.Phase6To7Structure (L := L) (K := K) σ E7 b) :
    ∀ b : Config (AgentState L K), HonestWindows.Phase7Honest (L := L) (K := K) n b →
      Phase7Convergence.classMassN σ b ≥ 1 →
      ∃ i j : Fin (L + 1), i.val + 1 = j.val ∧
        1 ≤ (Phase7Convergence.minorityAt7 (L := L) (K := K) σ j).sum b.count ∧
        E7 ≤ (Phase7Convergence.elimGap1 (L := L) (K := K) σ i).sum b.count := by
  intro b hb7 hmass
  exact EliminatorMargins.lemma7_4_phase7_elimGap1_floor σ (hAll7 b hb7) E7
    (hStruct7 b hb7) hmass hE7

/-! ## Slot 8 witness field (`WorkInputsV51.hwit8`). -/

/-- Produces the exact `WorkInputsV51.hwit8` field from a Phase7→8 eliminator-margin structure
available on the honest window, plus the necessary role-window bridge.

Field produced: `WorkInputsV51.hwit8`.
Carried remainder: `Phase8Honest → Phase8AllMain`, because `minorityAt` is Main-role filtered. -/
theorem hwit8_of_phase7To8Structure_honest {n E8 : ℕ} {σ : Sign}
    (hE8 : (E8 : ℝ) ≤ (1 : ℝ) * (n : ℝ) / 5)
    (hAll8 : ∀ b : Config (AgentState L K),
      HonestWindows.Phase8Honest (L := L) (K := K) n b →
      Phase8Convergence.Phase8AllMain (L := L) (K := K) n b)
    (hStruct8 : ∀ b : Config (AgentState L K),
      HonestWindows.Phase8Honest (L := L) (K := K) n b →
      EliminatorMargins.Phase7To8Structure (L := L) (K := K) σ E8 b) :
    ∀ b : Config (AgentState L K), HonestWindows.Phase8Honest (L := L) (K := K) n b →
      Phase7Convergence.minorityU σ b ≥ 1 →
      ∃ i : Fin (L + 1),
        1 ≤ (Phase8Convergence.minorityAt (L := L) (K := K) σ i).sum b.count ∧
        E8 ≤ (Phase8Convergence.elimAbove (L := L) (K := K) σ i).sum b.count := by
  intro b hb8 hminor
  obtain ⟨i, hmini⟩ := EliminatorMargins.exists_minorityAt_of_minorityU_pos σ b hminor
  exact ⟨i, hmini,
    EliminatorMargins.lemma7_6_phase8_elimAbove_floor σ (hAll8 b hb8) E8
      (hStruct8 b hb8) i hmini hE8⟩

/-- The honest survival constant `14n/75` is strong enough for the landed consumer's `n/5`
side-condition.

Field support for: `WorkInputsV51.hwit8`. -/
theorem fourteen_seventyfive_le_one_fifth (n : ℕ) :
    (14 : ℝ) * (n : ℝ) / 75 ≤ (1 : ℝ) * (n : ℝ) / 5 := by
  have hn0 : (0 : ℝ) ≤ n := by exact_mod_cast Nat.zero_le n
  nlinarith

/-! ## Slot 7/8 per-level budget fields (`WorkInputsV51.hpt7`, `WorkInputsV51.hpt8`). -/

/-- Local bridge between the floor-adapter ENNReal subtraction rate and the calibrated real rate. -/
theorem ofReal_one_sub {r : ℝ} (hr0 : 0 ≤ r) :
    ENNReal.ofReal (1 - r) = 1 - ENNReal.ofReal r := by
  rw [ENNReal.ofReal_sub _ hr0, ENNReal.ofReal_one]

/-- α-parametric per-level `qHat` budget closer.

This is the exact arithmetic adapter behind `WorkInputsV51.hpt7` and `WorkInputsV51.hpt8`.
The caller supplies the usual real rectangle comparison for each level and the matching horizon.
-/
theorem qHat_budget_at_alpha {E n M₀ : ℕ} {α : ℝ} (tWin : ℕ → ℕ)
    (hn : 2 ≤ n) (hM1 : 1 ≤ M₀) (hM₀ : (M₀ : ℝ) ≤ n)
    (hα0 : 0 < α) (hα1 : α ≤ 1)
    (hq0 : 0 ≤ 1 - (E : ℝ) / ((n : ℝ) * ((n : ℝ) - 1)))
    (hrate : ∀ m ∈ Finset.Icc 1 M₀,
      1 - (E : ℝ) / ((n : ℝ) * ((n : ℝ) - 1)) ≤
        1 - α * (m : ℝ) / n)
    (hT : ∀ m ∈ Finset.Icc 1 M₀,
      (3 / α) * ((n : ℝ) / (m : ℝ)) * Real.log n ≤ tWin m) :
    ∀ m ∈ Finset.Icc 1 M₀, (FinalAssemblyV2.qHat E n m) ^ (tWin m) ≤
      (DrainCalibration.budgetNN M₀ n : ℝ≥0∞) := by
  intro m hmI
  have hm1 : 1 ≤ m := (Finset.mem_Icc.mp hmI).1
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hden_pos : 0 < (n : ℝ) * ((n : ℝ) - 1) := by nlinarith
  have hfrac0 : 0 ≤ (E : ℝ) / ((n : ℝ) * ((n : ℝ) - 1)) :=
    div_nonneg (by exact_mod_cast Nat.zero_le E) (le_of_lt hden_pos)
  rw [FinalAssemblyV2.qHat_eq_on_pos E n m hm1, DrainRates.levelRate,
    ← ofReal_one_sub hfrac0]
  exact DrainCalibration.rect_pow_le_budget_enn hn hm1 hM1 hM₀ hα0 hα1 hq0
    (hrate m hmI) (hT m hmI)

/-- Produces the exact `WorkInputsV51.hpt7` field at `α₇ = 4/15`.

Field produced: `WorkInputsV51.hpt7`.
Carried arithmetic: per-level real rate comparison and horizon at `4/15`. -/
theorem hpt7_budget_alpha {E7 n M₀ : ℕ} (tWin7 : ℕ → ℕ)
    (hn : 2 ≤ n) (hM1 : 1 ≤ M₀) (hM₀ : (M₀ : ℝ) ≤ n)
    (hq0 : 0 ≤ 1 - (E7 : ℝ) / ((n : ℝ) * ((n : ℝ) - 1)))
    (hrate : ∀ m ∈ Finset.Icc 1 M₀,
      1 - (E7 : ℝ) / ((n : ℝ) * ((n : ℝ) - 1)) ≤
        1 - (4 / 15 : ℝ) * (m : ℝ) / n)
    (hT : ∀ m ∈ Finset.Icc 1 M₀,
      (3 / (4 / 15 : ℝ)) * ((n : ℝ) / (m : ℝ)) * Real.log n ≤ tWin7 m) :
    ∀ m ∈ Finset.Icc 1 M₀, (FinalAssemblyV2.qHat E7 n m) ^ (tWin7 m) ≤
      (DrainCalibration.budgetNN M₀ n : ℝ≥0∞) :=
  qHat_budget_at_alpha (E := E7) (n := n) (M₀ := M₀)
    (α := (4 / 15 : ℝ)) tWin7 hn hM1 hM₀ (by norm_num) (by norm_num)
    hq0 hrate hT

/-- Produces the exact `WorkInputsV51.hpt8` field at the honest re-cut `α₈' = 14/75`.

Field produced: `WorkInputsV51.hpt8`.
Carried arithmetic: per-level real rate comparison and horizon at `14/75`, matching
`BranchAndBudget.recut_budget_closes`. -/
theorem hpt8_budget_recut {E8 n M₀ : ℕ} (tWin8 : ℕ → ℕ)
    (hn : 2 ≤ n) (hM1 : 1 ≤ M₀) (hM₀ : (M₀ : ℝ) ≤ n)
    (hq0 : 0 ≤ 1 - (E8 : ℝ) / ((n : ℝ) * ((n : ℝ) - 1)))
    (hrate : ∀ m ∈ Finset.Icc 1 M₀,
      1 - (E8 : ℝ) / ((n : ℝ) * ((n : ℝ) - 1)) ≤
        1 - (14 / 75 : ℝ) * (m : ℝ) / n)
    (hT : ∀ m ∈ Finset.Icc 1 M₀,
      (3 / (14 / 75 : ℝ)) * ((n : ℝ) / (m : ℝ)) * Real.log n ≤ tWin8 m) :
    ∀ m ∈ Finset.Icc 1 M₀, (FinalAssemblyV2.qHat E8 n m) ^ (tWin8 m) ≤
      (DrainCalibration.budgetNN M₀ n : ℝ≥0∞) :=
  qHat_budget_at_alpha (E := E8) (n := n) (M₀ := M₀)
    (α := (14 / 75 : ℝ)) tWin8 hn hM1 hM₀ (by norm_num) (by norm_num)
    hq0 hrate hT

#print axioms hwit7_of_phase6To7Structure_honest
#print axioms hwit8_of_phase7To8Structure_honest
#print axioms fourteen_seventyfive_le_one_fifth
#print axioms qHat_budget_at_alpha
#print axioms hpt7_budget_alpha
#print axioms hpt8_budget_recut

end PkgBAtoms
end ExactMajority
