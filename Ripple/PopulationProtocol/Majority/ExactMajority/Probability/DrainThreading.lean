/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Drain threading — feeding the carried structural floor into each phase's drop rectangle

`DrainCalibration.lean` (D-6) discharged the failure budget `hε` of every phase drain
instance but left the per-step drain bound `hstep`/`hdrop` carried as an abstract
hypothesis.  This file (D-7) THREADS the carried *structural* count floor (the
eliminator/reserve/main-count lower bound already present in each phase's `Pre`/`Inv`)
THROUGH the phase's existing drop-probability rectangle lemma
(`*_drop_prob_rect*`) to produce the CONCRETE drop-probability floor
`ofReal(α·m/(n(n−1))) ≤ drop-mass`, and then chains it through the existing engine
packagers (`*_hdrop_of_floor*` / `*_hstep_of_floor*`) to discharge the engine `hdrop`
(levels form a) / `hstep` (crude form b, at the honest level `m = 1`).

## The generic arithmetic bridge

`ofReal_div_le_of_num_le` : `a ≤ b`, `0 ≤ a`, `0 ≤ d` ⟹ `ofReal(a/d) ≤ ofReal(b/d)`.
This is the only new analytic content; everything else is honest count bookkeeping
(`Finset.sum`-monotonicity from the structural floor) plus the existing rectangle and
packager lemmas re-applied with a derived `p`.

## What is HONEST vs structurally vacuous

The CRUDE engine (`crude_PhaseConvergenceW`, form b) needs
`hstep : ∀ b, Inv b → 1 ≤ Φ b → K b (potDone Φ)ᶜ ≤ q`.  For `Φ b ≥ 2` a single drain
drops `Φ` by `≥ 1` but NOT to `0`, so `K b (potDone Φ)ᶜ = 1` — the crude `hstep` is
genuinely vacuous unless one restricts to `Φ b = 1`.  The HONEST multi-level drain is the
LEVELS engine (`levels_PhaseConvergenceW`, form a) whose `hdrop` is per-level
`K b (potBelow Φ m)ᶜ ≤ q m`, which the rectangle floor discharges at EVERY level `m`.
So the principal D-7 deliverables are the per-level `hdrop`s (the honest engine input);
the crude `hstep` is delivered only at the `m = 1` level (where the drop reaches `potDone`).

NEW file; no existing file is edited; no sorry/admit/axiom/native_decide.
-/

import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.DrainCalibration

namespace ExactMajority

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace DrainThreading

/-! ## Part A — the generic arithmetic bridge. -/

/-- **The drop-floor monotone bridge.**  A larger rectangle count `b` over the same
denominator `d` gives a larger `ofReal` drop floor.  Used to replace the rectangle's
exact count `(#min·#elim)` by the carried structural floor `(margin·m)`. -/
theorem ofReal_div_le_of_num_le {a b d : ℝ} (hab : a ≤ b) (ha : 0 ≤ a) (hd : 0 ≤ d) :
    ENNReal.ofReal (a / d) ≤ ENNReal.ofReal (b / d) := by
  apply ENNReal.ofReal_le_ofReal
  rcases eq_or_lt_of_le hd with hd0 | hd0
  · simp [← hd0]
  · gcongr

/-! ## Part B — Phase 8 (`minorityU σ`, `Phase8AllMain`, α = 1/5).

The carried structural floor (Doty Lemma 7.4 `0.8|M|` majority minus Lemma 7.6 `0.2|M|`
minority) supplies, at some witness exponent level `i`, an eliminator margin
`(elimAbove σ i).sum count ≥ E` together with at least one minority agent at level `i`
(`(minorityAt σ i).sum count ≥ 1`).  Threaded through `minorityU_drop_prob_rect`, this
yields the drop-probability floor `ofReal(E/(n(n−1))) ≤ drop-mass`, which the existing
packager `minorityU_hdrop_of_floor` (levels) / the `m = 1` crude bridge turn into the
engine `hdrop` / `hstep`. -/

open Phase8Convergence

/-- **Phase 8 — structural floor ⟹ concrete drop-probability floor.**  At a witness level
`i` with `≥ 1` minority and eliminator margin `≥ E`, the one-step drop probability of
`minorityU σ` is `≥ ofReal(E/(n(n−1)))`. -/
theorem phase8_drop_floor_of_struct {L K : ℕ} (σ : Sign) (n : ℕ) (hn : 2 ≤ n)
    (c : Config (AgentState L K)) (hInv : Phase8Convergence.Phase8AllMain n c)
    (i : Fin (L + 1)) (E : ℕ)
    (hmin : 1 ≤ (Phase8Convergence.minorityAt (L := L) (K := K) σ i).sum c.count)
    (helim : E ≤ (Phase8Convergence.elimAbove (L := L) (K := K) σ i).sum c.count) :
    ENNReal.ofReal ((E : ℝ) / ((n : ℝ) * ((n : ℝ) - 1))) ≤
      ((NonuniformMajority L K).stepDistOrSelf c).toMeasure
        {c' | Phase7Convergence.minorityU σ c' + 1 ≤ Phase7Convergence.minorityU σ c} := by
  refine le_trans ?_ (Phase8Convergence.minorityU_drop_prob_rect σ n hn c hInv i)
  -- E ≤ (#min·#elim), since #min ≥ 1 and #elim ≥ E.
  have hprod : (E : ℕ) ≤
      (Phase8Convergence.minorityAt (L := L) (K := K) σ i).sum c.count *
        (Phase8Convergence.elimAbove (L := L) (K := K) σ i).sum c.count := by
    calc (E : ℕ) ≤ 1 * E := by omega
      _ ≤ (Phase8Convergence.minorityAt (L := L) (K := K) σ i).sum c.count * E :=
          Nat.mul_le_mul_right _ hmin
      _ ≤ (Phase8Convergence.minorityAt (L := L) (K := K) σ i).sum c.count *
            (Phase8Convergence.elimAbove (L := L) (K := K) σ i).sum c.count :=
          Nat.mul_le_mul_left _ helim
  have hnR : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  apply DrainThreading.ofReal_div_le_of_num_le _ (by positivity) (by nlinarith)
  exact_mod_cast hprod

/-- **Phase 8 — the levels-engine `hdrop` from the structural floor.**  At a level `m`
with the carried witness floor (`≥ 1` minority and eliminator margin `≥ E` at some level
`i`), the level-`m` failure mass is `≤ 1 − ofReal(E/(n(n−1)))`. -/
theorem phase8_hdrop_of_struct {L K : ℕ} (σ : Sign) (n m : ℕ) (hn : 2 ≤ n)
    (b : Config (AgentState L K)) (hb8 : Phase8Convergence.Phase8AllMain n b)
    (hbm : Phase7Convergence.minorityU σ b = m)
    (i : Fin (L + 1)) (E : ℕ)
    (hmin : 1 ≤ (Phase8Convergence.minorityAt (L := L) (K := K) σ i).sum b.count)
    (helim : E ≤ (Phase8Convergence.elimAbove (L := L) (K := K) σ i).sum b.count) :
    (NonuniformMajority L K).transitionKernel b
        (OneSidedCancel.potBelow (Phase7Convergence.minorityU σ) m)ᶜ
      ≤ 1 - ENNReal.ofReal ((E : ℝ) / ((n : ℝ) * ((n : ℝ) - 1))) :=
  Phase8Convergence.minorityU_hdrop_of_floor σ n m
    (ENNReal.ofReal ((E : ℝ) / ((n : ℝ) * ((n : ℝ) - 1)))) b hb8 hbm
    (phase8_drop_floor_of_struct σ n hn b hb8 i E hmin helim)

/-- **Phase 8 — the crude-engine `hstep` from the structural floor, at `m = 1`.**  When
`minorityU σ b = 1` the strict-drop event reaches `potDone`, so the structural floor gives
the crude `hstep` failure `(potDone)ᶜ ≤ 1 − ofReal(E/(n(n−1)))`.  (For `minorityU σ b ≥ 2`
a single drain cannot reach `potDone`, so the crude `hstep` is structurally vacuous there;
the honest multi-level drain uses `phase8_hdrop_of_struct` + the levels engine.) -/
theorem phase8_hstep_of_struct_one {L K : ℕ} (σ : Sign) (n : ℕ) (hn : 2 ≤ n)
    (b : Config (AgentState L K)) (hb8 : Phase8Convergence.Phase8AllMain n b)
    (hb1 : Phase7Convergence.minorityU σ b = 1)
    (i : Fin (L + 1)) (E : ℕ)
    (hmin : 1 ≤ (Phase8Convergence.minorityAt (L := L) (K := K) σ i).sum b.count)
    (helim : E ≤ (Phase8Convergence.elimAbove (L := L) (K := K) σ i).sum b.count) :
    (NonuniformMajority L K).transitionKernel b
        (OneSidedCancel.potDone (fun c => Phase7Convergence.minorityU σ c))ᶜ
      ≤ 1 - ENNReal.ofReal ((E : ℝ) / ((n : ℝ) * ((n : ℝ) - 1))) := by
  have hdone_eq :
      (OneSidedCancel.potDone (fun c : Config (AgentState L K) =>
          Phase7Convergence.minorityU σ c))ᶜ
      = (OneSidedCancel.potBelow (fun c : Config (AgentState L K) =>
          Phase7Convergence.minorityU σ c) 1)ᶜ := by
    ext y
    simp only [OneSidedCancel.potDone, OneSidedCancel.potBelow,
      Set.mem_compl_iff, Set.mem_setOf_eq]; omega
  rw [hdone_eq]
  exact phase8_hdrop_of_struct σ n 1 hn b hb8 hb1 i E hmin helim

/-! ## Part C — Phase 7 (`classMassN σ`, `Inv7Sum`, α = 4/15).

The carried eliminator floor (Doty Lemma 7.4 `elimGap1 ≥ 0.8·mainCount ≥ 4n/15`) supplies,
at a gap-1 witness pair of levels `(i, j)` with `j = i + 1`, an eliminator margin
`(elimGap1 σ i).sum count ≥ E` and at least one minority at the larger level `j`
(`(minorityAt7 σ j).sum count ≥ 1`).  Threaded through `classMassN_drop_prob_rect7`, this
yields the drop floor `ofReal(E/(n(n−1))) ≤ classMass-drop-mass`, which the existing
packagers `classMassN_hdrop_of_floor7` (levels) / `classMassN_hstep_of_floor7` (crude
`m = 1`) turn into the engine `hdrop` / `hstep`. -/

/-- **Phase 7 — structural floor ⟹ concrete σ-class-mass drop floor.**  At a gap-1 witness
`(i, j=i+1)` with `≥ 1` minority at `j` and eliminator margin `≥ E` at `i`, the one-step
drop probability of `classMassN σ` is `≥ ofReal(E/(n(n−1)))`. -/
theorem phase7_drop_floor_of_struct {L K : ℕ} (σ : Sign) (n : ℕ) (hn : 2 ≤ n)
    (c : Config (AgentState L K)) (hInv : Phase7Convergence.Phase7AllMain n c)
    (i j : Fin (L + 1)) (hg1 : i.val + 1 = j.val) (E : ℕ)
    (hmin : 1 ≤ (Phase7Convergence.minorityAt7 (L := L) (K := K) σ j).sum c.count)
    (helim : E ≤ (Phase7Convergence.elimGap1 (L := L) (K := K) σ i).sum c.count) :
    ENNReal.ofReal ((E : ℝ) / ((n : ℝ) * ((n : ℝ) - 1))) ≤
      ((NonuniformMajority L K).stepDistOrSelf c).toMeasure
        {c' | Phase7Convergence.classMassN σ c' + 1 ≤ Phase7Convergence.classMassN σ c} := by
  refine le_trans ?_ (Phase7Convergence.classMassN_drop_prob_rect7 σ n hn c hInv i j hg1)
  have hprod : (E : ℕ) ≤
      (Phase7Convergence.elimGap1 (L := L) (K := K) σ i).sum c.count *
        (Phase7Convergence.minorityAt7 (L := L) (K := K) σ j).sum c.count := by
    calc (E : ℕ) ≤ E * 1 := by omega
      _ ≤ E * (Phase7Convergence.minorityAt7 (L := L) (K := K) σ j).sum c.count :=
          Nat.mul_le_mul_left _ hmin
      _ ≤ (Phase7Convergence.elimGap1 (L := L) (K := K) σ i).sum c.count *
            (Phase7Convergence.minorityAt7 (L := L) (K := K) σ j).sum c.count :=
          Nat.mul_le_mul_right _ helim
  have hnR : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  apply DrainThreading.ofReal_div_le_of_num_le _ (by positivity) (by nlinarith)
  exact_mod_cast hprod

/-- **Phase 7 — the levels-engine `hdrop` from the structural floor.** -/
theorem phase7_hdrop_of_struct {L K : ℕ} (σ : Sign) (n m : ℕ) (hn : 2 ≤ n)
    (b : Config (AgentState L K)) (hb7 : Phase7Convergence.Phase7AllMain n b)
    (hbm : Phase7Convergence.classMassN σ b = m)
    (i j : Fin (L + 1)) (hg1 : i.val + 1 = j.val) (E : ℕ)
    (hmin : 1 ≤ (Phase7Convergence.minorityAt7 (L := L) (K := K) σ j).sum b.count)
    (helim : E ≤ (Phase7Convergence.elimGap1 (L := L) (K := K) σ i).sum b.count) :
    (NonuniformMajority L K).transitionKernel b
        (OneSidedCancel.potBelow (Phase7Convergence.classMassN σ) m)ᶜ
      ≤ 1 - ENNReal.ofReal ((E : ℝ) / ((n : ℝ) * ((n : ℝ) - 1))) :=
  Phase7Convergence.classMassN_hdrop_of_floor7 σ m
    (ENNReal.ofReal ((E : ℝ) / ((n : ℝ) * ((n : ℝ) - 1)))) b hbm
    (phase7_drop_floor_of_struct σ n hn b hb7 i j hg1 E hmin helim)

/-- **Phase 7 — the crude-engine `hstep` from the structural floor, at `m = 1`.**  At
`classMassN σ b = 1` the strict-drop event reaches `potDone`, so the structural floor gives
the crude `hstep` failure `(potDone)ᶜ ≤ 1 − ofReal(E/(n(n−1)))`.  (For `classMassN σ b ≥ 2`
a single cancel drops the mass by `≥ 1` but not to `0`, so the crude `hstep` is structurally
vacuous there; the honest multi-level mass drain uses `phase7_hdrop_of_struct` + levels.) -/
theorem phase7_hstep_of_struct_one {L K : ℕ} (σ : Sign) (n : ℕ) (hn : 2 ≤ n)
    (b : Config (AgentState L K)) (hb7 : Phase7Convergence.Phase7AllMain n b)
    (hb1 : Phase7Convergence.classMassN σ b = 1)
    (i j : Fin (L + 1)) (hg1 : i.val + 1 = j.val) (E : ℕ)
    (hmin : 1 ≤ (Phase7Convergence.minorityAt7 (L := L) (K := K) σ j).sum b.count)
    (helim : E ≤ (Phase7Convergence.elimGap1 (L := L) (K := K) σ i).sum b.count) :
    (NonuniformMajority L K).transitionKernel b
        (OneSidedCancel.potDone (fun c => Phase7Convergence.classMassN σ c))ᶜ
      ≤ 1 - ENNReal.ofReal ((E : ℝ) / ((n : ℝ) * ((n : ℝ) - 1))) :=
  Phase7Convergence.classMassN_hstep_of_floor7 σ
    (ENNReal.ofReal ((E : ℝ) / ((n : ℝ) * ((n : ℝ) - 1)))) b hb1
    (phase7_drop_floor_of_struct σ n hn b hb7 i j hg1 E hmin helim)

end DrainThreading

end ExactMajority
