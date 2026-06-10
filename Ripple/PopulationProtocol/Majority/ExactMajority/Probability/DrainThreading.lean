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

end DrainThreading

end ExactMajority
