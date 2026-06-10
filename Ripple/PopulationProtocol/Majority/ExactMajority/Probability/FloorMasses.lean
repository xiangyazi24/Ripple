/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# FloorMasses — discharging the three protocol-mass residuals of FloorPrefix

This file is **append-only** and discharges the three named protocol hypotheses that
`Probability/FloorPrefix.lean` left as inputs to `pool_expNeg_one_step_drift`:

* **`hstep`** — the `±2` per-step interaction range: `∀ᵐ c', (pool c : ℤ) − 2 ≤ pool c'`
  on the one-step kernel (Stage 1).
* **`hbirth`** — the Rule-1 birth rectangle: `ofReal(uMin(uMin−1)/(n(n−1))) ≤ birthR1Mass c`
  on `PoolDriftRegion` (Stage 2).
* **`hdeath`** — the Rule-4 fresh-CR drain rectangle: `r4FreshCRDrainMass c ≤
  ofReal(Ahi²/(n(n−1)))` on `PoolDriftRegion` (Stage 3).

All three follow the established kernel-mass routes:

* Stage 1 reuses `HourCouplingV2.countP_stepOrSelf_diff_le_two` (the bounded-difference
  atom: any single interaction changes a `countP` by at most `2`) plus the support
  reduction of `hour_bdd`.  `assignableCount = countP isAssignableBool` is definitional.
* Stage 2 mirrors `RoleSplitConcentration.phase0_mcrCount_decrease_prob_oneSided`'s
  rectangle route (`stepDistOrSelf_toMeasure_ge` over a `good` pair set whose image lands
  in the target), with the MCR×MCR diagonal mass `mcrCount·(mcrCount−1)/(n(n−1))` and the
  config-level R1 birth `+2` effect from `assignable_rule1_both_fresh`.
* Stage 3 is the upper-bound dual: `stepDist`'s mass on `{pool drops}` equals the
  `interactionPMF` mass on the preimage; that preimage is contained in the block square of
  the *assignable* agents (a pool drop deletes an assignable agent, so a drop requires both
  members assignable); the block bound `pair_block_prob_le_sq` (cloned for `AgentState`)
  caps it by `(assignableCount/n)² ≤ Ahi²/(n(n−1))`.

Stage 4 instantiates `FloorPrefix.pool_expNeg_one_step_drift` with all three facts, leaving
only the (pure-scalar, already-proven) favorability and the analytic core.
-/

import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.FloorPrefix
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.HourCouplingV2

namespace ExactMajority
namespace FloorMasses

open MeasureTheory ProbabilityTheory RoleSplitConcentration FloorPrefix
open scoped ENNReal NNReal Real BigOperators

variable {L K : ℕ}

/-! ## Stage 1 — `hstep`: the `±2` per-step interaction range.

`assignableCount` is a `countP`, and `HourCouplingV2.countP_stepOrSelf_diff_le_two` already
shows any single chosen-pair update changes any `countP` by at most `2`.  Lifting to the
one-step kernel via the support reduction (every support point is `stepOrSelf c r₁ r₂` or
`c` itself) gives the a.e. lower bound `pool c − 2 ≤ pool c'`. -/

/-- **The single-step lower bound on `assignableCount`.**  For every chosen ordered pair,
the successor `assignableCount` is at least `assignableCount c − 2` (the deterministic `±2`
interaction range, `countP_stepOrSelf_diff_le_two` specialised to `isAssignableBool`). -/
theorem assignableCount_stepOrSelf_ge
    (c : Config (AgentState L K)) (r₁ r₂ : AgentState L K) :
    (assignableCount (L := L) (K := K) c : ℤ) - 2
      ≤ (assignableCount (L := L) (K := K)
          (Protocol.stepOrSelf (NonuniformMajority L K) c r₁ r₂) : ℤ) := by
  have h := (HourCouplingV2.countP_stepOrSelf_diff_le_two
    (fun a => isAssignableBool (L := L) (K := K) a = true) c r₁ r₂).2
  -- `assignableCount = countP isAssignableBool` (definitional).
  simpa only [assignableCount_eq_countP] using by linarith [h]

/-- **`hstep` (general form).**  On the one-step kernel from any `c`, almost every successor
`c'` satisfies `assignableCount c − 2 ≤ assignableCount c'`.  Support reduction (mirrors
`HourCouplingV2.hour_bdd`): every support point is `stepOrSelf c r₁ r₂` (or `c` itself, the
trivial case). -/
theorem pool_step_ge_ae (c : Config (AgentState L K)) :
    ∀ᵐ c' ∂((NonuniformMajority L K).transitionKernel c),
      (assignableCount (L := L) (K := K) c : ℤ) - 2
        ≤ (assignableCount (L := L) (K := K) c' : ℤ) := by
  classical
  -- It suffices to verify the bound on every support point.
  have hsupp : ∀ c' ∈ ((NonuniformMajority L K).stepDistOrSelf c).support,
      (assignableCount (L := L) (K := K) c : ℤ) - 2
        ≤ (assignableCount (L := L) (K := K) c' : ℤ) := by
    intro c' hc'
    have hcase : (∃ r₁ r₂, Protocol.stepOrSelf (NonuniformMajority L K) c r₁ r₂ = c')
        ∨ c' = c := by
      by_cases hc : 2 ≤ c.card
      · rw [show (NonuniformMajority L K).stepDistOrSelf c
            = (NonuniformMajority L K).stepDist c hc by
            unfold Protocol.stepDistOrSelf; rw [dif_pos hc]] at hc'
        obtain ⟨⟨r₁, r₂⟩, hr⟩ :=
          Protocol.stepDist_support (NonuniformMajority L K) c hc c' hc'
        exact Or.inl ⟨r₁, r₂, hr⟩
      · rw [show (NonuniformMajority L K).stepDistOrSelf c = PMF.pure c by
            unfold Protocol.stepDistOrSelf; rw [dif_neg hc]] at hc'
        rw [PMF.mem_support_pure_iff] at hc'
        exact Or.inr hc'
    rcases hcase with ⟨r₁, r₂, hstep⟩ | hcx
    · rw [← hstep]; exact assignableCount_stepOrSelf_ge c r₁ r₂
    · rw [hcx]; omega
  -- Lift the support bound to a.e. (kernel = `stepDistOrSelf c`'s toMeasure).
  change ∀ᵐ c' ∂((NonuniformMajority L K).stepDistOrSelf c).toMeasure, _
  rw [ae_iff]
  change ((NonuniformMajority L K).stepDistOrSelf c).toMeasure
    {c' | ¬ (assignableCount (L := L) (K := K) c : ℤ) - 2
        ≤ (assignableCount (L := L) (K := K) c' : ℤ)} = 0
  rw [PMF.toMeasure_apply_eq_zero_iff _ (DiscreteMeasurableSpace.forall_measurableSet _)]
  rw [Set.disjoint_left]
  intro c' hc' hbad
  exact hbad (hsupp c' hc')

end FloorMasses
end ExactMajority
