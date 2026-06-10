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

/-! ## Stage 2 — `hbirth`: the Rule-1 birth rectangle.

A single interaction between two **fresh** (unassigned, phase-0) MCR agents fires Rule 1
(`MCR,MCR → Main,CR`) and produces two fresh assignables, raising the pool by exactly `+2`
(`assignable_rule1_both_fresh`).  The good ordered pairs are the `freshMcrF ×ˢ freshMcrF`
off-diagonal rectangle; its `interactionPMF` mass is `freshMcrCount·(freshMcrCount−1)/(n(n−1))`
(`sum_interactionCount_freshMcr`), and `stepDistOrSelf_toMeasure_ge` lifts it onto the
birth band `{c' | pool c + 2 ≤ pool c'}` whose mass is `birthR1Mass`.

The honest count carried by R1 is the **unassigned** phase-0 MCR count `freshMcrCount`, *not*
the bare `mcrCount`: an *assigned* MCR (allowed by `cardPhaseShell`, which only fixes
`role = mcr → phase 0`) would not produce two fresh assignables.  See the Stage-2 wrap-up
note for the `hbirth` adapter, which holds verbatim once `uMin ≤ freshMcrCount`. -/

/-- The fresh-MCR predicate: an unassigned phase-0 MCR (a Rule-1 initiator/responder). -/
def isFreshMcr (a : AgentState L K) : Bool :=
  decide (a.role = .mcr) && (!a.assigned) && decide (a.phase.val = 0)

theorem isFreshMcr_iff (a : AgentState L K) :
    isFreshMcr (L := L) (K := K) a = true ↔
      a.role = .mcr ∧ a.assigned = false ∧ a.phase.val = 0 := by
  unfold isFreshMcr
  simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_true_eq]
  tauto

/-- Count of fresh (unassigned phase-0) MCR agents — the honest R1-birth initiator pool. -/
def freshMcrCount (c : Config (AgentState L K)) : ℕ :=
  Multiset.countP (fun a => isFreshMcr (L := L) (K := K) a) c

/-! ### The Transition→Phase0Transition full bridge for a fresh-MCR pair. -/

/-- When both inputs are fresh (unassigned phase-0) MCR, the full `Transition` equals the
phase-0 reaction `Phase0Transition`: `phaseEpidemicUpdate` is the identity (both at phase 0),
and the post-step `finishPhase10Entry` is the identity since the Rule-1 outputs are at phase
0 (≠ 10, both `IsAssignable`). -/
theorem Transition_eq_phase0_of_fresh_mcr_pair
    (s t : AgentState L K)
    (hs_role : s.role = .mcr) (ht_role : t.role = .mcr)
    (hs_un : s.assigned = false) (ht_un : t.assigned = false)
    (hs_ph : s.phase.val = 0) (ht_ph : t.phase.val = 0) :
    Transition L K s t = Phase0Transition L K s t := by
  have hpe := phaseEpidemicUpdate_eq_self_of_both_phase0 (L := L) (K := K) s t hs_ph ht_ph
  have hs0 : s.phase = (⟨0, by omega⟩ : Fin _) := Fin.ext hs_ph
  -- The Phase0Transition outputs are both assignable, hence at phase 0 (≠ 10).
  obtain ⟨hout1, hout2⟩ :=
    assignable_rule1_both_fresh s t hs_role ht_role hs_un ht_un hs_ph ht_ph
  have hout1_ph : (Phase0Transition L K s t).1.phase.val ≠ 10 := by
    rw [hout1.1]; omega
  have hout2_ph : (Phase0Transition L K s t).2.phase.val ≠ 10 := by
    rw [hout2.1]; omega
  unfold Transition
  rw [hpe]
  simp only
  rw [hs0]
  rw [finishPhase10Entry_eq_self_of_after_ne_10 (L := L) (K := K) _ _ hout1_ph,
      finishPhase10Entry_eq_self_of_after_ne_10 (L := L) (K := K) _ _ hout2_ph]

/-- **Config-level Rule-1 birth `+2`.**  When the chosen pair `{s,t} ≤ c` are both fresh
MCR, the successor config raises the pool by exactly `2`: the removed pair carries `0`
assignables (MCR ⟹ not assignable) and the output carries `2` (`assignable_rule1_both_fresh`),
so `assignableCount (c − {s,t} + outputs) = assignableCount c + 2`. -/
theorem birthR1_config_eq
    (c : Config (AgentState L K)) (s t : AgentState L K)
    (h_sub : ({s, t} : Config (AgentState L K)) ≤ c)
    (hs_role : s.role = .mcr) (ht_role : t.role = .mcr)
    (hs_un : s.assigned = false) (ht_un : t.assigned = false)
    (hs_ph : s.phase.val = 0) (ht_ph : t.phase.val = 0) :
    assignableCount (L := L) (K := K)
        (c - {s, t} + {(Transition L K s t).1, (Transition L K s t).2})
      = assignableCount (L := L) (K := K) c + 2 := by
  have h_restore : c - {s, t} + {s, t} = c := Multiset.sub_add_cancel h_sub
  -- The output pair carries exactly 2 assignables; the input pair carries 0.
  obtain ⟨hout1, hout2⟩ :=
    assignable_rule1_both_fresh s t hs_role ht_role hs_un ht_un hs_ph ht_ph
  have htr := Transition_eq_phase0_of_fresh_mcr_pair s t hs_role ht_role hs_un ht_un hs_ph ht_ph
  have hpair_out : assignableCount (L := L) (K := K)
      ({(Transition L K s t).1, (Transition L K s t).2} : Config (AgentState L K)) = 2 := by
    rw [htr, assignableCount_pair',
      (isAssignableBool_iff _).mpr hout1, (isAssignableBool_iff _).mpr hout2]
    simp
  have hpair_in : assignableCount (L := L) (K := K)
      ({s, t} : Config (AgentState L K)) = 0 := by
    rw [assignableCount_pair',
      not_isAssignable_of_mcr (L := L) (K := K) hs_role,
      not_isAssignable_of_mcr (L := L) (K := K) ht_role]
    simp
  -- `assignableCount` is additive over multiset `+`.
  have hadd : ∀ x y : Config (AgentState L K),
      assignableCount (L := L) (K := K) (x + y)
        = assignableCount (L := L) (K := K) x + assignableCount (L := L) (K := K) y :=
    fun x y => Multiset.countP_add _ _ _
  calc assignableCount (L := L) (K := K)
          (c - {s, t} + {(Transition L K s t).1, (Transition L K s t).2})
      = assignableCount (L := L) (K := K) (c - {s, t}) + 2 := by
        rw [hadd, hpair_out]
    _ = assignableCount (L := L) (K := K) (c - {s, t})
          + assignableCount (L := L) (K := K) ({s, t} : Config (AgentState L K)) + 2 := by
        rw [hpair_in]
    _ = assignableCount (L := L) (K := K) (c - {s, t} + {s, t}) + 2 := by
        rw [hadd]
    _ = assignableCount (L := L) (K := K) c + 2 := by rw [h_restore]

/-! ### The fresh-MCR rectangle (`freshMcrF ×ˢ freshMcrF`). -/

/-- The fresh-MCR initiator/responder Finset. -/
def freshMcrF : Finset (AgentState L K) :=
  Finset.univ.filter (fun s : AgentState L K => isFreshMcr (L := L) (K := K) s = true)

/-- `∑_{s ∈ freshMcrF} count s = freshMcrCount`. -/
theorem sum_count_freshMcrF (c : Config (AgentState L K)) :
    ∑ s ∈ freshMcrF (L := L) (K := K), c.count s =
      freshMcrCount (L := L) (K := K) c := by
  set F := freshMcrF (L := L) (K := K) with hF
  set cm := Multiset.filter (fun a : AgentState L K =>
    isFreshMcr (L := L) (K := K) a = true) c with hcm
  have hcount : ∀ s ∈ F, c.count s = Multiset.count s cm := fun s hs => by
    show Multiset.count s c = Multiset.count s cm
    have hs_fresh : isFreshMcr (L := L) (K := K) s = true := (Finset.mem_filter.mp hs).2
    simp only [cm, Multiset.count_filter, hs_fresh, ite_true]
  calc ∑ s ∈ F, c.count s
      = ∑ s ∈ F, Multiset.count s cm := Finset.sum_congr rfl hcount
    _ = Multiset.card cm :=
        Multiset.sum_count_eq_card (s := F) (m := cm)
          (fun a ha => Finset.mem_filter.mpr ⟨Finset.mem_univ a,
            (Multiset.mem_filter.mp ha).2⟩)
    _ = freshMcrCount (L := L) (K := K) c := by
        rw [freshMcrCount, hcm, ← Multiset.countP_eq_card_filter]

/-- For a fixed fresh-MCR initiator `s₁`, the row sum of `interactionCount s₁ s₂` over
fresh-MCR responders is `count s₁ · (freshMcrCount − 1)`.  (Diagonal `s₁ = s₂` subtracts
one; mirror of `sum_interactionCount_mcrF_right`.) -/
theorem sum_interactionCount_freshMcrF_right (c : Config (AgentState L K))
    (s₁ : AgentState L K) (hs₁ : isFreshMcr (L := L) (K := K) s₁ = true) :
    ∑ s₂ ∈ freshMcrF (L := L) (K := K), c.interactionCount s₁ s₂ =
      c.count s₁ * (freshMcrCount (L := L) (K := K) c - 1) := by
  set F := freshMcrF (L := L) (K := K) with hF
  by_cases hzero : c.count s₁ = 0
  · have hall : ∀ s₂ ∈ F, c.interactionCount s₁ s₂ = 0 := fun s₂ _ => by
      unfold Config.interactionCount Config.count
      unfold Config.count at hzero
      split_ifs with h
      · subst h; simp [hzero]
      · simp [hzero]
    rw [Finset.sum_eq_zero hall]; simp [hzero]
  · have hfactor : ∀ s₂ ∈ F, c.interactionCount s₁ s₂ =
        c.count s₁ * if s₁ = s₂ then c.count s₁ - 1 else c.count s₂ := by
      intro s₂ _; unfold Config.interactionCount
      by_cases h : s₁ = s₂ <;> simp [h]
    rw [Finset.sum_congr rfl hfactor, ← Finset.mul_sum]; congr 1
    have hs₁F : s₁ ∈ F := Finset.mem_filter.mpr ⟨Finset.mem_univ s₁, hs₁⟩
    set f : AgentState L K → ℕ :=
      fun s₂ => if s₁ = s₂ then c.count s₁ - 1 else c.count s₂ with hfdef
    have hf_s₁ : f s₁ = c.count s₁ - 1 := if_pos rfl
    have hf_ne : ∀ s₂ ∈ F.erase s₁, f s₂ = c.count s₂ :=
      fun s₂ hs₂ => if_neg (Finset.ne_of_mem_erase hs₂).symm
    calc ∑ s₂ ∈ F, f s₂
        = f s₁ + ∑ s₂ ∈ F.erase s₁, f s₂ := (Finset.add_sum_erase F f hs₁F).symm
      _ = (c.count s₁ - 1) + ∑ s₂ ∈ F.erase s₁, c.count s₂ := by
          rw [hf_s₁, Finset.sum_congr rfl hf_ne]
      _ = freshMcrCount (L := L) (K := K) c - 1 := by
          have hse : c.count s₁ + ∑ s₂ ∈ F.erase s₁, c.count s₂ =
              freshMcrCount (L := L) (K := K) c := by
            rw [Finset.add_sum_erase F (fun s => c.count s) hs₁F]
            exact sum_count_freshMcrF c
          have hcount_pos : 0 < c.count s₁ := Nat.pos_of_ne_zero hzero
          omega

/-- The fresh-MCR×fresh-MCR rectangle sum `= freshMcrCount·(freshMcrCount−1)`. -/
theorem sum_interactionCount_freshMcr (c : Config (AgentState L K)) :
    ∑ s₁ ∈ freshMcrF (L := L) (K := K), ∑ s₂ ∈ freshMcrF (L := L) (K := K),
        c.interactionCount s₁ s₂ =
      freshMcrCount (L := L) (K := K) c * (freshMcrCount (L := L) (K := K) c - 1) := by
  have hstep : ∀ s₁ ∈ freshMcrF (L := L) (K := K),
      ∑ s₂ ∈ freshMcrF (L := L) (K := K), c.interactionCount s₁ s₂ =
        c.count s₁ * (freshMcrCount (L := L) (K := K) c - 1) := fun s₁ hs₁ =>
    sum_interactionCount_freshMcrF_right c s₁ (Finset.mem_filter.mp hs₁).2
  rw [Finset.sum_congr rfl hstep, ← Finset.sum_mul, sum_count_freshMcrF]

end FloorMasses
end ExactMajority
