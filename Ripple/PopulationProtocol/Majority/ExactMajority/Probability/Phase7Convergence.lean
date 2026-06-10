/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Phase 7 — one-sided cancellation of high-level minority mass (Doty et al. §6, Phase 7)

`Phase7Transition` (Protocol/Transition.lean:1303) cancels opposite-sign Main
agents whose exponent **gap is ≤ 2**, via `cancelSplit`:

```
def Phase7Transition (s t) :=
  if s.role = .main ∧ t.role = .main then cancelSplit L K s t
  else (s,t)   -- (clock agents run the counter subroutine)
```

and `cancelSplit` (Transition.lean:1213) on two opposite-sign dyadic biases
`±2^{-i}`, `∓2^{-j}`:

* gap 0 (`i = j`):      both become `.zero`           (full cancel);
* gap 1 (`i+1 = j`):    `s ↦ 2^{-(i+1)}`, `t ↦ 0`     (one-sided drain of `t`);
* gap 2 (`i+2 = j`):    `s ↦ ±2^{-(i+1)}`, `t ↦ ±2^{-(i+2)}` (both take `s`'s sign);
* gap ≥ 3:              no change.

The **minority** sign is a fixed parameter `σ : Sign`; the **majority/eliminator**
sign is `σ.flip`.  After Phase 6 (Lemma 7.3) at least `0.87|M|` Main agents
remain, the vast majority of the majority sign; the few minority agents sit at
exponent levels `i ∈ {l, l+1, l+2}` (Theorem 6.2 / Phase-6 output).  Each cancel
reaction strictly removes one minority agent OR keeps the minority count fixed and
never creates a new minority agent.

## Honest predicate / potential choices (vs the HANDOFF sketch placeholders)

The sketch named `Phase6PostCore`, `NoMinorityAtOrAboveL2`, `IsMinority`,
`initialMainCount` — none of which exist in the repo.  We read honest in-file
predicates off the actual `cancelSplit` / `Phase7Transition` rule:

* `minoritySt σ a` — `a` is a Main with a `σ`-signed dyadic bias (the minority);
* `minorityU σ c`  — the count of such agents (the Doty `|B|`, the target pool);
* `Inv7 σ n c`     — the carried Phase-6/7 structural invariant: size `n`, every
  agent at phase 7, and the **minority-non-creation** structural fact
  `MinorityClosed σ` (no `Transition` step ever turns a non-`σ` agent into a
  `σ`-Main), which is exactly what `PotNonincrOn` needs and which holds because
  `cancelSplit`'s outputs only ever carry sign `s.sign` (never introduce a *new*
  minority sign on a non-minority agent — verified per-pair).

The potential `Φ = minorityU σ` is non-increasing under the real kernel
(`minorityU_pow_noincr`), and `{Φ = 0}` is exactly `NoMinority σ`, the Phase-7
post `NoMinorityAtOrAboveL2` rendered honestly (no minority agent remains at all —
stronger than the paper's "below −(l+2)", which is the form the cancellation engine
delivers since cancellation drains the WHOLE minority pool).

This file instantiates `OneSidedCancel.crude_PhaseConvergenceW` (form b) — the
honest uniform per-step drain engine — with `Inv = Inv7 σ n`, `Φ = minorityU σ`,
and the per-step drop `q` supplied by the eliminator-floor rectangle bound
`minority_drain_prob`.  The level-decomposed form (a) `levels_PhaseConvergenceW`
is documented at the foot of the file as the paper-faithful `O(n log n)` upgrade;
the crude form already delivers the whp tail at horizon `Θ(n² log n)` with the
honest `0.8|M|` eliminator floor.

NEW file; no existing file is edited; no sorry/admit/axiom/native_decide.
-/

import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.OneSidedCancel
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.PhaseConvergenceWeak
import Ripple.PopulationProtocol.Majority.ExactMajority.Analysis.Invariants

namespace ExactMajority

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace Phase7Convergence

variable {L K : ℕ}

attribute [local instance] Classical.propDecidable

instance instMeasurableSpaceAgentState7 : MeasurableSpace (AgentState L K) := ⊤
instance instDiscreteMeasurableSpaceAgentState7 :
    DiscreteMeasurableSpace (AgentState L K) where
  forall_measurableSet _ := trivial

/-! ## Part A — the minority predicate and count. -/

/-- An agent is a **minority** agent (sign `σ`) if it is a Main holding a
`σ`-signed dyadic bias.  This is the Doty `B`-pool: the opposite-sign agents being
drained by the `σ.flip` majority eliminators. -/
def minoritySt (σ : Sign) (a : AgentState L K) : Prop :=
  a.role = Role.main ∧ ∃ i : Fin (L + 1), a.bias = Bias.dyadic σ i

/-- A bias-side characterization of `minoritySt`: the bias is `σ`-signed dyadic. -/
def biasIsSigned (σ : Sign) (b : Bias L) : Prop :=
  match b with
  | .zero => False
  | .dyadic s _ => s = σ

instance (σ : Sign) (b : Bias L) : Decidable (biasIsSigned σ b) := by
  unfold biasIsSigned; cases b <;> infer_instance

theorem minoritySt_iff (σ : Sign) (a : AgentState L K) :
    minoritySt σ a ↔ a.role = Role.main ∧ biasIsSigned σ a.bias := by
  unfold minoritySt biasIsSigned
  cases hb : a.bias with
  | zero => simp
  | dyadic s i =>
      constructor
      · rintro ⟨hr, j, hj⟩; injection hj with hjs _; exact ⟨hr, hjs⟩
      · rintro ⟨hr, hs⟩; exact ⟨hr, i, by rw [hs]⟩

instance (σ : Sign) (a : AgentState L K) : Decidable (minoritySt σ a) :=
  decidable_of_iff _ (minoritySt_iff σ a).symm

/-- The minority count (the Doty `|B|`). -/
def minorityU (σ : Sign) (c : Config (AgentState L K)) : ℕ :=
  Multiset.countP (fun a => minoritySt σ a) c

/-! ## Part B — the per-pair reduction to `cancelSplit` for two phase-7 Mains. -/

/-- For two phase-7 agents, `phaseEpidemicUpdate` is the identity (max of equal
phases, no init to run, no phase-10 entry).  Mirror of Phase 4's
`phaseEpidemicUpdate_eq_self_of_phase4` at threshold 7. -/
theorem phaseEpidemicUpdate_eq_self_of_phase7 (s t : AgentState L K)
    (hs : s.phase.val = 7) (ht : t.phase.val = 7) :
    phaseEpidemicUpdate L K s t = (s, t) := by
  have hsp : s.phase = ⟨7, by decide⟩ := Fin.ext hs
  have htp : t.phase = ⟨7, by decide⟩ := Fin.ext ht
  unfold phaseEpidemicUpdate
  rw [hsp, htp, max_self]
  simp only [runInitsBetween_self_api]
  have hs_self : ({s with phase := (⟨7, by decide⟩ : Fin 11)} : AgentState L K) = s := by
    rw [← hsp]
  have ht_self : ({t with phase := (⟨7, by decide⟩ : Fin 11)} : AgentState L K) = t := by
    rw [← htp]
  rw [hs_self, ht_self]
  rw [if_neg (by push Not; intro _; simp)]

/-- `cancelSplit` never changes an agent's phase (it only rewrites `.bias`). -/
theorem cancelSplit_phase (s t : AgentState L K) :
    (cancelSplit L K s t).1.phase = s.phase ∧ (cancelSplit L K s t).2.phase = t.phase := by
  unfold cancelSplit
  match s.bias, t.bias with
  | .zero, _ => simp
  | .dyadic _ _, .zero => simp
  | .dyadic sgn_s i, .dyadic sgn_t j => simp; split_ifs <;> simp

/-- **Per-pair reduction.**  Two phase-7 Main agents interact via `cancelSplit`
under the full `Transition` (epidemic = id, dispatch = `Phase7Transition`, no
phase-10 finish since phase stays 7, and neither is a clock so the counter branch
is skipped). -/
theorem Transition_eq_cancelSplit_of_phase7_main (s t : AgentState L K)
    (hs7 : s.phase.val = 7) (ht7 : t.phase.val = 7)
    (hsM : s.role = Role.main) (htM : t.role = Role.main) :
    Transition L K s t = cancelSplit L K s t := by
  have hepi := phaseEpidemicUpdate_eq_self_of_phase7 (L := L) (K := K) s t hs7 ht7
  have hsp : s.phase = ⟨7, by decide⟩ := Fin.ext hs7
  -- Phase7Transition with both Main, neither clock = cancelSplit.
  have hnsclk : s.role ≠ Role.clock := by rw [hsM]; decide
  have hntclk : t.role ≠ Role.clock := by rw [htM]; decide
  have hp7 : Phase7Transition L K s t = cancelSplit L K s t := by
    unfold Phase7Transition
    simp only [if_pos (show s.role = Role.main ∧ t.role = Role.main from ⟨hsM, htM⟩),
      cancelSplit_role_fst, cancelSplit_role_snd,
      if_neg hnsclk, if_neg hntclk]
  obtain ⟨hcs1, hcs2⟩ := cancelSplit_phase (L := L) (K := K) s t
  unfold Transition
  rw [hepi]
  simp only [hsp]
  rw [show (Phase7Transition L K s t) = cancelSplit L K s t from hp7]
  rw [finishPhase10Entry_eq_self_of_after_ne_10 (L := L) (K := K) s _ (by rw [hcs1, hs7]; omega),
      finishPhase10Entry_eq_self_of_after_ne_10 (L := L) (K := K) t _ (by rw [hcs2, ht7]; omega)]

end Phase7Convergence

end ExactMajority

#print axioms ExactMajority.Phase7Convergence.Transition_eq_cancelSplit_of_phase7_main
