/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Phase 4 — tie detection / non-tie continuation (Doty et al. §6, Phase 4)

`Phase4Transition` (Protocol/Transition.lean:1042) is the post-clock **tie
detector**:

```
def Phase4Transition (s t) :=
  let hasBigBias a := match a.bias with
    | .zero      => false
    | .dyadic _ i => decide (i.val < L)
  if hasBigBias s || hasBigBias t then (advancePhase s, advancePhase t)  -- → Phase 5
  else (s, t)                                                            -- stay (tie)
```

So a phase-4 agent with a **big bias** (a nonzero dyadic bias whose exponent
index `i < L`, i.e. `|bias| > 2^{-L}`) is a **witness**: meeting *any* partner
advances both to Phase 5.  This file formalizes both branches of Phase 4:

* **Tie branch** (Theorem 6.1 input): if no agent has a big bias (all biased
  agents are at the minimum exponent `L`, so `|g| < 1 ⟹ g = 0`), then
  `Phase4Transition` is the identity forever, every agent keeps output `T`, and
  the population is *deterministically* stable — `StableTie4` is one-step closed.
  This gives a `PhaseConvergenceW` with `t = 0`, `ε = 0`.

* **Non-tie branch** (Theorem 6.2 input): some agent has already advanced to
  Phase `≥ 5` (the epidemic source — provided by the upstream phase, exactly as
  `Phase3Convergence` carries its source `∃ a, 4 ≤ a.phase`).  The phase-`max`
  epidemic baked into `phaseEpidemicUpdate` then spreads `phase ≥ 5` to everyone:
  whenever a phase-`< 5` agent meets a phase-`≥ 5` agent, BOTH outputs land at
  phase `≥ 5` (`Transition_*_phase_ge_pair_max`).  The descending potential is
  `phaseBelowCount 5` (count of not-yet-advanced agents), the SAME mechanism as
  `Phase3Convergence`'s `phaseBelowCount 4` descent, ported to threshold 5.

## Honest predicate choices (vs. the HANDOFF sketch placeholders)

The sketch named `TieAllMinExp`, `Phase3StructuredNonTiePost`, `StableTieOutput`,
`Phase5Pre`, which do not exist in the repo.  We use honest in-file predicates
read off the actual `Phase4Transition` rule:

* `noBigBias a`     — `a.bias` is `.zero` or `.dyadic _ i` with `¬ i.val < L`
  (mirrors `StableEndpoints.phase4NoBigBias`, which is `private`);
* `StableTie4 c`    — every agent is phase-4, output `T`, `noBigBias` (mirrors the
  `private` `StableEndpoints.phase4TieWith`); this is the tie `Post`;
* `Advanced5 c`     — every agent is at phase `≥ 5` (`phaseBelowCount 5 c = 0`);
  the non-tie `Post`.

NEW file; no existing file is edited; no sorry/admit/axiom/native_decide.
-/

import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.PhaseConvergenceWeak
import Ripple.PopulationProtocol.Majority.ExactMajority.Analysis.Phase3Convergence

namespace ExactMajority

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace Phase4Convergence

variable {L K : ℕ}

attribute [local instance] Classical.propDecidable

/-! ## Part A — the no-big-bias predicate and the tie window. -/

/-- An agent has *no big bias* if its bias is zero or a dyadic with exponent index
`= L` (i.e. `¬ i.val < L`).  This is exactly the negation of `Phase4Transition`'s
`hasBigBias` guard, so a population of no-big-bias phase-4 agents never advances. -/
def noBigBias (a : AgentState L K) : Prop :=
  match a.bias with
  | .zero => True
  | .dyadic _ i => ¬ i.val < L

instance (a : AgentState L K) : Decidable (noBigBias a) := by
  unfold noBigBias; cases a.bias <;> infer_instance

/-- The Phase-4 **tie window / stable-tie postcondition**: every agent is a phase-4
agent reporting output `T` with no big bias.  Mirrors the `private`
`StableEndpoints.phase4TieWith`. -/
def StableTie4 (c : Config (AgentState L K)) : Prop :=
  ∀ a ∈ c, a.phase.val = 4 ∧ a.output = Output.T ∧ noBigBias a

instance (c : Config (AgentState L K)) : Decidable (StableTie4 c) := by
  unfold StableTie4; infer_instance

/-! ## Part B — the tie branch is deterministically one-step closed. -/

/-- With no big bias on either side, the `Phase4Transition` guard is `false`, so it
is the identity. -/
theorem Phase4Transition_eq_self_of_noBigBias (s t : AgentState L K)
    (hs : noBigBias (L := L) (K := K) s) (ht : noBigBias (L := L) (K := K) t) :
    Phase4Transition L K s t = (s, t) := by
  unfold Phase4Transition
  dsimp
  unfold noBigBias at hs ht
  have hsb : (match s.bias with
      | .zero => false
      | .dyadic _ i => decide (i.val < L)) = false := by
    cases hb : s.bias with
    | zero => rfl
    | dyadic sg i => rw [hb] at hs; simp only [decide_eq_false_iff_not]; exact hs
  have htb : (match t.bias with
      | .zero => false
      | .dyadic _ i => decide (i.val < L)) = false := by
    cases hb : t.bias with
    | zero => rfl
    | dyadic sg i => rw [hb] at ht; simp only [decide_eq_false_iff_not]; exact ht
  rw [hsb, htb]; rfl

/-- For two phase-4 agents, `phaseEpidemicUpdate` is the identity (max of equal
phases, no init to run, no phase-10 entry). -/
theorem phaseEpidemicUpdate_eq_self_of_phase4 (s t : AgentState L K)
    (hs : s.phase.val = 4) (ht : t.phase.val = 4) :
    phaseEpidemicUpdate L K s t = (s, t) := by
  have hsp : s.phase = ⟨4, by decide⟩ := Fin.ext hs
  have htp : t.phase = ⟨4, by decide⟩ := Fin.ext ht
  unfold phaseEpidemicUpdate
  rw [hsp, htp, max_self]
  simp only [runInitsBetween_self_api]
  have hs_self : ({s with phase := (⟨4, by decide⟩ : Fin 11)} : AgentState L K) = s := by
    rw [← hsp]
  have ht_self : ({t with phase := (⟨4, by decide⟩ : Fin 11)} : AgentState L K) = t := by
    rw [← htp]
  rw [hs_self, ht_self]
  rw [if_neg (by push_neg; intro _; simp)]

/-- **Per-pair tie preservation.**  Two tie-agents (phase 4, output `T`, no big
bias) produce two tie-agents under the full `Transition`. -/
theorem Transition_preserves_tie_pair (s t : AgentState L K)
    (hs4 : s.phase.val = 4) (ht4 : t.phase.val = 4)
    (hsT : s.output = Output.T) (htT : t.output = Output.T)
    (hsB : noBigBias (L := L) (K := K) s) (htB : noBigBias (L := L) (K := K) t) :
    let s' := (Transition L K s t).1
    let t' := (Transition L K s t).2
    (s'.phase.val = 4 ∧ s'.output = Output.T ∧ noBigBias (L := L) (K := K) s') ∧
      (t'.phase.val = 4 ∧ t'.output = Output.T ∧ noBigBias (L := L) (K := K) t') := by
  intro s' t'
  have hepi := phaseEpidemicUpdate_eq_self_of_phase4 (L := L) (K := K) s t hs4 ht4
  have hp4 := Phase4Transition_eq_self_of_noBigBias (L := L) (K := K) s t hsB htB
  have hsp : s.phase = ⟨4, by decide⟩ := Fin.ext hs4
  -- Transition unfolds: phaseEpidemicUpdate = (s,t); dispatch at phase 4 = Phase4Transition = (s,t).
  have hTrans : Transition L K s t = (s, t) := by
    unfold Transition
    rw [hepi]
    simp only [hsp]
    rw [show (Phase4Transition L K s t) = (s, t) from hp4]
    -- finishPhase10Entry s s = s, finishPhase10Entry t t = t (phase 4 ≠ 10).
    rw [finishPhase10Entry_eq_self_of_after_ne_10 (L := L) (K := K) s s (by rw [hs4]; omega),
        finishPhase10Entry_eq_self_of_after_ne_10 (L := L) (K := K) t t (by rw [ht4]; omega)]
  have hs'eq : s' = s := by show (Transition L K s t).1 = s; rw [hTrans]
  have ht'eq : t' = t := by show (Transition L K s t).2 = t; rw [hTrans]
  rw [hs'eq, ht'eq]
  exact ⟨⟨hs4, hsT, hsB⟩, ⟨ht4, htT, htB⟩⟩

end Phase4Convergence

end ExactMajority
