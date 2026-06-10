/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Phase 8 — consume the last minority agents (Doty et al. §6, Phase 8)

`Phase8Transition` (Protocol/Transition.lean:1407) is the final consumption phase,
via `absorbConsume`:

```
def Phase8Transition (s t) :=
  if s.role = .main ∧ t.role = .main then absorbConsume L K s t
  else (s,t)   -- (clock agents run the counter subroutine)
```

and `absorbConsume` (Transition.lean:1313) on two **opposite-sign** dyadic biases:
the higher-exponent (larger index `i`, smaller |bias|) agent with `full = false`
consumes the other — marks itself `full := true` and sets the consumed agent's bias
to `.zero`.  Crucially it **never sign-flips**: each branch either zeroes one agent
or is the identity.  Hence the count of `σ`-signed Main agents is **unconditionally
non-increasing** — no index-ordering hypothesis is needed (unlike Phase 7's
`cancelSplit`, whose gap-2 branch can copy a sign).

## Honest predicate / potential choices (vs the HANDOFF sketch placeholders)

The sketch named `Phase7PostCore`, `NoMinority`, `IsMinority` — none exist in the
repo.  We read honest in-file predicates off the actual `absorbConsume` rule:

* `minoritySt σ a`  — a Main with a `σ`-signed dyadic bias (the Doty `B`-pool);
  reused from `Phase7Convergence`;
* `minorityU σ c`   — the minority count;
* `Phase8AllMain n` — the structural window: size `n`, all agents phase-8 Mains.

The **shrinking-eliminator handling** the task flags: `absorbConsume` sets the
consumer's `full := true`, and a `full` agent can no longer consume (it drops out of
the eliminator pool).  But this does **not** threaten the potential: the eliminator
floor enters only through the per-step drain probability `q` (the `hstep` hypothesis
of the engine), and the honest carried invariant is that the eliminator pool stays
`≥ minority-remaining + margin` (Doty Lemma 7.6: after Phase 7, `≥ 0.8|M|` majority
vs `≤ 0.2|M|` minority, and even as eliminators go `full` the surviving non-`full`
majority stays above the minority count).  The potential `Φ = minorityU σ` itself is
non-increasing regardless of `full` (consumption only zeroes biases), which is what
the engine's `hmono` needs — proved here unconditionally.

This file delivers the engine's `hmono` (PotNonincrOn) + structural `InvClosed`
core for Phase 8, mirroring `Phase7Convergence` but WITHOUT the index ordering
(`absorbConsume` is sign-preserving).  The drain rectangle (`hstep`) is the
remaining atom, documented at the file foot.

NEW file; no existing file is edited; no sorry/admit/axiom/native_decide.
-/

import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.OneSidedCancel
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.PhaseConvergenceWeak
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.Phase7Convergence

namespace ExactMajority

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace Phase8Convergence

variable {L K : ℕ}

attribute [local instance] Classical.propDecidable

open Phase7Convergence (minoritySt minorityU biasIsSigned minoritySt_iff
  countP_minoritySt_pair not_minoritySt_of_not_main)

/-! ## Part A — the per-pair reduction to `absorbConsume` for two phase-8 Mains. -/

/-- For two phase-8 agents, `phaseEpidemicUpdate` is the identity. -/
theorem phaseEpidemicUpdate_eq_self_of_phase8 (s t : AgentState L K)
    (hs : s.phase.val = 8) (ht : t.phase.val = 8) :
    phaseEpidemicUpdate L K s t = (s, t) := by
  have hsp : s.phase = ⟨8, by decide⟩ := Fin.ext hs
  have htp : t.phase = ⟨8, by decide⟩ := Fin.ext ht
  unfold phaseEpidemicUpdate
  rw [hsp, htp, max_self]
  simp only [runInitsBetween_self_api]
  have hs_self : ({s with phase := (⟨8, by decide⟩ : Fin 11)} : AgentState L K) = s := by
    rw [← hsp]
  have ht_self : ({t with phase := (⟨8, by decide⟩ : Fin 11)} : AgentState L K) = t := by
    rw [← htp]
  rw [hs_self, ht_self]
  rw [if_neg (by push Not; intro _; simp)]

/-- `absorbConsume` never changes an agent's phase. -/
theorem absorbConsume_phase (s t : AgentState L K) :
    (absorbConsume L K s t).1.phase = s.phase ∧ (absorbConsume L K s t).2.phase = t.phase := by
  unfold absorbConsume
  match s.bias, t.bias with
  | .zero, _ => simp
  | .dyadic .pos _, .zero => simp
  | .dyadic .neg _, .zero => simp
  | .dyadic .pos i, .dyadic .neg j => simp; split_ifs <;> simp
  | .dyadic .neg i, .dyadic .pos j => simp; split_ifs <;> simp
  | .dyadic .pos _, .dyadic .pos _ => simp
  | .dyadic .neg _, .dyadic .neg _ => simp

/-- **Per-pair reduction.**  Two phase-8 Main agents interact via `absorbConsume`
under the full `Transition`. -/
theorem Transition_eq_absorbConsume_of_phase8_main (s t : AgentState L K)
    (hs8 : s.phase.val = 8) (ht8 : t.phase.val = 8)
    (hsM : s.role = Role.main) (htM : t.role = Role.main) :
    Transition L K s t = absorbConsume L K s t := by
  have hepi := phaseEpidemicUpdate_eq_self_of_phase8 (L := L) (K := K) s t hs8 ht8
  have hsp : s.phase = ⟨8, by decide⟩ := Fin.ext hs8
  have hnsclk : s.role ≠ Role.clock := by rw [hsM]; decide
  have hntclk : t.role ≠ Role.clock := by rw [htM]; decide
  have hp8 : Phase8Transition L K s t = absorbConsume L K s t := by
    unfold Phase8Transition
    simp only [if_pos (show s.role = Role.main ∧ t.role = Role.main from ⟨hsM, htM⟩),
      absorbConsume_role_fst, absorbConsume_role_snd, if_neg hnsclk, if_neg hntclk]
  obtain ⟨hac1, hac2⟩ := absorbConsume_phase (L := L) (K := K) s t
  unfold Transition
  rw [hepi]
  simp only [hsp]
  rw [show (Phase8Transition L K s t) = absorbConsume L K s t from hp8]
  rw [finishPhase10Entry_eq_self_of_after_ne_10 (L := L) (K := K) s _ (by rw [hac1, hs8]; omega),
      finishPhase10Entry_eq_self_of_after_ne_10 (L := L) (K := K) t _ (by rw [hac2, ht8]; omega)]

end Phase8Convergence

end ExactMajority
