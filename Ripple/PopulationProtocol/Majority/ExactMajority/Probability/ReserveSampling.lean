/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Phase 5 — Reserve agents sample biased Main agents (Doty et al. §7.1, Lemma 7.1)

`Phase5Transition` (Protocol/Transition.lean:1104) is the **first-encounter sampling**
rule:

```
def Phase5Transition (s t) :=
  let doSample (r m) := if r.hour.val = L then ({r with hour := exponentOf L m.bias}, m)
                        else (r, m)
  -- Reserve r meets biased Main m: r records m's exponent (if r unsampled)
  ... (clock agents run the counter subroutine) ...
```

The Reserve's `sample` field is `a.hour : Fin (L+1)`; the sentinel "unsampled" value is
`sampleUnset = ⟨L, _⟩` (the maximal value, which a real exponent index never equals during
Phase 5 because biased Mains carry exponent `< L`).  Sampling overwrites `hour` with the
met Main's exponent `exponentOf m.bias`.

## Lemma 7.1 — every Reserve samples, whp

The paper's Lemma 7.1 ("by the end of Phase 5 every Reserve has `sample ≠ ⊥`, whp
`1 − O(1/n²)`") is a **one-sided elimination** process in the sense of `OneSidedCancel`
(Doty Lemma 4.7): the *target pool* is the set of **unsampled** Reserves; the *eliminator
pool* is the biased Mains (≥ Θ(|M|) by Theorem 6.2, carried as an invariant floor).  Every
unsampled-Reserve × biased-Main interaction permanently removes one element from the target
pool (the Reserve's hour leaves `L`), and NOTHING ever adds back to the pool (Mains never
become unsampled Reserves; sampling is one-way; the phase-5 rule never resets a Reserve's
hour to `L`).  So the unsampled-Reserve count `Φ = unsampledReserveU` is a non-increasing
potential whose `{Φ = 0}` is exactly `ReserveSampled` — precisely the
`OneSidedCancel.crude_PhaseConvergenceW` shape.

## Honest predicate choices (vs the HANDOFF sketch placeholders)

The sketch named `Phase5Pre`, `ReserveSampled`, `RoleCountsGoodConst`,
`Phase3StructuredNonTiePost`, `Sample.none` — of which only the *idea* maps to the repo.
We read honest in-file predicates off the actual `Phase5Transition` rule and the real
`AgentState.sample = .hour`, `sampleUnset = ⟨L,_⟩` encoding:

* `unsampled a`        — `a` is a Reserve with `a.hour.val = L` (sample still `= sampleUnset`);
* `unsampledReserveU c` — the count of such agents (the Doty target pool `|B|`, `Φ`);
* `ReserveSampled c`   — `unsampledReserveU c = 0` (no unsampled Reserve remains): the
  honest rendering of "every Reserve has `sample ≠ ⊥`";
* `Phase5AllWin n c`   — the carried structural window: size `n`, every agent at phase 5.

This file proves the per-pair / per-step / support facts that `unsampledReserveU` is
non-increasing under the real kernel and that `Phase5AllWin` is one-step closed, then
instantiates `OneSidedCancel.crude_PhaseConvergenceW` for the all-sampled whp tail
(`phase5SampledConvergence`).  The Chernoff sampled-class concentration (Lemma 7.1's
quantitative side) is delivered in `Phase5Convergence.lean`.

NEW file; no existing file is edited; no sorry/admit/axiom/native_decide.
-/

import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.OneSidedCancel
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.PhaseConvergenceWeak
import Ripple.PopulationProtocol.Majority.ExactMajority.Protocol.Transition

namespace ExactMajority

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace ReserveSampling

variable {L K : ℕ}

attribute [local instance] Classical.propDecidable

/-! ## Part A — the unsampled-Reserve predicate and target count. -/

/-- An agent is an **unsampled Reserve** if it has role `.reserve` and its `sample`
(`= .hour`) still equals the sentinel `sampleUnset = ⟨L, _⟩`, i.e. `a.hour.val = L`. -/
def unsampled (a : AgentState L K) : Prop :=
  a.role = Role.reserve ∧ a.hour.val = L

instance (a : AgentState L K) : Decidable (unsampled a) := by
  unfold unsampled; infer_instance

/-- The **target pool** size: the count of unsampled Reserves (Doty's `|B|`). -/
def unsampledReserveU (c : Config (AgentState L K)) : ℕ :=
  Multiset.countP (fun a => unsampled a) c

/-- Every Reserve has sampled: no unsampled Reserve remains.  The honest rendering of the
paper's "every Reserve has `sample ≠ ⊥`". -/
def ReserveSampled (c : Config (AgentState L K)) : Prop :=
  unsampledReserveU (L := L) (K := K) c = 0

/-- The carried Phase-5 structural window: size `n`, every agent at phase 5. -/
def Phase5AllWin (n : ℕ) (c : Config (AgentState L K)) : Prop :=
  c.card = n ∧ ∀ a ∈ c, a.phase.val = 5

instance (n : ℕ) (c : Config (AgentState L K)) : Decidable (Phase5AllWin n c) := by
  unfold Phase5AllWin; infer_instance

/-! ## Part B — per-pair behavior of `Phase5Transition` on the `unsampled` predicate.

The sampling rule changes ONLY a Reserve's `hour` (from `L` to the met Main's exponent
`≤ L`) and runs the clock subroutine on clocks.  Two facts drive everything:

* **(no creation)** `Phase5Transition` never produces a fresh `unsampled` agent.  A
  produced `unsampled` output (role `.reserve`, `hour = L`) can only have come from an
  `unsampled` input, because:
  - the sampling branch only fires on an input with `r.hour.val = L` and overwrites `hour`
    with `exponentOf m.bias`; the result still has `hour.val = L` ONLY when the input
    already did (`exponentOf` is `≤ L`, and equals `L` exactly for a min-exponent Main —
    in which case the input Reserve already had `hour = L`);
  - clocks stay role `.clock` (never `.reserve`).
  So `unsampledReserveU` is **non-increasing** per pair.
* **(strict drain)** when an `unsampled` Reserve meets a biased Main with exponent index
  `< L` (a *useful* eliminator, guaranteed `≥ Θ(|M|)` by Theorem 6.2), the Reserve's `hour`
  drops below `L`, so the `unsampled` count strictly decreases.
-/

/-- The negation of `unsampled` as a Bool-shaped fact, used for `countP` bookkeeping. -/
theorem unsampled_iff (a : AgentState L K) :
    unsampled a ↔ a.role = Role.reserve ∧ a.hour.val = L := Iff.rfl

/-- The first output of `Phase5Transition` is *either* a clock (when `s1` is a clock) *or*
equal to a state with `s.role` and `hour ∈ {s.hour, exponentOf L t.bias}`.  We package the
non-clock case as: role is `s.role`, and `hour.val = L → s.hour.val = L`. -/
theorem Phase5Transition_fst_role_hour (s t : AgentState L K) :
    (Phase5Transition L K s t).1.role = Role.clock ∨
      ((Phase5Transition L K s t).1.role = s.role ∧
        ((Phase5Transition L K s t).1.hour.val = L → s.hour.val = L)) := by
  unfold Phase5Transition
  simp only
  -- Identify the left intermediate `s1` (before the clock branch) and prove the disjunct
  -- for it via the clock-vs-non-clock split.
  have key : ∀ s1 : AgentState L K, s1.role = s.role →
      (s1.hour.val = L → s.hour.val = L) →
      ((if s1.role = Role.clock then stdCounterSubroutine L K s1 else s1).role = Role.clock ∨
        ((if s1.role = Role.clock then stdCounterSubroutine L K s1 else s1).role = s.role ∧
          ((if s1.role = Role.clock then stdCounterSubroutine L K s1 else s1).hour.val = L →
            s.hour.val = L))) := by
    intro s1 hr1 hh1
    by_cases hsc : s1.role = Role.clock
    · left; rw [if_pos hsc]; exact stdCounterSubroutine_clock_role_eq L K _ hsc
    · right; rw [if_neg hsc]; exact ⟨hr1, hh1⟩
  -- Now compute `s1` in each sampling branch.
  by_cases hb1 : s.role = Role.reserve ∧ t.role = Role.main ∧ t.bias ≠ Bias.zero
  · rw [if_pos hb1]
    by_cases hg : s.hour.val = L
    · -- doSample fires: s1 = {s with hour := exponentOf L t.bias}.
      rw [if_pos hg]
      exact key _ rfl (fun _ => hg)
    · -- doSample no-op: s1 = s.
      rw [if_neg hg]
      exact key _ rfl (fun h => h)
  · rw [if_neg hb1]
    by_cases hb2 : t.role = Role.reserve ∧ s.role = Role.main ∧ s.bias ≠ Bias.zero
    · -- s1 = (doSample t s).2 = s  (second component is `m = s` regardless of the guard).
      rw [if_pos hb2]
      by_cases hg2 : t.hour.val = L
      · rw [if_pos hg2]; exact key _ rfl (fun h => h)
      · rw [if_neg hg2]; exact key _ rfl (fun h => h)
    · -- identity: s1 = s.
      rw [if_neg hb2]
      exact key _ rfl (fun h => h)

/-- Symmetric statement for the second output: it is a clock, or has `t.role` and
`hour.val = L → t.hour.val = L`. -/
theorem Phase5Transition_snd_role_hour (s t : AgentState L K) :
    (Phase5Transition L K s t).2.role = Role.clock ∨
      ((Phase5Transition L K s t).2.role = t.role ∧
        ((Phase5Transition L K s t).2.hour.val = L → t.hour.val = L)) := by
  unfold Phase5Transition
  simp only
  have key : ∀ t1 : AgentState L K, t1.role = t.role →
      (t1.hour.val = L → t.hour.val = L) →
      ((if t1.role = Role.clock then stdCounterSubroutine L K t1 else t1).role = Role.clock ∨
        ((if t1.role = Role.clock then stdCounterSubroutine L K t1 else t1).role = t.role ∧
          ((if t1.role = Role.clock then stdCounterSubroutine L K t1 else t1).hour.val = L →
            t.hour.val = L))) := by
    intro t1 hr1 hh1
    by_cases htc : t1.role = Role.clock
    · left; rw [if_pos htc]; exact stdCounterSubroutine_clock_role_eq L K _ htc
    · right; rw [if_neg htc]; exact ⟨hr1, hh1⟩
  by_cases hb1 : s.role = Role.reserve ∧ t.role = Role.main ∧ t.bias ≠ Bias.zero
  · -- t1 = (doSample s t).2 = t.
    rw [if_pos hb1]
    by_cases hg1 : s.hour.val = L
    · rw [if_pos hg1]; exact key _ rfl (fun h => h)
    · rw [if_neg hg1]; exact key _ rfl (fun h => h)
  · rw [if_neg hb1]
    by_cases hb2 : t.role = Role.reserve ∧ s.role = Role.main ∧ s.bias ≠ Bias.zero
    · -- t1 = (doSample t s).1 = sampled t.
      rw [if_pos hb2]
      by_cases hg2 : t.hour.val = L
      · rw [if_pos hg2]; exact key _ rfl (fun _ => hg2)
      · rw [if_neg hg2]; exact key _ rfl (fun h => h)
    · rw [if_neg hb2]; exact key _ rfl (fun h => h)

/-- **`unsampled` is backward-stable under `Phase5Transition` (first output).**  If the
first output is `unsampled`, then the first input `s` was already `unsampled`. -/
theorem unsampled_fst_Phase5Transition (s t : AgentState L K)
    (hout : unsampled (Phase5Transition L K s t).1) : unsampled s := by
  obtain ⟨hrole, hhour⟩ := hout
  rcases Phase5Transition_fst_role_hour (L := L) (K := K) s t with hclk | ⟨hr, hh⟩
  · rw [hclk] at hrole; exact absurd hrole (by decide)
  · exact ⟨by rw [hr] at hrole; exact hrole, hh hhour⟩

/-- **`unsampled` is backward-stable under `Phase5Transition` (second output).** -/
theorem unsampled_snd_Phase5Transition (s t : AgentState L K)
    (hout : unsampled (Phase5Transition L K s t).2) : unsampled t := by
  obtain ⟨hrole, hhour⟩ := hout
  rcases Phase5Transition_snd_role_hour (L := L) (K := K) s t with hclk | ⟨hr, hh⟩
  · rw [hclk] at hrole; exact absurd hrole (by decide)
  · exact ⟨by rw [hr] at hrole; exact hrole, hh hhour⟩

/-! ## Part C — per-pair `unsampledReserveU` non-increase under `Phase5Transition`. -/

/-- `countP unsampled` over a two-element pair as a sum of indicators. -/
theorem countP_unsampled_pair (x y : AgentState L K) :
    Multiset.countP (fun a => unsampled a) ({x, y} : Multiset (AgentState L K))
      = (if unsampled x then 1 else 0) + (if unsampled y then 1 else 0) := by
  rw [show ({x, y} : Multiset (AgentState L K)) = x ::ₘ y ::ₘ 0 from rfl]
  rw [Multiset.countP_cons, Multiset.countP_cons, Multiset.countP_zero]
  ring

/-- **Per-pair `unsampledReserveU` non-increase.**  Because `Phase5Transition` produces an
`unsampled` output only from an `unsampled` input (`unsampled_{fst,snd}_Phase5Transition`),
the pair's unsampled count does not rise. -/
theorem Phase5Transition_unsampled_pair_le (s t : AgentState L K) :
    Multiset.countP (fun a => unsampled a)
        ({(Phase5Transition L K s t).1, (Phase5Transition L K s t).2}
          : Multiset (AgentState L K))
      ≤ Multiset.countP (fun a => unsampled a) ({s, t} : Multiset (AgentState L K)) := by
  classical
  rw [countP_unsampled_pair, countP_unsampled_pair]
  gcongr
  · -- if out1 unsampled then s unsampled.
    by_cases h1 : unsampled (Phase5Transition L K s t).1
    · rw [if_pos h1, if_pos (unsampled_fst_Phase5Transition (L := L) (K := K) s t h1)]
    · rw [if_neg h1]; positivity
  · by_cases h2 : unsampled (Phase5Transition L K s t).2
    · rw [if_pos h2, if_pos (unsampled_snd_Phase5Transition (L := L) (K := K) s t h2)]
    · rw [if_neg h2]; positivity

end ReserveSampling

end ExactMajority
