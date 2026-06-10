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

/-! ## Part D — the dispatch reduction `Transition = Phase5Transition` on phase-5 pairs. -/

/-- `advancePhase` raises an agent's phase by at most one. -/
theorem advancePhase_phase_le_succ (a : AgentState L K) :
    (advancePhase L K a).phase.val ≤ a.phase.val + 1 := by
  unfold advancePhase; split
  · simp
  · omega

/-- `phaseInit` at target phase `p` with `p.val = 6` only rewrites `counter` (clocks) or is
the identity; it never touches `phase`.  So an agent already at phase 6 stays at phase 6. -/
theorem phaseInit_phase_eq_of_six (a : AgentState L K) (p : Fin 11) (hp : p.val = 6)
    (ha : a.phase.val = 6) :
    (phaseInit L K p a).phase.val = 6 := by
  unfold phaseInit
  have h1 : ¬ p.val = 1 := by omega
  have h2 : ¬ p.val = 2 := by omega
  have h3 : ¬ p.val = 3 := by omega
  have h4 : ¬ p.val = 4 := by omega
  have h5 : ¬ p.val = 5 := by omega
  rw [dif_neg h1, dif_neg h2, dif_neg h3, dif_neg h4, dif_neg h5, dif_pos hp]
  by_cases hc : a.role = Role.clock <;> simp [hc, ha]

/-- `advancePhaseWithInit` of a phase-5 agent lands at phase 6 (advance to 6, then
`phaseInit` at 6 keeps it). -/
theorem advancePhaseWithInit_phase_eq_six_of_five (a : AgentState L K) (ha : a.phase.val = 5) :
    (advancePhaseWithInit L K a).phase.val = 6 := by
  unfold advancePhaseWithInit
  have hadv : (advancePhase L K a).phase.val = 6 := by
    unfold advancePhase
    have : a.phase.val < 10 := by omega
    simp only [this, dif_pos]; omega
  rw [phaseInit_phase_eq_of_six (L := L) (K := K) (advancePhase L K a)
    (advancePhase L K a).phase hadv hadv]

/-- `stdCounterSubroutine` of a phase-5 agent lands at phase 5 or 6. -/
theorem stdCounterSubroutine_phase_le_six_of_five (a : AgentState L K) (ha : a.phase.val = 5) :
    (stdCounterSubroutine L K a).phase.val ≤ 6 := by
  unfold stdCounterSubroutine; split
  · rw [advancePhaseWithInit_phase_eq_six_of_five (L := L) (K := K) a ha]
  · simp [ha]

/-- Both `Phase5Transition` outputs land at phase `≤ 6` when both inputs are at phase 5.
The sampling/identity branches keep phase 5; the clock branch caps at 6. -/
theorem Phase5Transition_phase_le_six (s t : AgentState L K)
    (hs : s.phase.val = 5) (ht : t.phase.val = 5) :
    (Phase5Transition L K s t).1.phase.val ≤ 6 ∧
      (Phase5Transition L K s t).2.phase.val ≤ 6 := by
  -- The sampling step never changes phase; so each intermediate `s1`/`t1` is at phase 5,
  -- and the clock branch then caps at 6.
  have hsample_phase : ∀ r m : AgentState L K, r.phase.val = 5 →
      (if r.role = Role.clock then stdCounterSubroutine L K r else r).phase.val ≤ 6 := by
    intro r m hr
    by_cases hrc : r.role = Role.clock
    · rw [if_pos hrc]; exact stdCounterSubroutine_phase_le_six_of_five (L := L) (K := K) r hr
    · rw [if_neg hrc]; omega
  -- s1 has phase = s.phase = 5 (sampling only writes hour); same for t1.
  have hs1_phase : ∀ s1 : AgentState L K, s1.phase.val = 5 →
      (if s1.role = Role.clock then stdCounterSubroutine L K s1 else s1).phase.val ≤ 6 :=
    fun s1 h => hsample_phase s1 s1 h
  -- Compute s1.phase / t1.phase = 5 from the sampling branches.
  refine ⟨?_, ?_⟩
  · unfold Phase5Transition; simp only
    by_cases hb1 : s.role = Role.reserve ∧ t.role = Role.main ∧ t.bias ≠ Bias.zero
    · rw [if_pos hb1]
      by_cases hg : s.hour.val = L
      · rw [if_pos hg]; exact hs1_phase _ (by simpa using hs)
      · rw [if_neg hg]; exact hs1_phase _ hs
    · rw [if_neg hb1]
      by_cases hb2 : t.role = Role.reserve ∧ s.role = Role.main ∧ s.bias ≠ Bias.zero
      · rw [if_pos hb2]
        by_cases hg2 : t.hour.val = L
        · rw [if_pos hg2]; exact hs1_phase _ hs
        · rw [if_neg hg2]; exact hs1_phase _ hs
      · rw [if_neg hb2]; exact hs1_phase _ hs
  · unfold Phase5Transition; simp only
    by_cases hb1 : s.role = Role.reserve ∧ t.role = Role.main ∧ t.bias ≠ Bias.zero
    · rw [if_pos hb1]
      by_cases hg : s.hour.val = L
      · rw [if_pos hg]; exact hs1_phase _ ht
      · rw [if_neg hg]; exact hs1_phase _ ht
    · rw [if_neg hb1]
      by_cases hb2 : t.role = Role.reserve ∧ s.role = Role.main ∧ s.bias ≠ Bias.zero
      · rw [if_pos hb2]
        by_cases hg2 : t.hour.val = L
        · rw [if_pos hg2]; exact hs1_phase _ (by simpa using ht)
        · rw [if_neg hg2]; exact hs1_phase _ ht
      · rw [if_neg hb2]; exact hs1_phase _ ht

/-- For two phase-5 agents, `phaseEpidemicUpdate` is the identity (max of equal phases,
no init to run, no phase-10 entry).  Mirror of `phaseEpidemicUpdate_eq_self_of_phase7`. -/
theorem phaseEpidemicUpdate_eq_self_of_phase5 (s t : AgentState L K)
    (hs : s.phase.val = 5) (ht : t.phase.val = 5) :
    phaseEpidemicUpdate L K s t = (s, t) := by
  have hsp : s.phase = ⟨5, by decide⟩ := Fin.ext hs
  have htp : t.phase = ⟨5, by decide⟩ := Fin.ext ht
  unfold phaseEpidemicUpdate
  rw [hsp, htp, max_self]
  simp only [runInitsBetween_self_api]
  have hs_self : ({s with phase := (⟨5, by decide⟩ : Fin 11)} : AgentState L K) = s := by
    rw [← hsp]
  have ht_self : ({t with phase := (⟨5, by decide⟩ : Fin 11)} : AgentState L K) = t := by
    rw [← htp]
  rw [hs_self, ht_self]
  rw [if_neg (by push Not; intro _; simp)]

/-- **Per-pair reduction.**  Two phase-5 agents interact via `Phase5Transition` under the
full `Transition` (epidemic = id, dispatch = `Phase5Transition`, and neither output reaches
phase 10 so the phase-10 finish is the identity). -/
theorem Transition_eq_Phase5Transition_of_phase5 (s t : AgentState L K)
    (hs : s.phase.val = 5) (ht : t.phase.val = 5) :
    Transition L K s t = Phase5Transition L K s t := by
  have hepi := phaseEpidemicUpdate_eq_self_of_phase5 (L := L) (K := K) s t hs ht
  have hsp : s.phase = ⟨5, by decide⟩ := Fin.ext hs
  obtain ⟨hle1, hle2⟩ := Phase5Transition_phase_le_six (L := L) (K := K) s t hs ht
  unfold Transition
  rw [hepi]
  simp only [hsp]
  rw [finishPhase10Entry_eq_self_of_after_ne_10 (L := L) (K := K) s _ (by omega),
      finishPhase10Entry_eq_self_of_after_ne_10 (L := L) (K := K) t _ (by omega)]

/-! ## Part E — `unsampledReserveU` non-increase under the real kernel on the phase-5 window. -/

private theorem mem_of_app_left5 {c : Config (AgentState L K)}
    {r₁ r₂ : AgentState L K} (happ : Protocol.Applicable c r₁ r₂) : r₁ ∈ c :=
  Multiset.mem_of_le (show ({r₁, r₂} : Multiset (AgentState L K)) ≤ c from happ) (by simp)

private theorem mem_of_app_right5 {c : Config (AgentState L K)}
    {r₁ r₂ : AgentState L K} (happ : Protocol.Applicable c r₁ r₂) : r₂ ∈ c :=
  Multiset.mem_of_le (show ({r₁, r₂} : Multiset (AgentState L K)) ≤ c from happ) (by simp)

/-- **`unsampledReserveU` is non-increasing under any chosen-pair update on the all-phase-5
window.**  An applicable pair `(r₁, r₂)` are both phase-5 agents, so `Transition` reduces to
`Phase5Transition`, whose per-pair `unsampled`-count does not rise
(`Phase5Transition_unsampled_pair_le`). -/
theorem unsampledReserveU_stepOrSelf_le (n : ℕ) (c : Config (AgentState L K))
    (hInv : Phase5AllWin n c) (r₁ r₂ : AgentState L K) :
    unsampledReserveU (L := L) (K := K)
        (Protocol.stepOrSelf (NonuniformMajority L K) c r₁ r₂)
      ≤ unsampledReserveU (L := L) (K := K) c := by
  obtain ⟨_, hph⟩ := hInv
  by_cases happ : Protocol.Applicable c r₁ r₂
  · have hm1 := mem_of_app_left5 happ
    have hm2 := mem_of_app_right5 happ
    have h15 : r₁.phase.val = 5 := hph r₁ hm1
    have h25 : r₂.phase.val = 5 := hph r₂ hm2
    have hsub : ({r₁, r₂} : Multiset (AgentState L K)) ≤ c := happ
    have hc' : Protocol.stepOrSelf (NonuniformMajority L K) c r₁ r₂
        = c - {r₁, r₂} + {(Transition L K r₁ r₂).1, (Transition L K r₁ r₂).2} := by
      unfold Protocol.stepOrSelf; rw [if_pos happ]; rfl
    unfold unsampledReserveU
    rw [hc', Multiset.countP_add, Multiset.countP_sub hsub]
    rw [Transition_eq_Phase5Transition_of_phase5 (L := L) (K := K) r₁ r₂ h15 h25]
    have hpair := Phase5Transition_unsampled_pair_le (L := L) (K := K) r₁ r₂
    have hpair_le : Multiset.countP (fun a => unsampled a)
        ({r₁, r₂} : Multiset (AgentState L K))
          ≤ Multiset.countP (fun a => unsampled a) c := Multiset.countP_le_of_le _ hsub
    omega
  · rw [Protocol.stepOrSelf_eq_self_of_not_applicable happ]

/-- The kernel-support version: any successor of a phase-5-window config has no larger
unsampled-Reserve count. -/
theorem unsampledReserveU_support_le (n : ℕ) (c c' : Config (AgentState L K))
    (hInv : Phase5AllWin n c)
    (hc' : c' ∈ ((NonuniformMajority L K).stepDistOrSelf c).support) :
    unsampledReserveU (L := L) (K := K) c' ≤ unsampledReserveU (L := L) (K := K) c := by
  by_cases hc : 2 ≤ c.card
  · rw [show (NonuniformMajority L K).stepDistOrSelf c
        = (NonuniformMajority L K).stepDist c hc by
        unfold Protocol.stepDistOrSelf; rw [dif_pos hc]] at hc'
    obtain ⟨⟨r₁, r₂⟩, hr⟩ := Protocol.stepDist_support (NonuniformMajority L K) c hc c' hc'
    rw [← hr]; exact unsampledReserveU_stepOrSelf_le n c hInv r₁ r₂
  · rw [show (NonuniformMajority L K).stepDistOrSelf c = PMF.pure c by
        unfold Protocol.stepDistOrSelf; rw [dif_neg hc]] at hc'
    rw [PMF.mem_support_pure_iff] at hc'; subst hc'; exact le_refl _

/-! ## Part F — the `PotNonincrOn` drift and the all-sampled `PhaseConvergenceW` instance.

`unsampledReserveU` is non-increasing along the kernel from any phase-5-window state
(`unsampledReserveU_support_le`), which is exactly `OneSidedCancel.PotNonincrOn`.  The
remaining engine inputs are:

* `hClosed : InvClosed K Inv` — the window-closure.  For the **uniform all-phase-5**
  window `Phase5AllWin` this is genuinely NOT one-step closed (a zero-counter clock pair
  advances both clocks to phase 6, leaving the window), so `hClosed` is a **carried
  hypothesis** here — exactly the honest pattern `Phase7Convergence.phase7Convergence'`
  uses for its carried `hmono`.  Discharging it on the genuinely-closed superwindow
  `card = n ∧ ∀ a ∈ c, 5 ≤ a.phase.val` requires the cross-phase per-pair backward-stability
  of `unsampled` for the dispatch branches `6..10` (Phase-6 `doSplit` maps reserve→main, so
  it removes — never creates — unsampled Reserves; Phases 7–10 leave reserves untouched).
  That cross-phase reduction is the precise campaign gap recorded in the report.
* `hstep : drain` — the per-step drop probability from the biased-Main (index `< L`)
  eliminator floor carried by Theorem 6.2.  Supplied as a carried honest input, exactly as
  `Phase7`'s drain `hstep`.
-/

/-- **`unsampledReserveU` non-increases along the real kernel on the phase-5 window**
(`OneSidedCancel.PotNonincrOn`). -/
theorem potNonincrOn_unsampledReserveU (n : ℕ) :
    OneSidedCancel.PotNonincrOn (fun c => Phase5AllWin (L := L) (K := K) n c)
      (NonuniformMajority L K).transitionKernel
      (fun c => unsampledReserveU (L := L) (K := K) c) := by
  intro c hInv
  change ((NonuniformMajority L K).stepDistOrSelf c).toMeasure
    {x | unsampledReserveU (L := L) (K := K) c < unsampledReserveU (L := L) (K := K) x} = 0
  rw [PMF.toMeasure_apply_eq_zero_iff _ (DiscreteMeasurableSpace.forall_measurableSet _)]
  rw [Set.disjoint_left]
  intro x hsupp hx
  exact absurd (unsampledReserveU_support_le n c x hInv hsupp) (by
    simp only [Set.mem_setOf_eq] at hx; omega)

/-- `ReserveSampled c` (every Reserve has sampled) is exactly `unsampledReserveU c = 0`,
i.e. `c ∈ potDone (unsampledReserveU)`. -/
theorem reserveSampled_iff_potDone (c : Config (AgentState L K)) :
    ReserveSampled (L := L) (K := K) c ↔
      c ∈ OneSidedCancel.potDone (fun c => unsampledReserveU (L := L) (K := K) c) := by
  unfold ReserveSampled OneSidedCancel.potDone
  simp only [Set.mem_setOf_eq]

/-- **Lemma 7.1 (all Reserves sampled), as a `PhaseConvergenceW` on the real kernel.**

`Pre c = Phase5AllWin n c ∧ unsampledReserveU c ≤ M₀` (the phase-5 window plus a target
budget), `Post c = Phase5AllWin n c ∧ unsampledReserveU c = 0` (still in the window, no
unsampled Reserve left = `ReserveSampled`).  The horizon is `t` interactions with failure
`ε ≥ q^t`.

Instantiates `OneSidedCancel.crude_PhaseConvergenceW` with `Inv = Phase5AllWin n`,
`Φ = unsampledReserveU` (drift discharged by `potNonincrOn_unsampledReserveU`), the carried
window-closure `hClosed`, and the carried eliminator-floor drain `hstep` (per-step drop `≤ q`
from the biased-Main pool, Doty Lemma 4.7 / Theorem 6.2 floor). -/
noncomputable def phase5SampledConvergence (n : ℕ)
    (hClosed : OneSidedCancel.InvClosed (NonuniformMajority L K).transitionKernel
      (fun c => Phase5AllWin (L := L) (K := K) n c))
    (q : ℝ≥0∞)
    (hstep : ∀ b : Config (AgentState L K), Phase5AllWin (L := L) (K := K) n b →
      1 ≤ unsampledReserveU (L := L) (K := K) b →
      (NonuniformMajority L K).transitionKernel b
        (OneSidedCancel.potDone (fun c => unsampledReserveU (L := L) (K := K) c))ᶜ ≤ q)
    (M₀ : ℕ) (t : ℕ) (ε : ℝ≥0) (hε : (q ^ t : ℝ≥0∞) ≤ (ε : ℝ≥0∞)) :
    PhaseConvergenceW (NonuniformMajority L K).transitionKernel :=
  OneSidedCancel.crude_PhaseConvergenceW
    (NonuniformMajority L K).transitionKernel
    (fun c => Phase5AllWin (L := L) (K := K) n c)
    hClosed
    (fun c => unsampledReserveU (L := L) (K := K) c)
    (potNonincrOn_unsampledReserveU n)
    q hstep M₀ t ε hε

/-- The `Post` of `phase5SampledConvergence` is exactly `Phase5AllWin n ∧ ReserveSampled`. -/
theorem phase5SampledConvergence_post (n : ℕ)
    (hClosed : OneSidedCancel.InvClosed (NonuniformMajority L K).transitionKernel
      (fun c => Phase5AllWin (L := L) (K := K) n c))
    (q : ℝ≥0∞)
    (hstep : ∀ b : Config (AgentState L K), Phase5AllWin (L := L) (K := K) n b →
      1 ≤ unsampledReserveU (L := L) (K := K) b →
      (NonuniformMajority L K).transitionKernel b
        (OneSidedCancel.potDone (fun c => unsampledReserveU (L := L) (K := K) c))ᶜ ≤ q)
    (M₀ : ℕ) (t : ℕ) (ε : ℝ≥0) (hε : (q ^ t : ℝ≥0∞) ≤ (ε : ℝ≥0∞)) :
    (phase5SampledConvergence n hClosed q hstep M₀ t ε hε).Post =
      fun c => Phase5AllWin (L := L) (K := K) n c ∧ ReserveSampled (L := L) (K := K) c := by
  rfl

end ReserveSampling

end ExactMajority
