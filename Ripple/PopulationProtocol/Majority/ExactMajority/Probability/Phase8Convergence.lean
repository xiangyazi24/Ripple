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

/-! ## Part B — per-pair minority non-increase under `absorbConsume` (unconditional).

Every `absorbConsume` branch either is the identity or sets exactly one agent's
bias to `.zero` (consumption) while only flipping the other's `full` flag — it
**never changes a sign**.  So the `σ`-Main count of the produced pair is at most
that of the consumed pair, with NO index-ordering hypothesis. -/

/-- A bias-side characterization, reused. `absorbConsume` preserves roles
(`absorbConsume_role_fst/snd`), so indicators are evaluated at Mains exactly when
the inputs are. -/
theorem absorbConsume_minorityU_pair_le (σ : Sign) (s t : AgentState L K)
    (hsM : s.role = Role.main) (htM : t.role = Role.main) :
    Multiset.countP (fun a => minoritySt σ a)
        ({(absorbConsume L K s t).1, (absorbConsume L K s t).2} : Multiset (AgentState L K))
      ≤ Multiset.countP (fun a => minoritySt σ a)
          ({s, t} : Multiset (AgentState L K)) := by
  classical
  have hr1 : (absorbConsume L K s t).1.role = s.role := absorbConsume_role_fst L K s t
  have hr2 : (absorbConsume L K s t).2.role = t.role := absorbConsume_role_snd L K s t
  rw [countP_minoritySt_pair, countP_minoritySt_pair]
  have key : ∀ x : AgentState L K, x.role = Role.main →
      (minoritySt σ x ↔ biasIsSigned σ x.bias) := fun x hx => by
    rw [minoritySt_iff]; exact ⟨fun h => h.2, fun h => ⟨hx, h⟩⟩
  rw [if_congr (key s hsM) rfl rfl, if_congr (key t htM) rfl rfl,
      if_congr (key _ (by rw [hr1]; exact hsM)) rfl rfl,
      if_congr (key _ (by rw [hr2]; exact htM)) rfl rfl]
  -- Bias-level case analysis: each branch zeroes a bias or is identity.
  unfold absorbConsume biasIsSigned
  rcases hsb : s.bias with _ | ⟨sgs, i⟩ <;> rcases htb : t.bias with _ | ⟨sgt, j⟩ <;>
    simp only [hsb, htb]
  all_goals (
    first
    | (rcases sgs with _ | _ <;> rcases sgt with _ | _ <;>
        simp only [] <;> split_ifs <;> simp_all <;> omega)
    | (split_ifs <;> simp_all <;> omega)
    | simp_all)

/-- When the pair is **not** both Main, `Phase8Transition` leaves every Main's bias
unchanged (`absorbConsume` not invoked; the clock subroutine touches only the clock
side, not a Main).  So the minority count is unchanged. -/
theorem Phase8Transition_minorityU_eq_of_not_both_main (σ : Sign) (s t : AgentState L K)
    (h : ¬ (s.role = Role.main ∧ t.role = Role.main)) :
    Multiset.countP (fun a => minoritySt σ a)
        ({(Phase8Transition L K s t).1, (Phase8Transition L K s t).2}
          : Multiset (AgentState L K))
      = Multiset.countP (fun a => minoritySt σ a) ({s, t} : Multiset (AgentState L K)) := by
  classical
  rw [countP_minoritySt_pair, countP_minoritySt_pair]
  have hside : ∀ (x : AgentState L K),
      (if minoritySt σ (if x.role = Role.clock then stdCounterSubroutine L K x else x)
        then (1 : ℕ) else 0) = (if minoritySt σ x then 1 else 0) := by
    intro x
    by_cases hxc : x.role = Role.clock
    · rw [if_pos hxc]
      have h1 : ¬ minoritySt σ (stdCounterSubroutine L K x) :=
        not_minoritySt_of_not_main σ _ (by
          have hcr : (stdCounterSubroutine L K x).role = Role.clock :=
            stdCounterSubroutine_clock_role_eq (L := L) (K := K) x hxc
          rw [hcr]; decide)
      have h2 : ¬ minoritySt σ x := not_minoritySt_of_not_main σ x (by rw [hxc]; decide)
      rw [if_neg h1, if_neg h2]
    · rw [if_neg hxc]
  unfold Phase8Transition
  simp only [if_neg h]
  rw [hside s, hside t]

/-! ## Part C — config-level non-increase over an all-Main phase-8 window. -/

/-- The all-Main phase-8 window: the honest carried Phase-7 output (every agent a
phase-8 Main).  No index ordering is needed — `absorbConsume` is sign-preserving. -/
def Phase8AllMain (n : ℕ) (c : Config (AgentState L K)) : Prop :=
  c.card = n ∧ ∀ a ∈ c, a.phase.val = 8 ∧ a.role = Role.main

private theorem mem_of_app_left8 {c : Config (AgentState L K)}
    {r₁ r₂ : AgentState L K} (happ : Protocol.Applicable c r₁ r₂) : r₁ ∈ c :=
  Multiset.mem_of_le (show ({r₁, r₂} : Multiset (AgentState L K)) ≤ c from happ) (by simp)

private theorem mem_of_app_right8 {c : Config (AgentState L K)}
    {r₁ r₂ : AgentState L K} (happ : Protocol.Applicable c r₁ r₂) : r₂ ∈ c :=
  Multiset.mem_of_le (show ({r₁, r₂} : Multiset (AgentState L K)) ≤ c from happ) (by simp)

/-- **Per-pair `Transition` minority non-increase, both-Main.**  Reduce to
`absorbConsume` and apply the unconditional pair bound. -/
theorem Transition_minorityU_pair_le_of_both_main (σ : Sign) (s t : AgentState L K)
    (hs8 : s.phase.val = 8) (ht8 : t.phase.val = 8)
    (hsM : s.role = Role.main) (htM : t.role = Role.main) :
    Multiset.countP (fun a => minoritySt σ a)
        ({(Transition L K s t).1, (Transition L K s t).2} : Multiset (AgentState L K))
      ≤ Multiset.countP (fun a => minoritySt σ a) ({s, t} : Multiset (AgentState L K)) := by
  rw [Transition_eq_absorbConsume_of_phase8_main s t hs8 ht8 hsM htM]
  exact absorbConsume_minorityU_pair_le σ s t hsM htM

/-- `minorityU σ` is non-increasing under any chosen-pair update on an all-Main
phase-8 window. -/
theorem minorityU_stepOrSelf_le (σ : Sign) (n : ℕ) (c : Config (AgentState L K))
    (hInv : Phase8AllMain n c) (r₁ r₂ : AgentState L K) :
    minorityU σ (Protocol.stepOrSelf (NonuniformMajority L K) c r₁ r₂)
      ≤ minorityU σ c := by
  obtain ⟨_, hph⟩ := hInv
  by_cases happ : Protocol.Applicable c r₁ r₂
  · have hm1 := mem_of_app_left8 happ
    have hm2 := mem_of_app_right8 happ
    obtain ⟨h18, h1M⟩ := hph r₁ hm1
    obtain ⟨h28, h2M⟩ := hph r₂ hm2
    have hsub : ({r₁, r₂} : Multiset (AgentState L K)) ≤ c := happ
    have hc' : Protocol.stepOrSelf (NonuniformMajority L K) c r₁ r₂
        = c - {r₁, r₂} + {(Transition L K r₁ r₂).1, (Transition L K r₁ r₂).2} := by
      unfold Protocol.stepOrSelf; rw [if_pos happ]; rfl
    unfold minorityU
    rw [hc', Multiset.countP_add, Multiset.countP_sub hsub]
    have hpair := Transition_minorityU_pair_le_of_both_main σ r₁ r₂ h18 h28 h1M h2M
    have hpair_le : Multiset.countP (fun a => minoritySt σ a)
        ({r₁, r₂} : Multiset (AgentState L K))
          ≤ Multiset.countP (fun a => minoritySt σ a) c := Multiset.countP_le_of_le _ hsub
    omega
  · rw [Protocol.stepOrSelf_eq_self_of_not_applicable happ]

/-- `minorityU σ` is non-increasing on the one-step kernel support. -/
theorem minorityU_le_on_support (σ : Sign) (n : ℕ) (m : ℕ)
    (c c' : Config (AgentState L K)) (hInv : Phase8AllMain n c)
    (hle : minorityU σ c ≤ m)
    (hc' : c' ∈ ((NonuniformMajority L K).stepDistOrSelf c).support) :
    minorityU σ c' ≤ m := by
  by_cases hc : 2 ≤ c.card
  · rw [show (NonuniformMajority L K).stepDistOrSelf c
        = (NonuniformMajority L K).stepDist c hc by
        unfold Protocol.stepDistOrSelf; rw [dif_pos hc]] at hc'
    obtain ⟨⟨r₁, r₂⟩, hr⟩ := Protocol.stepDist_support (NonuniformMajority L K) c hc c' hc'
    rw [← hr]; exact le_trans (minorityU_stepOrSelf_le σ n c hInv r₁ r₂) hle
  · rw [show (NonuniformMajority L K).stepDistOrSelf c = PMF.pure c by
        unfold Protocol.stepDistOrSelf; rw [dif_neg hc]] at hc'
    rw [PMF.mem_support_pure_iff] at hc'; subst hc'; exact hle

/-- **The engine's `hmono` (PotNonincrOn) ingredient for Phase 8.** -/
theorem minorityU_kernel_noincr (σ : Sign) (n : ℕ) (c : Config (AgentState L K))
    (hInv : Phase8AllMain n c) :
    (NonuniformMajority L K).transitionKernel c
      {x | minorityU σ c < minorityU σ x} = 0 := by
  change ((NonuniformMajority L K).stepDistOrSelf c).toMeasure
    {x | minorityU σ c < minorityU σ x} = 0
  rw [PMF.toMeasure_apply_eq_zero_iff _ (DiscreteMeasurableSpace.forall_measurableSet _)]
  rw [Set.disjoint_left]
  intro x hsupp hx
  simp only [Set.mem_setOf_eq] at hx
  have hle : minorityU σ x ≤ minorityU σ c :=
    minorityU_le_on_support σ n (minorityU σ c) c x hInv le_rfl hsupp
  omega

/-- Packaged as the engine's `PotNonincrOn` predicate. -/
theorem potNonincrOn_minorityU (σ : Sign) (n : ℕ) :
    OneSidedCancel.PotNonincrOn (fun c => Phase8AllMain n c)
      (NonuniformMajority L K).transitionKernel (fun c => minorityU σ c) :=
  fun c hInv => minorityU_kernel_noincr σ n c hInv

/-! ## Part D — the structural (card + phase-8 + role-Main) closure of `Phase8AllMain`.

`absorbConsume` preserves phase (`absorbConsume_phase`) and role
(`absorbConsume_role_fst/snd`), and every applicable pair on the window is
both-Main, so `Transition` = `absorbConsume`.  Hence `Phase8AllMain` is one-step
closed — this is the FULL engine `InvClosed` (no separate ordering invariant is
needed, unlike Phase 7). -/

/-- `Phase8AllMain` is preserved by a chosen-pair update. -/
theorem Phase8AllMain_stepOrSelf (n : ℕ) (c : Config (AgentState L K))
    (hw : Phase8AllMain n c) (r₁ r₂ : AgentState L K) :
    Phase8AllMain n (Protocol.stepOrSelf (NonuniformMajority L K) c r₁ r₂) := by
  obtain ⟨hcard, hph⟩ := hw
  by_cases happ : Protocol.Applicable c r₁ r₂
  · have hm1 := mem_of_app_left8 happ
    have hm2 := mem_of_app_right8 happ
    obtain ⟨h18, h1M⟩ := hph r₁ hm1
    obtain ⟨h28, h2M⟩ := hph r₂ hm2
    have hac := Transition_eq_absorbConsume_of_phase8_main r₁ r₂ h18 h28 h1M h2M
    have hacphase := absorbConsume_phase (L := L) (K := K) r₁ r₂
    have hc' : Protocol.stepOrSelf (NonuniformMajority L K) c r₁ r₂
        = c - {r₁, r₂} + {(Transition L K r₁ r₂).1, (Transition L K r₁ r₂).2} := by
      unfold Protocol.stepOrSelf; rw [if_pos happ]; rfl
    refine ⟨?_, ?_⟩
    · have hcard' := Protocol.reachable_card_eq
        (Protocol.reachable_stepOrSelf (P := NonuniformMajority L K) c r₁ r₂)
      rw [hcard']; exact hcard
    · intro a ha
      rw [hc'] at ha
      rcases Multiset.mem_add.mp ha with hold | hnew
      · exact hph a (Multiset.mem_of_le (Multiset.sub_le_self _ _) hold)
      · rw [show ({(Transition L K r₁ r₂).1, (Transition L K r₁ r₂).2}
              : Multiset (AgentState L K))
            = (Transition L K r₁ r₂).1 ::ₘ (Transition L K r₁ r₂).2 ::ₘ 0 from rfl] at hnew
        simp only [Multiset.mem_cons, Multiset.notMem_zero, or_false] at hnew
        rw [hac] at hnew
        rcases hnew with h | h
        · subst h
          exact ⟨by rw [hacphase.1]; exact h18, by rw [absorbConsume_role_fst]; exact h1M⟩
        · subst h
          exact ⟨by rw [hacphase.2]; exact h28, by rw [absorbConsume_role_snd]; exact h2M⟩
  · rw [Protocol.stepOrSelf_eq_self_of_not_applicable happ]; exact ⟨hcard, hph⟩

/-- `Phase8AllMain` is one-step-support closed (the FULL engine `InvClosed`). -/
theorem Phase8AllMain_support_closed (n : ℕ) (c c' : Config (AgentState L K))
    (hw : Phase8AllMain n c)
    (hc' : c' ∈ ((NonuniformMajority L K).stepDistOrSelf c).support) :
    Phase8AllMain n c' := by
  by_cases hc : 2 ≤ c.card
  · rw [show (NonuniformMajority L K).stepDistOrSelf c
        = (NonuniformMajority L K).stepDist c hc by
        unfold Protocol.stepDistOrSelf; rw [dif_pos hc]] at hc'
    obtain ⟨⟨r₁, r₂⟩, hr⟩ := Protocol.stepDist_support (NonuniformMajority L K) c hc c' hc'
    rw [← hr]; exact Phase8AllMain_stepOrSelf n c hw r₁ r₂
  · rw [show (NonuniformMajority L K).stepDistOrSelf c = PMF.pure c by
        unfold Protocol.stepDistOrSelf; rw [dif_neg hc]] at hc'
    rw [PMF.mem_support_pure_iff] at hc'; subst hc'; exact hw

/-- Packaged as the engine's `InvClosed` predicate (FULL, for Phase 8). -/
theorem invClosed_phase8AllMain (n : ℕ) :
    OneSidedCancel.InvClosed (NonuniformMajority L K).transitionKernel
      (fun c => Phase8AllMain (L := L) (K := K) n c) := by
  intro c hInv
  change ((NonuniformMajority L K).stepDistOrSelf c).toMeasure
    {x | ¬ Phase8AllMain (L := L) (K := K) n x} = 0
  rw [PMF.toMeasure_apply_eq_zero_iff _ (DiscreteMeasurableSpace.forall_measurableSet _)]
  rw [Set.disjoint_left]
  intro x hsupp hx
  exact hx (Phase8AllMain_support_closed n c x hInv hsupp)

end Phase8Convergence

end ExactMajority
