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
import Ripple.PopulationProtocol.Majority.ExactMajority.Analysis.Invariants

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
  rcases s with
    ⟨sinput, soutput, sphase, srole, sassigned, sbias, ssmallBias,
      shour, sminute, sfull, sopinions, scounter⟩
  rcases t with
    ⟨tinput, toutput, tphase, trole, tassigned, tbias, tsmallBias,
      thour, tminute, tfull, topinions, tcounter⟩
  unfold noBigBias at hs ht
  unfold Phase4Transition
  dsimp at hs ht ⊢
  cases sbias with
  | zero =>
    cases tbias with
    | zero => simp
    | dyadic tg j => simp [ht]
  | dyadic sg i =>
    cases tbias with
    | zero => simp [hs]
    | dyadic tg j => simp [hs, ht]

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
  rw [if_neg (by push Not; intro _; simp)]

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

private theorem mem_of_applicable_left {c : Config (AgentState L K)}
    {r₁ r₂ : AgentState L K} (happ : Protocol.Applicable c r₁ r₂) : r₁ ∈ c := by
  have hle : ({r₁, r₂} : Multiset (AgentState L K)) ≤ c := happ
  exact Multiset.mem_of_le hle (by simp)

private theorem mem_of_applicable_right {c : Config (AgentState L K)}
    {r₁ r₂ : AgentState L K} (happ : Protocol.Applicable c r₁ r₂) : r₂ ∈ c := by
  have hle : ({r₁, r₂} : Multiset (AgentState L K)) ≤ c := happ
  exact Multiset.mem_of_le hle (by simp)

/-- `StableTie4` is preserved by a single chosen-pair update: the two produced
agents are tie-agents (`Transition_preserves_tie_pair`), the unchanged ones keep
the property. -/
theorem StableTie4_stepOrSelf (c : Config (AgentState L K))
    (hw : StableTie4 (L := L) (K := K) c) (r₁ r₂ : AgentState L K) :
    StableTie4 (L := L) (K := K)
      (Protocol.stepOrSelf (NonuniformMajority L K) c r₁ r₂) := by
  by_cases happ : Protocol.Applicable c r₁ r₂
  · have hmem1 := mem_of_applicable_left happ
    have hmem2 := mem_of_applicable_right happ
    obtain ⟨h14, h1T, h1B⟩ := hw r₁ hmem1
    obtain ⟨h24, h2T, h2B⟩ := hw r₂ hmem2
    have hc' : Protocol.stepOrSelf (NonuniformMajority L K) c r₁ r₂
        = c - {r₁, r₂} + {(Transition L K r₁ r₂).1, (Transition L K r₁ r₂).2} := by
      unfold Protocol.stepOrSelf; rw [if_pos happ]; rfl
    obtain ⟨hp1', hp2'⟩ :=
      Transition_preserves_tie_pair (L := L) (K := K) r₁ r₂ h14 h24 h1T h2T h1B h2B
    intro a ha
    rw [hc'] at ha
    rcases Multiset.mem_add.mp ha with hold | hnew
    · exact hw a (Multiset.mem_of_le (Multiset.sub_le_self _ _) hold)
    · rw [show ({(Transition L K r₁ r₂).1, (Transition L K r₁ r₂).2}
            : Multiset (AgentState L K))
          = (Transition L K r₁ r₂).1 ::ₘ (Transition L K r₁ r₂).2 ::ₘ 0 from rfl] at hnew
      simp only [Multiset.mem_cons, Multiset.notMem_zero, or_false] at hnew
      rcases hnew with h | h
      · subst h; exact hp1'
      · subst h; exact hp2'
  · rw [Protocol.stepOrSelf_eq_self_of_not_applicable happ]; exact hw

/-- `StableTie4` is one-step-support closed (kernel-absorbing). -/
theorem StableTie4_absorbing (c c' : Config (AgentState L K))
    (hw : StableTie4 (L := L) (K := K) c)
    (hc' : c' ∈ ((NonuniformMajority L K).stepDistOrSelf c).support) :
    StableTie4 (L := L) (K := K) c' := by
  by_cases hc : 2 ≤ c.card
  · rw [show (NonuniformMajority L K).stepDistOrSelf c = (NonuniformMajority L K).stepDist c hc by
        unfold Protocol.stepDistOrSelf; rw [dif_pos hc]] at hc'
    obtain ⟨⟨r₁, r₂⟩, hr⟩ := Protocol.stepDist_support (NonuniformMajority L K) c hc c' hc'
    rw [← hr]
    exact StableTie4_stepOrSelf c hw r₁ r₂
  · rw [show (NonuniformMajority L K).stepDistOrSelf c = PMF.pure c by
        unfold Protocol.stepDistOrSelf; rw [dif_neg hc]] at hc'
    rw [PMF.mem_support_pure_iff] at hc'
    subst hc'; exact hw

/-! ## Part C — the non-tie advanced-count epidemic (phase ≥ 5 spread).

The mechanism is the phase-`max` epidemic baked into `phaseEpidemicUpdate`:
whenever an advanced agent (`phase ≥ 5`) meets a not-yet-advanced agent, both
`Transition` outputs land at phase `≥ 5` (`Transition_*_phase_ge_pair_max`).  The
informed count `advancedU` is monotone and advances on each (advanced,
non-advanced) interaction.  This is the SAME engine as `Phase2Convergence`'s
opinion epidemic, with "informed" = "phase ≥ 5".  The window `Q4 n` only requires
every agent to be at phase `≥ 4` (so the partner of an advanced agent is also at
phase `≥ 4`, guaranteeing the `max ≥ 5` advance for BOTH outputs). -/

/-- An agent is *advanced* if it has reached Phase 5 or beyond. -/
def advancedP (a : AgentState L K) : Prop := 5 ≤ a.phase.val

instance (a : AgentState L K) : Decidable (advancedP a) := by
  unfold advancedP; infer_instance

/-- The advanced-agent count. -/
def advancedU (c : Config (AgentState L K)) : ℕ :=
  Multiset.countP (fun a => advancedP a) c

/-- The Phase-4 non-tie window: every agent has phase `≥ 4`, fixed size `n`.
One-step closed by phase monotonicity. -/
def Q4 (n : ℕ) (c : Config (AgentState L K)) : Prop :=
  c.card = n ∧ ∀ a ∈ c, 4 ≤ a.phase.val

instance (n : ℕ) (c : Config (AgentState L K)) : Decidable (Q4 n c) := by
  unfold Q4; infer_instance

/-- `countP advancedP` over a two-element pair. -/
theorem countP_advancedP_pair (x y : AgentState L K) :
    Multiset.countP (fun a => advancedP a) ({x, y} : Multiset (AgentState L K))
      = (if advancedP x then 1 else 0) + (if advancedP y then 1 else 0) := by
  rw [show ({x, y} : Multiset (AgentState L K)) = x ::ₘ y ::ₘ 0 from rfl]
  rw [Multiset.countP_cons, Multiset.countP_cons, Multiset.countP_zero]
  ring

/-- **Per-pair advanced-count monotonicity.**  Phase only rises under `Transition`
(`Transition_phase_monotone`), and `advancedP` is upward-closed in phase, so the
advanced count of the produced pair is at least that of the consumed pair. -/
theorem advancedP_pair_mono (s t : AgentState L K) :
    Multiset.countP (fun a => advancedP a) ({s, t} : Multiset (AgentState L K))
      ≤ Multiset.countP (fun a => advancedP a)
          ({(Transition L K s t).1, (Transition L K s t).2}
            : Multiset (AgentState L K)) := by
  have hmono := Transition_phase_monotone (L := L) (K := K) s t
  simp only [] at hmono
  obtain ⟨hsm, htm⟩ := hmono
  rw [countP_advancedP_pair, countP_advancedP_pair]
  have hs' : advancedP s → advancedP (Transition L K s t).1 := fun h => le_trans h hsm
  have ht' : advancedP t → advancedP (Transition L K s t).2 := fun h => le_trans h htm
  by_cases hsa : advancedP s
  · by_cases hta : advancedP t
    · rw [if_pos hsa, if_pos hta, if_pos (hs' hsa), if_pos (ht' hta)]
    · rw [if_pos hsa, if_neg hta, if_pos (hs' hsa)]; split_ifs <;> omega
  · by_cases hta : advancedP t
    · rw [if_neg hsa, if_pos hta, if_pos (ht' hta)]; split_ifs <;> omega
    · rw [if_neg hsa, if_neg hta]; omega

/-- **Per-pair advance.**  A mixed pair — one advanced (`phase ≥ 5`), one
in-window (`phase ≥ 4`) but not advanced — produces two advanced agents, since
both `Transition` outputs have phase `≥ max(s,t) ≥ 5`.  Hence the pair's advanced
count rises from 1 to 2. -/
theorem advancedP_pair_advances (s t : AgentState L K)
    (_hs4 : 4 ≤ s.phase.val) (_ht4 : 4 ≤ t.phase.val)
    (hmixed : (advancedP (L := L) (K := K) s ∧ ¬ advancedP (L := L) (K := K) t) ∨
              (¬ advancedP (L := L) (K := K) s ∧ advancedP (L := L) (K := K) t)) :
    Multiset.countP (fun a => advancedP a) ({s, t} : Multiset (AgentState L K)) + 1
      ≤ Multiset.countP (fun a => advancedP a)
          ({(Transition L K s t).1, (Transition L K s t).2}
            : Multiset (AgentState L K)) := by
  -- both outputs have phase ≥ max(s,t).phase ≥ 5.
  have hmax5 : 5 ≤ max s.phase.val t.phase.val := by
    rcases hmixed with ⟨hsa, _⟩ | ⟨_, hta⟩
    · exact le_trans hsa (le_max_left _ _)
    · exact le_trans hta (le_max_right _ _)
  have hout1 : advancedP (L := L) (K := K) (Transition L K s t).1 :=
    le_trans hmax5 (Transition_left_phase_ge_pair_max (L := L) (K := K) s t)
  have hout2 : advancedP (L := L) (K := K) (Transition L K s t).2 :=
    le_trans hmax5 (Transition_right_phase_ge_pair_max (L := L) (K := K) s t)
  rw [countP_advancedP_pair, countP_advancedP_pair, if_pos hout1, if_pos hout2]
  rcases hmixed with ⟨hsa, hta⟩ | ⟨hsa, hta⟩
  · rw [if_pos hsa, if_neg hta]
  · rw [if_neg hsa, if_pos hta]

/-- `advancedU` is non-decreasing under any chosen-pair update. -/
theorem advancedU_stepOrSelf_ge (c : Config (AgentState L K)) (r₁ r₂ : AgentState L K) :
    advancedU (L := L) (K := K) c
      ≤ advancedU (L := L) (K := K) (Protocol.stepOrSelf (NonuniformMajority L K) c r₁ r₂) := by
  by_cases happ : Protocol.Applicable c r₁ r₂
  · have hsub : ({r₁, r₂} : Multiset (AgentState L K)) ≤ c := happ
    have hc' : Protocol.stepOrSelf (NonuniformMajority L K) c r₁ r₂
        = c - {r₁, r₂} + {(Transition L K r₁ r₂).1, (Transition L K r₁ r₂).2} := by
      unfold Protocol.stepOrSelf; rw [if_pos happ]; rfl
    unfold advancedU
    rw [hc', Multiset.countP_add, Multiset.countP_sub hsub]
    have hpair_le : Multiset.countP (fun a => advancedP a)
        ({r₁, r₂} : Multiset (AgentState L K))
          ≤ Multiset.countP (fun a => advancedP a) c := Multiset.countP_le_of_le _ hsub
    have hmono := advancedP_pair_mono (L := L) (K := K) r₁ r₂
    omega
  · rw [Protocol.stepOrSelf_eq_self_of_not_applicable happ]

/-- `advancedU` is preserved-or-raised on the one-step kernel support. -/
theorem advancedU_ge_monotone (m : ℕ) (c c' : Config (AgentState L K))
    (h : m ≤ advancedU (L := L) (K := K) c)
    (hc' : c' ∈ ((NonuniformMajority L K).stepDistOrSelf c).support) :
    m ≤ advancedU (L := L) (K := K) c' := by
  by_cases hc : 2 ≤ c.card
  · rw [show (NonuniformMajority L K).stepDistOrSelf c = (NonuniformMajority L K).stepDist c hc by
        unfold Protocol.stepDistOrSelf; rw [dif_pos hc]] at hc'
    obtain ⟨⟨r₁, r₂⟩, hr⟩ := Protocol.stepDist_support (NonuniformMajority L K) c hc c' hc'
    rw [← hr]
    exact le_trans h (advancedU_stepOrSelf_ge c r₁ r₂)
  · rw [show (NonuniformMajority L K).stepDistOrSelf c = PMF.pure c by
        unfold Protocol.stepDistOrSelf; rw [dif_neg hc]] at hc'
    rw [PMF.mem_support_pure_iff] at hc'
    subst hc'; exact h

/-! ## Part D — the rectangle advance probability (DERIVED by pair-counting). -/

instance instMeasurableSpaceAgentState4 : MeasurableSpace (AgentState L K) := ⊤
instance instDiscreteMeasurableSpaceAgentState4 :
    DiscreteMeasurableSpace (AgentState L K) where
  forall_measurableSet _ := trivial

/-- A `phase = 4` (susceptible / not-yet-advanced) agent. -/
def susceptibleP (a : AgentState L K) : Prop := a.phase.val = 4

instance (a : AgentState L K) : Decidable (susceptibleP a) := by
  unfold susceptibleP; infer_instance

private theorem applicable_of_mem_distinct {c : Config (AgentState L K)}
    {x y : AgentState L K} (hx : x ∈ c) (hy : y ∈ c) (hxy : x ≠ y) :
    Protocol.Applicable c x y := by
  refine Multiset.le_iff_count.mpr ?_
  intro a
  rw [show ({x, y} : Multiset (AgentState L K)) = x ::ₘ y ::ₘ 0 from rfl,
      Multiset.count_cons, Multiset.count_cons, Multiset.count_zero]
  have hxc : 1 ≤ Multiset.count x c := Multiset.one_le_count_iff_mem.mpr hx
  have hyc : 1 ≤ Multiset.count y c := Multiset.one_le_count_iff_mem.mpr hy
  by_cases hax : a = x
  · subst hax
    have hay : ¬ a = y := fun h => hxy (h ▸ rfl)
    rw [if_pos rfl, if_neg hay]; omega
  · by_cases hay : a = y
    · subst hay; rw [if_neg hax, if_pos rfl]; omega
    · rw [if_neg hax, if_neg hay]; omega

/-- A scheduled (advanced, susceptible) pair advances the GLOBAL advanced count
`advancedU` by one. -/
theorem advancedU_stepOrSelf_advance (c : Config (AgentState L K)) (s t : AgentState L K)
    (happ : Protocol.Applicable c s t)
    (hs4 : 4 ≤ s.phase.val) (ht4 : 4 ≤ t.phase.val)
    (hmixed : (advancedP (L := L) (K := K) s ∧ ¬ advancedP (L := L) (K := K) t) ∨
              (¬ advancedP (L := L) (K := K) s ∧ advancedP (L := L) (K := K) t)) :
    advancedU (L := L) (K := K) c + 1
      ≤ advancedU (L := L) (K := K) (Protocol.stepOrSelf (NonuniformMajority L K) c s t) := by
  have hsub : ({s, t} : Multiset (AgentState L K)) ≤ c := happ
  have hc' : Protocol.stepOrSelf (NonuniformMajority L K) c s t
      = c - {s, t} + {(Transition L K s t).1, (Transition L K s t).2} := by
    unfold Protocol.stepOrSelf; rw [if_pos happ]; rfl
  unfold advancedU
  rw [hc', Multiset.countP_add, Multiset.countP_sub hsub]
  have hpair_le : Multiset.countP (fun a => advancedP a) ({s, t} : Multiset (AgentState L K))
      ≤ Multiset.countP (fun a => advancedP a) c := Multiset.countP_le_of_le _ hsub
  have hadv := advancedP_pair_advances (L := L) (K := K) s t hs4 ht4 hmixed
  omega

/-- **The generic rectangle → advanced-advance-probability bound.**  Mirrors
`Phase2Convergence.informed_advance_prob_of_rect`, with `advancedU` as the
advancing quantity. -/
theorem advanced_advance_prob_of_rect (n : ℕ) (hn : 2 ≤ n)
    (c : Config (AgentState L K)) (hcardn : c.card = n)
    (R : Finset (AgentState L K × AgentState L K)) (N : ℕ)
    (hadv : ∀ p ∈ R, 1 ≤ c.count p.1 → 1 ≤ c.count p.2 → (p.1 = p.2 → 2 ≤ c.count p.1) →
      advancedU (L := L) (K := K) c + 1
        ≤ advancedU (L := L) (K := K) (Protocol.stepOrSelf (NonuniformMajority L K) c p.1 p.2))
    (hcount : (N : ℕ) ≤ ∑ p ∈ R, c.interactionCount p.1 p.2) :
    ENNReal.ofReal ((N : ℝ) / ((n : ℝ) * ((n : ℝ) - 1))) ≤
      ((NonuniformMajority L K).stepDistOrSelf c).toMeasure
        {c' | advancedU (L := L) (K := K) c + 1 ≤ advancedU (L := L) (K := K) c'} := by
  set j := advancedU (L := L) (K := K) c with hjdef
  have hcard2 : 2 ≤ c.card := by rw [hcardn]; omega
  have hmeas : MeasurableSet {c' : Config (AgentState L K) | j + 1 ≤ advancedU c'} :=
    DiscreteMeasurableSpace.forall_measurableSet _
  set S : Finset (AgentState L K × AgentState L K) :=
    R.filter (fun p => 1 ≤ c.count p.1 ∧ 1 ≤ c.count p.2 ∧ (p.1 = p.2 → 2 ≤ c.count p.1)) with hS
  have hsub : (↑S : Set (AgentState L K × AgentState L K)) ⊆
      (Protocol.scheduledStep (NonuniformMajority L K) c) ⁻¹'
        {c' | j + 1 ≤ advancedU c'} := by
    intro p hp
    simp only [Finset.coe_filter, Set.mem_setOf_eq, hS] at hp
    obtain ⟨hpc, hp1, hp2, hp3⟩ := hp
    simp only [Set.mem_preimage, Set.mem_setOf_eq, Protocol.scheduledStep]
    exact hadv p hpc hp1 hp2 hp3
  have hstepDist : (NonuniformMajority L K).stepDistOrSelf c
      = (NonuniformMajority L K).stepDist c hcard2 := by
    unfold Protocol.stepDistOrSelf; rw [dif_pos hcard2]
  have hbase : ((NonuniformMajority L K).stepDistOrSelf c).toMeasure
        {c' | j + 1 ≤ advancedU c'}
      = (c.interactionPMF hcard2).toMeasure
          ((Protocol.scheduledStep (NonuniformMajority L K) c) ⁻¹'
            {c' | j + 1 ≤ advancedU c'}) := by
    rw [hstepDist]; unfold Protocol.stepDist
    rw [PMF.toMeasure_map_apply _ _ _ (Measurable.of_discrete) hmeas]
  rw [hbase]
  have hmono : (c.interactionPMF hcard2).toMeasure (↑S : Set _)
      ≤ (c.interactionPMF hcard2).toMeasure
          ((Protocol.scheduledStep (NonuniformMajority L K) c) ⁻¹'
            {c' | j + 1 ≤ advancedU c'}) :=
    measure_mono hsub
  refine le_trans ?_ hmono
  have hSmeasure : (c.interactionPMF hcard2).toMeasure (↑S : Set _)
      = ∑ p ∈ S, c.interactionProb p.1 p.2 := by
    rw [PMF.toMeasure_apply_finset]; rfl
  have hSsum : ∑ p ∈ S, c.interactionProb p.1 p.2
      = ∑ p ∈ R, c.interactionProb p.1 p.2 := by
    rw [hS]
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro p hpc hpnot
    rw [Finset.mem_filter] at hpnot
    push Not at hpnot
    have hexcl := hpnot hpc
    have hzero : c.interactionCount p.1 p.2 = 0 := by
      unfold Config.interactionCount
      by_cases h1 : 1 ≤ c.count p.1
      · by_cases h2 : 1 ≤ c.count p.2
        · obtain ⟨hpe, hlt⟩ := hexcl h1 h2
          rw [if_pos hpe]
          have hc1 : c.count p.1 = 1 := by omega
          rw [hc1]
        · have hz2 : c.count p.2 = 0 := by omega
          by_cases hpe : p.1 = p.2
          · rw [if_pos hpe]; rw [hpe, hz2, Nat.zero_mul]
          · rw [if_neg hpe, hz2, Nat.mul_zero]
      · have hz1 : c.count p.1 = 0 := by omega
        by_cases hpe : p.1 = p.2
        · rw [if_pos hpe, hz1, Nat.zero_mul]
        · rw [if_neg hpe, hz1, Nat.zero_mul]
    unfold Config.interactionProb; rw [hzero]; simp
  rw [hSmeasure, hSsum]
  have heqterm : ∀ p : AgentState L K × AgentState L K,
      c.interactionProb p.1 p.2
        = (↑(c.interactionCount p.1 p.2) : ℝ≥0∞) * (↑c.totalPairs)⁻¹ := by
    intro p; unfold Config.interactionProb; rw [div_eq_mul_inv]
  rw [Finset.sum_congr rfl (fun p _ => heqterm p), ← Finset.sum_mul, ← Nat.cast_sum]
  set M := ∑ p ∈ R, c.interactionCount p.1 p.2 with hM
  have htp : c.totalPairs = n * (n - 1) := by rw [Config.totalPairs, hcardn]
  rw [htp, ← div_eq_mul_inv]
  have hden_pos : (0 : ℝ) < ((n * (n - 1) : ℕ) : ℝ) := by
    have : 0 < n * (n - 1) := Nat.mul_pos (by omega) (by omega)
    exact_mod_cast this
  have hdenR : ((n * (n - 1) : ℕ) : ℝ) = (n : ℝ) * ((n : ℝ) - 1) := by
    rw [Nat.cast_mul, Nat.cast_sub (by omega)]; push_cast; ring
  have hstep1 : ENNReal.ofReal ((N : ℝ) / ((n : ℝ) * ((n : ℝ) - 1)))
      ≤ ENNReal.ofReal (((M : ℕ) : ℝ) / ((n * (n - 1) : ℕ) : ℝ)) := by
    apply ENNReal.ofReal_le_ofReal
    rw [hdenR]
    have hNM : (N : ℝ) ≤ (M : ℝ) := by exact_mod_cast hcount
    have hposden : (0 : ℝ) < (n : ℝ) * ((n : ℝ) - 1) := by rw [← hdenR]; exact hden_pos
    gcongr
  refine le_trans hstep1 ?_
  rw [← ENNReal.ofReal_natCast M, ← ENNReal.ofReal_natCast (n * (n - 1)),
      ← ENNReal.ofReal_div_of_pos hden_pos]

/-! ## Part E — the advanced×susceptible rectangle and the SYNC advance prob. -/

/-- For two state-finsets `A`, `B` of pairwise-distinct states, the
`interactionCount` mass of `A ×ˢ B` is `(∑_A count)·(∑_B count)`.  (Local copy of
`Phase2Convergence.sum_interactionCount_cross_disjoint'`.) -/
theorem sum_interactionCount_cross_disjoint
    (c : Config (AgentState L K)) (A B : Finset (AgentState L K))
    (hdisj : ∀ a ∈ A, ∀ b ∈ B, a ≠ b) :
    (∑ p ∈ A ×ˢ B, c.interactionCount p.1 p.2)
      = (∑ a ∈ A, c.count a) * (∑ b ∈ B, c.count b) := by
  rw [Finset.sum_product, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a ha
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b hb
  unfold Config.interactionCount
  rw [if_neg (hdisj a ha b hb)]

/-- `∑ count` over the advanced STATES equals `advancedU c`. -/
theorem sum_count_advanced (c : Config (AgentState L K)) :
    (∑ a ∈ Finset.univ.filter (fun a : AgentState L K => advancedP a), c.count a)
      = advancedU (L := L) (K := K) c := by
  have hcard : (Multiset.filter (fun a : AgentState L K => advancedP a) c).card
      = advancedU (L := L) (K := K) c := by
    unfold advancedU; rw [Multiset.countP_eq_card_filter]
  rw [← hcard]
  have hcount_eq : ∀ a ∈ Finset.univ.filter (fun a : AgentState L K => advancedP a),
      c.count a
        = Multiset.count a (Multiset.filter (fun a : AgentState L K => advancedP a) c) := by
    intro a ha
    rw [Finset.mem_filter] at ha
    rw [Config.count, Multiset.count_filter, if_pos ha.2]
  rw [Finset.sum_congr rfl hcount_eq, Multiset.sum_count_eq_card]
  intro a ha
  rw [Multiset.mem_filter] at ha
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ a, ha.2⟩

/-- `∑ count` over the susceptible STATES equals `countP susceptibleP c`. -/
theorem sum_count_susceptible (c : Config (AgentState L K)) :
    (∑ a ∈ Finset.univ.filter (fun a : AgentState L K => susceptibleP a), c.count a)
      = Multiset.countP (fun a => susceptibleP a) c := by
  have hcard : (Multiset.filter (fun a : AgentState L K => susceptibleP a) c).card
      = Multiset.countP (fun a => susceptibleP a) c := by
    rw [Multiset.countP_eq_card_filter]
  rw [← hcard]
  have hcount_eq : ∀ a ∈ Finset.univ.filter (fun a : AgentState L K => susceptibleP a),
      c.count a
        = Multiset.count a (Multiset.filter (fun a : AgentState L K => susceptibleP a) c) := by
    intro a ha
    rw [Finset.mem_filter] at ha
    rw [Config.count, Multiset.count_filter, if_pos ha.2]
  rw [Finset.sum_congr rfl hcount_eq, Multiset.sum_count_eq_card]
  intro a ha
  rw [Multiset.mem_filter] at ha
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ a, ha.2⟩

/-- On the window `Q4 n`, every agent is advanced (`phase ≥ 5`) XOR susceptible
(`phase = 4`), so `advancedU + susceptibleU = n`.  Hence the susceptible count is
`n − advancedU`. -/
theorem susceptible_count_eq (n : ℕ) (c : Config (AgentState L K)) (hw : Q4 n c) :
    Multiset.countP (fun a => susceptibleP a) c = n - advancedU (L := L) (K := K) c := by
  unfold advancedU
  have hsplit : Multiset.countP (fun a => advancedP a) c
      + Multiset.countP (fun a => susceptibleP a) c = c.card := by
    rw [Multiset.countP_eq_card_filter, Multiset.countP_eq_card_filter, ← Multiset.card_add]
    congr 1
    refine Multiset.ext.mpr ?_
    intro a
    rw [Multiset.count_add, Multiset.count_filter, Multiset.count_filter]
    by_cases hmem : a ∈ c
    · have hp4 := hw.2 a hmem
      by_cases hadv : advancedP (L := L) (K := K) a
      · have hnsus : ¬ susceptibleP (L := L) (K := K) a := by
          simp only [advancedP, susceptibleP] at hadv ⊢; omega
        rw [if_pos hadv, if_neg hnsus]; omega
      · have hsus : susceptibleP (L := L) (K := K) a := by
          simp only [advancedP, susceptibleP] at hadv ⊢; omega
        rw [if_neg hadv, if_pos hsus]; omega
    · have h0 : Multiset.count a c = 0 := Multiset.count_eq_zero.mpr hmem
      rw [h0]; simp
  rw [hw.1] at hsplit
  omega

/-- The advanced×susceptible rectangle `interactionCount` mass is `m·(n−m)`,
`m = advancedU c` (cross pairs distinct: advanced `phase ≥ 5`, susceptible
`phase = 4`). -/
theorem sum_interactionCount_syncRect (n : ℕ) (c : Config (AgentState L K)) (hw : Q4 n c) :
    (∑ p ∈ (Finset.univ.filter (fun a : AgentState L K => advancedP a)) ×ˢ
        (Finset.univ.filter (fun a : AgentState L K => susceptibleP a)),
        c.interactionCount p.1 p.2)
      = advancedU (L := L) (K := K) c * (n - advancedU (L := L) (K := K) c) := by
  rw [Phase2Convergence.sum_interactionCount_cross_disjoint' c _ _ ?_, sum_count_advanced,
      sum_count_susceptible, susceptible_count_eq n c hw]
  intro a ha b hb
  rw [Finset.mem_filter] at ha hb
  intro hab
  have haA : advancedP (L := L) (K := K) a := ha.2
  have hbS : susceptibleP (L := L) (K := K) b := hb.2
  rw [hab] at haA
  unfold advancedP susceptibleP at haA hbS; omega

/-- **The SYNC advanced-advance probability (DERIVED).**  One step raises
`advancedU` by `≥ 1` with probability `≥ m·(n−m)/(n(n−1))`, `m = advancedU c`. -/
theorem advanced_advance_prob (n : ℕ) (hn : 2 ≤ n)
    (c : Config (AgentState L K)) (hw : Q4 n c) :
    ENNReal.ofReal
        (((advancedU (L := L) (K := K) c * (n - advancedU (L := L) (K := K) c) : ℕ) : ℝ)
          / ((n : ℝ) * ((n : ℝ) - 1))) ≤
      ((NonuniformMajority L K).stepDistOrSelf c).toMeasure
        {c' | advancedU (L := L) (K := K) c + 1 ≤ advancedU (L := L) (K := K) c'} := by
  set R := (Finset.univ.filter (fun a : AgentState L K => advancedP a)) ×ˢ
    (Finset.univ.filter (fun a : AgentState L K => susceptibleP a)) with hR
  set m := advancedU (L := L) (K := K) c with hmdef
  have hcount : m * (n - m) ≤ ∑ p ∈ R, c.interactionCount p.1 p.2 := by
    rw [hR, sum_interactionCount_syncRect n c hw]
  refine advanced_advance_prob_of_rect n hn c hw.1 R (m * (n - m)) ?_ hcount
  · rintro ⟨a, b⟩ hp h1 h2 _hsame
    rw [hR, Finset.mem_product, Finset.mem_filter, Finset.mem_filter] at hp
    obtain ⟨⟨_, haA⟩, ⟨_, hbS⟩⟩ := hp
    have haadv : advancedP (L := L) (K := K) a := haA
    have hbsus : susceptibleP (L := L) (K := K) b := hbS
    have ha4 : 4 ≤ a.phase.val := by unfold advancedP at haadv; omega
    have hb4 : 4 ≤ b.phase.val := by unfold susceptibleP at hbsus; omega
    have hbnadv : ¬ advancedP (L := L) (K := K) b := by
      unfold advancedP susceptibleP at hbsus ⊢; omega
    have hamem : a ∈ c := Multiset.one_le_count_iff_mem.mp h1
    have hbmem : b ∈ c := Multiset.one_le_count_iff_mem.mp h2
    have hab : a ≠ b := by
      intro h; rw [h] at haadv; exact hbnadv haadv
    have happ : Protocol.Applicable c a b := applicable_of_mem_distinct hamem hbmem hab
    exact advancedU_stepOrSelf_advance c a b happ ha4 hb4 (Or.inl ⟨haadv, hbnadv⟩)

end Phase4Convergence

end ExactMajority
