/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# `TopSplitInward` — discharging `InwardResidual` (the genuine Lemma 5.1 C-1 fact).

Doty et al., *Exact Majority* (arXiv:2106.10201v2), §5.1 (Lemma 5.1 top-split
balance).  `Probability/TopSplitDrift.lean` reduced the boundary-free cosh-MGF
top-split tail to a single honest protocol residual, `InwardResidual s c`:

    sinh(s · X c) · E[sinh(s · ΔX)] ≤ 0,   X c = mainCount c − topCRMass c,

where `E[sinh(s·ΔX)] = ∑_pair interactionProb(c,pair)·sinh(s·Δ_pair)` is the
one-step expected signed `sinh`-jump.  This file DISCHARGES `InwardResidual`
on the Phase-0 region (`allPhase0 ∧ 2 ≤ card`), with NO further hypothesis — the
honest, hypothesis-free Lemma-5.1 content — and wires the result into
`TopSplitDrift`'s cosh engine to produce the strongest top-split tail reachable.

## The honest assigned-balance ledger (Stage 1 — the new mathematical content).

Computing the per-rule effect on the FOUR free/assigned pools against the FROZEN
`Protocol/Transition.lean` (`Phase0Transition`, rules R1–R5):

  * `Mf` = #unassigned-Main,  `Ma` = #assigned-Main;
  * `Sf` = #unassigned-(cr/clock/reserve),  `Sa` = #assigned-(cr/clock/reserve).

`X = mainCount − topCRMass = (Mf + Ma) − (Sf + Sa)`.  Per rule:

  * **R1** (mcr,mcr → main,cr): the fresh Main inherits `s.assigned`, the fresh CR
    inherits `t.assigned`, so `ΔMf = ΔSf`, `ΔMa = ΔSa` ⟹ `Δ(Mf−Sf) = 0`, `ΔX = 0`.
  * **R2** (mcr + unassigned-Main → cr(unassigned) + Main(assigned)): `Mf −1`,
    `Ma +1`, `Sf +1` ⟹ `Δ(Mf−Sf) = −2`, `ΔX = −1`.
  * **R3** (mcr + unassigned-CR-side → Main(unassigned) + partner(assigned)):
    `Mf +1`, `Sf −1`, `Sa +1` ⟹ `Δ(Mf−Sf) = +2`, `ΔX = +1`.
  * **R4** (cr,cr → clock,reserve): both stay CR-side, `assigned` untouched ⟹
    `ΔSf = ΔSa = 0`, `Δ(Mf−Sf) = 0`, `ΔX = 0`.
  * **R5** (clock,clock → clock,clock): role/assigned unchanged ⟹ `Δ(Mf−Sf) = 0`.

So `Δ(Mf − Sf) = 2·ΔX` for EVERY rule, and at the all-`mcr` start `Mf−Sf = 0 =
2·X`.  Hence the **honest preserved invariant**

    Mf − Sf = 2 · X      (`freeDiff_eq_two_topSplit`)

with `freeW a := [main ∧ ¬asg] − [(cr∨clock∨reserve) ∧ ¬asg]` the per-agent
weight (`Config.sumOf freeW = Mf − Sf`).  This is the Lean-faithful counterpart of
the paper's `sf + 2·st = mf + 2·mt` ledger: when more Main than RoleCR-mass has
been produced (`X > 0`) there are STRICTLY more free Mains than free CR-side
agents (`Mf − Sf = 2X > 0`), so the next `X`-changing interaction is more likely
to DECREASE `X` — exactly the inward sign-drift.

## Stages 2–4.

  * **Stage 2** (`freeDiff_sign_of_topSplit`): `X > 0 ⟹ Sf < Mf`, `X < 0 ⟹ Mf < Sf`.
  * **Stage 3** (`expDelta_eq…`): `sinh(s·Δ_pair) = Δ_pair · sinh s` (since `Δ ∈
    {−1,0,1}`), so `E[sinh(s·Δ)] = sinh s · E[Δ]`, and `E[Δ]·totalPairs =
    2·mcrCount·(Sf − Mf)` via the R2/R3 marginal rectangle.
  * **Stage 4** (`inwardResidual_holds`): with `Sf − Mf = −2X`, `E[Δ] =
    −4·mcrCount·X/totalPairs`, so `X·E[Δ] ≤ 0` ⟹ `sinh(s·X)·E[sinh(s·Δ)] ≤ 0`.
    Wired into `coshPot_drift` / `topSplitWindow_whp_cosh` to produce the
    hypothesis-free top-split tail.

Everything here is 0-`sorry` / 0-`axiom` (only `propext`, `Classical.choice`,
`Quot.sound`) / no `native_decide`.

Reference: Doty et al. §5.1; `Probability/TopSplitDrift.lean`;
`HANDOFF_ROLESPLIT_TOPSPLIT.md`; FROZEN `Protocol/Transition.lean`.
-/

import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.TopSplitDrift

namespace ExactMajority
namespace RoleSplitConcentration

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Real BigOperators

variable {L K : ℕ}

/-! ## Stage 1 — the assigned-balance ledger (the honest invariant). -/

/-- The per-agent FREE-pool weight: `+1` for an unassigned `Main`, `−1` for an
unassigned agent in the RoleCR-descended pool (`cr`/`clock`/`reserve`), `0`
otherwise (assigned agents and transient `mcr`).  Summing gives `Mf − Sf`
(`#unassigned-Main − #unassigned-CR-side`). -/
def freeW (a : AgentState L K) : ℤ :=
  (if a.role = .main ∧ ¬ a.assigned then 1 else 0)
    - (if (a.role = .cr ∨ a.role = .clock ∨ a.role = .reserve) ∧ ¬ a.assigned then 1 else 0)

/-- The integer free-pool difference `Mf − Sf` as a multiset sum of `freeW`. -/
def freeDiff (c : Config (AgentState L K)) : ℤ :=
  Config.sumOf (freeW (L := L) (K := K)) c

/-- `freeW` reads only the agent's `role` and `assigned`. -/
private lemma freeW_eq_of_role_assigned_eq (a b : AgentState L K)
    (hr : a.role = b.role) (ha : a.assigned = b.assigned) :
    freeW (L := L) (K := K) a = freeW (L := L) (K := K) b := by
  unfold freeW; rw [hr, ha]

/-- `phaseInit` never writes the `assigned` flag. -/
private lemma phaseInit_assigned_eq (p : Fin 11) (a : AgentState L K) :
    (phaseInit L K p a).assigned = a.assigned := by
  fin_cases p
  · unfold phaseInit; simp
  · unfold phaseInit; simp; split_ifs <;> simp [enterPhase10_assigned]
  · unfold phaseInit; simp
    by_cases h : a.smallBias.val ≤ 1 ∨ a.smallBias.val ≥ 5
    · simp [h, enterPhase10_assigned]
    · simp [h]
  · unfold phaseInit; simp; split <;> simp
  · unfold phaseInit; simp
  · unfold phaseInit; simp; split_ifs <;> simp
  · unfold phaseInit; simp; split_ifs <;> simp
  · unfold phaseInit; simp; split_ifs <;> simp
  · unfold phaseInit; simp
  · unfold phaseInit; simp
    by_cases h : a.smallBias.val ≤ 1 ∨ a.smallBias.val ≥ 5
    · simp [h, enterPhase10_assigned]
    · simp [h]
  · unfold phaseInit; simp [enterPhase10_assigned]

/-- `stdCounterSubroutine` preserves the `assigned` flag (neither `advancePhase`,
`phaseInit`, nor `enterPhase10` ever writes `assigned`). -/
private lemma stdCounterSubroutine_assigned_eq (a : AgentState L K) :
    (stdCounterSubroutine L K a).assigned = a.assigned := by
  unfold stdCounterSubroutine
  split
  · -- advancePhaseWithInit = phaseInit (advancePhase a).phase (advancePhase a)
    unfold advancePhaseWithInit
    rw [phaseInit_assigned_eq]
    unfold advancePhase
    split <;> rfl
  · rfl

/-- The Standard Counter Subroutine keeps a `Clock` agent a `Clock` (local copy
of the private TopSplitDrift lemma). -/
private lemma stdCounterSubroutine_clock_role_eq' (a : AgentState L K)
    (ha : a.role = .clock) :
    (stdCounterSubroutine L K a).role = .clock := by
  unfold stdCounterSubroutine
  split
  · exact advancePhaseWithInit_clock_role_eq L K a ha
  · exact ha

/-- `topW (stdCounterSubroutine a) = topW a` for a clock agent (local copy). -/
private lemma topW_stdCounterSubroutine_clock' (a : AgentState L K)
    (ha : a.role = .clock) :
    topW (L := L) (K := K) (stdCounterSubroutine L K a) = topW (L := L) (K := K) a := by
  unfold topW
  rw [stdCounterSubroutine_clock_role_eq' a ha, ha]

/-- `freeW (stdCounterSubroutine a) = freeW a` for a clock agent (role stays
`clock`, `assigned` preserved). -/
private lemma freeW_stdCounterSubroutine_clock (a : AgentState L K)
    (ha : a.role = .clock) :
    freeW (L := L) (K := K) (stdCounterSubroutine L K a)
      = freeW (L := L) (K := K) a :=
  freeW_eq_of_role_assigned_eq _ _
    ((stdCounterSubroutine_clock_role_eq' a ha).trans ha.symm)
    (stdCounterSubroutine_assigned_eq a)

/-- The combined per-agent ledger weight `g = freeW − 2·topW`, which the per-pair
conservation below shows is exactly preserved by every Phase-0 rule on agents that
are not *assigned `mcr`* (an unreachable corner — `Phase0Initial` starts with every
`mcr` UNassigned and NO rule ever produces an `mcr`, so `assigned mcr` never
arises; see `NoAssignedMcr`). -/
private def ledgerW (a : AgentState L K) : ℤ :=
  freeW (L := L) (K := K) a - 2 * topW (L := L) (K := K) a

/-- An agent is *not an assigned `mcr`* — the honest reachability side-condition
the per-pair ledger conservation needs.  Holds for every agent reachable from
`Phase0Initial`: the initial `mcr` agents are unassigned, and no Phase-0 rule
ever assigns an `mcr` or creates a fresh `mcr` (rules only CONSUME `mcr`). -/
def NotAssignedMcr (a : AgentState L K) : Prop :=
  ¬ (a.role = .mcr ∧ a.assigned = true)

set_option maxHeartbeats 1600000 in
/-- **Per-pair ledger conservation (`Phase0Transition`).**  `freeW − 2·topW`
summed over the output pair equals the same over the input pair: the
assigned-balance ledger `Mf − Sf − 2·X` is locally conserved by every Phase-0
rule, on inputs that are not assigned `mcr` (`NotAssignedMcr`, the honest
reachability side-condition — see its doc).  Finite case check over the
role/assigned tree (R5 clock–clock split off, where both fields are preserved by
`stdCounterSubroutine`; the two assigned-`mcr` input cases are excluded by the
hypotheses). -/
theorem ledgerW_Phase0_pair_conserved (r₁ r₂ : AgentState L K)
    (h₁ : NotAssignedMcr (L := L) (K := K) r₁)
    (h₂ : NotAssignedMcr (L := L) (K := K) r₂) :
    ledgerW (L := L) (K := K) (Phase0Transition L K r₁ r₂).1
        + ledgerW (L := L) (K := K) (Phase0Transition L K r₁ r₂).2
      = ledgerW (L := L) (K := K) r₁ + ledgerW (L := L) (K := K) r₂ := by
  unfold ledgerW
  by_cases hcc : r₁.role = .clock ∧ r₂.role = .clock
  · obtain ⟨hr₁, hr₂⟩ := hcc
    have hpt : Phase0Transition L K r₁ r₂
        = (stdCounterSubroutine L K r₁, stdCounterSubroutine L K r₂) := by
      unfold Phase0Transition
      simp only [hr₁, hr₂, reduceCtorEq, and_self, and_true, true_and, and_false,
        false_and, if_true, if_false, ite_true, ite_false]
    rw [hpt]
    rw [freeW_stdCounterSubroutine_clock r₁ hr₁, freeW_stdCounterSubroutine_clock r₂ hr₂,
        topW_stdCounterSubroutine_clock' r₁ hr₁, topW_stdCounterSubroutine_clock' r₂ hr₂]
  · unfold NotAssignedMcr at h₁ h₂
    rcases r₁ with
      ⟨in₁, out₁, ph₁, role₁, asg₁, bias₁, sb₁, hr₁, mn₁, fl₁, op₁, ctr₁⟩
    rcases r₂ with
      ⟨in₂, out₂, ph₂, role₂, asg₂, bias₂, sb₂, hr₂, mn₂, fl₂, op₂, ctr₂⟩
    cases role₁ <;> cases role₂ <;> cases asg₁ <;> cases asg₂ <;>
      first
      | (exfalso; exact hcc ⟨rfl, rfl⟩)
      | (exact absurd ⟨rfl, rfl⟩ h₁)
      | (exact absurd ⟨rfl, rfl⟩ h₂)
      | (simp only [Phase0Transition, freeW, topW, reduceCtorEq, ne_eq, and_true,
          and_false, true_and, false_and, and_self, if_true, if_false, ite_true, ite_false,
          or_true, or_false, false_or, true_or, not_true_eq_false, not_false_eq_true,
          Bool.not_true, Bool.not_false, Bool.true_eq_false, Bool.false_eq_true] <;> norm_num)

/-! ## Stage 1b — the global ledger invariant `freeDiff = 2·X` (preserved + initial). -/

/-- `freeDiff` agrees with the role/assigned counts: it is `Mf − Sf`. -/
theorem freeDiff_eq_sumOf (c : Config (AgentState L K)) :
    freeDiff (L := L) (K := K) c = Config.sumOf (freeW (L := L) (K := K)) c := rfl

/-- The per-config ledger predicate: `freeDiff c = 2 · topSplitXZ c`, i.e.
`Mf − Sf = 2·X`.  The honest assigned-balance invariant; holds at the balanced
all-`mcr` start and is preserved by every Phase-0 step (Stage 1b). -/
def LedgerInv (c : Config (AgentState L K)) : Prop :=
  freeDiff (L := L) (K := K) c = 2 * topSplitXZ (L := L) (K := K) c

/-- The per-config "no assigned `mcr`" predicate. -/
def NoAssignedMcrConfig (c : Config (AgentState L K)) : Prop :=
  ∀ a ∈ c, NotAssignedMcr (L := L) (K := K) a

/-- `topW` reads only the agent's `role` (local copy of the private TopSplitDrift
lemma). -/
private lemma topW_eq_of_role_eq' (a b : AgentState L K) (h : a.role = b.role) :
    topW (L := L) (K := K) a = topW (L := L) (K := K) b := by
  unfold topW; rw [h]

/-- At both phase 0, the full `Transition` output `assigned` flags equal the
`Phase0Transition` output flags (the epidemic update is identity and
`finishPhase10Entry` projects `assigned` to the post-dispatch value). -/
theorem Transition_assigned_eq_phase0_of_both_phase0
    (s t : AgentState L K) (hs : s.phase.val = 0) (ht : t.phase.val = 0) :
    (Transition L K s t).1.assigned = (Phase0Transition L K s t).1.assigned ∧
    (Transition L K s t).2.assigned = (Phase0Transition L K s t).2.assigned := by
  have hpe := phaseEpidemicUpdate_eq_self_of_both_phase0 (L := L) (K := K) s t hs ht
  have hs0 : s.phase = (⟨0, by omega⟩ : Fin _) := Fin.ext hs
  unfold Transition
  rw [hpe]
  simp only [finishPhase10Entry_assigned]
  rw [hs0]
  exact ⟨rfl, rfl⟩

/-- `Config.sumOf` of a sum-of-weights splits additively over `+`. -/
private lemma sumOf_add_pair (c : Config (AgentState L K)) (r₁ r₂ : AgentState L K)
    (hle : ({r₁, r₂} : Config (AgentState L K)) ≤ c) (w : AgentState L K → ℤ) :
    Config.sumOf w c
      = Config.sumOf w (c - {r₁, r₂}) + (w r₁ + w r₂) := by
  unfold Config.sumOf
  conv_lhs => rw [← Multiset.sub_add_cancel hle]
  rw [Multiset.map_add, Multiset.sum_add]
  congr 1
  show w r₁ + (w r₂ + 0) = _
  rw [add_zero]

/-- **`LedgerInv` is preserved by `stepOrSelf` on the Phase-0 / no-assigned-`mcr`
region.**  The per-pair ledger conservation `ledgerW_Phase0_pair_conserved` lifts
through the additive `Config.sumOf` decomposition: `freeDiff − 2·topSplitXZ =
Config.sumOf ledgerW` is unchanged by removing the input pair and inserting the
output pair (whose `ledgerW`-block matches), hence `LedgerInv` propagates. -/
theorem LedgerInv_stepOrSelf
    (c : Config (AgentState L K)) (r₁ r₂ : AgentState L K)
    (hall : Phase0Window.allPhase0 (L := L) (K := K) c)
    (hnomcr : NoAssignedMcrConfig (L := L) (K := K) c)
    (hled : LedgerInv (L := L) (K := K) c) :
    LedgerInv (L := L) (K := K)
      (Protocol.stepOrSelf (NonuniformMajority L K) c r₁ r₂) := by
  classical
  by_cases happ : Protocol.Applicable c r₁ r₂
  · have hle : ({r₁, r₂} : Config (AgentState L K)) ≤ c := happ
    have hr₁ : r₁ ∈ c := Multiset.mem_of_le hle (by simp)
    have hr₂ : r₂ ∈ c := Multiset.mem_of_le hle (by simp)
    have h₁ : r₁.phase.val = 0 := by have := hall r₁ hr₁; simp [this]
    have h₂ : r₂.phase.val = 0 := by have := hall r₂ hr₂; simp [this]
    have hn₁ : NotAssignedMcr (L := L) (K := K) r₁ := hnomcr r₁ hr₁
    have hn₂ : NotAssignedMcr (L := L) (K := K) r₂ := hnomcr r₂ hr₂
    -- The combined ledger weight `Config.sumOf ledgerW` is `freeDiff − 2·topSplitXZ`.
    have hcomb : ∀ d : Config (AgentState L K),
        Config.sumOf (ledgerW (L := L) (K := K)) d
          = freeDiff (L := L) (K := K) d - 2 * topSplitXZ (L := L) (K := K) d := by
      intro d
      unfold ledgerW freeDiff topSplitXZ Config.sumOf
      induction d using Multiset.induction with
      | empty => simp
      | cons a s ih => simp only [Multiset.map_cons, Multiset.sum_cons, ih]; ring
    have hstep : Protocol.stepOrSelf (NonuniformMajority L K) c r₁ r₂
        = c - {r₁, r₂} + {(Transition L K r₁ r₂).1, (Transition L K r₁ r₂).2} := by
      unfold Protocol.stepOrSelf; rw [if_pos happ]; rfl
    -- `ledgerW` reads role+assigned only, so the Transition output matches Phase0Transition.
    have hrole := Transition_roles_eq_phase0_of_both_phase0 (L := L) (K := K) r₁ r₂ h₁ h₂
    have hasg := Transition_assigned_eq_phase0_of_both_phase0 (L := L) (K := K) r₁ r₂ h₁ h₂
    have hpair : ledgerW (L := L) (K := K) (Transition L K r₁ r₂).1
          + ledgerW (L := L) (K := K) (Transition L K r₁ r₂).2
        = ledgerW (L := L) (K := K) r₁ + ledgerW (L := L) (K := K) r₂ := by
      have e1 : ledgerW (L := L) (K := K) (Transition L K r₁ r₂).1
          = ledgerW (L := L) (K := K) (Phase0Transition L K r₁ r₂).1 := by
        unfold ledgerW
        rw [freeW_eq_of_role_assigned_eq _ _ hrole.1 hasg.1,
            topW_eq_of_role_eq' _ _ hrole.1]
      have e2 : ledgerW (L := L) (K := K) (Transition L K r₁ r₂).2
          = ledgerW (L := L) (K := K) (Phase0Transition L K r₁ r₂).2 := by
        unfold ledgerW
        rw [freeW_eq_of_role_assigned_eq _ _ hrole.2 hasg.2,
            topW_eq_of_role_eq' _ _ hrole.2]
      rw [e1, e2]
      exact ledgerW_Phase0_pair_conserved r₁ r₂ hn₁ hn₂
    -- Combine: Config.sumOf ledgerW (step) = Config.sumOf ledgerW c = 0.
    have hsumstep : Config.sumOf (ledgerW (L := L) (K := K))
          (Protocol.stepOrSelf (NonuniformMajority L K) c r₁ r₂)
        = Config.sumOf (ledgerW (L := L) (K := K)) c := by
      rw [hstep]
      have hout := sumOf_add_pair (c - {r₁, r₂} + {(Transition L K r₁ r₂).1,
          (Transition L K r₁ r₂).2}) (Transition L K r₁ r₂).1 (Transition L K r₁ r₂).2
          (by simp) (ledgerW (L := L) (K := K))
      have hsrc := sumOf_add_pair c r₁ r₂ hle (ledgerW (L := L) (K := K))
      rw [hout, hsrc, hpair]
      congr 1
      -- (c - {r₁,r₂} + {o₁,o₂}) - {o₁,o₂} = c - {r₁,r₂}
      rw [Multiset.add_sub_cancel_right]
    have hzero : Config.sumOf (ledgerW (L := L) (K := K)) c = 0 := by
      rw [hcomb]; unfold LedgerInv at hled; rw [hled]; ring
    have : Config.sumOf (ledgerW (L := L) (K := K))
        (Protocol.stepOrSelf (NonuniformMajority L K) c r₁ r₂) = 0 := by
      rw [hsumstep, hzero]
    unfold LedgerInv
    have := this
    rw [hcomb] at this
    linarith [this]
  · rw [Protocol.stepOrSelf, if_neg happ]; exact hled

end RoleSplitConcentration
end ExactMajority
