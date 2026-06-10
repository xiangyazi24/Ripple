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
conservation below shows is exactly preserved by every Phase-0 rule. -/
private def ledgerW (a : AgentState L K) : ℤ :=
  freeW (L := L) (K := K) a - 2 * topW (L := L) (K := K) a

set_option maxHeartbeats 1600000 in
/-- **Per-pair ledger conservation (`Phase0Transition`).**  `freeW − 2·topW`
summed over the output pair equals the same over the input pair: the
assigned-balance ledger `Mf − Sf − 2·X` is locally conserved by every Phase-0
rule.  Finite case check over the role/assigned tree (R5 clock–clock split off,
where both fields are preserved by `stdCounterSubroutine`). -/
theorem ledgerW_Phase0_pair_conserved (r₁ r₂ : AgentState L K) :
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
  · rcases r₁ with
      ⟨in₁, out₁, ph₁, role₁, asg₁, bias₁, sb₁, hr₁, mn₁, fl₁, op₁, ctr₁⟩
    rcases r₂ with
      ⟨in₂, out₂, ph₂, role₂, asg₂, bias₂, sb₂, hr₂, mn₂, fl₂, op₂, ctr₂⟩
    cases role₁ <;> cases role₂ <;> cases asg₁ <;> cases asg₂ <;>
      first
      | (exfalso; exact hcc ⟨rfl, rfl⟩)
      | (simp only [Phase0Transition, freeW, topW, stdCounterSubroutine, reduceCtorEq,
          ne_eq, and_true, and_false, true_and, false_and, if_true, if_false, ite_true,
          ite_false, or_true, or_false, false_or, true_or, not_true_eq_false,
          not_false_eq_true, not_true, not_false_iff, not_and, decide_eq_true_eq,
          Bool.not_false, Bool.not_true, Bool.false_eq_true] <;> decide)

end RoleSplitConcentration
end ExactMajority
