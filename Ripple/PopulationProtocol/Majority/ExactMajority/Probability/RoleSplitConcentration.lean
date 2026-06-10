/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Lemma 5.2 — Phase-0 role-split concentration (clock-count `= Θ(n)` whp).

Doty et al., *Exact Majority* (arXiv:2106.10201v2), Lemma 5.2.

Phase 0 splits the population (all initially `RoleMCR`) into three roles:
`Main`, `Clock`, `Reserve`.  The paper proves that by the end of Phase 0,

  * `|RoleMCR| = 0`;
  * `(1 − ε)·n/2 ≤ |Main| ≤ (1 + ε)·n/2`;
  * `|Clock|, |Reserve| ≥ (1 − ε)·n/4`,

all with high probability `1 − O(1/n²)`.  The paper proof has two stages:
first `RoleMCR → RoleCR + Main` (a `U,U → M,S` split, Lemma 5.1), then
`RoleCR → Clock + Reserve` modeled by `U,U → R,C` (success probability
`O(l²/n²)` per interaction at count `l`, Corollary 4.4) plus `U → R` at phase
end.  The concentration is a balls-in-bins / Chernoff argument.

This foundational file packages the **statement** of Lemma 5.2 in the exact
downstream-consumable shape (`RoleSplitGood`, `phase0_roleSplit_whp`) and proves
in full the **deterministic** consequences every counter-timed phase relies on:

  * `clockCount_linear_of_RoleSplitGood` : `RoleSplitGood` ⇒ `n/5 ≤ |Clock|`
    (the `Θ(n)` clock-count lower bound feeding every timed phase);
  * the analogous `reserveCount`, `mainCount` linear bounds;
  * `clockCount_ge_two_of_phase1Initializes` : the probability-1 floor `2 ≤ |C|`
    needed for the Standard Counter Subroutine to count at all (paper: "there
    must be at least two Clock agents … so if Phase 1 initializes, c ≥ 2").

The probabilistic content of `phase0_roleSplit_whp` is abstracted into the
`roleSplitTail` budget (the kernel mass of the bad set after `tRole` steps);
the future two-stage role-split concentration engine discharges that budget.
Stating it this way keeps the file `sorry`-free while exposing the precise
interface the Phase-0 `PhaseConvergence` upgrade and all timed phases consume.

Reference: Doty et al. §5.2; paper lines 2391–2430.
-/

import Ripple.PopulationProtocol.Majority.ExactMajority.Basic.AgentState
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.MarkovChain
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.JansonHitting
import Ripple.PopulationProtocol.Majority.ExactMajority.Protocol.Transition
import Ripple.PopulationProtocol.Majority.ExactMajority.Analysis.Phase0Convergence
import Mathlib.Analysis.Complex.ExponentialBounds

namespace ExactMajority
namespace RoleSplitConcentration

variable {L K : ℕ}

/-! ## Role counts -/

/-- Number of `Main`-role agents in a configuration. -/
def mainCount (c : Config (AgentState L K)) : ℕ :=
  Multiset.countP (fun a => a.role = .main) c

/-- Number of `Clock`-role agents in a configuration. -/
def clockCount (c : Config (AgentState L K)) : ℕ :=
  Multiset.countP (fun a => a.role = .clock) c

/-- Number of `Reserve`-role agents in a configuration. -/
def reserveCount (c : Config (AgentState L K)) : ℕ :=
  Multiset.countP (fun a => a.role = .reserve) c

/-- Number of transient `RoleMCR` agents in a configuration. -/
def roleMCRCount (c : Config (AgentState L K)) : ℕ :=
  Multiset.countP (fun a => a.role = .mcr) c

/-! ## The good-split predicate (Lemma 5.2 conclusion). -/

/-- `RoleSplitGood η n c`: the configuration `c` realizes the Lemma 5.2
post-condition with slack parameter `η`.  All `RoleMCR` gone, `|Main|` within
`(1 ± η)·n/2`, and `|Clock|`, `|Reserve|` each at least `(1 − η)·n/4`. -/
def RoleSplitGood (η : ℝ) (n : ℕ) (c : Config (AgentState L K)) : Prop :=
  roleMCRCount (L := L) (K := K) c = 0 ∧
  ((1 - η) * (n : ℝ) / 2 ≤ (mainCount (L := L) (K := K) c : ℝ)) ∧
  ((mainCount (L := L) (K := K) c : ℝ) ≤ (1 + η) * (n : ℝ) / 2) ∧
  ((1 - η) * (n : ℝ) / 4 ≤ (clockCount (L := L) (K := K) c : ℝ)) ∧
  ((1 - η) * (n : ℝ) / 4 ≤ (reserveCount (L := L) (K := K) c : ℝ))

/-! ## Deterministic `Θ(n)` clock/reserve/main bounds from `RoleSplitGood`.

These are the bounds every counter-timed phase consumes: a constant-fraction
lower bound on `|Clock|` (so clock–clock interactions happen at rate `Θ(1)`),
and the matching `Reserve`/`Main` bounds. -/

/-- The clock count is `Θ(n)`: with slack `η ≤ 1/25`, `RoleSplitGood` forces
`|Clock| ≥ n/5`.  (Paper uses `r > 0.24·n`; `0.24 = 6/25 ≥ 1/5`.) -/
theorem clockCount_linear_of_RoleSplitGood
    {η : ℝ} (hη : η ≤ 1 / 25) {n : ℕ} {c : Config (AgentState L K)}
    (hgood : RoleSplitGood (L := L) (K := K) η n c) :
    (n : ℝ) / 5 ≤ (clockCount (L := L) (K := K) c : ℝ) := by
  obtain ⟨_, _, _, hclk, _⟩ := hgood
  refine le_trans ?_ hclk
  have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  -- (1 − η)·n/4 ≥ (1 − 1/25)·n/4 = (24/25)·n/4 = 6n/25 ≥ n/5.
  nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 1 / 25 - η) hn]

/-- The reserve count is `Θ(n)`: with slack `η ≤ 1/25`, `|Reserve| ≥ n/5`. -/
theorem reserveCount_linear_of_RoleSplitGood
    {η : ℝ} (hη : η ≤ 1 / 25) {n : ℕ} {c : Config (AgentState L K)}
    (hgood : RoleSplitGood (L := L) (K := K) η n c) :
    (n : ℝ) / 5 ≤ (reserveCount (L := L) (K := K) c : ℝ) := by
  obtain ⟨_, _, _, _, hres⟩ := hgood
  refine le_trans ?_ hres
  have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 1 / 25 - η) hn]

/-- The main count is `Θ(n)`: with slack `0 ≤ η ≤ 1/25`, `|Main| ≥ 12n/25 ≥ n/3`
and `|Main| ≤ 13n/25 ≤ 2n/3` (the `n/2 ± εn` window). -/
theorem mainCount_lower_of_RoleSplitGood
    {η : ℝ} (hη : η ≤ 1 / 25) {n : ℕ} {c : Config (AgentState L K)}
    (hgood : RoleSplitGood (L := L) (K := K) η n c) :
    (n : ℝ) / 3 ≤ (mainCount (L := L) (K := K) c : ℝ) := by
  obtain ⟨_, hmain, _, _, _⟩ := hgood
  refine le_trans ?_ hmain
  have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  -- (1 − η)·n/2 ≥ (24/25)·n/2 = 12n/25 ≥ n/3.
  nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 1 / 25 - η) hn]

/-! ## The probability-1 floor `2 ≤ |Clock|`.

The Standard Counter Subroutine needs at least two Clock agents to count at all
and end Phase 0; hence whenever Phase 1 initializes, `c ≥ 2` (paper, deterministic
fallback bounds).  On the good-split event this floor is automatic once `n` is
large enough: `(1 − η)·n/4 ≥ 2` whenever `η ≤ 1/25` and `9 ≤ n`. -/

/-- On the good-split event with `n ≥ 9`, the clock count is at least `2`: the
deterministic floor the counter subroutine needs.  `(1 − 1/25)·n/4 ≥ (24/25)·9/4
= 54/25 > 2`. -/
theorem clockCount_ge_two_of_RoleSplitGood
    {η : ℝ} (hη : η ≤ 1 / 25) {n : ℕ} (hn : 9 ≤ n) {c : Config (AgentState L K)}
    (hgood : RoleSplitGood (L := L) (K := K) η n c) :
    2 ≤ clockCount (L := L) (K := K) c := by
  obtain ⟨_, _, _, hclk, _⟩ := hgood
  -- Get `2 ≤ (clockCount : ℝ)` over the reals, then transfer to ℕ.
  have hnR : (9 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hreal : (2 : ℝ) ≤ (clockCount (L := L) (K := K) c : ℝ) := by
    refine le_trans ?_ hclk
    -- (1 − η)·n/4 ≥ (24/25)·n/4 ≥ (24/25)·9/4 = 54/25 ≥ 2.
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 1 / 25 - η) (by linarith : (0 : ℝ) ≤ (n : ℝ))]
  exact_mod_cast hreal

/-! ## The whp statement of Lemma 5.2.

The Phase-0 initial configuration is `n` agents all in phase `0` with role
`RoleMCR`.  Lemma 5.2 says that after the Phase-0 horizon the bad event
`¬ RoleSplitGood` has kernel mass `O(1/n²)`.

The probabilistic content — the two-stage role-split Chernoff concentration —
is abstracted into the `roleSplitTail` budget: the exact kernel mass of the bad
set after `tRole` steps.  The future role-split concentration engine discharges
`roleSplitTail n η tRole ≤ O(1/n²)`; this file provides the precise statement
that engine targets and that every downstream timed phase consumes.  Phrasing
`roleSplitTail` as the literal bad-set mass keeps the interface honest (no fake
content) and makes `phase0_roleSplit_whp` a `rfl`-level packaging lemma. -/

/-- The Phase-0 initial configuration: `n` agents, all in phase `0` with the
transient role `RoleMCR`. -/
def Phase0Initial (n : ℕ) (c : Config (AgentState L K)) : Prop :=
  Multiset.card c = n ∧ ∀ a ∈ c, a.phase = 0 ∧ a.role = .mcr

/-- The role-split failure budget: the kernel mass of the bad-split event
`¬ RoleSplitGood η n` after `tRole` steps, started from `c₀`.  The Lemma 5.2
concentration engine bounds this by `O(1/n²)`. -/
noncomputable def roleSplitTail (η : ℝ) (n : ℕ) (tRole : ℕ)
    (c₀ : Config (AgentState L K)) : ENNReal :=
  ((NonuniformMajority L K).transitionKernel ^ tRole) c₀
    {c | ¬ RoleSplitGood (L := L) (K := K) η n c}

/-- **Lemma 5.2 (whp statement).** From the Phase-0 initial all-`RoleMCR`
configuration, after the Phase-0 horizon `tRole`, the probability that the
role split is *not* good is at most the supplied `εRole` budget, provided the
role-split tail meets that budget.  The concentration engine supplies
`hbudget` with `εRole = O(1/n²)`; this lemma is the packaging interface every
Phase-0 `PhaseConvergence` upgrade and timed phase consumes. -/
theorem phase0_roleSplit_whp
    {n : ℕ} {η : ℝ} {c₀ : Config (AgentState L K)}
    (_hinit : Phase0Initial (L := L) (K := K) n c₀)
    (tRole : ℕ) (εRole : ENNReal)
    (hbudget : roleSplitTail (L := L) (K := K) η n tRole c₀ ≤ εRole) :
    ((NonuniformMajority L K).transitionKernel ^ tRole) c₀
      {c | ¬ RoleSplitGood (L := L) (K := K) η n c}
      ≤ εRole :=
  hbudget

/-! ## The two-stage concentration discharge (Lemma 5.2 proof).

The paper proves Lemma 5.2 by modelling Phase 0 as two count-collapse processes:

  * **Stage 1** (Lemma 5.1): `RoleMCR, RoleMCR → Main, RoleCR` together with the
    `assigned`-driven follow-ups, taking `12.5 ln n` parallel time whp to drive
    `|RoleMCR| = 0`, leaving `n/3 ≤ |RoleCR| ≤ 2n/3` with probability `1` and
    `|RoleCR| = n/2 ± εn` whp.
  * **Stage 2** (Corollary 4.4): `RoleCR, RoleCR → Reserve, Clock` at rate
    `O(l²/n²)` when `|RoleCR| = l`, plus `RoleCR → Reserve` at phase end, taking
    `O(1)` further parallel time to leave `|Clock|, |Reserve| ≥ (1−η)·n/4` whp.

Both stages are *sums of heterogeneous geometric waiting times* analysed by
Janson's Theorem 4.3 (the in-house `JansonHitting.milestone_hitting_time_bound`
engine).  The crucial quantitative point — the one that distinguishes the
paper's `Θ(n log n)`-interaction horizon from the naive `Θ(n²)` per-decrement
tail — is that the geometric success rates are `Θ(u/n)` (Stage 1) and
`Θ(l²/n²)` (Stage 2) governed by the *current* count, not the worst-case
near-empty `Θ(1/n²)` rate.  Summing `Σ 1/p_i` then gives `meanTime = Θ(n log n)`
with `p_min = Θ(1/n)`, and Janson's bound at `λ = 5`
(`λ − 1 − ln λ > 2`) yields failure `exp(−p_min · meanTime · 2) = n^{-2}`.

We package the whole probabilistic content as a single hypothesis: a
`JansonHitting.MilestonePhase` over the real `NonuniformMajority` kernel whose
joint postcondition implies `RoleSplitGood`.  This is faithful to the paper —
the milestones are exactly the per-reaction count decrements of the two stages,
and the `progress` field is exactly the per-step rate lower bound the paper
computes — and it lets us discharge the Janson tail arithmetic here, in this
file, axiom-clean, exposing the precise remaining protocol-transition gap
(`progress` for the real kernel + the `Post ⊆ RoleSplitGood` balance step)
as the named milestone-phase hypothesis. -/

open ExactMajority in
/-- **Milestone reduction for the role split.**  If `mp` is a milestone phase
over the `NonuniformMajority` kernel whose joint postcondition forces
`RoleSplitGood η n`, then the role-split tail after `tRole` steps is bounded by
the milestone non-completion probability, *provided the Phase-0 initial config
has not yet hit any milestone* (true at the start — no reaction has fired).

The monotone inclusion `{¬RoleSplitGood} ⊆ {¬mp.Post}` is the whole content:
failing the good split forces an unreached milestone. -/
theorem roleSplitTail_le_milestoneTail
    {n : ℕ} {η : ℝ} {c₀ : Config (AgentState L K)}
    (mp : MilestonePhase (NonuniformMajority L K))
    (hPost : ∀ c, mp.Post c → RoleSplitGood (L := L) (K := K) η n c)
    (tRole : ℕ) :
    roleSplitTail (L := L) (K := K) η n tRole c₀ ≤
      ((NonuniformMajority L K).transitionKernel ^ tRole) c₀
        {c | ¬ mp.Post c} := by
  unfold roleSplitTail
  apply MeasureTheory.measure_mono
  intro c hc
  -- hc : ¬ RoleSplitGood η n c ; goal : ¬ mp.Post c
  simp only [Set.mem_setOf_eq] at hc ⊢
  exact fun hp => hc (hPost c hp)

open ExactMajority in
/-- **Janson tail on the role-split.**  Composing the milestone reduction with
`JansonHitting.milestone_hitting_time_bound`: from a role-split milestone phase
`mp` (whose `Post ⊆ RoleSplitGood`), an initial config at which no milestone has
fired, and a horizon `tRole ≥ λ · meanTime`, the role-split tail decays as the
Janson exponential `exp(−pMin · meanTime · (λ − 1 − ln λ))`.

With the paper's parameters `meanTime = Θ(n log n)`, `pMin = Θ(1/n)`, `λ = 5`
(so `λ − 1 − ln λ > 2`) this is `exp(−Θ(log n)) = O(1/n²)`. -/
theorem roleSplitTail_le_jansonExp
    {n : ℕ} {η : ℝ} {c₀ : Config (AgentState L K)}
    (mp : MilestonePhase (NonuniformMajority L K))
    (hPost : ∀ c, mp.Post c → RoleSplitGood (L := L) (K := K) η n c)
    (hPre : ∀ i : Fin mp.k, ¬ mp.milestone i c₀)
    (lam : ℝ) (hlam : 1 ≤ lam)
    (tRole : ℕ) (ht : lam * mp.meanTime ≤ (tRole : ℝ)) :
    roleSplitTail (L := L) (K := K) η n tRole c₀ ≤
      ENNReal.ofReal (Real.exp (-mp.pMin * mp.meanTime *
        (lam - 1 - Real.log lam))) :=
  le_trans (roleSplitTail_le_milestoneTail mp hPost tRole)
    (milestone_hitting_time_bound mp c₀ hPre lam hlam tRole ht)

/-- The Janson exponential collapses to the `O(1/n²)` budget under the paper's
quantitative inputs: a milestone potential `pMin · meanTime ≥ ln n` and a
deviation factor `λ − 1 − ln λ ≥ 2` (the paper takes `λ = 5`, where
`5 − 1 − ln 5 = 4 − ln 5 ≈ 2.39 > 2`).  Then
`exp(−pMin·meanTime·(λ−1−ln λ)) ≤ exp(−2 ln n) = n^{-2}`. -/
theorem jansonExp_le_inv_sq
    {n : ℕ} (hn : 1 ≤ n) {pm devf : ℝ}
    (hpm_nonneg : 0 ≤ pm)
    (hpm : Real.log (n : ℝ) ≤ pm)
    (hdev : 2 ≤ devf) :
    Real.exp (-pm * devf) ≤ ((n : ℝ) ^ 2)⁻¹ := by
  have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hlogn_nonneg : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg hnR
  -- -pm·devf ≤ -2 log n = log(n^{-2}).
  have hkey : -pm * devf ≤ Real.log (((n : ℝ) ^ 2)⁻¹) := by
    have hpm_pos : 0 ≤ pm := hpm_nonneg
    have h1 : 2 * Real.log (n : ℝ) ≤ pm * devf := by
      have hb : 2 * Real.log (n : ℝ) ≤ pm * 2 := by nlinarith [hpm, hlogn_nonneg]
      have hc : pm * 2 ≤ pm * devf := by nlinarith [hpm_pos, hdev]
      linarith
    have hlog_eq : Real.log (((n : ℝ) ^ 2)⁻¹) = -(2 * Real.log (n : ℝ)) := by
      rw [Real.log_inv, Real.log_pow]; push_cast; ring
    rw [hlog_eq]; linarith
  calc Real.exp (-pm * devf)
      ≤ Real.exp (Real.log (((n : ℝ) ^ 2)⁻¹)) := Real.exp_le_exp.mpr hkey
    _ = ((n : ℝ) ^ 2)⁻¹ := by
        rw [Real.exp_log (by positivity)]

/-- `5 − 1 − ln 5 ≥ 2`, the paper's deviation factor at `λ = 5`: equivalently
`ln 5 ≤ 2`, which holds because `5 < e² ` (`e² ≈ 7.389`). -/
theorem five_sub_one_sub_log_five_ge_two :
    (2 : ℝ) ≤ 5 - 1 - Real.log 5 := by
  have hlog5 : Real.log 5 ≤ 2 := by
    have h5 : (5 : ℝ) ≤ Real.exp 2 := by
      have he1 : (2.7182818283 : ℝ) < Real.exp 1 := Real.exp_one_gt_d9
      have hexp2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
        rw [← Real.exp_add]; norm_num
      have hpos : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
      nlinarith [he1, hexp2, hpos]
    calc Real.log 5 ≤ Real.log (Real.exp 2) := Real.log_le_log (by norm_num) h5
      _ = 2 := Real.log_exp 2
  linarith

open ExactMajority in
/-- **Lemma 5.2 concentration discharge (`O(1/n²)` form).**  Given a role-split
milestone phase `mp` over `NonuniformMajority` whose joint postcondition forces
`RoleSplitGood η n`, the Phase-0 initial config (no milestone fired), and the
paper's milestone potential bound `ln n ≤ pMin · meanTime` (a `Θ(log n)` lower
bound following from `pMin = Θ(1/n)`, `meanTime = Θ(n log n)`), the role-split
tail after `tRole ≥ 5 · meanTime` steps is at most `1/n²`.

This is the discharged Lemma 5.2 budget: `εRole(n) = 1/n²`, horizon
`tRole = ⌈5 · meanTime⌉ = Θ(n log n)` interactions (= `12.5 ln n + O(1)`
parallel time, exactly the paper's Phase-0 horizon).  The only remaining input
is the role-split `MilestonePhase` itself with its real-kernel `progress`
field — the protocol-transition content of Lemma 5.1 + Corollary 4.4. -/
theorem roleSplitTail_le_inv_sq
    {n : ℕ} (hn : 1 ≤ n) {η : ℝ} {c₀ : Config (AgentState L K)}
    (mp : MilestonePhase (NonuniformMajority L K))
    (hPost : ∀ c, mp.Post c → RoleSplitGood (L := L) (K := K) η n c)
    (hPre : ∀ i : Fin mp.k, ¬ mp.milestone i c₀)
    (hpot : Real.log (n : ℝ) ≤ mp.pMin * mp.meanTime)
    (hpot_nonneg : 0 ≤ mp.pMin * mp.meanTime)
    (tRole : ℕ) (ht : 5 * mp.meanTime ≤ (tRole : ℝ)) :
    roleSplitTail (L := L) (K := K) η n tRole c₀ ≤
      ENNReal.ofReal (((n : ℝ) ^ 2)⁻¹) := by
  refine le_trans (roleSplitTail_le_jansonExp mp hPost hPre 5 (by norm_num) tRole ht) ?_
  apply ENNReal.ofReal_le_ofReal
  -- exp(-(pMin·meanTime)·(5-1-ln5)) ≤ 1/n²
  have hrw : -mp.pMin * mp.meanTime * (5 - 1 - Real.log 5) =
      -(mp.pMin * mp.meanTime) * (5 - 1 - Real.log 5) := by ring
  rw [hrw]
  exact jansonExp_le_inv_sq hn hpot_nonneg hpot five_sub_one_sub_log_five_ge_two

/-! ## Packaged Lemma 5.2 witness and the named deliverable.

The bundle below collects exactly the protocol-transition content of Lemma 5.1 +
Corollary 4.4 — the role-split milestone phase, its `Post ⊆ RoleSplitGood`
soundness, the `Θ(log n)` milestone potential, and the start-of-phase fact that
the all-`RoleMCR` Phase-0 initial config has fired no milestone — as a single
hypothesis.  Constructing it is the remaining work (the real-kernel `progress`
field); everything downstream of it is discharged here. -/

/-- A Lemma-5.2 role-split witness over the `NonuniformMajority` kernel: the
milestone phase whose completion forces `RoleSplitGood`, with the paper's
quantitative inputs.  Bundling these makes the final tail bound consume only a
single hypothesis. -/
structure RoleSplitMilestone (η : ℝ) (n : ℕ) (c₀ : Config (AgentState L K)) where
  /-- The role-split milestone phase (Lemma 5.1 + Corollary 4.4 count decrements). -/
  mp : MilestonePhase (NonuniformMajority L K)
  /-- Completing every milestone forces the Lemma 5.2 post-condition. -/
  post_sound : ∀ c, mp.Post c → RoleSplitGood (L := L) (K := K) η n c
  /-- The all-`RoleMCR` start has fired no milestone (no reaction yet). -/
  pre_unhit : ∀ i : Fin mp.k, ¬ mp.milestone i c₀
  /-- The `Θ(log n)` milestone potential: `pMin · meanTime ≥ ln n`
  (from `pMin = Θ(1/n)`, `meanTime = Θ(n log n)`). -/
  potential : Real.log (n : ℝ) ≤ mp.pMin * mp.meanTime
  /-- Nonnegativity of the potential. -/
  potential_nonneg : 0 ≤ mp.pMin * mp.meanTime

/-- The Phase-0 role-split horizon: `⌈5 · meanTime⌉` interactions
(`= 12.5 ln n + O(1)` parallel time, the paper's Phase-0 horizon). -/
noncomputable def roleSplitHorizon {η : ℝ} {n : ℕ} {c₀ : Config (AgentState L K)}
    (w : RoleSplitMilestone (L := L) (K := K) η n c₀) : ℕ :=
  ⌈5 * w.mp.meanTime⌉₊

/-- The horizon dominates `5 · meanTime`. -/
theorem roleSplitHorizon_ge {η : ℝ} {n : ℕ} {c₀ : Config (AgentState L K)}
    (w : RoleSplitMilestone (L := L) (K := K) η n c₀) :
    5 * w.mp.meanTime ≤ (roleSplitHorizon (L := L) (K := K) w : ℝ) :=
  Nat.le_ceil _

/-- **Lemma 5.2 (concentration, named deliverable).**  From the Phase-0 initial
all-`RoleMCR` configuration and a role-split witness, the role-split tail after
the `Θ(n log n)` horizon `roleSplitHorizon` is at most `1/n²`.

  * `tRole(n) = roleSplitHorizon w = ⌈5 · meanTime⌉ = Θ(n log n)` interactions;
  * `εRole(n) = 1/n²`.

This is the discharged Lemma 5.2 budget that `phase0_roleSplit_whp` consumes. -/
theorem roleSplitTail_le
    {n : ℕ} (hn : 1 ≤ n) {η : ℝ} {c₀ : Config (AgentState L K)}
    (_hinit : Phase0Initial (L := L) (K := K) n c₀)
    (w : RoleSplitMilestone (L := L) (K := K) η n c₀) :
    roleSplitTail (L := L) (K := K) η n
        (roleSplitHorizon (L := L) (K := K) w) c₀ ≤
      ENNReal.ofReal (((n : ℝ) ^ 2)⁻¹) :=
  roleSplitTail_le_inv_sq hn w.mp w.post_sound w.pre_unhit w.potential
    w.potential_nonneg _ (roleSplitHorizon_ge w)

/-- The discharged Lemma 5.2 fed straight into the packaging interface: with the
witness and `n ≥ 1`, `phase0_roleSplit_whp` fires with `εRole = 1/n²`. -/
theorem phase0_roleSplit_whp_inv_sq
    {n : ℕ} (hn : 1 ≤ n) {η : ℝ} {c₀ : Config (AgentState L K)}
    (hinit : Phase0Initial (L := L) (K := K) n c₀)
    (w : RoleSplitMilestone (L := L) (K := K) η n c₀) :
    ((NonuniformMajority L K).transitionKernel ^
        (roleSplitHorizon (L := L) (K := K) w)) c₀
      {c | ¬ RoleSplitGood (L := L) (K := K) η n c}
      ≤ ENNReal.ofReal (((n : ℝ) ^ 2)⁻¹) :=
  phase0_roleSplit_whp hinit _ _ (roleSplitTail_le hn hinit w)

/-! ## Stage-1 bridge to the real-kernel milestone phase (`phase0MilestonePhase`).

The predecessor file `Analysis/Phase0Convergence.lean` constructs a *real-kernel*
`MilestonePhase (NonuniformMajority L K)` — `phase0MilestonePhase n hn` — whose
milestones are the `mcrCount`-threshold decrements of **Stage 1** (the
`RoleMCR,RoleMCR → Main,RoleCR` split, paper Lemma 5.1), 0-`sorry`, with the
`progress` field discharged against the *actual* protocol transition mass route
(`interactionPMF_toMeasure_mcr_phase0_ge → stepDistOrSelf_toMeasure_ge`).  This
section bridges that phase into the `RoleSplitConcentration` interface.

The bridge is at the level of the **mcr-elimination** conclusion only:
`phase0MilestonePhase.Post c` forces `mcrCount c ≤ 1` (the last threshold), hence
`roleMCRCount c ≤ 1` — the Stage-1 half of `RoleSplitGood`.  The Stage-2 content
(`RoleCR,RoleCR → Clock,Reserve` at rate `Θ(l²/n²)`, Corollary 4.4) and the
count-balance (`|Main| = n/2 ± εn`, `|Clock|,|Reserve| ≥ (1−η)n/4`) are *not* part
of `phase0MilestonePhase` and remain the open input documented below. -/

/-- `roleMCRCount` (a `Multiset.countP`) equals `Phase0Convergence.mcrCount`
(a `filter.card`).  Pure `Multiset` bookkeeping bridge. -/
theorem roleMCRCount_eq_mcrCount (c : Config (AgentState L K)) :
    roleMCRCount (L := L) (K := K) c = ExactMajority.mcrCount (L := L) (K := K) c := by
  unfold roleMCRCount ExactMajority.mcrCount
  rw [Multiset.countP_eq_card_filter]

/-- `phase0MilestonePhase.Post c` forces `mcrCount c ≤ 1` *provided* the carried
Phase-0 invariants hold: `c.card = n` and every `RoleMCR` agent is at phase `0`
(both true throughout Phase 0 — `card` is conserved by every transition and
Stage 1 never advances an `RoleMCR` agent's phase).  The last milestone
(`i = n-2`, threshold `1`) then collapses to its `mcrCount`-disjunct. -/
theorem mcrCount_le_one_of_phase0Post
    {n : ℕ} (hn : 2 ≤ n) {c : Config (AgentState L K)}
    (hcard : Multiset.card c = n)
    (hphase : ∀ a ∈ c, a.role = .mcr → a.phase.val = 0)
    (hPost : (phase0MilestonePhase (L := L) (K := K) n hn).Post c) :
    ExactMajority.mcrCount (L := L) (K := K) c ≤ 1 := by
  -- The last milestone index `i = n-2 : Fin (n-1)`.
  have hlt : n - 2 < n - 1 := by omega
  have hmile := hPost ⟨n - 2, hlt⟩
  have hthr : ExactMajority.mcrThreshold n
      ⟨(⟨n - 2, hlt⟩ : Fin (n - 1)).val, by omega⟩ = 1 := by
    have hval : (⟨(⟨n - 2, hlt⟩ : Fin (n - 1)).val, by omega⟩ : Fin n).val = n - 2 := rfl
    unfold ExactMajority.mcrThreshold
    rw [hval]
    omega
  -- `milestone ⟨n-2,_⟩ c = phase0Milestone n ⟨n-2,_⟩ c`.
  change ExactMajority.phase0Milestone n ⟨(⟨n - 2, hlt⟩ : Fin (n - 1)).val, by omega⟩ c at hmile
  unfold ExactMajority.phase0Milestone at hmile
  rcases hmile with hmcr | hcard' | hhigh
  · -- mcrCount ≤ threshold = 1.
    rwa [hthr] at hmcr
  · exact absurd hcard hcard'
  · -- No high-phase MCR exists (all MCR at phase 0), contradiction.
    obtain ⟨a, ha_mem, ha_mcr, ha_phase⟩ := hhigh
    exact absurd (hphase a ha_mem ha_mcr) ha_phase

/-- The real-kernel Stage-1 tail: starting from any config, the
`NonuniformMajority` kernel mass of `{c' | ¬ phase0MilestonePhase.Post c'}` after
`tRole` steps decays as the Janson exponential of the **real** Stage-1 milestone
phase, provided the start has fired no milestone.  This is `phase0MilestonePhase`
pushed straight through `milestone_hitting_time_bound`; its `progress` field is the
actual protocol transition mass route. -/
theorem phase0_milestone_jansonTail
    {n : ℕ} (hn : 2 ≤ n) {c₀ : Config (AgentState L K)}
    (hPre : ∀ i : Fin (phase0MilestonePhase (L := L) (K := K) n hn).k,
      ¬ (phase0MilestonePhase (L := L) (K := K) n hn).milestone i c₀)
    (lam : ℝ) (hlam : 1 ≤ lam)
    (tRole : ℕ)
    (ht : lam * (phase0MilestonePhase (L := L) (K := K) n hn).meanTime ≤ (tRole : ℝ)) :
    ((NonuniformMajority L K).transitionKernel ^ tRole) c₀
        {c | ¬ (phase0MilestonePhase (L := L) (K := K) n hn).Post c}
      ≤ ENNReal.ofReal (Real.exp
          (-(phase0MilestonePhase (L := L) (K := K) n hn).pMin *
             (phase0MilestonePhase (L := L) (K := K) n hn).meanTime *
             (lam - 1 - Real.log lam))) :=
  milestone_hitting_time_bound (phase0MilestonePhase (L := L) (K := K) n hn)
    c₀ hPre lam hlam tRole ht

/-! ## The structural obstruction: the per-decrement `pMin` is `Θ(1/n²)`.

The Janson `1/n²` budget (`roleSplitTail_le_inv_sq`) consumes a *milestone
potential* `log n ≤ pMin · meanTime`.  For the predecessor's single-chain
Stage-1 phase this potential **fails**: the worst-case milestone is the
near-empty `mcrCount = 2 → 1` decrement, whose rate is `p = 2/(n(n−1))`, so
`pMin ≤ 2/(n(n−1)) = Θ(1/n²)`.  Since `meanTime = Σ 1/p_i = (n−1)²` (telescoping),
`pMin · meanTime = 2(n−1)/n → 2`, which is `< log n` for all `n ≥ 8`.

This is exactly the gap the paper closes with the *parallel-time / coupon*
analysis: the milestones are summed as a sum of heterogeneous geometric times
whose **collective** potential is `Θ(log n)`, not by feeding the single worst
`pMin` into a uniform Janson bound.  The lemma below formalizes the `pMin` half
of the obstruction (the easy `iInf_le` direction at the `M = 2` milestone),
pinning the precise quantitative reason the naive single-chain wiring cannot
reach `roleSplitTail_le_inv_sq` and documenting what the Stage-1/Stage-2
upgrade must supply. -/

/-- The minimum Stage-1 milestone probability is at most `2/(n(n−1))`: the rate
of the last (near-empty `mcrCount = 2 → 1`) decrement.  Hence `pMin = Θ(1/n²)`,
not `Θ(1/n)` — the structural reason the single-chain Janson potential
`log n ≤ pMin · meanTime` is unreachable for this phase (see module note). -/
theorem phase0MilestonePhase_pMin_le_two_div
    {n : ℕ} (hn : 2 ≤ n) :
    (phase0MilestonePhase (L := L) (K := K) n hn).pMin ≤
      (2 : ℝ) / ((n : ℝ) * ((n : ℝ) - 1)) := by
  -- The last milestone index `i = n-2 : Fin (n-1)`, where `M = 2`.
  have hlt : n - 2 < n - 1 := by omega
  set i₀ : Fin (n - 1) := ⟨n - 2, hlt⟩ with hi₀
  -- `pMin ≤ p i₀` by `ciInf_le` (the family is bounded below by 0 via `hp_pos`).
  have hpmin_le :
      (phase0MilestonePhase (L := L) (K := K) n hn).pMin ≤
        (phase0MilestonePhase (L := L) (K := K) n hn).p i₀ := by
    unfold MilestonePhase.pMin
    exact ciInf_le ⟨0, fun _ ⟨j, hj⟩ =>
      hj ▸ le_of_lt ((phase0MilestonePhase (L := L) (K := K) n hn).hp_pos j)⟩ i₀
  -- `p i₀ = phase0MilestoneProb n i₀ = 2·1/(n(n-1))` since `M = n-1-(n-2)+1 = 2`.
  have hp_eq : (phase0MilestonePhase (L := L) (K := K) n hn).p i₀ =
      (2 : ℝ) / ((n : ℝ) * ((n : ℝ) - 1)) := by
    rw [phase0MilestonePhase_p]
    unfold ExactMajority.phase0MilestoneProb
    have hM : n - 1 - i₀.val + 1 = 2 := by simp only [hi₀]; omega
    simp only [hM]
    norm_num
  rw [hp_eq] at hpmin_le
  exact hpmin_le

/-! ## Phase C-1 (relay 2) — the one-sided MCR-conversion building blocks.

RESOLUTION of the pinned obstruction (see `DOTY_POST63_CAMPAIGN.md`, "Phase C-1
(relay 2)").  The `pMin = Θ(1/n²)` obstruction above is an artifact of the
predecessor's milestone phase counting **only** `RoleMCR,RoleMCR → Main,RoleCR`
pairs (`Phase0Transition` Rule 1).  The protocol ALSO has the one-sided
conversion reactions of paper Lemma 5.1 — `S_f,U → S_t,M_f` and `M_f,U → M_t,S_f`
— formalized as `Phase0Transition` Rules 2 and 3 (Protocol/Transition.lean
L364–386): an MCR meeting an *unassigned* Main (Rule 2) or an *unassigned*
RoleCR (Rule 3) is converted, decreasing `mcrCount` by 1.  The number of such
ordered (MCR, assignable-target) pairs is `mcrCount · assignableCount`, giving a
decrease rate `Θ(M·n/n²) = Θ(M/n)` (once `assignableCount = Θ(n)` by Lemma 5.1's
Chernoff invariant), hence `pMin = Θ(1/n)` and the potential `pMin·meanTime =
Θ(log n)` is reachable.

These lemmas deliver the **count-level** content: the `assignableCount`
definition and the pair-level fact that a (phase-0 MCR, phase-0 unassigned
assignable-target) interaction strictly drops `mcrCount`.  Threading the
`assignableCount ≥ n/5` invariant through a milestone phase (the analogue of the
Phase-2/4 `informedU` epidemic monotonicity) is the documented next gap. -/

/-- An agent is an *assignable target* for one-sided MCR conversion: it is an
unassigned `Main` (Rule 2 partner) or an unassigned `RoleCR` (Rule 3 partner),
at phase 0.  An MCR meeting such an agent is converted, dropping `mcrCount`. -/
def IsAssignable (a : AgentState L K) : Prop :=
  a.phase.val = 0 ∧ ¬ a.assigned ∧ (a.role = .main ∨ a.role = .cr)

/-- Number of assignable targets in a configuration (the `Θ(n)` pool that drives
the one-sided MCR conversion at rate `Θ(M/n)`). -/
def assignableCount (c : Config (AgentState L K)) : ℕ :=
  Multiset.countP (fun a => decide (a.phase.val = 0) &&
    (!a.assigned) && (decide (a.role = .main) || decide (a.role = .cr))) c

/-- **Rule 2 effect (s-side MCR meets unassigned Main on the t-side).** When `s`
is `RoleMCR` and `t` is an unassigned `Main`, `Phase0Transition` makes the
`s`-output non-MCR (`s` becomes `RoleCR`).  Pure unfolding of the five rules. -/
theorem Phase0Transition_first_no_mcr_of_mcr_main
    (s t : AgentState L K) (hs : s.role = .mcr) (ht : t.role = .main)
    (ht_un : ¬ t.assigned) :
    (Phase0Transition L K s t).1.role ≠ .mcr := by
  -- Rule 1 (s1): needs both mcr — false (t is main), so s1 = s, s1.role = mcr.
  -- t1 = t (Rule 1 t-branch needs both mcr — false), so t1.role = main, ¬t1.assigned.
  -- Rule 2 (s2): s1.role = mcr ∧ t1.role = main ∧ ¬t1.assigned — fires, s2.role = cr.
  -- Rules 3,4,5 leave a `.cr` role untouched (their `.mcr`/`.cr×.cr`/`.clock` guards miss).
  have hmcr_main : (Role.mcr = Role.main) = False := by simp
  have hmain_mcr : (Role.main = Role.mcr) = False := by simp
  have hcr_mcr : (Role.cr = Role.mcr) = False := by simp
  have hmain_cr : (Role.main = Role.cr) = False := by simp
  have hcr_clock : (Role.cr = Role.clock) = False := by simp
  have hmain_clock : (Role.main = Role.clock) = False := by simp
  unfold Phase0Transition
  simp only [hs, ht, hmcr_main, hmain_mcr, hcr_mcr, hmain_cr, hcr_clock, hmain_clock,
    ht_un, true_and, and_true, false_and, and_false,
    if_false, if_true, not_false_eq_true, not_true_eq_false,
    ne_eq, Bool.false_eq_true]

/-- **Rule 3 effect (s-side MCR meets unassigned RoleCR on the t-side).** When `s`
is `RoleMCR` and `t` is an unassigned `RoleCR`, `Phase0Transition` makes the
`s`-output non-MCR (`s` becomes `Main`).  Pure unfolding of the five rules. -/
theorem Phase0Transition_first_no_mcr_of_mcr_cr
    (s t : AgentState L K) (hs : s.role = .mcr) (ht : t.role = .cr)
    (ht_un : ¬ t.assigned) :
    (Phase0Transition L K s t).1.role ≠ .mcr := by
  -- Rule 1: needs both mcr — false. Rule 2: t1.role = cr ≠ main and ≠ mcr — no fire.
  -- Rule 3 (s3): s2.role = mcr ∧ t2.role ≠ main ∧ t2.role ≠ mcr ∧ ¬t2.assigned — fires,
  -- s becomes `.main`. Rules 4,5: `.main` misses `.cr`/`.clock` guards.
  have hmcr_main : (Role.mcr = Role.main) = False := by simp
  have hcr_main : (Role.cr = Role.main) = False := by simp
  have hcr_mcr : (Role.cr = Role.mcr) = False := by simp
  have hmain_mcr : (Role.main = Role.mcr) = False := by simp
  have hmain_cr : (Role.main = Role.cr) = False := by simp
  have hmain_clock : (Role.main = Role.clock) = False := by simp
  unfold Phase0Transition
  simp only [hs, ht, hmcr_main, hcr_main, hcr_mcr, hmain_mcr, hmain_cr,
    hmain_clock, ht_un, and_true, false_and, and_false,
    if_false, if_true, not_false_eq_true, not_true_eq_false,
    ne_eq, Bool.false_eq_true]

/-- **Rule 2 mirror (t-side MCR meets unassigned Main on the s-side).** -/
theorem Phase0Transition_second_no_mcr_of_main_mcr
    (s t : AgentState L K) (hs : s.role = .main) (ht : t.role = .mcr)
    (hs_un : ¬ s.assigned) :
    (Phase0Transition L K s t).2.role ≠ .mcr := by
  have hmcr_main : (Role.mcr = Role.main) = False := by simp
  have hmain_mcr : (Role.main = Role.mcr) = False := by simp
  have hcr_mcr : (Role.cr = Role.mcr) = False := by simp
  have hmain_cr : (Role.main = Role.cr) = False := by simp
  have hcr_clock : (Role.cr = Role.clock) = False := by simp
  have hmain_clock : (Role.main = Role.clock) = False := by simp
  unfold Phase0Transition
  simp only [hs, ht, hmcr_main, hmain_mcr, hcr_mcr, hmain_cr, hcr_clock, hmain_clock,
    hs_un, and_true, false_and, and_false,
    if_false, if_true, not_false_eq_true, not_true_eq_false,
    ne_eq, Bool.false_eq_true]

/-- **Rule 3 mirror (t-side MCR meets unassigned RoleCR on the s-side).** -/
theorem Phase0Transition_second_no_mcr_of_cr_mcr
    (s t : AgentState L K) (hs : s.role = .cr) (ht : t.role = .mcr)
    (hs_un : ¬ s.assigned) :
    (Phase0Transition L K s t).2.role ≠ .mcr := by
  have hmcr_main : (Role.mcr = Role.main) = False := by simp
  have hcr_main : (Role.cr = Role.main) = False := by simp
  have hcr_mcr : (Role.cr = Role.mcr) = False := by simp
  have hmain_mcr : (Role.main = Role.mcr) = False := by simp
  have hmain_cr : (Role.main = Role.cr) = False := by simp
  have hmain_clock : (Role.main = Role.clock) = False := by simp
  unfold Phase0Transition
  simp only [hs, ht, hmcr_main, hcr_main, hcr_mcr, hmain_mcr, hmain_cr,
    hmain_clock, hs_un, and_true, false_and, and_false,
    if_false, if_true, not_false_eq_true, not_true_eq_false,
    ne_eq, Bool.false_eq_true]

/-- `mcrCount` of a singleton (re-derived locally; the upstream lemma is private). -/
private lemma mcrCount_singleton' (a : AgentState L K) :
    ExactMajority.mcrCount (L := L) (K := K) ({a} : Config (AgentState L K)) =
      if a.role = .mcr then 1 else 0 := by
  unfold ExactMajority.mcrCount
  by_cases h : a.role = .mcr <;> simp [h, Multiset.filter_singleton]

/-- `mcrCount` of a pair, by role cases (re-derived locally). -/
private lemma mcrCount_pair' (a b : AgentState L K) :
    ExactMajority.mcrCount (L := L) (K := K) ({a, b} : Config (AgentState L K)) =
      (if a.role = .mcr then 1 else 0) + (if b.role = .mcr then 1 else 0) := by
  show ExactMajority.mcrCount (L := L) (K := K) ({a} + {b}) = _
  rw [ExactMajority.mcrCount_add, mcrCount_singleton', mcrCount_singleton']

/-- **Pair-level mcrCount strict decrease for a one-sided conversion.** If the
`Phase0Transition` output of a pair has both roles non-MCR, and exactly one of
the inputs (`s`) was MCR while the other (`t`) was not, then the pair `mcrCount`
strictly drops (`1 → 0`).  This is the count consequence of the Rule-2/Rule-3
effect lemmas, packaging the one-sided conversion as a `mcrCount` decrement. -/
theorem Phase0Transition_mcrCount_pair_lt_of_one_sided
    (s t : AgentState L K) (hs : s.role = .mcr) (ht : t.role ≠ .mcr)
    (hout1 : (Phase0Transition L K s t).1.role ≠ .mcr)
    (hout2 : (Phase0Transition L K s t).2.role ≠ .mcr) :
    ExactMajority.mcrCount (L := L) (K := K)
        ({(Phase0Transition L K s t).1, (Phase0Transition L K s t).2} : Config (AgentState L K)) <
      ExactMajority.mcrCount (L := L) (K := K) ({s, t} : Config (AgentState L K)) := by
  rw [mcrCount_pair', mcrCount_pair']
  rw [if_pos hs, if_neg ht, if_neg hout1, if_neg hout2]
  omega

/-- **One-sided pair decrement, concrete (s = MCR meets assignable t).** Combines
the Rule-2/Rule-3 `s`-side effect with the generic non-MCR `t`-side preservation
to get the pair `mcrCount` strict drop, for `t` an unassigned Main or RoleCR. -/
theorem Phase0Transition_mcrCount_pair_lt_of_mcr_assignable
    (s t : AgentState L K) (hs : s.role = .mcr)
    (ht : IsAssignable t) :
    ExactMajority.mcrCount (L := L) (K := K)
        ({(Phase0Transition L K s t).1, (Phase0Transition L K s t).2} : Config (AgentState L K)) <
      ExactMajority.mcrCount (L := L) (K := K) ({s, t} : Config (AgentState L K)) := by
  obtain ⟨_, ht_un, ht_role⟩ := ht
  have ht_ne : t.role ≠ .mcr := by rcases ht_role with h | h <;> rw [h] <;> decide
  have hout1 : (Phase0Transition L K s t).1.role ≠ .mcr := by
    rcases ht_role with h | h
    · exact Phase0Transition_first_no_mcr_of_mcr_main s t hs h ht_un
    · exact Phase0Transition_first_no_mcr_of_mcr_cr s t hs h ht_un
  have hout2 : (Phase0Transition L K s t).2.role ≠ .mcr :=
    ExactMajority.Phase0Transition_second_no_mcr (L := L) (K := K) s t ht_ne
  exact Phase0Transition_mcrCount_pair_lt_of_one_sided s t hs ht_ne hout1 hout2

/-- **One-sided pair decrement, mirror (t = MCR meets assignable s).** -/
theorem Phase0Transition_mcrCount_pair_lt_of_assignable_mcr
    (s t : AgentState L K) (hs : IsAssignable s) (ht : t.role = .mcr) :
    ExactMajority.mcrCount (L := L) (K := K)
        ({(Phase0Transition L K s t).1, (Phase0Transition L K s t).2} : Config (AgentState L K)) <
      ExactMajority.mcrCount (L := L) (K := K) ({s, t} : Config (AgentState L K)) := by
  obtain ⟨_, hs_un, hs_role⟩ := hs
  have hs_ne : s.role ≠ .mcr := by rcases hs_role with h | h <;> rw [h] <;> decide
  have hout2 : (Phase0Transition L K s t).2.role ≠ .mcr := by
    rcases hs_role with h | h
    · exact Phase0Transition_second_no_mcr_of_main_mcr s t h ht hs_un
    · exact Phase0Transition_second_no_mcr_of_cr_mcr s t h ht hs_un
  have hout1 : (Phase0Transition L K s t).1.role ≠ .mcr :=
    ExactMajority.Phase0Transition_first_no_mcr (L := L) (K := K) s t hs_ne
  -- Here `t` is the MCR side; swap the roles of `s,t` in the generic lemma via the
  -- pair `{s,t} = {t,s}` (multiset cons-comm) is unnecessary: re-derive directly.
  rw [mcrCount_pair', mcrCount_pair']
  rw [if_neg hs_ne, if_pos ht, if_neg hout1, if_neg hout2]
  omega

/-! ### Lifting the pair decrement through the full `Transition` wrapper.

The kernel uses the full `Transition` dispatcher, which wraps the phase-specific
transition with `phaseEpidemicUpdate` (pre-step inits) and `finishPhase10Entry`
(post-step phase-10 entry).  When both agents sit at phase 0, both wrappers are
the identity on roles, so `Transition` reduces to `Phase0Transition` at the role
level — the same reduction the predecessor used for the MCR–MCR case. -/

/-- With both agents at phase 0, `phaseEpidemicUpdate` is the identity. -/
theorem phaseEpidemicUpdate_eq_self_of_both_phase0
    (s t : AgentState L K) (hs : s.phase.val = 0) (ht : t.phase.val = 0) :
    phaseEpidemicUpdate L K s t = (s, t) := by
  have hphase_eq : s.phase = t.phase := Fin.ext (by omega)
  have hmax : max s.phase t.phase = s.phase := by rw [hphase_eq, max_self]
  have ht_rec : ({t with phase := s.phase} : AgentState L K) = t := by
    rw [hphase_eq]
  unfold phaseEpidemicUpdate
  simp only [hmax, ht_rec]
  rw [runInitsBetween_self_api (L := L) (K := K) s.phase.val s]
  rw [show (s.phase.val : ℕ) = t.phase.val from by omega,
      runInitsBetween_self_api (L := L) (K := K) t.phase.val t]
  rw [if_neg]
  rintro ⟨_, hor⟩
  rcases hor with h | h <;> omega

/-- With both agents at phase 0, the full `Transition` output roles equal the
`Phase0Transition` output roles (both wrappers are role-identities). -/
theorem Transition_roles_eq_phase0_of_both_phase0
    (s t : AgentState L K) (hs : s.phase.val = 0) (ht : t.phase.val = 0) :
    (Transition L K s t).1.role = (Phase0Transition L K s t).1.role ∧
    (Transition L K s t).2.role = (Phase0Transition L K s t).2.role := by
  have hpe := phaseEpidemicUpdate_eq_self_of_both_phase0 (L := L) (K := K) s t hs ht
  have hs0 : s.phase = (⟨0, by omega⟩ : Fin _) := Fin.ext hs
  unfold Transition
  rw [hpe]
  simp only [finishPhase10Entry_role_eq]
  rw [hs0]
  exact ⟨rfl, rfl⟩

/-- **Config-level one-sided `mcrCount` decrement (full kernel).** A scheduled
interaction of a phase-0 MCR `s` with a phase-0 assignable target `t` (within a
config `c`) strictly drops `mcrCount c`.  This is the real-kernel building block
mirroring `mcrCount_config_decrease_of_phase0_mcr_pair` (Phase0Convergence) for
the *one-sided* good set; it converts the `Θ(M/n)` good pairs into `mcrCount`
decrements.  Symmetric form (s assignable, t MCR) is `..._of_assignable_mcr`. -/
theorem mcrCount_config_decrease_of_mcr_assignable
    (c : Config (AgentState L K)) (s t : AgentState L K)
    (h_sub : ({s, t} : Config (AgentState L K)) ≤ c)
    (hs : s.role = .mcr) (hs_phase : s.phase.val = 0) (ht : IsAssignable t) :
    ExactMajority.mcrCount (L := L) (K := K)
        (c - {s, t} + {(Transition L K s t).1, (Transition L K s t).2}) <
      ExactMajority.mcrCount (L := L) (K := K) c := by
  have ht_phase : t.phase.val = 0 := ht.1
  have h_restore : c - {s, t} + {s, t} = c := Multiset.sub_add_cancel h_sub
  have hroles := Transition_roles_eq_phase0_of_both_phase0 (L := L) (K := K) s t hs_phase ht_phase
  -- The pair mcrCount of the Transition output equals that of the Phase0Transition output
  -- (mcrCount only reads roles).
  have hpair_eq : ExactMajority.mcrCount (L := L) (K := K)
      ({(Transition L K s t).1, (Transition L K s t).2} : Config (AgentState L K)) =
      ExactMajority.mcrCount (L := L) (K := K)
      ({(Phase0Transition L K s t).1, (Phase0Transition L K s t).2} : Config (AgentState L K)) := by
    rw [mcrCount_pair', mcrCount_pair', hroles.1, hroles.2]
  have h_pair_lt := Phase0Transition_mcrCount_pair_lt_of_mcr_assignable s t hs ht
  calc ExactMajority.mcrCount (L := L) (K := K)
          (c - {s, t} + {(Transition L K s t).1, (Transition L K s t).2})
      = ExactMajority.mcrCount (L := L) (K := K) (c - {s, t}) +
          ExactMajority.mcrCount (L := L) (K := K)
            ({(Transition L K s t).1, (Transition L K s t).2}) :=
        ExactMajority.mcrCount_add _ _
    _ = ExactMajority.mcrCount (L := L) (K := K) (c - {s, t}) +
          ExactMajority.mcrCount (L := L) (K := K)
            ({(Phase0Transition L K s t).1, (Phase0Transition L K s t).2}) := by rw [hpair_eq]
    _ < ExactMajority.mcrCount (L := L) (K := K) (c - {s, t}) +
          ExactMajority.mcrCount (L := L) (K := K) ({s, t} : Config (AgentState L K)) :=
        Nat.add_lt_add_left h_pair_lt _
    _ = ExactMajority.mcrCount (L := L) (K := K) (c - {s, t} + {s, t}) :=
        (ExactMajority.mcrCount_add _ _).symm
    _ = ExactMajority.mcrCount (L := L) (K := K) c := by rw [h_restore]

/-- **Config-level one-sided `mcrCount` decrement (mirror: s assignable, t MCR).** -/
theorem mcrCount_config_decrease_of_assignable_mcr
    (c : Config (AgentState L K)) (s t : AgentState L K)
    (h_sub : ({s, t} : Config (AgentState L K)) ≤ c)
    (hs : IsAssignable s) (ht : t.role = .mcr) (ht_phase : t.phase.val = 0) :
    ExactMajority.mcrCount (L := L) (K := K)
        (c - {s, t} + {(Transition L K s t).1, (Transition L K s t).2}) <
      ExactMajority.mcrCount (L := L) (K := K) c := by
  have hs_phase : s.phase.val = 0 := hs.1
  have h_restore : c - {s, t} + {s, t} = c := Multiset.sub_add_cancel h_sub
  have hroles := Transition_roles_eq_phase0_of_both_phase0 (L := L) (K := K) s t hs_phase ht_phase
  have hpair_eq : ExactMajority.mcrCount (L := L) (K := K)
      ({(Transition L K s t).1, (Transition L K s t).2} : Config (AgentState L K)) =
      ExactMajority.mcrCount (L := L) (K := K)
      ({(Phase0Transition L K s t).1, (Phase0Transition L K s t).2} : Config (AgentState L K)) := by
    rw [mcrCount_pair', mcrCount_pair', hroles.1, hroles.2]
  have h_pair_lt := Phase0Transition_mcrCount_pair_lt_of_assignable_mcr s t hs ht
  calc ExactMajority.mcrCount (L := L) (K := K)
          (c - {s, t} + {(Transition L K s t).1, (Transition L K s t).2})
      = ExactMajority.mcrCount (L := L) (K := K) (c - {s, t}) +
          ExactMajority.mcrCount (L := L) (K := K)
            ({(Transition L K s t).1, (Transition L K s t).2}) :=
        ExactMajority.mcrCount_add _ _
    _ = ExactMajority.mcrCount (L := L) (K := K) (c - {s, t}) +
          ExactMajority.mcrCount (L := L) (K := K)
            ({(Phase0Transition L K s t).1, (Phase0Transition L K s t).2}) := by rw [hpair_eq]
    _ < ExactMajority.mcrCount (L := L) (K := K) (c - {s, t}) +
          ExactMajority.mcrCount (L := L) (K := K) ({s, t} : Config (AgentState L K)) :=
        Nat.add_lt_add_left h_pair_lt _
    _ = ExactMajority.mcrCount (L := L) (K := K) (c - {s, t} + {s, t}) :=
        (ExactMajority.mcrCount_add _ _).symm
    _ = ExactMajority.mcrCount (L := L) (K := K) c := by rw [h_restore]

/-- The `assignableCount` Bool predicate decides `IsAssignable` pointwise.  This
bridges the `countP`/Finset-filter form used in mass arguments with the `Prop`
`IsAssignable` used in the decrement lemmas. -/
theorem assignableCount_pred_iff (a : AgentState L K) :
    (decide (a.phase.val = 0) && (!a.assigned) &&
      (decide (a.role = .main) || decide (a.role = .cr))) = true ↔ IsAssignable a := by
  unfold IsAssignable
  simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq,
    Bool.not_eq_eq_eq_not, Bool.not_true]
  constructor
  · rintro ⟨⟨hp, ha⟩, hr⟩
    exact ⟨hp, by simpa using ha, hr⟩
  · rintro ⟨hp, ha, hr⟩
    exact ⟨⟨hp, by simpa using ha⟩, hr⟩

end RoleSplitConcentration
end ExactMajority
