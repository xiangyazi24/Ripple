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

/-! ### Per-rule `assignableCount` accounting — the deterministic delta.

These three lemmas pin the *exact* per-step change of the assignable pool, settling
the floor route (deterministic regime-split vs Chernoff).  In this encoding:

  * **Rule 2** (`s = MCR`, `t = unassigned Main`): `s`→`CR` with `assigned`
    *untouched*, so the `s`-output is a **fresh unassigned CR** — assignable.  `t`
    becomes assigned.  Net Δassignable `= 0`  (`assignable_rule2_s_stays`).
  * **Rule 3** (`s = MCR`, `t = unassigned RoleCR`): `s`→`Main` with
    `assigned := true` — **NOT** assignable; `t` becomes assigned.  Net Δ `= −1`
    (`assignable_rule3_s_assigned`).
  * **Rule 1** (`MCR,MCR`): both outputs `assigned`-untouched, roles `Main`/`CR`
    — `+2` if the MCRs were unassigned.

So `assignableCount` is **not** monotone in this encoding: Rule 3 (and Rule 4) drop
it.  This differs from the paper's reaction 3 `Mf,U → Mt,Sf`, which produces a
*fresh* unassigned `Sf` and keeps the pool conserved.  Consequently the clean
deterministic floor does NOT transfer; Gap (B) genuinely needs the probabilistic
Chernoff floor (documented in the campaign note). -/

/-- **Rule 2 keeps the `s`-output assignable.** `s = MCR` meeting an unassigned
`Main` `t` becomes a `CR` with `assigned` unchanged; if `s` was unassigned and at
phase 0, the output `s`-agent is a *fresh* assignable (`role = cr`, `¬assigned`,
phase 0).  This is the conserving half of Rule 2. -/
theorem assignable_rule2_s_stays
    (s t : AgentState L K) (hs : s.role = .mcr) (ht : t.role = .main)
    (ht_un : t.assigned = false) (hs_un : s.assigned = false) (hs_ph : s.phase.val = 0) :
    IsAssignable (Phase0Transition L K s t).1 := by
  have hmcr_main : (Role.mcr = Role.main) = False := by simp
  have hmain_mcr : (Role.main = Role.mcr) = False := by simp
  have hrole : (Phase0Transition L K s t).1.role = .cr := by
    unfold Phase0Transition
    simp [hs, ht, hmcr_main, hmain_mcr, ht_un, hs_un]
  have hassigned : (Phase0Transition L K s t).1.assigned = false := by
    unfold Phase0Transition
    simp [hs, ht, hmcr_main, hmain_mcr, ht_un, hs_un]
  have hphase : (Phase0Transition L K s t).1.phase.val = 0 := by
    have : (Phase0Transition L K s t).1.phase = s.phase := by
      unfold Phase0Transition
      simp [hs, ht, hmcr_main, hmain_mcr, ht_un, hs_un]
    rw [this]; exact hs_ph
  exact ⟨hphase, by rw [hassigned]; simp, Or.inr hrole⟩

/-- **Rule 3 marks the `s`-output assigned.** `s = MCR` meeting an unassigned
non-Main/non-MCR (i.e. `RoleCR`) `t` becomes a `Main` with `assigned := true`,
hence **not** assignable.  This is the consuming half of Rule 3 (the reason
`assignableCount` is not monotone here). -/
theorem assignable_rule3_s_assigned
    (s t : AgentState L K) (hs : s.role = .mcr)
    (ht_nm : t.role ≠ .main) (ht_nmcr : t.role ≠ .mcr) (ht_un : t.assigned = false) :
    (Phase0Transition L K s t).1.assigned = true := by
  have hmcr_main : (Role.mcr = Role.main) = False := by simp
  unfold Phase0Transition
  simp [hs, hmcr_main, ht_nm, ht_nmcr, ht_un]

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

/-! ## Phase C-1 (relay 2, continued) — the one-sided interactionPMF mass route.

We now build the `Θ(M·assignable/n²)` per-step decrease probability for the
one-sided good set, cloning the MCR–MCR mass route of `Phase0Convergence`
(`sum_interactionCount_mcr → interactionPMF_toMeasure_mcr_phase0_ge →
phase0_mcrCount_decrease_prob`).  The key simplification over the MCR–MCR case:
an MCR initiator and an assignable responder are **always distinct** states
(`mcr ≠ main, cr`), so each `interactionCount` term is the clean product
`count s₁ · count s₂` with **no `−1`**, giving the exact product
`mcrCount c · assignableCount c` (vs the `M·(M−1)` of the diagonal case).

### The role/Bool predicate the assignable Finset filters on. -/

/-- The decidable predicate that the `assignableCount` `countP` and the
assignable Finset filter share.  Equals `IsAssignable` pointwise
(`assignableCount_pred_iff`). -/
def isAssignableBool (a : AgentState L K) : Bool :=
  decide (a.phase.val = 0) && (!a.assigned) &&
    (decide (a.role = .main) || decide (a.role = .cr))

/-- `assignableCount` re-expressed via `isAssignableBool` (definitional). -/
theorem assignableCount_eq_countP (c : Config (AgentState L K)) :
    assignableCount (L := L) (K := K) c =
      Multiset.countP (fun a => isAssignableBool (L := L) (K := K) a) c := rfl

/-- The MCR filter Finset (initiators of the one-sided conversion). -/
private def mcrF : Finset (AgentState L K) :=
  Finset.univ.filter (fun s : AgentState L K => s.role = .mcr)

/-- The assignable filter Finset (responders of the one-sided conversion). -/
private def assignF : Finset (AgentState L K) :=
  Finset.univ.filter (fun s : AgentState L K => isAssignableBool (L := L) (K := K) s = true)

/-- `∑_{s ∈ mcrF} c.count s = mcrCount c`.  (Clone of `sum_count_mcr_filter`,
re-derived locally since the upstream is `private`.) -/
private lemma sum_count_mcrF (c : Config (AgentState L K)) :
    ∑ s ∈ mcrF (L := L) (K := K), c.count s =
      ExactMajority.mcrCount (L := L) (K := K) c := by
  set F := mcrF (L := L) (K := K) with hF
  set cm := Multiset.filter (fun a : AgentState L K => a.role = .mcr) c with hcm
  have hcount : ∀ s ∈ F, c.count s = Multiset.count s cm := fun s hs => by
    show Multiset.count s c = Multiset.count s cm
    have hs_mcr : (fun a : AgentState L K => a.role = .mcr) s :=
      (Finset.mem_filter.mp hs).2
    simp only [cm, Multiset.count_filter, hs_mcr, ite_true]
  calc ∑ s ∈ F, c.count s
      = ∑ s ∈ F, Multiset.count s cm := Finset.sum_congr rfl hcount
    _ = Multiset.card cm :=
        Multiset.sum_count_eq_card (s := F) (m := cm)
          (fun a ha => Finset.mem_filter.mpr ⟨Finset.mem_univ a,
            (Multiset.mem_filter.mp ha).2⟩)
    _ = ExactMajority.mcrCount (L := L) (K := K) c := by
        rw [ExactMajority.mcrCount, hcm]

/-- `∑_{s ∈ assignF} c.count s = assignableCount c`.  The assignable analogue of
`sum_count_mcrF`; `assignableCount` is a `countP`, hence a `filter`-card. -/
private lemma sum_count_assignF (c : Config (AgentState L K)) :
    ∑ s ∈ assignF (L := L) (K := K), c.count s =
      assignableCount (L := L) (K := K) c := by
  set F := assignF (L := L) (K := K) with hF
  set ca := Multiset.filter (fun a : AgentState L K =>
    isAssignableBool (L := L) (K := K) a = true) c with hca
  have hcount : ∀ s ∈ F, c.count s = Multiset.count s ca := fun s hs => by
    show Multiset.count s c = Multiset.count s ca
    have hs_a : isAssignableBool (L := L) (K := K) s = true :=
      (Finset.mem_filter.mp hs).2
    simp only [ca, Multiset.count_filter, hs_a, ite_true]
  calc ∑ s ∈ F, c.count s
      = ∑ s ∈ F, Multiset.count s ca := Finset.sum_congr rfl hcount
    _ = Multiset.card ca :=
        Multiset.sum_count_eq_card (s := F) (m := ca)
          (fun a ha => Finset.mem_filter.mpr ⟨Finset.mem_univ a,
            (Multiset.mem_filter.mp ha).2⟩)
    _ = assignableCount (L := L) (K := K) c := by
        rw [assignableCount_eq_countP, hca, ← Multiset.countP_eq_card_filter]

/-- For a fixed MCR initiator `s₁`, summing `interactionCount s₁ s₂` over
assignable responders gives `count s₁ · assignableCount c` — **no `−1`**, since
an MCR initiator is never equal to an assignable responder. -/
private lemma sum_interactionCount_assignF_right (c : Config (AgentState L K))
    (s₁ : AgentState L K) (hs₁ : s₁.role = .mcr) :
    ∑ s₂ ∈ assignF (L := L) (K := K), c.interactionCount s₁ s₂ =
      c.count s₁ * assignableCount (L := L) (K := K) c := by
  have hne : ∀ s₂ ∈ assignF (L := L) (K := K), s₁ ≠ s₂ := by
    intro s₂ hs₂ heq
    have hs₂_a : isAssignableBool (L := L) (K := K) s₂ = true :=
      (Finset.mem_filter.mp hs₂).2
    have hs₂_assignable : IsAssignable s₂ :=
      (assignableCount_pred_iff (L := L) (K := K) s₂).mp hs₂_a
    obtain ⟨_, _, hrole⟩ := hs₂_assignable
    rw [← heq] at hrole
    rcases hrole with h | h <;> rw [hs₁] at h <;> exact absurd h (by decide)
  have hfactor : ∀ s₂ ∈ assignF (L := L) (K := K),
      c.interactionCount s₁ s₂ = c.count s₁ * c.count s₂ := by
    intro s₂ hs₂
    unfold Config.interactionCount
    rw [if_neg (hne s₂ hs₂)]
  rw [Finset.sum_congr rfl hfactor, ← Finset.mul_sum, sum_count_assignF]

/-- **Cross-class interaction-count sum.**  Summing `interactionCount` over the
rectangle `mcrF ×ˢ assignF` gives the clean product `mcrCount c · assignableCount
c` (Phase C-1 gap atom #1). -/
private lemma sum_interactionCount_mcr_assign (c : Config (AgentState L K)) :
    ∑ s₁ ∈ mcrF (L := L) (K := K), ∑ s₂ ∈ assignF (L := L) (K := K),
        c.interactionCount s₁ s₂ =
      ExactMajority.mcrCount (L := L) (K := K) c *
        assignableCount (L := L) (K := K) c := by
  have hstep : ∀ s₁ ∈ mcrF (L := L) (K := K),
      ∑ s₂ ∈ assignF (L := L) (K := K), c.interactionCount s₁ s₂ =
        c.count s₁ * assignableCount (L := L) (K := K) c := by
    intro s₁ hs₁
    exact sum_interactionCount_assignF_right c s₁
      (Finset.mem_filter.mp (show s₁ ∈ Finset.univ.filter _ from hs₁)).2
  rw [Finset.sum_congr rfl hstep, ← Finset.sum_mul, sum_count_mcrF]

/-- Positive `interactionCount` implies `Applicable` (re-derived locally; the
upstream `applicable_of_pos_iCount` is `private`). -/
private lemma applicable_of_pos_iCount' (c : Config (AgentState L K))
    (s₁ s₂ : AgentState L K) (h : 0 < c.interactionCount s₁ s₂) :
    Protocol.Applicable c s₁ s₂ := by
  show {s₁, s₂} ≤ c; rw [Multiset.le_iff_count]; intro a
  simp only [Config.interactionCount, Config.count] at h
  simp only [Multiset.insert_eq_cons, Multiset.count_cons, Multiset.count_singleton]
  by_cases heq : s₁ = s₂
  · subst heq; simp only [ite_true] at h
    have : 2 ≤ Multiset.count s₁ c := by
      by_contra h_lt
      have hle : Multiset.count s₁ c ≤ 1 := by omega
      have : Multiset.count s₁ c * (Multiset.count s₁ c - 1) = 0 := by
        rcases Nat.eq_zero_or_pos (Multiset.count s₁ c) with h0 | h0
        · simp [h0]
        · have : Multiset.count s₁ c = 1 := by omega
          simp [this]
      omega
    by_cases ha : a = s₁ <;> simp_all
  · simp only [heq, ite_false] at h
    have hc1 : 0 < Multiset.count s₁ c := pos_of_mul_pos_left h (Nat.zero_le _)
    have hc2 : 0 < Multiset.count s₂ c := pos_of_mul_pos_right h (Nat.zero_le _)
    by_cases ha1 : a = s₁ <;> by_cases ha2 : a = s₂ <;> simp_all <;> omega

/-- **One-sided interactionPMF mass bound (MCR initiator × assignable responder).**
The PMF mass of the good set "`p.1` is a phase-0 MCR, `p.2` is assignable, and
`(p.1,p.2)` is applicable" is at least `mcrCount·assignableCount/(card(card-1))`.
Clone of `interactionPMF_toMeasure_mcr_phase0_ge`; uses the clean cross-class
product `sum_interactionCount_mcr_assign`. -/
private lemma interactionPMF_toMeasure_mcr_assign_ge
    (c : Config (AgentState L K)) (hc : 2 ≤ c.card)
    (h_phase0 : ∀ a ∈ c, a.role = .mcr → a.phase.val = 0) :
    (c.interactionPMF hc).toMeasure
      {p : AgentState L K × AgentState L K |
        p.1.role = .mcr ∧ p.1.phase.val = 0 ∧ IsAssignable p.2 ∧
        Protocol.Applicable c p.1 p.2} ≥
    ENNReal.ofReal
      (((ExactMajority.mcrCount (L := L) (K := K) c *
          assignableCount (L := L) (K := K) c : ℕ) : ℝ) /
        (c.card * (c.card - 1) : ℝ)) := by
  set target := {p : AgentState L K × AgentState L K |
    p.1.role = .mcr ∧ p.1.phase.val = 0 ∧ IsAssignable p.2 ∧
    Protocol.Applicable c p.1 p.2}
  set F := mcrF (L := L) (K := K) with hFdef
  set G := assignF (L := L) (K := K) with hGdef
  have h_sub : (↑(F ×ˢ G) : Set _) ∩ (c.interactionPMF hc).support ⊆ target := by
    intro ⟨s₁, s₂⟩ ⟨h_mem, h_supp⟩
    have hs₁_mcr : s₁.role = .mcr :=
      (Finset.mem_filter.mp (Finset.mem_product.mp h_mem).1).2
    have hs₂_a : isAssignableBool (L := L) (K := K) s₂ = true :=
      (Finset.mem_filter.mp (Finset.mem_product.mp h_mem).2).2
    have hs₂_assign : IsAssignable s₂ :=
      (assignableCount_pred_iff (L := L) (K := K) s₂).mp hs₂_a
    rw [PMF.mem_support_iff] at h_supp
    have h_app : Protocol.Applicable c s₁ s₂ := by
      apply applicable_of_pos_iCount'
      by_contra h0; exact h_supp (show c.interactionProb s₁ s₂ = 0 by
        simp [Config.interactionProb, show c.interactionCount s₁ s₂ = 0 by omega])
    exact ⟨hs₁_mcr,
      h_phase0 s₁ (Multiset.mem_of_le h_app (Multiset.mem_cons_self _ _)) hs₁_mcr,
      hs₂_assign, h_app⟩
  have h_le := (c.interactionPMF hc).toMeasure_mono
    (DiscreteMeasurableSpace.forall_measurableSet _) h_sub
  suffices h_val : (c.interactionPMF hc).toMeasure (↑(F ×ˢ G)) ≥
      ENNReal.ofReal
        (((ExactMajority.mcrCount (L := L) (K := K) c *
            assignableCount (L := L) (K := K) c : ℕ) : ℝ) /
          (c.card * (c.card - 1) : ℝ)) from le_trans h_val h_le
  rw [PMF.toMeasure_apply_finset]
  simp_rw [show ∀ p : AgentState L K × AgentState L K,
    (c.interactionPMF hc) p = (c.interactionCount p.1 p.2 : ENNReal) / c.totalPairs
    from fun _ => rfl, div_eq_mul_inv, ← Finset.sum_mul]
  conv_lhs => arg 1; rw [Finset.sum_product' F G
    (fun s₁ s₂ => (c.interactionCount s₁ s₂ : ENNReal))]
  have h_comb := sum_interactionCount_mcr_assign (L := L) (K := K) c
  set MM := ExactMajority.mcrCount (L := L) (K := K) c *
    assignableCount (L := L) (K := K) c with hMM
  rw [show (∑ s₁ ∈ F, ∑ s₂ ∈ G, (c.interactionCount s₁ s₂ : ENNReal)) =
      ((MM : ℕ) : ENNReal) from by exact_mod_cast h_comb, ← div_eq_mul_inv]
  have h1 : 1 ≤ c.card := by omega
  have hprod_pos : (0 : ℝ) < ↑c.card * (↑c.card - 1) := by
    apply mul_pos
    · exact Nat.cast_pos.mpr (by omega)
    · exact sub_pos.mpr (by exact_mod_cast (show 1 < c.card by omega))
  show ↑MM / ↑c.totalPairs ≥
    ENNReal.ofReal (((MM : ℕ) : ℝ) / (↑c.card * (↑c.card - 1)))
  have hcard_cast : ↑c.card * (↑c.card - 1 : ℝ) = ((c.card * (c.card - 1) : ℕ) : ℝ) := by
    push_cast [Nat.cast_sub h1]; ring
  rw [ENNReal.ofReal_div_of_pos hprod_pos, hcard_cast,
    ENNReal.ofReal_natCast, ENNReal.ofReal_natCast,
    show (c.card * (c.card - 1) : ℕ) = c.totalPairs from rfl]

/-! ### The strengthened one-sided decrease probability.

Chaining the mass bound through `stepDistOrSelf_toMeasure_ge` and the inherited
config-level one-sided decrement lemmas gives the `Θ(M·assignable/n²)` per-step
probability that the scheduled step strictly drops `mcrCount`.  We use the SINGLE
(MCR initiator × assignable responder) direction; the mirror direction would only
sharpen the constant by a factor of 2 and is not needed to reach the `Θ(M/n)`
rate once `assignableCount = Θ(n)`. -/

/-- **Strengthened one-sided decrease probability (Phase C-1 gap atom #3).** On a
config `c` with `card = n`, all MCR agents at phase 0, the scheduled-step
distribution puts mass at least `mcrCount·assignableCount/(n(n−1))` on the event
`{mcrCount decreases}`.  This is the one-sided analogue of
`phase0_mcrCount_decrease_prob` — the rate that, with `assignableCount = Θ(n)`,
gives `Θ(M/n)` and hence `pMin = Θ(1/n)`. -/
theorem phase0_mcrCount_decrease_prob_oneSided
    (c : Config (AgentState L K)) (n : ℕ)
    (h_card : c.card = n) (hn2 : 2 ≤ n)
    (h_phase0 : ∀ a ∈ c, a.role = .mcr → a.phase.val = 0) :
    ((NonuniformMajority L K).stepDistOrSelf c).toMeasure
        {c' | ExactMajority.mcrCount (L := L) (K := K) c' <
          ExactMajority.mcrCount (L := L) (K := K) c} ≥
      ENNReal.ofReal
        (((ExactMajority.mcrCount (L := L) (K := K) c *
            assignableCount (L := L) (K := K) c : ℕ) : ℝ) /
          (n * (n - 1) : ℝ)) := by
  have hc2 : 2 ≤ c.card := by omega
  set good : Set (AgentState L K × AgentState L K) :=
    {p | p.1.role = .mcr ∧ p.1.phase.val = 0 ∧ IsAssignable p.2 ∧
         Protocol.Applicable c p.1 p.2} with hgooddef
  have hgood : ∀ pair ∈ good, (NonuniformMajority L K).scheduledStep c pair ∈
      {c' | ExactMajority.mcrCount (L := L) (K := K) c' <
        ExactMajority.mcrCount (L := L) (K := K) c} := by
    intro ⟨s, t⟩ ⟨hs_mcr, hs_phase, ht_assign, happ⟩
    simp only [Set.mem_setOf_eq]
    unfold Protocol.scheduledStep Protocol.stepOrSelf
    rw [if_pos happ]
    exact mcrCount_config_decrease_of_mcr_assignable c s t happ hs_mcr hs_phase ht_assign
  calc ((NonuniformMajority L K).stepDistOrSelf c).toMeasure
          {c' | ExactMajority.mcrCount (L := L) (K := K) c' <
            ExactMajority.mcrCount (L := L) (K := K) c}
      ≥ (c.interactionPMF hc2).toMeasure good :=
        stepDistOrSelf_toMeasure_ge c hc2 _ good hgood
    _ ≥ ENNReal.ofReal
          (((ExactMajority.mcrCount (L := L) (K := K) c *
              assignableCount (L := L) (K := K) c : ℕ) : ℝ) /
            (c.card * (c.card - 1) : ℝ)) :=
        interactionPMF_toMeasure_mcr_assign_ge c hc2 h_phase0
    _ = ENNReal.ofReal
          (((ExactMajority.mcrCount (L := L) (K := K) c *
              assignableCount (L := L) (K := K) c : ℕ) : ℝ) /
            (n * (n - 1) : ℝ)) := by rw [h_card]

/-! ### Combined decrease rate (MCR×MCR ∪ MCR×assignable).

The paper's `p = 2u/(5n)` rate comes from combining Rule-1 (MCR×MCR, the
`u(u−1)/n²` diagonal) with Rules 2,3 (MCR×assignable, the `u·assignable/n²`
cross term).  Both good sets land in `{mcrCount decreases}` and are **disjoint**
(a responder is either MCR or assignable, never both, since `mcr ≠ main, cr`).
Aggregating the two rectangles gives the combined mass `[M(M−1) +
M·assignable]/(n(n−1))`.

NOTE on the structural blocker (documented for the milestone-family gap): this
combined per-step rate is the consumable a *floor-carrying* milestone phase
needs, but `MilestonePhase.progress` (JansonHitting.lean) requires the rate to
hold UNCONDITIONALLY at every config with milestones `<i` reached and `i` not.
At a config where `assignableCount = 0` and `mcrCount = M` is small, neither term
reaches `Θ(M/n)` — so the combined rate `≥ Θ(M/n)` needs the Chernoff floor
`assignableCount ≥ n/5`, which the plain `MilestonePhase` cannot carry.  See the
campaign note's Phase-C-1 gap atom #4.  This lemma delivers the combined rate;
the floor + a floor-carrying milestone variant remain the genuine open gap. -/

/-- For a fixed MCR initiator `s₁`, the sum of `interactionCount s₁ s₂` over MCR
responders is `count s₁ · (mcrCount c − 1)` (re-derived locally; upstream is
`private`).  The diagonal `s₁ = s₂` subtracts one. -/
private lemma sum_interactionCount_mcrF_right (c : Config (AgentState L K))
    (s₁ : AgentState L K) (hs₁ : s₁.role = .mcr) :
    ∑ s₂ ∈ mcrF (L := L) (K := K), c.interactionCount s₁ s₂ =
      c.count s₁ * (ExactMajority.mcrCount (L := L) (K := K) c - 1) := by
  set F := mcrF (L := L) (K := K) with hF
  by_cases hzero : c.count s₁ = 0
  · have hall : ∀ s₂ ∈ F, c.interactionCount s₁ s₂ = 0 := fun s₂ _ => by
      unfold Config.interactionCount Config.count
      unfold Config.count at hzero
      split_ifs with h
      · subst h; simp [hzero]
      · simp [hzero]
    rw [Finset.sum_eq_zero hall]; simp [hzero]
  · have hfactor : ∀ s₂ ∈ F, c.interactionCount s₁ s₂ =
        c.count s₁ * if s₁ = s₂ then c.count s₁ - 1 else c.count s₂ := by
      intro s₂ _; unfold Config.interactionCount
      by_cases h : s₁ = s₂ <;> simp [h]
    rw [Finset.sum_congr rfl hfactor, ← Finset.mul_sum]; congr 1
    have hs₁F : s₁ ∈ F := Finset.mem_filter.mpr ⟨Finset.mem_univ s₁, hs₁⟩
    set f : AgentState L K → ℕ :=
      fun s₂ => if s₁ = s₂ then c.count s₁ - 1 else c.count s₂ with hfdef
    have hf_s₁ : f s₁ = c.count s₁ - 1 := if_pos rfl
    have hf_ne : ∀ s₂ ∈ F.erase s₁, f s₂ = c.count s₂ :=
      fun s₂ hs₂ => if_neg (Finset.ne_of_mem_erase hs₂).symm
    calc ∑ s₂ ∈ F, f s₂
        = f s₁ + ∑ s₂ ∈ F.erase s₁, f s₂ := (Finset.add_sum_erase F f hs₁F).symm
      _ = (c.count s₁ - 1) + ∑ s₂ ∈ F.erase s₁, c.count s₂ := by
          rw [hf_s₁, Finset.sum_congr rfl hf_ne]
      _ = ExactMajority.mcrCount (L := L) (K := K) c - 1 := by
          have hse : c.count s₁ + ∑ s₂ ∈ F.erase s₁, c.count s₂ =
              ExactMajority.mcrCount (L := L) (K := K) c := by
            rw [Finset.add_sum_erase F (fun s => c.count s) hs₁F]
            exact sum_count_mcrF c
          have hcount_pos : 0 < c.count s₁ := Nat.pos_of_ne_zero hzero
          omega

/-- The MCR×MCR rectangle sum `= mcrCount·(mcrCount−1)` (re-derived locally). -/
private lemma sum_interactionCount_mcr_mcr (c : Config (AgentState L K)) :
    ∑ s₁ ∈ mcrF (L := L) (K := K), ∑ s₂ ∈ mcrF (L := L) (K := K),
        c.interactionCount s₁ s₂ =
      ExactMajority.mcrCount (L := L) (K := K) c *
        (ExactMajority.mcrCount (L := L) (K := K) c - 1) := by
  have hstep : ∀ s₁ ∈ mcrF (L := L) (K := K),
      ∑ s₂ ∈ mcrF (L := L) (K := K), c.interactionCount s₁ s₂ =
        c.count s₁ * (ExactMajority.mcrCount (L := L) (K := K) c - 1) := fun s₁ hs₁ =>
    sum_interactionCount_mcrF_right c s₁ (Finset.mem_filter.mp hs₁).2
  rw [Finset.sum_congr rfl hstep, ← Finset.sum_mul, sum_count_mcrF]

/-- `mcrF` and `assignF` are disjoint: an MCR agent is never assignable. -/
private lemma mcrF_disjoint_assignF :
    Disjoint (mcrF (L := L) (K := K)) (assignF (L := L) (K := K)) := by
  rw [Finset.disjoint_left]
  intro a ha ha'
  have h_mcr : a.role = .mcr := (Finset.mem_filter.mp ha).2
  have h_a : isAssignableBool (L := L) (K := K) a = true := (Finset.mem_filter.mp ha').2
  obtain ⟨_, _, hrole⟩ := (assignableCount_pred_iff (L := L) (K := K) a).mp h_a
  rcases hrole with h | h <;> rw [h_mcr] at h <;> exact absurd h (by decide)

/-- **Combined rectangle sum** over `mcrF ×ˢ (mcrF ∪ assignF)`:
`mcrCount·(mcrCount−1) + mcrCount·assignableCount`. -/
private lemma sum_interactionCount_mcr_combined (c : Config (AgentState L K)) :
    ∑ s₁ ∈ mcrF (L := L) (K := K),
      ∑ s₂ ∈ mcrF (L := L) (K := K) ∪ assignF (L := L) (K := K),
        c.interactionCount s₁ s₂ =
      ExactMajority.mcrCount (L := L) (K := K) c *
          (ExactMajority.mcrCount (L := L) (K := K) c - 1) +
        ExactMajority.mcrCount (L := L) (K := K) c *
          assignableCount (L := L) (K := K) c := by
  have hsplit : ∀ s₁ ∈ mcrF (L := L) (K := K),
      ∑ s₂ ∈ mcrF (L := L) (K := K) ∪ assignF (L := L) (K := K),
          c.interactionCount s₁ s₂ =
        (∑ s₂ ∈ mcrF (L := L) (K := K), c.interactionCount s₁ s₂) +
          (∑ s₂ ∈ assignF (L := L) (K := K), c.interactionCount s₁ s₂) := by
    intro s₁ _
    exact Finset.sum_union (mcrF_disjoint_assignF (L := L) (K := K))
  rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib,
    sum_interactionCount_mcr_mcr, sum_interactionCount_mcr_assign]

/-- **Combined interactionPMF mass bound.** The PMF mass of the good set "`p.1` is
a phase-0 MCR, `p.2` is a phase-0 MCR *or* assignable, and `(p.1,p.2)` is
applicable" is at least `[mcrCount·(mcrCount−1) + mcrCount·assignableCount] /
(card(card−1))` — the combined diagonal + cross rate.  Re-runs the rectangle
argument over `mcrF ×ˢ (mcrF ∪ assignF)`. -/
private lemma interactionPMF_toMeasure_mcr_combined_ge
    (c : Config (AgentState L K)) (hc : 2 ≤ c.card)
    (h_phase0 : ∀ a ∈ c, a.role = .mcr → a.phase.val = 0) :
    (c.interactionPMF hc).toMeasure
      {p : AgentState L K × AgentState L K |
        p.1.role = .mcr ∧ p.1.phase.val = 0 ∧
        ((p.2.role = .mcr ∧ p.2.phase.val = 0) ∨ IsAssignable p.2) ∧
        Protocol.Applicable c p.1 p.2} ≥
    ENNReal.ofReal
      (((ExactMajority.mcrCount (L := L) (K := K) c *
          (ExactMajority.mcrCount (L := L) (K := K) c - 1) +
          ExactMajority.mcrCount (L := L) (K := K) c *
            assignableCount (L := L) (K := K) c : ℕ) : ℝ) /
        (c.card * (c.card - 1) : ℝ)) := by
  set target := {p : AgentState L K × AgentState L K |
    p.1.role = .mcr ∧ p.1.phase.val = 0 ∧
    ((p.2.role = .mcr ∧ p.2.phase.val = 0) ∨ IsAssignable p.2) ∧
    Protocol.Applicable c p.1 p.2}
  set F := mcrF (L := L) (K := K) with hFdef
  set G := mcrF (L := L) (K := K) ∪ assignF (L := L) (K := K) with hGdef
  have h_sub : (↑(F ×ˢ G) : Set _) ∩ (c.interactionPMF hc).support ⊆ target := by
    intro ⟨s₁, s₂⟩ ⟨h_mem, h_supp⟩
    have hs₁_mcr : s₁.role = .mcr :=
      (Finset.mem_filter.mp (Finset.mem_product.mp h_mem).1).2
    have hs₂_mem : s₂ ∈ G := (Finset.mem_product.mp h_mem).2
    rw [PMF.mem_support_iff] at h_supp
    have h_app : Protocol.Applicable c s₁ s₂ := by
      apply applicable_of_pos_iCount'
      by_contra h0; exact h_supp (show c.interactionProb s₁ s₂ = 0 by
        simp [Config.interactionProb, show c.interactionCount s₁ s₂ = 0 by omega])
    have h2cond : (s₂.role = .mcr ∧ s₂.phase.val = 0) ∨ IsAssignable s₂ := by
      rcases Finset.mem_union.mp hs₂_mem with hm | ha
      · have hs₂_mcr : s₂.role = .mcr := (Finset.mem_filter.mp hm).2
        exact Or.inl ⟨hs₂_mcr,
          h_phase0 s₂ (Multiset.mem_of_le h_app
            (Multiset.mem_cons.mpr (Or.inr (Multiset.mem_singleton_self _)))) hs₂_mcr⟩
      · exact Or.inr ((assignableCount_pred_iff (L := L) (K := K) s₂).mp
          (Finset.mem_filter.mp ha).2)
    exact ⟨hs₁_mcr,
      h_phase0 s₁ (Multiset.mem_of_le h_app (Multiset.mem_cons_self _ _)) hs₁_mcr,
      h2cond, h_app⟩
  have h_le := (c.interactionPMF hc).toMeasure_mono
    (DiscreteMeasurableSpace.forall_measurableSet _) h_sub
  suffices h_val : (c.interactionPMF hc).toMeasure (↑(F ×ˢ G)) ≥
      ENNReal.ofReal
        (((ExactMajority.mcrCount (L := L) (K := K) c *
            (ExactMajority.mcrCount (L := L) (K := K) c - 1) +
            ExactMajority.mcrCount (L := L) (K := K) c *
              assignableCount (L := L) (K := K) c : ℕ) : ℝ) /
          (c.card * (c.card - 1) : ℝ)) from le_trans h_val h_le
  rw [PMF.toMeasure_apply_finset]
  simp_rw [show ∀ p : AgentState L K × AgentState L K,
    (c.interactionPMF hc) p = (c.interactionCount p.1 p.2 : ENNReal) / c.totalPairs
    from fun _ => rfl, div_eq_mul_inv, ← Finset.sum_mul]
  conv_lhs => arg 1; rw [Finset.sum_product' F G
    (fun s₁ s₂ => (c.interactionCount s₁ s₂ : ENNReal))]
  have h_comb := sum_interactionCount_mcr_combined (L := L) (K := K) c
  set MM := ExactMajority.mcrCount (L := L) (K := K) c *
      (ExactMajority.mcrCount (L := L) (K := K) c - 1) +
    ExactMajority.mcrCount (L := L) (K := K) c *
      assignableCount (L := L) (K := K) c with hMM
  rw [show (∑ s₁ ∈ F, ∑ s₂ ∈ G, (c.interactionCount s₁ s₂ : ENNReal)) =
      ((MM : ℕ) : ENNReal) from by exact_mod_cast h_comb, ← div_eq_mul_inv]
  have h1 : 1 ≤ c.card := by omega
  have hprod_pos : (0 : ℝ) < ↑c.card * (↑c.card - 1) := by
    apply mul_pos
    · exact Nat.cast_pos.mpr (by omega)
    · exact sub_pos.mpr (by exact_mod_cast (show 1 < c.card by omega))
  show ↑MM / ↑c.totalPairs ≥
    ENNReal.ofReal (((MM : ℕ) : ℝ) / (↑c.card * (↑c.card - 1)))
  have hcard_cast : ↑c.card * (↑c.card - 1 : ℝ) = ((c.card * (c.card - 1) : ℕ) : ℝ) := by
    push_cast [Nat.cast_sub h1]; ring
  rw [ENNReal.ofReal_div_of_pos hprod_pos, hcard_cast,
    ENNReal.ofReal_natCast, ENNReal.ofReal_natCast,
    show (c.card * (c.card - 1) : ℕ) = c.totalPairs from rfl]

/-- **Combined decrease probability (Phase C-1 combined rate).** On a config `c`
with `card = n`, all MCR at phase 0, and `mcrCount ≥ 2`, the scheduled step drops
`mcrCount` with mass at least `[M(M−1) + M·assignable]/(n(n−1))` — the paper's
combined Rule-1 + Rules-2,3 rate.  At `assignableCount ≥ n/5` (the Chernoff
floor) and `M ≤ n` this is `≥ Θ(M/n)`. -/
theorem phase0_mcrCount_decrease_prob_combined
    (c : Config (AgentState L K)) (n : ℕ)
    (h_card : c.card = n) (hn2 : 2 ≤ n)
    (h_phase0 : ∀ a ∈ c, a.role = .mcr → a.phase.val = 0) :
    ((NonuniformMajority L K).stepDistOrSelf c).toMeasure
        {c' | ExactMajority.mcrCount (L := L) (K := K) c' <
          ExactMajority.mcrCount (L := L) (K := K) c} ≥
      ENNReal.ofReal
        (((ExactMajority.mcrCount (L := L) (K := K) c *
            (ExactMajority.mcrCount (L := L) (K := K) c - 1) +
            ExactMajority.mcrCount (L := L) (K := K) c *
              assignableCount (L := L) (K := K) c : ℕ) : ℝ) /
          (n * (n - 1) : ℝ)) := by
  have hc2 : 2 ≤ c.card := by omega
  set good : Set (AgentState L K × AgentState L K) :=
    {p | p.1.role = .mcr ∧ p.1.phase.val = 0 ∧
         ((p.2.role = .mcr ∧ p.2.phase.val = 0) ∨ IsAssignable p.2) ∧
         Protocol.Applicable c p.1 p.2} with hgooddef
  have hgood : ∀ pair ∈ good, (NonuniformMajority L K).scheduledStep c pair ∈
      {c' | ExactMajority.mcrCount (L := L) (K := K) c' <
        ExactMajority.mcrCount (L := L) (K := K) c} := by
    intro ⟨s, t⟩ ⟨hs_mcr, hs_phase, ht_cond, happ⟩
    simp only [Set.mem_setOf_eq]
    unfold Protocol.scheduledStep Protocol.stepOrSelf
    rw [if_pos happ]
    rcases ht_cond with ⟨ht_mcr, ht_phase⟩ | ht_assign
    · exact mcrCount_config_decrease_of_phase0_mcr_pair c s t happ hs_phase ht_phase
        hs_mcr ht_mcr
    · exact mcrCount_config_decrease_of_mcr_assignable c s t happ hs_mcr hs_phase ht_assign
  calc ((NonuniformMajority L K).stepDistOrSelf c).toMeasure
          {c' | ExactMajority.mcrCount (L := L) (K := K) c' <
            ExactMajority.mcrCount (L := L) (K := K) c}
      ≥ (c.interactionPMF hc2).toMeasure good :=
        stepDistOrSelf_toMeasure_ge c hc2 _ good hgood
    _ ≥ ENNReal.ofReal
          (((ExactMajority.mcrCount (L := L) (K := K) c *
              (ExactMajority.mcrCount (L := L) (K := K) c - 1) +
              ExactMajority.mcrCount (L := L) (K := K) c *
                assignableCount (L := L) (K := K) c : ℕ) : ℝ) /
            (c.card * (c.card - 1) : ℝ)) :=
        interactionPMF_toMeasure_mcr_combined_ge c hc2 h_phase0
    _ = ENNReal.ofReal
          (((ExactMajority.mcrCount (L := L) (K := K) c *
              (ExactMajority.mcrCount (L := L) (K := K) c - 1) +
              ExactMajority.mcrCount (L := L) (K := K) c *
                assignableCount (L := L) (K := K) c : ℕ) : ℝ) /
            (n * (n - 1) : ℝ)) := by rw [h_card]

/-! ## Gap (A): the invariant-relative milestone engine `MilestonePhaseOn`.

`JansonHitting.MilestonePhase.progress` (JansonHitting.lean L48–51) demands the
per-step rate `≥ p i` **unconditionally** at every config with milestones `<i`
reached and `i` unreached.  For the role split that is false at *adversarial*
configs (`mcrCount = 2, assignableCount = 0` ⟹ combined rate `Θ(1/n²)`), so the
plain engine cannot carry the Chernoff floor `assignableCount ≥ n/5`.

The fix is an **invariant-relative** variant: carry a side predicate `Inv` that
is *one-step closed* from `Inv`-configs (`InvClosed`), require `progress` only at
`Inv`-configs, and start at an `Inv`-config.  Because the chain started at an
`Inv`-config never visits `¬Inv`-configs (mass `0` by `InvClosed`), the MGF
contraction `∫ Φ̃ ≤ exp(−s)·Φ̃` need only hold at `Inv`-configs — exactly where
`progress` is available.  Threading `Inv` through an `_on` geometric-decay closes
the tail.  This mirrors the E2 `PotNonincrOn`/`InvClosed` `_on`-ladder
(`OneSidedCancel.lean`), here lifted to the *Janson milestone* MGF engine.

The MGF *real-analysis* optimisation (`janson_exponential_tail_from_mgf`,
`geometricProductMGF`) depends only on `(k, p)`, so it is reused verbatim through
a throwaway plain `MilestonePhase` with the same `(k, p)` (`toDummyMP`). Only the
kernel-side contraction is re-proved `Inv`-relativised. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Real

attribute [local instance] Classical.propDecidable

open ExactMajority in
/-- An **invariant-relative** milestone phase over a protocol `P`: same milestone
data as `MilestonePhase`, but `progress` is required only at `Inv`-configs, with
`Inv` one-step closed (`inv_closed`).  The downstream tail bound is taken from an
`Inv`-start, so `progress` off `Inv` is never needed. -/
structure MilestonePhaseOn (P : Protocol (AgentState L K)) where
  /-- Number of milestones. -/
  k : ℕ
  /-- The milestone predicates. -/
  milestone : Fin k → Config (AgentState L K) → Prop
  /-- Per-step success probabilities. -/
  p : Fin k → ℝ
  /-- Positivity of the rates. -/
  hp_pos : ∀ i, 0 < p i
  /-- The rates are probabilities. -/
  hp_le_one : ∀ i, p i ≤ 1
  /-- Each milestone, once reached, stays reached. -/
  milestone_monotone : ∀ i c c',
    milestone i c → c' ∈ (P.stepDistOrSelf c).support → milestone i c'
  /-- The carried side invariant. -/
  Inv : Config (AgentState L K) → Prop
  /-- `Inv` is one-step closed: from an `Inv`-config the next-step mass on
  `¬ Inv` is `0`. -/
  inv_closed : ∀ c, Inv c → (P.transitionKernel c) {c' | ¬ Inv c'} = 0
  /-- **Invariant-relative progress.** At every `Inv`-config with milestones
  `< i` reached and `i` not, the next-step mass on `{milestone i}` is `≥ p i`. -/
  progress_on : ∀ i c, Inv c →
    (∀ j < i, milestone j c) → ¬ milestone i c →
    (P.stepDistOrSelf c).toMeasure {c' | milestone i c'} ≥ ENNReal.ofReal (p i)

namespace MilestonePhaseOn

variable {P : Protocol (AgentState L K)}

/-- The postcondition: all milestones reached. -/
def Post (mp : MilestonePhaseOn (L := L) (K := K) P) (c : Config (AgentState L K)) : Prop :=
  ∀ i, mp.milestone i c

/-- Mean waiting time `Σ 1/p_i` (identical to the plain engine's). -/
noncomputable def meanTime (mp : MilestonePhaseOn (L := L) (K := K) P) : ℝ :=
  ∑ i : Fin mp.k, (mp.p i)⁻¹

/-- Minimum rate `⨅ p_i` (identical to the plain engine's). -/
noncomputable def pMin (mp : MilestonePhaseOn (L := L) (K := K) P) : ℝ :=
  ⨅ i : Fin mp.k, mp.p i

/-- A throwaway plain `MilestonePhase` with the **same** `(k, p)` but the
*trivial* milestone `fun _ _ => True` (so `progress`'s antecedent `¬ milestone`
is `¬True = False` — vacuously dischargeable).  Used only to borrow the *pure
real-analysis* MGF optimisation (`pMin`, `meanTime`, `geometricProductMGF`,
`janson_exponential_tail_from_mgf`), which reads only `(k, p, hp_pos,
hp_le_one)` — so `toDummyMP.pMin = mp.pMin` and `.meanTime = mp.meanTime` by
definition.  The kernel-side contraction is proved separately `Inv`-relativised. -/
noncomputable def toDummyMP (mp : MilestonePhaseOn (L := L) (K := K) P) :
    MilestonePhase P where
  k := mp.k
  milestone := fun _ _ => True
  p := mp.p
  hp_pos := mp.hp_pos
  hp_le_one := mp.hp_le_one
  milestone_monotone := fun _ _ _ _ _ => trivial
  progress := fun _ _ _ hnot => absurd trivial hnot

/-- `toDummyMP` preserves `pMin` (both equal `⨅ p_i`). -/
theorem toDummyMP_pMin (mp : MilestonePhaseOn (L := L) (K := K) P) :
    (mp.toDummyMP).pMin = mp.pMin := rfl

/-- `toDummyMP` preserves `meanTime` (both equal `Σ 1/p_i`). -/
theorem toDummyMP_meanTime (mp : MilestonePhaseOn (L := L) (K := K) P) :
    (mp.toDummyMP).meanTime = mp.meanTime := rfl

/-! ### MGF potential for the `_on` engine (mirrors JansonHitting's `private`
machinery, re-derived here since those are not exported). -/

/-- The single MGF factor `(p·e^s)/(1−(1−p)·e^s)`. -/
noncomputable def mgfFactor (mp : MilestonePhaseOn (L := L) (K := K) P) (s : ℝ)
    (i : Fin mp.k) : ℝ :=
  (mp.p i * Real.exp s) / (1 - (1 - mp.p i) * Real.exp s)

theorem mgfFactor_pos (mp : MilestonePhaseOn (L := L) (K := K) P) {s : ℝ}
    (hs_valid : ∀ i, (1 - mp.p i) * Real.exp s < 1) (i : Fin mp.k) :
    0 < mp.mgfFactor s i :=
  div_pos (mul_pos (mp.hp_pos i) (Real.exp_pos s)) (by linarith [hs_valid i])

theorem mgfFactor_ge_one (mp : MilestonePhaseOn (L := L) (K := K) P) {s : ℝ}
    (hs_pos : 0 < s) (hs_valid : ∀ i, (1 - mp.p i) * Real.exp s < 1) (i : Fin mp.k) :
    1 ≤ mp.mgfFactor s i := by
  rw [mgfFactor, le_div_iff₀ (by linarith [hs_valid i]), one_mul]
  have : mp.p i * Real.exp s + (1 - mp.p i) * Real.exp s = Real.exp s := by ring
  linarith [Real.add_one_le_exp s]

/-- Milestones not yet reached at `c`. -/
noncomputable def unreached (mp : MilestonePhaseOn (L := L) (K := K) P)
    (c : Config (AgentState L K)) : Finset (Fin mp.k) :=
  Finset.filter (fun i => ¬ mp.milestone i c) Finset.univ

/-- The partial MGF: product of factors over unreached milestones. -/
noncomputable def partialMGF (mp : MilestonePhaseOn (L := L) (K := K) P) (s : ℝ)
    (c : Config (AgentState L K)) : ℝ :=
  ∏ i ∈ mp.unreached c, mp.mgfFactor s i

theorem partialMGF_pos (mp : MilestonePhaseOn (L := L) (K := K) P) {s : ℝ}
    (hs_valid : ∀ i, (1 - mp.p i) * Real.exp s < 1) (c : Config (AgentState L K)) :
    0 < mp.partialMGF s c :=
  Finset.prod_pos fun i _ => mp.mgfFactor_pos hs_valid i

theorem partialMGF_ge_one_of_not_post (mp : MilestonePhaseOn (L := L) (K := K) P)
    {s : ℝ} (hs_pos : 0 < s) (hs_valid : ∀ i, (1 - mp.p i) * Real.exp s < 1)
    (c : Config (AgentState L K)) (hc : ¬ mp.Post c) :
    1 ≤ mp.partialMGF s c := by
  refine Finset.one_le_prod fun i _ => mp.mgfFactor_ge_one hs_pos hs_valid i

theorem partialMGF_eq_full_of_none_reached (mp : MilestonePhaseOn (L := L) (K := K) P)
    (s : ℝ) (c₀ : Config (AgentState L K)) (hPre : ∀ i, ¬ mp.milestone i c₀) :
    mp.partialMGF s c₀ = ∏ i : Fin mp.k, mp.mgfFactor s i := by
  have h_eq : mp.unreached c₀ = Finset.univ := by
    ext i
    simp only [unreached, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
    exact hPre i
  rw [partialMGF, h_eq]

/-- The truncated potential: `0` on `Post`, else `ofReal (partialMGF)`. -/
noncomputable def truncMGF (mp : MilestonePhaseOn (L := L) (K := K) P) (s : ℝ) :
    Config (AgentState L K) → ℝ≥0∞ :=
  fun c => if mp.Post c then 0 else ENNReal.ofReal (mp.partialMGF s c)

theorem truncMGF_measurable (mp : MilestonePhaseOn (L := L) (K := K) P) (s : ℝ) :
    Measurable (mp.truncMGF s) :=
  fun _ _ => DiscreteMeasurableSpace.forall_measurableSet _

/-- Monotonicity along the kernel support: `partialMGF` does not increase. -/
theorem partialMGF_mono_of_support (mp : MilestonePhaseOn (L := L) (K := K) P)
    {s : ℝ} (hs_pos : 0 < s) (hs_valid : ∀ i, (1 - mp.p i) * Real.exp s < 1)
    (c c' : Config (AgentState L K))
    (hsupp : c' ∈ (P.stepDistOrSelf c).support) :
    mp.partialMGF s c' ≤ mp.partialMGF s c := by
  refine Finset.prod_le_prod_of_subset_of_one_le ?_ ?_ ?_
  · intro i hi
    simp only [unreached, Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    exact fun h => hi (mp.milestone_monotone i c c' h hsupp)
  · exact fun i _ => (mp.mgfFactor_pos hs_valid i).le
  · exact fun i _ _ => mp.mgfFactor_ge_one hs_pos hs_valid i

/-- When milestone `j` is reached at `c'`, `partialMGF` drops the `j`-th factor. -/
theorem partialMGF_drop_reached (mp : MilestonePhaseOn (L := L) (K := K) P)
    {s : ℝ} (hs_pos : 0 < s) (hs_valid : ∀ i, (1 - mp.p i) * Real.exp s < 1)
    (c c' : Config (AgentState L K)) (j : Fin mp.k)
    (hj_unreached : j ∈ mp.unreached c) (hj_reached : mp.milestone j c')
    (hsupp : c' ∈ (P.stepDistOrSelf c).support) :
    mp.partialMGF s c' ≤ mp.partialMGF s c / mp.mgfFactor s j := by
  rw [le_div_iff₀ (mp.mgfFactor_pos hs_valid j)]
  have h_sub : mp.unreached c' ⊆ (mp.unreached c).erase j := by
    intro i hi
    simp only [unreached, Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    rw [Finset.mem_erase]
    refine ⟨fun h_eq => by rw [h_eq] at hi; exact hi hj_reached, ?_⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact fun h => hi (mp.milestone_monotone i c c' h hsupp)
  have h_prod_sub : mp.partialMGF s c' ≤ ∏ i ∈ (mp.unreached c).erase j, mp.mgfFactor s i :=
    Finset.prod_le_prod_of_subset_of_one_le h_sub
      (fun i _ => (mp.mgfFactor_pos hs_valid i).le)
      (fun i _ _ => mp.mgfFactor_ge_one hs_pos hs_valid i)
  calc mp.partialMGF s c' * mp.mgfFactor s j
      ≤ (∏ i ∈ (mp.unreached c).erase j, mp.mgfFactor s i) * mp.mgfFactor s j := by
        gcongr; exact (mp.mgfFactor_pos hs_valid j).le
    _ = ∏ i ∈ insert j ((mp.unreached c).erase j), mp.mgfFactor s i := by
        rw [Finset.prod_insert (by simp [Finset.mem_erase])]; ring
    _ = mp.partialMGF s c := by rw [partialMGF]; congr 1; exact Finset.insert_erase hj_unreached

/-! ### `Post` absorbing and the first-unreached selector (shared with the
plain engine but re-derived for the `_on` data). -/

/-- `Post` is absorbing under the kernel: once all milestones hold they stay. -/
theorem post_absorbing (mp : MilestonePhaseOn (L := L) (K := K) P)
    (c : Config (AgentState L K)) (hPost : mp.Post c) :
    (P.transitionKernel c) {c' | mp.Post c'} = 1 := by
  change (P.stepDistOrSelf c).toMeasure {c' | mp.Post c'} = 1
  rw [(P.stepDistOrSelf c).toMeasure_apply_eq_one_iff
    (DiscreteMeasurableSpace.forall_measurableSet _)]
  exact fun c' hc' i => mp.milestone_monotone i c c' (hPost i) hc'

/-- The unreached set is nonempty when `Post` fails. -/
theorem unreached_nonempty_of_not_post (mp : MilestonePhaseOn (L := L) (K := K) P)
    (c : Config (AgentState L K)) (hc : ¬ mp.Post c) : (mp.unreached c).Nonempty := by
  rw [Finset.nonempty_iff_ne_empty]
  intro h; apply hc; intro i; by_contra hi
  have : i ∈ mp.unreached c := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩
  rw [h] at this; simp at this

/-- The minimal unreached milestone index. -/
noncomputable def firstUnreached (mp : MilestonePhaseOn (L := L) (K := K) P)
    (c : Config (AgentState L K)) (hne : (mp.unreached c).Nonempty) : Fin mp.k :=
  (mp.unreached c).min' hne

theorem firstUnreached_unhit (mp : MilestonePhaseOn (L := L) (K := K) P)
    (c : Config (AgentState L K)) (hc : ¬ mp.Post c) :
    mp.firstUnreached c (mp.unreached_nonempty_of_not_post c hc) ∈ mp.unreached c :=
  Finset.min'_mem _ _

theorem firstUnreached_minimal (mp : MilestonePhaseOn (L := L) (K := K) P)
    (c : Config (AgentState L K)) (hc : ¬ mp.Post c) (i : Fin mp.k)
    (hi : i < mp.firstUnreached c (mp.unreached_nonempty_of_not_post c hc)) :
    mp.milestone i c := by
  by_contra h_not
  have h_mem : i ∈ mp.unreached c := Finset.mem_filter.mpr ⟨Finset.mem_univ _, h_not⟩
  exact absurd (lt_of_lt_of_le hi (Finset.min'_le _ _ h_mem)) (lt_irrefl _)

/-! ### The algebraic MGF contraction identity (re-derived). -/

theorem mgf_contraction_identity (p s : ℝ) (hp_pos : 0 < p)
    (hs_valid : (1 - p) * Real.exp s < 1) :
    (1 - p) + p * ((1 - (1 - p) * Real.exp s) / (p * Real.exp s)) = Real.exp (-s) := by
  have hp_ne : p ≠ 0 := hp_pos.ne'
  have hexp_ne : Real.exp s ≠ 0 := (Real.exp_pos s).ne'
  field_simp
  rw [Real.exp_neg]; field_simp [hp_ne, hexp_ne]; ring

/-! ### The one-step contraction (where `progress_on` enters, at `Inv`-configs). -/

/-- Pointwise a.e. bound on `partialMGF` after one step, at the first-unreached
milestone `j`.  Identical to JansonHitting's, no `progress` used here. -/
theorem partialMGF_pointwise_bound (mp : MilestonePhaseOn (L := L) (K := K) P)
    {s : ℝ} (hs_pos : 0 < s) (hs_valid : ∀ i, (1 - mp.p i) * Real.exp s < 1)
    (c : Config (AgentState L K)) (j : Fin mp.k) (hj_unreached : j ∈ mp.unreached c) :
    ∀ᵐ c' ∂(P.stepDistOrSelf c).toMeasure,
      ENNReal.ofReal (mp.partialMGF s c') ≤
        if mp.milestone j c' then
          ENNReal.ofReal (mp.partialMGF s c / mp.mgfFactor s j)
        else ENNReal.ofReal (mp.partialMGF s c) := by
  rw [ae_iff]
  rw [PMF.toMeasure_apply_eq_zero_iff (p := P.stepDistOrSelf c)
    (DiscreteMeasurableSpace.forall_measurableSet _)]
  rw [Set.disjoint_left]
  intro c' hsupp hbad
  apply hbad
  by_cases hm : mp.milestone j c'
  · simp only [hm, ite_true]
    exact ENNReal.ofReal_le_ofReal
      (mp.partialMGF_drop_reached hs_pos hs_valid c c' j hj_unreached hm hsupp)
  · simp only [hm, ite_false]
    exact ENNReal.ofReal_le_ofReal
      (mp.partialMGF_mono_of_support hs_pos hs_valid c c' hsupp)

/-- **One-step contraction** of the ENNReal partial MGF — at an `Inv`-config with
`¬ Post`.  This is the only place `progress_on` is consumed (and `Inv c` is the
exactly-available extra hypothesis). -/
theorem partialMGF_one_step_contraction_on (mp : MilestonePhaseOn (L := L) (K := K) P)
    {s : ℝ} (hs_pos : 0 < s) (hs_valid : ∀ i, (1 - mp.p i) * Real.exp s < 1)
    (c : Config (AgentState L K)) (hInv : mp.Inv c) (hc : ¬ mp.Post c) :
    ∫⁻ c', ENNReal.ofReal (mp.partialMGF s c') ∂(P.transitionKernel c) ≤
      ENNReal.ofReal (Real.exp (-s)) * ENNReal.ofReal (mp.partialMGF s c) := by
  set j := mp.firstUnreached c (mp.unreached_nonempty_of_not_post c hc) with hj_def
  have hj_in : j ∈ mp.unreached c := mp.firstUnreached_unhit c hc
  have hj_minimal : ∀ i < j, mp.milestone i c := mp.firstUnreached_minimal c hc
  set Mj := {c' : Config (AgentState L K) | mp.milestone j c'} with hMj_def
  have hMj_meas : MeasurableSet Mj := DiscreteMeasurableSpace.forall_measurableSet _
  set Φc := mp.partialMGF s c with hΦc_def
  set fj := mp.mgfFactor s j with hfj_def
  have hΦc_pos : 0 < Φc := mp.partialMGF_pos hs_valid c
  have hfj_pos : 0 < fj := mp.mgfFactor_pos hs_valid j
  have hfj_ge_one : 1 ≤ fj := mp.mgfFactor_ge_one hs_pos hs_valid j
  change ∫⁻ c', ENNReal.ofReal (mp.partialMGF s c') ∂(P.stepDistOrSelf c).toMeasure ≤ _
  have h_bound := mp.partialMGF_pointwise_bound hs_pos hs_valid c j hj_in
  calc ∫⁻ c', ENNReal.ofReal (mp.partialMGF s c') ∂(P.stepDistOrSelf c).toMeasure
      ≤ ∫⁻ c', (if mp.milestone j c' then ENNReal.ofReal (Φc / fj)
          else ENNReal.ofReal Φc) ∂(P.stepDistOrSelf c).toMeasure :=
        lintegral_mono_ae h_bound
    _ = (∫⁻ c' in Mj, ENNReal.ofReal (Φc / fj) ∂(P.stepDistOrSelf c).toMeasure) +
        (∫⁻ c' in Mjᶜ, ENNReal.ofReal Φc ∂(P.stepDistOrSelf c).toMeasure) := by
        rw [← lintegral_add_compl _ hMj_meas]
        congr 1
        · refine lintegral_congr_ae ?_
          filter_upwards [ae_restrict_mem hMj_meas] with c' hc'
          simp only [Set.mem_setOf_eq, Mj] at hc'; simp [hc']
        · refine lintegral_congr_ae ?_
          filter_upwards [ae_restrict_mem hMj_meas.compl] with c' hc'
          simp only [Set.mem_compl_iff, Set.mem_setOf_eq, Mj] at hc'; simp [hc']
    _ = ENNReal.ofReal (Φc / fj) * (P.stepDistOrSelf c).toMeasure Mj +
        ENNReal.ofReal Φc * (P.stepDistOrSelf c).toMeasure Mjᶜ := by
        rw [lintegral_const, Measure.restrict_apply_univ,
            lintegral_const, Measure.restrict_apply_univ]
    _ ≤ ENNReal.ofReal (Real.exp (-s)) * ENNReal.ofReal Φc := by
        set q := (P.stepDistOrSelf c).toMeasure Mj with hq_def
        set qc := (P.stepDistOrSelf c).toMeasure Mjᶜ with hqc_def
        have hq_ge : q ≥ ENNReal.ofReal (mp.p j) := by
          have h_unhit : ¬ mp.milestone j c := (Finset.mem_filter.mp hj_in).2
          exact mp.progress_on j c hInv hj_minimal h_unhit
        haveI : IsProbabilityMeasure (P.stepDistOrSelf c).toMeasure :=
          PMF.toMeasure.isProbabilityMeasure _
        have hq_le_one : q ≤ 1 := by
          calc q ≤ (P.stepDistOrSelf c).toMeasure Set.univ := measure_mono (Set.subset_univ _)
            _ = 1 := measure_univ
        have hq_ne_top : q ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top hq_le_one
        have hqc_eq : qc = 1 - q := by
          have h_compl := measure_compl hMj_meas hq_ne_top
          rw [show (P.stepDistOrSelf c).toMeasure Set.univ = 1 from measure_univ] at h_compl
          exact h_compl
        set qr := q.toReal with hqr_def
        have hqr_nonneg : 0 ≤ qr := ENNReal.toReal_nonneg
        have hqr_le_one : qr ≤ 1 := by
          have := ENNReal.toReal_mono ENNReal.one_ne_top hq_le_one
          rwa [ENNReal.toReal_one] at this
        have hq_ofReal : q = ENNReal.ofReal qr := (ENNReal.ofReal_toReal hq_ne_top).symm
        have hpj_le_qr : mp.p j ≤ qr := by
          have h1 : ENNReal.ofReal (mp.p j) ≤ ENNReal.ofReal qr := by rwa [← hq_ofReal]
          exact (ENNReal.ofReal_le_ofReal_iff hqr_nonneg).mp h1
        have h1mqr_nonneg : 0 ≤ 1 - qr := by linarith
        have hqc_ofReal : qc = ENNReal.ofReal (1 - qr) := by
          rw [hqc_eq, hq_ofReal,
              show (1 : ℝ≥0∞) = ENNReal.ofReal 1 from ENNReal.ofReal_one.symm,
              ← ENNReal.ofReal_sub 1 hqr_nonneg]
        have hΦc_div_fj_nonneg : 0 ≤ Φc / fj := div_nonneg hΦc_pos.le hfj_pos.le
        have hexp_neg_s_nonneg : (0 : ℝ) ≤ Real.exp (-s) := (Real.exp_pos _).le
        have lhs_eq : ENNReal.ofReal (Φc / fj) * q + ENNReal.ofReal Φc * qc =
            ENNReal.ofReal (Φc / fj * qr + Φc * (1 - qr)) := by
          rw [hq_ofReal, hqc_ofReal,
              ← ENNReal.ofReal_mul hΦc_div_fj_nonneg,
              ← ENNReal.ofReal_mul hΦc_pos.le,
              ← ENNReal.ofReal_add (mul_nonneg hΦc_div_fj_nonneg hqr_nonneg)
                (mul_nonneg hΦc_pos.le h1mqr_nonneg)]
        have rhs_eq : ENNReal.ofReal (Real.exp (-s)) * ENNReal.ofReal Φc =
            ENNReal.ofReal (Real.exp (-s) * Φc) := by
          rw [← ENNReal.ofReal_mul hexp_neg_s_nonneg]
        rw [lhs_eq, rhs_eq]
        apply ENNReal.ofReal_le_ofReal
        have hpj_pos := mp.hp_pos j
        have h_factor : Φc / fj * qr + Φc * (1 - qr) = Φc * ((1 - qr) + qr / fj) := by
          field_simp; ring
        have h_rhs_factor : Real.exp (-s) * Φc = Φc * Real.exp (-s) := by ring
        rw [h_factor, h_rhs_factor]
        apply mul_le_mul_of_nonneg_left _ hΦc_pos.le
        have h_inv_fj : (1 - (1 - mp.p j) * Real.exp s) / (mp.p j * Real.exp s) = 1 / fj := by
          rw [hfj_def, mgfFactor]; field_simp
        have h_identity := mgf_contraction_identity (mp.p j) s hpj_pos (hs_valid j)
        rw [h_inv_fj] at h_identity
        have h_identity' : 1 - mp.p j * (1 - 1 / fj) = Real.exp (-s) := by linarith
        have h_rewrite : (1 - qr) + qr / fj = 1 - qr * (1 - 1 / fj) := by field_simp; ring
        rw [h_rewrite, ← h_identity']
        have h_coeff_nonneg : 0 ≤ 1 - 1 / fj := by
          rw [sub_nonneg, div_le_one hfj_pos]; exact hfj_ge_one
        linarith [mul_le_mul_of_nonneg_right hpj_le_qr h_coeff_nonneg]

/-- **Full one-step contraction at an `Inv`-config** (handles `Post` and `¬Post`):
`∫ truncMGF dK(c) ≤ exp(−s)·truncMGF(c)`.  On `Post c` the LHS is `0` (absorbing);
on `¬Post c` it is `partialMGF_one_step_contraction_on`. -/
theorem truncMGF_contracts_on (mp : MilestonePhaseOn (L := L) (K := K) P)
    {s : ℝ} (hs_pos : 0 < s) (hs_valid : ∀ i, (1 - mp.p i) * Real.exp s < 1)
    (c : Config (AgentState L K)) (hInv : mp.Inv c) :
    ∫⁻ c', mp.truncMGF s c' ∂(P.transitionKernel c) ≤
      ENNReal.ofReal (Real.exp (-s)) * mp.truncMGF s c := by
  by_cases hc : mp.Post c
  · simp only [truncMGF, if_pos hc, mul_zero]
    have h_ae : (fun c' => if mp.Post c' then (0 : ℝ≥0∞)
        else ENNReal.ofReal (mp.partialMGF s c')) =ᵐ[P.transitionKernel c] 0 := by
      rw [Filter.eventuallyEq_iff_exists_mem]
      refine ⟨{y | mp.Post y}, ?_, fun y hy => if_pos hy⟩
      rw [mem_ae_iff]
      have h1 := mp.post_absorbing c hc
      have h_meas : MeasurableSet {y : Config (AgentState L K) | mp.Post y} :=
        DiscreteMeasurableSpace.forall_measurableSet _
      calc P.transitionKernel c {y | mp.Post y}ᶜ
          = P.transitionKernel c Set.univ - P.transitionKernel c {y | mp.Post y} :=
            measure_compl h_meas (by rw [h1]; exact ENNReal.one_ne_top)
        _ = 1 - 1 := by rw [measure_univ, h1]
        _ = 0 := tsub_self _
    exact le_of_eq (lintegral_eq_zero_of_ae_eq_zero h_ae)
  · simp only [truncMGF, if_neg hc]
    calc ∫⁻ c', (if mp.Post c' then 0 else ENNReal.ofReal (mp.partialMGF s c'))
            ∂(P.transitionKernel c)
        ≤ ∫⁻ c', ENNReal.ofReal (mp.partialMGF s c') ∂(P.transitionKernel c) := by
          refine lintegral_mono fun c' => ?_
          by_cases hc' : mp.Post c' <;> simp [hc']
      _ ≤ ENNReal.ofReal (Real.exp (-s)) * ENNReal.ofReal (mp.partialMGF s c) :=
        mp.partialMGF_one_step_contraction_on hs_pos hs_valid c hInv hc

/-- **Inv-relative geometric decay.**  From an `Inv`-start, the `t`-step
expectation of `truncMGF` contracts geometrically.  The contraction need only
hold at `Inv`-configs (`truncMGF_contracts_on`), because by `inv_closed` the
chain stays in `Inv` (mass `0` off `Inv`).  Mirrors `lintegral_geometric_decay`
relativised to the reachable `Inv`-set. -/
theorem lintegral_geometric_decay_on (mp : MilestonePhaseOn (L := L) (K := K) P)
    {s : ℝ} (hs_pos : 0 < s) (hs_valid : ∀ i, (1 - mp.p i) * Real.exp s < 1)
    (t : ℕ) (c : Config (AgentState L K)) (hInv : mp.Inv c) :
    ∫⁻ c', mp.truncMGF s c' ∂((P.transitionKernel ^ t) c) ≤
      ENNReal.ofReal (Real.exp (-s)) ^ t * mp.truncMGF s c := by
  induction t generalizing c with
  | zero =>
    simp only [pow_zero, one_mul]
    change ∫⁻ c', mp.truncMGF s c' ∂(Kernel.id c) ≤ mp.truncMGF s c
    rw [Kernel.id_apply, lintegral_dirac' c (mp.truncMGF_measurable s)]
  | succ t ih =>
    change ∫⁻ c', mp.truncMGF s c' ∂(((P.transitionKernel ^ t) ∘ₖ P.transitionKernel) c) ≤ _
    rw [Kernel.lintegral_comp _ _ c (mp.truncMGF_measurable s)]
    have hclosed : (P.transitionKernel c) {x | ¬ mp.Inv x} = 0 := mp.inv_closed c hInv
    calc ∫⁻ b, ∫⁻ c', mp.truncMGF s c' ∂((P.transitionKernel ^ t) b) ∂(P.transitionKernel c)
        ≤ ∫⁻ b, ENNReal.ofReal (Real.exp (-s)) ^ t * mp.truncMGF s b
            ∂(P.transitionKernel c) := by
          refine lintegral_mono_ae ?_
          rw [Filter.eventually_iff_exists_mem]
          refine ⟨{x | mp.Inv x}, ?_, fun b hb => ih b hb⟩
          rw [mem_ae_iff]
          have hco : ({x | mp.Inv x}ᶜ : Set (Config (AgentState L K))) = {x | ¬ mp.Inv x} := by
            ext y; simp only [Set.mem_compl_iff, Set.mem_setOf_eq]
          rw [hco]; exact hclosed
      _ = ENNReal.ofReal (Real.exp (-s)) ^ t *
            ∫⁻ b, mp.truncMGF s b ∂(P.transitionKernel c) :=
          lintegral_const_mul _ (mp.truncMGF_measurable s)
      _ ≤ ENNReal.ofReal (Real.exp (-s)) ^ t *
            (ENNReal.ofReal (Real.exp (-s)) * mp.truncMGF s c) := by
          gcongr; exact mp.truncMGF_contracts_on hs_pos hs_valid c hInv
      _ = ENNReal.ofReal (Real.exp (-s)) ^ (t + 1) * mp.truncMGF s c := by
          rw [pow_succ, mul_assoc]

/-! ### The Inv-relative milestone tail and hitting-time bound. -/

/-- `{¬Post} ⊆ {1 ≤ truncMGF}`. -/
theorem not_post_subset_ge_one (mp : MilestonePhaseOn (L := L) (K := K) P)
    {s : ℝ} (hs_pos : 0 < s) (hs_valid : ∀ i, (1 - mp.p i) * Real.exp s < 1) :
    {c | ¬ mp.Post c} ⊆ {c | 1 ≤ mp.truncMGF s c} := by
  intro c hc
  simp only [Set.mem_setOf_eq] at hc ⊢
  rw [show mp.truncMGF s c = ENNReal.ofReal (mp.partialMGF s c) from if_neg hc,
    ← ENNReal.ofReal_one]
  exact ENNReal.ofReal_le_ofReal (mp.partialMGF_ge_one_of_not_post hs_pos hs_valid c hc)

/-- **Inv-relative milestone tail via MGF.**  From an `Inv`-start `c₀` with no
milestone reached, the `t`-step mass on `¬Post` is bounded by the geometric MGF
decay.  This is the `_on` analogue of `milestone_tail_bound_via_mgf`. -/
theorem milestone_tail_bound_via_mgf_on (mp : MilestonePhaseOn (L := L) (K := K) P)
    (c₀ : Config (AgentState L K)) (hInv₀ : mp.Inv c₀)
    (hPre : ∀ i : Fin mp.k, ¬ mp.milestone i c₀)
    {s : ℝ} (hs_pos : 0 < s) (hs_valid : ∀ i, (1 - mp.p i) * Real.exp s < 1) (t : ℕ) :
    (P.transitionKernel ^ t) c₀ {c | ¬ mp.Post c} ≤
      ENNReal.ofReal (Real.exp (-s * t) *
        ∏ i : Fin mp.k, mp.mgfFactor s i) := by
  by_cases hk : mp.k = 0
  · have hempty : {c : Config (AgentState L K) | ¬ mp.Post c} = ∅ := by
      ext c
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_not, Post]
      intro i; exact absurd i.2 (by omega)
    simp [hempty]
  have hk_pos : 0 < mp.k := Nat.pos_of_ne_zero hk
  haveI : Nonempty (Fin mp.k) := ⟨⟨0, hk_pos⟩⟩
  have hexp_s_pos : (0 : ℝ) < Real.exp (-s) := Real.exp_pos _
  have hNotPost : ¬ mp.Post c₀ := fun h => absurd (h ⟨0, hk_pos⟩) (hPre ⟨0, hk_pos⟩)
  have hmarkov := mul_meas_ge_le_lintegral₀
    (μ := (P.transitionKernel ^ t) c₀) (mp.truncMGF_measurable s).aemeasurable (1 : ℝ≥0∞)
  simp only [one_mul] at hmarkov
  calc (P.transitionKernel ^ t) c₀ {c | ¬ mp.Post c}
      ≤ (P.transitionKernel ^ t) c₀ {c | 1 ≤ mp.truncMGF s c} :=
        measure_mono (mp.not_post_subset_ge_one hs_pos hs_valid)
    _ ≤ ∫⁻ c', mp.truncMGF s c' ∂((P.transitionKernel ^ t) c₀) := hmarkov
    _ ≤ ENNReal.ofReal (Real.exp (-s)) ^ t * mp.truncMGF s c₀ :=
        mp.lintegral_geometric_decay_on hs_pos hs_valid t c₀ hInv₀
    _ = ENNReal.ofReal (Real.exp (-s * t) * ∏ i : Fin mp.k, mp.mgfFactor s i) := by
        rw [show mp.truncMGF s c₀ = ENNReal.ofReal (mp.partialMGF s c₀) from if_neg hNotPost,
          mp.partialMGF_eq_full_of_none_reached s c₀ hPre,
          ← ENNReal.ofReal_pow hexp_s_pos.le, ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        rw [show -s * (t : ℝ) = (t : ℝ) * (-s) from by ring, Real.exp_nat_mul]

/-- `geometricProductMGF` (on the dummy `(k,p)`) equals `∏ mgfFactor`. -/
theorem geometricProductMGF_eq_prod_mgfFactor
    (mp : MilestonePhaseOn (L := L) (K := K) P) (s : ℝ) :
    geometricProductMGF mp.k mp.p s = ∏ i : Fin mp.k, mp.mgfFactor s i := rfl

/-- `pMin` is positive when there is at least one milestone. -/
theorem pMin_pos (mp : MilestonePhaseOn (L := L) (K := K) P) (hk : 0 < mp.k) :
    0 < mp.pMin := by
  haveI : Nonempty (Fin mp.k) := ⟨⟨0, hk⟩⟩
  obtain ⟨j₀, _, hj₀⟩ := Finset.exists_min_image Finset.univ mp.p
    ⟨⟨0, hk⟩, Finset.mem_univ _⟩
  have h_eq : ⨅ i, mp.p i = mp.p j₀ := le_antisymm
    (ciInf_le ⟨0, fun x ⟨j, hj⟩ => hj ▸ (mp.hp_pos j).le⟩ j₀)
    (le_ciInf fun i => hj₀ i (Finset.mem_univ i))
  rw [pMin, h_eq]; exact mp.hp_pos j₀

theorem pMin_le (mp : MilestonePhaseOn (L := L) (K := K) P) (i : Fin mp.k) :
    mp.pMin ≤ mp.p i :=
  ciInf_le ⟨0, fun _ ⟨j, hj⟩ => hj ▸ (mp.hp_pos j).le⟩ i

/-- **Milestone hitting-time concentration (invariant-relative, Gap A).**  From
an `Inv`-start `c₀` with no milestone reached, the probability of NOT completing
all milestones within `λ·meanTime` steps is at most
`exp(−pMin·meanTime·(λ−1−ln λ))` — the **same** Janson tail as the plain engine,
but with `progress` required only along the (closed) `Inv`-set.  The MGF
real-analysis optimisation is borrowed from `janson_exponential_tail_from_mgf`
via the `(k,p)`-identical `toDummyMP`. -/
theorem milestone_hitting_time_bound_on (mp : MilestonePhaseOn (L := L) (K := K) P)
    (c₀ : Config (AgentState L K)) (hInv₀ : mp.Inv c₀)
    (hPre : ∀ i : Fin mp.k, ¬ mp.milestone i c₀)
    (lam : ℝ) (hlam : 1 ≤ lam)
    (t : ℕ) (ht : lam * mp.meanTime ≤ (t : ℝ)) :
    (P.transitionKernel ^ t) c₀ {c | ¬ mp.Post c} ≤
      ENNReal.ofReal (Real.exp (-mp.pMin * mp.meanTime * (lam - 1 - Real.log lam))) := by
  by_cases hk : mp.k = 0
  · have hempty : {c : Config (AgentState L K) | ¬ mp.Post c} = ∅ := by
      ext c
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_not, Post]
      intro i; exact absurd i.2 (by omega)
    simp [hempty]
  by_cases hlam_eq : lam = 1
  · have hzero : -mp.pMin * mp.meanTime * (lam - 1 - Real.log lam) = 0 := by
      rw [hlam_eq, Real.log_one]; ring
    rw [hzero, Real.exp_zero, ENNReal.ofReal_one]
    have hMK : ∀ s : ℕ, IsMarkovKernel (P.transitionKernel ^ s) := by
      intro s; induction s with
      | zero => rw [pow_zero]
                exact inferInstanceAs (IsMarkovKernel (Kernel.id : Kernel (Config (AgentState L K)) _))
      | succ s ih => haveI := ih; rw [pow_succ]
                     exact inferInstanceAs (IsMarkovKernel ((P.transitionKernel ^ s) ∘ₖ _))
    haveI := hMK t
    haveI : IsProbabilityMeasure ((P.transitionKernel ^ t) c₀) :=
      IsMarkovKernel.isProbabilityMeasure _
    calc (P.transitionKernel ^ t) c₀ {c | ¬ mp.Post c}
        ≤ (P.transitionKernel ^ t) c₀ Set.univ := measure_mono (Set.subset_univ _)
      _ ≤ 1 := prob_le_one
  · have hlam_gt : 1 < lam := lt_of_le_of_ne hlam (Ne.symm hlam_eq)
    have hk_pos : 0 < mp.k := Nat.pos_of_ne_zero hk
    set s : ℝ := mp.pMin * (1 - 1 / lam) with hs_def
    have hpmin_pos : 0 < mp.pMin := mp.pMin_pos hk_pos
    have hs_pos : 0 < s := by
      apply mul_pos hpmin_pos
      have : 1 / lam < 1 := by rw [div_lt_one (by linarith)]; exact hlam_gt
      linarith
    have hs_valid : ∀ i, (1 - mp.p i) * Real.exp s < 1 := by
      intro i
      have hsi : s ≤ mp.p i := by
        calc s = mp.pMin * (1 - 1 / lam) := hs_def
          _ ≤ mp.pMin * 1 := by
              apply mul_le_mul_of_nonneg_left _ hpmin_pos.le
              linarith [div_pos one_pos (show (0:ℝ) < lam by linarith)]
          _ = mp.pMin := mul_one _
          _ ≤ mp.p i := mp.pMin_le i
      have hne : (-s : ℝ) ≠ 0 := by linarith
      calc (1 - mp.p i) * Real.exp s
          ≤ (1 - s) * Real.exp s := by
            apply mul_le_mul_of_nonneg_right _ (Real.exp_pos s).le; linarith
        _ < 1 := by
            have h1 : 1 - s < Real.exp (-s) := by linarith [Real.add_one_lt_exp hne]
            have h2 := mul_lt_mul_of_pos_right h1 (Real.exp_pos s)
            rwa [← Real.exp_add, neg_add_cancel, Real.exp_zero] at h2
    -- Borrow the pure MGF optimisation from the dummy `(k,p)`-identical plain phase.
    have h_opt := janson_exponential_tail_from_mgf mp.toDummyMP lam hlam (t : ℝ) ht s hs_def
    rw [mp.toDummyMP_meanTime, mp.toDummyMP_pMin] at h_opt
    have h_tail := mp.milestone_tail_bound_via_mgf_on c₀ hInv₀ hPre hs_pos hs_valid t
    -- `toDummyMP.k = mp.k`, `toDummyMP.p = mp.p` (rfl), so its geometricProductMGF = ∏ mgfFactor.
    have hkp : geometricProductMGF mp.toDummyMP.k mp.toDummyMP.p s =
        ∏ i : Fin mp.k, mp.mgfFactor s i := mp.geometricProductMGF_eq_prod_mgfFactor s
    rw [hkp] at h_opt
    exact le_trans h_tail (ENNReal.ofReal_le_ofReal h_opt)

end MilestonePhaseOn

end RoleSplitConcentration
end ExactMajority
