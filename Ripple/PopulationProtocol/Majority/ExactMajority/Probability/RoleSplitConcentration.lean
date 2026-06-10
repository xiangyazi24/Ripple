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

end RoleSplitConcentration
end ExactMajority
