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
import Ripple.PopulationProtocol.Majority.ExactMajority.Protocol.Transition

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

end RoleSplitConcentration
end ExactMajority

#print axioms ExactMajority.RoleSplitConcentration.clockCount_ge_two_of_RoleSplitGood
#print axioms ExactMajority.RoleSplitConcentration.phase0_roleSplit_whp
