/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Phase 5 — Reserve sampling convergence + sampled-class concentration (Doty §7.1, Lemma 7.1)

This file assembles the Phase-5 `PhaseConvergenceW` (Lemma 7.1) on top of the
`ReserveSampling.lean` machinery and adds the **sampled-class concentration** — the
genuinely new, quantitative side of Lemma 7.1 that Phase 6 consumes.

## The staticity finding (the load-bearing fact)

The paper's footnote 11 (§7.1) states explicitly *why* sampling (Phase 5) and splitting
(Phase 6) are separated into two phases: so that the **Main agents keep a fixed exponent
distribution while the Reserves sample it**.  We verify this at the protocol level:

> **`Phase5Transition` never changes any agent's `bias`.**

`Phase5Transition` only ever (a) writes a *Reserve's* `hour` (the sample field) and
(b) runs the clock counter subroutine on *clocks* (which preserves `bias` for phase ≥ 5).
A Main's `bias` is therefore frozen throughout Phase 5.  Consequently the **biased-Main
exponent-class profile is a deterministic invariant of Phase 5** (`biasedMainClassU` is
conserved by every kernel step on the phase-5 window), and each Reserve's sample is an
independent draw against this *static* class profile.

## The concentration design (sum-of-independent-indicators Chernoff)

With the Main class profile static, the sampled-Reserve class counts `R_{−i}` are sums of
independent indicators: under the uniform-pair kernel the first biased Main a Reserve meets
is ~uniform over the biased-Main pool, so each newly-sampled Reserve lands in class `−i`
with probability `class_i / biasedTotal`.  The per-step drift of the sampled-class-`i`
deficit potential is therefore the standard `WindowConcentration` exponential-MGF
contraction (in-house machinery; no external Chernoff axiom).  The paper's `−l` vs `−(l+1)`
case split (Lemma 7.2's two cases) selects *which* static class fraction is ≥ the needed
floor (`0.18|R|` resp. `0.58|R|`); both are instances of the same concentration with
different target classes.

This file delivers:
* the staticity theorems (Main bias frozen ⟹ class profile conserved);
* the sampled-class / biased-Main class count infrastructure;
* the `ReserveSampleGood` predicate (all-sampled ∧ a sampled-class floor) and the assembled
  `phase5Convergence` `PhaseConvergenceW`, with the all-sampled side discharged by
  `ReserveSampling.phase5SampledConvergence` and the class-concentration floor carried as the
  honest in-house-MGF input (the precise campaign hook recorded in the report).

NEW file; no existing file is edited; no sorry/admit/axiom/native_decide.
-/

import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.ReserveSampling

namespace ExactMajority

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace Phase5Convergence

open ReserveSampling

variable {L K : ℕ}

attribute [local instance] Classical.propDecidable

/-! ## Part A — staticity: `Phase5Transition` freezes every agent's `bias`. -/

/-- `phaseInit` preserves `bias` for any target phase `p` with `p.val ≥ 5` (only the
phase-{1,2,3} inits ever rewrite `bias`, and those are `< 5`).  Local copy of the protocol's
`private` lemma. -/
theorem phaseInit_bias_ge_five (p : Fin 11) (a : AgentState L K) (hp : 5 ≤ p.val) :
    (phaseInit L K p a).bias = a.bias := by
  set_option linter.unusedSimpArgs false in
  fin_cases p <;> simp_all (config := { decide := false }) <;>
    simp [phaseInit, enterPhase10] <;> split_ifs <;> simp [enterPhase10]

/-- `advancePhaseWithInit` preserves `bias` for an agent at phase ≥ 5 (advancePhase keeps
bias; the post-advance `phaseInit` lands at a phase `≥ 6 ≥ 5`, so it preserves bias too —
unless capped at phase 10, where `phaseInit` at 10 = `enterPhase10`, which also preserves
bias). -/
theorem advancePhaseWithInit_bias_ge_five (a : AgentState L K) (ha : 5 ≤ a.phase.val) :
    (advancePhaseWithInit L K a).bias = a.bias := by
  unfold advancePhaseWithInit
  have hadv_bias : (advancePhase L K a).bias = a.bias := by
    unfold advancePhase; split <;> rfl
  have hadv_phase : 5 ≤ (advancePhase L K a).phase.val := by
    exact le_trans ha (advancePhase_phase_nondec L K a)
  rw [phaseInit_bias_ge_five (advancePhase L K a).phase (advancePhase L K a) hadv_phase]
  exact hadv_bias

/-- `stdCounterSubroutine` preserves `bias` for an agent at phase ≥ 5. -/
theorem stdCounterSubroutine_bias_ge_five (a : AgentState L K) (ha : 5 ≤ a.phase.val) :
    (stdCounterSubroutine L K a).bias = a.bias := by
  unfold stdCounterSubroutine
  split
  · exact advancePhaseWithInit_bias_ge_five (L := L) (K := K) a ha
  · rfl

/-- **Staticity (left output).**  `Phase5Transition` never changes the first agent's `bias`
when both agents are at phase 5.  Sampling only writes `hour`; the clock subroutine
preserves `bias` for phase ≥ 5. -/
theorem Phase5Transition_fst_bias_eq (s t : AgentState L K)
    (hs : s.phase.val = 5) :
    (Phase5Transition L K s t).1.bias = s.bias := by
  unfold Phase5Transition
  simp only
  -- The left output is `if s1.role = clock then stdCounterSubroutine s1 else s1`, where
  -- `s1 ∈ {s, {s with hour := …}}` (sampling only writes hour ⇒ bias = s.bias), and the
  -- clock subroutine preserves bias for phase ≥ 5.
  have hstep : ∀ s1 : AgentState L K, s1.bias = s.bias → s1.phase.val = 5 →
      (if s1.role = Role.clock then stdCounterSubroutine L K s1 else s1).bias = s.bias := by
    intro s1 hb1 hp1
    by_cases hsc : s1.role = Role.clock
    · rw [if_pos hsc, stdCounterSubroutine_bias_ge_five (L := L) (K := K) s1 (by omega)]; exact hb1
    · rw [if_neg hsc]; exact hb1
  by_cases hb1 : s.role = Role.reserve ∧ t.role = Role.main ∧ t.bias ≠ Bias.zero
  · rw [if_pos hb1]
    by_cases hg : s.hour.val = L
    · rw [if_pos hg]; exact hstep _ rfl (by simpa using hs)
    · rw [if_neg hg]; exact hstep _ rfl hs
  · rw [if_neg hb1]
    by_cases hb2 : t.role = Role.reserve ∧ s.role = Role.main ∧ s.bias ≠ Bias.zero
    · rw [if_pos hb2]
      by_cases hg2 : t.hour.val = L
      · rw [if_pos hg2]; exact hstep _ rfl hs
      · rw [if_neg hg2]; exact hstep _ rfl hs
    · rw [if_neg hb2]; exact hstep _ rfl hs

/-- **Staticity (second output).** -/
theorem Phase5Transition_snd_bias_eq (s t : AgentState L K)
    (ht : t.phase.val = 5) :
    (Phase5Transition L K s t).2.bias = t.bias := by
  unfold Phase5Transition
  simp only
  have hstep : ∀ t1 : AgentState L K, t1.bias = t.bias → t1.phase.val = 5 →
      (if t1.role = Role.clock then stdCounterSubroutine L K t1 else t1).bias = t.bias := by
    intro t1 hb1 hp1
    by_cases htc : t1.role = Role.clock
    · rw [if_pos htc, stdCounterSubroutine_bias_ge_five (L := L) (K := K) t1 (by omega)]; exact hb1
    · rw [if_neg htc]; exact hb1
  by_cases hb1 : s.role = Role.reserve ∧ t.role = Role.main ∧ t.bias ≠ Bias.zero
  · rw [if_pos hb1]
    by_cases hg : s.hour.val = L
    · rw [if_pos hg]; exact hstep _ rfl ht
    · rw [if_neg hg]; exact hstep _ rfl ht
  · rw [if_neg hb1]
    by_cases hb2 : t.role = Role.reserve ∧ s.role = Role.main ∧ s.bias ≠ Bias.zero
    · rw [if_pos hb2]
      by_cases hg2 : t.hour.val = L
      · rw [if_pos hg2]; exact hstep _ rfl (by simpa using ht)
      · rw [if_neg hg2]; exact hstep _ rfl ht
    · rw [if_neg hb2]; exact hstep _ rfl ht

/-! ## Part B — role staticity and the conserved biased-Main class profile. -/

/-- `phaseInit` preserves `role` for any target phase `p` with `p.val ≥ 5`.  Local copy of
the protocol's `private` lemma. -/
theorem phaseInit_role_ge_five (p : Fin 11) (a : AgentState L K) (hp : 5 ≤ p.val) :
    (phaseInit L K p a).role = a.role := by
  set_option linter.unusedSimpArgs false in
  fin_cases p <;> simp_all (config := { decide := false }) <;>
    simp [phaseInit, enterPhase10] <;> split_ifs <;> simp [enterPhase10]

/-- `advancePhaseWithInit` preserves `role` for an agent at phase ≥ 5. -/
theorem advancePhaseWithInit_role_ge_five (a : AgentState L K) (ha : 5 ≤ a.phase.val) :
    (advancePhaseWithInit L K a).role = a.role := by
  unfold advancePhaseWithInit
  have hadv_role : (advancePhase L K a).role = a.role := by unfold advancePhase; split <;> rfl
  have hadv_phase : 5 ≤ (advancePhase L K a).phase.val :=
    le_trans ha (advancePhase_phase_nondec L K a)
  rw [phaseInit_role_ge_five (advancePhase L K a).phase (advancePhase L K a) hadv_phase]
  exact hadv_role

/-- `stdCounterSubroutine` preserves `role` for an agent at phase ≥ 5. -/
theorem stdCounterSubroutine_role_ge_five (a : AgentState L K) (ha : 5 ≤ a.phase.val) :
    (stdCounterSubroutine L K a).role = a.role := by
  unfold stdCounterSubroutine
  split
  · exact advancePhaseWithInit_role_ge_five (L := L) (K := K) a ha
  · rfl

/-- **Staticity of `role` (left output).**  A phase-5 Phase5Transition keeps the first
agent's `role`.  (Sampling writes `hour` only; clock subroutine preserves role for ph ≥ 5.) -/
theorem Phase5Transition_fst_role_eq (s t : AgentState L K) (_hs : s.phase.val = 5) :
    (Phase5Transition L K s t).1.role = s.role := by
  rcases Phase5Transition_fst_role_hour (L := L) (K := K) s t with hclk | ⟨hr, _⟩
  · -- left output is a clock; this forces s.role to be clock too (else sampling/identity
    -- keeps role = s.role, contradicting clock).  We instead show s.role = clock.
    -- From the structure: the only way the output is a clock is `s1.role = clock`, and
    -- `s1.role = s.role` in all non-clock-producing branches.  So `s.role = clock`.
    -- Re-derive via the role-hour disjunct's second component if available; otherwise the
    -- output clock came from a clock input.  We argue: if s.role ≠ clock then output role
    -- = s.role ≠ clock, contradiction.
    by_cases hsc : s.role = Role.clock
    · rw [hclk, hsc]
    · -- non-clock branch: output role = s.role; but hclk says clock — contradiction unless
      -- s.role = clock.  We reconstruct output role = s.role.
      exfalso
      -- Use the bias-style hstep: output role equals s.role in every non-clock-producing case.
      have hrole_out : (Phase5Transition L K s t).1.role = s.role := by
        unfold Phase5Transition; simp only
        have hstep : ∀ s1 : AgentState L K, s1.role = s.role →
            (if s1.role = Role.clock then stdCounterSubroutine L K s1 else s1).role = s.role := by
          intro s1 hr1
          by_cases h1 : s1.role = Role.clock
          · rw [if_pos h1, stdCounterSubroutine_clock_role_eq L K _ h1]; rw [hr1] at h1; exact h1.symm
          · rw [if_neg h1]; exact hr1
        by_cases hb1 : s.role = Role.reserve ∧ t.role = Role.main ∧ t.bias ≠ Bias.zero
        · rw [if_pos hb1]
          by_cases hg : s.hour.val = L
          · rw [if_pos hg]; exact hstep _ rfl
          · rw [if_neg hg]; exact hstep _ rfl
        · rw [if_neg hb1]
          by_cases hb2 : t.role = Role.reserve ∧ s.role = Role.main ∧ s.bias ≠ Bias.zero
          · rw [if_pos hb2]
            by_cases hg2 : t.hour.val = L
            · rw [if_pos hg2]; exact hstep _ rfl
            · rw [if_neg hg2]; exact hstep _ rfl
          · rw [if_neg hb2]; exact hstep _ rfl
      rw [hrole_out] at hclk; exact hsc hclk
  · exact hr

/-- **Staticity of `role` (second output).** -/
theorem Phase5Transition_snd_role_eq (s t : AgentState L K) (_ht : t.phase.val = 5) :
    (Phase5Transition L K s t).2.role = t.role := by
  rcases Phase5Transition_snd_role_hour (L := L) (K := K) s t with hclk | ⟨hr, _⟩
  · by_cases htc : t.role = Role.clock
    · rw [hclk, htc]
    · exfalso
      have hrole_out : (Phase5Transition L K s t).2.role = t.role := by
        unfold Phase5Transition; simp only
        have hstep : ∀ t1 : AgentState L K, t1.role = t.role →
            (if t1.role = Role.clock then stdCounterSubroutine L K t1 else t1).role = t.role := by
          intro t1 hr1
          by_cases h1 : t1.role = Role.clock
          · rw [if_pos h1, stdCounterSubroutine_clock_role_eq L K _ h1]; rw [hr1] at h1; exact h1.symm
          · rw [if_neg h1]; exact hr1
        by_cases hb1 : s.role = Role.reserve ∧ t.role = Role.main ∧ t.bias ≠ Bias.zero
        · rw [if_pos hb1]
          by_cases hg : s.hour.val = L
          · rw [if_pos hg]; exact hstep _ rfl
          · rw [if_neg hg]; exact hstep _ rfl
        · rw [if_neg hb1]
          by_cases hb2 : t.role = Role.reserve ∧ s.role = Role.main ∧ s.bias ≠ Bias.zero
          · rw [if_pos hb2]
            by_cases hg2 : t.hour.val = L
            · rw [if_pos hg2]; exact hstep _ rfl
            · rw [if_neg hg2]; exact hstep _ rfl
          · rw [if_neg hb2]; exact hstep _ rfl
      rw [hrole_out] at hclk; exact htc hclk
  · exact hr

/-! ## Part C — the class counts and the conserved biased-Main class profile.

`biasedMainClass σ i a` flags a Main with dyadic bias `σ·2^{−i}` (exponent index `i`); its
count `biasedMainClassU σ i` is the **static** profile that the Reserves sample against.
`sampledReserveClass i a` flags a Reserve whose recorded sample is exponent index `i`
(`hour.val = i`); its count `sampledReserveClassU i` is the quantity the concentration
controls.  The former is `(role, bias)`-only and conserved per Phase-5 step by staticity. -/

/-- A Main with dyadic bias of sign `σ`, exponent index `i` (paper exponent `−i`). -/
def biasedMainClass (σ : Sign) (i : Fin (L + 1)) (a : AgentState L K) : Prop :=
  a.role = Role.main ∧ a.bias = Bias.dyadic σ i

instance (σ : Sign) (i : Fin (L + 1)) (a : AgentState L K) :
    Decidable (biasedMainClass σ i a) := by unfold biasedMainClass; infer_instance

/-- The (static) count of biased Mains in class `(σ, i)`. -/
def biasedMainClassU (σ : Sign) (i : Fin (L + 1)) (c : Config (AgentState L K)) : ℕ :=
  Multiset.countP (fun a => biasedMainClass σ i a) c

/-- A Reserve whose recorded sample is exponent index `i` (`sample = hour = i`). -/
def sampledReserveClass (i : Fin (L + 1)) (a : AgentState L K) : Prop :=
  a.role = Role.reserve ∧ a.hour.val = i.val

instance (i : Fin (L + 1)) (a : AgentState L K) :
    Decidable (sampledReserveClass i a) := by unfold sampledReserveClass; infer_instance

/-- The count of Reserves that sampled class `i`. -/
def sampledReserveClassU (i : Fin (L + 1)) (c : Config (AgentState L K)) : ℕ :=
  Multiset.countP (fun a => sampledReserveClass i a) c

/-- `countP biasedMainClass` over a two-element pair as a sum of indicators. -/
theorem countP_biasedMainClass_pair (σ : Sign) (i : Fin (L + 1)) (x y : AgentState L K) :
    Multiset.countP (fun a => biasedMainClass σ i a) ({x, y} : Multiset (AgentState L K))
      = (if biasedMainClass σ i x then 1 else 0) + (if biasedMainClass σ i y then 1 else 0) := by
  rw [show ({x, y} : Multiset (AgentState L K)) = x ::ₘ y ::ₘ 0 from rfl]
  rw [Multiset.countP_cons, Multiset.countP_cons, Multiset.countP_zero]; ring

/-- **`biasedMainClass` is preserved both ways by `Phase5Transition` (left output).**  By
`(role, bias)`-staticity the first output is `biasedMainClass σ i` iff `s` is. -/
theorem biasedMainClass_fst_iff (σ : Sign) (i : Fin (L + 1)) (s t : AgentState L K)
    (hs : s.phase.val = 5) :
    biasedMainClass σ i (Phase5Transition L K s t).1 ↔ biasedMainClass σ i s := by
  unfold biasedMainClass
  rw [Phase5Transition_fst_role_eq (L := L) (K := K) s t hs,
      Phase5Transition_fst_bias_eq (L := L) (K := K) s t hs]

/-- **`biasedMainClass` preserved both ways (second output).** -/
theorem biasedMainClass_snd_iff (σ : Sign) (i : Fin (L + 1)) (s t : AgentState L K)
    (ht : t.phase.val = 5) :
    biasedMainClass σ i (Phase5Transition L K s t).2 ↔ biasedMainClass σ i t := by
  unfold biasedMainClass
  rw [Phase5Transition_snd_role_eq (L := L) (K := K) s t ht,
      Phase5Transition_snd_bias_eq (L := L) (K := K) s t ht]

/-- **Per-pair conservation of `biasedMainClassU`** under a phase-5 `Phase5Transition`. -/
theorem Phase5Transition_biasedMainClass_pair_eq (σ : Sign) (i : Fin (L + 1))
    (s t : AgentState L K) (hs : s.phase.val = 5) (ht : t.phase.val = 5) :
    Multiset.countP (fun a => biasedMainClass σ i a)
        ({(Phase5Transition L K s t).1, (Phase5Transition L K s t).2}
          : Multiset (AgentState L K))
      = Multiset.countP (fun a => biasedMainClass σ i a)
          ({s, t} : Multiset (AgentState L K)) := by
  classical
  rw [countP_biasedMainClass_pair, countP_biasedMainClass_pair]
  rw [if_congr (biasedMainClass_fst_iff (L := L) (K := K) σ i s t hs) rfl rfl,
      if_congr (biasedMainClass_snd_iff (L := L) (K := K) σ i s t ht) rfl rfl]

/-! ## Part D — the static profile is a kernel invariant, plus the assembled instance. -/

private theorem mem_of_app_left5' {c : Config (AgentState L K)}
    {r₁ r₂ : AgentState L K} (happ : Protocol.Applicable c r₁ r₂) : r₁ ∈ c :=
  Multiset.mem_of_le (show ({r₁, r₂} : Multiset (AgentState L K)) ≤ c from happ) (by simp)

private theorem mem_of_app_right5' {c : Config (AgentState L K)}
    {r₁ r₂ : AgentState L K} (happ : Protocol.Applicable c r₁ r₂) : r₂ ∈ c :=
  Multiset.mem_of_le (show ({r₁, r₂} : Multiset (AgentState L K)) ≤ c from happ) (by simp)

/-- **`biasedMainClassU σ i` is conserved by any chosen-pair update on the all-phase-5
window** (the static profile).  An applicable pair are both phase-5 agents, so `Transition`
reduces to `Phase5Transition`, whose per-pair class count is conserved. -/
theorem biasedMainClassU_stepOrSelf_eq (σ : Sign) (i : Fin (L + 1)) (n : ℕ)
    (c : Config (AgentState L K)) (hInv : Phase5AllWin n c) (r₁ r₂ : AgentState L K) :
    biasedMainClassU (L := L) (K := K) σ i
        (Protocol.stepOrSelf (NonuniformMajority L K) c r₁ r₂)
      = biasedMainClassU (L := L) (K := K) σ i c := by
  obtain ⟨_, hph⟩ := hInv
  by_cases happ : Protocol.Applicable c r₁ r₂
  · have h15 : r₁.phase.val = 5 := hph r₁ (mem_of_app_left5' happ)
    have h25 : r₂.phase.val = 5 := hph r₂ (mem_of_app_right5' happ)
    have hsub : ({r₁, r₂} : Multiset (AgentState L K)) ≤ c := happ
    have hc' : Protocol.stepOrSelf (NonuniformMajority L K) c r₁ r₂
        = c - {r₁, r₂} + {(Transition L K r₁ r₂).1, (Transition L K r₁ r₂).2} := by
      unfold Protocol.stepOrSelf; rw [if_pos happ]; rfl
    unfold biasedMainClassU
    rw [hc', Multiset.countP_add, Multiset.countP_sub hsub]
    rw [Transition_eq_Phase5Transition_of_phase5 (L := L) (K := K) r₁ r₂ h15 h25]
    rw [Phase5Transition_biasedMainClass_pair_eq (L := L) (K := K) σ i r₁ r₂ h15 h25]
    have hpair_le : Multiset.countP (fun a => biasedMainClass σ i a)
        ({r₁, r₂} : Multiset (AgentState L K))
          ≤ Multiset.countP (fun a => biasedMainClass σ i a) c :=
      Multiset.countP_le_of_le _ hsub
    omega
  · rw [Protocol.stepOrSelf_eq_self_of_not_applicable happ]

/-- The kernel-support version: the static biased-Main class profile is unchanged by any
single kernel step from a phase-5-window config. -/
theorem biasedMainClassU_support_eq (σ : Sign) (i : Fin (L + 1)) (n : ℕ)
    (c c' : Config (AgentState L K)) (hInv : Phase5AllWin n c)
    (hc' : c' ∈ ((NonuniformMajority L K).stepDistOrSelf c).support) :
    biasedMainClassU (L := L) (K := K) σ i c' = biasedMainClassU (L := L) (K := K) σ i c := by
  by_cases hc : 2 ≤ c.card
  · rw [show (NonuniformMajority L K).stepDistOrSelf c
        = (NonuniformMajority L K).stepDist c hc by
        unfold Protocol.stepDistOrSelf; rw [dif_pos hc]] at hc'
    obtain ⟨⟨r₁, r₂⟩, hr⟩ := Protocol.stepDist_support (NonuniformMajority L K) c hc c' hc'
    rw [← hr]; exact biasedMainClassU_stepOrSelf_eq σ i n c hInv r₁ r₂
  · rw [show (NonuniformMajority L K).stepDistOrSelf c = PMF.pure c by
        unfold Protocol.stepDistOrSelf; rw [dif_neg hc]] at hc'
    rw [PMF.mem_support_pure_iff] at hc'; subst hc'; rfl

/-! ### The Phase-5 post predicate and the assembled `PhaseConvergenceW`.

`ReserveSampleGood i K₀ c` is the honest rendering of the paper's Phase-5 output for Phase 6:
*every Reserve has sampled* (`ReserveSampled`) AND *enough Reserves sampled the useful level*
(`sampledFloor`), the Chernoff floor `R_{−l} ≥ 0.18|R|` resp. `R_{−(l+1)} ≥ 0.58|R|`.  The
level index `i` and required count `K₀` parameterise both case-split branches of Lemma 7.2. -/

/-- The sampled-class floor at level `i`: at least `K₀` Reserves recorded sample `i`. -/
def sampledFloor (i : Fin (L + 1)) (K₀ : ℕ) (c : Config (AgentState L K)) : Prop :=
  K₀ ≤ sampledReserveClassU (L := L) (K := K) i c

/-- **Phase-5 output predicate** (`ReserveSampleGood`): all Reserves sampled, and at least
`K₀` of them at the useful level `i` (the Chernoff floor Phase 6 needs). -/
def ReserveSampleGood (i : Fin (L + 1)) (K₀ : ℕ) (c : Config (AgentState L K)) : Prop :=
  ReserveSampled (L := L) (K := K) c ∧ sampledFloor (L := L) (K := K) i K₀ c

/-- **The assembled Phase-5 `PhaseConvergenceW`** (Lemma 7.1).

`Pre c = Phase5AllWin n c ∧ unsampledReserveU c ≤ M₀`; `Post c = Phase5AllWin n c ∧
ReserveSampleGood i K₀ c`.  Built from the all-sampled engine
(`ReserveSampling.phase5SampledConvergence`) intersected with the sampled-class concentration
event.  The concentration tail `hConc` is the in-house exponential-MGF Chernoff on the
`sampledReserveClassU`-deficit potential against the *static* class profile
(`biasedMainClassU` is conserved by `biasedMainClassU_support_eq`, so the draw distribution is
fixed) — the precise campaign hook for that MGF drift. -/
noncomputable def phase5Convergence (n : ℕ) (i : Fin (L + 1)) (K₀ : ℕ)
    (hClosed : OneSidedCancel.InvClosed (NonuniformMajority L K).transitionKernel
      (fun c => Phase5AllWin (L := L) (K := K) n c))
    (q : ℝ≥0∞)
    (hstep : ∀ b : Config (AgentState L K), Phase5AllWin (L := L) (K := K) n b →
      1 ≤ unsampledReserveU (L := L) (K := K) b →
      (NonuniformMajority L K).transitionKernel b
        (OneSidedCancel.potDone (fun c => unsampledReserveU (L := L) (K := K) c))ᶜ ≤ q)
    (M₀ t : ℕ) (ε : ℝ≥0) (hε : (q ^ t : ℝ≥0∞) ≤ (ε : ℝ≥0∞))
    (εConc : ℝ≥0)
    (hConc : ∀ c₀, Phase5AllWin (L := L) (K := K) n c₀ →
      unsampledReserveU (L := L) (K := K) c₀ ≤ M₀ →
      ((NonuniformMajority L K).transitionKernel ^ t) c₀
        {c | ¬ sampledFloor (L := L) (K := K) i K₀ c} ≤ (εConc : ℝ≥0∞)) :
    PhaseConvergenceW (NonuniformMajority L K).transitionKernel where
  Pre c := Phase5AllWin (L := L) (K := K) n c ∧ unsampledReserveU (L := L) (K := K) c ≤ M₀
  Post c := Phase5AllWin (L := L) (K := K) n c ∧ ReserveSampleGood (L := L) (K := K) i K₀ c
  t := t
  ε := ε + εConc
  convergence := by
    intro c₀ hPre
    obtain ⟨hwin, hbud⟩ := hPre
    set P5 := phase5SampledConvergence (L := L) (K := K) n hClosed q hstep M₀ t ε hε with hP5
    have hsampled := P5.convergence c₀ ⟨hwin, hbud⟩
    have hcover : {c : Config (AgentState L K) |
        ¬ (Phase5AllWin (L := L) (K := K) n c ∧
            ReserveSampleGood (L := L) (K := K) i K₀ c)}
          ⊆ {c | ¬ P5.Post c} ∪ {c | ¬ sampledFloor (L := L) (K := K) i K₀ c} := by
      intro c hc
      simp only [Set.mem_setOf_eq, Set.mem_union] at hc ⊢
      rw [phase5SampledConvergence_post (L := L) (K := K) n hClosed q hstep M₀ t ε hε]
      by_cases hfloor : sampledFloor (L := L) (K := K) i K₀ c
      · left
        intro hContra
        exact hc ⟨hContra.1, hContra.2, hfloor⟩
      · exact Or.inr hfloor
    calc ((NonuniformMajority L K).transitionKernel ^ t) c₀
            {c | ¬ (Phase5AllWin (L := L) (K := K) n c ∧
              ReserveSampleGood (L := L) (K := K) i K₀ c)}
        ≤ ((NonuniformMajority L K).transitionKernel ^ t) c₀
            ({c | ¬ P5.Post c} ∪ {c | ¬ sampledFloor (L := L) (K := K) i K₀ c}) :=
          measure_mono hcover
      _ ≤ ((NonuniformMajority L K).transitionKernel ^ t) c₀ {c | ¬ P5.Post c}
            + ((NonuniformMajority L K).transitionKernel ^ t) c₀
              {c | ¬ sampledFloor (L := L) (K := K) i K₀ c} := measure_union_le _ _
      _ ≤ (ε : ℝ≥0∞) + (εConc : ℝ≥0∞) := by
          gcongr
          · exact hsampled
          · exact hConc c₀ hwin hbud
      _ = ((ε + εConc : ℝ≥0) : ℝ≥0∞) := by rw [ENNReal.coe_add]

end Phase5Convergence

end ExactMajority
