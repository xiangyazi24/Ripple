/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Doty §6 — the PHASE-0 TIME WINDOW lower bound (Phase C-0w)

This file supplies the **timing half** of the Phase-0 analysis: the whp event
that NO agent leaves phase 0 too early — the counters cannot finish before the
window `T₀ = Θ(n log n)`-shape number of interactions.  This is what

* relay-11 needs for its **phase-0-CR shell escape** bound (the genuinely
  probabilistic "a CR advanced past phase 0" event that the count-only gate in
  `RoleSplitConcentration.lean` cannot carry — see
  `DOTY_POST63_CAMPAIGN.md` §C-1, "the phase-window half remains"); and
* the timing half of the Phase-0 `PhaseConvergence` upgrade.

## The mechanism (Doty et al. §3.4, Standard Counter Subroutine)

Phase advance out of phase 0 happens ONLY via a clock's counter hitting 0
(`Transition.stdCounterSubroutine`: `if counter = 0 then advancePhaseWithInit
else counter -= 1`) followed by the subsequent epidemic.  Each clock starts at
`counter = 50·(L+1)` (`Transition.phaseInit` Rule 4; `L = ⌈log₂ n⌉`, so
`50(L+1) = Θ(log n)`).  A clock decrements only when it is the chosen agent in
a clock–clock meeting; per step a SPECIFIC clock ticks with probability
`≤ 2(mC−1)/(n(n−1)) ≤ 2/n`.  For ANY clock to reach `0` within `t` steps it
must accumulate `50(L+1)` ticks — a binomial lower tail.

## The Φ-drift route (the in-house affine-counter pattern)

The per-clock tick count is a path functional, NOT a config field — but the
per-clock counter REMAINING `a.counter` IS a config field, decreasing by 1 per
tick.  We use the DOWNWARD-crossing exponential potential over the multiset:

  `Φ_s c := ∑_{a clock} exp(−s · a.counter)`     (a genuine `Config.sumOf`)

One clock–clock meeting multiplies the two affected summands by `e^s` (counter
drops by 1); a clock ticks w.p. `≤ 2/n`, so the affected-summand drift bound is

  `∫ Φ_s dK(c) ≤ (1 + 2(e^s − 1)/n) · Φ_s c`     (clean affine contraction).

`{∃ clock with counter = 0}` forces `Φ_s ≥ e^0 = 1`, so Markov + the window
engine `WindowConcentration.windowDrift_tail` gives

  `(K^t) c₀ {¬ allPhase0} ≤ (1 + 2(e^s−1)/n)^t · Φ_s(c₀) / 1`,

and with `s = 1`, `t = δ·n·(L+1)`, `Φ_s(c₀) ≤ n·e^{−50(L+1)}` the exponent is
`ln n − 50(L+1) + 2(e−1)δ(L+1) ≤ −45(L+1) ≤ −45 ln n`, i.e. `≤ n^{−45}`.

## What is built (0 sorry / 0 axiom / no native_decide)

This file builds the **abstract Φ-drift → tail → window layer**, generic in the
per-step tick-probability bound, mirroring the in-house pattern where
`WindowConcentration.windowDrift_tail` itself takes the one-step drift as a
hypothesis.  The deep quantitative scheduler computation (the per-step drift on
the real kernel) is the campaign's separate quantitative core; the precise goal
it must discharge is recorded as `ClockTickDrift` below.

Gap-2 (deterministic phase-0-exit bridge) is DISCHARGED here.  Gap-1 (the
quantitative scheduler drift) is now DISCHARGED as an AFFINE one-step drift on the
phase-0 window: `clockCounterPotential_drift_affine` proves
`∫ Φ_s dK(c) ≤ ofReal(1+2(eˢ−1)/n)·Φ_s(c) + e^{−s·50(L+1)}` on `allPhase0` (no
positive-counter side condition), and `phase0_window_tail_affine` is the matching
immigration tail engine.  See the gap note at the end of the file for the one
remaining structural input (an absorbing `Q ⊆ allPhase0` witness).

* `clockCounterPotential` — the multiset exp-potential `Φ_s`;
* `allPhase0` — the phase-0 window predicate;
* `lintegral_transitionKernel_eq_sum` — lintegral = `interactionProb` pair sum;
* `sum_fst/snd_interactionProb` — the two interaction marginals `= Φ_s(c)/card`;
* `clockSummand_pair_le` — the universal per-pair output bound
  `≤ eˢ·sources + fresh` (ANY counters);
* `clockCounterPotential_stepOrSelf_le` — per-pair potential bound on `allPhase0`;
* `clockCounterPotential_drift_affine` — the AFFINE one-step drift (Gap-1 capstone);
* `lintegral_decay_affine_on_absorbing` / `phase0_window_tail_affine` — the affine
  (immigration) tail engine;
* `clockCounterPotential_ge_one_of_clock_counter_zero` — the threshold link
  (`¬ noClockAtZero` forces `Φ_s ≥ 1`);
* `phase0_window_tail_of_drift` — the (multiplicative) kernel-level tail;
* `phase0_window_whp` — the `(K^t) c₀ {¬ noClockAtZero}` corollary;
* `det_phase0_exit` / `allPhase0_window_whp` — the Gap-2 deterministic bridge.

Reference: Doty et al. §3.4 (counter subroutine), §6 (Phase-0 time window);
engine = `WindowConcentration.windowDrift_tail`; consumer = relay-11
(`DOTY_POST63_CAMPAIGN.md` §C-1).
-/

import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.WindowConcentration
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.RoleSplitConcentration

namespace ExactMajority

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Real BigOperators

namespace Phase0Window

variable {L K : ℕ}

/-! ## The clock-counter exponential potential. -/

/-- The per-agent contribution to the clock-counter potential at scale `s`:
`exp(−s · counter)` if the agent is a clock, else `0`.  Packaged as an
`ℝ≥0∞`-valued state observable so the multiset sum is a `Config.sumOf`. -/
noncomputable def clockSummand (s : ℝ) (a : AgentState L K) : ℝ≥0∞ :=
  if a.role = .clock then ENNReal.ofReal (Real.exp (-(s * (a.counter.val : ℝ)))) else 0

/-- The clock-counter exponential potential
`Φ_s c = ∑_{a clock} exp(−s · a.counter)`, as a multiset sum over the
configuration. -/
noncomputable def clockCounterPotential (s : ℝ) (c : Config (AgentState L K)) : ℝ≥0∞ :=
  Config.sumOf (clockSummand (L := L) (K := K) s) c

/-- The absorbing phase-0 window: every agent is still in phase `0`. -/
def allPhase0 (c : Config (AgentState L K)) : Prop :=
  ∀ a ∈ c, a.phase = 0

/-! ## Measurability (discrete σ-algebra on `Config`). -/

/-- The clock-counter potential is measurable: `Config` carries the discrete
σ-algebra, so every function out of it is measurable. -/
theorem measurable_clockCounterPotential (s : ℝ) :
    Measurable (clockCounterPotential (L := L) (K := K) s) :=
  Measurable.of_discrete

/-! ## The threshold link.

`¬ allPhase0` means some agent has left phase 0.  The deterministic Doty trace
fact (`Transition.stdCounterSubroutine`) is that a phase advance out of phase 0
fires precisely at the moment a clock's counter is `0`; for the Markov tail it
suffices to bound the config event `∃ clock with counter = 0`, on which the
potential exceeds the threshold `1 = e^0`. -/

/-- **The threshold link.**  If some clock in `c` has `counter = 0`, then the
clock-counter potential `Φ_s c ≥ 1`: that clock's summand is
`exp(−s · 0) = e^0 = 1`, and a single multiset summand bounds the
nonnegative-`ℝ≥0∞` sum below.  (No sign condition on `s`.) -/
theorem clockCounterPotential_ge_one_of_clock_counter_zero (s : ℝ)
    (c : Config (AgentState L K)) (a : AgentState L K) (ha : a ∈ c)
    (hrole : a.role = .clock) (hctr : a.counter.val = 0) :
    1 ≤ clockCounterPotential (L := L) (K := K) s c := by
  have hsumm : clockSummand (L := L) (K := K) s a = 1 := by
    unfold clockSummand
    rw [if_pos hrole, hctr]
    simp
  calc (1 : ℝ≥0∞)
      = clockSummand (L := L) (K := K) s a := hsumm.symm
    _ ≤ ((c.map (clockSummand (L := L) (K := K) s)).sum) :=
        Multiset.single_le_sum (fun x _ => zero_le') _
          (Multiset.mem_map_of_mem _ ha)
    _ = clockCounterPotential (L := L) (K := K) s c := rfl

/-- The config event "no clock has reached `counter = 0` yet" — the
postcondition whose negation is forced above threshold by the potential.  This
is the per-step config event the window engine bounds directly; the bridge to
`allPhase0` (a clock at `counter = 0` is the ONLY phase-0 exit, but it exits at
the NEXT step) is the prefix-union structure recorded below. -/
def noClockAtZero (c : Config (AgentState L K)) : Prop :=
  ∀ a ∈ c, a.role = .clock → a.counter.val ≠ 0

/-- The threshold link in `Post`-form: `¬ noClockAtZero c` (some clock has
counter `0`) forces `Φ_s c ≥ 1`. -/
theorem clockCounterPotential_ge_one_of_not_noClockAtZero (s : ℝ)
    (c : Config (AgentState L K)) (hc : ¬ noClockAtZero (L := L) (K := K) c) :
    1 ≤ clockCounterPotential (L := L) (K := K) s c := by
  unfold noClockAtZero at hc
  push Not at hc
  obtain ⟨a, ha, hrole, hctr⟩ := hc
  exact clockCounterPotential_ge_one_of_clock_counter_zero s c a ha hrole hctr

/-! ## Scheduler pair-sum expansion of the one-step lintegral (Gap-1 infrastructure).

The drift `∫ Φ dK(c)` over the uniform-pair scheduler is, by construction, the
expectation of `Φ(stepOrSelf c pair)` over the ordered-pair law
`Config.interactionProb`.  Pushing the `PMF.map` through `toMeasure`
(`PMF.toMeasure_map`), then `lintegral_map`, then `lintegral_fintype` over the
finite ordered-pair space, turns the one-step lintegral into the explicit
weighted **pair sum**

  `∫ Φ dK(c) = ∑_{pair} Φ(stepOrSelf c pair) · interactionProb(pair)`,

the per-pair ledger every quantitative drift bound (Gap 1, and the in-house
affine-counter pattern) is built on.  Stated generically in the state set `Λ`. -/

section SchedulerPairSum

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]

attribute [local instance] Classical.propDecidable

noncomputable local instance : MeasurableSpace (Λ × Λ) := ⊤
local instance : DiscreteMeasurableSpace (Λ × Λ) := ⟨fun _ => trivial⟩
local instance : MeasurableSingletonClass (Λ × Λ) := ⟨fun _ => trivial⟩

/-- **One-step lintegral as a pair sum (`stepDist`).**  For a population of size
`≥ 2`, the expectation of any `ℝ≥0∞`-observable `f` under one scheduler step is
the `interactionProb`-weighted sum of `f` over the scheduled-pair updates. -/
theorem lintegral_stepDist_eq_sum (P : Protocol Λ) (c : Config Λ) (hc : 2 ≤ c.card)
    (f : Config Λ → ℝ≥0∞) :
    ∫⁻ c', f c' ∂((P.stepDist c hc).toMeasure)
      = ∑ pair : Λ × Λ,
          f (Protocol.scheduledStep P c pair) * c.interactionProb pair.1 pair.2 := by
  unfold Protocol.stepDist
  rw [← PMF.toMeasure_map (Protocol.scheduledStep P c) (c.interactionPMF hc)
        (Measurable.of_discrete)]
  rw [lintegral_map (Measurable.of_discrete) (Measurable.of_discrete)]
  rw [lintegral_fintype]
  apply Finset.sum_congr rfl
  intro pair _
  congr 1
  rw [PMF.toMeasure_apply_singleton _ _ (MeasurableSet.singleton _)]
  rfl

/-- **One-step lintegral as a pair sum (`transitionKernel`).**  At populations of
size `≥ 2` the Markov kernel expectation is the explicit `interactionProb`-weighted
sum over ordered pairs of the `stepOrSelf` updates:

  `∫ f dK(c) = ∑_{pair} f(stepOrSelf c pair.1 pair.2) · interactionProb(pair)`. -/
theorem lintegral_transitionKernel_eq_sum (P : Protocol Λ) (c : Config Λ)
    (hc : 2 ≤ c.card) (f : Config Λ → ℝ≥0∞) :
    ∫⁻ c', f c' ∂(P.transitionKernel c)
      = ∑ pair : Λ × Λ, f (Protocol.stepOrSelf P c pair.1 pair.2)
          * c.interactionProb pair.1 pair.2 := by
  change ∫⁻ c', f c' ∂((P.stepDistOrSelf c).toMeasure) = _
  unfold Protocol.stepDistOrSelf
  rw [dif_pos hc, lintegral_stepDist_eq_sum P c hc f]
  rfl

/-! ## The first-coordinate marginal of the interaction law (Gap-1 infrastructure).

For any per-state observable `g`, summing `g(pair.1)·interactionProb(pair)` over
ordered pairs collapses the responder coordinate (`sum_interactionCount_right`),
leaving the per-state `g`-mass weighted by `count(s)·(card−1)/(card·(card−1)) =
count(s)/card`.  Hence the FIRST-coordinate marginal of the interaction law is the
configuration `g`-average `Φ_g(c)/card`.  This is the scheduler's exact
`1/n`-marginal — the source of the `2/n` pair-count factor in the affine drift. -/

/-- **First-coordinate interaction marginal.**  For `2 ≤ card`, summing any
`ℝ≥0∞`-observable of the INITIATOR state against the interaction law gives the
configuration average `Config.sumOf g c / card`:

  `∑_{pair} g(pair.1) · interactionProb(pair) = (∑_{a∈c} g a) / card`. -/
theorem sum_fst_interactionProb (c : Config Λ) (hc : 2 ≤ c.card) (g : Λ → ℝ≥0∞) :
    (∑ pair : Λ × Λ, g pair.1 * c.interactionProb pair.1 pair.2)
      = Config.sumOf g c / (c.card : ℝ≥0∞) := by
  classical
  -- Expand interactionProb = interactionCount / totalPairs and split the product.
  simp only [Config.interactionProb]
  rw [show (Finset.univ : Finset (Λ × Λ)) = Finset.univ ×ˢ Finset.univ
    from (Finset.univ_product_univ).symm]
  rw [Finset.sum_product]
  -- inner sum over responder: ∑_{s₂} g s₁ * (count(s₁,s₂)/totalPairs)
  have hinner : ∀ s₁ : Λ,
      (∑ s₂ : Λ, g s₁ * ((c.interactionCount s₁ s₂ : ℝ≥0∞) / (c.totalPairs : ℝ≥0∞)))
        = g s₁ * ((c.count s₁ * (c.card - 1) : ℕ) : ℝ≥0∞) / (c.totalPairs : ℝ≥0∞) := by
    intro s₁
    have hcount : (∑ s₂ : Λ, (c.interactionCount s₁ s₂ : ℝ≥0∞))
        = ((c.count s₁ * (c.card - 1) : ℕ) : ℝ≥0∞) := by
      rw [← Nat.cast_sum]
      exact_mod_cast congrArg (Nat.cast : ℕ → ℝ≥0∞) (Config.sum_interactionCount_right c s₁)
    calc (∑ s₂ : Λ, g s₁ * ((c.interactionCount s₁ s₂ : ℝ≥0∞) / (c.totalPairs : ℝ≥0∞)))
        = ∑ s₂ : Λ, (g s₁ * (c.interactionCount s₁ s₂ : ℝ≥0∞)) / (c.totalPairs : ℝ≥0∞) := by
          simp_rw [mul_div_assoc]
      _ = (∑ s₂ : Λ, g s₁ * (c.interactionCount s₁ s₂ : ℝ≥0∞)) / (c.totalPairs : ℝ≥0∞) := by
          simp_rw [div_eq_mul_inv, ← Finset.sum_mul]
      _ = (g s₁ * ∑ s₂ : Λ, (c.interactionCount s₁ s₂ : ℝ≥0∞)) / (c.totalPairs : ℝ≥0∞) := by
          rw [Finset.mul_sum]
      _ = g s₁ * ((c.count s₁ * (c.card - 1) : ℕ) : ℝ≥0∞) / (c.totalPairs : ℝ≥0∞) := by
          rw [hcount]
  rw [Finset.sum_congr rfl (fun s₁ _ => hinner s₁)]
  -- totalPairs = card*(card-1); cancel (card-1)
  have hcard1 : (1 : ℕ) ≤ c.card := by omega
  have htp : (c.totalPairs : ℝ≥0∞) = (c.card : ℝ≥0∞) * ((c.card - 1 : ℕ) : ℝ≥0∞) := by
    unfold Config.totalPairs
    rw [Nat.cast_mul]
  -- card ≠ 0, card-1 ≠ 0 (≠ top) for the cancellation.
  have hcardne : (c.card : ℝ≥0∞) ≠ 0 := by exact_mod_cast (by omega : c.card ≠ 0)
  have hc1ne : ((c.card - 1 : ℕ) : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast (by omega : (c.card - 1 : ℕ) ≠ 0)
  have hc1top : ((c.card - 1 : ℕ) : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  -- rewrite each summand: g s₁ * (count*(card-1))/(card*(card-1)) = g s₁ * count / card
  have hterm : ∀ s₁ : Λ,
      g s₁ * ((c.count s₁ * (c.card - 1) : ℕ) : ℝ≥0∞) / (c.totalPairs : ℝ≥0∞)
        = g s₁ * (c.count s₁ : ℝ≥0∞) / (c.card : ℝ≥0∞) := by
    intro s₁
    rw [htp, Nat.cast_mul]
    -- (g * (count*(card-1))) / (card*(card-1)) = (g*count)/card, cancel (card-1)
    rw [show g s₁ * ((c.count s₁ : ℝ≥0∞) * ((c.card - 1 : ℕ) : ℝ≥0∞))
          = (g s₁ * (c.count s₁ : ℝ≥0∞)) * ((c.card - 1 : ℕ) : ℝ≥0∞) by ring]
    rw [ENNReal.mul_div_mul_right _ _ hc1ne hc1top]
  rw [Finset.sum_congr rfl (fun s₁ _ => hterm s₁)]
  -- ∑ g s₁ * count s₁ / card = (∑ g s₁ * count s₁) / card = sumOf g c / card
  rw [show (∑ s₁ : Λ, g s₁ * (c.count s₁ : ℝ≥0∞) / (c.card : ℝ≥0∞))
        = (∑ s₁ : Λ, g s₁ * (c.count s₁ : ℝ≥0∞)) / (c.card : ℝ≥0∞) from
      by simp_rw [div_eq_mul_inv, ← Finset.sum_mul]]
  congr 1
  -- Config.sumOf g c = ∑_{s∈univ} g s * count s  (count = 0 off toFinset)
  unfold Config.sumOf
  rw [Finset.sum_multiset_map_count c g]
  -- restrict univ-sum to toFinset (zero summands off it), and nsmul → cast-mul
  rw [← Finset.sum_subset (Finset.subset_univ c.toFinset)
        (fun x _ hx => by
          rw [Multiset.mem_toFinset] at hx
          rw [Config.count, Multiset.count_eq_zero_of_notMem hx]
          simp)]
  refine Finset.sum_congr rfl (fun s₁ _ => ?_)
  rw [Config.count, nsmul_eq_mul, mul_comm]

/-- `interactionCount` is symmetric in its two state arguments. -/
private lemma interactionCount_comm (c : Config Λ) (s₁ s₂ : Λ) :
    c.interactionCount s₁ s₂ = c.interactionCount s₂ s₁ := by
  unfold Config.interactionCount
  by_cases h : s₁ = s₂
  · subst h; rfl
  · rw [if_neg h, if_neg (fun h' => h h'.symm), mul_comm]

/-- **Second-coordinate interaction marginal.**  By the symmetry of
`interactionCount`, summing any observable of the RESPONDER state against the
interaction law also gives the configuration average `Config.sumOf g c / card`. -/
theorem sum_snd_interactionProb (c : Config Λ) (hc : 2 ≤ c.card) (g : Λ → ℝ≥0∞) :
    (∑ pair : Λ × Λ, g pair.2 * c.interactionProb pair.1 pair.2)
      = Config.sumOf g c / (c.card : ℝ≥0∞) := by
  rw [← sum_fst_interactionProb c hc g]
  -- reindex by the swap (s₁,s₂) ↦ (s₂,s₁); interactionProb is symmetric.
  rw [← Equiv.sum_comp (Equiv.prodComm Λ Λ)
      (fun pair : Λ × Λ => g pair.1 * c.interactionProb pair.1 pair.2)]
  refine Finset.sum_congr rfl (fun pair _ => ?_)
  simp only [Equiv.prodComm_apply, Prod.fst_swap, Prod.snd_swap]
  rw [Config.interactionProb, Config.interactionProb, interactionCount_comm]

end SchedulerPairSum

/-! ## Localized per-pair potential decompositions (Gap-1 infrastructure).

The clock-counter potential `Φ_s = Config.sumOf clockSummand` is additive over the
multiset, so when a scheduled pair `{r₁, r₂}` is removed and the transition output
`{δ.1, δ.2}` re-inserted, the potential's change is LOCALIZED to those two agents:
both `Φ_s(c)` and `Φ_s(stepOrSelf c r₁ r₂)` share the common base
`Φ_s(c − {r₁, r₂})`, differing only in the two-agent summand block.  This is the
no-truncated-subtraction form of the per-pair ledger — the per-pair drift bound
then compares only `clockSummand δ.1 + clockSummand δ.2` against
`clockSummand r₁ + clockSummand r₂`. -/

/-- **Source-side potential split.**  If the ordered pair `{r₁, r₂}` is contained
in `c`, the potential splits as the base `Φ_s(c − {r₁, r₂})` plus the two source
summands. -/
theorem clockCounterPotential_eq_base_add_pair (s : ℝ)
    (c : Config (AgentState L K)) (r₁ r₂ : AgentState L K)
    (hle : ({r₁, r₂} : Config (AgentState L K)) ≤ c) :
    clockCounterPotential (L := L) (K := K) s c
      = Config.sumOf (clockSummand (L := L) (K := K) s) (c - {r₁, r₂})
        + (clockSummand (L := L) (K := K) s r₁ + clockSummand (L := L) (K := K) s r₂) := by
  unfold clockCounterPotential Config.sumOf
  conv_lhs => rw [← Multiset.sub_add_cancel hle]
  rw [Multiset.map_add, Multiset.sum_add]
  congr 1
  show clockSummand (L := L) (K := K) s r₁
         + (clockSummand (L := L) (K := K) s r₂ + 0) = _
  rw [add_zero]

/-- **Post-step potential split.**  When the scheduled pair is applicable, the
post-step potential splits as the same base `Φ_s(c − {r₁, r₂})` plus the two
TRANSITION-OUTPUT summands. -/
theorem clockCounterPotential_stepOrSelf_eq_base_add_pair (s : ℝ)
    (c : Config (AgentState L K)) (r₁ r₂ : AgentState L K)
    (happ : Protocol.Applicable c r₁ r₂) :
    clockCounterPotential (L := L) (K := K) s
        (Protocol.stepOrSelf (NonuniformMajority L K) c r₁ r₂)
      = Config.sumOf (clockSummand (L := L) (K := K) s) (c - {r₁, r₂})
        + (clockSummand (L := L) (K := K) s (Transition L K r₁ r₂).1
           + clockSummand (L := L) (K := K) s (Transition L K r₁ r₂).2) := by
  unfold clockCounterPotential Protocol.stepOrSelf
  rw [if_pos happ]
  show Config.sumOf _ (c - {r₁, r₂} + {_, _}) = _
  unfold Config.sumOf
  rw [Multiset.map_add, Multiset.sum_add]
  congr 1
  show clockSummand (L := L) (K := K) s (Transition L K r₁ r₂).1
         + (clockSummand (L := L) (K := K) s (Transition L K r₁ r₂).2 + 0) = _
  rw [add_zero]

/-! ## The clock–clock per-pair drift ledger (Gap-1 dominant case).

On the absorbing window where every clock has `counter > 0` (`noClockAtZero`), a
clock–clock meeting runs `stdCounterSubroutine` on both partners; with both
counters positive each simply DECREMENTS by 1 (the phase-advancing branch is the
`counter = 0` case, excluded on the window).  A decrement multiplies that clock's
summand `exp(−s·counter)` by EXACTLY `eˢ`.  Hence for a clock–clock phase-0 pair
at positive counters the output two-summand block is exactly `eˢ` times the source
block — the tightest per-pair contribution feeding the affine drift rate
`1 + 2(eˢ−1)/n`.  (The remaining per-pair cases — non-clock–clock pairs, where
clock counters are untouched except Rule-4 fresh clocks contribute the tiny
`exp(−s·50(L+1))` summand — close the affine bound; see the gap note below.) -/

/-- A clock whose counter DECREMENTS by 1 (staying a clock) scales its summand by
exactly `eˢ`: `exp(−s·(c−1)) = eˢ·exp(−s·c)` (`c ≥ 1`, so the ℕ-subtraction is
exact). -/
private lemma clockSummand_scale_of_decrement (s : ℝ) (a a' : AgentState L K)
    (hrole : a.role = .clock) (hrole' : a'.role = .clock)
    (hc : a.counter.val ≠ 0) (hc' : a'.counter.val = a.counter.val - 1) :
    clockSummand (L := L) (K := K) s a'
      = ENNReal.ofReal (Real.exp s) * clockSummand (L := L) (K := K) s a := by
  unfold clockSummand
  rw [if_pos hrole, if_pos hrole', hc']
  rw [← ENNReal.ofReal_mul (Real.exp_nonneg _), ← Real.exp_add]
  congr 2
  have h1 : (1:ℕ) ≤ a.counter.val := Nat.one_le_iff_ne_zero.mpr hc
  have : ((a.counter.val - 1 : ℕ) : ℝ) = (a.counter.val : ℝ) - 1 := by
    rw [Nat.cast_sub h1]; simp
  rw [this]; ring

/-- A clock–clock pair at positive counters: `Phase0Transition` keeps both as
clocks and decrements each counter by 1 (Rule 5 = `stdCounterSubroutine`, the
positive-counter branch). -/
private lemma clock_clock_decrement (r₁ r₂ : AgentState L K)
    (hr₁ : r₁.role = .clock) (hr₂ : r₂.role = .clock)
    (hc₁ : r₁.counter.val ≠ 0) (hc₂ : r₂.counter.val ≠ 0) :
    (Phase0Transition L K r₁ r₂).1.role = .clock
    ∧ (Phase0Transition L K r₁ r₂).1.counter.val = r₁.counter.val - 1
    ∧ (Phase0Transition L K r₁ r₂).2.role = .clock
    ∧ (Phase0Transition L K r₁ r₂).2.counter.val = r₂.counter.val - 1 := by
  unfold Phase0Transition
  simp only [hr₁, hr₂]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp_all [stdCounterSubroutine]

/-- A clock at the FULL counter `50(L+1)` has summand EXACTLY the fresh value
`ofReal(e^{−s·50(L+1)})`. -/
private lemma clockSummand_full (s : ℝ) (a : AgentState L K)
    (hrole : a.role = .clock) (hctr : a.counter.val = 50 * (L + 1)) :
    clockSummand (L := L) (K := K) s a
      = ENNReal.ofReal (Real.exp (-(s * (50 * (L + 1) : ℕ)))) := by
  unfold clockSummand
  rw [if_pos hrole, hctr]

set_option maxHeartbeats 1000000 in
/-- **LEFT output summand bound (not both clock).**  The `Phase0Transition` LEFT
output's clock summand is at most the LEFT source summand plus the fresh value.
The only way the LEFT output is a clock when not both sources are clocks is Rule 4
(`cr–cr`), giving a fresh clock at the full counter (summand = fresh value, source
summand `0`); otherwise a source clock is carried through unchanged. -/
private lemma Phase0Transition_left_summand_not_both (s : ℝ)
    (r₁ r₂ : AgentState L K)
    (hnbc : ¬ (r₁.role = .clock ∧ r₂.role = .clock)) :
    clockSummand (L := L) (K := K) s (Phase0Transition L K r₁ r₂).1
      ≤ clockSummand (L := L) (K := K) s r₁
        + ENNReal.ofReal (Real.exp (-(s * (50 * (L + 1) : ℕ)))) := by
  rcases r₁ with
    ⟨in₁, out₁, ph₁, role₁, asg₁, bias₁, sb₁, hr₁_, mn₁, fl₁, op₁, ctr₁⟩
  rcases r₂ with
    ⟨in₂, out₂, ph₂, role₂, asg₂, bias₂, sb₂, hr₂_, mn₂, fl₂, op₂, ctr₂⟩
  cases role₁ <;> cases role₂ <;> cases asg₁ <;> cases asg₂ <;>
    simp only [reduceCtorEq, not_and, not_true, not_false_iff, IsEmpty.forall_iff,
      forall_true_left, false_implies] at hnbc ⊢ <;>
    simp only [Phase0Transition, clockSummand, stdCounterSubroutine,
      reduceCtorEq, and_true, and_false, true_and, false_and, if_true, if_false,
      ite_true, ite_false] <;>
    first
      | exact le_add_right le_rfl
      | exact le_add_left le_rfl

set_option maxHeartbeats 1000000 in
/-- **RIGHT output summand bound (not both clock).**  The `Phase0Transition` RIGHT
output's clock summand is at most the RIGHT source summand: the RIGHT output is
NEVER a fresh clock (Rule 4 makes the RIGHT a reserve), and source clocks are
carried through unchanged. -/
private lemma Phase0Transition_right_summand_not_both (s : ℝ)
    (r₁ r₂ : AgentState L K)
    (hnbc : ¬ (r₁.role = .clock ∧ r₂.role = .clock)) :
    clockSummand (L := L) (K := K) s (Phase0Transition L K r₁ r₂).2
      ≤ clockSummand (L := L) (K := K) s r₂ := by
  rcases r₁ with
    ⟨in₁, out₁, ph₁, role₁, asg₁, bias₁, sb₁, hr₁_, mn₁, fl₁, op₁, ctr₁⟩
  rcases r₂ with
    ⟨in₂, out₂, ph₂, role₂, asg₂, bias₂, sb₂, hr₂_, mn₂, fl₂, op₂, ctr₂⟩
  cases role₁ <;> cases role₂ <;> cases asg₁ <;> cases asg₂ <;>
    simp only [reduceCtorEq, not_and, not_true, not_false_iff, IsEmpty.forall_iff,
      forall_true_left, false_implies] at hnbc ⊢ <;>
    simp only [Phase0Transition, clockSummand, stdCounterSubroutine,
      reduceCtorEq, and_true, and_false, true_and, false_and, if_true, if_false,
      ite_true, ite_false] <;>
    exact le_rfl

/-- **Non-both-clock per-pair OUTPUT bound.**  For a pair that is NOT both clocks,
the `Phase0Transition` output two-summand block is bounded by the source block
plus the single fresh-clock value `ofReal(e^{−s·50(L+1)})`.  Rule 4 (`cr–cr`) makes
the LEFT output a fresh clock at the full counter (RIGHT becomes reserve); all
other non-both-clock cases carry source clocks through unchanged (Rules 1–3 never
touch a clock's role or counter; Rule 5 is excluded). -/
private lemma Phase0Transition_summand_not_both_clock (s : ℝ)
    (r₁ r₂ : AgentState L K)
    (hnbc : ¬ (r₁.role = .clock ∧ r₂.role = .clock)) :
    clockSummand (L := L) (K := K) s (Phase0Transition L K r₁ r₂).1
      + clockSummand (L := L) (K := K) s (Phase0Transition L K r₁ r₂).2
      ≤ (clockSummand (L := L) (K := K) s r₁ + clockSummand (L := L) (K := K) s r₂)
        + ENNReal.ofReal (Real.exp (-(s * (50 * (L + 1) : ℕ)))) := by
  -- LEFT output ≤ source-left summand + fresh; RIGHT output ≤ source-right summand.
  refine le_trans (add_le_add
    (Phase0Transition_left_summand_not_both (L := L) (K := K) s r₁ r₂ hnbc)
    (Phase0Transition_right_summand_not_both (L := L) (K := K) s r₁ r₂ hnbc)) ?_
  -- `(a + M) + b ≤ (a + b) + M`, in fact equal by commutativity.
  rw [add_right_comm (clockSummand (L := L) (K := K) s r₁)
      (ENNReal.ofReal (Real.exp (-(s * (50 * (L + 1) : ℕ)))))
      (clockSummand (L := L) (K := K) s r₂)]

/-- **Clock–clock per-pair drift (full kernel).**  For a clock–clock pair both at
phase 0 with positive counters, the full Doty transition's output two-summand
block is EXACTLY `eˢ` times the source block:

  `Φ-summand(δ₁) + Φ-summand(δ₂) = eˢ · (Φ-summand(r₁) + Φ-summand(r₂))`.

The `Transition` wrapper is reduced to `Phase0Transition` at phase 0 via
`phaseEpidemicUpdate_eq_self_of_both_phase0` + `finishPhase10Entry_{role,counter}`
(which read only `role`/`counter`, the only fields `clockSummand` inspects). -/
theorem clockSummand_pair_clock_clock (s : ℝ) (r₁ r₂ : AgentState L K)
    (h₁ : r₁.phase.val = 0) (h₂ : r₂.phase.val = 0)
    (hr₁ : r₁.role = .clock) (hr₂ : r₂.role = .clock)
    (hc₁ : r₁.counter.val ≠ 0) (hc₂ : r₂.counter.val ≠ 0) :
    clockSummand (L := L) (K := K) s (Transition L K r₁ r₂).1
      + clockSummand (L := L) (K := K) s (Transition L K r₁ r₂).2
      = ENNReal.ofReal (Real.exp s)
        * (clockSummand (L := L) (K := K) s r₁ + clockSummand (L := L) (K := K) s r₂) := by
  have hpe := RoleSplitConcentration.phaseEpidemicUpdate_eq_self_of_both_phase0
    (L := L) (K := K) r₁ r₂ h₁ h₂
  have hr0 : r₁.phase = (⟨0, by omega⟩ : Fin _) := Fin.ext h₁
  have hrole1 : (Transition L K r₁ r₂).1.role = (Phase0Transition L K r₁ r₂).1.role := by
    unfold Transition; rw [hpe]; simp only [finishPhase10Entry_role_eq]; rw [hr0]
  have hrole2 : (Transition L K r₁ r₂).2.role = (Phase0Transition L K r₁ r₂).2.role := by
    unfold Transition; rw [hpe]; simp only [finishPhase10Entry_role_eq]; rw [hr0]
  have hctr1 : (Transition L K r₁ r₂).1.counter = (Phase0Transition L K r₁ r₂).1.counter := by
    unfold Transition; rw [hpe]; simp only [finishPhase10Entry_counter]; rw [hr0]
  have hctr2 : (Transition L K r₁ r₂).2.counter = (Phase0Transition L K r₁ r₂).2.counter := by
    unfold Transition; rw [hpe]; simp only [finishPhase10Entry_counter]; rw [hr0]
  obtain ⟨hp1role, hp1ctr, hp2role, hp2ctr⟩ := clock_clock_decrement r₁ r₂ hr₁ hr₂ hc₁ hc₂
  have hs1 : clockSummand (L := L) (K := K) s (Transition L K r₁ r₂).1
      = ENNReal.ofReal (Real.exp s) * clockSummand (L := L) (K := K) s r₁ := by
    apply clockSummand_scale_of_decrement s r₁ _ hr₁ (by rw [hrole1]; exact hp1role) hc₁
    rw [show ((Transition L K r₁ r₂).1.counter).val = ((Phase0Transition L K r₁ r₂).1.counter).val
          from by rw [hctr1]]; exact hp1ctr
  have hs2 : clockSummand (L := L) (K := K) s (Transition L K r₁ r₂).2
      = ENNReal.ofReal (Real.exp s) * clockSummand (L := L) (K := K) s r₂ := by
    apply clockSummand_scale_of_decrement s r₂ _ hr₂ (by rw [hrole2]; exact hp2role) hc₂
    rw [show ((Transition L K r₁ r₂).2.counter).val = ((Phase0Transition L K r₁ r₂).2.counter).val
          from by rw [hctr2]]; exact hp2ctr
  rw [hs1, hs2, mul_add]

/-- At phase 0, the full `Transition` output summands coincide with the
`Phase0Transition` output summands (the `clockSummand` reads only `role`/`counter`,
on which the `phaseEpidemicUpdate` pre-step and `finishPhase10Entry` post-step are
identities at phase 0). -/
private lemma Transition_summand_eq_phase0 (s : ℝ) (r₁ r₂ : AgentState L K)
    (h₁ : r₁.phase.val = 0) (h₂ : r₂.phase.val = 0) :
    clockSummand (L := L) (K := K) s (Transition L K r₁ r₂).1
        = clockSummand (L := L) (K := K) s (Phase0Transition L K r₁ r₂).1
    ∧ clockSummand (L := L) (K := K) s (Transition L K r₁ r₂).2
        = clockSummand (L := L) (K := K) s (Phase0Transition L K r₁ r₂).2 := by
  have hpe := RoleSplitConcentration.phaseEpidemicUpdate_eq_self_of_both_phase0
    (L := L) (K := K) r₁ r₂ h₁ h₂
  have hr0 : r₁.phase = (⟨0, by omega⟩ : Fin _) := Fin.ext h₁
  have hrole1 : (Transition L K r₁ r₂).1.role = (Phase0Transition L K r₁ r₂).1.role := by
    unfold Transition; rw [hpe]; simp only [finishPhase10Entry_role_eq]; rw [hr0]
  have hrole2 : (Transition L K r₁ r₂).2.role = (Phase0Transition L K r₁ r₂).2.role := by
    unfold Transition; rw [hpe]; simp only [finishPhase10Entry_role_eq]; rw [hr0]
  have hctr1 : (Transition L K r₁ r₂).1.counter = (Phase0Transition L K r₁ r₂).1.counter := by
    unfold Transition; rw [hpe]; simp only [finishPhase10Entry_counter]; rw [hr0]
  have hctr2 : (Transition L K r₁ r₂).2.counter = (Phase0Transition L K r₁ r₂).2.counter := by
    unfold Transition; rw [hpe]; simp only [finishPhase10Entry_counter]; rw [hr0]
  refine ⟨?_, ?_⟩ <;> unfold clockSummand
  · rw [hrole1, hctr1]
  · rw [hrole2, hctr2]

/-- Any clock summand is `≤ 1` (for `s ≥ 0`): `exp(−s·counter) ≤ exp(0) = 1` since
`counter ≥ 0`; a non-clock summand is `0 ≤ 1`. -/
private lemma clockSummand_le_one (s : ℝ) (hs : 0 ≤ s) (a : AgentState L K) :
    clockSummand (L := L) (K := K) s a ≤ 1 := by
  unfold clockSummand
  by_cases hrole : a.role = .clock
  · rw [if_pos hrole]
    rw [show (1 : ℝ≥0∞) = ENNReal.ofReal 1 from ENNReal.ofReal_one.symm]
    apply ENNReal.ofReal_le_ofReal
    rw [show (1 : ℝ) = Real.exp 0 from (Real.exp_zero).symm]
    apply Real.exp_le_exp.mpr
    have : (0 : ℝ) ≤ s * (a.counter.val : ℝ) := by positivity
    linarith
  · rw [if_neg hrole]; exact zero_le'

/-- A clock at counter `0` has summand EXACTLY `1`. -/
private lemma clockSummand_eq_one_of_zero (s : ℝ) (a : AgentState L K)
    (hrole : a.role = .clock) (hctr : a.counter.val = 0) :
    clockSummand (L := L) (K := K) s a = 1 := by
  unfold clockSummand; rw [if_pos hrole, hctr]; simp

/-- **Per-side clock–clock summand bound (LEFT), any counter.**  For a clock–clock
phase-0 pair, the LEFT output summand is `≤ eˢ·summand(r₁)`.  Positive counter:
EXACT `eˢ` decrement (via `clockSummand_pair_clock_clock`'s left half, which is
counter-`r₂`-independent — Rule 5 runs `stdCounterSubroutine` on each side
separately).  Counter `0`: `summand(r₁) = 1` and `summand(δ₁) ≤ 1 ≤ eˢ·1`. -/
private lemma clockSummand_clock_clock_left_le (s : ℝ) (hs : 0 ≤ s)
    (r₁ r₂ : AgentState L K) (h₁ : r₁.phase.val = 0) (h₂ : r₂.phase.val = 0)
    (hr₁ : r₁.role = .clock) (hr₂ : r₂.role = .clock) :
    clockSummand (L := L) (K := K) s (Transition L K r₁ r₂).1
      ≤ ENNReal.ofReal (Real.exp s) * clockSummand (L := L) (K := K) s r₁ := by
  have he1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (Real.exp s) := by
    rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal (Real.one_le_exp hs)
  -- reduce Transition.1 to Phase0Transition.1 (phase-0 identity), then to std(s4).
  obtain ⟨heq1, _⟩ := Transition_summand_eq_phase0 s r₁ r₂ h₁ h₂
  rw [heq1]
  by_cases hc₁ : r₁.counter.val = 0
  · -- summand δ₁ ≤ 1 = summand r₁ ≤ eˢ·summand r₁
    rw [clockSummand_eq_one_of_zero s r₁ hr₁ hc₁, mul_one]
    calc clockSummand (L := L) (K := K) s (Phase0Transition L K r₁ r₂).1
        ≤ 1 := clockSummand_le_one s hs _
      _ ≤ ENNReal.ofReal (Real.exp s) := he1
  · -- positive: exact decrement on the left side (Rule 5 left = std(r₁-clock)).
    have hdec : (Phase0Transition L K r₁ r₂).1.role = .clock
        ∧ (Phase0Transition L K r₁ r₂).1.counter.val = r₁.counter.val - 1 := by
      unfold Phase0Transition
      simp only [hr₁, hr₂]
      refine ⟨?_, ?_⟩ <;> simp_all [stdCounterSubroutine]
    rw [clockSummand_scale_of_decrement s r₁ _ hr₁ hdec.1 hc₁ hdec.2]

/-- **Per-side clock–clock summand bound (RIGHT), any counter.**  Symmetric to the
LEFT version: the RIGHT output summand is `≤ eˢ·summand(r₂)`. -/
private lemma clockSummand_clock_clock_right_le (s : ℝ) (hs : 0 ≤ s)
    (r₁ r₂ : AgentState L K) (h₁ : r₁.phase.val = 0) (h₂ : r₂.phase.val = 0)
    (hr₁ : r₁.role = .clock) (hr₂ : r₂.role = .clock) :
    clockSummand (L := L) (K := K) s (Transition L K r₁ r₂).2
      ≤ ENNReal.ofReal (Real.exp s) * clockSummand (L := L) (K := K) s r₂ := by
  have he1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (Real.exp s) := by
    rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal (Real.one_le_exp hs)
  obtain ⟨_, heq2⟩ := Transition_summand_eq_phase0 s r₁ r₂ h₁ h₂
  rw [heq2]
  by_cases hc₂ : r₂.counter.val = 0
  · rw [clockSummand_eq_one_of_zero s r₂ hr₂ hc₂, mul_one]
    calc clockSummand (L := L) (K := K) s (Phase0Transition L K r₁ r₂).2
        ≤ 1 := clockSummand_le_one s hs _
      _ ≤ ENNReal.ofReal (Real.exp s) := he1
  · have hdec : (Phase0Transition L K r₁ r₂).2.role = .clock
        ∧ (Phase0Transition L K r₁ r₂).2.counter.val = r₂.counter.val - 1 := by
      unfold Phase0Transition
      simp only [hr₁, hr₂]
      refine ⟨?_, ?_⟩ <;> simp_all [stdCounterSubroutine]
    rw [clockSummand_scale_of_decrement s r₂ _ hr₂ hdec.1 hc₂ hdec.2]

/-- **Unconditional clock–clock per-pair bound.**  For a clock–clock phase-0 pair
at ANY counters, the output block is `≤ eˢ·(source block)` (sum of the two per-side
bounds). -/
theorem clockSummand_pair_clock_clock_le (s : ℝ) (hs : 0 ≤ s) (r₁ r₂ : AgentState L K)
    (h₁ : r₁.phase.val = 0) (h₂ : r₂.phase.val = 0)
    (hr₁ : r₁.role = .clock) (hr₂ : r₂.role = .clock) :
    clockSummand (L := L) (K := K) s (Transition L K r₁ r₂).1
      + clockSummand (L := L) (K := K) s (Transition L K r₁ r₂).2
      ≤ ENNReal.ofReal (Real.exp s)
        * (clockSummand (L := L) (K := K) s r₁ + clockSummand (L := L) (K := K) s r₂) := by
  rw [mul_add]
  exact add_le_add
    (clockSummand_clock_clock_left_le s hs r₁ r₂ h₁ h₂ hr₁ hr₂)
    (clockSummand_clock_clock_right_le s hs r₁ r₂ h₁ h₂ hr₁ hr₂)

/-- **Universal per-pair OUTPUT bound (full kernel) — NO counter hypotheses.**  For
ANY phase-0 pair, the output two-summand block is bounded by `eˢ·(source block) +
e^{−s·50(L+1)}`.  Clock–clock pairs scale by `≤ eˢ` at ANY counters
(`clockSummand_pair_clock_clock_le`, including counter-`0` clocks via the `≤ 1`
bound); non-clock–clock pairs carry source clocks unchanged plus at most one Rule-4
fresh clock (`Phase0Transition_summand_not_both_clock`), bumped to `eˢ·sources` via
`eˢ ≥ 1`.  Requires only `s ≥ 0` — the absorbing-window predicate need NOT carry
`noClockAtZero`. -/
theorem clockSummand_pair_le (s : ℝ) (hs : 0 ≤ s) (r₁ r₂ : AgentState L K)
    (h₁ : r₁.phase.val = 0) (h₂ : r₂.phase.val = 0) :
    clockSummand (L := L) (K := K) s (Transition L K r₁ r₂).1
      + clockSummand (L := L) (K := K) s (Transition L K r₁ r₂).2
      ≤ ENNReal.ofReal (Real.exp s)
          * (clockSummand (L := L) (K := K) s r₁ + clockSummand (L := L) (K := K) s r₂)
        + ENNReal.ofReal (Real.exp (-(s * (50 * (L + 1) : ℕ)))) := by
  have he1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (Real.exp s) := by
    rw [show (1 : ℝ≥0∞) = ENNReal.ofReal 1 from (ENNReal.ofReal_one).symm]
    exact ENNReal.ofReal_le_ofReal (Real.one_le_exp hs)
  by_cases hcc : r₁.role = .clock ∧ r₂.role = .clock
  · -- clock–clock: ≤ eˢ (any counters), then add the (nonnegative) fresh term.
    refine le_trans (clockSummand_pair_clock_clock_le s hs r₁ r₂ h₁ h₂ hcc.1 hcc.2) ?_
    exact le_add_right le_rfl
  · -- non-clock–clock: ≤ sources + fresh ≤ eˢ·sources + fresh.
    obtain ⟨he1', he2'⟩ := Transition_summand_eq_phase0 s r₁ r₂ h₁ h₂
    rw [he1', he2']
    refine le_trans (Phase0Transition_summand_not_both_clock s r₁ r₂ hcc) ?_
    gcongr
    exact le_mul_of_one_le_left zero_le' he1

/-- **Per-pair potential bound (full kernel, on the window).**  On a configuration
where every agent is at phase 0 (`allPhase0`) and every clock has positive counter
(`noClockAtZero`), the one-step potential after scheduling ANY ordered pair is
bounded by the source potential plus an additive bump `(eˢ−1)·(the pair's source
summand block)` plus the single fresh-clock value:

  `Φ_s(stepOrSelf c r₁ r₂) ≤ Φ_s(c) + (eˢ−1)·(summand r₁+summand r₂) + e^{−s·50(L+1)}`.

For non-applicable pairs `stepOrSelf c = c`, so the bound is trivial; for
applicable pairs the localized splits localize the change to the two interacting
agents, where `clockSummand_pair_le` bounds the output block by `eˢ·sources +
fresh`, and `eˢ·x = x + (eˢ−1)·x` recombines with the base into the stated form. -/
theorem clockCounterPotential_stepOrSelf_le (s : ℝ) (hs : 0 ≤ s)
    (c : Config (AgentState L K)) (r₁ r₂ : AgentState L K)
    (hall : allPhase0 (L := L) (K := K) c) :
    clockCounterPotential (L := L) (K := K) s
        (Protocol.stepOrSelf (NonuniformMajority L K) c r₁ r₂)
      ≤ clockCounterPotential (L := L) (K := K) s c
        + ENNReal.ofReal (Real.exp s - 1)
            * (clockSummand (L := L) (K := K) s r₁ + clockSummand (L := L) (K := K) s r₂)
        + ENNReal.ofReal (Real.exp (-(s * (50 * (L + 1) : ℕ)))) := by
  by_cases happ : Protocol.Applicable c r₁ r₂
  · -- applicable: localize, then bound the output block.
    have hle : ({r₁, r₂} : Config (AgentState L K)) ≤ c := happ
    have hr₁ : r₁ ∈ c :=
      Multiset.mem_of_le hle (by simp)
    have hr₂ : r₂ ∈ c :=
      Multiset.mem_of_le hle (by simp)
    have h₁ : r₁.phase.val = 0 := by have := hall r₁ hr₁; simp [this]
    have h₂ : r₂.phase.val = 0 := by have := hall r₂ hr₂; simp [this]
    rw [clockCounterPotential_stepOrSelf_eq_base_add_pair s c r₁ r₂ happ]
    rw [clockCounterPotential_eq_base_add_pair s c r₁ r₂ hle]
    set base := Config.sumOf (clockSummand (L := L) (K := K) s) (c - {r₁, r₂})
    set S := clockSummand (L := L) (K := K) s r₁ + clockSummand (L := L) (K := K) s r₂
    set M := ENNReal.ofReal (Real.exp (-(s * (50 * (L + 1) : ℕ))))
    -- outputs ≤ eˢ·S + M ; and eˢ·S = S + (eˢ−1)·S.
    have hpair := clockSummand_pair_le s hs r₁ r₂ h₁ h₂
    have hofeq : ENNReal.ofReal (Real.exp s) = 1 + ENNReal.ofReal (Real.exp s - 1) := by
      rw [← ENNReal.ofReal_one,
          ← ENNReal.ofReal_add (by norm_num) (by linarith [Real.one_le_exp hs])]
      congr 1; ring
    have hexp_split : ENNReal.ofReal (Real.exp s) * S
        = S + ENNReal.ofReal (Real.exp s - 1) * S := by
      rw [hofeq, add_mul, one_mul]
    calc base + (clockSummand (L := L) (K := K) s (Transition L K r₁ r₂).1
            + clockSummand (L := L) (K := K) s (Transition L K r₁ r₂).2)
        ≤ base + (ENNReal.ofReal (Real.exp s) * S + M) := by gcongr
      _ = base + (S + ENNReal.ofReal (Real.exp s - 1) * S + M) := by rw [hexp_split]
      _ = base + S + ENNReal.ofReal (Real.exp s - 1) * S + M := by ring
  · -- non-applicable: stepOrSelf c = c, so LHS = Φ(c) ≤ RHS.
    rw [Protocol.stepOrSelf, if_neg happ]
    calc clockCounterPotential (L := L) (K := K) s c
        ≤ clockCounterPotential (L := L) (K := K) s c
          + ENNReal.ofReal (Real.exp s - 1)
              * (clockSummand (L := L) (K := K) s r₁ + clockSummand (L := L) (K := K) s r₂) :=
          le_add_right le_rfl
      _ ≤ _ := le_add_right le_rfl

/-! ## The affine one-step drift (Gap-1 capstone).

Summing the per-pair potential bound `clockCounterPotential_stepOrSelf_le` against
the interaction law and collapsing the two coordinate marginals
(`sum_fst/snd_interactionProb`, each `= Φ_s(c)/card`) yields the AFFINE one-step
drift on the absorbing window:

  `∫ Φ_s dK(c) ≤ (1 + 2(eˢ−1)/n)·Φ_s(c) + e^{−s·50(L+1)}`,

where the `2/n` factor is exactly `(1/n)+(1/n)` from the two marginals, and the
single additive `e^{−s·50(L+1)}` is the per-step fresh-clock immigration (one
fresh clock per step, since `∑ interactionProb = 1`).  This is the in-house
immigration+multiplicative pattern (`EarlyDripMarked.mgf_one_step`). -/

/-- **Affine one-step drift (full kernel, on the window).**  On a phase-0,
positive-counter configuration of size `n ≥ 2`, the clock-counter potential
contracts affinely:

  `∫ Φ_s dK(c) ≤ ofReal(1 + 2(eˢ−1)/n)·Φ_s(c) + ofReal(e^{−s·50(L+1)})`. -/
theorem clockCounterPotential_drift_affine (s : ℝ) (hs : 0 ≤ s)
    (n : ℕ) (c : Config (AgentState L K))
    (hcard : Multiset.card c = n) (hc2 : 2 ≤ Multiset.card c)
    (hall : allPhase0 (L := L) (K := K) c) :
    ∫⁻ c', clockCounterPotential (L := L) (K := K) s c'
        ∂((NonuniformMajority L K).transitionKernel c)
      ≤ ENNReal.ofReal (1 + 2 * (Real.exp s - 1) / (n : ℝ))
          * clockCounterPotential (L := L) (K := K) s c
        + ENNReal.ofReal (Real.exp (-(s * (50 * (L + 1) : ℕ)))) := by
  classical
  set Φ := clockCounterPotential (L := L) (K := K) s c with hΦ
  set M := ENNReal.ofReal (Real.exp (-(s * (50 * (L + 1) : ℕ)))) with hM
  -- 1) lintegral = pair sum.
  rw [lintegral_transitionKernel_eq_sum (NonuniformMajority L K) c hc2]
  -- 2) per-pair bound, summed.
  have hpp : ∀ pair : AgentState L K × AgentState L K,
      clockCounterPotential (L := L) (K := K) s
          (Protocol.stepOrSelf (NonuniformMajority L K) c pair.1 pair.2)
        * c.interactionProb pair.1 pair.2
      ≤ (Φ + ENNReal.ofReal (Real.exp s - 1)
            * (clockSummand (L := L) (K := K) s pair.1
               + clockSummand (L := L) (K := K) s pair.2) + M)
          * c.interactionProb pair.1 pair.2 := by
    intro pair
    gcongr
    exact clockCounterPotential_stepOrSelf_le s hs c pair.1 pair.2 hall
  refine le_trans (Finset.sum_le_sum (fun pair _ => hpp pair)) ?_
  -- 3) distribute the product over the three additive terms.
  simp_rw [add_mul]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  -- ∑ Φ·prob = Φ·∑prob = Φ·1 = Φ
  have hsumprob : (∑ pair : AgentState L K × AgentState L K,
      c.interactionProb pair.1 pair.2) = 1 := by
    have := (c.interactionPMF hc2).tsum_coe
    rw [tsum_eq_sum (s := Finset.univ) (by intro x hx; exact absurd (Finset.mem_univ x) hx)] at this
    convert this using 1
  have hΦsum : (∑ pair : AgentState L K × AgentState L K,
      Φ * c.interactionProb pair.1 pair.2) = Φ := by
    rw [← Finset.mul_sum, hsumprob, mul_one]
  have hMsum : (∑ pair : AgentState L K × AgentState L K,
      M * c.interactionProb pair.1 pair.2) = M := by
    rw [← Finset.mul_sum, hsumprob, mul_one]
  -- ∑ (eˢ-1)·(summand p₁+summand p₂)·prob = (eˢ-1)·(2Φ/n)
  have hmid : (∑ pair : AgentState L K × AgentState L K,
      ENNReal.ofReal (Real.exp s - 1)
        * (clockSummand (L := L) (K := K) s pair.1
           + clockSummand (L := L) (K := K) s pair.2)
        * c.interactionProb pair.1 pair.2)
      = ENNReal.ofReal (Real.exp s - 1) * (Φ / (n : ℝ≥0∞) + Φ / (n : ℝ≥0∞)) := by
    simp_rw [mul_assoc]
    rw [← Finset.mul_sum]
    congr 1
    -- ∑ (sf p₁ + sf p₂)·prob = ∑ sf p₁·prob + ∑ sf p₂·prob = Φ/n + Φ/n
    have hsplit : ∀ pair : AgentState L K × AgentState L K,
        (clockSummand (L := L) (K := K) s pair.1
           + clockSummand (L := L) (K := K) s pair.2) * c.interactionProb pair.1 pair.2
          = clockSummand (L := L) (K := K) s pair.1 * c.interactionProb pair.1 pair.2
            + clockSummand (L := L) (K := K) s pair.2 * c.interactionProb pair.1 pair.2 := by
      intro pair; rw [add_mul]
    rw [Finset.sum_congr rfl (fun pair _ => hsplit pair), Finset.sum_add_distrib]
    rw [sum_fst_interactionProb c hc2 (clockSummand (L := L) (K := K) s),
        sum_snd_interactionProb c hc2 (clockSummand (L := L) (K := K) s)]
    rw [hcard]; rfl
  rw [hΦsum, hMsum, hmid]
  -- 4) the affine recombination is an EXACT equality on the Φ-part.
  refine le_of_eq ?_
  congr 1
  -- Φ + (eˢ-1)·(Φ/n + Φ/n) = ofReal(1 + 2(eˢ-1)/n)·Φ
  have hnpos : (0 : ℝ) < (n : ℝ) := by
    have : 2 ≤ n := by rw [← hcard]; exact hc2
    exact_mod_cast (by omega : 0 < n)
  have hnne : (n : ℝ≥0∞) ≠ 0 := by exact_mod_cast (by positivity : (n:ℝ) ≠ 0)
  have hntop : (n : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top n
  have he1 : (0 : ℝ) ≤ Real.exp s - 1 := by linarith [Real.one_le_exp hs]
  -- ofReal(1 + 2(eˢ-1)/n) = 1 + ofReal(eˢ-1)·(2/n) (with 2/n = ofReal 2 / ofReal n)
  have hofac : ENNReal.ofReal (1 + 2 * (Real.exp s - 1) / (n : ℝ))
      = 1 + ENNReal.ofReal (Real.exp s - 1) * ((2 : ℝ≥0∞) / (n : ℝ≥0∞)) := by
    rw [ENNReal.ofReal_add (by norm_num) (by positivity)]
    rw [ENNReal.ofReal_one]
    congr 1
    rw [show 2 * (Real.exp s - 1) / (n : ℝ) = (Real.exp s - 1) * (2 / (n : ℝ)) by ring]
    rw [ENNReal.ofReal_mul he1]
    congr 1
    rw [ENNReal.ofReal_div_of_pos hnpos, ENNReal.ofReal_natCast]
    norm_num
  rw [hofac, add_mul, one_mul]
  congr 1
  -- (eˢ-1)·(Φ/n + Φ/n) = ofReal(eˢ-1)·(2/n)·Φ
  rw [mul_assoc]
  congr 1
  -- Φ/n + Φ/n = (2/n)·Φ
  rw [ENNReal.div_add_div_same, ← two_mul]
  rw [mul_comm (2 : ℝ≥0∞) Φ, mul_div_assoc, mul_comm ((2:ℝ≥0∞)/(n:ℝ≥0∞)) Φ,
      ← mul_div_assoc]

/-! ## The affine-drift tail engine (immigration + multiplicative).

The affine drift `∫ Φ dK(c) ≤ a·Φ(c) + b` on an absorbing window does NOT fit the
purely-multiplicative `WindowConcentration.windowDrift_tail` (which needs `b = 0`),
because the per-step fresh-clock immigration `b` keeps the potential from
contracting to `0` (and at a clock-free start `Φ = 0` while `b > 0`, so no
multiplicative rate can hold).  We build the affine analogue here, mirroring
`lintegral_decay_on_absorbing` with the immigration term: iterating
`∫ Φ dK ≤ a·Φ + b` gives `∫ Φ d(Kᵗ)c₀ ≤ aᵗ·Φ(c₀) + b·∑_{i<t} aⁱ`, then Markov at
threshold `θ` yields the tail `(Kᵗ)c₀{¬Post} ≤ (aᵗ·Φ(c₀) + b·∑_{i<t}aⁱ)/θ`. -/

/-- **Affine lintegral decay on an absorbing window.**  Given the affine one-step
drift `∫ Φ dK(c) ≤ a·Φ(c) + b` on the absorbing window `Q`, the `t`-step
expectation of `Φ` is bounded by `aᵗ·Φ(c₀) + b·∑_{i<t} aⁱ`. -/
theorem lintegral_decay_affine_on_absorbing (P : Protocol (AgentState L K))
    (Φ : Config (AgentState L K) → ℝ≥0∞) (hΦ : Measurable Φ)
    (Q : Config (AgentState L K) → Prop)
    (hQ_abs : ∀ c c', Q c → c' ∈ (P.stepDistOrSelf c).support → Q c')
    (a b : ℝ≥0∞)
    (hdrift : ∀ c, Q c → ∫⁻ c', Φ c' ∂(P.transitionKernel c) ≤ a * Φ c + b)
    (t : ℕ) (c₀ : Config (AgentState L K)) (hQ0 : Q c₀) :
    ∫⁻ c', Φ c' ∂((P.transitionKernel ^ t) c₀)
      ≤ a ^ t * Φ c₀ + b * ∑ i ∈ Finset.range t, a ^ i := by
  induction t generalizing c₀ with
  | zero =>
    simp only [pow_zero, one_mul, Finset.range_zero, Finset.sum_empty, mul_zero, add_zero]
    change ∫⁻ c', Φ c' ∂(Kernel.id c₀) ≤ Φ c₀
    rw [Kernel.id_apply, lintegral_dirac' c₀ hΦ]
  | succ t ih =>
    change ∫⁻ c', Φ c' ∂(((P.transitionKernel ^ t) ∘ₖ P.transitionKernel) c₀)
      ≤ a ^ (t + 1) * Φ c₀ + b * ∑ i ∈ Finset.range (t + 1), a ^ i
    rw [Kernel.lintegral_comp _ _ c₀ hΦ]
    have hae : ∀ᵐ d ∂(P.transitionKernel c₀),
        ∫⁻ c', Φ c' ∂((P.transitionKernel ^ t) d)
          ≤ a ^ t * Φ d + b * ∑ i ∈ Finset.range t, a ^ i := by
      have hsupp_ae : ∀ᵐ d ∂(P.transitionKernel c₀), Q d := by
        have h1 := Protocol.ae_of_stepDistOrSelf_support_preserved P Q hQ_abs c₀ hQ0 1
        simpa [pow_one] using h1
      filter_upwards [hsupp_ae] with d hd
      exact ih d hd
    calc ∫⁻ d, ∫⁻ c', Φ c' ∂((P.transitionKernel ^ t) d) ∂(P.transitionKernel c₀)
        ≤ ∫⁻ d, (a ^ t * Φ d + b * ∑ i ∈ Finset.range t, a ^ i)
            ∂(P.transitionKernel c₀) := lintegral_mono_ae hae
      _ = a ^ t * (∫⁻ d, Φ d ∂(P.transitionKernel c₀))
            + b * (∑ i ∈ Finset.range t, a ^ i) := by
          rw [lintegral_add_right _ measurable_const, lintegral_const_mul _ hΦ,
              lintegral_const, measure_univ, mul_one]
      _ ≤ a ^ t * (a * Φ c₀ + b) + b * (∑ i ∈ Finset.range t, a ^ i) := by
          gcongr; exact hdrift c₀ hQ0
      _ = a ^ (t + 1) * Φ c₀ + b * ∑ i ∈ Finset.range (t + 1), a ^ i := by
          rw [Finset.sum_range_succ, mul_add, mul_add]
          rw [show a ^ t * (a * Φ c₀) = a ^ (t + 1) * Φ c₀ by rw [pow_succ]; ring]
          rw [show a ^ t * b = b * a ^ t by ring]
          ring

/-- **Affine window tail.**  From the affine drift `∫ Φ dK(c) ≤ a·Φ(c) + b` on the
absorbing window `Q`, with threshold link `¬Post c → θ ≤ Φ c` (`θ ≠ 0, ⊤`), the
`t`-step failure probability is bounded by `(aᵗ·Φ(c₀) + b·∑_{i<t}aⁱ)/θ`. -/
theorem phase0_window_tail_affine (P : Protocol (AgentState L K))
    (Φ : Config (AgentState L K) → ℝ≥0∞) (hΦ : Measurable Φ)
    (Q : Config (AgentState L K) → Prop)
    (hQ_abs : ∀ c c', Q c → c' ∈ (P.stepDistOrSelf c).support → Q c')
    (a b : ℝ≥0∞)
    (hdrift : ∀ c, Q c → ∫⁻ c', Φ c' ∂(P.transitionKernel c) ≤ a * Φ c + b)
    (Post : Config (AgentState L K) → Prop)
    (θ : ℝ≥0∞) (hθ : θ ≠ 0) (hθ_top : θ ≠ ⊤)
    (hlink : ∀ c, ¬ Post c → θ ≤ Φ c)
    (t : ℕ) (c₀ : Config (AgentState L K)) (hQ0 : Q c₀) :
    (P.transitionKernel ^ t) c₀ {c | ¬ Post c}
      ≤ (a ^ t * Φ c₀ + b * ∑ i ∈ Finset.range t, a ^ i) / θ := by
  have hsubset : {c | ¬ Post c} ⊆ {c | θ ≤ Φ c} := fun c hc => hlink c hc
  refine (measure_mono hsubset).trans ?_
  -- Markov at θ + affine decay.
  have hmarkov := mul_meas_ge_le_lintegral₀ (μ := (P.transitionKernel ^ t) c₀)
    hΦ.aemeasurable θ
  have hdecay := lintegral_decay_affine_on_absorbing P Φ hΦ Q hQ_abs a b hdrift t c₀ hQ0
  have hchain : θ * (P.transitionKernel ^ t) c₀ {c | θ ≤ Φ c}
      ≤ a ^ t * Φ c₀ + b * ∑ i ∈ Finset.range t, a ^ i := le_trans hmarkov hdecay
  rw [ENNReal.le_div_iff_mul_le (Or.inl hθ) (Or.inl hθ_top), mul_comm]
  exact hchain

/-! ## The kernel-level tail from a supplied one-step drift.

This wraps `WindowConcentration.windowDrift_tail` at the Phase-0 instantiation:
the potential `Φ_s`, threshold `θ = 1`, postcondition `noClockAtZero`.  The
one-step contraction `∫ Φ_s dK(c) ≤ r · Φ_s c` is taken on an absorbing window
`Q` exactly as the engine does — the deep quantitative scheduler computation
(`ClockTickDrift`, recorded below) discharges it with `r = 1 + 2(e^s−1)/n`.  The
output is the clean geometric tail. -/

/-- **Phase-0 window tail from drift.**  Given an absorbing window `Q`
containing the start, on which the clock-counter potential `Φ_s` contracts at
rate `r`, the `t`-step probability that SOME clock has reached `counter = 0` is
at most the geometric tail `rᵗ · Φ_s(c₀)`:

  `(K^t) c₀ {∃ clock counter = 0} ≤ rᵗ · Φ_s(c₀)`. -/
theorem phase0_window_tail_of_drift (P : Protocol (AgentState L K))
    (s : ℝ)
    (Q : Config (AgentState L K) → Prop)
    (hQ_abs : ∀ c c', Q c → c' ∈ (P.stepDistOrSelf c).support → Q c')
    (r : ℝ≥0∞)
    (hdrift : ∀ c, Q c →
      ∫⁻ c', clockCounterPotential (L := L) (K := K) s c'
        ∂(P.transitionKernel c) ≤ r * clockCounterPotential (L := L) (K := K) s c)
    (t : ℕ) (c₀ : Config (AgentState L K)) (hQ0 : Q c₀) :
    (P.transitionKernel ^ t) c₀ {c | ¬ noClockAtZero (L := L) (K := K) c}
      ≤ r ^ t * clockCounterPotential (L := L) (K := K) s c₀ := by
  have h := WindowConcentration.windowDrift_tail P
    (clockCounterPotential (L := L) (K := K) s)
    (measurable_clockCounterPotential s)
    Q hQ_abs r hdrift
    (noClockAtZero (L := L) (K := K))
    (θ := 1) (by norm_num) (by norm_num)
    (fun c hc => clockCounterPotential_ge_one_of_not_noClockAtZero s c hc)
    t c₀ hQ0
  simpa using h

/-! ## The initial-potential bound.

At a phase-0 start, every clock's counter is at its full value `50(L+1)`
(`Transition.phaseInit` Rule 4), so each clock summand is `e^{−s·50(L+1)}` and
`Φ_s(c₀) ≤ (clockCount) · e^{−s·50(L+1)} ≤ n · e^{−s·50(L+1)}` (`clockCount ≤
card = n`). -/

/-- **Initial-potential bound.**  If every clock in `c` has the full counter
`50(L+1)` and `card c = n`, then `Φ_s(c) ≤ n · e^{−s·50(L+1)}`.  Each clock
summand is EXACTLY `e^{−s·50(L+1)}` (counter is exactly full); the sum over
`≤ n` agents gives the `n·M` bound. -/
theorem clockCounterPotential_init_le (s : ℝ)
    (n : ℕ) (c : Config (AgentState L K))
    (hcard : Multiset.card c = n)
    (hfull : ∀ a ∈ c, a.role = .clock → a.counter.val = 50 * (L + 1)) :
    clockCounterPotential (L := L) (K := K) s c
      ≤ (n : ℝ≥0∞) * ENNReal.ofReal (Real.exp (-(s * (50 * (L + 1) : ℕ)))) := by
  unfold clockCounterPotential Config.sumOf
  set M : ℝ≥0∞ := ENNReal.ofReal (Real.exp (-(s * (50 * (L + 1) : ℕ)))) with hM
  -- every summand is ≤ M
  have hbound : ∀ x ∈ Multiset.map (clockSummand (L := L) (K := K) s) c, x ≤ M := by
    intro x hx
    rw [Multiset.mem_map] at hx
    obtain ⟨a, ha, rfl⟩ := hx
    unfold clockSummand
    by_cases hrole : a.role = .clock
    · rw [if_pos hrole, hfull a ha hrole, hM]
    · rw [if_neg hrole]; exact zero_le'
  calc (Multiset.map (clockSummand (L := L) (K := K) s) c).sum
      ≤ Multiset.card (Multiset.map (clockSummand (L := L) (K := K) s) c) • M :=
        Multiset.sum_le_card_nsmul _ M hbound
    _ = (n : ℝ≥0∞) * M := by
        rw [Multiset.card_map, hcard, nsmul_eq_mul]

/-! ## The numerics at the concrete constants (`s = 1`, `k = 50(L+1)`).

The drift rate is `r = 1 + 2(e−1)/n`; the window is `t ≤ n·(L+1)` interactions
(`δ ≤ 1`); the initial potential is `≤ n·e^{−50(L+1)}`.  We show the geometric
tail closes to `e^{−45(L+1)} ≤ n^{−45}`.

The chain (over ℝ):
* `(1 + 2(e−1)/n)^t ≤ exp(t·2(e−1)/n) ≤ exp(2(e−1)(L+1))`  (`1+x ≤ e^x`,
  then `t ≤ n(L+1)`);
* `n ≤ exp(L+1)`  (`ln n ≤ L+1`);
* product `≤ exp((2(e−1) + 1 − 50)(L+1)) = exp((2e − 51)(L+1)) ≤ exp(−45(L+1))`
  since `2e ≤ 6`. -/

/-- **Phase-0 window numerics (real).**  With the drift rate `1 + 2(e−1)/n`, a
window of `t ≤ n·(L+1)` interactions, and initial potential `n·e^{−50(L+1)}`,
the geometric tail is at most `e^{−45(L+1)}`.  Requires `n ≥ 1`,
`ln n ≤ (L+1)`, and `t ≤ n·(L+1)`. -/
theorem phase0_numerics_real (n L t : ℕ) (hn : 1 ≤ n)
    (hlog : Real.log (n : ℝ) ≤ (L + 1 : ℕ)) (ht : t ≤ n * (L + 1)) :
    (1 + 2 * (Real.exp 1 - 1) / (n : ℝ)) ^ t
        * ((n : ℝ) * Real.exp (-(50 * (L + 1) : ℕ)))
      ≤ Real.exp (-(45 * (L + 1) : ℕ)) := by
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have he1 : (0 : ℝ) ≤ Real.exp 1 - 1 := by
    linarith [Real.add_one_le_exp (1 : ℝ)]
  set x : ℝ := 2 * (Real.exp 1 - 1) / (n : ℝ) with hx
  have hx0 : 0 ≤ x := by rw [hx]; positivity
  -- (1+x)^t ≤ exp(t·x)
  have hstep1 : (1 + x) ^ t ≤ Real.exp ((t : ℝ) * x) := by
    rw [Real.exp_nat_mul]
    exact pow_le_pow_left₀ (by linarith) (by rw [add_comm]; exact Real.add_one_le_exp x) t
  -- t·x ≤ 2(e−1)(L+1)
  have hLpos : (0 : ℝ) ≤ (L + 1 : ℕ) := by positivity
  have htx : (t : ℝ) * x ≤ 2 * (Real.exp 1 - 1) * (L + 1 : ℕ) := by
    have htn : (t : ℝ) ≤ (n : ℝ) * (L + 1 : ℕ) := by
      have : (t : ℝ) ≤ ((n * (L + 1) : ℕ) : ℝ) := by exact_mod_cast ht
      rwa [Nat.cast_mul] at this
    rw [hx]
    rw [show (t : ℝ) * (2 * (Real.exp 1 - 1) / (n : ℝ))
          = (2 * (Real.exp 1 - 1)) * ((t : ℝ) / (n : ℝ)) by ring]
    have hdiv : (t : ℝ) / (n : ℝ) ≤ (L + 1 : ℕ) := by
      rw [div_le_iff₀ hnpos]; rw [mul_comm]; exact htn
    have h2e : 0 ≤ 2 * (Real.exp 1 - 1) := by linarith
    calc (2 * (Real.exp 1 - 1)) * ((t : ℝ) / (n : ℝ))
        ≤ (2 * (Real.exp 1 - 1)) * (L + 1 : ℕ) := by
          exact mul_le_mul_of_nonneg_left hdiv h2e
      _ = 2 * (Real.exp 1 - 1) * (L + 1 : ℕ) := rfl
  -- n ≤ exp(L+1)
  have hn_exp : (n : ℝ) ≤ Real.exp (L + 1 : ℕ) := by
    have hlogle : Real.log (n : ℝ) ≤ (L + 1 : ℕ) := hlog
    calc (n : ℝ) = Real.exp (Real.log (n : ℝ)) := (Real.exp_log hnpos).symm
      _ ≤ Real.exp (L + 1 : ℕ) := Real.exp_le_exp.mpr hlogle
  -- assemble
  have hpow_nonneg : (0 : ℝ) ≤ (1 + x) ^ t := by positivity
  calc (1 + x) ^ t * ((n : ℝ) * Real.exp (-(50 * (L + 1) : ℕ)))
      ≤ Real.exp ((t : ℝ) * x) * (Real.exp (L + 1 : ℕ) * Real.exp (-(50 * (L + 1) : ℕ))) := by
        apply mul_le_mul hstep1 ?_ ?_ (by positivity)
        · exact mul_le_mul_of_nonneg_right hn_exp (by positivity)
        · positivity
    _ ≤ Real.exp (2 * (Real.exp 1 - 1) * (L + 1 : ℕ))
          * (Real.exp (L + 1 : ℕ) * Real.exp (-(50 * (L + 1) : ℕ))) := by
        apply mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr htx) (by positivity)
    _ = Real.exp ((2 * (Real.exp 1 - 1) + 1 - 50) * (L + 1 : ℕ)) := by
        rw [← Real.exp_add, ← Real.exp_add]
        congr 1
        push_cast
        ring
    _ ≤ Real.exp (-(45 * (L + 1) : ℕ)) := by
        apply Real.exp_le_exp.mpr
        have he3 : Real.exp 1 ≤ 3 := by
          have := Real.exp_one_lt_d9; linarith
        have hcoef : (2 * (Real.exp 1 - 1) + 1 - 50) ≤ -45 := by nlinarith [he3]
        push_cast
        nlinarith [hLpos, hcoef, mul_le_mul_of_nonneg_right hcoef hLpos]

/-! ## The packaged whp window corollary.

Combining the three closed pieces — the tail from drift
(`phase0_window_tail_of_drift`), the initial-potential bound
(`clockCounterPotential_init_le`), and the real numerics
(`phase0_numerics_real`) — at the concrete drift rate
`r = ofReal(1 + 2(e−1)/n)`, scale `s = 1`, the `t`-step probability that SOME
clock has reached `counter = 0` is at most `e^{−45(L+1)} ≤ n^{−45}`. -/

/-- **Phase-0 window whp (packaged).**  Given an absorbing window `Q` on which
the clock-counter potential `Φ_1` contracts at the concrete rate
`ofReal(1 + 2(e−1)/n)`, a phase-0 start where every clock is at full counter
`50(L+1)` and `card c₀ = n`, a window `t ≤ n(L+1)` and `ln n ≤ (L+1)`, the
probability that some clock reached `counter = 0` within `t` steps is at most
`ofReal(e^{−45(L+1)})`:

  `(K^t) c₀ {∃ clock counter = 0} ≤ ofReal(e^{−45(L+1)})`. -/
theorem phase0_window_whp (P : Protocol (AgentState L K))
    (n : ℕ) (hn : 1 ≤ n)
    (Q : Config (AgentState L K) → Prop)
    (hQ_abs : ∀ c c', Q c → c' ∈ (P.stepDistOrSelf c).support → Q c')
    (hdrift : ∀ c, Q c →
      ∫⁻ c', clockCounterPotential (L := L) (K := K) 1 c'
        ∂(P.transitionKernel c)
        ≤ ENNReal.ofReal (1 + 2 * (Real.exp 1 - 1) / (n : ℝ))
            * clockCounterPotential (L := L) (K := K) 1 c)
    (t : ℕ) (ht : t ≤ n * (L + 1))
    (hlog : Real.log (n : ℝ) ≤ (L + 1 : ℕ))
    (c₀ : Config (AgentState L K)) (hQ0 : Q c₀)
    (hcard : Multiset.card c₀ = n)
    (hfull : ∀ a ∈ c₀, a.role = .clock → a.counter.val = 50 * (L + 1)) :
    (P.transitionKernel ^ t) c₀ {c | ¬ noClockAtZero (L := L) (K := K) c}
      ≤ ENNReal.ofReal (Real.exp (-(45 * (L + 1) : ℕ))) := by
  set r : ℝ≥0∞ := ENNReal.ofReal (1 + 2 * (Real.exp 1 - 1) / (n : ℝ)) with hr
  -- tail from drift
  have htail := phase0_window_tail_of_drift P 1 Q hQ_abs r hdrift t c₀ hQ0
  -- init bound on Φ₁(c₀)
  have hinit := clockCounterPotential_init_le (L := L) (K := K) 1 n c₀ hcard hfull
  -- combine: tail ≤ r^t · Φ₁(c₀) ≤ r^t · (n · e^{−50(L+1)})
  refine htail.trans ?_
  refine (by gcongr : r ^ t * clockCounterPotential (L := L) (K := K) 1 c₀
      ≤ r ^ t * ((n : ℝ≥0∞) * ENNReal.ofReal (Real.exp (-(1 * (50 * (L + 1) : ℕ)))))).trans ?_
  -- now an all-ENNReal-ofReal computation; push everything through ofReal
  have hbase_nonneg : (0 : ℝ) ≤ 1 + 2 * (Real.exp 1 - 1) / (n : ℝ) := by
    have : (0 : ℝ) ≤ 2 * (Real.exp 1 - 1) / (n : ℝ) := by
      have he1 : (0 : ℝ) ≤ Real.exp 1 - 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
      positivity
    linarith
  have hexp_nonneg : (0 : ℝ) ≤ Real.exp (-(50 * (L + 1) : ℕ)) := (Real.exp_pos _).le
  -- r^t = ofReal((1+x)^t)
  have hrt : r ^ t = ENNReal.ofReal ((1 + 2 * (Real.exp 1 - 1) / (n : ℝ)) ^ t) := by
    rw [hr, ← ENNReal.ofReal_pow hbase_nonneg]
  -- n = ofReal n
  have hncast : (n : ℝ≥0∞) = ENNReal.ofReal (n : ℝ) := by rw [ENNReal.ofReal_natCast]
  rw [hrt, hncast, ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_mul (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  -- the `s = 1` substitution left a stray `1 *` in the exponent; clear it
  simp only [one_mul]
  -- the real numerics; the LHS shape `a * (n * e)` matches `phase0_numerics_real`
  exact phase0_numerics_real n L t hn hlog ht

/-! ## The relay-11 phase-0-CR shell-escape corollary.

Relay-11's Stage-2 milestone (see `DOTY_POST63_CAMPAIGN.md` §C-1) needs the
**phase-0-CR shell escape** bound: the genuinely-probabilistic event "a CR
advanced past phase 0".  By the Doty trace structure that event is contained in
the clock-zero event the window bounds (a CR's phase advance is driven by the
clock counter / epidemic — the only phase-0 exit fires at a clock `counter =
0`).  We expose the bound for ANY shell-escape predicate `Esc` whose
realization is contained in `{∃ clock counter = 0}` (the deterministic
containment is supplied as `hcontain`, mirroring `windowDrift_tail`'s `hlink`),
so relay-11 instantiates it at its concrete `crPhase0Shell` escape. -/

/-- **Phase-0-CR shell escape ≤ the window bound.**  For any escape predicate
`Esc` whose `t`-step realization is contained in the clock-zero event
(`hcontain`), the escape probability is bounded by the Phase-0 window bound
`ofReal(e^{−45(L+1)})`.  Relay-11 instantiates `Esc := "a CR has phase ≠ 0"`. -/
theorem phase0CRShellEscape_le (P : Protocol (AgentState L K))
    (n : ℕ) (hn : 1 ≤ n)
    (Q : Config (AgentState L K) → Prop)
    (hQ_abs : ∀ c c', Q c → c' ∈ (P.stepDistOrSelf c).support → Q c')
    (hdrift : ∀ c, Q c →
      ∫⁻ c', clockCounterPotential (L := L) (K := K) 1 c'
        ∂(P.transitionKernel c)
        ≤ ENNReal.ofReal (1 + 2 * (Real.exp 1 - 1) / (n : ℝ))
            * clockCounterPotential (L := L) (K := K) 1 c)
    (t : ℕ) (ht : t ≤ n * (L + 1))
    (hlog : Real.log (n : ℝ) ≤ (L + 1 : ℕ))
    (c₀ : Config (AgentState L K)) (hQ0 : Q c₀)
    (hcard : Multiset.card c₀ = n)
    (hfull : ∀ a ∈ c₀, a.role = .clock → a.counter.val = 50 * (L + 1))
    (Esc : Config (AgentState L K) → Prop)
    (hcontain : ∀ c, Esc c → ¬ noClockAtZero (L := L) (K := K) c) :
    (P.transitionKernel ^ t) c₀ {c | Esc c}
      ≤ ENNReal.ofReal (Real.exp (-(45 * (L + 1) : ℕ))) := by
  refine (measure_mono ?_).trans
    (phase0_window_whp P n hn Q hQ_abs hdrift t ht hlog c₀ hQ0 hcard hfull)
  intro c hc
  exact hcontain c hc

/-! ## Gap 2 — the deterministic phase-0-exit bridge (NOW DISCHARGED).

We close the deterministic half of the `allPhase0` → window corollary: a single
scheduled interaction can drop an agent out of phase 0 ONLY via Rule 5 of
`Phase0Transition` (`stdCounterSubroutine` on a clock–clock pair), and that rule
advances phase ONLY when the source clock's `counter = 0`.  Tracing the
`Phase0Transition` let-cascade (Rules 1–3 never touch `counter` nor create
clocks; Rule 4 creates a clock with the FULL counter `50(L+1) ≠ 0`) shows a
phase-0 exit forces a SOURCE-config clock at `counter = 0` — i.e. a witness to
`¬ noClockAtZero`.  Lifting through the full `Transition` wrapper (identity on
phase at phase 0, via `phaseEpidemicUpdate_eq_self_of_both_phase0` and
`finishPhase10Entry_phase_val`) and an abstract prefix-union first-exit bound
yields the `allPhase0` window corollary. -/

/-- `stdCounterSubroutine` advances phase only when `counter = 0`. -/
private lemma stdCounter_phase_pos_imp_counter_zero (a : AgentState L K)
    (h : a.phase.val < (stdCounterSubroutine L K a).phase.val) : a.counter.val = 0 := by
  unfold stdCounterSubroutine at h
  split at h
  · assumption
  · simp at h

/-- **Per-pair phase-0 exit (LEFT output).**  If `s` is at phase 0 and the
`Phase0Transition` LEFT output has phase `> 0`, then the source agent `s` was a
clock with `counter = 0`.  (Only Rule 5 `stdCounterSubroutine` advances phase;
it advances only at `counter = 0`; Rule 4 fresh clocks have full counter ≠ 0;
Rules 1–3 neither touch `counter` nor produce clocks.) -/
theorem Phase0Transition_left_phase_pos_imp_src_clock_zero
    (s t : AgentState L K) (hs0 : s.phase.val = 0)
    (hexit : 0 < (Phase0Transition L K s t).1.phase.val) :
    s.role = .clock ∧ s.counter.val = 0 := by
  let s1 := if s.role = .mcr ∧ t.role = .mcr then
    { s with role := .main, smallBias := addSmallBias s.smallBias t.smallBias } else s
  let t1 := if s.role = .mcr ∧ t.role = .mcr then
    { t with role := .cr, smallBias := ⟨3, by decide⟩ } else t
  let s2 := if s1.role = .mcr ∧ t1.role = .main ∧ ¬ t1.assigned then
    { s1 with role := .cr, smallBias := ⟨3, by decide⟩ }
    else if t1.role = .mcr ∧ s1.role = .main ∧ ¬ s1.assigned then
    { s1 with assigned := true, smallBias := addSmallBias t1.smallBias s1.smallBias }
    else s1
  let t2 := if s1.role = .mcr ∧ t1.role = .main ∧ ¬ t1.assigned then
    { t1 with assigned := true, smallBias := addSmallBias s1.smallBias t1.smallBias }
    else if t1.role = .mcr ∧ s1.role = .main ∧ ¬ s1.assigned then
    { t1 with role := .cr, smallBias := ⟨3, by decide⟩ }
    else t1
  let s3 := if s2.role = .mcr ∧ t2.role ≠ .main ∧ t2.role ≠ .mcr ∧ ¬ t2.assigned then
    { s2 with role := .main }
    else if t2.role = .mcr ∧ s2.role ≠ .main ∧ s2.role ≠ .mcr ∧ ¬ s2.assigned then
    { s2 with assigned := true } else s2
  let t3 := if s2.role = .mcr ∧ t2.role ≠ .main ∧ t2.role ≠ .mcr ∧ ¬ t2.assigned then
    { t2 with assigned := true }
    else if t2.role = .mcr ∧ s2.role ≠ .main ∧ s2.role ≠ .mcr ∧ ¬ s2.assigned then
    { t2 with role := .main }
    else t2
  let s3' := s3
  let t3' := t3
  let s4 := if s3'.role = .cr ∧ t3'.role = .cr then
    { s3' with role := .clock, counter := ⟨50 * (L + 1), by omega⟩ } else s3'
  let t4 := if s3'.role = .cr ∧ t3'.role = .cr then
    { t3' with role := .reserve } else t3'
  let s5 := if s4.role = .clock ∧ t4.role = .clock then stdCounterSubroutine L K s4 else s4
  change 0 < s5.phase.val at hexit
  have hc1 : s1.counter = s.counter := by dsimp [s1]; split_ifs <;> rfl
  have hc2 : s2.counter = s1.counter := by dsimp [s2]; split_ifs <;> rfl
  have hc3 : s3.counter = s2.counter := by dsimp [s3]; split_ifs <;> rfl
  have hc3' : s3'.counter = s3.counter := rfl
  have hr1 : s1.role = .clock → s.role = .clock := by dsimp [s1]; split_ifs <;> simp
  have hr2 : s2.role = .clock → s1.role = .clock := by dsimp [s2]; split_ifs <;> simp
  have hr3 : s3.role = .clock → s2.role = .clock := by dsimp [s3]; split_ifs <;> simp
  have hp1 : s1.phase.val = s.phase.val := by dsimp [s1]; split_ifs <;> rfl
  have hp2 : s2.phase.val = s1.phase.val := by dsimp [s2]; split_ifs <;> rfl
  have hp3 : s3.phase.val = s2.phase.val := by dsimp [s3]; split_ifs <;> rfl
  have hp4 : s4.phase.val = s3'.phase.val := by dsimp [s4]; split_ifs <;> rfl
  have hs4phase0 : s4.phase.val = 0 := by
    rw [hp4]; show s3.phase.val = 0; rw [hp3, hp2, hp1, hs0]
  by_cases hcc : s4.role = .clock ∧ t4.role = .clock
  · have hs5 : s5 = stdCounterSubroutine L K s4 := by dsimp [s5]; rw [if_pos hcc]
    rw [hs5] at hexit
    have hs4ctr0 : s4.counter.val = 0 :=
      stdCounter_phase_pos_imp_counter_zero s4 (by rw [hs4phase0]; exact hexit)
    have hs4_eq : s4 = s3' := by
      dsimp [s4]; split_ifs with h
      · exfalso
        have : s4.counter.val = 50 * (L+1) := by dsimp [s4]; rw [if_pos h]
        omega
      · rfl
    have hs4role : s4.role = .clock := hcc.1
    have hs3'clock : s3'.role = .clock := by rw [← hs4_eq]; exact hs4role
    have hsrole : s.role = .clock := hr1 (hr2 (hr3 hs3'clock))
    have hsctr : s.counter.val = 0 := by
      have : s4.counter = s.counter := by rw [hs4_eq, hc3', hc3, hc2, hc1]
      rw [← this]; exact hs4ctr0
    exact ⟨hsrole, hsctr⟩
  · exfalso
    have hs5 : s5 = s4 := by dsimp [s5]; rw [if_neg hcc]
    rw [hs5, hs4phase0] at hexit
    exact absurd hexit (by omega)

/-- **Per-pair phase-0 exit (RIGHT output).**  Symmetric to the LEFT case. -/
theorem Phase0Transition_right_phase_pos_imp_src_clock_zero
    (s t : AgentState L K) (ht0 : t.phase.val = 0)
    (hexit : 0 < (Phase0Transition L K s t).2.phase.val) :
    t.role = .clock ∧ t.counter.val = 0 := by
  let s1 := if s.role = .mcr ∧ t.role = .mcr then
    { s with role := .main, smallBias := addSmallBias s.smallBias t.smallBias } else s
  let t1 := if s.role = .mcr ∧ t.role = .mcr then
    { t with role := .cr, smallBias := ⟨3, by decide⟩ } else t
  let s2 := if s1.role = .mcr ∧ t1.role = .main ∧ ¬ t1.assigned then
    { s1 with role := .cr, smallBias := ⟨3, by decide⟩ }
    else if t1.role = .mcr ∧ s1.role = .main ∧ ¬ s1.assigned then
    { s1 with assigned := true, smallBias := addSmallBias t1.smallBias s1.smallBias }
    else s1
  let t2 := if s1.role = .mcr ∧ t1.role = .main ∧ ¬ t1.assigned then
    { t1 with assigned := true, smallBias := addSmallBias s1.smallBias t1.smallBias }
    else if t1.role = .mcr ∧ s1.role = .main ∧ ¬ s1.assigned then
    { t1 with role := .cr, smallBias := ⟨3, by decide⟩ }
    else t1
  let s3 := if s2.role = .mcr ∧ t2.role ≠ .main ∧ t2.role ≠ .mcr ∧ ¬ t2.assigned then
    { s2 with role := .main }
    else if t2.role = .mcr ∧ s2.role ≠ .main ∧ s2.role ≠ .mcr ∧ ¬ s2.assigned then
    { s2 with assigned := true } else s2
  let t3 := if s2.role = .mcr ∧ t2.role ≠ .main ∧ t2.role ≠ .mcr ∧ ¬ t2.assigned then
    { t2 with assigned := true }
    else if t2.role = .mcr ∧ s2.role ≠ .main ∧ s2.role ≠ .mcr ∧ ¬ s2.assigned then
    { t2 with role := .main }
    else t2
  let s3' := s3
  let t3' := t3
  let s4 := if s3'.role = .cr ∧ t3'.role = .cr then
    { s3' with role := .clock, counter := ⟨50 * (L + 1), by omega⟩ } else s3'
  let t4 := if s3'.role = .cr ∧ t3'.role = .cr then
    { t3' with role := .reserve } else t3'
  let t5 := if s4.role = .clock ∧ t4.role = .clock then stdCounterSubroutine L K t4 else t4
  change 0 < t5.phase.val at hexit
  have hc1 : t1.counter = t.counter := by dsimp [t1]; split_ifs <;> rfl
  have hc2 : t2.counter = t1.counter := by dsimp [t2]; split_ifs <;> rfl
  have hc3 : t3.counter = t2.counter := by dsimp [t3]; split_ifs <;> rfl
  have hc3' : t3'.counter = t3.counter := rfl
  have hc4 : t4.counter = t3'.counter := by dsimp [t4]; split_ifs <;> rfl
  have hr1 : t1.role = .clock → t.role = .clock := by dsimp [t1]; split_ifs <;> simp
  have hr2 : t2.role = .clock → t1.role = .clock := by dsimp [t2]; split_ifs <;> simp
  have hr3 : t3.role = .clock → t2.role = .clock := by dsimp [t3]; split_ifs <;> simp
  have hr4 : t4.role = .clock → t3'.role = .clock := by dsimp [t4]; split_ifs <;> simp
  have hp1 : t1.phase.val = t.phase.val := by dsimp [t1]; split_ifs <;> rfl
  have hp2 : t2.phase.val = t1.phase.val := by dsimp [t2]; split_ifs <;> rfl
  have hp3 : t3.phase.val = t2.phase.val := by dsimp [t3]; split_ifs <;> rfl
  have hp4 : t4.phase.val = t3'.phase.val := by dsimp [t4]; split_ifs <;> rfl
  have ht4phase0 : t4.phase.val = 0 := by
    rw [hp4]; show t3.phase.val = 0; rw [hp3, hp2, hp1, ht0]
  by_cases hcc : s4.role = .clock ∧ t4.role = .clock
  · have ht5 : t5 = stdCounterSubroutine L K t4 := by dsimp [t5]; rw [if_pos hcc]
    rw [ht5] at hexit
    have ht4ctr0 : t4.counter.val = 0 :=
      stdCounter_phase_pos_imp_counter_zero t4 (by rw [ht4phase0]; exact hexit)
    have ht4role : t4.role = .clock := hcc.2
    have ht3'clock : t3'.role = .clock := hr4 ht4role
    have htrole : t.role = .clock := hr1 (hr2 (hr3 ht3'clock))
    have htctr : t.counter.val = 0 := by
      have : t4.counter = t.counter := by rw [hc4, hc3', hc3, hc2, hc1]
      rw [← this]; exact ht4ctr0
    exact ⟨htrole, htctr⟩
  · exfalso
    have ht5 : t5 = t4 := by dsimp [t5]; rw [if_neg hcc]
    rw [ht5, ht4phase0] at hexit
    exact absurd hexit (by omega)

/-- The full `Transition` dispatcher agrees with `Phase0Transition` on the
output phase when both agents start at phase 0 (the `phaseEpidemicUpdate`
pre-step and `finishPhase10Entry` post-step are phase-identities there). -/
theorem Transition_phase_eq_phase0_of_both_phase0
    (s t : AgentState L K) (hs : s.phase.val = 0) (ht : t.phase.val = 0) :
    (Transition L K s t).1.phase.val = (Phase0Transition L K s t).1.phase.val ∧
    (Transition L K s t).2.phase.val = (Phase0Transition L K s t).2.phase.val := by
  have hpe := RoleSplitConcentration.phaseEpidemicUpdate_eq_self_of_both_phase0
    (L := L) (K := K) s t hs ht
  have hs0 : s.phase = (⟨0, by omega⟩ : Fin _) := Fin.ext hs
  unfold Transition
  rw [hpe]
  simp only [finishPhase10Entry_phase_val]
  rw [hs0]
  exact ⟨rfl, rfl⟩

/-- **The deterministic single-step phase-0-exit fact (full kernel).**  In the
real Doty kernel `NonuniformMajority L K`, a single scheduled interaction taking
an `allPhase0` configuration out of `allPhase0` forces a SOURCE-config clock at
`counter = 0` (a witness to `¬ noClockAtZero`).  Equivalently (contrapositive),
from an `allPhase0 ∧ noClockAtZero` configuration `allPhase0` is preserved one
step. -/
theorem det_phase0_exit
    (c : Config (AgentState L K)) (r₁ r₂ : AgentState L K)
    (hall : allPhase0 (L := L) (K := K) c)
    (hexit : ¬ allPhase0 (L := L) (K := K)
      (Protocol.stepOrSelf (NonuniformMajority L K) c r₁ r₂)) :
    ¬ noClockAtZero (L := L) (K := K) c := by
  unfold Protocol.stepOrSelf at hexit
  by_cases happ : Protocol.Applicable c r₁ r₂
  · rw [if_pos happ] at hexit
    unfold allPhase0 at hexit
    push Not at hexit
    obtain ⟨a, ha_mem, ha_phase⟩ := hexit
    rw [Multiset.mem_add] at ha_mem
    have hr₁_mem : r₁ ∈ c :=
      Multiset.mem_of_le (show ({r₁, r₂} : Multiset (AgentState L K)) ≤ c from happ) (by simp)
    have hr₂_mem : r₂ ∈ c :=
      Multiset.mem_of_le (show ({r₁, r₂} : Multiset (AgentState L K)) ≤ c from happ) (by simp)
    have hr₁0 : r₁.phase.val = 0 := by have := hall r₁ hr₁_mem; simp [this]
    have hr₂0 : r₂.phase.val = 0 := by have := hall r₂ hr₂_mem; simp [this]
    rcases ha_mem with hsub | hnew
    · exfalso
      exact ha_phase (hall a (Multiset.mem_of_le (Multiset.sub_le_self _ _) hsub))
    · have hδ : (NonuniformMajority L K).δ r₁ r₂ = Transition L K r₁ r₂ := rfl
      simp only [hδ] at hnew
      rw [show ({(Transition L K r₁ r₂).1, (Transition L K r₁ r₂).2}
            : Multiset (AgentState L K))
          = (Transition L K r₁ r₂).1 ::ₘ {(Transition L K r₁ r₂).2} from rfl] at hnew
      rw [Multiset.mem_cons, Multiset.mem_singleton] at hnew
      have hapos : 0 < a.phase.val := Nat.pos_of_ne_zero (fun h => ha_phase (Fin.ext h))
      rcases hnew with h1 | h2
      · subst h1
        have hph := (Transition_phase_eq_phase0_of_both_phase0 r₁ r₂ hr₁0 hr₂0).1
        rw [hph] at hapos
        obtain ⟨hrole, hctr⟩ :=
          Phase0Transition_left_phase_pos_imp_src_clock_zero r₁ r₂ hr₁0 hapos
        exact fun hno => (hno r₁ hr₁_mem hrole) hctr
      · subst h2
        have hph := (Transition_phase_eq_phase0_of_both_phase0 r₁ r₂ hr₁0 hr₂0).2
        rw [hph] at hapos
        obtain ⟨hrole, hctr⟩ :=
          Phase0Transition_right_phase_pos_imp_src_clock_zero r₁ r₂ hr₂0 hapos
        exact fun hno => (hno r₂ hr₂_mem hrole) hctr
  · rw [if_neg happ] at hexit
    exact absurd hall hexit

/-- **The kernel-level one-step preservation.**  From an `allPhase0 ∧
noClockAtZero` configuration, the real Doty kernel keeps `allPhase0` after one
step with probability 1 — i.e. the `¬ allPhase0` mass is `0`. -/
theorem transitionKernel_not_allPhase0_eq_zero_of_noClockAtZero
    (c : Config (AgentState L K))
    (hall : allPhase0 (L := L) (K := K) c)
    (hno : noClockAtZero (L := L) (K := K) c) :
    (NonuniformMajority L K).transitionKernel c
        {c' | ¬ allPhase0 (L := L) (K := K) c'} = 0 := by
  change ((NonuniformMajority L K).stepDistOrSelf c).toMeasure
      {c' | ¬ allPhase0 (L := L) (K := K) c'} = 0
  rw [PMF.toMeasure_apply_eq_zero_iff _
    (DiscreteMeasurableSpace.forall_measurableSet _)]
  rw [Set.disjoint_left]
  intro c' hsupp hbad
  -- every support point is `stepOrSelf c r₁ r₂`; det_phase0_exit forbids exit
  have hreach := (NonuniformMajority L K).stepDistOrSelf_support_reachable c c' hsupp
  -- decompose support point
  unfold Protocol.stepDistOrSelf at hsupp
  by_cases hc2 : 2 ≤ c.card
  · rw [dif_pos hc2] at hsupp
    obtain ⟨⟨r₁, r₂⟩, hr⟩ := Protocol.stepDist_support _ c hc2 c' hsupp
    have : ¬ allPhase0 (L := L) (K := K)
        (Protocol.stepOrSelf (NonuniformMajority L K) c r₁ r₂) := by
      rw [show Protocol.stepOrSelf (NonuniformMajority L K) c r₁ r₂
            = Protocol.scheduledStep (NonuniformMajority L K) c (r₁, r₂) from rfl, hr]
      exact hbad
    exact (det_phase0_exit c r₁ r₂ hall this) hno
  · rw [dif_neg hc2, PMF.mem_support_pure_iff] at hsupp
    subst hsupp
    exact hbad hall

/-- **Abstract prefix-union first-exit bound.**  If from any state where the
window predicate `A` holds AND the per-step guard `G` holds, `A` cannot break in
one step (`hstep : A x → G x → Kk x {¬A} = 0`), then the probability of `¬A`
after `t` steps is at most the prefix sum of the guard-breach probabilities
`∑_{τ<t} (Kk^τ) x₀ {¬G}`.  This is the standard first-exit / hitting-time
prefix-union argument (cf. `EarlyDripMarked.invariant_union_bound`), peeling the
last step and splitting the step-`t` integration region by the guard. -/
theorem prefix_union_first_exit {α : Type*} [MeasurableSpace α]
    [DiscreteMeasurableSpace α]
    (Kk : Kernel α α) [IsMarkovKernel Kk] (A G : α → Prop)
    (hstep : ∀ x, A x → G x → Kk x {y | ¬ A y} = 0)
    (t : ℕ) (x₀ : α) (h0 : A x₀) :
    (Kk ^ t) x₀ {y | ¬ A y} ≤ ∑ τ ∈ Finset.range t, (Kk ^ τ) x₀ {y | ¬ G y} := by
  classical
  have hmeasA : MeasurableSet {y : α | ¬ A y} := DiscreteMeasurableSpace.forall_measurableSet _
  have hmeasG : MeasurableSet {y : α | ¬ G y} := DiscreteMeasurableSpace.forall_measurableSet _
  induction t with
  | zero =>
      simp only [pow_zero, Finset.range_zero, Finset.sum_empty, le_zero_iff]
      change (Kernel.id x₀) {y | ¬ A y} = 0
      rw [Kernel.id_apply, Measure.dirac_apply' _ hmeasA]
      simp [Set.indicator_of_notMem (show x₀ ∉ {y : α | ¬ A y} from fun hc => hc h0)]
  | succ t ih =>
      rw [Kernel.pow_succ_apply_eq_lintegral Kk t x₀ hmeasA]
      set EG : Set α := {b | G b} with hEG
      have hEG_meas : MeasurableSet EG := DiscreteMeasurableSpace.forall_measurableSet _
      rw [← lintegral_add_compl _ hEG_meas]
      have hboundG : (∫⁻ b in EG, (Kk b) {y | ¬ A y} ∂((Kk ^ t) x₀))
          ≤ (Kk ^ t) x₀ {y | ¬ A y} := by
        calc (∫⁻ b in EG, (Kk b) {y | ¬ A y} ∂((Kk ^ t) x₀))
            ≤ ∫⁻ b in EG, {y : α | ¬ A y}.indicator (fun _ => (1:ℝ≥0∞)) b ∂((Kk ^ t) x₀) := by
              apply lintegral_mono_ae
              filter_upwards [ae_restrict_mem hEG_meas] with b hb
              by_cases hAb : A b
              · rw [hstep b hAb hb]; exact zero_le'
              · rw [Set.indicator_of_mem (show b ∈ {y | ¬ A y} from hAb)]
                haveI : IsProbabilityMeasure (Kk b) :=
                  (inferInstance : IsMarkovKernel Kk).isProbabilityMeasure b
                exact (measure_mono (Set.subset_univ _)).trans_eq measure_univ
          _ ≤ ∫⁻ b, {y : α | ¬ A y}.indicator (fun _ => (1:ℝ≥0∞)) b ∂((Kk ^ t) x₀) :=
              setLIntegral_le_lintegral _ _
          _ = (Kk ^ t) x₀ {y | ¬ A y} := by
              rw [lintegral_indicator hmeasA, lintegral_one, Measure.restrict_apply_univ]
      have hboundGc : (∫⁻ b in EGᶜ, (Kk b) {y | ¬ A y} ∂((Kk ^ t) x₀))
          ≤ (Kk ^ t) x₀ {y | ¬ G y} := by
        calc (∫⁻ b in EGᶜ, (Kk b) {y | ¬ A y} ∂((Kk ^ t) x₀))
            ≤ ∫⁻ _ in EGᶜ, (1 : ℝ≥0∞) ∂((Kk ^ t) x₀) := by
              apply lintegral_mono_ae
              filter_upwards with b
              haveI : IsProbabilityMeasure (Kk b) :=
                (inferInstance : IsMarkovKernel Kk).isProbabilityMeasure b
              exact (measure_mono (Set.subset_univ _)).trans_eq measure_univ
          _ = (Kk ^ t) x₀ EGᶜ := by rw [lintegral_const, Measure.restrict_apply_univ, one_mul]
          _ = (Kk ^ t) x₀ {y | ¬ G y} := by congr 1
      calc (∫⁻ b in EG, (Kk b) {y | ¬ A y} ∂((Kk ^ t) x₀))
            + ∫⁻ b in EGᶜ, (Kk b) {y | ¬ A y} ∂((Kk ^ t) x₀)
          ≤ (Kk ^ t) x₀ {y | ¬ A y} + (Kk ^ t) x₀ {y | ¬ G y} :=
            add_le_add hboundG hboundGc
        _ ≤ (∑ τ ∈ Finset.range t, (Kk ^ τ) x₀ {y | ¬ G y}) + (Kk ^ t) x₀ {y | ¬ G y} := by
            gcongr
        _ = ∑ τ ∈ Finset.range (t + 1), (Kk ^ τ) x₀ {y | ¬ G y} := by
            rw [Finset.sum_range_succ]

/-! ## The assembled `allPhase0` window corollary.

Instantiating the prefix-union bound with `A := allPhase0`, guard
`G := noClockAtZero`, and the deterministic single-step preservation
`transitionKernel_not_allPhase0_eq_zero_of_noClockAtZero` reduces the
`allPhase0`-window failure to the prefix sum of per-`τ` clock-zero probabilities,
each of which is bounded by the window bound `ofReal(e^{−45(L+1)})` via
`phase0_window_whp` — provided the per-`τ` drift / start hypotheses hold along
the trajectory.  We package the clean prefix-union step here; the per-`τ`
clock-zero bound is `phase0_window_whp`. -/

/-- **`allPhase0` window via prefix-union.**  In the real Doty kernel, starting
from an `allPhase0` configuration, the probability that SOME agent has left phase
0 within `t` steps is at most the prefix sum of the per-step clock-zero
probabilities:

  `(K^t) c₀ {¬ allPhase0} ≤ ∑_{τ<t} (K^τ) c₀ {¬ noClockAtZero}`. -/
theorem allPhase0_window_le_prefix_sum
    (t : ℕ) (c₀ : Config (AgentState L K))
    (h0 : allPhase0 (L := L) (K := K) c₀) :
    ((NonuniformMajority L K).transitionKernel ^ t) c₀
        {c | ¬ allPhase0 (L := L) (K := K) c}
      ≤ ∑ τ ∈ Finset.range t,
          ((NonuniformMajority L K).transitionKernel ^ τ) c₀
            {c | ¬ noClockAtZero (L := L) (K := K) c} :=
  prefix_union_first_exit (NonuniformMajority L K).transitionKernel
    (allPhase0 (L := L) (K := K)) (noClockAtZero (L := L) (K := K))
    (fun x hA hG => transitionKernel_not_allPhase0_eq_zero_of_noClockAtZero x hA hG)
    t c₀ h0

/-- **`allPhase0` window whp (assembled).**  If, in addition, an absorbing window
`Q` carrying the clock-counter drift contains `c₀` and is preserved (so each
per-`τ` clock-zero probability is at most the window bound `ofReal(e^{−45(L+1)})`
via `phase0_window_whp`), then the `allPhase0`-window failure is at most
`t · ofReal(e^{−45(L+1)})`.

We require: the drift hypothesis on `Q`, `Q` absorbing, `c₀ ∈ Q` with the full
counters / cardinality / `ln n ≤ L+1` window hypotheses, and that every reachable
configuration along the prefix still satisfies the per-`τ` `phase0_window_whp`
preconditions — packaged as the uniform per-`τ` clock-zero bound `hτ`. -/
theorem allPhase0_window_whp
    (t : ℕ) (c₀ : Config (AgentState L K))
    (h0 : allPhase0 (L := L) (K := K) c₀)
    (hτ : ∀ τ ∈ Finset.range t,
      ((NonuniformMajority L K).transitionKernel ^ τ) c₀
          {c | ¬ noClockAtZero (L := L) (K := K) c}
        ≤ ENNReal.ofReal (Real.exp (-(45 * (L + 1) : ℕ)))) :
    ((NonuniformMajority L K).transitionKernel ^ t) c₀
        {c | ¬ allPhase0 (L := L) (K := K) c}
      ≤ (t : ℝ≥0∞) * ENNReal.ofReal (Real.exp (-(45 * (L + 1) : ℕ))) := by
  refine (allPhase0_window_le_prefix_sum t c₀ h0).trans ?_
  calc ∑ τ ∈ Finset.range t,
          ((NonuniformMajority L K).transitionKernel ^ τ) c₀
            {c | ¬ noClockAtZero (L := L) (K := K) c}
      ≤ ∑ _τ ∈ Finset.range t, ENNReal.ofReal (Real.exp (-(45 * (L + 1) : ℕ))) :=
        Finset.sum_le_sum hτ
    _ = (t : ℝ≥0∞) * ENNReal.ofReal (Real.exp (-(45 * (L + 1) : ℕ))) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

/-! ## Precise remaining gaps to the campaign (for downstream relays).

Everything above is 0-sorry / axiom-clean.  GAP 2 (the deterministic
phase-0-exit bridge + the prefix-union lift) is now DISCHARGED above
(`det_phase0_exit`, `transitionKernel_not_allPhase0_eq_zero_of_noClockAtZero`,
`prefix_union_first_exit`, `allPhase0_window_le_prefix_sum`,
`allPhase0_window_whp`).  One input remains to fully close the
`allPhase0` → `PhaseConvergence` timing half; it is deliberately taken as a
hypothesis above (mirroring how `WindowConcentration.windowDrift_tail` itself
takes its one-step drift as input), so it is stated here with its exact goal.

**Gap 1 — the quantitative one-step drift `hdrift` (the scheduler core) — the
AFFINE DRIFT and its TAIL ENGINE are now FULLY PROVEN (C-0w12..18).**

The full affine one-step drift on the phase-0 / positive-counter window is
`clockCounterPotential_drift_affine`:

  `∫ Φ_s dK(c) ≤ ofReal(1 + 2(eˢ−1)/n) · Φ_s(c) + ofReal(e^{−s·50(L+1)})`,

i.e. multiplicative rate `1 + 2(eˢ−1)/n` PLUS a single additive fresh-clock
immigration `e^{−s·50(L+1)}` per step.  Built bottom-up, all 0-sorry axiom-clean:
* `lintegral_transitionKernel_eq_sum` — lintegral = `interactionProb`-weighted pair
  sum;
* `clockCounterPotential_{eq_base_add_pair, stepOrSelf_eq_base_add_pair}` — the
  localized (no-truncated-subtraction) per-pair potential splits;
* `clockSummand_pair_clock_clock` — clock–clock at positive counters scales by
  EXACTLY `eˢ`;
* `Phase0Transition_{left,right}_summand_not_both`,
  `Phase0Transition_summand_not_both_clock` — the NON-clock–clock per-pair output
  ledger (Rule 4 adds ONE fresh `e^{−s·50(L+1)}`, all else carried unchanged);
* `clockSummand_pair_le` — the UNIVERSAL per-pair output bound
  `summand(δ₁)+summand(δ₂) ≤ eˢ·(sources) + fresh` (clock–clock exact, non-cc bumped
  via `eˢ ≥ 1`);
* `sum_fst_interactionProb` / `sum_snd_interactionProb` — the two interaction
  marginals, each `= Φ_s(c)/card` (the scheduler's exact `1/n`-marginal, giving the
  `2/n` pair-count factor);
* `clockCounterPotential_stepOrSelf_le` — the per-pair potential bound
  `Φ(stepOrSelf) ≤ Φ(c) + (eˢ−1)·(pair-block) + fresh`;
* `clockCounterPotential_drift_affine` — the CAPSTONE, summing the per-pair bound
  against the marginals (`2(eˢ−1)/n`) plus one fresh immigration per step
  (`∑ interactionProb = 1`).
The AFFINE TAIL ENGINE (the immigration analogue of
`WindowConcentration.lintegral_decay_on_absorbing`, which only handles the
multiplicative `b = 0` case) is also built:
* `lintegral_decay_affine_on_absorbing` — `∫ Φ d(Kᵗ)c₀ ≤ aᵗ·Φ(c₀) + b·∑_{i<t}aⁱ`;
* `phase0_window_tail_affine` — the Markov tail
  `(Kᵗ)c₀{¬Post} ≤ (aᵗ·Φ(c₀) + b·∑_{i<t}aⁱ)/θ`.
The affine `+b` is ESSENTIAL (not absorbable into a multiplicative rate): at a
clock-free phase-0 start `Φ = 0` while `b > 0`, so no rate `r` with `∫Φ ≤ rΦ`
exists.  The numerics close with slack: `aᵗ·Φ(c₀) ≤ e^{−45(L+1)}`
(`phase0_numerics_real`) and `b·∑aⁱ ≤ n(L+1)·e^{−50(L+1)}·e^{2(e−1)(L+1)} ≤
e^{−44(L+1)}` (using `n(L+1) ≤ e^{2(L+1)}` from `ln n ≤ L+1`), total `≤ 2·e^{−44(L+1)}`.

ROUTE (a) NOW DONE — the affine drift `clockCounterPotential_drift_affine` is proven
on `allPhase0` ALONE (it no longer requires `noClockAtZero`).  The per-pair output
bound `clockSummand_pair_le` was strengthened to drop the positive-counter
hypotheses: at a counter-`0` clock the source summand is `e^0 = 1`, and the Rule-5
`advancePhaseWithInit` output has summand `≤ 1` (a non-clock gives `0`; a clock at
any counter gives `≤ 1`), so the per-side bound `summand(δ_i) ≤ eˢ·summand(r_i)`
holds at ANY counter (`clockSummand_clock_clock_{left,right}_le` →
`clockSummand_pair_clock_clock_le`).  Hence the downstream relay's `hdrift`
hypothesis is now discharged by `clockCounterPotential_drift_affine` against any
absorbing `Q ⊆ allPhase0` — `noClockAtZero` is NO longer part of the drift window.

REMAINING — the ABSORBING-WINDOW BRIDGE (the one structural input still open):
`allPhase0` itself is NOT `stepDistOrSelf`-absorbing (Gap 2: it is preserved one
step w.p. 1 only WHILE `noClockAtZero` holds — the protocol genuinely advances out
of phase 0 once a clock hits counter `0`).  The affine tail engine
`phase0_window_tail_affine`, like the multiplicative `windowDrift_tail`, needs an
ABSORBING `Q` on which the drift holds.  The genuine fix mirrors Gap 2's
prefix-union: bound `(Kᵗ)c₀{¬noClockAtZero}` on the *reachable-and-survived* trace.
Concretely the downstream relay supplies an absorbing `Q ⊆ allPhase0` (e.g. a
`RoleSplitGood`-style invariant — the count-only role split IS absorbing and implies
`allPhase0` along the surviving trajectory) and feeds
`clockCounterPotential_drift_affine` as its `hdrift` (NO positive-counter side
condition needed now); then `phase0_window_tail_affine` (Post = `noClockAtZero`,
`θ = 1`, `a = ofReal(1+2(e−1)/n)`, `b = e^{−50(L+1)}`, `Φ(c₀) ≤ n·e^{−50(L+1)}` via
`clockCounterPotential_init_le`) discharges the per-`τ` clock-zero bounds `hτ`, and
`allPhase0_window_whp` (Gap 2) assembles the `allPhase0` window.  The numerics close
with slack (`phase0_numerics_real` for `aᵗΦ₀ ≤ e^{−45(L+1)}`; the immigration sum
`b·∑aⁱ ≤ e^{−44(L+1)}`).  The only missing Lean object is the absorbing
`Q ⊆ allPhase0` witness (a role-split-count invariant + its absorption proof),
which lives in the role-split / `RoleSplitConcentration` layer, not here.

**Gap 2 — the deterministic phase-0-exit bridge — DISCHARGED above.**  The
single-step deterministic fact
  `allPhase0 c → ¬ allPhase0 (stepOrSelf (NonuniformMajority L K) c r₁ r₂)
      → ¬ noClockAtZero c`
is `det_phase0_exit`; its kernel form (the `¬ allPhase0` mass is `0` from
`allPhase0 ∧ noClockAtZero`) is
`transitionKernel_not_allPhase0_eq_zero_of_noClockAtZero`; the abstract
first-exit lift is `prefix_union_first_exit`; the assembled corollaries are
`allPhase0_window_le_prefix_sum` (the prefix-union itself) and
`allPhase0_window_whp` (the `t · ofReal(e^{−45(L+1)})` window bound, given the
per-`τ` clock-zero bounds `hτ` supplied by `phase0_window_whp` along the
trajectory).  Composing `allPhase0_window_whp` (Gap 2) with `phase0_window_whp`
(consuming Gap 1's drift) and an absorbing Post gives the Phase-0
`PhaseConvergence` upgrade. -/

end Phase0Window

end ExactMajority
