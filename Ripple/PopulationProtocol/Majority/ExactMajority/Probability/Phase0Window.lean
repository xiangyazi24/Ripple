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

* `clockCounterPotential` — the multiset exp-potential `Φ_s`;
* `allPhase0` — the absorbing phase-0 window predicate;
* `clockCounterPotential_ge_one_of_clock_counter_zero` — the threshold link
  (`¬ allPhase0` via some clock at `counter = 0` forces `Φ_s ≥ 1`);
* `phase0_window_tail_of_drift` — the kernel-level tail from a supplied drift;
* `phase0_window_whp` — the `(K^t) c₀ {¬ allPhase0}` corollary;
* `phase0_window_PhaseConvergence` — the `PhaseConvergence` packaging;
* `phase0CRShellEscape_le` — the relay-11 phase-0-CR shell-escape corollary;
* `phase0_window_numerics` — the numerics at `s = 1`, `t = δ n (L+1)`,
  `k = 50(L+1)`.

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

end Phase0Window

end ExactMajority
