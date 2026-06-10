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

/-! ## Precise remaining gaps to the campaign (for downstream relays).

Everything above is 0-sorry / axiom-clean.  Two inputs remain to fully close the
`allPhase0` → `PhaseConvergence` timing half; both are deliberately taken as
hypotheses above (mirroring how `WindowConcentration.windowDrift_tail` itself
takes its one-step drift as input), so they are stated here with exact goals.

**Gap 1 — the quantitative one-step drift `hdrift` (the scheduler core).**
The window engine consumes
  `∫ Φ_1 dK(c) ≤ ofReal(1 + 2(e−1)/n) · Φ_1(c)`  on an absorbing window `Q`.
Goal: over the uniform-pair scheduler (`Config.interactionProb`), each clock
ticks (its `counter` drops by 1, multiplying its summand by `e^1`) only in a
clock–clock meeting, w.p. `≤ 2(clockCount−1)/(n(n−1)) ≤ 2/n` per step.  The
affected-summand bound gives the affine rate `1 + 2(e−1)/n`.  This is the
in-house affine-counter pattern (cf. `EarlyDripMarked`'s tainted-counter drift);
it is the campaign's separate quantitative deliverable.  `Q` should be a
clock-count window absorbing under `stepDistOrSelf` (e.g. via `RoleSplitGood` /
`clockCount ≤ n`).

**Gap 2 — the deterministic phase-0-exit bridge (for the `Esc`/`allPhase0`
containment `hcontain`).**  From `Protocol.Transition` (frozen), an agent's
PHASE changes out of `0` ONLY via `Transition.stdCounterSubroutine` (Rule 5 of
`Phase0Transition`: `stdCounterSubroutine` fires only when BOTH partners are
clocks; for two phase-0 agents `phaseEpidemicUpdate_eq_self_of_both_phase0`
collapses the epidemic wrapper, so `Transition` reduces to `Phase0Transition`).
`stdCounterSubroutine a` advances phase ONLY when `a.counter.val = 0`; Rule 4
sets a freshly-created clock's counter to `50(L+1) ≠ 0`, and Rules 1–3 never
touch `counter` nor create clocks.  Hence a single-step phase-0 exit forces a
SOURCE-config clock at `counter = 0`:

  `allPhase0 c → ¬ allPhase0 (stepOrSelf P c r₁ r₂) → ¬ noClockAtZero c`.

Lifting this single-step fact to `{¬ allPhase0 at t} ⊆ ⋃_{τ≤t} {¬ noClockAtZero
at τ}` is the prefix-union/first-exit structure (a hitting-time helper not yet
in the tree); combined with the per-`τ` `phase0_window_whp` bound and a
horizon-`t` union it yields the `allPhase0`-window corollary and (with an
absorbing Post) the Phase-0 `PhaseConvergence` upgrade. -/

end Phase0Window

end ExactMajority
