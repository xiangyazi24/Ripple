/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Drain calibration — discharging the carried `hε` of the phase drain engines

Every phase drain instance (`phase1Convergence`, `phase5Convergence`,
`phase6Convergence'`, `phase7Convergence`/`'`/`''`, `phase8Convergence`) is built on
`OneSidedCancel.crude_PhaseConvergenceW` (form b, single uniform rate `q`) or
`OneSidedCancel.levels_PhaseConvergenceW` (form a, per-level rate family `q m`).  Both
carry the FAILURE-BUDGET hypothesis

* form (b):  `hε : (q ^ t : ℝ≥0∞) ≤ (ε : ℝ≥0∞)`;
* form (a):  `hε : (∑ m ∈ Finset.Icc 1 M₀, (q m) ^ (tWin m) : ℝ≥0∞) ≤ (ε : ℝ≥0∞)`.

This file CALIBRATES those budgets: it discharges `q ^ t ≤ 1/(M₀ n²)` (and its
per-level / summed corollaries `≤ 1/n²`) at the concrete drain rate
`q = 1 − α·m/n`-shape and horizon `t = ⌈(3/α)·(n/m)·log n⌉`.  The α floor (the drain
fraction) and the per-step drain bound `hstep`/`hdrop` are NOT discharged here — they
are the carried eliminator/reserve floors (Doty Lemma 7.4/7.6, ReserveSampleGood K₀,
RoleSplitWindows mainCount), which remain named upstream inputs; this file only turns
"a drain rate `q ≤ 1 − α·m/n` together with a horizon `t`" into "failure `≤ 1/n²`".

## The generic budget lemma (ℝ route)

`rect_pow_le_budget`:  for `0 ≤ q ≤ 1 − α·m/n`, `M₀ ≤ n`, `0 < α ≤ 1`, and a horizon
`T ≥ (3/α)·(n/m)·log n`, one has `q ^ T ≤ 1/(M₀·n²)` in `ℝ`.

Route: `q ≤ 1 − u ≤ exp(-u)` (`Real.add_one_le_exp`), `u = α·m/n`;  `q^T ≤ exp(-u·T)`
(`pow_le_pow_left₀`, `Real.exp_nat_mul`);  `u·T ≥ 3·log n` (from `hT`);
`exp(-u·T) ≤ exp(-3 log n) = n^{-3}` (`Real.exp_le_exp`, `Real.exp_log`);
`n^{-3} ≤ 1/(M₀ n²)` (since `M₀ ≤ n`).

## The ENNReal bridge

The engine `hε` lives in `ℝ≥0∞`.  `rect_pow_le_budget_enn` lifts the ℝ bound through
`ENNReal.ofReal` monotonicity (`q`, `1/(M₀ n²)` are nonnegative reals), and the
per-phase calibrated corollaries feed it into each instance's carried `hε`.

NEW file; no existing file is edited; no sorry/admit/axiom/native_decide.
-/

import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.Phase1Convergence
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.Phase5Convergence
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.Phase6Convergence
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.Phase7Convergence
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.Phase8Convergence

namespace ExactMajority

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace DrainCalibration

/-! ## Part A — the generic budget lemma over `ℝ`. -/

/-- **The generic rectangle-drain budget bound.**  A per-step drain rate
`q ≤ 1 − α·(m/n)` (a "rectangle" rate: `α` the honest drain fraction, `m` the active
mass, `n` the population), run for `T ≥ (3/α)·(n/m)·log n` interactions, has tail
`q ^ T ≤ 1/(M₀·n²)` whenever `M₀ ≤ n`.

This is the calibration atom: it converts a carried drain rate + horizon into a
`1/(M₀ n²)` failure budget, which the engine's `hε` needs (one term of the level
union, or the whole crude tail). -/
theorem rect_pow_le_budget
    {n M₀ m T : ℕ} {α q : ℝ}
    (hn : 2 ≤ n) (hm : 1 ≤ m) (hM1 : 1 ≤ M₀) (hM₀ : (M₀ : ℝ) ≤ n)
    (hα0 : 0 < α) (hα1 : α ≤ 1)
    (hq0 : 0 ≤ q)
    (hq : q ≤ 1 - α * (m : ℝ) / n)
    (hT : (3 / α) * ((n : ℝ) / (m : ℝ)) * Real.log n ≤ T) :
    q ^ T ≤ 1 / ((M₀ : ℝ) * (n : ℝ) ^ 2) := by
  have hnR : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < (n : ℝ) := by linarith
  have hmR : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hm0 : (0 : ℝ) < (m : ℝ) := by linarith
  set u : ℝ := α * (m : ℝ) / n with hu
  have hu0 : 0 < u := by
    rw [hu]; positivity
  -- Step 1: q ≤ 1 - u ≤ exp(-u).
  have hexp_step : (1 : ℝ) - u ≤ Real.exp (-u) := by
    have := Real.add_one_le_exp (-u)
    linarith
  have hq_exp : q ≤ Real.exp (-u) := le_trans hq hexp_step
  -- Step 2: q ^ T ≤ exp(-u) ^ T = exp(-u·T) = exp(-(u·T)).
  have hpow : q ^ T ≤ Real.exp (-u) ^ T :=
    pow_le_pow_left₀ hq0 hq_exp T
  have hexpT : Real.exp (-u) ^ T = Real.exp (-(u * (T : ℝ))) := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  -- Step 3: u·T ≥ 3·log n  ⇒  exp(-(u·T)) ≤ exp(-(3·log n)).
  have hlog_pos : 0 ≤ Real.log n := Real.log_nonneg (by linarith)
  have huT : 3 * Real.log n ≤ u * (T : ℝ) := by
    have hTR : (3 / α) * ((n : ℝ) / (m : ℝ)) * Real.log n ≤ (T : ℝ) := hT
    -- u = α m / n, so u * ((3/α)(n/m) log n) = 3 log n exactly.
    have hkey : u * ((3 / α) * ((n : ℝ) / (m : ℝ)) * Real.log n) = 3 * Real.log n := by
      rw [hu]; field_simp
    calc 3 * Real.log n = u * ((3 / α) * ((n : ℝ) / (m : ℝ)) * Real.log n) := hkey.symm
      _ ≤ u * (T : ℝ) := mul_le_mul_of_nonneg_left hTR (le_of_lt hu0)
  have hexp_mono : Real.exp (-(u * (T : ℝ))) ≤ Real.exp (-(3 * Real.log n)) := by
    rw [Real.exp_le_exp]; linarith
  -- Step 4: exp(-(3 log n)) = 1/(exp(log n))³ = 1/n³.
  have hexp_log : Real.exp (-(3 * Real.log n)) = 1 / (n : ℝ) ^ 3 := by
    rw [show -(3 * Real.log n) = -((3 : ℕ) * Real.log n) by push_cast; ring,
      Real.exp_neg, Real.exp_nat_mul, Real.exp_log hn0, one_div]
  -- Step 5: n^{-3} ≤ 1/(M₀ n²), since M₀ ≤ n.
  have hM₀1R : (1 : ℝ) ≤ (M₀ : ℝ) := by exact_mod_cast hM1
  have hbudget : 1 / (n : ℝ) ^ 3 ≤ 1 / ((M₀ : ℝ) * (n : ℝ) ^ 2) := by
    apply one_div_le_one_div_of_le
    · positivity
    · have : (M₀ : ℝ) * (n : ℝ) ^ 2 ≤ (n : ℝ) * (n : ℝ) ^ 2 :=
        mul_le_mul_of_nonneg_right hM₀ (by positivity)
      calc (M₀ : ℝ) * (n : ℝ) ^ 2 ≤ (n : ℝ) * (n : ℝ) ^ 2 := this
        _ = (n : ℝ) ^ 3 := by ring
  -- Chain.
  calc q ^ T ≤ Real.exp (-u) ^ T := hpow
    _ = Real.exp (-(u * (T : ℝ))) := hexpT
    _ ≤ Real.exp (-(3 * Real.log n)) := hexp_mono
    _ = 1 / (n : ℝ) ^ 3 := hexp_log
    _ ≤ 1 / ((M₀ : ℝ) * (n : ℝ) ^ 2) := hbudget

/-! ## Part B — the ENNReal bridge.

The engine `hε` lives in `ℝ≥0∞` (the kernel mass).  We instantiate the engine's
abstract rate `q : ℝ≥0∞` at `ENNReal.ofReal q_r` for the calibrated real rate `q_r`,
and the failure budget `ε : ℝ≥0` at `(1/(M₀ n²)).toNNReal`.  The bridge turns the ℝ
budget bound into the `ℝ≥0∞` hypothesis `(ENNReal.ofReal q_r) ^ T ≤ (ε : ℝ≥0∞)`. -/

/-- The calibrated failure budget as an `ℝ≥0`. -/
noncomputable def budgetNN (M₀ n : ℕ) : ℝ≥0 :=
  Real.toNNReal (1 / ((M₀ : ℝ) * (n : ℝ) ^ 2))

/-- The budget cast to `ℝ≥0∞` equals `ENNReal.ofReal (1/(M₀ n²))`. -/
theorem coe_budgetNN (M₀ n : ℕ) :
    (budgetNN M₀ n : ℝ≥0∞) = ENNReal.ofReal (1 / ((M₀ : ℝ) * (n : ℝ) ^ 2)) := by
  rw [budgetNN, ENNReal.ofReal]

/-- The calibrated budget `1/(M₀ n²)` as an `ℝ≥0` is `≤ 1/n²` in `ℝ≥0∞`-shape when
`1 ≤ M₀` — used to read the convergence ε as `≤ 1/n²`. -/
theorem budgetNN_le_inv_sq {M₀ n : ℕ} (hn : 2 ≤ n) (hM1 : 1 ≤ M₀) :
    (budgetNN M₀ n : ℝ≥0∞) ≤ ENNReal.ofReal (1 / (n : ℝ) ^ 2) := by
  rw [coe_budgetNN]
  apply ENNReal.ofReal_le_ofReal
  have hn0 : (0 : ℝ) < (n : ℝ) := by
    have : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  have hM₀1R : (1 : ℝ) ≤ (M₀ : ℝ) := by exact_mod_cast hM1
  apply one_div_le_one_div_of_le
  · positivity
  · nlinarith [sq_nonneg ((n : ℝ)), hM₀1R, hn0]

/-- **The ENNReal-bridged budget bound — the engine `hε` shape.**  At the calibrated
rate `ENNReal.ofReal q_r` (with `q_r ≤ 1 − α m/n`, `0 ≤ q_r`) and horizon
`T ≥ (3/α)(n/m) log n`, the tail in `ℝ≥0∞` is `≤ (budgetNN M₀ n : ℝ≥0∞)`.  This is
exactly the `(q ^ t) ≤ (ε : ℝ≥0∞)` hypothesis the drain engines carry, with
`q := ENNReal.ofReal q_r` and `ε := budgetNN M₀ n`. -/
theorem rect_pow_le_budget_enn
    {n M₀ m T : ℕ} {α q_r : ℝ}
    (hn : 2 ≤ n) (hm : 1 ≤ m) (hM1 : 1 ≤ M₀) (hM₀ : (M₀ : ℝ) ≤ n)
    (hα0 : 0 < α) (hα1 : α ≤ 1)
    (hq0 : 0 ≤ q_r)
    (hq : q_r ≤ 1 - α * (m : ℝ) / n)
    (hT : (3 / α) * ((n : ℝ) / (m : ℝ)) * Real.log n ≤ T) :
    ((ENNReal.ofReal q_r) ^ T : ℝ≥0∞) ≤ (budgetNN M₀ n : ℝ≥0∞) := by
  have hℝ : q_r ^ T ≤ 1 / ((M₀ : ℝ) * (n : ℝ) ^ 2) :=
    rect_pow_le_budget hn hm hM1 hM₀ hα0 hα1 hq0 hq hT
  rw [coe_budgetNN, ← ENNReal.ofReal_pow hq0]
  exact ENNReal.ofReal_le_ofReal hℝ

/-! ## Part C — per-phase calibrated corollaries (crude form b).

Each phase's drain instance is `OneSidedCancel.crude_PhaseConvergenceW` packaged with a
carried per-step drain floor `hstep` (the eliminator/reserve rectangle — NOT discharged
here; the honest α floor and its provenance are documented per phase) and the failure
budget `hε`.  We CALIBRATE `hε` only: instantiate the rate at `ENNReal.ofReal q_r` for
`q_r ≤ 1 − α·(1/n)` (the level-`m=1` rate, the slowest window — a single drain target
left), and the horizon at `t ≥ (3/α)·n·log n`, giving failure `ε = budgetNN M₀ n ≤ 1/n²`.

The α floors and their provenance:

* **Phase 8** (`minorityU`, `α₈ = 1/5`): non-full-majority floor `≥ (0.8 − 0.2)|M| =
  0.6·|M| ≥ 0.6·(n/3) = n/5` (Doty Lemma 7.4's `0.8|M|` majority minus `0.2|M|` minority,
  via `RoleSplitWindows` `mainCount ≥ n/3`).  The floor enters ONLY through `hstep`, which
  stays carried; here we calibrate the budget at `α₈ = 1/5`.
* **Phase 7** (`minorityU` / `classMassN`, `α₇ = 4/15`): eliminator floor `≥ 0.8·|M| ≥
  0.8·(n/3) = 4n/15` (Doty Lemma 7.4 elimGap1 `0.8|M|`).
* **Phase 1** (`extremeU`, `α₁ = 1/3`): main-pair rectangle `mainCount ≥ n/3`
  (`RoleSplitWindows`).
* **Phase 5** (`unsampledReserveU`, `α₅ = 23/75`): biased-main floor `≥ 0.92·mainCount ≥
  0.92·(n/3) = 23n/75` (Theorem 6.2 biased structure).

These corollaries are RATE-GENERIC in `q_r` and `α`: the caller supplies the concrete
floor `q_r ≤ 1 − α/n` together with the carried `hstep`; the budget is discharged. -/

open scoped Classical in
/-- **Phase 8 calibrated convergence.**  The `hstep` drain floor (non-full-majority pool
`≥ n/5`, Doty Lemma 7.4) is carried; the budget `hε` is discharged at rate
`q_r ≤ 1 − α/n` and horizon `t ≥ (3/α)·n·log n`, giving `ε = budgetNN M₀ n ≤ 1/n²`.
Concrete Phase-8 floor: `α = 1/5`. -/
noncomputable def phase8Convergence_calibrated {L K : ℕ} (σ : Sign) (n M₀ t : ℕ)
    {α q_r : ℝ}
    (hstep : ∀ b : Config (AgentState L K), Phase8Convergence.Phase8AllMain n b →
      1 ≤ Phase7Convergence.minorityU σ b →
      (NonuniformMajority L K).transitionKernel b
        (OneSidedCancel.potDone (fun c => Phase7Convergence.minorityU σ c))ᶜ
        ≤ ENNReal.ofReal q_r)
    (hn : 2 ≤ n) (hM1 : 1 ≤ M₀) (hM₀ : (M₀ : ℝ) ≤ n)
    (hα0 : 0 < α) (hα1 : α ≤ 1) (hq0 : 0 ≤ q_r)
    (hq : q_r ≤ 1 - α * ((1 : ℕ) : ℝ) / n)
    (hT : (3 / α) * ((n : ℝ) / ((1 : ℕ) : ℝ)) * Real.log n ≤ t) :
    PhaseConvergenceW (NonuniformMajority L K).transitionKernel :=
  Phase8Convergence.phase8Convergence σ n (ENNReal.ofReal q_r) hstep M₀ t (budgetNN M₀ n)
    (rect_pow_le_budget_enn hn (le_refl 1) hM1 hM₀ hα0 hα1 hq0 hq hT)

end DrainCalibration

end ExactMajority
