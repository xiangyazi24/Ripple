/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# `NumericInstances` — residual #6: the mechanical numeric side-condition sweep.

Several Doty headlines carry an *explicitly-numeric named hypothesis* — a side condition
whose statement involves only numerals / casts / `Real.exp` / `Real.log` inequalities, kept
explicit at the call site so the surrounding probabilistic argument stays clean.  These are
NOT genuinely-open protocol facts; they are arithmetic instances that hold with enormous
slack at the locked Doty constants (`n ≥ DotyParams.N₀ = 10^40`, `δ ≤ 1`, the window
`t ≤ n(L+1)`).  This file discharges them as standalone arithmetic lemmas whose statements
match the carried hypotheses *verbatim*, so any consumer can `exact`/`apply` them.

This file is APPEND-ONLY: it edits no existing file.  It imports only the light Mathlib
analysis leaves (exp / log / exponential bounds), so the single-file `lake env lean` build is
dependency-cheap.

## Inventory (the named numeric side conditions across the day-2 close files)

| # | hypothesis            | file / consumer                                      | shape                                                                 | status |
|---|-----------------------|------------------------------------------------------|-----------------------------------------------------------------------|--------|
| 1 | `hrecmass`            | `DotyExpectedTime.doty_expected_time_concrete`        | `(1/n)·(2·Brecover)·(1−1/2)⁻¹ ≤ 4·Cbad·n·(L+1)`                       | DISCHARGED here (`hrecmass_of_recover_cap`) |
| 1'| `hrecmass`            | `ReachableLadder.doty_expected_time_reachable`        | *identical statement to #1*                                            | same instance closes both |
| 2 | `hnum`                | `KilledTailConsumers.phase0_killed_window_unconditional_closed` | `ofReal(e^{−50(L+1)})·∑_{i<τ} ofReal(1+2(e−1)/n)^i ≤ B`     | DISCHARGED here (`phase0_immigration_geom_sum_closed`) |

### Genuinely-NON-numeric (verified dangling but NOT in scope of this sweep)

- `IntegerProfileSquaring` (ProfileSquaringRate) — a TRUE §6 hour dynamic recurrence
  (`Z_i ≲ µ_{≥i}`), not arithmetic.
- `Phase6BandPositionFacts`, `SurvivalBandAbove` (BandLocalization) — protocol band-routing
  / survival facts.
- `ReachablePhaseRegimeClassification`, `ReachableClockFloors` (ReachableLadder) — the
  reachable-state regime classification + Lemma-5.2 floor propagation.
- per-level drain rates `q` (AveragingCollapse, per-phase convergence) — Corollary-1 averaging
  rate atoms.
- `hRecover` / `hBpos` (the `Brecover` recovery cap itself) — the §5 recovery bound, a
  probabilistic fact; only its *arithmetic consequence* `Brecover ≤ Cbad·n·(L+1)` is numeric
  (and that feeds #1 here).
- `hClassify` / `hFloors` (ReachableLadder) — protocol classification, NOT numeric.
- `Gap2_reachability_target` is *discharged* (`gap2_reachability_target_discharged`); its
  geometric budget surfaces as a CONCLUSION, not an open named hypothesis.
- `hPre_low` (LateFloor) — a generic role-split checkpoint hypothesis, NOT a numeral
  inequality.
- `hlog : Real.log n ≤ (L+1)` and `ht : τ ≤ n(L+1)` are kept as DOMAIN hypotheses of the
  instances below: they are the genuine window/scale conditions the campaign establishes, not
  free numerics to be invented.
-/

import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Complex.ExponentialBounds

namespace ExactMajority
namespace NumericInstances

open scoped ENNReal BigOperators NNReal

/-! ## Instance #1 — the recovery-mass side condition `hrecmass`.

`doty_expected_time_concrete` (DotyExpectedTime) and `doty_expected_time_reachable`
(ReachableLadder) carry the *identical* numeric hypothesis

  `(1/n) · (2·Brecover) · (1 − 1/2)⁻¹ ≤ 4·Cbad·n·(L+1)`.

The factor `(1 − 1/2)⁻¹ = 2`, so the LHS is `4·Brecover/n`.  With the E2-dominated cap
`Brecover ≤ Cbad·n·(L+1)` (the recovery bound after the progress-set transfer) the LHS is
`≤ 4·Cbad·(L+1) ≤ 4·Cbad·n·(L+1)` for `n ≥ 1`.  We prove the side condition from exactly the
cap `Brecover ≤ Cbad·n·(L+1)` and `1 ≤ n`. -/

/-- The constant `(1 − 1/2 : ℝ≥0∞)⁻¹ = 2`. -/
theorem inv_one_sub_half : (1 - (1 / 2 : ℝ≥0∞))⁻¹ = 2 := by
  have h : (1 : ℝ≥0∞) - (1 / 2 : ℝ≥0∞) = 1 / 2 := by
    rw [ENNReal.sub_eq_of_eq_add (by norm_num)]
    rw [ENNReal.div_add_div_same]
    rw [show (1 : ℝ≥0∞) + 1 = 2 by norm_num]
    rw [ENNReal.div_self (by norm_num) (by norm_num)]
  rw [h]
  rw [ENNReal.inv_div (by norm_num) (by norm_num)]
  norm_num

/-- **Instance #1 — the recovery-mass side condition.**  From the E2-dominated recovery cap
`Brecover ≤ Cbad·n·(L+1)` and `1 ≤ n`, the numeric hypothesis `hrecmass` of
`doty_expected_time_concrete` / `doty_expected_time_reachable` holds:

  `(1/n) · (2·Brecover) · (1 − 1/2)⁻¹ ≤ 4·Cbad·n·(L+1)`. -/
theorem hrecmass_of_recover_cap (n L Cbad Brecover : ℕ) (hn : 1 ≤ n)
    (hcap : Brecover ≤ Cbad * n * (L + 1)) :
    (1 / n : ℝ≥0∞) * ((2 * Brecover : ℕ) : ℝ≥0∞) * (1 - (1 / 2 : ℝ≥0∞))⁻¹
      ≤ ((4 * Cbad * n * (L + 1) : ℕ) : ℝ≥0∞) := by
  have hnpos : (0 : ℝ≥0∞) < (n : ℝ≥0∞) := by
    exact_mod_cast hn
  have hnne : (n : ℝ≥0∞) ≠ 0 := ne_of_gt hnpos
  have hntop : (n : ℝ≥0∞) ≠ ⊤ := by exact_mod_cast (ENNReal.natCast_ne_top n)
  -- rewrite `(1 − 1/2)⁻¹ = 2`
  rw [inv_one_sub_half]
  -- LHS = (1/n) · (2·Brecover) · 2 = (4·Brecover)/n
  have hcast : ((2 * Brecover : ℕ) : ℝ≥0∞) = 2 * (Brecover : ℝ≥0∞) := by push_cast; ring
  rw [hcast]
  have hLHS : (1 / n : ℝ≥0∞) * (2 * (Brecover : ℝ≥0∞)) * 2
      = (4 * (Brecover : ℝ≥0∞)) / (n : ℝ≥0∞) := by
    rw [one_div]
    rw [ENNReal.div_eq_inv_mul]
    ring
  rw [hLHS]
  -- the target `(4·Brecover)/n ≤ 4·Cbad·n·(L+1)` ⟺ `4·Brecover ≤ (4·Cbad·n·(L+1))·n`
  rw [ENNReal.div_le_iff hnne hntop]
  -- 4·Brecover ≤ 4·Cbad·n·(L+1) ≤ (4·Cbad·n·(L+1))·n  (since 1 ≤ n)
  have hbcap : (4 * (Brecover : ℝ≥0∞)) ≤ ((4 * Cbad * n * (L + 1) : ℕ) : ℝ≥0∞) := by
    have : (Brecover : ℝ≥0∞) ≤ ((Cbad * n * (L + 1) : ℕ) : ℝ≥0∞) := by exact_mod_cast hcap
    calc (4 * (Brecover : ℝ≥0∞)) ≤ 4 * ((Cbad * n * (L + 1) : ℕ) : ℝ≥0∞) := by gcongr
      _ = ((4 * Cbad * n * (L + 1) : ℕ) : ℝ≥0∞) := by push_cast; ring
  calc (4 * (Brecover : ℝ≥0∞))
      ≤ ((4 * Cbad * n * (L + 1) : ℕ) : ℝ≥0∞) := hbcap
    _ = ((4 * Cbad * n * (L + 1) : ℕ) : ℝ≥0∞) * 1 := (mul_one _).symm
    _ ≤ ((4 * Cbad * n * (L + 1) : ℕ) : ℝ≥0∞) * (n : ℝ≥0∞) := by
        gcongr
        exact_mod_cast hn

/-! ## Instance #2 — the immigration geometric-sum closure `hnum`.

`phase0_killed_window_unconditional_closed` (KilledTailConsumers) carries the explicit
immigration numeric

  `ofReal(e^{−50(L+1)}) · ∑_{i<τ} ofReal(1 + 2(e−1)/n)^i ≤ B`.

We close it at the campaign's documented `e^{−44(L+1)}` budget.  The real chain:

* `∑_{i<τ} a^i ≤ τ · a^τ`  (`a ≥ 1`, each term `≤ a^τ`);
* `a^τ = (1 + 2(e−1)/n)^τ ≤ exp(τ·2(e−1)/n) ≤ exp(2(e−1)(L+1))`  (`1+x ≤ e^x`, `τ ≤ n(L+1)`);
* `τ ≤ n(L+1) ≤ exp(L+1)·exp(L+1) = exp(2(L+1))`  (`n ≤ exp(L+1)` from `ln n ≤ L+1`,
  `L+1 ≤ exp(L+1)`);
* product `≤ exp((−50 + 2 + 2(e−1))(L+1)) = exp((2e − 50)(L+1)) ≤ exp(−44(L+1))`
  since `2e ≤ 6`.

This is the same arithmetic as `Phase0Window.phase0_numerics_real`, applied to the immigration
tail (the leading `Φ(c₀)` term replaced by the `τ` geometric prefix). -/

/-- **Real geometric-sum bound for the immigration tail.**  With drift rate `1 + 2(e−1)/n`,
window `τ ≤ n(L+1)`, `ln n ≤ (L+1)`, `1 ≤ n`:

  `e^{−50(L+1)} · ∑_{i<τ} (1 + 2(e−1)/n)^i ≤ e^{−44(L+1)}`. -/
theorem phase0_immigration_geom_sum_real (n L τ : ℕ) (hn : 1 ≤ n)
    (hlog : Real.log (n : ℝ) ≤ (L + 1 : ℕ)) (hτ : τ ≤ n * (L + 1)) :
    Real.exp (-(50 * (L + 1) : ℕ))
        * ∑ i ∈ Finset.range τ, (1 + 2 * (Real.exp 1 - 1) / (n : ℝ)) ^ i
      ≤ Real.exp (-(44 * (L + 1) : ℕ)) := by
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have he1 : (0 : ℝ) ≤ Real.exp 1 - 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  set x : ℝ := 2 * (Real.exp 1 - 1) / (n : ℝ) with hx
  have hx0 : 0 ≤ x := by rw [hx]; positivity
  have ha1 : (1 : ℝ) ≤ 1 + x := by linarith
  have haτ_nonneg : (0 : ℝ) ≤ (1 + x) ^ τ := by positivity
  -- (1+x)^τ ≤ exp(τ·x) ≤ exp(2(e−1)(L+1))
  have hLpos : (0 : ℝ) ≤ (L + 1 : ℕ) := by positivity
  have htn : (τ : ℝ) ≤ (n : ℝ) * (L + 1 : ℕ) := by
    have : (τ : ℝ) ≤ ((n * (L + 1) : ℕ) : ℝ) := by exact_mod_cast hτ
    rwa [Nat.cast_mul] at this
  have htx : (τ : ℝ) * x ≤ 2 * (Real.exp 1 - 1) * (L + 1 : ℕ) := by
    rw [hx]
    rw [show (τ : ℝ) * (2 * (Real.exp 1 - 1) / (n : ℝ))
          = (2 * (Real.exp 1 - 1)) * ((τ : ℝ) / (n : ℝ)) by ring]
    have hdiv : (τ : ℝ) / (n : ℝ) ≤ (L + 1 : ℕ) := by
      rw [div_le_iff₀ hnpos, mul_comm]; exact htn
    have h2e : 0 ≤ 2 * (Real.exp 1 - 1) := by linarith
    exact mul_le_mul_of_nonneg_left hdiv h2e
  have hpow_le : (1 + x) ^ τ ≤ Real.exp (2 * (Real.exp 1 - 1) * (L + 1 : ℕ)) := by
    have hstep1 : (1 + x) ^ τ ≤ Real.exp ((τ : ℝ) * x) := by
      rw [Real.exp_nat_mul]
      exact pow_le_pow_left₀ (by linarith) (by rw [add_comm]; exact Real.add_one_le_exp x) τ
    exact hstep1.trans (Real.exp_le_exp.mpr htx)
  -- ∑_{i<τ} (1+x)^i ≤ τ · (1+x)^τ
  have hsum_le : ∑ i ∈ Finset.range τ, (1 + x) ^ i ≤ (τ : ℝ) * (1 + x) ^ τ := by
    calc ∑ i ∈ Finset.range τ, (1 + x) ^ i
        ≤ ∑ i ∈ Finset.range τ, (1 + x) ^ τ := by
          apply Finset.sum_le_sum
          intro i hi
          have hile : i ≤ τ := le_of_lt (Finset.mem_range.mp hi)
          exact pow_le_pow_right₀ ha1 hile
      _ = (τ : ℝ) * (1 + x) ^ τ := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  -- τ ≤ exp(2(L+1)):  τ ≤ n(L+1), n ≤ exp(L+1), (L+1) ≤ exp(L+1)
  have hn_exp : (n : ℝ) ≤ Real.exp (L + 1 : ℕ) := by
    calc (n : ℝ) = Real.exp (Real.log (n : ℝ)) := (Real.exp_log hnpos).symm
      _ ≤ Real.exp (L + 1 : ℕ) := Real.exp_le_exp.mpr hlog
  have hLp1_exp : ((L + 1 : ℕ) : ℝ) ≤ Real.exp (L + 1 : ℕ) := by
    have := Real.add_one_le_exp ((L + 1 : ℕ) : ℝ)
    linarith
  have hτ_exp : (τ : ℝ) ≤ Real.exp (2 * (L + 1 : ℕ)) := by
    have hτnn : (0 : ℝ) ≤ (τ : ℝ) := by positivity
    calc (τ : ℝ) ≤ (n : ℝ) * (L + 1 : ℕ) := htn
      _ ≤ Real.exp (L + 1 : ℕ) * Real.exp (L + 1 : ℕ) := by
          apply mul_le_mul hn_exp hLp1_exp hLpos (Real.exp_pos _).le
      _ = Real.exp (2 * (L + 1 : ℕ)) := by rw [← Real.exp_add]; congr 1; ring
  -- assemble
  have hτnn : (0 : ℝ) ≤ (τ : ℝ) := by positivity
  calc Real.exp (-(50 * (L + 1) : ℕ))
          * ∑ i ∈ Finset.range τ, (1 + x) ^ i
      ≤ Real.exp (-(50 * (L + 1) : ℕ)) * ((τ : ℝ) * (1 + x) ^ τ) := by
        apply mul_le_mul_of_nonneg_left hsum_le (Real.exp_pos _).le
    _ ≤ Real.exp (-(50 * (L + 1) : ℕ))
          * (Real.exp (2 * (L + 1 : ℕ)) * Real.exp (2 * (Real.exp 1 - 1) * (L + 1 : ℕ))) := by
        apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
        exact mul_le_mul hτ_exp hpow_le haτ_nonneg (Real.exp_pos _).le
    _ = Real.exp ((-(50 : ℝ) + 2 + 2 * (Real.exp 1 - 1)) * (L + 1 : ℕ)) := by
        rw [← Real.exp_add, ← Real.exp_add]
        congr 1
        push_cast
        ring
    _ ≤ Real.exp (-(44 * (L + 1) : ℕ)) := by
        apply Real.exp_le_exp.mpr
        have he3 : Real.exp 1 ≤ 3 := by have := Real.exp_one_lt_d9; linarith
        have hcoef : (-(50 : ℝ) + 2 + 2 * (Real.exp 1 - 1)) ≤ -44 := by nlinarith [he3]
        push_cast
        nlinarith [hLpos, mul_le_mul_of_nonneg_right hcoef hLpos]

/-- **Instance #2 — the immigration geometric-sum side condition (ENNReal `ofReal` form).**
The exact shape of the `hnum` hypothesis of `phase0_killed_window_unconditional_closed`, closed
at the budget `B := ofReal(e^{−44(L+1)})`:

  `ofReal(e^{−50(L+1)}) · ∑_{i<τ} ofReal(1 + 2(e−1)/n)^i ≤ ofReal(e^{−44(L+1)})`.

(Note `1 * (50·(L+1)) = 50·(L+1)`, matching the literal `s = 1` form in the consumer.) -/
theorem phase0_immigration_geom_sum_closed (n L τ : ℕ) (hn : 1 ≤ n)
    (hlog : Real.log (n : ℝ) ≤ (L + 1 : ℕ)) (hτ : τ ≤ n * (L + 1)) :
    ENNReal.ofReal (Real.exp (-(1 * (50 * (L + 1) : ℕ))))
        * ∑ i ∈ Finset.range τ,
            ENNReal.ofReal (1 + 2 * (Real.exp 1 - 1) / (n : ℝ)) ^ i
      ≤ ENNReal.ofReal (Real.exp (-(44 * (L + 1) : ℕ))) := by
  have hbase_nonneg : (0 : ℝ) ≤ 1 + 2 * (Real.exp 1 - 1) / (n : ℝ) := by
    have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have he1 : (0 : ℝ) ≤ Real.exp 1 - 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
    have : (0 : ℝ) ≤ 2 * (Real.exp 1 - 1) / (n : ℝ) := by positivity
    linarith
  -- push the powers and the sum through ofReal
  have hpow : ∀ i, ENNReal.ofReal (1 + 2 * (Real.exp 1 - 1) / (n : ℝ)) ^ i
      = ENNReal.ofReal ((1 + 2 * (Real.exp 1 - 1) / (n : ℝ)) ^ i) := by
    intro i; rw [← ENNReal.ofReal_pow hbase_nonneg]
  have hsum_ofReal : ∑ i ∈ Finset.range τ,
        ENNReal.ofReal (1 + 2 * (Real.exp 1 - 1) / (n : ℝ)) ^ i
      = ENNReal.ofReal (∑ i ∈ Finset.range τ, (1 + 2 * (Real.exp 1 - 1) / (n : ℝ)) ^ i) := by
    rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => by positivity)]
    exact Finset.sum_congr rfl (fun i _ => hpow i)
  rw [hsum_ofReal]
  rw [one_mul]
  rw [← ENNReal.ofReal_mul (Real.exp_pos _).le]
  exact ENNReal.ofReal_le_ofReal (phase0_immigration_geom_sum_real n L τ hn hlog hτ)

end NumericInstances
end ExactMajority
