/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# WidthPrefixConcrete — the concrete free-τ width family (Phase B-13)

`WidthPrefix.lean` (B-8) supplies the RAW-parameter free-τ machinery for the §6 moving-frame width
engine: `checkpoint_composition_prefix`, `windowedFrontProfile_whp_checkpoint` (the `KK := j` window
wrapper), `windowedFrontProfile_whp_prefix` (the remainder version at `τ = w·j + r`, taking the
`r`-horizon remainder window bound `δRem` as an INPUT), and `goodFrontWidth_whp_at`.  The deferred
piece was "the concrete-parameter discharge of `δRem` — the `r`-horizon analog of the `w`-window
`window_failure_le`/`hB` ladder".

This file discharges that `δRem` at the concrete `DotyParams` parameters and assembles the
τ-uniform (over the hour horizon) concrete width family that B-12's `clock_unconditional_concrete`
needs for its single open input `εside`.

## The `δRem` discharge — honest analysis of the horizon split.

`window_failure_le` (in `EarlyDripMarked`) is ALREADY horizon-parametric: at ANY horizon `r` it
bounds `(markedK^r) mc₀ {¬recInv} ≤ δ` from a per-window bad-event bound at the SAME horizon `r`
(the region/floor/P3/X-exit modes are NULL at every horizon, via `ae_notG_pow`).  So the
remainder bound is `window_failure_le` instantiated at `r`.

The per-window bad-event bound at horizon `r` is `per_window_delta` re-run with `w := r`.  Its
`w`-dependent hypotheses split by direction:
* `hsmall` (`σw·(1+y)^r ≤ thresh`): the base `1+y ≥ 1`, so `r < w ⟹ (1+y)^r ≤ (1+y)^w`; the LHS
  SHRINKS — holds a fortiori for `r < w`.
* `hfloor` (`floor_margin_params`: `δgLocked ≤ r·(1.8(1−e^{−1/10})/n) − const`): the RHS has a
  `+r·(positive)` term, so for `r < w` the RHS SHRINKS.  The slack at the full window `w` is tiny
  (≈ 4·10⁻⁶), so the floor margin GENUINELY FAILS for small `r` (and fails outright at `r = 0`).

Hence re-running the §6 ladder at `r` is NOT possible for small remainders: this is a real
structural break, not a missing arithmetic step.  The honest fix (exactly the route the campaign
audit blessed — "a coarse uniform δRem for partial windows") is the **trivial probability bound**
`δRem := 1`: from ANY start, `(markedK^r) mc₀ {¬recInv} ≤ 1`, valid at EVERY `r` (including the
broken small-`r` regime).  This yields an explicit — if coarse — concrete width family, which is
all `εside` needs: B-12's `εside` is itself a named UNIFORM bound, not required to be `< 1`.

The remainder contributes `Tcap · δRem = Tcap` to the per-`τ` width budget (the union over the
`Tcap` recurrence levels); the checkpoint part contributes the same `KK·deltaB`-shape as the
endpoint budget (since `j ≤ KK`).  The τ-uniform width mass is therefore
`Tcap·(KK·deltaB n + 1 + (escape + tail)) + climb`.

ZERO sorry, zero new axiom, zero native_decide.
-/

import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.WidthPrefix
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.DotyParams
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.ClockBudgets

namespace ExactMajority

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Real BigOperators Classical

namespace EarlyDripMarked

open ClockRealKernel

variable {L K : ℕ}

/-! ## Part 1 — the coarse remainder bound `δRem := 1`.

The `r`-horizon remainder block `(markedK^r) mc₀ {¬recInv}` is a probability mass, hence `≤ 1`,
at EVERY remainder horizon `r` and EVERY start `mc₀` — in particular across the small-`r` regime
where the §6 floor margin breaks.  This is the universally-valid `δRem` consumed by
`windowedFrontProfile_whp_prefix`. -/

/-- **`markedK_pow_isMarkov`** — every power of the marked kernel is a Markov kernel. -/
instance markedK_pow_isMarkov (T θn r : ℕ) :
    IsMarkovKernel ((markedK (L := L) (K := K) T θn) ^ r) := by
  induction r with
  | zero =>
      rw [pow_zero]
      exact inferInstanceAs (IsMarkovKernel (Kernel.id : Kernel (Config (MarkedAgent L K)) _))
  | succ s ihs =>
      rw [pow_succ]
      exact inferInstanceAs (IsMarkovKernel ((markedK (L := L) (K := K) T θn ^ s) ∘ₖ
        markedK (L := L) (K := K) T θn))

/-- **`rem_le_one`** — the trivial `r`-horizon remainder bound: from ANY start, the `{¬recInv}` mass
after `r` marked steps is `≤ 1` (a probability measure).  This is the honest universal `δRem` for
the partial-window remainder block: the §6 ladder's floor margin genuinely fails for small `r`
(it requires the FULL window `w` of drift), so no `deltaB`-shape bound holds at every `r`; `1` does.
-/
theorem rem_le_one (T θn n : ℕ) (cc : ℝ) (r : ℕ) (mc₀ : Config (MarkedAgent L K))
    (_hInv : recInv (L := L) (K := K) T θn n cc mc₀) :
    ((markedK (L := L) (K := K) T θn) ^ r) mc₀
        {mc | ¬ recInv (L := L) (K := K) T θn n cc mc} ≤ 1 := by
  haveI : IsProbabilityMeasure (((markedK (L := L) (K := K) T θn) ^ r) mc₀) :=
    (markedK_pow_isMarkov (L := L) (K := K) T θn r).isProbabilityMeasure mc₀
  exact prob_le_one

/-! ## Part 2 — the concrete `hsmall` at a prefix horizon `w·j + r ≤ w·KK`.

`windowedFrontProfile_whp_prefix` needs the scale smallness `σ·(1+4/n)^(w·j+r) ≤ 1/2` at the
prefix horizon.  At the concrete `σ := DotyParams.σ n` the endpoint smallness
`σ·(1+4/n)^(w·KK) ≤ 1/2` is `DotyParams.hsmall_eq`; for a prefix horizon `w·j + r ≤ w·KK` the LHS
shrinks (base `1+4/n ≥ 1`), so the prefix smallness follows. -/

/-- **`hsmall_prefix_concrete`** — the concrete scale smallness at a prefix horizon `τ ≤ w·KK`. -/
theorem hsmall_prefix_concrete (n : ℕ) (hn : DotyParams.N₀ ≤ n) (τ : ℕ)
    (hτ : τ ≤ DotyParams.w n * DotyParams.KK L K) :
    DotyParams.σ (L := L) (K := K) n * (1 + 4 / (n : ℝ)) ^ τ ≤ 1 / 2 := by
  have hbase : (1 : ℝ) ≤ 1 + 4 / (n : ℝ) := by
    have hnpos : 0 < n := DotyParams.N₀_pos n hn
    have : (0 : ℝ) ≤ 4 / (n : ℝ) := by positivity
    linarith
  have hσ0 : 0 ≤ DotyParams.σ (L := L) (K := K) n := (DotyParams.σ_pos (L := L) (K := K) n hn).le
  have hpow : (1 + 4 / (n : ℝ)) ^ τ
      ≤ (1 + 4 / (n : ℝ)) ^ (DotyParams.w n * DotyParams.KK L K) :=
    pow_le_pow_right₀ hbase hτ
  calc DotyParams.σ (L := L) (K := K) n * (1 + 4 / (n : ℝ)) ^ τ
      ≤ DotyParams.σ (L := L) (K := K) n * (1 + 4 / (n : ℝ)) ^ (DotyParams.w n * DotyParams.KK L K) :=
        mul_le_mul_of_nonneg_left hpow hσ0
    _ ≤ 1 / 2 := DotyParams.hsmall_eq (L := L) (K := K) n hn

/-! ## Part 3 — the concrete prefix `WindowedFrontProfile` mass at `τ = w·j + r`.

Instantiate `windowedFrontProfile_whp_prefix` (B-8) at the concrete `DotyParams` parameters:
`θn := θn n`, `cc := 9/10`, `θ := θ n`, `σ := σw`-engine via `DotyParams.σ n`, `w := w n`, the
per-window `δ T := deltaB n` (discharged by `DotyParams.hB_params`), and the remainder
`δRem T := 1` (the coarse universal bound `rem_le_one`).  The result is the per-`τ` analog of
`DotyParams.windowedFrontProfile_whp_final`'s mass, valid at ANY minute boundary `τ = w·j + r`,
`r < w`, `j ≤ KK − 1` (so `τ ≤ w·KK`). -/

open ClockFrontProfile in
/-- **`windowedFrontProfile_whp_prefix_concrete`** — the `WindowedFrontProfile`-failure mass at a
prefix horizon `τ = w·j + r` (`r < w`, `τ ≤ w·KK`) at the concrete parameters.  The per-window
`δ := deltaB n` is `DotyParams.hB_params`; the remainder `δRem := 1` is the coarse `rem_le_one`. -/
theorem windowedFrontProfile_whp_prefix_concrete (n : ℕ) (hn : DotyParams.N₀ ≤ n)
    (mc₀ : Config (MarkedAgent L K))
    (hcard : mc₀.card = n)
    (hge3 : AllClockGE3 (L := L) (K := K) (eraseConfig (L := L) (K := K) mc₀))
    (hnotP3 : ¬ AllClockP3 (L := L) (K := K) (eraseConfig (L := L) (K := K) mc₀))
    (hclean : ∀ m ∈ mc₀, m.2 = false)
    (Tcap : ℕ) (hcap : ClockFrontShape.capMinute (L := L) (K := K) < Tcap)
    (j r : ℕ) (hr : r < DotyParams.w n) (hjKK : j ≤ DotyParams.KK L K - 1) :
    ((NonuniformMajority L K).transitionKernel ^ (DotyParams.w n * j + r))
        (eraseConfig (L := L) (K := K) mc₀)
        {c | (c.card = n ∧ AllClockP3 (L := L) (K := K) c ∧
            (∀ T, DotyParams.θ n ≤ ClockFrontProfile.frac (L := L) (K := K) T c →
              (9/10 : ℝ) * (rBeyond (L := L) (K := K) T c : ℝ) ^ 2 / (n : ℝ) + (DotyParams.tt n : ℝ)
                ≤ (rBeyond (L := L) (K := K) T c : ℝ) ^ 2 / (n : ℝ)))
          ∧ ¬ WindowedFrontProfile (L := L) (K := K) (DotyParams.θ n) c}
      ≤ ∑ T ∈ Finset.range Tcap,
          (((j : ℝ≥0∞) * DotyParams.deltaB n + 1)
            + ((GatedDrift.killK (markedK (L := L) (K := K) T (DotyParams.θn n))
                (taintedGate (L := L) (K := K) n) ^ (DotyParams.w n * j + r)) (some mc₀) {none}
              + ENNReal.ofReal
                (Real.exp (DotyParams.σ (L := L) (K := K) n
                    * (1 + 4 / (n : ℝ)) ^ (DotyParams.w n * j + r)
                    * (taintedCount (L := L) (K := K) mc₀ : ℝ)
                  + 2 * DotyParams.σ (L := L) (K := K) n
                      * (1 + 4 / (n : ℝ)) ^ (DotyParams.w n * j + r)
                      * ((DotyParams.θn n : ℝ) / (n : ℝ)) ^ 2
                      * ((DotyParams.w n * j + r : ℕ) : ℝ)
                  - DotyParams.σ (L := L) (K := K) n * ((DotyParams.tt n + 1 : ℕ) : ℝ))))) := by
  have hτle : DotyParams.w n * j + r ≤ DotyParams.w n * DotyParams.KK L K := by
    have hKKpos : 1 ≤ DotyParams.KK L K := by
      unfold DotyParams.KK; omega
    have hjle : j + 1 ≤ DotyParams.KK L K := by omega
    calc DotyParams.w n * j + r ≤ DotyParams.w n * j + DotyParams.w n := by omega
      _ = DotyParams.w n * (j + 1) := by ring
      _ ≤ DotyParams.w n * DotyParams.KK L K := Nat.mul_le_mul_left _ hjle
  exact windowedFrontProfile_whp_prefix (L := L) (K := K) (DotyParams.θn n) n
    (DotyParams.two_le n hn) (9/10) (DotyParams.w n) r (DotyParams.θ n) (DotyParams.θ_pos n hn)
    (fun _ => DotyParams.deltaB n) (fun _ => 1)
    (DotyParams.hB_params (L := L) (K := K) n hn)
    (fun T mc₀' hInv => rem_le_one (L := L) (K := K) T (DotyParams.θn n) n (9/10) r mc₀' hInv)
    (DotyParams.σ (L := L) (K := K) n) (DotyParams.σ_pos n hn) j
    (hsmall_prefix_concrete (L := L) (K := K) n hn (DotyParams.w n * j + r) hτle)
    (DotyParams.tt n) Tcap hcap mc₀
    (fun T _ => DotyParams.h0_params n (9/10) mc₀ hcard hge3 hnotP3 T)
    (fun T _ => DotyParams.hmark_params mc₀ hclean T)

/-! ## Part 4 — the concrete free-τ `GoodFrontWidth`-failure family at `τ = w·j + r`.

Feed the Part-3 prefix `WindowedFrontProfile` mass (`wfpB`) and the free-`t` climb mass
(`DotyParams.climbBound_whp_concrete`, `climbB`) into `DotyParams.goodFrontWidth_whp_concrete`
(the deterministic `GoodFrontWidth ⟸ WindowedFrontProfile ∧ ClimbBound` glue).  The result is the
per-`τ` `GoodFrontWidth (frontWidthBound n + W₂)`-failure mass at the SAME prefix horizon, the
free-τ analog of `DotyParams.goodFrontWidth_whp_final` (which is locked to the endpoint `w·KK`). -/

open ClockFrontProfile in
/-- **`goodFrontWidth_whp_at_concrete`** — the concrete moving-frame width-failure mass at a prefix
horizon `τ = w·j + r` (`r < w`, `τ ≤ w·KK`).  The `WindowedFrontProfile` side is
`windowedFrontProfile_whp_prefix_concrete` (Part 3); the `ClimbBound` side is
`DotyParams.climbBound_whp_concrete` (free `t`).  The RHS is the prefix WFP budget plus the gated
climb-tail sum at `τ`. -/
theorem goodFrontWidth_whp_at_concrete (n : ℕ) (hn : DotyParams.N₀ ≤ n)
    (mc₀ : Config (MarkedAgent L K))
    (hcard : mc₀.card = n)
    (hge3 : AllClockGE3 (L := L) (K := K) (eraseConfig (L := L) (K := K) mc₀))
    (hnotP3 : ¬ AllClockP3 (L := L) (K := K) (eraseConfig (L := L) (K := K) mc₀))
    (hclean : ∀ m ∈ mc₀, m.2 = false)
    (Tcap : ℕ) (hcap : ClockFrontShape.capMinute (L := L) (K := K) < Tcap)
    (W₂ : ℕ) (hW₂ : 2 ≤ W₂) (B' : ℕ) (s : ℝ) (hs : 0 ≤ s)
    (j r : ℕ) (hr : r < DotyParams.w n) (hjKK : j ≤ DotyParams.KK L K - 1) :
    ((NonuniformMajority L K).transitionKernel ^ (DotyParams.w n * j + r))
        (eraseConfig (L := L) (K := K) mc₀)
        {c | (c.card = n ∧ AllClockP3 (L := L) (K := K) c ∧
            (∀ T, DotyParams.θ n ≤ ClockFrontProfile.frac (L := L) (K := K) T c →
              (9/10 : ℝ) * (rBeyond (L := L) (K := K) T c : ℝ) ^ 2 / (n : ℝ) + (DotyParams.tt n : ℝ)
                ≤ (rBeyond (L := L) (K := K) T c : ℝ) ^ 2 / (n : ℝ)))
          ∧ ¬ GoodFrontWidth (L := L) (K := K)
              (FrontTail.frontWidthBound n + W₂) c}
      ≤ (∑ T ∈ Finset.range Tcap,
          (((j : ℝ≥0∞) * DotyParams.deltaB n + 1)
            + ((GatedDrift.killK (markedK (L := L) (K := K) T (DotyParams.θn n))
                (taintedGate (L := L) (K := K) n) ^ (DotyParams.w n * j + r)) (some mc₀) {none}
              + ENNReal.ofReal
                (Real.exp (DotyParams.σ (L := L) (K := K) n
                    * (1 + 4 / (n : ℝ)) ^ (DotyParams.w n * j + r)
                    * (taintedCount (L := L) (K := K) mc₀ : ℝ)
                  + 2 * DotyParams.σ (L := L) (K := K) n
                      * (1 + 4 / (n : ℝ)) ^ (DotyParams.w n * j + r)
                      * ((DotyParams.θn n : ℝ) / (n : ℝ)) ^ 2
                      * ((DotyParams.w n * j + r : ℕ) : ℝ)
                  - DotyParams.σ (L := L) (K := K) n * ((DotyParams.tt n + 1 : ℕ) : ℝ))))))
        + (∑ k ∈ Finset.range (ClockFrontShape.capMinute (L := L) (K := K) + 1),
            ((GatedDrift.killK ((NonuniformMajority L K).transitionKernel)
                (ClimbTail.climbGate (L := L) (K := K) n k B' (DotyParams.θn n))
                  ^ (DotyParams.w n * j + r))
                (some (eraseConfig (L := L) (K := K) mc₀)) {none} +
              (ENNReal.ofReal (1 + ((B' : ℝ) / (n : ℝ)) ^ 2 * (Real.exp s - 1)))
                  ^ (DotyParams.w n * j + r) *
                ClimbTail.climbPot (L := L) (K := K) k (DotyParams.θn n) s
                  (eraseConfig (L := L) (K := K) mc₀) /
                ENNReal.ofReal (Real.exp (s * ((W₂ : ℝ) - 1))))) := by
  exact DotyParams.goodFrontWidth_whp_concrete n hn W₂ (DotyParams.w n * j + r) mc₀ _ _
    (windowedFrontProfile_whp_prefix_concrete (L := L) (K := K) n hn mc₀ hcard hge3 hnotP3 hclean
      Tcap hcap j r hr hjKK)
    (DotyParams.climbBound_whp_concrete (L := L) (K := K) n W₂ hn hW₂ B' s hs
      (DotyParams.w n * j + r) (eraseConfig (L := L) (K := K) mc₀))

/-! ## Part 5 — the free-τ width feeder `εW(τ)` in the `ClockBudgets.WidthSideP` shape.

`ClockBudgets.syncFail_le` / `sidePrefix_le_assembled` consume the width feeder in the shape
`(realκ^τ) c₀ {c | WidthSideP n c ∧ ¬GoodFrontWidth W c} ≤ εW`, where `WidthSideP n` is the §6
side conjunct `card = n ∧ AllClockP3 ∧ (the recurrence negligibility)` and `W = frontWidthBound n +
W₂`.  `goodFrontWidth_whp_at_concrete`'s event is exactly this (its `cc = 9/10`, `tt = tt n`,
`θ = θ n` match `WidthSideP`'s conjunct verbatim — only the `∧`-association differs), and
`realκ L K = (NonuniformMajority L K).transitionKernel` by `abbrev`.  So the concrete free-τ family
IS the width feeder at FREE `τ = w·j + r ≤ w·KK`.  We name its RHS as the explicit `εWAt`. -/

open ClockFrontProfile in
/-- The explicit per-`τ` width feeder at `τ = w·j + r`: the Part-4 RHS (prefix WFP budget + gated
climb-tail sum), named for the `syncFail_le` consumer. -/
noncomputable def εWAt (n : ℕ) (mc₀ : Config (MarkedAgent L K)) (Tcap W₂ B' : ℕ) (s : ℝ)
    (j r : ℕ) : ℝ≥0∞ :=
  (∑ T ∈ Finset.range Tcap,
      (((j : ℝ≥0∞) * DotyParams.deltaB n + 1)
        + ((GatedDrift.killK (markedK (L := L) (K := K) T (DotyParams.θn n))
            (taintedGate (L := L) (K := K) n) ^ (DotyParams.w n * j + r)) (some mc₀) {none}
          + ENNReal.ofReal
            (Real.exp (DotyParams.σ (L := L) (K := K) n
                * (1 + 4 / (n : ℝ)) ^ (DotyParams.w n * j + r)
                * (taintedCount (L := L) (K := K) mc₀ : ℝ)
              + 2 * DotyParams.σ (L := L) (K := K) n
                  * (1 + 4 / (n : ℝ)) ^ (DotyParams.w n * j + r)
                  * ((DotyParams.θn n : ℝ) / (n : ℝ)) ^ 2
                  * ((DotyParams.w n * j + r : ℕ) : ℝ)
              - DotyParams.σ (L := L) (K := K) n * ((DotyParams.tt n + 1 : ℕ) : ℝ))))))
    + (∑ k ∈ Finset.range (ClockFrontShape.capMinute (L := L) (K := K) + 1),
        ((GatedDrift.killK ((NonuniformMajority L K).transitionKernel)
            (ClimbTail.climbGate (L := L) (K := K) n k B' (DotyParams.θn n))
              ^ (DotyParams.w n * j + r))
            (some (eraseConfig (L := L) (K := K) mc₀)) {none} +
          (ENNReal.ofReal (1 + ((B' : ℝ) / (n : ℝ)) ^ 2 * (Real.exp s - 1)))
              ^ (DotyParams.w n * j + r) *
            ClimbTail.climbPot (L := L) (K := K) k (DotyParams.θn n) s
              (eraseConfig (L := L) (K := K) mc₀) /
            ENNReal.ofReal (Real.exp (s * ((W₂ : ℝ) - 1)))))

open ClockFrontProfile in
/-- **`widthFail_at_concrete`** — the free-τ analog of `ClockBudgets.widthFail_concrete`: the
concrete width-failure-on-side mass `εW` in the EXACT `syncFail_le` shape `{c | WidthSideP n c ∧
¬GoodFrontWidth W c}`, at ANY prefix horizon `τ = w·j + r ≤ w·KK` (not just the endpoint `w·KK`).
This is `goodFrontWidth_whp_at_concrete` (Part 4) with the conjunct re-associated to `WidthSideP`. -/
theorem widthFail_at_concrete (n : ℕ) (hn : DotyParams.N₀ ≤ n)
    (mc₀ : Config (MarkedAgent L K))
    (hcard : mc₀.card = n)
    (hge3 : AllClockGE3 (L := L) (K := K) (eraseConfig (L := L) (K := K) mc₀))
    (hnotP3 : ¬ AllClockP3 (L := L) (K := K) (eraseConfig (L := L) (K := K) mc₀))
    (hclean : ∀ m ∈ mc₀, m.2 = false)
    (Tcap : ℕ) (hcap : ClockFrontShape.capMinute (L := L) (K := K) < Tcap)
    (W₂ : ℕ) (hW₂ : 2 ≤ W₂) (B' : ℕ) (s : ℝ) (hs : 0 ≤ s)
    (j r : ℕ) (hr : r < DotyParams.w n) (hjKK : j ≤ DotyParams.KK L K - 1) :
    (ClockKilledMinute.realκ L K ^ (DotyParams.w n * j + r))
        (eraseConfig (L := L) (K := K) mc₀)
        {c | ClockBudgets.WidthSideP (L := L) (K := K) n c ∧
          ¬ GoodFrontWidth (L := L) (K := K) (FrontTail.frontWidthBound n + W₂) c}
      ≤ εWAt (L := L) (K := K) n mc₀ Tcap W₂ B' s j r := by
  refine le_trans (measure_mono ?_)
    (goodFrontWidth_whp_at_concrete (L := L) (K := K) n hn mc₀ hcard hge3 hnotP3 hclean
      Tcap hcap W₂ hW₂ B' s hs j r hr hjKK)
  intro c hc
  rw [Set.mem_setOf_eq] at hc
  obtain ⟨⟨hcardc, hP3c, hnegc⟩, hgfw⟩ := hc
  exact ⟨⟨hcardc, hP3c, hnegc⟩, hgfw⟩

end EarlyDripMarked

end ExactMajority
