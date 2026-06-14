/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# `FloorFailAdapter` — the FloorFail side-prefix adapter (thin, deterministic).

`ClockUnconditional.FloorFail mC T = {c | ¬ (mC/10 ≤ rBeyond (T+1) c)}` is the seed-leg lower-bound
failure (SEPARATE from front-width). Its probabilistic engine is ALREADY PROVEN
(`ClockRealSeed`/`ClockKilledMinute`/`ClockWeakAssembly`); this file is the thin DETERMINISTIC wiring:
- `FloorFail = ¬ SeedPost` (seedLo = mC/10), bridging FloorFail to the proven seed machinery;
- `Q_mix (T+1) ⟹ ¬ FloorFail (T)` (the crossedT 0.9-floor dominates the mC/10 floor).
NO sorry / admit / axiom / native_decide.
-/

import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.ClockUnconditional
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.ClockKilledMinute

namespace ExactMajority

namespace FloorFailAdapter

open ClockRealKernel ClockRealMixed ClockKilledMinute
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

variable {L K : ℕ}

/-- **`FloorFail = ¬ SeedPost`.**  `seedLo mC = mC/10`, so the seed postcondition `SeedPost` (the proven
seed-leg target) is exactly the complement of `FloorFail`.  This bridges FloorFail to the proven seed
machinery (`ClockKilledMinute.clock_real_seed_step_gated`, `ClockWeakAssembly.clock_real_seed_leg_avg`). -/
theorem FloorFail_iff_not_SeedPost (n mC T : ℕ) (c : Config (AgentState L K)) :
    c ∈ ClockUnconditional.FloorFail (L := L) (K := K) mC T ↔
      ¬ ClockKilledMinute.SeedPost (L := L) (K := K) n mC T c := by
  unfold ClockUnconditional.FloorFail ClockKilledMinute.SeedPost ClockRealSeed.seedLo
  simp only [Set.mem_setOf_eq]

/-- **`Q_mix (T+1) ⟹ ¬ FloorFail (T)`.**  `Q_mix n mC (T+1)`'s `crossedT` field is `9·mC/10 ≤ rBeyond
(T+1)`, which dominates the FloorFail floor `mC/10 ≤ rBeyond (T+1)`.  So once the next minute's Q_mix is
established, FloorFail at the current minute cannot occur — FloorFail is genuinely the SEED STEP between
`Q_mix(T)` and `QbulkWin(T)`, not a consequence of `Q_mix(T)` alone. -/
theorem not_FloorFail_of_Q_mix_succ {n mC T : ℕ} {c : Config (AgentState L K)}
    (hQ : Q_mix (L := L) (K := K) n mC (T + 1) c) :
    c ∉ ClockUnconditional.FloorFail (L := L) (K := K) mC T := by
  unfold ClockUnconditional.FloorFail
  simp only [Set.mem_setOf_eq, not_not]
  exact le_trans (by omega : mC / 10 ≤ 9 * mC / 10) hQ.crossedT

/-- The seed postcondition implies the floor (the `¬ FloorFail` direction), directly. -/
theorem not_FloorFail_of_SeedPost {n mC T : ℕ} {c : Config (AgentState L K)}
    (hsp : ClockKilledMinute.SeedPost (L := L) (K := K) n mC T c) :
    c ∉ ClockUnconditional.FloorFail (L := L) (K := K) mC T :=
  fun hmem => (FloorFail_iff_not_SeedPost n mC T c).mp hmem hsp

/-- **`FloorFail = {¬ SeedPost}` as SETS.**  The set-level companion of `FloorFail_iff_not_SeedPost`,
used to rewrite the proven seed-engine bounds (stated over `{c | ¬ SeedPost …}`) directly into
`FloorFail` language for the `sidePrefix_le` `hfloor` feeder. -/
theorem FloorFail_eq_not_SeedPost (n mC T : ℕ) :
    ClockUnconditional.FloorFail (L := L) (K := K) mC T
      = {c : Config (AgentState L K) | ¬ ClockKilledMinute.SeedPost (L := L) (K := K) n mC T c} := by
  ext c; exact FloorFail_iff_not_SeedPost n mC T c

/-- **Floor persistence (one step).**  On any `Q_mix n mC T` config `c`, `rBeyond (T+1)` is
non-decreasing on the one-step support (`hmono_mix_discharged`).  So once the `mC/10` floor is met
(`¬ FloorFail`), it stays met at every successor — FloorFail cannot RE-appear once crossed, as long
as `Q_mix(T)` holds.  This is the deterministic spine of floor persistence through the bulk leg
(the residual `Q_mix(T)`-prefix failure is the SEPARATE `QmixFail` feeder). -/
theorem not_FloorFail_step_of_Q_mix {n mC T : ℕ} {c c' : Config (AgentState L K)}
    (hQ : Q_mix (L := L) (K := K) n mC T c)
    (hc' : c' ∈ ((NonuniformMajority L K).stepDistOrSelf c).support)
    (hnf : c ∉ ClockUnconditional.FloorFail (L := L) (K := K) mC T) :
    c' ∉ ClockUnconditional.FloorFail (L := L) (K := K) mC T := by
  unfold ClockUnconditional.FloorFail at hnf ⊢
  simp only [Set.mem_setOf_eq, not_not] at hnf ⊢
  exact le_trans hnf
    (ClockMonoDischarge.hmono_mix_discharged (L := L) (K := K) n mC T c c' hQ hc')

/-- **`FloorFail` single-horizon bound — the `hfloor` feeder.**  Rewrites the proven gated seed
step `ClockKilledMinute.clock_real_seed_step_gated` (escape + killed-now budget on `{¬ SeedPost}`)
into `FloorFail` language.  This is exactly the per-`τ` shape `sidePrefix_le` consumes for `hfloor`. -/
theorem FloorFail_horizon_le (n mC T tseed : ℕ) (εseed εesc : ℝ≥0∞)
    (c₀ : Config (AgentState L K))
    (hesc : ((ClockKilledMinute.κQ_now (L := L) (K := K) n mC T) ^ tseed) (some c₀)
        {(none : Option (Config (AgentState L K)))} ≤ εesc)
    (hkilled : ((ClockKilledMinute.κQ_now (L := L) (K := K) n mC T) ^ tseed) (some c₀)
        {o | ¬ ClockKilledMinute.optLift
          (ClockKilledMinute.SeedPost (L := L) (K := K) n mC T) o} ≤ εseed) :
    ((realκ L K) ^ tseed) c₀
        (ClockUnconditional.FloorFail (L := L) (K := K) mC T) ≤ εesc + εseed := by
  rw [FloorFail_eq_not_SeedPost n mC T]
  exact ClockKilledMinute.clock_real_seed_step_gated n mC T tseed εseed εesc c₀ hesc hkilled

end FloorFailAdapter

end ExactMajority
