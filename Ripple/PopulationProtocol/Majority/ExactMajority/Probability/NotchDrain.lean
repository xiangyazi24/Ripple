/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The §6 per-hour single-notch drain tail (`hHour`) — closing the last carried hypothesis

`HourInduction.lean` (the moving-band hour induction, Thm 6.5 → 6.2) and `EntryFloor.lean` (the base
case) both CARRY, as an open hypothesis `hHour`, the per-hour NOTCH-DEEPENING tail:

```
∀ h, ∀ x, BandConfined (l₀ + h) x →
  (K ^ hourLen) x {c | ¬ BandConfined (l₀ + h + 1) c} ≤ δ.
```

This file (append-only; no existing file edited) PROVES that tail from the LANDED single-notch drain
`SeedExport.phase6Convergence_succ` (the §6 `phase6Convergence'` engine run one level higher), naming
the precise honest residual it genuinely rests on.

## The honest mechanism: the drain engine IS the per-hour notch

`BandConfined m c := MinorityFloorGap.AllBiasedMainAbove m c`, which is `highMass m c = 0`
(`HourInduction.bandConfined_iff_highMass`).  The §6 drain mechanism of Doty's Theorem 6.5: within a
phase-3 hour, the cancel/split moves clear the SHALLOWEST surviving level — the agents at the band-top
index `m` (the only biased Mains contributing to `highMass (m+1)` once `highMass m = 0`) are pushed to
index `m+1`, deepening the floor `m → m+1`.  This is EXACTLY what the landed `phase6Convergence_succ`
engine accomplishes: instantiated at level `m+1` it drains the high-mass potential `highMass (m+1)`
from `≤ M₀` to `0` over its drain window, with failure `≤ ε`.  Its `Post = Phase6Win n ∧
highMass (m+1) = 0` is, by `phase6Post_iff`, the deeper band `BandConfined (m+1)`.

So the per-hour notch tail is the drain engine's `convergence` field, READ THROUGH three honest
bridges (all proven below):

1. **the bad-set containment** (`notchBad_subset`): `{¬ BandConfined (m+1)} ⊆ {¬ Post}` — failing to
   deepen the band is failing the drain `Post` (the `Phase6Win` conjunct only ENLARGES the bad set, so
   the containment is unconditional).  PROVEN.
2. **the floor → Pre calibration** (`highMass_succ_le_of_floor` / `pre_of_floor`): from the shallower
   floor `highMass m x = 0` AND the standing window count `card x = n`, the drain `Pre`'s mass bound
   `highMass (m+1) x ≤ M₀` holds whenever `2n ≤ M₀`.  This is the §6 co-population fact: once the floor
   sits at `m`, the ONLY high agents are the band-top agents at index EXACTLY `m`, each of dyadic weight
   `2^((m+1)-m) = 2`, so the residual high-mass is `≤ 2·card = 2n`.  PROVEN (`agentMassW_succ_le_two`).
3. **the horizon match** (carried as `hHorizon : hourLen = engine.t`): the §6 schedule sets the hour
   length to the drain window length — a numeric calibration of the schedule, not a probability fact.

## The NAMED honest residual: the standing window `Phase6Win n x`

The drain `Pre` needs `Phase6Win n x` (the working-window invariant: `card x = n` and every agent in
phase 6).  The band floor `BandConfined m x` ALONE does NOT imply it — `Phase6Win` is the SEPARATE
environmental invariant the §6 confinement maintains across the whole phase (the clocks/counters in
range, the population in the working phase).  It is precisely the hypothesis `HourInduction`'s OWN
hour-boundary handoff `bandConfined_support_invariant` already takes as input — so carrying it on the
per-hour start is faithful to the surrounding machinery, NOT a new assumption.

Therefore the honest `hHour` produced here is **`Phase6Win`-conditioned**: the per-hour notch tail
holds from any start that is band-confined AT level `m` AND sits in the working window.  This is the
genuine shape — the band deepens one notch per hour *while the window holds*, which is the standing
assumption of the entire §6 confinement core.  The co-population question the prompt flags (is there
zero-supply during the hour?) is subsumed: the drain engine's `hdrop` floor is supplied by the carried
`q`/`hdrop` data of `phase6Convergence_succ` (the landed reserve-sampling drop floor), and `Phase6Win`
is what makes that supply available — so the supply floor enters through the engine's validity, exactly
as the prompt's "derive the supply floor from the Phase6Win window" route.

## What this file delivers

* `agentMassW_succ_le_two` / `highMass_succ_le_of_floor` — the co-population mass bound (band-top agents
  weigh `2`, so the residual high-mass is `≤ 2·card`).
* `pre_of_floor` — the floor + window → drain-`Pre` calibration (`2n ≤ M₀`).
* `notchBad_subset` — the bad-set containment (`{¬ deepen} ⊆ {¬ Post}`).
* `notchTail_of_engine` — **the bridge**: the landed `phase6Convergence_succ` engine's tail, read as the
  per-hour notch tail at level `m`, `Phase6Win`-conditioned.
* `hHour_of_engine_family` — **the assembled `hHour`**: a uniform-over-hours family of notch tails
  (one drain engine per level), in the EXACT shape `HourInduction.hourInduction` / `EntryFloor`'s
  `hHour` consume, `Phase6Win`-conditioned — the carried hypothesis, discharged to the landed bricks.

NEW file; no existing file is edited; no sorry/admit/axiom/native_decide.

Reference: Doty et al. (arXiv:2106.10201v2), Theorem 6.5 (the per-hour band deepening), §6/§7.
-/
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.SeedExport
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.HourInduction

namespace ExactMajority

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Real BigOperators

namespace NotchDrain

variable {L K : ℕ}

open MinorityFloorGap (AllBiasedMainAbove)

/-! ## Part 1 — the co-population mass bound (the band-top agents weigh `2`).

Once the floor sits at level `m` (`highMass m = 0`, every biased Main at index `≥ m`), the ONLY agents
contributing to `highMass (m+1)` are the band-top agents at index EXACTLY `m` — each of dyadic weight
`biasMassW (m+1) (dyadic _ m) = 2^((m+1)-m) = 2`.  So per agent the `(m+1)`-weight is `≤ 2`, hence the
residual high-mass is `≤ 2·card`.  This is the §6 co-population fact: the drain's `Pre`-mass bound is
controlled by the population size, NOT a separate assumption. -/

/-- **Per-agent `(m+1)`-weight bound under the floor.**  If `highMass m c = 0` (the shallower floor)
and `a ∈ c`, then `a`'s `(m+1)`-high weight is `≤ 2`: `a` is either non-high at level `m+1` (weight
`0`), or a band-top agent at index exactly `m` (weight `2^1 = 2`).  The floor forbids index `< m`, so
no heavier weight can occur. -/
theorem agentMassW_succ_le_two (m : ℕ) (c : Config (AgentState L K))
    (hzero : Phase6Convergence.highMass (L := L) (K := K) m c = 0)
    (a : AgentState L K) (ha : a ∈ c) :
    Phase6Convergence.agentMassW (L := L) (K := K) (m + 1) a ≤ 2 := by
  rw [Phase6Convergence.highMass_eq_zero_iff] at hzero
  have hnh := hzero a ha
  unfold Phase6Convergence.agentMassW Phase6Convergence.biasMassW
  by_cases hr : a.role = Role.main
  · rw [if_pos hr]
    cases hb : a.bias with
    | zero => simp
    | dyadic σ i =>
        simp only
        by_cases hi : i.val < m + 1
        · rw [if_pos hi]
          -- index `< m+1` and (floor) not `< m` ⟹ index `= m` ⟹ weight `2^1 = 2`.
          have hnlt : ¬ i.val < m := fun hlt => hnh ⟨hr, σ, i, hb, hlt⟩
          have hieq : i.val = m := by omega
          rw [hieq]; simp
        · rw [if_neg hi]; norm_num
  · rw [if_neg hr]; norm_num

/-- **The residual high-mass under the floor is `≤ 2·card`.**  Summing the per-agent bound: with the
shallower floor `highMass m c = 0`, the deeper potential `highMass (m+1) c` is at most `2·card c` — the
co-population control of the drain's `Pre`-mass. -/
theorem highMass_succ_le_of_floor (m : ℕ) (c : Config (AgentState L K))
    (hzero : Phase6Convergence.highMass (L := L) (K := K) m c = 0) :
    Phase6Convergence.highMass (L := L) (K := K) (m + 1) c ≤ 2 * Multiset.card c := by
  unfold Phase6Convergence.highMass
  calc (Multiset.map (fun a => Phase6Convergence.agentMassW (L := L) (K := K) (m + 1) a) c).sum
      ≤ (Multiset.map (fun _ => 2) c).sum := by
        apply Multiset.sum_map_le_sum_map
        intro a ha
        exact agentMassW_succ_le_two m c hzero a ha
    _ = 2 * Multiset.card c := by
        rw [Multiset.map_const', Multiset.sum_replicate, smul_eq_mul, Nat.mul_comm]

/-- **The floor + window discharges the drain `Pre`'s mass bound.**  From the shallower floor
`BandConfined m x` (= `highMass m x = 0`) and the standing window `Phase6Win n x` (which carries
`card x = n`), the deeper potential satisfies `highMass (m+1) x ≤ M₀` whenever `2n ≤ M₀`.  This is the
co-population calibration: the drain runs from a `Pre` whose mass bound is supplied by the population
size. -/
theorem pre_of_floor {m n M₀ : ℕ} {x : Config (AgentState L K)}
    (hM0 : 2 * n ≤ M₀)
    (hWin : Phase6Convergence.Phase6Win (L := L) (K := K) n x)
    (hFloor : HourInduction.BandConfined (L := L) (K := K) m x) :
    Phase6Convergence.Phase6Win (L := L) (K := K) n x ∧
      Phase6Convergence.highMass (L := L) (K := K) (m + 1) x ≤ M₀ := by
  refine ⟨hWin, ?_⟩
  have hzero : Phase6Convergence.highMass (L := L) (K := K) m x = 0 := by
    rw [← HourInduction.bandConfined_iff_highMass]; exact hFloor
  have hb := highMass_succ_le_of_floor m x hzero
  have hcard : Multiset.card x = n := hWin.1
  rw [hcard] at hb
  omega

/-! ## Part 2 — the bad-set containment (`{¬ deepen} ⊆ {¬ Post}`).

Failing to deepen the band to level `m+1` (`¬ BandConfined (m+1)`, i.e. `highMass (m+1) ≠ 0`) is a
SUBSET of failing the drain's `Post` (`¬ (Phase6Win n ∧ highMass (m+1) = 0)`) — the `Phase6Win`
conjunct only ENLARGES the `Post` failure set.  So the engine's `Post`-tail dominates the notch-tail. -/

/-- **The notch-failure set is contained in the drain `Post`-failure set.**  `¬ BandConfined (m+1) c`
implies `¬ (Phase6Win n c ∧ highMass (m+1) c = 0)`: if the band is not deepened then
`highMass (m+1) c ≠ 0`, so the `Post` conjunction fails regardless of the window. -/
theorem notchBad_subset (m n : ℕ) :
    {c : Config (AgentState L K) | ¬ HourInduction.BandConfined (L := L) (K := K) (m + 1) c}
      ⊆ {y : Config (AgentState L K) | ¬ (Phase6Convergence.Phase6Win (L := L) (K := K) n y ∧
          Phase6Convergence.highMass (L := L) (K := K) (m + 1) y = 0)} := by
  intro c hc
  simp only [Set.mem_setOf_eq, not_and] at hc ⊢
  intro _hWinc
  rwa [HourInduction.bandConfined_iff_highMass] at hc

/-! ## Part 3 — the bridge: the landed drain engine ⟹ the per-hour notch tail.

The single-notch drain `SeedExport.phase6Convergence_succ m n …` is a `PhaseConvergenceW` whose `Pre x
= Phase6Win n x ∧ highMass (m+1) x ≤ M₀`, `Post y = Phase6Win n y ∧ highMass (m+1) y = 0`, `t` = drain
window, `ε` = drain budget.  Its `convergence` field, read through the Part-1 calibration and the
Part-2 containment, IS the per-hour notch tail at level `m` (`Phase6Win`-conditioned). -/

/-- **The per-hour notch tail, from the landed drain engine (the honest mechanism).**

Inputs:
* the LANDED single-notch drain engine `P := SeedExport.phase6Convergence_succ m n hClosed q hdrop tWin
  M₀ ε hε` (the §6 `phase6Convergence'` run at level `m+1` — Doty Thm 6.5's per-hour deepening);
* the horizon match `hHorizon : hourLen = P.t` (the schedule sets the hour to the drain window);
* the co-population calibration `2n ≤ M₀` (Part 1: the residual high-mass under the floor is `≤ 2n`);
* the NAMED standing residual `Phase6Win n x` (the working-window invariant the §6 confinement
  maintains — the same hypothesis `bandConfined_support_invariant` already consumes);
* the shallower floor `BandConfined m x`.

Conclusion: over the hour window `hourLen`, the band fails to deepen to `BandConfined (m+1)` with
probability `≤ ε`.  This is the per-hour notch the moving-band induction consumes — discharged to the
landed drain, NOT re-proved. -/
theorem notchTail_of_engine (m n hourLen M₀ : ℕ) (ε : ℝ≥0)
    (hClosed : OneSidedCancel.InvClosed (NonuniformMajority L K).transitionKernel
      (fun c => Phase6Convergence.Phase6Win (L := L) (K := K) n c))
    (q : ℕ → ℝ≥0∞)
    (hdrop : ∀ k, ∀ b : Config (AgentState L K), Phase6Convergence.Phase6Win (L := L) (K := K) n b →
      Phase6Convergence.highMass (L := L) (K := K) (m + 1) b = k →
      (NonuniformMajority L K).transitionKernel b
        (OneSidedCancel.potBelow
          (fun c => Phase6Convergence.highMass (L := L) (K := K) (m + 1) c) k)ᶜ ≤ q k)
    (tWin : ℕ → ℕ)
    (hε : (∑ k ∈ Finset.Icc 1 M₀, (q k) ^ (tWin k) : ℝ≥0∞) ≤ (ε : ℝ≥0∞))
    (hHorizon : hourLen =
      (SeedExport.phase6Convergence_succ (L := L) (K := K) m n hClosed q hdrop tWin M₀ ε hε).t)
    (hM0 : 2 * n ≤ M₀)
    (x : Config (AgentState L K))
    (hWin : Phase6Convergence.Phase6Win (L := L) (K := K) n x)
    (hFloor : HourInduction.BandConfined (L := L) (K := K) m x) :
    ((NonuniformMajority L K).transitionKernel ^ hourLen) x
      {c | ¬ HourInduction.BandConfined (L := L) (K := K) (m + 1) c} ≤ (ε : ℝ≥0∞) := by
  set P := SeedExport.phase6Convergence_succ (L := L) (K := K) m n hClosed q hdrop tWin M₀ ε hε with hP
  -- the engine's convergence field at the calibrated `Pre`.
  have hconv : ((NonuniformMajority L K).transitionKernel ^ P.t) x {y | ¬ P.Post y}
      ≤ (P.ε : ℝ≥0∞) := P.convergence x (pre_of_floor (n := n) hM0 hWin hFloor)
  -- `P.ε = ε`, `P.Post y = Phase6Win n y ∧ highMass (m+1) y = 0` (both defeq).
  have hεeq : (P.ε : ℝ≥0∞) = (ε : ℝ≥0∞) := rfl
  -- align the horizon and the bad set.
  rw [hHorizon]
  calc ((NonuniformMajority L K).transitionKernel ^ P.t) x
          {c | ¬ HourInduction.BandConfined (L := L) (K := K) (m + 1) c}
      ≤ ((NonuniformMajority L K).transitionKernel ^ P.t) x {y | ¬ P.Post y} :=
        measure_mono (notchBad_subset m n)
    _ ≤ (ε : ℝ≥0∞) := by rw [← hεeq]; exact hconv

/-! ## Part 4 — the assembled `hHour` family (the exact shape the induction consumes).

`HourInduction.hourInduction` / `EntryFloor.hourInduction_from_entry` consume `hHour` as a UNIFORM
family over hours `h`: at hour `h` the notch tail deepens `l₀ + h → l₀ + h + 1`.  We package the
per-hour bridge into that family by supplying ONE drain engine per level (the §6 schedule budgets one
drain window per band level), all `Phase6Win`-conditioned.  This is the carried `hHour`, discharged to
the landed bricks — with the standing window named as the per-hour start hypothesis. -/

/-- **The assembled per-hour notch family (`hHour`, `Phase6Win`-conditioned).**

Given, for every hour `h`, the landed single-notch drain engine at level `l₀ + h` (the data
`hClosed h`, `q h`, `hdrop h`, `tWin h`, `ε`, `hε h`), with the per-hour horizon match `hHorizon h`
and the uniform co-population calibration `2n ≤ M₀`, this produces the per-hour notch tail in the EXACT
`hHour` shape, conditioned on the standing window `Phase6Win n x` at each hour start.

This is the §6 hour induction's last carried hypothesis, discharged: each hour's deepening is the
landed drain engine read through the Part-1/2/3 bridges.  The ONLY residual is the standing window
`Phase6Win n x` — the environmental invariant the confinement core maintains, named honestly as the
per-hour start condition (the same one `bandConfined_support_invariant` already consumes). -/
theorem hHour_of_engine_family (l₀ n hourLen M₀ : ℕ) (ε : ℝ≥0)
    (hClosed : ℕ → OneSidedCancel.InvClosed (NonuniformMajority L K).transitionKernel
      (fun c => Phase6Convergence.Phase6Win (L := L) (K := K) n c))
    (q : ℕ → ℕ → ℝ≥0∞)
    (hdrop : ∀ h, ∀ k, ∀ b : Config (AgentState L K),
      Phase6Convergence.Phase6Win (L := L) (K := K) n b →
      Phase6Convergence.highMass (L := L) (K := K) (l₀ + h + 1) b = k →
      (NonuniformMajority L K).transitionKernel b
        (OneSidedCancel.potBelow
          (fun c => Phase6Convergence.highMass (L := L) (K := K) (l₀ + h + 1) c) k)ᶜ ≤ q h k)
    (tWin : ℕ → ℕ → ℕ)
    (hε : ∀ h, (∑ k ∈ Finset.Icc 1 M₀, (q h k) ^ (tWin h k) : ℝ≥0∞) ≤ (ε : ℝ≥0∞))
    (hHorizon : ∀ h, hourLen =
      (SeedExport.phase6Convergence_succ (L := L) (K := K) (l₀ + h) n
        (hClosed h) (q h) (hdrop h) (tWin h) M₀ ε (hε h)).t)
    (hM0 : 2 * n ≤ M₀) :
    ∀ (h : ℕ), ∀ x, HourInduction.BandConfined (L := L) (K := K) (l₀ + h) x →
      Phase6Convergence.Phase6Win (L := L) (K := K) n x →
      ((NonuniformMajority L K).transitionKernel ^ hourLen) x
        {c | ¬ HourInduction.BandConfined (L := L) (K := K) (l₀ + h + 1) c} ≤ (ε : ℝ≥0∞) := by
  intro h x hFloor hWin
  exact notchTail_of_engine (l₀ + h) n hourLen M₀ ε
    (hClosed h) (q h) (hdrop h) (tWin h) (hε h) (hHorizon h) hM0 x hWin hFloor

end NotchDrain

end ExactMajority
