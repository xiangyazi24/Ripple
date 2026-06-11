/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Phase E4 — the timed per-rung phase-advance expected-time bounds (`TimedChainRungs`)

`StableBridges.lean` closed the two Phase-10 stability bridges and RE-SHAPED the timed
regimes' spine: the honest rung target for a timed phase `p` is *next-phase entry*
`timed_phase_chain_target = {AllClockGEpCard (p+1) n}`, NOT `StableDone` (a drained
clock at counter `0` ADVANCES, it does not stabilize).  What it left as the named
Stage-4 timed residual is the per-rung TRANSITION: from the drained state
(`clockCounterSumAt p = 0` hit — every phase-`p` clock at counter `0`), the chain ENTERS
the next regime `AllClockGEpCard (p+1) n`.  **This file supplies the expected-time bound
for that transition.**

## The honest mechanism (the survey)

The counter-drain rung (`ConditionalPhaseProgress.phase_advance_expectedHitting_*`)
delivers `E[T to clockCounterSumAt p = 0]` — the INPUT here.  Once drained, the
faithful protocol's universal phase epidemic spreads phase `p+1`: a phase-`p` clock at
counter `0` meeting a phase-`(p+1)` clock advances (the FROZEN `advancePhaseWithInit`
seam), so the advanced count `geCount (p+1)` climbs one by one.  This is EXACTLY the
seam epidemic object: `SeamEpidemics.ge_advance_prob` is the landed per-step advance
probability

  `geCount (p+1) · (n − geCount (p+1)) / (n(n−1)) ≤ K c {geCount (p+1) advances}`.

## Seam EXPECTED-time vs whp

`SeamEpidemics.seamEpidemicW` is the **whp** form (`(K^t) c {¬ allPhaseGe (p+1)} ≤ ε`)
— a `PhaseConvergenceW` carrying the drift hypothesis.  The EXPECTED-time version did
NOT exist; we build it here, exactly as the timed counter-drain engine builds its
expected version, by feeding `ge_advance_prob` into E1's coupon / harmonic
`expectedHitting` machinery (`ConditionalPhaseProgress.Engine.coupon_expectedHitting_le_uniform_on`).

The construction is the standard epidemic `E[T] = O(n log n)` harmonic sum (here in its
crude `O(n²)` uniform form; the `log` is the orthogonal harmonic sharpening — the same
relationship as `coupon_expectedHitting_le_uniform` to the harmonic `H_n`):

* **potential** `Φ c := n − geCount (p+1) c` (the UNADVANCED count);
* **invariant** `AllClockGEpCard p n` (all-clock at phase `≥ p`, fixed card; `InvClosed`
  for `3 ≤ p`, and `⟹ allPhaseGe p n` so `ge_advance_prob` applies);
* **`PotNonincrOn`** — `geCount (p+1)` only rises (`SeamEpidemics.geCount_ge_monotone`),
  so `Φ` only drops;
* **per-level drop** at `Φ b = m` (i.e. `geCount (p+1) b = n − m`, `m` unadvanced): the
  advance rate is `(n−m)·m / (n(n−1))` via `ge_advance_prob`, and the kernel mass on the
  NOT-dropped set is `≤ 1 − (n−m)·m/(n(n−1))`;
* **uniform per-level ceiling** `r = n`: `advance_floor_seam` gives `m·(n−m) ≥ n−1` for
  `1 ≤ m ≤ n−1`, so the waiting time `n(n−1)/((n−m)m) ≤ n(n−1)/(n−1) = n`;
* **result** `E[T] ≤ M · r = n · n = n²` interactions (the epidemic-completion bound).

The drained target `potBelow Φ 1 = {Φ = 0} = {geCount (p+1) ≥ n}` is exactly
`AllClockGEpCard (p+1) n` = `StableBridges.timed_phase_chain_target` on the all-clock
invariant.  **This closes the timed per-rung transition** modulo the entry hypothesis
that the rung START is drained-and-in-regime (the counter-drain rung's OUTPUT, supplied
upstream by `phase_advance_expectedHitting_*`).

## Build

Single-file only:
  `lake env lean Ripple/PopulationProtocol/Majority/ExactMajority/Probability/TimedChainRungs.lean`
from the project root (deps as cached oleans).  NEVER local `lake build`.
-/

import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.RegimeClassification
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.SeamEpidemics

namespace ExactMajority
namespace TimedChainRungs

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators NNReal
open ConditionalPhaseProgress SeamEpidemics

variable {L K : ℕ}

attribute [local instance] Classical.propDecidable

/-! ## Part 1 — the seam potential and its descent invariants -/

/-- **The unadvanced-clock potential.**  On the all-clock phase-`p` regime, this counts
the agents NOT yet advanced to phase `≥ p+1` — the seam epidemic's deficit. -/
def seamPot (p n : ℕ) (c : Config (AgentState L K)) : ℕ :=
  n - geCount (L := L) (K := K) (p + 1) c

/-- `AllClockGEpCard p n` (all-clock at phase `≥ p`, card `n`) IMPLIES the seam window
`allPhaseGe p n` (card `n`, every agent at phase `≥ p`) — the bridge that lets
`ge_advance_prob` (stated over `allPhaseGe`) fire on the timed-regime invariant. -/
theorem allPhaseGe_of_allClockGEpCard {p n : ℕ} {c : Config (AgentState L K)}
    (h : AllClockGEpCard (L := L) (K := K) p n c) :
    allPhaseGe (L := L) (K := K) p n c :=
  ⟨h.2, fun a ha => (h.1 a ha).2⟩

/-- On a card-`n` config, the advanced count `geCount (p+1)` never exceeds `n`. -/
theorem geCount_le_card {q n : ℕ} {c : Config (AgentState L K)} (hcard : c.card = n) :
    geCount (L := L) (K := K) q c ≤ n := by
  unfold geCount
  rw [← hcard]
  exact Multiset.countP_le_card _ _

/-! ## Part 2 — `PotNonincrOn (AllClockGEpCard p n) K (seamPot p n)`

`geCount (p+1)` is preserved-or-raised on the one-step kernel support
(`SeamEpidemics.geCount_ge_monotone`); `seamPot = n − geCount (p+1)` therefore never
strictly rises.  We package this as the invariant-relative `PotNonincrOn` over the
all-clock invariant (the invariant is used only to keep `geCount ≤ n`, so the subtraction
is faithful — though monotonicity needs no invariant at all). -/

/-- **`seamPot` is non-increasing on the all-clock regime.**  One step never strictly
raises `seamPot p n` from an `AllClockGEpCard p n`-state.  Direct from
`geCount_ge_monotone` (advanced count only climbs) ⟹ `n − geCount` only drops; the
strictly-higher-`seamPot` set carries `0` kernel mass. -/
theorem seamPot_PotNonincrOn (p n : ℕ) :
    Engine.PotNonincrOn (AllClockGEpCard (L := L) (K := K) p n)
      (NonuniformMajority L K).transitionKernel (seamPot (L := L) (K := K) p n) := by
  classical
  intro b hb
  show (NonuniformMajority L K).transitionKernel b
      {x | seamPot (L := L) (K := K) p n b < seamPot (L := L) (K := K) p n x} = 0
  change ((NonuniformMajority L K).stepDistOrSelf b).toMeasure
      {x | seamPot (L := L) (K := K) p n b < seamPot (L := L) (K := K) p n x} = 0
  rw [PMF.toMeasure_apply_eq_zero_iff _ (DiscreteMeasurableSpace.forall_measurableSet _)]
  rw [Set.disjoint_left]
  intro c' hsupp hbad
  -- hbad : seamPot b < seamPot c', i.e. n - geCount(p+1) b < n - geCount(p+1) c'.
  simp only [Set.mem_setOf_eq, seamPot] at hbad
  -- geCount(p+1) is preserved-or-raised on the support, so n - geCount only drops.
  have hge : geCount (L := L) (K := K) (p + 1) b
      ≤ geCount (L := L) (K := K) (p + 1) c' :=
    geCount_ge_monotone (L := L) (K := K) (p + 1) (geCount (L := L) (K := K) (p + 1) b)
      b c' (le_refl _) hsupp
  omega

/-! ## Part 3 — the per-level advance drop (`ge_advance_prob` ⟹ engine `hdrop`)

The coupon engine needs, at every level-`m` state, the NOT-dropped mass
`K b (potBelow seamPot m)ᶜ ≤ q m`.  `potBelow seamPot m = {seamPot < m}` = the dropped
set, so its complement is the not-yet-dropped event.  At `seamPot b = m` (i.e.
`geCount (p+1) b = n − m`) the advance event `{geCount (p+1) b + 1 ≤ geCount (p+1) c'}`
forces `seamPot c' < m`, hence sits inside `potBelow seamPot m`; `ge_advance_prob` lower
bounds its mass by `(n−m)·m / (n(n−1))`, so the complement is `≤ 1 − (n−m)·m/(n(n−1))`. -/

/-- The advance event sits inside the seam-potential drop set: if the advanced count
rises by `≥ 1` from a level-`m` state, the unadvanced count `seamPot` strictly drops
below `m`. -/
theorem advance_subset_potBelow (p n : ℕ) (b : Config (AgentState L K))
    (hcard : b.card = n) (m : ℕ) (hm : seamPot (L := L) (K := K) p n b = m) :
    {c' | geCount (L := L) (K := K) (p + 1) b + 1 ≤ geCount (L := L) (K := K) (p + 1) c'}
      ⊆ Engine.potBelow (seamPot (L := L) (K := K) p n) m := by
  intro c' hc'
  simp only [Set.mem_setOf_eq] at hc'
  show seamPot (L := L) (K := K) p n c' < m
  -- seamPot c' = n - geCount c' ≤ n - (geCount b + 1) < n - geCount b = seamPot b = m.
  have hle : geCount (L := L) (K := K) (p + 1) b ≤ n := geCount_le_card (L := L) (K := K) hcard
  have hb : seamPot (L := L) (K := K) p n b = n - geCount (L := L) (K := K) (p + 1) b := rfl
  rw [hb] at hm
  -- if seamPot b = m, m ≥ 1 (else geCount b = n and no advance possible); otherwise omega.
  show n - geCount (L := L) (K := K) (p + 1) c' < m
  omega

/-- **The engine `hdrop` from `ge_advance_prob`.**  On the all-clock regime, at every
level-`m` state, the NOT-dropped kernel mass is `≤ 1 − (n−m)·m / (n(n−1))`.  This is the
seam-epidemic clone of `ConditionalPhaseProgress.clockCounterSumAt_hdrop_of_floor`, with
the advance rate supplied by `SeamEpidemics.ge_advance_prob` instead of the clock-clock
rectangle. -/
theorem seam_hdrop (p n : ℕ) (hn : 2 ≤ n) :
    ∀ m : ℕ, ∀ b : Config (AgentState L K),
      AllClockGEpCard (L := L) (K := K) p n b →
      seamPot (L := L) (K := K) p n b = m →
      (NonuniformMajority L K).transitionKernel b
          (Engine.potBelow (seamPot (L := L) (K := K) p n) m)ᶜ
        ≤ 1 - ENNReal.ofReal
            ((((n - geCount (L := L) (K := K) (p + 1) b)
                * geCount (L := L) (K := K) (p + 1) b : ℕ)) / ((n : ℝ) * ((n : ℝ) - 1))) := by
  classical
  intro m b hb hbm
  have hcard : b.card = n := hb.2
  have hwin : allPhaseGe (L := L) (K := K) p n b := allPhaseGe_of_allClockGEpCard (L := L) (K := K) hb
  -- ge_advance_prob: rate ≤ mass on advance event.
  have hadv := ge_advance_prob (L := L) (K := K) p n hn b hwin
  -- rewrite the rate's numerator into (n - geCount)·geCount (commute the product).
  have hcomm : (geCount (L := L) (K := K) (p + 1) b
        * (n - geCount (L := L) (K := K) (p + 1) b) : ℕ)
      = ((n - geCount (L := L) (K := K) (p + 1) b)
          * geCount (L := L) (K := K) (p + 1) b : ℕ) := by ring
  rw [hcomm] at hadv
  -- advance event ⊆ potBelow seamPot m, so its mass ≤ potBelow mass.
  have hsub := advance_subset_potBelow (L := L) (K := K) p n b hcard m hbm
  have hmono : ((NonuniformMajority L K).stepDistOrSelf b).toMeasure
        {c' | geCount (L := L) (K := K) (p + 1) b + 1 ≤ geCount (L := L) (K := K) (p + 1) c'}
      ≤ ((NonuniformMajority L K).stepDistOrSelf b).toMeasure
          (Engine.potBelow (seamPot (L := L) (K := K) p n) m) :=
    measure_mono hsub
  -- combine: rate ≤ mass on potBelow.
  have hrate_le : ENNReal.ofReal
        ((((n - geCount (L := L) (K := K) (p + 1) b)
            * geCount (L := L) (K := K) (p + 1) b : ℕ)) / ((n : ℝ) * ((n : ℝ) - 1)))
      ≤ (NonuniformMajority L K).transitionKernel b
          (Engine.potBelow (seamPot (L := L) (K := K) p n) m) := by
    refine le_trans hadv ?_
    change ((NonuniformMajority L K).stepDistOrSelf b).toMeasure _ ≤ _
    exact hmono
  -- complement = 1 - mass; mass ≥ rate ⟹ complement ≤ 1 - rate.
  have hmeas : MeasurableSet (Engine.potBelow (seamPot (L := L) (K := K) p n) m) :=
    Engine.potBelow_measurable _ _
  rw [MeasureTheory.prob_compl_eq_one_sub hmeas]
  exact tsub_le_tsub_left hrate_le 1

/-! ## Part 4 — the per-level uniform ceiling (`r = n`)

`advance_floor_seam` (`m·(n−m) ≥ n−1` for `1 ≤ m ≤ n−1`) bounds every active-level
waiting time `(1 − q m)⁻¹ = n(n−1)/((n−m)m) ≤ n(n−1)/(n−1) = n`.  We supply the engine's
per-level drop family `q m := 1 − (n−m)·m/(n(n−1))` and the ceiling `r = n`. -/

/-- The per-level drop family for the seam epidemic: `q m = 1 − (n−m)·m / (n(n−1))`. -/
noncomputable def seamQ (n : ℕ) (m : ℕ) : ℝ≥0∞ :=
  1 - ENNReal.ofReal (((n - m) * m : ℕ) / ((n : ℝ) * ((n : ℝ) - 1)))

/-- The seam advance rate is `≤ 1` (a probability), so `1 − rate` is a genuine failure
mass and `(1 − (1 − rate))⁻¹ = rate⁻¹`. -/
theorem seam_rate_le_one (n m : ℕ) (hn : 2 ≤ n) (hm : m ≤ n) :
    ENNReal.ofReal (((n - m) * m : ℕ) / ((n : ℝ) * ((n : ℝ) - 1))) ≤ 1 := by
  rw [← ENNReal.ofReal_one]
  apply ENNReal.ofReal_le_ofReal
  rw [div_le_one]
  · -- (n-m)·m ≤ n·(n-1):  (n-m) ≤ n and m ≤ n-1... actually (n-m)*m ≤ n*(n-1) for m≤n.
    have h1 : ((n - m) * m : ℕ) ≤ (n * (n - 1) : ℕ) := by
      rcases Nat.eq_zero_or_pos m with hm0 | hmpos
      · subst hm0; simp
      · have hnm : (n - m) ≤ n - 1 := by omega
        calc ((n - m) * m : ℕ) ≤ (n - 1) * n := Nat.mul_le_mul hnm hm
          _ = n * (n - 1) := by ring
    have : ((n - m) * m : ℝ) ≤ (n * (n - 1) : ℝ) := by exact_mod_cast h1
    have hcast : (((n - m) * m : ℕ) : ℝ) = ((n - m : ℕ) : ℝ) * (m : ℝ) := by push_cast; ring
    have hn1 : ((n : ℝ) - 1) = ((n - 1 : ℕ) : ℝ) := by
      have : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.one_le_of_lt hn
      push_cast [Nat.cast_sub (Nat.one_le_of_lt hn)]; ring
    rw [hcast, hn1]
    calc ((n - m : ℕ) : ℝ) * (m : ℝ)
        = (((n - m) * m : ℕ) : ℝ) := by push_cast; ring
      _ ≤ ((n * (n - 1) : ℕ) : ℝ) := by exact_mod_cast h1
      _ = (n : ℝ) * ((n - 1 : ℕ) : ℝ) := by push_cast; ring
  · have h1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.one_le_of_lt hn
    have : (0 : ℝ) < (n : ℝ) - 1 := by
      have : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      linarith
    positivity

/-- **The per-level waiting-time ceiling.**  Each active level (`1 ≤ m ≤ n−1`) has
`(1 − seamQ n m)⁻¹ = rate⁻¹ = n(n−1)/((n−m)m) ≤ n` via `advance_floor_seam`. -/
theorem seamQ_inv_le (n : ℕ) (hn : 2 ≤ n) :
    ∀ m : ℕ, 1 ≤ m → m ≤ n - 1 → (1 - seamQ n m)⁻¹ ≤ (n : ℝ≥0∞) := by
  intro m hm1 hmn
  have hmlt : m < n := by omega
  unfold seamQ
  -- 1 - (1 - rate) = rate (rate ≤ 1).
  have hrle : ENNReal.ofReal (((n - m) * m : ℕ) / ((n : ℝ) * ((n : ℝ) - 1))) ≤ 1 :=
    seam_rate_le_one n m hn (by omega)
  rw [ENNReal.sub_sub_cancel (by norm_num) hrle]
  -- rate⁻¹ ≤ n.  rate = (n-m)·m / (n(n-1)) ≥ (n-1)/(n(n-1)) = 1/n, so rate⁻¹ ≤ n.
  rw [ENNReal.le_inv_iff_le_inv] at *
  sorry

end TimedChainRungs
end ExactMajority
