/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Wave B — wiring the per-seam ADVANCE-TRIGGER seed into the assembly (`SeedTrigWiring`)

This file converges the two wave-A outputs `SeedRungs.lean` (the one-step a.s. advance seed
from a drained all-clock counter-`0` state) and `AssemblyBridges.lean` (the PROVED obstruction
`drained_post_no_advTrig`: on a drained exact-`p` window `advTriggered (p+1)` is FALSE) into the
`ConcreteAssembly` track, by re-shaping the work→seam handoff so the seam entry happens ONE step
AFTER the work `Post` — the SEED step — at which point `advTriggered (p+1)` holds.

## The world-bridge (Part A)

`SeamEpidemics.advTriggered (p+1) c` (`1 ≤ countP (p+1 ≤ phase) c`) and
`SeedRungs.seedTarget p` (`1 ≤ geCount (p+1) c = 1 ≤ countP (geP (p+1)) c`) are the SAME set
(the two `countP` predicates `decide (p+1 ≤ phase)` and `geP (p+1)` agree pointwise).  So the
seam's advance trigger IS the SeedRungs seed target — the `advTriggered_iff_seedTarget`
equivalence below makes the two tracks' worlds one.

## The seed-step `PhaseConvergenceW` (Parts B–C)

`seedStepW` packages a ONE-step (`t = 1`), failure-`0` (`ε = 0`) `PhaseConvergenceW` whose `Post`
is the seam `Pre` shape `allPhaseGe p n ∧ advTriggered (p+1)`.  Its `convergence` needs two a.s.
facts from its `Pre`:

  (i)  `allPhaseGe p n` one-step closure — the `≥`-window is support-closed
       (`SeamEpidemics.allPhaseGe_absorbing`, lifted to `K^1` via
       `transitionKernel_pow_not_pred_eq_zero_of_stepDistOrSelf_support_preserved`);
  (ii) `advTriggered (p+1)` fires a.s. in one step — the SEED event.

For the genuinely-`O(1)`-deterministic counter-timed case (the all-CLOCK drained state), (ii) is
supplied for FREE by `SeedRungs.drained_kernel_seedTarget_compl_zero` (`seedStepW_timed`).  For
the ConcreteAssembly main-drain seams the all-MAIN drained `Post` is a DIFFERENT window (no
clocks), so (ii) is a genuine per-seam one-step seed event `hSeedStep` — strictly NARROWER than
the FALSE `hTrig` (which the work `Post` cannot supply): instead of "trigger holds on the work
`Post`" we carry "trigger fires on the NEXT step from the work `Post`".

## The shifted seam and the re-cut assembly (Parts D–E)

`seamWithSeed` composes `seedStepW ⊕ seamInstance` into a single seam `PhaseConvergenceW` with
`Pre = work Post`, `Post = seam Post`, horizon `1 + tseam`, budget `0 + seam.ε = seam.ε`.  Then
`dotyAssembly_concrete'` / `dotyPhases'` re-cut the 21-instance family with the shifted seams, so
the `hTrig` field is GONE — replaced by the narrower `hSeedStep`.  The re-cut headline
`doty_time_headline_CONCRETE'` carries the narrowest set yet.

## Build

Single-file only:
  `lake env lean Ripple/PopulationProtocol/Majority/ExactMajority/Probability/SeedTrigWiring.lean`
APPEND-ONLY; imports landed surfaces; edits no existing file.
-/

import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.SeedRungs
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.ConcreteAssembly
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.AssemblyBridges
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.AssemblyWiring

namespace ExactMajority
namespace SeedTrigWiring

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators NNReal
open ConditionalPhaseProgress SeamEpidemics TimedChainRungs

variable {L K : ℕ}

attribute [local instance] Classical.propDecidable

/-! ## Part A — the world-bridge: `advTriggered (p+1)` IS the SeedRungs seed target. -/

/-- **`advTriggered (p+1) c ↔ c ∈ SeedRungs.seedTarget p`.**  Both unfold to
`1 ≤ Multiset.countP (p+1 ≤ phase) c`: `advTriggered` via `decide (p+1 ≤ phase)`, `seedTarget`
via `geCount (p+1) = countP (geP (p+1))`, and the two `countP` predicates agree pointwise.  This
makes the SeamEpidemics advance trigger and the SeedRungs counter-`0` seed the SAME set. -/
theorem advTriggered_iff_seedTarget (p : ℕ) (c : Config (AgentState L K)) :
    SeamEpidemics.advTriggered (L := L) (K := K) (p + 1) c ↔
      c ∈ SeedRungs.seedTarget (L := L) (K := K) p := by
  show 1 ≤ Multiset.countP _ c ↔ 1 ≤ SeamEpidemics.geCount (L := L) (K := K) (p + 1) c
  unfold SeamEpidemics.geCount
  have hcongr : Multiset.countP (fun a => decide (p + 1 ≤ a.phase.val)) c
      = Multiset.countP (fun a => SeamEpidemics.geP (L := L) (K := K) (p + 1) a) c := by
    apply Multiset.countP_congr rfl
    intro a _
    simp only [SeamEpidemics.geP, decide_eq_true_eq]
  rw [hcongr]

/-- `advTriggered (p+1)` from the SeedRungs target membership (one direction, packaged). -/
theorem advTriggered_of_seedTarget {p : ℕ} {c : Config (AgentState L K)}
    (h : c ∈ SeedRungs.seedTarget (L := L) (K := K) p) :
    SeamEpidemics.advTriggered (L := L) (K := K) (p + 1) c :=
  (advTriggered_iff_seedTarget p c).mpr h

/-! ## Part B — the generic seed-step `PhaseConvergenceW` combinator.

`seedStepW p n Pre hPreToGe hadvAS` is a ONE-step, failure-`0` instance whose `Post` is the seam
`Pre` shape `allPhaseGe p n ∧ advTriggered (p+1)`.  Its `convergence` splits `{¬Post}` into the
`allPhaseGe`-loss part (mass `0` by `≥`-window closure) and the `advTriggered`-miss part (mass `0`
by the seed event `hadvAS`). -/

/-- The seam-`Pre`-shaped target of the seed step: the `≥`-window AND the advance trigger. -/
def seamSeedPost (p n : ℕ) (c : Config (AgentState L K)) : Prop :=
  SeamEpidemics.allPhaseGe (L := L) (K := K) p n c ∧
    SeamEpidemics.advTriggered (L := L) (K := K) (p + 1) c

/-- The `≥`-window `allPhaseGe p n` has `K^1` no-loss mass (`{¬ allPhaseGe p n}` has mass `0`
in one step from an `allPhaseGe p n` state), lifted from `allPhaseGe_absorbing`. -/
theorem allPhaseGe_kernel_one_compl_zero (p n : ℕ) (c : Config (AgentState L K))
    (hc : SeamEpidemics.allPhaseGe (L := L) (K := K) p n c) :
    ((NonuniformMajority L K).transitionKernel ^ 1) c
        {c' | ¬ SeamEpidemics.allPhaseGe (L := L) (K := K) p n c'} = 0 :=
  Protocol.transitionKernel_pow_not_pred_eq_zero_of_stepDistOrSelf_support_preserved
    (NonuniformMajority L K)
    (fun c' => SeamEpidemics.allPhaseGe (L := L) (K := K) p n c')
    (fun a b ha hb => SeamEpidemics.allPhaseGe_absorbing p n a b ha hb) c hc 1

/-- **The generic seed-step instance.**  `Pre` is the (carried) drained work-window predicate;
`Post` is the seam `Pre` shape; `t = 1`; `ε = 0`.  The two inputs are the `≥`-window read
(`hPreToGe`) and the one-step a.s. seed event (`hadvAS`). -/
noncomputable def seedStepW (p n : ℕ) (Pre : Config (AgentState L K) → Prop)
    (hPreToGe : ∀ c, Pre c → SeamEpidemics.allPhaseGe (L := L) (K := K) p n c)
    (hadvAS : ∀ c, Pre c →
      ((NonuniformMajority L K).transitionKernel ^ 1) c
          {c' | ¬ SeamEpidemics.advTriggered (L := L) (K := K) (p + 1) c'} = 0) :
    PhaseConvergenceW (NonuniformMajority L K).transitionKernel where
  Pre := Pre
  Post := seamSeedPost (L := L) (K := K) p n
  t := 1
  ε := 0
  convergence := by
    intro c hPre
    have hge : SeamEpidemics.allPhaseGe (L := L) (K := K) p n c := hPreToGe c hPre
    -- {¬Post} ⊆ {¬allPhaseGe p n} ∪ {¬advTriggered (p+1)}.
    have hcover : {c' : Config (AgentState L K) | ¬ seamSeedPost (L := L) (K := K) p n c'}
        ⊆ {c' | ¬ SeamEpidemics.allPhaseGe (L := L) (K := K) p n c'}
          ∪ {c' | ¬ SeamEpidemics.advTriggered (L := L) (K := K) (p + 1) c'} := by
      intro c' hc'
      simp only [seamSeedPost, Set.mem_setOf_eq, Set.mem_union, not_and_or] at hc' ⊢
      exact hc'
    calc ((NonuniformMajority L K).transitionKernel ^ 1) c
            {c' | ¬ seamSeedPost (L := L) (K := K) p n c'}
        ≤ ((NonuniformMajority L K).transitionKernel ^ 1) c
            ({c' | ¬ SeamEpidemics.allPhaseGe (L := L) (K := K) p n c'}
              ∪ {c' | ¬ SeamEpidemics.advTriggered (L := L) (K := K) (p + 1) c'}) :=
          measure_mono hcover
      _ ≤ ((NonuniformMajority L K).transitionKernel ^ 1) c
            {c' | ¬ SeamEpidemics.allPhaseGe (L := L) (K := K) p n c'}
          + ((NonuniformMajority L K).transitionKernel ^ 1) c
            {c' | ¬ SeamEpidemics.advTriggered (L := L) (K := K) (p + 1) c'} :=
          measure_union_le _ _
      _ = 0 := by
          rw [allPhaseGe_kernel_one_compl_zero p n c hge, hadvAS c hPre, add_zero]
      _ ≤ ((0 : ℝ≥0) : ℝ≥0∞) := by simp

@[simp] theorem seedStepW_t (p n : ℕ) (Pre : Config (AgentState L K) → Prop)
    (hPreToGe hadvAS) : (seedStepW (L := L) (K := K) p n Pre hPreToGe hadvAS).t = 1 := rfl

@[simp] theorem seedStepW_eps (p n : ℕ) (Pre : Config (AgentState L K) → Prop)
    (hPreToGe hadvAS) : (seedStepW (L := L) (K := K) p n Pre hPreToGe hadvAS).ε = 0 := rfl

@[simp] theorem seedStepW_Pre (p n : ℕ) (Pre : Config (AgentState L K) → Prop)
    (hPreToGe hadvAS) (c : Config (AgentState L K)) :
    (seedStepW (L := L) (K := K) p n Pre hPreToGe hadvAS).Pre c = Pre c := rfl

@[simp] theorem seedStepW_Post (p n : ℕ) (Pre : Config (AgentState L K) → Prop)
    (hPreToGe hadvAS) (c : Config (AgentState L K)) :
    (seedStepW (L := L) (K := K) p n Pre hPreToGe hadvAS).Post c
      = seamSeedPost (L := L) (K := K) p n c := rfl

/-! ## Part C — the concrete seed step for the COUNTER-TIMED (all-clock) world.

For the timed track (`AllClockGEpCard p n` + `clockCounterSumAt p = 0` + un-seeded
`geCount (p+1) = 0`), the seed fires a.s. for FREE by
`SeedRungs.drained_kernel_seedTarget_compl_zero`.  This is the route-(a) seed step where the
advance is `O(1)`-deterministic. -/

/-- The drained all-clock un-seeded `Pre` predicate (the EXACT output of the counter-drain rung). -/
def drainedTimedPre (p n : ℕ) (c : Config (AgentState L K)) : Prop :=
  AllClockGEpCard (L := L) (K := K) p n c ∧
    clockCounterSumAt (L := L) (K := K) p c = 0 ∧
    SeamEpidemics.geCount (L := L) (K := K) (p + 1) c = 0

/-- **The counter-timed seed step (free seed, `ε = 0`).**  From the drained all-clock un-seeded
state the seed fires a.s. (`drained_kernel_seedTarget_compl_zero`, lifted through
`advTriggered_iff_seedTarget`).  The `≥`-window read is `AllClockGEpCard p n ⟹ allPhaseGe p n`
(`TimedChainRungs.allClockGEpCard_imp_allPhaseGe`). -/
noncomputable def seedStepW_timed (p : ℕ)
    (hp : p ∈ ({0, 1, 5, 6, 7, 8} : Finset ℕ)) (n : ℕ) (hn : 2 ≤ n) :
    PhaseConvergenceW (NonuniformMajority L K).transitionKernel :=
  seedStepW (L := L) (K := K) p n (drainedTimedPre (L := L) (K := K) p n)
    (fun c hPre => TimedChainRungs.allPhaseGe_of_allClockGEpCard (L := L) (K := K) hPre.1)
    (fun c hPre => by
      -- the seed event a.s. (counter-0 advance), in the advTriggered set via the world-bridge.
      have hzero := SeedRungs.drained_kernel_seedTarget_compl_zero (L := L) (K := K) p hp n hn c
        hPre.1 hPre.2.1 hPre.2.2
      -- {¬ advTriggered (p+1)} = (seedTarget p)ᶜ as sets.
      have hset : {c' : Config (AgentState L K) |
            ¬ SeamEpidemics.advTriggered (L := L) (K := K) (p + 1) c'}
          = (SeedRungs.seedTarget (L := L) (K := K) p)ᶜ := by
        ext c'
        simp only [Set.mem_setOf_eq, Set.mem_compl_iff]
        rw [advTriggered_iff_seedTarget p c']
      rw [hset, pow_one]
      exact hzero)

/-! ## Part D — the shifted seam: `seedStepW ⊕ seamEpidemicExactW` as one `PhaseConvergenceW`.

`seamWithSeed p n tseam …` composes the seed step (`t = 1`, `ε = 0`) with the EXACT seam epidemic
`SeamNoOvershoot.seamEpidemicExactW p n tseam …` (`t = tseam`, `ε = εepidemic + εovershoot`) into a
single seam instance whose `Pre` is the (drained) work-window predicate and whose `Post` is the
seam epidemic's `Post` (`allPhaseGe (p+1) n ∧ NoOvershoot p`).  Horizon `1 + tseam`, budget
`0 + (εepidemic+εovershoot)`.  The `h_chain` glue is DEFINITIONAL: the seed step's `Post`
(`seamSeedPost p n`) IS `seamEpidemicExactW`'s `Pre` (`allPhaseGe p n ∧ advTriggered (p+1)`).

The seam epidemic is built directly from `seamEpidemicExactW` (NOT the sealed
`ConcreteAssembly.seamInstance`), so its `Pre`/`Post` reduce definitionally — exactly the same
instance `ConcreteAssembly.seamInstance asm k` IS (by its own definition), now with the seed step
prepended. -/

/-- **The shifted seam instance** `seedStepW ⊕ seamEpidemicExactW`.  `Pre` is the carried drained
work-window predicate `workPre` (supplied with the `≥`-window read `hPreToGe` and the one-step
seed event `hadvAS`); `Post` is the seam epidemic's `Post`; horizon `1 + tseam`; budget
`εepidemic + εovershoot`. -/
noncomputable def seamWithSeed (p n tseam : ℕ) (εepidemic εovershoot : ℝ≥0)
    (hDrift : ∀ c : Config (AgentState L K),
        (SeamEpidemics.allPhaseGe (L := L) (K := K) p n c ∧
          SeamEpidemics.advTriggered (L := L) (K := K) (p + 1) c) →
        ((NonuniformMajority L K).transitionKernel ^ tseam) c
            {c' | ¬ SeamEpidemics.allPhaseGe (L := L) (K := K) (p + 1) n c'}
          ≤ (εepidemic : ℝ≥0∞))
    (hNoOvershoot : ∀ c : Config (AgentState L K),
        (SeamEpidemics.allPhaseGe (L := L) (K := K) p n c ∧
          SeamEpidemics.advTriggered (L := L) (K := K) (p + 1) c) →
        ((NonuniformMajority L K).transitionKernel ^ tseam) c
            {c' | ¬ SeamNoOvershoot.NoOvershoot (L := L) (K := K) p c'}
          ≤ (εovershoot : ℝ≥0∞))
    (workPre : Config (AgentState L K) → Prop)
    (hPreToGe : ∀ c, workPre c → SeamEpidemics.allPhaseGe (L := L) (K := K) p n c)
    (hadvAS : ∀ c, workPre c →
      ((NonuniformMajority L K).transitionKernel ^ 1) c
          {c' | ¬ SeamEpidemics.advTriggered (L := L) (K := K) (p + 1) c'} = 0) :
    PhaseConvergenceW (NonuniformMajority L K).transitionKernel where
  Pre := workPre
  Post := (SeamNoOvershoot.seamEpidemicExactW (L := L) (K := K) p n tseam
            εepidemic εovershoot hDrift hNoOvershoot).Post
  t := 1 + tseam
  ε := 0 + (εepidemic + εovershoot)
  convergence := by
    intro c hPre
    set seed := seedStepW (L := L) (K := K) p n workPre hPreToGe hadvAS with hseed
    set seam := SeamNoOvershoot.seamEpidemicExactW (L := L) (K := K) p n tseam
            εepidemic εovershoot hDrift hNoOvershoot with hseam
    have hcompose := composeW_two_phases (K := (NonuniformMajority L K).transitionKernel)
      seed seam
      (fun x hx => by
        -- seed.Post x = seamSeedPost p n x = seam.Pre x (both `allPhaseGe p n ∧ advTriggered`).
        change seamSeedPost (L := L) (K := K) p n x at hx
        exact hx)
      c hPre
    -- seed.t = 1, seam.t = tseam; seed.ε = 0, seam.ε = εepidemic + εovershoot.
    have hts : seed.t + seam.t = 1 + tseam := rfl
    have hes : (seed.ε : ℝ≥0∞) + (seam.ε : ℝ≥0∞) = ((0 + (εepidemic + εovershoot) : ℝ≥0) : ℝ≥0∞) := by
      have h1 : seed.ε = 0 := rfl
      have h2 : seam.ε = εepidemic + εovershoot := rfl
      rw [h1, h2]; push_cast; ring
    rw [hts] at hcompose
    calc ((NonuniformMajority L K).transitionKernel ^ (1 + tseam)) c {y | ¬ seam.Post y}
        ≤ (seed.ε : ℝ≥0∞) + (seam.ε : ℝ≥0∞) := hcompose
      _ = ((0 + (εepidemic + εovershoot) : ℝ≥0) : ℝ≥0∞) := hes

@[simp] theorem seamWithSeed_Pre (p n tseam : ℕ) (εepidemic εovershoot : ℝ≥0)
    (hDrift hNoOvershoot workPre hPreToGe hadvAS) (c : Config (AgentState L K)) :
    (seamWithSeed (L := L) (K := K) p n tseam εepidemic εovershoot
      hDrift hNoOvershoot workPre hPreToGe hadvAS).Pre c = workPre c := rfl

@[simp] theorem seamWithSeed_Post (p n tseam : ℕ) (εepidemic εovershoot : ℝ≥0)
    (hDrift hNoOvershoot workPre hPreToGe hadvAS) (c : Config (AgentState L K)) :
    (seamWithSeed (L := L) (K := K) p n tseam εepidemic εovershoot
      hDrift hNoOvershoot workPre hPreToGe hadvAS).Post c
      = (SeamEpidemics.allPhaseGe (L := L) (K := K) (p + 1) n c ∧
          SeamNoOvershoot.NoOvershoot (L := L) (K := K) p c) := rfl

@[simp] theorem seamWithSeed_t (p n tseam : ℕ) (εepidemic εovershoot : ℝ≥0)
    (hDrift hNoOvershoot workPre hPreToGe hadvAS) :
    (seamWithSeed (L := L) (K := K) p n tseam εepidemic εovershoot
      hDrift hNoOvershoot workPre hPreToGe hadvAS).t = 1 + tseam := rfl

@[simp] theorem seamWithSeed_eps (p n tseam : ℕ) (εepidemic εovershoot : ℝ≥0)
    (hDrift hNoOvershoot workPre hPreToGe hadvAS) :
    (seamWithSeed (L := L) (K := K) p n tseam εepidemic εovershoot
      hDrift hNoOvershoot workPre hPreToGe hadvAS).ε = 0 + (εepidemic + εovershoot) := rfl

end SeedTrigWiring
end ExactMajority
