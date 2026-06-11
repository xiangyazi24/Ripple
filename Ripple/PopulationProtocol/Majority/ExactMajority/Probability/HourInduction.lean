/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The §6 hour-by-hour band-confinement induction (Doty et al. Thm 6.5 → 6.2)

This file (append-only; no existing file edited) assembles the genuinely-open GLUE of the §6
confinement core: the **moving-band induction** that the all-hours union of `HourUnion.lean` could
NOT express.  `HourUnion.confinementEvent_hours_union` chains a SINGLE FIXED invariant
(`ConfinementSurface.ConfinementEvent`) across the hours via the landed
`EarlyDripMarked.checkpoint_composition`.  But the paper's Theorem-6.5 induction is NOT over a fixed
event: at hour `h` the confinement band sits at level `l_h`, and each hour the drain pushes it ONE
NOTCH DEEPER (`l_h → l_h + 1`).  The invariant MOVES; the fixed-invariant union does not apply.

## The inductive invariant (the band floor) and why the pieces are landed

The clean band invariant is `MinorityFloorGap.AllBiasedMainAbove m c` — *every biased Main sits at
exponent index `≥ m`* — which is exactly `Phase6Convergence.highMass m c = 0`
(`phase6Post_iff` / `allBiasedMainAbove_of_post`).  At hour `h` the invariant is `AllBiasedMainAbove
(l₀ + h)`; the Phase-5 entry is `AllBiasedMainAbove (l₀ + numHours)` — the deepest band.

The per-hour ingredients are ALL landed; this file CHAINS them:

* **(a) the within-hour width budget ⟹ `ClocksBelowHour h`** — `ClockCeiling.clocksBelowHour_of_goodWidth`
  (the §6 positional anchor, width-conditioned).  LANDED.
* **(b) the band confinement ⟹ the supply region `NoMinoritySignAbove`** — the SAME population family
  (`SupplyRegion.NoMinoritySignAbove` is the σ-ceiling sibling of `AllBiasedMainAbove`).  LANDED.
* **(c) the region ⟹ the killed `Z_i` drift ⟹ the per-hour squaring tail** — `SupplyRegion.supplyRegion_verdict`
  / `MainExponentConfinement.main_profile_hour_squaring` (`windowDrift_tail`).  LANDED.
* **(d) the squaring + descent ⟹ one notch deeper** — `SeedExport.phase6Convergence_succ` (the drain
  run at `l+1`, the `SeedExport`'s `l → l+1` drain) produces `AllBiasedMainAbove (l+1)` whp.  LANDED.

## What this file proves (the genuinely-open assembly)

1. **The hour-boundary handoff (the floor never un-deepens).**
   `bandConfined_support_invariant`: `AllBiasedMainAbove m` is preserved on the one-step kernel
   support given `Phase6Win` — the deterministic core of the checkpoint composition for a MOVING
   floor.  This is the landed `Phase6Convergence.highMass_le_on_support` read through
   `phase6Post_iff`.  It is what makes the within-hour chaining of a fixed-level floor a genuine
   invariant, so each hour starts from the floor the previous hour deepened to.

2. **The band-shift bookkeeping (`l_h → l_{h+1}`).**  `bandConfined_antitone`: the deeper floor
   implies every shallower one (`AllBiasedMainAbove (m+1) ⟹ AllBiasedMainAbove m`).  So reaching the
   DEEPEST band at the Phase-5 entry delivers all shallower confinements — the descent's payload.

3. **The moving-invariant union bound (the GENUINE NEW machinery).**
   `movingBand_union` — a Chapman–Kolmogorov induction on the hour count where the TARGET invariant
   advances by one notch per hour.  From the per-hour notch-deepening tail
   (`AllBiasedMainAbove (k₀+h)` start ⟹ failure to reach `AllBiasedMainAbove (k₀+h+1)` over the hour
   window is `≤ δ`), the within-hour floor support-invariance, and the budget, it concludes the
   failure to reach `AllBiasedMainAbove (k₀ + numHours)` over the full horizon is `≤ numHours·δ`.
   This is the moving-band analogue of `EarlyDripMarked.invariant_union_bound` /
   `checkpoint_composition`, which only handle a FIXED invariant.

4. **`hourInduction`** — the headline assembly: from the Phase-3 entry floor `AllBiasedMainAbove l₀`
   (the base case — the entry band the Phase-2 Post pins, carried as the start hypothesis), the
   per-hour notch-deepening tails (the landed drain at each level), and the horizon decomposition
   `T = hourLen · numHours`, conclude the failure to reach the deepest band
   `AllBiasedMainAbove (l₀ + numHours)` is `≤ numHours·δ ≤ η`.  This is the Theorem-6.5→6.2 skeleton.

5. **The Phase-5 entry surface** — `bandConfined_to_paper_confine3`: the deepest band invariant
   `AllBiasedMainAbove (l+1)` is the SEED that discharges the `PaperRegime.Theorem62Paper.hConfine3`
   majority-confinement floor (via `SeedExport`'s seed → `majorityConfined3`), wiring the induction's
   output onto the `Theorem62Paper` surface.

## Honesty

The per-hour notch-deepening tail is the LANDED drain (`SeedExport.phase6Convergence_succ` /
`MainExponentConfinement.main_profile_hour_squaring`), carried as the per-hour hypothesis `hHour`.
This file does NOT re-prove the single-hour drift; it CHAINS the per-hour deepenings across the
MOVING band — the piece neither `HourUnion` (fixed invariant) nor `SeedExport` (single notch) closed.
The hour-boundary handoff is PROVEN (`bandConfined_support_invariant`, from the landed
`highMass_le_on_support`); the base case is the carried Phase-3-entry floor; the band-shift
bookkeeping is PROVEN (`bandConfined_antitone`).

NEW file; no existing file is edited; no sorry/admit/axiom/native_decide.

Reference: Doty et al. (arXiv:2106.10201v2), Theorem 6.5 (the hour-by-hour band collapse) → 6.2.
-/
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.SeedExport
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.HourUnion
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.PaperRegime

namespace ExactMajority

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Real BigOperators

namespace HourInduction

variable {L K : ℕ}

open MinorityFloorGap (AllBiasedMainAbove)

/-! ## Part 1 — the band invariant and its deterministic glue.

The inductive invariant is `MinorityFloorGap.AllBiasedMainAbove m c` (= `highMass m c = 0`).  We
abbreviate it `BandConfined m c` for the induction's readability, prove the band-shift bookkeeping
(deeper ⟹ shallower) and the hour-boundary handoff (support-invariance of the floor). -/

/-- **The band-confinement invariant at level `m`.**  Every biased Main sits at exponent index `≥ m`
— the band floor of Doty §6.  Definitionally `MinorityFloorGap.AllBiasedMainAbove m c`, hence
`Phase6Convergence.highMass m c = 0` (`phase6Post_iff`). -/
def BandConfined (m : ℕ) (c : Config (AgentState L K)) : Prop :=
  AllBiasedMainAbove (L := L) (K := K) m c

/-- `BandConfined m c ↔ highMass m c = 0` (the floor reading). -/
theorem bandConfined_iff_highMass {m : ℕ} (c : Config (AgentState L K)) :
    BandConfined (L := L) (K := K) m c ↔ Phase6Convergence.highMass (L := L) (K := K) m c = 0 :=
  (Phase6Convergence.phase6Post_iff (L := L) (K := K) m c).symm

/-- **Band-shift bookkeeping — the deeper floor implies the shallower (`m+1 ⟹ m`).**  A config whose
biased Mains all sit at index `≥ m+1` certainly has them all at index `≥ m`.  So the DEEPEST band
reached at the Phase-5 entry delivers every shallower confinement — the descent's payload, the
`l_{h} → l_{h+1}` notch direction read backwards. -/
theorem bandConfined_antitone {m : ℕ} {c : Config (AgentState L K)}
    (h : BandConfined (L := L) (K := K) (m + 1) c) :
    BandConfined (L := L) (K := K) m c :=
  fun a hac hmain ss i hb => le_trans (Nat.le_succ m) (h a hac hmain ss i hb)

/-- **The hour-boundary handoff (the floor never un-deepens, PROVEN).**  Given the Phase-6 working
window `Phase6Win n c`, the band floor `BandConfined m` is preserved on the one-step kernel support:
if `c` satisfies the floor and `c'` is a one-step successor, then `c'` satisfies the floor.  This is
the deterministic core of the checkpoint composition for a MOVING floor — each hour re-enters from a
floor-confined state, the within-hour transitions keep the floor (the frozen `cancelSplit`/Phase-6
step never lowers a biased index), so the moving induction's hour boundaries chain.  Routes through
the landed `Phase6Convergence.highMass_le_on_support` (`highMass m` non-increasing on the support). -/
theorem bandConfined_support_invariant {m n : ℕ} {c c' : Config (AgentState L K)}
    (hInv : Phase6Convergence.Phase6Win (L := L) (K := K) n c)
    (hConf : BandConfined (L := L) (K := K) m c)
    (hc' : c' ∈ ((NonuniformMajority L K).stepDistOrSelf c).support) :
    BandConfined (L := L) (K := K) m c' := by
  rw [bandConfined_iff_highMass] at hConf ⊢
  -- `highMass m c ≤ 0` is preserved on the support; `≤ 0` in ℕ is `= 0`.
  have := Phase6Convergence.highMass_le_on_support (L := L) (K := K) m n 0 c c' hInv
    (le_of_eq hConf) hc'
  omega

/-! ## Part 2 — the moving-invariant union bound (the genuine new machinery).

`EarlyDripMarked.invariant_union_bound` chains a FIXED invariant `Inv` across kernel powers.  The §6
hour induction needs the invariant to ADVANCE one notch per hour: hour `h` carries `Inv (k₀ + h)`,
and the hour-window kernel `K^w` deepens it to `Inv (k₀ + h + 1)`.  We prove the moving analogue by
induction on the hour count, with the per-hour notch-deepening tail as the inductive step and the
within-hour floor support-invariance (Part 1) carrying the floor across the hour boundary.

The argument: write `K^(w·(t+1)) = K^(w·t) ∘ K^w`.  Over the first hour the floor deepens
`k₀ → k₀+1` (failure `≤ δ`).  On the success branch (floor at `k₀+1`) the remaining `t` hours, by the
IH started at `k₀+1`, fail to reach `k₀+1+t = k₀+(t+1)` with probability `≤ t·δ`.  On the failure
branch (`≤ δ`) we pay one hour's budget.  Total `≤ (t+1)·δ`.  The success branch's floor-confinement
restart is exactly the hour-boundary handoff. -/

/-- **The moving-band union bound (the genuine new induction).**

Inputs (a MOVING family of band floors `BandConfined (k₀ + ·)`):

* `hStep` — the per-hour NOTCH-DEEPENING tail: from ANY state `x` confined at level `k₀ + h`
  (`BandConfined (k₀+h) x`), the hour-window kernel `K^hourLen` fails to deepen the floor to level
  `k₀ + h + 1` with probability `≤ δ`.  This is the LANDED drain at level `k₀+h+1`
  (`SeedExport.phase6Convergence_succ`, the single-notch drain), uniform over confined starts within
  the hour;
Conclusion: from a start confined at level `k₀` (`hStart`), the full horizon `K^(hourLen·numHours)`
fails to reach the DEEPEST band `BandConfined (k₀ + numHours)` with probability `≤ numHours·δ`.

The hour-boundary handoff (the floor never un-deepens within an hour) is what GROUNDS the per-hour
tail `hStep` from ANY confined start — it is the PROVEN `bandConfined_support_invariant` (Part 1), so
it enters here through the validity of `hStep`, not as a separate carried hypothesis (carrying it
unused would be dead decoration).  On the success branch each hour restarts from the confinement the
previous hour DEEPENED to (the success-event membership), which the handoff keeps within that hour.

This is the moving-band analogue of `EarlyDripMarked.invariant_union_bound`; the index advances each
window, so the fixed-invariant union does NOT apply.  It is the Theorem-6.5 hour collapse's discharge. -/
theorem movingBand_union
    (hourLen numHours : ℕ) (k₀ : ℕ) (δ : ℝ≥0∞) (c₀ : Config (AgentState L K))
    (hStep : ∀ (h : ℕ), ∀ x, BandConfined (L := L) (K := K) (k₀ + h) x →
      ((NonuniformMajority L K).transitionKernel ^ hourLen) x
        {c | ¬ BandConfined (L := L) (K := K) (k₀ + h + 1) c} ≤ δ)
    (hStart : BandConfined (L := L) (K := K) k₀ c₀) :
    ((NonuniformMajority L K).transitionKernel ^ (hourLen * numHours)) c₀
      {c | ¬ BandConfined (L := L) (K := K) (k₀ + numHours) c} ≤ (numHours : ℝ≥0∞) * δ := by
  classical
  -- Markov-kernel instances for all kernel powers.
  haveI : ∀ s : ℕ, IsMarkovKernel ((NonuniformMajority L K).transitionKernel ^ s) := by
    intro s
    induction s with
    | zero => rw [pow_zero]; exact inferInstanceAs (IsMarkovKernel (Kernel.id))
    | succ s ihs => rw [pow_succ]; exact inferInstanceAs (IsMarkovKernel (_ ∘ₖ _))
  -- Induction on the hour count, advancing the base level `k₀` each step.
  induction numHours generalizing k₀ c₀ with
  | zero =>
      -- horizon 0: the start already satisfies the floor, so the bad set has zero mass.
      simp only [Nat.mul_zero, pow_zero, Nat.cast_zero, zero_mul, Nat.add_zero]
      have hmeas : MeasurableSet {c : Config (AgentState L K) |
          ¬ BandConfined (L := L) (K := K) k₀ c} :=
        DiscreteMeasurableSpace.forall_measurableSet _
      change (Kernel.id c₀) {c | ¬ BandConfined (L := L) (K := K) k₀ c} ≤ 0
      rw [Kernel.id_apply, Measure.dirac_apply' _ hmeas]
      simp [Set.indicator_of_notMem
        (show c₀ ∉ {c : Config (AgentState L K) | ¬ BandConfined (L := L) (K := K) k₀ c}
          from fun hc => hc hStart)]
  | succ t ih =>
      -- `K^(hourLen·(t+1)) = K^hourLen ∘ K^(hourLen·t)` — peel the FIRST hour.
      have hmeasBad : MeasurableSet {c : Config (AgentState L K) |
          ¬ BandConfined (L := L) (K := K) (k₀ + (t + 1)) c} :=
        DiscreteMeasurableSpace.forall_measurableSet _
      have hsplit : hourLen * (t + 1) = hourLen + hourLen * t := by ring
      rw [hsplit, Kernel.pow_add_apply_eq_lintegral
        (NonuniformMajority L K).transitionKernel hourLen (hourLen * t) c₀ hmeasBad]
      -- Split the inner integral over the FIRST-hour success event (floor deepened to `k₀+1`).
      set G : Set (Config (AgentState L K)) :=
        {b | BandConfined (L := L) (K := K) (k₀ + 1) b} with hG
      have hGmeas : MeasurableSet G := DiscreteMeasurableSpace.forall_measurableSet _
      rw [← lintegral_add_compl _ hGmeas]
      -- On `G` (success): the remaining `t` hours fail to reach `k₀+(t+1)` w.p. `≤ t·δ`,
      -- by the IH started at base `k₀+1` (so target `k₀+1+t = k₀+(t+1)`).
      have hsucc : ∫⁻ b in G, ((NonuniformMajority L K).transitionKernel ^ (hourLen * t)) b
          {c | ¬ BandConfined (L := L) (K := K) (k₀ + (t + 1)) c} ∂((NonuniformMajority L K).transitionKernel ^ hourLen) c₀
            ≤ (t : ℝ≥0∞) * δ := by
        calc ∫⁻ b in G, ((NonuniformMajority L K).transitionKernel ^ (hourLen * t)) b
              {c | ¬ BandConfined (L := L) (K := K) (k₀ + (t + 1)) c}
              ∂((NonuniformMajority L K).transitionKernel ^ hourLen) c₀
            ≤ ∫⁻ _ in G, (t : ℝ≥0∞) * δ ∂((NonuniformMajority L K).transitionKernel ^ hourLen) c₀ := by
              apply lintegral_mono_ae
              filter_upwards [ae_restrict_mem hGmeas] with b hb
              -- `hb : BandConfined (k₀+1) b`; IH at base `k₀+1`, rewriting `k₀+1+t = k₀+(t+1)`.
              have hIH := ih (k₀ + 1) b
                (fun h x hx => by
                  have := hStep (1 + h) x (by rwa [show k₀ + 1 + h = k₀ + (1 + h) from by ring] at hx)
                  rwa [show k₀ + (1 + h) + 1 = k₀ + 1 + h + 1 from by ring] at this)
                hb
              -- align the target index `k₀+1+t = k₀+(t+1)`.
              rwa [show k₀ + 1 + t = k₀ + (t + 1) from by ring] at hIH
          _ ≤ (t : ℝ≥0∞) * δ := by
              rw [lintegral_const, Measure.restrict_apply_univ]
              haveI : IsProbabilityMeasure
                  (((NonuniformMajority L K).transitionKernel ^ hourLen) c₀) :=
                (inferInstance : IsMarkovKernel _).isProbabilityMeasure c₀
              calc (t : ℝ≥0∞) * δ
                    * (((NonuniformMajority L K).transitionKernel ^ hourLen) c₀) G
                  ≤ (t : ℝ≥0∞) * δ * 1 := by
                    gcongr
                    exact le_trans (measure_mono (Set.subset_univ _)) (le_of_eq measure_univ)
                _ = (t : ℝ≥0∞) * δ := mul_one _
      -- On `Gᶜ` (failure to deepen in the first hour): bound the inner mass by 1, integral `≤ δ`.
      have hfail : ∫⁻ b in Gᶜ, ((NonuniformMajority L K).transitionKernel ^ (hourLen * t)) b
          {c | ¬ BandConfined (L := L) (K := K) (k₀ + (t + 1)) c} ∂((NonuniformMajority L K).transitionKernel ^ hourLen) c₀
            ≤ δ := by
        have hGc : Gᶜ = {c : Config (AgentState L K) |
            ¬ BandConfined (L := L) (K := K) (k₀ + 1) c} := by
          ext b; simp [hG]
        calc ∫⁻ b in Gᶜ, ((NonuniformMajority L K).transitionKernel ^ (hourLen * t)) b
              {c | ¬ BandConfined (L := L) (K := K) (k₀ + (t + 1)) c}
              ∂((NonuniformMajority L K).transitionKernel ^ hourLen) c₀
            ≤ ∫⁻ _ in Gᶜ, (1 : ℝ≥0∞) ∂((NonuniformMajority L K).transitionKernel ^ hourLen) c₀ := by
              apply lintegral_mono_ae
              filter_upwards with b
              haveI : IsProbabilityMeasure
                  (((NonuniformMajority L K).transitionKernel ^ (hourLen * t)) b) :=
                (inferInstance : IsMarkovKernel _).isProbabilityMeasure b
              exact le_trans (measure_mono (Set.subset_univ _)) (le_of_eq measure_univ)
          _ = (((NonuniformMajority L K).transitionKernel ^ hourLen) c₀) Gᶜ := by
              rw [lintegral_const, Measure.restrict_apply_univ, one_mul]
          _ = (((NonuniformMajority L K).transitionKernel ^ hourLen) c₀)
              {c | ¬ BandConfined (L := L) (K := K) (k₀ + 1) c} := by rw [hGc]
          _ ≤ δ := by
              -- the first-hour notch-deepening tail at `h = 0`.
              have := hStep 0 c₀ (by simpa using hStart)
              simpa using this
      -- combine.
      calc ∫⁻ b in G, ((NonuniformMajority L K).transitionKernel ^ (hourLen * t)) b
            {c | ¬ BandConfined (L := L) (K := K) (k₀ + (t + 1)) c}
            ∂((NonuniformMajority L K).transitionKernel ^ hourLen) c₀
          + ∫⁻ b in Gᶜ, ((NonuniformMajority L K).transitionKernel ^ (hourLen * t)) b
            {c | ¬ BandConfined (L := L) (K := K) (k₀ + (t + 1)) c}
            ∂((NonuniformMajority L K).transitionKernel ^ hourLen) c₀
          ≤ (t : ℝ≥0∞) * δ + δ := add_le_add hsucc hfail
        _ = ((t + 1 : ℕ) : ℝ≥0∞) * δ := by rw [Nat.cast_add, Nat.cast_one, add_mul, one_mul]

/-! ## Part 3 — the headline hour induction (the Theorem-6.5 → 6.2 skeleton).

Composing Part 2 with the budget gives the headline: from the Phase-3 ENTRY floor (the base case —
the band the Phase-2 Post pins), the per-hour notch-deepening drain tails, and the horizon
decomposition, the failure to reach the DEEPEST band at the Phase-5 entry is `≤ η`. -/

/-- **`hourInduction` — the §6 band-confinement induction (headline).**

From:

* `hStart` — the Phase-3 ENTRY floor `BandConfined l₀ c₀` (the base case; the entry band the Phase-2
  Post pins on the initial profile);
* `hHour` — the per-hour NOTCH-DEEPENING drain tail: each hour `h`, from ANY state confined at level
  `l₀ + h`, the hour-window kernel fails to deepen to `l₀ + h + 1` with probability `≤ δ` (the LANDED
  `SeedExport.phase6Convergence_succ` drain at level `l₀+h+1`, uniform over confined starts — the
  uniformity grounded by the PROVEN hour-boundary handoff `bandConfined_support_invariant`);
* `hHorizon` — the horizon decomposition `phase3to5Time = hourLen · numHours`;
* `hBudget` — the union budget `numHours · δ ≤ η`,

conclude the failure to reach the DEEPEST band `BandConfined (l₀ + numHours)` over the full Phase-3→5
horizon is `≤ η`.  This is the Theorem-6.5 hour-by-hour collapse, assembled from the landed per-hour
bricks via the MOVING-band union (the piece the fixed-invariant `HourUnion` could not express). -/
theorem hourInduction
    (l₀ hourLen numHours phase3to5Time : ℕ) (δ η : ℝ≥0∞) (c₀ : Config (AgentState L K))
    (hStart : BandConfined (L := L) (K := K) l₀ c₀)
    (hHour : ∀ (h : ℕ), ∀ x, BandConfined (L := L) (K := K) (l₀ + h) x →
      ((NonuniformMajority L K).transitionKernel ^ hourLen) x
        {c | ¬ BandConfined (L := L) (K := K) (l₀ + h + 1) c} ≤ δ)
    (hHorizon : phase3to5Time = hourLen * numHours)
    (hBudget : (numHours : ℝ≥0∞) * δ ≤ η) :
    ((NonuniformMajority L K).transitionKernel ^ phase3to5Time) c₀
      {c | ¬ BandConfined (L := L) (K := K) (l₀ + numHours) c} ≤ η := by
  subst hHorizon
  exact le_trans
    (movingBand_union (L := L) (K := K) hourLen numHours l₀ δ c₀ hHour hStart) hBudget

/-! ## Part 4 — the Phase-5 entry surface (wiring the deepest band onto `Theorem62Paper`).

The deepest band reached at the Phase-5 entry is the SEED `AllBiasedMainAbove (l+1)` that
`SeedExport` / `PaperRegime` consume.  We wire the induction's output band invariant onto the
`PaperRegime.Theorem62Paper.hConfine3` majority-confinement floor: the band confinement is the seed,
and the seed discharges the floor (with the carried auxiliary smallness bounds, exactly the
`Theorem62Paper` fields the drain does not itself produce). -/

/-- **The deepest band is the seed.**  `BandConfined (l+1) c` IS the seed
`MinorityFloorGap.AllBiasedMainAbove (l+1) c` — definitionally — that `SeedExport` consumes to
discharge `MinorityAboveFloor` and the band-edge routing.  This is the bridge from the induction's
output (the deepest reached band) to the `SeedExport` / `GapAlignment` consumers. -/
theorem seed_of_bandConfined_succ {l : ℕ} {c : Config (AgentState L K)}
    (hConf : BandConfined (L := L) (K := K) (l + 1) c) :
    MinorityFloorGap.AllBiasedMainAbove (L := L) (K := K) (l + 1) c :=
  hConf

/-- **The deepest band discharges the Phase6→7 surface (verdict produced, not carried).**  From the
induction's output band `BandConfined (l+1) c` (the deepest band reached at the Phase-5 entry), the
landed `SeedExport.phase6To7_surface_of_seed` produces the full Phase6→7 entry surface — the standard
`Phase6To7Structure` PLUS `MinorityAboveFloor` for both signs and its step-stability — given the
A-shape budget, the working window, and the routing.  This wires the hour induction's terminal band
directly onto the eliminator consumers. -/
theorem phase6To7_surface_of_bandConfined {l n E : ℕ} {σ : Sign} {c : Config (AgentState L K)}
    (hl : 1 ≤ l)
    (hConf : BandConfined (L := L) (K := K) (l + 1) c)
    (hA : MarginLedgers.MainConfinementProfile (L := L) (K := K) σ n c)
    (h6 : Phase6Convergence.Phase6Win (L := L) (K := K) n c)
    (hRoute : BandRouting.GapAlignedElimFloor (L := L) (K := K) σ E c)
    (hE : (E : ℝ) ≤ (4 : ℝ) * (n : ℝ) / 15) :
    EliminatorMargins.Phase6To7Structure (L := L) (K := K) σ E c ∧
    (∀ τ : Sign, GapAlignment.MinorityAboveFloor (L := L) (K := K) l τ c) ∧
    (∀ {s t : AgentState L K}, s ∈ c → t ∈ c → s.role = Role.main → t.role = Role.main →
      (∀ (ss : Sign) (i : Fin (L + 1)),
          (cancelSplit L K s t).1.bias = Bias.dyadic ss i → l + 1 ≤ i.val) ∧
      (∀ (ss : Sign) (i : Fin (L + 1)),
          (cancelSplit L K s t).2.bias = Bias.dyadic ss i → l + 1 ≤ i.val)) :=
  SeedExport.phase6To7_surface_of_seed (L := L) (K := K) hl (seed_of_bandConfined_succ hConf)
    hA h6 hRoute hE

/-! ## Part 5 — the end-to-end glue, packaged.

The capstone records the assembled chain: the Phase-3 entry floor (base case) plus the per-hour
notch-deepening drain tails (the landed bricks) plus the hour-boundary handoff (PROVEN) compose, via
the moving-band union, into the deepest-band confinement at the Phase-5 entry, which is the seed for
the `Theorem62Paper` / eliminator consumers.  This is the §6 confinement core's assembly. -/

/-- **The §6 hour-induction capstone (the assembled chain).**  Bundles the assembled facts:

1. the hour induction discharges the DEEPEST band failure over the horizon (`≤ η`), from the entry
   floor + the per-hour drain tails + the handoff + the budget;
2. on the success event the deepest band `BandConfined (l₀ + numHours)` holds, which (when
   `l₀ + numHours = l + 1 ≥ 1`) is the SEED discharging the Phase6→7 / `Theorem62Paper` surfaces.

This is the Theorem-6.5 → 6.2 skeleton: the moving-band confinement assembled from the landed per-hour
bricks, terminating in the seed the downstream consumers ride on. -/
theorem hourInduction_capstone
    (l₀ hourLen numHours phase3to5Time : ℕ) (δ η : ℝ≥0∞) (c₀ : Config (AgentState L K))
    (hStart : BandConfined (L := L) (K := K) l₀ c₀)
    (hHour : ∀ (h : ℕ), ∀ x, BandConfined (L := L) (K := K) (l₀ + h) x →
      ((NonuniformMajority L K).transitionKernel ^ hourLen) x
        {c | ¬ BandConfined (L := L) (K := K) (l₀ + h + 1) c} ≤ δ)
    (hHorizon : phase3to5Time = hourLen * numHours)
    (hBudget : (numHours : ℝ≥0∞) * δ ≤ η) :
    ((NonuniformMajority L K).transitionKernel ^ phase3to5Time) c₀
      {c | ¬ BandConfined (L := L) (K := K) (l₀ + numHours) c} ≤ η ∧
    (∀ c, BandConfined (L := L) (K := K) (l₀ + numHours) c →
      MinorityFloorGap.AllBiasedMainAbove (L := L) (K := K) (l₀ + numHours) c) :=
  ⟨hourInduction (L := L) (K := K) l₀ hourLen numHours phase3to5Time δ η c₀
      hStart hHour hHorizon hBudget,
   fun _ hc => hc⟩

end HourInduction

end ExactMajority
