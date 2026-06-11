/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Margin instantiation — WAVE 2 roster items #6 / #7 and the ClockZeroTail↔Wave1 splice
(`MarginInstantiation`)

Append-only deliverable for the ATOM CAMPAIGN ROSTER (WAVE 2).  This file edits NO existing
file: it (a) instantiates the two landed eliminator-margin SURFACES into the exact
`FinalAssemblyV2.WorkInputsHonest` field shapes `hPhase6Post7` / `hPhase7Post8`, leaving ONLY
the Theorem-6.2-flavored `MainConfinementProfile` confinement (the open C atom) and the landed
survival band as carried inputs; and (b) delivers the splice lemma that produces
`SeamQuickWins.DotyAtomsWave1Inputs.hOvershootTail`'s consumed shape from
`ClockZeroTail.seam_noOvershoot_tail_of_entry` — so the wave-1 produced-seam `hNoOvershoot` chain
is end-to-end from the seam-entry facts.

## #6 — `hPhase6Post7` from the single-level positional surface

The `WorkInputsHonest.hPhase6Post7` field shape is

  `∀ b, Phase7Convergence.Inv7Sum n b → EliminatorMargins.Phase6To7Structure σ E7 b`.

`PositionalCluster.phase6To7_surface_singleLevel` (`PositionalCluster:282`) is the landed
NARROWEST surface (single-level minority → ONE predecessor at the `2n/15` pigeonhole share, NO
boundary appeal).  Its remaining hypotheses, after this instantiation, split cleanly:

* `hA : MarginLedgers.MainConfinementProfile σ n b` — the A-shape confinement profile (Theorem 6.2
  entry facts), whose `majorityProfileMass ≥ 4n/15` budget is `MarginLedgers.majorityProfileMass_floor`.
  This is the open **C atom** (`Theorem62Paper`-flavored); it is the ONLY carried input — carried
  here per-config as `hConf`;
* `h6 : Phase6Convergence.Phase6Win n b` — the Phase-6 window Pre (carried as `hWin6`);
* the band-position facts `hgap` / `hConfined` (`MinorityConfinedGap1`) / `hSingle`
  (single-level collapse) / `hOcc` (the gap-1 occupancy at the pigeonhole share) — carried per-config
  as `hPos`;
* `hE7 : E7 ≤ 4n/15` — the honest budget scalar.

EVERYTHING ELSE is wired: the adapter consumes `Inv7Sum n b` (the field's hypothesis), feeds the
carried confinement + window + positional facts into `phase6To7_surface_singleLevel`, and produces
the field value.

## #7 — `hPhase7Post8` from the landed spend chain (mirror surface)

The `WorkInputsHonest.hPhase7Post8` field shape is

  `∀ b, Phase8Convergence.Phase8AllMain n b → EliminatorMargins.Phase7To8Structure σ E8 b`.

The Phase-7→8 analogue surface is the landed `SpendLedgerLift` chain:
`phase7SpendLedger_canonical` (the canonical spend `Entry ∸ elimAbove`, ALWAYS true) +
`survivalBand_…` (the genuinely-stochastic trajectory band, reduced to the per-step band closure of
`SurvivalAccounting.cancelSplit_elimAbove_survives_or_charged` and the per-pair ledgers of
`BandStepBookkeeping`) ⟹ `phase7_to_phase8_via_canonicalSpend` ⟹ `Phase7To8Structure`.

The entry margin = #6's output at the Phase-7 entry config (`hEntry7 : Phase6To7Structure σ E8 …`);
the surviving-eliminator band `hSurv b : SurvivalBandAbove σ E8 b` is the landed spend chain's
trajectory content; the honest constant is `E8 ≤ n/5` (the `14n/75` survival floor of
`SurvivalAccounting.survival_floor_honest`, recorded by `honest_survival_floor`).  Everything but the
carried survival band + the #6-entry margin is wired.

## The splice — ClockZeroTail ⟷ SeamQuickWins `hOvershootTail`

`SeamQuickWins.DotyAtomsWave1Inputs.hOvershootTail` (`SeamQuickWins:127`) is CONSUMED as a per-seam
input: it TAKES `DetSeamOvershootBridge (seamP k)` as an explicit argument plus the seam `Pre`
(`allPhaseGe (seamP k) n ∧ advTriggered (seamP k + 1)`), and produces the per-seam no-overshoot
bound `≤ εovershoot k`.

`ClockZeroTail.seam_noOvershoot_tail_of_entry` (`ClockZeroTail:178`) is exactly the producer that
TAKES the deterministic bridge `hdet` as an argument and delivers
`(K^tseam) c₀ {¬NoOvershoot p} ≤ tseam · e^{−40(L+1)}` from the seam-entry facts
(`NoOvershoot p c₀` + `SeamEntryFullCounter p c₀`) plus the structural guards + arithmetic.  The
splice (`hOvershootTail_of_entry`) derives, per config `c` satisfying the seam `Pre`, the entry facts
`hStartNoOver`/`hEntry`/`hcard` (supplied by the wave-1 work-Post / seed-step structure as per-config
hypotheses), threads them through `seam_noOvershoot_tail_of_entry`, and folds the budget fit — landing
EXACTLY the `hOvershootTail` shape.  **Splice verdict: the shapes match**; the only adaptation is the
`tseam · e^{−40(L+1)} ≤ εovershoot` budget step (the per-seam budget wrapper, supplied as `hε`).

NEW file; no existing file is edited; no sorry/admit/axiom/native_decide.
-/

import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.PositionalCluster
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.SpendLedgerLift
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.FinalAssemblyV2
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.ClockZeroTail

namespace ExactMajority

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Real BigOperators

namespace MarginInstantiation

variable {L K : ℕ}

/-! ## Part 1 — #6: the `hPhase6Post7` field from the single-level positional surface.

The carried per-config positional witness for the single-level surface
(`PositionalCluster.phase6To7_surface_singleLevel`): the gap structure, minority confinement,
single-level collapse, and the gap-1 occupancy at the pigeonhole share.  Everything EXCEPT the
Theorem-6.2 confinement profile (`hConf`, the open C atom) and the Phase-6 window (`hWin6`). -/

/-- **The single-level positional witness at a config** (the narrowed band datum).  Asserts the
EXISTENCE of a single live minority level `j₀` with gap-1 predecessor `p` (`p + 1 = j₀`), the minority
confinement, the single-level collapse onto `j₀`, and the gap-1 occupancy at `p`.  This is EXACTLY the
residual `phase6To7_surface_singleLevel` consumes beyond the confinement profile, the Phase-6 window,
and the budget scalar.  Phrased as a `Prop` existential over the band indices `j₀`/`p` (which depend
on `c`). -/
def SingleLevelWitness (σ : Sign) (E : ℕ) (c : Config (AgentState L K)) : Prop :=
  ∃ (j₀ p : Fin (L + 1)),
    p.val + 1 = j₀.val ∧
    BandLocalization.MinorityConfinedGap1 (L := L) (K := K) σ c ∧
    (∀ j : Fin (L + 1),
      1 ≤ (Phase7Convergence.minorityAt7 (L := L) (K := K) σ j).sum c.count → j.val = j₀.val) ∧
    E ≤ (Phase7Convergence.elimGap1 (L := L) (K := K) σ p).sum c.count

/-- **#6 — `hPhase6Post7` PRODUCED from the single-level surface.**  Delivers the exact
`FinalAssemblyV2.WorkInputsHonest.hPhase6Post7` field value

  `∀ b, Phase7Convergence.Inv7Sum n b → EliminatorMargins.Phase6To7Structure σ E7 b`

from the landed `PositionalCluster.phase6To7_surface_singleLevel`.  CARRIED inputs (per config):

* `hConf` — `MarginLedgers.MainConfinementProfile σ n b` (Theorem 6.2 A-shape confinement; the open
  **C atom**, `Theorem62Paper`-flavored; the global `4n/15` budget rides via
  `MarginLedgers.majorityProfileMass_floor`);
* `hWin6` — `Phase6Convergence.Phase6Win n b` (the Phase-6 window Pre);
* `hPos` — the `SingleLevelWitness` (band-position facts: gap / confinement / single-level / gap-1
  occupancy at the `2n/15` share).

WIRED: the `Inv7Sum n b` hypothesis is consumed (its `Phase7AllMain` structural core is the window
the positional facts live on), and the single-level surface is instantiated.  The honest budget
scalar `hE7 : E7 ≤ 4n/15` is the only arithmetic input. -/
theorem hPhase6Post7_singleLevel {n E7 : ℕ} {σ : Sign}
    (hE7 : (E7 : ℝ) ≤ (4 : ℝ) * (n : ℝ) / 15)
    (hConf : ∀ b : Config (AgentState L K),
      Phase7Convergence.Inv7Sum (L := L) (K := K) n b →
      MarginLedgers.MainConfinementProfile (L := L) (K := K) σ n b)
    (hWin6 : ∀ b : Config (AgentState L K),
      Phase7Convergence.Inv7Sum (L := L) (K := K) n b →
      Phase6Convergence.Phase6Win (L := L) (K := K) n b)
    (hPos : ∀ b : Config (AgentState L K),
      Phase7Convergence.Inv7Sum (L := L) (K := K) n b →
      SingleLevelWitness (L := L) (K := K) σ E7 b) :
    ∀ b : Config (AgentState L K),
      Phase7Convergence.Inv7Sum (L := L) (K := K) n b →
      EliminatorMargins.Phase6To7Structure (L := L) (K := K) σ E7 b := by
  intro b hInv
  obtain ⟨j₀, p, hgap, hConfined, hSingle, hOcc⟩ := hPos b hInv
  exact PositionalCluster.phase6To7_surface_singleLevel hgap (hConf b hInv) (hWin6 b hInv)
    hConfined hSingle hOcc hE7

/-! ## Part 2 — #7: the `hPhase7Post8` field from the landed spend chain (mirror surface).

The Phase-7→8 analogue of #6.  The landed `SpendLedgerLift` chain — canonical spend (always true) +
the genuinely-stochastic survival-band trajectory lift (per-pair ledgers from `SurvivalAccounting` /
`BandStepBookkeeping`, the margin-band step closure) — composes through
`SpendLedgerLift.phase7_to_phase8_via_canonicalSpend` into `Phase7To8Structure`.  The entry margin
is #6's output at the Phase-7 entry config; the survival band is the landed trajectory content; the
honest constant is `E8 ≤ n/5` (the `14n/75` survival floor). -/

/-- **#7 — `hPhase7Post8` PRODUCED from the landed spend chain.**  Delivers the exact
`FinalAssemblyV2.WorkInputsHonest.hPhase7Post8` field value

  `∀ b, Phase8Convergence.Phase8AllMain n b → EliminatorMargins.Phase7To8Structure σ E8 b`

via the mirror surface `SpendLedgerLift.phase7_to_phase8_via_canonicalSpend`.  CARRIED inputs (per
config):

* `hEntry7` — `EliminatorMargins.Phase6To7Structure σ E8 (entry7 b)` (**#6's output** at the Phase-7
  entry config `entry7 b`; the canonical-spend ledger's `hStart`);
* `h7win` — `Phase7Convergence.Phase7AllMain n b` (the Phase-7 all-Main structural window the spend
  ledger and survival band live on);
* `hSurv` — `BandLocalization.SurvivalBandAbove σ E8 b` (the **landed spend chain's** trajectory band:
  the surviving above-level eliminator supply, from `survivalBand_ae_along_trajectory` reduced to the
  per-pair ledgers);
* `hEntryDom` — the trivial entry-domination `elimAbove ≤ Entry` (survivors never exceed entry mass).

WIRED: the `Phase8AllMain n b` hypothesis is consumed; `phase7_to_phase8_via_canonicalSpend` supplies
the canonical-spend `Phase7SpendLedger` (always true) internally, and folds the survival band into
`Phase7To8Structure`.  The honest constant `hE8 : E8 ≤ n/5` is the only arithmetic input
(`14n/75 = 4n/15 − 2n/25` survival floor, `honest_survival_floor`). -/
theorem hPhase7Post8_of_survival {n E8 Entry : ℕ} {σ : Sign}
    (entry7 : Config (AgentState L K) → Config (AgentState L K))
    (hE8 : (E8 : ℝ) ≤ (1 : ℝ) * (n : ℝ) / 5)
    (hEntry7 : ∀ b : Config (AgentState L K),
      Phase8Convergence.Phase8AllMain (L := L) (K := K) n b →
      EliminatorMargins.Phase6To7Structure (L := L) (K := K) σ E8 (entry7 b))
    (h7win : ∀ b : Config (AgentState L K),
      Phase8Convergence.Phase8AllMain (L := L) (K := K) n b →
      Phase7Convergence.Phase7AllMain (L := L) (K := K) n b)
    (hSurv : ∀ b : Config (AgentState L K),
      Phase8Convergence.Phase8AllMain (L := L) (K := K) n b →
      BandLocalization.SurvivalBandAbove (L := L) (K := K) σ E8 b)
    (hEntryDom : ∀ b : Config (AgentState L K),
      Phase8Convergence.Phase8AllMain (L := L) (K := K) n b →
      ∀ i : Fin (L + 1),
        1 ≤ (Phase8Convergence.minorityAt (L := L) (K := K) σ i).sum b.count →
        (Phase8Convergence.elimAbove (L := L) (K := K) σ i).sum b.count ≤ Entry) :
    ∀ b : Config (AgentState L K),
      Phase8Convergence.Phase8AllMain (L := L) (K := K) n b →
      EliminatorMargins.Phase7To8Structure (L := L) (K := K) σ E8 b := by
  intro b hb8
  exact SpendLedgerLift.phase7_to_phase8_via_canonicalSpend (Entry := Entry)
    (hEntry7 b hb8) (h7win b hb8) (hSurv b hb8) (hEntryDom b hb8) hE8

/-! ## Part 3 — the splice: ClockZeroTail ⟷ SeamQuickWins `hOvershootTail`.

The wave-1 consumed input `SeamQuickWins.DotyAtomsWave1Inputs.hOvershootTail` TAKES the deterministic
overshoot bridge `DetSeamOvershootBridge (seamP k)` as an argument; `ClockZeroTail`'s
`seam_noOvershoot_tail_of_entry` is exactly the producer that takes the same bridge and delivers the
no-overshoot tail from the seam-entry facts.  We splice them at the per-seam level: from the seam-entry
facts (`hStartNoOver`/`hEntry`/`hcard` — supplied per config by the wave-1 work-Post / seed-step
structure), the structural guards, and the budget fit, we PRODUCE the `hOvershootTail` shape.

The shapes match exactly — the only adaptation is the per-seam budget step
`tseam · e^{−40(L+1)} ≤ εovershoot` (the budget wrapper). -/

/-- **The splice lemma (per seam).**  Produces EXACTLY the
`SeamQuickWins.DotyAtomsWave1Inputs.hOvershootTail` shape — `∀ (bridge), ∀ c, (seam Pre) → bound` —
for ONE seam with phase `p`, horizon `tseam`, budget `εovershoot`, destination `p + 1 ∈ {1,6,7,8}`.

The producer is `ClockZeroTail.seam_noOvershoot_tail_of_entry` (which TAKES the bridge as an explicit
argument, matching the `hOvershootTail` interface).  Its inputs:

* the structural guards `hq : CounterResetDest (p+1)`, `hdisp : SeamRegimeDispatch p`, plus the
  size/log/timing arithmetic (`hn`/`hn2`/`hlog`/`ht`);
* the per-config seam-entry facts derived from the seam `Pre`: `hcard` (card = n), `hStartNoOver`
  (`NoOvershoot p`), `hEntry` (`SeamEntryFullCounter p` — every just-advanced phase-`(p+1)` clock at
  full counter), each supplied by the wave-1 work-Post / seed-step structure on the seam `Pre`;
* the budget fit `hε : tseam · e^{−40(L+1)} ≤ εovershoot`.

The `DetSeamOvershootBridge (p)` argument is the wave-1 PRODUCED bridge (`#5a`,
`detSeamOvershootBridge_of_wf`); here it is THREADED through (not reproved), exactly as the
`hOvershootTail` interface demands.  Splice verdict: end-to-end from the bundle. -/
theorem hOvershootTail_of_entry
    (p n tseam : ℕ) (εovershoot : ℝ≥0)
    (hq : SeamNoOvershoot.CounterResetDest (p + 1))
    (hdisp : SeamNoOvershoot.SeamRegimeDispatch (L := L) (K := K) p)
    (hn : 1 ≤ n) (hn2 : 2 ≤ n)
    (hlog : Real.log (n : ℝ) ≤ (L + 1 : ℕ))
    (ht : tseam ≤ n * (L + 1))
    (hcard : ∀ c : Config (AgentState L K),
      (SeamEpidemics.allPhaseGe (L := L) (K := K) p n c ∧
        SeamEpidemics.advTriggered (L := L) (K := K) (p + 1) c) →
      Multiset.card c = n)
    (hStartNoOver : ∀ c : Config (AgentState L K),
      (SeamEpidemics.allPhaseGe (L := L) (K := K) p n c ∧
        SeamEpidemics.advTriggered (L := L) (K := K) (p + 1) c) →
      SeamNoOvershoot.NoOvershoot (L := L) (K := K) p c)
    (hEntry : ∀ c : Config (AgentState L K),
      (SeamEpidemics.allPhaseGe (L := L) (K := K) p n c ∧
        SeamEpidemics.advTriggered (L := L) (K := K) (p + 1) c) →
      SeamNoOvershoot.SeamEntryFullCounter (L := L) (K := K) p c)
    (hε : (tseam : ℝ≥0∞) * ENNReal.ofReal (Real.exp (-(40 * (L + 1) : ℕ)))
        ≤ (εovershoot : ℝ≥0∞)) :
    SeamNoOvershoot.DetSeamOvershootBridge (L := L) (K := K) p →
    ∀ c : Config (AgentState L K),
      (SeamEpidemics.allPhaseGe (L := L) (K := K) p n c ∧
        SeamEpidemics.advTriggered (L := L) (K := K) (p + 1) c) →
      ((NonuniformMajority L K).transitionKernel ^ tseam) c
          {c' | ¬ SeamNoOvershoot.NoOvershoot (L := L) (K := K) p c'}
        ≤ (εovershoot : ℝ≥0∞) := by
  intro hdet c hPre
  refine le_trans ?_ hε
  exact SeamNoOvershoot.seam_noOvershoot_tail_of_entry p n tseam hq hdisp hdet hn hn2 hlog ht c
    (hcard c hPre) (hStartNoOver c hPre) (hEntry c hPre)

/-- **The splice, all seams at once.**  Lifts `hOvershootTail_of_entry` over `k : Fin 10` at the
per-seam phase `seamP k`, horizon `seamT k`, budget `εovershoot k` — producing the FULL
`SeamQuickWins.DotyAtomsWave1Inputs.hOvershootTail` field shape (the `∀ k`, `∀ bridge`, `∀ c`,
seam-`Pre` → bound) from per-seam entry facts and guards.  This is the value the wave-1 input record
consumes for `hOvershootTail`; with it (and the wave-1 produced bridge `#5a`), the produced-seam
`hNoOvershoot` chain is end-to-end. -/
theorem hOvershootTail_field_of_entry
    (seamP seamT : Fin 10 → ℕ) (n : ℕ) (εovershoot : Fin 10 → ℝ≥0)
    (hq : ∀ k : Fin 10, SeamNoOvershoot.CounterResetDest (seamP k + 1))
    (hdisp : ∀ k : Fin 10, SeamNoOvershoot.SeamRegimeDispatch (L := L) (K := K) (seamP k))
    (hn : 1 ≤ n) (hn2 : 2 ≤ n)
    (hlog : Real.log (n : ℝ) ≤ (L + 1 : ℕ))
    (ht : ∀ k : Fin 10, seamT k ≤ n * (L + 1))
    (hcard : ∀ (k : Fin 10) (c : Config (AgentState L K)),
      (SeamEpidemics.allPhaseGe (L := L) (K := K) (seamP k) n c ∧
        SeamEpidemics.advTriggered (L := L) (K := K) (seamP k + 1) c) →
      Multiset.card c = n)
    (hStartNoOver : ∀ (k : Fin 10) (c : Config (AgentState L K)),
      (SeamEpidemics.allPhaseGe (L := L) (K := K) (seamP k) n c ∧
        SeamEpidemics.advTriggered (L := L) (K := K) (seamP k + 1) c) →
      SeamNoOvershoot.NoOvershoot (L := L) (K := K) (seamP k) c)
    (hEntry : ∀ (k : Fin 10) (c : Config (AgentState L K)),
      (SeamEpidemics.allPhaseGe (L := L) (K := K) (seamP k) n c ∧
        SeamEpidemics.advTriggered (L := L) (K := K) (seamP k + 1) c) →
      SeamNoOvershoot.SeamEntryFullCounter (L := L) (K := K) (seamP k) c)
    (hε : ∀ k : Fin 10,
      (seamT k : ℝ≥0∞) * ENNReal.ofReal (Real.exp (-(40 * (L + 1) : ℕ)))
        ≤ (εovershoot k : ℝ≥0∞)) :
    ∀ (k : Fin 10),
      SeamNoOvershoot.DetSeamOvershootBridge (L := L) (K := K) (seamP k) →
      ∀ (c : Config (AgentState L K)),
        (SeamEpidemics.allPhaseGe (L := L) (K := K) (seamP k) n c ∧
          SeamEpidemics.advTriggered (L := L) (K := K) (seamP k + 1) c) →
        ((NonuniformMajority L K).transitionKernel ^ (seamT k)) c
            {c' | ¬ SeamNoOvershoot.NoOvershoot (L := L) (K := K) (seamP k) c'}
          ≤ (εovershoot k : ℝ≥0∞) :=
  fun k =>
    hOvershootTail_of_entry (seamP k) n (seamT k) (εovershoot k) (hq k) (hdisp k) hn hn2 hlog
      (ht k) (hcard k) (hStartNoOver k) (hEntry k) (hε k)

end MarginInstantiation

end ExactMajority
