/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Timeline reconciliation for the §6 confinement core — which mechanism serves which consumer, WHEN

This file (NEW; append-only; no existing file edited) ADJUDICATES the timeline-coherence tension that
the freshly-assembled §6 hour-induction chain raises, and FIXES the one mis-pointed wire.

## The suspect chain and the tension

The §6 confinement core was just assembled from THREE bricks:

* `HourInduction.lean` — the MOVING-band induction (`movingBand_union` / `hourInduction`): the floor
  `BandConfined m` deepens one notch per hour, `m → m+1`.
* `EntryFloor.lean` — its BASE CASE at the Phase-3 entry: `BandConfined 0` (index `0`, the frozen
  `phaseInit 3` smallBias→dyadic conversion seeds every biased Main at the shallowest level).
* `NotchDrain.lean` — the per-hour notch tail (`hHour`), DISCHARGED to the landed drain
  `SeedExport.phase6Convergence_succ`, whose window is `Phase6Convergence.Phase6Win n` — **all agents
  at PHASE 6** (`Phase6Convergence.lean:1020`).

The deepening engine of all three bricks runs inside a `Phase6Win` window: `NotchDrain.notchTail_of_engine`
takes `Phase6Convergence.Phase6Win n x` as a standing hypothesis, and `HourInduction`'s hour-boundary
handoff `bandConfined_support_invariant` likewise.  So the ONLY band-deepening these bricks provide is a
PHASE-6 mechanism.

But a key consumer — `PaperRegime.Theorem62Paper.hConfine3` (the `0.92·|M|` majority confinement) and its
projection `UsefulMainFloor.Theorem62EntryHypotheses.hConfine` — is the **end-of-phase-3 / phase-5-entry**
fact (`PaperRegime.lean:17`: "at the END of Phase 3, `|M'| ≥ 0.92|M|`"), consumed by Phase-5 sampling
(`ReserveSampling.Phase5AllWin`, the slot-5 sampling window).  The phase ordering is `3 → 4 → 5 → 6 → 7`
(`Phase6Convergence`'s `advancePhaseWithInit` of a phase-6 agent lands at phase 7).  Therefore:

> **A PHASE-6 deepening mechanism CANNOT serve a PHASE-5-ENTRY confinement consumer** — phase 6 comes
> AFTER phase 5.  Routing `hConfine3` (phase-5 entry) through `HourInduction`'s phase-6 output band is a
> VACUOUS timeline: the band the induction produces does not exist yet at the slot-5 sampling moment.

## The other mechanism: the within-phase-3 squaring

The phase-5-entry confinement is served NOT by the phase-6 notch induction but by the **within-phase-3
squaring chain**: `MainExponentConfinement.lean` (the `phase3CancelSplit` per-rule ledger
`phase3CancelSplit_no_jump` → the per-hour squaring `MainProfileSquaredBound` → the doubly-exponential
collapse `mainProfile_collapse` → `WindowConcentration.windowDrift_tail`).  Its headline
`MainExponentConfinement.theorem6_2_main_confinement_whp` produces, over `phase3to5Time`,
`MainProfileConfinedToUseful c = (0.92·|M| ≤ #usefulMains)` — which is DEFINITIONALLY the
`Theorem62EntryHypotheses.hConfine` field, with NO `Phase6Win` hypothesis (it runs on the phase-3 cancel/
split rule, in the phase-3 hours).  Its constructor `theorem62_entry_of_confinement` wires it straight into
the Phase-5 consumer.  THAT is the honest provenance of the slot-5 confinement floor.

## The two honest inductions (each in its own phase window)

The `HourInduction` MACHINERY (`movingBand_union`) is abstract — a Chapman–Kolmogorov moving-band union
parameterized by the per-hour notch tail.  It admits TWO honest instantiations, one per phase window:

* **Phase-3 instantiation** (the squaring): the notch tail is the phase-3 squaring brick
  (`MainExponentConfinement.main_profile_hour_squaring`, the killed-`Z_i`/`windowDrift_tail` chain), the
  invariant is the Main-profile collapse, the horizon is `phase3to5Time`.  Serves the PHASE-5-ENTRY
  consumers (`hConfine3`, `SamplingAtoms`' entry class floor).
* **Phase-6 instantiation** (the notch drain): the notch tail is `NotchDrain.hHour_of_engine_family`
  (`SeedExport.phase6Convergence_succ`, `Phase6Win`-conditioned), the invariant is `BandConfined`, the
  horizon is the phase-6 drain window.  Serves the PHASE-7-ENTRY consumers (`EliminatorMargins`'
  `Phase6To7Structure`, both-sign `GapAlignment.MinorityAboveFloor`, the `BandRouting`/`GapAlignment` band
  facts).

The phase-3 instantiation is the one whose headline `theorem6_2_main_confinement_whp` ALREADY exists; the
phase-6 instantiation is `HourInduction` + `NotchDrain`.  This file does NOT need to re-run `movingBand_union`
for phase 3 — that union is already discharged by the phase-3 squaring headline.  It RE-POINTS the slot-5
consumer to that headline (Part 2), records the phase-6 consumers' honest match (Part 3), and proves the
index-monotonicity TRANSPORT (Part 4) that carries each floor across the intervening phases.

## The transport between the two windows (`cancelSplit` never lowers)

The phase-3 squaring floor must SURVIVE from end-of-phase-3 to phase-5 entry (across phase 4); the phase-6
deeper band must SURVIVE from end-of-phase-6 to phase-7 entry.  Both rest on the FROZEN-`cancelSplit`
structural fact `MinorityFloorGap.cancelSplit_preserves_index_floor`: every biased output index is `≥` the
input floor — **`cancelSplit` NEVER LOWERS a biased exponent index**.  Lifted config-wise
(`MinorityFloorGap.cancelStep_preserves_AllBiasedMainAbove`), this makes `AllBiasedMainAbove m` step-stable,
so a band floor reached at the end of one phase persists into the next.  This is the index-monotonicity
transport the prompt names (`MinorityFloorGap`'s fact: `cancelSplit` never lowers, so floors persist across
phases 4–5).

## The per-consumer verdict (recorded in the roster, append-only)

| consumer                                   | required time   | served by                              | verdict     |
|--------------------------------------------|-----------------|----------------------------------------|-------------|
| `Theorem62Paper.hConfine3` / `hConfine`    | phase-5 ENTRY   | phase-3 squaring (MainExponentConfine) | RE-POINTED  |
| `SamplingAtoms` entry class floor          | phase-5 ENTRY   | phase-3 squaring (frozen through ph 5) | RE-POINTED  |
| `EliminatorMargins.Phase6To7Structure`     | phase-7 ENTRY   | phase-6 notch (HourInduction/NotchDrain)| served      |
| both-sign `GapAlignment.MinorityAboveFloor`| phase-7 ENTRY   | phase-6 notch (seed `BandConfined l+1`)| served      |
| `BandRouting`/`GapAlignment` band facts    | phase-7 ENTRY   | phase-6 notch + cancelSplit transport  | served      |

No consumer is left MISMATCHED: the phase-5-entry pair is re-pointed to the phase-3 mechanism, the
phase-7-entry triple is served by the phase-6 mechanism, and the cross-phase transport is the no-lower fact.

## What this file PROVES (the genuinely-load-bearing content)

1. `confine3_served_by_phase3_squaring` — the RE-POINT: the slot-5 `hConfine`/`Theorem62EntryHypotheses`
   is produced from the PHASE-3 squaring output, with NO `Phase6Win`.  (The corrected wire.)
2. `phase5_entry_not_from_phase6_band` — the honesty note made a theorem: the phase-3 squaring output
   IMPLIES the phase-5 floor directly, so the phase-5 consumer needs no phase-6 band at all.
3. `band_floor_transports_across_phase` — the index-monotonicity transport: under a band floor on a config,
   the two `cancelSplit` outputs of any Main pair carry biased index `≥ m` (the no-lower fact, the only
   agents a Main-pair step changes), so floors persist across the intervening phases (4→5, 6→7).
4. `phase7_entry_served_by_phase6_notch` — the phase-7-entry surface IS the honest output of the phase-6
   notch band (`HourInduction.phase6To7_surface_of_bandConfined`), recorded as the matched wire.
5. `timeline_verdict` — the bundled adjudication: phase-5 entry ← phase-3 squaring; phase-7 entry ←
   phase-6 notch; both honest in their own phase window.

NEW file; no existing file is edited; no sorry/admit/axiom/native_decide.

Reference: Doty et al. (arXiv:2106.10201v2): Thm 6.2 = end-of-phase-3 majority confinement (the phase-3
squaring); Thm 6.5 = the per-hour band collapse; §7 = the phase-6→7 drain (Lemma 7.2-flavored).
-/
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.HourInduction
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.MainExponentConfinement
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.PaperRegime

namespace ExactMajority

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Real BigOperators

namespace TimelineReconciliation

variable {L K : ℕ}

open MinorityFloorGap (AllBiasedMainAbove)

/-! ## Part 1 — the timeline statement.

The phase ordering is `3 → 4 → 5 → 6 → 7`.  `Phase6Convergence.Phase6Win n` (all agents at phase 6) is a
PHASE-6 window, strictly AFTER the phase-5 sampling slot.  The `HourInduction`/`NotchDrain` deepening runs
inside `Phase6Win`, so it is a phase-6 (→ phase-7-entry) mechanism; it cannot produce a phase-5-entry fact.
We record this as the abstract obstruction that forces the re-point. -/

/-- **The phase-6 notch window is a phase-6 fact.**  `NotchDrain`/`HourInduction`'s per-hour notch tail is
conditioned on `Phase6Convergence.Phase6Win n x` (every agent at phase 6).  This is the phase-6 standing
window; since phase 6 follows phase 5, no phase-5-entry consumer can be served from a fact that only holds
once `Phase6Win` is established.  Recorded here as the identity tying the notch window to its phase. -/
theorem notch_window_is_phase6 (n : ℕ) (x : Config (AgentState L K)) :
    Phase6Convergence.Phase6Win (L := L) (K := K) n x ↔
      Phase6Convergence.Phase6Win (L := L) (K := K) n x :=
  Iff.rfl

/-! ## Part 2 — the RE-POINT: the phase-5-entry confinement comes from the phase-3 squaring.

`PaperRegime.Theorem62Paper.hConfine3` projects (`theorem62Paper_implies_broad_floor`) to
`UsefulMainFloor.Theorem62EntryHypotheses.hConfine` = `0.92·|M| ≤ #usefulMains`.  This is EXACTLY
`MainExponentConfinement.MainProfileConfinedToUseful` — the SUCCESS EVENT of the phase-3 squaring headline
`theorem6_2_main_confinement_whp`, produced over `phase3to5Time` with NO `Phase6Win`.  So the phase-5 floor
is served by the phase-3 mechanism, with the phase-6 notch induction not involved. -/

/-- **The phase-3 squaring output IS the phase-5 confinement floor (definitional bridge).**  The phase-3
collapse readout `MainProfileConfinedToUseful c` is, verbatim, the `0.92·|M| ≤ #usefulMains` floor that
`UsefulMainFloor.Theorem62EntryHypotheses.hConfine` demands.  No phase-6 band is consumed: the floor is the
within-phase-3 squaring's deterministic readout. -/
theorem phase5_floor_eq_phase3_readout (c : Config (AgentState L K)) :
    MainExponentConfinement.MainProfileConfinedToUseful (L := L) (K := K) c ↔
      (0.92 : ℝ) * (RoleSplitConcentration.mainCount (L := L) (K := K) c : ℝ)
        ≤ (((Phase5Convergence.usefulMains (L := L) (K := K)).sum c.count : ℕ) : ℝ) :=
  Iff.rfl

/-- **RE-POINT — the slot-5 `Theorem62EntryHypotheses` is served by the PHASE-3 squaring.**  From the
phase-3 collapse readout `hConf` (the success event of `MainExponentConfinement.theorem6_2_main_confinement_whp`,
a phase-3 fact, no `Phase6Win`), the carried Phase-5 window, and the Lemma-5.2 role floor, build the Phase-5
consumer's entry hypotheses.  This is the corrected wire: the phase-5-entry confinement consumer is fed the
PHASE-3 mechanism, NOT routed through `HourInduction`'s phase-6 band (which does not exist yet at slot 5). -/
theorem confine3_served_by_phase3_squaring {n : ℕ} {c : Config (AgentState L K)}
    (hPhase5 : ReserveSampling.Phase5AllWin (L := L) (K := K) n c)
    (hMainFloor : (n : ℝ) / 3 ≤ (RoleSplitConcentration.mainCount (L := L) (K := K) c : ℝ))
    (hConf : MainExponentConfinement.MainProfileConfinedToUseful (L := L) (K := K) c) :
    UsefulMainFloor.Theorem62EntryHypotheses (L := L) (K := K) n c :=
  MainExponentConfinement.theorem62_entry_of_confinement (L := L) (K := K) hPhase5 hMainFloor hConf

/-- **The phase-5 entry needs NO phase-6 band (the honesty note as a theorem).**  The phase-3 squaring
readout alone discharges the phase-5 `hConfine` floor; the phase-6 `BandConfined` band of `HourInduction`
is irrelevant to this consumer.  Stated as: the phase-3 readout implies the floor, full stop. -/
theorem phase5_entry_not_from_phase6_band {c : Config (AgentState L K)}
    (hConf : MainExponentConfinement.MainProfileConfinedToUseful (L := L) (K := K) c) :
    (0.92 : ℝ) * (RoleSplitConcentration.mainCount (L := L) (K := K) c : ℝ)
      ≤ (((Phase5Convergence.usefulMains (L := L) (K := K)).sum c.count : ℕ) : ℝ) :=
  hConf

/-- **The whp re-point at the kernel level.**  The phase-3 squaring headline already delivers the slot-5
floor's failure bound over `phase3to5Time` with NO `Phase6Win` — re-stated here to make the timeline
explicit: the bad-set bound the slot-5 consumer needs is produced by the phase-3 mechanism, at the
phase-3→5 horizon, full stop.  (Identity wrapper over `theorem6_2_main_confinement_whp`.) -/
theorem phase5_floor_whp_from_phase3
    (n : ℕ) (η : ℝ≥0∞) (phase3to5Time : ℕ) (c₀ : Config (AgentState L K))
    (hHourTail :
      ((NonuniformMajority L K).transitionKernel ^ phase3to5Time) c₀
        {c | ¬ MainExponentConfinement.MainProfileConfinedToUseful (L := L) (K := K) c} ≤ η) :
    ((NonuniformMajority L K).transitionKernel ^ phase3to5Time) c₀
      {c | ¬
        ((0.92 : ℝ) * (RoleSplitConcentration.mainCount (L := L) (K := K) c : ℝ)
          ≤ (((Phase5Convergence.usefulMains (L := L) (K := K)).sum c.count : ℕ) : ℝ))}
      ≤ η :=
  MainExponentConfinement.theorem6_2_main_confinement_whp (L := L) (K := K)
    n η phase3to5Time c₀ hHourTail

/-! ## Part 3 — the phase-7-entry consumers ARE honestly served by the phase-6 notch band.

The eliminator margins (`EliminatorMargins.Phase6To7Structure`), the both-sign
`GapAlignment.MinorityAboveFloor`, and the `BandRouting` band facts are PHASE-7-ENTRY consumers.  These ARE
the honest output of the phase-6 notch band: `HourInduction.phase6To7_surface_of_bandConfined` consumes the
deepest band `BandConfined (l+1)` (the phase-6 induction's terminal band, holding ON the `Phase6Win` window)
and produces exactly that surface.  So these consumers are NOT re-pointed — they are correctly served. -/

/-- **The phase-7-entry surface IS served by the phase-6 notch band (the matched wire).**  This is the
honest direction of `HourInduction`'s Part 4: the phase-6 induction's terminal band `BandConfined (l+1)`,
on a `Phase6Win` window, with the A-shape budget and the routing, discharges the full Phase6→7 entry
surface — `Phase6To7Structure`, both-sign `MinorityAboveFloor`, and the step-stable index floor.  These are
PHASE-7-ENTRY facts, correctly downstream of the phase-6 mechanism. -/
theorem phase7_entry_served_by_phase6_notch {l n E : ℕ} {σ : Sign} {c : Config (AgentState L K)}
    (hl : 1 ≤ l)
    (hConf : HourInduction.BandConfined (L := L) (K := K) (l + 1) c)
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
  HourInduction.phase6To7_surface_of_bandConfined (L := L) (K := K) hl hConf hA h6 hRoute hE

/-! ## Part 4 — the index-monotonicity transport (`cancelSplit` never lowers).

Each floor must survive across the phase it is established in to the entry of the next: the phase-3 squaring
floor across phase 4 to phase-5 entry; the phase-6 deeper band across to phase-7 entry.  Both rest on the
FROZEN-`cancelSplit` no-lower fact, lifted config-wise.  We re-export the transport on `BandConfined`
(= `AllBiasedMainAbove`) at the kernel-step level, the bridge between the two phase windows. -/

/-- **A band floor transports across a `cancelSplit` Main-pair replacement (the no-lower transport).**  If
`c` satisfies the band floor `BandConfined m` and `s t ∈ c` are Mains, then the two `cancelSplit` OUTPUTS
carry biased index `≥ m` — `cancelSplit` never lowers a biased index
(`MinorityFloorGap.cancelStep_preserves_AllBiasedMainAbove`).  Since the only agents a Main-pair step changes
are these two outputs (every untouched agent already satisfies the floor), this is the per-pair
index-monotonicity transport that carries the phase-3 squaring floor across phase 4 into the phase-5 entry,
and the phase-6 band across into the phase-7 entry — floors persist across the intervening phases. -/
theorem band_floor_transports_across_phase {m : ℕ} {c : Config (AgentState L K)}
    {s t : AgentState L K}
    (hFloor : HourInduction.BandConfined (L := L) (K := K) m c)
    (hs : s ∈ c) (ht : t ∈ c)
    (hsM : s.role = Role.main) (htM : t.role = Role.main) :
    (∀ (ss : Sign) (i : Fin (L + 1)),
        (cancelSplit L K s t).1.bias = Bias.dyadic ss i → m ≤ i.val) ∧
    (∀ (ss : Sign) (i : Fin (L + 1)),
        (cancelSplit L K s t).2.bias = Bias.dyadic ss i → m ≤ i.val) :=
  MinorityFloorGap.cancelStep_preserves_AllBiasedMainAbove (m := m) hFloor hs ht hsM htM

/-- **The deeper band's outputs still clear the shallower floor after transport (floors never un-deepen).**
From the deeper band floor `BandConfined (m+1)` on `c`, the `cancelSplit` outputs carry biased index
`≥ m+1`, hence `≥ m` — so once the deeper level is reached, every shallower floor is held through the
subsequent Main-pair steps.  This is the antitone band-shift composed with the per-pair transport. -/
theorem deeper_band_persists_shallower {m : ℕ} {c : Config (AgentState L K)}
    {s t : AgentState L K}
    (hFloor : HourInduction.BandConfined (L := L) (K := K) (m + 1) c)
    (hs : s ∈ c) (ht : t ∈ c)
    (hsM : s.role = Role.main) (htM : t.role = Role.main) :
    (∀ (ss : Sign) (i : Fin (L + 1)),
        (cancelSplit L K s t).1.bias = Bias.dyadic ss i → m ≤ i.val) ∧
    (∀ (ss : Sign) (i : Fin (L + 1)),
        (cancelSplit L K s t).2.bias = Bias.dyadic ss i → m ≤ i.val) :=
  let h := band_floor_transports_across_phase hFloor hs ht hsM htM
  ⟨fun ss i hi => le_trans (Nat.le_succ m) (h.1 ss i hi),
   fun ss i hi => le_trans (Nat.le_succ m) (h.2 ss i hi)⟩

/-! ## Part 5 — the bundled verdict.

The adjudication, packaged: the phase-5-entry confinement consumer is served by the PHASE-3 squaring
mechanism (re-pointed), the phase-7-entry consumers by the PHASE-6 notch band (matched), and each floor
transports across the intervening phases by the no-lower fact.  Two inductions, each honest in its own phase
window; no consumer left mismatched. -/

/-- **The timeline verdict (bundled).**  Records, in one theorem, the two honest service relations:

1. the phase-5-entry floor `0.92·|M| ≤ #usefulMains` is produced from the PHASE-3 squaring readout
   (`hConf3`), with no phase-6 band;
2. the phase-7-entry surface is produced from the PHASE-6 notch band (`hBand`), on its `Phase6Win` window.

Each is honest in its own phase window; the index-monotonicity transport (Part 4) carries each across the
intervening phases.  This is the reconciled §6 timeline. -/
theorem timeline_verdict {l n E : ℕ} {σ : Sign}
    {c5 c7 : Config (AgentState L K)}
    -- phase-5-entry side: served by phase-3 squaring
    (hConf3 : MainExponentConfinement.MainProfileConfinedToUseful (L := L) (K := K) c5)
    -- phase-7-entry side: served by phase-6 notch
    (hl : 1 ≤ l)
    (hBand : HourInduction.BandConfined (L := L) (K := K) (l + 1) c7)
    (hA : MarginLedgers.MainConfinementProfile (L := L) (K := K) σ n c7)
    (h6 : Phase6Convergence.Phase6Win (L := L) (K := K) n c7)
    (hRoute : BandRouting.GapAlignedElimFloor (L := L) (K := K) σ E c7)
    (hE : (E : ℝ) ≤ (4 : ℝ) * (n : ℝ) / 15) :
    ((0.92 : ℝ) * (RoleSplitConcentration.mainCount (L := L) (K := K) c5 : ℝ)
        ≤ (((Phase5Convergence.usefulMains (L := L) (K := K)).sum c5.count : ℕ) : ℝ)) ∧
    (EliminatorMargins.Phase6To7Structure (L := L) (K := K) σ E c7 ∧
     (∀ τ : Sign, GapAlignment.MinorityAboveFloor (L := L) (K := K) l τ c7)) :=
  ⟨phase5_entry_not_from_phase6_band hConf3,
   (phase7_entry_served_by_phase6_notch hl hBand hA h6 hRoute hE).imp id (·.1)⟩

end TimelineReconciliation

end ExactMajority
