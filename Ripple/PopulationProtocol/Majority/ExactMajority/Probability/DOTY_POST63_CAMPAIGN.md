
---

## TimelineReconciliation.lean — §6 timeline adjudication: phase-5 entry RE-POINTED to phase-3 squaring (2026-06-11)

New append-only file `Probability/TimelineReconciliation.lean` ADJUDICATES the timeline-coherence tension
the freshly-assembled hour-induction chain (`HourInduction` + `EntryFloor` + `NotchDrain`) raises, and FIXES
the one mis-pointed wire. Single-file `lake env lean` clean (EXIT 0); `#print axioms ⊆ [propext,
Classical.choice, Quot.sound]`; 0 sorry/admit/axiom/native_decide; `git diff --check` clean; append-only (no
existing file edited).

### The tension

The notch-deepening engine of all three new bricks runs inside `Phase6Convergence.Phase6Win n` — **all
agents at PHASE 6** (`NotchDrain.notchTail_of_engine` and `HourInduction.bandConfined_support_invariant`
both take it as a standing hypothesis). But `PaperRegime.Theorem62Paper.hConfine3` / its projection
`UsefulMainFloor.Theorem62EntryHypotheses.hConfine` (the `0.92·|M|` confinement) is the **end-of-phase-3 /
phase-5-entry** fact (`PaperRegime.lean:17`), consumed by Phase-5 sampling (`ReserveSampling.Phase5AllWin`).
Phase ordering is `3 → 4 → 5 → 6 → 7`, so a PHASE-6 mechanism cannot serve a PHASE-5-ENTRY consumer — routing
`hConfine3` through `HourInduction`'s phase-6 band is a VACUOUS timeline.

### The per-consumer verdict (the timeline map)

| consumer                                   | required time   | served by                              | verdict     |
|--------------------------------------------|-----------------|----------------------------------------|-------------|
| `Theorem62Paper.hConfine3` / `hConfine`    | phase-5 ENTRY   | phase-3 squaring (MainExponentConfine) | RE-POINTED  |
| `SamplingAtoms` entry class floor          | phase-5 ENTRY   | phase-3 squaring (frozen through ph 5) | RE-POINTED  |
| `EliminatorMargins.Phase6To7Structure`     | phase-7 ENTRY   | phase-6 notch (HourInduction/NotchDrain)| served      |
| both-sign `GapAlignment.MinorityAboveFloor`| phase-7 ENTRY   | phase-6 notch (seed `BandConfined l+1`)| served      |
| `BandRouting`/`GapAlignment` band facts    | phase-7 ENTRY   | phase-6 notch + `cancelSplit` transport| served      |

No consumer is left MISMATCHED.

### The fix (re-point) + the two-induction doctrine

The phase-5-entry confinement is served by the **within-phase-3 squaring** chain
(`MainExponentConfinement.theorem6_2_main_confinement_whp`: the `phase3CancelSplit` ledger → per-hour
squaring → doubly-exponential collapse → `windowDrift_tail`), whose success event
`MainProfileConfinedToUseful` IS `hConfine`, with NO `Phase6Win`. The `HourInduction.movingBand_union`
machinery is abstract and admits TWO honest instantiations: a phase-3 one (the squaring, already discharged
by the existing headline — serves slot-5) and a phase-6 one (`NotchDrain`'s `hHour` — serves slot-7 entry).
Two inductions, each honest in its own phase window.

Proven: `confine3_served_by_phase3_squaring` (the corrected wire — `Theorem62EntryHypotheses` from the
phase-3 readout, no `Phase6Win`); `phase5_entry_not_from_phase6_band`; `phase5_floor_whp_from_phase3` (the
kernel-level whp re-point); `phase7_entry_served_by_phase6_notch` (the matched wire from the phase-6 band);
`band_floor_transports_across_phase` / `deeper_band_persists_shallower` (the index-monotonicity transport —
`MinorityFloorGap.cancelStep_preserves_AllBiasedMainAbove`, `cancelSplit` never lowers, so floors persist
across phases 4–5 and 6–7); `timeline_verdict` (the bundled adjudication). Pairs with `HourInduction.lean`,
`EntryFloor.lean`, `NotchDrain.lean`, `MainExponentConfinement.lean`, `PaperRegime.lean`.

---

## NotchDrain.lean — the §6 per-hour single-notch drain tail (`hHour`), DISCHARGED (2026-06-11)

New append-only file `Probability/NotchDrain.lean` PROVES the last carried hypothesis of the §6 hour
induction: the per-hour notch-deepening tail `hHour` that `HourInduction.hourInduction` /
`EntryFloor.hourInduction_from_entry` consume open. Single-file `lake env lean` clean (EXIT 0, no
warnings); `#print axioms ⊆ [propext, Classical.choice, Quot.sound]` for all six theorems; 0
sorry/admit/axiom/native_decide; `git diff --check` clean; append-only (no existing file edited).

### The gap discharged

`HourInduction` (moving-band induction) and `EntryFloor` (base case) both CARRY, open, the per-hour
notch tail `∀ h x, BandConfined (l₀+h) x → (K^hourLen) x {¬ BandConfined (l₀+h+1)} ≤ δ`. This file
discharges it to the LANDED single-notch drain `SeedExport.phase6Convergence_succ` (the §6
`phase6Convergence'` engine run one level higher).

### The honest mechanism found

`BandConfined m = highMass m = 0`. The drain engine at level `m+1` has `Post = Phase6Win n ∧
highMass (m+1) = 0`, which by `phase6Post_iff` IS `BandConfined (m+1)`. So the per-hour notch IS the
drain engine's `convergence` field, read through three PROVEN bridges:

1. `notchBad_subset` — `{¬ BandConfined (m+1)} ⊆ {¬ Post}` (the `Phase6Win` conjunct only enlarges the
   bad set; unconditional containment).
2. `agentMassW_succ_le_two` / `highMass_succ_le_of_floor` / `pre_of_floor` — the **co-population mass
   bound**: once the floor sits at `m`, the only high agents are the band-top agents at index EXACTLY
   `m`, each of dyadic weight `2^((m+1)-m) = 2`, so the residual `highMass (m+1) ≤ 2·card = 2n`. Hence
   the drain `Pre`'s mass bound `≤ M₀` discharges from the floor + window whenever `2n ≤ M₀`. This is
   the co-population question the prompt flagged, answered: the supply is controlled by `n`, not a
   separate assumption.
3. horizon match `hourLen = engine.t` (the schedule sets the hour to the drain window; a numeric
   calibration, carried).

`notchTail_of_engine` is the bridge; `hHour_of_engine_family` assembles the uniform-over-hours `hHour`
family (one drain engine per band level) in the EXACT shape the induction consumes.

### How much of `hHour` closed vs the NAMED residual

The probability content of `hHour` is FULLY discharged to the landed drain — no new drift re-proved,
no sorry. The honest residual is NAMED precisely: the standing window `Phase6Win n x` (`card x = n`,
every agent in phase 6) at each hour start. The band floor ALONE does not imply it — `Phase6Win` is the
SEPARATE environmental invariant the §6 confinement maintains across the phase, and it is EXACTLY the
hypothesis `HourInduction.bandConfined_support_invariant` already consumes. So the produced `hHour` is
`Phase6Win`-conditioned: faithful to the surrounding machinery, not a new assumption. The drain's
reserve-supply floor (`hdrop`) enters through the carried engine data, made available BY `Phase6Win` —
exactly the prompt's "derive the supply floor from the window" route.

### What is PROVEN here

* `agentMassW_succ_le_two` — per-agent `(m+1)`-weight `≤ 2` under the floor (band-top agents weigh 2).
* `highMass_succ_le_of_floor` — residual high-mass `≤ 2·card` under the floor (co-population control).
* `pre_of_floor` — floor + `Phase6Win` → drain `Pre` (`2n ≤ M₀` calibration).
* `notchBad_subset` — the bad-set containment.
* `notchTail_of_engine` — the per-hour notch tail from the landed drain engine (`Phase6Win`-conditioned).
* `hHour_of_engine_family` — the assembled `hHour` family in the induction's exact shape.

Pairs with `HourInduction.lean` (moving-band induction), `EntryFloor.lean` (base case), `SeedExport.lean`
(single-notch drain engine). Closes the §6 induction's last brick modulo the named standing window.

---

## EntryFloor.lean — the §6 hour-induction BASE CASE: the Phase-3 entry band floor (hStart) (2026-06-11)

New append-only file `Probability/EntryFloor.lean` supplies the base case that `HourInduction.lean`'s
`hourInduction` / `movingBand_union` consume as `hStart` — `BandConfined l₀ c₀`, the band floor at
the Phase-3 entry — and surveys its HONEST provenance from the frozen `phaseInit 3` (Transition.lean).
Single-file `lake env lean` clean (EXIT 0); `#print axioms ⊆ [propext, Classical.choice, Quot.sound]`
for every theorem; 0 sorry/admit/axiom/native_decide; `git diff --check` clean; append-only.

### The provenance chain (where the entry floor comes from)

The §6 dyadic-exponent track does NOT exist in Phases 1–2:

* **Phase 1** averages the **`smallBias`** field (the `Fin 7` "small bias" track, values `0..6`) — NOT
  the dyadic `Bias L` exponent track.  `phaseInit 1` only touches roles/counters.
* **Phase 2** detects opinions from `smallBias` (`phaseInit 2`: error if `|smallBias|` out of band,
  else `opinions := sign(smallBias)`).  Still no dyadic track.
* **Phase 3** BORNS the dyadic track.  `phaseInit 3` at a Main runs the smallBias → dyadic conversion:
  `newBias := if smallBias.val < 3 then .dyadic .neg ⟨0,_⟩ else if > 3 then .dyadic .pos ⟨0,_⟩ else .zero`,
  then `{ a with bias := newBias, hour := ⟨0,_⟩ }`.  So every biased Main enters at dyadic exponent
  index **exactly `0`** (the SHALLOWEST level, bias `±1`; `Bias.lean`: `i=0 ↔ ±1`).  DETERMINISTIC.

### The entry floor `l₀ = 0` (proven, sharp)

`AllBiasedMainAbove m c` = every biased Main sits at index `≥ m`.  At Phase-3 entry every biased
Main's index is the init value `0`:

* `allBiasedMainAbove_zero` — `AllBiasedMainAbove 0 c` for ANY config (the dyadic index is a
  `Fin (L+1)`, so `0 ≤ i.val` unconditionally).  The trivially-honest floor; `l₀ = 0`.
* `bandConfined_entry` — the same in `HourInduction.BandConfined 0` shape (the `hStart` the induction
  consumes).  Holds for any start config — no nontrivial entry hypothesis needed.
* `phaseInit3_main_bias_index_zero` — the SHARP provenance: a *biased* Main (`smallBias.val ≠ 3`)
  entering Phase 3 has bias `.dyadic ss ⟨0,_⟩`, so its index is literally `0` (achieved, not merely
  `≥ 0`).  This is the deterministic init mapping that pins `l₀ = 0`.

### The hour arithmetic (`numHours = l + 1`; where `l` sits relative to `L`)

`hourInduction` deepens `l₀ → l₀ + numHours`.  The seed consumers (`SeedExport.seedExport_of_post_succ`,
`phase6To7_surface_of_seed`, `Theorem62Paper.hConfine3`) ride on the TERMINAL floor
`AllBiasedMainAbove (l+1)`.  Matching: `l₀ + numHours = l + 1` with `l₀ = 0` ⟹ **`numHours = l + 1`**.
The §6 schedule budgets one hour per level; the clock carries `L+1` hours (indices `0..L`).
`SeedExport`'s `l+1` drain runs while a free sampling hour exists strictly above the band-top `l` and
below the saturated top `L`, i.e. the explicit budget side-condition `l + 2 ≤ L`.  Hence:

```
l ≤ L − 2   ⟹   terminal seed level  l + 1 ≤ L − 1,
   numHours = l + 1 ≤ L − 1 < L + 1   (two hours of slack: the band-top hour l and the top hour L).
```

`entryFloor_hour_arithmetic` records this honestly: `0 + (l+1) = l+1 ∧ l+1 ≤ L−1 ∧ L−1 < L+1` from
`l + 2 ≤ L`.

### What is PROVEN here

1. `allBiasedMainAbove_zero` / `bandConfined_entry` — the entry floor `l₀ = 0` (the `hStart` shape).
2. `phaseInit3_main_bias_index_zero` — the SHARP phaseInit-3 provenance (entry index literally `0`).
3. `entryFloor_hour_arithmetic` — the hour accounting `numHours = l+1 ≤ L−1 < L+1`.
4. `hourInduction_from_entry` — the headline wiring: `HourInduction.hourInduction` instantiated at
   `l₀ = 0`, `numHours = l + 1`, delivering the terminal seed `BandConfined (l+1)` failure `≤ η` over
   the Phase-3→5 horizon from any start config + the landed per-hour drain tails + the budget.

This closes the §6 induction's BASE CASE: the entry floor is `l₀ = 0` (phaseInit-3-seeded), and the
deepening budget `numHours = l + 1` fits the `(L+1)`-hour schedule.  Pairs with `HourInduction.lean`
(the moving-band induction) and `SeedExport.lean` (the single-notch drain).

---

## HourInduction.lean — the §6 moving-band hour induction: Thm 6.5 → 6.2 skeleton assembled (2026-06-11)

New append-only file `Probability/HourInduction.lean` assembles the genuinely-open GLUE of the §6
confinement core: the **moving-band induction** that the fixed-invariant all-hours union
(`HourUnion.confinementEvent_hours_union`) could NOT express.  Single-file `lake env lean` clean
(EXIT 0, no warnings); `#print axioms ⊆ [propext, Classical.choice, Quot.sound]` for every theorem;
0 sorry/admit/axiom/native_decide; `git diff --check` clean; append-only (no existing file edited).

### The gap the fixed-invariant union left open

`HourUnion.lean` chains a SINGLE FIXED invariant (`ConfinementSurface.ConfinementEvent`) across the
hours via `EarlyDripMarked.checkpoint_composition`.  But Doty's Theorem-6.5 induction is NOT over a
fixed event: at hour `h` the band floor sits at level `l_h`, and each hour the drain pushes it ONE
NOTCH DEEPER (`l_h → l_h + 1`).  The invariant MOVES; the fixed-invariant union does not apply.
`SeedExport.lean` lands the SINGLE-notch drain (`l → l+1`); this file CHAINS the notches.

### The inductive invariant and the landed per-hour bricks (all consumed, none re-proved)

* invariant `BandConfined m c := MinorityFloorGap.AllBiasedMainAbove m c` (= `highMass m c = 0`);
* (a) width budget → `ClocksBelowHour h` (`ClockCeiling.clocksBelowHour_of_goodWidth`) — LANDED;
* (b) band → supply region `NoMinoritySignAbove` (`SupplyRegion`, same population family) — LANDED;
* (c) region → killed `Z_i` drift → per-hour squaring tail
  (`SupplyRegion.supplyRegion_verdict` / `MainExponentConfinement.main_profile_hour_squaring`) — LANDED;
* (d) squaring + descent → one notch deeper (`SeedExport.phase6Convergence_succ`) — LANDED.

### What is PROVEN here (the genuine assembly)

1. `bandConfined_support_invariant` — **the hour-boundary handoff** (the floor never un-deepens within
   an hour), PROVEN from the landed `Phase6Convergence.highMass_le_on_support` through `phase6Post_iff`.
2. `bandConfined_antitone` — **the band-shift bookkeeping** (`m+1 ⟹ m`): the deepest band delivers all
   shallower confinements (the descent's payload).
3. `movingBand_union` — **the genuinely-new machinery**: a Chapman–Kolmogorov induction on the hour
   count where the TARGET invariant ADVANCES one notch per hour.  The moving-band analogue of
   `EarlyDripMarked.invariant_union_bound`/`checkpoint_composition` (which only handle a FIXED
   invariant).  From the per-hour notch-deepening tail (`hStep`) + the entry floor, it discharges the
   DEEPEST-band failure `≤ numHours·δ`.  The handoff grounds `hStep`'s uniformity over confined starts
   (so it enters through `hStep`'s validity, NOT as a dead carried hypothesis).
4. `hourInduction` — **the headline**: from the Phase-3 entry floor (base case) + the per-hour drain
   tails + the horizon decomposition + the budget, the failure to reach the deepest band
   `BandConfined (l₀ + numHours)` at the Phase-5 entry is `≤ η`.  The Thm-6.5 → 6.2 skeleton.
5. `phase6To7_surface_of_bandConfined` / `seed_of_bandConfined_succ` — **the Phase-5 entry surface**:
   the deepest band IS the seed `AllBiasedMainAbove (l+1)` discharging `SeedExport`'s Phase6→7 /
   `PaperRegime.Theorem62Paper` consumers (the eliminator margin + both-sign `MinorityAboveFloor`).
6. `hourInduction_capstone` — the bundled chain (discharge + seed readout).

### Honest accounting

The per-hour drain tail is the LANDED single-notch drain, carried as `hHour`; this file does NOT
re-prove the single-hour drift.  Base case = the carried Phase-3-entry floor `hStart`.  Hour-boundary
handoff = PROVEN.  Band-shift bookkeeping = PROVEN.  The genuinely-new content is the moving-band
union; everything else is the landed per-hour bricks chained.

---

## ClockCeiling.lean — the width-Post → `ClocksBelowHour` derivation: the §6 positional chain collapses onto the width machinery (2026-06-11)

New append-only file `Probability/ClockCeiling.lean` supplies the SINGLE load-bearing bridge the
positional cluster was missing, and event-conditions the WHOLE §6 positional chain on the landed
clock-front WIDTH Post.  Single-file `lake env lean` clean (EXIT 0, no warnings); `#print axioms ⊆
[propext, Classical.choice, Quot.sound]`; 0 sorry/admit/axiom/native_decide; `git diff --check`
clean; append-only (no existing file edited).

### The crux: PROVING the provenance `PositionalCluster` left as a note

`PositionalCluster.lean` DEFINED `ClocksBelowHour h c` (every clock `minute < (h+1)·K`) as a snapshot
with the note "provenance: the window `Window h`/`cAbove h = 0` confines the clocks below the current
hour", and proved the per-step engine `ClocksBelowHour h ⟹ drag stamps hour ≤ h` (+ the cancel
coupling to the index ceiling).  This file PROVES that provenance from the landed width machinery:

* `clocksBelowHour_of_rBeyond_eq_zero` — `rBeyond ((h+1)·K) c = 0` (empty front above the hour
  boundary) ⟹ `ClocksBelowHour h c`, via the landed `ClockFrontShape.clock_lt_of_rBeyond_eq_zero`.
  The hour-`h` boundary IS the minute `(h+1)·K`; `capMinute = K·(L+1)` is the `h = L` instance.
* `rBeyond_eq_zero_of_goodWidth_of_bulk_below` — the level-`M` contrapositive of the landed
  `ClockFrontProfile.GoodFrontWidth` width invariant: on the good-width event, if the `0.1` bulk has
  not reached within `W` of `M` (`10·rBeyond (M−W) c < card`), then `rBeyond M c = 0`.  This GENERALISES
  `ClockFrontProfile.frontSync_of_goodWidth_of_bulk_below` (the `M = capMinute` / `FrontSync`
  instance) to EVERY hour boundary `M = (h+1)·K`.
* `clocksBelowHour_of_goodWidth` — the composite, the load-bearing bridge: **`GoodFrontWidth W c` +
  bulk-behind ⟹ `ClocksBelowHour h c`**, deterministic, zero new probabilistic content.
* `clocksBelowHour_cap_of_goodWidth` — the cap-hour `h = L` instance, tying the positional
  `ClocksBelowHour` to the landed `FrontSync` cap-safety (one width event drives both).

### How much of the §6 positional chain became event-conditioned

The ENTIRE positional cluster collapses onto the single width Post `GoodFrontWidth W`:

```
GoodFrontWidth W  ─►  rBeyond ((h+1)K) c = 0  ─►  ClocksBelowHour h
   (Part 2)              (Part 1)
ClocksBelowHour h ─►  drag/cancel hour ceiling  ─►  MainHourBelow h
   (PositionalCluster.dragLeft/Right_mainHour_le + mainHour_le_of_clockBelow_cancelSplit;
    re-exported here as dragLeft/Right_mainHour_le_of_clocksBelow + mainHourBelow_step)
MainHourBelow h   ─►  AllBiasedMainBelow h  (WindowReconciliation; allBiasedMainBelow_of_snapshots)
AllBiasedMainBelow ─► MajorityTopEdge / band top edges  (majorityTopEdge_of_snapshots)
                   ─►  CeilingRoute / phase6To7_surface_widthConditioned  (the corrected Phase6→7
                       surface, the band-edge + drag-control consumers)
```

So the positional roster's remaining snapshots — the hour ceiling `MainHourBelow (l+2)`, the index
ceiling `AllBiasedMainBelow (l+2)`, the band top edges, and the `SupplyRegion`/`SupplyDispatch` drag
control downstream — are all event-conditioned on the SINGLE landed width budget.  Their
probabilistic complement is exactly the landed width-budget tail (`WidthTransport` /
`CrossHourSide` / `ClockBudgets.WidthSideP`), so this file adds NO new probabilistic content: the
§6 positional cluster is now a deterministic readout of the one clock-front width event.

### Status marker

`clock_ceiling_status : True` documents the build/audit; the load-bearing decls are
`clocksBelowHour_of_goodWidth` and `phase6To7_surface_widthConditioned`.

---

## SlotAtoms.lean — roster #10 + #15 + #4 (WAVE 2, B-class one-instantiation items) (2026-06-11)

New append-only file `Probability/SlotAtoms.lean` discharges three WAVE-2 roster items by wiring
landed machinery (no new math).  Single-file `lake env lean` clean (uisai2 /dev/shm, v4.30.0 @
mathlib c5ea0035, EXIT 0, no warnings); all 19 exported decls `#print axioms ⊆ [propext,
Classical.choice, Quot.sound]`; 0 sorry/admit/axiom/native_decide; max line width 100; append-only.

### #10 — `hpull1` PRODUCED + entry-gap VERDICT + far-witness side selection

The slot-1 partner-pool floor `WorkInputsHonest.hpull1` (`∀ b, Phase1AllMain n b → P1 ≤
pullPosSet.sum count`) is PRODUCED from the landed Phase-1 chain (`AveragingRate` strict-drop
rectangles + the `{2,3,4}` ceiling → `PartnerMargin` Θ(n) floors → `AveragingCollapse` variance):

* `lowSet_subset_pullPosSet` / `lowSet_sum_le_pullPosSet` — the lift `lowSet ⊆ pullPosSet`
  (Main `val ≤ 3` ⊆ Main `val ≤ 4`), the missing inclusion connecting the chain's `lowSet` floor to
  the field's `pullPosSet`.
* `pullPos_floor_of_entry` — the DETERMINISTIC floor `(n − g + 3)/4 ≤ pullPosSet.sum count` from
  `PartnerMargin.EntrySumPinned n g b` (= `Phase1AllMain ∧ |centredBiasSum| ≤ g`) via
  `lowSet_floor_of_entry` + the lift.
* `hpull1_of_gap_persistence` — **the #10 adapter**: produces the EXACT `hpull1` field at
  `P1 = (n − g + 3)/4 = Θ(n)` from the ENTRY-GAP PERSISTENCE
  `hgap : ∀ b, Phase1AllMain n b → |centredBiasSum b| ≤ g`.
* `hdrop1_of_gap_persistence` — composes `Hext1` (carried) + the produced `hpull1` through
  `DrainRates.hdrop1_of_chain`, giving the full slot-1 per-level rate `levelRate ((n−g+3)/4) n`.
* `far_high_side` / `far_low_side` — the far-witness side selection (re-exports of
  `secondMomentN_hdrop_of_entry_{high,low}`): a far-high witness pairs against the `lowSet` floor, a
  far-low witness against the `highSet` floor — the per-config datum the structure lemma
  `farExists_of_secondMoment_gt_n` leaves open.

**Entry-gap VERDICT.**  The chain start (`PartnerMargin.EntrySumPinned n g`) pins `|centredBiasSum| ≤
g`, where `g` is the CONSERVED initial opinion gap: each Main encodes a `±1` opinion, so
`centredBiasSum = #plus − #minus = gap`, `avgFin7`-conserved (`centredBiasSum_stepOrSelf_eq`) and
one-step support-closed (`EntrySumPinned_support_closed`).  So the gap-persistence input `hgap` is
NOT an extra residual — it holds on every in-window config because the chain stays inside
`EntrySumPinned n g` from the Doty εn-gap entry.  The `{2,3,4}`-ceiling `Θ(n)` margin yields the
paper-faithful `q = 1 − Θ(1/n)`, `t = Θ(n log n)` horizon (Lemma 5.3 / [45], NOT the crude `g = n`
degenerate `P = ⌈0/4⌉`).  **`hext1` VERDICT:** `Hext1` (`1 ≤ extremePosSet.sum`, the `+3`-saturated
extreme floor) is a STRUCTURAL SATURATION floor — genuinely persistence-carried, NOT
chain-dischargeable (the `|centredBiasSum| ≤ g` invariant bounds the SIGNED sum, not the existence of
a saturated extreme); it is the partner of `hpull1` in the `+3 × partner` strict-drop rectangle.

### #15 — the opaque work slots, replace-by-constructor (constructor table)

| slot | constructor | source | rate status |
|---|---|---|---|
| `work0` | `slot0W` ← `EndpointWiring.roleSplitW_of_two_stage` | three-stage role-split CK union | stage tails carried |
| `work2` | `slot2W` ← `(Phase2Convergence.phase2Convergence …).toW` | opinion-union doubling seed | `s,t,ε` PARAMETER-carried |
| `work3` | `slot3W` ← `EndpointWiring.phase3Convergence_bounded` | §6 clock side budget (bounded horizon) | side `εside` carried |
| `work9` | `slot9W` ← `(Phase2Convergence.phase2Convergence …).toW` | pre-phase-10 opinion-union | `s,t,ε` PARAMETER-carried |

`SlotInstanceInputs` carries the four constructors' named calibration data; `SlotInstanceInputs.work{0,2,3,9}`
are the per-slot constructed instances; `slotInstances_of_named` is the **bundle adapter** exhibiting
the four opaque `WorkInputsHonest.work{0,2,3,9}` fields as the named constructors (no longer anonymous
instances).  Survey finding on the `Phase2Convergence.toW` instances: they are NOT parameter-closed —
they CARRY the epidemic rate `s`, horizon `t`, budget `ε` and the union-algebra hypotheses
(`singleSign`, `opinionsUnion` idempotents) as honest scalar/structural inputs (the wiring-table's
"epidemic rate in instance").  `PhaseConvergence.toW` forgets the absorption to the weak instance the
work family uses.

### #4 — `hSeedStep` honest mechanism (the drain-seam verdict)

**The honest mechanism FOUND.**  The drain work `Post`s (`Phase1AllMain`, `Phase8AllMain`) are
DRAINED EXACT windows — `card = n`, every agent at phase EXACTLY `p`, ALL Main.  On such a window
`advTriggered (p+1)` is FALSE (`AssemblyBridges.drained_post_no_advTrig`, re-exported as
`drained_no_advTrig`): no agent is at phase ≥ p+1.  So `hSeedStep` is genuinely NOT a `Post` read — it
is the ONE-STEP seam-entry event "the next interaction advances some agent into phase p+1".  Whose
phase advances is seeded by phase-`(p+1)` PRESENCE (`AtRiskClockZero p` → `advTriggered (p+1)`,
`AssemblyBridges.advTriggered_of_atRiskClockZero`).  Two honest worlds:

* **(a) counter-timed seams** — the seam-start configuration is the drained ALL-CLOCK state
  (`AllClockGEpCard p n ∧ clockCounterSumAt p = 0 ∧ geCount (p+1) = 0`).  The seed fires for FREE
  (full rectangle, advance rate 1): `hSeedStep_timed_of_drained` ← `SeedRungs.drained_kernel_seedTarget_compl_zero`
  (`p ∈ {0,1,5,6,7,8}`), re-stated in the `advTriggered` set via `advTriggered_iff_seedTarget`.
* **(b) all-Main drain seams** — re-reading `ConcreteAssembly`'s window structure resolved the
  prompt's "Mains + clocks coexist?" question: the work-window predicate `Phase1AllMain`/`Phase8AllMain`
  is genuinely ALL-MAIN (`c.card = n ∧ ∀ a ∈ c, Main` — the ENTIRE multiset is Mains, `n` is the full
  card; there are NO clocks in `c`).  So the structural clock-advance seed is UNAVAILABLE (no clocks
  to tick), and the all-Main `Post` cannot manufacture the phase-`(p+1)` agent (it pins all `n` agents
  to phase `p`).  The seed is therefore a genuine per-seam one-step event — the precise named
  remainder `SeedStepEvent (seamP k) ((work k).Post)`.  `hSeedStep_of_event` PRODUCES the
  `DotyAssembly'.hSeedStep` field from the per-seam `SeedStepEvent` family (trivial wiring; for
  counter-timed seams `SeedStepEvent` is `hSeedStep_timed_of_drained` ∘ the drained-state read).

**Verdict:** for the all-Main drain seams `hSeedStep` is NOT the clock seed (no clocks present); it is
the genuine main-advance one-step seam-entry event, isolated as the named `SeedStepEvent` remainder.

---

## ClockZeroTail.lean — roster #5(b): the AtRiskClockZero seam tail GATE, closed (2026-06-11, WAVE 2)

New append-only file `Probability/ClockZeroTail.lean` discharges WAVE-2 roster item **#5(b)** — the
per-seam clock-zero tail that GATES every no-overshoot seam (10 seams).  The landed
`SeamPairAdapter` affine engine (`seam_atRiskClockZero_tail_honest`, honest `2·eˢ·freshVal`
immigration, budget `e^{−40(L+1)}`) consumed ONE remaining probabilistic input it could not
manufacture from the kernel alone: the **initial-potential bound**
`Φ_1(c₀) = seamClockPotential p 1 c₀ ≤ n·e^{−50(L+1)}` (the `hinitΦ` hypothesis).  This file PROVES
it and wires the full no-overshoot chain into the `DotyAssembly'.hNoOvershoot` feeder fields.

### The initial-potential derivation (the crux)

`seamClockSummand p 1 a` is NONZERO only for a CLOCK at the NEW phase `p+1`
(`if role=clock ∧ phase=p+1 then exp(−counter) else 0`).  At the seam START the phase-`(p+1)`
clocks are exactly the ones JUST advanced into `p+1` — counter-advanced from phase `p` via
`stdCounterSubroutine → advancePhaseWithInit → phaseInit (p+1)`, OR epidemic-dragged from a lower
phase via `runInitsBetween → phaseInit (p+1)` (the `SeamPairAdapter` advance-immigration lemmas).
For the counter-reset destination set `{1,6,7,8}`, BOTH paths run `phaseInit (p+1)` on the clock,
which RESETS `counter := 50(L+1)` (`Protocol/Transition.lean:138/166-173`, FROZEN; this is the
`freshVal` exponent).  So every at-risk clock at the seam start has the FULL counter, its summand
is EXACTLY `e^{−50(L+1)} = M`, and the sum over the `≤ n` agents is `≤ n·M`.  This is the seam
analogue of `Phase0Window.clockCounterPotential_init_le` (every phase-0 clock full), with the
"full counter" condition restricted to the at-risk phase-`(p+1)` clocks the seam summand reads.

The FROZEN seam-entry fact is named `SeamEntryFullCounter p c` (= every phase-`(p+1)` clock has
counter `50(L+1)` — the just-advanced/reset clocks), and `seamClockPotential_init_le` derives
`hinitΦ` from it (the same `Multiset.sum_le_card_nsmul` argument as Phase 0, the nonzero summands
pinned to `M` by the full-counter hypothesis).

### What was built (all axiom-clean ⊆ [propext, Classical.choice, Quot.sound]; 0 sorry/admit/axiom/native_decide)

| Theorem | Content |
|---|---|
| `SeamEntryFullCounter` | the seam-start full-counter predicate on phase-`(p+1)` clocks |
| `seamClockPotential_init_le` | **the crux**: `Φ_1(c₀) ≤ n·e^{−50(L+1)}` from the full-counter entry fact (mirror of `clockCounterPotential_init_le`) |
| `seam_atRiskTail_of_entry` | the honest at-risk tail with `hinitΦ` DISCHARGED from the entry fact (specialises `seam_atRiskClockZero_tail_honest`) |
| `seam_noOvershoot_tail_of_entry` | the assembled `(K^tseam) c₀ {¬NoOvershoot} ≤ tseam·e^{−40(L+1)}` — per-`τ` at-risk tails (each FROM the FIXED `c₀` at horizon `τ`, SAME entry fact) composed through `seam_noOvershoot_tail` + the deterministic bridge |
| `hNoOvershoot_field_of_entry` | the per-seam `hNoOvershoot` value AT the `DotyAssembly'.hNoOvershoot` field shape, PRODUCED for `CounterResetDest (p+1) ∈ {1,6,7,8}`: `Wf`-region (discharges `DetSeamOvershootBridge` via `detSeamOvershootBridge_of_wf`) + `SeamRegimeDispatch` + per-config seam-entry facts (`hStartNoOver`/`hEntry`/`hcard`) + budget fit `tseam·e^{−40(L+1)} ≤ εovershoot` |
| `counterResetDest_of_seamP_mem` / `not_counterResetDest_of_guarded` | the produced-vs-guarded destination accounting |

### hNoOvershoot: PRODUCED vs GUARDED (the field deliverable)

In `dotyPhases'` the 10 seams advance `seamP k → seamP k + 1` along the phase chain (`seamP k = k`),
so destination `= k+1`.  `hNoOvershoot_field_of_entry` PRODUCES the `DotyAssembly'.hNoOvershoot`
feeder value exactly for the honest counter-reset destination set:

* **PRODUCED** (counter-timed, full-counter reset on entry; the `SeamPairAdapter` honest set):
  destinations `{1,6,7,8}` — seams with `seamP k ∈ {0,5,6,7}` (`counterResetDest_of_seamP_mem`).
* **GUARDED** (named, not faked; `not_counterResetDest_of_guarded` certifies they FAIL
  `CounterResetDest`):
  - destinations `{2,4,9}` UNTIMED (opinion-union / big-bias) — no-overshoot from the work-phase /
    big-bias guards in `SeamEpidemics`;
  - destinations `{3,5}` counter-timed but NO counter reset on entry (`phase 3` `phaseInit` sets
    `minute`; `phase 5` predecessor advances via `advancePhase`, no `phaseInit`) — no-overshoot from
    the dedicated minute/hour width machinery (`ClockOLogN`/`ClockReal*`);
  - destination `10` = error/backup entry, outside the seam chain.

The seam-entry facts `hStartNoOver` (start `NoOvershoot p`) / `hEntry` (`SeamEntryFullCounter p`) are
the honest per-config readings of the seam-start configuration the work `Post`/seed step delivers
(carried as feeder hypotheses, not faked); the only opaque side condition remaining on the produced
seams is the global `Wf`-region (the `Analysis`-layer reachability invariant
`reachable_preserves_well_formed_agent_quota`) feeding the deterministic bridge — already the
`SeamOvershootBridge` carry, not a new residual.

### Build/audit

Single-file `lake env lean` clean (local v4.30.0 olean closure, mathlib c5ea0035, EXIT 0, no
warnings); olean emitted via `-o`.  All six exported decls `#print axioms ⊆ [propext,
Classical.choice, Quot.sound]` (`counterResetDest_of_seamP_mem` only `propext`;
`not_counterResetDest_of_guarded` no axioms).  0 sorry/admit/axiom/native_decide; `git diff --check`
clean; max line width 97.  Append-only; no existing file edited.

---

## FinalAssemblyV2.lean — F1+F2+F3 final-audit fix (whp half) (2026-06-11)

The final adversarial audit (`/tmp/codex_final_audit.md`) flagged three defects in
`FinalAssembly.doty_theorem_3_1_whp`.  `FinalAssemblyV2.lean` fixes all three, append-only (edits no
existing file), single-file `lake env lean` clean (`#print axioms ⊆ [propext, Classical.choice,
Quot.sound]`; 0 sorry/admit/axiom/native_decide).

**F1 (CRITICAL) — `hcompFail` PRODUCED, not carried.**  The old whp theorem carried `hcompFail` (the
assembled bad-event bound) as a FREE binder — tautological.  V2 produces it: `doty_time_composition_W2`
applied at the concrete honest family `phases'V2 ra` delivers `.1` (failure mass at the LITERAL sum
horizon `∑ i, (phases'V2 ra i).t`), and `hcompFail_produced` folds it to the opaque `T`.

The wall (extensively characterised): the assembled failure bound `(K^T)… ≤ …` is intractable to
PRODUCE-and-CONSUME at the *sum* horizon in a downstream file.  The composition's `.1` extraction is
tractable only IN the file where `doty_time_composition_W2` is first used (DotyTimeHeadline /
BudgetTightening) — over an abstract `phases`/`asm`, where `(dotyPhases' asm i).t` is an
irreducibly-stuck projection.  Once that output's *type* (which carries `(K^(∑ … i).t)`) is consumed
downstream — via `obtain`, `.1`, `subst`, `rw [hT]; exact`, or `▸` — the defeq checker must `whnf`
the kernel power against the `Fin 21` sum, which diverges (measured: still times out at 3M, and
running at 8M for >12 min — NOT heavy-finite, so a bare `set_option maxHeartbeats` does NOT land,
route (c) rejected).

The winning route is a metavar-assignment fold (route b, born in T-form):
* `BudgetTightening.doty_time_headline_W2_inv_sq` is the LANDED in-file `.1`-producer giving
  `(K^(∑ … i).t)… ≤ 21/n² ∧ ∑ … ≤ 21·C0·n·(L+1)` over an abstract `phases`.
* `fold_pair_to_T {S : ℕ}` takes the produced pair as `hpair` at the OPAQUE/implicit `S` and a fold
  `hT : T = S`, concluding `(K^T)…`.  `S` is IMPLICIT, so when the W2-inv-sq result is passed as
  `hpair`, unification ASSIGNS `?S := ∑ (dotyPhases' asm i).t` by metavar assignment — NOT a defeq
  `whnf` of two `(K^∑…)` terms (the divergent direction).  The `subst hT; exact hpair` is then
  syntactic.  (This is the `AssemblyBridges.hcompFail_of_composition` idiom — `hpair` arrives free —
  refined so the horizon is captured by an implicit metavar, the single move that clears the wall.)
* `whp_of_asm'` packages production+fold over a FREE `asm : DotyAssembly'`, concluding at the opaque
  `T`.  `doty_theorem_3_1_whp_v2` INSTANTIATES it at `asm := toAssembly'V2 ra` (the honest assembly):
  pure substitution of an already-checked proof, and the opaque-`T` output is consumed cheaply.

`hcompFail` is GONE from `doty_theorem_3_1_whp_v2`.  No `set_option maxHeartbeats`, no axiom beyond
`[propext, Classical.choice, Quot.sound]`.

**F2+F3 — the work family made HONEST (levels engine; the dead per-level inputs on the path).**  The
old `AssemblyWiring.dotyWorkConcrete` used the CRUDE single-step `potDone` rate for slots 1/5/7/8
(`DrainRates.lean`'s own doc: "structurally vacuous for `Φ ≥ 2`", matching the floor only at `m=1`),
while the honest per-level machinery was landed but DEAD off the path.  V2's `dotyWorkHonest` builds
slots 1/5/7/8 on `OneSidedCancel.levels_PhaseConvergenceW` (the Phase-6 engine), consuming:
* slot 1 — `DrainRates.hdrop1_of_chain` (the +3 extreme witness + the Lemma-5.3 partner-pool floor);
* slot 5 — a LEVELS drain on `unsampledReserveU` (`DrainRates.hdrop5_of_chain`, the Theorem-6.2
  biased-Main floor) composed with the carried sampling concentration `hConc` at the levels horizon
  `∑ tWin5 m` (mirroring `Phase5Convergence.phase5Convergence`);
* slot 7 — the gap-1 eliminator margin `hPhase6Post7` (Lemma 7.4), through `slot7_hdrop_direct`
  (an inlined `slot7_levels_hdrop`, minority witness PROVED);
* slot 8 — the above-level eliminator margin `hPhase7Post8` (Lemma 7.6), through `slot8_hdrop_direct`.

Each honest slot has the SAME `Pre`/`Post` as the crude one (both engines: `Pre = Inv ∧ Φ ≤ M₀`,
`Post = Inv ∧ Φ = 0`), so every downstream bridge / seam connects unchanged.  The level engine wants
the per-level binder at every `m`; the landed `hdrop{5,7,8}_of_chain` are guarded `1 ≤ m`, so the
rate is `qHat E n m = if 1 ≤ m then levelRate E n m else 1` (the `m=0` binder is the trivial
`K b (potBelow Φ 0)ᶜ ≤ 1`; the budget sum over `Icc 1 M₀` only reads `m ≥ 1`, where `qHat =
levelRate`).

`WorkInputsHonest` is the re-cut residual record: the crude `hstep1/5/7/8` are DROPPED; the carried
per-slot atoms are now the structural floors (`hext1`/`hpull1`/`hmain5`), the eliminator margins
(`hPhase6Post7`/`hPhase7Post8` — the advertised events now CONSUMED, not dead), the per-level budgets
(`hpt1/5/7/8`), and the sampling concentration (`hConc`).

**V2 surface.**  `doty_theorem_3_1_whp_v2 : (K^T) c₀ {¬ majorityStableEndpoint} ≤ 21/n² ∧ T ≤
21·C0·n·(L+1) ∧ T ≤ 21·C0·n·(⌈log₂ n⌉+1)`, over `DotyRegime n L K` + `DotyResidualAtomsV2`.  Remaining
binders: `hReg` (regime), `ra` (residual atoms — now the honest bundle), `T`/`hT` (horizon
bookkeeping), `ht`/`hε` (budget/time arithmetic), `hx₀` (start pin), `h_post` (endpoint bridge).
`hcompFail` is gone (produced).  The expected half (`doty_theorem_3_1_expected`) is unchanged in
`FinalAssembly.lean`; V2 covers the whp half, the audit's crux.

## DoublingEdges.lean — hour-gated top edge + occupancy verdict (2026-06-10)

The §6 "doubling chain passes through every level, band is 3 levels" positional content of
`BandEdges.lean` (`MajorityTopEdge`, `MinorityTopEdge`, `TwoLevelOccupancy`) is now discharged to the
honest FROZEN-rule mechanism, splitting deterministic from probabilistic content.

**Hour-gated TOP edge (the headline, FULLY PROVEN).** The doubling/split move `phase3CancelSplit`
raises a level ONLY under the guard `partner.hour.val > i.val`, so the raised level `i+1 ≤
partner.hour.val` — the top edge IS the hour ceiling. `phase3CancelSplit_preserves_top_edge`: inputs
`≤ top` + all `hour.val ≤ top` ⟹ outputs `≤ top`. This is the exact mirror of the landed FLOOR
`MinorityFloorGap.cancelSplit_preserves_index_floor`, proven exhaustively over the frozen branches.
The snapshot consumer predicate is `AllBiasedMainBelow top c` (front at the band top — the within-hour
clock-front fact); from the SINGLE ceiling, `majorityTopEdge_of_hourCeiling` +
`minorityTopEdge_of_hourCeiling` produce BOTH carried top-band readouts.

**Occupancy verdict: CONDITIONAL.** `TwoLevelOccupancy` is a simultaneous-population SNAPSHOT, hence a
probabilistic timing fact — NOT a deterministic ledger. The deterministic chain content is the no-jump
SOURCE `raise_traces_to_predecessor` (mass at `i+1` traces to `i`, never skips). The snapshot is
delivered conditionally via the named event `PredecessorLevelsCoPopulated` (both levels populated at
the routing instant). This is the honest line between what the FROZEN rules give for free (the top
edge) and what needs a within-hour concentration argument (the occupancy).

**Wired:** `phase6_to_phase7_of_doubling_edges` / `phase6To7_surface_of_doubling_edges` feed
`BandEdges.phase6_to_phase7_of_seed_edges`, producing `EliminatorMargins.Phase6To7Structure σ E c`
from the seed + the one hour ceiling + the co-population event. Carried residual reduced to: hour
ceiling (deterministic clock-front front-position) + co-population timing event (probabilistic).

**Audit.** 7/7 theorems axiom-clean ⊆ [propext, Classical.choice, Quot.sound]; 0
sorry/admit/axiom/native_decide; lake env lean clean (uisai2 shm, v4.30.0 + mathlib c5ea00351c28).

---

## PaperRegime.lean — ChatGPT paper-faithfulness audit verdicts (2026-06-11)

New append-only file `Probability/PaperRegime.lean` answers the ChatGPT faithfulness audit
(`/tmp/gpt_faithfulness.out`, 2026-06-09).  Each auditor claim was VERIFIED against the actual
source BEFORE acting; the actual source wins over the auditor's reconstruction (the auditor could
not fetch `DotyParams.lean` / this doc, so several "HIGH" flags were unverified suspicions).

| # | Auditor claim | Source verdict (file:line) | Action taken |
|---|---|---|---|
| 1 | Thm 6.2 object: paper's `0.92|M'|` is MAJORITY-sign Mains at THREE exact levels `{l,l+1,l+2}`; Lean's `hConfine` is broad (both-sign, index `<L`). HIGH divergence. | **PARTIAL-RIGHT.** `UsefulMainFloor.lean:197` `hConfine = 0.92·|M| ≤ usefulMains.sum` is genuinely broad (both-sign, all index `<L`). BUT the file already documents `M' ⊆ usefulMains` (`UsefulMainFloor.lean:182,196`), and `MarginLedgers.lean:255` already carries the sign-aware `MainConfinementProfile` (`majorityProfileMass σ` / `minorityProfileMass σ`). The MISSING piece was only the **3-level restriction** `{l,l+1,l+2}`. | Defined the paper-faithful object `PaperRegime.majorityConfined3 σ l c` (majority-sign Mains at the three exact levels) + `Theorem62Paper` structure (confinement + mass-above `≤0.06|M|` + minority-small `≤0.12|M|`). PROVED the projection chain: `majorityConfined3 ≤ usefulMains` (`majorityConfined3_le_usefulMains`, needs `l+2<L`) ⟹ `theorem62Paper_implies_broad_floor` (faithful ⟹ broad `hConfine`); and `majorityConfined3 ≤ majorityProfileMass` ⟹ `mainConfinementProfile_of_paper` (faithful ⟹ the sign-aware eliminator-ledger A-shape that drives `majorityProfileMass_floor`/`4n/45`). `hConfine` re-stated honestly as the Phase-5 sampling projection of the faithful object. |
| 2 | `K=45`: paper proof needs `k=45` minutes/hour at `p=1`; Lean polymorphic in arbitrary `K`. HIGH (stronger-than-paper ⟹ probably false unless width lemmas carry `45≤K`). | **RIGHT (diagnosis), but no bug.** Confirmed: `ClockFrontShape.capMinute = K*(L+1)` and ALL §6 width/seam lemmas are polymorphic in `K` (`DotyParams.lean` threads `{L K : ℕ}` with NO `K`-lower-bound hypothesis; the headline `DotyTimeHeadline.lean:324` is polymorphic in `{L K n}`). Polymorphism over `K` means the lemmas HOLD for the paper's `K=45` (it is an instance) — not false; it is an unstated regime tie. | Added the named predicate `PaperRegime.DotyRegime n L K` collecting the regime ties in ONE inspectable place: `hLlog : L = Nat.clog 2 n`, `hK : 45 ≤ K`, `hN : N₀ ≤ n`. Documented as THE regime hypothesis to thread into the concrete headline. Accessors `DotyRegime.{L_eq_clog,K_ge_45,N₀_le,two_le_n}`. |
| 3 | `wp=3/200`: HIGH if it is a transition probability (the clock drip rate). | **WRONG.** The FROZEN protocol transition is DETERMINISTIC per pair (`Transition.lean`: every `PhaseNTransition : AgentState → AgentState → AgentState × AgentState`; no `Prob`/`PMF`/`p`-rate anywhere in `Protocol/`). The only randomness is uniform pair selection. `wp` enters ONLY as the analysis step-count `DotyParams.w n = ⌊3n/200⌋` (`DotyParams.lean:44`) and the MGF window-rung ratio `uW = 2(1+ε)·wp = 603/20000` (`DotyParams.lean:454`). It is an ANALYSIS constant, not a drip rate. Paper's "drip probability `p=1`" = the deterministic frozen rule. | Documented in `PaperRegime.lean` Part 5; closed with the proven identity `wp_is_analysis_constant : DotyParams.uW = 2·(1+1/200)·(3/200)` exhibiting `wp` purely as an MGF quantity. |
| 4 | `L = ⌈log₂ n⌉` carried only in comments, not as a hypothesis. Medium. | **RIGHT.** `AgentState` carries `L` as a bare parameter (comments say `L=⌈log₂n⌉`); the headline does not tie it. | Included as `DotyRegime.hLlog : L = Nat.clog 2 n` (`Nat.clog 2 n = ⌈log₂ n⌉`). |

**Build/audit.** `Probability/PaperRegime.lean` — single-file `lake env lean` clean + `lake build`
target EXIT 0 (3417 jobs, uisai2 /dev/shm, v4.30.0 @ mathlib c5ea0035). All exported theorems
`#print axioms ⊆ [propext, Classical.choice, Quot.sound]`; 0 sorry/admit/axiom/native_decide;
lint-clean (no longLine in this file). Append-only; no existing file edited.

**Scope note (honest).** `PaperRegime.lean` is a *surface*/*definitions* file: it states the
paper-faithful object and PROVES the deterministic projections (faithful ⟹ broad floor; faithful ⟹
sign-aware A-shape; the regime predicate; the wp identity). It does NOT discharge the probabilistic
CONTENT of Theorem 6.2 (`hConfine3`/`hMassAbove`/`hMinoritySmall` remain carried whp facts inside
`Theorem62Paper`, exactly as `hConfine` was carried in `UsefulMainFloor`) — that bias-ledger
collapse is the same genuinely-new probabilistic residual flagged in `UsefulMainFloor.lean`'s header.
What changed: the carried object is now the paper-faithful majority-sign 3-level one, the broad floor
is a PROVEN consequence of it, and the regime ties are collected in one named predicate.

---

## SampledClassTail.lean — Lemma 7.1 sampled-class concentration re-based on the KILLED gate (2026-06-11)

New append-only file `Probability/SampledClassTail.lean` attacks the slot-5 `hConc` carry that
`EndpointWiring.lean` pinned to provenance (the Lemma-7.1 sampled-class floor tail
`(Kᵗ) c₀ {¬sampledFloor i K₀} ≤ εConc`).  The landed per-step pieces (MGF drift
`Phase5Convergence.sampledClass_windowDrift_contraction`, threshold link `sampledFloor_link`) did
not assemble via `WindowConcentration.windowDrift_PhaseConvergence` for two reasons recorded in
the survey: (a) `Phase5AllWin` not absorbing; (b) the rate floor `hrfloor`.

**Superwindow re-base VERDICT: FALSE for the contraction direction (verified vs FROZEN rules).**
The prompt's route — re-base on the absorbing superwindow `PhaseGE5Win` and claim the sampled-class
count is FROZEN on the phase-≥6 part — does NOT hold.  `sampledReserveClass i a := a.role =
Role.reserve ∧ a.hour.val = i` (`Phase5Convergence:278`).  `Phase6Transition` (`Transition.lean:1209`)
routes a Reserve+Main pair through `doSplit` (`:1154`), whose FIRST output sets `role := .main`
(`:1160`).  So a class-`i` Reserve that splits FLIPS role reserve→main and is REMOVED from
`sampledReserveClassU i` — the count strictly DECREASES on a phase-6 split, so the deficit potential
`Φ = exp(−s·N)` can RISE, breaking `∫Φ dK ≤ ρ·Φ`.  The superwindow is absorbing but NOT a drift
carrier (exactly the obstruction `Phase5Convergence.lean:1041-1046` already records).  Frozen-profile
note: the *static Main bias profile* IS frozen on Phase 5 (`biasedMainClassU_support_eq`,
`Phase5Convergence:364`), but the *sampled Reserve class count* is NOT frozen across phase 6.

**The HONEST re-base: the KILLED-AFFINE engine** (`GatedDrift.real_window_killed_affine`,
`KilledAffineTail.lean`).  Gate `G := Phase5AllWin n` carries the drift where it genuinely holds; the
killed kernel `killK_now K G` absorbs STRUCTURALLY (cemetery `killΦ = 0`), removing the absorption
obstruction (blocker (a)) with NO false freeze claim.  Landed (all axiom-clean):

| Theorem | Content |
|---|---|
| `sampledClassDrift_on_gate` | per-step multiplicative drift `∫Φ dK ≤ ρ·Φ + 0` on the gate (lift of `sampledClass_windowDrift_contraction`; rate floor `hrfloor` threaded) |
| `sampledClass_killed_tail` | **pure killed tail, NO escape, NO exit bridge**: floor-failure mass ≤ `ρᵗ·Φ(c₀)/θ`, `θ=exp(−s·K₀)`, `ρ=ofReal(1−r(1−e^{−s}))`. Decays when `ρ<1`. Blocker (a) dissolved. |
| `sampledClass_real_window` | real chain ≤ killed tail + escape prefix `∑_{τ<t}(Kᵀ)c₀{θ≤Φ}`, via `real_window_killed_affine`; the exit bridge (clock-separation) carried as explicit hypothesis |
| `hConcDemand_of_real_window` | produces the exact `EndpointWiring.hConcDemand` shape from `hrfloor` + exit bridge + uniform per-τ escape bound + arithmetic fit |

**How much of hConc closed.**  The ABSORPTION obstruction (blocker (a)) is RESOLVED — the pure
killed tail is fully landed (axiom-clean) from the rate floor alone.  Two GENUINELY-probabilistic
residuals remain, now carried as explicit NAMED hypotheses with file:line provenance (pinned, not
hidden): (b) the rate floor `hrfloor` (the in-house Chernoff rise-probability content) and the
clock-timing escape (the Phase-5/Phase-6 separation — paper footnote 11 / Lemma 5.2 — since leaving
`Phase5AllWin` is the clock-advance event, NOT a `sampledReserveClassU`-threshold, the exit bridge is
not manufacturable from the count alone).  `hConcDemand_of_real_window` turns the opaque `hConc`
carry into an explicit assembler consuming exactly those two atoms.

**Build/audit.**  Single-file `lake env lean` clean (local v4.30.0 olean closure, mathlib
c5ea0035).  All four exported theorems `#print axioms ⊆ [propext, Classical.choice, Quot.sound]`;
0 sorry/admit/axiom/native_decide; `git diff --check` clean; max line width 100. Append-only; no
existing file edited.

## PositionalCluster.lean — §6 hour-ceiling consequence + occupancy honest core (2026-06-11, wave C)

The last POSITIONAL cluster: the carried snapshots riding on the clock-front / hour machinery.
Append-only; no existing file edited.  Single-file `lake env lean` clean; all 11 exports
`#print axioms ⊆ [propext, Classical.choice, Quot.sound]`; 0 sorry/admit/axiom/native_decide;
`git diff --check` clean; max line width 100.

### Item 1 — the hour-stamp ceiling `MainHourBelow (l+2)`: VERDICT = clock-front consequence.

The Main `hour` FIELD is written by exactly TWO frozen mechanisms (verified `Protocol/Transition.lean`):

1. the **Phase-3 Rule-2 Main-Clock drag** (`HourCoupling.phase3_drag_left`/`_right`):
   `hour := min L (clock.minute / K)`.  Under the landed clock-front confinement
   `ClocksBelowHour h` (every clock `minute < (h+1)·K`, i.e. `¬ HourCoupling.clockAboveP h`) the
   floor arithmetic `dragStamp_le_of_clockBelow` gives `min L (minute/K) ≤ h`.  So the drag stamps the
   Main `hour ≤ h` BY the clock front being below hour `h+1` — the honest content of the carried
   "hour stamps ≤ current hour index".  `dragLeft_mainHour_le` / `dragRight_mainHour_le` PROVE this.

2. the **Phase-3 Rule-3 cancel** branch of `phase3CancelSplit` (Transition.lean:583/587):
   `hour := i` (the agent's OWN exponent index).  This COUPLES the hour ceiling to the INDEX ceiling:
   `mainHour_le_of_clockBelow_cancelSplit` proves `phase3CancelSplit` preserves `hour ≤ top` GIVEN
   both `hour ≤ top` AND `index ≤ top` (the index ceiling `AllBiasedMainBelow top`) on the inputs.
   This is the honest subtlety the audit-table did not name: unlike the index top-edge
   (`DoublingEdges.phase3CancelSplit_preserves_top_edge`), the hour ceiling genuinely NEEDS the index
   hypothesis, because the cancel re-stamps `hour := index`.  The Rule-4 split writes only `bias`
   (hour untouched); identity branches preserve.

`mainHourBelow_step_mainMain` assembles the clock-free (Main×Main) step: the move is exactly
`phase3CancelSplit`, so the hour ceiling propagates one step from the index ceiling alone.

**Hour-ceiling derivation verdict.**  `MainHourBelow (l+2)` is NOT an independent carry — it is a
CONSEQUENCE of the SAME two facts the index ceiling `AllBiasedMainBelow (l+2)` rides on: the
clock-front confinement `ClocksBelowHour (l+2)` (drag side) + the index ceiling (cancel side, the
coupling).  One clock-front confinement event drives BOTH snapshots; the hour snapshot's
reachability form is exactly the index ceiling's reachability form.  The per-agent
`BiasedMainIndexLeHour` stays FALSE-step (`CeilingRoute.biasedMainIndexLeHour_not_step_preserved`,
unchanged); the GLOBAL hour ceiling the corrected `CeilingRoute` surface needs IS the step-preserved
clock-front consequence.  `phase6To7_surface_positional` re-exports the corrected surface fed the
genuinely-step-preserved index ceiling.  (The FULL `Phase3Transition` step — incl. clock×clock
minute dynamics, reserve/mcr/cr roles, `stdCounterSubroutine` — lives in `HourCouplingV2`'s `Window`
supermartingale; we expose the two load-bearing hour-writing mechanisms, which is what the consumer
rides on.)

### Item 2 — occupancy honest core: per-live-minority-level, NOT both-levels-unconditional.

Re-reading the ACTUAL consumer `EliminatorMargins.Phase6To7Structure` (def line 191):
`∀ j, 1 ≤ minorityAt7 σ j → ∃ i, i+1 = j ∧ E ≤ elimGap1 σ i` — the PER-LIVE-MINORITY form (for each
live `j`, mass at the SPECIFIC predecessor `j−1`), definitionally `BandLocalization.MajorityBandAtGap1`.

**Honest core.**  The carried `BandEdges.TwoLevelOccupancy` (BOTH `{l,l+1}` carry `≥ E`) is needed
ONLY when the minority STRADDLES both band levels `{l+1, l+2}`.  When the minority collapses to a
SINGLE level `j₀` (the common case under the doubling drain), the consumer needs occupancy at the
SINGLE predecessor `j₀−1` alone — `majorityBandAtGap1_of_single_level` PROVES this.

**Honest constants (proved).**  Pigeonhole of the global majority budget
`MarginLedgers.majorityProfileMass_floor = 4n/15` over the 2-element predecessor set `{l,l+1}` gives
ONE level `≥ 2n/15`; `single_level_E_le_consumer` admits `E ≤ 2n/15` into the consumer's `E ≤ 4n/15`.
BOTH levels at the per-level share `E = 2n/15` consume `2·(2n/15) = 4n/15` — EXACTLY the global
budget, the BOUNDARY case (`twoLevel_E_boundary_exact : 2·(2n/15) = 4n/15`, zero slack).  So
two-level occupancy is honest only AT the budget boundary; the per-level (single-pigeonhole-level)
form is the genuinely-minimal honest surface.

### Item 3 — the narrowest surface.

`phase6To7_surface_perLevel` routes through `BandLocalization.Phase6BandPositionFacts` (per-level
band position) — strictly narrower than the carried `TwoLevelOccupancy` (which forces BOTH `{l,l+1}`
regardless of where the minority sits): it needs occupancy ONLY at the actually-occupied predecessor
levels.  `phase6To7_surface_singleLevel` is the minimal end-to-end discharge for the single-level
minority (occupancy at ONE predecessor, fed `E ≤ 2n/15`, no boundary-case appeal).

---

## AtomsV2 — the F4/F5/F6 honesty re-cut (final adversarial audit `/tmp/codex_final_audit.md`)

_Appended 2026-06-11.  New append-only file `Probability/AtomsV2.lean` (0-sorry, axiom-clean,
single-file `lake env lean` verified).  Owns the ATOMS/EXPECTED side; the concurrent
`FinalAssemblyV2.lean` owns the disjoint assembly side (no overlapping names — `AtomsV2` namespace,
all decls `…V2`/`…_v2`/`…_numeral`)._

### F4 — global `hBranch` oracle → per-slot regime data atom (PRODUCED, not bound)

`FinalAssembly.doty_theorem_3_1_expected` carried the global
`hBranch : ∀ b, Reachable → notDone → ChainEndBranch n init b Brecover (βfinal b)` as a free binder —
an oracle the off-event has no deterministic discharge for (proven dishonest, `BranchAndBudget` Part 4
/ `HANDOFF_HLADDER`).  The fix moves the classification INTO the bundle as the precisely-scoped atom:

* `SlotRegimeData n init b Brecover βfinal` — the per-reachable-not-done-state FINITE regime data
  (`Sum`-type): a timed-slot `BranchAndBudget.ChainSlotData` witness, OR an `S1` phase-10-majority
  dispatch witness, OR a `Tie1plus` phase-10-tie dispatch witness.  Inspectable finite per-slot data,
  NOT a global `ChainEndBranch`.
* `branchOfSlotRegime` PRODUCES `ChainEndBranch` from that data via the landed on-chain builders
  `BranchAndBudget.branch_of_slot` / `branch_of_phase10_{majority,tie}` (a `def`, i.e. theorem).
* `DotySlotClassifier` = the per-state supply of `SlotRegimeData`; `branchOfClassifier` produces the
  full global `hBranch` content from it.
* `doty_theorem_3_1_expected_v2` is the de-freed expected theorem: same conclusion, but the global
  oracle is REPLACED by `hSlotClass : DotySlotClassifier …`, from which `hBranch` is produced and
  threaded to `FinalAssembly.doty_theorem_3_1_expected`.  The genuinely-open content is now the
  finite per-slot regime data, not a global oracle.

### F5 — numeral constants pinned + K/N threaded

* **(a) numerals.**  Dominant per-instance window = the honest slot-8 re-cut `α₈' = 14/75`, horizon
  `(3/α₈')·n·log n = (225/14)·n·log n ≈ 16.07·n·log n`.  `BranchAndBudget.recut_window_coeff_bounds`
  proves `16 < 225/14 < 17`, so the honest integer ceiling is `C0 = 17` (`C0_numeral`, certified
  above the re-cut window by `C0_numeral_above_recut`).  `Cbad = 3` (`Cbad_numeral`) is the phase-10
  majority backup cap `3·n²·(1+2 log n)` (larger of maj `3` / tie `2`).  Delivered:
  `doty_theorem_3_1_whp_numeral` (`T ≤ 21·17·n·(L+1)`, failure `≤ 21/n²`) and
  `doty_theorem_3_1_expected_numeral` (`E[T] ≤ (21·17 + 4·3)·n·(L+1) = 369·n·(L+1)`), both with the
  `clog` form, at LITERAL constants.
* **(b) K/N threading.**  `regime_threads_K` (`45 ≤ K`, the §6 minutes/hour width tie) and
  `regime_threads_N` (`DotyParams.N₀ ≤ n`, the finite-`n` floor) consume `hReg.hK` / `hReg.hN` —
  live, not dead.  `regime_two_le_n` derives `2 ≤ n` from the threaded regime.

### F6 — opaque-instance / hx₀ / h_post

* **(a)/(b) hx₀.**  `(phases' ra ⟨0⟩).Pre = work0.Pre`; slot 0 is `EndpointWiring.roleSplitW_of_two_stage`
  (`Pre = stage1.Pre`).  The honest start is a `Phase0Initial`-flavoured `Pre`; the bridge is the
  identity on the slot-0 `Pre` pin (carried as `hx₀`, derivable from the initial config through the
  slot-0 `Pre` interface — no extra residual beyond the start pin).
* **(c) h_post — the honest VERDICT (genuine residual).**  `(phases' ra ⟨20⟩).Post = Phase10Post`
  (slot-10 = `Phase10Drop.phase10Convergence`, `Post = ∃ o, ∀ a ∈ c, phase=10 ∧ output=o`).  This does
  NOT imply `majorityStableEndpoint`: the disjunct is `phase10MajorityWitness init c`, which requires
  the agreed output `o` to MATCH the init-gap sign (`.A`/`.B`/`.T` for `gap >`/`<`/`= 0`).  `Phase10Post`
  leaves `o` unpinned.  So `h_post` is a GENUINE residual: the conserved gap-sign match
  `Phase10SignMatch` (the chain-conserved `phase10ActiveSignedSum = initialGap`,
  `BackupEntry.arrival_classification`) is carried, and `postOfSign` PRODUCES `h_post` from it.  Verdict
  recorded honestly: NOT freely dischargeable from `Phase10Post` alone.

### Axiom audit

All new decls (`doty_theorem_3_1_expected_v2`, `_whp_numeral`, `_expected_numeral`,
`branchOfClassifier`, `branchOfSlotRegime`, `postOfSign`, `C0_numeral_above_recut`,
`regime_threads_{K,N}`) `#print axioms ⊆ [propext, Classical.choice, Quot.sound]`.  No
sorry/admit/axiom/native_decide.

---

## Round-2 unification rebase — `FinalAssemblyV3.lean`

Round-2 audit (`/tmp/codex_final_audit2.md`) confirmed `FinalAssemblyV2.doty_theorem_3_1_whp_v2` is a
genuine whp repair (no free `hcompFail`; bound PRODUCED through
`BudgetTightening.doty_time_headline_W2_inv_sq`; slots 1/5/7/8 on the levels engine) but pinned the
residual items as cross-file debt: the numeral whp corollary was still an IMPOSTOR (old `FinalAssembly`
+ `hcompFail`), the expected theorem a FRAGMENT (old `FinalAssembly.DotyResidualAtoms`/`phases'`),
`hStart`/`hPhase10Sign` documented but unwired, K/N threading dead, and `WorkInputsHonest.hM₀` a true
dead field.  `FinalAssemblyV3.lean` performs the unification rebase, append-only.

### What was wired vs honestly documented

* **(item 1) numeral whp rebased onto V2** — `doty_theorem_3_1_whp_numeral_v3` :=
  `FinalAssemblyV2.doty_theorem_3_1_whp_v2` at `C0 = AtomsV2.C0_numeral = 17`.  NO `hcompFail`
  anywhere; the bound is produced through the V2 path.  (Replaces AtomsV2's IMPOSTOR corollary.)
* **(item 2) expected rebased onto the honest work family** — `doty_theorem_3_1_expected_v3` feeds the
  GENERIC capstone `ChainEndRecut.doty_expected_time_chain_end'` the family `FinalAssemblyV2.phases'V2
  ra.v2` (levels-engine `dotyWorkHonest`) + the V2 chain map `FinalAssemblyV2.phases'V2_h_chain`; the
  global `hBranch` is PRODUCED from `AtomsV2.DotySlotClassifier` via `AtomsV2.branchOfClassifier`.
  Numeral corollary `doty_theorem_3_1_expected_numeral_v3` at `(21·17 + 4·3) = 369`.  (Replaces
  AtomsV2's FRAGMENT, which still threaded `FinalAssembly.DotyResidualAtoms`/`phases'`.)
* **(item 3a) `hStart` WIRED** — the V3 bundle carries `hStart : Phase0Initial n c₀` + the slot-0
  `Pre` pin `hWork0PreOfStart`; `hx₀_of_start` PRODUCES `(phases'V2 ra.v2 ⟨0⟩).Pre c₀` through
  `slot0_pre_pin` (`(phases'V2 ra ⟨0⟩).Pre = work0.Pre`, reduced past the `irreducible`
  `dotyWorkHonest` by `unfold`).  The free `hx₀` binder is GONE from the V3 surfaces.
* **(item 3b) `hPostOfSign` WIRED** — the V3 bundle carries `hPhase10Sign : AtomsV2.Phase10SignMatch
  init`; `h_post_of_sign` PRODUCES `h_post` via `AtomsV2.postOfSign` through `slot20_post_pin`
  (`(phases'V2 ra ⟨20⟩).Post → Phase10Post`).  The free `h_post` binder is GONE from the V3 surfaces.
* **(item 4) K/N threading — HONESTLY DOCUMENTED, not fake-threaded.**  Survey of the V2 work slots
  (`slot1Honest` / `slot5Honest` / `slot7Honest` / `slot8Honest` / `slot5DrainLevels`): every
  constructor takes `2 ≤ n` only — NONE carries a `45 ≤ K` or `N₀ ≤ n` hypothesis.  No
  `DotyResidualAtomsV2` field consumes them either.  So there is NO current instance hypothesis that
  genuinely needs `hReg.hK` / `hReg.hN`; threading them would be a binder consumed nowhere (dishonest).
  `hK_hN_threading_status` records that the helpers are derivable from `hReg` (available, not
  fabricated), while the V3 theorems honestly consume only `hReg.hLlog` (once, for the `clog` form).
* **(item 5) dead `hM₀` ABSORBED (honest deadness record).**  `FinalAssemblyV2.WorkInputsHonest.hM₀ :
  (M₀ : ℝ) ≤ n` is never referenced on the proof-term chain.  The V3 surfaces never read it; it is
  dead V2-internal debt.  Append-only discipline forbids editing the V2 structure, so the field
  remains physically present, but it is provably absent from the V3 final-theorem proof terms
  (documented in `hM₀_is_dead` prose; the V3 bundle's content is start/sign atoms + the V2 work-family
  interface, none touching `hM₀`).

### V3 final-surface binder table (zero unexplained binders)

Classification key: **regime** = `DotyRegime` size/log pins; **residual-bundle** = the V3 residual
atoms (`DotyResidualAtomsV3`, which embeds `DotyResidualAtomsV2` + start/sign); **boilerplate** =
measurability / absorbing / positivity / reachability plumbing; **arithmetic** = time/budget/mass
inequalities consumed by the composition.

#### `doty_theorem_3_1_whp_numeral_v3` (6 binders)

| binder | class | role |
|---|---|---|
| `hReg : DotyRegime n L K` | regime | the `clog` form (`hReg.hLlog`: `L = ⌈log₂ n⌉`); only `hLlog` consumed |
| `ra : DotyResidualAtomsV3 n 17` | residual-bundle | the V2 honest-path atoms + `hStart`/`hPhase10Sign` (PRODUCE `hx₀`/`h_post`) |
| `T : ℕ` | arithmetic | the opaque sum horizon |
| `hT : T = ∑ i, (phases'V2 ra.v2 i).t` | arithmetic | folds the produced bound to `T` |
| `ht : ∀ i, (phases'V2 ra.v2 i).t ≤ ra.v2.Cphase i · n · (L+1)` | arithmetic | per-instance time budget |
| `hε : ∀ i, (phases'V2 ra.v2 i).ε ≤ ra.v2.δ i` | arithmetic | per-instance failure budget |

No free `hcompFail` (item 1); no free `hx₀` / `h_post` (item 3, produced in-bundle).

#### `doty_theorem_3_1_expected_v3` (12 binders)

| binder | class | role |
|---|---|---|
| `hReg : DotyRegime n L K` | regime | the `clog` form (`hReg.hLlog`); only `hLlog` consumed |
| `ra : DotyResidualAtomsV3 n C0` | residual-bundle | V2 honest atoms + `hStart`/`hPhase10Sign` |
| `hc₀Reach : ReachableFrom L K init c₀` | boilerplate | reachable-relative conditioning surface |
| `ht : …t ≤ Cphase·n·(L+1)` | arithmetic | per-instance time budget |
| `hε : …ε ≤ δ` | arithmetic | per-instance failure budget |
| `hDone : MeasurableSet (StableDone …)` | boilerplate | hitting-set measurability |
| `hDoneAbs : ∀ x ∈ StableDone, K x (StableDone)ᶜ = 0` | boilerplate | `StableDone` absorbing |
| `hBpos : 0 < Brecover` | boilerplate | recovery-cap positivity |
| `βfinal : Config → ℝ≥0∞` | residual-bundle | per-state recovery budget function (branch param) |
| `hSlotClass : DotySlotClassifier n init Brecover βfinal` | residual-bundle | F4 per-slot regime data (PRODUCES `hBranch`) |
| `hδ : ∑ i, δ i ≤ 1/n` | arithmetic | aggregate failure mass |
| `hrecmass : (1/n)·(2·Brecover)·(1−1/2)⁻¹ ≤ 4·Cbad·n·(L+1)` | arithmetic | split-geometric recovery mass cap |

No free `hBranch` (F4, produced from `hSlotClass`); no free `hx₀` / `h_post` (item 3, produced
in-bundle).  The family is `phases'V2` (levels-engine honest work), not the old crude `phases'`
(item 2).

### Axiom audit

All V3 decls (`doty_theorem_3_1_whp_numeral_v3`, `doty_theorem_3_1_expected_v3`,
`doty_theorem_3_1_expected_numeral_v3`, `slot0_pre_pin`, `slot20_post_pin`, `hx₀_of_start`,
`h_post_of_sign`, `hK_hN_threading_status`) `#print axioms ⊆ [propext, Classical.choice, Quot.sound]`
(`hK_hN_threading_status` only `propext`).  No sorry/admit/axiom/native_decide; single-file
`lake env lean` clean (no warnings).

---

## ATOM CAMPAIGN ROSTER — discharging `DotyResidualAtomsV3` toward a FAITHFUL Theorem 3.1 (2026-06-11)

Strategy pass (read-only survey; NO Lean written). Goal: enumerate EVERY non-arithmetic /
non-boilerplate carried field reachable from the two V3 final theorems
(`FinalAssemblyV3.doty_theorem_3_1_{whp_numeral,expected}_v3`), give each its exact statement
(file:line), landed machinery, classification, and a ranked attack order.

### Classification key

- **(A) dischargeable-from-landed** — the discharger already exists axiom-clean; only wiring /
  an adapter / a structure-field instantiation is needed. No new math.
- **(B) one-engine-instantiation away** — the engine + protocol facts exist; one honest
  instantiation (or one residual side-condition discharge) is needed.
- **(C) genuinely-new probability** — the missing mathematical object does not exist yet; state
  the paper section.
- **(D) primitive regime / start input** — belongs in `DotyRegime` / the initial-config shape;
  not a dischargeable residual (it is an honest hypothesis about the problem instance).

### Where the open content lives (3 nested buckets, all under `DotyResidualAtomsV3`)

`DotyResidualAtomsV3 n C0` = `{ v2 : DotyResidualAtomsV2, hStart, hWork0PreOfStart, hPhase10Sign }`
(`FinalAssemblyV3.lean:117-131`). `v2 : DotyResidualAtomsV2` (`FinalAssemblyV2.lean:460-494`) =
`{ wih : WorkInputsHonest, seam feeders/bridges, Cphase/δ/c₀/init/hC0/hδ }`. `wih : WorkInputsHonest`
(`FinalAssemblyV2.lean:325-422`) = the per-slot probabilistic atoms. The expected theorem additionally
takes `hSlotClass : DotySlotClassifier` (`FinalAssemblyV3.lean:197`, the F4 branch oracle).

### The roster

| # | Atom (field) | Statement file:line | Consumers | Landed machinery (wave) | Class |
|---|---|---|---|---|---|
| 1 | `hDrift` (seam epidemic drift) | `FinalAssemblyV2.lean:467` (= `DotyAssembly'.hDrift`, `SeedTrigWiring.lean:319`) | `toAssembly'V2` → `dotyPhases'` seam instances → whp composition | **`SeamEpidemics.seam_drift` (SeamEpidemics:1093)** PRODUCES exactly this shape, axiom-clean, modulo the Phase-4-shape tail check `hε` (pure arithmetic on `s,t,ε`). `seamEpidemicW_calibrated` (:1129) is the ready wrapper. | **A** |
| 2 | `hWorkPostToWindow` (work.Post → allPhaseGe) | `FinalAssemblyV2.lean:479` | seam→work bridge in `dotyPhases'` | **`AssemblyBridges.mk_hWorkPostToWindow` (AssemblyBridges:233)** builds it from a per-slot card/phase pin (`work.Post → card=n ∧ phase=seamP k`). Deterministic; the pin is a `Post`-shape read each honest slot already has. | **A** |
| 3 | `hWindowToWorkPre` (allPhaseEq → next work.Pre) | `FinalAssemblyV2.lean:486` | seam→work entry in `dotyPhases'` | **`AssemblyBridges.mk_hWindowToWorkPre_pin` (AssemblyBridges:249)** delivers the card/phase pin half. PARTIAL: the drain-budget / role / sign entry pins per phase are carried separately (the per-phase `Pre` content). Wiring + the small per-phase entry adapters. | **A** (card/phase) / **B** (per-phase entry pins) |
| 4 | `hSeedStep` (one-step advTriggered seed) | `FinalAssemblyV2.lean:482` | seed rung in `dotyPhases'` | **`SeedRungs.drained_kernel_seedTarget_compl_zero` (SeedRungs:319)** proves the one-step a.s. seed (`kernel c (seedTarget)ᶜ = 0`) for `p ∈ {0,1,5,6,7,8}` from `AllClockGEpCard ∧ drained ∧ unseeded`. The `advTriggered = 0` shape is `advTriggered_iff_geCount` (SeamEpidemics:1076) away. Adapter: connect `work.Post` ⟹ the drained/unseeded guard. | **A**/**B** |
| 5 | `hNoOvershoot` (seam clock no-overshoot) | `FinalAssemblyV2.lean:473` (= `DotyAssembly'.hNoOvershoot`, `SeedTrigWiring.lean:325`) | seam instances → whp composition | **`SeamNoOvershoot.seam_noOvershoot_tail` (SeamNoOvershoot:731)** + `hNoOvershoot_one_seam` (:763) produce the shape, modulo TWO residuals: (a) `DetSeamOvershootBridge p` — **DISCHARGED** by `SeamOvershootBridge.detSeamOvershootBridge_of_wf` (:1607) from seam-region `Wf` reachability invariants; (b) the per-τ `AtRiskClockZero ≤ exp(−40(L+1))` clock-zero tail — NOT yet landed as a kernel bound. | **B** ((a) done; (b) is the open within-seam clock-zero concentration) |
| 6 | `hPhase6Post7` (slot-7 gap-1 eliminator margin, Lemma 7.4) | `FinalAssemblyV2.lean:403` | `slot7Honest` → `slot7_hdrop_direct` → levels engine | **§6 doubling cluster landed**: `DoublingEdges.phase6To7_surface_of_doubling_edges` (:289) + `PositionalCluster.phase6To7_surface_perLevel/singleLevel` (:268/:282) produce `Phase6To7Structure` from the hour-ceiling (deterministic clock-front) + a co-population / per-level occupancy event. The hour ceiling is PROVEN; the occupancy is the carried within-hour timing event. | **B** (occupancy/co-population timing event is the one probabilistic instantiation) |
| 7 | `hPhase7Post8` (slot-8 above-level eliminator margin, Lemma 7.6) | `FinalAssemblyV2.lean:412` | `slot8Honest` → `slot8_hdrop_direct` → levels engine | `EliminatorMargins.Phase7To8Structure` (:202) is the consumer; `lemma7_6_phase8_elimAbove_floor` is landed. The margin's existence (above-level minority mass ≥ E8) is the same §6 doubling-drain positional content as #6, one level up — no dedicated surface theorem landed yet (mirror of #6). | **B** |
| 8 | `hmain5` + `P5` (slot-5 Theorem-6.2 biased-Main floor) | `FinalAssemblyV2.lean:376` | `slot5Honest` → `slot5DrainLevels` → `DrainRates.hdrop5_of_chain` | **`UsefulMainFloor.theorem6_2_usefulMains_floor` (:207)** PRODUCES `P ≤ usefulMains.sum` from `Theorem62EntryHypotheses` + `P ≤ 23n/75`. The named entry hypotheses' `hConfine` (the broad both-sign floor) is the carried whp fact; `PaperRegime.theorem62Paper_implies_broad_floor` shows it follows from the paper-faithful `majorityConfined3`. The bias-ledger collapse delivering `hConfine`/`majorityProfileMass_floor` is genuinely-new. | **C** (Doty §6 / Thm 6.2 bias-ledger collapse) |
| 9 | `hConc` + `εConc` (slot-5 Lemma 7.1 sampled-class concentration) | `FinalAssemblyV2.lean:383` | `slot5Honest` convergence (union with drain) | **`SampledClassTail` wave landed** the pure killed tail (`sampledClass_killed_tail` :135, absorption blocker dissolved, axiom-clean) and `hConcDemand_of_real_window` (:233). TWO genuinely-probabilistic residuals remain as named hypotheses: (b) the rate floor `hrfloor` (in-house Chernoff rise-probability) + the Phase-5/6 clock-separation exit bridge. | **C** (Doty Lemma 7.1 / footnote 11 + Lemma 5.2 clock-separation) |
| 10 | `hext1` / `hpull1` + `P1` (slot-1 extreme + partner-pool floors, Lemma 5.3 / [45]) | `FinalAssemblyV2.lean:353` / `:356` | `slot1Honest` → `DrainRates.hdrop1_of_chain` | `hext1` (`1 ≤ extremePos.sum`) is a structural saturation floor (persistence-carried). `hpull1` (`P1 ≤ pullPos.sum`) is Lemma 5.3 partner-pool; `EliminatorMargins.phase1_pullPos_floor_of_mainCount_and_saturated_bound` (:168) is the landed floor adapter — needs the saturated-main count instantiation. | **B** (hpull1 via landed adapter) / **C** (hext1 persistence is structural-but-carried) |
| 11 | `hdrop6` + `q6` (slot-6 Phase-6 band drain per-level rate) | `FinalAssemblyV2.lean:392` | `dotyWorkHonest` slot 6 → `phase6Convergence_calibrated` | The §6 band-drain levels engine; the per-level rate `q6` is the carried Phase-6 drain probability (the within-band doubling-drain rate). Same engine as slots 1/5/7/8, carried abstractly here. | **C** (Doty §6 Phase-6 drain rate; the core §6 width content) |
| 12 | `hStart : Phase0Initial n c₀` + `hWork0PreOfStart` | `FinalAssemblyV3.lean:122` / `:126` | `hx₀_of_start` → slot-0 `Pre` | `Phase0Initial n c := card=n ∧ ∀a, phase=0 ∧ role=mcr` (`RoleSplitConcentration:165`) — the all-`mcr` phase-0 START shape. This is an honest fact ABOUT the initial configuration, not a residual to prove. `hWork0PreOfStart` is the slot-0 `Pre = Phase0Initial`-flavoured pin (deterministic interface). | **D** (start) / `hWork0PreOfStart` is **A** (slot-0 `Pre` interface) |
| 13 | `hPhase10Sign : Phase10SignMatch init` | `FinalAssemblyV3.lean:131` (def `AtomsV2.lean:142`) | `h_post_of_sign` → `postOfSign` → slot-20 `Post` → endpoint | `Phase10SignMatch init := ∀c, Phase10Post c → phase10MajorityWitness init c` (agreed output matches init-gap sign). On the good chain this is the conserved `phase10ActiveSignedSum = initialGap`; **`BackupEntry.arrival_classification` (:189)** produces the `S1`/`Tie1plus` sign classification from `validInitial + Reachable + AllPhase10 + 0 ≤ gap`. The full sign-match conservation is the Doty §11 phase-10 backup-entry argument. | **C** (Doty §11 phase-10 sign conservation) |
| 14 | `hSlotClass : DotySlotClassifier n init Brecover βfinal` (EXPECTED only) | `FinalAssemblyV3.lean:197` (def `AtomsV2.lean:109`) | `branchOfClassifier` → `hBranch` → `doty_expected_time_chain_end'` | Per-reachable-not-done-state supply of `SlotRegimeData` (a `ChainSlotData`, or a phase-10 maj/tie dispatch witness). `branchOfClassifier` (`AtomsV2:118`) PRODUCES `hBranch` axiom-clean from it via the landed `branch_of_slot` / `branch_of_phase10_*` builders. The OPEN content = the per-state slot regime data exists for every off-trajectory state (the §6/§11 off-event regime cover). | **C** (the genuine expected-side open content: off-event slot dispatch — Doty §5–§11 chain-end regime cover) |
| 15 | `work0` / `work2` / `work3` / `work9` (carried opaque `PhaseConvergenceW` instances) | `FinalAssemblyV2.lean:344-347` | `dotyWorkHonest` slots 0/2/3/9 | Structural phases (role-split, doubling seed, band-init, pre-phase-10). Named constructors exist (`EndpointWiring.roleSplitW_of_two_stage` for slot 0, `phase3Convergence_bounded`, etc.); each carried as a finished instance. Instantiating them faithfully = wiring the landed per-phase constructors with their own residuals (recursively classified, mostly structural). | **B** (named constructor instantiation, residuals mostly structural) |
| — | `hM₀ : (M₀:ℝ) ≤ n` (DEAD field) | `FinalAssemblyV2.lean:342` | NONE (provably unread on the V3 proof-term chain) | Dead V2-internal debt; recorded honestly in `hM₀_is_dead`. Removed by a future non-append V2 re-cut. NOT a residual. | — (dead) |

### Ranked attack order

**Wave 1 — the (A) quick wins (deterministic seam wiring; no new math).** Discharge the seam
feeders/bridges that already have axiom-clean producers; this collapses the seam half of
`DotyResidualAtomsV2` to pure arithmetic side-conditions:
1. **#1 `hDrift`** ← `seam_drift` / `seamEpidemicW_calibrated` (adapter only).
2. **#2 `hWorkPostToWindow`** ← `mk_hWorkPostToWindow` (per-slot card/phase pin read).
3. **#3 `hWindowToWorkPre`** (card/phase half) ← `mk_hWindowToWorkPre_pin`.
4. **#12 `hWork0PreOfStart`** (slot-0 `Pre` interface) — deterministic pin.
5. **#5(a) `DetSeamOvershootBridge`** ← `detSeamOvershootBridge_of_wf` (already landed; just thread `Wf`).
   These five share one wiring file and let the seam composition close on landed terms.

**Wave 2 — the (B) one-instantiation items, by downstream weight.** Each gates a whole slot or
the no-overshoot seam:
6. **#5(b) `AtRiskClockZero` clock-zero tail** — highest weight (gates EVERY seam's `hNoOvershoot`,
   10 seams); one within-seam clock-zero concentration bound (`≤ exp(−40(L+1))` per step).
7. **#6 `hPhase6Post7`** (slot-7 eliminator margin) — gates slot 7; instantiate the landed
   `phase6To7_surface_singleLevel` with the single-level occupancy event.
8. **#7 `hPhase7Post8`** (slot-8) — mirror of #6 one level up; build the Lemma-7.6 above-level surface.
9. **#10 `hpull1`** (slot-1 partner-pool) — instantiate `phase1_pullPos_floor_…` with the saturated-main count.
10. **#15 `work0/2/3/9`** — instantiate the named per-phase constructors (residuals mostly structural).
11. **#4 `hSeedStep`** — connect `work.Post` ⟹ drained/unseeded guard, then `drained_kernel_seedTarget_compl_zero`.

**Wave 3 — the (C) genuinely-new probability, by paper-difficulty ASCENDING.** These need a new
mathematical object; do the most-scaffolded first:
12. **#9 `hConc` residuals** — most scaffolded (killed tail landed; only `hrfloor` Chernoff +
    clock-separation exit bridge remain). Doty Lemma 7.1 / footnote 11.
13. **#13 `hPhase10Sign`** — `arrival_classification` landed; remaining = the conserved
    `phase10ActiveSignedSum = initialGap` (Doty §11 backup-entry).
14. **#8 `hmain5` (Theorem 6.2 floor)** — `PaperRegime.majorityConfined3` object + projections
    landed; remaining = the bias-ledger collapse delivering `hConfine` (Doty §6 Thm 6.2).
15. **#11 `hdrop6` / q6** (Phase-6 band-drain rate) — the §6 width core (within-band doubling-drain rate).
16. **#14 `hSlotClass`** — the expected-side off-event slot-dispatch cover (Doty §5–§11 chain-end
    regime); hardest, the whole off-trajectory regime map. Sequenced last.

**(D) primitive — not on the attack path:** #12 `hStart : Phase0Initial` (honest start hypothesis,
belongs to the instance, not dischargeable); the dead `hM₀` (remove in a future V2 re-cut).

### Recommended first three waves (summary)

- **Wave 1 (A, quick wins):** #1 `hDrift`, #2 `hWorkPostToWindow`, #3 `hWindowToWorkPre` (card/phase),
  #12 `hWork0PreOfStart`, #5(a) `DetSeamOvershootBridge`. One seam-wiring file; all producers landed.
- **Wave 2 (B, by weight):** #5(b) `AtRiskClockZero` tail (gates all 10 no-overshoot seams), then
  #6 `hPhase6Post7`, #7 `hPhase7Post8`, #10 `hpull1`, #15 `work0/2/3/9`, #4 `hSeedStep`.
- **Wave 3 (C, easiest paper-math first):** #9 `hConc` residuals → #13 `hPhase10Sign` → #8 Thm-6.2
  floor → #11 Phase-6 drain rate → #14 `hSlotClass` (the off-event regime cover, last).

## SeamQuickWins.lean — WAVE 1 (A-class quick wins) DISCHARGED (2026-06-11)

New append-only file `Probability/SeamQuickWins.lean`.  Delivers the narrowed bundle constructor
`SeamQuickWins.dotyAtomsWave1 : DotyAtomsWave1Inputs n C0 → FinalAssemblyV3.DotyResidualAtomsV3 n C0`,
in which the five (A)-class seam fields are PRODUCED from landed machinery (no longer free inputs).
The input record `DotyAtomsWave1Inputs` carries each producer's calibration data and the
still-open residuals verbatim.  0-sorry, axiom-clean (`#print axioms ⊆ {propext, Classical.choice,
Quot.sound}`).

| # | Atom (field) | Status | Producer wired (file:line) |
|---|---|---|---|
| 1 | `hDrift` (10 seam epidemic drifts) | ✅ PRODUCED | `wave1_hDrift` ← `SeamEpidemics.seam_drift` (`SeamEpidemics:1093`), per-seam at `p=seamP k`, `t=seamT k`, rate `sDrift k`, tail check `hεDrift k` |
| 2 | `hWorkPostToWindow` (work.Post → allPhaseGe) | ✅ PRODUCED | `wave1_hWorkPostToWindow` ← `AssemblyBridges.mk_hWorkPostToWindow` (`AssemblyBridges:233`) over `dotyWorkHonest wih`'s 11 slots with per-slot window read `hwin` |
| 3 | `hWindowToWorkPre` (allPhaseEq → next work.Pre) | ✅ PRODUCED | `wave1_hWindowToWorkPre` ← `AssemblyBridges.mk_hWindowToWorkPre_pin` (`AssemblyBridges:249`) ∘ carried per-phase entry residual `hEntryPin` |
| 12 | `hWork0PreOfStart` (slot-0 `Pre` interface) | ✅ WIRED | V3 bundle field ← carried slot-0 pin `hWork0Pin : Phase0Initial n c₀ → work0.Pre c₀` (the `slot0_pre_pin` reduction is already landed) |
| 5(a) | `DetSeamOvershootBridge` → `hNoOvershoot` | ✅ PRODUCED + WIRED | `wave1_hNoOvershoot` PRODUCES `DetSeamOvershootBridge (seamP k)` ← `SeamNoOvershoot.detSeamOvershootBridge_of_wf` (`SeamOvershootBridge:1604`) from `hReset k` + `hWf`, and FEEDS it into the consumed 5(b) tail `hOvershootTail k` |

**Consumed (not in scope — named input only):** 5(b) `AtRiskClockZero` clock-zero tail — the
ClockZeroTail agent's territory.  In `DotyAtomsWave1Inputs` it is the field `hOvershootTail`,
stated from the seam `Pre` and TAKING the produced bridge as an explicit argument; the clock-zero
concentration is NOT reproved here.

**Carried verbatim (still open, other waves):** `wih` (#6–#11, #15 work-slot atoms), `hSeedStep`
(#4), `hStart` (#12 D), `hPhase10Sign` (#13), and the budget/config/regime scalars
(`Cphase/δ/c₀/init/hC0/hδ`).

---

## SamplingAtoms.lean — roster #9 (Wave 3): the two slot-5 sampling-concentration atoms (2026-06-11)

New append-only file `Probability/SamplingAtoms.lean` discharges the two remaining inputs of the
slot-5 sampling concentration that `SampledClassTail.lean`'s `hConcDemand_of_real_window` left
named: **ATOM 1** the rate floor `hrfloor`, and **ATOM 2** the clock-separation escape.  0 sorry/
admit/axiom/native_decide; `#print axioms ⊆ {propext, Classical.choice, Quot.sound}`; single-file
`lake env lean` clean + `lake build` green (3618 jobs); max line width 100; append-only.

**ATOM 1 — `hrfloor` (the rate floor): PRODUCED.**  The per-step rise-probability floor the
sampled-class drift consumes is `Phase5Convergence.sampledReserveClassU_rise_prob_rect5`
(`Phase5Convergence:945`): on a phase-5 window the one-step rise probability is
`≥ (#unsampledReserves · #classMains_σi)/(n(n−1))` — the cross-rectangle sampling mass, with the
Main bias profile FROZEN through phase 5 (`biasedMainClassU_support_eq`, `Phase5Convergence:364`),
so the rate is the ENTRY-time class profile.  `hrfloor_of_floors` produces the exact `hrfloor` shape
from three named inputs by `Nat`-product monotonicity into that landed floor:
* `classFloor ≤ (classMainStates σ i).sum c.count` — the entry class count (the Thm-6.2 `usefulMains`
  chain's named entry input; FROZEN ⟹ carried `∀ c ∈ gate`);
* `reserveFloor ≤ (unsampledReserves).sum c.count` — the unsampled-reserve floor (`RoleSplitGood`'s
  `reserveCount ≥ (1−η)·n/4`-flavored export, `RoleSplitConcentration:105`, restricted to unsampled);
* static persistence = the `∀ c ∈ gate` quantifier itself (the entry profile transported by the
  FROZEN phase-5 rules).
The constant rate is `rateFloor reserveFloor classFloor n = (reserveFloor·classFloor)/(n(n−1))`;
`rateFloor_le_one` discharges `r ≤ 1` from the honest budget `reserveFloor·classFloor ≤ n(n−1)`.

**ATOM 2 — the clock-separation escape: HONEST NEGATIVE VERDICT (named carry, not faked).**  The
prompt's proposed route — instantiate the `ClockZeroTail`/`SeamNoOvershoot` seam tail with the
`p=4→5` roles swapped for an `e^{−40(L+1)}` budget — is **STRUCTURALLY BLOCKED**, verified vs the
FROZEN rules:
* `seam_atRiskTail_of_entry` (`ClockZeroTail:147`) requires `CounterResetDest (p+1)`, i.e.
  `p+1 ∈ {1,6,7,8}` (`SeamPairAdapter.CounterResetDest:80`).  Destination `5 ∉ {1,6,7,8}` —
  `CounterResetDest 5` is FALSE (the set is `CounterTimedPhase` *minus phase 5*).
* Structural cause (`SeamPairBound.lean` FINDING 2, lines 44–53): the predecessor `Phase4Transition`
  advances clocks via `advancePhase` (big-bias gate), which does NOT run `phaseInit`/reset the
  counter.  A clock counter-advanced from phase 4 into phase 5 keeps its OLD counter, so
  `SeamEntryFullCounter 4` ("every phase-5 clock at full counter `50(L+1)`", `ClockZeroTail:91`) is
  FALSE at phase-5 entry — `seamClockPotential_init_le`'s hypothesis cannot be discharged, breaking
  the affine immigration tail.  (NB: `phaseInit 5` *would* reset — `Transition.lean:166` — but the
  p=4→5 seam reaches phase 5 by `advancePhase`, not `phaseInit`.)
So the `e^{−40(L+1)}` budget is unavailable through the seam machinery; the phase-5 counter-drain is
governed by the dedicated minute/hour width machinery (`ClockOLogN`/`ClockReal*`).  We do NOT
manufacture a false bound.  ATOM 2 stays the named per-`τ` prefix bound `clockSeparationEscape n s i
K₀ t β` — the exact `hβ` field `hConcDemand_of_real_window` consumes — pinned with file:line
provenance.

**Slot-5 final surface.**  `hConcDemand_of_atoms` feeds ATOM 1 (produced) + ATOM 2 (named) into
`SampledClassTail.hConcDemand_of_real_window`; `phase5Convergence_of_atoms` composes with
`EndpointWiring.phase5Convergence_of_hConc`.  Slot 5 is now hypothesis-free except: the two entry
floors `hres`/`hcls` + budget `hbudget` (ATOM 1's named inputs), the clock-separation exit bridge
`hbridge` + per-`τ` escape `hesc`/`clockSeparationEscape` (ATOM 2's named remainder), the carried
window closure `hClosed` / drain `hstep`, and the arithmetic fits `hε'`/`hεC`.

| Atom | Status | Producer / remainder (file:line) |
|---|---|---|
| #9 ATOM 1 `hrfloor` | ✅ PRODUCED | `hrfloor_of_floors` ← `sampledReserveClassU_rise_prob_rect5` (`Phase5Convergence:945`) from `classFloor`+`reserveFloor`+budget |
| #9 ATOM 2 escape | ⏸ NAMED REMAINDER (seam tail proven inapplicable) | `clockSeparationEscape`; honest verdict: `CounterResetDest 5` FALSE (`SeamPairBound` FINDING 2) — width machinery, not seam tail |

---

## SmallSweep.lean — small-items sweep: #10 `hext1` / #15 work2,work9 / #4 SeedStepEvent / #13-14 SignMatch threading (2026-06-11)

New append-only file `Probability/SmallSweep.lean` (0 sorry/admit/axiom/native_decide; all 17 decls
`#print axioms ⊆ {propext, Classical.choice, Quot.sound}`; single-file `lake env lean` EXIT 0; max
line width 100; `git diff --check` clean; edits NO existing file).  Four verdicts:

| atom | verdict | landed decls |
|---|---|---|
| **(1) `hext1`** (slot-1 extreme) | survey claim FALSE-as-stated; `SlotAtoms` verdict PROVEN sharp | `extremeU_pos_of_extremePos_sum`, `exists_extremeSt_of_extremeU_pos`, `extremeSt_val_zero_or_six`, `hext1_not_from_extremeU` |
| **(2) `work2`/`work9`** epidemic params | union ALGEBRA locked (`decide`); epidemic SCALARS NOT pinned by `DotyParams` | `Ucal`/`vcal` (+7 `decide` union facts), `calibratedUnionW`, `calibratedUnionW_eq_phase2` |
| **(3) `SeedStepEvent`** drain-seam | window repair did NOT dissolve it | `hSeedStep_timed_of_drained`, `seedStepEvent_needs_drained_state`, `hSeedStep_of_event` |
| **(4) SignMatch threading** | both per-config oracles threaded from one rooted invariant | `hasActiveAgent_of_reachable`, `phase10SignMatch_of_rooted`, `post_of_rooted`, `reachableFrom_kernel_closed_export` |

### (1) `hext1` — survey claim FALSE-as-stated (the `extremeU > 0` witness is two-sided)

The survey hoped `extremeU > 0` literally IS the `Hext1` witness.  It is NOT: `extremeU =
countP extremeSt` and `extremeSt a = (main ∧ extremeVal a.smallBias)` with
`extremeVal v = (v.val = 0 ∨ v.val = 6)` (`Phase1Convergence:114`) — it counts the saturated
extremes at BOTH ends.  But `Hext1`/`extremePosSet` pins the `+3` end ALONE
(`extremePos a = main ∧ smallBias.val = 6`, `DrainThreading:226`).  PROVEN: the `+3` → `extremeU`
direction (`extremeU_pos_of_extremePos_sum`, the `+3` extremes ARE counted), the two-sided extraction
(`exists_extremeSt_of_extremeU_pos`, mirror of `EliminatorMargins.exists_minorityAt_of_minorityU_pos`),
and the sharp separation `extremeSt_val_zero_or_six` (the witness is val `0` = `−3` OR val `6` = `+3`).
So `extremeU > 0` does NOT force a `+3` extreme — `hext1` is the SIGN-SELECTED `+3` floor, a structural
saturation carry, exactly `SlotAtoms`' original verdict now proven sharp (not chain-dischargeable).

### (2) `work2`/`work9` — union algebra locked, epidemic scalars NOT

Survey of `DotyParams.lean`: NO phase-2 opinion-union epidemic rate is pinned (no `s`/`t`/`ε` for the
doubling seed).  So the SCALARS are genuinely free calibration inputs; only the union ALGEBRA is
pinned (concrete `Fin 8` bit arithmetic).  `calibratedUnionW` instantiates
`Phase2Convergence.phase2Convergence` at the CONCRETE single-sign pair `U = 4` (`+1`-only), `v = 0`
(empty) — all seven union-algebra side conditions (`singleSign`, the four `opinionsUnion` idempotents,
`U ≠ v`) discharged by `decide` — embedded weak via `.toW`.  Both slot 2 (doubling seed) and slot 9
(pre-phase-10 union) are the SAME `calibratedUnionW`; only the carried epidemic horizon `(s,t,ε)` and
budget `hε` differ (the honest scalar residual).

### (3) `SeedStepEvent` — window repair did NOT dissolve it (likely-windfall check = NEGATIVE)

The campaign hypothesised the `HonestDrainSlots` window repair (all-Main → phase-only honest windows
WHERE CLOCKS EXIST) lets the FREE timed seed `SeedRungs.drained_kernel_seedTarget_compl_zero` apply on
the drained Post, dissolving `SeedStepEvent`.  **It does NOT.**  The honest Post `Phase{1,8}Honest`
(`HonestWindows:125/133`) is phase-ONLY (`card = n ∧ ∀ a ∈ c, a.phase.val = p`); it permits clocks to
coexist but pins NOTHING about clock counters.  The timed seed needs the drained ALL-CLOCK state
`AllClockGEpCard p n ∧ clockCounterSumAt p = 0 ∧ geCount (p+1) = 0` — none of which the phase-only Post
supplies (`seedStepEvent_needs_drained_state` makes the missing drained-state premise explicit).  So
`SeedStepEvent` survives as the genuine one-step remainder; the two honest worlds (counter-timed
`hSeedStep_timed_of_drained`; all-Main/honest-window carried event) are unchanged.

### (4) SignMatch threading — two oracles → one rooted invariant

`SignMatch.phase10SignMatch_of_reachable` carried two per-config oracles `hreach`/`hact`.  THREADED:
reachability rides on `reachableFrom_kernel_closed` (`ReachableLadder:96`); the activity invariant
`hasActiveAgent` propagates along the all-phase-10 chain by `phase10_hasActiveAgent_preserved_by_step`
(`Analysis/Phase10Backup:1946`, the public Phase-10 liveness lemma) + `phase10_phase_preserved_by_step`,
chained over `ReflTransGen` reachability in `hasActiveAgent_of_reachable`.  `phase10SignMatch_of_rooted`
produces `AtomsV2.Phase10SignMatch init` from a single ACTIVE all-phase-10 root + the chain reachability
(the `hc₀Reach`-flavoured conditioning surface the V3 expected theorem already carries); `post_of_rooted`
composes with `AtomsV2.postOfSign` for `h_post`.  The two per-config oracles collapse into the single
rooted activity+reachability hypothesis the correctness chain already owns.

---

## FinalAssemblyV4.lean — THE DEFINITIVE CONSOLIDATION: the Doty Theorem 3.1 pair on the HONEST family (2026-06-11)

New append-only file `Probability/FinalAssemblyV4.lean` assembles the definitive pair.  It puts the
genuinely HONEST work family `HonestDrainSlots.dotyWorkHonestV3` (slots 1/7/8 on the chain-honest
phase-only windows `Phase{1,7,8}Honest`, NOT the all-Main UNSAT windows) ON THE PROOF PATH of the whp
half, and re-bases the leaky off-event expected half on the same V4 residual bundle.  0 sorry/admit/
axiom/native_decide; single-file `lake env lean` EXIT 0; `#print axioms ⊆ {propext, Classical.choice,
Quot.sound}` for all nine declarations; `git diff --check` clean; edits NO existing file.

### The two V4 signatures

* **`doty_theorem_3_1_whp_v4`** (`FinalAssemblyV4:doty_theorem_3_1_whp_v4`): over `DotyRegime n L K`
  + `DotyResidualAtomsV4 n C0`, `(K^T) c₀ {¬ majorityStableEndpoint init} ≤ 21/n² ∧ T ≤ 21·C0·n·(L+1)
  ∧ T ≤ 21·C0·n·(⌈log₂ n⌉+1)`.  PRODUCED by instantiating the POLYMORPHIC
  `FinalAssemblyV2.whp_of_asm'` (free `asm`; the `21/n²` bound produced through
  `BudgetTightening.doty_time_headline_W2_inv_sq`) at the V4 honest assembly `toAssembly'V4`, whose
  `work := dotyWorkHonestV3 wi`.  NO `hcompFail`; `hx₀`/`h_post` produced in-bundle (`hx₀_of_start_v4`
  / `h_post_of_sign_v4`, the slot-0/20 pins through `dotyWorkHonestV3_carried_eq` — the honest re-cut
  leaves slots 0/10 carried, so the pins reduce onto `wi.base.work0.Pre` / `Phase10Post`).
* **`doty_theorem_3_1_expected_v4_final`** (`FinalAssemblyV4:doty_theorem_3_1_expected_v4_final`):
  `OffEventEndgame.doty_theorem_3_1_expected_v4` (the leaky-good-invariant split-geometric: exact
  `J = ReachableFrom` closure, leaky `G` membership, off-good mass charged to the leak `η` — NO
  deterministic off-event ladder) re-based on the V4 bundle's `init`/`c₀`:
  `E[T c₀ → StableDone] ≤ Tgood + δgood·sRec·(1 − (1/2 + η))⁻¹`.  Headline corollary
  `doty_theorem_3_1_expected_v4_headline` lands `(21·C0 + 4·Cbad)·n·(L+1)` via
  `OffEventEndgame.v4_headline_of_budget` exactly when the leak fits the recovery budget.

Numeral corollaries at `C0 = 17`, `Cbad = 3`: `doty_theorem_3_1_whp_numeral_v4` (`≤ 21·17·n·(L+1)`),
`doty_theorem_3_1_expected_v4_numeral` (`≤ (21·17 + 4·3)·n·(L+1) = 369·n·(L+1)`).

### Consumption-sweep self-audit (every production ON path; every carried field genuinely open)

* **ON the proof path:** `dotyWorkHonestV3 wi` (the honest family enters `whp_of_asm'` via
  `toAssembly'V4`); the slot-0/20 pins via `dotyWorkHonestV3_carried_eq`; `hStart`/`hPhase10Sign`
  produce `hx₀`/`h_post`; the seam fields enter `toAssembly'V4`; budget/regime via `whp_of_asm'`
  arguments + `hReg.hLlog` for the `clog` form.  No dead decoration: `phases'V4_eq` is the recorded
  unfold equality (the V2/V3 `phases'_eq` pattern), the `[local irreducible] dotyWorkHonestV3` blocks
  the horizon-fold whnf divergence (placed AFTER the pins, which need the carried-slot reduction).
* **GENUINELY OPEN (grep-verified NOT discharged by any plugged file):** each field below.

### THE DEFINITIVE FINAL-SURFACE TABLE — `DotyResidualAtomsV4` (19 binders)

Classification key: **OPEN** = genuinely-open named fact (the statement of what stands between this
and FAITHFUL); **PROD** = production input (a calibration datum the landed producer consumes, the
math is landed); **BOIL** = arithmetic/config boilerplate.

| # | field | class | statement | paper citation + landed partial machinery |
|---|---|---|---|---|
| 1 | `wi : WorkInputsHonestV3 n` | **OPEN** (bundle) | the HONEST work record (slots 1/7/8 on chain-honest windows + the within-slot atoms) | bundles the genuinely-open within-slot facts below; survival forms via `WindowSurvival` (`hClosed{1,7,8}`) |
| 1a | `wi.hext1H` (+3 extreme floor) | **OPEN** | `1 ≤ extremePosSet.sum b` on `Phase1Honest` | Doty Lemma 5.3 / [45]; `SmallSweep` proved survey's `extremeU>0` FALSE-as-stated (`extremeSt_val_zero_or_six` — the witness is val 0=−3 OR 6=+3; the +3 end is SIGN-SELECTED, structural saturation carry) |
| 1b | `wi.hpull1H` (partner pool) | **OPEN** | `P1 ≤ pullPosSet.sum b` on `Phase1Honest` | Doty Lemma 5.3 partner pool; `EliminatorMargins.phase1_pullPos_floor_…` (:168) landed adapter (needs saturated-main count) |
| 1c | `wi.hwit7` (gap-1 elim margin) | **OPEN** | per-config gap-1 eliminator margin on `Phase7Honest` | Doty Lemma 7.4; `MarginInstantiation.hPhase6Post7_singleLevel` (:131) instantiable from the §6 doubling-drain positional content + `SingleLevelWitness` |
| 1d | `wi.hwit8` (above-level elim margin) | **OPEN** | per-config above-level eliminator margin on `Phase8Honest` | Doty Lemma 7.6; `MarginInstantiation.hPhase7Post8_of_survival` (:180), mirror of 1c one level up |
| 1e | `wi.base.hmain5` + `P5` | **OPEN** | slot-5 Thm-6.2 biased-Main floor `P5 ≤ usefulMains.sum` | Doty §6 / Thm 6.2 bias-ledger collapse; `UsefulMainFloor.theorem6_2_usefulMains_floor` (:207) + `PaperRegime.theorem62Paper_implies_broad_floor` landed; the ledger collapse delivering `hConfine` is genuinely-new |
| 1f | `wi.base.hConc` + `εConc` | **OPEN** | slot-5 Lemma-7.1 sampled-class concentration | Doty Lemma 7.1 / footnote 11; `SampledClassTail` killed tail landed; `SamplingAtoms` ATOM 1 `hrfloor` PRODUCED (`sampledReserveClassU_rise_prob_rect5`), ATOM 2 clock-sep escape NAMED (`clockSeparationEscape`, `CounterResetDest 5` FALSE — width machinery not seam tail) |
| 1g | `wi.base.hClosed5` | **OPEN** | slot-5 honest-window closure `InvClosed K Phase5AllWin` | the carried within-seam closure (named, mirrors `phase6Convergence'` doctrine) |
| 1h | `wi.base.hdrop6` + `q6` | **OPEN** | slot-6 Phase-6 band-drain per-level rate | Doty §6 Phase-6 drain rate (the core §6 width content); the within-band doubling-drain rate |
| 1i | `wi.base.{work0,work2,work3,work9}` | **OPEN** (opaque) | carried `PhaseConvergenceW` stage instances (role-split / doubling seed / band-init / pre-phase-10) | `SmallSweep`: union ALGEBRA locked (`calibratedUnionW` at concrete `U=4`/`v=0`, `decide`); epidemic SCALARS `(s,t,ε)` genuinely free calibration inputs (`DotyParams` pins no phase-2 union rate) |
| 2 | `seamP`/`seamT`/`εepidemic`/`εovershoot` | **PROD** | per-seam phase/horizon/budgets | calibration data the Wave-1 producers consume |
| 3 | `hDrift` (seam epidemic drift) | **PROD** | `(K^seamT) c {¬allPhaseGe(p+1)} ≤ εepidemic` | Doty §10; `SeamQuickWins.wave1_hDrift` ← `SeamEpidemics.seam_drift` (:1093), modulo per-seam Phase-4-shape tail check |
| 4 | `hNoOvershoot` (seam clock no-overshoot) | **OPEN** ({2,3,4,5,9} tails) | `(K^seamT) c {¬NoOvershoot p} ≤ εovershoot` | Doty Lemma 5.2 clock-separation; `wave1_hNoOvershoot` produces `DetSeamOvershootBridge`; `ClockZeroTail.seam_atRiskTail_of_entry` discharges the GATE for `{1,6,7,8}` reset dests; the non-reset {2,3,4,5,9} clock-zero tails (`AtRiskClockZero ≤ exp(−40(L+1))`) stay NAMED |
| 5 | `hWorkPostToWindow` | **PROD** | `work.Post → allPhaseGe(seamP)` | `SeamQuickWins.wave1_hWorkPostToWindow` ← `AssemblyBridges.mk_hWorkPostToWindow` (:233) |
| 6 | `hSeedStep` (one-step seed) | **OPEN** | `(K^1) c {¬advTriggered(p+1)} = 0` from `work.Post` | Doty §10 seed rung; `SmallSweep` NEGATIVE verdict (`seedStepEvent_needs_drained_state`): the phase-only window does NOT supply the drained ALL-CLOCK state the timed seed needs — `SeedStepEvent` survives |
| 7 | `hWindowToWorkPre` | **OPEN** (per-phase entry) | `allPhaseEq(p+1) → next work.Pre` | card/phase half PRODUCIBLE (`AssemblyBridges.mk_hWindowToWorkPre_pin` :249); the per-phase drain-budget/role/sign entry pins carried |
| 8 | `Cphase`/`δ`/`c₀`/`init`/`hC0`/`hδ` | **BOIL** | budget/config scalars + fits | arithmetic side conditions |
| 9 | `hStart : Phase0Initial n c₀` | **OPEN** (primitive) | the all-`mcr` phase-0 START shape | Doty initial config (`RoleSplitConcentration:165`); honest hypothesis about the problem instance, produces `hx₀` |
| 10 | `hWork0PreOfStart` | **PROD** (interface) | `Phase0Initial n c₀ → work0.Pre c₀` | slot-0 `Pre` deterministic interface pin |
| 11 | `hPhase10Sign : Phase10SignMatch init` | **OPEN** | `∀c, Phase10Post c → phase10MajorityWitness init c` | Doty §11 phase-10 sign conservation; `SignMatch.phase10SignMatch_of_rooted` threads it from a single rooted activity+reachability invariant; `BackupEntry.arrival_classification` (:189) landed; full conservation is §11 backup-entry, produces `h_post` |

**Expected-side additional binders (on `doty_theorem_3_1_expected_v4_final`, not in the V4 bundle):**

| field | class | citation |
|---|---|---|
| `hOnGood : OnGoodSlotClassifier` | **OPEN** | the on-J-good classifier (regime data ONLY on the good slice); Doty §5–§11 chain-end regime cover; `OffEventEndgame` proved the over-quantified `DotySlotClassifier` DISHONEST (no off-event ladder, `BranchAndBudget` Part 4) |
| `η` (leak budget) + `hLeak` | **OPEN** | the off-good escape budget (WindowSurvival-style `T·η` cemetery charge); the off-event mass is here, additively, NOT in a classifier |
| `hGoodBlock` | **OPEN** | the good-slice per-block half-failure (produced from `hOnGood`'s good-slice caps) |
| `hfail` | landed | the whp horizon (`doty_time_headline_W2` / `doty_theorem_3_1_whp_v4` output) |

### What stands between this and FAITHFUL

The honest residual is exactly the OPEN rows above: the §6 within-slot probability (Thm 6.2
bias-ledger `1e`, Phase-6 drain rate `1h`, eliminator margins `1c`/`1d`, Lemma-7.1 clock-separation
escape `1f`/`4`), the structural saturation carries (`1a`/`1b`), the §11 sign conservation (`11`), the
opaque stage scalars (`1i`), the off-event leak `η`/`hLeak`/`hOnGood`, and the primitive start
hypothesis `9` (`DotyRegime` + `Phase0Initial`).  Every other surface — the whp composition, the
seam epidemic drift/window bridges, the leaky split-geometric Markov tail, the on-good branch
production, `hx₀`/`h_post` — is DISCHARGED axiom-clean and ON the proof path of the V4 pair.

### Axiom audit

```
doty_theorem_3_1_whp_v4            : [propext, Classical.choice, Quot.sound]
doty_theorem_3_1_whp_numeral_v4    : [propext, Classical.choice, Quot.sound]
doty_theorem_3_1_expected_v4_final : [propext, Classical.choice, Quot.sound]
doty_theorem_3_1_expected_v4_headline : [propext, Classical.choice, Quot.sound]
doty_theorem_3_1_expected_v4_numeral  : [propext, Classical.choice, Quot.sound]
slot0_pre_pin_v4 / slot20_post_pin_v4 / hx₀_of_start_v4 / h_post_of_sign_v4 : same
```

---

## V7 ASSEMBLY — `FinalAssemblyV7.lean` (V6 re-cut with the HONEST A/B producers)

**What landed.** `FinalAssemblyV7.lean` (append-only; edits NO existing file) — a V6 re-cut whose
ONLY change is the slot-1 / slot-7 / slot-8 wiring.  V6 consumed the AUDITED-DEFECT producers that
carried the globally-false all-Main bridge; V7 replaces those three wires with the HONEST redos from
`PkgA2HonestFloor` / `PkgB2HonestMargin`.

**The three honest re-wires (on the proof term of `toWorkInputsV51`, grep-verifiable):**
- `hext1H := PkgA2HonestFloor.hext1H_of_extremePos_witness n ra.hwit1` (already honest, re-exported).
- `hpull1H := PkgA2HonestFloor.hpull1H_of_honestEntry n ra.g ra.mc ra.hHonestEntry1` at the HONEST
  floor `P1 := (mc − g + 3)/4` (from `Phase1Honest` + `|centredBiasSum| ≤ g` + the chain-carried
  Main-count floor `mc ≤ mainCount`).  `hpt1` rectangle calibration re-keyed to `qRectReal ((mc−g+3)/4) n`.
- `hwit7 := PkgB2HonestMargin.hwit7_honest ra.hMainMass7 ra.hStruct7` (§6/§7 mass↔Main-minority carry
  + carried §6 Post; NO all-Main bridge).
- `hwit8 := PkgB2HonestMargin.hwit8_honest ra.hStruct8` (carried §7 Post ALONE, ZERO extra; NO bridge).

**New honest inputs added to `DotyResidualAtomsV7` (carried, with provenance):** `mc` (chain Main-count
floor from `RoleSplitGood`), `hHonestEntry1` (`PkgA2HonestFloor.HonestEntry n g mc`), `hMainMass7`
(§6/§7 surviving-class-mass is Main-carried).  **Dropped from V6** (used by NOTHING but the defect
producers): `hE7`, `hAll7`, `hE8`, `hAll8`.

**C/D/E/F UNCHANGED** (conditional-honest carries, not defects).  For C: `hConf5` stays a CARRIED
field, doc-commented as THE GENUINE RESIDUAL — the whp confinement event `⊬` the pointwise `hmain5`
(`ConfinementSurface:36`); pointwise success at `b` is an OPEN paper-probability gap.  V7 does NOT
pretend it is produced.

**Theorems (same conclusions as V6/V5.1):** `doty_theorem_3_1_whp_v7` / `_whp_numeral_v7`
(`≤ 21/n²`, `T ≤ 21·C0·n·(L+1)`, clog form) and `doty_theorem_3_1_expected_v7` / `_expected_v7_numeral`
(`E[T] ≤ 369·n·(L+1)`), each routing through the landed V5.1 theorems on `toResidualV51 ra …`.

**False-bridge absence (grep-verified).** `PkgAAtoms.hpull1H_of_entry_on_honest`,
`PkgAAtoms.hpull1H_of_allMain_and_gap_on_honest`, `PkgBAtoms.hwit7_of_phase6To7Structure_honest`,
`PkgBAtoms.hwit8_of_phase7To8Structure_honest`, `PartnerMargin.EntrySumPinned`, `Phase7AllMain`,
`Phase8AllMain` appear in NO V7 proof term — only in doc-comments as the named DEFECT.

**Build/audit.** Single-file `lake env lean` clean (uisai2 /dev/shm, v4.30.0 + mathlib c5ea00351c28,
EXIT 0, no warnings); no `sorry`/`admit`/`axiom`/`native_decide`.  `#print axioms` on all four V7
theorems = `[propext, Classical.choice, Quot.sound]`.  Built atop canonical HEAD 5d99c156.

---

## V7 RESIDUAL TRIAGE — FINAL GAP ROSTER

**What landed.** `Probability/V7ResidualClear.lean` (append-only; edits NO existing file; single-file
`lake env lean` EXIT 0; `#print axioms` on all 10 produced lemmas = `[propext, Classical.choice,
Quot.sound]`; no `sorry`/`admit`/`axiom`/`native_decide`).  It is the HONEST (a)/(b) discharge layer
for `FinalAssemblyV7.DotyResidualAtomsV7`: it produces — as standalone axiom-clean terms — the
deterministic-arithmetic / locked-calibration residual fields, and records (as a compile-checked
doc anchor) the genuinely-landed chain-wiring whose (b) fields are cleared by DIRECT wiring at
instantiation.  Class (c) — the irreducible paper-probability gaps — is UNTOUCHED and rostered below.

### The honest accounting principle

`DotyResidualAtomsV7` is a PARAMETERIZED bundle: each slot's calibration scalars (`P1`, `P5`, `E7`,
`E8`, window lengths, MGF slopes) are FREE fields, locked to their paper values only by the
side-relation fields.  A field is genuinely class (a) iff — ONCE the locked floor/margin side-relation
is in scope — it is a pure-arithmetic consequence with NO hidden probability.  A field is class (b)
iff the landed chain already EXPORTS it (so an instantiator wires it directly, no new math).  A field
is class (c) iff its truth IS a paper-probability statement (a whp bound, a Chernoff/Azuma tail, a
margin lower bound, a confinement event) that no landed file discharges.

Honesty guard applied: two fields the prompt hoped were class (a) — `hrate7`/`hrate8` (the slot-7/8
rate-shape comparisons) — turned out, on algebra, to be EQUIVALENT to the eliminator-margin LOWER
bounds `(4/15)·M₀·(n−1) ≤ E7` and `(14/75)·M₀·(n−1) ≤ E8`, which are §7 paper-probability content.
`V7ResidualClear.rate_shape_of_margin_lb` produces ONLY the pure-arithmetic shell (per-`m` field ⟸
worst-case margin bound); the margin bound itself is MOVED TO class (c) (gaps C5/C6 below).  We do
NOT manufacture it.

### THE THREE-CLASS TABLE (field → class → disposition)

Class key: **(a)** deterministic arithmetic / locked calibration — CLEARED in `V7ResidualClear`;
**(b)** chain-wiring the landed chain exports — CLEARED by direct wiring at instantiation;
**(c)** genuine paper-probability gap — KEPT as named residual (roster below).
Fields are grouped by slot/role; scalar-only binders (the free `P`/`E`/`tWin`/`s`/`t`/`c`/`L0`
calibration numbers and the regime `hn`/`hM1`/`hM₀1`, budget `Cphase`/`δ`/`hC0`/`hδ`, config
`c₀`/`init`/`k10`) are BOIL — neither math nor gap, just the instance data — and are noted once.

| slot / group | fields | class | disposition |
|---|---|---|---|
| regime/budget/config (BOIL) | `σ M₀ hn hM1 hM₀1 Cphase δ hC0 hδ c₀ init k10 s10 hs10 k10` | (a)-triv | side conditions; `hδ`/`hC0` are `≤ 1/n²` / `≤ C0` arithmetic fits at the locked budget |
| **slot 1 — rect nonneg** | `hq01` | **(a)** | `V7ResidualClear.hq01_of_floor_le_n` (from `(mc−g+3)/4 ≤ n`) |
| slot 1 — rect rate cmp | `hq1` | (a)/(c)-edge | rate-shape `qRectReal((mc−g+3)/4) ≤ 1−α·m/n`; pure at `α≡1` once floor pinned; tied to the slot-1 partner-floor margin (gap **C1**) |
| slot 1 — α calib | `hα01 hα11` | **(a)** | `V7ResidualClear.hα0_one`/`hα1_one` at `α ≡ 1` |
| slot 1 — window len | `tWin1 hT1` | (a) | `PkgAAtoms.rectTWin` + `rectTWin_spec` (landed) at the calibrated window |
| slot 1 — honest entry | `g mc hwit1 hHonestEntry1` | **(c)** | the §5 partner-floor whp inputs — gap **C1** |
| slot 1 — escape tail | `η1 hescW1 hηtail1 hfit1 escapeε1 c1 L01` | **(c)** | one-step escape mass `hescW1` + its tail — gap **C7** |
| **slot 5 — rect nonneg** | `hq05` | **(a)** | `V7ResidualClear.hq05_of_hP5` (from carried `hP5`) |
| slot 5 — rect rate cmp | `hq5` | (a)/(c)-edge | as `hq1`; tied to the biased-Main floor (gap **C2**) |
| slot 5 — α calib | `hα05 hα15` | **(a)** | `hα0_one`/`hα1_one` at `α ≡ 1` |
| slot 5 — window len | `tWin5 hT5` | (a) | `rectTWin`/`rectTWin_spec` |
| slot 5 — floor bound | `hP5` | **(a)** | `V7ResidualClear.hP5_locked` at `P5 = ⌊23n/75⌋` |
| **slot 5 — confinement** | `hConf5` | **(c)** | THE genuine residual — gap **C2** (whp ⊬ pointwise) |
| slot 5 — main floor | `hMainFloor5` | **(b)** | `RoleSplitConcentration.RoleSplitGood ⇒ mainCount ≥ n/3` (landed export; wired directly) |
| slot 5 — closure | `hClosed5` | (c)-doc | documented non-reset closure exception — gap **C8** |
| slot 5 — concentration | `i5 hiL5 K₀ e5s e5hs e5reserveFloor e5classFloor e5hbudget e5hres e5hcls εConc e5hbridge e5β e5hwidth e5hε P5 tWin5` | **(c)** | Lemma-7.1 sampled-class concentration + width-survival — gap **C3** |
| **slot 7 — elim nonneg** | `hq07` | **(a)** | `V7ResidualClear.hq0_elim_of_le_pairs` (from `E7 ≤ n(n−1)`) |
| slot 7 — rate shape | `hrate7` | **(c)** | ⟺ margin LB `(4/15)M₀(n−1) ≤ E7`; shell `rate_shape_of_margin_lb`, margin = gap **C5** |
| slot 7 — window len | `E7 tWin7 hTw7` | (a) | `hTw7` = window ceiling (landed shape) |
| slot 7 — mass carry | `hMainMass7` | **(c)** | §6/§7 surviving-class-mass-is-Main-minority — gap **C5** |
| slot 7 — structure Post | `hStruct7` | **(c)** | `Phase6To7Structure σ E7` carried §6 Post whp — gap **C5** |
| slot 7 — escape tail | `η7 hescW7 hηtail7 hfit7 escapeε7 c7 L07` | **(c)** | gap **C7** |
| **slot 8 — elim nonneg** | `hq08` | **(a)** | `V7ResidualClear.hq0_elim_of_le_pairs` (from `E8 ≤ n(n−1)`) |
| slot 8 — rate shape | `hrate8` | **(c)** | ⟺ margin LB `(14/75)M₀(n−1) ≤ E8`; shell `rate_shape_of_margin_lb`, margin = gap **C6** |
| slot 8 — survival const | (locked `14n/75`) | **(a)** | `V7ResidualClear.honest_E8_le_one_fifth` |
| slot 8 — window len | `E8 tWin8 hTw8` | (a) | window ceiling |
| slot 8 — structure Post | `hStruct8` | **(c)** | `Phase7To8Structure σ E8` carried §7 Post whp — gap **C6** |
| slot 8 — escape tail | `η8 hescW8 hηtail8 hfit8 escapeε8 c8 L08` | **(c)** | gap **C7** |
| slot 6 — padded drain | `l qpos6 tWin6 hdrop6pos hpt6pos` | **(c)** | Phase-6 within-band doubling-drain rate — gap **C4** |
| slot 6 — escape tail | `η6 hescW6 hηtail6 hfit6 escapeε6 c6 L06` | **(c)** | gap **C7** |
| slots 0/2/3/9 — stage W | `w0stage1 w0stage15 w0stage2 w0chain1 w0chain2 w2s w2hs w2t w2ε w2hε w3* w9*` | **(c)** | opaque `PhaseConvergenceW` stage instances (role-split/doubling-seed/clock-bulk/pre-10) — gap **C9** (union ALGEBRA landed; epidemic SCALARS free) |
| slot 4 — epidemic | `s4 hs4 t4 ε4 hε4` | **(c)** | Phase-4 constant-density epidemic tail — gap **C9** |
| slot 10 — block geom | `s10 hs10 hsB10` | **(a)** | `V7ResidualClear.hsB10_of_ge` at locked `s10` (ceiling) |
| seam — drift/overshoot | `seamP seamT εepidemic εovershoot hDrift hNoOvershoot` | **(c)** | §10 seam epidemic drift + clock no-overshoot tails — gap **C10** |
| seam — glue (thm args) | `hPost2Win hSeedEvent hWin2Pre` | **(c)** | seed-step + window↔work entry pins (passed as theorem args) — gap **C10** |
| start/sign — Pkg F | `hStart hStagePre0` | (b)/(c) | `hStart` = primitive `Phase0Initial` hypothesis; `hStagePre0` = slot-0 Pre interface (landed pin) |
| start/sign — reach/root | `hInitValid hAllRoot hActRoot hReach10` | **(c)** | §11 phase-10 sign conservation / reachability roster — gap **C11** |

**Counts.** Of the ~112 structure binders + the 3 theorem-arg glue families:
- **class (a) CLEARED in `V7ResidualClear.lean` (10 produced lemmas):** `hq01`, `hq05`, `hq07`,
  `hq08`, `hα01/hα11/hα05/hα15` (the `α≡1` calibration), `hP5`, the slot-8 survival constant
  `14n/75 ≤ n/5`, `hsB10`, plus the shared shells `qRectReal_nonneg_of_le_pairs` and
  `rate_shape_of_margin_lb`.  Together with the BOIL side conditions and the landed window-ceiling
  `tWin`/`hT` calibration (`rectTWin`/`rectTWin_spec`), this clears the entire DETERMINISTIC-ARITHMETIC
  surface of the residual.
- **class (b) CLEARED by direct landed wiring:** `hMainFloor5` (from `RoleSplitGood`), `hStagePre0`
  (slot-0 Pre interface pin).  These need no new term — the landed export is wired at instantiation.
- **class (c) KEPT — 11 named gaps (the next-campaign roster):** below.

### THE DEFINITIVE (c) GAP ROSTER — the irreducible paper-probability gaps

| # | gap | V7 fields | paper citation | landed partial machinery | why genuinely open |
|---|---|---|---|---|---|
| **C1** | slot-1 partner-floor + sign witness whp | `g mc hwit1 hHonestEntry1` (and `hq1`'s margin) | Doty Lemma 5.3 (entry/partner pool) + Lemma 5.3 +3 sign | `PkgA2HonestFloor.hpull1H_of_honestEntry`/`hext1H_of_extremePos_witness` consume them; `EntryFloor`/`DrainThreading.extremePos` landed | the HONEST entry `\|centredBiasSum\| ≤ g` ∧ `mc ≤ mainCount` is a CONSERVATION + concentration whp fact on the Phase-1 window; not produced from the phase-only window |
| **C2** | slot-5 biased-Main confinement (pointwise) | `hConf5` (and `hq5`'s floor) | Doty §6 / Thm 6.2 bias-ledger collapse | `PkgCAtoms.hmain5_of_pointwise_confinement` consumes it; `MainExponentConfinement`/`ConfinementSurface:36` landed; `UsefulMainFloor.theorem6_2_usefulMains_floor` landed | the whp confinement EVENT `⊬` the POINTWISE `MainProfileConfinedToUseful` at the witness `b`; needs pointwise success — the campaign's flagged Pkg-C residual |
| **C3** | slot-5 sampled-class concentration + width-survival | `e5* εConc e5β e5hwidth i5 K₀` | Doty Lemma 7.1 / footnote 11 | `SampledClassTail` killed tail landed; `SamplingAtoms` ATOM 1 `hrfloor` PRODUCED; `PkgEAtoms.phase5WidthSurvivalExport` shape landed | ATOM 2 — the clock-separation escape `clockSeparationEscape` (`CounterResetDest 5` FALSE: width machinery, not seam tail) — and the averaging-rate Chernoff core are the open whp inputs |
| **C4** | slot-6 Phase-6 within-band drain rate | `l qpos6 hdrop6pos hpt6pos` | Doty §6 Phase-6 doubling-drain | `PkgDAtoms.hdrop6_padded_from_positive`/`hpt6_padded_from_positive` consume them; `Phase6Convergence.highMass` landed | the per-level positive drain rate `qpos6 m` is the §6 width content (the within-band doubling-drain probability); not a landed term |
| **C5** | slot-7 gap-1 eliminator margin (mass + structure + rate) | `hMainMass7 hStruct7 hrate7` | Doty Lemma 7.4 (gap-1 eliminator) | `PkgB2HonestMargin.hwit7_honest` consumes them; `EliminatorMargins.Phase6To7Structure`/`MarginInstantiation.hPhase6Post7_singleLevel:131` landed | `hMainMass7` (surviving σ-class MASS ⇒ Main minority COUNT) ∧ the §6 Post `≥ E7` ∧ the margin LB `(4/15)M₀(n−1) ≤ E7` are whp eliminator-margin facts |
| **C6** | slot-8 above-level eliminator margin (structure + rate) | `hStruct8 hrate8` | Doty Lemma 7.6 (above-level eliminator) | `PkgB2HonestMargin.hwit8_honest` consumes `hStruct8` ALONE; `EliminatorMargins.Phase7To8Structure`/`MarginInstantiation.hPhase7Post8_of_survival:180` landed | the §7 Post `≥ E8` ∧ margin LB `(14/75)M₀(n−1) ≤ E8` are whp; one level up from C5, ZERO extra hypothesis but same whp class |
| **C7** | one-step escape tails (slots 1/6/7/8) | `η{1,6,7,8} hescW{1,6,7,8} hηtail{1,6,7,8} hfit{1,6,7,8}` | Doty §5 window-survival escape | `PkgDAtoms.hescε{1,6,7,8}_of_tail_fit` consume them (tail-fit ALGEBRA landed) | `hescW*` (one-step kernel mass OUT of the honest window `≤ η`) is the affine-engine escape bound; the tail-fit `η ≤ exp(−c(L+1))` is the per-window whp escape — the engine SHAPE is landed but the per-window rate is the open input |
| **C8** | slot-5 honest-window closure | `hClosed5` | documented non-reset exception (mirrors `phase6Convergence'` doctrine) | `OneSidedCancel.InvClosed`/`ReserveSampling.Phase5AllWin` landed | the within-seam Phase-5 closure (Phase 5 is the documented non-reset window); carried, not a probability bound but a structural closure obligation |
| **C9** | opaque stage `PhaseConvergenceW` instances + Phase-4 epidemic | `w0*` `w2*` `w3*` `w9*` `s4 t4 ε4` | Doty §-stage role-split/doubling-seed/clock-bulk/pre-10 + §-epidemic | `PkgFAtoms.work{0,2,3,9}_*` consume them; union ALGEBRA `calibratedUnionW` landed (`decide`); `ClockKilledMinute.minuteRate`/`ClockRealBulk.bulkHi`/`ClockBudgets.εclock` landed | the epidemic SCALARS `(s,t,ε)` and the clock-bulk budget are free calibration inputs — `DotyParams` pins the §6 windowed-front engine but NOT the phase-2/4/9 union rates |
| **C10** | seam epidemic drift + clock no-overshoot + seed/entry glue | `hDrift hNoOvershoot` + `hPost2Win hSeedEvent hWin2Pre` | Doty §10 (seam epidemics) + Lemma 5.2 (clock separation) | `SeamQuickWins.wave1_*`/`SeamEpidemics.seam_drift:1093` landed for `hDrift`; `ClockZeroTail.seam_atRiskTail_of_entry` for {1,6,7,8}; `SmallSweep.seedStepEvent_needs_drained_state` (NEGATIVE) | the non-reset {2,3,4,5,9} clock-zero overshoot tails + the seed-step rung (phase-only window ⊬ drained all-clock state) + the per-phase entry pins stay whp-open |
| **C11** | §11 phase-10 sign conservation / reachability | `hInitValid hAllRoot hActRoot hReach10` (and `hStart`) | Doty §11 (backup-entry sign conservation) | `PkgFAtoms.hPhase10Sign_of_rooted` consumes them; `SignMatch.phase10SignMatch_of_rooted`/`BackupEntry.arrival_classification:189` landed | full §11 backup-entry sign conservation `∀c, Phase10Post c → phase10MajorityWitness init c` threaded from a single rooted activity+reachability invariant; the reachability roster `hReach10` is the open instance fact |

### What stands between V7 and FAITHFUL

After this triage, the honest open surface is EXACTLY the 11 (c) gaps: the §5 partner-floor + +3
witness (C1), the Thm-6.2 pointwise confinement (C2), the Lemma-7.1 sampled-class concentration /
clock-separation escape (C3), the Phase-6 drain rate (C4), the §7 gap-1 / §8 above-level eliminator
margins (C5/C6), the window-survival escape rates (C7), the Phase-5 closure (C8), the opaque stage /
epidemic scalars (C9), the §10 seam tails + seed/entry glue (C10), and the §11 sign conservation
(C11).  EVERYTHING else — the rectangle nonnegativities, the α calibration, the locked floor/survival
constants, the block-geometric budget, the window-ceiling lengths — is now DISCHARGED axiom-clean in
`V7ResidualClear.lean` (class a) or wired directly from the landed chain (class b, `hMainFloor5` /
`hStagePre0`).

### Axiom audit

```
V7ResidualClear.qRectReal_nonneg_of_le_pairs : [propext, Classical.choice, Quot.sound]
V7ResidualClear.hq05_of_hP5                  : [propext, Classical.choice, Quot.sound]
V7ResidualClear.hq01_of_floor_le_n           : [propext, Classical.choice, Quot.sound]
V7ResidualClear.hq0_elim_of_le_pairs         : [propext, Classical.choice, Quot.sound]
V7ResidualClear.rate_shape_of_margin_lb      : [propext, Classical.choice, Quot.sound]
V7ResidualClear.hP5_locked                   : [propext, Classical.choice, Quot.sound]
V7ResidualClear.honest_E8_le_one_fifth       : [propext, Classical.choice, Quot.sound]
V7ResidualClear.hα0_one / hα1_one            : [propext, Classical.choice, Quot.sound]
V7ResidualClear.hsB10_of_ge                  : [propext, Classical.choice, Quot.sound]
```
Single-file `lake env lean` EXIT 0 (uisai2 `~/repos/Ripple-atoms`, opus-wip, v4.30.0 + mathlib
`v4.30.0`); no `sorry`/`admit`/`axiom`/`native_decide`; no warnings.
