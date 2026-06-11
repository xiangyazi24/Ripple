
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
