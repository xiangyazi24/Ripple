
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
