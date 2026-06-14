# DOCTRINE — autonomous grind: Thm 6.9 → converges to C-A (front-shape hcap_all)

**Approval:** user "继续啃 Thm 6.9. 自主执行." (2026-06-13). Driving autonomously to milestone/hard-block.

## Finding (Thm 6.9 audit, 2026-06-13)
- ABSTRACT Thm 6.9 (`ClockHourBounds.clock_hour_bounds` / `all_hours_O_log_n` on `clockProto (Minute L₀)`):
  GENUINELY PROVEN, axiom-clean `[propext, Classical.choice, Quot.sound]`, SATISFIABLE preconditions
  (`seedFloorInv` seed floor + ε Chernoff rate bounds). NOT vacuous. ✓ DONE.
- REAL-kernel `ClockRealHours.clock_real_O_log_n`: carries the BARE `habs_mix_all` (∀T c c', Q_mix→support→Q_mix).
  FrontSyncConc established the bare deterministic Q_mix closure is FALSE off FrontSync (at-cap counter=1
  witness `counterPos_one_step_NOT_closed_witness`) ⟹ conditionally vacuous on a false hyp. SUPERSEDED by the
  FrontSync-gated honest `ClockUnconditional.clock_real_unconditional`, which carries `hwin_all`
  (`FrontSyncConc.FrontFeederWindow`) — the C-A front-width residual.
- `ClockFrontWidth` reduced `hwin_all` to the SINGLE terminal residual `hcap_all`:
  `rBeyond (cap−1) c ≤ Bcap` on reachable FrontSync configs (Bcap = O(log log n) doubly-exp envelope cap).
  Everything else PROVEN: per-level squaring `front_breach_le_capSq`/`rBeyond_seed_le_rBeyondSq`, union bound
  `frontSync_union_horizon`, 1/poly budget, `FrontSyncConcentration_remaining` discharge.

**CONVERGENCE:** Thm 6.9 (honest real) AND Lemma 6.10 BOTH reduce to C-A = `hcap_all` = the front-shape
maintenance. This is THE genuine deepest remaining core.

## Goal (one sentence)
Discharge `ClockFrontWidth.hcap_all` (the doubly-exp front-feeder cap on the reachable FrontSync trajectory),
closing the honest real-kernel clock (Thm 6.9) and the FrontSync-gated Q_mix closure.

## Avenues
- (a) **Multi-level downward cascade** (the roadmap structure, ChatGPT-confirmed): maintain the within-envelope
  profile `RWithinEnvelope f₀ i` from the subcritical entry i₀ (where front fraction first ≤ 1/2... actually ≤ n^{−0.4})
  down/up the O(log log n) leading levels via the proven per-level squared seed `front_breach_le_capSq`, with the
  EARLY-DRIP GHOST term (essential — bare recurrence false at tiny tail). Anchor at the subcritical level; the
  doubly-exp envelope collapses below 1/n within `frontWidthBound n = O(log log n)` levels (`rFront_emptied_of_envelope`,
  PROVEN). The genuine residual: `rEnvelope_maintained` (the within-envelope invariant along the trajectory).
- (b) **Couple to the abstract `FrontShapeInduction`** (Config (Minute L₀)) where `front_shape_collapse`/
  `front_emptied_real`/`frontShape_couples_earlyDrip` are PROVEN — transfer the abstract maintenance to the
  real `rFrontFrac`. (The abstract model has the full doubly-exp maintenance; the real-kernel transfer is the gap.)
- (c) **Lean-friendly transfer theorem** (ChatGPT recommendation): `Pr[∀i,t. n^{−0.4} ≤ X_i ≤ 0.1 ⟹ X_{i+1} ≤ p X_i²]
  ≥ 1 − n^{−ω(1)}`, then `frontWidth_loglog` consumes it; one sparse-pioneer/no-long-early-drip lemma for sub-n^{−0.4}.

## Terminal conditions
- SUCCESS: `hcap_all` discharged on the reachable FrontSync domain, axiom-clean. Then clock_real_unconditional
  is unconditional (modulo the satisfiable entry), and Thm 6.9 real is honest.
- HONEST-RESIDUAL: `rEnvelope_maintained` isolated precisely over the reachable domain (refutation-checked,
  not a false universal), with the exact remaining lemma named.

## ⚑ MAJOR SYNTHESIS FINDING (2026-06-13 autonomous audit) — C-A is GENUINELY OPEN

The autonomous Thm 6.9 grind audited the whole §6 clock chain and found: the deep core (C-A front-shape
maintenance) is "discharged" by a CHAIN OF FILES, each REDUCING it to a carried `∀c` hypothesis that is
FALSE (a bunched/at-cap witness), then "deferred to another avenue" — but NEVER honestly proven over the
reachable domain. The false `∀c` hypotheses, all refutable by the SAME pattern:
- **Lemma 6.10** `hour_coupling_v2` : `∀c Regime` — FALSE (empty config, `clockCount 0 ≠ C`).
  REFUTATION VERIFIED IN LEAN: `Lemma610StoppedAzuma.regime_not_universal`. FIXED via stopped kernel.
- **clock_real_O_log_n** : `habs_mix_all` (∀c, Q_mix → support → Q_mix) — FALSE (a phase-3 clock with
  counter 0 at the minute-cap advances to phase 4, breaking `clockPhase3`; at-cap counterPos witness).
- **FrontNarrowConc** `rFrontNarrow_concentration_proven`/`clock_frontSync_via_narrow` : `hfeeder_all`
  (∀c, rBeyond(cap−1)=0 ∧ AllClockP3 ∧ card=n → RWithinEnvelope f₀ (cap−2)) — FALSE: n clocks bunched at
  minute cap−2 satisfy the LHS (rBeyond(cap−1)=0) but rFrontFrac(cap−2)=1 ≫ envelope (e.g. f₀=0 ⟹ env=0).
- **ClockFrontWidth** `rEnvelope_maintained` (∀c) — EXPLICITLY noted FALSE in its own docstring.

ALL follow the `regime_not_universal` pattern (verified-in-Lean exemplar). So C-A is NOT discharged: the
"proven" concentrations are conditionally-vacuous on false `∀c` deferrals.

HONEST TARGET (the genuine deep core, unchanged): the within-envelope maintenance over the REACHABLE
trajectory (NOT `∀c`), with the early-drip GHOST term (Doty Lemma 6.3). This is the multi-session piece
mapped in `CLOCK_FRONTSHAPE_ROADMAP.md` (avenues a/b/c). The fix PATTERN is the same as Lemma 6.10's:
replace the false `∀c` window with a STOPPED/reachable-restricted construction whose maintenance is the
genuine probabilistic concentration. The Lemma 6.10 stopped-kernel fix is the verified template.

## ROUTE PLAN v0 (architecture, PRE-PROOF — to refine with ChatGPT over several rounds)

User directive (2026-06-13): "先规划好路线, 不用贸然上证明" + "多走几轮" — architect first, multi-round ChatGPT.

The honest C-A discharge = prove FrontSync maintained whp over O(log n) steps, conditional on a SATISFIABLE
synchronized-start hypothesis (NOT a false ∀c). Four components:

COMPONENT 1 — the level-split (bulk vs leading).
  rFrontFrac(i) is decreasing in i (≈1 at i=0 → 0 at i=cap). Define the subcritical entry
  i₀ := largest level with rFrontFrac(i) ≥ θ (θ const, ~0.1). BULK (i ≤ i₀): fraction Θ(1), trivially within
  an envelope ≈ 1 — NO concentration. LEADING (i > i₀): fraction < θ subcritical, the doubly-exp squaring
  applies. The within-envelope invariant is non-trivial ONLY on the O(log log n) leading levels.
  OPEN Q (round 1): is i₀ cleanly Lean-definable on the actual config? Does the split give a clean structure?

COMPONENT 2 — the leading-front within-envelope maintenance (THE CORE).
  Union bound over the O(log log n) leading levels × O(log n) steps of the PROVEN squared seed
  (rBeyond_seed_le_rBeyondSq), PLUS the early-drip GHOST (Doty Lemma 6.3) for the bottom-of-leading levels
  where the bare squaring breaks (single lucky drip at tiny tail).
  OPEN Q (round 1): cleanest Lean formalization of the ghost that AVOIDS tracking per-agent provenance
  (e.g. a separate Chernoff over the O(log log n)·H interactions each with prob ≤ p·n^{−0.9})?

COMPONENT 3 — the stopped-kernel wrapper (the VERIFIED Lemma 6.10 template).
  front-shape regime = {leading front within envelope ∧ i₀ well-defined}. K* = piecewise{regime} K id.
  On the regime: per-step breach bounded (front_breach_le_capSq, PROVEN); off: frozen. ⟹ FrontSync-breach
  concentration for K* is HONEST (no false ∀c), conditional on the within-envelope START.
  OPEN Q (round 1): does the stopped-kernel template fit a MULTI-LEVEL invariant, or is a level-indexed
  family of stopped supermartingales cleaner? (Lemma 6.10 was a single supermartingale.)

COMPONENT 4 — the satisfiable entry + the remaining obligation.
  Entry: the synchronized phase-3 seam where the front is within envelope (satisfiable, from role-split/seam).
  Remaining genuine concentration = regime-confinement (trajectory stays within envelope whp) = Components 1-2.

ROUND PLAN: R1 (fired) — level-split + ghost + stopped-structure + minimal hypothesis. R2 — refine i₀ def +
ghost-negligibility Chernoff + exact union budget. R3 — entry hypothesis + wiring. THEN code (per user: no
rushing into proofs). The verified `regime_not_universal` + `Lemma610StoppedAzuma` are the templates.

## Anti-patterns (the campaign's traps)
NO false ∀-universal (the at-cap habs_mix trap, the ∀c Regime Lemma-6.10 trap); the within-envelope maintenance
must be over the REACHABLE/subcritical domain. Early-drip ghost is ESSENTIAL (bare squaring false at tiny tail).
Refutation-check every carried hypothesis FIRST.
