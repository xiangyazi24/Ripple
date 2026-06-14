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

## ROUTE PLANNING — my own investigation findings (2026-06-13, pre-ChatGPT-round-1)

While ChatGPT reads xiangyazi24/Ripple @0062175 (family: scalar-potential/stopped-fit; family2: avenue-b
coupling), I audited the codebase myself:

FINDING 1 — the within-envelope MAINTENANCE is proven NOWHERE. Every front-shape lemma (abstract
`FrontShapeInduction` AND real `ClockFrontWidth`/`FrontNarrowConc`) ASSUMES `FrontWithinEnvelope`/
`RWithinEnvelope`/`hfeeder_all` as a hypothesis and proves CONSEQUENCES (the count cap, the empty-front,
the early-drip smallness). NO theorem CONCLUDES the maintenance. Grep confirms: no `→ FrontWithinEnvelope`
/ `→ RWithinEnvelope` maintenance theorem exists.

FINDING 2 — AVENUE (b) IS DEAD. The abstract `clockProto (Minute L₀)` model has the SAME gap: its
`frontShape_couples_earlyDrip` (within-envelope → count cap) and `early_drip_small_at` (the ghost bound)
are BOTH conditional on `FrontWithinEnvelope`/`hwin`. So coupling the abstract model to the real kernel
transfers a CONDITIONAL result — no free lunch. The genuine concentration (the probabilistic maintenance)
must be proven directly (avenue a), on the reachable/stopped domain.

FINDING 3 — NO scalar front potential exists in the codebase. So the KEY architecture decision (the family
question): can a SINGLE scalar potential Ψ_front = Σ_i w_i·rFrontFrac(i) (doubly-exp weights) be made a
supermartingale on the within-envelope regime — reducing C-A to ONE stopped Azuma (my verified
Lemma610StoppedAzuma template)? If YES → C-A closes by the exact Lemma 6.10 pattern. If NO → multi-level
union + early-drip-ghost Chernoff (harder). This is THE pivot; await ChatGPT family round 1.

REVISED ROUTE (converging): avenue (a) only [b dead]. The maintenance is the genuine open core, proven
nowhere. The stopped-kernel wrapper (Lemma 6.10 template) eliminates the false ∀c. The OPEN architecture
question = scalar-potential-supermartingale (one stopped Azuma) vs multi-level-union+ghost. Decide via
ChatGPT round 1, THEN code.

## ROUTE PLAN v1 (ChatGPT family round-1 @0062175, 2026-06-13) — the AGREED architecture

PIVOT RESOLVED: NO single scalar potential exists for the front-shape (unlike Lemma 6.10's Φ). So C-A
is NOT one stopped Azuma — it is a LEVEL-INDEXED family + an AUGMENTED GHOST KERNEL + a pathwise first-exit
union bound. The honest target is a PATHWISE stopped/first-exit statement, NOT ∀c.

THE ARCHITECTURE (one line):
  SyncStart ⟹ WindowGood + GhostSmall + SparseNoChain ⟹ CleanTail ⟹ FrontWidthOK.

THREE REGIMES (tail counts X_i := rBeyond(i)/C₀, NOT pointwise; ρ=0.1, ε=n^{−0.45}, ε_clean=n^{−0.4}, η=n^{−0.85}):
  bulk        X_i ≥ 0.1            — DELIBERATELY IGNORED (used only in deterministic front-width, via bulkIdx).
  mesoscopic  n^{−0.4} ≤ X_i ≤ 0.1 — the squaring recurrence X_{i+1} ≤ 0.9p·X_i² + D_{i+1}/C₀ (Lemma 6.3 + ghost).
  sparse      X_i < n^{−0.4}       — the seed-only union bound (where my PROVEN rBeyond_seed_le_rBeyondSq fits).

THE GHOST (essential, NOT "no early drips" — too strong): an AUGMENTED kernel. Either labeled descendant
sets `GhostState = {cfg, ghost : level → Finset AgentId}` or (for the multiset kernel) a DOMINATING
ghost-count `GhostDomState = {cfg, D : level → ℕ}` with one-step domination:
  P[D_i gets early immigrant | F_t] ≤ 1_{X_i<ε}·p·X_i²;  P[D_i grows by epidemic] ≤ 2D_i/n.
The ghost-count need not equal the true set — only dominate under a coupling. GhostSmall: D_i/C₀ ≤ η whp.
Negligible vs X_i² when X_i ≥ n^{−0.4} (X_i² ≥ n^{−0.8} ≫ n^{−0.85}) — THIS is why the clean recurrence uses n^{−0.4}.

STOPPED KERNEL: applied LOCALLY per level (`K63star i z = if Active63 i z then Kaug z else pure z`), NOT as
one global envelope drift. Active63 i = Phase3Window ∧ ε ≤ X_i ≤ ρ ∧ GhostSmall ∧ ParentWindowGood.

FOUR LAYERS:
  A (deterministic tail geometry): bulkIdx, MesoscopicCleanAt → squareEnvelope → FrontWidthOK. Consumes my
    EXISTING frontWidth_loglog / rFront_emptied_of_envelope.
  B (Lemma 6.3 window transfer + ghost): `lemma63_window_transfer` from 3 window ingredients
    (parent_tail_growth: X_i(t−L) ≤ a·X_i(t); drip_immigration ≤ b·p·X_i²·C₀; epidemic_amplification:
    nonGhost(t) ≤ γ(nonGhost(t−L)+imm)), constants γ(0.9a²+b)<0.9 [a≈0.84, b≈0.11, γ≈1.23, window L=0.1n].
    → `lemma65_clean_step_from_ghost` (0.9pX² + n^{−0.85} ≤ pX² for X ≥ n^{−0.4}). THE honest ∀c replacement.
  C (whp concentration): windowGood_all_levels_whp, ghostSmall_all_levels_whp, sparsePioneer_whp (Chernoff/
    Janson, union over levels×steps). My proven seed lemmas → sparsePioneer only.
  D (first-exit transfer): ShapeGoodPath (WindowGood ∧ GhostSmall ∧ NoSparsePioneer all t≤H) → FrontWidthOK
    deterministically; then `front_shape_exit_prob ≤ n^{−A1}+n^{−A2}+n^{−A3}` (pure union bound).

SyncStart HYPOTHESIS (SATISFIABLE — excludes the bunched-at-cap witness, which is NOT a synchronized entry):
  card=n ∧ Phase3ClockConfig ∧ C₀=clockCount ∧ C₀ ≥ κn ∧ InitialClockTail (X_0=1 ∧ ∀i>0 X_i=0, if minutes start at 0)
  ∧ no_ghost (D_0 = 0).

SCOPE: this is a LARGE multi-session build (the augmented ghost kernel is a new state space; the Layer-B
window argument + Layer-C concentrations are substantial). But the architecture is now CONCRETE and agreed.
ROUND 2 (next): refine the GhostDomState domination coupling (Layer B/C) + the augmented-kernel Lean
construction (is Kaug a clean Mathlib kernel?). family2 (avenue-b coupling) pending — my audit already killed it.

## family2 round-1 (avenue-b coupling) — CONFIRMS avenue (b) DEAD (2026-06-13 @0062175)

ChatGPT read the real code and confirms: the clock-minute projection `π(c) = (c.filter role=clock).map minute`
is a LAZY clockProto — `map π (K_real c) = p_clockPair·K_abs(π c) + (1−p_clockPair)·pure(π c)` (non-clock
interactions leave the clock subconfig unchanged), where `p_clockPair = clockCount(clockCount−1)/(card(card−1))`.
The laziness kills EXACT kernel functoriality (intertwining fails: condition "every sampled pair is clock-clock"
fails in the mixed protocol; clockProto sees mC clocks, real samples from n). AND: "the abstract file does NOT
prove a full reachable-trajectory maintenance theorem; it proves per-level squaring, envelope collapse, and a
CONDITIONAL early-drip handoff" — exactly my Finding 1. ⟹ avenue (b) dead (both my audit + ChatGPT-on-real-code).
USEFUL DETAIL retained: the lazy coupling `p_clockPair·K_abs + (1−p)·pure` may help Layer A/B relate the real
per-level squaring to the abstract envelope arithmetic (a lazy embedding), even though it doesn't transfer the theorem.

⟹ ROUTE PLAN v1 (avenue a, augmented ghost kernel, 4 layers) is the CONFIRMED route. Round 2: refine the
augmented-ghost-kernel Lean construction + the domination coupling (the hardest NEW object).

## ROUTE PLAN v2 — round-2 refinements (2026-06-13 @67fedb9)

### family2 R2 (Layer B): Layer B CANNOT be avoided for mesoscopic; write it FORWARD.
- KEY SIMPLIFICATION Q ANSWERED **NO**: the per-step squared seed (`rBeyond_seed_le_rBeyondSq`) only controls
  the FIRST seed into an EMPTY child level — NOT the child tail count once nonempty. Mesoscopic needs three
  things the seed lemma can't see: (1) parent normalization over the window; (2) cumulative drip-immigration
  concentration over L=0.1n steps; (3) epidemic AMPLIFICATION of immigrants. GhostSmall removes only the
  SPARSE early-drip ghost, NOT legitimate mesoscopic immigration/amplification. So: sparse `X_i<n^{−0.4}` →
  my seed lemmas ✓; mesoscopic `n^{−0.4}≤X_i≤0.1` → STILL need Layer B. Only the FORM simplifies.
- FORWARD FORM (do NOT formalize the past): rewrite `X_i(t−L) ≤ a·X_i(t)` as window-start `X_i(s) ≤ a·X_i(s+L)`,
  a `K^L` theorem from the window-start config; aggregate by integrating over the window-start distribution
  `∫ ((Kaug i)^L) z {bad} ∂((Kaug i)^τ c₀)`. No conditional-expectation, no past. Layer D unions over
  window-starts + first-exits. `lemma63_window_transfer_forward (i z) (hActive : Active63 i z) : (Kaug i ^ Lwin) z
  {z' | X(i+1) z' > 0.9 p X(i)²  + D(i+1)/C₀} ≤ ε_window`.
- EPIDEMIC MACHINERY @67fedb9: `ConstantDensityEpidemic.constantDensity_epidemic_O1_parallel` (forward growth
  lower bound, but CONSTANT-density 0.1n→0.9n only, not mesoscopic); `EpidemicTime` (analytic/conditional, not
  ready); `JansonHitting.milestone_hitting_time_bound` (generic milestone wrapper — the CLOSEST reusable, must
  specialize for multiplicative growth x→x/a in the mesoscopic range). The specific mesoscopic parent-growth
  lemma is NOT packaged — must build it (from JansonHitting).

### family R2 (augmented ghost kernel @67fedb9) — RESOLVED. ROUTE PLAN v2-FINAL below.

GHOST KERNEL CONSTRUCTION (resolved):
- INSTRUMENTED kernel `Kevent : Kernel cfg StepEvent` — samples the real interaction but RETAINS a certificate
  `StepEvent = {cfg', i, j, kind : ReactionKind, dripCoin, ...}`, with `map StepEvent.cfg' (Kevent c) = K c`.
- `Kaug z = map (updateAug z) (Kevent z.cfg)`, `updateAug z e = {cfg := e.cfg', D := updateD_from_event z e}`.
- EXACT cfg marginal: `map GhostDomState.cfg (Kaug z) = K z.cfg` (map_map + Kevent_cfg_marginal) ⟹ the augmented
  chain's cfg-projection IS the real protocol chain. `Kernel.map` for deterministic D-update; `Kernel.bind` if D
  needs extra dominating randomness. (A bare `Kernel.comp` is NOT enough — the D-update needs the realized transition.)
- DETERMINISTIC ghost from BARE cfg path = UNSOUND (multiset forgets provenance; worst-case overcharge destroys
  GhostSmall). Sound options: (B) deterministic from the INSTRUMENTED path (StepEvent certificate), or (C) a
  STOCHASTIC dominating count `KD_step` with `P[ΔD_i^imm]≤1_{X_i<ε}pX_i²`, `P[ΔD_i^epi]≤2D_i/n`. C is the v1 line.

GHOSTSMALL CONCENTRATION (resolved — REUSES MY VERIFIED TEMPLATE):
- D_i is NOT a supermartingale (positive drift `E[ΔD_i] ≲ 1_{X_i<ε}pX_i² + 2D_i/n`). So Lemma 6.10's Φ pattern
  does NOT apply to D_i directly. BUT the stopped-kernel WRAPPER applies per level:
  `KghostStar i = Kernel.piecewise {GhostActive i} Kaug Kernel.id` (exactly my Lemma610StoppedAzuma piecewise).
- The POTENTIAL is an EXPONENTIAL supermartingale `Ψ = exp(λ D_i − B_t(λ))` (predictable log-mgf compensator) —
  `∫ Ψ d(KghostStar i z) ≤ Ψ z` unconditionally by the SAME stopped-kernel case split, Chernoff read-off. THIS
  REUSES `AzumaKernel.expSupermartingale_drift` (the exp-MGF kernel drift I already used for Lemma 6.10) + my
  Lemma610StoppedAzuma piecewise wrapper. Or (Option 3, cleanest math) a direct dominating immigration+Yule
  branching Chernoff: D_{t+1} ≤ D_t + Bern(λ_t≤p n^{−0.9}) + Bern(2D_t/n); μ_imm ≤ O(n^{0.1} polylog) ≪ ηC₀=n^{0.15}.
- LOCALIZE: GhostSmall for level i holds ONLY in the LOCAL Doty Lemma-6.3 window (before/around X_i entering the
  mesoscopic band) — NOT the global O(log n) run (a tiny seed could eventually amplify too much over all time).

## ROUTE PLAN v2-FINAL — the Lean lemma chain (both round-2 answers synthesized, ready to code)
```
Kevent                    -- instrument real step; `map cfg' (Kevent c) = K c`  [NEW kernel object]
Kaug                      -- = map(updateAug) Kevent; `map cfg (Kaug z) = K z.cfg` (exact marginal)
K63star i / KghostStar i  -- = piecewise {Active63 i / GhostActive i} Kaug id    [my Lemma610StoppedAzuma piecewise]
ghostSmall_level_whp i    -- exp-supermartingale (AzumaKernel.expSupermartingale_drift) OR branching Chernoff; LOCAL window
ghostSmall_all_levels_whp -- finite union over leading levels
lemma63_window_transfer_forward i  -- FORWARD K^Lwin window-start; consumes GhostSmall; mesoscopic recurrence
                                      X(i+1) ≤ 0.9p X(i)² + D(i+1)/C₀  (parent-growth[JansonHitting] + imm + ampl)
lemma65_clean_step_from_ghost      -- 0.9p X² + n^{−0.85} ≤ p X² for X ≥ n^{−0.4}  [deterministic algebra]
sparsePioneer_whp         -- my proven rBeyond_seed_le_rBeyondSq + sparse-chain union (sparse regime only)
bulkIdx / MesoscopicCleanAt / FrontWidthOK  -- Layer A deterministic geometry; consumes frontWidth_loglog
front_shape_exit_prob     -- Layer D: ShapeGoodPath ⟹ FrontWidthOK (deterministic) + union ≤ n^{−A1}+n^{−A2}+n^{−A3}
```
START hypothesis: `SyncClockStart` (card=n ∧ Phase3 ∧ C₀=clockCount ∧ C₀≥κn ∧ InitialClockTail ∧ D₀=0) — SATISFIABLE,
excludes the bunched-at-cap witness. CODING ORDER: Layer A (low-risk, existing lemmas) → Kevent/Kaug scaffold +
the marginal theorem → K63star + ghostSmall_level (reuse Lemma610StoppedAzuma exp-drift) → Layer B forward → Layer D union.

## Anti-patterns (the campaign's traps)
NO false ∀-universal (the at-cap habs_mix trap, the ∀c Regime Lemma-6.10 trap); the within-envelope maintenance
must be over the REACHABLE/subcritical domain. Early-drip ghost is ESSENTIAL (bare squaring false at tiny tail).
Refutation-check every carried hypothesis FIRST.
