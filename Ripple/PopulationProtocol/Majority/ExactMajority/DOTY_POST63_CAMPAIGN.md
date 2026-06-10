# Doty Thm 3.1 time half — the post-Lemma-6.3 campaign plan

_Drafted 2026-06-09 evening, while agent 3 closes the last Lemma-6.3 wiring item (hB).
Position at drafting: windowedFrontProfile_whp + goodFrontWidth_whp + climbBound_whp landed on the
real kernel (0-sorry, axiom-clean, uisai2-verified ×3). This file plans everything from there to
the unconditional Theorem 3.1 time half._

## Where the campaign stands

PROVEN (real kernel, whp, modulo the hB instantiation in flight):
- The §6 coupled time-window engine: per-level squaring recurrence (Thm 6.5 windowed form),
  GoodFrontWidth = the moving-frame width invariant, ClimbBound. This was the deep core.
- Lemma 6.10 hour coupling (HourCouplingV2, Azuma) — proven earlier, not yet wired.
- Phases 2 & 9 untimed PhaseConvergence instances.
- The abstract AND transferred real-kernel per-minute clock machinery (ClockReal* chain) — but its
  FrontSync maintenance still consumes the FALSE `hwin_all`; that consumption is what Phase B fixes.
- Correctness half: complete (stable_majority_correct).

## Phase B — the clock rewire (drop `hwin_all`)  [first; ~12–18 bricks]

Goal: the real-kernel per-hour O(log n) clock as an unconditional whp theorem.
1. **Fix the concrete parameters ONCE, up front**: θn(n), tt(n), w(n), KK(n), Tcap, the scale
   floor N₀ (currently n ≥ 25641, θn ≥ 30000 carried abstractly). Every later discharge uses these;
   choosing them first avoids rework. Deliverable: a `DotyParams`-style structure or a fixed set of
   defs + the norm_num facts they satisfy.
2. Discharge the carried scale hypotheses of windowedFrontProfile_whp_packaged / goodFrontWidth_whp /
   climbBound_whp at those parameters → clean whp statements with hypotheses `N₀ ≤ n` only.
3. Rethread the FrontSync consumers: FrontSyncConc / ClockFrontWidth / ClockEnvMaint /
   ClockFullJoint currently carry `hwin_all` (FALSE as ∀-reachable). Replace the input with the
   GoodFrontWidth-whp event via `frontSync_of_goodWidth_of_bulk_below` (deterministic glue, proven)
   + a horizon union. NOTE: not a find-replace — the existing statements are shaped for a
   deterministic invariant; they need whp-event versions (mirror how real_front_squares_whp wraps
   its event). Audit each consumer file for what it actually needs.
4. Re-derive `clock_real_faithful_O_log_n` (the composed per-hour clock) on the rewired inputs;
   retire the false-hypothesis variants; update `clock_honest_verdict`.

## Phase C — the timed phase instances  [the volume; ~25–35 bricks; PARALLELIZABLE]

A1's `compose_n_phases` (PhaseConvergence.lean) needs 11 instances; 2 & 9 exist. Remaining:
- Phase 3 = the clock itself → falls out of Phase B (the big one).
- Phases 0, 1: initialization + role assignment + smallBias counters. Includes the **clock-count
  Θ(n)** concentration (the role split) — an input the clock constants implicitly need; make it
  explicit here.
- Phases 4, 5, 6, 7, 8, 10: per-phase epidemics / counter timeouts at constant fraction — A0-style
  analyses on existing machinery (ConstantDensityEpidemic, WindowConcentration, stdCounter timing,
  the new gated engines where rates are conditional).
PARALLELIZATION: each phase analysis goes in ITS OWN new file (Phase4Convergence.lean, …) so
multiple subagents can run concurrently without single-file races. Phase 2/9's existing instance
(Phase2Convergence.lean) is the template.
Risk note: phases 5–8 interact with Reserve agents & sampling (paper §7.1) — read the paper section
before speccing each; do not guess the per-phase event structure.

## Phase D — composition  [~8–12 bricks]

1. Wire Lemma 6.10 (hour_coupling_v2) + the Phase-B clock into the phase-3 timed instance
   (hours advance together ⟹ the phase-3 window closes in O(log n)).
2. `compose_n_phases` with all 11 instances → `doty_time_headline` UNCONDITIONAL:
   stabilization in O(log n) parallel time whp. Update every honest-verdict marker.

## Phase E — expected time  [~8–15 bricks]  — SCOPED 2026-06-10 (paper read done)

Paper's argument (§7 wrap-up, "We finally justify that the expected stabilization time is
O(n log n) [interactions]"): three-event split AT TIME 0, not a from-any-reachable-config restart:
- **Good** (whp ≥ 1 − O(1/n²)): all phase whp-events hold → stabilize in O(log n) parallel time.
- **Bad-with-big-clock** (prob ≤ O(1/n²), |C| ≥ 0.24n by Lemma 5.2 whp): timed phases still
  advance via counters in expected O(log n) each (Thm 6.9 + Chernoff on counter rounds), untimed
  phases pass by epidemic expected O(log n) → reach backup Phase 10, which stabilizes in expected
  O(n log n) parallel time (**Lemma 7.7**). Contribution O(1/n²)·O(n log n) = o(1).
- **Tiny-clock** (|C| = o(n); note |C| ≥ 2 always by Lemma 5.2's deterministic part, and |C| is
  FIXED after Phase 0): probability super-polynomially small; conditional time at most poly(n)
  (counter decrements at rate ≥ |C|/n ≥ 2/n). Negligible product.

Lean bricks:
- **E1** `Probability/ExpectedHitting.lean` (NEW): hitting-time expectation toolkit on kernel
  powers. E[T] = ∑_t P(T > t) (or block form E[T] ≤ s·∑_k P(T > k·s)); the geometric-tail lemma
  (∀ config in a closed class, P(not done in s steps) ≤ q ⟹ P(T > k·s) ≤ q^k ⟹ E[T] ≤ s/(1−q));
  the conditioning-free split E[T] ≤ t₀ + ∑_{t≥t₀} P(T>t). Generic, no protocol content.
  **DONE 2026-06-10** (0-sorry, axiom-clean = [propext, Classical.choice, Quot.sound] on all 13
  thms; single-file EXIT_0). Generic over `K : Kernel α α` `[IsMarkovKernel K]` + fixed measurable
  `Done` set + absorption hyp `∀ x ∈ Done, K x Doneᶜ = 0` (matches GeometricDrift's generic style,
  so it applies directly to `(NonuniformMajority L K).transitionKernel`). Design choice: closure
  class is taken to be `Doneᶜ` itself — the per-block hypothesis is `∀ b ∈ Doneᶜ, (K^s) b Doneᶜ ≤ q`
  ("from every not-done state, s steps finish w.p. ≥ 1−q"), no separate invariant-class bookkeeping
  needed. `expectedHitting K c Done := ∑' t, (K^t) c Doneᶜ` (= E[T] under the standard tail-sum
  identity). Delivered (signatures abbreviated, all in namespace `ExactMajority`):
  - `expectedHitting` (def), `expectedHitting_eq_tsum`.
  - `bad_antitone` / `bad_antitone_le` — `(K^t) c Doneᶜ` antitone in `t` from absorption (Lemma 0).
  - `pow_absorbing` — `Done` absorbing for 1 step ⟹ absorbing for m steps.
  - `expectedHitting_le_block` — `E[T] ≤ s · ∑' k, (K^(k·s)) c Doneᶜ` (block form, `s ≠ 0`).
  - `bad_block_contracts_from` / `bad_block_contracts` — `(K^(m+s)) c₀ Doneᶜ ≤ q·(K^m) c₀ Doneᶜ`.
  - `bad_block_geometric` — `(K^(k·s)) c₀ Doneᶜ ≤ q^k`.
  - `expectedHitting_geometric` — `E[T] ≤ s · (1−q)⁻¹`.
  - `kernel_pow_le_one`, `expectedHitting_split` — `E[T] ≤ t₀ + ∑' t, (K^(t₀+t)) c Doneᶜ`.
  - `tail_le_block`, `bad_block_geometric_from` — shifted-base block + geometric helpers.
  - `expectedHitting_split_geometric` — **Phase-E4 capstone**: hyps `(K^t₀) c₀ Doneᶜ ≤ δ` +
    per-block `q` (`s≠0`) ⟹ `E[T] ≤ t₀ + δ·s·(1−q)⁻¹`. Nothing left out.
- **E2** Lemma 7.7: Phase-10 backup expected O(n log n) parallel time. Correctness-side
  infrastructure exists (Analysis/Phase10Backup.lean: signed sums, active counts). Probability
  side: cancel/spread reactions at rate ≥ activeCount²/n²-style → coupon-collector/geometric
  sums. Uses E1's geometric-tail on the active-count potential.
  **PARTIAL 2026-06-10** (generic engine complete, capstone reduced to ONE strong-Markov lemma;
  0-sorry, axiom-clean = [propext, Classical.choice, Quot.sound]; both files single-file EXIT_0).
  Convention: all bounds in INTERACTION COUNTS (= kernel steps); parallel time = interactions/n,
  so cancel = O(n²), coupon stages = O(n² log n) each. Delivered:
  - `ExpectedHitting.lean` (appended, generic): `expectedHitting_one_step` (one-step success ≥ p ⇒
    E[T] ≤ p⁻¹), `expectedHitting_one_step_q` (failure ≤ q ⇒ E[T] ≤ (1-q)⁻¹). SHAs ceb63d86.
  - `Probability/Phase10ExpectedTime.lean` (NEW). Generic `Coupon` section over `K : Kernel α α`,
    `Φ : α → ℕ`, `Done = potDone Φ = {Φ = 0}`:
    * `potDone/potAbove/potBelow` (+ measurable/compl), `compl_potDone`.
    * **chaining** `bad_split_through_mid`, `expectedHitting_le_through_mid`
      (`Done ⊆ Mid` ⇒ E[hit Done] ≤ E[hit Mid] + ∑ₜ P(Mid∖Done at t)). SHA d101ca6f.
    * **occupation engine** `PotNonincr K Φ` (one step never raises Φ), `potBelow_absorbing`,
      `pow_above_eq_zero_of_start_le` ({Φ>m} stays 0-mass from Φc≤m), `level_occ_contract`,
      `level_occ_geometric`, `level_occ_expectedHitting` (CONSTRAINED start Φc≤m ⇒
      E[hit {Φ<m}] ≤ (1-q)⁻¹). SHA 3c8ad20b.
    * **coupon assembly** `occLevel`, `expectedHitting_eq_tsum_occLevel` (exact occupation
      decomposition E[hit Done] = ∑'ₘ occLevel(m+1)), `coupon_expectedHitting_le_of_occBounds`
      (per-level occ ≤ (1-qₘ)⁻¹ + high-level vanishing ⇒ E[hit Done] ≤ ∑_{m=1}^M (1-qₘ)⁻¹,
      the harmonic sum). SHA e2e1849e.
  - **BLOCKER (single, precisely isolated)** SHA dee0ef4c: the capstone needs `occLevel K Φ m c ≤
    (1-qₘ)⁻¹` for ARBITRARY start (strong-Markov first-passage). `level_occ_expectedHitting`
    proves the CONSTRAINED-start (Φc≤m) version; the gap is purely the first-passage restart
    (occLevel m c = ∫_b occLevel m b d(Kc) for Φc>m ⇒ occLevel is harmonic above level m, bounded
    by the constrained value at first entry into {Φ≤m}). Needs ~first-passage occupation identity,
    not yet a generic kernel lemma here. Once it lands, `coupon_expectedHitting_le_of_occBounds`
    closes the harmonic bound immediately.
  - **Phase-10 instantiation target** (documented in file): K = (NonuniformMajority L K).transitionKernel;
    cancel Φ=activeBCount, absorb-T/convert-passive Φ=wrongACount; needs (1) PotNonincr from
    support-wide non-increase (easy: no reaction creates active-B / un-A's an A), (2) per-level
    drop qₘ = 1 - m/(n(n-1)) — the **state-multiplicity** subtlety: "active A" is a CLASS of
    AgentState records, so `Phase2TimeConvergence.step_advance_prob`'s single-pair technique must
    be aggregated over the class via `interactionCount` additivity, (3) ∑ n(n-1)/m = n(n-1)Hₙ.
    Stage chaining via `expectedHitting_le_through_mid`, majority/tie split via backupSignal sign.
- **E3** Conditional progress: from any config with |C| ≥ 2 (post-Phase-0), each timed phase ends
  within expected O(n/|C| · log n)-shape time (counter always ticks); gives both the bad-event
  O(log n) (|C| ≥ 0.24n) and the tiny-clock poly(n) bound from ONE parameterized lemma.
- **E4** The time-0 three-event split + summation: good whp event (Phase D headline) + Lemma 5.2
  clock-count concentration (Phase C, phases 0/1 line) + E2 + E3 → `doty_expected_time_O_log_n`.
Dependencies: E1, E2 are independent of Phases B–D (parallelizable NOW); E4 needs D's headline +
C's clock-count concentration.

## Phase F — audit, headline, release  [~6–10 bricks]

1. Repo-wide independent audit: axioms per theorem (not just the newest), no undischarged
   `_of_X`-style reduction hypotheses smuggling assumptions, no vacuous `True := trivial` markers
   standing in for content.
2. The single clean headline `theorem doty_thm31_time` with hypotheses `N₀ ≤ n` + protocol
   assumptions only.
3. Release per the standing 铁律: canonical → xiangyazi24/Ripple main 推平, verified tag,
   REPO_COPIES.md reconciliation. Blog 027 time-claim un-retraction (it was retracted 2026-06-06;
   the claim becomes true again — write the correction honestly, referencing the retraction).
4. DNA32 poster material refresh (deadline 2026-05-25 has passed — check what the poster actually
   needed; the showcase value remains for the Ho-Lin Chen project foundation).

## Order & rationale

B → C(parallel) → D → E → F. B first because every later phase consumes the clock and the
parameter choices; C parallelizes once B's parameters are fixed; D is pure composition; E has the
one scoping unknown (start its paper-read during C's parallel waits); F is hygiene + shipping.

## What we are explicitly NOT doing (scope fence)

- Space optimality (the paper's state-count side beyond state_count_poly_bound) — out of scope.
- The Θ(n log n)-interactions-vs-parallel-time conversion subtleties beyond what the existing
  parallel-time wrappers already handle.
- SSEM (Kanaya et al.) — separate, already complete.

## OVERNIGHT COORDINATION (2026-06-10 night; multiple windows live)

Line assignments to avoid file races (each line owns its files exclusively):
- **family (this line): Phase B** — DotyParams + scale-hypothesis discharge (incl. the hB ladder
  ceiling facts) in a NEW file `Probability/DotyParams.lean`, then the FrontSync consumer rethread
  (FrontSyncConc/ClockFrontWidth/ClockEnvMaint/ClockFullJoint edits) — these existing files are
  family-line-owned tonight.
- **family2 / family3 (when they come up): Phase C phase instances** — ONE NEW FILE PER PHASE
  (Phase4Convergence.lean, Phase5Convergence.lean, …), template = Phase2Convergence.lean. Suggested
  split: family2 takes phases 0/1 (+ the clock-count Θ(n) role-split concentration), family3 takes
  4/5/6 (read paper §7.1 FIRST for 5/6 Reserve-agent structure). Phases 7/8/10 next. Do NOT touch
  EarlyDripMarked.lean, ClockFrontProfile.lean, or any family-line file.
- Commit per lemma, push, sync-ripple-wip.sh, 0-sorry/axiom-clean discipline as per the doctrine.
- ChatGPT consults run from the family line (the family tab holds the repo connector); other lines
  request consults by writing questions into /tmp/gpt_requests_<line>.md and pinging family chat.

## Phase B step 3 — ARCHITECTURE SETTLED (2026-06-10 night, family line)

Findings (verified in code, not speculation):
1. **post_absorbing is dead weight in composition.** `compose_two_phases`/`compose_n_phases`
   never USE the field — only re-package it. → `PhaseConvergenceW` (no absorption) +
   `composeW_two/n_phases` + `PhaseConvergence.toW` landed in
   `Probability/PhaseConvergenceWeak.lean` (B-3b, identical proofs).
2. **Endpoint bridge landed** (`Probability/ClockFrontSyncFromWidth.lean`, B-3a): general
   level-i emptiness `rBeyond_eq_zero_of_goodWidth_of_bulk_below` + measure-union bridges
   `frontSync_whp_of_goodFrontWidth` / `capFeederEmpty_whp_of_goodFrontWidth` (abstract side
   event P matching goodFrontWidth_whp's carried conjunct).
3. **The remaining crux is clock_real_step's INTERNAL habs_mix** (ClockRealBulk ~353/423,
   ClockRealMixed ~1118: the drift windows must be absorbing ALONG the leg). Route:
   **killed kernel.** `GatedDrift.real_le_killed` (GatedGeometricDrift.lean:139) is the
   UNCONDITIONAL coupling `(K^t) x {bad} ≤ (killK^t) (some x) {none ∨ some bad}`; with
   measure_union_le this gives the master decomposition
     real {¬Post at leg end} ≤ killed {some ¬Post} + killed {none}
   — (a) `killed {some ¬Post}`: re-run clock_real_step's seed/bulk MGF on `killK κ Q_mix-gate`
   where the window is absorbing BY CONSTRUCTION (killK_drift pattern);
   (b) `killed {none}` = escape mass = Q_mix breach along the leg, bounded by per-step squared
   cap-seed on width-good configs + per-leg width re-certification (goodFrontWidth_whp_concrete
   at minute boundaries via the B-3a bridge). NO new coupling machinery needed.
4. Outstanding for step 3: classify every habs_mix use inside clock_real_step's callees
   (drift-absorbing vs endpoint-transport — ChatGPT letter 2 in flight, task output
   /tmp/gpt_a_phaseB2.out), then `clock_real_step_gated` + minuteStepPhaseW instances +
   composeW. Escape-budget arithmetic at DotyParams' concrete parameters.

## Phase B step 3 — horizon/start audit results (ChatGPT letter 4, family3, 2026-06-10 ~4am)

1. **Checkpoint prefixes are free**: windowedFrontProfile_whp at τ = j·w is the SAME theorem with
   KK := j (hsmall at w·j follows from hsmall at w·KK since j ≤ KK and the base > 1 — check
   direction when wiring). Remainders τ = j·w + r need ONE generic lemma
   `checkpoint_composition_prefix` (invariant_union_bound's split + a terminal r-block; hrem input
   `∀ x, Inv x → (Kk^r) x {¬Inv} ≤ δr`). No new probability.
2. **ClimbBound side is already horizon-free** (climb_real_tail/climbBound_whp take free t; the
   DotyParams wrapper kept t free).
3. **Start conditions (the real crux)**: recInv does NOT follow from Q_mix + AllClockP3 + card.
   All-clean lift ⟹ MarkInv (markInv_of_clean) + taintedCount = 0, but recInv only via
   window-closed (recInv_of_window_closed: ¬AllClockP3 ∨ rBeyond > n/10). At a mid-run minute
   boundary with AllClockP3 ∧ open window, a FRESH all-clean lift fails recInv (cleanAbove = full
   tail ⟹ recurrence inequality false in the window). ⟹ **Design: ONE marked chain per clock run**,
   started at the phase-3 entry (where ¬AllClockP3 ⟹ recInv all T via h0_params), maintained whp
   by the §6 engine itself (window_failure_le per window); the per-minute escape accounting reads
   real-kernel prefix events off this single chain via markedK_pow_erase (horizon/event free) +
   checkpoint prefixes. Do NOT re-lift per minute.
4. Targets sketched by the letter: wfpPrefixBound/climbPrefixBound defs + goodFrontWidth_whp_prefix
   (∀ τ ≤ M family). New-lemma list: checkpoint_composition_prefix (+ a δRem r-horizon window bound,
   supplied as input).

## Phase B step 3 — the COMPLETE prefix ladder (letter 4 full version; acceptance spec for the
WidthPrefix brick)

Five wrapper lemmas, no new probability (1-2 generic, 3-5 are copies of existing proofs with the
prefix lemma substituted):
1. `checkpoint_composition_prefix` — j full windows via checkpoint_composition + one terminal
   r-block (split intermediate state on Inv; charge δRem on Inv, complement absorbed in prior mass).
2. `recurrence_checkpoint_prefix` — specialize to Inv := recInv, Kk := markedK; window_failure_le
   for both block types (full-w and remainder-r; the r-horizon hB input may be carried as δRem).
3. `front_squares_whp_prefix` — copy front_squares_whp; recurrence_checkpoint →
   recurrence_checkpoint_prefix; markInv_ae_pow at τ; tainted_marked_tail_explicit at t := τ.
4. `real_front_union_prefix` — copy real_front_union; markedK_pow_erase at τ; union over T < Tcap.
5. `windowedFrontProfile_whp_prefix` — copy windowedFrontProfile_whp; deterministic subset
   (windowedFrontProfile_of_not_bad) unchanged; real_front_union → real_front_union_prefix.
Then `goodFrontWidth_whp_prefix` (∀ τ ≤ M family): wfpPrefixBound (j := τ/w, r := τ%w; per-T sum of
j·δWin T + δRem T r + killK-none at τ + tainted MGF at τ) + climbPrefixBound (already free-t side).
Pure-wrapper facts: climbBound side free in t; markedK_pow_erase free; neg conjunct droppable via
neg_params. The only open engineering point: supplying hBrem (r-horizon per-window engine at the
scale hypotheses, or a coarse uniform δRem for partial windows).

## Phase B step 3 — letter 2 full version addenda (2026-06-10)

- DONE already: kill_escape_le_prefix_union (B-7, single side-set S form — instantiate S :=
  W ∧ B ∧ P and split the prefix sums by set-inclusion at the caller), PhaseConvergenceW (B-3b),
  endpoint bridges (B-3a), prefix machinery (WidthPrefix brick in flight).
- OPTIONAL polish (not on critical path): exact survivor projection
  `killK_pow_someSet_eq_liveK_pow` via sub-Markov `liveK := piecewise G K (const 0)` — the Option
  analogue of markedK_pow_erase; our killed_alive_le_real is the inequality version and suffices.
- The killed minute phase skeleton (names locked): Qgate/κQ abbrevs, killedMinutePre/Post (none ∈
  Post — escape paid separately, drift never bounds it), clock_killed_stepW :
  PhaseConvergenceW (κQ n mC T) via composeW_two_phases of killed seed/bulk legs (alive branch =
  rSeedPot_contracts_seed / rSeedPot_contracts_bulk; off-gate successor = none ∈ Post),
  clock_real_step_gated (real_le_killed + split none ∪ alive-bad + hesc), clock_real_step_gatedW
  (PhaseConvergenceW on the REAL kernel, ε = εseed+εbulk+εesc as ℝ≥0) — feeds composeW_n_phases
  exactly where faithfulMinutePhases sat. ε_leg := M·qQ + ∑_{τ<M}(εW+εP+εB)(τ); qQ = 0 if the
  phase/counter side gates are deterministic on the good event, else folded into εP.
- HIGH-RISK unknown still open (letter 3, family2, in flight): whether
  WindowConcentration.windowDrift_PhaseConvergence and the seed/bulk drift lemmas are
  kernel-parametric (instantiable at κQ) or hard-code the real kernel (→ minimal generalization
  needed).
