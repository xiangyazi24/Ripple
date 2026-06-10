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
- **E2** Lemma 7.7: Phase-10 backup expected O(n log n) parallel time. Correctness-side
  infrastructure exists (Analysis/Phase10Backup.lean: signed sums, active counts). Probability
  side: cancel/spread reactions at rate ≥ activeCount²/n²-style → coupon-collector/geometric
  sums. Uses E1's geometric-tail on the active-count potential.
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
