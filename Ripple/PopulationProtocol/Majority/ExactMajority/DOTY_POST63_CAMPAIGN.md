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

## Phase E — expected time  [~8–15 bricks; ONE unscoped piece]

whp → E[T] = O(log n) needs a fallback bound: from ANY reachable config, stabilization within
poly(n) time with constant probability (then geometric restart argument). The paper's argument
lives around §3/Thm 3.1's wrap-up — SCOPING READ REQUIRED before speccing (this is the only
remaining item whose math we have not fully mapped). Candidate route: correctness half's
reachability + coarse coupon-collector epidemic bounds.

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
