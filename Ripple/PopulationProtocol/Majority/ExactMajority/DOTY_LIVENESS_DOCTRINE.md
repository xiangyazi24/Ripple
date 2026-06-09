# Doty Theorem 3.1 — full faithful liveness (probabilistic §4 core)

**Directive (Xiang, 2026-06-06, voice):** 除非论文错了，或我们有更好的结论，否则不退缩、不躲。
The unconditional ∀ L K statement is false (L=0); the FAITHFUL paper theorem is at L=⌈log₂ n⌉ (paper line 251)
with n sufficiently large. Goal: prove `stable_majority_correct` faithfully — NO conditional dodge, NO partial.
This requires formalizing the paper's §4 probabilistic argument. Not a weakening, not a deferral: the paper's
actual theorem.

## Status going in
- sorry #1 (phase-4 tie callback) — CLOSED, axiom-clean (output-T invariant built; preserved locally).
- sorry #2 (small-pop / liveness) — open; the real content.
- The deterministic chain proves: from synchronized checkpoint, descent reaches a majorityStableEndpoint
  PROVIDED the protocol drives minorities out / reaches phase 10. The missing piece is exactly the paper's
  probabilistic liveness: minority eliminated by hour ⌈log₂(1/g)⌉ ≤ L w.h.p. (gap≠0 → unanimous majority),
  and tie (gap=0) settles to ±2^{−L} both-signs (detectable). At the n=2^L boundary the crude sum-bound
  card<2^L is too weak; need the hour-elimination argument.

## What the faithful theorem needs (the paper's §4)
1. Clock concentration: the drip+epidemic minute/hour clock gives Θ(log n) time per hour, hours synchronized
   w.h.p. (Doty §4 clock lemmas; "junta-driven phase clock" analogue).
2. Minority elimination: by hour h, opinionated agents split down to exponent h; minority count → 0 by
   hour ⌈log₂(1/g)⌉ ≤ L w.h.p. (Lemma 4.6 + the gap/exponent argument, paper lines 339, 2247, 1620).
3. Compose into: from any reachable config (n large), reach a majorityStableEndpoint w.p. 1 (eventually) —
   discharging the obligation `stable_majority_correct_of_majorityStableEndpoint_reachability` needs.

## Reusable machinery (already in unified Ripple — do NOT rebuild)
- SSEM/Probability/: expectedHittingTime, ProbHitWithin, drift→hitting bridges, expectedHittingTime_le_window_mul_inv,
  tail bounds, Freedman/martingale, RandomScheduler, SchedulerBridge, SelectionCount. (Martingale hitting-time toolkit.)
- PopProto/Convergence/: GeometricDrift, CentralSupermartingale, Drift, RegionBounds, RelativeChange
  (AAE 3-state supermartingale apparatus — multiplicative drift, geometric decay).
- ExactMajority/ existing: phase0_creates_two_clocks_general, phase_epidemic_reachability_from_config,
  the deterministic descent chain, phase4LocallyStable_initialGap_zero (the card<2^L crude version).

## Avenues (ranked)
(a) MAP-FIRST: precisely list every Doty §4 lemma needed to discharge the majorityStableEndpoint obligation;
    for each, identify reusable Ripple machinery vs genuinely-new. Produce the dependency DAG + difficulty.
(b) Clock concentration via PopProto GeometricDrift/Drift reuse (the drip clock is a multiplicative-drift process).
(c) Minority elimination via SSEM hitting-time + the exponent/hour induction.
(d) Compose → majorityStableEndpoint reachability → close sorry #2 → faithful theorem.

## Terminal conditions
SUCCESS: stable_majority_correct (faithful: L=⌈log₂ n⌉, n large) proven, 0 sorry, axioms clean, full build green.
HARD-STOP only: paper genuinely wrong (escalate), or a needed Mathlib probability primitive genuinely absent.
NO soft retreat to a conditional/partial statement.

## Note
This is the paper's probabilistic heart and connects to the Ho-Lin-Chen research direction. Treat as a real
multi-round campaign (like the SSEM complexity campaign), not a one-shot. Drive it round by round.
