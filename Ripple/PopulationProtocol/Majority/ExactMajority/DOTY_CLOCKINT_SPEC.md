# Doty time-half — Avenue C2: clock re-composition (per-minute O(1) from S1+S2b+S3) → O(log n) clock

Directive: 绝对不退缩. The three §6 regimes are now proven at kernel/one-step level: S1 bulk (0.1→0.9 in O(1)
parallel, kernel-level), S2b front (one-step squaring on real chain + doubly-exp arithmetic), S3 early-drip
(kernel tail O(n^−0.85)). The general FRAMEWORK (WindowConcentration.lean) wraps drifts into PhaseConvergence.
This avenue INTEGRATES them: prove ONE minute advances in O(1) parallel time, then compose over the clock's
L₀=k·L levels → O(log n) clock, REPLACING the proven Θ(log²n) (ClockTimeConvergence.clock_composed_via_A0).

Repo: ~/.openclaw/workspace/projects/Ripple (local, NO .git). Build: nice -n 15 env LEAN_NUM_THREADS=2
~/.elan/bin/lake build <Module>. Read ALL of: Probability/ClockTimeConvergence.lean (the Θ(log²n) result +
clock model + honest verdict naming exactly this integration), Probability/ConstantDensityEpidemic.lean (S1),
Probability/FrontTailDecay.lean + FrontTailKernel.lean (S2/S2b), Probability/EarlyDripBound.lean (S3),
Probability/WindowConcentration.lean (framework), Probability/TimeComposition.lean + PhaseConvergence.lean
(A1 / compose_n_phases). Paper: ref/Doty-2021-exact-majority.txt Theorem 6.8 / Lemma 6.4 (the O(1)-parallel-
per-minute assembly from the three regimes).

## The integration (paper Lemma 6.4 / Theorem 6.8)
ONE minute advances in O(1) parallel time because the minute-count crosses via three combined regimes:
- early (S3): the over-eager front d≥ is O(n^−0.85) — negligible, doesn't gate;
- bulk (S1): once a constant fraction holds the minute, it spreads 0.1→0.9 in O(1) parallel;
- front (S2b): the last leaders' doubly-exp tail empties in O(1) (the O(log log n) front total is lower-order).
So per minute = O(1) parallel w.h.p. (failure 1/poly). Compose L₀ = k·L = Θ(log n) minutes (k const, L=⌈log₂n⌉)
⇒ clock total O(log n) parallel, failure ≤ L₀·(per-minute failure) = 1/poly via union (compose_n_phases / a
range-sum). This is `perMinuteO1` × `L₀` replacing A0's `Θ(log n)`-per-level in clock_composed_via_A0.

## Task (NEW file Probability/ClockOLogN.lean)
1. `perMinute_O1`: ONE minute level advances (all agents minute i → minute ≥ i+1, or the milestone) within
   t = C·n interactions (= O(1) parallel) with failure ≤ 1/poly(n), by COMBINING S1 (bulk crossing) + S2b
   (front emptying) + S3 (early-drip negligible) on that level. Use the framework where each regime is a
   window; the three combine by a union bound on the level's failure event. The substantive obligation:
   correctly stitch the three regimes' kernel bounds for one minute (the bulk gives the constant fraction, S2b
   the top, S3 bounds the early front) — match Lemma 6.4's accounting.
2. `clock_O_log_n`: compose `perMinute_O1` over L₀ = k·L levels (reuse ClockTimeConvergence's level structure +
   compose_n_phases / a Finset.range sum like clock_composed_total_le) ⇒ total interactions ≤ C·n·L₀ =
   O(n log n) (parallel O(log n)), failure ≤ L₀/poly = 1/poly. State it as the kernel-level
   (K^T) c₀ {¬ clock-synchronized} ≤ 1/poly with T/n = O(log n) — the upgrade of clock_composed_via_A0 from
   Θ(log²n) to O(log n).
3. If genuinely stuck stitching one regime into the per-minute (e.g. S2b's multi-level front still needs its own
   compose, or S3's transient bound doesn't directly slot in), do the stitch HONESTLY — build the missing
   per-minute glue — or STOP and report the precise missing lemma. Do NOT fake O(1)/minute.

## HARD RULES (automode, NO effort cap; 绝对不退缩)
NEW file ClockOLogN.lean only; do NOT edit existing files (S1/S2/S2b/S3/framework/clock/A1). Reuse all of them.
No sorry/admit/new axiom/native_decide. Iterate lake build until clean. Do NOT fake the O(1)/minute combination
— it must genuinely follow from S1+S2b+S3. If a regime doesn't slot in, STOP and report the exact glue lemma
needed. Do NOT git. Final message: perMinute_O1 + clock_O_log_n statements + bounds, how each of S1/S2b/S3 is
used, build verdict, #print axioms, honest status (clock now O(log n) kernel-level, or blocked on exact glue).
After this: remaining ~9 phases via framework → A1 doty_time_headline → the paper's O(log n) theorem.