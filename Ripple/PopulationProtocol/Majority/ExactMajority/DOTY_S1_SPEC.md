# Doty time-half §6 core — Avenue S1: constant-fraction epidemic in O(1) parallel time

Directive (Xiang): 不退缩，要论文的命题 O(log n)，不缩水. The clock keystone is PROVEN at Θ(log²n) via the
unit-coverage (pMin=Θ(1/n)) template; the paper's O(log n) needs the CONSTANT-DENSITY epidemic to cross
0.1→0.9 in O(1) PARALLEL time. S1 is the most central, most reusable missing piece.

Repo: ~/.openclaw/workspace/projects/Ripple (local, NO .git — do NOT git). Build:
nice -n 15 env LEAN_NUM_THREADS=2 ~/.elan/bin/lake build <Module>. Read: DOTY_TIME_SCOPING.md,
the clock file Probability/ClockTimeConvergence.lean (its honest-verdict doc lists S1/S2/S3 precisely),
A0's Probability/Phase2TimeConvergence.lean (harmonic/meanTime template, λ method), and CRUCIALLY the existing
Probability/EpidemicTime.lean theorem `epidemicTime_concentration_of_tail_bounds` (it is CONDITIONAL on exactly
the one-sided tails S1 must derive) + Probability/Epidemic.lean, Probability/Concentration.lean,
Probability/DiscreteChernoff.lean. Paper: ref/Doty-2021-exact-majority.txt §4 Lemma 4.5 + §6 Thm 6.9
(ln 9 < 2.2 bulk crossing).

## What S1 is
The "rumor epidemic" with a CONSTANT fraction already informed (density in [0.1, 0.9]) advances its informed
count by a constant factor per O(1) PARALLEL time — because at constant density the per-interaction advance
probability is Θ(1) (not Θ(1/n)): a uniformly random pair is informed×uninformed ∝ (0.1·n)(0.9·n)/n² = Θ(1).
Hence crossing 0.1→0.9 takes O(1) parallel time (paper: ≤ ln 9 + slack ≈ 2.2). This is the regime A0 did NOT
cover (A0 was unit-coverage, pMin=Θ(1/n), the slow tail of the epidemic).

## Task (NEW file Probability/ConstantDensityEpidemic.lean)
1. Read `epidemicTime_concentration_of_tail_bounds` precisely: what one-sided tail hypotheses does it take, and
   what does discharging them give? The goal is to PROVE those hypotheses for the constant-density regime, then
   instantiate it to get: starting from informed ≥ 0.1·n, within t = O(n) interactions (= O(1) PARALLEL),
   informed ≥ 0.9·n with prob ≥ 1 − exp(−Θ(n)) (or 1 − 1/poly).
2. The core probabilistic fact: in the constant-density window, the informed count is a submartingale with
   per-step drift Θ(1/n) and bounded increments — Azuma/Chernoff (use Probability/DiscreteChernoff.lean +
   Mathlib's `MeasureTheory`/`ProbabilityTheory` concentration: `ProbabilityTheory.measure_ge_le_exp...` /
   Hoeffding/Azuma if present) gives the one-sided tail. Concretely: over T = c·n interactions, the number of
   "advancing" steps concentrates around its mean (≥ Θ(T/n)·n = Θ(T)) with exponential tails.
3. Deliver: `constantDensity_epidemic_O1_parallel (n) (hn)` — from informed ≥ ⌈n/10⌉, the kernel reaches
   informed ≥ ⌈9n/10⌉ within t ≤ C·n interactions with failure ≤ 1/n (or exp(−Θ(n))). State it so it composes
   with the clock (the clock's per-minute bulk crossing) to replace the Θ(log n)-per-level template with
   O(1)-per-level, upgrading clock_composed to O(log n).

## HARD RULES (automode, NO effort cap — this is the paper's §6 probabilistic core; 不退缩)
NEW file ConstantDensityEpidemic.lean only; do NOT edit existing files. Reuse DiscreteChernoff/Concentration +
Mathlib concentration. No sorry/admit/new axiom/native_decide. Iterate lake build until clean. This is genuinely
hard. If a specific Mathlib concentration primitive (Azuma for bounded-difference submartingales, or a
Chernoff/Hoeffding form) is genuinely ABSENT, identify it EXACTLY and either build a self-contained version or
STOP and report the precise primitive + where the paper uses it — do NOT fake. Do NOT git. Final message: the
constant-density tail lemma + the O(1)-parallel crossing theorem (statements + bounds), how it discharges
epidemicTime_concentration_of_tail_bounds, build verdict, #print axioms, and the honest status (proven / blocked
on exactly-named primitive). This is the keystone-within-the-keystone; full O(log n) follows from S1 + S2 + S3.