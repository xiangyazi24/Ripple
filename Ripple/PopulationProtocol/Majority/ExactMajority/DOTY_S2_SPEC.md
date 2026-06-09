# Doty time-half §6 core — Avenue S2: doubly-exponential FRONT tail (Theorem 6.5)

Directive: 不退缩，论文的 O(log n)，不缩水. S1 (constant-density bulk 0.1→0.9 in O(1) parallel) is PROVEN.
S2 is the front-tail half: the leading minutes (the O(log log n)-width front of the clock distribution) shrink
DOUBLY-exponentially, which is what lets the front not bottleneck the O(1)-per-minute accounting (paper footnote 9).

Repo: ~/.openclaw/workspace/projects/Ripple (local, NO .git). Build: nice -n 15 env LEAN_NUM_THREADS=2
~/.elan/bin/lake build <Module>. Read: the clock honest-verdict in Probability/ClockTimeConvergence.lean
(lists S2 precisely), S1's Probability/ConstantDensityEpidemic.lean (its new primitive lintegral_decay_on_absorbing
+ windowPot_contracts_on_floor + advance_prob_ge — REUSE), Probability/DiscreteChernoff.lean,
Probability/Concentration.lean. Paper: ref/Doty-2021-exact-majority.txt Theorem 6.5 (front tail
`c≥i+1(t) < p·c≥i(t)²` type doubly-exponential decay) + the surrounding §6.

## What S2 is (from the paper)
The "front" of the minute distribution = the small set of agents at the HIGHEST minutes (the leaders). The paper's
Theorem 6.5 shows this front decays doubly-exponentially: if a fraction c≥i are at minute ≥ i, then the fraction
at minute ≥ i+1 satisfies `c≥i+1 ≲ p·c≥i²` (squaring each step ⇒ doubly-exponential in the number of steps).
This is why the leading O(log log n) minutes cost only O(1) parallel total (not O(log log n)), keeping the
per-minute accounting at O(1).

## Task (NEW file Probability/FrontTailDecay.lean)
1. Read Theorem 6.5's exact statement in the paper + identify the random quantity (c≥i = fraction at minute ≥ i,
   under the drip+epidemic clock). The drip reaction Ci,Ci→Ci,Ci+1 advances a leader only when TWO leaders meet
   ⇒ rate ∝ c≥i² (the squaring); epidemic only spreads existing max, doesn't create new front. So the front
   advance is a quadratic-rate process.
2. Formalize the one-step front bound: E[c≥i+1 after Δt] ≤ p·c≥i² + (small), i.e. the count at the top minute
   grows only quadratically-suppressed. Use the scheduler pair-selection prob (two top-minute agents meet
   w.p. ∝ (top count)²/n²) — reuse S1's advance_prob_ge style derivation but for the SQUARED (two-leader) event.
3. Compose over the front minutes: doubly-exponential decay ⇒ the front O(log log n) minutes are all crossed in
   O(1) total parallel time w.h.p. Deliver a lemma `frontTail_O1_parallel` (or the per-step `frontTail_step`)
   stating the front contribution to the clock time is O(1) parallel with failure ≤ 1/poly.

## HARD RULES (automode, NO effort cap; 不退缩)
NEW file FrontTailDecay.lean only; do NOT edit existing files. Reuse S1's primitives (lintegral_decay_on_absorbing,
the advance-prob derivation), DiscreteChernoff/Concentration, Mathlib probability. No sorry/admit/new
axiom/native_decide. Iterate lake build until clean. Genuinely hard §6 probability. If a specific Mathlib
concentration/large-deviation primitive is genuinely ABSENT, name it EXACTLY and either build self-contained or
STOP and report precisely (+ the paper lemma using it) — do NOT fake. Do NOT git. Final message: the front-tail
lemma(s) (statements + bounds), how it reuses S1, build verdict, #print axioms, honest status (proven / blocked
on exactly-named primitive). After S2: S3 (early-drip Lemma 6.3), then re-compose clock with S1+S2+S3 → O(log n).