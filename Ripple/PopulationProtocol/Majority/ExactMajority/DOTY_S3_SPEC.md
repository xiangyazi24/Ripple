# Doty time-half §6 — Avenue S3: early-drip set bound (Lemma 6.3)

Directive: 绝对不退缩. Third and last of the three §6 pieces (S1 bulk ✓, S2/S2b front ✓, S3 early-drip). With
S3, the clock's per-minute cost is bounded O(1) for ALL three regimes (bulk/front/early), enabling the clock
re-composition Θ(log²n) → O(log n).

Repo: ~/.openclaw/workspace/projects/Ripple (local, NO .git). Build: nice -n 15 env LEAN_NUM_THREADS=2
~/.elan/bin/lake build <Module>. Read: the NEW framework Probability/WindowConcentration.lean
(`windowDrift_PhaseConvergence`, `windowGrowth_PhaseConvergence`, `measure_ge_thresh_on_absorbing` — USE these,
the wrapping is now free), S1's Probability/ConstantDensityEpidemic.lean (advance_prob_ge, the bulk),
S2's Probability/FrontTailDecay.lean (dripPair_prob_le_sq), Probability/DiscreteChernoff.lean,
Probability/Concentration.lean. Paper: ref/Doty-2021-exact-majority.txt Lemma 6.3 + the early-drip discussion
(~lines 1839-1960: d≥i = "early drip" mass, the front-of-the-front before epidemic catches up).

## What S3 is (paper Lemma 6.3)
The "early-drip" set d≥i+1 = agents that have dripped to minute ≥ i+1 BEFORE the epidemic bulk reaches minute i
— the over-eager leaders. Lemma 6.3: d≥i+1 = O(n^{−0.85}) (a tiny fraction), via non-uniform large deviations:
the drip is a rare event (prob Θ(1/n) per pair) and over the relevant window the count concentrates below
n·n^{−0.85} = n^{0.15} w.h.p. This caps the early front so it doesn't run ahead and break the O(1)-per-minute
accounting (it's the third input to Lemma 6.4 / Theorem 6.8 that S2b flagged as needed).

## Task (NEW file Probability/EarlyDripBound.lean)
1. Read Lemma 6.3's exact statement + the early-drip quantity. Model the early-drip count over the clock as a
   process whose per-step increase is the drip event (rate Θ(1/n) per same-minute pair, from S2's
   dripPair_prob_le_sq) BEFORE the level is epidemic-supported.
2. Use the FRAMEWORK: define a potential Φ on the early-drip count (e.g. exp(s·dripCount) for the upper-growth
   dual `windowGrowth_PhaseConvergence`), prove the one-step contraction `∫ Φ dK ≤ r·Φ` on the pre-bulk window
   (the rare-drip regime), and get the kernel-level tail d≥i+1 ≤ n^{−0.85}-scale w.h.p. for free via the
   framework wrapping. The substantive obligation is the one-step MGF/contraction bound for the drip-count at
   the n^{−0.45}/n^{−0.9} scales (non-uniform large deviation — DiscreteChernoff + the framework).
3. Deliver `earlyDrip_kernel_bound` (kernel-level (Kᵗ) bound on the early-drip count being too large) + a
   `PhaseConvergence`-compatible form, feeding the clock re-composition.

## HARD RULES (automode, NO effort cap; 绝对不退缩)
NEW file EarlyDripBound.lean only; do NOT edit existing files. USE the framework windowGrowth/windowDrift
(wrapping is free) + dripPair_prob_le_sq + DiscreteChernoff/Concentration/Mathlib. No sorry/admit/new
axiom/native_decide. Iterate lake build until clean. Genuinely hard non-uniform large deviation. If a Mathlib
concentration primitive at the n^{−0.45} scale is genuinely absent, name it EXACTLY + build self-contained or
STOP and report precisely (do NOT fake; do NOT leave the one-step contraction as an abstract hypothesis — the
framework removes the WRAPPING, you still owe the genuine one-step bound). Do NOT git. Final message: the
early-drip kernel bound (statement + n^{−0.85} scale), how it uses the framework + dripPair_prob_le_sq, build
verdict, #print axioms, honest status. After S3: clock re-composition (S1 bulk + S2b front + S3 early via
framework, per-minute O(1)) → O(log n), then remaining phases → A1 compose → the headline.