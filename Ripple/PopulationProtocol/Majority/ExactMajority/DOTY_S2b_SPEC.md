# Doty time-half §6 — Avenue S2b: kernel-level front-tail bound (discharge the FrontRecurrence hypothesis)

Directive: 不退缩，绝对不退缩. S2 proved the squaring MECHANISM (dripPair_prob_le_sq, scheduler-level, real)
+ the doubly-exponential ARITHMETIC (given the recurrence). S2b derives the recurrence on the REAL stochastic
front count — i.e. a kernel-level front-tail bound, the analogue of S1's constantDensity_tail. This closes the
gap so the front tail is as complete as S1.

Repo: ~/.openclaw/workspace/projects/Ripple (local, NO .git). Build: nice -n 15 env LEAN_NUM_THREADS=2
~/.elan/bin/lake build <Module>. Read: S2's Probability/FrontTailDecay.lean (dripPair_prob_le_sq = the proven
one-step squaring bound; FrontRecurrence/frontTail_doubly_exp/frontTail_O1_parallel = the arithmetic taking the
recurrence as hypothesis — your job is to PRODUCE the recurrence/tail on real counts), S1's
Probability/ConstantDensityEpidemic.lean (lintegral_decay_on_absorbing + windowPot_contracts_on_floor +
constantDensity_tail = the TEMPLATE for going one-step-bound → kernel-level tail; REUSE), DiscreteChernoff/Concentration.
Paper: ref/Doty-2021-exact-majority.txt Theorem 6.5.

## The gap S2b closes
S2's `frontTail_O1_parallel` assumes `hrec : FrontRecurrence p f` for an abstract `f : ℕ → ℝ`. The real front
count `c≥i(t)` (fraction at minute ≥ i at time t) must be shown to satisfy this recurrence W.H.P. over a window,
from the one-step bound `dripPair_prob_le_sq` (two-leader meet prob ≤ (m/n)²). This is the concentration step:
one-step E[Δ front-count] ≤ p·(front fraction)² ⟹ over a window the front-count tail decays as the squared
recurrence, w.h.p. — a kernel-level `(Kᵗ) c₀ {front too large} ≤ ...` bound.

## Task (NEW file Probability/FrontTailKernel.lean)
1. Define the front-count quantity over the clockProto (S1/S2 already have the clock + interactionProb algebra):
   `frontCount T c = #agents at minute ≥ T` (or the fraction). Reuse S2's `beyond`/`dripPair_prob_le_sq` and
   S1's monotonicity (`beyond_ge_monotone`).
2. Prove the kernel-level front bound: from a config with front fraction ≤ f0 (subcritical, p·f0 ≤ 1/2), the
   front count at the NEXT minute level decays per the squaring — produce
   `frontTail_kernel : (Kᵗ) c₀ {c | frontCount (i+1) c ≥ threshold} ≤ <doubly-exp/poly bound>`, using S1's
   `lintegral_decay_on_absorbing`-style potential (here the potential encodes the SQUARED front, contracting
   because the two-leader advance prob is quadratically suppressed — the contraction comes from
   dripPair_prob_le_sq's ≤ (m/n)² instead of S1's ≥ 1/100).
   NOTE the direction differs from S1: S1 lower-bounded advance (informed grows); S2b UPPER-bounds front advance
   (leaders are RARE, front stays small) — so the potential/contraction is set up to bound front growth from
   ABOVE. Adapt S1's template accordingly (you may need an upper-tail / supermartingale-increase variant of
   lintegral_decay_on_absorbing; build it self-contained if S1's exact form doesn't transfer).
3. Discharge S2's hypothesis: show the real front count satisfies `FrontRecurrence` (or directly feed
   frontTail_kernel into a kernel-level version of frontTail_O1_parallel), so the front O(log log n) cost is a
   theorem about the actual clock, not an abstract f.

## HARD RULES (automode, NO effort cap; 绝对不退缩)
NEW file FrontTailKernel.lean only; do NOT edit existing files (S1, S2, clock, etc.). REUSE
dripPair_prob_le_sq + S1's lintegral_decay_on_absorbing template + DiscreteChernoff/Concentration/Mathlib.
No sorry/admit/new axiom/native_decide. Iterate lake build until clean. Genuinely hard §6 concentration. If a
specific Mathlib primitive is absent, name it EXACTLY + build self-contained or STOP and report precisely — do
NOT fake, do NOT leave the recurrence as an abstract hypothesis (that's the gap you're closing). Do NOT git.
Final message: the kernel-level front-tail lemma (statement + bound), how it discharges S2's FrontRecurrence
hypothesis on real counts, build verdict, #print axioms, honest status (front tail now kernel-level proven, or
blocked on exactly-named primitive). After S2b: S3 (early-drip), then re-compose S1+S2+S3 → O(log n).