# Doty time-half — Avenue C4: front-shape minute induction (Thm 6.5) → profile invariant → lower bound + hour-sync

Directive: 挨个做，绝对不退缩. Next piece in the consult-confirmed DAG after C3 (upper). C4 builds the
front-shape via minute-index induction (Theorem 6.5), coupling S2b (one-step squaring) + S3 (early-drip), giving
the profile invariant c≥i+1 < p·c≥i² — which yields the clock LOWER bound (Lemmas 6.6/6.7) and is needed for
hour-synchronization (the genuine expected-stabilization-time correctness, not just the upper time magnitude).

Repo: ~/.openclaw/workspace/projects/Ripple (local, NO .git). Build: nice -n 15 env LEAN_NUM_THREADS=2
~/.elan/bin/lake build <Module>. Read: the consult-confirmed DAG in DOTY_CLOCKFAITHFUL_SPEC.md (REFINEMENT
section), C3's Probability/ClockFaithful.lean (the upper bound + clock model + the seed/bulk phases),
S2b Probability/FrontTailKernel.lean (frontTail_kernel_one_step_le_beyondSq = the one-step squaring on the real
chain; FrontTail.frontTail_doubly_exp / frontWidth_loglog = the doubly-exp arithmetic), S3
Probability/EarlyDripBound.lean (earlyDrip_kernel_bound = d≥ ≤ t·(B/n)², O(n^−0.85)), the framework
WindowConcentration.lean. Paper: ref/Doty-2021-exact-majority.txt Theorem 6.5 (front shape, minute induction),
Lemma 6.3 (continuous-time shape c≥i+1 ≤ 0.9p·c≥i² + d≥i+1), Lemmas 6.6/6.7 (lower bound).

## The faithful structure (consults)
Theorem 6.5 is INDUCTION ON MINUTE INDEX i, maintaining the cumulative-tail profile invariant
    n^−0.4 ≤ c≥i(t) ≤ 0.1  ⟹  c≥i+1(t) < p·c≥i(t)²
with two internal inductive claims proved INSIDE: front width from t+≥i to t01≥i is O(log log n), and the
early-drip d≥i+1(t01≥i) stays O(n^−0.85). The coupling C2 lacked: early-drip-small DEPENDS on front-width.

## Task (NEW file Probability/FrontShapeInduction.lean)
1. Define the minute-index profile predicate `FrontShapeAt i` (the cumulative-tail bound c≥i+1 < p·c≥i² holds at
   minute i, on the real clock count beyond/card) + `FrontWidthAt i` (O(log log n) width) + `EarlyDripSmallAt i`
   (d≥i+1 ≤ O(n^−0.85)).
2. The induction step `frontShape_step : (FrontShapeAt i ∧ width/early at i) → FrontShapeAt (i+1)` — DERIVE
   c≥i+1 < p·c≥i² from S2b's one-step squaring (frontTail_kernel_one_step_le_beyondSq) + Lemma 6.3 local form +
   the early-drip closure (S3, with B = the inductively-maintained front-width cap, COUPLED not assumed).
3. `front_shape_all : ∀ i < N, FrontShapeAt i` by induction (union of step-failures, high-prob).
4. `clock_step_lower` (Lemmas 6.6/6.7): from the front shape, T_low ≤ t01(i+1) − t01(i) (the clock doesn't run
   too far ahead — the lower bound). This is what the upper bound C3 lacks for the full Thm 6.8.

## HARD RULES (automode, NO effort cap; 绝对不退缩)
NEW file FrontShapeInduction.lean only; do NOT edit existing files (reuse S2b/S3/C3/framework). The coupling
(early-drip ← front-width) must be GENUINE, not assumed (that was C2's flaw). No sorry/admit/new
axiom/native_decide. Iterate lake build until clean. The genuinely hard content: the minute-index induction
maintaining c≥i+1 < p·c≥i² with early-drip coupled to front-width. If a step needs a sub-lemma not yet built,
build it honestly or STOP and report the exact gap — do NOT leave the invariant as an abstract hypothesis. Do
NOT git. Final message: FrontShapeAt + the induction + clock_step_lower statements, how S2b/S3 are COUPLED (not
assumed), build verdict, #print axioms, honest status (front shape + lower bound proven kernel-level, or blocked
on exact sub-lemma). After C4: clock_minute_bounds (Thm 6.8 = C3 upper + C4 lower) + clock_hour_bounds (Thm 6.9)
+ assemble → faithful O(log n) clock, then other phases + A1 → expected-time headline.