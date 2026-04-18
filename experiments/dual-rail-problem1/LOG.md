# UCNC25 Problem 1 — Constant-k Dual-Rail Boundedness: Experiment Log

**Target problem.** For a bounded GPAC `y' = p(y)` (i.e. `y(t) ∈ (-β, β)^n`
for some `β > 0` on `[0, ∞)`), is there a constant `k > 0` such that the
dual-railed system

    u_i' = p̂_i⁺(u, v) - k · u_i · v_i,
    v_i' = p̂_i⁻(u, v) - k · u_i · v_i,
    u_i(0) = v_i(0) = 0,

keeps `u, v` bounded on `[0, ∞)`?

Known: the `Z = p̂⁺ + p̂⁻` polynomial-scaled version is bounded (DNA25).

## Strategy

- Collect candidate bounded GPACs from the literature, preferring those with
  structure that might stress the constant-k annihilation (high oscillation,
  multi-species coupling, high polynomial degree, near-singular dynamics).
- For each, simulate both the original GPAC and the dual-railed system at a
  sweep of `k` values, log the `max_{t ∈ [0, T]} (u_i + v_i)` trend.
- Plot both the original trajectory and the `u_i, v_i` trajectories at
  selected `k`.
- Record observations: bounded / unbounded, `k*` (if any) where behavior
  flips, shape of instability, `k → ∞` limiting behavior.

## Experiment template (per file)

Each experiment lives in `experiment_NN_slug/`:

    experiment_NN_slug/
    ├── system.md          -- plain-language system description + why we're
    │                         trying this system
    ├── run.py             -- numerical simulation + plotting
    ├── original.png       -- original GPAC trajectory
    ├── dualrail_k=....png -- dual-rail trajectories at selected k values
    ├── k_sweep.png        -- boundedness as function of k
    └── notes.md           -- observations, conclusions, follow-ups

## Running index

| # | System | Source | Features | Status | Conclusion |
|---|--------|--------|----------|--------|------------|
| 01 | `y' = 1 − y³` | degree-3 pedagogical | high degree, monotone → 1 | done | bounded for k ≥ ~10; small k blow up; nullcline analysis matches |
| 02 | biased Van der Pol | oscillator | limit cycle, sign-changing, stiff μ | done | bounded for k ≳ 10 across μ ∈ {1, 5, 20}; Tikhonov to minimal repr; k* independent of μ |
| 03 | biased Hopf normal form | clean oscillator | limit cycle r ≈ 1, ω tunable | done | bounded for k ≳ 100 across ω ∈ {1..100}; k* ω-independent (surprising, expected k* ∝ ω) |
| 04 | Brusselator | native CRN | positive species, 2-species autocat. | done | bounded for k ≳ 100; hypothesis that non-neg species → smaller k* disproved; spurious v-rail from degradation |
| 05 | Lorenz (biased) | bounded chaos | degree 2, chaotic, |x|~20 |z|~50 | done | bounded for k ≳ 10; degree-2 drops k* 10× vs degree-3 Hopf/Brusselator |
| 06 | y' = C − C·y³ | scalar, C-scaled | coefficient-scaling test | done | k*(C) = C · k*(1), collapse verified for C ∈ {1, 10, 100, 1000} |
| 07 | BP cascade (z, w, λy-gate) | Bournez-Pouly style | internal rate λ, fixed amplitude [0,1] | done | k* ≈ O(1) regardless of λ ∈ [1, 1000]! Coefficient on *cancelling* term ≠ threat |
| 08 | y' = ε + A·y² − A·y³ | engineered | non-cancelling A on both ±monomials | done | k* = Θ(A) confirmed; v_ss = A/k matches; coefficient on *non-cancelling* monomial DOES drive k* |

## Interim pattern (after 5 experiments)

- All 5 systems confirm conjecture: ∃ finite k bounding dual-rail.
- k* scales with polynomial-coefficient magnitude × typical amplitude,
  NOT with oscillation frequency, NOT with amplitude alone.
- Degree-2 systems have k* roughly 10× smaller than degree-3 systems
  with comparable coefficients.
- Failure mode at k < k* is mass blow-up (finite-time singularity),
  not just "larger but bounded" oscillation.
- Tikhonov slow-manifold picture holds universally: as k → ∞, the
  dual-rail tracks the minimal representation `(u, v) = (x⁺, x⁻)`.

No counterexample candidates yet. Next step: try to *construct* a
system where k* is demonstrably very large.

## After 8 experiments — refined understanding

Experiments 06-08 pin down the scaling law:

- **Exp 06**: C·(1 − y³), coefficient C on a non-cancelling term at
  fixed point y = 1 ⇒ k*(C) = Θ(C).
- **Exp 07**: λ·(w² − y²), coefficient λ on a term that cancels to 0
  on the slow manifold ⇒ k*(λ) = O(1).
- **Exp 08**: A·(y² − y³), coefficient A multiplies both ±monomials
  which are individually O(A) at y = 1, but net RHS = 0 ⇒ k*(A) = Θ(A).

**Refined hypothesis:** k* scales with `max_t ||p̂⁺(u(t), v(t)) +
p̂⁻(u(t), v(t))||` — the maximum instantaneous total production rate
into (u, v) on the trajectory. This is not the max coefficient (can
be much smaller via cancellation, exp 07) and not the net RHS (can
be much larger via non-cancelling parallel monomials, exp 08).

**Uniform-β question:** can k* depend only on the boundedness
parameter β? Exp 08 answers NO: family `{y' = ε + A·y² − A·y³}_A`
has β ≈ 1 for all A, but k* = Θ(A) grows. So any constant-k theorem
must allow k to depend on p, not just on β.

## Candidate systems to try

Prioritized queue:

1. **Van der Pol oscillator** (bounded limit cycle). `y'' − μ(1−y²)y' + y = 0`
   rewritten as first-order. Features: stable limit cycle, oscillation
   frequency tunable via `μ`. Hypothesis: high `μ` (stiff) might stress
   constant-k annihilation.
2. **Brusselator** (bounded periodic). Two-species chemical oscillator
   `x' = A + x²y − Bx − x`, `y' = Bx − x²y`. Original is bounded for
   suitable parameters; positive-only so trivial after shift. Might still
   be useful after offset shift to push into GPAC form with bounded oscillation.
3. **Lotka-Volterra with saturation**. `x' = x(1 − x) − xy/(1+x)`, etc.
   Rational → polynomial after dual-railing a denominator. Features:
   multi-species, possible oscillation.
4. **Hopf normal form**. `y_1' = y_1 − y_1·(y_1²+y_2²) − ω·y_2`,
   `y_2' = y_2 − y_2·(y_1²+y_2²) + ω·y_1`. Stable circular limit cycle of
   radius 1, frequency ω. Clean high-frequency test case.
5. **Bournez-Pouly constructions for exponentially-growing intermediates**
   (from [bournez.pdf] / [lacl19.pdf]). Candidates where internal intermediate
   variables are large even though the output is bounded.
6. **Chua's circuit** (chaotic but bounded).
7. **Lorenz attractor**. Bounded chaos. Probably most stressful for constant-k
   if any.
8. **Any GPAC computing a specific irrational via a polynomial ODE
   with a high-degree intermediate** (from RTCRN1 / Bounded). These
   match the CRN computability context directly.
9. **Conway's constant λ ≈ 1.3036** (suggested by Xiang 2026-04-18).
   Unique positive real root of a specific degree-71 integer polynomial
   q(x). GPAC via gradient descent: `y' = −q(y)·q'(y)`, RHS degree ≈ 141.
   Per refined hypothesis (exp 07), the cancelling `q·q' → 0` structure
   at fixed point should give k* = O(1) despite huge coefficients —
   a stress test for the on-trajectory production hypothesis.

## Log conventions

- Timestamp each entry in `notes.md`.
- Save all plots as PNG, not PDF, so they render in MD previews.
- If a system starts looking like a counterexample, mark it **⚠ candidate**
  in the running index and spend extra effort on it.
- If an experiment needs a re-run with different parameters, archive the
  old `notes.md` section with a date stamp rather than deleting.
