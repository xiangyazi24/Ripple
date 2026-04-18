# Experiment 06 — Scaled Scalar Cubic

## System

Scalar cubic with coefficient `C`:

    y'(t) = C − C · y(t)³,   y(0) = 0.

For any `C > 0`, y converges monotonically to 1 (same fixed point as
experiment 01, `y³ = 1`). The coefficient C only affects the
*time scale*: solution is `y(t; C) = y₁(C · t)` where `y₁` is the
C = 1 solution. All trajectories reach y ≈ 1 in O(1/C) time.

## Purpose

Isolate the effect of polynomial-coefficient magnitude on k*. Previous
experiments mixed amplitude, degree, and coefficient. Here amplitude
and degree are held fixed (degree 3, y ∈ [0, 1]) and only C varies.

Test values: C ∈ {1, 10, 100, 1000}.

## Dual-rail

    p(y) = C(1 − y³) = C − C·(u − v)³
         = C − C·u³ + 3C·u²v − 3C·uv² + C·v³

    p̂⁺ = C + 3C·u²v + C·v³
    p̂⁻ = C·u³ + 3C·uv²

    u' = C + 3C·u²v + C·v³ − k·u·v,  u(0) = 0
    v' = C·u³ + 3C·uv²       − k·u·v,  v(0) = 0

## Hypothesis

**k* = Θ(C).** From experiment 01, scalar cubic at C = 1 has k* ≈ 10.
If the coefficient-dominance hypothesis (developed after experiments
02–05) is correct, we expect:

- C = 1: k* ≈ 10 (baseline, experiment 01 confirmed)
- C = 10: k* ≈ 100
- C = 100: k* ≈ 1000
- C = 1000: k* ≈ 10000

Linear scaling, because the whole ODE is just time-rescaled.

## A priori observation

Actually, there's a cleaner argument: the C-scaled system is
equivalent to the C = 1 system under the time substitution
`τ = C·t`. Rescaling the time rescales BOTH sides of the dual-rail
ODE *except* the annihilation term — rescaling k by C keeps the
annihilation rate invariant. So k*(C) = C · k*(1) exactly.

This is a **sanity-check experiment** for the numerical pipeline
rather than a genuine exploration of conjecture.

## Why this system

- Quickest way to validate the coefficient-scaling hypothesis numerically.
- If numerical result disagrees with the analytic prediction, the
  coefficient-dominance hypothesis (or the integration scheme) is
  suspect.
