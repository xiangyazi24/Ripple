# Experiment 07 — Bournez-Pouly-Style Cascade

## System

Three-species bounded cascade with internal rate parameter `λ`:

    z' = 1 − z,                   z(0) = 0   (bootstrap, bounded)
    w' = z − w,                   w(0) = 0   (delay, bounded)
    y' = λ · (w² − y²),           y(0) = 0   (fast-sigmoid-gate)

Amplitude: `z, w, y ∈ [0, 1]` (shown below). Internal rate `λ > 0`
controls how fast the y-gate activates once the w-cascade supplies it.

### Boundedness

- `z' = 1 − z`: linear, z(t) = 1 − e^(−t) ∈ [0, 1]. Bounded.
- `w' = z − w`: driven by bounded z, stable, w → 1 from 0. Bounded in [0, 1].
- `y' = λ(w² − y²)`: When w ∈ [0, 1], the flow has stable fixed
  point at y = w (since `∂/∂y λ(w² − y²) = −2λy < 0` for y > 0).
  Starting at y(0) = 0, y(t) ∈ [0, 1].

All amplitudes in [0, 1] regardless of λ. But internal coefficient
λ can be any positive number.

## GPAC form

    p₁(z, w, y) = 1 − z
    p₂(z, w, y) = z − w
    p₃(z, w, y) = λ · w² − λ · y²

All polynomial, max degree 2.

## Dual-rail

`z = u₁ − v₁`, `w = u₂ − v₂`, `y = u₃ − v₃`. Since all originals are
non-negative, we expect v_i to be small (minimal repr).

    p̂₁⁺ = 1 + v₁                  p̂₁⁻ = u₁
    p̂₂⁺ = u₁ + v₂                 p̂₂⁻ = v₁ + u₂
    p̂₃⁺ = λ(u₂² + v₂²) + 2λ u₃ v₃ p̂₃⁻ = 2λ u₂ v₂ + λ(u₃² + v₃²)

Wait let me redo p̂₃ carefully:
    w² − y² = (u₂−v₂)² − (u₃−v₃)²
            = u₂² − 2u₂v₂ + v₂² − u₃² + 2u₃v₃ − v₃²
    λ(w² − y²):  pos: λu₂², λv₂², 2λu₃v₃
                 neg: 2λu₂v₂, λu₃², λv₃²
    p̂₃⁺ = λu₂² + λv₂² + 2λu₃v₃
    p̂₃⁻ = 2λu₂v₂ + λu₃² + λv₃²

Constant-k ODE:

    u_i' = p̂_i⁺ − k u_i v_i,
    v_i' = p̂_i⁻ − k u_i v_i.

## Hypothesis

**k* = Θ(λ).** By the same coefficient-scaling argument from
experiment 06 (applied now to just species 3's equation, since species
1, 2 have coefficient 1). Expected k-threshold grows linearly with λ
while amplitude stays fixed at [0, 1].

This is the Bournez-Pouly signature: bounded GPAC with large internal
coefficient forcing large k*.

## Why this system

- **Amplitude is fixed at [0, 1]** — rules out amplitude-scaling
  explanation for any k* growth.
- **λ is purely an internal rate parameter.** If k* grows with λ, it
  proves the dual-rail is sensitive to internal parameters, not just
  observable amplitude.
- **Consistent with the conjecture** (per-system existence of k), but
  meaningful warning: the "some k" cannot be a universal constant
  across all bounded GPACs.

## Connection to Bournez-Pouly

Real Bournez-Graça-Pouly constructions for analog computing use
cascades of sigmoid gates like this, with rates λ growing as the
target accuracy ε decreases (λ ∼ polylog(1/ε) or worse). Our
conjecture being per-system-k-exists means each ε gets its own k(ε),
and k(ε) can grow with 1/ε — this is not a violation.
