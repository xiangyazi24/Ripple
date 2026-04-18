# Experiment 03 — Hopf Normal Form (with bias)

## System

Supercritical Hopf normal form (`r² = x₁² + x₂²`):

    x₁' =  x₁ − x₁·r² − ω·x₂ + c,
    x₂' =  x₂ − x₂·r² + ω·x₁.

With `c = 0`, origin is a fixed point — zero-init stays at 0. Add
bias `c > 0` to `x₁` equation; limit cycle (radius ≈ 1 for small c)
persists, FP shifts near origin and is unstable for c < c*.

## GPAC form (degree 3)

    p₁(x) = x₁ − x₁·x₁² − x₁·x₂² − ω·x₂ + c,
    p₂(x) = x₂ − x₂·x₁² − x₂·x₂² + ω·x₁.

## Dual-rail split

`x_i = u_i − v_i`. Expand each `x_j·x_l²` term and collect by sign.

For `x₁·r² = x₁·x₁² + x₁·x₂²`: both cubes in a single variable, and
mixed `x₁·x₂²`. After expansion:

    x₁·x₁² = (u₁−v₁)³  = u₁³ − 3u₁²v₁ + 3u₁v₁² − v₁³,
    x₁·x₂² = (u₁−v₁)(u₂−v₂)²
           = u₁u₂² − 2u₁u₂v₂ + u₁v₂² − v₁u₂² + 2v₁u₂v₂ − v₁v₂².

And dually for `x₂·r²`. Split each monomial by its sign, collect into
p̂⁺ / p̂⁻ per variable. The `−ω·x₂` in p₁ contributes `+ω·v₂` to p̂₁⁺ and
`+ω·u₂` to p̂₁⁻. The `+ω·x₁` in p₂ contributes `+ω·u₁` to p̂₂⁺ and
`+ω·v₁` to p̂₂⁻. The `+x_i` linear term contributes `+u_i` to p̂_i⁺.
The `+c` goes to p̂₁⁺.

Full p̂⁺ / p̂⁻ (see run.py for the coded form):

    p̂₁⁺ = u₁ + 3u₁²v₁ + v₁³ + 2u₁u₂v₂ + v₁u₂² + v₁v₂² + ω·v₂ + c,
    p̂₁⁻ = v₁ + u₁³ + 3u₁v₁² + u₁u₂² + u₁v₂² + 2v₁u₂v₂ + ω·u₂.

    p̂₂⁺ = u₂ + 3u₂²v₂ + v₂³ + 2u₂u₁v₁ + v₂u₁² + v₂v₁² + ω·u₁,
    p̂₂⁻ = v₂ + u₂³ + 3u₂v₂² + u₂u₁² + u₂v₁² + 2v₂u₁v₁ + ω·v₁.

## Properties of interest

- **Amplitude fixed at ≈ 1** independent of ω — so amplitude scaling
  is controlled out of the experiment.
- **Frequency ω tunable** independently. High ω stress-tests
  annihilation transient time `1/k` against the period `2π/ω`.
- **Smoother than Van der Pol** (sinusoidal-like, not stiff), so the
  `x_i` sign changes are smooth — a gentler test.

## Hypothesis

k-threshold scales with ω (not with amplitude, since amplitude is
fixed). Expect something like `k* ≳ C·ω` for some constant C.

## Why this system

Clean separation of amplitude and frequency effects, which the Van der
Pol experiment couldn't separate. If the k-threshold does scale with ω,
it means constant-k fails for fast oscillations — but the conjecture
only asks for *existence* of some k, and k can be chosen per-system.
