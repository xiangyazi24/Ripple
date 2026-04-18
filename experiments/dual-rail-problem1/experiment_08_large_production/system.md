# Experiment 08 — Large On-Trajectory Production

## System

Scalar GPAC with a source term and internal coefficient A on a
non-cancelling polynomial structure:

    y' = ε + A·y² − A·y³,   y(0) = 0,

with `ε = 0.001` (small source to bootstrap from origin) and
`A ∈ {1, 10, 100, 1000}`.

## Boundedness

Fixed points: y' = 0 ⇒ ε + A·y²(1 − y) = 0. For y ∈ [0, 1], y²(1−y)
≥ 0, so we need y(1 − y) ≈ 0, i.e. y ≈ 0 or y ≈ 1. Since ε > 0, no
exact fixed point at y = 0. Near y = 1: A·y²(1−y) = −ε ⇒ y slightly
above 1 (but close). So y → y* ≈ 1 + ε/A.

Trajectory: y starts at 0, rises through the stable arm. Bounded in
[0, ~1 + ε/A].

**On-trajectory production:** At the steady state y ≈ 1,
`A·y² − A·y³ = A·1 − A·1 = 0`, so the NET flow is 0 (balanced by ε).
BUT the individual monomial productions are LARGE:

    y²|_{y=1} = 1 ⇒ A·y²|_{y=1} = A  (positive monomial)
    y³|_{y=1} = 1 ⇒ A·y³|_{y=1} = A  (negative monomial)

So p̂⁺ (from +A·y² and +A·y³'s positive monomials) and p̂⁻ (from
−A·y³'s positive monomials) both have contribution O(A). Unlike
experiment 07's BP cascade, these contributions do NOT cancel
between u and v: they track `y²` and `y³` directly.

**Prediction:** k* = Θ(A). This is the case the refined hypothesis
from experiment 07 predicts to be hard.

## Dual-rail expansion

`y = u − v`:

    y² = (u − v)² = u² − 2uv + v²
       +y² monomials: +u², +v² ∈ p̂⁺;  2uv ∈ p̂⁻

    y³ = u³ − 3u²v + 3uv² − v³
       +y³ monomials would split; but coefficient is -A:
       -y³ = -u³ + 3u²v - 3uv² + v³
       positive monomials of -y³: 3u²v, v³ ∈ p̂⁺;  u³, 3uv² ∈ p̂⁻

Combining with coefficient A:

    p̂⁺ = ε + A·u² + A·v² + 3A·u²v + A·v³
    p̂⁻ = 2A·uv + A·u³ + 3A·uv²

On trajectory (u ≈ 1, v ≈ 0):
    p̂⁺ ≈ ε + A + 0 + 0 + 0 = A + ε
    p̂⁻ ≈ 0 + A + 0 = A
Both O(A). Steady-state v solves:
    v' = p̂⁻ − k·u·v ≈ A − k·v = 0 ⇒ v* = A/k.

For v* to stay small (≤ 0.1 say), need k ≥ 10A. So **k* = Θ(A)**,
as predicted.

## Contrast with experiment 07

Experiment 07's BP gate: p̂⁺ ≈ λ·u_w², p̂⁻ ≈ λ·u_y². As y tracks w,
u_y ≈ u_w, so p̂⁻ = λ·u_y² ≈ λ·u_w² = p̂⁺. The ANNIHILATION equation
for v_y's steady state is λ·u_w² − k·u_y·v_y ≈ 0, giving
v_y ≈ u_w²·λ/(k·u_y) = λ/k. Hmm, so even BP cascade should give
v_y = Θ(λ/k)? But measured v_y was tiny...

Actually the measured `max v_y` for λ=1000, k=100: should be ~10.
But we measured... let me re-check exp 07 data. From summary,
λ=1000, k=100 was not one of my test points. The smallest k tested
at λ=1000 was 100. Let me verify.

Actually looking more carefully at exp 07's run.py, `ks =
np.logspace(log10(0.1*λ), log10(1e4*λ))` so for λ=1000, k from 100 to
1e7. At k=100, k/λ=0.1. I reported peak = 0.3 at that point. So v_y
is tiny. But my analysis says v_y should be ~λ/k = 10.

Discrepancy suggests my analysis is wrong for experiment 07 — the
cancellation is subtler than I wrote. Maybe I'll revisit later.

For *this* experiment, the analysis should be cleaner because the
"no cancellation" case is unambiguous.

## Hypothesis

Yes: k* = Θ(A). If this holds, we've characterized the coefficient-
sensitivity: it's about on-trajectory monomial magnitudes, not max
coefficient.

## Why this system

Engineered to be the opposite of experiment 07: no slow-manifold
cancellation of the A·y² and A·y³ contributions at the fixed point
y = 1. Both monomials are O(A) individually.
