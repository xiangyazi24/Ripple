# Experiment 06 Notes — Scaled Scalar Cubic

Date: 2026-04-18

## Setup

`y' = C − C·y³`, y(0) = 0, C ∈ {1, 10, 100, 1000}. T = 10/C (same
τ = C·t range for all C). k swept ∈ [0.1C, 10⁴C].

## Analytic prediction

Under `τ = C·t`, the original ODE becomes `dy/dτ = 1 − y³`, the
baseline C = 1 system. Same substitution on the dual-rail: the only
term *not* scaling with C is the annihilation `k·u·v` (since k is a
free constant). So defining `k̃ = k/C`, the τ-rescaled dual-rail is
the baseline dual-rail with annihilation `k̃ · u · v`. **k*(C) = C · k*(1).**

## Results

Plot `k_over_C_collapse.png`: for all four C values, plotting peak
of (u, v) vs `k/C` collapses onto a single curve. The transition
from blow-up to bounded happens at **`k/C ≈ 5`**.

(Baseline from experiment 01 was k* ≈ 10, so k*(1) ≈ 5–10 in this
more finely-sampled sweep.)

## Conclusion

**Coefficient-scaling hypothesis confirmed analytically and numerically.**
For a one-parameter family of systems differing only by a multiplicative
coefficient C, k*(C) = C · k*(1). The Tikhonov slow manifold scales
identically because the annihilation rate `k·u·v` is the one term with
`k` as a free coefficient.

## Implication for the conjecture

The conjecture states `∃ k > 0` making the dual-rail bounded *for each
system individually*. Coefficient scaling is consistent with this.
What would break the conjecture is a family of bounded GPACs indexed
by a parameter `n` where the required k*(n) grows faster than any
constant can bound — e.g., requiring `k → ∞` as the GPAC grows more
complex. But the conjecture is stated per-system, so scaling is fine.

However, this does mean that for a GPAC with coefficient C, choosing
k = O(C) is *necessary*. If the coefficient is very large but the
trajectory amplitude stays bounded, k still has to grow with C to
keep up.

## Files

- `system.md`, `run.py`, `summary.txt`
- `dualrail_C=*_k=*_{sufficient,insufficient}.png` — representative traces
- `k_over_C_collapse.png` — rescaled k-sweep collapse

## Next

Experiment 07: Bournez-Pouly-style construction — bounded GPAC with
*large internal intermediate* coefficients but bounded outputs.
