# Experiment 03 Notes — Hopf Normal Form (biased c = 0.05)

Date: 2026-04-18

## Setup

Original:  `x₁' = x₁ − x₁·r² − ω·x₂ + c,  x₂' = x₂ − x₂·r² + ω·x₁`,
`r² = x₁² + x₂²`, c = 0.05, zero init. Bias kicks trajectory off origin;
converges to limit cycle of radius ≈ 1.

Dual-rail: degree-3 monomial-wise split (see `system.md`, `run.py`).

Swept ω ∈ {1, 5, 20, 100} × k ∈ {0.1, 1, 10, 100, 1000, 10000}.

## Results

Amplitude of original is ≈ 1 for all ω. Reported peak is the worst
among `max u₁, max v₁, max u₂, max v₂`. `finite` = all values finite
at end of integration.

| ω | k = 0.1 | k = 1 | k = 10 | k = 100 | k = 1000 | k = 10000 |
|---|---------|-------|--------|---------|----------|-----------|
| 1  | 2.5 ✗  | 3.1 ✗ | 3.1 ✗ | **1.03** ✓ | 1.02 ✓ | 1.02 ✓ |
| 5  | 5.2 ✗  | 9.5 ✗ | 10.6 ✗ | **1.03** ✓ | 1.01 ✓ | 1.01 ✓ |
| 20 | 5.6 ✗  | 5.4 ✗ | 11.1 ✗ | **1.08** ✓ | 1.00 ✓ | 1.00 ✓ |
| 100 | 5.7 ✗ | 5.2 ✗ | 5.1 ✗ | **1.76** ✓ | 1.02 ✓ | 1.00 ✓ |

`✗` = integrator produced NaN / blow-up; `✓` = finite, bounded.

## Observations

1. **k-threshold is essentially ω-independent, around k* ≈ 100.**
   This is the most striking finding. A priori one would expect the
   annihilation time scale `1/k` to need to beat the oscillation
   period `2π/ω`, giving `k* ∝ ω`. That's not what we see: k* is
   roughly the same across two decades of ω.

2. **Within the bounded regime, tracking quality does depend on ω.**
   At k = 100, ω = 1 tracks at <3% error, ω = 100 overshoots to 1.76
   (76% error). To get <5% tracking at ω = 100 we need k ≥ 1000. So
   there is an `ω`-dependent quality threshold, but not a boundedness
   threshold.

3. **Failure mode at small k is mass blow-up, not oscillation growth.**
   The LSODA integrator emits step-size-collapse warnings, and the
   reported peaks grow with decreasing k in a monotone-ish way
   (though for ω = 5 the peak at k = 10 is actually *larger* than at
   k = 0.1 — some nonlinear interaction with when the integrator
   gives up). Suggests finite-time blow-up of `u + v` while `u - v`
   stays near the limit cycle.

4. **`k → ∞` tracks the minimal representation.** Same as experiments
   01, 02: `u_i → x_i⁺, v_i → x_i⁻`, visible in plots
   `dualrail_omega=*_k=10000.png`.

## Conclusion

**Not a counterexample.** Constant-k dual-rail is bounded for k ≳ 100,
for all tested ω ∈ [1, 100]. The k-threshold does not grow with ω,
contradicting a naive time-scale argument. This suggests that the
threshold is determined by *spatial* (polynomial-coefficient) rather
than *temporal* features of the GPAC.

## Why isn't k* frequency-dependent?

Conjecture: In the slow-manifold picture, the fast variable is `u_i · v_i`
and the manifold is `{u_i · v_i = 0, u_i − v_i = x_i(t)}`. Projection onto
the manifold averages out the ω-dependent rotation: the *signed* difference
`u_i − v_i` follows the original dynamics, and the *product* `u_i · v_i`
is drained at rate k (not rate k·ω). The oscillation frequency enters the
rotation of `(x₁, x₂)` but does not slow down the annihilation.

More formally: `(u_i · v_i)' = (p̂_i⁺ + p̂_i⁻) − k·u_i·v_i + ...`, so the
rotation rate ω appears in `p̂⁺, p̂⁻` individually but cancels in the sum
for the annihilation-relevant product equation. (TODO: verify this
calculation.)

## Caveats

- Only tested ω ≤ 100. The ω* → ∞ scaling is untested.
- Amplitude is fixed at ≈ 1. Changing the "`1·x`" coefficient in the Hopf
  ODE scales amplitude as 1/√coef. Untested whether k* scales with
  amplitude.
- The finite-time blow-up claim at small k is inferred from integrator
  behaviour, not a rigorous bound.

## Files

- `system.md` — system description and dual-rail expansion
- `run.py` — simulation
- `original_omega=*.png` — x₁, x₂ trajectories + phase portrait
- `dualrail_omega=*_k=*.png` — u, v vs x per species
- `k_threshold.png` — aggregated peak-vs-k plot across ω
- `summary.txt` — per-run dict summary

## Next

Experiment 04: Brusselator — positive-species chemical oscillator.
Native CRN origin rather than constructed bounded GPAC. Features:
two-species nonlinear coupling with natural bounds.
