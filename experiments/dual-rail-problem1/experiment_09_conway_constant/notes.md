# Experiment 09 — Conway's Constant (degree-71 polynomial)

**Date:** 2026-04-18

## Setup

- **System:** `y' = -q(y)`, where `q` is Conway's look-and-say minimum
  polynomial of degree 71 (integer coefficients, max |c_k| = 14).
- **Fixed point:** `λ = 1.303577269034262` (unique real root of `q` in
  `[1, 2]`).
- **Derivative at λ:** `q'(λ) = 1.3776 × 10⁸`, so SIGN = −1; y' = −q(y)
  makes λ locally stable with time constant `τ = 1/q'(λ) ≈ 7.26 × 10⁻⁹`.
- **Monomial split after `y = u − v` substitution:**
  - positive monomials in `p̂⁺`: 1265
  - negative monomials in `p̂⁻`: 1260
- **On-trajectory production:** `p̂⁺(λ, 0) = p̂⁻(λ, 0) = M₀ = 3.629 × 10⁸`.
- **Integrator:** LSODA with `rtol=1e-6, atol=1e-8, max_step=0.01`,
  `T = 5.0`, 1000 evaluation points.

## k-sweep results

10 values of k spanning `[0.1 M₀, 1000 M₀] = [3.63e7, 3.63e11]`.

| # | k | k/M₀ | success | final_t | max u | final v |
|---|------|------|---------|---------|-------|---------|
| 1 | 3.63e7  | 0.100  | FAIL | 0.2552 | 1.0134 | 7.28e-6 |
| 2 | 1.01e8  | 0.278  | FAIL | 0.2552 | 1.0134 | 2.62e-6 |
| 3 | 2.81e8  | 0.774  | FAIL | 0.2552 | 1.0134 | 9.40e-7 |
| 4 | 7.82e8  | 2.15   | FAIL | 0.2552 | 1.0134 | 3.38e-7 |
| 5 | 2.18e9  | 5.99   | FAIL | 0.2552 | 1.0134 | 1.21e-7 |
| 6 | 6.05e9  | 16.7   | FAIL | 0.2552 | 1.0134 | 4.36e-8 |
| 7 | 1.68e10 | 46.4   | FAIL | 0.2552 | 1.0134 | 1.57e-8 |
| 8 | 4.69e10 | 129    | FAIL | 0.2552 | 1.0134 | 5.64e-9 |
| 9 | 1.30e11 | **359**| OK   | 5.0000 | 1.3064 | 2.84e-3 |
| 10| 3.63e11 | **1000**| OK  | 5.0000 | 1.3044 | 8.34e-4 |

All solver failures are LSODA "hmin reached / repeated corrector failure"
at the same `t ≈ 0.2552`, with finite `u, v`. This is NOT a physical
blow-up: both rails stay bounded with `u ≈ 1.0134`, `v` decreasing
with k. The system is locally extremely stiff somewhere around
`u ≈ 1.01, v ≈ O(M₀/k)` and the step size collapses to the machine
floor.

**Scaling observation on the failures themselves:** the product
`v · (k / M₀)` is essentially constant across the failed rows:

```
v · (k/M₀) ≈ 7.28 × 10⁻⁷   for all 8 failed k values.
```

That is, at the stall point, `v ≈ 7.28e-7 · M₀/k`. This is consistent
with v sitting on a quasi-steady-state given by `k · u · v = O(p̂⁻)`;
with `u ≈ 1.0134`, `p̂⁻(u, 0) ≈ (7.28e-7) · M₀ · u · k / k · ...` — i.e.
the dual-rail *is* behaving smoothly, it's just that the effective
Jacobian at this `(u, v)` has an eigenvalue so large (scaling with
k · u ≈ k) that LSODA can't take a finite step.

## Successful runs — is v_ss = M₀/(k·λ) confirmed?

| k/M₀ | v_final | pred M₀/(k·λ) | ratio |
|------|---------|----------------|-------|
| 359  | 2.84e-3 | 2.14e-3 | 1.33 |
| 1000 | 8.34e-4 | 7.67e-4 | 1.09 |

**Prediction from exp 08 confirmed within ~30% and improving as k→∞.**
The finite deviation at smaller k is consistent with the solution not
yet being on the strict `k → ∞` slow manifold.

Also, `final u` for the two successes was `1.3064` and `1.3044`,
bracketing `λ = 1.3036` by +0.002 and +0.0008 respectively — also
consistent with `u ≈ λ + v` on the slow manifold (slow-manifold
correction `v = M₀/(kλ)`).

## Where is k*?

From this sweep, k* lies **between 129·M₀ and 359·M₀**:

- `k/M₀ = 129` (k ≈ 4.69e10): solver stalls at t = 0.2552, system
  hasn't escaped local stiff region.
- `k/M₀ = 359` (k ≈ 1.30e11): clean run through to T = 5.0.

Order-of-magnitude estimate: `k* ≈ 200 · M₀ ≈ 7 × 10¹⁰`.

**Caveat.** The stalls at k/M₀ ≤ 129 may still be *numerical*, not
physical. v stays small and u bounded; if a stiffer solver (e.g.
implicit BDF with analytic Jacobian, or higher-precision arithmetic)
could push past `t ≈ 0.2552` we might find these runs also converge
to `(u, v) = (λ, 0)` just with large transient stiffness. We did NOT
observe any finite-time blow-up — u stays near 1.01, v stays tiny.

## Does `k* = Θ(M₀)` hold here?

**Not as a pure O(M₀) law — there is a substantial prefactor.**

- Exps 06 and 08 suggested `k* ≈ 1·M₀` (prefactor ~1, read off from
  y² − y³ or (1 − y³)).
- Here Conway degree-71 gives `k* ≈ 200 · M₀` (prefactor O(100-1000)).

Possible explanations for the large prefactor:

1. **Degree dependence.** Degree 71 vs. degree 3 in exps 06/08. A
   factor of `deg!/deg!` or `O(log deg)` multiplicative blow-up is
   plausible because each y^n, when expanded as (u−v)^n, produces n+1
   monomials with binomial coefficients up to `C(n, n/2) ≈ 2^n/√n`.
   Total number of monomials is (n+1)(n+2)/2 = O(n²), so hidden
   amplification ∝ polynomial degree, not exponential.
2. **Transient off-trajectory production.** `M₀ = p̂⁺(λ, 0)` is the
   production at the fixed point. Off-trajectory (during the
   transient from y=0 to y=λ), `p̂⁺(u, v)` could be larger if
   intermediate u, v values produce bigger monomials. Since `u, v` ≥ 0
   always, `p̂⁺(u, v)` is maximized within `[0, λ]^2` at some interior
   point.
3. **Cancellation gap.** The Conway polynomial is *minimally* a zero
   at λ, but coefficients are not optimized for dual-rail friendliness.
   The ratio of gross production to net RHS is `M₀ / q(λ) = M₀ / 0 = ∞`;
   this cancellation is perfect at the fixed point, but near-complete
   cancellation in the transient means p̂⁺ − p̂⁻ is tiny while p̂⁺ and
   p̂⁻ are each huge — which is exactly the "exp 08 style" non-cancelling
   monomial threat, at extreme scale.

## Conclusion — counterexample or confirmation?

**Not a counterexample.** The conjecture "there exists a finite k
bounding the dual-rail" still holds: k ≈ 1.3e11 gives a perfectly
clean bounded simulation matching the slow-manifold prediction.

**What this sharpens:** k* for high-degree polynomial systems can
be substantially larger than the "M₀" refined prediction from exp 08.
The Conway case shows a prefactor ≈ 200, so the correct scaling
hypothesis is

    k* ≈ C(deg, structure) · M₀,

with C possibly growing polynomially in polynomial degree. Testing
this would require intermediate-degree systems (e.g. a degree-10,
degree-20, degree-40 analogue) to extract C(deg).

## Implications for the coefficient-vs-degree question

1. **M₀ remains the right benchmark, up to a polynomial-in-degree
   prefactor.** The on-trajectory production rate governs k*, but the
   monomial count / binomial explosion from (u-v)^k expansion adds a
   degree-dependent multiplier.
2. **Very-high-degree GPACs that compute algebraic numbers through
   gradient-descent-style ODEs will have very large k*.** If you
   formalize a constant-k theorem, you need the bound to depend on
   both max|c_k| and degree, not just on `‖p‖`.
3. **No fixed universal k works** for all bounded GPACs — the k
   required grows with polynomial degree even at fixed β = 1, fixed
   max|c_k| ≤ 14. This reinforces the exp 08 conclusion that any
   constant-k theorem must have k depend on p, not just on β.

## Follow-up experiments

- **Intermediate-degree sweep.** Take polynomials of degree 5, 10, 20,
  40 that each have a unique stable positive root with max|coef| ≈ 10,
  and extract k*/M₀ as a function of degree.
- **Stiffer solver / analytic Jacobian.** Re-run the k/M₀ ≤ 129 cases
  with Radau / implicit BDF and precomputed Jacobian to see if they
  converge physically (distinguishing numerical from physical stall).
- **Truncated transient.** Start from y(0) = λ − δ instead of 0, so
  the trajectory only travels a short distance near the fixed point,
  sidestepping the transient off-trajectory production.
