# Experiment 09 — Conway's Constant: High-Degree Polynomial GPAC

## System

Conway's constant `λ ≈ 1.303577269034296` is the unique positive real
root of a specific degree-71 integer polynomial `q(x)` with
coefficients ranging from −12 to +14. It governs the asymptotic growth
rate of the look-and-say sequence.

We use the simplest bounded GPAC that computes λ:

    y' = −q(y),   y(0) = 0

Since `q(0) = −6 < 0`, `q(λ) = 0`, and λ is the unique positive real
root, starting from `y = 0` the trajectory increases monotonically
toward λ. If `q'(λ) > 0` (confirmed numerically) then λ is a stable
fixed point, and the trajectory converges.

## Why this system

Xiang's suggestion (2026-04-18): stress-test the constant-k conjecture
with HIGH DEGREE rather than high coefficient. The refined hypothesis
from experiments 06–08 says `k* = Θ(max_t M(t))` where
`M(t) = ||p̂⁺(u(t), v(t)) + p̂⁻(u(t), v(t))||` is the total production
rate into u, v on trajectory.

**The tension:** on trajectory at `y = λ`, we have `q(y) = 0` exactly,
so the net RHS is zero. BUT the individual monomials are gigantic:
`y^71 ≈ 1.304^71 ≈ 1.2e8`. The dual-rail splits q into positive and
negative monomials of `u, v`, and each of these monomials is large at
`(u, v) ≈ (λ, 0)` — the cancellation is algebraic (identity q(λ) = 0),
not variable-tracking (as in experiment 07 where `w² − y² → 0` by
w, y tracking).

**Two possibilities:**

- **Bounded (refined hypothesis holds):** even the algebraic
  cancellation propagates in a way that makes M(t) small enough that
  some finite k works. k* will likely still be Θ(max individual
  monomial), which is ~1e8 here.
- **Counterexample to constant k:** the monomial expansion into
  (p̂⁺, p̂⁻) breaks the algebraic cancellation, and no k suffices for
  this polynomial.

Previous experiments (01–08) suggest bounded, but all had degree ≤ 3.
Conway jumps to degree 71 — 25× larger than any prior test.

## Dual-rail expansion

For each term `r_k · y^k` in `y' = −q(y)` (so `r_k = −c_k` where
`c_k` is the Conway coefficient), substitute `y = u − v`:

    y^k = Σ_{j=0}^{k} C(k,j) · u^{k−j} · (−v)^j
        = Σ_j (−1)^j · C(k,j) · u^{k−j} · v^j

Each term `r_k · (−1)^j · C(k,j) · u^{k−j} · v^j` has sign
`sign(r_k) · (−1)^j`. Positive-signed terms go into p̂⁺, negative into
p̂⁻. Total number of monomials: `Σ_{k=0}^{71} (k+1) = 72·73/2 = 2628`.

Code builds the monomial list once and evaluates at each ODE step.

## Expected behavior

At steady state `u ≈ λ`, `v ≈ v_ss`:

    p̂⁺(λ, v_ss) ≈ p̂⁺(λ, 0) + O(v_ss)
    p̂⁻(λ, v_ss) ≈ p̂⁻(λ, 0) + O(v_ss)

With p̂⁺(λ, 0) = sum of positive monomials in −q(u) evaluated at u=λ,
and p̂⁻(λ, 0) = sum of negative monomials. Since −q(λ) = 0 exactly,
p̂⁺(λ, 0) = p̂⁻(λ, 0) = some M₀ ≥ 0.

Numerically M₀ computed below (in run.py).

Steady-state v satisfies `v' = p̂⁻(λ, 0) − k·λ·v ≈ 0`, giving
`v_ss ≈ M₀ / (k·λ)`.

So k* should scale with M₀: k* ≈ 10·M₀/λ to get v_ss ≤ 0.1.

## Conway polynomial coefficients

From Conway (1987), reproduced by Wikipedia and OEIS A137275:

```
c[0..71] = [-6, 3, -6, 12, -4, 7, -7, 1, 0, 5, -2, -4, -12, 2, 7, 12,
            -7, -10, -4, 3, 9, -7, 0, -8, 14, -3, 9, 2, -3, -10, -2, -6,
            1, 10, -3, 1, 7, -7, 7, -12, -5, 8, 6, 10, -8, -8, -7, -3,
            9, 1, 6, 6, -2, -3, -10, -2, 3, 5, 2, -1, -1, -1, -1, -1,
            1, 2, 2, -1, -2, -1, 0, 1]
```
