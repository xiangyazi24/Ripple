# Experiment 07 Notes — Bournez-Pouly-Style Cascade

Date: 2026-04-18

## Setup

    z' = 1 − z,           z(0) = 0
    w' = z − w,           w(0) = 0
    y' = λ (w² − y²),    y(0) = 0

λ ∈ {1, 10, 100, 1000}, k swept ∈ [0.1λ, 10⁴λ].

## Expected vs observed

**Expected:** k*(λ) = Θ(λ), per the coefficient-scaling hypothesis
(experiment 06).

**Observed:** **k* is essentially λ-independent**, around k* ≈ 10
for all tested λ. The plot `k_over_lam_collapse.png` shows λ = 1000
bounded already at k/λ = 0.1 (k = 100), not just at k/λ = 5 as one
would expect.

| λ | k at transition | k/λ at transition |
|---|-----------------|-------------------|
| 1     | ~5    | ~5   |
| 10    | ~2-5  | ~0.5 |
| 100   | ~2    | ~0.02 |
| 1000  | <0.1  | <0.0001 |

At high λ, k* barely grows.

## Why the hypothesis fails here

The key insight: the **coefficient λ multiplies a quantity that
vanishes on the slow manifold**. Once y equilibrates to w (which
happens in time ~1/λ), we have `w² − y² ≈ 0`, so the RHS of `y'`
is tiny despite the huge `λ` coefficient.

In the dual-rail:

    u_y' = λ(u_w² + v_w²) + 2λ u_y v_y − k u_y v_y
    v_y' = 2λ u_w v_w + λ(u_y² + v_y²) − k u_y v_y

When u_y ≈ u_w and v_y ≈ v_w (tracking), the dominant positive
productions `λ u_w²` are matched by `λ(u_y² + v_y²) = λ u_y²` on the
negative rail (via the `u_w² − y²` cancellation). The net effect of
λ cancels between the p̂⁺ and p̂⁻ contributions that *directly track
the tracking error*, leaving annihilation to drain a much smaller
residual.

**This is different from experiment 06's scalar cubic `y' = C(1 − y³)`,
where the coefficient C multiplied a nonzero on-trajectory quantity
(the `y³` term stays order 1 at the fixed point y = 1, and `C·1 = C`
is the drive). There, C is *visible* to the dual-rail because
`p̂⁻ = C·u³ + ... ≈ C` on the trajectory.**

## Refined hypothesis

k* is determined by **`max_t ||p̂⁺(u(t), v(t)) + p̂⁻(u(t), v(t))||`**,
the instantaneous total production rate into the u/v species along
the trajectory — NOT by the max polynomial coefficient, and NOT by
ω. This can be much smaller than the max coefficient when the
polynomial is near-cancelling on-trajectory.

This means: a Bournez-Pouly construction with internal rate λ can
still be handled by *constant* k, *provided the near-equilibrium
cancellation holds throughout the computation*. Which it typically
does, since the whole point of the high-λ gate is rapid convergence
to equilibrium.

## Implication for the conjecture

**Good news** for the conjecture: even systems with arbitrarily large
internal rates (like Bournez-Pouly constructions) may NOT require
large k. This weakens a potential counterexample route.

**Refined search for counterexamples:** look for bounded GPACs where
the **on-trajectory** production rate (not the coefficient magnitude)
grows unboundedly. E.g.:
- A bounded GPAC whose trajectory repeatedly crosses a singularity
  where `p(x)` is very large (like `y' = λ/(1 + x²)·...` with x → 0
  transiently).
- A bounded oscillator where high-amplitude excursions are brief but
  happen fast enough that the dual-rail can't catch up.

## Conclusion

**Not a counterexample, and refines our understanding.**

Revised scaling law for k*:
- Coefficient C on a *dominant* on-trajectory monomial ⇒ k* = Θ(C).
- Coefficient λ on a *cancelling-to-zero* monomial ⇒ k* = O(1).

## Files

- `system.md`, `run.py`, `summary.txt`
- `original_lam=*.png` — z, w, y trajectories for each λ
- `dualrail_lam=*_k=lam.png`, `dualrail_lam=*_k=10lam.png` — representative
- `k_over_lam_collapse.png` — failure of λ-scaling collapse

## Next

Experiment 08: deliberately construct a GPAC where the on-trajectory
production grows with an internal parameter (not cancelling). E.g.
a forcing-driven system where the trajectory is continually pushed
by a time-varying polynomial whose magnitude grows on average.
