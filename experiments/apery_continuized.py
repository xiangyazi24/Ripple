"""
Continuized series PIVP for computing F(x₀) from zero ICs.

The idea: the Apéry series terms a_n·x₀^n satisfy a recurrence with
RATIONAL coefficients in n. We "continuize" this by replacing n with a
continuous variable τ and introducing auxiliary variables for 1/(τ+1)
and 1/(2τ+1).

The resulting system is a degree-7 polynomial PIVP with ALL ZERO ICs
(well, rational ICs) that converges to F(x₀).

If this works, we can:
1. Run the continuized series PIVP to compute F(x₀), F'(x₀), F''(x₀)
2. Feed these into the main polynomial PIVP via low-pass filters
3. The combined system has rational ICs and computes ζ(3)

The critical question: does the continuous integral ∫₀^∞ b(τ) dτ
equal the discrete sum Σ b_n, or is there an Euler-Maclaurin correction?

If they differ, can we correct for it?
"""

import numpy as np
from scipy.integrate import solve_ivp
from scipy.special import zeta, comb
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt

ZETA3 = float(zeta(3))


def discrete_series(x0, N=200):
    """Compute F(x₀) = Σ a_n x₀^n discretely."""
    s = 0.0
    for n in range(1, N+1):
        cn = (-1)**(n-1) / (n**3 * comb(2*n, n, exact=True))
        s += cn * x0**n
    return s


def continuized_system(tau, y, x0):
    """Continuized series PIVP.

    State: [τ_var, p, q, b, c, bp, cp, bpp, cpp]
    where:
      τ_var: continuous counter (τ' = 1)
      p = 1/(τ_var+1): p' = -p²
      q = 1/(2τ_var+1): q' = -2q²
      b: current "term" (continuous analogue of a_n · x₀^n)
      c: running sum (c → F(x₀))
      bp, cp: for F'(x₀) — terms are n·a_n·x₀^{n-1}
      bpp, cpp: for F''(x₀) — terms are n(n-1)·a_n·x₀^{n-2}

    The recurrence: a_{n+1}x₀^{n+1} = x₀ · r(n) · a_n·x₀^n
    where r(n) = -n³/(2(n+1)²(2n+1))

    Continuized: b' = db/dτ
    At integers, we want b(n) = a_n x₀^n.
    Between integers, b(τ) interpolates.

    The "instantaneous ratio" at τ:
    r(τ) = -τ³/(2(τ+1)²(2τ+1)) = -τ³ p² q / 2

    ODE for b: b' = (x₀ · r(τ) - 1) · b = (-x₀ τ³ p² q / 2 - 1) · b

    Wait — this isn't quite right. The recurrence gives the RATIO
    between consecutive terms, not the derivative. The derivative
    d/dτ[a(τ)·x₀^τ] involves ln(x₀) which is transcendental.

    Better approach: track the TERM as b(τ) with b(n) ≈ a_n x₀^n.
    The recurrence: b_{n+1} = x₀ · r(n) · b_n
    Ratio: b_{n+1}/b_n = x₀ · r(n)

    For continuous interpolation, use: b'(τ) = [x₀·r(τ) - 1]·b(τ)
    This gives b(τ+1)/b(τ) ≈ exp(∫_τ^{τ+1} [x₀·r(s)-1] ds)
    ≈ exp(x₀·r(τ)-1) ≈ (x₀·r(τ)-1+1) = x₀·r(τ) for |x₀·r(τ)| << 1.

    Actually, the better ODE for matching the recurrence is:
    b' = ln(x₀·r(τ)) · b
    But ln is not polynomial.

    Alternative: use b' = (x₀·r(τ) - 1)·b as an approximation.
    This gives b(τ) that DECAYS like the discrete terms but may not
    match exactly. The integral ∫b dτ will differ from Σb_n.

    Let me just test numerically what ∫₀^∞ b(τ) dτ gives vs Σ b_n.
    """
    t, p, q, b, c = y

    # r(τ) = -τ³ p² q / 2
    r = -t**3 * p**2 * q / 2.0

    dt = 1.0
    dp = -p**2
    dq = -2.0 * q**2
    db = (x0 * r - 1.0) * b
    dc = b

    return [dt, dp, dq, db, dc]


def continuized_v2(tau, y, x0):
    """Version 2: use b' = (x₀·r(τ))·b (without the -1 term).

    This gives b(τ+1)/b(τ) ≈ exp(x₀·r(τ)) ≈ x₀·r(τ) for small ratio.
    But actually, we want b to match the DISCRETE recurrence more closely.

    Alternative formulation: track log(|b|) instead of b.
    Let L = ln|b|. Then L' = x₀·r(τ) - 1 (from v1) or L' = ln(x₀|r(τ)|) (exact).
    Neither is polynomial.

    Let's try yet another approach: track the PARTIAL SUM directly.
    """
    t, p, q, b, c = y
    r = -t**3 * p**2 * q / 2.0

    dt = 1.0
    dp = -p**2
    dq = -2.0 * q**2
    # b' = (x₀·r(τ)) · b (no -1 term, smoother)
    db = x0 * r * b
    dc = b

    return [dt, dp, dq, db, dc]


def run():
    fig, axes = plt.subplots(2, 2, figsize=(14, 10))
    fig.suptitle('Continuized Series: ∫b(τ)dτ vs Σb_n', fontsize=14)

    x0 = 0.01
    F_exact = discrete_series(x0, 300)
    print(f"x₀ = {x0}")
    print(f"F(x₀) exact (series) = {F_exact:.15e}")

    # b(1) = a₁·x₀ = x₀/2
    b0 = x0 / 2.0

    # ICs: τ=1, p=1/2, q=1/3, b=b0, c=b0 (first term already counted)
    # Actually start at τ=1 with c=b0 (the n=1 term)
    y0 = [1.0, 0.5, 1.0/3.0, b0, b0]

    TAU_MAX = 50.0
    tau_eval = np.linspace(1, TAU_MAX, 5000)

    # --- Version 1: b' = (x₀r - 1)b ---
    print("\n=== Version 1: b' = (x₀r - 1)b ===")
    sol1 = solve_ivp(lambda t, y: continuized_system(t, y, x0),
                     [1, TAU_MAX], y0, t_eval=tau_eval,
                     rtol=1e-13, atol=1e-15, method='DOP853')

    c1_final = sol1.y[4, -1]
    err1 = abs(c1_final - F_exact)
    print(f"  ∫b dτ = {c1_final:.15e}")
    print(f"  Error vs discrete sum = {err1:.2e}")
    print(f"  Relative error = {err1/abs(F_exact):.2e}")

    ax = axes[0, 0]
    ax.semilogy(sol1.t, np.abs(sol1.y[3]), 'b-', lw=1)
    ax.set_title('V1: |b(τ)| (term magnitude)')
    ax.set_xlabel('τ'); ax.set_ylabel('|b(τ)|')
    ax.grid(True, alpha=0.3)

    ax = axes[0, 1]
    ax.plot(sol1.t, sol1.y[4], 'b-', lw=1.5, label=f'c(τ) → {c1_final:.6e}')
    ax.axhline(F_exact, color='r', ls='--', alpha=0.5, label=f'F(x₀) = {F_exact:.6e}')
    ax.set_title('V1: running sum c(τ)')
    ax.set_xlabel('τ'); ax.set_ylabel('c')
    ax.legend(fontsize=8); ax.grid(True, alpha=0.3)

    # --- Version 2: b' = x₀r·b ---
    print("\n=== Version 2: b' = x₀r·b ===")
    sol2 = solve_ivp(lambda t, y: continuized_v2(t, y, x0),
                     [1, TAU_MAX], y0, t_eval=tau_eval,
                     rtol=1e-13, atol=1e-15, method='DOP853')

    c2_final = sol2.y[4, -1]
    err2 = abs(c2_final - F_exact)
    print(f"  ∫b dτ = {c2_final:.15e}")
    print(f"  Error vs discrete sum = {err2:.2e}")
    print(f"  Relative error = {err2/abs(F_exact):.2e}")

    ax = axes[1, 0]
    ax.semilogy(sol2.t, np.abs(sol2.y[3]), 'r-', lw=1)
    ax.set_title('V2: |b(τ)| (term magnitude)')
    ax.set_xlabel('τ'); ax.set_ylabel('|b(τ)|')
    ax.grid(True, alpha=0.3)

    ax = axes[1, 1]
    ax.plot(sol2.t, sol2.y[4], 'r-', lw=1.5, label=f'c(τ) → {c2_final:.6e}')
    ax.axhline(F_exact, color='r', ls='--', alpha=0.5, label=f'F(x₀) = {F_exact:.6e}')
    ax.set_title('V2: running sum c(τ)')
    ax.set_xlabel('τ'); ax.set_ylabel('c')
    ax.legend(fontsize=8); ax.grid(True, alpha=0.3)

    # --- Compare discrete terms with continuous ---
    print("\n=== Discrete vs Continuous term comparison ===")
    print(f"  {'n':>4s}  {'a_n x₀^n':>15s}  {'b_v1(n)':>15s}  {'b_v2(n)':>15s}")
    for n in range(1, 15):
        a_n = (-1)**(n-1) / (n**3 * comb(2*n, n, exact=True))
        bn_exact = a_n * x0**n

        # Interpolate continuous b at integer τ=n
        idx1 = np.argmin(np.abs(sol1.t - n))
        idx2 = np.argmin(np.abs(sol2.t - n))
        b_v1 = sol1.y[3, idx1]
        b_v2 = sol2.y[3, idx2]

        print(f"  {n:4d}  {bn_exact:15.6e}  {b_v1:15.6e}  {b_v2:15.6e}")

    plt.tight_layout()
    outpath = '/Users/huangx/.openclaw/workspace/projects/Ripple/experiments/apery_continuized.png'
    plt.savefig(outpath, dpi=150, bbox_inches='tight')
    print(f"\nPlot saved to {outpath}")


if __name__ == '__main__':
    run()
