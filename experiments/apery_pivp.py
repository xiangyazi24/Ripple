"""
The TIME-RESCALED polynomial system for ζ(3).

Key result: the ODE x²(4+x)F''' + x(10+3x)F'' + (2+x)F' = 1
can be rewritten as a POLYNOMIAL autonomous system via time rescaling:

  x'  = x²(4+x)(1-x)                                       [polynomial!]
  F'  = G1·x²(4+x)(1-x)                                    [polynomial!]
  G1' = G2·x²(4+x)(1-x)                                    [polynomial!]
  G2' = (1-x)[1 - (10x+3x²)G2 - (2+x)G1]                  [polynomial!]

This is a PIVP! All right-hand sides are polynomial in (x, F, G1, G2).
The system computes ζ(3) = (5/2)·F(∞) with exponential convergence.

Remaining issue: the exact initial conditions are at x=0 (where x is a
fixed point), so we must start at x₀>0 with series-derived ICs.

This experiment:
1. Measures convergence RATE in the rescaled time
2. Shows the polynomial PIVP IS first-floor
3. Analyzes sensitivity to IC precision (does approximate IC → approximate limit?)
"""

import numpy as np
from scipy.integrate import solve_ivp
from scipy.special import zeta, comb
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt

ZETA3 = float(zeta(3))
TARGET = (2.0/5.0) * ZETA3


def apery_series_derivs(x, N=300):
    """Compute F(x), F'(x), F''(x) from the Apéry accelerated series."""
    F = 0.0
    Fp = 0.0
    Fpp = 0.0
    for n in range(1, N+1):
        cn = (-1)**(n-1) / (n**3 * comb(2*n, n, exact=True))
        F += cn * x**n
        Fp += cn * n * x**(n-1)
        if n >= 2:
            Fpp += cn * n * (n-1) * x**(n-2)
    return F, Fp, Fpp


def pivp_polynomial(tau, y):
    """The polynomial PIVP for ζ(3).

    State: [x, F, G1, G2]
    ALL right-hand sides are polynomial.
    """
    x, F, G1, G2 = y
    h = x**2 * (4 + x) * (1 - x)
    dx = h
    dF = G1 * h
    dG1 = G2 * h
    dG2 = (1-x) * (1.0 - (10*x + 3*x**2)*G2 - (2+x)*G1)
    return [dx, dF, dG1, dG2]


def run():
    fig, axes = plt.subplots(2, 2, figsize=(14, 10))
    fig.suptitle('Polynomial PIVP for ζ(3) — Time-Rescaled Apéry ODE', fontsize=14)

    # --- Test 1: Convergence rate measurement ---
    print("=== Polynomial PIVP: convergence rate ===")
    x0 = 0.01
    F0, G10, G20 = apery_series_derivs(x0, N=300)

    TAU_MAX = 200.0
    tau_eval = np.linspace(0, TAU_MAX, 20000)

    sol = solve_ivp(pivp_polynomial, [0, TAU_MAX],
                    [x0, F0, G10, G20],
                    t_eval=tau_eval, rtol=1e-13, atol=1e-15,
                    method='DOP853')

    x_sol = sol.y[0]
    F_sol = sol.y[1]
    G1_sol = sol.y[2]
    G2_sol = sol.y[3]
    err_F = np.abs(F_sol - TARGET)
    err_x = np.abs(x_sol - 1.0)

    # Fit convergence rate (near x=1, expect exp(-5τ) since x'≈5(1-x))
    mask = (err_F > 1e-14) & (sol.t > 20) & (sol.t < TAU_MAX - 5)
    if mask.sum() > 10:
        coeffs = np.polyfit(sol.t[mask], np.log(np.maximum(err_F[mask], 1e-16)), 1)
        alpha_F = -coeffs[0]
    else:
        alpha_F = float('nan')

    mask_x = (err_x > 1e-14) & (sol.t > 20) & (sol.t < TAU_MAX - 5)
    if mask_x.sum() > 10:
        coeffs_x = np.polyfit(sol.t[mask_x], np.log(np.maximum(err_x[mask_x], 1e-16)), 1)
        alpha_x = -coeffs_x[0]
    else:
        alpha_x = float('nan')

    print(f"  x convergence rate:    α_x = {alpha_x:.4f}")
    print(f"  F convergence rate:    α_F = {alpha_F:.4f}")
    print(f"  Expected near x=1:     α ≈ 5 (since x²(4+x)(1-x) ≈ 5(1-x))")
    print(f"  F(τ_max) = {F_sol[-1]:.15f}")
    print(f"  error = {err_F[-1]:.2e}")
    print()

    ax = axes[0, 0]
    ax.semilogy(sol.t, np.maximum(err_x, 1e-16), 'b-', lw=1, label=f'|x-1|, α={alpha_x:.2f}')
    ax.semilogy(sol.t, np.maximum(err_F, 1e-16), 'r-', lw=1.5, label=f'|F-target|, α={alpha_F:.2f}')
    ax.semilogy(tau_eval, np.exp(-5*tau_eval)*0.01, 'k--', alpha=0.3, label='~e^{-5τ}')
    ax.set_title('Polynomial PIVP convergence')
    ax.set_xlabel('τ (rescaled time)'); ax.set_ylabel('Error')
    ax.legend(fontsize=8); ax.grid(True, alpha=0.3)

    # --- Test 2: Sensitivity to IC precision ---
    print("=== IC sensitivity analysis ===")
    perturbations = [1e-4, 1e-6, 1e-8, 1e-10, 1e-12]
    F_finals = []

    for delta in perturbations:
        sol_p = solve_ivp(pivp_polynomial, [0, TAU_MAX],
                          [x0, F0 + delta, G10, G20],
                          rtol=1e-13, atol=1e-15, method='DOP853')
        F_p = sol_p.y[1, -1]
        err_p = abs(F_p - TARGET)
        amplification = err_p / delta if delta > 0 else float('nan')
        print(f"  δF₀ = {delta:.0e}: F(∞) error = {err_p:.2e}, amplification = {amplification:.2f}")
        F_finals.append(err_p)

    ax = axes[0, 1]
    ax.loglog(perturbations, F_finals, 'bo-', lw=1.5)
    ax.loglog(perturbations, perturbations, 'r--', alpha=0.5, label='linear (amplification=1)')
    ax.set_title('IC sensitivity: δF₀ → δF(∞)')
    ax.set_xlabel('IC perturbation δF₀'); ax.set_ylabel('Output error δF(∞)')
    ax.legend(fontsize=8); ax.grid(True, alpha=0.3)

    # --- Test 3: Different x₀ starting points ---
    print("\n=== Different starting points ===")
    x0_vals = [0.001, 0.01, 0.05, 0.1, 0.3, 0.5]
    for x0_test in x0_vals:
        F0_t, G10_t, G20_t = apery_series_derivs(x0_test, N=300)
        sol_t = solve_ivp(pivp_polynomial, [0, TAU_MAX],
                          [x0_test, F0_t, G10_t, G20_t],
                          rtol=1e-13, atol=1e-15, method='DOP853')
        F_t = sol_t.y[1, -1]
        err_t = abs(F_t - TARGET)
        x_t = sol_t.y[0, -1]
        print(f"  x₀={x0_test:.3f}: x(∞)={x_t:.10f}, F(∞) error={err_t:.2e}")

    # --- Test 4: ζ(3) via the polynomial PIVP ---
    ax = axes[1, 0]
    zeta3_sol = (5.0/2.0) * F_sol
    err_zeta3 = np.abs(zeta3_sol - ZETA3)
    ax.semilogy(sol.t, np.maximum(err_zeta3, 1e-16), 'b-', lw=1.5,
                label=f'|(5/2)F - ζ(3)|, α={alpha_F:.2f}')
    ax.semilogy(tau_eval, np.exp(-5*tau_eval)*0.01, 'k--', alpha=0.3, label='~e^{-5τ}')
    ax.set_title('ζ(3) from polynomial PIVP')
    ax.set_xlabel('τ'); ax.set_ylabel('|output - ζ(3)|')
    ax.legend(fontsize=8); ax.grid(True, alpha=0.3)

    # --- Test 5: Phase portrait (x vs F) ---
    ax = axes[1, 1]
    ax.plot(x_sol, F_sol, 'b-', lw=1.5)
    ax.axhline(TARGET, color='r', ls='--', alpha=0.5, label=f'(2/5)ζ(3)')
    ax.axvline(1.0, color='g', ls='--', alpha=0.3)
    ax.plot(x_sol[0], F_sol[0], 'go', ms=8, label=f'start (x₀={x0})')
    ax.plot(x_sol[-1], F_sol[-1], 'r*', ms=10, label='end (x≈1)')
    ax.set_title('Phase portrait: x vs F')
    ax.set_xlabel('x'); ax.set_ylabel('F')
    ax.legend(fontsize=8); ax.grid(True, alpha=0.3)

    plt.tight_layout()
    outpath = '/Users/huangx/.openclaw/workspace/projects/Ripple/experiments/apery_pivp.png'
    plt.savefig(outpath, dpi=150, bbox_inches='tight')
    print(f"\nPlot saved to {outpath}")

    # --- Grand Summary ---
    print(f"\n{'='*70}")
    print("POLYNOMIAL PIVP FOR ζ(3) — GRAND SUMMARY")
    print(f"{'='*70}")
    print(f"")
    print(f"THE SYSTEM (all polynomial):")
    print(f"  x'  = x²(4+x)(1-x)         = 4x² - 3x³ - x⁴")
    print(f"  F'  = G1·x²(4+x)(1-x)")
    print(f"  G1' = G2·x²(4+x)(1-x)")
    print(f"  G2' = (1-x)[1 - (10x+3x²)G2 - (2+x)G1]")
    print(f"")
    print(f"OUTPUT: ζ(3) = (5/2)·lim F(τ) as τ→∞")
    print(f"")
    print(f"CONVERGENCE: exponential with rate α_F ≈ {alpha_F:.2f}")
    print(f"  (near x=1: x²(4+x) ≈ 5, so rate ≈ 5 in rescaled time)")
    print(f"")
    print(f"IC SENSITIVITY: amplification factor ≈ 1 (well-conditioned)")
    print(f"")
    print(f"REMAINING ISSUE: x=0 is a fixed point.")
    print(f"  Must start at x₀ > 0 with series-derived ICs.")
    print(f"  ICs at x₀ are NOT exactly rational but can be")
    print(f"  approximated to arbitrary precision by rational partial sums.")
    print(f"  IC error → proportional output error (amplification ≈ 1).")
    print(f"")
    print(f"FOR R_RTCRN: need a single PIVP with rational ICs that")
    print(f"  computes EXACTLY ζ(3). The current construction gives")
    print(f"  a FAMILY of PIVPs, one per precision level.")
    print(f"  Gap: connecting approximate ICs to exact computation.")


if __name__ == '__main__':
    run()
