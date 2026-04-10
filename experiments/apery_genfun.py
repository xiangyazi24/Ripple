"""
Apéry generating function approach to ζ(3) first-floor computability.

Key idea: The series F(x) = Σ_{n≥1} (-1)^{n-1}/(n³ C(2n,n)) x^n satisfies
a linear ODE with polynomial (integer) coefficients. F(1) = (2/5)ζ(3).

Since the radius of convergence is 4, F is analytic at x=1, so
F(1-e^{-t}) → F(1) at exponential rate (at least e^{-t}).

The change of variables x = 1-e^{-t}, implemented by x' = 1-x,
gives a polynomial ODE in t. If we can handle the regular singular
point at x=0, this gives a PIVP with rational coefficients computing
ζ(3) at first-floor rate.

The ODE for F:
The recurrence: 2(n+1)²(2n+1) a_{n+1} + n³ a_n = 0 for n ≥ 1.
At n=0: 2·a₁ = 1 ≠ 0, so the generating function ODE is NON-HOMOGENEOUS.

Via generating function machinery (θ = x d/dx):
(4θ³ - 2θ² + xθ³)F = x
i.e., x²(4+x) F''' + x(10+3x) F'' + (2+x) F' = 1
"""

import numpy as np
from scipy.integrate import solve_ivp
from scipy.special import zeta, comb
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt

ZETA3 = float(zeta(3))


def apery_series(x, N=200):
    """Compute F(x) = Σ_{n=1}^N (-1)^{n-1}/(n³ C(2n,n)) x^n."""
    s = 0.0
    for n in range(1, N+1):
        term = (-1)**(n-1) / (n**3 * comb(2*n, n, exact=True)) * x**n
        s += term
    return s


def apery_series_derivs(x, N=200):
    """Compute F(x), F'(x), F''(x) from the series."""
    F = 0.0
    Fp = 0.0
    Fpp = 0.0
    for n in range(1, N+1):
        cn = (-1)**(n-1) / (n**3 * comb(2*n, n, exact=True))
        F += cn * x**n
        Fp += cn * n * x**(n-1) if n >= 1 else 0
        Fpp += cn * n * (n-1) * x**(n-2) if n >= 2 else 0
    return F, Fp, Fpp


def verify_ode_at_point(x0=0.5, N=300):
    """Verify the ODE at a specific point using the series."""
    F = 0.0
    Fp = 0.0
    Fpp = 0.0
    Fppp = 0.0
    for n in range(1, N+1):
        cn = (-1)**(n-1) / (n**3 * comb(2*n, n, exact=True))
        F += cn * x0**n
        if n >= 1:
            Fp += cn * n * x0**(n-1)
        if n >= 2:
            Fpp += cn * n * (n-1) * x0**(n-2)
        if n >= 3:
            Fppp += cn * n * (n-1) * (n-2) * x0**(n-3)

    # ODE: x²(4+x) F''' + x(10+3x) F'' + (2+x) F' = 1
    lhs = (x0**2 * (4+x0) * Fppp
           + x0 * (10 + 3*x0) * Fpp
           + (2 + x0) * Fp)
    residual = lhs - 1.0
    print(f"ODE verification at x={x0}: LHS={lhs:.6f}, residual={residual:.2e}")
    print(f"  F={F:.10f}, F'={Fp:.10f}, F''={Fpp:.10f}, F'''={Fppp:.10f}")
    return residual


def system_x_domain(x, y):
    """ODE system in x-domain.

    State: [F, F', F'']
    ODE: x²(4+x) F''' + x(10+3x) F'' + (2+x) F' = 1
    So: F''' = [1 - x(10+3x) F'' - (2+x) F'] / [x²(4+x)]
    """
    F, Fp, Fpp = y
    if abs(x) < 1e-15:
        # Use series: F'''(0) = 6a_3 = 6/540 = 1/90
        return [Fp, Fpp, 1.0/90.0]

    Fppp = (1.0 - x * (10 + 3*x) * Fpp - (2 + x) * Fp) / (x**2 * (4 + x))
    return [Fp, Fpp, Fppp]


def system_t_domain(t, y):
    """ODE system in t-domain with x = 1 - e^{-t}.

    State: [x, F, G1, G2] where G1 = F', G2 = F'' (derivatives w.r.t. x)

    x' = 1-x (= e^{-t})
    F_dot = G1 · (1-x)
    G1_dot = G2 · (1-x)
    G2_dot = F'''(x) · (1-x) where F''' from the ODE

    The ODE: x²(4+x) F''' + x(10+3x) F'' + (2+x) F' = 1
    So: F''' = [1 - x(10+3x) G2 - (2+x) G1] / [x²(4+x)]
    """
    x, F, G1, G2 = y
    dx = 1.0 - x

    if abs(x) < 1e-12:
        return [dx, G1 * dx, G2 * dx, (1.0/90.0) * dx]

    Fppp = (1.0 - x * (10 + 3*x) * G2 - (2 + x) * G1) / (x**2 * (4 + x))
    dF = G1 * dx
    dG1 = G2 * dx
    dG2 = Fppp * dx

    return [dx, dF, dG1, dG2]


def run():
    fig, axes = plt.subplots(2, 2, figsize=(14, 10))
    fig.suptitle('Apéry Generating Function: F(x) → (2/5)ζ(3) at x=1', fontsize=14)

    target = (2.0/5.0) * ZETA3
    print(f"Target: F(1) = (2/5)ζ(3) = {target:.15f}")
    print(f"ζ(3) = {ZETA3:.15f}")
    print()

    # --- Step 0: Verify the ODE ---
    print("=== ODE Verification ===")
    for x0 in [0.1, 0.3, 0.5, 0.8, 1.0]:
        verify_ode_at_point(x0, N=300)
    print()

    # --- Step 1: Series computation of F(1) ---
    print("=== Series Computation ===")
    for N in [10, 20, 50, 100, 200]:
        val = apery_series(1.0, N)
        err = abs(val - target)
        print(f"  N={N:4d}: F(1) = {val:.15f}, error = {err:.2e}")
    print()

    # --- Step 2: Integrate in x-domain from x0 to x=1 ---
    print("=== x-domain ODE integration ===")
    x0 = 0.01
    F0, Fp0, Fpp0 = apery_series_derivs(x0, N=300)
    print(f"  Starting at x0={x0}: F={F0:.10e}, F'={Fp0:.10e}, F''={Fpp0:.10e}")

    sol_x = solve_ivp(system_x_domain, [x0, 1.0], [F0, Fp0, Fpp0],
                      t_eval=np.linspace(x0, 1.0, 2000),
                      rtol=1e-13, atol=1e-15, method='DOP853')
    F_at_1 = sol_x.y[0, -1]
    err_x = abs(F_at_1 - target)
    print(f"  F(1) via ODE = {F_at_1:.15f}, error = {err_x:.2e}")
    print()

    # Plot x-domain
    ax = axes[0, 0]
    ax.plot(sol_x.t, sol_x.y[0], 'b-', lw=1.5)
    ax.axhline(target, color='r', ls='--', alpha=0.5, label=f'(2/5)ζ(3) = {target:.6f}')
    ax.set_title('F(x) from x₀ to 1 (x-domain ODE)')
    ax.set_xlabel('x'); ax.set_ylabel('F(x)')
    ax.legend(fontsize=8); ax.grid(True, alpha=0.3)

    # --- Step 3: Integrate in t-domain: x(t) = 1 - e^{-t} ---
    print("=== t-domain ODE integration (x = 1 - e^{-t}) ===")
    # Start at t0 corresponding to x0
    t0 = -np.log(1 - x0)
    T_MAX = 30.0
    print(f"  Starting at t0={t0:.4f} (x0={x0})")

    t_eval = np.linspace(t0, T_MAX, 4000)
    y0_t = [x0, F0, Fp0, Fpp0]

    sol_t = solve_ivp(system_t_domain, [t0, T_MAX], y0_t,
                      t_eval=t_eval,
                      rtol=1e-13, atol=1e-15, method='DOP853')

    F_t = sol_t.y[1]
    err_t = np.abs(F_t - target)

    F_final_t = F_t[-1]
    print(f"  F(1) via t-domain ODE = {F_final_t:.15f}, error = {abs(F_final_t - target):.2e}")

    # Fit convergence rate
    mask = (err_t > 1e-13) & (sol_t.t > 2) & (sol_t.t < T_MAX - 2)
    if mask.sum() > 10:
        coeffs = np.polyfit(sol_t.t[mask], np.log(np.maximum(err_t[mask], 1e-16)), 1)
        alpha = -coeffs[0]
        floor = "FIRST" if alpha > 0.3 else "NOT first"
    else:
        alpha = float('nan')
        floor = "N/A (converged too fast)"
    print(f"  Convergence rate α = {alpha:.4f} → {floor} floor")
    print()

    # Plot t-domain convergence
    ax = axes[0, 1]
    ax.semilogy(sol_t.t, np.maximum(err_t, 1e-16), 'b-', lw=1.5, label=f'|F - (2/5)ζ(3)|, α={alpha:.2f}')
    ax.semilogy(t_eval, np.exp(-t_eval), 'r--', alpha=0.4, label='e^{-t}')
    ax.semilogy(t_eval, np.exp(-2*t_eval), 'g--', alpha=0.4, label='e^{-2t}')
    ax.set_title('t-domain convergence (gen. function)')
    ax.set_xlabel('t'); ax.set_ylabel('|F(x(t)) - (2/5)ζ(3)|')
    ax.legend(fontsize=8); ax.grid(True, alpha=0.3)

    # --- Step 4: Full ζ(3) via scaling ---
    ax = axes[1, 0]
    zeta3_t = (5.0/2.0) * F_t
    err_zeta3 = np.abs(zeta3_t - ZETA3)
    ax.semilogy(sol_t.t, np.maximum(err_zeta3, 1e-16), 'b-', lw=1.5, label='|(5/2)F - ζ(3)|')
    ax.semilogy(t_eval, np.exp(-t_eval), 'r--', alpha=0.4, label='e^{-t}')
    ax.set_title('ζ(3) convergence via (5/2)F(x(t))')
    ax.set_xlabel('t'); ax.set_ylabel('Error')
    ax.legend(fontsize=8); ax.grid(True, alpha=0.3)
    print(f"  ζ(3) via (5/2)F = {zeta3_t[-1]:.15f}, error = {abs(zeta3_t[-1]-ZETA3):.2e}")

    # --- Step 5: Compare with polylog cascade ---
    print("\n=== Comparison with polylog cascade ===")
    T_EVAL_P = np.linspace(0, T_MAX, 4000)

    def polylog_cascade(t, y):
        S1, S2, S3, u = y
        return [u/(1+u), np.log(2)-S1, np.pi**2/12-S2, -u]

    sol_P = solve_ivp(polylog_cascade, [0, T_MAX], [0,0,0,1],
                      t_eval=T_EVAL_P, rtol=1e-13, atol=1e-15, method='DOP853')
    zeta3_P = (4.0/3.0) * sol_P.y[2]
    err_P = np.abs(zeta3_P - ZETA3)
    mask_P = (err_P > 1e-13) & (sol_P.t > 2) & (sol_P.t < T_MAX - 2)
    if mask_P.sum() > 10:
        coeffs_P = np.polyfit(sol_P.t[mask_P], np.log(np.maximum(err_P[mask_P], 1e-16)), 1)
        alpha_P = -coeffs_P[0]
    else:
        alpha_P = float('nan')

    ax = axes[1, 1]
    ax.semilogy(sol_t.t, np.maximum(err_zeta3, 1e-16), 'b-', lw=1.5,
                label=f'Gen. func. (α={alpha:.2f})')
    ax.semilogy(sol_P.t, np.maximum(err_P, 1e-16), 'c-', lw=1,
                label=f'Polylog cascade (α={alpha_P:.2f})')
    ax.semilogy(T_EVAL_P, np.exp(-T_EVAL_P), 'r--', alpha=0.4, label='e^{-t}')
    ax.set_title('Comparison: gen. function vs polylog cascade')
    ax.set_xlabel('t'); ax.set_ylabel('|output - ζ(3)|')
    ax.legend(fontsize=8); ax.grid(True, alpha=0.3)

    plt.tight_layout()
    outpath = '/Users/huangx/.openclaw/workspace/projects/Ripple/experiments/apery_genfun.png'
    plt.savefig(outpath, dpi=150, bbox_inches='tight')
    print(f"\nPlot saved to {outpath}")

    # --- Summary ---
    print(f"\n{'='*60}")
    print("SUMMARY")
    print(f"{'='*60}")
    print(f"ζ(3) = {ZETA3:.15f}")
    print(f"(2/5)ζ(3) = {target:.15f}")
    print(f"")
    print(f"Series F(1) (N=200): {apery_series(1.0, 200):.15f}")
    print(f"x-domain ODE F(1):   {F_at_1:.15f}")
    print(f"t-domain ODE F(1):   {F_final_t:.15f}")
    print(f"")
    print(f"Gen. func. convergence rate: α = {alpha:.4f}")
    print(f"Polylog cascade rate:        α = {alpha_P:.4f}")
    print(f"")
    print("KEY QUESTION: Does the gen. func. ODE have ONLY")
    print("rational coefficients and rational ICs?")
    print(f"  ODE coefficients: x²(4+x)F''' + x(10+3x)F'' + (2+x)F' = 0")
    print(f"  → YES, all integer coefficients!")
    print(f"  ICs: F(0)=0, F'(0)=1/2, F''(0)=-1/24")
    print(f"  → YES, all rational!")
    print(f"  Singularity at x=0: regular singular point (need to handle)")


if __name__ == '__main__':
    run()
