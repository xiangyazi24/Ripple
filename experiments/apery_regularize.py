"""
Attempt to regularize the Apéry generating function ODE to get a PIVP.

The ODE: x²(4+x) F''' + x(10+3x) F'' + (2+x) F' = 1

In t-domain (x = 1 - e^{-t}, x' = 1-x):
F_dot = F'·(1-x)
G1_dot = F''·(1-x)
G2_dot = F'''·(1-x) = [(1 - x(10+3x)G2 - (2+x)G1) / (x²(4+x))] · (1-x)

The 1/x² makes this non-polynomial. But the numerator vanishes to order x²
along the solution (proven by Frobenius theory), so F''' is actually bounded.

Approach 1: Time rescaling — multiply all RHS by x²(4+x)
  x_dot = x²(4+x)(1-x)   [polynomial!]
  F_dot = G1·x²(4+x)(1-x)
  G1_dot = G2·x²(4+x)(1-x)
  G2_dot = (1-x)·[1 - x(10+3x)G2 - (2+x)G1]  [polynomial!]

Problem: at x=0, ALL derivatives vanish → system stalls at t=0.
But: does it EVENTUALLY move? Yes, if we perturb slightly.

Approach 2: Auxiliary variable absorbing x²
  Define P = x²(4+x)·F''' = 1 - x(10+3x)F'' - (2+x)F'
  Then P satisfies its own ODE (differentiate the relation).

Approach 3: Rewrite F = Σ aₙ xⁿ as a DIFFERENT function.
  Since a₀=0, define H = F/x. Then H(0) = a₁ = 1/2 (nonzero).
  H = F/x, H' = (F' - H)/x = (G1 - H)/x (still has 1/x...)

Approach 4: Use x directly as time (no reparametrization).
  Just integrate from x₀=ε to x=1 with x as time.
  For PIVP: the system IS polynomial in x-time if we don't divide.
  But the PIVP needs AUTONOMOUS (no explicit time dependence).
  We can add x as a state variable with x'=1 (identity clock).
  Then: F'=G1, G1'=G2, G2' = [1 - x(10+3x)G2 - (2+x)G1]/(x²(4+x))
  Still has 1/x².

Approach 5: Factor out the singular behavior via the indicial equation.
  At x=0, the three Frobenius exponents are ρ=0 (double) and ρ=1/2.
  Our solution has ρ=0 (analytic). The second ρ=0 solution has log(x).

  Key insight: define NEW state variables that are regular at x=0.
  Since P(x) := 1 - (2+x)F' - x(10+3x)F'' vanishes to order x² at x=0
  along the analytic solution, define R = P/x².

  Then F''' = R/(4+x) and we need an ODE for R.

Let's try Approach 5 numerically.
"""

import numpy as np
from scipy.integrate import solve_ivp
from scipy.special import zeta, comb
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt

ZETA3 = float(zeta(3))
TARGET = (2.0/5.0) * ZETA3


def apery_coeffs(N=300):
    """Compute a_n = (-1)^{n-1}/(n³ C(2n,n))."""
    a = [0.0]  # a_0 = 0
    for n in range(1, N+1):
        a.append((-1)**(n-1) / (n**3 * comb(2*n, n, exact=True)))
    return a


def series_eval(a, x, k=0):
    """Evaluate k-th derivative of F(x) = Σ a_n x^n."""
    s = 0.0
    for n in range(max(k, 1), len(a)):
        coeff = a[n]
        for j in range(k):
            coeff *= (n - j)
        s += coeff * x**(n-k)
    return s


def compute_R_from_series(a, x, N=None):
    """Compute R(x) = [1 - (2+x)F' - x(10+3x)F''] / x² from series."""
    if N is None:
        N = len(a) - 1
    Fp = series_eval(a, x, 1)
    Fpp = series_eval(a, x, 2)
    P = 1.0 - (2+x)*Fp - x*(10+3*x)*Fpp
    if abs(x) < 1e-15:
        # L'Hôpital: R(0) = lim P(x)/x² as x→0
        # P(x) = Σ p_n x^n where p_0 = 0, p_1 = 0, p_2 = R(0)
        # From the ODE: R(0) = F'''(0)·(4+0) = (1/90)·4 = 4/90 = 2/45
        return 2.0/45.0
    return P / x**2


def compute_Rp_from_series(a, x):
    """Compute R'(x) from series, for verification."""
    dx = 1e-7
    if abs(x) < dx:
        return (compute_R_from_series(a, x+dx) - compute_R_from_series(a, x)) / dx
    return (compute_R_from_series(a, x+dx) - compute_R_from_series(a, x-dx)) / (2*dx)


def derive_R_ode():
    """
    Derive the ODE for R = P/x² where P = 1 - (2+x)F' - x(10+3x)F''.

    R = [1 - (2+x)F' - x(10+3x)F''] / x²

    So F''' = R/(4+x) from the original ODE x²(4+x)F''' = P = x²R.

    Differentiate R w.r.t. x:
    R' = d/dx [P/x²] = (P'x² - 2xP) / x⁴ = P'/x² - 2P/x³ = P'/x² - 2R/x

    P = 1 - (2+x)F' - x(10+3x)F''
    P' = -(F' + (2+x)F'') - ((10+6x)F'' + x(10+3x)F''')
       = -F' - (2+x)F'' - (10+6x)F'' - x(10+3x)F'''
       = -F' - (12+7x)F'' - x(10+3x)F'''

    Substitute F''' = R/(4+x):
    P' = -F' - (12+7x)F'' - x(10+3x)R/(4+x)

    Now P'/x² = -F'/x² - (12+7x)F''/x² - (10+3x)R/(x(4+x))

    This still has 1/x² ... we need F'/x² and F''/x² to be expressible
    in terms of our state variables.

    Since F = Σ a_n x^n with a_0=0:
    F/x = Σ a_n x^{n-1} → this is analytic, call it H
    F'/x = H + H' - 1/x terms... hmm

    Actually F' = a_1 + 2a_2 x + ... so F'/x² is NOT bounded at x=0 (it's ~a_1/x²).

    But wait: R' involves P'/x² - 2R/x. Let's compute P'/x²:
    P' = -F' - (12+7x)F'' - x(10+3x)R/(4+x)

    P'/x² = -F'/x² - (12+7x)F''/x² - (10+3x)R/(x(4+x))

    This diverges. So R' is NOT bounded as a function of (R, F, F', F'', x).

    HOWEVER: R' = P'/x² - 2R/x might still be bounded if the divergent
    parts cancel. Let's check numerically.
    """
    pass


def system_approach1_rescaled(tau, y):
    """Approach 1: Time-rescaled polynomial system.

    Time variable: dτ such that dt = dτ / [x²(4+x)(1-x)]
    Or equivalently, all RHS multiplied by x²(4+x):

    x_dot = x²(4+x)(1-x) = (4x² - 3x³ - x⁴)
    F_dot = G1·(4x² - 3x³ - x⁴)    [= G1·x²(4+x)(1-x)]
    G1_dot = G2·(4x² - 3x³ - x⁴)
    G2_dot = (1-x)·[1 - (10x+3x²)G2 - (2+x)G1]

    Problem: x(0)=0 is a fixed point (all dots = 0).
    We start at (x₀, F₀, G1₀, G2₀) with x₀ > 0.
    """
    x, F, G1, G2 = y
    h = x**2 * (4 + x) * (1 - x)
    dF = G1 * h
    dG1 = G2 * h
    dG2 = (1-x) * (1.0 - (10*x + 3*x**2)*G2 - (2+x)*G1)
    return [h, dF, dG1, dG2]


def system_approach5_R(t, y):
    """Approach 5: Track R = P/x² as auxiliary variable.

    State: [x, F, G1, R] where G1 = F', R = [1-(2+x)G1-x(10+3x)F'']/x²

    From R: x²R = 1 - (2+x)G1 - x(10+3x)F''
    So: F'' = [1 - (2+x)G1 - x²R] / [x(10+3x)]
    And: F''' = R/(4+x)

    t-domain (x' = 1-x):
    x_dot = 1-x
    F_dot = G1·(1-x)
    G1_dot = F''·(1-x) = [(1-(2+x)G1-x²R)/(x(10+3x))]·(1-x)
    R_dot = R'·(1-x) where R' needs to be expressed in terms of state vars

    The issue is computing R' = dR/dx in terms of (x, F, G1, R).

    From R = P/x²: R' = P'/x² - 2R/x (see derivation above)
    P' = -G1 - (12+7x)F'' - x(10+3x)R/(4+x)
    where F'' = [1-(2+x)G1-x²R]/(x(10+3x))

    R' = [-G1 - (12+7x)·{(1-(2+x)G1-x²R)/(x(10+3x))} - x(10+3x)R/(4+x)] / x²  -  2R/x

    This is complex but let me try it numerically.
    """
    x, F, G1, R = y
    dx = 1.0 - x

    if abs(x) < 1e-12:
        # At x=0: F''=−1/24, R=2/45
        # G1_dot = F''·1 = −1/24
        # R_dot: need to compute. Use series: R(ε)≈R(0)+R'(0)·ε
        return [dx, G1*dx, (-1.0/24.0)*dx, 0.0]

    # F'' from the relation: x²R = 1 - (2+x)G1 - x(10+3x)F''
    # F'' = [1 - (2+x)G1 - x²R] / [x(10+3x)]
    denom_Fpp = x * (10 + 3*x)
    Fpp = (1.0 - (2+x)*G1 - x**2 * R) / denom_Fpp

    # P' = -G1 - (12+7x)Fpp - x(10+3x)R/(4+x)
    Pp = -G1 - (12 + 7*x)*Fpp - x*(10+3*x)*R/(4+x)

    # R' = P'/x² - 2R/x
    Rp = Pp/x**2 - 2*R/x

    dF = G1 * dx
    dG1 = Fpp * dx
    dR = Rp * dx

    return [dx, dF, dG1, dR]


def run():
    a = apery_coeffs(300)

    fig, axes = plt.subplots(2, 2, figsize=(14, 10))
    fig.suptitle('Regularization Approaches for Apéry ODE', fontsize=14)

    # --- Verify R = P/x² from series ---
    print("=== R(x) = P/x² verification from series ===")
    for x0 in [0.0, 0.01, 0.1, 0.3, 0.5, 0.8, 1.0]:
        R_val = compute_R_from_series(a, x0)
        print(f"  R({x0}) = {R_val:.10f}")
    print()

    # Check if R' is bounded from series
    print("=== R'(x) from series (checking boundedness) ===")
    for x0 in [0.001, 0.01, 0.05, 0.1, 0.3, 0.5, 0.8]:
        Rp_val = compute_Rp_from_series(a, x0)
        print(f"  R'({x0}) = {Rp_val:.10f}")
    print()

    # --- Approach 1: Time-rescaled system ---
    print("=== Approach 1: Time-rescaled polynomial system ===")
    x0 = 0.01
    F0 = series_eval(a, x0, 0)
    G10 = series_eval(a, x0, 1)
    G20 = series_eval(a, x0, 2)
    print(f"  Starting at x0={x0}: F={F0:.8e}, G1={G10:.8e}, G2={G20:.8e}")

    TAU_MAX = 500.0
    tau_eval = np.linspace(0, TAU_MAX, 10000)

    sol1 = solve_ivp(system_approach1_rescaled, [0, TAU_MAX],
                     [x0, F0, G10, G20],
                     t_eval=tau_eval, rtol=1e-13, atol=1e-15,
                     method='DOP853')

    x_1 = sol1.y[0]
    F_1 = sol1.y[1]
    err_1 = np.abs(F_1 - TARGET)
    x_final = x_1[-1]
    F_final = F_1[-1]
    print(f"  x(τ_max) = {x_final:.10f}")
    print(f"  F(τ_max) = {F_final:.15f}, error = {abs(F_final - TARGET):.2e}")

    ax = axes[0, 0]
    ax.plot(sol1.t, x_1, 'b-', lw=1.5)
    ax.axhline(1.0, color='r', ls='--', alpha=0.3)
    ax.set_title(f'Approach 1: x(τ) → 1? (x_final={x_final:.4f})')
    ax.set_xlabel('τ (rescaled time)'); ax.set_ylabel('x')
    ax.grid(True, alpha=0.3)

    ax = axes[0, 1]
    ax.plot(sol1.t, F_1, 'b-', lw=1.5)
    ax.axhline(TARGET, color='r', ls='--', alpha=0.5, label=f'(2/5)ζ(3)={TARGET:.6f}')
    ax.set_title('Approach 1: F(τ) → (2/5)ζ(3)?')
    ax.set_xlabel('τ'); ax.set_ylabel('F')
    ax.legend(fontsize=8); ax.grid(True, alpha=0.3)

    # --- Approach 5: R = P/x² system ---
    print("\n=== Approach 5: R = P/x² auxiliary variable ===")
    R0 = compute_R_from_series(a, x0)
    print(f"  Starting at x0={x0}: G1={G10:.8e}, R={R0:.8e}")

    T_MAX = 30.0
    t0 = -np.log(1 - x0)
    t_eval = np.linspace(t0, T_MAX, 4000)

    try:
        sol5 = solve_ivp(system_approach5_R, [t0, T_MAX],
                         [x0, F0, G10, R0],
                         t_eval=t_eval, rtol=1e-12, atol=1e-14,
                         method='DOP853', max_step=0.1)

        F_5 = sol5.y[1]
        err_5 = np.abs(F_5 - TARGET)
        F5_final = F_5[-1]
        print(f"  F(T_max) = {F5_final:.15f}, error = {abs(F5_final - TARGET):.2e}")

        # Fit rate
        mask = (err_5 > 1e-13) & (sol5.t > 2) & (sol5.t < T_MAX - 2)
        if mask.sum() > 10:
            coeffs = np.polyfit(sol5.t[mask], np.log(np.maximum(err_5[mask], 1e-16)), 1)
            alpha5 = -coeffs[0]
        else:
            alpha5 = float('nan')
        print(f"  Convergence rate α = {alpha5:.4f}")

        ax = axes[1, 0]
        ax.semilogy(sol5.t, np.maximum(err_5, 1e-16), 'b-', lw=1.5,
                    label=f'R approach (α={alpha5:.2f})')
        ax.semilogy(t_eval, np.exp(-t_eval), 'r--', alpha=0.4, label='e^{-t}')
        ax.set_title('Approach 5: R auxiliary variable')
        ax.set_xlabel('t'); ax.set_ylabel('|F - (2/5)ζ(3)|')
        ax.legend(fontsize=8); ax.grid(True, alpha=0.3)

    except Exception as e:
        print(f"  Approach 5 FAILED: {e}")
        ax = axes[1, 0]
        ax.text(0.5, 0.5, f'Failed:\n{e}', transform=ax.transAxes,
                ha='center', va='center', fontsize=10, color='red')

    # --- Summary plot: R(x) behavior ---
    ax = axes[1, 1]
    xs = np.linspace(0.001, 1.0, 500)
    Rs = [compute_R_from_series(a, x) for x in xs]
    ax.plot(xs, Rs, 'b-', lw=1.5)
    ax.set_title('R(x) = P(x)/x² (should be smooth)')
    ax.set_xlabel('x'); ax.set_ylabel('R(x)')
    ax.grid(True, alpha=0.3)

    plt.tight_layout()
    outpath = '/Users/huangx/.openclaw/workspace/projects/Ripple/experiments/apery_regularize.png'
    plt.savefig(outpath, dpi=150, bbox_inches='tight')
    print(f"\nPlot saved to {outpath}")

    # --- Final summary ---
    print(f"\n{'='*60}")
    print("REGULARIZATION SUMMARY")
    print(f"{'='*60}")
    print(f"R(x) = P(x)/x² is smooth on [0,1]: R(0)={2/45:.6f}, R(1)={compute_R_from_series(a, 1.0):.6f}")
    print(f"")
    print(f"Approach 1 (time rescale): x reaches {x_final:.4f} at τ={TAU_MAX}")
    print(f"  → System is polynomial but slow (x stuck near 0)")
    print(f"")
    print(f"The fundamental issue: the PIVP needs polynomial RHS,")
    print(f"but the original ODE has a regular singular point at x=0.")
    print(f"Time rescaling makes it polynomial but kills convergence at x=0.")
    print(f"The R=P/x² approach eliminates F''' but R' still has 1/x terms.")


if __name__ == '__main__':
    run()
