"""
Test IBP-compensated zerolized Apéry system.

The IBP target: s̄₃' = (1/2)(u₃+w₂) + E₂ + t·E₂'
This removes the dependence on exact C = 1/(e-1).

Key test: does the IBP-corrected system with DYNAMIC constants
(E₁→e, E₂→C, E₃→D) converge to ζ(3) at first-floor rate?
"""

import numpy as np
from scipy.integrate import solve_ivp
from scipy.special import zeta
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt

ZETA3 = float(zeta(3))
T_MAX = 40.0
T_EVAL = np.linspace(0, T_MAX, 8000)


def system_full(t, y):
    """Fully dynamic zerolized Apéry system with IBP compensation.

    State variables (13 total):
    [0-6]  v, u1, u2, u3, r, w1, w2  — main block (zerolized)
    [7-10] E, E1, E2, E3             — auxiliary block
    [11]   s3_ibp                     — IBP-compensated target
    [12]   s3_no_ibp                  — simple target (for comparison)

    The IBP target:
    s̄₃' = (1/2)(u₃+w₂) + E₂ + t·E₂'
    where E₂' = 1 - (E₁-1)·E₂

    The constants in the main drift are replaced by dynamic variables:
    e → E₁, C → E₂, D → E₃
    """
    v, u1, u2, u3, r, w1, w2, E, E1, E2, E3, s3_ibp, s3_no_ibp = y

    # Auxiliary block
    dE  = 1.0 - E
    dE1 = E1 * (1.0 - E)
    E1m1 = max(E1 - 1.0, 1e-10)  # E₁ - 1 → e-1, protect early time
    dE2 = 1.0 - E1m1 * E2
    dE3 = E1 * E2 - E3

    # Main block with DYNAMIC constants
    vu1_prod = (v + E1) * (u1 + E2)
    dv  = -(v + E1) * (u1 + E2) * (v + E1 - 1.0)
    du1 = (u1 + E2) * (vu1_prod - 1.0)
    du2 = (u2 + E2) * (vu1_prod - 2.0)
    du3 = (u3 + E2) * (vu1_prod - 3.0)
    dr  = -(r + E3) * (r + E2)
    dw1 = (r + E2) - (r + E3) * (w1 + E2)
    dw2 = 2.0 * (w1 + E2) - (r + E3) * (w2 + E2)

    # IBP-compensated target: s̄₃' = (1/2)(u₃+w₂) + E₂ + t·E₂'
    ds3_ibp = 0.5 * (u3 + w2) + E2 + t * dE2

    # Simple target (no IBP): s₃' = (1/2)(u₃+w₂) + E₂
    ds3_no_ibp = 0.5 * (u3 + w2) + E2

    return [dv, du1, du2, du3, dr, dw1, dw2,
            dE, dE1, dE2, dE3, ds3_ibp, ds3_no_ibp]


def system_exact(t, y):
    """Same but with EXACT constants in drift (for baseline comparison)."""
    v, u1, u2, u3, r, w1, w2, E, E1, E2, E3, s3_exact, _ = y

    e_val = np.e
    C = 1.0 / (e_val - 1.0)
    D = e_val / (e_val - 1.0)

    dE  = 1.0 - E
    dE1 = E1 * (1.0 - E)
    dE2 = 1.0 - max(E1 - 1.0, 1e-10) * E2
    dE3 = E1 * E2 - E3

    vu1_prod = (v + e_val) * (u1 + C)
    dv  = -(v + e_val) * (u1 + C) * (v + e_val - 1.0)
    du1 = (u1 + C) * (vu1_prod - 1.0)
    du2 = (u2 + C) * (vu1_prod - 2.0)
    du3 = (u3 + C) * (vu1_prod - 3.0)
    dr  = -(r + D) * (r + C)
    dw1 = (r + C) - (r + D) * (w1 + C)
    dw2 = 2.0 * (w1 + C) - (r + D) * (w2 + C)

    # With exact constants: s₃' = (1/2)(u₃+w₂) + C
    ds3 = 0.5 * (u3 + w2) + C
    return [dv, du1, du2, du3, dr, dw1, dw2,
            dE, dE1, dE2, dE3, ds3, 0.0]


def polylog_cascade_exact(t, y):
    """Baseline: polylog cascade with exact constants."""
    S1, S2, S3, u = y
    return [u/(1+u), np.log(2)-S1, np.pi**2/12-S2, -u]


def run():
    fig, axes = plt.subplots(2, 2, figsize=(14, 10))
    fig.suptitle(f'ζ(3) Convergence: IBP Compensation Analysis', fontsize=14)

    y0 = [0.0]*7 + [0.0, 1.0, 0.0, 0.0] + [0.0, 0.0]

    # --- Polylog cascade (baseline) ---
    print("Polylog cascade (exact)...")
    sol_P = solve_ivp(polylog_cascade_exact, [0, T_MAX], [0,0,0,1],
                      t_eval=T_EVAL, rtol=1e-13, atol=1e-15, method='DOP853')
    out_P = (4/3) * sol_P.y[2]
    err_P = np.abs(out_P - ZETA3)

    # --- Exact constants ---
    print("Zerolized + exact constants...")
    sol_E = solve_ivp(system_exact, [0, T_MAX], y0,
                      t_eval=T_EVAL, rtol=1e-12, atol=1e-14,
                      method='DOP853', max_step=0.05)
    err_E = np.abs(sol_E.y[11] - ZETA3)

    # --- Dynamic + IBP ---
    print("Zerolized + dynamic + IBP...")
    sol_D = solve_ivp(system_full, [0, T_MAX], y0,
                      t_eval=T_EVAL, rtol=1e-12, atol=1e-14,
                      method='DOP853', max_step=0.05)
    err_D_ibp = np.abs(sol_D.y[11] - ZETA3)
    err_D_no_ibp = np.abs(sol_D.y[12] - ZETA3)

    # --- Plot 1: IBP vs no-IBP ---
    ax = axes[0, 0]
    ax.semilogy(sol_D.t, np.maximum(err_D_ibp, 1e-16), 'b-', lw=1.5, label='with IBP')
    ax.semilogy(sol_D.t, np.maximum(err_D_no_ibp, 1e-16), 'm-', lw=1.5, label='without IBP')
    ax.semilogy(T_EVAL, np.exp(-T_EVAL), 'r--', alpha=0.4, label='e^{-t}')
    ax.set_title('Dynamic system: IBP vs no IBP')
    ax.set_xlabel('t'); ax.set_ylabel('|output - ζ(3)|')
    ax.legend(fontsize=8); ax.grid(True, alpha=0.3)

    # --- Plot 2: All approaches compared ---
    ax = axes[0, 1]
    ax.semilogy(sol_P.t, np.maximum(err_P, 1e-16), 'c-', lw=1, label='polylog cascade')
    ax.semilogy(sol_E.t, np.maximum(err_E, 1e-16), 'g-', lw=1, label='exact C,D')
    ax.semilogy(sol_D.t, np.maximum(err_D_ibp, 1e-16), 'b-', lw=1.5, label='dynamic + IBP')
    ax.semilogy(T_EVAL, np.exp(-T_EVAL), 'r--', alpha=0.4, label='e^{-t}')
    ax.set_title('All approaches compared')
    ax.set_xlabel('t'); ax.set_ylabel('Error')
    ax.legend(fontsize=8); ax.grid(True, alpha=0.3)

    # --- Plot 3: Values over time ---
    ax = axes[1, 0]
    ax.plot(sol_D.t, sol_D.y[11], 'b-', lw=1.5, label='IBP target')
    ax.plot(sol_D.t, sol_D.y[12], 'm-', lw=1, label='simple target')
    ax.axhline(ZETA3, color='r', ls='--', alpha=0.5, label=f'ζ(3)={ZETA3:.6f}')
    ax.set_title('Target values over time')
    ax.set_xlabel('t'); ax.set_ylabel('value')
    ax.legend(fontsize=8); ax.grid(True, alpha=0.3)
    ax.set_xlim(0, T_MAX)

    # --- Plot 4: Auxiliary block convergence ---
    ax = axes[1, 1]
    e_val = np.e
    C_val = 1.0/(e_val-1)
    D_val = e_val/(e_val-1)
    ax.semilogy(sol_D.t, np.maximum(np.abs(sol_D.y[7] - 1.0), 1e-16), label='|E-1|')
    ax.semilogy(sol_D.t, np.maximum(np.abs(sol_D.y[8] - e_val), 1e-16), label='|E₁-e|')
    ax.semilogy(sol_D.t, np.maximum(np.abs(sol_D.y[9] - C_val), 1e-16), label='|E₂-C|')
    ax.semilogy(sol_D.t, np.maximum(np.abs(sol_D.y[10] - D_val), 1e-16), label='|E₃-D|')
    ax.semilogy(T_EVAL, np.exp(-T_EVAL), 'r--', alpha=0.4, label='e^{-t}')
    ax.set_title('Auxiliary block convergence')
    ax.set_xlabel('t'); ax.set_ylabel('Error')
    ax.legend(fontsize=8); ax.grid(True, alpha=0.3)

    plt.tight_layout()
    outpath = '/Users/huangx/.openclaw/workspace/projects/Ripple/experiments/apery_ibp.png'
    plt.savefig(outpath, dpi=150, bbox_inches='tight')
    print(f"\nPlot saved to {outpath}")

    # Summary
    print(f"\n{'='*60}")
    print(f"SUMMARY")
    print(f"{'='*60}")
    print(f"ζ(3) = {ZETA3:.15f}")
    print(f"")

    for label, t_arr, err_arr, val_arr in [
        ("Polylog cascade (exact)", sol_P.t, err_P, out_P),
        ("Exact C,D in drift", sol_E.t, err_E, sol_E.y[11]),
        ("Dynamic + IBP", sol_D.t, err_D_ibp, sol_D.y[11]),
        ("Dynamic + no IBP", sol_D.t, err_D_no_ibp, sol_D.y[12]),
    ]:
        final_val = val_arr[-1]
        final_err = err_arr[-1]
        # Fit rate
        mask = (err_arr > 1e-12) & (t_arr > 3) & (t_arr < T_MAX - 2)
        if mask.sum() > 10:
            coeffs = np.polyfit(t_arr[mask], np.log(np.maximum(err_arr[mask], 1e-16)), 1)
            alpha = -coeffs[0]
            floor = "FIRST" if alpha > 0.3 else "NOT first"
        else:
            alpha = float('nan')
            floor = "N/A"
        print(f"{label:30s}: val={final_val:.10f}  err={final_err:.2e}  α={alpha:.4f}  → {floor} floor")


if __name__ == '__main__':
    run()
