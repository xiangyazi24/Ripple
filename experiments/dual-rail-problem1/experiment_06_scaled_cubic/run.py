"""Experiment 06: scaled scalar cubic y' = C - C*y^3, test k*(C) = C * k*(1)."""
from __future__ import annotations

import os
import numpy as np
from scipy.integrate import solve_ivp
import matplotlib.pyplot as plt

HERE = os.path.dirname(os.path.abspath(__file__))


def original_rhs(C):
    def rhs(_t, y):
        return [C * (1.0 - y[0] ** 3)]
    return rhs


def dualrail_rhs(k, C):
    def rhs(_t, state):
        u, v = state
        u_dot = C + 3.0 * C * u * u * v + C * v ** 3 - k * u * v
        v_dot = C * u ** 3 + 3.0 * C * u * v * v - k * u * v
        return [u_dot, v_dot]
    return rhs


def simulate():
    Cs = [1.0, 10.0, 100.0, 1000.0]
    T_scale = 10.0  # T = T_scale / C, same "τ-time" for all C

    # For each C, test k spanning 0.1*k_expected to 10*k_expected
    # where k_expected = 10*C
    all_results = []
    for C in Cs:
        T = T_scale / C
        t_eval = np.linspace(0.0, T, 4000)

        sol_orig = solve_ivp(
            original_rhs(C), (0.0, T), [0.0], t_eval=t_eval,
            rtol=1e-10, atol=1e-12,
        )

        ks_this = np.logspace(np.log10(0.1 * C), np.log10(1e4 * C), 15)
        rows = []
        for k in ks_this:
            sol = solve_ivp(
                dualrail_rhs(k, C), (0.0, T), [0.0, 0.0], t_eval=t_eval,
                rtol=1e-8, atol=1e-10, method="LSODA",
            )
            u, v = sol.y
            row = dict(
                C=C, k=float(k),
                max_u=float(np.nanmax(u)),
                max_v=float(np.nanmax(v)),
                all_finite=bool(np.all(np.isfinite(sol.y))),
            )
            rows.append(row)
            print(row)
        all_results.extend(rows)

        # Plot trajectories at k_expected = 10*C (sufficient) and k = C (insufficient)
        for k, tag in [(10.0 * C, "sufficient"), (C, "insufficient")]:
            sol = solve_ivp(
                dualrail_rhs(k, C), (0.0, T), [0.0, 0.0], t_eval=t_eval,
                rtol=1e-9, atol=1e-11, method="LSODA",
            )
            fig, ax = plt.subplots(figsize=(8, 4))
            ax.plot(sol.t, sol.y[0], label="u")
            ax.plot(sol.t, sol.y[1], label="v")
            ax.plot(sol.t, sol.y[0] - sol.y[1], "--", label="u - v")
            ax.plot(sol_orig.t, sol_orig.y[0], ":", label="y (orig)")
            ax.set_xlabel("t")
            ax.set_title(f"Scaled cubic C={C}, k={k:.1f} ({tag})")
            ax.legend()
            fig.tight_layout()
            fig.savefig(os.path.join(HERE, f"dualrail_C={C}_k={k:.1f}_{tag}.png"), dpi=120)
            plt.close(fig)

    # k_threshold plot: peak vs k, rescaled by C
    fig, ax = plt.subplots(figsize=(8, 5))
    for C in Cs:
        rows = [r for r in all_results if r["C"] == C]
        ks = np.array([r["k"] for r in rows])
        peak = np.array([max(r["max_u"], r["max_v"]) for r in rows])
        # plot on rescaled axis: k/C
        ax.loglog(ks / C, peak, "o-", label=f"C = {C}")
    ax.set_xlabel("k / C  (rescaled)")
    ax.set_ylabel("max peak of u, v")
    ax.axhline(1.5, color="gray", linestyle="--", alpha=0.5, label="y max ~1")
    ax.set_title("Scaled cubic: do curves collapse under k ← k/C?")
    ax.legend()
    fig.tight_layout()
    fig.savefig(os.path.join(HERE, "k_over_C_collapse.png"), dpi=120)
    plt.close(fig)

    with open(os.path.join(HERE, "summary.txt"), "w") as f:
        for r in all_results:
            f.write(str(r) + "\n")


if __name__ == "__main__":
    simulate()
