"""Experiment 08: y' = ε + A*y^2 - A*y^3. Test k*(A) = Θ(A) via monomial size."""
from __future__ import annotations

import os
import numpy as np
from scipy.integrate import solve_ivp
import matplotlib.pyplot as plt

HERE = os.path.dirname(os.path.abspath(__file__))

EPS = 0.001


def original_rhs(A):
    def rhs(_t, y):
        return [EPS + A * y[0] ** 2 - A * y[0] ** 3]
    return rhs


def dualrail_rhs(k, A):
    """p = ε + A y² − A y³.
    +A y²: +A u² + A v², 2A uv (abs to neg)
    -A y³: +3A u²v + A v³, A u³ + 3A u v² (to neg)
    """
    def rhs(_t, state):
        u, v = state
        pplus = EPS + A * u * u + A * v * v + 3.0 * A * u * u * v + A * v ** 3
        pminus = 2.0 * A * u * v + A * u ** 3 + 3.0 * A * u * v * v
        ann = k * u * v
        return [pplus - ann, pminus - ann]
    return rhs


def simulate():
    As = [1.0, 10.0, 100.0, 1000.0]

    all_results = []
    for A in As:
        # Time to reach near-1: dominated by y² growth when y small; y ≈ 1 on T ~ 1/A plus some.
        T = max(10.0 / A, 5.0)
        t_eval = np.linspace(0.0, T, 4000)
        sol_orig = solve_ivp(
            original_rhs(A), (0.0, T), [0.0], t_eval=t_eval,
            rtol=1e-10, atol=1e-12,
        )
        # orig plot
        fig, ax = plt.subplots(figsize=(8, 4))
        ax.plot(sol_orig.t, sol_orig.y[0], label="y")
        ax.axhline(1.0, color="gray", linestyle="--", alpha=0.5)
        ax.set_xlabel("t")
        ax.set_title(f"Original, A = {A}, ε = {EPS}")
        ax.legend()
        fig.tight_layout()
        fig.savefig(os.path.join(HERE, f"original_A={A}.png"), dpi=120)
        plt.close(fig)

        ks = np.logspace(np.log10(0.1 * A), np.log10(1e4 * A), 15)
        for k in ks:
            sol = solve_ivp(
                dualrail_rhs(k, A), (0.0, T), [0.0, 0.0], t_eval=t_eval,
                rtol=1e-8, atol=1e-10, method="LSODA",
            )
            u, v = sol.y
            row = dict(
                A=A, k=float(k),
                max_u=float(np.nanmax(u)),
                max_v=float(np.nanmax(v)),
                final_v=float(v[-1]) if np.isfinite(v[-1]) else float("nan"),
                all_finite=bool(np.all(np.isfinite(sol.y))),
            )
            all_results.append(row)
            print(row)

        # representative plots
        for k_rel, tag in [(1.0, "k=A"), (10.0, "k=10A"), (100.0, "k=100A")]:
            k = k_rel * A
            sol = solve_ivp(
                dualrail_rhs(k, A), (0.0, T), [0.0, 0.0], t_eval=t_eval,
                rtol=1e-9, atol=1e-11, method="LSODA",
            )
            fig, ax = plt.subplots(figsize=(8, 4))
            ax.plot(sol.t, sol.y[0], label="u")
            ax.plot(sol.t, sol.y[1], label="v")
            ax.plot(sol.t, sol.y[0] - sol.y[1], "--", label="u - v")
            ax.plot(sol_orig.t, sol_orig.y[0], ":", label="y (orig)")
            ax.set_xlabel("t")
            ax.set_title(f"A = {A}, k = {k} ({tag}): v_ss pred = A/k = {A/k:.4g}")
            ax.legend()
            fig.tight_layout()
            fig.savefig(os.path.join(HERE, f"dualrail_A={A}_{tag}.png"), dpi=120)
            plt.close(fig)

    # k/A collapse
    fig, ax = plt.subplots(figsize=(8, 5))
    for A in As:
        rows = [r for r in all_results if r["A"] == A]
        ks = np.array([r["k"] for r in rows])
        peaks = np.array([max(r["max_u"], r["max_v"]) for r in rows])
        finals_v = np.array([abs(r["final_v"]) if np.isfinite(r["final_v"]) else np.nan for r in rows])
        ax.loglog(ks / A, peaks, "o-", label=f"A = {A} (peak)")
    # theoretical curve: v_ss = A/k = 1/(k/A)
    ka_arr = np.logspace(-1, 4, 100)
    ax.loglog(ka_arr, 1.0 + 1.0 / ka_arr, "k--", alpha=0.5, label="pred 1 + A/k")
    ax.set_xlabel("k / A (rescaled)")
    ax.set_ylabel("peak max(u, v)")
    ax.set_title("Large-production cubic: k* = Θ(A) expected")
    ax.legend()
    fig.tight_layout()
    fig.savefig(os.path.join(HERE, "k_over_A_collapse.png"), dpi=120)
    plt.close(fig)

    # v_ss vs k/A plot
    fig, ax = plt.subplots(figsize=(8, 5))
    for A in As:
        rows = [r for r in all_results if r["A"] == A]
        ks = np.array([r["k"] for r in rows])
        fvs = np.array([abs(r["final_v"]) if np.isfinite(r["final_v"]) else np.nan for r in rows])
        mask = np.isfinite(fvs) & (fvs > 1e-15)
        if mask.sum() > 0:
            ax.loglog(ks[mask] / A, fvs[mask], "o-", label=f"A = {A}")
    ka_arr = np.logspace(0, 4, 50)
    ax.loglog(ka_arr, 1.0 / ka_arr, "k--", alpha=0.5, label="1 / (k/A) pred")
    ax.set_xlabel("k / A")
    ax.set_ylabel("|v| at t = T (final)")
    ax.set_title("Steady-state v vs k/A")
    ax.legend()
    fig.tight_layout()
    fig.savefig(os.path.join(HERE, "v_ss_vs_kA.png"), dpi=120)
    plt.close(fig)

    with open(os.path.join(HERE, "summary.txt"), "w") as f:
        for r in all_results:
            f.write(str(r) + "\n")


if __name__ == "__main__":
    simulate()
