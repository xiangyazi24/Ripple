"""Experiment 07: Bournez-Pouly-style cascade, internal rate λ.

z' = 1 - z,       z(0) = 0
w' = z - w,       w(0) = 0
y' = λ(w² - y²),  y(0) = 0

All amplitudes in [0, 1]. Internal coefficient λ.
Test whether k*(λ) = Θ(λ).
"""
from __future__ import annotations

import os
import numpy as np
from scipy.integrate import solve_ivp
import matplotlib.pyplot as plt

HERE = os.path.dirname(os.path.abspath(__file__))


def original_rhs(lam):
    def rhs(_t, state):
        z, w, y = state
        return [1.0 - z, z - w, lam * (w * w - y * y)]
    return rhs


def dualrail_rhs(k, lam):
    def rhs(_t, state):
        u1, v1, u2, v2, u3, v3 = state
        p1p = 1.0 + v1
        p1n = u1
        p2p = u1 + v2
        p2n = v1 + u2
        p3p = lam * (u2 * u2 + v2 * v2) + 2.0 * lam * u3 * v3
        p3n = 2.0 * lam * u2 * v2 + lam * (u3 * u3 + v3 * v3)
        a1 = k * u1 * v1
        a2 = k * u2 * v2
        a3 = k * u3 * v3
        return [p1p - a1, p1n - a1, p2p - a2, p2n - a2, p3p - a3, p3n - a3]
    return rhs


def simulate():
    lams = [1.0, 10.0, 100.0, 1000.0]
    T = 15.0

    all_results = []
    for lam in lams:
        t_eval = np.linspace(0.0, T, 4000)
        sol_orig = solve_ivp(
            original_rhs(lam), (0.0, T), [0.0, 0.0, 0.0], t_eval=t_eval,
            rtol=1e-10, atol=1e-12,
        )
        # plot original
        fig, ax = plt.subplots(figsize=(8, 4))
        ax.plot(sol_orig.t, sol_orig.y[0], label="z")
        ax.plot(sol_orig.t, sol_orig.y[1], label="w")
        ax.plot(sol_orig.t, sol_orig.y[2], label="y")
        ax.set_xlabel("t")
        ax.set_ylabel("species")
        ax.set_title(f"Original cascade, λ = {lam}")
        ax.legend()
        fig.tight_layout()
        fig.savefig(os.path.join(HERE, f"original_lam={lam}.png"), dpi=120)
        plt.close(fig)

        # k sweep: test k from 0.1*lam to 10000*lam
        ks = np.logspace(np.log10(0.1 * lam), np.log10(1e4 * lam), 15)
        for k in ks:
            sol = solve_ivp(
                dualrail_rhs(k, lam), (0.0, T), [0.0]*6, t_eval=t_eval,
                rtol=1e-8, atol=1e-10, method="LSODA",
            )
            u1, v1, u2, v2, u3, v3 = sol.y
            row = dict(
                lam=lam, k=float(k),
                max_u1=float(np.nanmax(u1)), max_v1=float(np.nanmax(v1)),
                max_u2=float(np.nanmax(u2)), max_v2=float(np.nanmax(v2)),
                max_u3=float(np.nanmax(u3)), max_v3=float(np.nanmax(v3)),
                all_finite=bool(np.all(np.isfinite(sol.y))),
            )
            all_results.append(row)
            print(row)

        # representative plots: k = lam (insufficient?), k = 10*lam (sufficient?)
        for k_rel, tag in [(1.0, "k=lam"), (10.0, "k=10lam")]:
            k = k_rel * lam
            sol = solve_ivp(
                dualrail_rhs(k, lam), (0.0, T), [0.0]*6, t_eval=t_eval,
                rtol=1e-9, atol=1e-11, method="LSODA",
            )
            fig, axes = plt.subplots(3, 1, figsize=(10, 8), sharex=True)
            labels = ["z", "w", "y"]
            u1, v1, u2, v2, u3, v3 = sol.y
            for i, (u, v) in enumerate([(u1, v1), (u2, v2), (u3, v3)]):
                axes[i].plot(sol.t, u, label=f"u_{labels[i]}")
                axes[i].plot(sol.t, v, label=f"v_{labels[i]}")
                axes[i].plot(sol.t, u - v, "--", alpha=0.5, label="u - v")
                axes[i].plot(sol_orig.t, sol_orig.y[i], ":", alpha=0.7,
                             label=f"{labels[i]} orig")
                axes[i].set_ylabel(labels[i])
                axes[i].legend(loc="upper right", fontsize=7)
            axes[0].set_title(f"BP cascade, λ={lam}, k={k} ({tag})")
            axes[-1].set_xlabel("t")
            fig.tight_layout()
            fig.savefig(os.path.join(HERE, f"dualrail_lam={lam}_{tag}.png"), dpi=120)
            plt.close(fig)

    # k_threshold plot: peak vs k/lam
    fig, ax = plt.subplots(figsize=(8, 5))
    for lam in lams:
        rows = [r for r in all_results if r["lam"] == lam]
        ks = np.array([r["k"] for r in rows])
        peaks = np.array(
            [max(r["max_u1"], r["max_v1"], r["max_u2"], r["max_v2"],
                 r["max_u3"], r["max_v3"]) for r in rows]
        )
        ax.loglog(ks / lam, peaks, "o-", label=f"λ = {lam}")
    ax.axhline(1.5, color="gray", linestyle="--", alpha=0.5,
               label="amplitude ~1")
    ax.set_xlabel("k / λ (rescaled)")
    ax.set_ylabel("max peak of all u, v")
    ax.set_title("BP cascade: does k* scale linearly with internal λ?")
    ax.legend()
    fig.tight_layout()
    fig.savefig(os.path.join(HERE, "k_over_lam_collapse.png"), dpi=120)
    plt.close(fig)

    with open(os.path.join(HERE, "summary.txt"), "w") as f:
        for r in all_results:
            f.write(str(r) + "\n")


if __name__ == "__main__":
    simulate()
