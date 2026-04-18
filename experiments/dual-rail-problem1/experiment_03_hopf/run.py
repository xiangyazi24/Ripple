"""Experiment 03: Hopf normal form (biased) dual-rail constant-k test.

x1' = x1 - x1*r^2 - omega*x2 + c
x2' = x2 - x2*r^2 + omega*x1
r^2 = x1^2 + x2^2
"""
from __future__ import annotations

import os
import numpy as np
from scipy.integrate import solve_ivp
import matplotlib.pyplot as plt

HERE = os.path.dirname(os.path.abspath(__file__))

C_BIAS = 0.05  # small bias to kick off zero-init limit cycle


def original_rhs(omega):
    def rhs(_t, y):
        x1, x2 = y
        r2 = x1 * x1 + x2 * x2
        return [x1 - x1 * r2 - omega * x2 + C_BIAS, x2 - x2 * r2 + omega * x1]

    return rhs


def dualrail_rhs(k, omega):
    """Split p_1, p_2 monomial-wise by sign.

    p1 = x1 - x1*x1^2 - x1*x2^2 - omega*x2 + c
    p2 = x2 - x2*x1^2 - x2*x2^2 + omega*x1

    Let x_i = u_i - v_i. Expand each cubic and collect by sign.
    """

    def rhs(_t, state):
        u1, v1, u2, v2 = state

        # -x1*x1^2 = -(u1-v1)^3 = -u1^3 + 3u1^2 v1 - 3u1 v1^2 + v1^3
        # pos: 3u1^2 v1, v1^3    neg: u1^3, 3u1 v1^2
        # -x1*x2^2 = -(u1-v1)(u2-v2)^2
        # (u2-v2)^2 = u2^2 - 2u2 v2 + v2^2
        # -(u1-v1)*... = -u1 u2^2 + 2 u1 u2 v2 - u1 v2^2
        #                + v1 u2^2 - 2 v1 u2 v2 + v1 v2^2
        # pos: 2 u1 u2 v2, v1 u2^2, v1 v2^2
        # neg: u1 u2^2, u1 v2^2, 2 v1 u2 v2
        # -omega*x2 = -omega*(u2-v2) = -omega u2 + omega v2
        # pos: omega v2,  neg: omega u2
        # +c, +u1 (from +x1 pos), -v1 in neg
        p1p = (
            u1
            + 3.0 * u1 * u1 * v1 + v1 ** 3
            + 2.0 * u1 * u2 * v2 + v1 * u2 * u2 + v1 * v2 * v2
            + omega * v2
            + C_BIAS
        )
        p1n = (
            v1
            + u1 ** 3 + 3.0 * u1 * v1 * v1
            + u1 * u2 * u2 + u1 * v2 * v2 + 2.0 * v1 * u2 * v2
            + omega * u2
        )

        # p2 = x2 - x2*x1^2 - x2*x2^2 + omega*x1
        # -x2*x1^2 = -(u2-v2)(u1-v1)^2 (by symmetry swap indices in the above)
        # -x2*x2^2 = same cube expansion for species 2
        # +omega*x1 = +omega*u1 - omega*v1  -> pos: omega u1, neg: omega v1
        p2p = (
            u2
            + 3.0 * u2 * u2 * v2 + v2 ** 3
            + 2.0 * u2 * u1 * v1 + v2 * u1 * u1 + v2 * v1 * v1
            + omega * u1
        )
        p2n = (
            v2
            + u2 ** 3 + 3.0 * u2 * v2 * v2
            + u2 * u1 * u1 + u2 * v1 * v1 + 2.0 * v2 * u1 * v1
            + omega * v1
        )

        ann1 = k * u1 * v1
        ann2 = k * u2 * v2
        return [p1p - ann1, p1n - ann1, p2p - ann2, p2n - ann2]

    return rhs


def run_one(omega, T, ks):
    t_eval = np.linspace(0.0, T, 8000)
    sol_orig = solve_ivp(
        original_rhs(omega),
        (0.0, T),
        [0.0, 0.0],
        t_eval=t_eval,
        rtol=1e-10,
        atol=1e-12,
        method="LSODA",
    )
    sols = {}
    for k in ks:
        sols[k] = solve_ivp(
            dualrail_rhs(k, omega),
            (0.0, T),
            [0.0, 0.0, 0.0, 0.0],
            t_eval=t_eval,
            rtol=1e-10,
            atol=1e-12,
            method="LSODA",
        )
    return sol_orig, sols


def plot_original(sol_orig, omega, fname):
    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(12, 4))
    ax1.plot(sol_orig.t, sol_orig.y[0], label="x1")
    ax1.plot(sol_orig.t, sol_orig.y[1], label="x2")
    ax1.set_xlabel("t")
    ax1.set_title(f"Original Hopf, omega = {omega}")
    ax1.legend()
    ax2.plot(sol_orig.y[0], sol_orig.y[1])
    ax2.set_xlabel("x1")
    ax2.set_ylabel("x2")
    ax2.set_title("Phase portrait")
    ax2.set_aspect("equal")
    fig.tight_layout()
    fig.savefig(fname, dpi=120)
    plt.close(fig)


def plot_dualrail(sol_orig, sol_dr, k, omega, fname):
    fig, axes = plt.subplots(2, 1, figsize=(10, 6), sharex=True)
    u1, v1, u2, v2 = sol_dr.y
    axes[0].plot(sol_dr.t, u1, label="u1")
    axes[0].plot(sol_dr.t, v1, label="v1")
    axes[0].plot(sol_dr.t, u1 - v1, "--", alpha=0.5, label="u1 - v1")
    axes[0].plot(sol_orig.t, sol_orig.y[0], ":", alpha=0.7, label="x1 (orig)")
    axes[0].set_ylabel("species 1")
    axes[0].legend(loc="upper right")
    axes[0].set_title(f"Hopf dual-rail, omega = {omega}, k = {k}")
    axes[1].plot(sol_dr.t, u2, label="u2")
    axes[1].plot(sol_dr.t, v2, label="v2")
    axes[1].plot(sol_dr.t, u2 - v2, "--", alpha=0.5, label="u2 - v2")
    axes[1].plot(sol_orig.t, sol_orig.y[1], ":", alpha=0.7, label="x2 (orig)")
    axes[1].set_xlabel("t")
    axes[1].set_ylabel("species 2")
    axes[1].legend(loc="upper right")
    fig.tight_layout()
    fig.savefig(fname, dpi=120)
    plt.close(fig)


def simulate():
    omegas = [1.0, 5.0, 20.0, 100.0]
    ks = [0.1, 1.0, 10.0, 100.0, 1000.0, 10000.0]

    summary = []
    for omega in omegas:
        # enough cycles to see steady state: T ~ 10 periods = 10 * 2pi / omega,
        # but min 20 s for small omega to let bias kick in
        T = max(20.0, 20.0 * 2.0 * np.pi / omega)
        sol_orig, sols = run_one(omega, T, ks)
        plot_original(
            sol_orig, omega, os.path.join(HERE, f"original_omega={omega}.png")
        )
        for k, sol in sols.items():
            plot_dualrail(
                sol_orig, sol, k, omega,
                os.path.join(HERE, f"dualrail_omega={omega}_k={k}.png"),
            )
            u1, v1, u2, v2 = sol.y
            row = dict(
                omega=omega,
                k=k,
                max_u1=float(np.nanmax(u1)),
                max_v1=float(np.nanmax(v1)),
                max_u2=float(np.nanmax(u2)),
                max_v2=float(np.nanmax(v2)),
                max_r_orig=float(np.nanmax(np.sqrt(sol_orig.y[0]**2 + sol_orig.y[1]**2))),
                T=T,
                all_finite=bool(np.all(np.isfinite(sol.y))),
            )
            summary.append(row)
            print(row)

    # k-threshold plot: for each omega, minimum k that keeps peaks ≲ 2
    fig, ax = plt.subplots(figsize=(8, 4))
    for omega in omegas:
        rows = [r for r in summary if r["omega"] == omega]
        ks_arr = np.array([r["k"] for r in rows])
        peaks = np.array(
            [max(r["max_u1"], r["max_v1"], r["max_u2"], r["max_v2"]) for r in rows]
        )
        ax.loglog(ks_arr, peaks, "o-", label=f"ω = {omega}")
    ax.axhline(2.0, color="gray", linestyle="--", alpha=0.5, label="cycle amplitude ≈ 1 × 2")
    ax.set_xlabel("k")
    ax.set_ylabel("max peak across all u, v species")
    ax.set_title("Peak vs k at various ω")
    ax.legend()
    fig.tight_layout()
    fig.savefig(os.path.join(HERE, "k_threshold.png"), dpi=120)
    plt.close(fig)

    with open(os.path.join(HERE, "summary.txt"), "w") as f:
        for row in summary:
            f.write(str(row) + "\n")


if __name__ == "__main__":
    simulate()
