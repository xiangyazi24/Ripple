"""Experiment 09: Conway's constant via degree-71 polynomial.

y' = -q(y), q = Conway's look-and-say minimum polynomial (degree 71).
λ ≈ 1.3036 is the unique positive real root.

Tests whether k* stays finite for this high-degree system, and whether
it matches the on-trajectory production prediction M₀ = p̂⁺(λ, 0).
"""
from __future__ import annotations

import os
import numpy as np
from math import comb
from scipy.integrate import solve_ivp
from scipy.optimize import brentq
import matplotlib.pyplot as plt

HERE = os.path.dirname(os.path.abspath(__file__))

# Conway polynomial coefficients: CONWAY[k] = coefficient of x^k, k=0..71
CONWAY = [-6, 3, -6, 12, -4, 7, -7, 1, 0, 5, -2, -4, -12, 2, 7, 12,
          -7, -10, -4, 3, 9, -7, 0, -8, 14, -3, 9, 2, -3, -10, -2, -6,
          1, 10, -3, 1, 7, -7, 7, -12, -5, 8, 6, 10, -8, -8, -7, -3,
          9, 1, 6, 6, -2, -3, -10, -2, 3, 5, 2, -1, -1, -1, -1, -1,
          1, 2, 2, -1, -2, -1, 0, 1]
DEG = 71
assert len(CONWAY) == DEG + 1


def q_eval(y):
    r = 0.0
    for c in reversed(CONWAY):
        r = r * y + c
    return r


def q_prime_eval(y):
    r = 0.0
    for k in reversed(range(1, DEG + 1)):
        r = r * y + k * CONWAY[k]
    return r


# Find λ: unique real root of q in [1.0, 2.0]
LAM = brentq(q_eval, 1.0, 2.0)
QPRIME_LAM = q_prime_eval(LAM)
print(f"λ = {LAM:.15f}, q'(λ) = {QPRIME_LAM:.6e}", flush=True)

# Choose sign for y' = SIGN * q(y) so that λ is stable.
SIGN = -1 if QPRIME_LAM > 0 else +1
print(f"Using y' = {SIGN} * q(y) so λ is stable.", flush=True)

# Build monomial list for RHS = SIGN * q(y) = SIGN * sum_k CONWAY[k] y^k.
# Substitute y = u - v.
plus_terms = []
minus_terms = []

for k in range(DEG + 1):
    rk = SIGN * CONWAY[k]
    if rk == 0:
        continue
    sign_rk = 1 if rk > 0 else -1
    abs_rk = abs(rk)
    for j in range(k + 1):
        mono_sign = sign_rk * ((-1) ** j)
        coef = float(abs_rk) * float(comb(k, j))
        term = (k - j, j, coef)
        if mono_sign > 0:
            plus_terms.append(term)
        else:
            minus_terms.append(term)

print(f"Num positive monomials in p̂⁺: {len(plus_terms)}", flush=True)
print(f"Num negative monomials in p̂⁻: {len(minus_terms)}", flush=True)

# Vectorize the rail evaluation: store (exp_u, exp_v, coef) as numpy arrays
PLUS_EU = np.array([t[0] for t in plus_terms], dtype=np.int64)
PLUS_EV = np.array([t[1] for t in plus_terms], dtype=np.int64)
PLUS_C = np.array([t[2] for t in plus_terms], dtype=np.float64)
MINUS_EU = np.array([t[0] for t in minus_terms], dtype=np.int64)
MINUS_EV = np.array([t[1] for t in minus_terms], dtype=np.int64)
MINUS_C = np.array([t[2] for t in minus_terms], dtype=np.float64)


def eval_rails(u, v):
    up = np.ones(DEG + 1)
    vp = np.ones(DEG + 1)
    for i in range(1, DEG + 1):
        up[i] = up[i - 1] * u
        vp[i] = vp[i - 1] * v
    pp = float(np.sum(PLUS_C * up[PLUS_EU] * vp[PLUS_EV]))
    pm = float(np.sum(MINUS_C * up[MINUS_EU] * vp[MINUS_EV]))
    return pp, pm


def original_rhs(_t, state):
    (y,) = state
    return [SIGN * q_eval(y)]


def dualrail_rhs(k):
    def rhs(_t, state):
        u, v = state
        if not (np.isfinite(u) and np.isfinite(v)):
            return [0.0, 0.0]
        pp, pm = eval_rails(u, v)
        ann = k * u * v
        return [pp - ann, pm - ann]
    return rhs


# Report M₀ = p̂⁺(λ, 0) = p̂⁻(λ, 0): on-trajectory production at fixed point.
pp_lam, pm_lam = eval_rails(LAM, 0.0)
print(f"p̂⁺(λ, 0) = {pp_lam:.4e}", flush=True)
print(f"p̂⁻(λ, 0) = {pm_lam:.4e}", flush=True)


def simulate():
    T = 5.0
    t_eval = np.linspace(0.0, T, 1000)

    # Original trajectory
    print("Solving original trajectory...", flush=True)
    try:
        sol_orig = solve_ivp(
            original_rhs, (0.0, T), [0.0], t_eval=t_eval,
            rtol=1e-8, atol=1e-10, method="LSODA", max_step=0.01,
        )
        print(f"  orig done, success={sol_orig.success}, final y={sol_orig.y[0][-1]:.6f}", flush=True)
    except Exception as e:
        print(f"  orig failed: {e}", flush=True)
        sol_orig = None

    if sol_orig is not None and sol_orig.success:
        fig, ax = plt.subplots(figsize=(8, 4))
        ax.plot(sol_orig.t, sol_orig.y[0], label="y")
        ax.axhline(LAM, color="gray", linestyle="--", alpha=0.5,
                   label=f"λ = {LAM:.6f}")
        ax.set_xlabel("t")
        ax.set_title("Conway constant: y' = -q(y), y(0) = 0")
        ax.legend()
        fig.tight_layout()
        fig.savefig(os.path.join(HERE, "original.png"), dpi=120)
        plt.close(fig)

    # k sweep: span around M₀ — reduced range and fewer points
    M0 = max(pp_lam, pm_lam)
    k_lo = M0 * 0.1   # 3.6e7
    k_hi = M0 * 1000  # 3.6e11
    print(f"M₀ = {M0:.4e}; sweeping k over [{k_lo:.2e}, {k_hi:.2e}]", flush=True)
    ks = np.logspace(np.log10(k_lo), np.log10(k_hi), 10)

    results = []
    for idx, k in enumerate(ks):
        print(f"[{idx+1}/{len(ks)}] about to run k={k:.4e} (k/M0={k/M0:.2e})", flush=True)
        try:
            sol = solve_ivp(
                dualrail_rhs(k), (0.0, T), [0.0, 0.0], t_eval=t_eval,
                rtol=1e-6, atol=1e-8, method="LSODA", max_step=0.01,
            )
            u, v = sol.y
            row = dict(
                k=float(k),
                k_over_M0=float(k / M0),
                success=bool(sol.success),
                status=int(sol.status),
                message=str(sol.message),
                max_u=float(np.nanmax(u)) if u.size else float("nan"),
                max_v=float(np.nanmax(v)) if v.size else float("nan"),
                final_u=float(u[-1]) if u.size and np.isfinite(u[-1]) else float("nan"),
                final_v=float(v[-1]) if v.size and np.isfinite(v[-1]) else float("nan"),
                final_t=float(sol.t[-1]) if sol.t.size else 0.0,
                all_finite=bool(np.all(np.isfinite(sol.y))),
            )
        except Exception as e:
            row = dict(k=float(k), k_over_M0=float(k / M0),
                       error=str(e), all_finite=False, success=False)
        results.append(row)
        print(f"  result: {row}", flush=True)

    # Representative plots at several k values
    for k_rel, tag in [(1.0, "M0"), (10.0, "10M0"), (100.0, "100M0")]:
        k = M0 * k_rel
        print(f"Representative plot at k={tag} ({k:.3e})...", flush=True)
        try:
            sol = solve_ivp(
                dualrail_rhs(k), (0.0, T), [0.0, 0.0], t_eval=t_eval,
                rtol=1e-8, atol=1e-10, method="LSODA", max_step=0.01,
            )
            if sol.success:
                fig, ax = plt.subplots(figsize=(8, 4))
                ax.plot(sol.t, sol.y[0], label="u")
                ax.plot(sol.t, sol.y[1], label="v")
                ax.plot(sol.t, sol.y[0] - sol.y[1], "--", label="u - v")
                if sol_orig is not None and sol_orig.success:
                    ax.plot(sol_orig.t, sol_orig.y[0], ":", alpha=0.6, label="y (orig)")
                ax.axhline(LAM, color="gray", linestyle=":", alpha=0.5)
                ax.set_xlabel("t")
                ax.set_title(f"Conway: k = {k:.3e} ({tag}), M₀ = {M0:.3e}")
                ax.legend()
                fig.tight_layout()
                fig.savefig(os.path.join(HERE, f"dualrail_k={tag}.png"), dpi=120)
                plt.close(fig)
            else:
                print(f"  solver failed at k={tag}: {sol.message}", flush=True)
        except Exception as e:
            print(f"Plot k={tag} failed: {e}", flush=True)

    # Summary plots
    finite_res = [r for r in results if r.get("all_finite", False)]
    if finite_res:
        ks_fin = np.array([r["k"] for r in finite_res])
        peaks = np.array([max(r["max_u"], r["max_v"]) for r in finite_res])
        vfinals = np.array([abs(r["final_v"]) for r in finite_res])

        fig, axes = plt.subplots(1, 2, figsize=(12, 5))
        axes[0].loglog(ks_fin / M0, peaks, "o-", label="peak max(u,v)")
        axes[0].axhline(LAM, color="gray", linestyle=":", label=f"λ = {LAM:.4f}")
        axes[0].set_xlabel("k / M₀")
        axes[0].set_ylabel("peak")
        axes[0].set_title("Conway dual-rail: peak amplitude")
        axes[0].legend()

        axes[1].loglog(ks_fin / M0, vfinals, "o-", label="|v_final|")
        ka = np.logspace(-1, 4, 50)
        axes[1].loglog(ka, M0 / (ka * M0 * LAM), "k--", alpha=0.5,
                       label="pred M₀/(k·λ)")
        axes[1].set_xlabel("k / M₀")
        axes[1].set_ylabel("|v| at t = T")
        axes[1].set_title("Steady-state v")
        axes[1].legend()

        fig.tight_layout()
        fig.savefig(os.path.join(HERE, "k_sweep.png"), dpi=120)
        plt.close(fig)

    with open(os.path.join(HERE, "summary.txt"), "w") as f:
        f.write(f"λ = {LAM}\n")
        f.write(f"q'(λ) = {QPRIME_LAM}\n")
        f.write(f"SIGN = {SIGN}\n")
        f.write(f"p̂⁺(λ, 0) = {pp_lam}\n")
        f.write(f"p̂⁻(λ, 0) = {pm_lam}\n")
        f.write(f"M₀ = {M0}\n")
        f.write(f"num plus_terms = {len(plus_terms)}\n")
        f.write(f"num minus_terms = {len(minus_terms)}\n")
        f.write(f"T = {T}\n")
        for r in results:
            f.write(str(r) + "\n")
    print("Summary written.", flush=True)


if __name__ == "__main__":
    simulate()
