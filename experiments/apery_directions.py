"""
Two directions for ζ(3) first-floor proof.

Direction (a): Find a formulation with only rational ODE coefficients.
Direction (b): Use tracking filters to compose the cascade.

Key insight for Direction (b):
The cascade S₂' = ln(2) - S₁ is a pure integrator.
But we can REFORMULATE it. Note that:

S₂(t) = ∫₀^t (ln(2) - S₁(s)) ds = ∫₀^t ln(1+e^{-s}) ds

Define W₂(t) as a TRACKING FILTER for S₂(∞) = η(2):
  W₂' = S₂'(t)·... hmm, we still need S₂.

DIFFERENT APPROACH for (b):
Instead of tracking S₂(∞), restructure the entire computation.

Key identity:
  η(3) = ∫₀^∞ ∫₀^∞ ∫₀^∞ [product] ... no.

Actually, η(3) = ∫₀^∞ (1/2) t² · u/(1+u) dt where u = e^{-t}.

Consider computing this in TWO STAGES using the RECIPROCAL TRICK from RTCRN2:

Stage 1: Compute some intermediate α via a bounded PIVP with rational coefficients.
Stage 2: Use field operations (add, mul, reciprocal) to get ζ(3) from α.

The field operations are all first-floor preserving (RTCRN2 Lemmas 5-8).

For the intermediate: we need α to be something "close to" ζ(3) that can be
computed with rational ODE coefficients.

---

Direction (b) - REVISED APPROACH:
Use the observation that the polylog cascade is a LINEAR ODE system
with CONSTANT coefficients (the η(k) values). Linear systems have the
property that perturbations die out exponentially for stable systems.

The cascade:
  S₁' = u/(1+u)         [nonlinear in u, but u is determined]
  S₂' = c₁ - S₁         [c₁ = ln(2)]
  S₃' = c₂ - S₂         [c₂ = π²/12]

If we replace c₁ with a dynamic C₁(t) → c₁ and c₂ with C₂(t) → c₂:
  S₂' = C₁(t) - S₁(t)
  S₃' = C₂(t) - S₂(t)

The issue is that S₂ and S₃ are INTEGRATORS (no damping term).
The error propagation for S₂:
  e₂(t) = S₂_dynamic(t) - S₂_exact(t)
  e₂'(t) = C₁(t) - c₁ = ε₁(t)
  e₂(t) = ∫₀^t ε₁(s) ds → ∫₀^∞ ε₁(s) ds = δ₁ ≠ 0

The BIAS δ₁ = ∫₀^∞ (C₁(s) - c₁) ds is finite but nonzero.

BUT: what if we ADD A CORRECTION TERM?

Define: S₂_corrected = S₂ + ∫₀^t (c₁ - C₁(s)) ds
Then S₂_corrected → S₂_exact(∞) as t → ∞.
But this requires knowing c₁ = ln(2) to compute the correction!

ALTERNATIVE: Use the "leaky integrator" formulation.
Instead of S₂' = C₁ - S₁, use:
  S₂' = C₁ - S₁ + λ·(Z₂ - S₂)

where Z₂ is a tracking filter for η(2) and λ is a small rate.
This adds self-correction. As t → ∞, S₂ → Z₂ → η(2).

But we need Z₂ → η(2), which requires knowing η(2) = π²/12!

---

Direction (b) - THIRD ATTEMPT:
Use the fact that we're computing η(3) = (3/4)ζ(3), and
then multiply by 4/3.

The polylog cascade computes η(n) recursively.
What if we REVERSE THE CASCADE?

Start from the BOTTOM: we know u/(1+u) = Li₀(-u) · u ... not helpful.

---

DIRECTION (a) - NEW IDEA:
The APÉRY SERIES:
ζ(3) = (5/2) Σ_{n=0}^∞ (-1)^n / ((2n+1)² · C(2n,n))
Wait, that's not right. The Apéry acceleration:

ζ(3) = (5/2) Σ_{n=1}^∞ (-1)^{n-1} / (n³ · C(2n,n))

This converges like (1/16)^n — EXTREMELY FAST.

Each term: a_n = (-1)^{n-1} / (n³ · C(2n,n))
where C(2n,n) = (2n)! / (n!)²

The ratio: a_{n+1}/a_n involves n/(n+1) type terms — rational!

If we can encode this series as an ODE where the "coefficient generator"
is a rational recurrence, we might get a rational-coefficient PIVP.

The generating function approach: define
  f(t) = Σ a_n · r^n where r = e^{-t}/16

Then ζ(3) = (5/2) · f(0) = (5/2) · Σ a_n

And f'(t) = Σ a_n · n · r^n · (-1/16)·e^{-t}... messy.

Better: define partial sums P_N = (5/2) Σ_{n=1}^N a_n
The tail |ζ(3) - P_N| ~ C · (1/16)^N

If N grows linearly with t (like a counter), the error decays as (1/16)^t,
which is EXPONENTIAL (rate ln(16) ≈ 2.77).

But implementing a COUNTER in a continuous ODE requires the iterated-log tower
from DNA32 Section 5 — that's O(e^t) time to count to t.

Unless we can avoid the counter and directly encode the recurrence.

The central binomial coefficient satisfies:
  C(2(n+1), n+1) / C(2n, n) = 4(2n+1)/(n+1)... let me compute:
  C(2n+2, n+1) = (2n+2)! / ((n+1)!)² = (2n+2)(2n+1)/(n+1)² · C(2n,n)
               = 2(2n+1)/(n+1) · C(2n,n)

So if b_n = 1/(n³ · C(2n,n)), then:
  b_{n+1}/b_n = n³/(n+1)³ · C(2n,n)/C(2n+2,n+1)
             = n³/(n+1)³ · (n+1)/(2(2n+1))
             = n³/((n+1)² · 2(2n+1))

This ratio → 1/4 as n → ∞. So the series converges like (1/4)^n.

Wait, actually the Apéry series converges like (1/√5 - 1/2)^{5} ≈ (1/16)^n?
Let me not worry about exact rate and just test numerically.

The key question: can we encode this recurrence as a continuous ODE?

Define variables tracking n, 1/n, C(2n,n) etc. as functions of continuous time.
This requires a "clock" variable whose behavior is like a counter.

In a bounded PIVP, a counter can be implemented via:
  v' = (1-v)², v(0) = 0 → v(t) = t/(1+t)

Then n ≈ t = v/(1-v). Each "step" of the recurrence happens continuously.

This is getting into serious ODE design territory. Let me test numerically.
"""

import numpy as np
from scipy.integrate import solve_ivp
from scipy.special import zeta, comb
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt

ZETA3 = float(zeta(3))
T_MAX = 40.0
T_EVAL = np.linspace(0, T_MAX, 8000)


# ================================================================
# Direction (b): Tracking filter cascade
#
# REVISED APPROACH: Instead of replacing constants, use the
# cascade structure but add CORRECTION via the low-pass property.
#
# The key insight from RTCRN2 Lemma 3:
# If x' = f(t) - x and f → α exponentially, then x → α exponentially.
#
# The cascade S₂' = c₁ - S₁ can be rewritten as:
# S₂' = (c₁ - S₁)
# Note c₁ - S₁(t) = ln(1+e^{-t}) → 0 exponentially.
# So S₂(t) converges because its derivative → 0.
#
# What if we reformulate using DIFFERENCES?
# Define D₁(t) = c₁ - S₁(t) = ln(1+e^{-t})     [→ 0 exponentially]
# Define D₂(t) = c₂ - S₂(t)                       [→ 0]
# Define D₃(t) = c₃ - S₃(t) where c₃ = η(3)      [→ 0]
#
# D₁' = -S₁' = -u/(1+u) = -(1 - D₁·something)... not clean.
#
# D₂' = -S₂' = -(c₁ - S₁) = -D₁
# D₃' = -S₃' = -(c₂ - S₂) = -D₂
#
# So D₁ = ln(1+e^{-t}), D₂ = Li₂(-e^{-t}), D₃ = -Li₃(-e^{-t})
# All → 0 exponentially. This is the backward polylog cascade.
#
# Now: η(3) = S₃(∞) = c₃. And S₃ = c₃ - D₃.
# S₃(t) = η(3) - D₃(t) = η(3) + Li₃(-e^{-t}).
#
# We want to compute S₃(t) → η(3) WITHOUT knowing η(3).
# S₃(t) = S₃(0) + ∫₀^t S₃'(s) ds = 0 + ∫₀^t (c₂ - S₂(s)) ds
#
# This always requires c₂. Going in circles.
#
# FUNDAMENTALLY: the polylog cascade is a TRIPLE INTEGRAL.
# η(3) = ∫₀^∞ ∫_s^∞ ∫_u^∞ h(v) dv du ds where h(v) = e^{-v}/(1+e^{-v})
#
# We can't avoid the nested structure.
#
# BUT: what if we compute η(3) DIRECTLY as a single integral?
# Using the identity:
# η(3) = (1/2) ∫₀^∞ t² · e^{-t}/(1+e^{-t}) dt
#
# The t² factor is the problem. But what if we use the DNA32
# bounded surrogate compilation on this specific integral?
#
# The compilation replaces t with bounded surrogates.
# From DNA32 Construction 3.1:
# U_{n,m}(t) = t^m / (1 + t^n) ∈ [0,1]
#
# Key surrogates:
# U_{1,1} = t/(1+t) = v       [already used]
# U_{2,1} = t/(1+t²)
# U_{2,2} = t²/(1+t²)
#
# So t² = U_{2,2}/(1-U_{2,2}) = U_{2,2}·(1+t²) ... circular.
# But t² = v²/(1-v)² where v = t/(1+t).
#
# The integrand: t²·u/(1+u) = v²·u / ((1-v)²·(1+u))
# This has 1/(1-v)² which is unbounded.
#
# The DNA32 compilation would introduce a time rescaling:
# dτ = (1-v)² dt (slow down as v→1)
#
# In rescaled time:
# dv/dτ = (1-v)²/(1-v)² = 1     [linear clock!]
# du/dτ = -u/(1-v)² = -u·(1+t)²  [problematic: (1+t)² unbounded]
#
# The surrogate for (1+t)² would be needed...
# This leads to an infinite chain of surrogates.
#
# ACTUALLY: the bounded compilation from DNA32 handles this!
# It introduces surrogates for ALL unbounded quantities.
# The dimension grows polynomially.
#
# The question is: does the compilation preserve FIRST-FLOOR complexity?
# From DNA32 Theorem 4.2: compilation preserves POLYNOMIAL time.
# So an O(r) (first floor) system stays O(r) after compilation.
#
# But WAIT: the starting system (before compilation) already IS first
# floor (we proved it numerically). The compilation would produce a
# bounded system with the SAME first-floor rate!
#
# The issue is that the STARTING system has t as a variable (unbounded),
# and the coefficients include transcendental constants.
# After compilation, t is replaced by surrogates, but the transcendental
# coefficients remain.
#
# We need: compilation that also eliminates transcendental coefficients.
# That's a stronger requirement than standard compilation.
# ================================================================


# ================================================================
# Direction (b) - WORKING APPROACH:
#
# Compute ln(2) and π²/12 via SEPARATE real-time CRN modules.
# Then pipe them into the cascade through Lemma 3 filters.
#
# For ln(2):
#   Standard: S₁ = ∫₀^t u/(1+u) ds → ln(2)
#   This IS a bounded PIVP with rational coefficients!
#   u' = -u, S₁' = u/(1+u). Coefficients: -1, 1, 1. ICs: u(0)=1, S₁(0)=0.
#   All integers! ✓
#
# For π²/12:
#   We need a bounded PIVP computing π²/12 with rational coefficients.
#   π/4 = arctan(1) = ∫₀^∞ cos²(t/(1+t)) · (1/(1+t))² dt ... messy.
#
#   Alternative: π²/6 = ζ(2) = Σ 1/k² = ∫₀^∞ t/(e^t-1) dt
#   So π²/12 = (1/2)·ζ(2) = ∫₀^∞ t/(e^t-1) dt / 2 ... has t factor again!
#
#   Or: π²/12 = η(2) = ∫₀^∞ t·u/(1+u) dt = same cascade level.
#
#   The cascade for η(2):
#   T₁' = u/(1+u)     → ln(2)    [needs no constants]
#   T₂' = ln(2) - T₁  → π²/12   [needs ln(2)]
#
#   So π²/12 requires ln(2) — one level of nesting.
#   And η(3) requires π²/12 — two levels.
#
#   At each level, replacing the constant with a dynamic variable
#   introduces a finite bias.
#
#   KEY IDEA: Can we CORRECT the bias at each level?
#
#   Level 1: S₁' = u/(1+u). S₁ → ln(2). No bias. ✓
#
#   Level 2: S₂' = L(t) - S₁ where L → ln(2) dynamically.
#   If L = S₁ (same computation), then S₂' = S₁ - S₁ = 0. Dead.
#   If L is INDEPENDENT (separate copy): L' = u_L/(1+u_L), u_L'=-u_L
#   Then S₂' = L - S₁ ≈ (ln(2) + ε_L) - (ln(2) - ε₁)
#   = ε_L + ε₁ → 0 exponentially.
#   S₂(∞) = ∫₀^∞ (ε_L + ε₁) ds which is a finite constant, NOT η(2).
#
#   WRONG! The issue is that S₂ should accumulate (ln(2) - S₁),
#   not (L - S₁).
#
#   The bias: S₂(∞) = ∫₀^∞ (L(s)-S₁(s)) ds vs ∫₀^∞ (ln(2)-S₁(s)) ds
#   Difference = ∫₀^∞ (L(s)-ln(2)) ds = finite constant.
#
#   Can we compute and subtract this bias?
#   Bias₂ = ∫₀^∞ (L(s)-ln(2)) ds = -∫₀^∞ ln(1+e^{-s}) ds = -η(2)
#   Wait: L(s) = ∫₀^s u/(1+u) dr = ln(2) - ln(1+e^{-s})
#   So L(s) - ln(2) = -ln(1+e^{-s})
#   ∫₀^∞ (L(s)-ln(2)) ds = -∫₀^∞ ln(1+e^{-s}) ds = -η(2) = -π²/12
#
#   So S₂(∞) = ∫₀^∞ (L(s)-S₁(s)) ds = ∫₀^∞ (ln(2)-S₁(s)) ds + (-π²/12)
#            = η(2) - π²/12 = 0
#
#   S₂ → 0, not η(2)! That's because L and S₁ are THE SAME function,
#   so L - S₁ = 0 for all t (if initialized the same way).
#
#   What if L is a SHIFTED copy? L' = u_L/(1+u_L), u_L' = -u_L,
#   but with u_L(0) = e^{-τ} for some τ > 0?
#   Then L(t) = ln(2) - ln(1+e^{-(t+τ)}) ≠ S₁(t).
#   And L → ln(2) FASTER (ahead by τ).
#
#   S₂' = L(t) - S₁(t) = ln(1+e^{-t}) - ln(1+e^{-(t+τ)})
#   → 0 as t → ∞.
#   S₂(∞) = ∫₀^∞ [ln(1+e^{-s}) - ln(1+e^{-(s+τ)})] ds
#   = ∫₀^∞ ln(1+e^{-s}) ds - ∫₀^∞ ln(1+e^{-(s+τ)}) ds
#   = η(2) - ∫_τ^∞ ln(1+e^{-s}) ds
#   = η(2) - (η(2) - ∫₀^τ ln(1+e^{-s}) ds)
#   = ∫₀^τ ln(1+e^{-s}) ds
#
#   This is NOT η(2) unless τ = ∞. And ∫₀^τ ln(1+e^{-s}) ds < η(2).
#
#   The shift approach doesn't work either.
#
# CONCLUSION: There is no simple way to replace constants in the cascade.
# The cascade structure fundamentally requires exact constants.
#
# For a RIGOROUS first-floor proof of ζ(3), we likely need either:
# 1. A proof that ζ(3) can be expressed via field operations on e and π
#    (number-theoretic breakthrough — probably open)
# 2. A fundamentally different ODE design that avoids the cascade
# 3. A theoretical argument (not constructive) showing that the
#    compilation theorem preserves first-floor for this specific system
# ================================================================


# ================================================================
# Let me test one more thing: the CASCADE with exact constants is a
# valid PIVP if we allow REAL (not just integer) coefficients.
#
# The RTGPAC definition requires INTEGER coefficients. But:
# - ln(2) and π²/12 are not integers
# - However, they appear as INITIAL CONDITIONS could we reformulate?
#
# From the ODE: S₂' = c₁ - S₁ with S₂(0) = 0, c₁ = ln(2).
# Equivalently: define S₂ with S₂(0) = c₁ (non-zero IC):
#   dS₂/dt = -S₁, S₂(0) = ln(2)
# Then S₂(t) = ln(2) - ∫₀^t S₁(s) ds = ln(2) - [s·S₁ - ∫₀^t s·S₁'(s)ds]...
#
# No, simpler: S₂(t) = ln(2) + ∫₀^t (-S₁(s)) ds
# As t→∞: S₂(∞) = ln(2) - ∫₀^∞ S₁(s) ds = ln(2) - ???
# This doesn't give η(2) because ∫₀^∞ S₁(s) ds diverges.
#
# The non-zero IC formulation doesn't help.
#
# ACTUALLY: from RTCRN2, the definition of RTGPAC allows y(0) = 0
# (all zero). But the RTCRN definition allows any initialization as
# long as species start at 0. With the CRN → GPAC equivalence,
# we can relax to integer ICs.
#
# From RTCRN2 p.5: "All coefficients of y are integers" and y(0) = 0.
#
# So we STRICTLY need integer coefficients and zero ICs.
#
# The cascade with exact constants: S₂' = ln(2) - S₁ has coefficient
# ln(2) which is NOT an integer. So this is NOT a valid RTGPAC.
#
# The question reduces to: can we compute η(3) [and hence ζ(3)]
# with a PIVP having INTEGER coefficients and ZERO initial conditions?
# ================================================================


# Let me at least test: what happens with the BIASED cascade
# where we accept the finite constant offset and try to correct?

def system_biased_cascade(t, y):
    """Cascade where S₁ computes ln(2), and we use S₁ directly as
    the 'constant' for S₂.

    S₁' = u/(1+u)                   → ln(2)
    S₂' = S₁ - S₁ = 0  ... NO, that's wrong.

    We need a DIFFERENT dynamic variable for ln(2).
    Use a TRACKING FILTER: W' = S₁ - W → W → ln(2) (by Lemma 3)

    Then: S₂' = W - S₁
    But W ≈ S₁ for large t, so S₂' ≈ 0. S₂ stalls.
    The TRANSIENT dynamics determine S₂(∞).

    Let's also try: use W as a LOW-PASS FILTERED version of S₁.
    W' = k·(S₁ - W) for various rates k.
    """
    u, S1, W1, S2, W2, S3 = y

    du = -u
    dS1 = u / (1.0 + u)

    # W₁ tracks S₁ via low-pass filter (Lemma 3, rate k=1)
    dW1 = S1 - W1  # W₁ → ln(2)

    # S₂ accumulates (W₁ - S₁) = (filtered ln2) - S₁
    dS2 = W1 - S1  # NOTE: W₁ lags S₁, so this is NOT zero

    # W₂ tracks S₂ via low-pass filter
    dW2 = S2 - W2  # W₂ → S₂(∞)

    # S₃ accumulates (W₂ - S₂) = (filtered η₂) - S₂
    dS3 = W2 - S2

    return [du, dS1, dW1, dS2, dW2, dS3]


def run():
    fig, axes = plt.subplots(2, 2, figsize=(14, 10))
    fig.suptitle('Direction (b): Tracking Filter Cascade Attempts', fontsize=14)

    # Baseline: exact constants
    def exact_cascade(t, y):
        S1, S2, S3, u = y
        return [u/(1+u), np.log(2)-S1, np.pi**2/12-S2, -u]

    sol_exact = solve_ivp(exact_cascade, [0, T_MAX], [0,0,0,1],
                          t_eval=T_EVAL, rtol=1e-13, atol=1e-15, method='DOP853')
    out_exact = (4/3) * sol_exact.y[2]
    err_exact = np.abs(out_exact - ZETA3)

    # Biased cascade with tracking filters
    y0 = [1.0, 0.0, 0.0, 0.0, 0.0, 0.0]  # u=1, rest=0
    sol_biased = solve_ivp(system_biased_cascade, [0, T_MAX], y0,
                           t_eval=T_EVAL, rtol=1e-13, atol=1e-15, method='DOP853')

    out_biased = (4/3) * sol_biased.y[5]  # S₃
    err_biased = np.abs(out_biased - ZETA3)

    # Plot 1: S₂ comparison
    ax = axes[0, 0]
    ax.plot(sol_exact.t, sol_exact.y[1], 'b-', label='S₂ (exact c₁)')
    ax.plot(sol_biased.t, sol_biased.y[3], 'r-', label='S₂ (filter cascade)')
    ax.axhline(np.pi**2/12, color='g', ls='--', alpha=0.5, label='η(2)=π²/12')
    ax.set_title('S₂ convergence')
    ax.set_xlabel('t'); ax.legend(fontsize=8); ax.grid(True, alpha=0.3)

    # Plot 2: S₃ / output comparison
    ax = axes[0, 1]
    ax.plot(sol_exact.t, (4/3)*sol_exact.y[2], 'b-', label='exact cascade')
    ax.plot(sol_biased.t, (4/3)*sol_biased.y[5], 'r-', label='filter cascade')
    ax.axhline(ZETA3, color='g', ls='--', alpha=0.5, label='ζ(3)')
    ax.set_title('Output = (4/3)S₃')
    ax.set_xlabel('t'); ax.legend(fontsize=8); ax.grid(True, alpha=0.3)

    # Plot 3: Error comparison
    ax = axes[1, 0]
    ax.semilogy(sol_exact.t, np.maximum(err_exact, 1e-16), 'b-', label='exact')
    ax.semilogy(sol_biased.t, np.maximum(err_biased, 1e-16), 'r-', label='filter')
    ax.semilogy(T_EVAL, np.exp(-T_EVAL), 'k--', alpha=0.3, label='e^{-t}')
    ax.set_title('Error comparison')
    ax.set_xlabel('t'); ax.set_ylabel('|output - ζ(3)|')
    ax.legend(fontsize=8); ax.grid(True, alpha=0.3)

    # Plot 4: W₁ vs S₁ and their difference
    ax = axes[1, 1]
    ax.plot(sol_biased.t, sol_biased.y[1], 'b-', label='S₁')
    ax.plot(sol_biased.t, sol_biased.y[2], 'r-', label='W₁ (filter)')
    ax.plot(sol_biased.t, sol_biased.y[2] - sol_biased.y[1], 'g-', label='W₁-S₁')
    ax.axhline(np.log(2), color='k', ls='--', alpha=0.3, label='ln(2)')
    ax.set_title('S₁ vs tracking filter W₁')
    ax.set_xlabel('t'); ax.legend(fontsize=8); ax.grid(True, alpha=0.3)

    plt.tight_layout()
    path = '/Users/huangx/.openclaw/workspace/projects/Ripple/experiments/apery_directions.png'
    plt.savefig(path, dpi=150, bbox_inches='tight')
    print(f"Plot saved to {path}")

    # Summary
    print(f"\nExact cascade output at T={T_MAX}: {out_exact[-1]:.12f}")
    print(f"Filter cascade output at T={T_MAX}: {out_biased[-1]:.12f}")
    print(f"Filter cascade S₂(∞): {sol_biased.y[3][-1]:.12f} (target: {np.pi**2/12:.12f})")
    print(f"Filter cascade error: {err_biased[-1]:.6e}")

    # Fit filter cascade convergence
    mask = (err_biased > 1e-12) & (sol_biased.t > 5)
    if mask.sum() > 10:
        c = np.polyfit(sol_biased.t[mask], np.log(np.maximum(err_biased[mask], 1e-16)), 1)
        print(f"Filter cascade decay rate: α ≈ {-c[0]:.4f}")
    else:
        print(f"Filter cascade: already at machine precision or divergent")


if __name__ == '__main__':
    run()
