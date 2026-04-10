"""
Numerical experiments: convergence rate of various ODE constructions for ζ(3).

Goal: determine which constructions give first-floor (exponential) convergence,
i.e., |s(t) - ζ(3)| ~ C·e^{-αt} for some α > 0.

Three approaches:
1. Fermi-Dirac form with bounded surrogates
2. Iterated integral decomposition
3. Zerolized system with IBP compensation
"""

import numpy as np
from scipy.integrate import solve_ivp
from scipy.special import zeta
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt

ZETA3 = float(zeta(3))  # 1.2020569031595942
T_MAX = 30.0
T_EVAL = np.linspace(0, T_MAX, 5000)


# ================================================================
# Approach 1: Fermi-Dirac form
# ζ(3) = (2/3) ∫₀^∞ t²/(e^t + 1) dt
#
# Variables:
#   u = e^{-t}  → u' = -u, u(0)=1
#   v = t/(1+t) → v' = (1-v)², v(0)=0  [so t = v/(1-v)]
#   s = accumulator → s' = (2/3) · t² · u/(1+u)
#
# Since t = v/(1-v) and (1-v) = 1/(1+t):
#   t² = v²/(1-v)²
#   s' = (2/3) · v²/(1-v)² · u/(1+u)
#
# This is NOT polynomial because of 1/(1-v)². But we can introduce
# q = (1-v) = 1/(1+t), then 1/(1-v)² = 1/q².
#
# To make it polynomial, multiply through by q²:
# Define rescaled time τ where dτ/dt = 1 (keep physical time).
# We need another approach: track t² via a separate variable.
#
# Alternative: Let w = t² · e^{-t}. Then:
#   w' = (2t - t²)·e^{-t} = (2t - t²)·u
# But t is unbounded...
#
# Most direct approach: just use t as a non-bounded "clock" variable
# and see what convergence rate we get from the integral itself.
# The tail integral ∫_t^∞ s²/(e^s+1) ds ~ t²·e^{-t} → exponential.
# ================================================================

def approach1_fermi_dirac(t, y):
    """Direct integration: s' = (2/3) · t² · e^{-t}/(1 + e^{-t})"""
    s = y[0]
    u = np.exp(-t)
    ds = (2.0/3.0) * t**2 * u / (1.0 + u)
    return [ds]

def approach1_bounded(t, y):
    """Bounded-variable version using v = t/(1+t), u = e^{-t}.

    Variables: [s, u, v]
    s' = (2/3) · v² · u / ((1-v)² · (1+u))
    u' = -u
    v' = (1-v)²

    Note: 1/(1-v)² makes this non-polynomial, but we test convergence.
    """
    s, u, v = y
    q = 1.0 - v  # = 1/(1+t), bounded in (0, 1]
    if q < 1e-15:
        q = 1e-15
    ds = (2.0/3.0) * v**2 * u / (q**2 * (1.0 + u))
    du = -u
    dv = q**2
    return [ds, du, dv]


# ================================================================
# Approach 2: Iterated integral
# ζ(3) = (1/2) ∫₀^∞ t²/(e^t - 1) dt
#      = ∫₀^∞ t · [∫_t^∞ 1/(e^s-1) ds] dt     (by parts, u=t², dv=1/(e^t-1)dt... actually let me redo)
#
# Actually: ∫₀^∞ t²·g(t) dt where g(t) = Σ e^{-kt}
# = Σ_{k=1}^∞ ∫₀^∞ t²·e^{-kt} dt = Σ 2/k³ = 2·ζ(3)
#
# Iterated approach: define
#   G_k(t) = ∫_t^∞ e^{-ks} ds = e^{-kt}/k
#   H_k(t) = ∫_t^∞ G_k(s) ds = e^{-kt}/k²
#   I_k(t) = ∫_t^∞ H_k(s) ds = e^{-kt}/k³
#
# Then ζ(3) = Σ I_k(0) = Σ 1/k³.
#
# Define the running integrals from 0 to t:
#   g₁(t) = Σ_{k=1}^∞ (1 - e^{-kt})/k = -ln(1 - e^{-t})... hmm
#
# Better approach: define
#   A(t) = Σ e^{-kt} = e^{-t}/(1-e^{-t}) = 1/(e^t - 1)    [unbounded at t=0]
#   B(t) = Σ e^{-kt}/k = -ln(1-e^{-t})                      [also unbounded at t=0]
#   C(t) = Σ e^{-kt}/k² = Li₂(e^{-t})                       [bounded, C(0)=π²/6]
#
# Then ∫₀^t A(s) ds = -ln(1-e^{-t}) - ... complicated.
#
# Let me try a different decomposition. Use the Fermi-Dirac version
# to avoid singularity at 0:
# ζ(3) = (2/3) ∫₀^∞ t² · Σ (-1)^{k+1} e^{-kt} dt
#       = (2/3) Σ (-1)^{k+1} · 2/k³ = (4/3) η(3) = (4/3)·(3/4)ζ(3) = ζ(3) ✓
#
# Define partial sums via ODE:
#   For each k: track p_k(t) = ∫₀^t s² · (-1)^{k+1} · e^{-ks} ds
#   p_k' = (-1)^{k+1} · t² · e^{-kt}
#
# With N terms: S_N(t) = (2/3) Σ_{k=1}^N p_k(t)
# As t → ∞: S_N(∞) = (2/3) Σ_{k=1}^N (-1)^{k+1} · 2/k³ = (4/3) Σ_{k=1}^N (-1)^{k+1}/k³
#
# This gives the partial sum of η(3), not ζ(3) itself.
# We'd need N → ∞ for exactness.
#
# A FINITE system can't compute ζ(3) exactly this way.
# The iterated integral approach needs more thought.
#
# Instead, let's test the approach where we separate the integral into
# two layers to avoid t² directly:
#
# ζ(3) = (1/2) ∫₀^∞ t² · e^{-t}/(1-e^{-t}) dt    [Bose-Einstein, using u=e^{-t}]
#
# IBP: let f = t, g' = t·u/(1-u)
# We need ∫₀^∞ t·u/(1-u) dt = ∫₀^∞ t·Σ u^k dt = Σ 1/k² = π²/6
#
# So: (1/2)∫₀^∞ t²·u/(1-u) dt = (1/2)[t·(-Li₂(e^{-t})-t·ln(1-e^{-t}))]₀^∞ + ...
# This gets messy. Let me just numerically test the iterated structure.
#
# Define:
#   φ(t) = ∫_t^∞ u/(1-u) ds = -ln(1-e^{-t})     (= Li₁(e^{-t}))
#   ψ(t) = ∫_t^∞ φ(s) ds = Li₂(e^{-t})           (bounded, ψ(0)=π²/6)
#   χ(t) = ∫_t^∞ ψ(s) ds = Li₃(e^{-t})           (bounded, χ(0)=ζ(3))
#
# So ζ(3) = Li₃(1) = χ(0), and:
#   χ'(t) = -ψ(t) = -Li₂(e^{-t})
#   ψ'(t) = -φ(t) = ln(1-e^{-t})
#   φ'(t) = -u/(1-u) = -e^{-t}/(1-e^{-t})
#
# Running from t=0: χ(0)=ζ(3) → we want χ(0), but the ODE goes forward!
#
# Flip: define running integrals from 0:
#   Φ(t) = ∫₀^t e^{-s}/(1-e^{-s}) ds = -ln(1-e^{-t}) + ln(1-1) ... diverges!
#
# The 1/(1-e^{-t}) singularity at t=0 kills this.
#
# Use Fermi-Dirac to avoid singularity:
#   Φ(t) = ∫₀^t e^{-s}/(1+e^{-s}) ds = ln(1+e^{-0}) - ln(1+e^{-t})
#         = ln(2) - ln(1+e^{-t})    [bounded!]
#
# Then by parts twice from the Fermi-Dirac integral...
# this is getting algebraically heavy. Let me just code the direct computation.
# ================================================================

def approach2_polylog_cascade(t, y):
    """Track Li_n(e^{-t}) via cascading ODEs.

    Li_1(e^{-t}) = -ln(1-e^{-t})  → d/dt = e^{-t}/(1-e^{-t})
    Li_2(e^{-t}) = ∫_t^∞ Li_1/s... no, d/dt Li_n(e^{-t}) = -Li_{n-1}(e^{-t})/...

    Actually: d/dt Li_n(e^{-t}) = -e^{-t} · Li_{n-1}(e^{-t}) / e^{-t} · (1/t)...

    No. By chain rule: d/dt Li_n(e^{-t}) = Li_n'(e^{-t}) · (-e^{-t})
    And Li_n'(x) = Li_{n-1}(x)/x.
    So d/dt Li_n(e^{-t}) = Li_{n-1}(e^{-t})/e^{-t} · (-e^{-t}) = -Li_{n-1}(e^{-t})

    Beautiful! So:
      d/dt Li_3(e^{-t}) = -Li_2(e^{-t})
      d/dt Li_2(e^{-t}) = -Li_1(e^{-t})
      d/dt Li_1(e^{-t}) = -Li_0(e^{-t}) = -e^{-t}/(1-e^{-t})

    Problem: Li_1(0) = 0, Li_2(0) = 0, Li_3(0) = 0.
    But Li_3(1) = ζ(3), Li_2(1) = π²/6, Li_1(1) = ∞.

    The ODE runs BACKWARD: as t increases, e^{-t} → 0, and Li_n(e^{-t}) → 0.
    We want the VALUE at t=0, which is Li_3(1) = ζ(3).

    So this doesn't give a forward-converging ODE for ζ(3).

    Alternative: define w_n(t) = Li_n(1) - Li_n(e^{-t}) = ζ(n) - Li_n(e^{-t})
    Then w_n(0) = 0, w_n(∞) = ζ(n).
    And w_n'(t) = Li_{n-1}(e^{-t}) = ζ(n-1) - w_{n-1}(t).

    So: w₃' = ζ(2) - w₂ = π²/6 - w₂
        w₂' = ζ(1) - w₁ = ∞ ... diverges!

    Li_1(e^{-t}) = -ln(1-e^{-t}) which diverges as t→0⁺.
    So w₁(t) = ∞ - (-ln(1-e^{-t})) is not well-defined.
    """
    # This approach doesn't work directly due to Li_1 divergence.
    # Placeholder - won't use this.
    return [0, 0, 0]


# ================================================================
# Approach 2b: Fermi-Dirac polylog cascade (avoids Li_1 divergence!)
#
# η(n) = Σ (-1)^{k+1}/k^n = (1-2^{1-n})·ζ(n)
# η(n) = -Li_n(-1) = (1/Γ(n)) ∫₀^∞ t^{n-1}/(e^t+1) dt
#
# Li_n(-e^{-t}) derivative:
# d/dt Li_n(-e^{-t}) = Li_{n-1}(-e^{-t})/(-e^{-t}) · (e^{-t}) = -Li_{n-1}(-e^{-t})
#
# Same cascade! But now:
# Li_1(-x) = -ln(1+x), so Li_1(-e^{-t}) = -ln(1+e^{-t}) [BOUNDED! ∈ [-ln(2), 0)]
# Li_2(-e^{-t}) → Li_2(-1) = -π²/12 as t→0
# Li_3(-e^{-t}) → Li_3(-1) = -3ζ(3)/4 as t→0
#
# Define w_n(t) = -Li_n(-1) + Li_n(-e^{-t}) ... wait let me think.
# Li_n(-e^{-t}) goes from Li_n(-1) at t=0 to Li_n(0)=0 at t=∞.
# So Li_n(-e^{-t}) → 0 as t→∞.
#
# Define W_n(t) = -Li_n(-e^{-t}). Then:
# W_n(0) = -Li_n(-1) = η(n)
# W_n(∞) = 0
# W_n'(t) = -(-Li_{n-1}(-e^{-t})) = Li_{n-1}(-e^{-t}) = -W_{n-1}(t)
#
# This runs "down" again. We want forward convergence to ζ(3).
#
# Define S_n(t) = η(n) - W_n(t) = η(n) + Li_n(-e^{-t}).
# S_n(0) = η(n) + Li_n(-1) = η(n) - η(n) = 0.
# S_n(∞) = η(n).
# S_n'(t) = -W_n'(t) = W_{n-1}(t) = η(n-1) - S_{n-1}(t).
#
# So:
# S₁'(t) = η(0) - S₀(t)
# S₂'(t) = η(1) - S₁(t) = ln(2) - S₁(t)
# S₃'(t) = η(2) - S₂(t) = π²/12 - S₂(t)
#
# And η(0) = 1/2, S₀(t) = η(0) + Li_0(-e^{-t}) = 1/2 + (-e^{-t}/(1+e^{-t}))
#          = 1/2 - e^{-t}/(1+e^{-t}) = 1/(2(1+e^{-t}))... let me compute:
# Li_0(-x) = -x/(1+x) = 1/(1+x) - 1, so Li_0(-e^{-t}) = 1/(1+e^{-t}) - 1 = -e^{-t}/(1+e^{-t})
# S₀(t) = 1/2 - e^{-t}/(1+e^{-t}) = (1+e^{-t}-2e^{-t})/(2(1+e^{-t})) = (1-e^{-t})/(2(1+e^{-t}))
#
# So: S₁' = 1/2 - S₀ = 1/2 - (1-e^{-t})/(2(1+e^{-t})) = e^{-t}/(1+e^{-t})
# And: S₂' = ln(2) - S₁
#       S₃' = π²/12 - S₂
#
# S₃(∞) = η(3) = (3/4)ζ(3), so ζ(3) = (4/3)·S₃(∞).
#
# But this system involves the constants η(1) = ln(2) and η(2) = π²/12.
# These are themselves real-time computable! So we compose:
# - An ODE for ln(2): standard, real-time
# - An ODE for π²/12: uses π construction, real-time
# - The cascade S₁, S₂, S₃
#
# KEY QUESTION: Is the CASCADE first-floor?
# S₁(t) → η(1) = ln(2). How fast?
# S₁' = e^{-t}/(1+e^{-t}), so S₁(t) = ln(1+e^{-0}) - ln(1+e^{-t}) = ln(2) - ln(1+e^{-t})
# Error: |S₁(t) - ln(2)| = ln(1+e^{-t}) - ln(1) ~ e^{-t} → exponential!
#
# S₂' = ln(2) - S₁ = ln(1+e^{-t}) ~ e^{-t}
# So S₂(t) ~ ∫₀^t e^{-s} ds = 1-e^{-t}, and S₂(∞) = η(2) = π²/12.
# Error: |S₂(t) - π²/12| = |∫_t^∞ (ln(2)-S₁(s)) ds| = ∫_t^∞ ln(1+e^{-s}) ds ~ e^{-t}
# Still exponential!
#
# S₃' = π²/12 - S₂ ~ e^{-t}
# Error: |S₃(t) - η(3)| ~ e^{-t}
# EXPONENTIAL! FIRST FLOOR!
#
# THIS IS THE KEY INSIGHT! The Fermi-Dirac polylog cascade gives
# exponential convergence because each layer only adds O(e^{-t}) error!
#
# BUT: the constants ln(2) and π²/12 appear in the ODE coefficients.
# We need to replace them with dynamic variables.
# If those dynamic variables converge exponentially too, the composed
# system should still be first-floor (by the low-pass filter argument).
# ================================================================

def approach2b_fermi_cascade(t, y):
    """Fermi-Dirac polylog cascade.

    S₁' = e^{-t}/(1+e^{-t})           [= u/(1+u)]
    S₂' = ln(2) - S₁                   [uses exact constant]
    S₃' = π²/12 - S₂                   [uses exact constant]

    output = (4/3)·S₃ → ζ(3)

    Variables: [S1, S2, S3, u]
    u = e^{-t}, u' = -u
    """
    S1, S2, S3, u = y
    LN2 = np.log(2)
    PI2_12 = np.pi**2 / 12.0

    dS1 = u / (1.0 + u)
    dS2 = LN2 - S1
    dS3 = PI2_12 - S2
    du = -u
    return [dS1, dS2, dS3, du]


def approach2b_fermi_cascade_dynamic(t, y):
    """Same cascade but with dynamically computed constants.

    ln(2) computed via: L' = e^{-t}/(1+e^{-t}), L(0)=0 → L(∞)=ln(2)
    Wait, that's the same as S₁! So S₂' = S₁(∞) - S₁(t).

    Hmm, we need ln(2) as a constant, not S₁(t).

    Alternative: compute ln(2) via a separate fast ODE.
    L' = (1-L)·(1-v), where v=t/(1+t), L(0)=0 → L(t)=1-2^{-t/(1+t)}... no.

    Standard: ln(2) = ∫₀^∞ e^{-t}/(1+e^{-t}) dt = S₁(∞).

    We can use a "known value" ODE for ln(2):
    Use the identity ln(2) = 1 - 1/2 + 1/3 - ... or an integral.

    Simplest: x' = (1-x)·r, x(0)=0 where r is a suitable rate.
    For ln(2): e^{ln(2)} = 2, so 2^x with x=1 gives 2.

    Actually, the simplest bounded PIVP for ln(2):
    We know 1/(1+e^{-t}) → 1 exponentially. And
    ∫₀^t 1/(1+e^{-s}) ds = t - ln(1+e^{-t}) + ln(2) ~ t + ln(2) - ln(2) + ...

    Hmm, ln(2) is tricky to extract as a limit.

    Better: Use the fact that ln(2) = S₁(∞). So in the cascade,
    replace the constant ln(2) with a "target tracking" ODE:

    L tracks S₁'s long-run average via low-pass filter:
    L' = S₁' - (something that makes L → ln(2))

    Actually the simplest approach: L is just S₁ itself!
    S₂' = ln(2) - S₁ = (S₁(∞) - S₁(t)) → this is just the tail integral.

    So we don't need a separate variable for ln(2)!
    S₂' = S₁(∞) - S₁(t) where the RHS = ∫_t^∞ S₁'(s) ds = ∫_t^∞ u/(1+u) ds

    But in the ODE we write S₂' = ln(2) - S₁. The quantity (ln(2) - S₁(t))
    is just the tail integral, which is a function of the current state.

    We can't avoid knowing ln(2). Unless...

    We define: S₂' = u·φ where φ satisfies some ODE.

    Let me think... ln(1+e^{-t}) = ln(2) - S₁(t).
    And ln(1+u) where u = e^{-t}. So:
    S₂' = ln(1+u)

    And d/dt[ln(1+u)] = u'/(1+u) = -u/(1+u) = -S₁'

    So if we define w = ln(1+u), then:
    w' = -u/(1+u)
    S₂' = w

    But w(0) = ln(2) — a non-trivial initial condition!

    Alternative: define w̃ = w - ln(2) = ln(1+u) - ln(2) = ln((1+u)/2).
    w̃(0) = 0, w̃' = -u/(1+u).
    S₂' = w̃ + ln(2) — still need ln(2)!

    We're going in circles. The constant ln(2) must come from somewhere.

    For NOW: test with exact constants to confirm first-floor convergence,
    then figure out how to dynamically compute ln(2) and π²/12.
    """
    S1, S2, S3, u = y
    # Use exact constants for now
    LN2 = np.log(2)
    PI2_12 = np.pi**2 / 12.0

    dS1 = u / (1.0 + u)
    dS2 = LN2 - S1
    dS3 = PI2_12 - S2
    du = -u
    return [dS1, dS2, dS3, du]


# ================================================================
# Approach 3: Zerolized + IBP from existing Apéry construction
#
# From apery_report.tex, the IBP-compensated target is:
#   s̄₃'(t) = (1/2)(u₃ + w₂) + E₂(t) + t·E₂'(t)
# where the main block uses zerolized coordinates (all start at 0)
# but with constants C=1/(e-1) and D=e/(e-1) in the drift.
#
# Here we test: if we use EXACT constants C, D in the drift,
# what's the convergence rate of s̄₃?
# ================================================================

def approach3_zerolized_exact(t, y):
    """Zerolized main system with exact constants + IBP compensation.

    Constants (exact):
    C = 1/(e-1), D = e/(e-1)

    Main block (zerolized, all start at 0):
    v̇  = -(v+e)·(u1+C)·(v+e-1)
    u̇1 = (u1+C)·((v+e)·(u1+C) - 1)
    u̇2 = (u2+C)·((v+e)·(u1+C) - 2)
    u̇3 = (u3+C)·((v+e)·(u1+C) - 3)
    ṙ  = -(r+D)·(r+C)
    ẇ1 = (r+C) - (r+D)·(w1+C)
    ẇ2 = 2·(w1+C) - (r+D)·(w2+C)

    Auxiliary block:
    Ė  = 1 - E          → E→1
    Ė₁ = E₁·(1-E)      → E₁→e  (E₁(0)=1)
    Ė₂ = 1-(E₁-1)·E₂   → E₂→1/(e-1)=C
    Ė₃ = E₁·E₂ - E₃    → E₃→e/(e-1)=D

    IBP target:
    s̄₃' = (1/2)(u3 + w2) + E₂ + t·E₂'

    But t is unbounded! The term t·E₂' appears.
    E₂' = 1 - (E₁-1)·E₂
    t·E₂' ~ t · C·e^{-t} (since E₁→e, E₂→C both exponentially)
    → t·e^{-t} → 0 exponentially (up to polynomial prefactor)

    For the test, we use exact C, D in the drift and the full auxiliary + IBP.
    """
    # y = [v, u1, u2, u3, r, w1, w2, E, E1, E2, E3, sbar, clock_t]
    # clock_t tracks physical time (needed for t·E₂' term)

    v, u1, u2, u3, r, w1, w2, E, E1, E2, E3, sbar = y

    e_val = np.e
    C_val = 1.0 / (e_val - 1.0)
    D_val = e_val / (e_val - 1.0)

    # Main block with EXACT constants C, D
    vu1 = (v + e_val) * (u1 + C_val)
    dv = -(v + e_val) * (u1 + C_val) * (v + e_val - 1.0)
    du1 = (u1 + C_val) * (vu1 - 1.0)
    du2 = (u2 + C_val) * (vu1 - 2.0)
    du3 = (u3 + C_val) * (vu1 - 3.0)
    dr = -(r + D_val) * (r + C_val)
    dw1 = (r + C_val) - (r + D_val) * (w1 + C_val)
    dw2 = 2.0 * (w1 + C_val) - (r + D_val) * (w2 + C_val)

    # Auxiliary block
    dE = 1.0 - E
    dE1 = E1 * (1.0 - E)
    dE2 = 1.0 - (E1 - 1.0) * E2
    dE3 = E1 * E2 - E3

    # IBP target: s̄₃' = (1/2)(u3+w2) + E₂ + t·E₂'
    dsbar = 0.5 * (u3 + w2) + E2 + t * dE2

    return [dv, du1, du2, du3, dr, dw1, dw2, dE, dE1, dE2, dE3, dsbar]


# ================================================================
# Run experiments and plot convergence
# ================================================================

def run_and_plot():
    fig, axes = plt.subplots(2, 2, figsize=(14, 10))
    fig.suptitle(f'Convergence to ζ(3) = {ZETA3:.10f}', fontsize=14)

    # --- Approach 1: Direct Fermi-Dirac ---
    print("Running Approach 1: Fermi-Dirac direct...")
    sol1 = solve_ivp(approach1_fermi_dirac, [0, T_MAX], [0.0],
                     t_eval=T_EVAL, rtol=1e-12, atol=1e-14, method='DOP853')
    err1 = np.abs(sol1.y[0] * (2.0/3.0) - ZETA3)  # Wait, s already has 2/3 factor
    # Actually s'=(2/3)t²u/(1+u), so s(∞)=ζ(3) directly
    err1 = np.abs(sol1.y[0] - ZETA3)

    ax = axes[0, 0]
    ax.semilogy(sol1.t, np.maximum(err1, 1e-16), 'b-', linewidth=1)
    ax.set_title('Approach 1: Fermi-Dirac direct')
    ax.set_xlabel('t')
    ax.set_ylabel('|s(t) - ζ(3)|')
    ax.grid(True, alpha=0.3)
    # Plot reference lines
    ax.semilogy(sol1.t, np.exp(-sol1.t), 'r--', alpha=0.5, label='e^{-t} (first floor)')
    ax.semilogy(sol1.t, np.exp(-0.5*sol1.t), 'g--', alpha=0.5, label='e^{-t/2}')
    ax.legend(fontsize=8)

    # --- Approach 1b: Bounded variables ---
    print("Running Approach 1b: Fermi-Dirac bounded vars...")
    sol1b = solve_ivp(approach1_bounded, [0.001, T_MAX], [0.0, np.exp(-0.001), 0.001/(1+0.001)],
                      t_eval=T_EVAL[T_EVAL >= 0.001], rtol=1e-12, atol=1e-14, method='DOP853')
    err1b = np.abs(sol1b.y[0] - ZETA3)

    ax = axes[0, 1]
    ax.semilogy(sol1b.t, np.maximum(err1b, 1e-16), 'b-', linewidth=1)
    ax.set_title('Approach 1b: Fermi-Dirac bounded vars')
    ax.set_xlabel('t')
    ax.set_ylabel('|s(t) - ζ(3)|')
    ax.grid(True, alpha=0.3)
    ax.semilogy(sol1b.t, np.exp(-sol1b.t), 'r--', alpha=0.5, label='e^{-t}')
    ax.legend(fontsize=8)

    # --- Approach 2b: Fermi-Dirac polylog cascade ---
    print("Running Approach 2b: Fermi-Dirac polylog cascade...")
    sol2 = solve_ivp(approach2b_fermi_cascade, [0, T_MAX], [0.0, 0.0, 0.0, 1.0],
                     t_eval=T_EVAL, rtol=1e-12, atol=1e-14, method='DOP853')
    target2 = (4.0/3.0) * sol2.y[2]  # (4/3)·S₃ → ζ(3)
    err2 = np.abs(target2 - ZETA3)

    ax = axes[1, 0]
    ax.semilogy(sol2.t, np.maximum(err2, 1e-16), 'b-', linewidth=1)
    ax.set_title('Approach 2b: Fermi-Dirac polylog cascade (exact constants)')
    ax.set_xlabel('t')
    ax.set_ylabel('|(4/3)S₃(t) - ζ(3)|')
    ax.grid(True, alpha=0.3)
    ax.semilogy(sol2.t, np.exp(-sol2.t), 'r--', alpha=0.5, label='e^{-t} (first floor)')
    ax.semilogy(sol2.t, 0.5*sol2.t**2 * np.exp(-sol2.t), 'm--', alpha=0.5, label='t²e^{-t}')
    ax.legend(fontsize=8)

    # --- Approach 3: Zerolized + IBP ---
    print("Running Approach 3: Zerolized + IBP...")
    # Initial: all main vars 0, E=0, E₁=1, E₂=0, E₃=0, sbar=0
    y0_3 = [0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0,  # main block
            0.0, 1.0, 0.0, 0.0,  # aux block: E, E₁, E₂, E₃
            0.0]  # sbar
    sol3 = solve_ivp(approach3_zerolized_exact, [0.001, T_MAX],
                     [0.0]*7 + [1.0 - np.exp(-0.001), np.exp(0.001*(1-np.exp(-0.001))), 0.0, 0.0, 0.0],
                     t_eval=T_EVAL[T_EVAL >= 0.001], rtol=1e-12, atol=1e-14, method='DOP853',
                     max_step=0.01)
    # Hmm, ICs for the aux block at t=0.001 are tricky. Let me start at t=0 properly.
    y0_3 = [0.0]*7 + [0.0, 1.0, 0.0, 0.0, 0.0]
    try:
        sol3 = solve_ivp(approach3_zerolized_exact, [0, T_MAX], y0_3,
                         t_eval=T_EVAL, rtol=1e-12, atol=1e-14, method='DOP853',
                         max_step=0.05)
        err3 = np.abs(sol3.y[11] - ZETA3)

        ax = axes[1, 1]
        ax.semilogy(sol3.t, np.maximum(err3, 1e-16), 'b-', linewidth=1)
        ax.set_title('Approach 3: Zerolized + IBP (exact C,D in drift)')
        ax.set_xlabel('t')
        ax.set_ylabel('|s̄₃(t) - ζ(3)|')
        ax.grid(True, alpha=0.3)
        ax.semilogy(sol3.t, np.exp(-sol3.t), 'r--', alpha=0.5, label='e^{-t}')
        ax.legend(fontsize=8)
    except Exception as e:
        print(f"Approach 3 failed: {e}")
        axes[1, 1].text(0.5, 0.5, f'Failed: {e}', transform=axes[1, 1].transAxes,
                        ha='center', fontsize=10)

    plt.tight_layout()
    plt.savefig('/Users/huangx/.openclaw/workspace/projects/Ripple/experiments/apery_convergence.png',
                dpi=150, bbox_inches='tight')
    print(f"Plot saved to experiments/apery_convergence.png")

    # Print convergence rates
    print("\n=== Convergence Rate Analysis ===")
    print(f"ζ(3) = {ZETA3:.15f}")

    for label, t_arr, err_arr in [
        ("Approach 1 (Fermi-Dirac)", sol1.t, err1),
        ("Approach 2b (Polylog cascade)", sol2.t, err2),
    ]:
        # Fit log(error) ~ -α·t + C
        mask = (err_arr > 1e-14) & (t_arr > 5)
        if mask.sum() > 10:
            log_err = np.log(np.maximum(err_arr[mask], 1e-16))
            t_fit = t_arr[mask]
            coeffs = np.polyfit(t_fit, log_err, 1)
            alpha = -coeffs[0]
            print(f"\n{label}:")
            print(f"  Fitted decay rate α ≈ {alpha:.4f}")
            print(f"  Error at t=10: {err_arr[np.argmin(np.abs(t_arr-10))]:.2e}")
            print(f"  Error at t=20: {err_arr[np.argmin(np.abs(t_arr-20))]:.2e}")
            if alpha > 0.5:
                print(f"  → FIRST FLOOR (exponential convergence)")
            else:
                print(f"  → NOT first floor")


if __name__ == '__main__':
    run_and_plot()
