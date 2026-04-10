"""
Test composite ODE system for ζ(3) with ALL constants computed dynamically.

Key question: does the combined system still converge exponentially (first floor)?

Three sub-experiments:
A. Polylog cascade with EXACT constants (baseline — confirmed first floor)
B. Polylog cascade with DYNAMIC ln(2) and π²/12 (from auxiliary ODEs)
C. Zerolized Apéry system with DYNAMIC C=1/(e-1), D=e/(e-1)
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


# ================================================================
# System A: Polylog cascade with exact constants (baseline)
# ================================================================
def system_A(t, y):
    S1, S2, S3, u = y
    dS1 = u / (1.0 + u)
    dS2 = np.log(2) - S1
    dS3 = np.pi**2 / 12.0 - S2
    du = -u
    return [dS1, dS2, dS3, du]


# ================================================================
# System B: Polylog cascade with dynamic constants
#
# We need ln(2) and π²/12 as dynamic variables.
#
# ln(2): computed by L' = u/(1+u), L(0)=0, L(∞)=ln(2)
#   (this is the SAME ODE as S₁, so L = S₁)
#
# Since S₂' needs (ln(2) - S₁) = ln(1+e^{-t}), and we can't
# directly get ln(1+e^{-t}) as a polynomial in state variables,
# we use the TRACKING FILTER approach from RTCRN2 Lemma 3.
#
# But the cascade S₂ is a pure integrator, not a tracking filter.
# The correct approach: restructure using the fact that
#   S₂(t) = ∫₀^t ln(1+e^{-s}) ds
# and express ln(1+e^{-s}) via bounded variables.
#
# Key identity: if w = 1/(1+u), then ln(1+u) = ∫₀^u 1/(1+x) dx.
# We can track ∫₀^t 1/(1+u(s)) ds = ∫₀^t (1+u)^{-1} ds.
# Since (1+u)^{-1} is rational in u, this IS a polynomial ODE!
#
# Wait: ∫₀^t 1/(1+e^{-s}) ds = t + ln(1+e^{-t}) - ln(2)
# (by direct computation). That doesn't give us what we want.
#
# Alternative approach: track ln(1+u) via its ODE.
# L = ln(1+u), L(0) = ln(2). Not zero IC.
#
# Different idea: use the RECIPROCAL to avoid ln.
# From RTCRN2 Lemma 4: x' = 1 - f(t)·x where f→α gives x→1/α.
#
# For ln(2): we know e^{ln(2)} = 2.
# If we have a variable E → e and a tracking variable for 1/E → 1/e,
# then 2/E → 2/e, and ln(2) = ... no, this doesn't help directly.
#
# SIMPLEST APPROACH: Use the fact that the integrand of S₂ is
# g(t) = ln(1+e^{-t}), which can be decomposed as:
#
# g(t) = ∫₀^{e^{-t}} 1/(1+x) dx
#
# In an ODE framework, we can track this by expanding ln(1+u):
# ln(1+u) = u - u²/2 + u³/3 - ... for |u| ≤ 1.
# Since u = e^{-t} ∈ (0,1], this converges.
#
# But a truncated series gives a WRONG limit.
#
# THE REAL SOLUTION: Don't use the polylog cascade.
# Instead, use the DIRECT Fermi-Dirac integral approach
# with auxiliary ODEs for the t² factor.
#
# OR: Use a TRACKING FILTER (Lemma 3) to track the running
# integral. If φ(t) → η(2) exponentially, then
# X' = φ(t) - X gives X → η(2) exponentially.
#
# We ALREADY HAVE φ(t) = S₂(t) converging to η(2).
# So S₂ itself IS the variable that converges to π²/12.
# The question is just: does it converge EXPONENTIALLY?
#
# From the exact-constant analysis: YES, S₂(t) → η(2) exponentially.
#
# The problem is only when we REPLACE the constant with a variable.
#
# KEY INSIGHT: We don't actually need to replace constants with variables
# in the CASCADE if we restructure. The cascade
#   S₁' = u/(1+u)    → ln(2)
#   S₂' = ln(2) - S₁ → π²/12
# is EQUIVALENT to just integrating ln(1+e^{-t}) dt.
# The "constant" ln(2) doesn't appear if we write it as:
#   S₂' = ln(1+e^{-t})
#
# And ln(1+e^{-t}) = ln(1+u). We need this as a state.
# L' = -u/(1+u), L(0) = ln(2). Non-trivial IC.
#
# ALTERNATIVELY: define M(t) = S₁(∞) - S₁(t) = ln(1+e^{-t}).
# But we can't compute S₁(∞) without knowing ln(2).
#
# ALTERNATIVE ALTERNATIVE: use the SUBSTITUTION directly.
# Instead of using the polylog cascade, directly formulate:
#   η(3) = ∫₀^∞ ∫₀^∞ ∫₀^∞ [u₁/(1+u₁)] · [u₂/(1+u₂)] · [u₃/(1+u₃)] du₁ du₂ du₃ ... no.
#
# OK let me try a completely different strategy.
# ================================================================


# ================================================================
# System B: Direct nested integration for η(3)
#
# η(3) = Σ_{k≥1} (-1)^{k+1}/k³ = (3/4)ζ(3)
#
# Consider the integral:
# η(3) = ∫₀^∞ ∫₀^∞ ∫₀^∞ e^{-(s₁+s₂+s₃)} / (1+e^{-(s₁+s₂+s₃)}) ds₃ ds₂ ds₁
#       = ∫₀^∞ ∫₀^∞ [-ln(1+e^{-(s₁+s₂+T)}) + ln(1+e^{-(s₁+s₂)})]|_{T=∞} ds₂ ds₁
#
# This is getting messy. Let me try something simpler.
#
# η(n) = (1/Γ(n)) ∫₀^∞ t^{n-1}/(e^t+1) dt
# η(3) = (1/2) ∫₀^∞ t²/(e^t+1) dt
#
# This has the t² issue again.
#
# COMPLETELY DIFFERENT APPROACH: Use the series directly with a CRN.
# Σ 1/k³ = 1 + 1/8 + 1/27 + ...
#
# For each k, compute 1/k³ via repeated reciprocal.
# Sum them via addition CRN.
# The tail Σ_{k>N} 1/k³ ~ 1/(2N²) (integral test).
# With N = e^t species, the tail decays exponentially.
#
# But we'd need e^t species — not finite!
#
# FINAL APPROACH that might work:
# Use the ZEROLIZED Apéry construction (Approach 3).
# It converges to ζ(3) WITHOUT needing transcendental constants
# as ODE coefficients, BECAUSE:
# - The main block uses EXACT constants C, D in the drift
# - BUT the IBP compensation replaces C with E₂(t)
# - The auxiliary block E₂(t) → C with zero IC
# - The t·E₂' term handles the bias
#
# Let me test this more carefully.
# ================================================================


# ================================================================
# System C: Fully dynamic zerolized Apéry system
#
# ALL constants (C, D) are computed by auxiliary ODEs.
# No transcendental constants appear anywhere.
# ================================================================

def system_C_fully_dynamic(t, y):
    """Fully dynamic: C and D replaced by E₂ and E₃ from aux block.

    Auxiliary block (all zero IC except E₁(0)=1):
      E'   = 1 - E              → 1          [exponential]
      E₁'  = E₁·(1-E)          → e          [exponential]
      E₂'  = 1 - (E₁-1)·E₂    → 1/(e-1)=C  [exponential]
      E₃'  = E₁·E₂ - E₃       → e/(e-1)=D  [exponential]

    Main block (zerolized with DYNAMIC C→E₂, D→E₃):
      v̇  = -(v+E₁)·(u1+E₂)·(v+E₁-1)
      u̇₁ = (u1+E₂)·((v+E₁)·(u1+E₂) - 1)
      u̇₂ = (u2+E₂)·((v+E₁)·(u1+E₂) - 2)
      u̇₃ = (u3+E₂)·((v+E₁)·(u1+E₂) - 3)
      ṙ  = -(r+E₃)·(r+E₂)
      ẇ₁ = (r+E₂) - (r+E₃)·(w1+E₂)
      ẇ₂ = 2·(w1+E₂) - (r+E₃)·(w2+E₂)

    IBP target:
      s̄₃' = (1/2)(u3 + w2) + E₂ + t·E₂'

    But t is unbounded! The term t·E₂' needs special handling.
    E₂' = 1 - (E₁-1)·E₂
    t·E₂' → 0 (since E₂' → 0 exponentially and t grows polynomially)

    To avoid tracking t explicitly, use the identity:
    Define Φ(t) = t·E₂(t) - ∫₀^t E₂(s) ds
    Then Φ' = E₂ + t·E₂' - E₂ = t·E₂'
    And the integral ∫₀^t E₂(s) ds can be tracked by another variable I₂.
    So Φ = t·E₂ - I₂, and Φ' = t·E₂' = E₂ + t·E₂' - E₂ = Φ' ... circular.

    Better: define I₂' = E₂ (accumulates ∫E₂ dt) and tE₂' = t·E₂' = E₂ + t·E₂' - E₂
    Use: d/dt(t·E₂) = E₂ + t·E₂'
    So define P = t·E₂. Then P' = E₂ + t·E₂'. And t·E₂' = P' - E₂.

    But P = t·E₂ is unbounded!

    Instead: just track the integral directly.
    s̄₃' = (1/2)(u3+w2) + E₂ + t·E₂'
    = (1/2)(u3+w2) + E₂ + t·(1 - (E₁-1)·E₂)
    = (1/2)(u3+w2) + E₂ + t - t·(E₁-1)·E₂

    t appears explicitly. We need to track the INTEGRAL of this,
    not the derivative. The contribution from the "t·E₂'" part:

    ∫₀^T t·E₂'(t) dt = [t·E₂(t)]₀^T - ∫₀^T E₂(t) dt = T·E₂(T) - ∫₀^T E₂(t) dt

    As T→∞: T·E₂(T) → ∞ (since E₂→C). And ∫₀^T E₂ dt → ∞.
    BUT: T·E₂(T) - ∫₀^T E₂(t) dt = T·C + o(1) - (T·C + δ + o(1)) = -δ + o(1)
    where δ = ∫₀^∞ (C - E₂(t)) dt is a finite constant.

    So ∫₀^∞ t·E₂'(t) dt converges! And equals -∫₀^∞ (C-E₂(t)) dt (by IBP).

    To avoid tracking t, define:
    Q' = E₂ [accumulates ∫E₂ dt]
    Then the contribution from t·E₂' to s̄₃ is:
    ∫₀^t s·E₂'(s) ds = t·E₂(t) - Q(t) ... still need t.

    Fundamental issue: t·E₂' involves t explicitly.

    WORKAROUND: use s̄₃ differently. Instead of using the IBP form,
    go back to the original target with the DYNAMIC zerolization.

    Original target (without IBP):
    s₃' = (1/2)(u₃+w₂) + C
    where u₃, w₂ are from the main block.

    In the fully dynamic version:
    s₃' = (1/2)(u₃+w₂) + E₂

    Limit: s₃(∞) = ∫₀^∞ [(1/2)(u₃+w₂) + E₂] dt

    With exact C: ∫₀^∞ [(1/2)(u₃+w₂) + C] dt = ζ(3)
    With dynamic E₂: ∫₀^∞ [(1/2)(u₃+w₂) + E₂] dt = ζ(3) - ∫₀^∞ (C-E₂) dt

    So the error is δ = ∫₀^∞ (C-E₂(t)) dt, a finite constant.
    This is exactly the bias that the IBP compensation was supposed to fix!

    The IBP trick: s̄₃ = s₃ - ∫₀^t (C-E₂(s)) ds ≈ s₃ - ∫₀^t (C-E₂(s)) ds
    but we can't compute ∫(C-E₂) without knowing C.

    HOWEVER: ∫₀^t (C-E₂(s)) ds = C·t - Q(t) where Q' = E₂.
    And C·t is unbounded.

    The IBP compensation paper uses:
    s̄₃ = s₃ - t·(C-E₂(t)) - ∫₀^t (... higher order ...)

    OK this is getting deep into the weeds. Let me just test NUMERICALLY:
    1. The simple dynamic version (E₂ replacing C, no IBP) — expect wrong limit
    2. The IBP version (using t explicitly) — expect correct limit
    """

    # y = [v, u1, u2, u3, r, w1, w2, E, E1, E2, E3, s3_simple, s3_ibp_accum]
    v, u1, u2, u3, r, w1, w2, E, E1, E2, E3, s3_simple, I_E2 = y

    # Auxiliary block
    dE  = 1.0 - E
    dE1 = E1 * (1.0 - E)
    dE2 = 1.0 - max(E1 - 1.0, 0.0) * E2  # clamp E1-1 ≥ 0 for stability
    dE3 = E1 * E2 - E3

    # Main block with DYNAMIC constants
    vu1_product = (v + E1) * (u1 + E2)
    dv  = -(v + E1) * (u1 + E2) * (v + E1 - 1.0)
    du1 = (u1 + E2) * (vu1_product - 1.0)
    du2 = (u2 + E2) * (vu1_product - 2.0)
    du3 = (u3 + E2) * (vu1_product - 3.0)
    dr  = -(r + E3) * (r + E2)
    dw1 = (r + E2) - (r + E3) * (w1 + E2)
    dw2 = 2.0 * (w1 + E2) - (r + E3) * (w2 + E2)

    # Simple target (no IBP): s₃' = (1/2)(u3+w2) + E₂
    ds3_simple = 0.5 * (u3 + w2) + E2

    # Track ∫E₂(t)dt for IBP analysis
    dI_E2 = E2

    return [dv, du1, du2, du3, dr, dw1, dw2,
            dE, dE1, dE2, dE3, ds3_simple, dI_E2]


def system_C_exact_constants(t, y):
    """Same main block but with EXACT C, D constants (for comparison)."""
    v, u1, u2, u3, r, w1, w2, E, E1, E2, E3, s3, I_E2 = y

    e_val = np.e
    C_exact = 1.0 / (e_val - 1.0)
    D_exact = e_val / (e_val - 1.0)

    # Auxiliary block (still runs, for tracking)
    dE  = 1.0 - E
    dE1 = E1 * (1.0 - E)
    dE2 = 1.0 - max(E1 - 1.0, 0.0) * E2
    dE3 = E1 * E2 - E3

    # Main block with EXACT constants
    vu1_product = (v + e_val) * (u1 + C_exact)
    dv  = -(v + e_val) * (u1 + C_exact) * (v + e_val - 1.0)
    du1 = (u1 + C_exact) * (vu1_product - 1.0)
    du2 = (u2 + C_exact) * (vu1_product - 2.0)
    du3 = (u3 + C_exact) * (vu1_product - 3.0)
    dr  = -(r + D_exact) * (r + C_exact)
    dw1 = (r + C_exact) - (r + D_exact) * (w1 + C_exact)
    dw2 = 2.0 * (w1 + C_exact) - (r + D_exact) * (w2 + C_exact)

    # Target: s₃' = (1/2)(u3+w2) + C (exact)
    ds3 = 0.5 * (u3 + w2) + C_exact
    dI_E2 = E2

    return [dv, du1, du2, du3, dr, dw1, dw2,
            dE, dE1, dE2, dE3, ds3, dI_E2]


def run_experiments():
    fig, axes = plt.subplots(2, 2, figsize=(14, 10))
    fig.suptitle(f'ζ(3) = {ZETA3:.10f}: Composite System Convergence', fontsize=14)

    # --- System A: Polylog cascade exact (baseline) ---
    print("System A: Polylog cascade (exact constants)...")
    sol_A = solve_ivp(system_A, [0, T_MAX], [0.0, 0.0, 0.0, 1.0],
                      t_eval=T_EVAL, rtol=1e-13, atol=1e-15, method='DOP853')
    out_A = (4.0/3.0) * sol_A.y[2]
    err_A = np.abs(out_A - ZETA3)

    ax = axes[0, 0]
    ax.semilogy(sol_A.t, np.maximum(err_A, 1e-16), 'b-', lw=1.5, label='cascade (exact)')
    ax.semilogy(sol_A.t, np.exp(-sol_A.t), 'r--', alpha=0.4, label='e^{-t}')
    ax.set_title('A: Polylog cascade (exact ln2, π²/12)')
    ax.set_xlabel('t'); ax.set_ylabel('|output - ζ(3)|')
    ax.legend(fontsize=8); ax.grid(True, alpha=0.3)

    # --- System C (exact constants): Zerolized Apéry ---
    print("System C (exact): Zerolized Apéry with exact C, D...")
    y0 = [0.0]*7 + [0.0, 1.0, 0.0, 0.0] + [0.0, 0.0]
    try:
        sol_Ce = solve_ivp(system_C_exact_constants, [0, T_MAX], y0,
                           t_eval=T_EVAL, rtol=1e-12, atol=1e-14,
                           method='DOP853', max_step=0.05)
        err_Ce = np.abs(sol_Ce.y[11] - ZETA3)

        ax = axes[0, 1]
        ax.semilogy(sol_Ce.t, np.maximum(err_Ce, 1e-16), 'b-', lw=1.5)
        ax.semilogy(sol_Ce.t, np.exp(-sol_Ce.t), 'r--', alpha=0.4, label='e^{-t}')
        ax.set_title('C (exact): Zerolized Apéry, exact C/D in drift')
        ax.set_xlabel('t'); ax.set_ylabel('|s₃(t) - ζ(3)|')
        ax.legend(fontsize=8); ax.grid(True, alpha=0.3)

        print(f"  s₃(T_MAX) = {sol_Ce.y[11][-1]:.12f}")
        print(f"  Error = {err_Ce[-1]:.2e}")
    except Exception as ex:
        print(f"  Failed: {ex}")
        axes[0, 1].text(0.5, 0.5, f'Failed: {ex}', transform=axes[0, 1].transAxes, ha='center')

    # --- System C (dynamic): Fully dynamic ---
    print("System C (dynamic): Fully dynamic E₂→C, E₃→D...")
    try:
        sol_Cd = solve_ivp(system_C_fully_dynamic, [0, T_MAX], y0,
                           t_eval=T_EVAL, rtol=1e-12, atol=1e-14,
                           method='DOP853', max_step=0.05)
        s3_dynamic = sol_Cd.y[11]
        err_Cd = np.abs(s3_dynamic - ZETA3)

        # Also compute IBP-corrected version:
        # s̄₃ ≈ s₃ + correction
        # The correction ≈ -∫₀^∞ (C-E₂) dt ≈ -(C·t - ∫E₂ dt) at large t
        # But this diverges. The IBP correction is:
        # ∫₀^t s·E₂' ds = t·E₂(t) - ∫₀^t E₂(s) ds
        # s̄₃ = s₃ + (t·E₂(t) - I_E₂(t)) — but t·E₂ is available from t and E₂.
        # ... Except we can't track t in a bounded system.

        C_exact = 1.0 / (np.e - 1.0)
        delta = C_exact * sol_Cd.t - sol_Cd.y[12]  # ≈ ∫(C-E₂)dt
        s3_corrected = s3_dynamic + delta  # Add back what was lost
        # Actually: s₃(dynamic) ≈ ζ(3) - δ∞ where δ∞ = ∫₀^∞(C-E₂)dt
        # So s₃ + ∫₀^t(C-E₂)ds should → ζ(3) if we knew C.
        # We don't know C, so this correction uses the exact C (cheating).

        ax = axes[1, 0]
        ax.semilogy(sol_Cd.t, np.maximum(err_Cd, 1e-16), 'b-', lw=1.5, label='simple (no IBP)')
        ax.semilogy(sol_Cd.t, np.exp(-sol_Cd.t), 'r--', alpha=0.4, label='e^{-t}')
        ax.set_title('C (dynamic): E₂→C, E₃→D (no IBP)')
        ax.set_xlabel('t'); ax.set_ylabel('|s₃(t) - ζ(3)|')
        ax.legend(fontsize=8); ax.grid(True, alpha=0.3)

        # What does s₃ converge to?
        print(f"  s₃(T_MAX) = {s3_dynamic[-1]:.12f}")
        print(f"  Target ζ(3) = {ZETA3:.12f}")
        print(f"  Bias = {s3_dynamic[-1] - ZETA3:.6e}")
        print(f"  ∫₀^T(C-E₂)dt at T_MAX ≈ {delta[-1]:.6e}")

    except Exception as ex:
        print(f"  Failed: {ex}")
        axes[1, 0].text(0.5, 0.5, f'Failed: {ex}', transform=axes[1, 0].transAxes, ha='center')

    # --- Analysis: convergence rate comparison ---
    ax = axes[1, 1]
    ax.semilogy(sol_A.t, np.maximum(err_A, 1e-16), 'b-', lw=1.5, label='A: cascade (exact)')
    try:
        ax.semilogy(sol_Ce.t, np.maximum(err_Ce, 1e-16), 'g-', lw=1.5, label='C: exact C,D')
        ax.semilogy(sol_Cd.t, np.maximum(err_Cd, 1e-16), 'm-', lw=1.5, label='C: dynamic (no IBP)')
    except:
        pass
    ax.semilogy(T_EVAL, np.exp(-T_EVAL), 'r--', alpha=0.4, label='e^{-t}')
    ax.set_title('All approaches compared')
    ax.set_xlabel('t'); ax.set_ylabel('Error')
    ax.legend(fontsize=8); ax.grid(True, alpha=0.3)

    plt.tight_layout()
    plt.savefig('/Users/huangx/.openclaw/workspace/projects/Ripple/experiments/apery_composite.png',
                dpi=150, bbox_inches='tight')
    print("\nPlot saved.")

    # Convergence rate fitting
    print("\n=== Convergence Rate Fitting ===")
    for label, t_arr, err_arr in [
        ("A: cascade exact", sol_A.t, err_A),
    ]:
        mask = (err_arr > 1e-14) & (t_arr > 5)
        if mask.sum() > 10:
            coeffs = np.polyfit(t_arr[mask], np.log(np.maximum(err_arr[mask], 1e-16)), 1)
            print(f"{label}: α ≈ {-coeffs[0]:.4f}")

    try:
        for label, t_arr, err_arr in [
            ("C: exact C,D", sol_Ce.t, err_Ce),
            ("C: dynamic", sol_Cd.t, err_Cd),
        ]:
            mask = (err_arr > 1e-10) & (t_arr > 3) & (t_arr < T_MAX - 1)
            if mask.sum() > 10:
                coeffs = np.polyfit(t_arr[mask], np.log(np.maximum(err_arr[mask], 1e-16)), 1)
                print(f"{label}: α ≈ {-coeffs[0]:.4f}")
            else:
                t10 = err_arr[np.argmin(np.abs(t_arr - 10))]
                t20 = err_arr[np.argmin(np.abs(t_arr - 20))]
                print(f"{label}: err@10={t10:.2e}, err@20={t20:.2e}")
    except:
        pass


if __name__ == '__main__':
    run_experiments()
