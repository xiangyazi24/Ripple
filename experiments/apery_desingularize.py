"""
Desingularization of the Apéry ODE at x=0.

Strategy: The ODE x²(4+x)F''' + x(10+3x)F'' + (2+x)F' = 1
has a regular singular point at x=0. The analytic solution F satisfies
F(0)=0, F'(0)=1/2, F''(0)=-1/24.

The key observation: the quantity
  P(x) := 1 - (2+x)F'(x) - x(10+3x)F''(x) = x²(4+x)F'''(x)
vanishes to order x² along the analytic solution (verified numerically).

Approach: Change variables from (F, F', F'') to (F, F', R) where
  R := F'''  (directly tracking the third derivative)

Then the system becomes:
  x' = 1-x  (original time)
  dF/dt = F'·(1-x)
  d(F')/dt = F''·(1-x)
  d(F'')/dt = F'''·(1-x) = R·(1-x)

We need R' = dR/dx = F''''(x). Differentiate the ODE:
  d/dx[x²(4+x)F''' + x(10+3x)F'' + (2+x)F'] = d/dx[1] = 0

  [2x(4+x)+x²]F''' + x²(4+x)F'''' + [(10+3x)+x(10+3x)'+x(10+3x)]F'' + x(10+3x)F''' + [1+...]F' + (2+x)F'' = 0

Wait, let me do this more carefully.

ODE: A(x)F''' + B(x)F'' + C(x)F' = 1
where A=x²(4+x), B=x(10+3x), C=(2+x)

Differentiate:
  A'F''' + AF'''' + B'F'' + BF''' + C'F' + CF'' = 0
  AF'''' = -A'F''' - (B+...)F''' - B'F'' - CF'' - C'F'

  AF'''' = -(A'+B)F''' - (B'+C)F'' - C'F'

A' = 2x(4+x)+x² = 8x+3x²
B+A' = x(10+3x)+8x+3x² = 18x+6x²
B' = 10+6x
B'+C = 10+6x+2+x = 12+7x
C' = 1

So: x²(4+x)F'''' = -(18x+6x²)F''' - (12+7x)F'' - F'

F'''' = [-(18x+6x²)F''' - (12+7x)F'' - F'] / [x²(4+x)]

STILL has 1/x²! The fourth derivative has the same singularity structure.

But: does the numerator vanish to order x² here too? Let's check.

At x=0: numerator = -0·F'''(0) - 12·F''(0) - F'(0) = -12·(-1/24) - 1/2 = 1/2 - 1/2 = 0 ✓

At x=0, first order: d/dx[numerator] at x=0:
= -(18)F'''(0) - (18x+6x²)F''''(0)|_{x=0} - 7F''(0) - (12+7x)F'''(0)|_{x=0} - F''(0)
= -18·(1/90) - 0 - 7·(-1/24) - 12·(1/90) - (-1/24)
= -18/90 + 7/24 - 12/90 + 1/24
= -1/5 + 1/3 - 2/15 + 1/24
= (-48 + 80 - 32 + 10)/240 = 10/240 = 1/24 ≠ 0

So the numerator vanishes to order x¹ (not x²) at x=0.
That means F'''' ~ x/x² = 1/x → DIVERGES.

This is expected: F'''' involves log(x) terms from the Frobenius expansion,
even though F, F', F'', F''' are all bounded.

Wait — if F is ANALYTIC at x=0, then ALL its derivatives are bounded.
But F'''' as computed from the ODE involves 1/x² in the coefficient,
and the numerator only vanishes to order 1, not 2. This seems contradictory.

Resolution: the analytic solution has F'''' bounded (since F is analytic),
but the ODE for F'''' (obtained by differentiating the original ODE)
has a STRONGER singularity. The formula F'''' = [stuff]/x² is correct
for general solutions, but for the SPECIFIC analytic solution, the
numerator vanishes fast enough.

Actually wait, I showed the numerator vanishes to order 1, giving
F'''' ~ 1/x. That CAN'T be right for an analytic function.

Let me recheck. If F is analytic: F(x) = Σ a_n x^n,
F'''' = Σ n(n-1)(n-2)(n-3) a_n x^{n-4} starting from n=4.
F''''(0) = 24·a_4 = 24 · [(-1)³/(4³·C(8,4))] = 24 · (-1/4480) = -24/4480 = -3/560.

So F''''(0) = -3/560, which is finite. The formula F'''' = [stuff]/x² must
give the same finite value via L'Hôpital. Let me recompute the numerator.

The numerator for F'''': -(18x+6x²)R - (12+7x)F'' - F'
where R = F''' = [1-(2+x)F'-x(10+3x)F''] / [x²(4+x)]

Near x=0: R(0) = F'''(0) = 1/90.
Numerator = -0 - 12(-1/24) - 1/2 = 1/2 - 1/2 = 0 ✓ (order x⁰ vanishes)

First derivative of numerator at x=0:
d/dx[-(18x+6x²)R - (12+7x)F'' - F']|_{x=0}
= -18R(0) - 0 - 7F''(0) - 0·R'(0) - 12F'''(0) - F''(0)
= -18/90 - 7(-1/24) - 12/90 - (-1/24)
= -1/5 + 7/24 - 2/15 + 1/24
= -1/5 + 8/24 - 2/15
= -1/5 + 1/3 - 2/15
= (-3 + 5 - 2)/15 = 0/15 = 0 ✓

So the numerator DOES vanish to order x² (I made an arithmetic error before).
Let me verify: -3/15 + 5/15 - 2/15 = 0 ✓

This means F'''' is also bounded (as expected for an analytic function),
and we could define R₂ = F''''/1 and get a clean relation.

The PATTERN: each differentiation of the ODE produces a higher-order
equation with the SAME 1/x² singularity, but the analytic-solution
numerator vanishes to order x² each time (maintaining regularity).

This suggests a DIFFERENT approach to desingularization:
instead of tracking F'', track the REGULARIZED quantity directly.

ALTERNATIVE APPROACH: Power series ODE (track coefficients aₙ).

Since F(x) = Σ aₙ xⁿ with a₀=0, and the aₙ satisfy a recurrence,
we could design a PIVP that generates the aₙ and accumulates the sum.

The recurrence: 2(n+1)²(2n+1) a_{n+1} + n³ aₙ = 0
i.e., a_{n+1} = -n³/(2(n+1)²(2n+1)) · aₙ

For x₀ fixed (rational), F(x₀) = Σ aₙ x₀ⁿ.
Each summand bₙ := aₙ x₀ⁿ satisfies:
b_{n+1}/bₙ = x₀ · a_{n+1}/aₙ = -x₀ n³/(2(n+1)²(2n+1))

For large n: |b_{n+1}/bₙ| → x₀/4.
So Σbₙ converges like (x₀/4)^n — SUPER-exponentially for small x₀.

Can we turn this into a PIVP? The ratio involves n, which is a discrete
counter. In continuous time, n(t) → ∞ and bₙ follows the recurrence...

This is the "continuous embedding of discrete recurrence" problem.
One approach: use n = e^t or n = t (continuous counter) and define
b(t) such that b(n) = bₙ. The ODE for b would be:
  b'(t) = [ratio(t) - 1] · b(t) · something

But ratio(t) is a rational function of t, which is NOT polynomial.
For a PIVP, we can introduce auxiliary variables for 1/(t+1), 1/(2t+1), etc.

Actually, for a PIVP: we can compute 1/(t+c) via the ODE z' = -z², z(0)=1/c.
So we CAN make rational functions of t polynomial by adding variables.

Let me try a different, more concrete approach:

APPROACH: BOOTSTRAPPING PIVP
1. Run the main polynomial PIVP starting at x₀ with ZERO ICs
   (i.e., F(0)=G1(0)=G2(0)=0 at τ=0, with x(0)=x₀)
2. The "correct" ICs are (F₀, G1₀, G2₀)
3. Since amplification = 1, the output error equals the IC error
4. Add a CORRECTION block that COMPUTES the IC error and subtracts it

The IC error is:
  δF₀ = 0 - F(x₀) = -F(x₀)
  δG1₀ = 0 - F'(x₀) = -F'(x₀)
  δG2₀ = 0 - F''(x₀) = -F''(x₀)

Since amplification = 1 for F: output error ≈ -F(x₀)
The correct output is F(1) = (2/5)ζ(3)
Our output is ≈ F(1) - F(x₀) = F(1) - F(x₀)

So: ζ(3) = (5/2)[output + F(x₀)]

If we can compute F(x₀) from a SEPARATE PIVP and add it!

But computing F(x₀) from a PIVP IS the original problem...

UNLESS x₀ is chosen so that F(x₀) is a KNOWN number in R_RTCRN.
For instance, if there's a special x₀ where F(x₀) has a closed form
involving e, π, and algebraics...

The series F(x₀) = Σ (-1)^{n-1} x₀^n/(n³ C(2n,n)) at special values:
- F(0) = 0 ← trivial, but x=0 is the fixed point
- F(1) = (2/5)ζ(3) ← what we want
- F(4sin²θ) might have a closed form for special θ (hypergeometric identity)

Let me check F(1/4):
F(1/4) = Σ (-1)^{n-1}/(4^n n³ C(2n,n))
Using C(2n,n) ≈ 4^n/√(πn): F(1/4) ≈ Σ (-1)^{n-1}√(πn)/n³ → doesn't simplify.

This approach of finding a "magic" x₀ seems unlikely to work.

FINAL APPROACH: Accept starting at x₀ > 0, use two-phase PIVP.

Phase 1: Compute F(x₀), F'(x₀), F''(x₀) to high precision
Phase 2: Run the main PIVP using these as ICs

Both phases are polynomial PIVPs. The combined system runs in parallel:
Phase 1 converges to exact ICs, Phase 2 uses approximate ICs.
As τ→∞, Phase 1 error → 0, and Phase 2 output → (2/5)ζ(3) + IC_error.

Key: use a LOW-PASS FILTER to combine:
  output' = (Phase2_output + Phase1_correction) - output

If Phase2_output → (2/5)ζ(3) + δ and Phase1_correction → -δ (both exponentially),
then output → (2/5)ζ(3) exponentially.

But Phase 1 computing F(x₀) is exactly our original problem in a different form.

ACTUALLY — wait. F(x₀) for SMALL x₀ is dominated by the first term:
F(x₀) = x₀/2 + O(x₀²). For x₀ = 1/100:
F(0.01) = 0.005 - 0.000000208 + ... ≈ 0.004998 (essentially 0.01/2 = 0.005)

What if we use F(x₀) ≈ Σ_{n=1}^N aₙ x₀ⁿ with small N?
Each partial sum IS rational. For N=1: F ≈ x₀/2 (error ~ x₀²/48)
For x₀=0.01, N=1: error ~ 10⁻⁴/48 ≈ 2×10⁻⁶.

The output error would then be 2×10⁻⁶ (amplification 1).
For more precision, use more terms. N=2: error ~ x₀³/540 ≈ 2×10⁻⁹.

So: with x₀ = 1/M (M large integer) and N-term partial sums as ICs,
the output error is O(1/(4M)^N). This is exponentially small in N.

For a SINGLE PIVP computing ζ(3) to arbitrary precision:
set M = 100, N = 5, get error < 10⁻¹³.
The ICs are exact rationals (finite sums of rational terms).

This gives a CONCRETE PIVP with EXACT RATIONAL ICs computing
a number within 10⁻¹³ of (2/5)ζ(3). Multiply by 5/2 to get ζ(3).

For EXACT computation (not approximate), we'd need N → ∞.
But for any FINITE precision, N is finite and the ICs are rational.

CONCLUSION: ζ(3) is in the CLOSURE of {polynomial-PIVP-computable numbers
with rational ICs}, but whether it's IN the set (rather than just a limit
point) depends on the regularization question.
"""

import numpy as np
from scipy.integrate import solve_ivp
from scipy.special import zeta, comb
from fractions import Fraction
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt

ZETA3 = float(zeta(3))
TARGET = (2.0/5.0) * ZETA3


def exact_rational_ics(x0_frac, N_terms):
    """Compute EXACT RATIONAL ICs using N_terms of the power series.

    x0_frac: Fraction (rational x₀)
    N_terms: how many series terms to include
    Returns (F, F', F'') as Fractions.
    """
    F = Fraction(0)
    Fp = Fraction(0)
    Fpp = Fraction(0)

    for n in range(1, N_terms + 1):
        # a_n = (-1)^{n-1} / (n³ · C(2n,n))
        sign = 1 if n % 2 == 1 else -1
        cn_num = sign
        cn_den = n**3 * int(comb(2*n, n, exact=True))
        a_n = Fraction(cn_num, cn_den)

        # F += a_n · x₀^n
        xn = x0_frac ** n
        F += a_n * xn

        # F' += n · a_n · x₀^{n-1}
        Fp += a_n * n * x0_frac ** (n-1)

        # F'' += n(n-1) · a_n · x₀^{n-2}
        if n >= 2:
            Fpp += a_n * n * (n-1) * x0_frac ** (n-2)

    return F, Fp, Fpp


def pivp_polynomial(tau, y):
    """The polynomial PIVP."""
    x, F, G1, G2 = y
    h = x**2 * (4 + x) * (1 - x)
    return [h, G1*h, G2*h, (1-x)*(1.0 - (10*x+3*x**2)*G2 - (2+x)*G1)]


def run():
    print("="*70)
    print("EXACT RATIONAL IC CONSTRUCTION FOR ζ(3)")
    print("="*70)

    x0 = Fraction(1, 100)  # x₀ = 0.01

    print(f"\nx₀ = {x0} = {float(x0)}")
    print(f"\n--- Rational ICs for different N ---")

    results = []
    for N in [1, 2, 3, 4, 5, 10, 15, 20]:
        F_rat, Fp_rat, Fpp_rat = exact_rational_ics(x0, N)

        # Convert to float for ODE integration
        F0 = float(F_rat)
        G10 = float(Fp_rat)
        G20 = float(Fpp_rat)

        # Run PIVP
        sol = solve_ivp(pivp_polynomial, [0, 300.0],
                        [float(x0), F0, G10, G20],
                        rtol=1e-14, atol=1e-16, method='DOP853')

        F_final = sol.y[1, -1]
        zeta3_approx = (5.0/2.0) * F_final
        err = abs(zeta3_approx - ZETA3)

        # Series tail bound: |error in F(x₀)| ≤ |a_{N+1}| x₀^{N+1} / (1 - x₀/4)
        a_N1 = 1.0 / ((N+1)**3 * comb(2*(N+1), N+1, exact=True))
        tail_bound = a_N1 * float(x0)**(N+1) / (1 - float(x0)/4)

        print(f"  N={N:2d}: IC tail bound ≤ {tail_bound:.2e}, "
              f"ζ(3) error = {err:.2e}")
        print(f"       F₀ = {F_rat} ≈ {F0:.15e}")
        results.append((N, tail_bound, err))

    print(f"\n--- Verification ---")
    print(f"ζ(3) = {ZETA3:.15f}")

    # Best result
    N = 20
    F_rat, Fp_rat, Fpp_rat = exact_rational_ics(x0, N)
    sol = solve_ivp(pivp_polynomial, [0, 300.0],
                    [float(x0), float(F_rat), float(Fp_rat), float(Fpp_rat)],
                    rtol=1e-14, atol=1e-16, method='DOP853')
    best = (5.0/2.0) * sol.y[1, -1]
    print(f"Best (N=20): {best:.15f}, error = {abs(best-ZETA3):.2e}")

    # Plot
    fig, axes = plt.subplots(1, 2, figsize=(14, 5))
    fig.suptitle('Exact Rational ICs: N-term Partial Sum → ζ(3) Precision', fontsize=14)

    Ns = [r[0] for r in results]
    tails = [r[1] for r in results]
    errs = [r[2] for r in results]

    ax = axes[0]
    ax.semilogy(Ns, tails, 'bs-', lw=1.5, label='IC tail bound')
    ax.semilogy(Ns, errs, 'ro-', lw=1.5, label='Actual ζ(3) error')
    ax.set_xlabel('N (series terms for ICs)')
    ax.set_ylabel('Error')
    ax.set_title('IC precision → output precision')
    ax.legend(); ax.grid(True, alpha=0.3)

    # Convergence for best N
    t_eval = np.linspace(0, 300, 5000)
    sol_best = solve_ivp(pivp_polynomial, [0, 300.0],
                         [float(x0), float(F_rat), float(Fp_rat), float(Fpp_rat)],
                         t_eval=t_eval, rtol=1e-14, atol=1e-16, method='DOP853')
    err_t = np.abs((5.0/2.0)*sol_best.y[1] - ZETA3)

    ax = axes[1]
    ax.semilogy(sol_best.t, np.maximum(err_t, 1e-16), 'b-', lw=1.5)
    ax.set_xlabel('τ (rescaled time)')
    ax.set_ylabel('|output - ζ(3)|')
    ax.set_title(f'Convergence with N={N} rational ICs')
    ax.grid(True, alpha=0.3)

    plt.tight_layout()
    outpath = '/Users/huangx/.openclaw/workspace/projects/Ripple/experiments/apery_desingularize.png'
    plt.savefig(outpath, dpi=150, bbox_inches='tight')
    print(f"\nPlot saved to {outpath}")

    # Grand summary
    print(f"\n{'='*70}")
    print("DESINGULARIZATION SUMMARY")
    print(f"{'='*70}")
    print(f"""
For any precision target 2^{{-r}}, we can construct a CONCRETE polynomial PIVP:

  x'  = 4x² − 3x³ − x⁴
  F'  = G1·(4x² − 3x³ − x⁴)
  G1' = G2·(4x² − 3x³ − x⁴)
  G2' = (1−x)[1 − (10x+3x²)G2 − (2+x)G1]

with x₀ = 1/100 and rational ICs computed from N ≈ {int(np.ceil(np.log(2)*1/np.log(400)))+1}·r series terms.

The ICs are EXACT rationals (finite sums). The PIVP output converges
exponentially to a value within 2^{{-r}} of (2/5)ζ(3).

IMPLICATION: ζ(3) is a limit of polynomial-PIVP-computable numbers.
For EACH precision r, there is a PIVP with rational ICs computing ζ(3) ± 2^{{-r}}.
The PIVP itself (polynomial, ICs) is finitely describable for each r.

This is STRONGER than "ζ(3) is computable" (which just requires an algorithm)
but WEAKER than "ζ(3) ∈ R_RTCRN" (which requires a SINGLE fixed PIVP).
""")


if __name__ == '__main__':
    run()
