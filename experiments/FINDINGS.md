# ζ(3) First-Floor Computability: Summary of Findings

**Date:** 2026-04-07  
**Status:** Obstacle identified — likely OPEN PROBLEM

## What We Proved (Numerically)

1. **ζ(3) has first-floor convergence** when the ODE system has exact
   transcendental coefficients:
   - Polylog cascade (needs ln(2), π²/12 as coefficients): α ≈ 1.0
   - Zerolized Apéry (needs e, 1/(e-1) in drift): α ≈ 0.89

2. **All attempts to dynamicalize the constants fail:**
   - Direct substitution E₂→C, E₃→D: wrong limit (3.53)
   - IBP compensation (t·E₂'): still wrong limit (3.18)
   - Tracking filter cascade: wrong limit (0.92)

## Why Dynamic Replacement Fails

The core issue: the polylog cascade and Apéry ODEs use **pure integrators**
(S' = f(t), no self-correction term). In a pure integrator, any constant
offset in the input accumulates forever:

  S(∞) = ∫₀^∞ f(s) ds + ∫₀^∞ ε(s) ds

Even if ε(s) → 0 exponentially, the integral ∫ε ds is a finite nonzero
constant (the "bias"). This bias shifts the limit permanently.

The RTCRN2 tracking filter (x' = f(t) - x) adds self-correction and
DOES preserve limits. But the cascade CANNOT be reformulated as tracking
filters because the cascade is computing INTEGRALS, not LIMITS.

## The Fundamental Question

**Is ζ(3) ∈ R_RTCRN?**

R_RTCRN requires:
- Integer rate constants
- All species initialized to 0
- Bounded concentrations
- Exponential convergence (|x(t) - α| ≤ 2^{-t})

R_RTCRN is a subfield of ℝ containing all algebraic numbers, e, and π.
But it is NOT known whether ζ(3) ∈ R_RTCRN.

This question is likely **open** and connected to:
- Whether ζ(3) has a closed form in terms of e and π (unknown)
- The transcendence theory of ζ(3) (Apéry proved irrationality in 1978;
  algebraic independence from π is unknown)

## BREAKTHROUGH: Apéry Generating Function Approach (2026-04-09)

### The Key Idea

The Apéry accelerated series F(x) = Σ (-1)^{n-1}/(n³ C(2n,n)) xⁿ satisfies:

  x²(4+x) F''' + x(10+3x) F'' + (2+x) F' = 1

- **All integer coefficients** ✓
- **Rational ICs**: F(0)=0, F'(0)=1/2, F''(0)=-1/24 ✓
- **F(1) = (2/5)ζ(3)** (x=1 within radius of convergence 4) ✓
- Via x = 1−e^{−t}: convergence rate **α ≈ 1.0** (FIRST FLOOR) ✓

### The Polynomial PIVP

Time-rescaling by x²(4+x) gives a fully polynomial system:

  x'  = 4x² − 3x³ − x⁴
  F'  = G1·x²(4+x)(1−x)
  G1' = G2·x²(4+x)(1−x)
  G2' = (1−x)[1 − (10x+3x²)G2 − (2+x)G1]

- Output: ζ(3) = (5/2)·lim F(τ)
- Convergence: α ≈ 0.05 in rescaled time (still first floor: μ(r) = O(r))
- IC sensitivity: amplification = 1.0 (perfectly conditioned)

### Zero-IC Canonical Form (DNA25 Theorem 3 technique)

For each precision target r, the PIVP can be converted to **canonical form**:
- **Zero initial conditions** ŷ(0) = 0
- **Integer polynomial coefficients** (after LCD clearing)
- **Degree ≤ 4**, dimension 4

Technique (from RTCRN2 paper, Theorem 3, generalized to ℚ):
1. Fix x₀ ∈ (0,1)∩ℚ, N terms → rational ICs c ∈ ℚ⁴
2. Shift: ŷ = y − c → zero ICs
3. Expand p(ŷ+c) → rational coefficients
4. Multiply RHS by LCD M → integer coefficients (time rescaling)

Results (x₀ = 1/2):
| N  | IC tail bound | |output−ζ(3)| | LCD digits |
|----|---------------|---------------|------------|
| 5  | 8.6e-8        | 2.6e-6        | 8          |
| 10 | 5.8e-13       | 4.8e-11       | 18         |
| 15 | 6.9e-18       | <1e-14        | 27         |

Each approximant α_r = (5/2)(F̂(∞)+c₂) ∈ R_RTCRN by field closure.
So ζ(3) = lim α_r with α_r ∈ R_RTCRN and |α_r−ζ(3)| ≤ 2^{-r}.

### Remaining Gap

x = 0 is a **fixed point** of the rescaled system (all derivatives vanish).
Must start at x₀ > 0 with series-derived ICs, which are NOT exactly rational.
The singularity is **removable** (G₂'(0) = 19/720, finite), but the quotient
[1−(2+x)G₁−(10x+3x²)G₂]/x² resists polynomial reformulation (infinite regress
of 1/x factors when introducing auxiliary variables).

Open question: **can the regular singular point at x = 0 be regularized
into a single polynomial PIVP?** Equivalently: **is ζ(3) ∈ R_RTCRN?**

### Experiments

- `apery_genfun.py` — Generating function ODE verification + convergence
- `apery_pivp.py` — Polynomial PIVP analysis, IC sensitivity
- `apery_regularize.py` — Regularization attempts (R = P/x², time rescaling)
- `apery_desingularize.py` — Exact rational IC construction (Fraction arithmetic)
- `apery_continuized.py` — Continuized series attempt (FAILED)
- `apery_zero_ic.py` — Zero-IC canonical form (Theorem 3 technique)

## Earlier Attempts (still relevant)

### A. Polylog cascade (exact constants)
- Works perfectly (α ≈ 1.0) but needs ln(2), π²/12 as coefficients
- Dynamic replacement of constants fails (pure integrator bias)

### B. Directions that failed
- Direct substitution E₂→C, E₃→D: wrong limit (3.53)
- IBP compensation: still wrong (3.18)
- Tracking filter cascade: wrong limit (0.92)

## For the Lean Framework (Ripple)

The framework should formalize:
1. The DEFINITIONS (PIVP, bounded time, hierarchy) — DONE
2. The basic field closure theorems — stated as axioms
3. **The Apéry generating function ODE** as a conditional result:
   "The polynomial PIVP starting at x₀ > 0 with exact ICs computes ζ(3)
   at first-floor rate"
4. The polylog cascade as a second conditional:
   "IF ODE coefficients are exact transcendentals, THEN first-floor"
5. The Apéry construction as: "ζ(3) is CRN-computable" (without floor claim)
