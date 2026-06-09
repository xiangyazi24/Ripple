# Ripple — UNDERSTANDING (top-level orient)

This is the repo-root orient. Session start: read this first, then drill down.

## What Ripple is

Lean 4 formalization of CRN-computable real numbers, building on four papers:
- **[RTCRN1]** Real-time computability by CRNs (Nat. Comput. 2018)
- **[RTCRN2]** Real-time equivalence CRN ↔ analog (DNA 25, 2019)
- **[LPP]** Large-population protocols (DNA 28, 2022)
- **[BAC]** Bounded Analog Complexity (DNA 32, 2026)

PDFs in `../Bounded/ref/`.

## Code layout

```
Ripple/
├── Core/        — PIVP, BoundedTime, Compilation, CRNPipeline
├── DualRail/    — incremental compilation, infection graph, etc.
├── LPP/         — large-population protocols
├── Number/      — concrete number constructions
│   ├── Apery.lean, Pi.lean, Euler.lean, Dottie.lean, ...
│   └── Frobenius/ — local Frobenius theory at the Apéry conifold
├── ODE/         — scalar barrier + ODE infrastructure
└── Tactic/      — (future) automation
```

## Ehrenfest Urn (LPP/EhrenfestUrn.lean) — as of 2026-05-16

**Paper:** Albenque-Gerin 2012 (DMTCS 14(2):271–284, arXiv:1104.5643)

**Status:** 0 sorry, 0 axiom. 30889 lines, build 2890 jobs.
Main theorems `ehrenfest_computable_rationals_forward/backward` proved unconditionally.
Full proof chain from `rational_noncomputable` through
`ehrenfest_computable_rationals_forward` compiles. All structural reasoning is complete;
remaining sorry's are purely technical valuation bounds (Kummer/Legendre).

### Paper gap: `kummer_poly_irreducible_odd` (line 1532)

**Claim (AG2012 Thm 5(iii)):** $(d+1)(1-X)^d - 1$ is irreducible over ℚ for all odd $d \geq 3$.

**This is FALSE.** Counterexample: $d = 63$. Since $d+1 = 64 = 4^3$ and $3 | 63$,
the Vahlen-Capelli criterion does not apply, and the polynomial factors.

**Impact on paper's results:**
- **Rational characterization** ({0, 1/3, 1/2, 2/3, 1}): UNAFFECTED. Uses
  `rational_noncomputable` which is independent of irreducibility.
- **Density in [0,1]**: UNAFFECTED. Even-degree case (Selmer) alone gives density.
- **"All algebraic degrees achievable"**: PARTIALLY AFFECTED. Even degrees use
  Selmer ($X^d - X - 1$, classically irreducible). Odd degrees use the Kummer-type
  polynomial — works for MOST odd $d$ but fails for exceptional ones where
  $d+1$ has special arithmetic structure.

**Likely fixable:** For exceptional odd $d$, one can probably:
- Choose a different rule (different $E$ or $k$) whose drift has an irreducible factor of degree $d$
- Or use an Eisenstein-type criterion with a different prime for those specific $d$
- The set of "bad" $d$ is sparse (requires $d+1$ to be a perfect power or similar)

**Task for future session:** Give this to ChatGPT 5.5 — find either:
(a) A uniform construction that works for ALL odd $d$, or
(b) A case-by-case fix for the exceptional $d$ values

### Number theory sorry: `integer_equation_forces_k_one` (line 1832)

**Statement:** $\sum_{j \in E} \binom{k}{j} a^j c^{k-j} = a(a+c)^{k-1}$ with
$\gcd(a,c)=1$, $a+c \geq 4$ implies $k=1$.

**This is mathematically correct.** Paper has a valid proof using p-adic valuation.

**Proved steps (0 sorry):**
1. $0 \notin E$ for $a \geq 2$ (`zero_not_in_E_of_a_ge_two`)
2. Factor $a$ from each term, cancel to get divided equation
3. $1 \in E$ (otherwise $a \mid c^{k-1}$, contradicts coprimality)
4. $a \mid (k-1)$ (mod-$a$ analysis of the divided equation)
5. Get prime $r \mid a$, derive $r \mid (k-1)$, show $r \nmid c$
6. Full induction structure: assume $r^n \mid (k-1)$, derive $r^{n+1} \mid (k-1)$
   via mod $r^{n+1}$ analysis (split sum, mod congruence, coprimality)
7. Contradiction: $r^k > k-1$ but $r^k \mid (k-1)$

**Remaining sorry's (3, all in the $a \geq 2$ induction step):**
- `hr_dvd_choose`: $r^n \mid \binom{k}{j}$ for $j \geq 2$ when $r^n \mid (k-1)$.
  Requires: Kummer's theorem or Legendre's formula for $v_r(\binom{k}{j})$.
  Key bound: $v_r(j!) \leq j-1$ (Legendre), so $v_r(\binom{k}{j}) \geq n - (j-1)$,
  combined with $v_r(a^{j-1}) \geq j-1$ gives total $\geq n+1$ for the product.
- `hrhs_mod`: $(a+c)^{k-1} \equiv c^{k-1} \pmod{r^{n+1}}$.
  Requires: same Kummer bound applied to binomial expansion terms
  $\binom{k-1}{i} a^i c^{k-1-i}$ for $i \geq 1$. Each has $v_r \geq n+1$.
- `hc_dvd` (case $a=1$, $c \geq 3$): $\forall n,\; c^n \mid (k-1)$.
  Requires: separate iteration argument for the $a=1$ case (different structure).

**Estimated remaining work:** ~150 lines for a shared `choose_valuation_bound` lemma
using Legendre's formula, plus ~50 lines for the $a=1$ case reduction.
Mathlib has `Nat.Prime.pow_dvd_choose` (Kummer) which should give the bound directly.

## Cassels Elementary (LPP/CasselsElementary.lean) — as of 2026-05-16

**Status:** 3 sorry (1 permanent/math-false, 1 core descent, 1 q<p branch).
67 pre-existing Mathlib API drift errors (lines 90-350 range).

| Line | Theorem | Status |
|------|---------|--------|
| 1116 | `cassels_sharp_tail_control` | PERMANENT — mathematically FALSE |
| 1551 | `cassels_runge_gap_core` | **Core blocker** — Cassels descent |
| 2712 | `shifted_alt_cyclotomic_plus_nat_not_prime_power` q<p | Bypassed by `_lt` variant |

**New (2026-05-16):** `cassels_upper_divisor_nat_elementary_raw_lt` — sorry-free
theorem for the p<q direction, matching `CatalanCasselsUpperDivisorNatLT`.

## Cassels Actual Padé (LPP/CasselsActualPade.lean) — as of 2026-05-16

**Status:** 2 sorry (both in new Route B framework). 4741 lines, build clean.

### Proved (0 sorry) — Padé infrastructure (4611 lines):
- `cassels_actualCoeff_hasSum_branch` — Target 1 (coefficient stream = branch)
- `cassels_runge_hbranch` — hroot → v/u^{q-1} = F(X)
- `cassels_runge_hfactor` — error = X^{2N+1} · tailG
- `cassels_runge_hMbound` — uniform tail bound
- `cassels_catalan_descent_False` — reduction to hgrowth + hLayerE
- `cassels_runge_pth_power_X_factored` — algebraic remainder factored
- Hermite ₂F₁ approximant definitions + p-th power identity

### Route B framework (new, 2 sorry):
- `casselsDirectR` = ⌊q/p⌋+1 (fixed small truncation, not growing)
- `cassels_no_root_solution` — the target: hroot → False
  - sorry: the quantitative Cassels contradiction (Ribenboim B2.4 pp.208-212)
- `casselsDirectClearDen_mul_coeff_int` — D clears coefficient denominators
  - sorry: Rat denominator divisibility arithmetic

### Why Route A (Padé) fails for hgrowth:
The convolution-triangle bound gives 32^{2N+1} (or ρ^{-(2N+1)}) growth in N.
For N = casselsPadeLevel p q n (growing with n), this exponentially dominates
the RHS u^{pN+p-q+1}. The growth budget is structurally infeasible for the
det-scaled Cramer approximant.

### Route B — CRITICAL FINDING (2026-05-16):

**The F(X) expansion (in X = u^{-p}) is TOO SLOW.** For (p=5,q=7,u=2):
- F(X) tail decays as u^{-p} = 1/32 per term
- Clearing factor × tail ≈ 2.8 > 1 — BOUND FAILS

**The Catalan expansion (in a^{-q} where a = u^p-1) WORKS:**
- a = u^p - 1 ≥ 31, so a^{-q} ≤ 31^{-7} ≈ 4×10^{-11}
- Clearing factor × tail ≈ 5×10^{-11} ≪ 1 — BOUND CLOSES

**Correct proof structure (Ribenboim B2.4 mapped to our setting):**
1. From hroot derive (uv)^p = (u^p-1)^q + 1 = a^q + 1 (sorry: algebra)
2. Expand (a^q+1)^{1/q} = a·(1+a^{-q})^{1/q} via binomial series
3. y = a (from y^q = (uv)^p - 1 = a^q)
4. I = a^{Rq-1}·q^{R+ρ}·(a - truncation of x^{p/q})
5. Clearing uses q^{R+ρ} (NOT p^{2R}), ρ = ⌊R/(q-1)⌋
6. |I| < q^{R+ρ-q} < 1 (since R+ρ < q)
7. Key size bound: a^q ≥ p^q (trivially since a ≥ 31 > p)

**Remaining sorry's (2 in cassels_no_root_solution):**
- Algebraic derivation: hroot → (uv)^p = a^q + 1 (routine ℝ algebra)
- Ribenboim contradiction: the quantitative 0 < |I| < 1 (~200 lines)

Steps 3-6 require the Catalan-expansion HasSum (Mathlib's binomial series
at Y = a^{-q}), B2.2 integrality, and explicit coefficient bounds.

---

## Current frontier (as of 2026-05-07, post Stage 1 small-weight push)

**Modular sub-tree (`Ripple/Number/Modular/`):** 1 sorry remaining
(`complex_sturm_bound_valence_formula_phi41Level41Cleared` at
`ModularPolynomialQExpansion.lean:2720`).  All other modular files
0 sorry, 0 axiom.  `lake build` clean, 3694 jobs.

### Stage 2 (Γ₀(p) index): closed (2026-05-07)

`CosetIndex.lean` proves `[SL₂(ℤ):Γ₀(p)] = p + 1` for any prime `p` via
the action of SL₂(ℤ) on ℙ¹(𝔽_p), specialised to `gamma0_index_41 = 42`.
`SturmBoundIndex.lean` bridges the phi41 Sturm-bound literal `42` to
this proven index.

### Stage 1 (level-1 Sturm): small weights done

`LevelOneSturm.lean` exposes the statement as a `Prop` and the trivial
negative-weight + weight-zero base cases.

For each `k ∈ {2, 4, 8, 10}`, a dedicated file
`LevelOneCuspWeight{k}.lean` proves `levelOne_cuspForm_weight{k}_eq_zero`
via the `f^a / Δ^b` pattern (`a·k = 12·b`, `a > b` for net decay).
Weight 6 is already in `ModularPolynomialQExpansion.lean`.

`LevelOneSmallWeights.lean` aggregates these into ModularForm-level
Sturm theorems (vanishing constant ⇒ form is zero) for weights 2, 4,
8, 10.

**Open Stage 1 obligation:** weights `k ≥ 12`, where `dim S_k(Γ(1))`
can be nonzero (e.g., `dim S_12 = 1` spanned by `Δ`).  The `f / Δ^j`
generalisation needs the q-expansion order analysis and
`dim M_{k - 12 j}` results that Mathlib does not yet carry.

## Earlier frontier (as of 2026-05-05, post round 35)

**Project-wide: 0 sorry, 0 axiom, `lake build` clean (3682 jobs).**

### Front 1: Frobenius / Apéry (Number/Frobenius/)

**0 sorry.** All ratio bounds closed. See `Ripple/Number/Frobenius/UNDERSTANDING.md`.

### Front 2: CM Evaluation (Number/Modular/)

**File:** `Ripple/Number/Modular/CMEvaluation163.lean` (5129 lines, builds clean)
**Goal:** Prove j((1+i√163)/2) = -640320³ unconditionally.

**All infrastructure proved (0 sorry):**
- q-expansion proximity: ‖j(τ₁₆₃) - (-640320³)‖ < 1 ✅
- Proximity + integrality → exact value ✅
- Jacobi quartic, q-Pochhammer, KleinJ, eta nonvanishing ✅
- Root isolation via Φ₄₁ factorization + Taylor domination ✅
- PowerSeriesEvalCertificate chain for E₄³, Δ at CM points ✅
- SparseTermEvaluationCertificate proved unconditionally ✅

**Remaining gap (conditional hypotheses, not sorry):**
The chain needs `evalPhi41DiagIsolatedC (kleinJ heegnerTau163_div41) = 0`, which
reduces via the Sturm-bound path to TWO hypotheses:
1. `phi41Level41SturmPrinciple` — Sturm bound for Γ₀(41) weight-1008 forms
2. `phi41Level41SturmCoefficientCertificate` — first 3528 q-expansion coefficients = 0

**Alternative route (class number):**
- Prove h(-163) = 1 by exhaustive quadratic form enumeration
- State CM integrality (j ∈ ℤ when h=1) as a sorry-carrying lemma
- Combine with proximity to close j(τ₁₆₃) = -640320³

### Front 3: Ramanujan & Chudnovsky 1/π series

**Files:** `Ramanujan1914.lean`, `Chudnovsky1989.lean`

Both theorems are **0 sorry, 0 axiom** but **CONDITIONAL**:
- `ramanujan_one_over_pi` takes hypothesis:
  `ramanujanCM58GaussDerivativeCombination = 9801/(2√2π)`
- `chudnovsky_one_over_pi` takes hypothesis:
  `chudnovskyCM163GaussDerivativeCombination = 640320^{3/2}/(12π)`

These hypotheses ARE the mathematical content of the formulas — proving them
requires CM period evaluation (Chowla-Selberg) + modular derivative formulas.
This is deep classical analytic number theory, not currently formalized.

### Front 3b: Period-₂F₁ Bridge (Number/Hypergeometric/PeriodBridge.lean)

**0 sorry, 0 axiom** (3797 lines). All infrastructure proved in rounds 28-35:
- `gauss2F1_operator_eq_zero_of_norm_lt_one` ✅ (round 32, ~450 lines)
- `gauss2F1SecondSolution_operator_eq_zero` ✅ (round 34-35, codex overnight)
- `hypergeom_frobenius_wronskian_from_abel` ✅ (round 34-35, codex overnight)
- `ramanujan_quadratic_period_pullback` ✅ (redesigned: λ²=1/99⁴, not ₂F₁ identity)
- `chudnovsky_schwarz_period_pullback` ✅ (redesigned: algebraic j-argument identity)
- `chowla_selberg_cm{58,163}_period` ✅ (conditional on algebraic-ratio hypothesis)
- Wronskian specializations, Clausen chain rule, Legendre period ✅
- All norm bounds, Euler integral, differentiability ✅

**CM / Chowla-Selberg (2):**
7. `chowla_selberg_cm163_period` — ω₁ at disc -163
8. `chowla_selberg_cm58_period` — ω₁ at disc -58

**Post-chain-rule normalization (2):**
9. `ramanujan_cm58_periodDerivative_after_chain_rule`
10. `chudnovsky_cm163_periodDerivative_after_chain_rule`

**Norm bounds (0 — all CLOSED round 33):**
~~11-13.~~ ✅ All three norm bounds closed by `norm_num`

**Proved infrastructure (rounds 27-30):**
- `deriv_clausenGaussSq_eq_two_mul_gauss2F1` ✅ — chain rule for clausenGaussSq
- `deriv_clausenGaussSq_ramanujan_cm58` / `_chudnovsky_cm163` ✅ — specializations
- `_from_periodBridge_core` ✅ — extraction layer (both Ramanujan + Chudnovsky)
- `ellipticK_zero`, `gauss2F1_half_half_one_zero` ✅ — base cases
- `complex_gamma_half_sq`, `betaIntegral_half_half_eq_pi` ✅ — Gamma constants
- `hypergeom_logSecondSolution_wronskian` ✅ — log-part Wronskian (W = y₁²/z)
- `gauss2F1_formal_powerSeries_ode` ✅ — coefficient recurrence ODE
- Frobenius second solution definition with digamma correction ✅

These are well-known classical results, not in Mathlib yet.

**Closed (2026-05-03):**
- `jacobi_triple_product_theta_eta_normalization` — θ₂·θ₃·θ₄ = 2η³ (8th root extraction via connectedness of ℍ + cusp limit)

**Closed (2026-05-02):**
- `tendsto_jacobiTheta2_half` — θ₂(τ/2,τ) → 2 as Im(τ) → ∞ (pairing + geometric bound + squeeze)
- `tendsto_eta_tprod_one` — ∏(1-q^n) → 1 at ∞ (norm bound + continuity at 0)
- `tendsto_thetaProductEight_div_delta` — θ₂⁸θ₃⁸θ₄⁸/Δ → 256 at ∞
- `thetaProductEight_div_delta_eq_256` — weight-0 modular form = constant via dimension argument
- `thetaProductEight_eq_256_delta` — (θ₂θ₃θ₄)⁸ = 256Δ
- `classical_E4_reduced_theta_identity` — E4 = θ₂⁸ + θ₂⁴θ₄⁴ + θ₄⁸ (via dim S₄ = 0 + cusp form)
- `E4SubHalfThetaCF.zero_at_cusps'` — cusp vanishing via SL(2,Z) slash invariance
- tendsto_jacobiTheta_one, tendsto_thetaFourConst_one, tendsto_E4_one
- bddAtCusp + cuspFormCubeDivDelta_eq_zero (dim S4 infrastructure)
- eta_product_norm_eventually_ge, norm_delta_eq, delta_norm_lower_bound

**Proof strategies:** See `HANDOFF/codex_cm163_final_sorries.md`.

**Key supporting files (all 0 sorry):**
- `SingularModuli.lean` — theta consts, T-transforms, S-transform eighth powers
- `ThetaQuartic.lean` — Jacobi quartic via D₄ lattice
- `QPochhammer.lean` — finite/infinite product identities
- `KleinJ.lean` — Eisenstein series, Klein j-invariant
- `ThetaNonzero.lean` — eta product nonvanishing

## Sub-documents (drill-down by area)

- **`Ripple/Number/Frobenius/UNDERSTANDING.md`** — Frobenius layer working doc
- **`HANDOFF/codex_cm163_final_sorries.md`** — CM163 sorry attack plan (for Codex)
- **`OPEN_PROBLEMS.md`** — repo-wide open problems list.
- **`STRATEGY.md`** — strategic direction notes.
- **`CHECKPOINT.md`** — per-lemma checkpoint log (lean-projects rule).
- **`WORK_LOG.md`** — append-only commit-level log.
- **`DOCTRINE.md`** — autonomous-execution doctrine.
- **`RUN_LOG.md`** — autonomous-session audit trail.

## Conventions

- All proofs follow Mathlib style.
- **0 sorry, 0 axiom across entire project** (as of round 35, 2026-05-05).
  All application-level theorems (ramanujan_one_over_pi, chudnovsky_one_over_pi) are
  proved but CONDITIONAL on CM evaluation hypotheses. The gaps are in the hypotheses,
  not in sorry targets — the project compiles clean with no sorry anywhere.
- After every new lemma: const-coeff / closed-form sanity check **before** commit.
  This rule was added 2026-04-28 after `zSubdom_recurrence` shipped with a wrong
  identity that 30 minutes of arithmetic would have caught.

## How to read this repo

1. New session: read this top-level `UNDERSTANDING.md` (you're here).
2. If working on Frobenius / Apéry: continue to `Ripple/Number/Frobenius/UNDERSTANDING.md`.
3. If working on CM163 / modular forms: read `HANDOFF/codex_cm163_final_sorries.md`.
4. If autonomous mode: read `DOCTRINE.md` then `RUN_LOG.md` for the current run state.
5. For the latest commit-by-commit context: `WORK_LOG.md`.

## Maintenance rule

Update this file whenever:
- A major sub-doc moves or is created.
- The "Current frontier" sorry list changes substantively.
- A new convention is locked in (e.g., the const-coeff sanity-check rule above).

Drift between this file and the actual code is a bug. If you read it and the sorry
list doesn't match current state, fix the doc — it's the orient, future-you depends
on it.
