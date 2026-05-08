# Ripple

A Lean 4 formalization of **Chemical Reaction Network computable numbers** — the class of real numbers a bounded CRN (equivalently, a polynomial initial value problem / GPAC) can compute in real time, and its refinements down to weaker analog models (large-population protocols, bounded-analog complexity).

## Where the name comes from

"Ripple" is a mishearing. The author meant *repository*, the word came out *ripple*, and the name stuck — because the underlying research actually did start small and ripple outward.

It began as a homework exercise in Jack Lutz's class at Iowa State: *can you compute rational numbers with a chemical reaction network?* That grew into algebraic numbers, then transcendentals (e, π, the Euler–Mascheroni constant γ, ln 2), then the shape of the whole real-time class, then weaker population-protocol refinements, then — on the other side — stronger infinite-time analogues. Each layer was a new ripple from the same class exercise.

This repository is the Lean 4 counterpart to that trajectory.

## Scope

Ripple formalizes the theory developed across four papers:

1. Huang, Klinge, Lathrop, Li, Lutz — *Real-time computability of real numbers by chemical reaction networks*, Nat. Comput. 2018.
2. Huang, Klinge, Lathrop — *Real-time equivalence of CRNs and analog computers*, DNA 25 (2019).
3. Huang, Huls — *Computing real numbers with large-population protocols*, DNA 28 (2022).
4. Chen, Huang — *Bounded analog complexity of real numbers* (submitted, 2026).

The goal is to treat these as one unified pipeline rather than four disjoint papers.

## What is formalized (as of 2026-05-08)

### CM-163 — `j((1+√−163)/2) = −640320³`

- **`KleinJCM163Statement_proof`** in `Ripple/Number/Modular/CMEvaluation163.lean`.
  The Heegner-class CM evaluation of the modular `j`-invariant at the
  unique class-number-1 discriminant `−163`, fully verified through the
  level-41 modular polynomial `Φ₄₁`. Closing this required:
  - **`atkinLehnerInclusion41`** — the matrix-algebra identity that the
    conjugate of `Γ₀(41)` by the Atkin-Lehner pullback `[[41,0],[0,1]]`
    sits inside `Γ(1)`.
  - **`levelOne_cuspForm_eq_zero_of_low_coeffs_vanish`** — a uniform
    level-1 Sturm bound for arbitrary even weight `k ≥ 4`: if the first
    `⌊k/12⌋ + 1` `q`-expansion coefficients of a level-1 cusp form
    vanish, the form is zero. Parametric in `(a, b, n)` with
    `a·k = 12·b` and `a·n ≥ b + 1`; dispatches on `k mod 12`.
  - **`phi41Level41ClearedAsModularForm`** — the bundled
    `ModularForm Γ₀(41) 1008` whose `q`-expansion equals
    `phi41Level41ClearedEulerQExpansion`, assembled via the graded ring
    of modular forms over the four building blocks (E₄ and Δ on Γ₀(41),
    plus their Atkin-Lehner pullbacks).
  - **`qExp_norm_coeff_zero_of_qExp_coeff_zero`** — the analytic
    substance of Sturm at level `N`: vanishing of the first M
    `q`-coefficients of `f` propagates to vanishing of the first M
    `q`-coefficients of `norm 𝒮ℒ f`, since each non-trivial coset
    contributes at least 0 to the order at infinity by boundedness at
    cusps.
  - **`levelGamma0_41_sturm_weight_1008`** — the Sturm bound at level
    `Γ₀(41)` weight `1008`: combine the q-expansion bridge with the
    generic level-1 Sturm at weight `1008·42 = 42336` and then
    `ModularForm.norm_eq_zero_iff` to deduce `f = 0`.

### ζ(3) — Apéry's constant

- **F1 (three-term recurrence).** `aperyA_recurrence` and `aperyB_recurrence` for the Apéry sequences aₙ, bₙ, closed via the pointwise vdPoorten (1979, §8) Zeilberger witness. `aperyW_pointwise` handles all three case regimes (k ≤ n−2, k = n−1, k = n) axiom-free.
- **F1′ (harmonic correction recurrence).** `aperyD_recurrence` and the decomposition `bₙ = H₃(n)·aₙ + dₙ`.
- **F2 (formal ODE).** `aperyGFA_satisfies_ode` (homogeneous) and `aperyGFB_satisfies_ode` (inhomogeneous with a single `z⁰` correction of 6, since the A-recurrence closes at n=0 but the B-recurrence does not). This is the Apéry differential operator `p(z)u‴ + q(z)u″ + r(z)u′ + s(z)u`.
- **Fermi–Dirac real-time encoding.** `fermi_integral_eq_zeta3` — the identity `(2/3)·∫₀^∞ x²/(1+eˣ) dx = ζ(3)` — via the geometric-remainder expansion `1/(1+eˣ) = Σ (−1)ᵏ e^(−(k+1)x)`, termwise integration, and the alternating-to-zeta rearrangement. Packaged as a `PIVP.Solution` in `apery_fermi_is_crn_computable`, together with a real-time modulus bound `|S(t) − ζ(3)| ≤ C·(t² + 2t + 2)·e^(−t)`.

### Large-population protocols

- **Main theorem (unconditional).** `bounded_crn_is_lpp_computable_unconditional` — every bounded certified PIVP is LPP-computable. Patches the DNA 28 gap where transient overshoot beyond the unit interval could break compilation, via a saturating surrogate `y' = (x − y)(U − y)` with `U ∈ (α, 1) ∩ ℚ`.
- **Algebraic case.** `algebraic_lpp_computable` — every algebraic number in [0,1] is LPP-computable. Five-pipeline construction: minimum-polynomial encoding → positive-rational shift → zero-init wrapper → Stage 1 quadraticization → Stage 2 bound-to-small-λ closure.
- **Stage-by-stage LPP pipeline.** `stage1_quadraticization`, `stage2_*`, `tpp_to_lpp`, `stage4_to_plpp`, reverse `lpp_to_gpac`.
- **Dual-rail and exp-shift constructions.** `dualRail_semantic_solution`, axiom-free.

### Catalan's constant G

`catalan_is_lpp_computable` in `Ripple/Number/CatalanCertified.lean` — G is LPP-computable via `G = ∫₀^∞ s·exp(−s)/(1 + exp(−2s)) ds`, compiled as a 4-variable bounded polynomial IVP (E, R, W = 1−V, G) with convergence bound `|G(t) − G| ≤ (t+1)·exp(−t)`.

### Foundational

- **e, π, ln 2, γ, ½e⁻¹.** Famous constants packaged as CRN-computable with zero sorries. `EulerGamma` is the most intricate.
- **Non-collapse theorem.** `zero_init_no_collapse` (Xiang's conjecture, fully proved).
- **Real-time foundation.** `algebraic_is_certified_crn`, `minPolyPIVP_certified`, `certified_add_rational_nonneg` — direct minimum-polynomial encoding of an algebraic number as a quadratic PIVP, plus rational shifts.

## What remains open

The repository has **0 `sorry` and 0 `axiom` declarations** across all
six pillars (Core, ODE, DualRail, LPP, Number, Number/Modular).

- **Kernel-only certificate for the Φ₄₁ Sturm coefficient zero check.**
  `phi41Level41RecurrenceCoeffArrayFirstZero_sturmBound` is currently
  closed via `native_decide`, which trusts the Lean compiler chain in
  addition to the kernel. The CRT-route helpers in
  `Ripple/Number/Modular/ModularPolynomialSturmCertificate.lean` are
  in place; replacing `native_decide` with a kernel-only Chinese
  Remainder Theorem certificate is feasible in principle but requires
  either a tighter problem-specific coefficient bound (the natural
  a-priori bound is ≈10^8590, demanding ≈468 CRT primes) or a custom
  reflection evaluator. See `RELEASE_NOTES.md` and
  `HANDOFF/crt_route_replace_native_decide.md` (in the working
  workspace) for the concrete plan.

## Trust footprint

There are no `axiom` declarations and no `sorry` in any tactic
position. The only trust beyond the Lean kernel is the `native_decide`
tactic, used in finitely many places to discharge large decidable
claims:

- `phi41Level41RecurrenceCoeffArrayFirstZero_sturmBound` — first 3529
  entries of the Φ₄₁ cleared `q`-expansion recurrence array vanish.
- `phi41Diag_root` — `evalPhi41Diag(j(τ₁₆₃)) = 0`.
- `phi41DiagCofactor_ne_zero` — the cofactor at the root is nonzero.
- A level-41 difference table check via `(List.range 83).Forall ...`.

`native_decide` compiles the decision procedure to native code and
trusts that the compiled program's result matches what the Lean
kernel would compute. The mathematical content is unchanged; only the
verification path differs from a strict kernel-only proof.

## Building

```bash
# Prerequisites: elan + Lake (https://leanprover.github.io/)
export PATH="$HOME/.elan/bin:$PATH"
lake exe cache get    # pull Mathlib oleans
lake build
```

Takes 10–20 minutes on first build (mostly Mathlib).

## Structure

```
Ripple/
├── Core/
│   ├── PIVP.lean          Polynomial initial value problems (GPAC model)
│   ├── BoundedTime.lean   Time modulus, complexity hierarchy
│   ├── Compilation.lean   Bounded surrogate compilation
│   └── CRNPipeline.lean   Dual-rail + readout, complexity preservation
├── LPP/                   Large-population-protocol compilation + main theorem
├── Number/
│   ├── AperySequences.lean   F1 / F1′ / F2 for the Apéry sequences
│   ├── AperyFermi.lean       Fermi–Dirac real-time encoding of ζ(3)
│   ├── ApreyBounded.lean     Conifold Frobenius witness
│   ├── Apery.lean            Overall ζ(3) theorem wiring
│   ├── Frobenius/            Regular-singular Frobenius theory (long-term pillar)
│   └── Modular/              Modular forms, j-invariant, CM-163, Φ₄₁ Sturm
├── ODE/                   Scalar Picard barriers, generic attractor tools
└── Tactic/                (future) automation for constructing proofs
```

`OPEN_PROBLEMS.md` lists the current research frontier; `WORK_LOG.md` and `CHECKPOINT.md` track session-level progress.

## Citing

If this formalization is useful in your work, cite the relevant paper above. The repository itself is a living artifact — referencing the commit hash alongside the paper is more informative than the repo alone.

## License

Apache-2.0, matching Mathlib. See `LICENSE`.
