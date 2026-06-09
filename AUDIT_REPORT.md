# Ripple Audit Report

Date: 2026-04-30

## Executive Status

I attempted the two requested `1/pi` identities in:

- `Ripple/Number/Chudnovsky1989.lean:165`
- `Ripple/Number/Ramanujan1914.lean:175`

They are not closable from the current Apéry/Frobenius infrastructure without
adding an unproved modular-form theorem or using an axiom-like external
placeholder.

The project-local proof-body `sorry` inventory, after stripping Lean comments,
is exactly:

```text
Ripple/Number/Chudnovsky1989.lean:165
Ripple/Number/Ramanujan1914.lean:175
```

I did not use `axiom`, `proof_wanted`, or any equivalent shortcut to close
them. I fixed one unrelated build break in `Chudnovsky1989.lean`: its
factorial recurrence proof had a trailing `ring` after `field_simp` had
already closed the goal.

Verified:

```bash
lake build Ripple.Number.Chudnovsky1989 Ripple.Number.Ramanujan1914
lake build Ripple.Number.Frobenius.AperyAGFSharpFromFrobenius
```

Both builds complete; the first emits the two expected `declaration uses
sorry` warnings.

## Why the Two Pi Identities Do Not Follow From F5

The recently completed F5 infrastructure proves a conifold lower bound for the
ordinary Apéry generating function. It is built around the Apéry conifold
operator, the singularity `z1 = 17 - 12 * sqrt 2`, and the three local
Frobenius exponents `0`, `1/2`, and `1`.

The two remaining identities are different mathematical objects:

- Ramanujan 1914 uses the hypergeometric function
  `3F2(1/4, 1/2, 3/4; 1, 1; 256 z)` at `z = 1 / 396^4`.
- Chudnovsky uses the `3F2(1/6, 1/2, 5/6; 1, 1; z)`-type CM evaluation at
  the class-number-1 discriminant `163`, with constants `640320`,
  `13591409`, and `545140134`.

The decisive missing ingredient is not local Frobenius analysis or coefficient
decay. It is the global modular evaluation identifying a specific
hypergeometric value and derivative with `1 / pi`. The existing files already
prove the one-dimensional formal-series obstruction:

- `Ramanujan1914.unique_solution_of_recurrence`
- `Chudnovsky1989.unique_solution_of_recurrence`

This confirms that the Apéry two-companion ratio-readout mechanism does not
transfer directly to these MUM-at-zero hypergeometric equations.

I checked Mathlib. It has
`Mathlib.Analysis.Real.Pi.Chudnovsky`, but that file explicitly says it does
not contain a proof yet and exposes only:

```lean
proof_wanted chudnovskySum_eq_pi_inv : chudnovskySum = pi^-1
```

Using that would be an axiom-level skip, so I did not use it.

## Minimal Paths To Close The Two Identities

### Option A: Modular-Form Route

Build the missing analytic stack:

1. Define the relevant modular lambda / elliptic integral / theta or Eisenstein
   series objects in Lean.
2. Prove the hypergeometric parametrization of the Picard-Fuchs solution.
3. Prove the singular-modulus evaluations:
   - Ramanujan: the level-58 / `396^4` evaluation.
   - Chudnovsky: the discriminant-163 / `640320^3` evaluation.
4. Translate the modular derivative identities into the exact linear
   combinations currently stated in the files.

This is the mathematically clean route, but it is a substantial new subsystem.

### Option B: Import And Formalize A Published Proof

Use a detailed proof source, preferably Milla's Chudnovsky proof for the
Chudnovsky formula and a parallel Ramanujan formula source. This still needs
the modular or elliptic-function layer, but the constants and transformation
identities are guided by the paper.

### Option C: Explicit Hypothesis Layer

If the immediate project goal is downstream CRN/PIVP compilation rather than
proving modular forms now, split each theorem into:

- a no-`sorry` theorem conditional on a named modular-evaluation proposition;
- the remaining proposition as the only open theorem.

This would keep the downstream dependency honest and searchable, while
avoiding hidden axioms.

## Redundancy And Architecture Findings

### 1. F5 denominator lower bound now has two independent routes

Current files:

- `Ripple/Number/Frobenius/AperyACoefficientSharpLower.lean`
- `Ripple/Number/Frobenius/AperyAGFSharpFromFrobenius.lean`

Both are useful:

- The coefficient route is shorter and relies on direct positivity/lower-bound
  coefficient estimates.
- The Frobenius/ODE route is structurally deeper and gives a reusable
  connection-coefficient/ODE uniqueness architecture.

Recommendation: keep both, but split
`AperyAGFSharpFromFrobenius.lean` into smaller files:

- `AperyCanonicalOperator.lean`
- `AperyCanonicalBranches.lean`
- `AperyCanonicalODE.lean`
- `AperyCanonicalConnection.lean`
- `AperyAGFSharpFromFrobenius.lean` as the final assembly file

The current file is over 9,500 lines, and `AperyGeneratingFunction.lean` is
over 22,000 lines. Both are now expensive to navigate.

### 2. Naming inconsistency: `Aprey*` vs `Apery*`

Files still using the typo:

- `Ripple/Number/ApreyBounded.lean`
- `Ripple/Number/ApreyScalarZ.lean`

There are multiple imports and comments referring to `Aprey`. Renaming is
mechanical but high-churn. Recommendation: defer until after current proof
pushes, then do one dedicated rename commit with import updates and compatibility
aliases if needed.

### 3. Debug/check files

`Ripple/_AxCheck.lean` is a debug file containing `#print axioms`. It is useful
locally but should not be imported by production modules. Recommendation: move
it under `experiments/` or rename to make its non-library status explicit.

### 4. F5Bridge layering is good but import pressure is rising

Current import references:

- `F5Bridge.lean` imports `AperyG2BoundedNearConifold` and
  `AperyACoefficientSharpLower`.
- `AperyAGFSharpFromFrobenius.lean` imports `AperyACoefficientSharpLower`,
  mostly to consume the already closed lower-bound API in intermediate wrappers.

Recommendation: put shared propositions and final theorem signatures in
`F5BridgeCore.lean`, keep proof-producing files independent where possible,
and avoid importing a proof route into another proof route unless the theorem is
actually consumed.

### 5. Residual TODOs are mostly honest

The codebase is now mostly explicit about remaining analytic gaps. The only
actual proof-body `sorry`s are the two pi identities. Other appearances of
`sorry`, `axiom`, and `TODO` are mostly comments, historical names, or
compatibility wrappers.

## Suggested Next Tasks

1. For Chudnovsky, add a no-`sorry` bridge from the local theorem statement to
   Mathlib's `chudnovskySum` definition, but do not use Mathlib's
   `proof_wanted`. This isolates the exact normalization/constant conversion.
2. For Ramanujan, create a `Ramanujan1914ModularGap.lean` file with a named
   proposition for the modular evaluation and a conditional theorem proving the
   current summation statement from it.
3. Split `AperyAGFSharpFromFrobenius.lean` once the current branch is stable.
4. Run a dedicated rename pass for `Aprey*` to `Apery*`.
