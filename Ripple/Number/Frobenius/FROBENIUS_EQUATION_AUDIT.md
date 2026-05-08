# Frobenius Equation Audit

This note records the source of the Phase 4 ODE/connection-coefficient mismatch.

## Canonical Apéry equation

The ordinary Apéry generating function `A(z) = Σ a_n z^n` satisfies the
canonical ordinary-derivative equation

```text
P(z) A'''(z) + Q(z) A''(z) + R(z) A'(z) + S(z) A(z) = 0
```

with

```text
P(z) = z^2 - 34 z^3 + z^4
Q(z) = 3z - 153 z^2 + 6 z^3
R(z) = 1 - 112z + 7z^2
S(z) = -5 + z
```

This is already proved in `AperyAGFSharpFromFrobenius.lean` as
`aperyGFAReal_satisfies_apery_ode_polynomial`.

Equivalently, before dividing by the harmless nonzero factor `z` near the
conifold, it is the standard theta-operator equation

```text
θ^3 - z(2θ+1)(17θ^2+17θ+5) + z^2(θ+1)^3.
```

## Reduced conifold operator

The existing conifold Frobenius branch package in `AperyInstance.lean` uses

```lean
aperyPsSeq 0 0 Number.aperyQconifold Number.aperyPconifold
```

This reduced operator has the same indicial equation at the simple zero
`z₁`, because the lower-order `R,S` terms do not enter the leading
`t^(ρ-2)` balance.  However, it is not the differential equation satisfied
by `A(z)`.

Consequently, a connection witness for `aperyGFAReal` cannot be obtained by
ODE uniqueness against `aperyBranchTriple` built from this reduced operator.
That would identify solutions of different ODEs.

## Fix direction

The root fix is to build the connection-coefficient route over the full
canonical operator

```lean
aperyCanonicalPsSeq =
  aperyPsSeq aperySconifold aperyRconifold
    Number.aperyQconifold Number.aperyPconifold
```

This object now exists in `AperyAGFSharpFromFrobenius.lean`, together with
the first formal half-branch theorem:

```lean
aperyCanonical_frobeniusSolution_is_solution_half
```

The old reduced branch package remains useful for leading-model and
indicial calculations, but it must not be used as the local basis for
`aperyGFAReal` connection coefficients.

