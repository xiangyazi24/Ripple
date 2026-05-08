# Connection Coefficients from the Apéry Literature (4-source synthesis)

_Written 2026-04-30 from the local PDFs in `projects/Ripple/ref/`._

This note records what the four supplied PDFs actually say about the Apéry
connection-coefficient gap in `F5Bridge.lean`.  It separates direct identities
from consequences that still require Lean-side branch normalization.

Notation used here:

- `A(z) = sum a_n z^n`, with `A(z) = 1 + 5z + 73z^2 + 1445z^3 + ...`.
- `B(z) = sum b_n z^n`, with `B(z) = 6z + (351/4)z^2 + ...`.
- `z1 = 17 - 12 sqrt(2) = (sqrt(2)-1)^4 = (1-sqrt(2))^4`.
- The repository's `A` is `aperyA`; the repository's `B` is `aperyB`.
- vdPoorten/Beukers use `b(X)` for our `A(X)` and `a(X)` for our `B(X)`.

## What We Found

### From vdPoorten 1979

Source:

```text
Alfred van der Poorten,
"A proof that Euler missed... Apéry's proof of the irrationality of ζ(3)",
The Mathematical Intelligencer 1(4), 1979, 195-203.
```

PDF status: scanned; `pdftotext` failed, so page 203 was OCR'd from PDF page 9.

Key location: printed p. 203, final discussion, attributed to Beukers.

Content found:

- vdPoorten writes the Apéry differential equation with leading factor
  `X^4 - 34 X^3 + X^2`.
- He says it has two `G`-function solutions:
  - `a(X) = 6X + a_2 X^2 + ...`;
  - `b(X) = 1 + b_1 X + b_2 X^2 + ...`.
- In repository notation, these are:
  - `a(X)` = our `B(X)`;
  - `b(X)` = our `A(X)`.
- The key statement is that `a(X) - ζ(3) b(X)` is regular, indeed vanishes,
  at `α' = (1 - sqrt(2))^4 = z1`.

Interpretation in repository notation:

```text
B(z) - ζ(3) A(z) is regular and vanishes at z = z1.
```

This is the strongest direct source found among the four PDFs for the
connection-coefficient cancellation needed by F5.

What it gives directly:

```text
regularity of B - ζA at z1
value (B - ζA)(z1) = 0
```

What it does not spell out:

```text
the numerical half-branch coefficient α_h(A)
the sign/nonzero proof for α_h(A)
the exact normalization relative to Lean's yAperyHalf
```

### From Beukers 1979

Source:

```text
Frits Beukers,
"A note on the irrationality of ζ(2) and ζ(3)",
Bulletin of the London Mathematical Society 11(3), 1979, 268-272.
```

Relevant location: Theorem 2, pp. 270-272.

Content found:

Beukers gives the integral proof for ζ(3).  With Legendre-type polynomials
`P_n`, he considers:

```text
integral of (-log(xy))/(1-xy) * P_n(x) P_n(y) dx dy.
```

The paper states that this integral equals a rational linear form in ζ(3):

```text
(A_n + B_n ζ(3)) * d_n^(-3)
```

for integers `A_n, B_n`, where `d_n = lcm(1,...,n)`.  After changes of
variables and partial integrations, Beukers obtains the exponential bound:

```text
0 < |A_n + B_n ζ(3)| < 2 ζ(3) * 27^n * (sqrt(2)-1)^(4n)
```

for sufficiently large `n`.

Interpretation for F5:

This paper does not give explicit conifold connection coefficients.  It does
give an independent proof that the Apéry linear forms have the extra
`(sqrt(2)-1)^4 = z1` scale.  It is consistent with, but weaker than, the
vdPoorten/Beukers regularity statement for `B - ζA`.

Use in Lean:

- useful as paper evidence for the smallness of the minimal solution;
- not directly enough to close the local `B'' - ζA''` bound without a
  transfer theorem from integral estimates to branch regularity.

### From Beukers 1987

Source:

```text
Frits Beukers,
"Irrationality proofs using modular forms",
Astérisque 147-148, 1987, 271-283.
```

Relevant locations:

- pp. 274-276: modular function `t(τ)` and Theorem 1 for ζ(3).
- p. 274: branching values of `t(τ)`.
- p. 276: the key non-branching statement for `E(t)(f(t)-ζ(3))`.

Content found:

Beukers defines a modular function `t(τ)` for `Γ_1(6)` satisfying:

```text
t(i∞) = 0
t(i/sqrt(6)) = (sqrt(2)-1)^4
t(2/5 + i/(5 sqrt(6))) = (sqrt(2)+1)^4
```

He defines modular forms/functions `E(τ)` and `f(τ)` and records expansions:

```text
E(t) = 1 + 5t + 73t^2 + 1445t^3 + ...
E(t) f(t) = 6t + (351/4)t^2 + ...
```

The remark immediately after Theorem 1 says:

```text
1, 5, 73, 1445, ... are exactly Apéry's numbers for ζ(3).
```

In repository notation:

```text
E(t)      = A(t)
E(t)f(t) = B(t)
```

The key equation in the proof is the modular transformation identity:

```text
E(-1/(6τ)) * (f(-1/(6τ)) - ζ(3))
  = E(τ) * (f(τ) - ζ(3)).
```

Since:

```text
E(t)(f(t)-ζ(3)) = B(t) - ζ(3)A(t),
```

Beukers then says that although the inverse map `t -> τ` branches at
`t = (sqrt(2)-1)^4`, the function:

```text
E(t)(f(t)-ζ(3))
```

has no branch point there, and its radius of convergence is at least the next
branching value:

```text
(sqrt(2)+1)^4.
```

Interpretation in repository notation:

```text
B(t) - ζ(3)A(t) has no branch point at t = z1.
```

Together with the expansion at `t=0`, this is the modular-forms version of
the vdPoorten p. 203 statement.  It is the cleanest supplied source for the
half-branch cancellation:

```text
β_h - ζ(3) α_h = 0.
```

What it gives directly:

```text
regularity/no branching of B - ζA at z1
radius jumps from (sqrt(2)-1)^4 to at least (sqrt(2)+1)^4
```

What it does not directly give:

```text
the explicit numeric value of α_h(A)
the sign of α_h(A) in Lean's normalization
```

### From Nesterenko 1996

Source PDF:

```text
Yu. V. Nesterenko,
"Modular functions and transcendence questions",
Sbornik: Mathematics 187(9), 1996, 1319-1348.
```

Note: despite the local filename `Nesterenko-1996-zeta3-remarks.pdf`, the
PDF title is not "A few remarks on ζ(3)".

Text search result:

- no occurrence of `Apéry` / `Apery`;
- no explicit ζ(3) Apéry connection-coefficient formula found;
- no direct use of the conifold values `17 ± 12 sqrt(2)` found.

Content found:

The paper studies modular functions and transcendence questions in a broad
setting.  It discusses modular differential equations and cites Nesterenko's
earlier work, but this supplied PDF does not appear to contain the explicit
Apéry ζ(3) connection coefficients needed for F5.

Conclusion:

```text
[not found in this PDF]
```

If Nesterenko has the desired explicit hypergeometric/Gamma constants, they
are likely in a different paper, not this supplied PDF.

## Synthesis: Identities We Can Use

### Identity (R-V): regular and vanishes at z1

Statement:

```text
B(z) - ζ(3) A(z) is regular and vanishes at z = z1.
```

Sources:

- vdPoorten 1979, printed p. 203, explicitly says regular and vanishing at
  `(1 - sqrt(2))^4`, attributed to Beukers.
- Beukers 1987, pp. 274-276, proves modularly that `E(t)(f(t)-ζ(3))` does
  not branch at `t=(sqrt(2)-1)^4`; with `E(t)=A(t)` and `E(t)f(t)=B(t)`.

Connection-coefficient interpretation:

For a local branch decomposition:

```text
B - ζA = c0 * phi_0 + ch * phi_1/2 + c1 * phi_1.
```

Regularity/no branch gives:

```text
ch = 0.
```

Vanishing at `z1` gives:

```text
c0 = 0
```

provided Lean's `phi_0(z1) = 1` and the other positive-exponent branches
vanish at the endpoint, as the current branch API is designed to express.

Thus:

```text
B - ζA = c1 * phi_1 + higher regular/less singular terms.
```

F5 consequence:

The half-branch coefficient in `B - ζA` is zero, so the `epsilon^(-3/2)`
singularity in the second derivative cancels:

```text
B''(z) - ζA''(z) is bounded near z1 from the left.
```

This is the mathematical content of:

```lean
AperyF5DifferentiatedNumeratorBoundedNearConifold
```

### Identity (NZ): A has nonzero half branch

Statement needed:

```text
A(z) has a nonzero phi_1/2 coefficient at z1.
```

Equivalent F5 form:

```text
epsilon^(3/2) A''(z) is bounded below by a positive constant.
```

Source status among the four PDFs:

```text
[not explicitly found]
```

Evidence:

- Beukers 1987 says `E(t)=A(t)` has radius controlled by the first branching
  value `z1 = (sqrt(2)-1)^4`, while `E(t)(f(t)-ζ(3))` avoids that branch and
  reaches the next branching value.  This strongly indicates `A` itself has
  a genuine branch at `z1`.
- However, the supplied text does not state an explicit coefficient
  `α_h(A) ≠ 0` or its sign.

Lean consequence needed:

```lean
AperyF5GFASecondRealThreeHalvesLowerNearConifold
```

This remains the one missing identity not directly stated by the supplied
PDFs.

## Lean Translation Suggestions

### 1. Define ordinary real B series

If the ordinary route is chosen, add later:

```lean
noncomputable def aperyGFBReal (z : ℝ) : ℝ :=
  ∑' n, (Number.aperyB n : ℝ) * z ^ n
```

### 2. Define the Apéry difference

Suggested later theorem-level object:

```lean
noncomputable def aperyGFDiffReal (z : ℝ) : ℝ :=
  aperyGFBReal z - aperyZeta3Series * Ripple.Frobenius.aperyGFAReal z
```

### 3. State the literature-backed regularity theorem

The clean paper-citation target is:

```lean
theorem aperyGFDiffReal_regular_at_conifold :
    -- in the local branch basis, no rho=1/2 component
    ...
```

and, separately:

```lean
theorem aperyGFDiffReal_vanishes_at_conifold :
    aperyGFDiffReal aperyConifoldZ1 = 0
```

The first theorem is the one that matters for the bounded second derivative
numerator.  The second theorem records the vdPoorten "vanishes" part and
kills the regular endpoint coefficient.

### 4. Strengthen step-c

Replace the placeholder Prop by something like:

```lean
def AperyFrobeniusConnectionCoefficientIdentification : Prop :=
  ∃ I α0 αh α1 β0 βh β1,
    IsAperyConnectionCoeffsOn α0 αh α1 A I ∧
    IsAperyConnectionCoeffsOn β0 βh β1 B I ∧
    βh = aperyZeta3Series * αh ∧
    β0 = aperyZeta3Series * α0 ∧
    αh ≠ 0
```

The `βh` equality is supported by Beukers 1987/vdPoorten 1979.  The `β0`
equality is supported by the "vanishes" statement if Lean's endpoint
normalization is as expected.  The `αh ≠ 0` field is still not explicitly
found in these four PDFs.

### 5. Close C9's two pieces separately

Use regularity/no-branching of `B - ζA` to prove:

```lean
theorem aperyF5_numerator_bounded_from_regular_difference :
    ... → AperyF5DifferentiatedNumeratorBoundedNearConifold
```

Use the nonzero half branch of `A` to prove:

```lean
theorem aperyF5_denominator_lower_from_A_half_branch :
    ... → AperyF5GFASecondRealThreeHalvesLowerNearConifold
```

Then:

```lean
theorem aperyF5_missing_connection_cancellation_and_denominator_lower
```

should be short assembly.

## Open Questions

1. The four supplied PDFs do not give an explicit numeric formula for
   `α_h(A)` in Lean's branch normalization.
2. The sign of `α_h(A)` is not explicitly stated.  It must match
   `aperyF5GFASecondReal_pos`, hence imply `epsilon^(3/2) A''(z) > 0`.
3. Beukers 1987 gives a modular non-branching statement for `B-ζA`; turning
   it into Lean still requires either:
   - formalizing enough modular-function theory, or
   - accepting a paper-cited analytic theorem as a named bridge lemma.
4. Beukers 1979 gives strong integral linear-form bounds, but not local
   conifold coefficients.  It is not by itself enough for the F5 local
   numerator theorem.

## Recommended Next Lean Steps

1. Add ordinary `aperyGFBReal` if needed.
2. Add a paper-backed bridge theorem:

```lean
theorem aperyGFB_sub_zeta_mul_GFA_regular_vanishes_at_conifold :
    -- B - ζA is regular and vanishes at z1
    ...
```

3. Split that theorem into the two branch-coefficient consequences:

```lean
βh = aperyZeta3Series * αh
β0 = aperyZeta3Series * α0
```

4. Prove or source the remaining nonzero denominator fact:

```lean
αh ≠ 0
```

5. Use the already closed C9 comparison theorem to discharge step d once the
   numerator boundedness and denominator lower bound are available.
