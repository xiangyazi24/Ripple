# F5 Connection Coefficients Gap

_Written 2026-04-30 to bridge `F5Bridge.lean` with external Apéry
literature._

This note records the exact external facts still missing from the F5
connection-coefficient route.  It is a paper-to-Lean checklist: once the
paper formulas are found, each item below should map to a named Lean lemma.

Do not import any coefficient formula from this note without checking the
paper and Lean's branch normalization.  Uncertain formulas are marked
`[needs paper confirmation]`.

## 1. Current Lean Gap

Relevant file:

```text
Ripple/Number/Frobenius/F5Bridge.lean
```

Remaining connection-level sorries:

```lean
theorem aperyRatioBound_step_c_connection_coefficients
    (_hbirk : AperyFrobeniusBirkhoffResidualSharpAsymptotics) :
    AperyFrobeniusConnectionCoefficientIdentification
```

and:

```lean
theorem aperyF5_missing_connection_cancellation_and_denominator_lower
    (_hcoef : AperyFrobeniusRatioFamilyCoefficientControl)
    (_hbirk : AperyFrobeniusBirkhoffResidualSharpAsymptotics)
    (_hconn : AperyFrobeniusConnectionCoefficientIdentification) :
    AperyF5DifferentiatedNumeratorBoundedNearConifold ∧
      AperyF5GFASecondRealThreeHalvesLowerNearConifold
```

The current `AperyFrobeniusConnectionCoefficientIdentification` is still only:

```lean
def AperyFrobeniusConnectionCoefficientIdentification : Prop :=
  ∃ C : ℝ, 0 < C
```

It should be strengthened to state real connection coefficients for the
ordinary Apéry generating functions `A` and `B` at the conifold point.

The C9 sub-sorry isolates the two analytic facts needed by step d:

```lean
def AperyF5DifferentiatedNumeratorBoundedNearConifold : Prop :=
  ∃ M : ℝ, 0 < M ∧
    ∃ δ : ℝ, 0 < δ ∧
      ∀ z : ℝ, 0 < z → z < aperyConifoldZ1 → aperyConifoldZ1 - z < δ →
        |aperyF5GFBSecondReal z - aperyZeta3Series * aperyF5GFASecondReal z| ≤ M
```

```lean
def AperyF5GFASecondRealThreeHalvesLowerNearConifold : Prop :=
  ∃ c : ℝ, 0 < c ∧
    ∃ δ : ℝ, 0 < δ ∧
      ∀ z : ℝ, 0 < z → z < aperyConifoldZ1 → aperyConifoldZ1 - z < δ →
        c ≤ |aperyConifoldZ1 - z| *
          Real.sqrt |aperyConifoldZ1 - z| * aperyF5GFASecondReal z
```

C9 already proves:

```lean
bounded numerator + denominator lower blow-up
  -> AperyF5DifferentiatedNumeratorThreeHalvesBound
```

So the remaining problem is coefficient identification, not final algebra.

## 2. Local Setup

The Apéry generating functions are:

```text
A(z) = sum_{n >= 0} a_n z^n
B(z) = sum_{n >= 0} b_n z^n
```

with:

```text
a_n = sum_{k=0}^n binom(n,k)^2 binom(n+k,k)^2.
```

Lean already proves the sequence-level limit:

```lean
theorem aperyB_div_aperyA_tendsto_zeta3 :
    Filter.Tendsto (fun n : ℕ => (aperyB n : ℝ) / (aperyA n : ℝ))
      Filter.atTop
      (nhds (∑' k : ℕ, 1 / ((k + 1 : ℝ) ^ 3)))
```

This verifies the global Apéry cancellation at coefficient level, but it does
not identify the local branch coefficients of `A(z)` and `B(z)`.

Conifold point:

```text
z₁ = 17 - 12 sqrt(2)
R  = 17 + 12 sqrt(2)
z₁ = 1 / R
```

Lean names:

```lean
Number.aperyConifoldZ1Poly
aperyConifoldZ1
aperyF5ConifoldZ1_eq_inv_R
```

`AperyConifoldIndicial.lean` proves:

```lean
lemma aperyConifoldIndicial_eq_zero_iff (ρ : ℝ) :
    aperyConifoldIndicial ρ = 0 ↔
      ρ = 0 ∨ ρ = (1 / 2 : ℝ) ∨ ρ = 1
```

Thus the local exponents are:

```text
0, 1/2, 1.
```

Use:

```text
t = z - z₁
epsilon = z₁ - z = -t
```

The F5 endpoint is the left limit `epsilon -> 0+`.

## 3. Existing Lean API

The connection predicate is:

```lean
def IsAperyConnectionCoeffsOn
    (a₀ a_half a₁ : ℝ) (f : ℝ → ℝ) (I : Set ℝ) : Prop :=
  ∀ t ∈ I, f (Number.aperyConifoldZ1Poly + t) =
    aperyBranchTriple a₀ a_half a₁ t
```

Branch names:

```lean
aperyBranchTriple
yAperyZero
yAperyHalf
yApery
aperyBranchAmplitude_zero
aperyBranchAmplitude_half
aperyBranchValue_one
```

Useful structural lemmas already exist:

```lean
IsAperyConnectionCoeffsOn.smul
IsAperyConnectionCoeffsOn.add
IsAperyConnectionCoeffsOn.sub
IsAperyConnectionCoeffsOn.right_endpoint
IsAperyConnectionCoeffsOn.a_half_from_f
IsAperyConnectionCoeffsOn.a_one_from_f
IsAperyConnectionCoeffsOn.cramer_recover
HasAperyConnectionCoeffsOn.cramer_recover
aperyExtractRegular
aperyExtractHalf
aperyExtractOne
```

So Lean can already manipulate triples and recover coefficients by Cramer
formulas.  What is missing is the actual transcendental triple for ordinary
`A` and `B`.

## 4. Missing Identities

Write the local expansions schematically:

```text
A(z) = α₀ phi_0(z) + α_h phi_h(z) + α₁ phi_1(z)
B(z) = β₀ phi_0(z) + β_h phi_h(z) + β₁ phi_1(z)
```

where `h` denotes exponent `1/2`.

### Identity A: A branch representation

Needed theorem shape:

```text
∃ I α₀ α_h α₁,
  IsAperyConnectionCoeffsOn α₀ α_h α₁ A I.
```

### Identity B: B branch representation

Needed theorem shape:

```text
∃ I β₀ β_h β₁,
  IsAperyConnectionCoeffsOn β₀ β_h β₁ B I.
```

If no ordinary `B` real-series def is available, add:

```lean
noncomputable def aperyGFBReal (z : ℝ) : ℝ :=
  ∑' n, (Number.aperyB n : ℝ) * z ^ n
```

F5 uses second derivatives:

```lean
aperyF5GFASecondReal
aperyF5GFBSecondReal
```

The ordinary route needs branch differentiation lemmas.  The direct F5 route
can state connection estimates directly for these second-derivative series.

### Identity C: half-power Apéry miracle

Key missing identity:

```text
β_h = ζ(3) * α_h.
```

Equivalently:

```text
β_h - ζ(3) α_h = 0.
```

This kills the `rho = 1/2` branch of `B - ζ(3) A`.  After two derivatives,
this is what makes:

```text
B''(z) - ζ(3) A''(z)
```

bounded near `z₁` from the left.

Lean output:

```lean
AperyF5DifferentiatedNumeratorBoundedNearConifold
```

### Identity D: nonzero half coefficient for A

Needed:

```text
α_h ≠ 0.
```

Prefer the sign-refined version:

```text
epsilon^(3/2) A''(z) >= c > 0
```

near `z₁`.  If Lean's half branch is normalized as:

```text
phi_h(z) = epsilon^(1/2) * (1 + O(epsilon)),
```

then:

```text
d^2/dz^2 epsilon^(1/2) = -1/4 * epsilon^(-3/2).
```

So under that convention:

```text
A''(z) ~ (-α_h / 4) * epsilon^(-3/2).
```

Since Lean proves `aperyF5GFASecondReal_pos`, this convention predicts
`α_h < 0`.  Check the actual `yAperyHalf` normalization before proving a
sign lemma.

Lean output:

```lean
AperyF5GFASecondRealThreeHalvesLowerNearConifold
```

### Identity E: regular coefficient cancellation, if needed

C10 requested recording:

```text
β₀ / α₀ = ζ(3)
```

equivalently:

```text
β₀ - ζ(3) α₀ = 0.
```

Caution: Lean's labels `0`, `1/2`, `1` are exponent labels.  Taylor
coefficient asymptotics at the radius are usually controlled by the
non-analytic half branch.  Some papers may call a leading asymptotic constant
`A_0`; do not assume that means Lean's exponent-0 coefficient `α₀`.

For F5 step d, Identity C is essential.

## 5. Literature Targets

### van der Poorten 1979

```text
Alfred van der Poorten,
"A proof that Euler missed... Apéry's proof of the irrationality of ζ(3)",
The Mathematical Intelligencer 1(4), 1979, 195-203.
```

Search for:

```text
"differential equation"
"singularities"
"second solution"
"17 + 12 sqrt 2"
"17 - 12 sqrt 2"
"zeta(3)"
```

Expected use: readable source for the Apéry differential equation and the
ζ(3) connection-constant cancellation.

### Apéry 1979

```text
Roger Apéry,
"Irrationalité de ζ(2) et ζ(3)",
Astérisque 61, 1979, 11-13.
```

Expected use: sequence and recurrence normalization.  Probably too short for
the full connection coefficient formulas.

### Beukers 1979

```text
Frits Beukers,
"A note on the irrationality of ζ(2) and ζ(3)",
Bulletin of the London Mathematical Society 11(3), 1979, 268-272.
```

Expected use: integral representation.  May prove cancellation indirectly by
identifying `B - ζA` with an integral whose local singularity is weaker than
the half branch.

### Beukers modular-form account

```text
Frits Beukers,
"Irrationality proofs using modular forms",
Astérisque 147-148, 1987.
```

Check page range from the paper copy before public citation.

Expected use: monodromy or period interpretation.  Probably not the shortest
Lean route because the repo has no modular-form infrastructure.

### Nesterenko 1996

```text
Yu. V. Nesterenko,
"A few remarks on ζ(3)",
Mathematical Notes 59(6), 1996, 625-636.
```

The Russian original is in `Matematicheskie Zametki` 59(6), 1996; check the
original page range from the paper copy if needed.

Expected use: explicit hypergeometric or Gamma-function constants.

Look for:

```text
a_n ~ C_A * (17 + 12 sqrt 2)^n * n^(-3/2)
b_n ~ C_B * (17 + 12 sqrt 2)^n * n^(-3/2)
C_B = ζ(3) C_A
C_A ≠ 0
```

If found, this should imply the half-branch identities after matching
singularity-analysis normalization.

## 6. Paper-to-Lean Checklist

1. Normalize variables:

```text
Lean z       = ordinary generating-function variable
Lean z₁      = 17 - 12 sqrt(2)
Lean t       = z - z₁
Lean epsilon = z₁ - z
R            = 17 + 12 sqrt(2) = 1 / z₁
```

2. Normalize branches against:

```lean
aperyBranchTriple
yAperyZero
yAperyHalf
yApery
```

Record scaling:

```text
paper_phi_0    = s0 * Lean_phi_0
paper_phi_half = sh * Lean_phi_half
paper_phi_1    = s1 * Lean_phi_1
```

3. Normalize `A` and `B` against `AperySequences.lean` and `F5Bridge.lean`.
Check for paper conventions using scaled or shifted `B`.

4. Strengthen step-c:

```lean
def AperyFrobeniusConnectionCoefficientIdentification : Prop :=
  ∃ I α₀ αh α₁ β₀ βh β₁,
    IsAperyConnectionCoeffsOn α₀ αh α₁ A I ∧
    IsAperyConnectionCoeffsOn β₀ βh β₁ B I ∧
    βh = aperyZeta3Series * αh ∧
    αh ≠ 0
```

Add a sign or lower-bound field if the paper gives it cleanly.

5. Keep paper constants separate from local calculus:

```lean
theorem aperyF5_numerator_bounded_from_half_cancellation :
    ... → AperyF5DifferentiatedNumeratorBoundedNearConifold
```

```lean
theorem aperyF5_denominator_lower_from_A_half :
    ... → AperyF5GFASecondRealThreeHalvesLowerNearConifold
```

Then `aperyF5_missing_connection_cancellation_and_denominator_lower` should
be short assembly.

## 7. Sanity Checks and Bottom Line

If a paper gives `a_n ~ C_A R^n n^(-3/2)` and
`b_n ~ C_B R^n n^(-3/2)`, Lean's proved theorem requires
`C_B / C_A = ζ(3)`.  The radius data must match
`R = 17 + 12 sqrt(2)` and `z₁ = 1 / R = 17 - 12 sqrt(2)`.

The imported half coefficient must also match `aperyF5GFASecondReal_pos`,
so it should imply `epsilon^(3/2) A''(z) >= c > 0`.  Finally, F5 uses
`B''(z) / A''(z)`, not `B(z) / A(z)`.

The two paper facts to find are:

```text
β_h = ζ(3) α_h
α_h is nonzero with the sign matching A'' > 0.
```

Equivalently, find the leading singular/asymptotic constants for `A` and `B`
at the conifold branch of exponent `1/2`, prove their ratio is ζ(3), and
verify the `A` constant is nonzero.

After that, the Lean work is:

1. strengthen `AperyFrobeniusConnectionCoefficientIdentification`;
2. prove branch calculus for numerator boundedness and denominator lower
   blow-up;
3. close `aperyF5_missing_connection_cancellation_and_denominator_lower`;
4. reuse the already closed C9 comparison theorem.
