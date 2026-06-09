# GAP_CHUDNOVSKY

Status: the theorem `Ripple.Number.Chudnovsky1989.chudnovsky_one_over_pi`
is still open.  No axiom, `proof_wanted`, or equivalent placeholder was used.

This file records the Lean-level gap after probing Mathlib.  Mathlib has a
file `Mathlib.Analysis.Real.Pi.Chudnovsky`, but it contains only definitions
and:

```lean
proof_wanted chudnovskySum_eq_pi_inv : chudnovskySum = π⁻¹
```

That theorem was not imported or used as evidence.

## Import Probe

The following imports were tested in `/tmp/PiImportProbe.lean` and
`/tmp/Hypergeom3F2SignatureProbe.lean`:

```lean
import Mathlib.Analysis.Real.Pi.Chudnovsky
import Mathlib.NumberTheory.ModularForms.JacobiTheta.OneVariable
import Mathlib.NumberTheory.ModularForms.DedekindEta
import Mathlib.NumberTheory.ModularForms.Delta
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.Basic
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.QExpansion
import Mathlib.NumberTheory.ModularForms.QExpansion
import Mathlib.NumberTheory.ModularForms.LevelOne
import Mathlib.Analysis.SpecialFunctions.OrdinaryHypergeometric
import Mathlib.Analysis.SpecialFunctions.Elliptic.Weierstrass
import Ripple.Number.Chudnovsky1989
```

Available and checked:

```lean
#check jacobiTheta
#check jacobiTheta_S_smul
#check ModularForm.eta
#check ModularForm.logDeriv_eta_eq_E2
#check ModularForm.delta
#check ModularForm.delta_S_invariant
#check ModularForm.delta_T_invariant
#check ordinaryHypergeometric
#check PeriodPair.weierstrassP
```

Not available under searched names:

- generalized hypergeometric `₃F₂`;
- Chudnovsky's `3F2(1/6,1/2,5/6;1,1;z)` modular parametrization;
- Klein `j`-invariant;
- theorem `j((1 + sqrt(-163))/2) = -640320^3`;
- class-number-1 / Heegner singular modulus evaluation in a form usable here;
- the derivative/quasi-modular evaluation producing `13591409` and
  `545140134`.

Searches used:

```bash
rg -n "jInvariant|jFunction|klein|Klein|modularJ|singularModulus|CM|Heegner|640320"
rg -n "Chudnovsky|chudnovskyTerm|proof_wanted"
rg -n "3F2|generalized|ordinaryHypergeometric|Clausen"
```

## Typed Local Target Decomposition

The following declarations typechecked in `/tmp/Hypergeom3F2SignatureProbe.lean`.
They are the exact Lean shape of the missing hypergeometric layer.

```lean
noncomputable def hypergeom3F2Coeff (a b c d e : ℂ) (n : ℕ) : ℂ :=
  ((Nat.factorial n : ℂ)⁻¹ *
    (Polynomial.eval a (ascPochhammer ℂ n)) *
    (Polynomial.eval b (ascPochhammer ℂ n)) *
    (Polynomial.eval c (ascPochhammer ℂ n)) *
    (Polynomial.eval d (ascPochhammer ℂ n))⁻¹ *
    (Polynomial.eval e (ascPochhammer ℂ n))⁻¹)

noncomputable def hypergeom3F2 (a b c d e : ℂ) (z : ℂ) : ℂ :=
  ∑' n : ℕ, hypergeom3F2Coeff a b c d e n * z ^ n

noncomputable def chudnovskyF : ℂ → ℂ :=
  hypergeom3F2 (1/6) (1/2) (5/6) 1 1

noncomputable def chudnovskyX : ℂ := -1728 / (640320 : ℂ)^3
```

The coefficient bridge needed before the modular proof can touch the current
file is:

```lean
theorem chudnovsky_a_eq_3F2_coeff (n : ℕ) :
    (Ripple.Number.Chudnovsky1989.a n : ℂ) =
      hypergeom3F2Coeff (1/6) (1/2) (5/6) 1 1 n * (1728 : ℂ)^n
```

Then the current series is equivalent to:

```lean
theorem chudnovskySeries_eq_3F2_derivative :
    (Ripple.Number.Chudnovsky1989.chudnovskySeries : ℂ) =
      13591409 * chudnovskyF chudnovskyX +
        545140134 * chudnovskyX * deriv chudnovskyF chudnovskyX
```

The missing modular evaluation, in exact typed form, is:

```lean
theorem chudnovsky_3F2_modular_eval_163 :
    (12 : ℂ) / (((640320 : ℝ)^(3/2 : ℝ) : ℝ) : ℂ) *
      (13591409 * chudnovskyF chudnovskyX +
        545140134 * chudnovskyX * deriv chudnovskyF chudnovskyX) =
    1 / (Real.pi : ℂ)
```

Together with real/complex coercion cleanup, this would prove:

```lean
theorem chudnovskyScaledSum_eq_pi_inv :
    Ripple.Number.Chudnovsky1989.chudnovskyScaledSum = 1 / Real.pi
```

and then the existing wrapper closes `chudnovsky_one_over_pi`.

## Missing Modular Lemmas

The following theorem families are the concrete missing infrastructure.

### Generalized Hypergeometric Infrastructure

```lean
theorem hypergeom3F2_hasDerivAt
    {a b c d e x : ℂ} (hx : ‖x‖ < 1) :
    HasDerivAt (hypergeom3F2 a b c d e)
      (∑' n : ℕ, ((n + 1 : ℂ) *
        hypergeom3F2Coeff a b c d e (n + 1) * x ^ n)) x
```

```lean
theorem chudnovsky_3F2_radius_one :
    (FormalMultilinearSeries.ofScalars ℂ
      (hypergeom3F2Coeff (1/6) (1/2) (5/6) 1 1)).radius = 1
```

This is not covered by `ordinaryHypergeometricSeries_radius_eq_one`, because
Mathlib's current hypergeometric file implements only ordinary/Gaussian `₂F₁`.

### Modular Parametrization

One possible route is through the Klein invariant:

```lean
noncomputable def kleinJ (τ : UpperHalfPlane) : ℂ := ...

theorem kleinJ_eq_E4_cubed_div_delta
    (τ : UpperHalfPlane) :
    kleinJ τ = E4 τ ^ 3 / ModularForm.delta τ
```

Mathlib currently has `delta`, `eta`, and `E2`, but no exposed `E4`, `E6`,
or `kleinJ` API found by search/import probe.

The required hypergeometric parametrization can be packaged as:

```lean
theorem chudnovsky_3F2_param_by_kleinJ
    (τ : UpperHalfPlane) :
    chudnovskyF (1728 / kleinJ τ) = modularWeightOneExpression τ
```

The right-hand side depends on the chosen route: Eisenstein-series
normalization, theta constants, or elliptic periods.  The current Mathlib API
does not provide the needed object or theorem.

### CM Singular Value And Derivative Evaluation

The constants in the current theorem require discriminant `163`.

```lean
noncomputable def tau163 : UpperHalfPlane := ...

theorem kleinJ_tau163 :
    kleinJ tau163 = -(640320 : ℂ)^3
```

The derivative/quasi-modular part must then produce the linear coefficient:

```lean
theorem chudnovsky_derivative_combo_tau163 :
    (12 : ℂ) / (((640320 : ℝ)^(3/2 : ℝ) : ℝ) : ℂ) *
      (13591409 * chudnovskyF chudnovskyX +
        545140134 * chudnovskyX * deriv chudnovskyF chudnovskyX) =
    1 / (Real.pi : ℂ)
```

This is the exact content absent from Mathlib's
`Analysis.Real.Pi.Chudnovsky`: the file explicitly leaves the final equality
as `proof_wanted`.

## Current Block

The current Lean environment contains pieces of modular-form analysis
(`eta`, `delta`, `E2`, theta transforms, q-expansion), but it does not contain
the Klein invariant, its CM value at discriminant `163`, or the generalized
`₃F₂` parametrization/derivative evaluation needed to derive the constants
`640320`, `13591409`, and `545140134`.
