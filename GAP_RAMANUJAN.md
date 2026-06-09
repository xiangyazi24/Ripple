# GAP_RAMANUJAN

Status: the theorem `Ripple.Number.Ramanujan1914.ramanujan_one_over_pi`
is still open.  No axiom, `proof_wanted`, or equivalent placeholder was used.

This file records the Lean-level gap after actually probing the available
Mathlib infrastructure.

## Import Probe

The following imports were tested in `/tmp/PiImportProbe.lean` and
`/tmp/Hypergeom3F2SignatureProbe.lean`:

```lean
import Mathlib.NumberTheory.ModularForms.JacobiTheta.OneVariable
import Mathlib.NumberTheory.ModularForms.DedekindEta
import Mathlib.NumberTheory.ModularForms.Delta
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.Basic
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.QExpansion
import Mathlib.NumberTheory.ModularForms.QExpansion
import Mathlib.NumberTheory.ModularForms.LevelOne
import Mathlib.Analysis.SpecialFunctions.OrdinaryHypergeometric
import Mathlib.Analysis.SpecialFunctions.Elliptic.Weierstrass
import Ripple.Number.Ramanujan1914
```

Available and checked:

```lean
#check jacobiTheta
#check jacobiTheta_S_smul
#check ModularForm.eta
#check ModularForm.logDeriv_eta_eq_E2
#check ModularForm.delta
#check ModularForm.delta_S_invariant
#check ordinaryHypergeometric
#check ordinaryHypergeometric_eq_tsum
#check PeriodPair.weierstrassP
```

Not available under searched names:

- generalized hypergeometric `₃F₂`;
- Clausen identity relating this `₃F₂` to a square of a `₂F₁`;
- modular lambda / elliptic modulus API;
- Klein `j`-invariant API;
- singular-modulus evaluation producing the Ramanujan `396^4` constants;
- the relevant quasi-modular derivative evaluation.

Searches used:

```bash
rg -n "Clausen|ellipticIntegral|complete.*elliptic|modular.*lambda|singular modulus|Heegner"
rg -n "jInvariant|jFunction|klein|Klein|modularJ|singularModulus|396|9801"
rg -n "3F2|generalized|ordinaryHypergeometric"
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

noncomputable def ramanujanF : ℂ → ℂ :=
  hypergeom3F2 (1/4) (1/2) (3/4) 1 1

noncomputable def ramanujanX : ℂ := 1 / (99 : ℂ)^4
```

The coefficient bridge needed before any modular proof can touch the current
file is:

```lean
theorem ramanujan_a_eq_3F2_coeff (n : ℕ) :
    (Ripple.Number.Ramanujan1914.a n : ℂ) =
      hypergeom3F2Coeff (1/4) (1/2) (3/4) 1 1 n * (256 : ℂ)^n
```

Then the current series is equivalent to:

```lean
theorem ramanujanSeries_eq_3F2_derivative :
    (Ripple.Number.Ramanujan1914.ramanujanSeries : ℂ) =
      1103 * ramanujanF ramanujanX +
        26390 * ramanujanX * deriv ramanujanF ramanujanX
```

The missing modular evaluation, in exact typed form, is:

```lean
theorem ramanujan_3F2_modular_eval_396 :
    (2 * (Real.sqrt 2 : ℂ) / 9801) *
      (1103 * ramanujanF ramanujanX +
        26390 * ramanujanX * deriv ramanujanF ramanujanX) =
    1 / (Real.pi : ℂ)
```

Together with real/complex coercion cleanup, this would prove:

```lean
theorem ramanujanScaledSum_eq_pi_inv :
    Ripple.Number.Ramanujan1914.ramanujanScaledSum = 1 / Real.pi
```

and then the existing wrapper closes `ramanujan_one_over_pi`.

## Missing Modular Lemmas

The modular path needs the following concrete theorem families.  These are not
present in Mathlib under the searched names.

### Generalized Hypergeometric Infrastructure

```lean
theorem hypergeom3F2_hasDerivAt
    {a b c d e x : ℂ} (hx : ‖x‖ < 1) :
    HasDerivAt (hypergeom3F2 a b c d e)
      (∑' n : ℕ, ((n + 1 : ℂ) *
        hypergeom3F2Coeff a b c d e (n + 1) * x ^ n)) x
```

```lean
theorem hypergeom3F2_clausen_quarter_half_three_quarter
    {x : ℂ} (hx : ‖x‖ < 1) :
    hypergeom3F2 (1/4) (1/2) (3/4) 1 1 x =
      ordinaryHypergeometric (1/8 : ℂ) (3/8 : ℂ) 1 x ^ 2
```

The exact `₂F₁` parameters may be adjusted depending on the chosen
normalization, but the needed theorem must be a typed Clausen identity for the
Ramanujan coefficient sequence.

### Modular Lambda / Theta Bridge

A usable bridge can be expressed via theta constants or eta quotients.  One
possible theta-constant API is:

```lean
noncomputable def theta2_const (τ : UpperHalfPlane) : ℂ := ...
noncomputable def theta3_const (τ : UpperHalfPlane) : ℂ := jacobiTheta τ
noncomputable def modularLambda (τ : UpperHalfPlane) : ℂ :=
  (theta2_const τ / theta3_const τ) ^ 4

theorem hypergeom2F1_eq_theta3_sq
    (τ : UpperHalfPlane) :
    ordinaryHypergeometric (1/8 : ℂ) (3/8 : ℂ) 1 (modularLambda τ) =
      theta3_const τ ^ 2
```

If the proof is developed through complete elliptic integrals instead, replace
this with the corresponding `₂F₁ = 2/pi * K` and theta/AGM evaluation lemmas.

### Singular Modulus And Derivative Evaluation

The exact constants in the current theorem require a CM point theorem.  A
workable shape is:

```lean
noncomputable def ramanujanTau58 : UpperHalfPlane := ...

theorem ramanujan_modularLambda_tau58 :
    modularLambda ramanujanTau58 = ramanujanX

theorem ramanujan_theta_derivative_combo_tau58 :
    (2 * (Real.sqrt 2 : ℂ) / 9801) *
      (1103 * ramanujanF ramanujanX +
        26390 * ramanujanX * deriv ramanujanF ramanujanX) =
    1 / (Real.pi : ℂ)
```

The second theorem is where the quasi-modular `E2` correction enters.  Mathlib
has `EisensteinSeries.E2` and its transform under `S`, but not the singular
value and derivative calculation producing `1103`, `26390`, and `9801`.

## Current Block

The current Lean environment has enough analytic primitives to start a modular
forms development, but it does not contain the concrete 1914 Ramanujan modular
evaluation.  The blocker is not algebraic rewriting of the existing series; it
is the absent CM/theta evaluation theorem above.
