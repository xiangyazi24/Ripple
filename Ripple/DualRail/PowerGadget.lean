/-
  Ripple.DualRail.PowerGadget — [BAC] §6 direct α^β construction.

  Given bounded PIVPs computing α > 0 and β, [BAC] §6 (Con 6.2, Thm 6.1)
  builds a 4-species extension (x₁, u, v, z) satisfying:

    x₁' = (x − 1) − x₁                             (low-pass filter, x₁ → α−1)
    u'  = (1 − v) · x₁'                            (u → ln α)
    v'  = (1 − v)² · x₁'                           (v = x₁/(1 + x₁))
    z'  = z · (y' · u + y · (1 − v) · x₁')         (z → α^β)

  with x₁(0) = u(0) = v(0) = 0, z(0) = 1.

  Note: [BAC] §6 assembles this as a single gadget — not as a composition of
  separate exp and log closures. The Lean stub in `Ripple/Core/CRNPipeline.lean`
  that factors α^β = exp(β · log α) via `h_exp` / `h_log` hypotheses is a
  placeholder; the faithful formalization is the direct 4-species construction
  implemented here.

  This file provides the **syntactic layer**:
    * the 4 new field polynomials (`x1RHS`, `uRHS`, `vRHS`, `zRHS`);
    * the combined `PolyPIVP ((d₁ + d₂) + 4)` (`powerPIVP`);
    * basic simp lemmas for output and initial values.

  Convergence (`z(t) → α^β`) and complexity preservation
  (`μ_{α^β}(r) = max(μ_α(r+C), μ_β(r+C)) + O(1)`) are downstream — separate
  files will build on top of this layer.
-/

import Ripple.Core.PIVP
import Ripple.Core.BoundedTime

set_option linter.style.show false

namespace Ripple.DualRail.Power

open MvPolynomial

variable {d₁ d₂ : ℕ}

/-! ## Indexing

We embed two input PIVPs of dimensions `d₁` and `d₂` into a combined state of
dimension `(d₁ + d₂) + 1 + 1 + 1 + 1`, nesting four `Fin.snoc` layers for the
new species `x₁`, `u`, `v`, `z` (in that order).
-/

/-- Embed a species index of the first input PIVP into the combined state. -/
def injX (d₁ d₂ : ℕ) (i : Fin d₁) : Fin ((d₁ + d₂) + 1 + 1 + 1 + 1) :=
  (Fin.castAdd d₂ i).castSucc.castSucc.castSucc.castSucc

/-- Embed a species index of the second input PIVP into the combined state. -/
def injY (d₁ d₂ : ℕ) (j : Fin d₂) : Fin ((d₁ + d₂) + 1 + 1 + 1 + 1) :=
  (Fin.natAdd d₁ j).castSucc.castSucc.castSucc.castSucc

/-- Index of the freshly introduced species `x₁` (innermost snoc). -/
def idxX1 (d₁ d₂ : ℕ) : Fin ((d₁ + d₂) + 1 + 1 + 1 + 1) :=
  (Fin.last (d₁ + d₂)).castSucc.castSucc.castSucc

/-- Index of `u` (logarithm tracker, second snoc). -/
def idxU (d₁ d₂ : ℕ) : Fin ((d₁ + d₂) + 1 + 1 + 1 + 1) :=
  (Fin.last ((d₁ + d₂) + 1)).castSucc.castSucc

/-- Index of `v` (auxiliary `v = x₁/(1+x₁)`, third snoc). -/
def idxV (d₁ d₂ : ℕ) : Fin ((d₁ + d₂) + 1 + 1 + 1 + 1) :=
  (Fin.last ((d₁ + d₂) + 1 + 1)).castSucc

/-- Index of `z` (power output, outermost snoc). -/
def idxZ (d₁ d₂ : ℕ) : Fin ((d₁ + d₂) + 1 + 1 + 1 + 1) :=
  Fin.last ((d₁ + d₂) + 1 + 1 + 1)

lemma injX_injective (d₁ d₂ : ℕ) : Function.Injective (injX d₁ d₂) := by
  intro i j h
  unfold injX at h
  have h₁ := (Fin.castSucc_injective _)
    ((Fin.castSucc_injective _)
      ((Fin.castSucc_injective _)
        ((Fin.castSucc_injective _) h)))
  exact Fin.castAdd_injective d₁ d₂ h₁

lemma injY_injective (d₁ d₂ : ℕ) : Function.Injective (injY d₁ d₂) := by
  intro i j h
  unfold injY at h
  have h₁ := (Fin.castSucc_injective _)
    ((Fin.castSucc_injective _)
      ((Fin.castSucc_injective _)
        ((Fin.castSucc_injective _) h)))
  exact Fin.natAdd_injective d₂ d₁ h₁

/-- Rename a polynomial over `Fin d₁` to the combined state along `injX`. -/
noncomputable def liftX (d₁ d₂ : ℕ) (p : MvPolynomial (Fin d₁) ℚ) :
    MvPolynomial (Fin ((d₁ + d₂) + 1 + 1 + 1 + 1)) ℚ :=
  rename (injX d₁ d₂) p

/-- Rename a polynomial over `Fin d₂` to the combined state along `injY`. -/
noncomputable def liftY (d₁ d₂ : ℕ) (p : MvPolynomial (Fin d₂) ℚ) :
    MvPolynomial (Fin ((d₁ + d₂) + 1 + 1 + 1 + 1)) ℚ :=
  rename (injY d₁ d₂) p

/-! ## The four new field polynomials

Per [BAC] Con 6.2:
  x₁' = (x − 1) − x₁
  u'  = (1 − v) · x₁'
  v'  = (1 − v)² · x₁'
  z'  = z · (y' · u + y · (1 − v) · x₁')
-/

/-- `x₁' = (X_x − 1) − X_{x₁}`. -/
noncomputable def x1RHS (d₁ d₂ : ℕ) (ix : Fin d₁) :
    MvPolynomial (Fin ((d₁ + d₂) + 1 + 1 + 1 + 1)) ℚ :=
  (X (injX d₁ d₂ ix) - 1) - X (idxX1 d₁ d₂)

/-- `u' = (1 − X_v) · x₁'`. -/
noncomputable def uRHS (d₁ d₂ : ℕ) (ix : Fin d₁) :
    MvPolynomial (Fin ((d₁ + d₂) + 1 + 1 + 1 + 1)) ℚ :=
  (1 - X (idxV d₁ d₂)) * x1RHS d₁ d₂ ix

/-- `v' = (1 − X_v)² · x₁'`. -/
noncomputable def vRHS (d₁ d₂ : ℕ) (ix : Fin d₁) :
    MvPolynomial (Fin ((d₁ + d₂) + 1 + 1 + 1 + 1)) ℚ :=
  (1 - X (idxV d₁ d₂)) ^ 2 * x1RHS d₁ d₂ ix

/-- `z' = X_z · (y' · X_u + X_y · (1 − X_v) · x₁')`,
where `y' = liftY (Py.field Py.output)` is the derivative of the y-output
species along its own PIVP. -/
noncomputable def zRHS (d₁ d₂ : ℕ) (ix : Fin d₁) (iy : Fin d₂)
    (yFieldAtOutput : MvPolynomial (Fin d₂) ℚ) :
    MvPolynomial (Fin ((d₁ + d₂) + 1 + 1 + 1 + 1)) ℚ :=
  X (idxZ d₁ d₂) *
    (liftY d₁ d₂ yFieldAtOutput * X (idxU d₁ d₂) +
     X (injY d₁ d₂ iy) * (1 - X (idxV d₁ d₂)) * x1RHS d₁ d₂ ix)

/-! ## Packaging the combined `PolyPIVP` -/

/-- Lifted input fields, packed via `Fin.append` on the first `d₁ + d₂` slots. -/
noncomputable def inputFields (Px : PolyPIVP d₁) (Py : PolyPIVP d₂) :
    Fin (d₁ + d₂) → MvPolynomial (Fin ((d₁ + d₂) + 1 + 1 + 1 + 1)) ℚ :=
  Fin.append (fun i => liftX d₁ d₂ (Px.field i))
             (fun j => liftY d₁ d₂ (Py.field j))

/-- Combined field on `Fin ((d₁ + d₂) + 4)` — input block followed by four
`Fin.snoc` layers (x₁, u, v, z). -/
noncomputable def powerField (Px : PolyPIVP d₁) (Py : PolyPIVP d₂) :
    Fin ((d₁ + d₂) + 1 + 1 + 1 + 1) →
      MvPolynomial (Fin ((d₁ + d₂) + 1 + 1 + 1 + 1)) ℚ :=
  Fin.snoc
   (Fin.snoc
    (Fin.snoc
     (Fin.snoc (inputFields Px Py) (x1RHS d₁ d₂ Px.output))
     (uRHS d₁ d₂ Px.output))
    (vRHS d₁ d₂ Px.output))
   (zRHS d₁ d₂ Px.output Py.output (Py.field Py.output))

/-- Combined initial condition: inputs unchanged, then `x₁(0) = u(0) = v(0) = 0`
and `z(0) = 1`. -/
noncomputable def powerInit (Px : PolyPIVP d₁) (Py : PolyPIVP d₂) :
    Fin ((d₁ + d₂) + 1 + 1 + 1 + 1) → ℚ :=
  Fin.snoc
   (Fin.snoc
    (Fin.snoc
     (Fin.snoc (Fin.append Px.init Py.init) (0 : ℚ))
     (0 : ℚ))
    (0 : ℚ))
   (1 : ℚ)

/-- The [BAC] §6 power gadget packaged as a `PolyPIVP`. Its `z` coordinate
converges to `α^β` whenever the inputs converge to `α` and `β`. Output is
the `z` slot. -/
noncomputable def powerPIVP (Px : PolyPIVP d₁) (Py : PolyPIVP d₂) :
    PolyPIVP ((d₁ + d₂) + 1 + 1 + 1 + 1) where
  field := powerField Px Py
  init := powerInit Px Py
  output := idxZ d₁ d₂

/-! ## Simp lemmas -/

@[simp] lemma powerPIVP_output (Px : PolyPIVP d₁) (Py : PolyPIVP d₂) :
    (powerPIVP Px Py).output = idxZ d₁ d₂ := rfl

@[simp] lemma powerPIVP_field_z (Px : PolyPIVP d₁) (Py : PolyPIVP d₂) :
    (powerPIVP Px Py).field (idxZ d₁ d₂) =
      zRHS d₁ d₂ Px.output Py.output (Py.field Py.output) := by
  show powerField Px Py (idxZ d₁ d₂) = _
  unfold powerField idxZ
  rw [Fin.snoc_last]

@[simp] lemma powerPIVP_field_v (Px : PolyPIVP d₁) (Py : PolyPIVP d₂) :
    (powerPIVP Px Py).field (idxV d₁ d₂) = vRHS d₁ d₂ Px.output := by
  show powerField Px Py (idxV d₁ d₂) = _
  unfold powerField idxV
  rw [show ((Fin.last ((d₁+d₂)+1+1)).castSucc :
      Fin ((d₁+d₂)+1+1+1+1)) = Fin.castSucc (Fin.last ((d₁+d₂)+1+1)) from rfl]
  rw [Fin.snoc_castSucc, Fin.snoc_last]

@[simp] lemma powerPIVP_field_u (Px : PolyPIVP d₁) (Py : PolyPIVP d₂) :
    (powerPIVP Px Py).field (idxU d₁ d₂) = uRHS d₁ d₂ Px.output := by
  show powerField Px Py (idxU d₁ d₂) = _
  unfold powerField idxU
  rw [show ((Fin.last ((d₁+d₂)+1)).castSucc.castSucc :
      Fin ((d₁+d₂)+1+1+1+1))
      = Fin.castSucc (Fin.castSucc (Fin.last ((d₁+d₂)+1))) from rfl]
  rw [Fin.snoc_castSucc, Fin.snoc_castSucc, Fin.snoc_last]

@[simp] lemma powerPIVP_field_x1 (Px : PolyPIVP d₁) (Py : PolyPIVP d₂) :
    (powerPIVP Px Py).field (idxX1 d₁ d₂) = x1RHS d₁ d₂ Px.output := by
  show powerField Px Py (idxX1 d₁ d₂) = _
  unfold powerField idxX1
  rw [show ((Fin.last (d₁+d₂)).castSucc.castSucc.castSucc :
      Fin ((d₁+d₂)+1+1+1+1))
      = Fin.castSucc (Fin.castSucc (Fin.castSucc (Fin.last (d₁+d₂)))) from rfl]
  rw [Fin.snoc_castSucc, Fin.snoc_castSucc, Fin.snoc_castSucc, Fin.snoc_last]

@[simp] lemma powerPIVP_init_z (Px : PolyPIVP d₁) (Py : PolyPIVP d₂) :
    (powerPIVP Px Py).init (idxZ d₁ d₂) = 1 := by
  show powerInit Px Py (idxZ d₁ d₂) = 1
  unfold powerInit idxZ
  rw [Fin.snoc_last]

@[simp] lemma powerPIVP_init_v (Px : PolyPIVP d₁) (Py : PolyPIVP d₂) :
    (powerPIVP Px Py).init (idxV d₁ d₂) = 0 := by
  show powerInit Px Py (idxV d₁ d₂) = 0
  unfold powerInit idxV
  rw [show ((Fin.last ((d₁+d₂)+1+1)).castSucc :
      Fin ((d₁+d₂)+1+1+1+1)) = Fin.castSucc (Fin.last ((d₁+d₂)+1+1)) from rfl]
  rw [Fin.snoc_castSucc, Fin.snoc_last]

@[simp] lemma powerPIVP_init_u (Px : PolyPIVP d₁) (Py : PolyPIVP d₂) :
    (powerPIVP Px Py).init (idxU d₁ d₂) = 0 := by
  show powerInit Px Py (idxU d₁ d₂) = 0
  unfold powerInit idxU
  rw [show ((Fin.last ((d₁+d₂)+1)).castSucc.castSucc :
      Fin ((d₁+d₂)+1+1+1+1))
      = Fin.castSucc (Fin.castSucc (Fin.last ((d₁+d₂)+1))) from rfl]
  rw [Fin.snoc_castSucc, Fin.snoc_castSucc, Fin.snoc_last]

@[simp] lemma powerPIVP_init_x1 (Px : PolyPIVP d₁) (Py : PolyPIVP d₂) :
    (powerPIVP Px Py).init (idxX1 d₁ d₂) = 0 := by
  show powerInit Px Py (idxX1 d₁ d₂) = 0
  unfold powerInit idxX1
  rw [show ((Fin.last (d₁+d₂)).castSucc.castSucc.castSucc :
      Fin ((d₁+d₂)+1+1+1+1))
      = Fin.castSucc (Fin.castSucc (Fin.castSucc (Fin.last (d₁+d₂)))) from rfl]
  rw [Fin.snoc_castSucc, Fin.snoc_castSucc, Fin.snoc_castSucc, Fin.snoc_last]

/-! ## Semantic field evaluation

These lemmas reduce the polynomial-valued field at each of the four new
species to its real-valued expression in the surrounding state `x`. They form
the bridge from the syntactic `PolyPIVP` layer to the semantic ODE layer used
in Picard-Lindelöf existence arguments.
-/

lemma evalField_x1 (Px : PolyPIVP d₁) (Py : PolyPIVP d₂)
    (x : Fin ((d₁ + d₂) + 1 + 1 + 1 + 1) → ℝ) :
    (powerPIVP Px Py).toPIVP.field x (idxX1 d₁ d₂)
      = (x (injX d₁ d₂ Px.output) - 1) - x (idxX1 d₁ d₂) := by
  show ((powerPIVP Px Py).field (idxX1 d₁ d₂)).eval₂ (Rat.castHom ℝ) x = _
  rw [powerPIVP_field_x1]
  unfold x1RHS
  simp only [MvPolynomial.eval₂_sub, MvPolynomial.eval₂_X, MvPolynomial.eval₂_one]

lemma evalField_u (Px : PolyPIVP d₁) (Py : PolyPIVP d₂)
    (x : Fin ((d₁ + d₂) + 1 + 1 + 1 + 1) → ℝ) :
    (powerPIVP Px Py).toPIVP.field x (idxU d₁ d₂)
      = (1 - x (idxV d₁ d₂))
          * ((x (injX d₁ d₂ Px.output) - 1) - x (idxX1 d₁ d₂)) := by
  show ((powerPIVP Px Py).field (idxU d₁ d₂)).eval₂ (Rat.castHom ℝ) x = _
  rw [powerPIVP_field_u]
  unfold uRHS x1RHS
  simp only [MvPolynomial.eval₂_sub, MvPolynomial.eval₂_mul,
             MvPolynomial.eval₂_X, MvPolynomial.eval₂_one]

lemma evalField_v (Px : PolyPIVP d₁) (Py : PolyPIVP d₂)
    (x : Fin ((d₁ + d₂) + 1 + 1 + 1 + 1) → ℝ) :
    (powerPIVP Px Py).toPIVP.field x (idxV d₁ d₂)
      = (1 - x (idxV d₁ d₂)) ^ 2
          * ((x (injX d₁ d₂ Px.output) - 1) - x (idxX1 d₁ d₂)) := by
  show ((powerPIVP Px Py).field (idxV d₁ d₂)).eval₂ (Rat.castHom ℝ) x = _
  rw [powerPIVP_field_v]
  unfold vRHS x1RHS
  simp only [MvPolynomial.eval₂_sub, MvPolynomial.eval₂_mul, MvPolynomial.eval₂_pow,
             MvPolynomial.eval₂_X, MvPolynomial.eval₂_one]

lemma evalField_z (Px : PolyPIVP d₁) (Py : PolyPIVP d₂)
    (x : Fin ((d₁ + d₂) + 1 + 1 + 1 + 1) → ℝ) :
    (powerPIVP Px Py).toPIVP.field x (idxZ d₁ d₂)
      = x (idxZ d₁ d₂)
        * ((Py.field Py.output).eval₂ (Rat.castHom ℝ) (fun j => x (injY d₁ d₂ j))
              * x (idxU d₁ d₂)
           + x (injY d₁ d₂ Py.output) * (1 - x (idxV d₁ d₂))
              * ((x (injX d₁ d₂ Px.output) - 1) - x (idxX1 d₁ d₂))) := by
  show ((powerPIVP Px Py).field (idxZ d₁ d₂)).eval₂ (Rat.castHom ℝ) x = _
  rw [powerPIVP_field_z]
  unfold zRHS x1RHS liftY
  simp only [MvPolynomial.eval₂_mul, MvPolynomial.eval₂_add, MvPolynomial.eval₂_sub,
             MvPolynomial.eval₂_X, MvPolynomial.eval₂_one]
  rw [MvPolynomial.eval₂_rename]
  rfl

end Ripple.DualRail.Power
