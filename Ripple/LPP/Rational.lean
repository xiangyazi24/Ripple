/-
  Ripple.LPP.Rational — Rational Numbers are LPP-Computable

  From [LPP] Lemma 10 / Bournez et al. Lemma 3:
  For any rational ν = p/q ∈ [0,1], the unimolecular LPP with q states
  and cyclic transitions X₁ → X₂ → ··· → X_q → X₁ computes ν.

  Each state converges to 1/q, so marking p states gives limit p/q = ν.

  The ODE for this system (on the simplex Σxᵢ = 1):
    x'ᵢ = x_{i-1} - xᵢ    (indices mod q)

  This is a unimolecular population protocol (UPP).
-/

import Ripple.LPP.Defs
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Logic.Equiv.Fin.Rotate

namespace Ripple

/-! ## Cyclic Unimolecular Protocol

The simplest LPP: q+1 states with transitions Xᵢ → X_{i+1 mod (q+1)}.

The formal (bimolecular-embedded) balance equation is:
  x'ᵢ = (x_{pred(i)} - xᵢ) · (Σ xₖ)
with production f_r(x) = (x_{pred(r)} + x_r) · (Σ xₖ) (homogeneous degree 2).

On the simplex (Σxₖ = 1), this reduces to x'ᵢ = x_{pred(i)} - xᵢ.

The bimolecular embedding: the unimolecular reaction Xᵢ → X_{pred(i)}
becomes Xᵢ + X_j → X_{pred(i)} + X_j for all j. -/

/-- The predecessor permutation: the inverse of finRotate.
Maps i ↦ i-1 mod (q+1). -/
abbrev predPerm (q : ℕ) : Equiv.Perm (Fin (q + 1)) :=
  (finRotate (q + 1)).symm

/-- The formal cyclic PP field (bimolecular-embedded):
x'ᵢ = (x_{pred(i)} - xᵢ) · (Σ xₖ).

This is the formal balance equation form, which is degree 2.
On the simplex (Σxₖ = 1), this reduces to x_{pred(i)} - xᵢ. -/
def cyclicField (q : ℕ) : (Fin (q + 1) → ℝ) → Fin (q + 1) → ℝ :=
  fun x i => (x (predPerm q i) - x i) * ∑ k, x k

/-- The cyclic field is conservative: Σx'ᵢ = 0.
Proof: Σ (x_{pred(i)} - xᵢ) = 0 by permutation reindexing. -/
theorem cyclicField_conservative (q : ℕ) :
    IsConservative (cyclicField q) := by
  intro x
  simp only [cyclicField, ← Finset.sum_mul, Finset.sum_sub_distrib]
  rw [sub_eq_zero.mpr (Equiv.sum_comp (predPerm q) x)]
  simp

/-- The production quadratic form for the cyclic protocol:
f_r(x) = (x_{pred(r)} + x_r) · (Σ xₖ). -/
noncomputable def cyclicProd (q : ℕ) (r : Fin (q + 1)) (x : Fin (q + 1) → ℝ) : ℝ :=
  (x (predPerm q r) + x r) * ∑ k, x k

/-- The cyclic field is PP-implementable with the balance equation form. -/
noncomputable def cyclicField_pp (q : ℕ) :
    IsPPImplementable (q + 1) (cyclicField q) where
  f := cyclicProd q
  f_pos := fun r x hx => by
    apply mul_nonneg
    · exact add_nonneg (hx _) (hx _)
    · exact Finset.sum_nonneg (fun i _ => hx i)
  f_homog := fun r c x => by
    simp only [cyclicProd, Pi.smul_apply, smul_eq_mul]
    simp_rw [← Finset.mul_sum]
    ring
  field_eq := fun x r => by simp [cyclicField, cyclicProd]; ring
  sum_f := fun x => by
    simp only [cyclicProd]
    rw [← Finset.sum_mul, Finset.sum_add_distrib, Equiv.sum_comp (predPerm q) x]
    ring

/-- On the simplex, the cyclic field reduces to x_{pred(i)} - xᵢ. -/
theorem cyclicField_on_simplex (q : ℕ) (x : Fin (q + 1) → ℝ)
    (hx : ∑ i, x i = 1) (i : Fin (q + 1)) :
    cyclicField q x i = x (predPerm q i) - x i := by
  simp [cyclicField, hx]

/-- The uniform distribution 1/(q+1) is an equilibrium of the cyclic system. -/
theorem cyclicField_equilibrium (q : ℕ) :
    cyclicField q (fun _ => (1 : ℝ) / (q + 1)) = fun _ => 0 := by
  ext i
  simp [cyclicField]

end Ripple
