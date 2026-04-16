/-
  Ripple.LPP.Syntactic — Syntactic PP Balance Equations

  Provides syntactic (coefficient-level) representations of PP balance
  equations, needed for the Stage 4 PLPP construction.

  The semantic `PPBalanceEquation` stores production functions f_r as
  arbitrary functions (Fin n → ℝ) → ℝ. This is sufficient for stating
  theorems and constructing witnesses, but Stage 4 needs to read off
  polynomial coefficients to construct PLPP transition rules.

  The syntactic `SynPPBalance` stores explicit ℚ≥0 coefficients:
    f_r(x) = Σ_{i,j} c_{r,i,j} · x_i · x_j

  This mirrors the PolyPIVP / PIVP distinction in Core/PIVP.lean.
-/

import Ripple.LPP.Defs

namespace Ripple

/-! ## Syntactic PP Balance Equation

A quadratic balance equation with explicit rational coefficients.
For a PP (population protocol), the production term for state r is
a homogeneous quadratic form f_r(x) = Σ_{i,j} c_{r,i,j} x_i x_j
where all coefficients are non-negative rationals.

The formal balance field is x'_r = f_r(x) - 2x_r(Σ x_k). -/

/-- A syntactic PP balance equation with explicit quadratic coefficients.

Each `f_r(x) = Σ_{i,j} coeff r i j · x_i · x_j` with non-negative
rational coefficients. The conservation identity `Σ_r coeff r i j = 2`
ensures formal conservation: Σ f_r(x) = 2(Σ x)². -/
structure SynPPBalance (n : ℕ) where
  /-- Coefficient tensor: f_r(x) = Σ_{i,j} coeff r i j · x_i · x_j. -/
  coeff : Fin n → Fin n → Fin n → ℚ
  /-- All coefficients are non-negative. -/
  coeff_nonneg : ∀ r i j, 0 ≤ coeff r i j
  /-- Formal conservation: Σ_r c_{r,i,j} = 2 for all i, j.
  This ensures Σ_r f_r(x) = 2·(Σ x_r)² as a formal polynomial identity.
  The constant 2 comes from the bimolecular interaction: each pair (i,j)
  contributes to both the r-th output slot and the partner slot. -/
  sum_coeff : ∀ i j : Fin n, ∑ r, coeff r i j = 2

namespace SynPPBalance

/-- Evaluate the production quadratic form f_r(x). -/
noncomputable def evalProd (eq : SynPPBalance n) (r : Fin n)
    (x : Fin n → ℝ) : ℝ :=
  ∑ i, ∑ j, (eq.coeff r i j : ℝ) * x i * x j

/-- The formal balance field: x'_r = f_r(x) - 2x_r(Σ x_k). -/
noncomputable def toField (eq : SynPPBalance n) :
    (Fin n → ℝ) → Fin n → ℝ :=
  fun x r => eq.evalProd r x - 2 * x r * (∑ k, x k)

/-- The production terms are positive polynomials. -/
theorem evalProd_nonneg (eq : SynPPBalance n) (r : Fin n)
    (x : Fin n → ℝ) (hx : ∀ i, 0 ≤ x i) :
    0 ≤ eq.evalProd r x := by
  apply Finset.sum_nonneg
  intro i _
  apply Finset.sum_nonneg
  intro j _
  apply mul_nonneg (mul_nonneg _ (hx i)) (hx j)
  exact_mod_cast eq.coeff_nonneg r i j

/-- The production sum equals 2·(Σ x)². -/
theorem sum_evalProd (eq : SynPPBalance n) (x : Fin n → ℝ) :
    ∑ r, eq.evalProd r x = 2 * (∑ i, x i) ^ 2 := by
  simp only [evalProd]
  -- Step 1: Swap sums and apply sum_coeff to reduce to ∑_i ∑_j 2 * x_i * x_j
  trans ∑ i : Fin n, ∑ j : Fin n, 2 * x i * x j
  · rw [Finset.sum_comm]; congr 1; funext i
    rw [Finset.sum_comm]; congr 1; funext j
    rw [← Finset.sum_mul, ← Finset.sum_mul]
    have : (∑ r : Fin n, (eq.coeff r i j : ℝ)) = 2 := by exact_mod_cast eq.sum_coeff i j
    rw [this]
  -- Step 2: ∑_i ∑_j 2 x_i x_j = 2(∑ x)²
  · simp_rw [show ∀ i j : Fin n, 2 * x i * x j = 2 * (x i * x j) from fun i j => by ring,
      ← Finset.mul_sum, ← Finset.sum_mul]
    ring

/-- The syntactic balance field is formally conservative. -/
theorem conservative (eq : SynPPBalance n) :
    IsConservative eq.toField := by
  intro x
  simp only [toField]
  -- Same structure as PPBalanceEquation.conservative_of_sum_eq
  have hrw : ∀ r : Fin n,
      eq.evalProd r x - 2 * x r * ∑ k : Fin n, x k =
      eq.evalProd r x - (2 * ∑ k : Fin n, x k) * x r := fun r => by ring
  simp_rw [hrw]
  rw [Finset.sum_sub_distrib (fun r => eq.evalProd r x)
    (fun r => (2 * ∑ k : Fin n, x k) * x r)]
  rw [← Finset.mul_sum, sum_evalProd, sq]
  ring

/-- Convert to the semantic PPBalanceEquation. -/
noncomputable def toPPBalance (eq : SynPPBalance n) : PPBalanceEquation n where
  f := fun r => eq.evalProd r
  f_pos := fun r x hx => eq.evalProd_nonneg r x hx

/-- The syntactic field agrees with the semantic field. -/
theorem toField_eq_balance (eq : SynPPBalance n) :
    eq.toField = eq.toPPBalance.toField := by
  ext x r
  simp [toField, toPPBalance, PPBalanceEquation.toField]

/-- CRN-implementability: x'_r = f_r(x) - 2(Σ x_k) · x_r.
The degradation rate for species r is 2(Σ x_k). -/
noncomputable def toCRN (eq : SynPPBalance n) :
    IsCRNImplementable n eq.toField where
  prod := fun r => eq.evalProd r
  degr := fun _ x => 2 * ∑ k, x k
  prod_pos := fun r x hx => eq.evalProd_nonneg r x hx
  degr_pos := fun _ x hx => by
    apply mul_nonneg (by norm_num)
    exact Finset.sum_nonneg (fun i _ => hx i)
  field_eq := fun x r => by
    simp [toField]
    ring

/-- PP-implementability of the syntactic balance equation. -/
noncomputable def toPP (eq : SynPPBalance n) :
    IsPPImplementable n eq.toField where
  f := fun r => eq.evalProd r
  f_pos := fun r x hx => eq.evalProd_nonneg r x hx
  f_homog := fun r c x => by
    simp only [evalProd, Pi.smul_apply, smul_eq_mul]
    simp_rw [show ∀ i j : Fin n, (eq.coeff r i j : ℝ) * (c * x i) * (c * x j) =
        c ^ 2 * ((eq.coeff r i j : ℝ) * x i * x j) from fun i j => by ring]
    simp_rw [← Finset.mul_sum]
  field_eq := fun x r => rfl
  sum_f := fun x => eq.sum_evalProd x

/-! ### Stage 4: Syntactic PP → PLPP

Given a syntactic PP balance equation with coefficients c_{r,i,j},
construct PLPP transition probabilities via the product distribution:
  α_{i,j,k,l} = c_{k,i,j} · c_{l,i,j} / 4

This works because the marginals satisfy:
  Σ_k α_{i,j,r,k} + Σ_k α_{i,j,k,r} = c_r/2 + c_r/2 = c_r

Key property: Σ_r c_{r,i,j} = 2 ensures Σ_{k,l} α_{i,j,k,l} = 4/4 = 1. -/

/-- Construct PLPP transitions from a syntactic PP balance equation.
Product distribution: α_{i,j,k,l} = c_{k,i,j} · c_{l,i,j} / 4. -/
def toPLPPTransitions (eq : SynPPBalance n) : PLPPTransitions n where
  α := fun i j k l => eq.coeff k i j * eq.coeff l i j / 4
  nonneg := fun i j k l =>
    div_nonneg (mul_nonneg (eq.coeff_nonneg k i j) (eq.coeff_nonneg l i j)) (by norm_num)
  sum_one := fun i j => by
    have h := eq.sum_coeff i j
    -- Inner sum: Σ_l c_k c_l / 4 = c_k · (Σ_l c_l) / 4 = c_k · 2 / 4 = c_k / 2
    have inner : ∀ k : Fin n,
        ∑ l : Fin n, eq.coeff k i j * eq.coeff l i j / 4 = eq.coeff k i j / 2 := by
      intro k
      simp_rw [mul_div_assoc, div_eq_mul_inv, ← Finset.mul_sum, ← Finset.sum_mul, h]
      norm_num
    simp_rw [inner, div_eq_mul_inv, ← Finset.sum_mul, h]
    norm_num

/-- Marginal sum: Σ_k α_{i,j,r,k} = c_{r,i,j} / 2 (in ℚ). -/
theorem toPLPPTransitions_row_marginal (eq : SynPPBalance n) (i j r : Fin n) :
    ∑ k, eq.toPLPPTransitions.α i j r k = eq.coeff r i j / 2 := by
  simp only [toPLPPTransitions]
  simp_rw [mul_div_assoc, div_eq_mul_inv, ← Finset.mul_sum, ← Finset.sum_mul, eq.sum_coeff i j]
  norm_num

/-- Marginal sum: Σ_k α_{i,j,k,r} = c_{r,i,j} / 2 (in ℚ). -/
theorem toPLPPTransitions_col_marginal (eq : SynPPBalance n) (i j r : Fin n) :
    ∑ k, eq.toPLPPTransitions.α i j k r = eq.coeff r i j / 2 := by
  simp only [toPLPPTransitions]
  simp_rw [show ∀ k : Fin n, eq.coeff k i j * eq.coeff r i j / 4 =
      eq.coeff r i j * eq.coeff k i j / 4 from fun k => by ring]
  simp_rw [mul_div_assoc, div_eq_mul_inv, ← Finset.mul_sum, ← Finset.sum_mul, eq.sum_coeff i j]
  norm_num

/-- Total marginal: Σ_k α_{r,k} + Σ_k α_{k,r} = c_r (in ℚ). -/
theorem toPLPPTransitions_marginal (eq : SynPPBalance n) (i j r : Fin n) :
    ∑ k, eq.toPLPPTransitions.α i j r k +
    ∑ k, eq.toPLPPTransitions.α i j k r = eq.coeff r i j := by
  rw [eq.toPLPPTransitions_row_marginal i j r, eq.toPLPPTransitions_col_marginal i j r]
  ring

/-- The PLPP balance field equals the syntactic balance field.
This is the core of Stage 4: the product distribution construction
exactly reproduces the PP balance equation without any ε-scaling. -/
theorem toPLPPTransitions_balanceField_eq (eq : SynPPBalance n) :
    eq.toPLPPTransitions.balanceField = eq.toField := by
  funext x r
  simp only [PLPPTransitions.balanceField, toField, evalProd]
  -- Both sides have the same degradation term; show production terms match
  congr 1
  congr 1; funext i; congr 1; funext j
  -- Goal: x i * x j * (Σ_k (α r k : ℝ) + Σ_k (α k r : ℝ)) = (c_r : ℝ) * x i * x j
  have hmarg := eq.toPLPPTransitions_marginal i j r
  have hmarg_real : (∑ k, (eq.toPLPPTransitions.α i j r k : ℝ)) +
      (∑ k, (eq.toPLPPTransitions.α i j k r : ℝ)) = (eq.coeff r i j : ℝ) := by
    exact_mod_cast hmarg
  rw [hmarg_real]
  ring

end SynPPBalance

end Ripple
