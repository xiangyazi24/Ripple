/-
  Ripple.DualRail.InfectionGraph — Infection graph for selective dual-railing.

  Formalizes Definitions 3–6 from:
    [UCNC25] Haisler, Huang, Migunov, Mohammed, Provence,
    "A Selective Dual-Railing Technique for General-Purpose Analog Computers",
    UCNC 2025, LNCS 16364, pp. 397–402.

  The infection graph determines which variables in a polynomial GPAC must
  be dual-railed to achieve CRN-implementability.

  Key insight (the "guard" condition): a variable x_b is protected from
  infection by x_a if every positive-coefficient monomial in x_b' that
  contains x_a also contains x_b itself. The self-multiplication ensures
  x_b' = prod − degr · x_b survives the substitution x_a → u_a − v_a.

  Architecture:
  - `IsIllFormed`         [Def 3]  ODE lacks CRN form x' = p − q·x
  - `Affects`             [Def 4]  x_a in positive terms of x_b'
  - `CanInfect`           [Def 5]  x_a affects x_b without guard
  - `infectionGraph`      [Def 6]  directed graph I(x)
  - `IsInfected`          [Alg 1]  reachable from ill-formed variables
  - `infectedSet`         the minimal dual-rail set R

  Status: definitions complete, key structural theorems stated.
  0 sorry in definitions; sorry in proof bodies where non-trivial.
-/

import Ripple.Core.PIVP
import Ripple.LPP.Defs
import Mathlib.Algebra.MvPolynomial.CommRing

namespace Ripple
namespace DualRail

open MvPolynomial

variable {d : ℕ}

/-! ## CRN-implementability

A single ODE x_i' = p_i(x) is CRN-implementable (Theorem 1 of [UCNC25])
iff it can be written x_i' = prod(x) − degr(x) · x_i where prod and degr
are polynomials with non-negative coefficients.

Equivalently: every monomial in p_i with a negative coefficient must be
divisible by X_i. -/

/-- A variable `i` is **well-formed** (CRN-implementable) if every negative-
coefficient monomial in `p_i` is divisible by `X_i`.
Eq. (1) of [UCNC25]: x_i' = p − q · x_i with p, q positive polynomials. -/
def IsWellFormed (p : Fin d → MvPolynomial (Fin d) ℚ) (i : Fin d) : Prop :=
  ∀ (σ : Fin d →₀ ℕ), (p i).coeff σ < 0 → 0 < σ i

/-- A variable `i` is **ill-formed** if its ODE fails the CRN form: there
exists a negative-coefficient monomial not divisible by `X_i`.
[UCNC25, Definition 3] -/
def IsIllFormed (p : Fin d → MvPolynomial (Fin d) ℚ) (i : Fin d) : Prop :=
  ∃ (σ : Fin d →₀ ℕ), (p i).coeff σ < 0 ∧ σ i = 0

theorem isIllFormed_iff_not_wellFormed (p : Fin d → MvPolynomial (Fin d) ℚ)
    (i : Fin d) :
    IsIllFormed p i ↔ ¬ IsWellFormed p i := by
  constructor
  · rintro ⟨σ, hcoeff, hexp⟩ hwf
    exact absurd (hwf σ hcoeff) (by omega)
  · intro h
    by_contra hall
    apply h
    intro σ hcoeff
    by_contra hσ
    exact hall ⟨σ, hcoeff, by omega⟩

/-! ## Definitions 4–6: Affects, CanInfect, Infection Graph -/

/-- Variable `a` **affects** variable `b`: `X_a` appears in some positive-
coefficient monomial of `p_b`. [UCNC25, Definition 4]

  "x_a appears anywhere in the positive terms of x_b', i.e. if there is a
   positive monomial T = x_a · S in x_b'." -/
def Affects (p : Fin d → MvPolynomial (Fin d) ℚ) (a b : Fin d) : Prop :=
  ∃ (σ : Fin d →₀ ℕ), 0 < (p b).coeff σ ∧ 0 < σ a

/-- Variable `a` **can infect** variable `b`: there is a positive-coefficient
monomial in `p_b` containing `X_a` but NOT `X_b`.

The absence of `X_b` is the key: it means `b` has no **self-guard** in that
term. When we dual-rail `a` (substituting x_a → u_a − v_a), the expansion
produces a negative term without x_b, breaking the CRN form x_b' = p − q·x_b.

Contrast: if every positive monomial containing X_a also contains X_b, then
a affects but does NOT infect b. The X_b factor absorbs the sign ambiguity
into the degradation term. [UCNC25, Definition 5] -/
def CanInfect (p : Fin d → MvPolynomial (Fin d) ℚ) (a b : Fin d) : Prop :=
  ∃ (σ : Fin d →₀ ℕ), 0 < (p b).coeff σ ∧ 0 < σ a ∧ σ b = 0

/-- `CanInfect` implies `Affects` (drop the guard condition). -/
theorem canInfect_implies_affects (p : Fin d → MvPolynomial (Fin d) ℚ)
    {a b : Fin d} :
    CanInfect p a b → Affects p a b := by
  rintro ⟨σ, hpos, ha, _⟩
  exact ⟨σ, hpos, ha⟩

/-- The **infection graph** on the variables of a polynomial system.
An edge from `a` to `b` means `a` can infect `b`.
[UCNC25, Definition 6]: I(x) = (V, E) where E = {(a, b) | a can infect b}. -/
def infectionGraph (p : Fin d → MvPolynomial (Fin d) ℚ) :
    Fin d → Fin d → Prop :=
  CanInfect p

/-! ## Transitive infection and the infected set (Algorithm 1)

Algorithm 1 of [UCNC25]:
  1. Build infection graph I(x)
  2. Compute SCCs via Tarjan's algorithm
  3. Identify ill-formed variables (ILL)
  4. Label an SCC as infected if reachable from an SCC containing an
     ill-formed variable
  5. R = union of all infected SCCs

Since reachability in the SCC condensation = transitive reachability in the
original graph (within and across SCCs), we formalize this directly via the
transitive closure of CanInfect. -/

/-- Transitive closure of the infection relation: `a` can transitively
infect `b` through a chain of infection edges. -/
inductive TransInfects (p : Fin d → MvPolynomial (Fin d) ℚ) :
    Fin d → Fin d → Prop where
  | single : CanInfect p a b → TransInfects p a b
  | trans : TransInfects p a b → CanInfect p b c → TransInfects p a c

/-- A variable is **infected** if it is ill-formed, or reachable in the
infection graph from some ill-formed variable. This captures Algorithm 1,
lines 4–8 of [UCNC25]. -/
def IsInfected (p : Fin d → MvPolynomial (Fin d) ℚ) (j : Fin d) : Prop :=
  IsIllFormed p j ∨ ∃ i, IsIllFormed p i ∧ TransInfects p i j

/-- The **infected set** R — the minimal set of variables that must be
dual-railed to achieve CRN-implementability.
[UCNC25, Algorithm 1, line 8] -/
def infectedSet (p : Fin d → MvPolynomial (Fin d) ℚ) : Set (Fin d) :=
  { j | IsInfected p j }

/-! ## Structural theorems -/

/-- **Guard preservation.** If `b ∉ R` (not infected) and `a ∈ R` (infected),
then `a` cannot infect `b`. Contrapositive: if `a` could infect `b`, then
`b` would be in R (contradiction).

This is the mathematical justification for Algorithm 1's correctness:
variables outside R are never infected, so their CRN form is preserved
after selectively dual-railing R. [UCNC25, paragraph after Algorithm 1] -/
theorem guard_preservation (p : Fin d → MvPolynomial (Fin d) ℚ)
    {b : Fin d} (hb : b ∉ infectedSet p)
    {a : Fin d} (ha : a ∈ infectedSet p) :
    ¬ CanInfect p a b := by
  intro h_infect
  apply hb
  show IsInfected p b
  cases ha with
  | inl hill =>
    right; exact ⟨a, hill, TransInfects.single h_infect⟩
  | inr hex =>
    obtain ⟨i, hill, hpath⟩ := hex
    right; exact ⟨i, hill, TransInfects.trans hpath h_infect⟩

/-- If `a ∈ R` affects `b ∉ R`, then `b` **guards itself**: every positive
monomial in `p_b` containing X_a also contains X_b.

This is the key property that makes selective dual-railing work: after
substituting x_a → u_a − v_a for all a ∈ R, the negative terms produced
in b's equation all contain x_b (from the guard), preserving the CRN form
x_b' = prod − degr · x_b. -/
theorem guarded_affects (p : Fin d → MvPolynomial (Fin d) ℚ)
    {a b : Fin d} (ha : a ∈ infectedSet p) (hb : b ∉ infectedSet p)
    (σ : Fin d →₀ ℕ) (hpos : 0 < (p b).coeff σ) (ha_exp : 0 < σ a) :
    0 < σ b := by
  by_contra h
  have h0 : σ b = 0 := by omega
  exact guard_preservation p hb ha ⟨σ, hpos, ha_exp, h0⟩

/-- Variables outside the infected set are well-formed. -/
theorem wellFormed_of_not_infected (p : Fin d → MvPolynomial (Fin d) ℚ)
    {i : Fin d} (hi : i ∉ infectedSet p) :
    IsWellFormed p i := by
  intro σ hcoeff
  by_contra h
  have h0 : σ i = 0 := by omega
  exact hi (Or.inl ⟨σ, hcoeff, h0⟩)

/-! ## Properties of the infected set -/

/-- The infected set contains all ill-formed variables. -/
theorem illFormed_mem_infectedSet (p : Fin d → MvPolynomial (Fin d) ℚ)
    {i : Fin d} (h : IsIllFormed p i) :
    i ∈ infectedSet p :=
  Or.inl h

/-- If every variable is well-formed, the infected set is empty. -/
theorem infectedSet_empty_of_allWellFormed (p : Fin d → MvPolynomial (Fin d) ℚ)
    (h : ∀ i, IsWellFormed p i) :
    infectedSet p = ∅ := by
  ext j
  simp only [Set.mem_empty_iff_false, iff_false]
  intro hj
  cases hj with
  | inl hill =>
    exact absurd (h j) ((isIllFormed_iff_not_wellFormed p j).mp hill)
  | inr hex =>
    obtain ⟨i, hill, _⟩ := hex
    exact absurd (h i) ((isIllFormed_iff_not_wellFormed p i).mp hill)

/-- If all variables are ill-formed, then R = Fin d. In this case selective
dual-railing coincides with all-at-once (Strategy S1). -/
theorem infectedSet_univ_of_allIllFormed (p : Fin d → MvPolynomial (Fin d) ℚ)
    (h : ∀ i, IsIllFormed p i) :
    infectedSet p = Set.univ := by
  ext j
  simp only [Set.mem_univ, iff_true]
  exact Or.inl (h j)

/-- The infected set is **closed under infection**: if `i ∈ R` and
`i` can infect `j`, then `j ∈ R`. -/
theorem infectedSet_closed (p : Fin d → MvPolynomial (Fin d) ℚ)
    {i j : Fin d} (hi : i ∈ infectedSet p) (h_inf : CanInfect p i j) :
    j ∈ infectedSet p := by
  rcases hi with hill | ⟨k, hk_ill, hpath⟩
  · exact Or.inr ⟨i, hill, TransInfects.single h_inf⟩
  · exact Or.inr ⟨k, hk_ill, TransInfects.trans hpath h_inf⟩

/-- The infected set is **minimal**: any set containing all ill-formed
variables and closed under infection contains `infectedSet`.
Together with `illFormed_mem_infectedSet` and `infectedSet_closed`,
this characterizes `infectedSet` as the least fixed point of the
infection closure operator. -/
theorem infectedSet_minimal (p : Fin d → MvPolynomial (Fin d) ℚ)
    (S : Set (Fin d))
    (h_ill : ∀ i, IsIllFormed p i → i ∈ S)
    (h_closed : ∀ i j, i ∈ S → CanInfect p i j → j ∈ S) :
    infectedSet p ⊆ S := by
  intro j hj
  rcases hj with hill | ⟨i, hill, hpath⟩
  · exact h_ill j hill
  · -- Propagate membership in S along the transitive infection path
    suffices ∀ (x y : Fin d), x ∈ S → TransInfects p x y → y ∈ S from
      this i j (h_ill i hill) hpath
    intro x y hx hxy
    induction hxy with
    | single hinf => exact h_closed _ _ hx hinf
    | trans _ hbc ih => exact h_closed _ _ ih hbc

/-! ## Bridge: PolyCRNDecomposition → IsWellFormed

A `PolyCRNDecomposition` witnesses the syntactic CRN form
`P.field i = prod_i − degr_i · X_i` with non-negative coefficients.
By `coeff_mul_X'`, every monomial `σ` in `degr_i * X_i` satisfies
`σ i ≥ 1`.  So any monomial with `σ i = 0` has
`coeff(σ, P.field i) = coeff(σ, prod_i) ≥ 0`,
which is the contrapositive of `IsWellFormed`. -/

theorem wellFormed_of_polyCRNDecomposition {d : ℕ} {P : PolyPIVP d}
    (pcd : PolyCRNDecomposition d P) (i : Fin d) :
    IsWellFormed P.field i := by
  intro σ hcoeff
  -- Goal: 0 < σ i.  We prove the contrapositive: σ i = 0 → coeff ≥ 0.
  by_contra h
  have hi0 : σ i = 0 := by omega
  -- Rewrite field using the decomposition.
  have hfield := pcd.field_eq i
  -- Compute coefficient of σ in P.field i.
  have hcoeff_eq : (P.field i).coeff σ =
      (pcd.prod i).coeff σ - (pcd.degr i * X i).coeff σ := by
    rw [hfield, MvPolynomial.coeff_sub]
  -- The coefficient of σ in degr_i * X_i vanishes because σ i = 0.
  have hdeg_zero : (pcd.degr i * X i).coeff σ = 0 := by
    classical
    rw [MvPolynomial.coeff_mul_X']
    simp [Finsupp.mem_support_iff, hi0]
  -- So the field coefficient equals the production coefficient ≥ 0.
  rw [hcoeff_eq, hdeg_zero, sub_zero] at hcoeff
  exact absurd hcoeff (not_lt.mpr (pcd.prod_nonneg i σ))

end DualRail
end Ripple
