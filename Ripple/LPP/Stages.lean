/-
  Ripple.LPP.Stages — Four-Stage GPAC→PP Construction

  Formalizes the four-stage algorithm from [LPP] §3 (Huang-Huls, DNA 28):
    Stage 1: CRN → CRN-implementable quadratic system (v-variables)
    Stage 2: Quadratic CRN → TPP-implementable cubic form (λ-trick + balancing dilation)
    Stage 3: TPP cubic form → PP-implementable quadratic form (self-product z_{i,j} = x_i·x_j)
    Stage 4: PP quadratic form → PLPP (ε-trick + rule construction)

  Also formalizes the basic operations from §3.2:
    Operation 1: Constant dilation (ε-trick)
    Operation 2: Time dilation (composition)
    Operation 3: Variable shrinking (λ-trick)
    Operation 4: Balancing dilation (g-trick)
-/

import Ripple.LPP.Defs
import Ripple.LPP.Example
import Ripple.LPP.Syntactic
import Ripple.Core.BoundedTime
import Mathlib.Analysis.Calculus.Deriv.Prod

namespace Ripple

/-! ## Non-dependent Fin tuple helpers

`Fin.snoc` and `Fin.addCases` are dependently typed, which makes `rw`/`simp`
fail in non-dependent contexts (where the result type is constant, e.g. `ℝ`).
These wrappers fix the motive to `fun _ => α`, enabling standard rewriting. -/

/-- Non-dependent `Fin.snoc`: appends a value to a tuple. -/
def vecSnoc {n : ℕ} {α : Type*} (f : Fin n → α) (a : α) : Fin (n + 1) → α :=
  @Fin.snoc n (fun _ => α) f a

@[simp] lemma vecSnoc_last {n : ℕ} {α : Type*} {f : Fin n → α} {a : α} :
    vecSnoc f a (Fin.last n) = a :=
  @Fin.snoc_last n (fun _ => α) a f

@[simp] lemma vecSnoc_castSucc {n : ℕ} {α : Type*} {f : Fin n → α} {a : α} {j : Fin n} :
    vecSnoc f a (Fin.castSucc j) = f j :=
  @Fin.snoc_castSucc n (fun _ => α) a f j

lemma vecSnoc_init {n : ℕ} {α : Type*} {f : Fin n → α} {a : α} :
    Fin.init (vecSnoc f a) = f :=
  @Fin.init_snoc n (fun _ => α) a f

/-- Non-dependent `Fin.addCases`: concatenates two tuples. -/
def vecAddCases {m n : ℕ} {α : Type*} (f : Fin m → α) (g : Fin n → α) :
    Fin (m + n) → α :=
  @Fin.addCases m n (fun _ => α) f g

@[simp] lemma vecAddCases_left {m n : ℕ} {α : Type*} {f : Fin m → α}
    {g : Fin n → α} {i : Fin m} :
    vecAddCases f g (Fin.castAdd n i) = f i :=
  Fin.addCases_left i

@[simp] lemma vecAddCases_right {m n : ℕ} {α : Type*} {f : Fin m → α}
    {g : Fin n → α} {i : Fin n} :
    vecAddCases f g (Fin.natAdd m i) = g i :=
  Fin.addCases_right i

/-- `Fin.castSucc` commutes with `Fin.natAdd` (they compose to the same embedding). -/
lemma Fin.castSucc_natAdd_comm {m n : ℕ} {j : Fin n} :
    (Fin.natAdd m j).castSucc = Fin.natAdd m (j.castSucc) := by
  ext; simp [Fin.natAdd, Fin.castSucc, Fin.castAdd]

/-- vecSnoc through the natAdd∘castSucc embedding. Lean normalizes
`Fin.castSucc (Fin.natAdd m j)` to `Fin.natAdd m (Fin.castSucc j)`,
so we need this form in addition to `vecSnoc_castSucc`. -/
@[simp] lemma vecSnoc_natAdd_castSucc {m n : ℕ} {α : Type*}
    {f : Fin (m + n) → α} {a : α} {j : Fin n} :
    vecSnoc f a (Fin.natAdd m (Fin.castSucc j)) = f (Fin.natAdd m j) := by
  rw [← Fin.castSucc_natAdd_comm]; exact vecSnoc_castSucc

/-! ## k-PP-implementable systems

From [LPP] Corollary 4: a function is k-PP-implementable iff it is
CRN-implementable, conservative, homogeneously degree k, and has no
positive xᵢᵏ term in x'ᵢ. A TPP (termolecular PP) is a 3-PP. -/

/-- A vector field is k-PP-implementable: CRN-implementable + conservative
+ degree ≤ k + no positive xᵢᵏ in x'ᵢ.

For k=2 this is PP-implementable (bimolecular reactions X+Y → W+Z).
For k=3 this is TPP-implementable (termolecular reactions X+Y+Z → U+V+W).

**Note:** The degree and no-self-power conditions are not yet enforced
in this structure. The `k` parameter is carried for type-level tracking
but will need semantic or syntactic enforcement when Stage proofs are
filled in. -/
structure IsKPPImplementable (k n : ℕ) (field : (Fin n → ℝ) → Fin n → ℝ)
    extends IsCRNImplementable n field where
  /-- The system is conservative (formal polynomial identity, not just on simplex). -/
  conservative : IsConservative field

/-- A TPP-implementable system is a 3-PP-implementable system.
Reactions have the form X + Y + Z → U + V + W. -/
abbrev IsTPPImplementable (n : ℕ) := IsKPPImplementable 3 n

/-! ## Basic Operations (§3.2)

These are the building blocks for the four-stage construction. -/

/-- Operation 1: Constant dilation (ε-trick).
If x'(t) = p(x(t)) then x(εt) solves x'(t) = ε·p(x(t)).
This scales the coefficients without changing the trajectory shape.

We state this as a fact about the scalar reparametrization. -/
theorem constant_dilation_reparametrize (ε : ℝ)
    (f g : ℝ → ℝ) (h_sol : ∀ t, HasDerivAt f (g t) t) :
    ∀ t, HasDerivAt (fun s => f (ε * s)) (ε * g (ε * t)) t := by
  intro t
  have h1 := (h_sol (ε * t)).comp t ((hasDerivAt_id t).const_mul ε)
  simp only [mul_one] at h1
  convert h1 using 1
  ring

/-- Operation 2: Constant dilation for vector fields.
If x(t) solves x' = field(x), then x(εt) solves x' = ε·field(x).
This is the vector-field version of `constant_dilation_reparametrize`. -/
def constantDilation {n : ℕ} (ε : ℝ) (field : (Fin n → ℝ) → Fin n → ℝ) :
    (Fin n → ℝ) → Fin n → ℝ :=
  fun x i => ε * field x i

/-- Constant dilation preserves CRN-implementability.
If field = prod - degr·x, then ε·field = (ε·prod) - (ε·degr)·x. -/
noncomputable def constantDilation_crn {n : ℕ} {ε : ℝ} (hε : 0 ≤ ε)
    {field : (Fin n → ℝ) → Fin n → ℝ}
    (crn : IsCRNImplementable n field) :
    IsCRNImplementable n (constantDilation ε field) where
  prod := fun i x => ε * crn.prod i x
  degr := fun i x => ε * crn.degr i x
  prod_pos := fun i x hx => mul_nonneg hε (crn.prod_pos i x hx)
  degr_pos := fun i x hx => mul_nonneg hε (crn.degr_pos i x hx)
  field_eq := fun x i => by
    simp only [constantDilation]
    rw [crn.field_eq]
    ring

/-- Constant dilation preserves conservation. -/
theorem constantDilation_conservative {n : ℕ} {ε : ℝ}
    {field : (Fin n → ℝ) → Fin n → ℝ} (hcons : IsConservative field) :
    IsConservative (constantDilation ε field) := by
  intro x
  simp only [constantDilation, ← Finset.mul_sum]
  rw [hcons x]
  ring

/-- Operation 3: Variable shrinking (λ-trick).
Given field on n variables, scaling y = λ·x gives a new field
where fieldλ(y)ᵢ = λ · field(y/λ)ᵢ.

If x(t) solves x' = field(x), then y(t) = λ·x(t) solves y' = fieldλ(y).
The degree of the polynomial field is preserved. -/
noncomputable def lambdaTrick {n : ℕ} (c : ℝ) (field : (Fin n → ℝ) → Fin n → ℝ) :
    (Fin n → ℝ) → Fin n → ℝ :=
  fun y i => c * field (fun j => y j / c) i

/-- Scaling cancellation: lambdaTrick c field (c • y) = c • field y. -/
theorem lambdaTrick_smul_cancel {n : ℕ} {c : ℝ} (hc : c ≠ 0)
    (field : (Fin n → ℝ) → Fin n → ℝ) (y : Fin n → ℝ) :
    lambdaTrick c field (c • y) = c • field y := by
  funext i
  simp only [lambdaTrick, Pi.smul_apply, smul_eq_mul, mul_div_cancel_left₀ _ hc]

/-- The λ-trick respects solutions: if x solves x' = field(x),
then c • x solves x' = lambdaTrick c field(c • x). -/
theorem lambdaTrick_solution {n : ℕ} {c : ℝ} (hc : c ≠ 0)
    {x : ℝ → Fin n → ℝ} {field : (Fin n → ℝ) → Fin n → ℝ}
    (h_sol : ∀ t, HasDerivAt x (field (x t)) t) :
    ∀ t, HasDerivAt (c • x ·) (lambdaTrick c field (c • x t)) t := by
  intro t
  rw [lambdaTrick_smul_cancel hc]
  exact (h_sol t).const_smul c

/-- The λ-trick preserves CRN-implementability.
If field = prod - degr·x, then lambdaTrick c field = (c·prod(·/c)) - degr(·/c)·x. -/
noncomputable def lambdaTrick_crn {n : ℕ} {c : ℝ} (hc : 0 < c)
    {field : (Fin n → ℝ) → Fin n → ℝ}
    (crn : IsCRNImplementable n field) :
    IsCRNImplementable n (lambdaTrick c field) where
  prod := fun i y => c * crn.prod i (fun j => y j / c)
  degr := fun i y => crn.degr i (fun j => y j / c)
  prod_pos := fun i y hy => by
    apply mul_nonneg hc.le
    exact crn.prod_pos i _ (fun k => div_nonneg (hy k) hc.le)
  degr_pos := fun i y hy =>
    crn.degr_pos i _ (fun k => div_nonneg (hy k) hc.le)
  field_eq := fun y i => by
    simp only [lambdaTrick]
    rw [crn.field_eq]
    have hc' : c ≠ 0 := ne_of_gt hc
    field_simp

/-- The one-trick: extend an n-variable system to n+1 by adding
x₀ with x₀' = -Σᵢ x'ᵢ. The extended system is conservative.
On the simplex with Σxᵢ = 1, the new variable x₀ = 1 - Σᵢ₌₁ⁿ xᵢ.

Unlike the g-trick (balancingDilation), the one-trick does NOT
multiply rates by x₀. It merely adds the conservation variable. -/
def oneTrick {n : ℕ} (field : (Fin n → ℝ) → Fin n → ℝ) :
    (Fin (n + 1) → ℝ) → Fin (n + 1) → ℝ :=
  fun x => Fin.cons
    (-(∑ j : Fin n, field (Fin.tail x) j))
    (fun j => field (Fin.tail x) j)

/-- The one-trick is conservative: Σᵢ₌₀ⁿ x'ᵢ = 0. -/
theorem oneTrick_conservative {n : ℕ}
    (field : (Fin n → ℝ) → Fin n → ℝ) :
    IsConservative (oneTrick field) := by
  intro x
  simp only [oneTrick]
  rw [Fin.sum_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ]
  linarith

/-! **Note:** The one-trick does NOT preserve CRN-implementability on its own,
because x₀' = -(Σ field_j) has no x₀-dependent degradation term. The balancing
dilation (`balancingDilation`) combines both the conservation extension and
the x₀-multiplication, and DOES preserve CRN-implementability. -/

/-- Operation 4: Balancing dilation (g-trick).
Given a field on n variables, construct a conservative field on n+1 variables
by multiplying each equation by x₀ and adding x'₀ = -Σx'ᵢ.

The new variable x₀ acts as a "population reservoir" that distributes
total mass among all variables. On the simplex (Σxᵢ = 1), this is
a time dilation by the factor x₀(t).

From [LPP] §3.2 Operation 4 / Theorem 13 proof. -/
def balancingDilation {n : ℕ} (field : (Fin n → ℝ) → Fin n → ℝ) :
    (Fin (n + 1) → ℝ) → Fin (n + 1) → ℝ :=
  fun x => Fin.cons
    (-(∑ j : Fin n, field (Fin.tail x) j) * x 0)
    (fun j => field (Fin.tail x) j * x 0)

/-- The balancing dilation is conservative: Σᵢ₌₀ⁿ x'ᵢ = 0.
Proof: x'₀ = -(Σfield_j)·x₀ and Σⱼ x'_{j+1} = (Σfield_j)·x₀. -/
theorem balancingDilation_conservative {n : ℕ}
    (field : (Fin n → ℝ) → Fin n → ℝ) :
    IsConservative (balancingDilation field) := by
  intro x
  simp only [balancingDilation]
  rw [Fin.sum_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ]
  rw [← Finset.sum_mul]
  ring

/-- The balancing dilation preserves CRN-implementability.
If the original field has CRN form x'ᵢ = pᵢ - qᵢxᵢ, then the balanced
system has CRN form:
  x'₀ = (Σⱼ qⱼx_{j+1})·x₀ - (Σⱼ pⱼ)·x₀
  x'_{i+1} = pᵢ·x₀ - (qᵢ·x₀)·x_{i+1}
All production and degradation terms are positive polynomials. -/
noncomputable def balancingDilation_crn {n : ℕ}
    {field : (Fin n → ℝ) → Fin n → ℝ}
    (crn : IsCRNImplementable n field) :
    IsCRNImplementable (n + 1) (balancingDilation field) where
  prod := Fin.cons
    (fun x => (∑ j : Fin n, crn.degr j (Fin.tail x) * x j.succ) * x 0)
    (fun j x => crn.prod j (Fin.tail x) * x 0)
  degr := Fin.cons
    (fun x => ∑ j : Fin n, crn.prod j (Fin.tail x))
    (fun j x => crn.degr j (Fin.tail x) * x 0)
  prod_pos := fun i x hx => by
    refine i.cases ?_ (fun j => ?_)
    · -- x₀: Σ degr(j)·x_{j+1}·x₀ ≥ 0
      simp only [Fin.cons_zero]
      apply mul_nonneg
      · exact Finset.sum_nonneg fun j _ =>
          mul_nonneg (crn.degr_pos j _ (fun k => hx k.succ)) (hx j.succ)
      · exact hx 0
    · -- x_{j+1}: prod(j)·x₀ ≥ 0
      simp only [Fin.cons_succ]
      exact mul_nonneg (crn.prod_pos j _ (fun k => hx k.succ)) (hx 0)
  degr_pos := fun i x hx => by
    refine i.cases ?_ (fun j => ?_)
    · simp only [Fin.cons_zero]
      exact Finset.sum_nonneg fun j _ => crn.prod_pos j _ (fun k => hx k.succ)
    · simp only [Fin.cons_succ]
      exact mul_nonneg (crn.degr_pos j _ (fun k => hx k.succ)) (hx 0)
  field_eq := fun x i => by
    refine i.cases ?_ (fun j => ?_)
    · -- x₀: -(Σ field_j)·x₀ = (Σ degr_j·x_{j+1})·x₀ - (Σ prod_j)·x₀
      simp only [balancingDilation, Fin.cons_zero]
      simp_rw [crn.field_eq (Fin.tail x), Finset.sum_sub_distrib]
      simp only [Fin.tail]
      ring
    · -- x_{j+1}: field_j·x₀ = prod_j·x₀ - (degr_j·x₀)·x_{j+1}
      simp only [balancingDilation, Fin.cons_succ]
      rw [crn.field_eq (Fin.tail x) j]
      simp only [Fin.tail]
      ring

/-! ## Simplex Invariance

Conservative fields preserve the total mass ∑xᵢ. This is fundamental:
the simplex constraint ∑xᵢ = 1 is an invariant of conservative dynamics. -/

/-- If a conservative field has a solution, the total mass ∑xᵢ(t) is constant.
Proof: d/dt(∑xᵢ) = ∑x'ᵢ = 0 (conservation), so ∑xᵢ is constant by
`is_const_of_deriv_eq_zero`. -/
theorem conservative_sum_constant {n : ℕ}
    {field : (Fin n → ℝ) → Fin n → ℝ}
    (hcons : IsConservative field)
    {sol : ℝ → Fin n → ℝ}
    (h_sol : ∀ t, HasDerivAt sol (field (sol t)) t) :
    ∀ a b : ℝ, ∑ i, sol a i = ∑ i, sol b i := by
  have h_sum_deriv : ∀ t, HasDerivAt (fun s => ∑ i, sol s i) 0 t := by
    intro t
    have h_comp : ∀ i, HasDerivAt (fun s => sol s i) (field (sol t) i) t :=
      hasDerivAt_pi.mp (h_sol t)
    have h1 := HasDerivAt.sum (fun (i : Fin n) (_ : i ∈ Finset.univ) => h_comp i)
    have h2 : (∑ i : Fin n, fun s => sol s i) = fun s => ∑ i, sol s i := by
      ext s; simp [Finset.sum_apply]
    rw [h2, hcons (sol t)] at h1
    exact h1
  exact is_const_of_deriv_eq_zero
    (fun x => (h_sum_deriv x).differentiableAt)
    (fun x => (h_sum_deriv x).deriv)

/-- Corollary: if a conservative solution starts on the simplex (∑xᵢ(0) = 1),
it stays on the simplex for all time. -/
theorem conservative_simplex_invariant {n : ℕ}
    {field : (Fin n → ℝ) → Fin n → ℝ}
    (hcons : IsConservative field)
    {sol : ℝ → Fin n → ℝ}
    (h_sol : ∀ t, HasDerivAt sol (field (sol t)) t)
    (h_init : ∑ i, sol 0 i = 1) :
    ∀ t, ∑ i, sol t i = 1 := by
  intro t
  rw [← h_init]
  exact (conservative_sum_constant hcons h_sol 0 t).symm

/-! ## Composed Transformations

Composing the basic operations to build stage constructions. -/

/-- The Stage 2 field construction: compose ε-scaling, λ-shrinking, and
balancing dilation. Given any CRN-implementable field, the composed
transformation produces a TPP-implementable (CRN + conservative) field.

The composed field is:
  balancingDilation (lambdaTrick c (constantDilation ε field))
which maps n-variable CRN → (n+1)-variable TPP.

This is the algebraic core of Stage 2 (Theorem 13 in [LPP]). The
analytic part (constructing solutions, proving convergence) is separate. -/
noncomputable def stage2_field {n : ℕ} (ε c : ℝ)
    (field : (Fin n → ℝ) → Fin n → ℝ) :
    (Fin (n + 1) → ℝ) → Fin (n + 1) → ℝ :=
  balancingDilation (lambdaTrick c (constantDilation ε field))

/-- The Stage 2 field is TPP-implementable. -/
noncomputable def stage2_field_tpp {n : ℕ} {ε c : ℝ} (hε : 0 ≤ ε) (hc : 0 < c)
    {field : (Fin n → ℝ) → Fin n → ℝ}
    (crn : IsCRNImplementable n field) :
    IsTPPImplementable (n + 1) (stage2_field ε c field) where
  toIsCRNImplementable :=
    balancingDilation_crn (lambdaTrick_crn hc (constantDilation_crn hε crn))
  conservative := balancingDilation_conservative _

/-! ## Self-Product (Stage 3 Building Block)

The self-product z_{i,j} = xᵢ · xⱼ is the key construction for Stage 3.
Given n variables xᵢ, introduce n² variables z indexed by Fin n × Fin n.
On the simplex (∑xₖ = 1), the row sum recovers the original variable:
  rowSum(z)ᵢ = ∑ⱼ z_{i,j} = ∑ⱼ xᵢxⱼ = xᵢ·∑ⱼ xⱼ = xᵢ.

The z-field is z'_{i,j} = field_i(x)·xⱼ + xᵢ·field_j(x), which is
quadratic in z when field has degree ≤ 3 (TPP), since degree 4 in x
= degree 2 in z. -/

/-- Row sum of the self-product matrix: given z : Fin n × Fin n → ℝ,
the row sum at i recovers xᵢ = ∑_j z_{i,j} on the simplex. -/
def selfProduct_rowSum {n : ℕ} (z : Fin n × Fin n → ℝ) : Fin n → ℝ :=
  fun i => ∑ j : Fin n, z (i, j)

/-- Self-product field: given a field on n variables, construct a field
on n×n variables via z'_{i,j} = field_i(rowSum z)·(rowSum z)_j + (rowSum z)_i·field_j(rowSum z).

**Degree warning:** When the input field is cubic (TPP), this field is degree 4
in z-variables (cubic × linear rowSum). It is NOT PP-implementable. The correct
PP-implementable field for Stage 3 (Theorem 15 in [LPP]) is obtained by symbolic
substitution (x_a·x_b → z_{a,b}), producing a degree-2 field that agrees with
selfProductField on the self-product manifold {z_{i,j} = x_i·x_j}. -/
def selfProductField {n : ℕ} (field : (Fin n → ℝ) → Fin n → ℝ) :
    (Fin n × Fin n → ℝ) → Fin n × Fin n → ℝ :=
  fun z ij =>
    let x := selfProduct_rowSum z
    field x ij.1 * x ij.2 + x ij.1 * field x ij.2

/-- The self-product field is conservative:
∑_{i,j} z'_{i,j} = 2·(∑ᵢ field_i(x))·(∑ⱼ xⱼ).
When the original field is conservative (∑field_i = 0), this is 0. -/
theorem selfProductField_conservative {n : ℕ}
    {field : (Fin n → ℝ) → Fin n → ℝ} (hcons : IsConservative field) :
    ∀ z : Fin n × Fin n → ℝ,
      ∑ ij : Fin n × Fin n, selfProductField field z ij = 0 := by
  intro z
  simp only [selfProductField]
  rw [Fintype.sum_prod_type]
  simp_rw [Finset.sum_add_distrib]
  have h1 : ∑ i : Fin n, ∑ j : Fin n,
      field (selfProduct_rowSum z) i * selfProduct_rowSum z j =
      (∑ i, field (selfProduct_rowSum z) i) * (∑ j, selfProduct_rowSum z j) := by
    rw [← Finset.sum_mul_sum]
  have h2 : ∑ i : Fin n, ∑ j : Fin n,
      selfProduct_rowSum z i * field (selfProduct_rowSum z) j =
      (∑ i, selfProduct_rowSum z i) * (∑ j, field (selfProduct_rowSum z) j) := by
    rw [← Finset.sum_mul_sum]
  rw [h1, h2, hcons]
  ring

/-! ## Self-product trajectory lemmas

The self-product z_{i,j}(t) = x_i(t)·x_j(t) satisfies the selfProductField ODE
by the product rule. These are the analytic building blocks for Stage 3. -/

/-- Row sum of the self-product recovers the original trajectory
(when z_{i,j} = x_i·x_j and ∑x = 1). -/
theorem selfProduct_rowSum_eq {n : ℕ} {x : Fin n → ℝ} (hsum : ∑ j, x j = 1) (i : Fin n) :
    selfProduct_rowSum (fun ij : Fin n × Fin n => x ij.1 * x ij.2) i = x i := by
  dsimp [selfProduct_rowSum]
  rw [← Finset.mul_sum, hsum, mul_one]

/-- Total sum of the self-product equals (∑x)². -/
theorem selfProduct_totalSum {n : ℕ} {x : Fin n → ℝ} :
    ∑ ij : Fin n × Fin n, x ij.1 * x ij.2 = (∑ i, x i) ^ 2 := by
  rw [Fintype.sum_prod_type]
  simp_rw [← Finset.mul_sum]
  rw [← Finset.sum_mul, sq]

/-- On the simplex, ∑z_{i,j} = 1. -/
theorem selfProduct_simplex {n : ℕ} {x : Fin n → ℝ} (hsum : ∑ j, x j = 1) :
    ∑ ij : Fin n × Fin n, x ij.1 * x ij.2 = 1 := by
  rw [selfProduct_totalSum, hsum]; ring

/-- The self-product trajectory z_{i,j}(t) = x_i(t)·x_j(t) satisfies the
selfProductField ODE, assuming x satisfies x' = field(x) and ∑x = 1.
This is just the product rule: z'_{i,j} = x'_i·x_j + x_i·x'_j. -/
theorem selfProduct_hasDerivAt {n : ℕ} {field : (Fin n → ℝ) → Fin n → ℝ}
    {x : ℝ → Fin n → ℝ} {t : ℝ}
    (h_sol : HasDerivAt x (fun i => field (x t) i) t)
    (h_simplex : ∑ j, x t j = 1) :
    HasDerivAt (fun s => fun ij : Fin n × Fin n => x s ij.1 * x s ij.2)
      (fun ij => selfProductField field
        (fun ij : Fin n × Fin n => x t ij.1 * x t ij.2) ij) t := by
  refine hasDerivAt_pi.mpr (fun ij => ?_)
  have h_i := hasDerivAt_pi.mp h_sol ij.1
  have h_j := hasDerivAt_pi.mp h_sol ij.2
  -- z'_{i,j} = x'_i · x_j + x_i · x'_j
  have h_prod := h_i.mul h_j
  -- Need to show the derivative matches selfProductField
  have h_row : selfProduct_rowSum (fun ij : Fin n × Fin n => x t ij.1 * x t ij.2) = x t :=
    funext (selfProduct_rowSum_eq h_simplex)
  convert h_prod using 1
  simp only [selfProductField, h_row]

/-! ## Stage 2 Cubic Form Structure

After Stage 2, the TPP system has a specific cubic form: for each non-zero
variable i, x'_i = (P_i(x) - Q_i(x)·x_i)·x₀ where P_i is quadratic and Q_i
is linear. This structure is essential for Stage 3: the self-product z-field
z'_{i,j} = x'_i·x_j + x_i·x'_j is degree 4 in z when expressed via rowSum,
but becomes degree 2 after symbolic substitution x_a·x_b → z_{a,b}, which
requires knowing the P_i/Q_i decomposition and their polynomial coefficients. -/

/-- Stage 2 cubic form output.
The field has the form x'_i = (P_i(x) - Q_i(x)·x_i)·x₀ for non-balancing variables,
with explicit quadratic/linear coefficients needed for Stage 3 symbolic substitution. -/
structure Stage2CubicForm (d : ℕ) (field : (Fin d → ℝ) → Fin d → ℝ) where
  /-- Index of the balancing variable x₀ -/
  zero : Fin d
  /-- Quadratic production coefficients: P_i(x) = ∑_a ∑_b A i a b · x_a · x_b -/
  A : Fin d → Fin d → Fin d → ℝ
  /-- Linear degradation coefficients: Q_i(x) = ∑_a B i a · x_a -/
  B : Fin d → Fin d → ℝ
  /-- Production coefficients are non-negative -/
  A_nonneg : ∀ i a b, 0 ≤ A i a b
  /-- Degradation coefficients are non-negative -/
  B_nonneg : ∀ i a, 0 ≤ B i a
  /-- Field decomposition: x'_i = (P_i - Q_i·x_i)·x₀ for i ≠ zero -/
  field_eq : ∀ i, i ≠ zero → ∀ x : Fin d → ℝ,
    field x i = ((∑ a, ∑ b, A i a b * x a * x b) -
      (∑ a, B i a * x a) * x i) * x zero
  /-- Conservation: x'₀ = -∑_{i≠0} x'_i -/
  field_zero : ∀ x : Fin d → ℝ,
    field x zero = -(∑ i ∈ Finset.univ.filter (· ≠ zero), field x i)

namespace Stage2CubicForm

variable {d : ℕ} {field : (Fin d → ℝ) → Fin d → ℝ} (s : Stage2CubicForm d field)

/-- The quadratic production term P_i(x) in x-variables. -/
def P (i : Fin d) (x : Fin d → ℝ) : ℝ :=
  ∑ a, ∑ b, s.A i a b * x a * x b

/-- The linear degradation term Q_i(x) in x-variables. -/
def Q (i : Fin d) (x : Fin d → ℝ) : ℝ :=
  ∑ a, s.B i a * x a

/-- P_i lifted to z-space via symbolic substitution x_a·x_b → z_{a,b}.
This is LINEAR in z (degree 1), not quadratic. -/
def Pz (i : Fin d) (z : Fin d × Fin d → ℝ) : ℝ :=
  ∑ a, ∑ b, s.A i a b * z (a, b)

/-- x₀·Q_i lifted to z-space: ∑_a B_i(a)·z_{zero,a}.
Linear in z (degree 1). -/
def x0Qz (i : Fin d) (z : Fin d × Fin d → ℝ) : ℝ :=
  ∑ a, s.B i a * z (s.zero, a)

/-- On the self-product manifold z_{a,b} = x_a·x_b, Pz agrees with P. -/
theorem Pz_eq_on_manifold (i : Fin d) (x : Fin d → ℝ) :
    s.Pz i (fun ij => x ij.1 * x ij.2) = s.P i x := by
  simp only [Pz, P]
  congr 1; ext a; congr 1; ext b; ring

/-- On the self-product manifold, x0Qz agrees with x_zero · Q. -/
theorem x0Qz_eq_on_manifold (i : Fin d) (x : Fin d → ℝ) :
    s.x0Qz i (fun ij => x ij.1 * x ij.2) = x s.zero * s.Q i x := by
  simp only [x0Qz, Q]
  simp_rw [show ∀ a, s.B i a * (x s.zero * x a) = x s.zero * (s.B i a * x a)
    from fun a => by ring]
  rw [← Finset.mul_sum]

/-- P is non-negative on the non-negative orthant. -/
theorem P_nonneg (i : Fin d) (x : Fin d → ℝ) (hx : ∀ k, 0 ≤ x k) :
    0 ≤ s.P i x :=
  Finset.sum_nonneg fun a _ =>
    Finset.sum_nonneg fun b _ =>
      mul_nonneg (mul_nonneg (s.A_nonneg i a b) (hx a)) (hx b)

/-- Q is non-negative on the non-negative orthant. -/
theorem Q_nonneg (i : Fin d) (x : Fin d → ℝ) (hx : ∀ k, 0 ≤ x k) :
    0 ≤ s.Q i x :=
  Finset.sum_nonneg fun a _ => mul_nonneg (s.B_nonneg i a) (hx a)

/-- Pz is non-negative on the non-negative orthant (z-space). -/
theorem Pz_nonneg (i : Fin d) (z : Fin d × Fin d → ℝ) (hz : ∀ p, 0 ≤ z p) :
    0 ≤ s.Pz i z :=
  Finset.sum_nonneg fun a _ =>
    Finset.sum_nonneg fun b _ => mul_nonneg (s.A_nonneg i a b) (hz _)

/-- x0Qz is non-negative on the non-negative orthant. -/
theorem x0Qz_nonneg (i : Fin d) (z : Fin d × Fin d → ℝ) (hz : ∀ p, 0 ≤ z p) :
    0 ≤ s.x0Qz i z :=
  Finset.sum_nonneg fun a _ => mul_nonneg (s.B_nonneg i a) (hz _)

/-- Sum of Pz over non-zero indices: total production in z-space. -/
def totalPz (z : Fin d × Fin d → ℝ) : ℝ :=
  ∑ k ∈ Finset.univ.filter (· ≠ s.zero), s.Pz k z

/-- Sum of ∑_a B_k(a)·z_{a,k} over non-zero k: total degradation-coupling in z-space. -/
def totalQxz (z : Fin d × Fin d → ℝ) : ℝ :=
  ∑ k ∈ Finset.univ.filter (· ≠ s.zero), ∑ a, s.B k a * z (a, k)

/-- On the manifold, totalPz = ∑_{k≠0} P_k(x). -/
theorem totalPz_eq_on_manifold (x : Fin d → ℝ) :
    s.totalPz (fun ij => x ij.1 * x ij.2) = ∑ k ∈ Finset.univ.filter (· ≠ s.zero), s.P k x := by
  simp only [totalPz]; congr 1; ext k; exact s.Pz_eq_on_manifold k x

/-- On the manifold, totalQxz = ∑_{k≠0} Q_k(x)·x_k. -/
theorem totalQxz_eq_on_manifold (x : Fin d → ℝ) :
    s.totalQxz (fun ij => x ij.1 * x ij.2) =
      ∑ k ∈ Finset.univ.filter (· ≠ s.zero), s.Q k x * x k := by
  simp only [totalQxz, Q]
  congr 1; ext k
  simp_rw [show ∀ a, s.B k a * (x a * x k) = s.B k a * x a * x k from fun a => by ring]
  rw [← Finset.sum_mul]

/-- Column coupling: ∑_{k≠0} z(k,j)·x0Qz_k(z). From [LPP] Theorem 15 Case 2:
the chain rule for z'_{0,j} produces ∑(x_k·x_j·x_0·Q_k) which lifts to
∑_{k≠0} z(k,j)·x0Qz_k in z-space.
On manifold: equals z(0,j)·totalQxz = x₀·xⱼ·∑_{k≠0} Q_k·x_k. -/
def colCoupling (j : Fin d) (z : Fin d × Fin d → ℝ) : ℝ :=
  ∑ k ∈ Finset.univ.filter (· ≠ s.zero), z (k, j) * s.x0Qz k z

/-- Row coupling: ∑_{k≠0} z(i,k)·x0Qz_k(z). Symmetric variant of colCoupling
for Case 2b (z'_{i,0}). -/
def rowCoupling (i : Fin d) (z : Fin d × Fin d → ℝ) : ℝ :=
  ∑ k ∈ Finset.univ.filter (· ≠ s.zero), z (i, k) * s.x0Qz k z

/-- On manifold, colCoupling j = x₀·xⱼ·∑_{k≠0} Q_k·x_k. -/
theorem colCoupling_eq_on_manifold (j : Fin d) (x : Fin d → ℝ) :
    s.colCoupling j (fun ab => x ab.1 * x ab.2) =
    (x s.zero * x j) *
    ∑ k ∈ Finset.univ.filter (· ≠ s.zero), s.Q k x * x k := by
  simp only [colCoupling]
  have h_x0Q : ∀ k, s.x0Qz k (fun ab => x ab.1 * x ab.2) = x s.zero * s.Q k x :=
    fun k => s.x0Qz_eq_on_manifold k x
  simp_rw [h_x0Q]
  simp_rw [show ∀ k, (x k * x j) * (x s.zero * s.Q k x) =
      (x s.zero * x j) * (s.Q k x * x k) from fun k => by ring]
  rw [← Finset.mul_sum]

/-- On manifold, rowCoupling i = xᵢ·x₀·∑_{k≠0} Q_k·x_k. -/
theorem rowCoupling_eq_on_manifold (i : Fin d) (x : Fin d → ℝ) :
    s.rowCoupling i (fun ab => x ab.1 * x ab.2) =
    (x i * x s.zero) *
    ∑ k ∈ Finset.univ.filter (· ≠ s.zero), s.Q k x * x k := by
  simp only [rowCoupling]
  have h_x0Q : ∀ k, s.x0Qz k (fun ab => x ab.1 * x ab.2) = x s.zero * s.Q k x :=
    fun k => s.x0Qz_eq_on_manifold k x
  simp_rw [h_x0Q]
  simp_rw [show ∀ k, (x i * x k) * (x s.zero * s.Q k x) =
      (x i * x s.zero) * (s.Q k x * x k) from fun k => by ring]
  rw [← Finset.mul_sum]

/-! ### Non-negativity of z-space building blocks -/

/-- totalPz is non-negative on the non-negative orthant. -/
theorem totalPz_nonneg (z : Fin d × Fin d → ℝ) (hz : ∀ p, 0 ≤ z p) :
    0 ≤ s.totalPz z :=
  Finset.sum_nonneg fun k _ => s.Pz_nonneg k z hz

/-- totalQxz is non-negative on the non-negative orthant. -/
theorem totalQxz_nonneg (z : Fin d × Fin d → ℝ) (hz : ∀ p, 0 ≤ z p) :
    0 ≤ s.totalQxz z :=
  Finset.sum_nonneg fun k _ =>
    Finset.sum_nonneg fun a _ => mul_nonneg (s.B_nonneg k a) (hz _)

/-- colCoupling is non-negative on the non-negative orthant. -/
theorem colCoupling_nonneg (j : Fin d) (z : Fin d × Fin d → ℝ) (hz : ∀ p, 0 ≤ z p) :
    0 ≤ s.colCoupling j z :=
  Finset.sum_nonneg fun k _ => mul_nonneg (hz _) (s.x0Qz_nonneg k z hz)

/-- rowCoupling is non-negative on the non-negative orthant. -/
theorem rowCoupling_nonneg (i : Fin d) (z : Fin d × Fin d → ℝ) (hz : ∀ p, 0 ≤ z p) :
    0 ≤ s.rowCoupling i z :=
  Finset.sum_nonneg fun k _ => mul_nonneg (hz _) (s.x0Qz_nonneg k z hz)

/-! ### Scaling (homogeneity) lemmas

These establish the polynomial degree of each building block:
Pz, x0Qz, totalPz, totalQxz are degree 1 (linear);
colCoupling, rowCoupling are degree 2 (quadratic);
ppField is degree 2 (homogeneous). -/

/-- Pz scales linearly: Pz(c•z) = c · Pz(z). -/
theorem Pz_smul (i : Fin d) (c : ℝ) (z : Fin d × Fin d → ℝ) :
    s.Pz i (c • z) = c * s.Pz i z := by
  simp only [Pz, Pi.smul_apply, smul_eq_mul]
  simp_rw [show ∀ a b, s.A i a b * (c * z (a, b)) = c * (s.A i a b * z (a, b))
    from fun a b => by ring]
  simp_rw [← Finset.mul_sum]

/-- x0Qz scales linearly: x0Qz(c•z) = c · x0Qz(z). -/
theorem x0Qz_smul (i : Fin d) (c : ℝ) (z : Fin d × Fin d → ℝ) :
    s.x0Qz i (c • z) = c * s.x0Qz i z := by
  simp only [x0Qz, Pi.smul_apply, smul_eq_mul]
  simp_rw [show ∀ a, s.B i a * (c * z (s.zero, a)) = c * (s.B i a * z (s.zero, a))
    from fun a => by ring]
  rw [← Finset.mul_sum]

/-- totalPz scales linearly. -/
theorem totalPz_smul (c : ℝ) (z : Fin d × Fin d → ℝ) :
    s.totalPz (c • z) = c * s.totalPz z := by
  simp only [totalPz, s.Pz_smul]
  rw [← Finset.mul_sum]

/-- totalQxz scales linearly. -/
theorem totalQxz_smul (c : ℝ) (z : Fin d × Fin d → ℝ) :
    s.totalQxz (c • z) = c * s.totalQxz z := by
  simp only [totalQxz, Pi.smul_apply, smul_eq_mul]
  simp_rw [show ∀ k a, s.B k a * (c * z (a, k)) = c * (s.B k a * z (a, k))
    from fun k a => by ring]
  simp_rw [← Finset.mul_sum]

/-- colCoupling scales quadratically: colCoupling(c•z) = c² · colCoupling(z). -/
theorem colCoupling_smul (j : Fin d) (c : ℝ) (z : Fin d × Fin d → ℝ) :
    s.colCoupling j (c • z) = c ^ 2 * s.colCoupling j z := by
  simp only [colCoupling, Pi.smul_apply, smul_eq_mul, s.x0Qz_smul]
  simp_rw [show ∀ k, c * z (k, j) * (c * s.x0Qz k z) = c ^ 2 * (z (k, j) * s.x0Qz k z)
    from fun k => by ring]
  rw [← Finset.mul_sum]

/-- rowCoupling scales quadratically. -/
theorem rowCoupling_smul (i : Fin d) (c : ℝ) (z : Fin d × Fin d → ℝ) :
    s.rowCoupling i (c • z) = c ^ 2 * s.rowCoupling i z := by
  simp only [rowCoupling, Pi.smul_apply, smul_eq_mul, s.x0Qz_smul]
  simp_rw [show ∀ k, c * z (i, k) * (c * s.x0Qz k z) = c ^ 2 * (z (i, k) * s.x0Qz k z)
    from fun k => by ring]
  rw [← Finset.mul_sum]

/-- The PP self-product z-field: degree-2 field on Fin d × Fin d obtained by
symbolic substitution x_a·x_b → z_{a,b} from the Stage 2 cubic form.
Agrees with selfProductField on the self-product manifold {z_{i,j} = x_i·x_j}.

Three cases from [LPP] Theorem 15 §3.5:
- Case 1 (i,j ≠ 0): z' = (z_{0,j}·Pz_i + z_{0,i}·Pz_j) - z_{i,j}·(x0Qz_i + x0Qz_j)
- Case 2a (i=0,j≠0): z' = z_{0,0}·Pz_j + ∑_{k≠0} z(k,j)·x0Qz_k - z_{0,j}·(x0Qz_j + totalPz)
- Case 2b (i≠0,j=0): z' = z_{0,0}·Pz_i + ∑_{k≠0} z(i,k)·x0Qz_k - z_{i,0}·(x0Qz_i + totalPz)
- Case 3 (i=j=0): z' = 2·z_{0,0}·(totalQxz - totalPz)

NOTE: This field is NOT globally conservative (∑ ppField z ≠ 0 for non-symmetric z).
It is conservative on the self-product manifold where z(i,j) = z(j,i). -/
noncomputable def ppField :
    (Fin d × Fin d → ℝ) → Fin d × Fin d → ℝ :=
  fun z ij =>
    if ij.1 ≠ s.zero ∧ ij.2 ≠ s.zero then
      -- Case 1: i,j ≠ zero
      (z (s.zero, ij.2) * s.Pz ij.1 z + z (s.zero, ij.1) * s.Pz ij.2 z) -
      z ij * (s.x0Qz ij.1 z + s.x0Qz ij.2 z)
    else if ij.1 = s.zero ∧ ij.2 = s.zero then
      -- Case 3: i = j = zero
      2 * z (s.zero, s.zero) * (s.totalQxz z - s.totalPz z)
    else if ij.1 = s.zero then
      -- Case 2a: first = zero, second ≠ zero ([LPP] Theorem 15 Case 2)
      z (s.zero, s.zero) * s.Pz ij.2 z + s.colCoupling ij.2 z -
      z ij * (s.x0Qz ij.2 z + s.totalPz z)
    else
      -- Case 2b: second = zero, first ≠ zero (symmetric to 2a)
      z (s.zero, s.zero) * s.Pz ij.1 z + s.rowCoupling ij.1 z -
      z ij * (s.x0Qz ij.1 z + s.totalPz z)

/-- ppField agrees with selfProductField on the self-product manifold.
On {z_{a,b} = x_a·x_b} with ∑x = 1, the degree-2 ppField and the degree-4
selfProductField evaluate to the same value for every (i,j). -/
theorem ppField_eq_on_manifold (x : Fin d → ℝ) (hsum : ∑ j, x j = 1)
    (ij : Fin d × Fin d) :
    s.ppField (fun ab => x ab.1 * x ab.2) ij =
    selfProductField field (fun ab => x ab.1 * x ab.2) ij := by
  -- Reduce selfProductField: rowSum on manifold recovers x
  have h_row : selfProduct_rowSum (fun ab : Fin d × Fin d => x ab.1 * x ab.2) = x :=
    funext (selfProduct_rowSum_eq hsum)
  simp only [selfProductField, h_row]
  -- Beta-reduce z-value applications (needed because ring treats lambdas as opaque)
  have hz_β : ∀ ab : Fin d × Fin d,
      (fun p : Fin d × Fin d => x p.1 * x p.2) ab = x ab.1 * x ab.2 := fun _ => rfl
  -- Helper: expand field x zero using conservation + Stage 2 form
  have h_fz : field x s.zero =
      x s.zero * (∑ k ∈ Finset.univ.filter (· ≠ s.zero), s.Q k x * x k -
                  ∑ k ∈ Finset.univ.filter (· ≠ s.zero), s.P k x) := by
    have h_each : ∀ k ∈ Finset.univ.filter (· ≠ s.zero),
        field x k = (s.P k x - s.Q k x * x k) * x s.zero :=
      fun k hk => s.field_eq k (Finset.mem_filter.mp hk).2 x
    rw [s.field_zero x, Finset.sum_congr rfl h_each, ← Finset.sum_mul,
        Finset.sum_sub_distrib]
    ring
  -- Case split on ppField
  unfold ppField
  split_ifs with h1 h3 h2a
  · -- Case 1: i,j ≠ zero
    obtain ⟨hi, hj⟩ := h1
    have h_fi : field x ij.1 = (s.P ij.1 x - s.Q ij.1 x * x ij.1) * x s.zero :=
      s.field_eq ij.1 hi x
    have h_fj : field x ij.2 = (s.P ij.2 x - s.Q ij.2 x * x ij.2) * x s.zero :=
      s.field_eq ij.2 hj x
    rw [s.Pz_eq_on_manifold ij.1, s.Pz_eq_on_manifold ij.2,
        s.x0Qz_eq_on_manifold ij.1, s.x0Qz_eq_on_manifold ij.2,
        h_fi, h_fj]
    ring
  · -- Case 3: i = j = zero
    obtain ⟨hi, hj⟩ := h3
    rw [hi, hj, s.totalQxz_eq_on_manifold, s.totalPz_eq_on_manifold, h_fz]
    ring
  · -- Case 2a: first = zero, second ≠ zero
    have hj : ij.2 ≠ s.zero := by
      intro h; exact h3 ⟨h2a, h⟩
    have hxi : x ij.1 = x s.zero := congr_arg x h2a
    have h_fj : field x ij.2 = (s.P ij.2 x - s.Q ij.2 x * x ij.2) * x s.zero :=
      s.field_eq ij.2 hj x
    have hz00 : (fun ab : Fin d × Fin d => x ab.1 * x ab.2) (s.zero, s.zero) =
        x s.zero * x s.zero := rfl
    have hzij : (fun ab : Fin d × Fin d => x ab.1 * x ab.2) ij = x ij.1 * x ij.2 := rfl
    rw [h2a, s.Pz_eq_on_manifold, s.x0Qz_eq_on_manifold,
        s.colCoupling_eq_on_manifold, s.totalPz_eq_on_manifold,
        h_fj, h_fz, hz00, hzij, hxi]
    ring
  · -- Case 2b: second = zero, first ≠ zero
    have hi : ij.1 ≠ s.zero := h2a
    have hj : ij.2 = s.zero := by
      by_contra h; exact absurd ⟨hi, h⟩ h1
    have hxj : x ij.2 = x s.zero := congr_arg x hj
    -- Use folded form (P, Q) to match ppField's Pz/x0Qz rewrites
    have h_fi : field x ij.1 = (s.P ij.1 x - s.Q ij.1 x * x ij.1) * x s.zero :=
      s.field_eq ij.1 hi x
    -- Beta-reduce z-applications and substitute ij.2 = zero
    have hz00 : (fun ab : Fin d × Fin d => x ab.1 * x ab.2) (s.zero, s.zero) =
        x s.zero * x s.zero := rfl
    have hzij : (fun ab : Fin d × Fin d => x ab.1 * x ab.2) ij = x ij.1 * x ij.2 := rfl
    rw [hj, s.Pz_eq_on_manifold, s.x0Qz_eq_on_manifold,
        s.rowCoupling_eq_on_manifold, s.totalPz_eq_on_manifold,
        h_fi, h_fz, hz00, hzij, hxj]
    ring

/-- ppField is degree-2 homogeneous: ppField(c•z) = c² · ppField(z).
This is a necessary condition for PP-implementability (production function
must be homogeneous degree 2). -/
theorem ppField_homog (c : ℝ) (z : Fin d × Fin d → ℝ) (ij : Fin d × Fin d) :
    s.ppField (c • z) ij = c ^ 2 * s.ppField z ij := by
  unfold ppField
  split_ifs with h1 h3 h2a
  all_goals simp only [Pi.smul_apply, smul_eq_mul]
  · rw [s.Pz_smul, s.Pz_smul, s.x0Qz_smul, s.x0Qz_smul]; ring
  · rw [s.totalQxz_smul, s.totalPz_smul]; ring
  · rw [s.Pz_smul, s.colCoupling_smul, s.x0Qz_smul, s.totalPz_smul]; ring
  · rw [s.Pz_smul, s.rowCoupling_smul, s.x0Qz_smul, s.totalPz_smul]; ring

/-! ### CRN decomposition of ppField

ppField has the CRN form: ppField(z)_{ij} = ppProd(ij,z) - ppDegr(ij,z)·z_{ij}
with ppProd ≥ 0 and ppDegr ≥ 0 on the non-negative orthant. -/

/-- Production part of the CRN decomposition of ppField. -/
noncomputable def ppProd (ij : Fin d × Fin d) (z : Fin d × Fin d → ℝ) : ℝ :=
  if ij.1 ≠ s.zero ∧ ij.2 ≠ s.zero then
    z (s.zero, ij.2) * s.Pz ij.1 z + z (s.zero, ij.1) * s.Pz ij.2 z
  else if ij.1 = s.zero ∧ ij.2 = s.zero then
    2 * z (s.zero, s.zero) * s.totalQxz z
  else if ij.1 = s.zero then
    z (s.zero, s.zero) * s.Pz ij.2 z + s.colCoupling ij.2 z
  else
    z (s.zero, s.zero) * s.Pz ij.1 z + s.rowCoupling ij.1 z

/-- Degradation part of the CRN decomposition of ppField. -/
noncomputable def ppDegr (ij : Fin d × Fin d) (z : Fin d × Fin d → ℝ) : ℝ :=
  if ij.1 ≠ s.zero ∧ ij.2 ≠ s.zero then
    s.x0Qz ij.1 z + s.x0Qz ij.2 z
  else if ij.1 = s.zero ∧ ij.2 = s.zero then
    2 * s.totalPz z
  else if ij.1 = s.zero then
    s.x0Qz ij.2 z + s.totalPz z
  else
    s.x0Qz ij.1 z + s.totalPz z

/-- ppField = ppProd - ppDegr · z (CRN decomposition). -/
theorem ppField_eq_crn (z : Fin d × Fin d → ℝ) (ij : Fin d × Fin d) :
    s.ppField z ij = s.ppProd ij z - s.ppDegr ij z * z ij := by
  unfold ppField ppProd ppDegr
  split_ifs with h1 h3
  · ring
  · obtain ⟨hi, hj⟩ := h3
    have : z ij = z (s.zero, s.zero) := by rw [show ij = (s.zero, s.zero) from Prod.ext hi hj]
    rw [this]; ring
  all_goals ring

/-- ppProd is non-negative on the non-negative orthant. -/
theorem ppProd_nonneg (ij : Fin d × Fin d) (z : Fin d × Fin d → ℝ)
    (hz : ∀ p : Fin d × Fin d, 0 ≤ z p) :
    0 ≤ s.ppProd ij z := by
  unfold ppProd
  split_ifs with h1 h3 h2a
  · -- Case 1: z(0,j)·Pz_i + z(0,i)·Pz_j
    exact add_nonneg
      (mul_nonneg (hz _) (s.Pz_nonneg ij.1 z hz))
      (mul_nonneg (hz _) (s.Pz_nonneg ij.2 z hz))
  · -- Case 3: 2·z(0,0)·totalQxz
    exact mul_nonneg (mul_nonneg (by norm_num) (hz _))
      (s.totalQxz_nonneg z hz)
  · -- Case 2a: z(0,0)·Pz_j + colCoupling_j
    exact add_nonneg
      (mul_nonneg (hz _) (s.Pz_nonneg ij.2 z hz))
      (s.colCoupling_nonneg ij.2 z hz)
  · -- Case 2b: z(0,0)·Pz_i + rowCoupling_i
    exact add_nonneg
      (mul_nonneg (hz _) (s.Pz_nonneg ij.1 z hz))
      (s.rowCoupling_nonneg ij.1 z hz)

/-- ppDegr is non-negative on the non-negative orthant. -/
theorem ppDegr_nonneg (ij : Fin d × Fin d) (z : Fin d × Fin d → ℝ)
    (hz : ∀ p : Fin d × Fin d, 0 ≤ z p) :
    0 ≤ s.ppDegr ij z := by
  unfold ppDegr
  split_ifs with h1 h3 h2a
  · exact add_nonneg (s.x0Qz_nonneg ij.1 z hz) (s.x0Qz_nonneg ij.2 z hz)
  · exact mul_nonneg (by norm_num) (s.totalPz_nonneg z hz)
  · exact add_nonneg (s.x0Qz_nonneg ij.2 z hz) (s.totalPz_nonneg z hz)
  · exact add_nonneg (s.x0Qz_nonneg ij.1 z hz) (s.totalPz_nonneg z hz)

end Stage2CubicForm

/-! ## Stage Theorems

The four stages of the GPAC → PP translation. Each stage is stated
as a theorem that transforms one type of system into a more restricted one
while preserving the computed limit. -/

/-- Stage 1 (Theorem 12 in [LPP]):
Any solution of a CRN is a solution of a CRN-implementable system
of degree at most two.

The construction introduces v-variables: v_{i₁,...,iₙ} = x₁^{i₁}···xₙ^{iₙ}
for each monomial. The resulting system is quadratic and CRN-implementable. -/
theorem stage1_quadraticization {d : ℕ} {α : ℝ}
    (btc : BoundedTimeComputable d α) :
    ∃ d' : ℕ, ∃ field' : (Fin d' → ℝ) → Fin d' → ℝ,
      ∃ _ : IsCRNImplementable d' field',
        ∃ btc' : BoundedTimeComputable d' α, True := by
  sorry

/-- Stage 2 (Theorem 13 in [LPP]):
Any solution of a quadratic CRN is a solution of a TPP-implementable
cubic form system.

The construction:
1. Apply λ-trick to shrink variables to [0,1]
2. Introduce balancing variable x₀ with ∑ᵢ xᵢ = 1
3. Apply balancing dilation (g-trick): multiply each x'ᵢ by x₀
4. Set x'₀ = -∑ᵢ x'ᵢ to ensure conservation -/
theorem stage2_to_tpp {d : ℕ} {α : ℝ}
    (btc : BoundedTimeComputable d α) :
    ∃ d' : ℕ, ∃ field' : (Fin d' → ℝ) → Fin d' → ℝ,
      ∃ _ : IsTPPImplementable d' field',
        ∃ btc' : BoundedTimeComputable d' α, True := by
  sorry

/-- Pure Stage 3 (Theorem 15 in [LPP]):
Given a TPP-implementable system on the simplex with rational initial
conditions and non-negativity, the self-product z_{i,j} = xᵢ·xⱼ gives
an LPP-computable number.

The construction:
1. z_{i,j}(t) = x_i(t)·x_j(t), so z' = selfProductField by product rule
2. selfProductField is PP-implementable (degree 4 in x → degree 2 in z)
3. ∑z = (∑x)² = 1 on simplex
4. Readout: marked z-variables track α

**Preconditions** (guaranteed by Stage 2 output):
- TPP-implementable field with rational simplex initial conditions
- Solution stays non-negative and on simplex for t ≥ 0
- Solution satisfies the field ODE -/
theorem tpp_to_lpp {d : ℕ} {α : ℝ}
    (_hα01 : 0 ≤ α ∧ α ≤ 1)
    (btc : BoundedTimeComputable d α)
    (_tpp : IsTPPImplementable d btc.pivp.field)
    (s : Stage2CubicForm d btc.pivp.field)
    (h_simplex : ∀ t, 0 ≤ t → ∑ i, btc.sol.trajectory t i = 1)
    (h_nonneg : ∀ t, 0 ≤ t → ∀ i, 0 ≤ btc.sol.trajectory t i)
    (h_init_rat : ∀ i, ∃ q : ℚ, btc.sol.trajectory 0 i = ↑q) :
    ∃ _ : IsLPPComputable α, True := by
  -- Abbreviations
  let x := btc.sol.trajectory
  let fld := btc.pivp.field
  let o := btc.pivp.output
  -- Index encoding: Fin d × Fin d ≃ Fin (d * d)
  let e : Fin d × Fin d ≃ Fin (d * d) := finProdFinEquiv
  -- Self-product trajectory: z_i(t) = x_{π₁(i)}(t)·x_{π₂(i)}(t)
  let z : ℝ → Fin (d * d) → ℝ := fun t i =>
    x t (e.symm i).1 * x t (e.symm i).2
  -- Self-product field transported through encoding
  let zfld : (Fin (d * d) → ℝ) → Fin (d * d) → ℝ := fun v i =>
    selfProductField fld (v ∘ e) (e.symm i)
  -- Marked states: output row {e(o, j) | j : Fin d}
  let marked : Finset (Fin (d * d)) := Finset.univ.image (fun j : Fin d => e (o, j))
  -- PP z-field from Stage2CubicForm: degree-2 via symbolic substitution x_a·x_b → z_{a,b}.
  -- s.ppField is defined on Fin d × Fin d; transport it through encoding e to Fin (d*d).
  let ppfld : (Fin (d * d) → ℝ) → Fin (d * d) → ℝ := fun v i =>
    s.ppField (v ∘ e) (e.symm i)
  -- NOTE: PP-implementability (IsPPImplementable) is NOT required here.
  -- The paper [LPP] Theorem 15 claims global conservation of the z-field, but
  -- formal verification shows the z-field is only conservative on the self-product
  -- manifold M = {z(i,j) = x_i·x_j}. For d=2, the residual off-manifold is
  -- z_{00}·(z_{01}-z_{10})·Pz_1. This is a gap in the paper. Since the trajectory
  -- never leaves M, manifold conservation suffices for all downstream properties.
  -- See IsLPPComputable docstring in Defs.lean for details.
  --
  -- Manifold agreement: ppfld and zfld agree on {z_{i,j} = x_i·x_j}
  have h_manifold : ∀ t, 0 ≤ t → ∀ i, ppfld (z t) i = zfld (z t) i := by
    intro t ht i
    change s.ppField (z t ∘ e) (e.symm i) = selfProductField fld (z t ∘ e) (e.symm i)
    have hze : z t ∘ e = fun ij => x t ij.1 * x t ij.2 :=
      funext fun ij => by simp [z, Function.comp]
    rw [hze]
    exact s.ppField_eq_on_manifold (x t) (h_simplex t ht) (e.symm i)
  -- z(t) solves the analytic field zfld by the product rule
  have h_sol_zfld : ∀ t, 0 ≤ t → HasDerivAt z (fun i => zfld (z t) i) t := by
    intro t ht
    refine hasDerivAt_pi.mpr (fun i => ?_)
    have h_sp := hasDerivAt_pi.mp
      (selfProduct_hasDerivAt (btc.sol.is_solution t ht) (h_simplex t ht)) (e.symm i)
    convert h_sp using 1
    change selfProductField fld (z t ∘ e) (e.symm i) =
      selfProductField fld (fun ij => x t ij.1 * x t ij.2) (e.symm i)
    congr 1; ext ij; simp [z]
  -- z(t) solves ppfld because ppfld agrees with zfld on the self-product manifold
  have h_sol_pp : ∀ t, 0 ≤ t → HasDerivAt z (fun i => ppfld (z t) i) t := by
    intro t ht
    convert h_sol_zfld t ht using 1
    ext i; exact h_manifold t ht i
  -- Helper: e is injective on the output row
  have h_e_inj : Function.Injective (fun j : Fin d => e (o, j)) :=
    fun _ _ h => (Prod.mk.inj (e.injective h)).2
  -- Helper: marked sum equals output value on simplex
  have h_sum_marked : ∀ t, 0 ≤ t → ∑ i ∈ marked, z t i = x t o := by
    intro t ht
    rw [Finset.sum_image h_e_inj.injOn]
    simp_rw [show ∀ j : Fin d, z t (e (o, j)) = x t o * x t j from fun j => by simp [z]]
    rw [← Finset.mul_sum, h_simplex t ht, mul_one]
  -- Build IsLPPComputable α
  exact ⟨{
    n := d * d
    field := ppfld
    sol := z
    marked := marked
    init_rational := fun i => by
      obtain ⟨q₁, hq₁⟩ := h_init_rat (e.symm i).1
      obtain ⟨q₂, hq₂⟩ := h_init_rat (e.symm i).2
      refine ⟨q₁ * q₂, ?_⟩
      change btc.sol.trajectory 0 (e.symm i).1 * btc.sol.trajectory 0 (e.symm i).2 = ↑(q₁ * q₂)
      rw [hq₁, hq₂, Rat.cast_mul]
    init_simplex := by
      rw [show (∑ i, z 0 i) = ∑ ij : Fin d × Fin d, x 0 ij.1 * x 0 ij.2 from
        Fintype.sum_equiv e.symm _ _ (fun _ => rfl)]
      exact selfProduct_simplex (h_simplex 0 le_rfl)
    init_nonneg := fun i =>
      mul_nonneg (h_nonneg 0 le_rfl (e.symm i).1) (h_nonneg 0 le_rfl (e.symm i).2)
    simplex := fun t ht => by
      rw [show (∑ i, z t i) = ∑ ij : Fin d × Fin d, x t ij.1 * x t ij.2 from
        Fintype.sum_equiv e.symm _ _ (fun _ => rfl)]
      exact selfProduct_simplex (h_simplex t ht)
    nonneg := fun t ht i =>
      mul_nonneg (h_nonneg t ht (e.symm i).1) (h_nonneg t ht (e.symm i).2)
    is_solution := fun t ht => h_sol_pp t ht
    convergence := by
      rw [Metric.tendsto_atTop]
      intro ε hε
      obtain ⟨r, hr⟩ := exists_nat_gt (-Real.log ε)
      refine ⟨max (btc.modulus r + 1) 0, fun t ht => ?_⟩
      have ht0 : 0 ≤ t := le_trans (le_max_right _ _) ht
      rw [Real.dist_eq, h_sum_marked t ht0]
      calc |x t o - α|
          < Real.exp (-(r : ℝ)) :=
            btc.convergence r t (lt_of_lt_of_le (by linarith : btc.modulus r < btc.modulus r + 1)
              (le_trans (le_max_left _ _) ht))
        _ < ε := by
            calc Real.exp (-(r : ℝ))
                < Real.exp (Real.log ε) := Real.exp_lt_exp.mpr (by linarith)
              _ = ε := Real.exp_log hε
  }, trivial⟩

/-- Stage 3 (full pipeline): any BTC number in [0,1] is LPP-computable.
Chains Stage 1 (quadraticization) → Stage 2 (→ TPP) → pure Stage 3 (→ LPP).

The proof should compose:
  Stage 1: `stage1_quadraticization` (general → quadratic CRN)
  Stage 2: `stage2_to_tpp` (quadratic CRN → TPP on simplex)
  Pure Stage 3: `tpp_to_lpp` (TPP → LPP via self-product) -/
theorem stage3_to_lpp {d : ℕ} {α : ℝ} (hα01 : 0 ≤ α ∧ α ≤ 1)
    (btc : BoundedTimeComputable d α) :
    ∃ _ : IsLPPComputable α, True := by
  sorry

/-- Stage 4 (Theorem 16 / Construction 1 in [LPP]):
Given a syntactic PP balance equation with explicit ℚ coefficients,
the product distribution α_{i,j,k,l} = c_{k,i,j} · c_{l,i,j} / 4
produces a PLPP whose balance field exactly matches the PP field.

**Design note:** Stage 4 requires syntactic (coefficient-level) input,
not just a semantic `IsPPImplementable`. This is because constructing
PLPP transition probabilities requires reading off the polynomial
coefficients c_{r,i,j}. In the pipeline, Stages 1–3 produce explicit
polynomial constructions, so the output is naturally syntactic.
The product distribution gives exact match (no ε-scaling needed)
because Σ_r c_{r,i,j} = 2 ensures Σ_{k,l} α_{i,j,k,l} = 1. -/
theorem stage4_to_plpp {n : ℕ} (eq : SynPPBalance n) :
    ∃ tr : PLPPTransitions n, tr.balanceField = eq.toField :=
  ⟨eq.toPLPPTransitions, eq.toPLPPTransitions_balanceField_eq⟩

/-! ## Main Theorem

The main result of [LPP]: LPPs compute the same set of numbers
in [0,1] as GPACs and CRNs. -/

/-- Main Theorem ([LPP]):
If α ∈ [0,1] is GPAC/CRN computable (bounded-time), then α is
LPP-computable.

The proof composes the four stages:
  CRN → quadratic CRN → TPP cubic → PP quadratic → PLPP → LPP. -/
theorem gpac_to_lpp {α : ℝ} (hα01 : 0 ≤ α ∧ α ≤ 1)
    (h : ∃ d : ℕ, ∃ _ : BoundedTimeComputable d α, True) :
    ∃ _ : IsLPPComputable α, True := by
  obtain ⟨d, btc, _⟩ := h
  exact stage3_to_lpp hα01 btc

/-- Corollary 18 in [LPP]: Algebraic numbers in [0,1] are LPP-computable. -/
theorem algebraic_lpp_computable {α : ℝ} (hα01 : 0 ≤ α ∧ α ≤ 1)
    (halg : ∃ p : Polynomial ℤ, p ≠ 0 ∧ (Polynomial.aeval α p : ℝ) = 0) :
    ∃ _ : IsLPPComputable α, True := by
  sorry

/-! ## Motivating Example

The number ½e⁻¹ is LPP-computable ([LPP] §1.2).

The ODE system:
  F' = -2FE,  E' = -E,  G' = 2FE + E
with F(0) = ½, E(0) = ½, G(0) = 0.

Then F(t) = ½·exp(exp(-t) - 1) → ½e⁻¹ as t → ∞.

The corresponding CRN:
  F + E → G + E  (rate 2)
  E → G -/

/-- ½e⁻¹ is LPP-computable. This is the motivating example from [LPP] §1.2,
demonstrating that the extended LPP notion (with continuum of equilibria)
can compute transcendental numbers. Fully verified — see Example.lean. -/
theorem half_exp_neg_one_lpp_computable :
    ∃ _ : IsLPPComputable (Real.exp (-1) / 2), True :=
  ⟨halfExpNegOne_lpp, trivial⟩

/-! ## LPP Numbers Are in [0,1]

An LPP-computable number is necessarily in the unit interval,
since the readout sum is bounded by the simplex constraint. -/

/-- An LPP-computable number is in [0,1]. The lower bound follows from
non-negativity of states; the upper bound from the simplex constraint. -/
theorem lpp_computable_in_01 {ν : ℝ} (h : IsLPPComputable ν) :
    0 ≤ ν ∧ ν ≤ 1 := by
  constructor
  · exact ge_of_tendsto h.convergence (Filter.eventually_atTop.mpr ⟨0, fun t ht =>
      Finset.sum_nonneg (fun i _ => h.nonneg t ht i)⟩)
  · exact le_of_tendsto h.convergence (Filter.eventually_atTop.mpr ⟨0, fun t ht => by
      calc ∑ i ∈ h.marked, h.sol t i
          ≤ ∑ i, h.sol t i := Finset.sum_le_sum_of_subset_of_nonneg
            (Finset.subset_univ _) (fun i _ _ => h.nonneg t ht i)
        _ = 1 := h.simplex t ht⟩)

/-! ## LPP → CRN-Computable (Easy Direction)

Every LPP-computable number is CRN-computable. This is the "easy"
direction of the main equivalence (Theorem 8 in [LPP]). The proof
augments the LPP system with a readout-sum variable. -/

/-- Every LPP-computable number is CRN-computable.
The construction augments the n-variable LPP with a (n+1)-th variable
tracking the marked-state sum, then extracts a BTC from the augmented
solution and convergence. -/
noncomputable def lpp_to_gpac {ν : ℝ} (h : IsLPPComputable ν) :
    IsCRNComputable ν := by
  -- Extract Tendsto → quantitative convergence
  have h_tend := h.convergence
  have h_quant : ∀ r : ℕ, ∃ T : ℝ, ∀ t, T < t →
      |∑ i ∈ h.marked, h.sol t i - ν| < Real.exp (-(r : ℝ)) := by
    intro r
    obtain ⟨T, hT⟩ := (Metric.tendsto_atTop.mp h_tend) (Real.exp (-(r : ℝ))) (Real.exp_pos _)
    exact ⟨T, fun t ht => by rw [← Real.dist_eq]; exact hT t (le_of_lt ht)⟩
  -- The augmented trajectory: Fin (h.n + 1) → ℝ
  -- Components 0..n-1: original LPP states; component n: readout sum
  let traj : ℝ → Fin (h.n + 1) → ℝ := fun t =>
    vecSnoc (h.sol t) (∑ j ∈ h.marked, h.sol t j)
  -- The augmented field
  let augField : (Fin (h.n + 1) → ℝ) → Fin (h.n + 1) → ℝ := fun v =>
    vecSnoc (h.field (Fin.init v)) (∑ j ∈ h.marked, h.field (Fin.init v) j)
  -- The PIVP
  let pivp : PIVP (h.n + 1) :=
    { field := augField, init := traj 0, output := Fin.last h.n }
  -- Helper: init reduces under vecSnoc
  have h_init : ∀ t, Fin.init (traj t) = h.sol t := by
    intro t; exact vecSnoc_init
  -- The solution
  have h_is_sol : ∀ t : ℝ, 0 ≤ t → HasDerivAt traj (augField (traj t)) t := by
    intro t ht
    have h_aug_eq : augField (traj t) = vecSnoc (h.field (h.sol t))
        (∑ j ∈ h.marked, h.field (h.sol t) j) := by
      simp only [augField, h_init]
    rw [h_aug_eq]
    refine hasDerivAt_pi.mpr (fun i => ?_)
    refine Fin.lastCases ?_ (fun j => ?_) i
    · -- i = last: readout sum
      have h_fn_eq : (fun s => traj s (Fin.last h.n)) =
          (fun s => ∑ j ∈ h.marked, h.sol s j) := by
        funext s; exact vecSnoc_last
      rw [vecSnoc_last, h_fn_eq]
      have h_sum := HasDerivAt.sum (fun j (_ : j ∈ h.marked) =>
        hasDerivAt_pi.mp (h.is_solution t ht) j)
      rwa [show (∑ j ∈ h.marked, fun s => h.sol s j) =
          (fun s => ∑ j ∈ h.marked, h.sol s j) from
          funext (fun s => Finset.sum_apply ..)] at h_sum
    · -- i = castSucc j: original state
      have h_fn_eq : (fun s => traj s (Fin.castSucc j)) = (fun s => h.sol s j) := by
        funext s; exact vecSnoc_castSucc
      rw [vecSnoc_castSucc, h_fn_eq]
      exact hasDerivAt_pi.mp (h.is_solution t ht) j
  let sol : PIVP.Solution pivp :=
    { trajectory := traj, init_cond := rfl, is_solution := h_is_sol }
  -- Boundedness: on the simplex, all components are in [0,1]
  have h_bounded : pivp.IsBounded sol.trajectory := by
    refine ⟨2, two_pos, fun t ht => ?_⟩
    rw [show sol.trajectory t = traj t from rfl,
        (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 2))]
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · -- last: ‖readout sum‖ ≤ 2
      simp only [traj, vecSnoc_last, Real.norm_eq_abs,
          abs_of_nonneg (Finset.sum_nonneg (fun k _ => h.nonneg t ht k))]
      calc ∑ k ∈ h.marked, h.sol t k
          ≤ ∑ k, h.sol t k := Finset.sum_le_sum_of_subset_of_nonneg
            (Finset.subset_univ _) (fun k _ _ => h.nonneg t ht k)
        _ = 1 := h.simplex t ht
        _ ≤ 2 := by norm_num
    · -- castSucc j: ‖sol j‖ ≤ 2
      simp only [traj, vecSnoc_castSucc, Real.norm_eq_abs,
          abs_of_nonneg (h.nonneg t ht j)]
      calc h.sol t j ≤ ∑ k, h.sol t k :=
            Finset.single_le_sum (fun k _ => h.nonneg t ht k) (Finset.mem_univ j)
        _ = 1 := h.simplex t ht
        _ ≤ 2 := by norm_num
  -- Time modulus (extracted from Tendsto via classical choice)
  let modulus : TimeModulus := fun r => (h_quant r).choose
  have h_mod_spec : ∀ r t, modulus r < t →
      |sol.trajectory t pivp.output - ν| < Real.exp (-(r : ℝ)) := by
    intro r t ht
    change |vecSnoc (h.sol t) (∑ j ∈ h.marked, h.sol t j) (Fin.last h.n) - ν| < _
    rw [vecSnoc_last]
    exact (h_quant r).choose_spec t ht
  exact ⟨h.n + 1, ⟨pivp, sol, modulus, h_bounded, h_mod_spec⟩, trivial⟩

/-! ## CRN-Computable Product Closure

The product of two CRN-computable numbers is CRN-computable.
The proof combines two independent PIVPs and adds a product variable. -/

/-- The product of two CRN-computable numbers is CRN-computable.
Given BTC(d₁,α) and BTC(d₂,β), construct BTC(d₁+d₂+1, α·β) by
running both systems in parallel and tracking the product of outputs. -/
noncomputable def crn_computable_mul {α β : ℝ}
    (ha : IsCRNComputable α) (hb : IsCRNComputable β) :
    IsCRNComputable (α * β) := by
  obtain ⟨d₁, btc₁, _⟩ := ha
  obtain ⟨d₂, btc₂, _⟩ := hb
  -- The combined trajectory: (d₁ + d₂) + 1 variables
  -- First d₁: system 1; next d₂: system 2; last: product of outputs
  let t₁ := btc₁.sol.trajectory
  let t₂ := btc₂.sol.trajectory
  let f₁ := btc₁.pivp.field
  let f₂ := btc₂.pivp.field
  let o₁ := btc₁.pivp.output
  let o₂ := btc₂.pivp.output
  -- Projections from the combined state to each subsystem
  let proj₁ : (Fin ((d₁ + d₂) + 1) → ℝ) → Fin d₁ → ℝ := fun v j =>
    v (Fin.castSucc (Fin.castAdd d₂ j))
  let proj₂ : (Fin ((d₁ + d₂) + 1) → ℝ) → Fin d₂ → ℝ := fun v j =>
    v (Fin.castSucc (Fin.natAdd d₁ j))
  -- Output indices lifted to combined space
  let o₁' : Fin ((d₁ + d₂) + 1) := Fin.castSucc (Fin.castAdd d₂ o₁)
  let o₂' : Fin ((d₁ + d₂) + 1) := Fin.castSucc (Fin.natAdd d₁ o₂)
  -- Combined trajectory
  let traj : ℝ → Fin ((d₁ + d₂) + 1) → ℝ := fun t =>
    vecSnoc (vecAddCases (t₁ t) (t₂ t)) (t₁ t o₁ * t₂ t o₂)
  -- Combined field
  let augField : (Fin ((d₁ + d₂) + 1) → ℝ) → Fin ((d₁ + d₂) + 1) → ℝ :=
    fun v => vecSnoc
      (vecAddCases (f₁ (proj₁ v)) (f₂ (proj₂ v)))
      (f₁ (proj₁ v) o₁ * v o₂' + v o₁' * f₂ (proj₂ v) o₂)
  -- PIVP
  let pivp : PIVP ((d₁ + d₂) + 1) :=
    { field := augField, init := traj 0, output := Fin.last (d₁ + d₂) }
  -- Helper: projections recover original trajectories
  have h_proj₁ : ∀ t, proj₁ (traj t) = t₁ t := by
    intro t; funext j; simp [proj₁, traj]
  have h_proj₂ : ∀ t, proj₂ (traj t) = t₂ t := by
    intro t; funext j; simp [proj₂, traj]
  have h_o₁ : ∀ t, traj t o₁' = t₁ t o₁ := by
    intro t; simp [traj, o₁']
  have h_o₂ : ∀ t, traj t o₂' = t₂ t o₂ := by
    intro t; simp [traj, o₂']
  -- HasDerivAt for the combined system
  have h_is_sol : ∀ t : ℝ, 0 ≤ t → HasDerivAt traj (augField (traj t)) t := by
    intro t ht
    have h_aug_eq : augField (traj t) = vecSnoc
        (vecAddCases (f₁ (t₁ t)) (f₂ (t₂ t)))
        (f₁ (t₁ t) o₁ * t₂ t o₂ + t₁ t o₁ * f₂ (t₂ t) o₂) := by
      simp only [augField, h_proj₁, h_proj₂, h_o₁, h_o₂]
    rw [h_aug_eq]
    refine hasDerivAt_pi.mpr (fun i => ?_)
    refine Fin.lastCases ?_ (fun j => ?_) i
    · -- i = last: product variable
      have h_fn_eq : (fun s => traj s (Fin.last _)) = (fun s => t₁ s o₁ * t₂ s o₂) := by
        funext s; simp [traj]
      simp only [vecSnoc_last]
      rw [h_fn_eq]
      exact (hasDerivAt_pi.mp (btc₁.sol.is_solution t ht) o₁).mul
        (hasDerivAt_pi.mp (btc₂.sol.is_solution t ht) o₂)
    · -- i = castSucc j: from one of the two subsystems
      refine Fin.addCases (fun j₁ => ?_) (fun j₂ => ?_) j
      · -- left part: system 1
        have h_fn_eq : (fun s => traj s (Fin.castSucc (Fin.castAdd d₂ j₁))) =
            (fun s => t₁ s j₁) := by
          funext s; simp [traj]
        simp only [vecSnoc_castSucc, vecAddCases_left]
        rw [h_fn_eq]
        exact hasDerivAt_pi.mp (btc₁.sol.is_solution t ht) j₁
      · -- right part: system 2
        have h_fn_eq : (fun s => traj s (Fin.castSucc (Fin.natAdd d₁ j₂))) =
            (fun s => t₂ s j₂) := by
          funext s; simp [traj]
        simp only [vecSnoc_castSucc, vecAddCases_right]
        rw [h_fn_eq]
        exact hasDerivAt_pi.mp (btc₂.sol.is_solution t ht) j₂
  let sol : PIVP.Solution pivp :=
    { trajectory := traj, init_cond := rfl, is_solution := h_is_sol }
  -- Convergence: product of outputs → α * β
  have h_tend : Filter.Tendsto (fun t => t₁ t o₁ * t₂ t o₂) Filter.atTop (nhds (α * β)) :=
    btc₁.to_tendsto.mul btc₂.to_tendsto
  -- Extract modulus from Tendsto
  have h_quant : ∀ r : ℕ, ∃ T : ℝ, ∀ t, T < t →
      |t₁ t o₁ * t₂ t o₂ - α * β| < Real.exp (-(r : ℝ)) := by
    intro r
    obtain ⟨T, hT⟩ := (Metric.tendsto_atTop.mp h_tend) (Real.exp (-(r : ℝ))) (Real.exp_pos _)
    exact ⟨T, fun t ht => by rw [← Real.dist_eq]; exact hT t (le_of_lt ht)⟩
  let modulus : TimeModulus := fun r => (h_quant r).choose
  -- Boundedness
  have h_bounded : pivp.IsBounded sol.trajectory := by
    obtain ⟨M₁, hM₁_pos, hM₁⟩ := btc₁.bounded
    obtain ⟨M₂, hM₂_pos, hM₂⟩ := btc₂.bounded
    refine ⟨M₁ + M₂ + M₁ * M₂, by positivity, fun t ht => ?_⟩
    rw [show sol.trajectory t = traj t from rfl,
        (pi_norm_le_iff_of_nonneg (by positivity))]
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · -- product variable: |x·y| ≤ M₁·M₂ ≤ M₁+M₂+M₁·M₂
      have h_eq : traj t (Fin.last _) = t₁ t o₁ * t₂ t o₂ := by simp [traj]
      rw [h_eq]
      calc |t₁ t o₁ * t₂ t o₂| = |t₁ t o₁| * |t₂ t o₂| := abs_mul _ _
        _ ≤ ‖t₁ t‖ * ‖t₂ t‖ :=
          mul_le_mul (norm_le_pi_norm (t₁ t) o₁)
            (norm_le_pi_norm (t₂ t) o₂) (abs_nonneg _) (norm_nonneg _)
        _ ≤ M₁ * M₂ :=
          mul_le_mul (hM₁ t ht) (hM₂ t ht) (norm_nonneg _) (le_of_lt hM₁_pos)
        _ ≤ M₁ + M₂ + M₁ * M₂ := le_add_of_nonneg_left (by positivity)
    · -- subsystem variables
      refine Fin.addCases (fun j₁ => ?_) (fun j₂ => ?_) j
      · have h_eq : traj t (Fin.castSucc (Fin.castAdd d₂ j₁)) = t₁ t j₁ := by
            simp [traj]
        rw [h_eq]
        calc |t₁ t j₁| = ‖t₁ t j₁‖ := (Real.norm_eq_abs _).symm
          _ ≤ ‖t₁ t‖ := norm_le_pi_norm _ _
          _ ≤ M₁ := hM₁ t ht
          _ ≤ M₁ + M₂ + M₁ * M₂ := by linarith [mul_pos hM₁_pos hM₂_pos]
      · have h_eq : traj t (Fin.castSucc (Fin.natAdd d₁ j₂)) = t₂ t j₂ := by
            simp [traj]
        rw [h_eq]
        calc |t₂ t j₂| = ‖t₂ t j₂‖ := (Real.norm_eq_abs _).symm
          _ ≤ ‖t₂ t‖ := norm_le_pi_norm _ _
          _ ≤ M₂ := hM₂ t ht
          _ ≤ M₁ + M₂ + M₁ * M₂ := by linarith [mul_pos hM₁_pos hM₂_pos]
  -- Package the BTC
  have h_conv : ∀ r t, modulus r < t →
      |sol.trajectory t pivp.output - α * β| < Real.exp (-(r : ℝ)) := by
    intro r t ht
    have h_eq : sol.trajectory t pivp.output = t₁ t o₁ * t₂ t o₂ := by
      simp [sol, pivp, traj]
    rw [h_eq]
    exact (h_quant r).choose_spec t ht
  exact ⟨(d₁ + d₂) + 1, ⟨pivp, sol, modulus, h_bounded, h_conv⟩, trivial⟩

/-! ## Product Protocol (Lemma 11)

LPP-computable numbers are closed under multiplication.
The proof routes through the GPAC pipeline: LPP → CRN → CRN (product)
→ LPP (via Stage 3). -/

/-- Lemma 11 in [LPP]: the product of two LPP-computable numbers
is LPP-computable.

The proof composes: `lpp_to_gpac` (LPP → CRN-computable) with
`crn_computable_mul` (product closure for CRN) and `gpac_to_lpp`
(CRN → LPP, via Stage 3). -/
theorem lpp_computable_mul {α β : ℝ}
    (ha : IsLPPComputable α) (hb : IsLPPComputable β) :
    ∃ _ : IsLPPComputable (α * β), True := by
  have ha01 := lpp_computable_in_01 ha
  have hb01 := lpp_computable_in_01 hb
  exact gpac_to_lpp ⟨mul_nonneg ha01.1 hb01.1, mul_le_one₀ ha01.2 hb01.1 hb01.2⟩
    (crn_computable_mul (lpp_to_gpac ha) (lpp_to_gpac hb))

/-! ## Unimolecular Protocols Compute Only Rationals (Lemma 10)

A large-population unimolecular protocol (LPUP) can only compute
rational numbers. The proof uses the functional graph structure:
each state transitions to exactly one other state, forming rho-shaped
paths that converge to cycles. -/

/-- Lemma 10 in [LPP]: a number computable by a unimolecular LPP
is rational. Unimolecular protocols are too weak to compute
transcendentals — the gap is precisely the bimolecular interactions. -/
theorem lpup_computes_rational {ν : ℝ}
    (h : IsLPPComputable ν)
    (hunimol : ∀ x : Fin h.n → ℝ, ∀ i : Fin h.n,
      ∃ a : Fin h.n → ℝ, h.field x i = ∑ j, a j * x j) :
    ∃ q : ℚ, ν = (q : ℝ) := by
  sorry

end Ripple
