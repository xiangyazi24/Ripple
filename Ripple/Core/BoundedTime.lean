/-
  Ripple.Core.BoundedTime — Bounded-Time Computability

  Defines time modulus and bounded-time complexity classes
  for bounded PIVPs.

  Key definition (from [BAC] Def 2.4):
    A bounded PIVP computes α with time modulus μ : ℕ → ℝ≥0 if
      |x(t) - α| < e^{-r}   whenever  t > μ(r).

  The time complexity of the computation is the asymptotic growth of μ(r).

  Hierarchy (from [BAC] §5):
    Floor 0 (real-time):  μ(r) = Θ(r)        — e.g., e, π
    Floor 1:              μ(r) = Θ(r²)       — quadratic
    Floor n:              μ(r) = Θ(rⁿ)       — degree-n polynomial
    Lambert W:            μ(r) = Θ(r log r)
    Tower k:              μ(r) = Θ(exp^(k+1)(r))
-/

import Ripple.Core.PIVP
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

namespace Ripple

/-- A time modulus is a function μ : ℕ → ℝ such that μ(r) bounds the time
  needed to achieve r bits of precision. -/
def TimeModulus := ℕ → ℝ

/-- A bounded PIVP computes α with time modulus μ if:
  for all r, for all t > μ(r), |x_output(t) - α| < e^{-r}. -/
structure BoundedTimeComputable (d : ℕ) (α : ℝ) where
  /-- The underlying PIVP. -/
  pivp : PIVP d
  /-- The solution to the PIVP. -/
  sol : PIVP.Solution pivp
  /-- The time modulus. -/
  modulus : TimeModulus
  /-- The PIVP is bounded. -/
  bounded : pivp.IsBounded sol.trajectory
  /-- Convergence with the given time modulus. -/
  convergence : ∀ r : ℕ, ∀ t : ℝ, t > modulus r →
    |sol.trajectory t pivp.output - α| < Real.exp (-(r : ℝ))

/-- A real number is CRN-computable if it is computable by some bounded PIVP. -/
def IsCRNComputable (α : ℝ) : Prop :=
  ∃ d : ℕ, ∃ _ : BoundedTimeComputable d α, True

/-- A real number is real-time CRN-computable (floor 0) if it has
  a linear time modulus: μ(r) = O(r), i.e., μ(r) ≤ C(r+1) for some C > 0. -/
def IsRealTimeComputable (α : ℝ) : Prop :=
  ∃ d : ℕ, ∃ btc : BoundedTimeComputable d α,
    ∃ C : ℝ, 0 < C ∧ ∀ r : ℕ, btc.modulus r ≤ C * (↑r + 1)

/-- A real number is polynomial-time CRN-computable (floor n) if it has
  time modulus μ(r) = O(r^n). -/
def IsPolyTimeComputable (α : ℝ) (n : ℕ) : Prop :=
  ∃ d : ℕ, ∃ btc : BoundedTimeComputable d α,
    ∃ C : ℝ, 0 < C ∧ ∀ r : ℕ, btc.modulus r ≤ C * (↑r + 1) ^ n

/-- A bounded-time computation whose underlying system is a syntactic
`PolyPIVP`, rather than an arbitrary semantic `PIVP`. This is the
non-vacuous notion needed for paper-level compilation theorems. -/
structure CertifiedBoundedTimeComputable (d : ℕ) (α : ℝ) where
  /-- The syntactic polynomial/rational PIVP. -/
  pivp : PolyPIVP d
  /-- A semantic solution of the associated ODE. -/
  sol : PIVP.Solution pivp.toPIVP
  /-- Time modulus. -/
  modulus : TimeModulus
  /-- Boundedness of the trajectory. -/
  bounded : pivp.toPIVP.IsBounded sol.trajectory
  /-- Convergence to the target with the stated modulus. -/
  convergence : ∀ r : ℕ, ∀ t : ℝ, t > modulus r →
    |sol.trajectory t pivp.output - α| < Real.exp (-(r : ℝ))

/-- Forget syntactic certificates and recover the older semantic notion. -/
noncomputable def CertifiedBoundedTimeComputable.toBoundedTimeComputable
    {d : ℕ} {α : ℝ} (btc : CertifiedBoundedTimeComputable d α) :
    BoundedTimeComputable d α where
  pivp := btc.pivp.toPIVP
  sol := btc.sol
  modulus := btc.modulus
  bounded := btc.bounded
  convergence := btc.convergence

/-- A real number is CRN-computable by a syntactically certified PIVP. -/
def IsCertifiedCRNComputable (α : ℝ) : Prop :=
  ∃ d : ℕ, ∃ _ : CertifiedBoundedTimeComputable d α, True

/-- A real number is real-time computable by a syntactically certified PIVP. -/
def IsCertifiedRealTimeComputable (α : ℝ) : Prop :=
  ∃ d : ℕ, ∃ btc : CertifiedBoundedTimeComputable d α,
    ∃ C : ℝ, 0 < C ∧ ∀ r : ℕ, btc.modulus r ≤ C * (↑r + 1)

/-- A `BoundedTimeComputable` enriched with the two orbit-level structural
sign conditions required by the HONEST Stage 2 chain:
`output_monotone` (output coordinate non-increasing along the BTC's own
orbit) and `weighted_nonpos` (the λ-trick `c`-weighted inner-field
combination is non-positive along the orbit — the LPP Remark 14 geometric
feasibility condition).

Intended for CRN-encoded Newton iterations approaching α. These fields are
plausibly satisfiable by real LPP constructions (unlike inner-field
conservation, which the v-variable output of Stage 1 is deliberately
non-conservative for). Downstream Stage 2 convergence theorems consume
this structure via `stage2_z0_invariant_final`. -/
structure CRNBoundedTimeComputable (d : ℕ) (α : ℝ) extends BoundedTimeComputable d α where
  /-- The output coordinate is monotone non-increasing along the BTC's own orbit.
  Holds for CRN-encoded Newton iterations approaching α from above. Enables
  Stage 2 convergence without ad-hoc output-sign hypotheses. -/
  output_monotone : ∀ t : ℝ, 0 ≤ t →
    pivp.field (sol.trajectory t) pivp.output ≤ 0
  /-- **LPP λ-trick room condition (orbit form).** For the λ-trick contraction
  parameter `c ∈ (0, 1]`, the `c`-weighted inner-field combination driving the
  Stage 2 slack variable `z₀` is non-positive along the BTC's own orbit:
  `F(x(t))_o + c · ∑_{j ≠ o} F(x(t))_j ≤ 0`.
  This is the *geometric* feasibility condition from [LPP, Remark 14]: the
  Newton-iteration orbit lives in the convex region where weighted motion
  towards the output coordinate dominates motion away from the simplex
  boundary. It is NOT implied by conservation alone (the inner field is
  generally non-conservative; conservation is a property of the *outer*
  balancingDilation-extended system). It IS the λ-trick design condition
  encoded at the structural level. -/
  weighted_nonpos : ∀ (c : ℝ), 0 < c → c ≤ 1 → ∀ t : ℝ, 0 ≤ t →
    pivp.field (sol.trajectory t) pivp.output
      + c * ∑ j ∈ Finset.univ.erase pivp.output,
          pivp.field (sol.trajectory t) j ≤ 0

/-- **Convex-combination reduction for `weighted_nonpos`.**

The structural `weighted_nonpos` field quantifies over all `c ∈ (0, 1]`, but
the expression `A + c·B` is affine in `c`. By convex combination
`A + c·B = (1-c)·A + c·(A+B)`, so the universal statement reduces to the two
endpoint conditions:

  * `A ≤ 0`  (equivalent to the `c → 0⁺` limit, i.e. `output_monotone`)
  * `A + B ≤ 0`  (the `c = 1` case)

This pure algebraic lemma lets us replace the c-parametric hypothesis with
two orbit-level sign conditions, which is what downstream `weighted_nonpos`
proofs (e.g. the v-variable transfer in `LPP/VVariable.lean`) actually need
to verify in practice. -/
lemma weighted_sum_nonpos_of_endpoints (A B c : ℝ)
    (hc : 0 < c) (hc1 : c ≤ 1) (hA : A ≤ 0) (hAB : A + B ≤ 0) :
    A + c * B ≤ 0 := by
  have h_decomp : A + c * B = (1 - c) * A + c * (A + B) := by ring
  rw [h_decomp]
  have h1 : (1 - c) * A ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (by linarith) hA
  have h2 : c * (A + B) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hc.le hAB
  linarith

/-- **Constructor helper: build `CRNBoundedTimeComputable.weighted_nonpos`
from output_monotone + the c=1 endpoint.** Uses
`weighted_sum_nonpos_of_endpoints` to discharge the c-parametric quantifier.
Callers need only verify the `c = 1` sum inequality on the orbit; the
`output_monotone` case at `c → 0⁺` is already the `output_monotone` field.

Saves duplicating the convex-combination argument at every instantiation. -/
lemma CRNBoundedTimeComputable.mk_weighted_nonpos {d : ℕ} {α : ℝ}
    (btc : BoundedTimeComputable d α)
    (h_mono : ∀ t : ℝ, 0 ≤ t →
      btc.pivp.field (btc.sol.trajectory t) btc.pivp.output ≤ 0)
    (h_sum_at_one : ∀ t : ℝ, 0 ≤ t →
      btc.pivp.field (btc.sol.trajectory t) btc.pivp.output
        + ∑ j ∈ Finset.univ.erase btc.pivp.output,
            btc.pivp.field (btc.sol.trajectory t) j ≤ 0) :
    ∀ (c : ℝ), 0 < c → c ≤ 1 → ∀ t : ℝ, 0 ≤ t →
      btc.pivp.field (btc.sol.trajectory t) btc.pivp.output
        + c * ∑ j ∈ Finset.univ.erase btc.pivp.output,
            btc.pivp.field (btc.sol.trajectory t) j ≤ 0 := by
  intro c hc hc1 t ht
  exact weighted_sum_nonpos_of_endpoints _ _ c hc hc1 (h_mono t ht) (h_sum_at_one t ht)

/-- **Full constructor from the two orbit-level endpoints.** Bundles a plain
`BoundedTimeComputable` with `output_monotone` and the `c = 1` sum inequality
into a `CRNBoundedTimeComputable`. The `c`-parametric `weighted_nonpos`
field is discharged via `mk_weighted_nonpos`. -/
def CRNBoundedTimeComputable.ofEndpoints {d : ℕ} {α : ℝ}
    (btc : BoundedTimeComputable d α)
    (h_mono : ∀ t : ℝ, 0 ≤ t →
      btc.pivp.field (btc.sol.trajectory t) btc.pivp.output ≤ 0)
    (h_sum_at_one : ∀ t : ℝ, 0 ≤ t →
      btc.pivp.field (btc.sol.trajectory t) btc.pivp.output
        + ∑ j ∈ Finset.univ.erase btc.pivp.output,
            btc.pivp.field (btc.sol.trajectory t) j ≤ 0) :
    CRNBoundedTimeComputable d α where
  toBoundedTimeComputable := btc
  output_monotone := h_mono
  weighted_nonpos := CRNBoundedTimeComputable.mk_weighted_nonpos btc h_mono h_sum_at_one

/-- Certified CRN-computability implies the older semantic notion. -/
theorem certified_crn_to_crn {α : ℝ} :
    IsCertifiedCRNComputable α → IsCRNComputable α := by
  intro ⟨d, btc, _⟩
  exact ⟨d, btc.toBoundedTimeComputable, trivial⟩

/-- Certified real-time computability implies the older semantic notion. -/
theorem certified_realtime_to_realtime {α : ℝ} :
    IsCertifiedRealTimeComputable α → IsRealTimeComputable α := by
  intro ⟨d, btc, C, hC, hmod⟩
  exact ⟨d, btc.toBoundedTimeComputable, C, hC, hmod⟩

/-- The convergence condition of BoundedTimeComputable implies Filter.Tendsto.
This converts the quantitative bound |sol(t) - α| < e^{-r} for t > μ(r)
into the topological statement sol(t) → α as t → ∞. -/
theorem BoundedTimeComputable.to_tendsto {d : ℕ} {α : ℝ}
    (btc : BoundedTimeComputable d α) :
    Filter.Tendsto (fun t => btc.sol.trajectory t btc.pivp.output)
      Filter.atTop (nhds α) := by
  rw [Metric.tendsto_atTop']
  intro ε hε
  -- Find r : ℕ such that exp(-r) < ε
  have h_exp : ∃ r : ℕ, Real.exp (-(r : ℝ)) < ε := by
    obtain ⟨n, hn⟩ := exists_nat_gt (-Real.log ε)
    exact ⟨n, by rwa [← Real.lt_log_iff_exp_lt hε, neg_lt]⟩
  obtain ⟨r, hr⟩ := h_exp
  exact ⟨btc.modulus r, fun t ht => by
    calc dist (btc.sol.trajectory t btc.pivp.output) α
        = |btc.sol.trajectory t btc.pivp.output - α| := Real.dist_eq _ _
      _ < Real.exp (-(r : ℝ)) := btc.convergence r t ht
      _ < ε := hr⟩

/-- Addition closure for real-time computable numbers (from [RTCRN2]).
  Constructs a combined (d₁+d₂+1)-dimensional PIVP that runs both sub-PIVPs in
  parallel with a sum-tracking output variable.
  Convergence uses triangle inequality + 2e^{-(r+1)} ≤ e^{-r} (since 2 ≤ e). -/
theorem realtime_field_add {α β : ℝ} :
    IsRealTimeComputable α → IsRealTimeComputable β → IsRealTimeComputable (α + β) := by
  intro ⟨d₁, btc₁, C₁, hC₁, hmod₁⟩ ⟨d₂, btc₂, C₂, hC₂, hmod₂⟩
  -- Combined PIVP: first d₁ components run PIVP₁, next d₂ run PIVP₂,
  -- last component tracks x₁_output + x₂_output.
  refine ⟨(d₁ + d₂) + 1, {
    pivp := {
      field := fun v =>
        let v₁ : Fin d₁ → ℝ := fun j => v (Fin.castSucc (Fin.castAdd d₂ j))
        let v₂ : Fin d₂ → ℝ := fun j => v (Fin.castSucc (Fin.natAdd d₁ j))
        Fin.snoc (Fin.append (btc₁.pivp.field v₁) (btc₂.pivp.field v₂))
          (btc₁.pivp.field v₁ btc₁.pivp.output + btc₂.pivp.field v₂ btc₂.pivp.output)
      init := Fin.snoc (Fin.append btc₁.pivp.init btc₂.pivp.init)
          (btc₁.pivp.init btc₁.pivp.output + btc₂.pivp.init btc₂.pivp.output)
      output := Fin.last (d₁ + d₂) }
    sol := {
      trajectory := fun t =>
        Fin.snoc (Fin.append (btc₁.sol.trajectory t) (btc₂.sol.trajectory t))
          (btc₁.sol.trajectory t btc₁.pivp.output + btc₂.sol.trajectory t btc₂.pivp.output)
      init_cond := by simp only [btc₁.sol.init_cond, btc₂.sol.init_cond]
      is_solution := fun t ht => by
        have hd₁ := btc₁.sol.is_solution t ht
        have hd₂ := btc₂.sol.is_solution t ht
        rw [hasDerivAt_pi] at hd₁ hd₂ ⊢
        refine Fin.lastCases ?_ (fun j => ?_)
        · -- Last component (sum tracker): d/dt (x₁_o₁ + x₂_o₂)
          simp only [Fin.snoc_last, Fin.snoc_castSucc, Fin.append_left, Fin.append_right]
          exact (hd₁ btc₁.pivp.output).add (hd₂ btc₂.pivp.output)
        · -- Sub-PIVP components
          refine Fin.addCases (fun j₁ => ?_) (fun j₂ => ?_) j
          · simp only [Fin.snoc_castSucc, Fin.append_left]
            exact hd₁ j₁
          · simp only [Fin.snoc_castSucc, Fin.append_right]
            exact hd₂ j₂ }
    modulus := fun r => max (btc₁.modulus (r + 1)) (btc₂.modulus (r + 1))
    bounded := ?_
    convergence := ?_ }, 2 * max C₁ C₂, by positivity, ?_⟩
  · -- Bounded: all components bounded by M₁ + M₂
    obtain ⟨M₁, hM₁, hb₁⟩ := btc₁.bounded
    obtain ⟨M₂, hM₂, hb₂⟩ := btc₂.bounded
    refine ⟨M₁ + M₂, by linarith, fun t ht => ?_⟩
    rw [pi_norm_le_iff_of_nonneg (by linarith)]
    refine Fin.lastCases ?_ (fun j => ?_)
    · -- Sum component
      simp only [Fin.snoc_last]
      rw [Real.norm_eq_abs]
      have h₁ : |btc₁.sol.trajectory t btc₁.pivp.output| ≤ M₁ := by
        have hcomp := norm_le_pi_norm (btc₁.sol.trajectory t) btc₁.pivp.output
        rw [Real.norm_eq_abs] at hcomp; linarith [hb₁ t ht]
      have h₂ : |btc₂.sol.trajectory t btc₂.pivp.output| ≤ M₂ := by
        have hcomp := norm_le_pi_norm (btc₂.sol.trajectory t) btc₂.pivp.output
        rw [Real.norm_eq_abs] at hcomp; linarith [hb₂ t ht]
      linarith [abs_add_le (btc₁.sol.trajectory t btc₁.pivp.output)
                           (btc₂.sol.trajectory t btc₂.pivp.output)]
    · -- Sub-PIVP components
      refine Fin.addCases (fun j₁ => ?_) (fun j₂ => ?_) j
      · simp only [Fin.snoc_castSucc, Fin.append_left]
        calc ‖btc₁.sol.trajectory t j₁‖
            ≤ ‖btc₁.sol.trajectory t‖ := norm_le_pi_norm _ _
          _ ≤ M₁ := hb₁ t ht
          _ ≤ M₁ + M₂ := le_add_of_nonneg_right (le_of_lt hM₂)
      · simp only [Fin.snoc_castSucc, Fin.append_right]
        calc ‖btc₂.sol.trajectory t j₂‖
            ≤ ‖btc₂.sol.trajectory t‖ := norm_le_pi_norm _ _
          _ ≤ M₂ := hb₂ t ht
          _ ≤ M₁ + M₂ := le_add_of_nonneg_left (le_of_lt hM₁)
  · -- Convergence: triangle inequality + 2e^{-(r+1)} ≤ e^{-r}
    intro r t ht
    simp only [Fin.snoc_last]
    have ht₁ : t > btc₁.modulus (r + 1) := lt_of_le_of_lt (le_max_left _ _) ht
    have ht₂ : t > btc₂.modulus (r + 1) := lt_of_le_of_lt (le_max_right _ _) ht
    have hc₁ := btc₁.convergence (r + 1) t ht₁
    have hc₂ := btc₂.convergence (r + 1) t ht₂
    have htri : |btc₁.sol.trajectory t btc₁.pivp.output +
        btc₂.sol.trajectory t btc₂.pivp.output - (α + β)|
      ≤ |btc₁.sol.trajectory t btc₁.pivp.output - α| +
        |btc₂.sol.trajectory t btc₂.pivp.output - β| := by
      have : btc₁.sol.trajectory t btc₁.pivp.output +
          btc₂.sol.trajectory t btc₂.pivp.output - (α + β) =
          (btc₁.sol.trajectory t btc₁.pivp.output - α) +
          (btc₂.sol.trajectory t btc₂.pivp.output - β) := by ring
      rw [this]; exact abs_add_le _ _
    have hexp : 2 * Real.exp (-(↑(r + 1) : ℝ)) ≤ Real.exp (-(↑r : ℝ)) := by
      have hcast : (-(↑(r + 1) : ℝ)) = -(↑r : ℝ) + (-1 : ℝ) := by push_cast; ring
      rw [hcast, Real.exp_add]
      have h2e : 2 * Real.exp (-1 : ℝ) ≤ 1 := by
        rw [Real.exp_neg, ← div_eq_mul_inv, div_le_one (Real.exp_pos 1)]
        linarith [Real.add_one_le_exp (1 : ℝ)]
      calc 2 * (Real.exp (-(↑r : ℝ)) * Real.exp (-1))
          = Real.exp (-(↑r : ℝ)) * (2 * Real.exp (-1)) := by ring
        _ ≤ Real.exp (-(↑r : ℝ)) * 1 :=
            mul_le_mul_of_nonneg_left h2e (le_of_lt (Real.exp_pos _))
        _ = Real.exp (-(↑r : ℝ)) := mul_one _
    linarith
  · -- Linear modulus: max(μ₁(r+1), μ₂(r+1)) ≤ 2·max(C₁,C₂)·(r+1)
    intro r
    have h₁ : btc₁.modulus (r + 1) ≤ max C₁ C₂ * (↑r + 2) := by
      calc btc₁.modulus (r + 1)
          ≤ C₁ * (↑(r + 1) + 1) := hmod₁ (r + 1)
        _ = C₁ * (↑r + 2) := by push_cast; ring
        _ ≤ max C₁ C₂ * (↑r + 2) :=
            mul_le_mul_of_nonneg_right (le_max_left C₁ C₂)
              (by positivity)
    have h₂ : btc₂.modulus (r + 1) ≤ max C₁ C₂ * (↑r + 2) := by
      calc btc₂.modulus (r + 1)
          ≤ C₂ * (↑(r + 1) + 1) := hmod₂ (r + 1)
        _ = C₂ * (↑r + 2) := by push_cast; ring
        _ ≤ max C₁ C₂ * (↑r + 2) :=
            mul_le_mul_of_nonneg_right (le_max_right C₁ C₂)
              (by positivity)
    calc max (btc₁.modulus (r + 1)) (btc₂.modulus (r + 1))
        ≤ max C₁ C₂ * (↑r + 2) := max_le h₁ h₂
      _ ≤ max C₁ C₂ * (2 * (↑r + 1)) := by
          apply mul_le_mul_of_nonneg_left
          · have : (0 : ℝ) ≤ ↑r := Nat.cast_nonneg r; linarith
          · exact le_of_lt (lt_of_lt_of_le hC₁ (le_max_left C₁ C₂))
      _ = 2 * max C₁ C₂ * (↑r + 1) := by ring

/-- Multiplication closure for real-time computable numbers (from [RTCRN2]).
  Constructs a combined (d₁+d₂+1)-dimensional PIVP that runs both sub-PIVPs in
  parallel with a product-tracking output variable (using the product rule).
  Convergence uses the three-term decomposition
  x₁x₂-αβ = x₁(x₂-β) + (x₁-α)x₂ - (x₁-α)(x₂-β) with a
  modulus shift by K = ⌈M₁+M₂+1⌉ to absorb the constant factor. -/
theorem realtime_field_mul {α β : ℝ} :
    IsRealTimeComputable α → IsRealTimeComputable β → IsRealTimeComputable (α * β) := by
  intro ⟨d₁, btc₁, C₁, hC₁, hmod₁⟩ ⟨d₂, btc₂, C₂, hC₂, hmod₂⟩
  obtain ⟨M₁, hM₁, hb₁⟩ := btc₁.bounded
  obtain ⟨M₂, hM₂, hb₂⟩ := btc₂.bounded
  -- K : ℕ with e^K > M₁+M₂+1 (via 1+x ≤ e^x)
  set K := Nat.ceil (M₁ + M₂ + 1) with hK_def
  have hK : M₁ + M₂ + 1 ≤ (↑K : ℝ) := Nat.le_ceil _
  have hexp_K : M₁ + M₂ + 1 < Real.exp (↑K : ℝ) :=
    calc M₁ + M₂ + 1 ≤ (↑K : ℝ) := hK
      _ < (↑K : ℝ) + 1 := by linarith
      _ ≤ Real.exp (↑K : ℝ) := Real.add_one_le_exp _
  -- Component bound helpers
  have hx₁_bound : ∀ t, 0 ≤ t → |btc₁.sol.trajectory t btc₁.pivp.output| ≤ M₁ := by
    intro t ht
    have := norm_le_pi_norm (btc₁.sol.trajectory t) btc₁.pivp.output
    rw [Real.norm_eq_abs] at this; linarith [hb₁ t ht]
  have hx₂_bound : ∀ t, 0 ≤ t → |btc₂.sol.trajectory t btc₂.pivp.output| ≤ M₂ := by
    intro t ht
    have := norm_le_pi_norm (btc₂.sol.trajectory t) btc₂.pivp.output
    rw [Real.norm_eq_abs] at this; linarith [hb₂ t ht]
  -- Combined PIVP: first d₁ run PIVP₁, next d₂ run PIVP₂, last = product tracker
  refine ⟨(d₁ + d₂) + 1, {
    pivp := {
      field := fun v =>
        let v₁ : Fin d₁ → ℝ := fun j => v (Fin.castSucc (Fin.castAdd d₂ j))
        let v₂ : Fin d₂ → ℝ := fun j => v (Fin.castSucc (Fin.natAdd d₁ j))
        Fin.snoc (Fin.append (btc₁.pivp.field v₁) (btc₂.pivp.field v₂))
          (btc₁.pivp.field v₁ btc₁.pivp.output * v₂ btc₂.pivp.output +
           v₁ btc₁.pivp.output * btc₂.pivp.field v₂ btc₂.pivp.output)
      init := Fin.snoc (Fin.append btc₁.pivp.init btc₂.pivp.init)
          (btc₁.pivp.init btc₁.pivp.output * btc₂.pivp.init btc₂.pivp.output)
      output := Fin.last (d₁ + d₂) }
    sol := {
      trajectory := fun t =>
        Fin.snoc (Fin.append (btc₁.sol.trajectory t) (btc₂.sol.trajectory t))
          (btc₁.sol.trajectory t btc₁.pivp.output * btc₂.sol.trajectory t btc₂.pivp.output)
      init_cond := by simp only [btc₁.sol.init_cond, btc₂.sol.init_cond]
      is_solution := fun t ht => by
        have hd₁ := btc₁.sol.is_solution t ht
        have hd₂ := btc₂.sol.is_solution t ht
        rw [hasDerivAt_pi] at hd₁ hd₂ ⊢
        refine Fin.lastCases ?_ (fun j => ?_)
        · -- Product tracker: d/dt (x₁ * x₂) = x₁' * x₂ + x₁ * x₂'
          simp only [Fin.snoc_last, Fin.snoc_castSucc, Fin.append_left, Fin.append_right]
          exact (hd₁ btc₁.pivp.output).mul (hd₂ btc₂.pivp.output)
        · refine Fin.addCases (fun j₁ => ?_) (fun j₂ => ?_) j
          · simp only [Fin.snoc_castSucc, Fin.append_left]
            exact hd₁ j₁
          · simp only [Fin.snoc_castSucc, Fin.append_right]
            exact hd₂ j₂ }
    modulus := fun r => max 0 (max (btc₁.modulus (r + K)) (btc₂.modulus (r + K)))
    bounded := ?_
    convergence := ?_ }, max C₁ C₂ * (↑K + 1), by positivity, ?_⟩
  · -- Bounded
    refine ⟨M₁ * M₂ + M₁ + M₂, by positivity, fun t ht => ?_⟩
    rw [pi_norm_le_iff_of_nonneg (by positivity)]
    refine Fin.lastCases ?_ (fun j => ?_)
    · -- Product component
      simp only [Fin.snoc_last]
      rw [Real.norm_eq_abs, abs_mul]
      calc |btc₁.sol.trajectory t btc₁.pivp.output| *
            |btc₂.sol.trajectory t btc₂.pivp.output|
          ≤ M₁ * M₂ := mul_le_mul (hx₁_bound t ht) (hx₂_bound t ht)
              (abs_nonneg _) (le_of_lt hM₁)
        _ ≤ M₁ * M₂ + M₁ + M₂ := by linarith [hM₁, hM₂]
    · -- Sub-PIVP components
      refine Fin.addCases (fun j₁ => ?_) (fun j₂ => ?_) j
      · simp only [Fin.snoc_castSucc, Fin.append_left]
        calc ‖btc₁.sol.trajectory t j₁‖
            ≤ ‖btc₁.sol.trajectory t‖ := norm_le_pi_norm _ _
          _ ≤ M₁ := hb₁ t ht
          _ ≤ M₁ * M₂ + M₁ + M₂ := by nlinarith [hM₂]
      · simp only [Fin.snoc_castSucc, Fin.append_right]
        calc ‖btc₂.sol.trajectory t j₂‖
            ≤ ‖btc₂.sol.trajectory t‖ := norm_le_pi_norm _ _
          _ ≤ M₂ := hb₂ t ht
          _ ≤ M₁ * M₂ + M₁ + M₂ := by nlinarith [hM₁]
  · -- Convergence: three-term decomposition + modulus shift by K
    intro r t ht
    simp only [Fin.snoc_last]
    have ht_pos : 0 < t := lt_of_le_of_lt (le_max_left 0 _) ht
    have ht₁ : t > btc₁.modulus (r + K) :=
      lt_of_le_of_lt (le_trans (le_max_left _ _) (le_max_right 0 _)) ht
    have ht₂ : t > btc₂.modulus (r + K) :=
      lt_of_le_of_lt (le_trans (le_max_right _ _) (le_max_right 0 _)) ht
    -- Abbreviations
    set x₁ := btc₁.sol.trajectory t btc₁.pivp.output
    set x₂ := btc₂.sol.trajectory t btc₂.pivp.output
    set e_rK := Real.exp (-(↑(r + K) : ℝ))
    have hc₁ : |x₁ - α| < e_rK := btc₁.convergence (r + K) t ht₁
    have hc₂ : |x₂ - β| < e_rK := btc₂.convergence (r + K) t ht₂
    have hx₁ : |x₁| ≤ M₁ := hx₁_bound t (le_of_lt ht_pos)
    have hx₂ : |x₂| ≤ M₂ := hx₂_bound t (le_of_lt ht_pos)
    -- Triangle: x₁x₂-αβ = x₁(x₂-β)+(x₁-α)x₂-(x₁-α)(x₂-β)
    have htri : |x₁ * x₂ - α * β| ≤
        |x₁| * |x₂ - β| + |x₁ - α| * |x₂| + |x₁ - α| * |x₂ - β| := by
      have heq : x₁ * x₂ - α * β =
        (x₁ * (x₂ - β) + (x₁ - α) * x₂) + (-(x₁ - α) * (x₂ - β)) := by ring
      calc |x₁ * x₂ - α * β|
          = |(x₁ * (x₂ - β) + (x₁ - α) * x₂) + (-(x₁ - α) * (x₂ - β))| := by rw [heq]
        _ ≤ |x₁ * (x₂ - β) + (x₁ - α) * x₂| + |-(x₁ - α) * (x₂ - β)| :=
            abs_add_le _ _
        _ ≤ (|x₁ * (x₂ - β)| + |(x₁ - α) * x₂|) + |-(x₁ - α) * (x₂ - β)| := by
            linarith [abs_add_le (x₁ * (x₂ - β)) ((x₁ - α) * x₂)]
        _ = |x₁| * |x₂ - β| + |x₁ - α| * |x₂| + |x₁ - α| * |x₂ - β| := by
            simp only [abs_mul, neg_mul, abs_neg]
    -- Bound each term
    have hb1 : |x₁| * |x₂ - β| ≤ M₁ * e_rK :=
      mul_le_mul hx₁ (le_of_lt hc₂) (abs_nonneg _) (le_of_lt hM₁)
    have hb2 : |x₁ - α| * |x₂| ≤ e_rK * M₂ :=
      mul_le_mul (le_of_lt hc₁) hx₂ (abs_nonneg _) (le_of_lt (Real.exp_pos _))
    have h_le_1 : e_rK ≤ 1 := by
      calc e_rK ≤ Real.exp 0 :=
            Real.exp_le_exp.mpr (neg_nonpos.mpr (by positivity))
        _ = 1 := Real.exp_zero
    have hb3 : |x₁ - α| * |x₂ - β| ≤ e_rK := by
      calc |x₁ - α| * |x₂ - β|
          ≤ e_rK * e_rK :=
            mul_le_mul (le_of_lt hc₁) (le_of_lt hc₂) (abs_nonneg _)
              (le_of_lt (Real.exp_pos _))
        _ ≤ 1 * e_rK :=
            mul_le_mul_of_nonneg_right h_le_1 (le_of_lt (Real.exp_pos _))
        _ = e_rK := one_mul _
    -- Sum: ≤ (M₁+M₂+1)·e_rK
    have hsum : |x₁ * x₂ - α * β| ≤ (M₁ + M₂ + 1) * e_rK := by linarith
    -- Rate: (M₁+M₂+1)·e_rK < exp(-r) via e^K > M₁+M₂+1
    have hrate : (M₁ + M₂ + 1) * e_rK < Real.exp (-(↑r : ℝ)) := by
      have hfactor : e_rK = Real.exp (-(↑r : ℝ)) * Real.exp (-(↑K : ℝ)) := by
        change Real.exp (-(↑(r + K) : ℝ)) = _
        rw [show (-(↑(r + K) : ℝ)) = -(↑r : ℝ) + (-(↑K : ℝ)) from by push_cast; ring,
            Real.exp_add]
      rw [hfactor, show (M₁ + M₂ + 1) * (Real.exp (-(↑r : ℝ)) * Real.exp (-(↑K : ℝ))) =
        Real.exp (-(↑r : ℝ)) * ((M₁ + M₂ + 1) * Real.exp (-(↑K : ℝ))) from by ring]
      have hfrac : (M₁ + M₂ + 1) * Real.exp (-(↑K : ℝ)) < 1 := by
        rw [Real.exp_neg, ← div_eq_mul_inv, div_lt_one (Real.exp_pos _)]
        exact hexp_K
      calc Real.exp (-(↑r : ℝ)) * ((M₁ + M₂ + 1) * Real.exp (-(↑K : ℝ)))
          < Real.exp (-(↑r : ℝ)) * 1 :=
            mul_lt_mul_of_pos_left hfrac (Real.exp_pos _)
        _ = Real.exp (-(↑r : ℝ)) := mul_one _
    linarith
  · -- Linear modulus: max 0 (max(μ₁(r+K),μ₂(r+K))) ≤ max(C₁,C₂)·(K+1)·(r+1)
    intro r
    have hcast : (↑(r + K) : ℝ) + 1 = ↑r + ↑K + 1 := by push_cast; ring
    have h₁ : btc₁.modulus (r + K) ≤ max C₁ C₂ * (↑r + ↑K + 1) := by
      have := hmod₁ (r + K); rw [hcast] at this
      exact le_trans this (mul_le_mul_of_nonneg_right (le_max_left C₁ C₂) (by positivity))
    have h₂ : btc₂.modulus (r + K) ≤ max C₁ C₂ * (↑r + ↑K + 1) := by
      have := hmod₂ (r + K); rw [hcast] at this
      exact le_trans this (mul_le_mul_of_nonneg_right (le_max_right C₁ C₂) (by positivity))
    have h_factor : (↑r : ℝ) + ↑K + 1 ≤ (↑K + 1) * (↑r + 1) := by
      have : (↑K + 1) * (↑r + 1) = ↑K * ↑r + ↑K + ↑r + 1 := by ring
      linarith [show (0 : ℝ) ≤ ↑K * ↑r from by positivity]
    calc max 0 (max (btc₁.modulus (r + K)) (btc₂.modulus (r + K)))
        ≤ max C₁ C₂ * (↑r + ↑K + 1) := max_le (by positivity) (max_le h₁ h₂)
      _ ≤ max C₁ C₂ * ((↑K + 1) * (↑r + 1)) :=
          mul_le_mul_of_nonneg_left h_factor
            (le_of_lt (lt_of_lt_of_le hC₁ (le_max_left C₁ C₂)))
      _ = max C₁ C₂ * (↑K + 1) * (↑r + 1) := by ring

/-- Any integer (or rational with integer PIVP embedding) is real-time computable.
  Proof: constant PIVP x' = 0, x(0) = c has solution x(t) = c,
  so |x(t) - c| = 0 < e^{-r} for all t.
  Note: our PIVP definition allows real ICs; in the full theory,
  ICs must be rational ([RTCRN2] Thm 3.2.10). -/
theorem realtime_const (c : ℝ) : IsRealTimeComputable c := by
  refine ⟨1, ?_, ?_⟩
  · exact {
      pivp := { field := fun _ => ![0], init := ![c], output := 0 }
      sol := {
        trajectory := fun _ => ![c]
        init_cond := by ext i; fin_cases i; simp
        is_solution := fun t _ => by
          convert hasDerivAt_const t (![c] : Fin 1 → ℝ) using 1
          ext i; fin_cases i; simp
      }
      modulus := fun _ => 0
      bounded := ⟨|c| + 1, by positivity, fun t _ => by
        rw [pi_norm_le_iff_of_nonneg (by positivity)]
        intro i; fin_cases i
        change ‖c‖ ≤ |c| + 1
        rw [Real.norm_eq_abs]
        linarith⟩
      convergence := by
        intro r t _
        simp only [Matrix.cons_val_zero, sub_self, abs_zero]
        exact Real.exp_pos _
    }
  · exact ⟨1, one_pos, fun _ => by positivity⟩

/-- A rational constant is real-time computable by a genuinely syntactic PIVP:
the field is the zero polynomial and the initial condition is the given
rational number. This theorem avoids the semantic loophole in
`realtime_const`. -/
theorem certified_realtime_rat_const (q : ℚ) :
    IsCertifiedRealTimeComputable (q : ℝ) := by
  refine ⟨1, ?_, 1, by positivity, ?_⟩
  · exact {
      pivp := {
        field := fun _ => 0
        init := fun _ => q
        output := 0
      }
      sol := {
        trajectory := fun _ => ![(q : ℝ)]
        init_cond := by
          ext i
          fin_cases i
          simp [PolyPIVP.toPIVP]
        is_solution := fun t _ => by
          simpa [PolyPIVP.toPIVP, PolyPIVP.evalField] using
            (hasDerivAt_const t (![(q : ℝ)] : Fin 1 → ℝ))
      }
      modulus := fun _ => 0
      bounded := by
        refine ⟨|(q : ℝ)| + 1, by positivity, fun t _ => ?_⟩
        rw [pi_norm_le_iff_of_nonneg (by positivity)]
        intro i
        fin_cases i
        change ‖(q : ℝ)‖ ≤ |(q : ℝ)| + 1
        rw [Real.norm_eq_abs]
        linarith
      convergence := by
        intro r t _
        simp only [Matrix.cons_val_zero, sub_self, abs_zero]
        exact Real.exp_pos _
    }
  · intro r
    positivity

/-- A rational constant is certified CRN-computable. -/
theorem certified_crn_rat_const (q : ℚ) :
    IsCertifiedCRNComputable (q : ℝ) := by
  obtain ⟨d, btc, _, _, _⟩ := certified_realtime_rat_const q
  exact ⟨d, btc, trivial⟩

/-- Negation closure: derived from mul and const. -α = (-1) * α. -/
theorem realtime_field_neg {α : ℝ} (ha : IsRealTimeComputable α) :
    IsRealTimeComputable (-α) := by
  have : -α = (-1) * α := by ring
  rw [this]
  exact realtime_field_mul (realtime_const (-1)) ha

/-- A one-sided exponential kernel has uniformly bounded mass. -/
private theorem integral_exp_decay_le {lam T t : ℝ} (hlam : 0 < lam) :
    ∫ s in T..t, Real.exp (-lam * (t - s)) ≤ 1 / lam := by
  have hderiv :
      ∀ s ∈ Set.uIcc T t,
        HasDerivAt (fun u => (1 / lam) * Real.exp (-lam * (t - u)))
          (Real.exp (-lam * (t - s))) s := by
    intro s hs
    have hinner : HasDerivAt (fun u => -lam * (t - u)) lam s := by
      convert (((hasDerivAt_const s t).sub (hasDerivAt_id s)).const_mul (-lam)) using 1
      ring
    convert hinner.exp.const_mul (1 / lam) using 1
    field_simp [hlam.ne']
  have hint : IntervalIntegrable (fun s => Real.exp (-lam * (t - s))) MeasureTheory.volume T t := by
    apply Continuous.intervalIntegrable
    fun_prop
  have hcalc :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  calc
    ∫ s in T..t, Real.exp (-lam * (t - s))
        = (1 / lam) - (1 / lam) * Real.exp (-lam * (t - T)) := by
            simpa [hlam.ne'] using hcalc
    _ ≤ 1 / lam := by
      have hnonneg : 0 ≤ (1 / lam) * Real.exp (-lam * (t - T)) := by positivity
      linarith

private theorem integral_prefix_split
    {g G : ℝ → ℝ} (hg_cont : Continuous g)
    (hG_def : G = fun t => ∫ s in (0 : ℝ)..t, g s) :
    ∀ {s t : ℝ}, 0 ≤ s → s ≤ t → G t = G s + ∫ u in s..t, g u := by
  intro s t hs hst
  have hadd :
      (∫ u in (0 : ℝ)..s, g u) + ∫ u in s..t, g u = ∫ u in (0 : ℝ)..t, g u :=
    intervalIntegral.integral_add_adjacent_intervals
      (hg_cont.intervalIntegrable 0 s) (hg_cont.intervalIntegrable s t)
  simpa [hG_def] using hadd.symm

private theorem kernel_integral_eq_sub
    {g : ℝ → ℝ} {k : ℝ → ℝ → ℝ}
    (hg_cont : Continuous g)
    (hk_cont : ∀ t, Continuous (fun s => k t s))
    (hk_hd : ∀ t s, HasDerivAt (fun u => k t u) (g s * k t s) s) :
    ∀ {T t : ℝ}, T ≤ t → ∫ s in T..t, g s * k t s = k t t - k t T := by
  intro T t hTt
  have hderiv : ∀ s ∈ Set.uIcc T t, HasDerivAt (fun u => k t u) (g s * k t s) s := by
    intro s hs
    exact hk_hd t s
  have hint : IntervalIntegrable (fun s => g s * k t s) MeasureTheory.volume T t :=
    (hg_cont.mul (hk_cont t)).intervalIntegrable T t
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint

private theorem integrating_factor_restart
    {G x : ℝ → ℝ} {k : ℝ → ℝ → ℝ}
    (hexpG : Continuous (fun s => Real.exp (G s)))
    (hk_exp : ∀ {s t : ℝ}, 0 ≤ s → s ≤ t → Real.exp (-G t) * Real.exp (G s) = k t s)
    (hx_def : x = fun t => Real.exp (-G t) * ∫ s in (0 : ℝ)..t, Real.exp (G s)) :
    ∀ {T t : ℝ}, 0 ≤ T → T ≤ t → x t = k t T * x T + ∫ s in T..t, k t s := by
  intro T t hT0 hTt
  have hfac : Real.exp (-G t) = k t T * Real.exp (-G T) := by
    calc
      Real.exp (-G t) = Real.exp (-G t) * (Real.exp (G T) * Real.exp (-G T)) := by
            rw [show Real.exp (G T) * Real.exp (-G T) = 1 by
              rw [← Real.exp_add, add_comm, neg_add_cancel, Real.exp_zero], mul_one]
      _ = (Real.exp (-G t) * Real.exp (G T)) * Real.exp (-G T) := by
            rw [mul_assoc]
      _ = k t T * Real.exp (-G T) := by
            rw [hk_exp hT0 hTt]
  set A : ℝ := ∫ s in (0 : ℝ)..T, Real.exp (G s)
  set B : ℝ := ∫ s in T..t, Real.exp (G s)
  have hsplit0 : A + B = ∫ s in (0 : ℝ)..t, Real.exp (G s) := by
    simp [A, B]
    exact intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
      (hexpG.intervalIntegrable 0 T) (hexpG.intervalIntegrable T t)
  have htail :
      Real.exp (-G t) * B = ∫ s in T..t, k t s := by
    dsimp [B]
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro s hs
    have hsI : s ∈ Set.Icc T t := by simpa [Set.uIcc_of_le hTt] using hs
    have hs0 : 0 ≤ s := le_trans hT0 hsI.1
    have hst : s ≤ t := hsI.2
    simpa using hk_exp hs0 hst
  calc
    x t = Real.exp (-G t) * ∫ s in (0 : ℝ)..t, Real.exp (G s) := by
            rw [hx_def]
    _ = Real.exp (-G t) * (A + B) := by
            rw [← hsplit0]
    _ = Real.exp (-G t) * A + Real.exp (-G t) * B := by
            ring
    _ = Real.exp (-G t) * A + ∫ s in T..t, k t s := by
            rw [htail]
    _ = (k t T * Real.exp (-G T)) * A + ∫ s in T..t, k t s := by
            rw [hfac]
    _ = k t T * x T + ∫ s in T..t, k t s := by
            simp [hx_def, A]
            ring

private theorem kernel_from_antiderivative
    {g G : ℝ → ℝ} {k : ℝ → ℝ → ℝ}
    (hk_def : k = fun t s => Real.exp (-(∫ u in s..t, g u)))
    (hG_split : ∀ {s t : ℝ}, 0 ≤ s → s ≤ t → G t = G s + ∫ u in s..t, g u) :
    ∀ {s t : ℝ}, 0 ≤ s → s ≤ t → Real.exp (-G t) * Real.exp (G s) = k t s := by
  intro s t hs hst
  have hsplit := hG_split hs hst
  calc
    Real.exp (-G t) * Real.exp (G s)
        = (Real.exp (-G s) * Real.exp (-(∫ u in s..t, g u))) * Real.exp (G s) := by
            rw [hsplit, neg_add, Real.exp_add]
    _ = Real.exp (-(∫ u in s..t, g u)) * (Real.exp (-G s) * Real.exp (G s)) := by
            ac_rfl
    _ = Real.exp (-(∫ u in s..t, g u)) := by
            rw [show Real.exp (-G s) * Real.exp (G s) = 1 from by
              rw [← Real.exp_add, neg_add_cancel, Real.exp_zero], mul_one]
    _ = k t s := by simp [hk_def]

private theorem forcing_integral_identity
    {α T t : ℝ} (hα_ne : α ≠ 0) {a b : ℝ → ℝ}
    (hinta : IntervalIntegrable a MeasureTheory.volume T t)
    (hintb : IntervalIntegrable b MeasureTheory.volume T t) :
    (∫ s in T..t, a s) - (1 / α) * ∫ s in T..t, b s
      = (1 / α) * ∫ s in T..t, (α * a s - b s) := by
  have hintaα : IntervalIntegrable (fun s => α * a s) MeasureTheory.volume T t :=
    hinta.const_mul α
  have hconstmul : ∫ s in T..t, α * a s = α * ∫ s in T..t, a s := by
    rw [intervalIntegral.integral_const_mul]
  calc
    (∫ s in T..t, a s) - (1 / α) * ∫ s in T..t, b s
        = (1 / α) * ((∫ s in T..t, α * a s) - ∫ s in T..t, b s) := by
            rw [hconstmul]
            field_simp [hα_ne]
    _ = (1 / α) * ∫ s in T..t, (α * a s - b s) := by
            rw [← intervalIntegral.integral_sub hintaα hintb]

private theorem forcing_integral_kernel_identity
    {α T t : ℝ} (hα_ne : α ≠ 0) {g k : ℝ → ℝ}
    (hintk : IntervalIntegrable k MeasureTheory.volume T t)
    (hintgk : IntervalIntegrable (fun s => g s * k s) MeasureTheory.volume T t) :
    (∫ s in T..t, k s) - (1 / α) * ∫ s in T..t, g s * k s =
      (1 / α) * ∫ s in T..t, (α - g s) * k s := by
  have hrewrite :
      ∫ s in T..t, (α * k s - g s * k s) = ∫ s in T..t, (α - g s) * k s := by
    apply intervalIntegral.integral_congr
    intro s hs
    ring
  calc
    (∫ s in T..t, k s) - (1 / α) * ∫ s in T..t, g s * k s
        = (1 / α) * ∫ s in T..t, (α * k s - g s * k s) := by
            exact forcing_integral_identity hα_ne hintk hintgk
    _ = (1 / α) * ∫ s in T..t, (α - g s) * k s := by
            rw [hrewrite]

private theorem abs_sub_inv_le_of_nonneg_le
    {α B x : ℝ} (hα_pos : 0 < α) (hx_nonneg : 0 ≤ x) (hx_le : x ≤ B + 2 / α) :
    |x - α⁻¹| ≤ B + 3 / α := by
  have h_inv_nn : 0 ≤ α⁻¹ := le_of_lt (inv_pos.mpr hα_pos)
  calc
    |x - α⁻¹| ≤ |x| + |α⁻¹| := by
      simpa [sub_eq_add_neg, abs_neg] using (abs_add_le x (-α⁻¹))
    _ = x + α⁻¹ := by
      rw [abs_of_nonneg hx_nonneg, abs_of_nonneg h_inv_nn]
    _ ≤ B + 2 / α + α⁻¹ := by
      linarith
    _ = B + 3 / α := by
      rw [show α⁻¹ = (1 / α : ℝ) by simp]
      ring

private theorem abs_two_term_mul_le
    {a b u v : ℝ} (ha_nonneg : 0 ≤ a) (hb_nonneg : 0 ≤ b) :
    |a * u + b * v| ≤ a * |u| + b * |v| := by
  calc
    |a * u + b * v| ≤ |a * u| + |b * v| :=
      abs_add_le _ _
    _ = a * |u| + b * |v| := by
      rw [abs_mul, abs_of_nonneg ha_nonneg, abs_mul, abs_of_nonneg hb_nonneg]

private theorem exp_mul_le_exp_tail
    {A delay : ℝ} {r N : ℕ}
    (hA_le : A ≤ Real.exp (↑N : ℝ))
    (hdelay : delay > ↑r + ↑N + 1) :
    Real.exp (-delay) * A < Real.exp (-(↑(r + 1) : ℝ)) := by
  calc
    Real.exp (-delay) * A ≤ Real.exp (-delay) * Real.exp (↑N : ℝ) :=
      mul_le_mul_of_nonneg_left hA_le (le_of_lt (Real.exp_pos _))
    _ = Real.exp (-delay + ↑N) := by
      rw [← Real.exp_add]
    _ < Real.exp (-(↑(r + 1) : ℝ)) := by
      apply Real.exp_lt_exp.mpr
      have hrewrite : (-(↑(r + 1) : ℝ)) = -(↑r : ℝ) - 1 := by
        push_cast
        ring
      rw [hrewrite]
      linarith

private theorem forcing_integral_abs_bound
    {g : ℝ → ℝ} {k : ℝ → ℝ → ℝ} {α T t : ℝ} {r Ntail : ℕ}
    (hg_cont : Continuous g)
    (hk_cont : ∀ t, Continuous (fun s => k t s))
    (hclose : ∀ s, T ≤ s → |g s - α| < Real.exp (-(↑(r + Ntail + 1) : ℝ)))
    (hk_le_exp : ∀ ⦃s : ℝ⦄, s ∈ Set.Icc T t →
      k t s ≤ Real.exp (-(α / 2) * (t - s)))
    (hk_nonneg : ∀ ⦃s : ℝ⦄, s ∈ Set.Icc T t → 0 ≤ k t s)
    (hTt : T ≤ t) :
    |∫ s in T..t, (α - g s) * k t s|
      ≤ Real.exp (-(↑(r + Ntail + 1) : ℝ)) *
          ∫ s in T..t, Real.exp (-(α / 2) * (t - s)) := by
  have hint_abs :
      IntervalIntegrable (fun s => |(α - g s) * k t s|) MeasureTheory.volume T t := by
    exact ((continuous_const.sub hg_cont).mul (hk_cont t)).norm.intervalIntegrable T t
  have hint_bound :
      IntervalIntegrable
        (fun s =>
          Real.exp (-(↑(r + Ntail + 1) : ℝ)) * Real.exp (-(α / 2) * (t - s)))
        MeasureTheory.volume T t := by
    apply Continuous.intervalIntegrable
    fun_prop
  calc
    |∫ s in T..t, (α - g s) * k t s|
        ≤ ∫ s in T..t, |(α - g s) * k t s| :=
          intervalIntegral.abs_integral_le_integral_abs hTt
    _ ≤ ∫ s in T..t,
          Real.exp (-(↑(r + Ntail + 1) : ℝ)) * Real.exp (-(α / 2) * (t - s)) := by
            apply intervalIntegral.integral_mono_on hTt
            · exact hint_abs
            · exact hint_bound
            · intro s hs
              have hclose_s : |α - g s| < Real.exp (-(↑(r + Ntail + 1) : ℝ)) := by
                simpa [abs_sub_comm] using hclose s hs.1
              have hk_s := hk_le_exp hs
              have hk_nonneg_s := hk_nonneg hs
              rw [abs_mul, abs_of_nonneg hk_nonneg_s]
              exact mul_le_mul (le_of_lt hclose_s) hk_s hk_nonneg_s
                (le_of_lt (Real.exp_pos _))
    _ = Real.exp (-(↑(r + Ntail + 1) : ℝ)) *
          ∫ s in T..t, Real.exp (-(α / 2) * (t - s)) := by
            rw [← intervalIntegral.integral_const_mul]

private theorem kernel_mass_le_two_div
    {α T t : ℝ} {φ : ℝ → ℝ}
    (hα_pos : 0 < α)
    (hintφ : IntervalIntegrable φ MeasureTheory.volume T t)
    (hφ_le : ∀ s ∈ Set.Icc T t, φ s ≤ Real.exp (-(α / 2) * (t - s)))
    (hTt : T ≤ t) :
    ∫ s in T..t, φ s ≤ 2 / α := by
  have hint_expdec :
      IntervalIntegrable (fun s => Real.exp (-(α / 2) * (t - s))) MeasureTheory.volume T t := by
    apply Continuous.intervalIntegrable
    fun_prop
  calc
    ∫ s in T..t, φ s ≤ ∫ s in T..t, Real.exp (-(α / 2) * (t - s)) := by
      apply intervalIntegral.integral_mono_on hTt
      · exact hintφ
      · exact hint_expdec
      · intro s hs
        exact hφ_le s hs
    _ ≤ 1 / (α / 2) := integral_exp_decay_le (by positivity)
    _ = 2 / α := by
      field_simp [ne_of_gt hα_pos]

private theorem reciprocal_error_decomposition
    {α T t : ℝ} {x g : ℝ → ℝ} {k : ℝ → ℝ → ℝ}
    (hrestart : x t = k t T * x T + ∫ s in T..t, k t s)
    (hk_id : ∫ s in T..t, g s * k t s = 1 - k t T)
    (hcomb :
      (∫ s in T..t, k t s) - (1 / α) * ∫ s in T..t, g s * k t s =
        (1 / α) * ∫ s in T..t, (α - g s) * k t s) :
    x t - α⁻¹ =
      k t T * (x T - α⁻¹) + (1 / α) * ∫ s in T..t, (α - g s) * k t s := by
  have hconst : α⁻¹ = k t T * α⁻¹ + (1 / α) * ∫ s in T..t, g s * k t s := by
    calc
      α⁻¹ = (1 / α : ℝ) := by simp
      _ = (1 / α) * (k t T + ∫ s in T..t, g s * k t s) := by
            rw [hk_id]
            ring
      _ = k t T * α⁻¹ + (1 / α) * ∫ s in T..t, g s * k t s := by
            ring
  calc
    x t - α⁻¹
        = (k t T * x T + ∫ s in T..t, k t s) - α⁻¹ := by
            rw [hrestart]
    _ = (k t T * x T + ∫ s in T..t, k t s) -
          (k t T * α⁻¹ + (1 / α) * ∫ s in T..t, g s * k t s) := by
            simpa using congrArg
              (fun z => (k t T * x T + ∫ s in T..t, k t s) - z) hconst
    _ = k t T * (x T - α⁻¹) +
          ((∫ s in T..t, k t s) - (1 / α) * ∫ s in T..t, g s * k t s) := by
            ring
    _ = k t T * (x T - α⁻¹) + (1 / α) * ∫ s in T..t, (α - g s) * k t s := by
            rw [hcomb]

private theorem scaled_forcing_tail_le
    {α F I : ℝ} {r Ntail : ℕ}
    (hα_pos : 0 < α)
    (hforcing : F ≤ Real.exp (-(↑(r + Ntail + 1) : ℝ)) * I)
    (hI_le : I ≤ 2 / α)
    (hA2_exp : (2 / α ^ 2 : ℝ) ≤ Real.exp (↑Ntail : ℝ)) :
    (1 / α) * F ≤ Real.exp (-(↑(r + 1) : ℝ)) := by
  have hα_ne : α ≠ 0 := ne_of_gt hα_pos
  calc
    (1 / α) * F ≤ (1 / α) * (Real.exp (-(↑(r + Ntail + 1) : ℝ)) * I) :=
      mul_le_mul_of_nonneg_left hforcing (by positivity)
    _ ≤ (1 / α) * (Real.exp (-(↑(r + Ntail + 1) : ℝ)) * (2 / α)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hI_le (le_of_lt (Real.exp_pos _))) (by positivity)
    _ = (2 / α ^ 2) * Real.exp (-(↑(r + Ntail + 1) : ℝ)) := by
      field_simp [hα_ne]
    _ ≤ Real.exp (↑Ntail : ℝ) * Real.exp (-(↑(r + Ntail + 1) : ℝ)) :=
      mul_le_mul_of_nonneg_right hA2_exp (le_of_lt (Real.exp_pos _))
    _ = Real.exp (-(↑(r + 1) : ℝ)) := by
      rw [← Real.exp_add]
      congr 1
      push_cast
      ring

private theorem two_mul_exp_succ_le_exp (r : ℕ) :
    2 * Real.exp (-(↑(r + 1) : ℝ)) ≤ Real.exp (-(↑r : ℝ)) := by
  have hcast : (-(↑(r + 1) : ℝ)) = -(↑r : ℝ) + (-1 : ℝ) := by
    push_cast
    ring
  rw [hcast, Real.exp_add]
  have h2e : 2 * Real.exp (-1 : ℝ) ≤ 1 := by
    rw [Real.exp_neg, ← div_eq_mul_inv, div_le_one (Real.exp_pos 1)]
    linarith [Real.add_one_le_exp (1 : ℝ)]
  calc
    2 * (Real.exp (-(↑r : ℝ)) * Real.exp (-1))
        = Real.exp (-(↑r : ℝ)) * (2 * Real.exp (-1)) := by
            ring
    _ ≤ Real.exp (-(↑r : ℝ)) * 1 :=
          mul_le_mul_of_nonneg_left h2e (le_of_lt (Real.exp_pos _))
    _ = Real.exp (-(↑r : ℝ)) := by
          ring

private theorem add_tail_bounds_lt_exp
    {A B : ℝ} {r : ℕ}
    (hA : A < Real.exp (-(↑(r + 1) : ℝ)))
    (hB : B ≤ Real.exp (-(↑(r + 1) : ℝ))) :
    A + B < Real.exp (-(↑r : ℝ)) := by
  have hsum : A + B < 2 * Real.exp (-(↑(r + 1) : ℝ)) := by
    linarith
  exact lt_of_lt_of_le hsum (two_mul_exp_succ_le_exp r)

/-- Reciprocal closure (positive case): from [RTCRN2] Lemma 4.
  Extend a PIVP computing α > 0 with a variable x satisfying
  x' = 1 - f_out(t)·x, x(0) = 0. The integrating factor solution
  x(t) = e^{-F(t)} · ∫₀ᵗ e^{F(s)} ds converges to 1/α exponentially. -/
private theorem realtime_field_inv_pos {α : ℝ} (hα_pos : 0 < α)
    (ha : IsRealTimeComputable α) : IsRealTimeComputable α⁻¹ := by
  have hα_ne : α ≠ 0 := ne_of_gt hα_pos
  obtain ⟨d, btc, C, hC, hmod⟩ := ha
  obtain ⟨M, hM, hbound⟩ := btc.bounded
  -- f(t) = trajectory output; g = continuous extension to all of ℝ
  set f : ℝ → ℝ := fun t => btc.sol.trajectory t btc.pivp.output with hf_def
  set g : ℝ → ℝ := fun t => f (max t 0) with hg_def
  have hg_cont : Continuous g := continuous_iff_continuousAt.mpr fun t => by
    have h1 : ContinuousAt f (max t 0) :=
      ((hasDerivAt_pi.mp (btc.sol.is_solution (max t 0) (le_max_right t 0)))
        btc.pivp.output).continuousAt
    have h2 : ContinuousAt (fun s => max s (0:ℝ)) t :=
      (continuous_id.max continuous_const).continuousAt
    exact ContinuousAt.comp (g := f) (f := fun s => max s (0:ℝ)) h1 h2
  have hg_eq : ∀ t, 0 ≤ t → g t = f t := fun t ht => by simp [hg_def, max_eq_left ht]
  have hf_bound : ∀ t, 0 ≤ t → |f t| ≤ M := fun t ht => by
    have := norm_le_pi_norm (btc.sol.trajectory t) btc.pivp.output
    rw [Real.norm_eq_abs] at this; linarith [hbound t ht]
  -- G(t) = ∫₀ᵗ g(s) ds (integrating factor)
  set G : ℝ → ℝ := fun t => ∫ s in (0:ℝ)..t, g s with hG_def
  have hG_hd : ∀ t, HasDerivAt G (g t) t := fun t =>
    intervalIntegral.integral_hasDerivAt_right (hg_cont.intervalIntegrable 0 t)
      (hg_cont.stronglyMeasurableAtFilter _ _) hg_cont.continuousAt
  have hG_cont : Continuous G :=
    continuous_iff_continuousAt.mpr fun t => (hG_hd t).continuousAt
  have hexpG : Continuous (fun s => Real.exp (G s)) := Real.continuous_exp.comp hG_cont
  -- x(t) = e^{-G(t)} · ∫₀ᵗ e^{G(s)} ds (reciprocal trajectory)
  set x : ℝ → ℝ := fun t => Real.exp (-G t) * ∫ s in (0:ℝ)..t, Real.exp (G s) with hx_def
  have hx_zero : x 0 = 0 := by
    simp [hx_def, hG_def, intervalIntegral.integral_same]
  -- HasDerivAt x (1 - g(t)·x(t)) at each t
  have hx_hd : ∀ t, HasDerivAt x (1 - g t * x t) t := by
    intro t
    have h2 := (hG_hd t).neg.exp  -- d/dt exp(-G(t))
    have h3 := intervalIntegral.integral_hasDerivAt_right (hexpG.intervalIntegrable 0 t)
      (hexpG.stronglyMeasurableAtFilter _ _) hexpG.continuousAt
    have h4 := h2.mul h3
    -- Convert Pi.mul function form to x
    have hfun : (fun t => Real.exp ((-G) t)) * (fun u => ∫ s in (0:ℝ)..u, Real.exp (G s)) = x := by
      ext s; simp [hx_def, Pi.mul_apply]
    rw [hfun] at h4
    -- Now h4 : HasDerivAt x (...) t; fix derivative value
    convert h4 using 1
    simp only [hx_def, Pi.neg_apply]
    rw [show Real.exp (-G t) * Real.exp (G t) = 1 from by
      rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]]
    ring
  set Npos : ℕ := Nat.ceil (2 / α) with hNpos_def
  set T0 : ℝ := C * (↑Npos + 1) + 1 with hT0_def
  set B0 : ℝ := Real.exp (M * T0) * (T0 * Real.exp (M * T0)) with hB0_def
  set Ninit : ℕ := Nat.ceil (B0 + 3 / α) with hNinit_def
  set Ntail : ℕ := Nat.ceil (2 / α ^ 2) with hNtail_def
  have hT0_pos : 0 < T0 := by
    rw [hT0_def]
    positivity
  have hNpos_ge : (2 / α : ℝ) ≤ Npos := Nat.le_ceil _
  have hNpos_exp : Real.exp (-(↑Npos : ℝ)) ≤ α / 2 := by
    have hplus : (↑Npos : ℝ) + 1 ≤ Real.exp (↑Npos : ℝ) := by
      simpa using Real.add_one_le_exp (↑Npos : ℝ)
    have hden_pos : 0 < (↑Npos : ℝ) + 1 := by positivity
    have h_inv : (1 : ℝ) / Real.exp (↑Npos : ℝ) ≤ 1 / ((↑Npos : ℝ) + 1) :=
      one_div_le_one_div_of_le hden_pos hplus
    have h_half : 1 / ((↑Npos : ℝ) + 1) ≤ α / 2 := by
      have htmp : (2 : ℝ) ≤ α * ((↑Npos : ℝ) + 1) := by
        have hmul := hNpos_ge
        field_simp [hα_ne] at hmul
        nlinarith [hmul, hα_pos]
      field_simp [hα_ne, hden_pos.ne']
      nlinarith
    simpa [Real.exp_neg] using le_trans h_inv h_half
  have hg_lower : ∀ t, T0 ≤ t → α / 2 ≤ g t := by
    intro t ht
    have ht0 : 0 ≤ t := le_trans hT0_pos.le ht
    have ht_mod : t > btc.modulus Npos := by
      have hlin := hmod Npos
      have : C * (↑Npos + 1) < t := by
        rw [hT0_def] at ht
        linarith
      exact lt_of_le_of_lt hlin this
    rw [hg_eq t ht0]
    have hconv := btc.convergence Npos t ht_mod
    have hclose : |f t - α| < α / 2 := lt_of_lt_of_le hconv hNpos_exp
    linarith [abs_lt.mp hclose]
  have hG_split : ∀ {s t : ℝ}, 0 ≤ s → s ≤ t → G t = G s + ∫ u in s..t, g u :=
    integral_prefix_split hg_cont hG_def
  set k : ℝ → ℝ → ℝ := fun t s => Real.exp (-(∫ u in s..t, g u)) with hk_def
  have hk_hd : ∀ t s, HasDerivAt (fun u => k t u) (g s * k t s) s := by
    intro t s
    have hleft :=
      intervalIntegral.integral_hasDerivAt_left (hg_cont.intervalIntegrable s t)
        (hg_cont.stronglyMeasurableAtFilter _ _) hg_cont.continuousAt
    simpa [k, hk_def, mul_comm] using hleft.neg.exp
  have hk_cont : ∀ t, Continuous (fun s => k t s) := by
    intro t
    exact continuous_iff_continuousAt.mpr fun s => (hk_hd t s).continuousAt
  have hk_integral : ∀ {T t : ℝ}, T ≤ t → ∫ s in T..t, g s * k t s = 1 - k t T := by
    intro T t hTt
    have hcalc := kernel_integral_eq_sub hg_cont hk_cont hk_hd hTt
    simpa [k, hk_def] using hcalc
  have hk_exp : ∀ {s t : ℝ}, 0 ≤ s → s ≤ t → Real.exp (-G t) * Real.exp (G s) = k t s :=
    kernel_from_antiderivative hk_def hG_split
  have hx_restart : ∀ {T t : ℝ}, 0 ≤ T → T ≤ t →
      x t = k t T * x T + ∫ s in T..t, k t s :=
    integrating_factor_restart hexpG hk_exp hx_def
  have hx_nonneg : ∀ t, 0 ≤ t → 0 ≤ x t := by
    intro t ht
    rw [hx_def]
    apply mul_nonneg
    · exact le_of_lt (Real.exp_pos _)
    · exact intervalIntegral.integral_nonneg ht (fun s hs => le_of_lt (Real.exp_pos _))
  have hG_abs_le : ∀ t, 0 ≤ t → t ≤ T0 → |G t| ≤ M * T0 := by
    intro t ht0 htT
    rw [hG_def]
    have h_abs_mono : ∫ s in (0 : ℝ)..t, |g s| ≤ ∫ s in (0 : ℝ)..t, M := by
      apply intervalIntegral.integral_mono_on ht0
      · exact hg_cont.norm.intervalIntegrable 0 t
      · exact continuous_const.intervalIntegrable 0 t
      · intro s hs
        rw [hg_eq s hs.1]
        exact hf_bound s hs.1
    calc
      |∫ s in (0 : ℝ)..t, g s| ≤ ∫ s in (0 : ℝ)..t, |g s| :=
        intervalIntegral.abs_integral_le_integral_abs ht0
      _ ≤ ∫ s in (0 : ℝ)..t, M := h_abs_mono
      _ = M * t := by
        rw [intervalIntegral.integral_const]
        simp [smul_eq_mul, mul_comm]
      _ ≤ M * T0 := mul_le_mul_of_nonneg_left htT (le_of_lt hM)
  have hx_pre : ∀ t, 0 ≤ t → t ≤ T0 → x t ≤ B0 := by
    intro t ht0 htT
    have h_exp_le : Real.exp (-G t) ≤ Real.exp (M * T0) := by
      apply Real.exp_le_exp.mpr
      have hG := hG_abs_le t ht0 htT
      linarith [(abs_le.mp hG).1]
    have h_int_le : ∫ s in (0 : ℝ)..t, Real.exp (G s) ≤ T0 * Real.exp (M * T0) := by
      have h_exp_mono :
          ∫ s in (0 : ℝ)..t, Real.exp (G s) ≤ ∫ s in (0 : ℝ)..t, Real.exp (M * T0) := by
        apply intervalIntegral.integral_mono_on ht0
        · exact hexpG.intervalIntegrable 0 t
        · exact continuous_const.intervalIntegrable 0 t
        · intro s hs
          have hsT : s ≤ T0 := le_trans hs.2 htT
          have hG := hG_abs_le s hs.1 hsT
          apply Real.exp_le_exp.mpr
          exact (abs_le.mp hG).2
      calc
        ∫ s in (0 : ℝ)..t, Real.exp (G s) ≤ ∫ s in (0 : ℝ)..t, Real.exp (M * T0) := h_exp_mono
        _ = t * Real.exp (M * T0) := by
          rw [intervalIntegral.integral_const]
          simp [smul_eq_mul]
        _ ≤ T0 * Real.exp (M * T0) :=
          mul_le_mul_of_nonneg_right htT (le_of_lt (Real.exp_pos _))
    have h_int_nonneg : 0 ≤ ∫ s in (0 : ℝ)..t, Real.exp (G s) :=
      intervalIntegral.integral_nonneg ht0 (fun s hs => le_of_lt (Real.exp_pos _))
    rw [hx_def, hB0_def]
    exact mul_le_mul h_exp_le h_int_le h_int_nonneg (le_of_lt (Real.exp_pos _))
  have hk_le_exp :
      ∀ {T t s : ℝ}, T0 ≤ T → s ∈ Set.Icc T t →
        k t s ≤ Real.exp (-(α / 2) * (t - s)) := by
    intro T t s hT0T hs
    have hmono : ∫ u in s..t, (α / 2 : ℝ) ≤ ∫ u in s..t, g u := by
      apply intervalIntegral.integral_mono_on hs.2
      · exact continuous_const.intervalIntegrable s t
      · exact hg_cont.intervalIntegrable s t
      · intro u hu
        exact hg_lower u (le_trans hT0T (le_trans hs.1 hu.1))
    have hconst : ∫ u in s..t, (α / 2 : ℝ) = (α / 2) * (t - s) := by
      simpa [sub_eq_add_neg, mul_comm, mul_left_comm, mul_assoc] using
        (intervalIntegral.integral_const (a := s) (b := t) (c := (α / 2 : ℝ)))
    have hneg : -(∫ u in s..t, g u) ≤ -(α / 2) * (t - s) := by
      linarith
    calc
      k t s = Real.exp (-(∫ u in s..t, g u)) := by simp [k]
      _ ≤ Real.exp (-(α / 2) * (t - s)) := Real.exp_le_exp.mpr hneg
  have hx_large : ∀ t, T0 ≤ t → x t ≤ B0 + 2 / α := by
    intro t htT
    have hrestart := hx_restart hT0_pos.le htT
    have hk_int : ∫ s in T0..t, k t s ≤ 2 / α := by
      have hint_expdec : IntervalIntegrable (fun s => Real.exp (-(α / 2) * (t - s))) MeasureTheory.volume T0 t := by
        apply Continuous.intervalIntegrable
        fun_prop
      calc
        ∫ s in T0..t, k t s ≤ ∫ s in T0..t, Real.exp (-(α / 2) * (t - s)) := by
          apply intervalIntegral.integral_mono_on htT
          · exact (hk_cont t).intervalIntegrable T0 t
          · exact hint_expdec
          · intro s hs
            exact hk_le_exp (le_rfl : T0 ≤ T0) hs
        _ ≤ 1 / (α / 2) := integral_exp_decay_le (by positivity)
        _ = 2 / α := by field_simp [hα_ne]
    have hk_one : k t T0 ≤ 1 := by
      have h_int_nonneg : 0 ≤ ∫ u in T0..t, g u := by
        apply intervalIntegral.integral_nonneg htT
        intro u hu
        have hlow := hg_lower u hu.1
        linarith
      calc
        k t T0 = Real.exp (-(∫ u in T0..t, g u)) := by simp [k]
        _ ≤ Real.exp 0 := Real.exp_le_exp.mpr (by linarith)
        _ = 1 := by simp
    have hxT0 : x T0 ≤ B0 := hx_pre T0 hT0_pos.le le_rfl
    have hxT0_nonneg : 0 ≤ x T0 := hx_nonneg T0 hT0_pos.le
    have hterm1 : k t T0 * x T0 ≤ B0 := by
      calc
        k t T0 * x T0 ≤ 1 * x T0 :=
          mul_le_mul_of_nonneg_right hk_one hxT0_nonneg
        _ ≤ 1 * B0 := by simpa using hxT0
        _ = B0 := by ring
    linarith
  have hB0_nonneg : 0 ≤ B0 := by
    rw [hB0_def]
    positivity
  have hA1_exp : B0 + 3 / α ≤ Real.exp (↑Ninit : ℝ) := by
    have hceil : B0 + 3 / α ≤ Ninit := Nat.le_ceil _
    have hnat : (↑Ninit : ℝ) ≤ Real.exp (↑Ninit : ℝ) := by
      have := Real.add_one_le_exp (↑Ninit : ℝ)
      linarith
    exact le_trans hceil hnat
  have hA2_exp : (2 / α ^ 2 : ℝ) ≤ Real.exp (↑Ntail : ℝ) := by
    have hceil : (2 / α ^ 2 : ℝ) ≤ Ntail := Nat.le_ceil _
    have hnat : (↑Ntail : ℝ) ≤ Real.exp (↑Ntail : ℝ) := by
      have := Real.add_one_le_exp (↑Ntail : ℝ)
      linarith
    exact le_trans hceil hnat
  let Cinv : ℝ :=
    (C + 2 / α) +
      (T0 + (C * (↑Ntail + 2) + 1) + (2 / α) * (↑Ninit + 1))
  -- Build (d+1)-dimensional PIVP
  refine ⟨d + 1, ?_, Cinv, ?_, ?_⟩
  · refine {
    pivp := {
      field := fun v =>
        Fin.snoc (btc.pivp.field (fun j => v (Fin.castSucc j)))
          (1 - v (Fin.castSucc btc.pivp.output) * v (Fin.last d))
      init := Fin.snoc btc.pivp.init 0
      output := Fin.last d }
    sol := {
      trajectory := fun t => Fin.snoc (btc.sol.trajectory t) (x t)
      init_cond := by
        ext i; refine Fin.lastCases ?_ (fun j => ?_) i
        · simp only [Fin.snoc_last]; exact hx_zero
        · simp only [Fin.snoc_castSucc]; exact congr_fun btc.sol.init_cond j
      is_solution := fun t ht => by
        rw [hasDerivAt_pi]
        refine Fin.lastCases ?_ (fun j => ?_)
        · -- Last component: d/dt x(t) = 1 - f(t)·x(t)
          simp only [Fin.snoc_last, Fin.snoc_castSucc]
          have := hx_hd t; rw [hg_eq t ht] at this; exact this
        · -- Original PIVP components
          simp only [Fin.snoc_castSucc]
          exact (hasDerivAt_pi.mp (btc.sol.is_solution t ht)) j }
    modulus := fun r =>
      max T0 (btc.modulus (r + Ntail + 1) + 1) + (2 / α) * (↑r + ↑Ninit + 1)
    bounded := by
      refine ⟨M + (B0 + 2 / α), by positivity, fun t ht => ?_⟩
      rw [pi_norm_le_iff_of_nonneg (by positivity)]
      refine Fin.lastCases ?_ (fun j => ?_)
      · simp only [Fin.snoc_last]
        rw [Real.norm_eq_abs]
        have hx_bound : x t ≤ B0 + 2 / α := by
          by_cases hcase : t ≤ T0
          · have hx_pre' := hx_pre t ht hcase
            have htail_nonneg : 0 ≤ 2 / α := by positivity
            linarith
          · exact hx_large t (le_of_lt (lt_of_not_ge hcase))
        have hx_nn : 0 ≤ x t := hx_nonneg t ht
        rw [abs_of_nonneg hx_nn]
        have htail_nonneg : 0 ≤ M := le_of_lt hM
        linarith
      · simp only [Fin.snoc_castSucc]
        calc
          ‖btc.sol.trajectory t j‖ ≤ ‖btc.sol.trajectory t‖ := norm_le_pi_norm _ _
          _ ≤ M := hbound t ht
          _ ≤ M + (B0 + 2 / α) := by
            have htail_nonneg : 0 ≤ B0 + 2 / α := by
              positivity
            linarith
    convergence := by
      intro r t ht
      simp only [Fin.snoc_last]
      set T : ℝ := max T0 (btc.modulus (r + Ntail + 1) + 1) with hT_def
      have hT0T : T0 ≤ T := by
        rw [hT_def]
        exact le_max_left _ _
      have hT_ge0 : 0 ≤ T := le_trans hT0_pos.le hT0T
      have hTt : T ≤ t := by
        have hdelay_nonneg : 0 ≤ (2 / α) * (↑r + ↑Ninit + 1) := by positivity
        rw [hT_def] at ht
        linarith
      have hT_mod : btc.modulus (r + Ntail + 1) < T := by
        rw [hT_def]
        have : btc.modulus (r + Ntail + 1) < btc.modulus (r + Ntail + 1) + 1 := by linarith
        exact lt_of_lt_of_le this (le_max_right _ _)
      have hclose : ∀ s, T ≤ s → |g s - α| < Real.exp (-(↑(r + Ntail + 1) : ℝ)) := by
        intro s hs
        have hs0 : 0 ≤ s := le_trans hT_ge0 hs
        rw [hg_eq s hs0]
        exact btc.convergence (r + Ntail + 1) s (lt_of_lt_of_le hT_mod hs)
      have hrestart := hx_restart hT_ge0 hTt
      have hk_id := hk_integral hTt
      have hintk : IntervalIntegrable (fun s => k t s) MeasureTheory.volume T t := (hk_cont t).intervalIntegrable T t
      have hintgk : IntervalIntegrable (fun s => g s * k t s) MeasureTheory.volume T t :=
        (hg_cont.mul (hk_cont t)).intervalIntegrable T t
      have hcomb :
          (∫ s in T..t, k t s) - (1 / α) * ∫ s in T..t, g s * k t s =
            (1 / α) * ∫ s in T..t, (α - g s) * k t s := by
        exact forcing_integral_kernel_identity hα_ne hintk hintgk
      have herr :
          x t - α⁻¹ =
            k t T * (x T - α⁻¹) + (1 / α) * ∫ s in T..t, (α - g s) * k t s := by
        exact reciprocal_error_decomposition hrestart hk_id hcomb
      have herr_abs :
          |x t - α⁻¹| ≤
            k t T * |x T - α⁻¹| + (1 / α) * |∫ s in T..t, (α - g s) * k t s| := by
        have hkT_nonneg : 0 ≤ k t T := by
          have hkT_pos : 0 < k t T := by
            change 0 < Real.exp (-(∫ u in T..t, g u))
            exact Real.exp_pos _
          exact le_of_lt hkT_pos
        have hαinv_nonneg : 0 ≤ (1 / α : ℝ) := by
          positivity
        rw [herr]
        exact abs_two_term_mul_le hkT_nonneg hαinv_nonneg
      have hkT_le : k t T ≤ Real.exp (-(α / 2) * (t - T)) := by
        exact hk_le_exp hT0T ⟨le_rfl, hTt⟩
      have hxT_bound : x T ≤ B0 + 2 / α := hx_large T hT0T
      have heT_bound : |x T - α⁻¹| ≤ B0 + 3 / α := by
        exact abs_sub_inv_le_of_nonneg_le hα_pos (hx_nonneg T hT_ge0) hxT_bound
      have hdelay : (α / 2) * (t - T) > ↑r + ↑Ninit + 1 := by
        have : t - T > (2 / α) * (↑r + ↑Ninit + 1) := by
          rw [hT_def] at ht
          linarith
        have hmul :
            (α / 2) * (t - T) > (α / 2) * ((2 / α) * (↑r + ↑Ninit + 1)) :=
          mul_lt_mul_of_pos_left this (by positivity)
        have hrhs : (α / 2) * ((2 / α) * (↑r + ↑Ninit + 1)) = ↑r + ↑Ninit + 1 := by
          field_simp [hα_ne]
        rw [hrhs] at hmul
        exact hmul
      have hfirst :
          k t T * |x T - α⁻¹| < Real.exp (-(↑(r + 1) : ℝ)) := by
        have hfirst_le :
            k t T * |x T - α⁻¹| ≤ Real.exp (-(α / 2) * (t - T)) * (B0 + 3 / α) :=
          mul_le_mul hkT_le heT_bound (by positivity) (by positivity)
        have htail_exp :
            Real.exp (-(α / 2) * (t - T)) * (B0 + 3 / α) < Real.exp (-(↑(r + 1) : ℝ)) := by
          have htail_exp' :=
            exp_mul_le_exp_tail (A := B0 + 3 / α) (delay := (α / 2) * (t - T)) hA1_exp hdelay
          have hrewrite : -((α / 2) * (t - T)) = (-(α / 2) * (t - T)) := by
            ring
          exact hrewrite ▸ htail_exp'
        exact lt_of_le_of_lt hfirst_le htail_exp
      have hI_le : ∫ s in T..t, Real.exp (-(α / 2) * (t - s)) ≤ 2 / α := by
        calc
          ∫ s in T..t, Real.exp (-(α / 2) * (t - s)) ≤ 1 / (α / 2) :=
            integral_exp_decay_le (by positivity)
          _ = 2 / α := by field_simp [hα_ne]
      have hforcing :
          |∫ s in T..t, (α - g s) * k t s|
            ≤ Real.exp (-(↑(r + Ntail + 1) : ℝ)) *
                ∫ s in T..t, Real.exp (-(α / 2) * (t - s)) := by
        exact forcing_integral_abs_bound hg_cont hk_cont hclose
          (fun {s} hs => hk_le_exp hT0T hs)
          (fun {s} hs => by
            have hk_pos : 0 < k t s := by
              change 0 < Real.exp (-(∫ u in s..t, g u))
              exact Real.exp_pos _
            exact le_of_lt hk_pos)
          hTt
      have hsecond :
          (1 / α) * |∫ s in T..t, (α - g s) * k t s|
            ≤ Real.exp (-(↑(r + 1) : ℝ)) := by
        exact scaled_forcing_tail_le hα_pos hforcing hI_le hA2_exp
      calc
        |x t - α⁻¹|
            ≤ k t T * |x T - α⁻¹| + (1 / α) * |∫ s in T..t, (α - g s) * k t s| := herr_abs
        _ < Real.exp (-(↑r : ℝ)) := add_tail_bounds_lt_exp hfirst hsecond
    }
  · dsimp [Cinv]
    positivity
  · intro r
    have htail_mod : btc.modulus (r + Ntail + 1) + 1 ≤ C * (↑r + ↑Ntail + 2) + 1 := by
      have hlin := hmod (r + Ntail + 1)
      calc
        btc.modulus (r + Ntail + 1) + 1 ≤ C * ((↑(r + Ntail + 1) : ℝ) + 1) + 1 := by
          linarith
        _ = C * (↑r + ↑Ntail + 2) + 1 := by
          push_cast
          ring
    calc
      max T0 (btc.modulus (r + Ntail + 1) + 1) + (2 / α) * (↑r + ↑Ninit + 1)
          ≤ (T0 + (C * (↑r + ↑Ntail + 2) + 1)) + (2 / α) * (↑r + ↑Ninit + 1) := by
              have htail_nonneg : 0 ≤ C * (↑r + ↑Ntail + 2) + 1 := by
                have hr_nonneg : 0 ≤ (↑r : ℝ) := Nat.cast_nonneg r
                have hNtail_nonneg : 0 ≤ (↑Ntail : ℝ) := Nat.cast_nonneg Ntail
                nlinarith [hC, hr_nonneg, hNtail_nonneg]
              have hmax :
                  max T0 (btc.modulus (r + Ntail + 1) + 1) ≤ T0 + (C * (↑r + ↑Ntail + 2) + 1) := by
                apply max_le
                · exact le_add_of_nonneg_right htail_nonneg
                · exact le_trans htail_mod (le_add_of_nonneg_left hT0_pos.le)
              linarith
      _ = (C + 2 / α) * ↑r +
            (T0 + (C * (↑Ntail + 2) + 1) + (2 / α) * (↑Ninit + 1)) := by
            ring
      _ ≤ Cinv * (↑r + 1) := by
            have hr_nonneg : 0 ≤ (↑r : ℝ) := Nat.cast_nonneg r
            have hK_nonneg : 0 ≤ T0 + (C * (↑Ntail + 2) + 1) + (2 / α) * (↑Ninit + 1) := by
              have hterm1 : 0 ≤ T0 := hT0_pos.le
              have hterm2 : 0 ≤ C * (↑Ntail + 2) + 1 := by
                have hmul_nonneg : 0 ≤ C * (↑Ntail + 2 : ℝ) := by
                  positivity
                linarith
              have hterm3 : 0 ≤ (2 / α) * (↑Ninit + 1) := by
                positivity
              linarith
            have hrest_nonneg :
                0 ≤ (C + 2 / α) + (T0 + (C * (↑Ntail + 2) + 1) + (2 / α) * (↑Ninit + 1)) * ↑r := by
              have hA_nonneg : 0 ≤ C + 2 / α := by
                positivity
              nlinarith
            calc
              (C + 2 / α) * ↑r + (T0 + (C * (↑Ntail + 2) + 1) + (2 / α) * (↑Ninit + 1))
                  ≤ (C + 2 / α) * ↑r +
                      (T0 + (C * (↑Ntail + 2) + 1) + (2 / α) * (↑Ninit + 1)) +
                      ((C + 2 / α) +
                        (T0 + (C * (↑Ntail + 2) + 1) + (2 / α) * (↑Ninit + 1)) * ↑r) := by
                    linarith
              _ = Cinv * (↑r + 1) := by
                    dsimp [Cinv]
                    ring

/-- Reciprocal closure for real-time computable numbers.
  When α ≠ 0 and α ∈ ℝ_RTCRN, then α⁻¹ ∈ ℝ_RTCRN.
  For α > 0: extend PIVP with x' = 1 - f(t)·x (integrating factor).
  For α < 0: reduce via 1/α = -(1/(-α)). -/
theorem realtime_field_inv {α : ℝ} (hα : α ≠ 0)
    (ha : IsRealTimeComputable α) : IsRealTimeComputable α⁻¹ := by
  by_cases hpos : 0 < α
  · exact realtime_field_inv_pos hpos ha
  · push Not at hpos
    have hneg : α < 0 := lt_of_le_of_ne hpos hα
    have h1 := realtime_field_inv_pos (neg_pos.mpr hneg) (realtime_field_neg ha)
    convert realtime_field_neg h1 using 1
    rw [inv_neg, neg_neg]

/-- Division closure: α / β = α · β⁻¹. -/
theorem realtime_field_div {α β : ℝ} (hβ : β ≠ 0)
    (ha : IsRealTimeComputable α) (hb : IsRealTimeComputable β) :
    IsRealTimeComputable (α / β) := by
  rw [div_eq_mul_inv]
  exact realtime_field_mul ha (realtime_field_inv hβ hb)

/-- Subtraction closure: derived from add and neg. -/
theorem realtime_field_sub {α β : ℝ} (ha : IsRealTimeComputable α)
    (hb : IsRealTimeComputable β) : IsRealTimeComputable (α - β) := by
  have : α - β = α + (-β) := sub_eq_add_neg α β
  rw [this]
  exact realtime_field_add ha (realtime_field_neg hb)

end Ripple
