/-
  Ripple.LPP.AddRationalPos — RTCRN1 Lemma 4.3, strictly positive q case

  Discharges `certified_add_rational_pos` (previously an axiom in
  `Ripple.LPP.AlgebraicConstruction`) by factoring into:

  1. **Structural extension (proved here).** Given a CertifiedBoundedTimeComputable
     witness for `β` with PolyCRNDecomposition, build a `d+1`-dimensional
     extended `PolyPIVP` where a new "relaxation tracker" species `y` obeys
     `y' = k·x_out + k·q − k·y` (with `k := 1` for the rate constant, just a
     convenient fixed positive rational). Lift the original polynomials via
     `MvPolynomial.rename Fin.castSucc` and `Fin.snoc` the new field for `y`.

  2. **Analytic content (narrow residual axiom).** The convergence of the
     extended trajectory to `β + q` with time modulus
       μ'(r) := μ(r+1) + (r + 1 + log(max(2β, 1))) · log(2)⁻¹
     under the linear relaxation ODE. This is the content Mathlib does not
     yet provide in a directly usable form; the underlying derivation is
       |y(t) − (β + q)| ≤ |y(0) − β − q| · e^{−t} + ∫₀^t e^{−(t−s)} |x_out(s) − β| ds.

  The residual axiom `relaxation_tracker_solution` is structural (existence
  of a solution trajectory with the stated bounds), scoped to the
  `relaxationPIVP` construction defined here. It replaces the monolithic
  `certified_add_rational_pos` axiom.
-/

import Ripple.Core.BoundedTime
import Ripple.LPP.Defs
import Mathlib.Algebra.MvPolynomial.Rename
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.Deriv.Mul

namespace Ripple
namespace Algebraic

open MvPolynomial

/-! ## Step 1: lift an original `PolyPIVP d` to a `PolyPIVP (d+1)`.

We extend along `Fin.castSucc : Fin d ↪ Fin (d+1)` so that:
- original species `i : Fin d` sits at `i.castSucc`;
- new species `y` sits at `Fin.last d`.
-/

/-- Rename the field polynomials along `Fin.castSucc`. -/
noncomputable def liftField {d : ℕ} (P : PolyPIVP d) :
    Fin d → MvPolynomial (Fin (d+1)) ℚ :=
  fun i => rename Fin.castSucc (P.field i)

/-- Rename the production polynomials along `Fin.castSucc`. -/
noncomputable def liftProd {d : ℕ} {P : PolyPIVP d}
    (pcd : PolyCRNDecomposition d P) :
    Fin d → MvPolynomial (Fin (d+1)) ℚ :=
  fun i => rename Fin.castSucc (pcd.prod i)

/-- Rename the degradation polynomials along `Fin.castSucc`. -/
noncomputable def liftDegr {d : ℕ} {P : PolyPIVP d}
    (pcd : PolyCRNDecomposition d P) :
    Fin d → MvPolynomial (Fin (d+1)) ℚ :=
  fun i => rename Fin.castSucc (pcd.degr i)

/-- Non-negativity of coefficients is preserved by `rename` along injections. -/
lemma coeff_rename_castSucc_nonneg {d : ℕ} (p : MvPolynomial (Fin d) ℚ)
    (hp : ∀ σ, 0 ≤ p.coeff σ) :
    ∀ σ, 0 ≤ (rename (Fin.castSucc (n := d)) p).coeff σ := by
  classical
  intro σ
  by_cases h : ∃ u : Fin d →₀ ℕ, u.mapDomain Fin.castSucc = σ
  · obtain ⟨u, hu⟩ := h
    subst hu
    rw [coeff_rename_mapDomain Fin.castSucc (Fin.castSucc_injective d)]
    exact hp u
  · rw [coeff_rename_eq_zero Fin.castSucc p σ (by
      intro u hu; exact absurd ⟨u, hu⟩ h)]

/-! ## Step 2: the relaxation tracker field for the new species `y`.

We use rate constant `k := 1` (a rational, positive), so:
- `field_y := X_out + q · 1 - X_y` (where X_out is the lifted output)
- `prod_y  := X_out + q · 1`
- `degr_y  := 1`
-/

/-- Production polynomial for the tracker species `y` = `X_out + q`. -/
noncomputable def trackerProd {d : ℕ} (P : PolyPIVP d) (q : ℚ) :
    MvPolynomial (Fin (d+1)) ℚ :=
  X (Fin.castSucc P.output) + C q

/-- Degradation polynomial for the tracker species `y` = `1`. -/
noncomputable def trackerDegr (d : ℕ) : MvPolynomial (Fin (d+1)) ℚ :=
  1

/-- Field polynomial for the tracker species `y` = `X_out + q − X_y`. -/
noncomputable def trackerField {d : ℕ} (P : PolyPIVP d) (q : ℚ) :
    MvPolynomial (Fin (d+1)) ℚ :=
  trackerProd P q - trackerDegr d * X (Fin.last d)

/-- Coefficients of `trackerProd P q = X_out + q` are non-negative when `0 ≤ q`. -/
lemma trackerProd_coeff_nonneg {d : ℕ} (P : PolyPIVP d) (q : ℚ) (hq : 0 ≤ q) :
    ∀ σ, 0 ≤ (trackerProd P q).coeff σ := by
  classical
  intro σ
  unfold trackerProd
  rw [MvPolynomial.coeff_add]
  have h1 : 0 ≤ (X (Fin.castSucc P.output) :
      MvPolynomial (Fin (d+1)) ℚ).coeff σ := by
    rw [MvPolynomial.coeff_X']
    split_ifs <;> norm_num
  have h2 : 0 ≤ (C q : MvPolynomial (Fin (d+1)) ℚ).coeff σ := by
    rw [MvPolynomial.coeff_C]
    split_ifs
    · exact hq
    · exact le_refl _
  linarith

/-- Coefficients of `trackerDegr d = 1` are non-negative. -/
lemma trackerDegr_coeff_nonneg (d : ℕ) :
    ∀ σ, 0 ≤ (trackerDegr d).coeff σ := by
  classical
  intro σ
  unfold trackerDegr
  rw [show (1 : MvPolynomial (Fin (d+1)) ℚ) = C 1 from (map_one _).symm,
      MvPolynomial.coeff_C]
  split_ifs
  · norm_num
  · exact le_refl _

/-! ## Step 3: build the extended `PolyPIVP (d+1)` via `Fin.snoc`. -/

/-- The extended polynomial IVP: original species lifted, plus a tracker `y`. -/
noncomputable def relaxationPIVP {d : ℕ} (P : PolyPIVP d) (q : ℚ) :
    PolyPIVP (d+1) where
  field := Fin.snoc (liftField P) (trackerField P q)
  init := Fin.snoc (fun i => P.init i) q
  output := Fin.last d

@[simp] lemma relaxationPIVP_output {d : ℕ} (P : PolyPIVP d) (q : ℚ) :
    (relaxationPIVP P q).output = Fin.last d := rfl

@[simp] lemma relaxationPIVP_field_castSucc {d : ℕ} (P : PolyPIVP d) (q : ℚ)
    (i : Fin d) :
    (relaxationPIVP P q).field i.castSucc = rename Fin.castSucc (P.field i) := by
  unfold relaxationPIVP
  simp [liftField, Fin.snoc_castSucc]

@[simp] lemma relaxationPIVP_field_last {d : ℕ} (P : PolyPIVP d) (q : ℚ) :
    (relaxationPIVP P q).field (Fin.last d) = trackerField P q := by
  unfold relaxationPIVP
  simp [Fin.snoc_last]

@[simp] lemma relaxationPIVP_init_castSucc {d : ℕ} (P : PolyPIVP d) (q : ℚ)
    (i : Fin d) :
    (relaxationPIVP P q).init i.castSucc = P.init i := by
  unfold relaxationPIVP
  simp [Fin.snoc_castSucc]

@[simp] lemma relaxationPIVP_init_last {d : ℕ} (P : PolyPIVP d) (q : ℚ) :
    (relaxationPIVP P q).init (Fin.last d) = q := by
  unfold relaxationPIVP
  simp [Fin.snoc_last]

/-! ## Step 4: the PolyCRNDecomposition of the extended system. -/

/-- The extended system admits a `PolyCRNDecomposition` when the original does
and `q ≥ 0`. Non-negativity of coefficients is preserved by `rename` (for the
original block) and holds by construction for the tracker row. -/
noncomputable def relaxationPIVP_polyCRN {d : ℕ} {P : PolyPIVP d} (q : ℚ)
    (hq : 0 ≤ q) (pcd : PolyCRNDecomposition d P) :
    PolyCRNDecomposition (d+1) (relaxationPIVP P q) where
  prod := Fin.snoc (liftProd pcd) (trackerProd P q)
  degr := Fin.snoc (liftDegr pcd) (trackerDegr d)
  prod_nonneg := by
    intro i σ
    refine Fin.lastCases ?_ (fun i' => ?_) i
    · rw [Fin.snoc_last]
      exact trackerProd_coeff_nonneg P q hq σ
    · rw [Fin.snoc_castSucc]
      exact coeff_rename_castSucc_nonneg (pcd.prod i') (pcd.prod_nonneg i') σ
  degr_nonneg := by
    intro i σ
    refine Fin.lastCases ?_ (fun i' => ?_) i
    · rw [Fin.snoc_last]
      exact trackerDegr_coeff_nonneg d σ
    · rw [Fin.snoc_castSucc]
      exact coeff_rename_castSucc_nonneg (pcd.degr i') (pcd.degr_nonneg i') σ
  init_nonneg := by
    intro i
    refine Fin.lastCases ?_ (fun i' => ?_) i
    · rw [relaxationPIVP_init_last]
      exact_mod_cast hq
    · rw [relaxationPIVP_init_castSucc]
      exact_mod_cast pcd.init_nonneg i'
  field_eq := by
    intro i
    refine Fin.lastCases ?_ (fun i' => ?_) i
    · -- last: field = trackerField = trackerProd - trackerDegr * X_y
      rw [relaxationPIVP_field_last, Fin.snoc_last, Fin.snoc_last]
      rfl
    · -- castSucc: field = rename (P.field i') = rename(prod i') - rename(degr i') * X_{i'.castSucc}
      rw [relaxationPIVP_field_castSucc, Fin.snoc_castSucc, Fin.snoc_castSucc]
      unfold liftProd liftDegr
      rw [pcd.field_eq i']
      rw [map_sub, map_mul, rename_X]

/-! ## Step 5: explicit Duhamel trajectory for the tracker species.

The extended `PolyPIVP` has, at the tracker coordinate `Fin.last d`, the scalar
linear inhomogeneous ODE
  y'(t) = x_out(t) + q − y(t),   y(0) = q
where `x_out(t) := cbtc.sol.trajectory t cbtc.pivp.output` is the original
output species' trajectory. The Duhamel/variation-of-constants formula gives
the explicit solution
  y(t) = e^{−t} · q + ∫₀^t e^{−(t−s)} · (x_out(s) + q) ds
       = q + ∫₀^t e^{−(t−s)} · x_out(s) ds           (since e^{−t}·q + q(1−e^{−t}) = q).

We build the combined (d+1)-dim trajectory by `Fin.snoc`, inheriting the first
`d` coordinates from `cbtc.sol` and using the integral formula for the last.

The convergence / boundedness analysis of this tracker is the remaining analytic
content; see `relaxation_tracker_solution` below (narrow residual axiom).
-/

/-- The output trajectory of the original BTC, as a function of time, extended
continuously to `t < 0` by freezing at the value at `t = 0`. This makes the
integrand `e^s · outTraj(s)` continuous on all of ℝ, which is needed for a
clean two-sided FTC at `t = 0`.

For `t ≥ 0`, `outTraj t = cbtc.sol.trajectory t cbtc.pivp.output` agrees with
the natural trajectory. For `t < 0`, `outTraj t = cbtc.sol.trajectory 0
cbtc.pivp.output = (cbtc.pivp.init cbtc.pivp.output : ℝ)` is just a constant
— chosen so that the combined function is continuous at 0. -/
noncomputable def outTraj {d : ℕ} {β : ℝ}
    (cbtc : CertifiedBoundedTimeComputable d β) : ℝ → ℝ :=
  fun t => cbtc.sol.trajectory (max 0 t) cbtc.pivp.output

@[simp] lemma outTraj_of_nonneg {d : ℕ} {β : ℝ}
    (cbtc : CertifiedBoundedTimeComputable d β) {t : ℝ} (ht : 0 ≤ t) :
    outTraj cbtc t = cbtc.sol.trajectory t cbtc.pivp.output := by
  unfold outTraj; rw [max_eq_right ht]

/-- The inner (unweighted) Duhamel integral `F(t) := ∫₀^t e^s · x_out(s) ds`,
so that `y(t) = q + e^{−t} · F(t)`. This reformulation pulls the time-dependent
factor `e^{−t}` outside the integral, avoiding Leibniz differentiation under
the integral sign. -/
noncomputable def trackerIntegral {d : ℕ} {β : ℝ}
    (cbtc : CertifiedBoundedTimeComputable d β) : ℝ → ℝ :=
  fun t => ∫ s in (0 : ℝ)..t, Real.exp s * outTraj cbtc s

/-- The tracker trajectory, defined by the Duhamel variation-of-constants
formula:
  y(t) = q + ∫₀^t e^{−(t−s)} · x_out(s) ds = q + e^{−t} · F(t)
where `F(t) = ∫₀^t e^s · x_out(s) ds = trackerIntegral cbtc t`. -/
noncomputable def trackerTraj {d : ℕ} {β : ℝ}
    (cbtc : CertifiedBoundedTimeComputable d β) (q : ℚ) : ℝ → ℝ :=
  fun t => (q : ℝ) + Real.exp (-t) * trackerIntegral cbtc t

/-- The full extended trajectory on `Fin (d+1)`: the first `d` coordinates are
inherited from `cbtc.sol.trajectory` (via `Fin.castSucc` decoding), and the
last coordinate is `trackerTraj`. -/
noncomputable def extendedTraj {d : ℕ} {β : ℝ}
    (cbtc : CertifiedBoundedTimeComputable d β) (q : ℚ) :
    ℝ → Fin (d+1) → ℝ :=
  fun t => Fin.snoc (fun i : Fin d => cbtc.sol.trajectory t i)
                     (trackerTraj cbtc q t)

@[simp] lemma extendedTraj_castSucc {d : ℕ} {β : ℝ}
    (cbtc : CertifiedBoundedTimeComputable d β) (q : ℚ) (t : ℝ) (i : Fin d) :
    extendedTraj cbtc q t i.castSucc = cbtc.sol.trajectory t i := by
  unfold extendedTraj
  simp [Fin.snoc_castSucc]

@[simp] lemma extendedTraj_last {d : ℕ} {β : ℝ}
    (cbtc : CertifiedBoundedTimeComputable d β) (q : ℚ) (t : ℝ) :
    extendedTraj cbtc q t (Fin.last d) = trackerTraj cbtc q t := by
  unfold extendedTraj
  simp [Fin.snoc_last]

/-- At `t = 0`, the Duhamel integral vanishes: `trackerIntegral cbtc 0 = 0`. -/
@[simp] lemma trackerIntegral_zero {d : ℕ} {β : ℝ}
    (cbtc : CertifiedBoundedTimeComputable d β) :
    trackerIntegral cbtc 0 = 0 := by
  unfold trackerIntegral
  simp

/-- At `t = 0`, `trackerTraj cbtc q 0 = q`. -/
lemma trackerTraj_zero {d : ℕ} {β : ℝ}
    (cbtc : CertifiedBoundedTimeComputable d β) (q : ℚ) :
    trackerTraj cbtc q 0 = (q : ℝ) := by
  unfold trackerTraj
  simp

/-- The initial condition of the extended trajectory matches the extended
PIVP's `init` vector. -/
lemma extendedTraj_init {d : ℕ} {β : ℝ}
    (cbtc : CertifiedBoundedTimeComputable d β) (q : ℚ) :
    extendedTraj cbtc q 0 = (relaxationPIVP cbtc.pivp q).toPIVP.init := by
  funext k
  refine Fin.lastCases ?_ (fun i => ?_) k
  · -- last coord
    rw [extendedTraj_last, trackerTraj_zero]
    show (q : ℝ) = ((relaxationPIVP cbtc.pivp q).init (Fin.last d) : ℝ)
    rw [relaxationPIVP_init_last]
  · -- castSucc coord
    rw [extendedTraj_castSucc]
    show cbtc.sol.trajectory 0 i = ((relaxationPIVP cbtc.pivp q).init i.castSucc : ℝ)
    rw [relaxationPIVP_init_castSucc]
    have := congrFun cbtc.sol.init_cond i
    rw [this]
    rfl

/-- `outTraj` (extended by freezing at `t = 0` for `t < 0`) is continuous on
all of ℝ. -/
lemma outTraj_continuous {d : ℕ} {β : ℝ}
    (cbtc : CertifiedBoundedTimeComputable d β) :
    Continuous (outTraj cbtc) := by
  -- Write outTraj(t) = (cbtc.sol.trajectory · cbtc.pivp.output) ∘ (max 0)
  unfold outTraj
  -- max 0 is continuous; the inner composition with the continuous trajectory.
  have hmax : Continuous (fun t : ℝ => max 0 t) := continuous_const.max continuous_id
  -- Trajectory composed with projection at `cbtc.pivp.output`, restricted to [0,∞),
  -- is continuous. For the composition `cbtc.sol.trajectory (max 0 t) cbtc.pivp.output`
  -- we need continuity of `s ↦ cbtc.sol.trajectory s cbtc.pivp.output` on the range
  -- of `max 0 _`, which is `[0,∞)`.
  -- Use `Continuous.comp` on the restricted-to-[0,∞)-and-extended trajectory.
  -- Concretely: define g s := cbtc.sol.trajectory s cbtc.pivp.output. `g` is continuous
  -- on [0, ∞) (each point t ≥ 0 has a HasDerivAt from is_solution, giving ContinuousAt).
  -- The image of `max 0` lies in [0, ∞), so `g ∘ (max 0)` is continuous as a composition
  -- on the subspace.
  have hg_contOn : ContinuousOn (fun s => cbtc.sol.trajectory s cbtc.pivp.output)
      (Set.Ici (0 : ℝ)) := by
    intro s hs
    have h := (hasDerivAt_pi.mp (cbtc.sol.is_solution s hs)) cbtc.pivp.output
    exact h.continuousAt.continuousWithinAt
  -- Image of max 0 is contained in Ici 0.
  have hmax_mem : ∀ t : ℝ, (max 0 t) ∈ Set.Ici (0 : ℝ) := fun t => le_max_left 0 t
  exact hg_contOn.comp_continuous hmax hmax_mem

/-- The integrand `s ↦ e^s · x_out(s)` is continuous on all of ℝ. -/
lemma trackerIntegrand_continuous {d : ℕ} {β : ℝ}
    (cbtc : CertifiedBoundedTimeComputable d β) :
    Continuous (fun s => Real.exp s * outTraj cbtc s) := by
  exact Real.continuous_exp.mul (outTraj_continuous cbtc)

/-- Pointwise version: `s ↦ e^s · x_out(s)` is continuous at every `s`. -/
lemma trackerIntegrand_continuousAt {d : ℕ} {β : ℝ}
    (cbtc : CertifiedBoundedTimeComputable d β) (s : ℝ) :
    ContinuousAt (fun u => Real.exp u * outTraj cbtc u) s :=
  (trackerIntegrand_continuous cbtc).continuousAt

/-- Interval-integrability of the inner Duhamel integrand on any `[a, b]`. -/
lemma trackerIntegrand_intervalIntegrable {d : ℕ} {β : ℝ}
    (cbtc : CertifiedBoundedTimeComputable d β) (a b : ℝ) :
    IntervalIntegrable (fun s => Real.exp s * outTraj cbtc s) MeasureTheory.volume a b :=
  (trackerIntegrand_continuous cbtc).intervalIntegrable a b

/-- **Two-sided FTC for the inner integral**: the inner integral has a
full `HasDerivAt` at every `t ∈ ℝ`. The extended `outTraj` is continuous
on all of ℝ, so the integrand is continuous everywhere, and FTC-1 applies. -/
lemma trackerIntegral_hasDerivAt {d : ℕ} {β : ℝ}
    (cbtc : CertifiedBoundedTimeComputable d β) (t : ℝ) :
    HasDerivAt (trackerIntegral cbtc) (Real.exp t * outTraj cbtc t) t := by
  unfold trackerIntegral
  have hint : IntervalIntegrable (fun s => Real.exp s * outTraj cbtc s)
      MeasureTheory.volume 0 t :=
    trackerIntegrand_intervalIntegrable cbtc 0 t
  have hmeas : StronglyMeasurableAtFilter
      (fun s => Real.exp s * outTraj cbtc s) (nhds t) MeasureTheory.volume :=
    (trackerIntegrand_continuous cbtc).stronglyMeasurableAtFilter _ _
  have hcontAt : ContinuousAt (fun s => Real.exp s * outTraj cbtc s) t :=
    trackerIntegrand_continuousAt cbtc t
  exact intervalIntegral.integral_hasDerivAt_right hint hmeas hcontAt

/-! ## Step 5b: per-coordinate uniform bound on the original trajectory. -/

/-- Per-coordinate uniform bound on `cbtc.sol.trajectory`, from the `IsBounded`
witness. Analogous to `BoundedTimeComputable.coord_bound` but at the semantic
`PolyPIVP` layer. -/
lemma cbtc_coord_bound {d : ℕ} {β : ℝ}
    (cbtc : CertifiedBoundedTimeComputable d β) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ t, 0 ≤ t → ∀ j : Fin d,
      |cbtc.sol.trajectory t j| ≤ M := by
  obtain ⟨M, hMpos, hM⟩ := cbtc.bounded
  refine ⟨M, hMpos.le, fun t ht j => ?_⟩
  have h1 : ‖cbtc.sol.trajectory t j‖ ≤ ‖cbtc.sol.trajectory t‖ :=
    norm_le_pi_norm _ _
  have h2 : ‖cbtc.sol.trajectory t‖ ≤ M := hM t ht
  rw [Real.norm_eq_abs] at h1
  linarith

/-- Uniform bound on `outTraj` on all of ℝ: the extension via `max 0 t`
only takes values at `t ≥ 0`, so the same bound applies. -/
lemma outTraj_bound {d : ℕ} {β : ℝ}
    (cbtc : CertifiedBoundedTimeComputable d β) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ t, |outTraj cbtc t| ≤ M := by
  obtain ⟨M, hM_nn, hM⟩ := cbtc_coord_bound cbtc
  refine ⟨M, hM_nn, fun t => ?_⟩
  unfold outTraj
  exact hM (max 0 t) (le_max_left _ _) cbtc.pivp.output

/-- The derivative of `trackerTraj cbtc q` at any `t : ℝ` matches the field:
`y'(t) = x_out(t) + q - y(t)`. Obtained by writing
`y(t) = q + e^{-t}·F(t)` and applying the product rule with
`(e^{-t})' = -e^{-t}` and `F'(t) = e^t · x_out(t)` (on the continuous
extension of `outTraj` to all of ℝ). -/
lemma trackerTraj_hasDerivAt {d : ℕ} {β : ℝ}
    (cbtc : CertifiedBoundedTimeComputable d β) (q : ℚ) (t : ℝ) :
    HasDerivAt (trackerTraj cbtc q)
      (outTraj cbtc t + (q : ℝ) - trackerTraj cbtc q t) t := by
  unfold trackerTraj
  have hF := trackerIntegral_hasDerivAt cbtc t
  -- derivative of `e^{-t}`: `-e^{-t}`.
  have hExpNeg : HasDerivAt (fun s : ℝ => Real.exp (-s)) (-Real.exp (-t)) t := by
    have h1 : HasDerivAt (fun s : ℝ => -s) (-1) t := (hasDerivAt_id t).neg
    have h2 : HasDerivAt (fun s : ℝ => Real.exp (-s)) (Real.exp (-t) * (-1)) t := h1.exp
    convert h2 using 1; ring
  -- Product rule: `(e^{-t} · F(t))' = -e^{-t}·F(t) + e^{-t}·(e^t · x_out(t))`
  --             = -e^{-t}·F(t) + x_out(t)`.
  have hProd : HasDerivAt (fun s => Real.exp (-s) * trackerIntegral cbtc s)
      (-Real.exp (-t) * trackerIntegral cbtc t +
        Real.exp (-t) * (Real.exp t * outTraj cbtc t)) t :=
    hExpNeg.mul hF
  -- Simplify: e^{-t} * e^t = 1, so second summand = x_out(t).
  have hSimp : -Real.exp (-t) * trackerIntegral cbtc t +
        Real.exp (-t) * (Real.exp t * outTraj cbtc t) =
      outTraj cbtc t - Real.exp (-t) * trackerIntegral cbtc t := by
    have hExpCancel : Real.exp (-t) * Real.exp t = 1 := by
      rw [← Real.exp_add]; simp
    calc -Real.exp (-t) * trackerIntegral cbtc t +
          Real.exp (-t) * (Real.exp t * outTraj cbtc t)
        = -Real.exp (-t) * trackerIntegral cbtc t +
            (Real.exp (-t) * Real.exp t) * outTraj cbtc t := by ring
      _ = -Real.exp (-t) * trackerIntegral cbtc t + 1 * outTraj cbtc t := by
            rw [hExpCancel]
      _ = outTraj cbtc t - Real.exp (-t) * trackerIntegral cbtc t := by ring
  -- Now add the constant q.
  have hFull : HasDerivAt (fun s => (q : ℝ) + Real.exp (-s) * trackerIntegral cbtc s)
      (outTraj cbtc t - Real.exp (-t) * trackerIntegral cbtc t) t := by
    have := (hasDerivAt_const t (q : ℝ)).add hProd
    convert this using 1
    rw [hSimp]; ring
  -- Rewrite RHS into the target form: `x_out(t) + q - y(t) = x_out(t) - e^{-t}·F(t)`
  -- because `y(t) - q = e^{-t}·F(t)`, so `x_out(t) + q - y(t) = x_out(t) - e^{-t}·F(t)`.
  convert hFull using 1
  show outTraj cbtc t + (q : ℝ) - ((q : ℝ) + Real.exp (-t) * trackerIntegral cbtc t) =
    outTraj cbtc t - Real.exp (-t) * trackerIntegral cbtc t
  ring

/-- Uniform bound on the tracker trajectory on `[0, ∞)`.

Using `y(t) = q + ∫₀^t e^{−(t−s)} · x_out(s) ds` and `|x_out| ≤ M`:
  `|y(t) − q| = |∫₀^t e^{−(t−s)} · x_out(s) ds|`
             `≤ M · ∫₀^t e^{−(t−s)} ds`
             `= M · (1 − e^{−t}) ≤ M`.
So `|y(t)| ≤ |q| + M`. -/
lemma trackerTraj_bound {d : ℕ} {β : ℝ}
    (cbtc : CertifiedBoundedTimeComputable d β) (q : ℚ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ t, 0 ≤ t → |trackerTraj cbtc q t| ≤ B := by
  obtain ⟨M, hM_nn, hM_bd⟩ := outTraj_bound cbtc
  refine ⟨|(q : ℝ)| + M, by positivity, fun t ht => ?_⟩
  -- |y(t)| = |q + e^{-t}·F(t)| ≤ |q| + e^{-t}·|F(t)|
  -- and |F(t)| = |∫₀^t e^s x_out(s) ds| ≤ ∫₀^t e^s · M ds = M · (e^t - 1)
  -- so e^{-t}·|F(t)| ≤ M·(1 - e^{-t}) ≤ M.
  unfold trackerTraj
  have h_exp_pos : 0 < Real.exp (-t) := Real.exp_pos _
  have h_exp_le : Real.exp (-t) ≤ 1 := by
    rw [show (1 : ℝ) = Real.exp 0 from (Real.exp_zero).symm]
    exact Real.exp_le_exp.mpr (by linarith)
  -- Bound |F(t)|. For t ≥ 0, F(t) = ∫₀^t e^s·x_out(s) ds.
  -- |F(t)| ≤ ∫₀^t |e^s · x_out(s)| ds ≤ ∫₀^t e^s · M ds = M·(e^t - 1).
  have hF_abs : |trackerIntegral cbtc t| ≤ M * (Real.exp t - 1) := by
    unfold trackerIntegral
    have habs : |∫ s in (0 : ℝ)..t, Real.exp s * outTraj cbtc s| ≤
        ∫ s in (0 : ℝ)..t, |Real.exp s * outTraj cbtc s| :=
      intervalIntegral.abs_integral_le_integral_abs ht
    have hbound_ptw : ∀ s ∈ Set.Icc (0 : ℝ) t,
        |Real.exp s * outTraj cbtc s| ≤ Real.exp s * M := by
      intro s hs
      rw [abs_mul]
      have hexp_nn : 0 ≤ Real.exp s := (Real.exp_pos s).le
      have hexp_abs : |Real.exp s| = Real.exp s := abs_of_nonneg hexp_nn
      rw [hexp_abs]
      exact mul_le_mul_of_nonneg_left (hM_bd s) hexp_nn
    have hexp_int : IntervalIntegrable (fun s => Real.exp s * M)
        MeasureTheory.volume 0 t :=
      (Real.continuous_exp.mul continuous_const).intervalIntegrable 0 t
    have hle_bd : ∫ s in (0 : ℝ)..t, |Real.exp s * outTraj cbtc s| ≤
        ∫ s in (0 : ℝ)..t, Real.exp s * M := by
      apply intervalIntegral.integral_mono_on ht
      · exact ((trackerIntegrand_continuous cbtc).abs).intervalIntegrable 0 t
      · exact hexp_int
      · exact hbound_ptw
    -- ∫₀^t e^s · M ds = M · (e^t - 1).
    have heval : ∫ s in (0 : ℝ)..t, Real.exp s * M = M * (Real.exp t - 1) := by
      rw [show (fun s => Real.exp s * M) = (fun s => M * Real.exp s) from
        funext fun s => by ring]
      rw [intervalIntegral.integral_const_mul]
      rw [integral_exp]
      rw [Real.exp_zero]
    calc |∫ s in (0 : ℝ)..t, Real.exp s * outTraj cbtc s|
        ≤ ∫ s in (0 : ℝ)..t, |Real.exp s * outTraj cbtc s| := habs
      _ ≤ ∫ s in (0 : ℝ)..t, Real.exp s * M := hle_bd
      _ = M * (Real.exp t - 1) := heval
  -- Now combine: |e^{-t}·F(t)| ≤ e^{-t}·|F(t)| ≤ e^{-t}·M·(e^t - 1) = M·(1 - e^{-t}) ≤ M.
  have habs_combined :
      |(q : ℝ) + Real.exp (-t) * trackerIntegral cbtc t| ≤ |(q : ℝ)| + M := by
    have h1 : |(q : ℝ) + Real.exp (-t) * trackerIntegral cbtc t| ≤
        |(q : ℝ)| + |Real.exp (-t) * trackerIntegral cbtc t| := abs_add_le _ _
    have h2 : |Real.exp (-t) * trackerIntegral cbtc t| ≤ M := by
      rw [abs_mul, abs_of_nonneg h_exp_pos.le]
      have h3 : Real.exp (-t) * |trackerIntegral cbtc t| ≤
          Real.exp (-t) * (M * (Real.exp t - 1)) :=
        mul_le_mul_of_nonneg_left hF_abs h_exp_pos.le
      have hsimp : Real.exp (-t) * (M * (Real.exp t - 1)) = M * (1 - Real.exp (-t)) := by
        have hExpCancel : Real.exp (-t) * Real.exp t = 1 := by
          rw [← Real.exp_add]; simp
        have hfact : Real.exp (-t) * (Real.exp t - 1) = 1 - Real.exp (-t) := by
          rw [mul_sub, hExpCancel, mul_one]
        calc Real.exp (-t) * (M * (Real.exp t - 1))
            = M * (Real.exp (-t) * (Real.exp t - 1)) := by ring
          _ = M * (1 - Real.exp (-t)) := by rw [hfact]
      have h_one_sub_le : M * (1 - Real.exp (-t)) ≤ M := by
        have hle : 1 - Real.exp (-t) ≤ 1 := by linarith
        have hge : 0 ≤ 1 - Real.exp (-t) := by linarith
        calc M * (1 - Real.exp (-t))
            ≤ M * 1 := mul_le_mul_of_nonneg_left hle hM_nn
          _ = M := mul_one _
      linarith [hsimp]
    linarith
  exact habs_combined

/-! ## Step 5c: the full `PIVP.Solution` for the extended system.

We now assemble the `extendedTraj` into a genuine `PIVP.Solution`. The
`init_cond` is immediate from `extendedTraj_init`. The `is_solution` (ODE
verification) splits by `Fin.lastCases`: for `Fin.castSucc i`, the derivative
is inherited from `cbtc.sol.is_solution`; for `Fin.last d`, it comes from
`trackerTraj_hasDerivAt` plus the field decoding identity.
-/

/-- Per-species PIVP-field value of the extended system, evaluated on the
extended trajectory at time `t`.

For `i.castSucc`: equals the original field (via `rename`/`Fin.snoc` identity).
For `Fin.last d`: equals `x_out(t) + q − y(t)`. -/
lemma relaxationPIVP_evalField_castSucc {d : ℕ} {β : ℝ}
    (cbtc : CertifiedBoundedTimeComputable d β) (q : ℚ) (t : ℝ) (i : Fin d) :
    (relaxationPIVP cbtc.pivp q).toPIVP.field (extendedTraj cbtc q t) i.castSucc
      = cbtc.pivp.toPIVP.field (cbtc.sol.trajectory t) i := by
  show (relaxationPIVP cbtc.pivp q).evalField (extendedTraj cbtc q t) i.castSucc
     = cbtc.pivp.evalField (cbtc.sol.trajectory t) i
  unfold PolyPIVP.evalField
  rw [relaxationPIVP_field_castSucc]
  -- eval₂ of rename Fin.castSucc P.field i = eval₂ P.field i (x ∘ Fin.castSucc).
  rw [MvPolynomial.eval₂_rename]
  congr 1
  funext j
  rw [Function.comp_apply, extendedTraj_castSucc]

lemma relaxationPIVP_evalField_last {d : ℕ} {β : ℝ}
    (cbtc : CertifiedBoundedTimeComputable d β) (q : ℚ) {t : ℝ} (ht : 0 ≤ t) :
    (relaxationPIVP cbtc.pivp q).toPIVP.field (extendedTraj cbtc q t) (Fin.last d)
      = outTraj cbtc t + (q : ℝ) - trackerTraj cbtc q t := by
  show (relaxationPIVP cbtc.pivp q).evalField (extendedTraj cbtc q t) (Fin.last d)
     = _
  unfold PolyPIVP.evalField
  rw [relaxationPIVP_field_last]
  -- trackerField = X P.output.castSucc + C q - 1 * X (Fin.last d)
  unfold trackerField trackerProd trackerDegr
  simp only [MvPolynomial.eval₂_sub, MvPolynomial.eval₂_add, MvPolynomial.eval₂_mul,
             MvPolynomial.eval₂_X, MvPolynomial.eval₂_C, MvPolynomial.eval₂_one]
  have h_out : extendedTraj cbtc q t (Fin.castSucc cbtc.pivp.output) = outTraj cbtc t := by
    rw [extendedTraj_castSucc, outTraj_of_nonneg cbtc ht]
  have h_y : extendedTraj cbtc q t (Fin.last d) = trackerTraj cbtc q t :=
    extendedTraj_last cbtc q t
  rw [h_out, h_y]
  -- Goal after rw: outTraj + Rat.castHom ℝ q - 1 * trackerTraj = outTraj + q - trackerTraj.
  -- 1 * trackerTraj = trackerTraj and Rat.castHom ℝ q = (q : ℝ).
  show outTraj cbtc t + (Rat.castHom ℝ) q - 1 * trackerTraj cbtc q t
     = outTraj cbtc t + (q : ℝ) - trackerTraj cbtc q t
  rw [one_mul]
  rfl

/-- Construct the full `PIVP.Solution` of the extended system, using the
explicit `extendedTraj`. Uses `cbtc.sol.is_solution` on the first `d`
coordinates (lifted via `Fin.castSucc`) and `trackerTraj_hasDerivAt` on
the last coordinate. -/
noncomputable def extendedSolution {d : ℕ} {β : ℝ}
    (cbtc : CertifiedBoundedTimeComputable d β) (q : ℚ) :
    PIVP.Solution (relaxationPIVP cbtc.pivp q).toPIVP where
  trajectory := extendedTraj cbtc q
  init_cond := extendedTraj_init cbtc q
  is_solution := by
    intro t ht
    refine hasDerivAt_pi.mpr ?_
    intro k
    refine Fin.lastCases ?_ (fun i => ?_) k
    · -- Last coord: trackerTraj has derivative = field at Fin.last d.
      have hDer : HasDerivAt (trackerTraj cbtc q)
          (outTraj cbtc t + (q : ℝ) - trackerTraj cbtc q t) t :=
        trackerTraj_hasDerivAt cbtc q t
      have hField := relaxationPIVP_evalField_last cbtc q ht
      have hLHS : (fun s => extendedTraj cbtc q s (Fin.last d)) = trackerTraj cbtc q := by
        funext s
        exact extendedTraj_last cbtc q s
      rw [hLHS, hField]
      exact hDer
    · -- castSucc coord: inherit from cbtc.sol.is_solution.
      have hDer_orig := (hasDerivAt_pi.mp (cbtc.sol.is_solution t ht)) i
      have hField := relaxationPIVP_evalField_castSucc cbtc q t i
      have hLHS : (fun s => extendedTraj cbtc q s i.castSucc)
          = fun s => cbtc.sol.trajectory s i := by
        funext s
        exact extendedTraj_castSucc cbtc q s i
      rw [hLHS, hField]
      exact hDer_orig

/-- The extended trajectory is bounded: each original coordinate by `M`
(from `cbtc.bounded`), and the tracker by `|q| + M`. -/
lemma extendedTraj_isBounded {d : ℕ} {β : ℝ}
    (cbtc : CertifiedBoundedTimeComputable d β) (q : ℚ) :
    (relaxationPIVP cbtc.pivp q).toPIVP.IsBounded (extendedTraj cbtc q) := by
  obtain ⟨M, hMpos, hMbd⟩ := cbtc.bounded
  obtain ⟨Btr, hBtr_nn, hBtr_bd⟩ := trackerTraj_bound cbtc q
  -- B := max M (|q| + Btr) + 1 > 0.
  refine ⟨max M Btr + 1, by positivity, fun t ht => ?_⟩
  -- Use `pi_norm_le_iff_of_nonneg`.
  rw [pi_norm_le_iff_of_nonneg (by positivity)]
  intro k
  refine Fin.lastCases ?_ (fun i => ?_) k
  · -- last: |trackerTraj q t| ≤ Btr ≤ max M Btr + 1.
    rw [extendedTraj_last, Real.norm_eq_abs]
    have h : |trackerTraj cbtc q t| ≤ Btr := hBtr_bd t ht
    have h_mx : Btr ≤ max M Btr := le_max_right _ _
    linarith
  · -- castSucc: ‖cbtc.sol.trajectory t i‖ ≤ M ≤ max M Btr + 1.
    rw [extendedTraj_castSucc]
    have h1 : ‖cbtc.sol.trajectory t i‖ ≤ ‖cbtc.sol.trajectory t‖ :=
      norm_le_pi_norm _ _
    have h2 : ‖cbtc.sol.trajectory t‖ ≤ M := hMbd t ht
    have h_mx : M ≤ max M Btr := le_max_left _ _
    linarith

/-! ## Step 5d: narrow analytic residual axiom — relaxation tracker convergence.

With `extendedSolution` and `extendedTraj_isBounded` in hand, the only remaining
analytic content is the **convergence** of the tracker coordinate to `β + q`
with an effective time modulus. The convergence is the standard linear-ODE
Grönwall estimate; Mathlib's API exposes this only in pieces.

We state it as a narrowed axiom: given the explicit `extendedSolution`, we
obtain a time modulus bounding convergence. The solution + boundedness parts
are now fully proved above. -/
axiom relaxation_tracker_convergence {β : ℝ} (q : ℚ) (hq : 0 < q) {d : ℕ}
    (cbtc : CertifiedBoundedTimeComputable d β) :
    ∃ modulus' : TimeModulus,
      ∀ r : ℕ, ∀ t : ℝ, t > modulus' r →
        |(extendedSolution cbtc q).trajectory t (Fin.last d) - (β + (q : ℝ))|
          < Real.exp (-(r : ℝ))

/-- Discharge the original-form `relaxation_tracker_solution` axiom in terms
of the explicit solution construction. The existence/boundedness parts are
proved; only convergence remains as the narrower axiom above. -/
theorem relaxation_tracker_solution {β : ℝ} (q : ℚ) (hq : 0 < q) {d : ℕ}
    (cbtc : CertifiedBoundedTimeComputable d β) :
    ∃ (sol' : PIVP.Solution (relaxationPIVP cbtc.pivp q).toPIVP)
      (modulus' : TimeModulus),
      (relaxationPIVP cbtc.pivp q).toPIVP.IsBounded sol'.trajectory ∧
      (∀ r : ℕ, ∀ t : ℝ, t > modulus' r →
        |sol'.trajectory t (Fin.last d) - (β + (q : ℝ))| < Real.exp (-(r : ℝ))) := by
  obtain ⟨mod', hconv⟩ := relaxation_tracker_convergence q hq cbtc
  exact ⟨extendedSolution cbtc q, mod',
    extendedTraj_isBounded cbtc q, hconv⟩

/-! ## Step 6: assemble the full `CertifiedBoundedTimeComputable`. -/

/-- RTCRN1 Lemma 4.3, strictly positive case: shifting `β` by `q > 0` preserves
certified CRN-computability with a `PolyCRNDecomposition`. Factored into the
structural extension (proved) and the linear-ODE convergence (narrow residual
axiom `relaxation_tracker_solution`). -/
theorem certified_add_rational_pos_proved {β : ℝ} (q : ℚ) (hq : 0 < q) {d : ℕ}
    (cbtc : CertifiedBoundedTimeComputable d β)
    (pcd : PolyCRNDecomposition d cbtc.pivp) :
    ∃ (d' : ℕ) (cbtc' : CertifiedBoundedTimeComputable d' (β + (q : ℝ)))
      (_ : PolyCRNDecomposition d' cbtc'.pivp), True := by
  obtain ⟨sol', mod', hbd, hconv⟩ := relaxation_tracker_solution q hq cbtc
  refine ⟨d + 1,
    { pivp := relaxationPIVP cbtc.pivp q
      sol := sol'
      modulus := mod'
      bounded := hbd
      convergence := by
        intro r t ht
        show |sol'.trajectory t (relaxationPIVP cbtc.pivp q).output
            - (β + (q : ℝ))| < _
        rw [relaxationPIVP_output]
        exact hconv r t ht },
    relaxationPIVP_polyCRN q (le_of_lt hq) pcd, trivial⟩

end Algebraic
end Ripple
