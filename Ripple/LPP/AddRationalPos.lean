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

  2. **Analytic content (now proved here).** The convergence of the
     extended trajectory to `β + q` under the linear relaxation ODE,
     with an explicit affine slowdown theorem and the derived existential
     modulus packaging. The underlying derivation is
       |y(t) − (β + q)| ≤ |y(0) − β − q| · e^{−t} + ∫₀^t e^{−(t−s)} |x_out(s) − β| ds.

  The old API names `relaxation_tracker_convergence` and
  `relaxation_tracker_solution` are retained, but they are theorems, not
  axioms. -/

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

The convergence / boundedness analysis of this tracker is the main analytic
content of this file; see `relaxation_tracker_solution` below.
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

/-- **Sharp upper bound on `trackerTraj`** when the output signal
`outTraj cbtc s` is pointwise bounded above by `U ≥ 0` on `[0, t]`.

If `0 ≤ q`, `0 ≤ U`, and `outTraj cbtc s ≤ U` for all `s ∈ [0, t]`, then
`trackerTraj cbtc q t ≤ U + q`. Proof via the Duhamel representation
`y(t) = q + e^{-t} · ∫₀^t e^s · x_out(s) ds`:
    `∫₀^t e^s · x_out(s) ds ≤ ∫₀^t e^s · U ds = U · (e^t − 1)`,
hence `y(t) ≤ q + e^{-t} · U · (e^t − 1) = q + U · (1 − e^{-t}) ≤ q + U`. -/
lemma trackerTraj_upper_of_outTraj_upper {d : ℕ} {β : ℝ}
    (cbtc : CertifiedBoundedTimeComputable d β) {q : ℚ} (hq : 0 ≤ q)
    {U : ℝ} (hU_nn : 0 ≤ U) {t : ℝ} (ht : 0 ≤ t)
    (hx_le : ∀ s, 0 ≤ s → s ≤ t → outTraj cbtc s ≤ U) :
    trackerTraj cbtc q t ≤ U + (q : ℝ) := by
  unfold trackerTraj
  have h_exp_pos : 0 < Real.exp (-t) := Real.exp_pos _
  have h_exp_le : Real.exp (-t) ≤ 1 := by
    rw [show (1 : ℝ) = Real.exp 0 from (Real.exp_zero).symm]
    exact Real.exp_le_exp.mpr (by linarith)
  -- Step A: bound `trackerIntegral cbtc t ≤ U · (e^t − 1)`.
  have hF_le : trackerIntegral cbtc t ≤ U * (Real.exp t - 1) := by
    unfold trackerIntegral
    have hbound_ptw : ∀ s ∈ Set.Icc (0 : ℝ) t,
        Real.exp s * outTraj cbtc s ≤ Real.exp s * U := by
      intro s hs
      exact mul_le_mul_of_nonneg_left (hx_le s hs.1 hs.2) (Real.exp_pos s).le
    have hexp_int : IntervalIntegrable (fun s => Real.exp s * U)
        MeasureTheory.volume 0 t :=
      (Real.continuous_exp.mul continuous_const).intervalIntegrable 0 t
    have hle_bd : ∫ s in (0 : ℝ)..t, Real.exp s * outTraj cbtc s ≤
        ∫ s in (0 : ℝ)..t, Real.exp s * U := by
      apply intervalIntegral.integral_mono_on ht
      · exact (trackerIntegrand_continuous cbtc).intervalIntegrable 0 t
      · exact hexp_int
      · exact hbound_ptw
    have heval : ∫ s in (0 : ℝ)..t, Real.exp s * U = U * (Real.exp t - 1) := by
      rw [show (fun s => Real.exp s * U) = (fun s => U * Real.exp s) from
        funext fun s => by ring]
      rw [intervalIntegral.integral_const_mul]
      rw [integral_exp]
      rw [Real.exp_zero]
    linarith [hle_bd, heval]
  -- Step B: multiply by the positive factor `e^{-t}`.
  have hProd_le : Real.exp (-t) * trackerIntegral cbtc t
      ≤ Real.exp (-t) * (U * (Real.exp t - 1)) :=
    mul_le_mul_of_nonneg_left hF_le h_exp_pos.le
  -- Algebraic simplification: `e^{-t} · U · (e^t − 1) = U · (1 − e^{-t})`.
  have hExpCancel : Real.exp (-t) * Real.exp t = 1 := by
    rw [← Real.exp_add]; simp
  have hSimp : Real.exp (-t) * (U * (Real.exp t - 1)) = U * (1 - Real.exp (-t)) := by
    have hfact : Real.exp (-t) * (Real.exp t - 1) = 1 - Real.exp (-t) := by
      rw [mul_sub, hExpCancel, mul_one]
    calc Real.exp (-t) * (U * (Real.exp t - 1))
        = U * (Real.exp (-t) * (Real.exp t - 1)) := by ring
      _ = U * (1 - Real.exp (-t)) := by rw [hfact]
  have hOneSub_le : U * (1 - Real.exp (-t)) ≤ U := by
    have hle : 1 - Real.exp (-t) ≤ 1 := by linarith
    calc U * (1 - Real.exp (-t))
        ≤ U * 1 := mul_le_mul_of_nonneg_left hle hU_nn
      _ = U := mul_one _
  have hqR_nn : (0 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  linarith [hSimp, hProd_le, hOneSub_le]

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

/-- Continuity of `trackerIntegral cbtc`: follows from
`trackerIntegral_hasDerivAt`, which gives `HasDerivAt` at every `t : ℝ`,
hence `ContinuousAt` at every `t`. -/
lemma trackerIntegral_continuous {d : ℕ} {β : ℝ}
    (cbtc : CertifiedBoundedTimeComputable d β) :
    Continuous (trackerIntegral cbtc) := by
  refine continuous_iff_continuousAt.mpr (fun t => ?_)
  exact (trackerIntegral_hasDerivAt cbtc t).continuousAt

/-- Continuity of `trackerTraj cbtc q`: as `q + e^{-t} · F(t)` with `F`
continuous and `e^{-t}` continuous, the composition is continuous. -/
lemma trackerTraj_continuous {d : ℕ} {β : ℝ}
    (cbtc : CertifiedBoundedTimeComputable d β) (q : ℚ) :
    Continuous (trackerTraj cbtc q) := by
  unfold trackerTraj
  have hExp : Continuous (fun t : ℝ => Real.exp (-t)) :=
    Real.continuous_exp.comp continuous_neg
  exact continuous_const.add (hExp.mul (trackerIntegral_continuous cbtc))

/-- Continuity of `extendedTraj cbtc q`: via `Fin.snoc` assembly of
the continuous `cbtc.sol.trajectory` (from `cbtc.trajectory_continuous`)
and the continuous `trackerTraj`. -/
lemma extendedTraj_continuous {d : ℕ} {β : ℝ}
    (cbtc : CertifiedBoundedTimeComputable d β) (q : ℚ) :
    Continuous (extendedTraj cbtc q) := by
  -- Pointwise continuity via `continuous_pi`: each component is continuous.
  refine continuous_pi (fun k => ?_)
  refine Fin.lastCases ?_ (fun i => ?_) k
  · -- Last coord: `trackerTraj cbtc q`.
    have h1 : (fun t : ℝ => extendedTraj cbtc q t (Fin.last d))
        = trackerTraj cbtc q := by
      funext s; exact extendedTraj_last cbtc q s
    rw [h1]
    exact trackerTraj_continuous cbtc q
  · -- castSucc coord: `cbtc.sol.trajectory t i` = `(continuous_apply i) ∘ cbtc.sol.trajectory`.
    have h1 : (fun t : ℝ => extendedTraj cbtc q t i.castSucc)
        = fun t : ℝ => cbtc.sol.trajectory t i := by
      funext s; exact extendedTraj_castSucc cbtc q s i
    rw [h1]
    exact (continuous_apply i).comp cbtc.trajectory_continuous

/-- Continuity of `extendedSolution cbtc q`'s trajectory. -/
lemma extendedSolution_trajectory_continuous {d : ℕ} {β : ℝ}
    (cbtc : CertifiedBoundedTimeComputable d β) (q : ℚ) :
    Continuous (extendedSolution cbtc q).trajectory :=
  extendedTraj_continuous cbtc q

/-! ## Step 5d: relaxation tracker convergence (Grönwall/Duhamel estimate).

With `extendedSolution` and `extendedTraj_isBounded` in hand, the remaining
analytic content is the **convergence** of the tracker coordinate to `β + q`
with an effective time modulus. We prove the standard linear-ODE Grönwall
estimate directly, using the Duhamel formula
  y(t) = q + e^{−t} · ∫₀^t e^s · x_out(s) ds
and the key algebraic identity
  y(t) − (β + q) = e^{−t} · (∫₀^t e^s · x_out(s) ds − β · e^t).
Splitting the integral at `T := cbtc.modulus (r+1)` and using
`|x_out(s) − β| < e^{−(r+1)}` for `s > T` yields the effective modulus.
-/

/-- Algebraic identity: `trackerTraj t − (β+q) = e^{-t} · (trackerIntegral t − β·e^t)`.
Pure arithmetic + `Real.exp_neg` + `exp(-t)·exp(t) = 1`. -/
lemma trackerTraj_sub_identity {d : ℕ} {β : ℝ}
    (cbtc : CertifiedBoundedTimeComputable d β) (q : ℚ) (t : ℝ) :
    trackerTraj cbtc q t - (β + (q : ℝ))
      = Real.exp (-t) * (trackerIntegral cbtc t - β * Real.exp t) := by
  unfold trackerTraj
  have hExpCancel : Real.exp (-t) * Real.exp t = 1 := by
    rw [← Real.exp_add]; simp
  have : Real.exp (-t) * (β * Real.exp t) = β := by
    calc Real.exp (-t) * (β * Real.exp t)
        = β * (Real.exp (-t) * Real.exp t) := by ring
      _ = β * 1 := by rw [hExpCancel]
      _ = β := by ring
  linarith [this]

/-- Bound on `trackerIntegral t − β · e^t` split at `T`:
  `trackerIntegral t − β · e^t = (trackerIntegral T − β · e^T) + ∫_T^t e^s · (x_out(s) − β) ds`.
The head piece is ≤ (M+|β|)(e^T−1) + |β|·e^T; the tail is bounded by the convergence hyp. -/
lemma trackerIntegral_split {d : ℕ} {β : ℝ}
    (cbtc : CertifiedBoundedTimeComputable d β)
    {T t : ℝ} (hT : 0 ≤ T) (hTt : T ≤ t) :
    trackerIntegral cbtc t - β * Real.exp t
      = (trackerIntegral cbtc T - β * Real.exp T)
        + ∫ s in T..t, Real.exp s * (outTraj cbtc s - β) := by
  unfold trackerIntegral
  have hInt1 := (trackerIntegrand_intervalIntegrable cbtc 0 T)
  have hInt2 := (trackerIntegrand_intervalIntegrable cbtc T t)
  have hadd : (∫ s in (0 : ℝ)..T, Real.exp s * outTraj cbtc s)
              + ∫ s in T..t, Real.exp s * outTraj cbtc s
              = ∫ s in (0 : ℝ)..t, Real.exp s * outTraj cbtc s :=
    intervalIntegral.integral_add_adjacent_intervals hInt1 hInt2
  have hExpInt : ∫ s in T..t, Real.exp s = Real.exp t - Real.exp T := by
    rw [integral_exp]
  have hβInt : ∫ s in T..t, Real.exp s * β = β * (Real.exp t - Real.exp T) := by
    rw [show (fun s => Real.exp s * β) = (fun s => β * Real.exp s) from
      funext fun _ => by ring]
    rw [intervalIntegral.integral_const_mul]
    rw [hExpInt]
  have hexpβ_ii : IntervalIntegrable (fun s => Real.exp s * β)
      MeasureTheory.volume T t :=
    (Real.continuous_exp.mul continuous_const).intervalIntegrable T t
  have hsub : ∫ s in T..t, Real.exp s * (outTraj cbtc s - β)
            = (∫ s in T..t, Real.exp s * outTraj cbtc s)
              - ∫ s in T..t, Real.exp s * β := by
    rw [show (fun s => Real.exp s * (outTraj cbtc s - β))
          = (fun s => Real.exp s * outTraj cbtc s - Real.exp s * β) from
      funext fun s => by ring]
    exact intervalIntegral.integral_sub hInt2 hexpβ_ii
  linarith [hadd, hβInt, hsub]

/-- Bound on the head piece `trackerIntegral T`: `|trackerIntegral T| ≤ M · (e^T − 1)`.
Direct consequence of `|x_out| ≤ M` and `∫₀^T e^s ds = e^T − 1`. -/
lemma trackerIntegral_abs_bound {d : ℕ} {β : ℝ}
    (cbtc : CertifiedBoundedTimeComputable d β)
    {M : ℝ} (hM_nn : 0 ≤ M) (hM_bd : ∀ t, |outTraj cbtc t| ≤ M)
    {T : ℝ} (hT : 0 ≤ T) :
    |trackerIntegral cbtc T| ≤ M * (Real.exp T - 1) := by
  unfold trackerIntegral
  have habs : |∫ s in (0 : ℝ)..T, Real.exp s * outTraj cbtc s| ≤
      ∫ s in (0 : ℝ)..T, |Real.exp s * outTraj cbtc s| :=
    intervalIntegral.abs_integral_le_integral_abs hT
  have hbound_ptw : ∀ s ∈ Set.Icc (0 : ℝ) T,
      |Real.exp s * outTraj cbtc s| ≤ Real.exp s * M := by
    intro s _
    rw [abs_mul]
    have hexp_nn : 0 ≤ Real.exp s := (Real.exp_pos s).le
    rw [abs_of_nonneg hexp_nn]
    exact mul_le_mul_of_nonneg_left (hM_bd s) hexp_nn
  have hexp_int : IntervalIntegrable (fun s => Real.exp s * M)
      MeasureTheory.volume 0 T :=
    (Real.continuous_exp.mul continuous_const).intervalIntegrable 0 T
  have hle_bd : ∫ s in (0 : ℝ)..T, |Real.exp s * outTraj cbtc s| ≤
      ∫ s in (0 : ℝ)..T, Real.exp s * M := by
    apply intervalIntegral.integral_mono_on hT
    · exact ((trackerIntegrand_continuous cbtc).abs).intervalIntegrable 0 T
    · exact hexp_int
    · exact hbound_ptw
  have heval : ∫ s in (0 : ℝ)..T, Real.exp s * M = M * (Real.exp T - 1) := by
    rw [show (fun s => Real.exp s * M) = (fun s => M * Real.exp s) from
      funext fun s => by ring]
    rw [intervalIntegral.integral_const_mul]
    rw [integral_exp]
    rw [Real.exp_zero]
  calc |∫ s in (0 : ℝ)..T, Real.exp s * outTraj cbtc s|
      ≤ ∫ s in (0 : ℝ)..T, |Real.exp s * outTraj cbtc s| := habs
    _ ≤ ∫ s in (0 : ℝ)..T, Real.exp s * M := hle_bd
    _ = M * (Real.exp T - 1) := heval

/-- Bound on the tail integral using the convergence hypothesis.
For `T ≤ t` and `|x_out(s) - β| < ε` for `s ≥ T` (with `T ≥ cbtc.modulus(r+1)`):
  `|∫_T^t e^s (x_out(s) − β) ds| ≤ ε · (e^t − e^T)`. -/
lemma tail_integral_bound {d : ℕ} {β : ℝ}
    (cbtc : CertifiedBoundedTimeComputable d β)
    {ε T t : ℝ} (hε_pos : 0 < ε) (hTt : T ≤ t)
    (hbd : ∀ s, T < s → |outTraj cbtc s - β| ≤ ε) :
    |∫ s in T..t, Real.exp s * (outTraj cbtc s - β)|
      ≤ ε * (Real.exp t - Real.exp T) := by
  have hcont : Continuous (fun s => Real.exp s * (outTraj cbtc s - β)) :=
    Real.continuous_exp.mul ((outTraj_continuous cbtc).sub continuous_const)
  have habs_int : IntervalIntegrable (fun s => |Real.exp s * (outTraj cbtc s - β)|)
      MeasureTheory.volume T t := hcont.abs.intervalIntegrable T t
  have hexpε_int : IntervalIntegrable (fun s => Real.exp s * ε)
      MeasureTheory.volume T t :=
    (Real.continuous_exp.mul continuous_const).intervalIntegrable T t
  have habs : |∫ s in T..t, Real.exp s * (outTraj cbtc s - β)|
      ≤ ∫ s in T..t, |Real.exp s * (outTraj cbtc s - β)| :=
    intervalIntegral.abs_integral_le_integral_abs hTt
  -- Use integral_mono_on but the bound holds pointwise for s ∈ Ioc(T,t), not at s=T.
  -- The set {T} has measure zero, so equality of integrals on (T, t] vs [T, t] is fine.
  -- We use the slightly weaker pointwise bound: |e^s·(x-β)| ≤ e^s · (|β| + M) at s = T,
  -- and ≤ e^s · ε elsewhere. Easier: continuity argument — since the integrand is
  -- bounded by ε on (T, t] and continuous, the bound extends to T by continuity.
  -- We prove: for all s in Icc T t, |x_out s - β| ≤ ε. At s = T, by continuity of x_out
  -- and hbd on approaching from above, |x_out T - β| ≤ ε.
  have hbd_closed : ∀ s ∈ Set.Icc T t, |outTraj cbtc s - β| ≤ ε := by
    intro s hs
    rcases eq_or_lt_of_le hs.1 with hTs | hTs
    · -- s = T: use continuity and limit from above
      -- Actually easier: the function `u ↦ |outTraj cbtc u - β|` is continuous,
      -- and ≤ ε on (T, t] which has T as a limit point. So value at T ≤ ε.
      have hcontAbs : Continuous (fun u => |outTraj cbtc u - β|) :=
        ((outTraj_continuous cbtc).sub continuous_const).abs
      have : ∀ᶠ u in nhdsWithin T (Set.Ioi T),
          |outTraj cbtc u - β| ≤ ε := by
        filter_upwards [self_mem_nhdsWithin] with u hu
        exact hbd u hu
      have hlimit : Filter.Tendsto (fun u => |outTraj cbtc u - β|)
          (nhdsWithin T (Set.Ioi T)) (nhds (|outTraj cbtc T - β|)) :=
        (hcontAbs.continuousAt).tendsto.mono_left nhdsWithin_le_nhds
      haveI hne : (nhdsWithin T (Set.Ioi T)).NeBot :=
        nhdsWithin_Ioi_neBot (le_refl T)
      -- use `le_of_tendsto` with eventually ≤
      subst hTs
      exact le_of_tendsto hlimit this
    · exact hbd s hTs
  have hle_bd : ∫ s in T..t, |Real.exp s * (outTraj cbtc s - β)| ≤
      ∫ s in T..t, Real.exp s * ε := by
    apply intervalIntegral.integral_mono_on hTt
    · exact habs_int
    · exact hexpε_int
    · intro s hs
      rw [abs_mul]
      have hexp_nn : 0 ≤ Real.exp s := (Real.exp_pos s).le
      rw [abs_of_nonneg hexp_nn]
      exact mul_le_mul_of_nonneg_left (hbd_closed s hs) hexp_nn
  have heval : ∫ s in T..t, Real.exp s * ε = ε * (Real.exp t - Real.exp T) := by
    rw [show (fun s => Real.exp s * ε) = (fun s => ε * Real.exp s) from
      funext fun s => by ring]
    rw [intervalIntegral.integral_const_mul]
    rw [integral_exp]
  linarith [habs, hle_bd, heval]

-- The proof term is large (many integral manipulations, exp arithmetic);
-- the default heartbeat budget is insufficient for elaboration.
set_option maxHeartbeats 800000 in
/-- The Grönwall-style convergence bound for the tracker.

**Sign-independent**: the proof uses only the Duhamel/exp-decay structure of
the linear scalar ODE `y' = x_out + q − y`, which is well-defined for any
`q : ℚ`. -/
theorem relaxation_tracker_convergence_affine {β : ℝ} (q : ℚ) {d : ℕ}
    (cbtc : CertifiedBoundedTimeComputable d β) :
    ∃ K : ℝ,
      ∀ r : ℕ, ∀ t : ℝ, t > max (cbtc.modulus (r+1)) 0 + (r : ℝ) + K →
        |(extendedSolution cbtc q).trajectory t (Fin.last d) - (β + (q : ℝ))|
          < Real.exp (-(r : ℝ)) := by
  -- Uniform bound M on outTraj.
  obtain ⟨M, hM_nn, hM_bd⟩ := outTraj_bound cbtc
  -- Let C := M + 2|β| + 1 > 0. We choose
  --   μ'(r) := max (cbtc.modulus (r+1)) 0 + r + log(2C) + 2.
  set C : ℝ := M + 2 * |β| + 1 with hC_def
  have hC_pos : 0 < C := by show 0 < M + 2 * |β| + 1; positivity
  have h2C_pos : 0 < 2 * C := by positivity
  refine ⟨Real.log (2 * C) + 2, ?_⟩
  intro r t ht
  -- Define T := max (cbtc.modulus (r+1)) 0.
  set T : ℝ := max (cbtc.modulus (r+1)) 0 with hT_def
  have hT_nn : 0 ≤ T := le_max_right _ _
  have hT_mod : cbtc.modulus (r+1) ≤ T := le_max_left _ _
  -- We have `ht : T + r + log(2C) + 2 < t`. Since `r ≥ 0, log(2C) > log(2) > 0` (as 2C ≥ 2),
  -- so `t > T`.
  have hC_ge_one : (1 : ℝ) ≤ C := by
    show (1 : ℝ) ≤ M + 2 * |β| + 1
    linarith [hM_nn, abs_nonneg β]
  have h_log_2C_nn : 0 ≤ Real.log (2 * C) := by
    apply Real.log_nonneg
    linarith
  have h_r_nn : (0 : ℝ) ≤ r := by positivity
  have hTt : T ≤ t := by linarith
  have h_gap : r + Real.log (2 * C) + 2 < t - T := by linarith
  -- Reduce goal to trackerTraj via extendedSolution.trajectory = extendedTraj.
  have hredex : (extendedSolution cbtc q).trajectory t (Fin.last d)
      = trackerTraj cbtc q t := extendedTraj_last cbtc q t
  rw [hredex]
  -- Use algebraic identity and split integral at T.
  rw [trackerTraj_sub_identity cbtc q t]
  rw [trackerIntegral_split cbtc hT_nn hTt]
  -- Convergence at r+1: for s > cbtc.modulus(r+1), |x_out(s) - β| < e^{-(r+1)}.
  -- Since T ≥ cbtc.modulus(r+1), the same bound holds for s > T.
  have hconv_r1 : ∀ s, T < s → |outTraj cbtc s - β| ≤ Real.exp (-((r+1 : ℕ) : ℝ)) := by
    intro s hs
    have hs_nn : 0 ≤ s := le_trans hT_nn (le_of_lt hs)
    have hs_mod : cbtc.modulus (r+1) < s := lt_of_le_of_lt hT_mod hs
    rw [outTraj_of_nonneg cbtc hs_nn]
    exact (cbtc.convergence (r+1) s hs_mod).le
  -- Bound tail integral.
  have htail := tail_integral_bound cbtc (Real.exp_pos _) hTt hconv_r1
  -- Bound head `trackerIntegral T − β·e^T`.
  have hhead_bd : |trackerIntegral cbtc T - β * Real.exp T| ≤
      M * (Real.exp T - 1) + |β| * Real.exp T := by
    calc |trackerIntegral cbtc T - β * Real.exp T|
        ≤ |trackerIntegral cbtc T| + |β * Real.exp T| := by
          rw [show trackerIntegral cbtc T - β * Real.exp T
              = trackerIntegral cbtc T + (-(β * Real.exp T)) from by ring]
          have := abs_add_le (trackerIntegral cbtc T) (-(β * Real.exp T))
          rw [abs_neg] at this
          exact this
      _ ≤ M * (Real.exp T - 1) + |β| * Real.exp T := by
          have h1 := trackerIntegral_abs_bound cbtc hM_nn hM_bd hT_nn
          have h2 : |β * Real.exp T| = |β| * Real.exp T := by
            rw [abs_mul, abs_of_nonneg (Real.exp_pos T).le]
          linarith
  -- Now combine.
  -- |trackerTraj t − (β+q)| = e^{-t} · |trackerIntegral t − β · e^t|
  -- trackerIntegral t − β · e^t = (trackerIntegral T − β · e^T) + ∫_T^t e^s (x_out - β) ds
  -- so ≤ (head) + (tail)
  rw [abs_mul, abs_of_nonneg (Real.exp_pos _).le]
  -- |(head part) + tail| ≤ (head_bd) + tail_bd.
  have hsum_bd :
      |(trackerIntegral cbtc T - β * Real.exp T)
        + ∫ s in T..t, Real.exp s * (outTraj cbtc s - β)|
      ≤ (M * (Real.exp T - 1) + |β| * Real.exp T)
        + Real.exp (-((r+1 : ℕ) : ℝ)) * (Real.exp t - Real.exp T) := by
    calc _ ≤ |trackerIntegral cbtc T - β * Real.exp T|
            + |∫ s in T..t, Real.exp s * (outTraj cbtc s - β)| := abs_add_le _ _
      _ ≤ _ := by linarith
  -- Multiply by e^{-t} ≥ 0.
  have hexp_nn : 0 ≤ Real.exp (-t) := (Real.exp_pos _).le
  have hmul : Real.exp (-t) * |(trackerIntegral cbtc T - β * Real.exp T)
                + ∫ s in T..t, Real.exp s * (outTraj cbtc s - β)|
      ≤ Real.exp (-t) * ((M * (Real.exp T - 1) + |β| * Real.exp T)
        + Real.exp (-((r+1 : ℕ) : ℝ)) * (Real.exp t - Real.exp T)) :=
    mul_le_mul_of_nonneg_left hsum_bd hexp_nn
  refine lt_of_le_of_lt hmul ?_
  -- Now rewrite RHS:
  -- e^{-t} · [(M(e^T−1) + |β|e^T) + e^{-(r+1)} (e^t − e^T)]
  --   = M·(e^{T-t} − e^{-t}) + |β| · e^{T-t} + e^{-(r+1)} · (1 − e^{T-t})
  --   ≤ (M + |β|) · e^{T-t} + e^{-(r+1)}
  have hexp_tt : Real.exp (-t) * Real.exp T = Real.exp (T - t) := by
    rw [← Real.exp_add]; congr 1; ring
  have hexp_ttt : Real.exp (-t) * Real.exp t = 1 := by
    rw [← Real.exp_add, add_comm]; simp
  have hr1_cancel :
      Real.exp (-((r + 1 : ℕ) : ℝ)) = Real.exp (-(r : ℝ)) * Real.exp (-1) := by
    rw [← Real.exp_add]
    congr 1
    push_cast
    ring
  -- Expand the RHS into a clean bound ≤ (M + |β|) · e^{T-t} + e^{-(r+1)}.
  have hRHS_bd :
      Real.exp (-t) * ((M * (Real.exp T - 1) + |β| * Real.exp T)
        + Real.exp (-((r+1 : ℕ) : ℝ)) * (Real.exp t - Real.exp T))
      ≤ (M + |β|) * Real.exp (T - t) + Real.exp (-((r+1 : ℕ) : ℝ)) := by
    have hexp_neg_t_pos : 0 < Real.exp (-t) := Real.exp_pos _
    have h_eq :
        Real.exp (-t) * ((M * (Real.exp T - 1) + |β| * Real.exp T)
          + Real.exp (-((r+1 : ℕ) : ℝ)) * (Real.exp t - Real.exp T))
        = M * Real.exp (T - t) - M * Real.exp (-t)
          + |β| * Real.exp (T - t)
          + Real.exp (-((r+1 : ℕ) : ℝ)) * (1 - Real.exp (T - t)) := by
      have h1 : Real.exp (-t) * (Real.exp T - 1) = Real.exp (T - t) - Real.exp (-t) := by
        rw [mul_sub, hexp_tt, mul_one]
      have h2 : Real.exp (-t) * Real.exp t = 1 := hexp_ttt
      have h3 : Real.exp (-t) * (Real.exp t - Real.exp T)
          = 1 - Real.exp (T - t) := by
        rw [mul_sub, h2, hexp_tt]
      calc Real.exp (-t) * ((M * (Real.exp T - 1) + |β| * Real.exp T)
          + Real.exp (-((r+1 : ℕ) : ℝ)) * (Real.exp t - Real.exp T))
          = M * (Real.exp (-t) * (Real.exp T - 1))
            + |β| * (Real.exp (-t) * Real.exp T)
            + Real.exp (-((r+1 : ℕ) : ℝ)) * (Real.exp (-t) * (Real.exp t - Real.exp T)) := by
            ring
        _ = M * (Real.exp (T - t) - Real.exp (-t))
            + |β| * Real.exp (T - t)
            + Real.exp (-((r+1 : ℕ) : ℝ)) * (1 - Real.exp (T - t)) := by
            rw [h1, hexp_tt, h3]
        _ = M * Real.exp (T - t) - M * Real.exp (-t)
            + |β| * Real.exp (T - t)
            + Real.exp (-((r+1 : ℕ) : ℝ)) * (1 - Real.exp (T - t)) := by ring
    rw [h_eq]
    have hM_exp_nn : 0 ≤ M * Real.exp (-t) :=
      mul_nonneg hM_nn hexp_neg_t_pos.le
    have h_exp_Tt_nn : 0 ≤ Real.exp (T - t) := (Real.exp_pos _).le
    have h_exp_Tt_le1 : Real.exp (T - t) ≤ 1 := by
      rw [show (1 : ℝ) = Real.exp 0 from (Real.exp_zero).symm]
      exact Real.exp_le_exp.mpr (by linarith)
    have h_one_sub_Tt_nn : 0 ≤ 1 - Real.exp (T - t) := by linarith
    have h_one_sub_Tt_le1 : 1 - Real.exp (T - t) ≤ 1 := by linarith
    have h_r1_pos : 0 ≤ Real.exp (-((r+1 : ℕ) : ℝ)) := (Real.exp_pos _).le
    have h4 : Real.exp (-((r+1 : ℕ) : ℝ)) * (1 - Real.exp (T - t))
        ≤ Real.exp (-((r+1 : ℕ) : ℝ)) * 1 :=
      mul_le_mul_of_nonneg_left h_one_sub_Tt_le1 h_r1_pos
    nlinarith [hM_exp_nn, h_exp_Tt_nn, h4]
  refine lt_of_le_of_lt hRHS_bd ?_
  -- Final step: (M+|β|) · e^{T-t} + e^{-(r+1)} < e^{-r}.
  -- Bound e^{T-t}: T-t < -r - log(2C) - 2, so e^{T-t} < e^{-r}/(2C·e²).
  have h_gap' : T - t < -(r : ℝ) - Real.log (2 * C) - 2 := by linarith
  have hexp_Tt_lt : Real.exp (T - t) < Real.exp (-(r : ℝ) - Real.log (2 * C) - 2) :=
    Real.exp_lt_exp.mpr h_gap'
  have hexp_split :
      Real.exp (-(r : ℝ) - Real.log (2 * C) - 2)
      = Real.exp (-(r : ℝ)) * ((1 : ℝ) / (2 * C)) * Real.exp (-2) := by
    have hrw : -(r : ℝ) - Real.log (2 * C) - 2
        = -(r : ℝ) + (-Real.log (2 * C)) + (-2) := by ring
    have hinv : Real.exp (-Real.log (2 * C)) = 1 / (2 * C) := by
      rw [Real.exp_neg, Real.exp_log h2C_pos, one_div]
    rw [hrw, Real.exp_add, Real.exp_add, hinv]
  -- Now (M+|β|) · e^{T-t} ≤ (M+|β|) · e^{-r}/(2C) · e^{-2} ≤ (C/2C) e^{-r}·e^{-2}
  --   = e^{-r} · e^{-2} / 2
  have hMβ_le_C : M + |β| ≤ C := by
    show M + |β| ≤ M + 2 * |β| + 1; linarith [abs_nonneg β]
  have hMβ_nn : 0 ≤ M + |β| := by linarith [hM_nn, abs_nonneg β]
  -- Combine:
  -- (M+|β|) · e^{T-t} < (M+|β|) · e^{-r}/(2C) · e^{-2} ≤ (1/2) · e^{-r} · e^{-2}
  have h_piece1_bd : (M + |β|) * Real.exp (T - t) ≤
      (M + |β|) * (Real.exp (-(r : ℝ)) * ((1 : ℝ) / (2 * C)) * Real.exp (-2)) := by
    have hle := (Real.exp_lt_exp.mpr h_gap').le
    have hmix : Real.exp (T - t) ≤ Real.exp (-(r : ℝ)) * ((1 : ℝ) / (2 * C)) * Real.exp (-2) := by
      rw [← hexp_split]; exact hle
    exact mul_le_mul_of_nonneg_left hmix hMβ_nn
  have h_piece1_le : (M + |β|) * (Real.exp (-(r : ℝ)) * ((1 : ℝ) / (2 * C)) * Real.exp (-2))
      ≤ Real.exp (-(r : ℝ)) * ((1 : ℝ) / 2) * Real.exp (-2) := by
    have h_coef : (M + |β|) * ((1 : ℝ) / (2 * C)) ≤ 1 / 2 := by
      rw [mul_one_div, div_le_div_iff₀ h2C_pos (by norm_num : (0 : ℝ) < 2)]
      linarith [hMβ_le_C, hC_pos]
    have h_rhs_nn : 0 ≤ Real.exp (-(r : ℝ)) * Real.exp (-2) := by positivity
    nlinarith [h_coef, h_rhs_nn, Real.exp_pos (-(r : ℝ)), Real.exp_pos (-(2 : ℝ)),
                mul_nonneg hMβ_nn (Real.exp_pos (-(r : ℝ))).le]
  -- Second piece: e^{-(r+1)} = e^{-r} · e^{-1}.
  have h_piece2 : Real.exp (-((r+1 : ℕ) : ℝ)) = Real.exp (-(r : ℝ)) * Real.exp (-1) := hr1_cancel
  -- Sum:
  -- (M+|β|) · e^{T-t} + e^{-(r+1)}
  --  < e^{-r}·(1/2)·e^{-2} + e^{-r}·e^{-1}
  --  = e^{-r} · ((1/2)·e^{-2} + e^{-1})
  -- Need to show (1/2)·e^{-2} + e^{-1} < 1. Since e^{-1} ≈ 0.368, e^{-2} ≈ 0.135:
  -- 0.5 · 0.135 + 0.368 = 0.068 + 0.368 = 0.436 < 1. ✓
  have h_exp_neg_1 : Real.exp (-1) < (1 : ℝ) / 2 := by
    have hlt : (2 : ℝ) < Real.exp 1 := by
      have h := Real.add_one_lt_exp (x := (1 : ℝ)) (by norm_num)
      linarith
    rw [Real.exp_neg]
    rw [show (1 : ℝ) / 2 = (2 : ℝ)⁻¹ by ring]
    exact (inv_lt_inv₀ (Real.exp_pos _) (by norm_num : (0 : ℝ) < 2)).mpr hlt
  have h_exp_neg_2_nn : 0 ≤ Real.exp (-2) := (Real.exp_pos _).le
  have h_exp_neg_2_le1 : Real.exp (-2) ≤ 1 := by
    rw [show (1 : ℝ) = Real.exp 0 from (Real.exp_zero).symm]
    exact Real.exp_le_exp.mpr (by norm_num)
  have h_sum_lt :
      Real.exp (-(r : ℝ)) * ((1 : ℝ) / 2) * Real.exp (-2) + Real.exp (-(r : ℝ)) * Real.exp (-1)
      < Real.exp (-(r : ℝ)) := by
    have hexp_r_pos : 0 < Real.exp (-(r : ℝ)) := Real.exp_pos _
    have h1 : Real.exp (-(r : ℝ)) * ((1 : ℝ) / 2) * Real.exp (-2)
        ≤ Real.exp (-(r : ℝ)) * ((1 : ℝ) / 2) * 1 :=
      mul_le_mul_of_nonneg_left h_exp_neg_2_le1 (by positivity)
    have h2 : Real.exp (-(r : ℝ)) * Real.exp (-1) < Real.exp (-(r : ℝ)) * ((1 : ℝ) / 2) :=
      mul_lt_mul_of_pos_left h_exp_neg_1 hexp_r_pos
    nlinarith [h1, h2, hexp_r_pos]
  linarith [h_piece1_bd, h_piece1_le, h_piece2, h_sum_lt]

/-- Existential-modulus packaging of `relaxation_tracker_convergence_affine`. -/
theorem relaxation_tracker_convergence {β : ℝ} (q : ℚ) {d : ℕ}
    (cbtc : CertifiedBoundedTimeComputable d β) :
    ∃ modulus' : TimeModulus,
      ∀ r : ℕ, ∀ t : ℝ, t > modulus' r →
        |(extendedSolution cbtc q).trajectory t (Fin.last d) - (β + (q : ℝ))|
          < Real.exp (-(r : ℝ)) := by
  obtain ⟨K, hK⟩ := relaxation_tracker_convergence_affine q cbtc
  refine ⟨fun r => max (cbtc.modulus (r+1)) 0 + (r : ℝ) + K, ?_⟩
  exact hK

/-- Discharge the original-form `relaxation_tracker_solution` axiom in terms
of the explicit solution construction. The existence/boundedness parts are
proved; only convergence remains as the narrower axiom above. -/
theorem relaxation_tracker_solution {β : ℝ} (q : ℚ) (_hq : 0 < q) {d : ℕ}
    (cbtc : CertifiedBoundedTimeComputable d β) :
    ∃ (sol' : PIVP.Solution (relaxationPIVP cbtc.pivp q).toPIVP)
      (modulus' : TimeModulus),
      (relaxationPIVP cbtc.pivp q).toPIVP.IsBounded sol'.trajectory ∧
      (∀ r : ℕ, ∀ t : ℝ, t > modulus' r →
        |sol'.trajectory t (Fin.last d) - (β + (q : ℝ))| < Real.exp (-(r : ℝ))) ∧
      Continuous sol'.trajectory := by
  obtain ⟨mod', hconv⟩ := relaxation_tracker_convergence q cbtc
  exact ⟨extendedSolution cbtc q, mod',
    extendedTraj_isBounded cbtc q, hconv,
    extendedSolution_trajectory_continuous cbtc q⟩

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
  obtain ⟨sol', mod', hbd, hconv, hcont⟩ := relaxation_tracker_solution q hq cbtc
  refine ⟨d + 1,
    { pivp := relaxationPIVP cbtc.pivp q
      sol := sol'
      modulus := mod'
      bounded := hbd
      trajectory_continuous := hcont
      convergence := by
        intro r t ht
        show |sol'.trajectory t (relaxationPIVP cbtc.pivp q).output
            - (β + (q : ℝ))| < _
        rw [relaxationPIVP_output]
        exact hconv r t ht },
    relaxationPIVP_polyCRN q (le_of_lt hq) pcd, trivial⟩

/-- **Sharp variant of `certified_add_rational_pos_proved`.** Given an
upstream sharp upper bound `∀ σ ≥ 0, cbtc.sol.trajectory σ cbtc.pivp.output
≤ β`, produce a downstream CBTC for `β + q` whose output trajectory is
also sharply bounded above, by `β + q`. Additionally, when `0 ≤ β` the
output trajectory is non-negative as well. The sharp bound flows via the
Duhamel representation through `trackerTraj_upper_of_outTraj_upper`. -/
theorem certified_add_rational_pos_sharp {β : ℝ} (q : ℚ) (hq : 0 < q)
    (hβ_nn : 0 ≤ β) {d : ℕ}
    (cbtc : CertifiedBoundedTimeComputable d β)
    (pcd : PolyCRNDecomposition d cbtc.pivp)
    (h_sharp_up : ∀ σ, 0 ≤ σ → cbtc.sol.trajectory σ cbtc.pivp.output ≤ β) :
    ∃ (d' : ℕ) (cbtc' : CertifiedBoundedTimeComputable d' (β + (q : ℝ)))
      (_ : PolyCRNDecomposition d' cbtc'.pivp),
      ∀ σ, 0 ≤ σ → cbtc'.sol.trajectory σ cbtc'.pivp.output ≤ β + (q : ℝ) := by
  obtain ⟨mod', hconv⟩ := relaxation_tracker_convergence q cbtc
  refine ⟨d + 1,
    { pivp := relaxationPIVP cbtc.pivp q
      sol := extendedSolution cbtc q
      modulus := mod'
      bounded := extendedTraj_isBounded cbtc q
      trajectory_continuous := extendedSolution_trajectory_continuous cbtc q
      convergence := by
        intro r t ht
        show |(extendedSolution cbtc q).trajectory t
            (relaxationPIVP cbtc.pivp q).output - (β + (q : ℝ))| < _
        rw [relaxationPIVP_output]
        exact hconv r t ht },
    relaxationPIVP_polyCRN q (le_of_lt hq) pcd, ?_⟩
  -- Sharp upper bound on extendedSolution at the output.
  intro σ hσ
  -- The output of the relaxation PIVP is Fin.last d; the extended trajectory
  -- at that index is `trackerTraj cbtc q σ`.
  show (extendedSolution cbtc q).trajectory σ (relaxationPIVP cbtc.pivp q).output
      ≤ β + (q : ℝ)
  rw [relaxationPIVP_output]
  -- extendedSolution.trajectory σ (Fin.last d) = extendedTraj cbtc q σ (Fin.last d)
  --                                            = trackerTraj cbtc q σ
  have h_traj_eq : (extendedSolution cbtc q).trajectory σ (Fin.last d)
      = trackerTraj cbtc q σ := extendedTraj_last cbtc q σ
  rw [h_traj_eq]
  -- Apply trackerTraj_upper_of_outTraj_upper with U = β.
  have h_outTraj_le : ∀ s, 0 ≤ s → s ≤ σ → outTraj cbtc s ≤ β := by
    intro s hs_nn _
    rw [outTraj_of_nonneg cbtc hs_nn]
    exact h_sharp_up s hs_nn
  have h := trackerTraj_upper_of_outTraj_upper cbtc (le_of_lt hq) hβ_nn hσ h_outTraj_le
  linarith

end Algebraic
end Ripple
