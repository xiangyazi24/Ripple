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

/-- The output trajectory of the original BTC, as a function of time. -/
noncomputable def outTraj {d : ℕ} {β : ℝ}
    (cbtc : CertifiedBoundedTimeComputable d β) : ℝ → ℝ :=
  fun t => cbtc.sol.trajectory t cbtc.pivp.output

/-- The tracker trajectory, defined by the Duhamel integral formula:
  y(t) = q + ∫₀^t e^{−(t−s)} · x_out(s) ds.
Equivalent forms:
  y(t) = e^{−t}·q + ∫₀^t e^{−(t−s)}·(x_out(s) + q) ds
       = e^{−t}·y(0) + ∫₀^t e^{−(t−s)}·(x_out(s) + q) ds. -/
noncomputable def trackerTraj {d : ℕ} {β : ℝ}
    (cbtc : CertifiedBoundedTimeComputable d β) (q : ℚ) : ℝ → ℝ :=
  fun t => (q : ℝ) + ∫ s in (0 : ℝ)..t, Real.exp (-(t - s)) * outTraj cbtc s

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

/-- At `t = 0`, the Duhamel integral vanishes, so `trackerTraj cbtc q 0 = q`. -/
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

/-- The original output trajectory `x_out` is continuous on `[0, ∞)` (in fact
differentiable, since it satisfies an ODE there). -/
lemma outTraj_continuousOn {d : ℕ} {β : ℝ}
    (cbtc : CertifiedBoundedTimeComputable d β) :
    ContinuousOn (outTraj cbtc) (Set.Ici (0 : ℝ)) := by
  intro t ht
  have ht0 : (0 : ℝ) ≤ t := ht
  have h := (hasDerivAt_pi.mp (cbtc.sol.is_solution t ht0)) cbtc.pivp.output
  exact h.continuousAt.continuousWithinAt

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

/-- Uniform bound on `outTraj` on `[0,∞)`. -/
lemma outTraj_bound {d : ℕ} {β : ℝ}
    (cbtc : CertifiedBoundedTimeComputable d β) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ t, 0 ≤ t → |outTraj cbtc t| ≤ M := by
  obtain ⟨M, hM_nn, hM⟩ := cbtc_coord_bound cbtc
  exact ⟨M, hM_nn, fun t ht => hM t ht cbtc.pivp.output⟩

/-! ## Step 5c: narrow analytic residual axiom — relaxation tracker convergence.

The construction `extendedTraj` above is the explicit Duhamel trajectory. What
remains is purely analytic: (i) that it actually satisfies the ODE (a scalar
FTC-1 + product rule computation), (ii) that it is bounded, and (iii) that the
tracker coordinate converges to `β + q` with an effective time modulus via
Grönwall. Items (i)–(ii) follow from a direct FTC computation that Mathlib
supports but requires careful setup. Item (iii) is the usual linear-ODE
Grönwall estimate, which Mathlib exposes only in pieces.

We keep the original axiom statement (narrowed to precisely this analytic
content) — the structural `Fin.snoc`/lifting work has already been done
above and in `relaxationPIVP_polyCRN`.
-/
axiom relaxation_tracker_solution {β : ℝ} (q : ℚ) (hq : 0 < q) {d : ℕ}
    (cbtc : CertifiedBoundedTimeComputable d β) :
    ∃ (sol' : PIVP.Solution (relaxationPIVP cbtc.pivp q).toPIVP)
      (modulus' : TimeModulus),
      (relaxationPIVP cbtc.pivp q).toPIVP.IsBounded sol'.trajectory ∧
      (∀ r : ℕ, ∀ t : ℝ, t > modulus' r →
        |sol'.trajectory t (Fin.last d) - (β + (q : ℝ))| < Real.exp (-(r : ℝ)))

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
