/-
  Ripple.Core.GlobalPicard — Global existence for scalar ODEs with
  globally Lipschitz, a-priori bounded fields.

  Mathlib's Picard-Lindelöf theorem gives *local* existence of solutions to
  ODEs on a small interval `[t₀ - ε, t₀ + ε]`.  For CRN / PIVP applications
  we need *global* (on `[0, ∞)`) existence.

  The file `Ripple.Core.ODEGlobal` contains a proven vector-valued version
  (`locally_lipschitz_bounded_global_ode_proved_continuous`) for fields on
  `Fin d → ℝ`.  This module re-exports the scalar specialization, which is
  sufficient for the Dottie number trajectory (where the underlying
  dynamics is really a scalar ODE `x' = cos x − x`).

  Main theorem
  ------------
  `scalar_global_existence`:  given a scalar field `v : ℝ → ℝ` that is
  globally Lipschitz and an a-priori bound `|y(t)| ≤ M` holding for every
  local solution on every `[0, T)`, there exists a global solution
  `x : ℝ → ℝ` with `x 0 = x₀`, and `x` is continuous on `ℝ`.

  This is a thin wrapper around
  `Ripple.locally_lipschitz_bounded_global_ode_proved_continuous` applied
  at dimension `d = 1` (with the isomorphism `ℝ ≃ (Fin 1 → ℝ)`).
-/

import Ripple.Core.ODEGlobal

open Set

namespace Ripple

/-! ## Scalar wrapper

We view a scalar field `v : ℝ → ℝ` as a vector field on `Fin 1 → ℝ` via
`vvec y := fun _ => v (y 0)`.  The global-existence machinery then works
at `d = 1` and we extract the scalar solution.
-/

namespace GlobalPicard

/-- Pack a scalar value into `Fin 1 → ℝ`. -/
@[simp] noncomputable def pack (x : ℝ) : Fin 1 → ℝ := fun _ => x

/-- Unpack `Fin 1 → ℝ` to a scalar. -/
@[simp] noncomputable def unpack (y : Fin 1 → ℝ) : ℝ := y 0

@[simp] lemma unpack_pack (x : ℝ) : unpack (pack x) = x := rfl

lemma pack_unpack (y : Fin 1 → ℝ) : pack (unpack y) = y := by
  ext i
  fin_cases i
  rfl

/-- `‖pack x‖ = |x|` for the sup norm on `Fin 1 → ℝ`. -/
lemma norm_pack (x : ℝ) : ‖pack x‖ = |x| := by
  have h1 : ‖pack x‖ ≤ |x| := by
    rw [pi_norm_le_iff_of_nonneg (abs_nonneg x)]
    intro i
    fin_cases i
    simp [pack, Real.norm_eq_abs]
  have h2 : |x| ≤ ‖pack x‖ := by
    have := norm_le_pi_norm (pack x) (0 : Fin 1)
    simpa [pack, Real.norm_eq_abs] using this
  linarith

lemma norm_eq_abs_unpack (y : Fin 1 → ℝ) : ‖y‖ = |y 0| := by
  conv_lhs => rw [← pack_unpack y]
  exact norm_pack (y 0)

/-- `HasDerivAt` for a `Fin 1 → ℝ`-valued function reduces to `HasDerivAt`
of its scalar component (since `Fin 1 → ℝ ≃ ℝ`). -/
lemma hasDerivAt_pack_iff {x : ℝ → ℝ} {v : ℝ} {t : ℝ} :
    HasDerivAt (fun s => pack (x s)) (pack v) t ↔ HasDerivAt x v t := by
  constructor
  · intro h
    have : HasDerivAt (fun s => (pack (x s)) 0) ((pack v) 0) t :=
      (hasDerivAt_pi.mp h) 0
    simpa [pack] using this
  · intro h
    apply hasDerivAt_pi.mpr
    intro i
    fin_cases i
    simpa [pack] using h

end GlobalPicard

open GlobalPicard

/-- **Scalar global existence from global Lipschitz + a priori bound.**
Given a scalar field `v : ℝ → ℝ` that is (uniformly) Lipschitz on every
ball, and an a priori bound `M` such that every local solution of the ODE
`x' = v(x)`, `x(0) = x₀`, is bounded by `M` on any `[0, T)`, there exists
a global solution `x : ℝ → ℝ` that is continuous on `ℝ`. -/
theorem scalar_global_existence
    (v : ℝ → ℝ) (x₀ : ℝ)
    (h_lip : ∀ R : ℝ, 0 < R → ∃ L : ℝ, ∀ x y : ℝ,
      |x| ≤ R → |y| ≤ R → |v x - v y| ≤ L * |x - y|)
    (M : ℝ) (hM : 0 < M)
    (h_invariant : ∀ (T : ℝ), 0 < T → ∀ (x : ℝ → ℝ),
      x 0 = x₀ →
      (∀ t ∈ Ico (0 : ℝ) T, HasDerivAt x (v (x t)) t) →
      ∀ t ∈ Ico (0 : ℝ) T, |x t| ≤ M) :
    ∃ x : ℝ → ℝ, x 0 = x₀ ∧
      (∀ t : ℝ, 0 ≤ t → HasDerivAt x (v (x t)) t) ∧ Continuous x := by
  -- Build the vector field on `Fin 1 → ℝ`.
  let f : (Fin 1 → ℝ) → Fin 1 → ℝ := fun y => pack (v (y 0))
  let y₀ : Fin 1 → ℝ := pack x₀
  -- Translate Lipschitz hypothesis to vector form.
  have h_lip_vec : ∀ R : ℝ, 0 < R → ∃ L : ℝ, ∀ x y : Fin 1 → ℝ,
      ‖x‖ ≤ R → ‖y‖ ≤ R → ‖f x - f y‖ ≤ L * ‖x - y‖ := by
    intro R hR
    obtain ⟨L, hL⟩ := h_lip R hR
    refine ⟨L, ?_⟩
    intro a b ha hb
    rw [norm_eq_abs_unpack] at ha hb
    have hab : |v (a 0) - v (b 0)| ≤ L * |a 0 - b 0| := hL _ _ ha hb
    rw [show (f a - f b) = pack (v (a 0) - v (b 0)) from ?_, norm_pack,
        show (a - b) = pack (a 0 - b 0) from ?_, norm_pack]
    · linarith [hab]
    · ext i; fin_cases i; simp [pack]
    · ext i; fin_cases i; simp [pack, f]
  -- Translate invariance hypothesis to vector form.
  have h_inv_vec : ∀ (T : ℝ), 0 < T → ∀ (y : ℝ → Fin 1 → ℝ),
      y 0 = y₀ →
      (∀ t ∈ Ico (0 : ℝ) T, HasDerivAt y (f (y t)) t) →
      ∀ t ∈ Ico (0 : ℝ) T, ‖y t‖ ≤ M := by
    intro T hT y hy0 hode t ht
    -- Define scalar solution x(t) := y(t) 0
    let x : ℝ → ℝ := fun t => y t 0
    have hx0 : x 0 = x₀ := by
      show y 0 0 = x₀
      rw [hy0]; rfl
    have hx_deriv : ∀ t ∈ Ico (0 : ℝ) T, HasDerivAt x (v (x t)) t := by
      intro s hs
      have h := (hasDerivAt_pi.mp (hode s hs)) 0
      change HasDerivAt x (f (y s) 0) s at h
      simpa [f, pack, x] using h
    have hx_bound : |x t| ≤ M := h_invariant T hT x hx0 hx_deriv t ht
    rw [norm_eq_abs_unpack]
    exact hx_bound
  -- Apply the vector-valued global existence theorem.
  obtain ⟨y, hy0, hy_deriv, hy_cont⟩ :=
    locally_lipschitz_bounded_global_ode_proved_continuous f y₀ h_lip_vec M hM h_inv_vec
  refine ⟨fun t => y t 0, ?_, ?_, ?_⟩
  · show y 0 0 = x₀
    rw [hy0]; rfl
  · intro t ht
    have h := (hasDerivAt_pi.mp (hy_deriv t ht)) 0
    change HasDerivAt (fun s => y s 0) (f (y t) 0) t at h
    simpa [f, pack] using h
  · exact (continuous_apply 0).comp hy_cont

end Ripple
