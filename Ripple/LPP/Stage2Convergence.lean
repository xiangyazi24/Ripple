/-
  Ripple.LPP.Stage2Convergence — Remark 14 replacement for `stage2_convergence_axiom`.

  Purpose: discharge `stage2_convergence_axiom` (used in `Stages.lean`'s
  `stage2_ode_axiom`) by the argument of [LPP, Remark 14]:

    * x₀(0) = 1, and on the simplex (∑ᵢ zᵢ = 1),
      z₀(s) = 1 - y_o(τ(s)) - c·∑_{j≠o} y_j(τ(s)).
    * If the BTC trajectory satisfies the "room" condition
          y_o(s) + c·∑_{j≠o} y_j(s) ≤ 1 - c_room   for all s ≥ 0,
      then z₀(s) ≥ c_room along the Stage 2 orbit — WITHOUT monotonicity.
    * Combined with `stage2_convergence_from_z0_invariant`, this closes
      the axiom.

  Status
  ------
  The reparametrization identity `stage2_output_eq_btc_output_at_tau` lives in
  `Stages.lean` but is FINITE-T (requires explicit bounds `M, L` on the
  window `[0, T]`). Remark 14 needs the ∀ s ≥ 0 version. The extension is
  packaged here as `stage2_unscaledTail_eq_btcTraj_comp_tau_global`.

  Caller responsibility. The "room" condition must be supplied by an upstream
  refinement of the BTC (e.g. a CRN on the simplex with bounded tail mass).
  A matching strengthened BTC for the algebraic pipeline is expected to live
  in `Ripple.LPP.AlgebraicConstruction` once this chain is in place.

  NO custom axioms beyond those already declared in Stages.lean.
-/

import Ripple.LPP.Stages

namespace Ripple

open scoped Topology

/-! ## Remark 14 step 1 — algebraic expression for `z₀` in reparam coordinates

On the Stage 2 simplex (`∑ᵢ sol(s)ᵢ = 1`), the 0-th coordinate `z₀(s)`
is determined by the tail:

  z₀(s) = 1 - ∑_{j : Fin d} sol(s)_{j.succ}
        = 1 - c · (unscaledTail s)_o - c · ∑_{j≠o} (unscaledTail s)_j + (1-c)·(unscaledTail s)_o

The λ-trick leaves the output coordinate unscaled (`selectiveUnscale o c · o = ·o`),
so `sol(s)_{o.succ} = (unscaledTail s)_o`, and for `j ≠ o`,
`sol(s)_{j.succ} = c · (unscaledTail s)_j`. -/

/-- Simplex decomposition of `z₀` using the λ-trick structure.

On the Stage 2 simplex, `z₀(s) = 1 - w_o(s) - c·∑_{j≠o} w_j(s)` where
`w = selectiveUnscale o c (tail sol)` and `o = btc.pivp.output`.

Pure algebraic identity — no ODE content. -/
theorem stage2_z0_eq_unscaledTail_sum {d : ℕ} [NeZero d] {α ε c : ℝ} (hc : c ≠ 0)
    {btc : BoundedTimeComputable d α}
    (sol : PIVP.Solution (stage2_pivp ε c btc.pivp))
    (s : ℝ) (_hs : 0 ≤ s)
    (h_sum : ∑ i, sol.trajectory s i = 1) :
    sol.trajectory s 0
      = 1 - selectiveUnscale btc.pivp.output c (Fin.tail (sol.trajectory s))
              btc.pivp.output
        - c * ∑ j ∈ Finset.univ.erase btc.pivp.output,
              selectiveUnscale btc.pivp.output c
                (Fin.tail (sol.trajectory s)) j := by
  -- Step 1: use conservation to move z₀ to the other side.
  have h_z0_eq : sol.trajectory s 0 = 1 - ∑ j : Fin d, sol.trajectory s j.succ := by
    have : sol.trajectory s 0 + ∑ j : Fin d, sol.trajectory s j.succ
        = ∑ i, sol.trajectory s i := by
      rw [Fin.sum_univ_succ]
    linarith [this, h_sum]
  rw [h_z0_eq]
  -- Step 2: split the tail sum by the λ-trick.
  -- At the output index o: sol(s)_{o.succ} = tail sol_o = unscale·o = w·o.
  -- At j ≠ o: sol(s)_{j.succ} = tail sol_j = c · w·j.
  set w := selectiveUnscale btc.pivp.output c (Fin.tail (sol.trajectory s))
    with hw_def
  have h_tail_o : sol.trajectory s btc.pivp.output.succ = w btc.pivp.output := by
    simp [hw_def, Fin.tail, selectiveUnscale_output]
  have h_tail_ne : ∀ j ≠ btc.pivp.output,
      sol.trajectory s j.succ = c * w j := by
    intro j hj
    have : Fin.tail (sol.trajectory s) j = sol.trajectory s j.succ := rfl
    rw [hw_def, selectiveUnscale_ne hj]
    simp only [Fin.tail]
    field_simp
  -- Step 3: rearrange the finite sum.
  have h_sum_split : ∑ j : Fin d, sol.trajectory s j.succ
      = w btc.pivp.output + ∑ j ∈ Finset.univ.erase btc.pivp.output, c * w j := by
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ btc.pivp.output)]
    rw [h_tail_o]
    rw [add_comm]
    congr 1
    apply Finset.sum_congr rfl
    intro j hj
    exact h_tail_ne j (Finset.mem_erase.mp hj).1
  rw [h_sum_split]
  rw [Finset.mul_sum]
  ring

/-! ## Remark 14 step 2 — `z₀ ≥ c_room` from a BTC room condition

Given the reparametrization identity `w(s) = btc.sol(τ(s))`, if the BTC
trajectory satisfies `y_o(σ) + c·∑_{j≠o} y_j(σ) ≤ 1 - c_room` for all σ ≥ 0,
then `z₀(s) ≥ c_room` for all s in the window where the reparam identity
holds.

This lemma is *local* — it takes the reparam identity as a hypothesis on
`[0, T]`. The global version (using the extended reparam identity) is
`stage2_z0_lb_from_btc_room_global`. -/

/-- Local z₀ lower bound from the BTC room condition and reparametrization.

Hypotheses:
  * `h_room`: the input BTC satisfies `y_o(σ) + c·∑_{j≠o} y_j(σ) ≤ 1 - c_room`
    for every `σ ≥ 0`.
  * `h_reparam`: on `[0, T]`, the Stage 2 unscaled tail equals `btc.sol ∘ τ`.
  * `h_sum`: simplex conservation of `sol` on `[0, T]`.
  * `h_τ_nn`: `τ(s) ≥ 0` on `[0, T]`.

Conclusion: `z₀(s) ≥ c_room` on `[0, T]`. -/
theorem stage2_z0_lb_from_btc_room_local
    {d : ℕ} [NeZero d] {α : ℝ} {ε c c_room : ℝ} (hc : c ≠ 0)
    {btc : BoundedTimeComputable d α}
    (sol : PIVP.Solution (stage2_pivp ε c btc.pivp))
    (h_room : ∀ σ, 0 ≤ σ →
      btc.sol.trajectory σ btc.pivp.output
        + c * ∑ j ∈ Finset.univ.erase btc.pivp.output,
              btc.sol.trajectory σ j ≤ 1 - c_room)
    (T : ℝ) (hT : 0 ≤ T)
    (h_reparam : Set.EqOn
      (fun s => selectiveUnscale btc.pivp.output c (Fin.tail (sol.trajectory s)))
      (fun s => btc.sol.trajectory (stage2_effectiveTime sol s))
      (Set.Icc (0 : ℝ) T))
    (h_sum : ∀ s, 0 ≤ s → ∑ i, sol.trajectory s i = 1)
    (h_τ_nn : ∀ s, 0 ≤ s → 0 ≤ stage2_effectiveTime sol s) :
    ∀ s ∈ Set.Icc (0 : ℝ) T, c_room ≤ sol.trajectory s 0 := by
  intro s hs
  -- Decompose z₀ via the simplex identity.
  rw [stage2_z0_eq_unscaledTail_sum hc sol s hs.1 (h_sum s hs.1)]
  -- Substitute the reparametrization identity.
  have h_eq := h_reparam hs
  -- Apply componentwise: at output and at each j ≠ output.
  have h_eq_o : selectiveUnscale btc.pivp.output c
      (Fin.tail (sol.trajectory s)) btc.pivp.output
        = btc.sol.trajectory (stage2_effectiveTime sol s) btc.pivp.output := by
    exact congrFun h_eq btc.pivp.output
  have h_eq_j : ∀ j ∈ Finset.univ.erase btc.pivp.output,
      selectiveUnscale btc.pivp.output c (Fin.tail (sol.trajectory s)) j
        = btc.sol.trajectory (stage2_effectiveTime sol s) j := by
    intro j _
    exact congrFun h_eq j
  rw [h_eq_o]
  rw [Finset.sum_congr rfl h_eq_j]
  -- Apply the room condition at σ = τ(s).
  have h_room_at := h_room _ (h_τ_nn s hs.1)
  linarith

/-! ## Remark 14 step 3 — global extension (still open)

`stage2_output_eq_btc_output_at_tau` (in Stages.lean) gives the reparam
identity on `[0, T]` conditioned on finite bounds `M, L`. To lift it to
`[0, ∞)`, we need `M` and `L` to hold uniformly in `T`. Two natural routes:

  (a) Use `btc.bounded` to get a global `M_btc` on `btc.sol`, then use the
      simplex bound `‖sol(s)‖ ≤ 1` on `sol` to bound the unscaled tail by
      `1/c`. The Lipschitz constant `L` of `btc.pivp.field` on `closedBall 0 M`
      for `M = max(M_btc, 1/c)` is finite by `quadraticForm_locally_lipschitz`
      (`A, B` decomposition). This is essentially the scaffolding inside
      `stage2_convergence_from_z0_invariant`.

  (b) Simply quantify the `[0, T]` version over `T` and collect the pointwise
      conclusion at each `s` using `T := s + 1`.

Route (b) is lighter. It's the same pattern as `pivp_solution_nonneg` in
Stages.lean. Kept as `sorry` until wired. -/

/-- Global reparametrization identity (Remark 14 step 3).

The unscaled tail of the Stage 2 solution equals `btc.sol ∘ τ` for all
`s ≥ 0`. Follows from the finite-T version `stage2_output_eq_btc_output_at_tau`
by taking `T := s + 1` and using `btc.bounded` + `quadraticForm_locally_lipschitz`
to supply uniform `M, L`. -/
theorem stage2_unscaledTail_eq_btcTraj_comp_tau_global
    {d : ℕ} [NeZero d] {α : ℝ} {ε c : ℝ}
    (hε : 0 < ε) (hc : 0 < c) (hc1 : c ≤ 1)
    {btc : BoundedTimeComputable d α}
    (A : Fin d → Fin d → Fin d → ℝ) (B : Fin d → Fin d → ℝ)
    (h_field : ∀ i x, btc.pivp.field x i =
      (∑ a, ∑ b, A i a b * x a * x b) - (∑ a, B i a * x a) * x i)
    (sol : PIVP.Solution (stage2_pivp ε c btc.pivp))
    (h_sol_nn : ∀ s, 0 ≤ s → ∀ i, 0 ≤ sol.trajectory s i)
    (h_sol_sum : ∀ s, 0 ≤ s → ∑ i, sol.trajectory s i = 1)
    (h_zero_init : btc.pivp.init btc.pivp.output = 0) :
    ∀ s, 0 ≤ s →
      selectiveUnscale btc.pivp.output c (Fin.tail (sol.trajectory s))
        = btc.sol.trajectory (stage2_effectiveTime sol s) := by
  sorry

/-! ## Remark 14 step 4 — main theorem replacing `stage2_convergence_axiom` -/

/-- **Remark 14 replacement for `stage2_convergence_axiom`**.

Given the "room" condition on the input BTC's trajectory — which cannot be
derived from `btc.bounded` alone but IS a property of CRNs designed on the
simplex — this theorem discharges the Stage 2 convergence with NO new axiom
or monotonicity assumption.

Hypotheses beyond those of `stage2_convergence_axiom`:
  * `hc1 : c ≤ 1` (pins `c ∈ (0, 1]` given `0 < c`)
  * `A, B`: the BTC's explicit quadratic CRN decomposition
  * `h_sol_nn, h_sol_sum`: CRN invariance of the Stage 2 solution (nonneg + simplex)
  * `h_zero_init`: `btc.pivp.init o = 0` — the DNA 25 normalization
  * `h_room`: **the Remark 14 room condition on the BTC trajectory**. -/
theorem stage2_convergence_from_room
    {d : ℕ} [NeZero d] {α : ℝ} {ε c c_room : ℝ}
    (hε : 0 < ε) (hc : 0 < c) (hc1 : c ≤ 1) (hεc : 1 ≤ ε * c)
    (hc_room_pos : 0 < c_room) (hc_room_le_c : c_room ≤ c)
    {btc : BoundedTimeComputable d α}
    (A : Fin d → Fin d → Fin d → ℝ) (B : Fin d → Fin d → ℝ)
    (h_field : ∀ i x, btc.pivp.field x i =
      (∑ a, ∑ b, A i a b * x a * x b) - (∑ a, B i a * x a) * x i)
    (sol : PIVP.Solution (stage2_pivp ε c btc.pivp))
    (h_sol_nn : ∀ s, 0 ≤ s → ∀ i, 0 ≤ sol.trajectory s i)
    (h_sol_sum : ∀ s, 0 ≤ s → ∑ i, sol.trajectory s i = 1)
    (h_zero_init : btc.pivp.init btc.pivp.output = 0)
    (h_room : ∀ σ, 0 ≤ σ →
      btc.sol.trajectory σ btc.pivp.output
        + c * ∑ j ∈ Finset.univ.erase btc.pivp.output,
              btc.sol.trajectory σ j ≤ 1 - c_room) :
    ∀ r : ℕ, ∀ t : ℝ, 0 ≤ t → t > btc.modulus r →
      |sol.trajectory t (stage2_pivp ε c btc.pivp).output - α| <
        Real.exp (-(r : ℝ)) := by
  intro r t ht_nn ht_gt
  -- Step 1: get the global reparametrization identity.
  have h_reparam_global := stage2_unscaledTail_eq_btcTraj_comp_tau_global
    hε hc hc1 A B h_field sol h_sol_nn h_sol_sum h_zero_init
  -- Step 2: τ(s) ≥ 0 from z₀ ≥ 0 (simplex).
  have h_z0_nn : ∀ s, 0 ≤ s → 0 ≤ sol.trajectory s 0 := fun s hs =>
    h_sol_nn s hs 0
  have h_τ_nn : ∀ s, 0 ≤ s → 0 ≤ stage2_effectiveTime sol s := fun s hs =>
    stage2_effectiveTime_nonneg hε.le sol h_z0_nn s hs
  -- Step 3: restate reparam identity as a local Set.EqOn and apply room lemma.
  have h_reparam_local : Set.EqOn
      (fun s => selectiveUnscale btc.pivp.output c (Fin.tail (sol.trajectory s)))
      (fun s => btc.sol.trajectory (stage2_effectiveTime sol s))
      (Set.Icc (0 : ℝ) t) := fun s hs => h_reparam_global s hs.1
  have h_z0_lb_local := stage2_z0_lb_from_btc_room_local
    (ne_of_gt hc) sol h_room t ht_nn h_reparam_local h_sol_sum h_τ_nn
  -- Step 4: c_room ≤ z₀(s) for all s ∈ [0, t]. Extend via the same argument
  -- pointwise: for each s ≥ 0, apply the local lemma with T := s. Hence a
  -- GLOBAL h_z0_lb with `c_room` (not `c`).
  have h_z0_lb : ∀ s, 0 ≤ s → c_room ≤ sol.trajectory s 0 := by
    intro s hs
    have h_local : Set.EqOn
        (fun u => selectiveUnscale btc.pivp.output c (Fin.tail (sol.trajectory u)))
        (fun u => btc.sol.trajectory (stage2_effectiveTime sol u))
        (Set.Icc (0 : ℝ) s) := fun u hu => h_reparam_global u hu.1
    exact stage2_z0_lb_from_btc_room_local
      (ne_of_gt hc) sol h_room s hs h_local h_sol_sum h_τ_nn s ⟨hs, le_refl _⟩
  -- Step 5: apply `stage2_convergence_from_z0_invariant` with c := c_room.
  -- But that theorem needs `ε·c_room ≥ 1`, which is STRONGER than `ε·c ≥ 1`.
  -- Option: instead of piping c_room through, use the `c ≤ z₀` lower bound
  -- (since c_room ≤ c and z₀ ≥ c_room implies nothing about z₀ ≥ c directly).
  --
  -- The cleanest route: use the effective-time lower bound `τ(t) ≥ ε·c_room·t`
  -- and require `ε·c_room ≥ 1`. That's why we add `hc_room_le_c` and NOT a
  -- bound relating `c_room` to `ε·c`. For the algebraic pipeline we can
  -- arrange `c_room = c` (take the room condition tight), closing this gap.
  sorry

/-! ## Summary

The Remark 14 chain is now scaffolded. Remaining proof obligations:

  1. `stage2_unscaledTail_eq_btcTraj_comp_tau_global` — extend the finite-T
     reparam identity to `[0, ∞)` via pointwise `T := s + 1` argument,
     supplying `M, L` from `btc.bounded` + `quadraticForm_locally_lipschitz`.

  2. Final composition of `stage2_convergence_from_room` — either
     strengthen `hεc` to `1 ≤ ε·c_room`, OR tighten the room condition so
     `c_room = c`. For algebraic btc from `AlgebraicConstruction`, the
     latter is expected to be achievable.

  3. Caller discharging `h_room`: requires strengthening the algebraic BTC
     construction to guarantee simplex-room behavior. Open task downstream. -/

end Ripple
