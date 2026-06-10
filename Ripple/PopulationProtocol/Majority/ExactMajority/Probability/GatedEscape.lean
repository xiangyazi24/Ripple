import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.GatedGeometricDrift

/-!
# GatedEscape — bounding the killed walk's ESCAPE MASS `(killK^t)(some x){none}`

The gated engine (`GatedGeometricDrift.lean`) bounds real-kernel tails BY the escape
mass (`gated_real_tail`: real tail ≤ `(killK^t)(some x){none}` + drift term), but
nothing bounds the escape mass itself.  This file supplies the generic bound: if every
gated state's one-step probability of LEAVING the gate is at most `η`, the escape mass
after `t` steps is at most `t·η`.

This is the `eB` residual's missing generic piece (the hour-escape
`(killK (markedK T θn) (taintedGate n) ^ (w·KK)) (some mc₀) {none}` of
`windowedFrontProfile_whp_packaged`): the tainted counter rises by at most one per step,
so on the gate (count ≤ threshold) the per-step breach probability is uniformly bounded,
and the escape mass is `horizon · per-step-breach`.

Note the one-step-lag convention of `killK`: a walker at `some x` with `x ∈ G` steps via
`K` into `some y` even when `y ∉ G`; the kill registers at the NEXT step.  The bound
`t·η` absorbs this lag.
-/

namespace ExactMajority

namespace GatedDrift

open MeasureTheory ProbabilityTheory

open scoped ENNReal

variable {α : Type*} [MeasurableSpace α] [DiscreteMeasurableSpace α] [Inhabited α]

local instance instOptionMS' : MeasurableSpace (Option α) := ⊤
local instance instOptionDMS' : DiscreteMeasurableSpace (Option α) := ⟨fun _ => trivial⟩

variable {K : Kernel α α} {G : Set α}

/-- For an ungated state `some y` (`y ∉ G`), the killed walk is at the cemetery from the
next step on: `(killK^t)(some y){none} = 1` for `1 ≤ t`. -/
theorem killed_none_of_ungated [IsMarkovKernel K] (y : α) (hy : y ∉ G) (t : ℕ)
    (ht : 1 ≤ t) :
    (killK K G ^ t) (some y) {(none : Option α)} = 1 := by
  classical
  obtain ⟨s, rfl⟩ : ∃ s, t = 1 + s := ⟨t - 1, by omega⟩
  have hdead : killK K G (some y) = Measure.dirac (none : Option α) := by
    unfold killK
    rw [Kernel.piecewise_apply, if_neg (fun h => hy ((some_mem_image_iff y).1 h)),
      Kernel.const_apply]
  rw [Kernel.pow_add_apply_eq_lintegral (killK K G) 1 s (some y)
      (DiscreteMeasurableSpace.forall_measurableSet _), pow_one, hdead,
    MeasureTheory.lintegral_dirac' _ (Measurable.of_discrete), none_absorbing s,
    Measure.dirac_apply' _ (DiscreteMeasurableSpace.forall_measurableSet _)]
  simp

/-- **The escape-mass bound.**  If every gated state leaves the gate in one `K`-step with
probability at most `η` (`hesc`), then from a gated start the killed walk's cemetery mass
after `t` steps is at most `t·η`:

  `(killK^t)(some x₀){none} ≤ t·η`.

Induction on `t`; per step, the alive-and-gated mass pays at most `η` for stepping out of
`G`, the already-ungated mass was paid for at the step that produced it. -/
theorem killed_none_mass_le [IsMarkovKernel K] (η : ℝ≥0∞)
    (hesc : ∀ x ∈ G, K x Gᶜ ≤ η) (t : ℕ) (x₀ : α) (hx₀ : x₀ ∈ G) :
    (killK K G ^ t) (some x₀) {(none : Option α)} ≤ (t : ℝ≥0∞) * η := by
  classical
  induction t generalizing x₀ with
  | zero =>
      rw [pow_zero]
      have hid : (Kernel.id : Kernel (Option α) (Option α)) (some x₀)
          {(none : Option α)} = 0 := by
        rw [Kernel.id_apply,
          Measure.dirac_apply' _ (DiscreteMeasurableSpace.forall_measurableSet _)]
        simp
      calc ((1 : Kernel (Option α) (Option α))) (some x₀) {(none : Option α)}
          = 0 := hid
        _ ≤ ((0 : ℕ) : ℝ≥0∞) * η := zero_le'
  | succ t ih =>
      have hCK : (killK K G ^ (t + 1)) (some x₀) {(none : Option α)}
          = ∫⁻ o, (killK K G ^ t) o {(none : Option α)} ∂(killK K G (some x₀)) := by
        rw [show t + 1 = 1 + t from by ring,
          Kernel.pow_add_apply_eq_lintegral (killK K G) 1 t (some x₀)
            (DiscreteMeasurableSpace.forall_measurableSet _), pow_one]
      rw [hCK, killK_some_gated (K := K) (G := G) x₀ hx₀,
        MeasureTheory.lintegral_map (Measurable.of_discrete) (Measurable.of_discrete)]
      -- ∫⁻ y, (killK^t)(some y){none} ∂(K x₀) split over G / Gᶜ.
      have hmeasG : MeasurableSet G := DiscreteMeasurableSpace.forall_measurableSet _
      rw [← lintegral_add_compl
        (fun y => (killK K G ^ t) (some y) {(none : Option α)}) hmeasG]
      have hbound1 : ∫⁻ y in G, (killK K G ^ t) (some y) {(none : Option α)} ∂(K x₀)
          ≤ (t : ℝ≥0∞) * η := by
        calc ∫⁻ y in G, (killK K G ^ t) (some y) {(none : Option α)} ∂(K x₀)
            ≤ ∫⁻ _ in G, (t : ℝ≥0∞) * η ∂(K x₀) := by
              apply lintegral_mono_ae
              filter_upwards [ae_restrict_mem hmeasG] with y hy
              exact ih y hy
          _ = ((t : ℝ≥0∞) * η) * (K x₀) G := by
              rw [lintegral_const, Measure.restrict_apply_univ]
          _ ≤ ((t : ℝ≥0∞) * η) * 1 := by
              gcongr
              calc (K x₀) G ≤ (K x₀) Set.univ := measure_mono (Set.subset_univ G)
                _ = 1 := measure_univ
          _ = (t : ℝ≥0∞) * η := mul_one _
      have hbound2 : ∫⁻ y in Gᶜ, (killK K G ^ t) (some y) {(none : Option α)} ∂(K x₀)
          ≤ η := by
        calc ∫⁻ y in Gᶜ, (killK K G ^ t) (some y) {(none : Option α)} ∂(K x₀)
            ≤ ∫⁻ _ in Gᶜ, (1 : ℝ≥0∞) ∂(K x₀) := by
              apply lintegral_mono_ae
              filter_upwards with y
              calc (killK K G ^ t) (some y) {(none : Option α)}
                  ≤ (killK K G ^ t) (some y) Set.univ := measure_mono (Set.subset_univ _)
                _ ≤ 1 := by
                    haveI : ∀ s : ℕ, IsMarkovKernel ((killK K G) ^ s) := by
                      intro s
                      induction s with
                      | zero =>
                          rw [pow_zero]
                          exact inferInstanceAs
                            (IsMarkovKernel (Kernel.id : Kernel (Option α) (Option α)))
                      | succ s ihs =>
                          haveI := ihs
                          rw [pow_succ]
                          exact inferInstanceAs
                            (IsMarkovKernel (((killK K G) ^ s) ∘ₖ (killK K G)))
                    haveI := this t
                    rw [measure_univ]
          _ = (K x₀) Gᶜ := by
              rw [lintegral_const, Measure.restrict_apply_univ, one_mul]
          _ ≤ η := hesc x₀ hx₀
      calc (∫⁻ y in G, (killK K G ^ t) (some y) {(none : Option α)} ∂(K x₀)) +
            (∫⁻ y in Gᶜ, (killK K G ^ t) (some y) {(none : Option α)} ∂(K x₀))
          ≤ (t : ℝ≥0∞) * η + η := add_le_add hbound1 hbound2
        _ = ((t : ℝ≥0∞) + 1) * η := by ring
        _ = ((t + 1 : ℕ) : ℝ≥0∞) * η := by
            congr 1
            push_cast
            ring

/-- **The fully-bounded gated real tail.**  Combining the escape-mass bound with
`gated_real_tail`: with a uniform per-step gate-leaving bound `η` on `G` and the drift
`r` on `G`, the REAL-kernel tail at the final potential is

  `(K^t) x {θ ≤ Φ} ≤ t·η + r^t·Φ x/θ`

— no killed-kernel quantity left in the statement. -/
theorem gated_real_tail_full [IsMarkovKernel K] (Φ : α → ℝ≥0∞) (r : ℝ≥0∞) (hr : 1 ≤ r)
    (hdrift_G : ∀ x ∈ G, ∫⁻ y, Φ y ∂(K x) ≤ r * Φ x)
    (η : ℝ≥0∞) (hesc : ∀ x ∈ G, K x Gᶜ ≤ η)
    (t : ℕ) (x : α) (hx : x ∈ G) (θ : ℝ≥0∞) (hθ0 : θ ≠ 0) (hθtop : θ ≠ ∞) :
    (K ^ t) x {y | θ ≤ Φ y} ≤ (t : ℝ≥0∞) * η + r ^ t * Φ x / θ := by
  refine le_trans (gated_real_tail (K := K) (G := G) Φ r hr hdrift_G t x θ hθ0 hθtop) ?_
  exact add_le_add (killed_none_mass_le η hesc t x hx) le_rfl

end GatedDrift

end ExactMajority
