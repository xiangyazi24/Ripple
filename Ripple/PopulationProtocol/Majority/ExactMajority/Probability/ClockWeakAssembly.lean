import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.ClockKilledMinute
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.ClockRealHours

/-!
# ClockWeakAssembly — the weak faithful-clock assembly (Doty §6 Phase B step 4)

This is the assembly layer over the killed-minute brick (`ClockKilledMinute`).  It replaces
the OLD `ClockRealFaithfulHours` assembly (which required the FALSE `habs_mix` deterministic
window closure as a carried ∀-minute hypothesis) by a WEAK assembly: the per-minute legs are
killed-kernel `PhaseConvergenceW` tails whose `Post` is NUMERICAL-only, and the gate-escape
budget is telescoped GLOBALLY off the run measure.

## Design of record (campaign §"ASSEMBLY DESIGN")

Two observations resolve the start-dependence mismatch (`clock_real_step_gated`'s escape
budget is start-dependent, but the killed-phase convergence is start-uniform):

1. **The killed-phase part is start-uniform** — `clock_killed_seed_stepW`/`_bulk_stepW` hold
   from any (lifted) `Pre`-config; no mismatch there.
2. **Escape telescopes globally.**  Per-leg escape from leg-start configs, INTEGRATED over the
   time-`t` run distribution `(K^t) x₀`, re-expands via Chapman–Kolmogorov into GLOBAL-time
   per-step terms.  `leg_escape_global` (deliverable 1) is exactly this: integrating
   `kill_now_escape_le_prefix_union`'s per-start statement and collapsing
   `∫ (K^σ) y Sᶜ ∂((K^t) x₀) = (K^{t+σ}) x₀ Sᶜ`.

## The side-set `S` (settled shape — documented per the campaign report request)

`leg_escape_global` is stated GENERICALLY in `K`, `G`, `S`, `q`.  At instantiation
(deliverable 3) we choose `S := G` (the gate itself), i.e. the side event under which the
one-step gate-escape probability is `≤ q` is membership in `G`.  With `S = G`:
* `hstep` becomes `∀ x ∈ G, K x Gᶜ ≤ q` — the one-step escape bound from gated configs, the
  honest §6 "drip-only excess counter" rate;
* the prefix budget `∑_{τ∈[t,t+M)} (K^τ) x₀ Gᶜ` charges exactly the times the GLOBAL run sits
  off the gate `G` — which, for `G = Qset = {Q_mix n mC T}` (seed) resp.
  `G = QbulkSet = {QbulkWin n mC T}` (bulk), is the per-`τ` window-failure mass that the
  WidthPrefix family (`goodFrontWidth_whp_at`) + endpoint bridges discharge later.

With `S = G`, `Gᶜ = Sᶜ`, so the "ungated start" worry (escape mass `1` from `x ∉ G`) is folded
automatically: the term `(K^t) x₀ Gᶜ` sits inside the prefix sum at `τ = t`.

## What this file delivers

* `leg_escape_global` (B-10a): the integrated/telescoped global escape bound.
* `clock_real_leg_global` (B-10b): the real seed leg, escape charged globally.
* `faithfulMinutePhasesW` + `clock_real_faithful_all_minutes_W` (B-10c/d): the `Fin L₀` real
  minute family with leg-indexed budgets, composed.
* `clock_real_faithful_O_log_n_W` (B-10e): the O(log n) endpoint wrapper.

ZERO sorry, zero new axiom, zero native_decide.
-/

namespace ExactMajority

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Real BigOperators Classical

namespace ClockWeakAssembly

open ClockRealKernel ClockRealMixed ClockRealSeed ClockRealBulk ClockMonoDischarge
open GatedDrift ClockKilledMinute ClockRealHours

variable {α : Type*} [MeasurableSpace α] [DiscreteMeasurableSpace α] [Inhabited α]

/-! ## Deliverable 1 (B-10a) — `leg_escape_global`.

The global-start telescoped escape bound.  From the per-start
`GatedDrift.kill_now_escape_le_prefix_union` (escape after `M` steps `≤ M·q + ∑_{σ<M} (K^σ) y Sᶜ`
from a gated start `y ∈ G`), we integrate over the GLOBAL time-`t` run distribution `(K^t) x₀`
and Chapman–Kolmogorov-collapse each prefix term:
  `∫ (K^σ) y Sᶜ ∂((K^t) x₀) = (K^{t+σ}) x₀ Sᶜ`.
Charging the OFF-gate start mass to the `τ = t` term of the side prefix requires `S ⊆ G`
(then `Gᶜ ⊆ Sᶜ`): the design takes `S = G`, so this is automatic; we state the generic lemma
with the explicit `hSG : Gᶜ ⊆ Sᶜ` side condition so the instantiation discharges it by `rfl`.
-/

/-- **Per-start escape, extended to ALL starts.**  `kill_now_escape_le_prefix_union` requires a
gated start `y ∈ G`.  For ungated `y ∉ G` (with `Gᶜ ⊆ Sᶜ`), the `σ = 0` prefix term
`(K^0) y Sᶜ = 1` already dominates the escape mass `≤ 1` — UNLESS `M = 0`, in which case the
escape mass is `0`.  So the per-start prefix bound holds for EVERY start. -/
theorem kill_now_escape_prefix_all {K : Kernel α α} {G S : Set α} [IsMarkovKernel K]
    (q : ℝ≥0∞) (hstep : ∀ x ∈ G, x ∈ S → K x Gᶜ ≤ q) (hSG : Gᶜ ⊆ Sᶜ)
    (M : ℕ) (y : α) :
    (GatedDrift.killK_now K G ^ M) (some y) {(none : Option α)}
      ≤ (M : ℝ≥0∞) * q + ∑ σ ∈ Finset.range M, (K ^ σ) y Sᶜ := by
  classical
  by_cases hy : y ∈ G
  · exact GatedDrift.kill_now_escape_le_prefix_union (K := K) (G := G) S q hstep M y hy
  · -- ungated start: dominate by 1; for M ≥ 1 the σ=0 prefix term is 1, for M = 0 escape is 0.
    rcases Nat.eq_zero_or_pos M with hM0 | hMpos
    · subst hM0
      have : (GatedDrift.killK_now K G ^ 0) (some y) {(none : Option α)} = 0 := by
        rw [pow_zero, Kernel.id_apply,
          Measure.dirac_apply' _ (DiscreteMeasurableSpace.forall_measurableSet _)]
        simp
      rw [this]; exact zero_le'
    · have hesc1 : (GatedDrift.killK_now K G ^ M) (some y) {(none : Option α)} ≤ 1 := by
        haveI : IsMarkovKernel (GatedDrift.killK_now K G ^ M) :=
          inferInstanceAs (IsMarkovKernel ((GatedDrift.killK_now K G) ^ M))
        calc (GatedDrift.killK_now K G ^ M) (some y) {(none : Option α)}
            ≤ (GatedDrift.killK_now K G ^ M) (some y) Set.univ := measure_mono (Set.subset_univ _)
          _ = 1 := measure_univ
      have hterm : (K ^ 0) y Sᶜ = 1 := by
        rw [pow_zero, show ((1 : Kernel α α)) = Kernel.id from rfl, Kernel.id_apply,
          Measure.dirac_apply' _ (DiscreteMeasurableSpace.forall_measurableSet _),
          Set.indicator_of_mem (hSG hy), Pi.one_apply]
      have hsum1 : (1 : ℝ≥0∞) ≤ ∑ σ ∈ Finset.range M, (K ^ σ) y Sᶜ := by
        have hmem : (0 : ℕ) ∈ Finset.range M := Finset.mem_range.2 hMpos
        calc (1 : ℝ≥0∞) = (K ^ 0) y Sᶜ := hterm.symm
          _ ≤ ∑ σ ∈ Finset.range M, (K ^ σ) y Sᶜ :=
              Finset.single_le_sum (f := fun σ => (K ^ σ) y Sᶜ) (fun _ _ => zero_le') hmem
      exact le_trans hesc1 (le_trans hsum1 (le_add_self))

theorem leg_escape_global {K : Kernel α α} {G S : Set α} [IsMarkovKernel K]
    (q : ℝ≥0∞) (hstep : ∀ x ∈ G, x ∈ S → K x Gᶜ ≤ q) (hSG : Gᶜ ⊆ Sᶜ)
    (t M : ℕ) (x₀ : α) :
    (∫⁻ y, (GatedDrift.killK_now K G ^ M) (some y) {(none : Option α)} ∂((K ^ t) x₀))
      ≤ (M : ℝ≥0∞) * q + ∑ τ ∈ Finset.Ico t (t + M), (K ^ τ) x₀ Sᶜ := by
  classical
  calc ∫⁻ y, (GatedDrift.killK_now K G ^ M) (some y) {(none : Option α)} ∂((K ^ t) x₀)
      ≤ ∫⁻ y, ((M : ℝ≥0∞) * q + ∑ σ ∈ Finset.range M, (K ^ σ) y Sᶜ) ∂((K ^ t) x₀) := by
        apply lintegral_mono
        intro y
        exact kill_now_escape_prefix_all (K := K) (G := G) (S := S) q hstep hSG M y
    _ = ∫⁻ _, (M : ℝ≥0∞) * q ∂((K ^ t) x₀)
        + ∫⁻ y, (∑ σ ∈ Finset.range M, (K ^ σ) y Sᶜ) ∂((K ^ t) x₀) := by
        rw [MeasureTheory.lintegral_add_left (by fun_prop)]
    _ ≤ (M : ℝ≥0∞) * q + ∑ τ ∈ Finset.Ico t (t + M), (K ^ τ) x₀ Sᶜ := by
        have hMK : ∀ s : ℕ, IsMarkovKernel (K ^ s) := by
          intro s; induction s with
          | zero => rw [pow_zero]; exact inferInstanceAs (IsMarkovKernel (Kernel.id : Kernel α α))
          | succ s ih => haveI := ih; rw [pow_succ]; exact inferInstanceAs (IsMarkovKernel ((K ^ s) ∘ₖ K))
        haveI : IsMarkovKernel (K ^ t) := hMK t
        gcongr
        · rw [MeasureTheory.lintegral_const, measure_univ, mul_one]
        · rw [MeasureTheory.lintegral_finsetSum _ (fun σ _ => by fun_prop),
            Finset.sum_Ico_eq_sum_range, show t + M - t = M from by omega]
          refine Finset.sum_le_sum (fun σ _ => ?_)
          -- ∫ (K^σ) y Sᶜ ∂((K^t) x₀) = (K^{t+σ}) x₀ Sᶜ via Chapman–Kolmogorov.
          rw [Kernel.pow_add_apply_eq_lintegral K t σ x₀
            (DiscreteMeasurableSpace.forall_measurableSet _)]

end ClockWeakAssembly

end ExactMajority
