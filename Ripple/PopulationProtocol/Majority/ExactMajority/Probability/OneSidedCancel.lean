/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Generic one-sided cancellation engine (Doty §6, Phases 7 & 8)

A reusable, protocol-agnostic engine for the **one-sided elimination** arguments
the blueprint assigns to Phases 7 and 8 (and reusable for Phase-5-style "everyone
gets hit" arguments).  The paper template is Doty et al. Lemma 4.7:

> A subpopulation `A` maintains its size above `a·n` (the **eliminators**), while a
> subpopulation `B` of targets is drained: every `A`-`B` interaction forces one
> agent in `B` to leave (a one-sided cancel reaction `a, b → a, 0`).  After
> `i` cancel reactions `|B| = b₁·n − i`; the time until `B` reaches `0` is whp
> `O(n log n)`.

We package this entirely in the existing kernel-power / `ℝ≥0∞` language.  We model
the target count by an abstract potential `Φ : Config → ℕ` (the size of `B`), and
the eliminator pool by a per-step **drop probability** lower bound carried by an
invariant `Inv` (the floor `|A| ≥ a·n`).  Two whp tails are delivered:

* **Form (b) — crude uniform.**  When `Φ ≥ 1`, a single interaction drains a target
  with probability `≥ 1 − q` (`q = 1 − eFloor/(n(n−1))`-shape).  A single geometric
  gives `(K^t) c {1 ≤ Φ} ≤ q^t`.  Horizon `t = Θ(n²)`; cheap fallback.  Packaged as
  `oneSidedCancel_crude_PhaseConvergenceW`.

* **Form (a) — level-decomposed (paper-faithful `O(n log n)`).**  Per target-level
  `m`, the drop rate is `eFloor·m/(n(n−1))`-shape, so the level-`m` window drains
  geometrically at its own (faster, level-dependent) rate.  Splitting the horizon
  `T = ∑_{m} t_m` into per-level windows and union-bounding gives
  `(K^T) c {1 ≤ Φ} ≤ ∑_{m=1}^{M₀} q_m ^ {t_m}`, the coupon-collector tail.  Packaged
  as `oneSidedCancel_levels_PhaseConvergenceW`.

Both reuse the invariant-relative level machinery from `Phase10ExpectedTime.lean`
(`PotNonincrOn`, `InvClosed`, `potDone`, `potBelow`, `level_occ_geometric_on`,
`pow_above_eq_zero_of_start_le_on`).  The *new* generic addition here is the
**fixed-horizon union-over-levels tail** (`levels_union_tail`): the level engine
there delivers `E[T]` (a `tsum`), whereas Phases 7/8 need a whp tail at a *fixed*
horizon `T`, which is the union over level windows.
-/

import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.ExpectedHitting
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.PhaseConvergenceWeak
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.CounterTimeout
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.Phase10ExpectedTime

namespace ExactMajority

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators NNReal

set_option linter.unusedSectionVars false

namespace OneSidedCancel

/-! ## Form (b) — the crude uniform whp tail

The simplest one-sided cancellation: while any target remains (`Φ ≥ 1`, i.e. the
state is in `(potDone Φ)ᶜ`), a single interaction fails to drain a target with
probability at most `q`.  Targets never increase (`PotNonincrOn`), so `{Φ = 0}` is
absorbing, and a single geometric over the not-done class gives `q^t`.

This is the `Φ`-potential specialization of `CounterTimeout.counterTimeout_tail_perStep`
with `Done := potDone Φ = {Φ = 0}`.  The eliminator floor enters only through `q`. -/

section Crude

variable {α : Type*} [MeasurableSpace α] [DiscreteMeasurableSpace α]

/-- `potDone Φ = {Φ = 0}` is absorbing under a target-count non-increasing on the
invariant: from a `{Φ = 0}`-state in `Inv`, one step cannot leave `{Φ = 0}`
(it cannot strictly raise `Φ`).  This is the `potDone` specialization of
`potBelow_absorbing_on` at `m = 1` (`{Φ < 1} = {Φ = 0}`). -/
theorem potDone_absorbing_on (K : Kernel α α) (Inv : α → Prop) (Φ : α → ℕ)
    (hmono : PotNonincrOn Inv K Φ) :
    ∀ x ∈ potDone Φ, Inv x → K x (potDone Φ)ᶜ = 0 := by
  intro x hx hInv
  -- {Φ = 0} = {Φ < 1} = potBelow Φ 1, and its complement is {1 ≤ Φ}.
  have hxlt : x ∈ potBelow Φ 1 := by
    simp only [potBelow, Set.mem_setOf_eq]
    have : Φ x = 0 := hx
    omega
  have hcompl : (potDone Φ)ᶜ = (potBelow Φ 1)ᶜ := by
    ext y; simp only [potDone, potBelow, Set.mem_compl_iff, Set.mem_setOf_eq]; omega
  rw [hcompl]
  exact potBelow_absorbing_on K Inv Φ hmono 1 x hxlt hInv

/-- **One-step crude contraction.**  Under non-increasing `Φ` on `Inv` and a uniform
per-step drop bound on the not-done class, appending one step to horizon `t`
contracts the not-done mass by `q`:
`(K^(t+1)) c (potDone Φ)ᶜ ≤ q · (K^t) c (potDone Φ)ᶜ`, for an `Inv`-start `c`.

Mirrors `level_occ_contract_on` but at the absorbing target `{Φ = 0}`: a.e. the
chain is in `Inv` (by `InvClosed`); on `{Φ = 0}` the bad mass is `0` (absorbing),
on `{1 ≤ Φ}` the one-step bad mass is `≤ q` (`hstep`). -/
theorem crude_contract (K : Kernel α α) [IsMarkovKernel K]
    (Inv : α → Prop) (hClosed : InvClosed K Inv)
    (Φ : α → ℕ) (hmono : PotNonincrOn Inv K Φ)
    (q : ℝ≥0∞)
    (hstep : ∀ b, Inv b → 1 ≤ Φ b → K b (potDone Φ)ᶜ ≤ q)
    (c : α) (hInvc : Inv c) (t : ℕ) :
    (K ^ (t + 1)) c (potDone Φ)ᶜ ≤ q * (K ^ t) c (potDone Φ)ᶜ := by
  classical
  have hbad : MeasurableSet ((potDone Φ)ᶜ : Set α) := (potDone_measurable Φ).compl
  have hAbs : ∀ x ∈ potDone Φ, Inv x → K x (potDone Φ)ᶜ = 0 :=
    potDone_absorbing_on K Inv Φ hmono
  rw [Kernel.pow_succ_apply_eq_lintegral K t c hbad]
  calc ∫⁻ b, K b (potDone Φ)ᶜ ∂((K ^ t) c)
      ≤ ∫⁻ b, q * Set.indicator ((potDone Φ)ᶜ) (fun _ => (1 : ℝ≥0∞)) b
          ∂((K ^ t) c) := by
        apply lintegral_mono_ae
        -- a.e. b lives in Inv (InvClosed).
        have hnull_inv : (K ^ t) c {x | ¬ Inv x} = 0 :=
          pow_not_inv_eq_zero K Inv hClosed c hInvc t
        rw [Filter.eventually_iff_exists_mem]
        refine ⟨{x | Inv x}, ?_, ?_⟩
        · rw [mem_ae_iff]
          have hcompl : ({x | Inv x}ᶜ : Set α) = {x | ¬ Inv x} := by
            ext y; simp only [Set.mem_compl_iff, Set.mem_setOf_eq]
          rw [hcompl]; exact hnull_inv
        · intro b hbInv
          simp only [Set.mem_setOf_eq] at hbInv
          by_cases hb0 : Φ b = 0
          · -- Φ b = 0: b ∈ potDone, Inv b, absorbing ⇒ K b bad = 0.
            have hbdone : b ∈ potDone Φ := hb0
            rw [hAbs b hbdone hbInv]; exact zero_le'
          · -- 1 ≤ Φ b: b ∈ (potDone Φ)ᶜ, so indicator = 1, and K b bad ≤ q.
            have hbmem : b ∈ ((potDone Φ)ᶜ : Set α) := by
              simp only [potDone, Set.mem_compl_iff, Set.mem_setOf_eq]; exact hb0
            rw [Set.indicator_of_mem hbmem, mul_one]
            exact hstep b hbInv (by omega)
    _ = q * (K ^ t) c (potDone Φ)ᶜ := by
        rw [lintegral_const_mul q (measurable_const.indicator hbad)]
        congr 1
        rw [lintegral_indicator hbad]; simp

/-- **Form (b): crude whp tail.**  Under a target count `Φ` non-increasing on `Inv`
(`PotNonincrOn`) with `Inv` `K`-closed (`InvClosed`), and a uniform per-step drop
bound `hstep` — from every `Inv`-state with at least one target remaining, a single
interaction fails to drain a target with probability `≤ q` — the not-done mass
decays geometrically: starting from an `Inv`-state, after `t` interactions at least
one target remains with probability `≤ q^t`.

`(potDone Φ)ᶜ = {y | 1 ≤ Φ y}` is the "still has a target" event. -/
theorem crude_tail (K : Kernel α α) [IsMarkovKernel K]
    (Inv : α → Prop) (hClosed : InvClosed K Inv)
    (Φ : α → ℕ) (hmono : PotNonincrOn Inv K Φ)
    (q : ℝ≥0∞)
    (hstep : ∀ b, Inv b → 1 ≤ Φ b → K b (potDone Φ)ᶜ ≤ q)
    (c : α) (hInvc : Inv c) (t : ℕ) :
    (K ^ t) c (potDone Φ)ᶜ ≤ q ^ t := by
  induction t with
  | zero =>
      simp only [pow_zero]
      calc (K ^ 0) c (potDone Φ)ᶜ ≤ (K ^ 0) c Set.univ :=
            measure_mono (Set.subset_univ _)
        _ = 1 := by
            rw [show (K ^ 0) = Kernel.id from pow_zero K, Kernel.id_apply, measure_univ]
  | succ t ih =>
      calc (K ^ (t + 1)) c (potDone Φ)ᶜ
          ≤ q * (K ^ t) c (potDone Φ)ᶜ :=
            crude_contract K Inv hClosed Φ hmono q hstep c hInvc t
        _ ≤ q * q ^ t := by gcongr
        _ = q ^ (t + 1) := by rw [pow_succ]; ring

end Crude

end OneSidedCancel

end ExactMajority
