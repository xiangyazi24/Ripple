/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Expected Hitting Time on Transition-Kernel Powers (Generic)

A small, protocol-agnostic toolkit for the **expected hitting time** of a target
("Done") set under iteration of a Markov kernel.

The codebase has no pathwise random variable `T`; everything is expressed through
kernel powers `(K ^ t) c S` and event masses in `ℝ≥0∞`. We therefore formalize the
expectation `E[T]` **directly** as the tail-sum

    expectedHitting K c Done  :=  ∑' t, (K ^ t) c Doneᶜ

where `Doneᶜ` is the "not done yet" event. Under the standard identity
`E[T] = ∑_{t ≥ 0} P(T > t)` and `{T > t} = {not done by time t}` this equals the
mean hitting time of `Done`. Everything below is stated and proved about this
`∑'`-quantity, entirely inside `ℝ≥0∞` (so no convergence side conditions arise).

## Conventions

We work over a generic measurable space `α` with a Markov kernel `K : Kernel α α`,
matching the generic style of `PopProtoCommon/Convergence/GeometricDrift.lean`.
This makes every lemma directly applicable to `(NonuniformMajority L K).transitionKernel`
(an `IsMarkovKernel` on `Config Λ`, a `DiscreteMeasurableSpace`).

`Done` is a **fixed** measurable set; the "bad event" family is the constant family
`Bad t = Doneᶜ`, with the monotonicity `P(Bad (t+1)) ≤ P(Bad t)` coming from
absorption of `Done` (Lemma 0). This fixed-set version is all Phase E needs.

## Main results

* `bad_antitone` — `(K^(t+1)) c Doneᶜ ≤ (K^t) c Doneᶜ` from `Done` absorbing.
* `expectedHitting_le_block` — block form `E[T] ≤ s · ∑' k, P(T > k·s)`.
* `expectedHitting_geometric` — uniform per-block success `q` over a `K`-closed
  class containing the start ⟹ `E[T] ≤ s · (1 - q)⁻¹`.
* `expectedHitting_split` — `E[T] ≤ t₀ + ∑' t, P(T > t₀ + t)`.
* `expectedHitting_split_geometric` — the combined `t₀ + δ·s·(1-q)⁻¹`-shape bound
  consumed by Phase E4.
-/

import Ripple.PopulationProtocol.Majority.PopProtoCommon.Convergence.GeometricDrift
import Mathlib.Probability.Kernel.Composition.Comp
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Logic.Equiv.Fin.Basic

namespace ExactMajority

open scoped ENNReal
open MeasureTheory ProbabilityTheory

variable {α : Type*} [MeasurableSpace α]

/-! ## Part 1 — The expected-hitting tail sum and its monotone bad event -/

/-- The **expected hitting time** of the set `Done` under the kernel `K`, started
at `c`, formalized directly as the tail sum `∑' t, P(not done by time t)`.

Under the standard identity `E[T] = ∑_{t ≥ 0} P(T > t)` with `{T > t}` = "Done not
yet hit by step `t`" (i.e. `(K^t) c Doneᶜ`), this `∑'` equals the mean hitting
time of `Done`. All lemmas in this file are about this quantity. -/
noncomputable def expectedHitting (K : Kernel α α) (c : α) (Done : Set α) : ℝ≥0∞ :=
  ∑' t : ℕ, (K ^ t) c Doneᶜ

/-- **Lemma 0 (monotone bad event).** If `Done` is absorbing
(`K x Doneᶜ = 0` for every `x ∈ Done`), then the "not done by time `t`" mass is
antitone in `t`: `(K^(t+1)) c Doneᶜ ≤ (K^t) c Doneᶜ`.

This is what makes the tail family genuinely decreasing, and underlies the block
bound. -/
theorem bad_antitone (K : Kernel α α) [IsMarkovKernel K]
    {Done : Set α} (hDone : MeasurableSet Done)
    (hAbs : ∀ x ∈ Done, K x Doneᶜ = 0)
    (c : α) (t : ℕ) :
    (K ^ (t + 1)) c Doneᶜ ≤ (K ^ t) c Doneᶜ := by
  have hbad : MeasurableSet (Doneᶜ : Set α) := hDone.compl
  rw [Kernel.pow_succ_apply_eq_lintegral K t c hbad]
  -- Pointwise: K b Doneᶜ ≤ 1_{Doneᶜ}(b).  On Done it is 0; on Doneᶜ it is ≤ 1.
  calc ∫⁻ b, K b Doneᶜ ∂((K ^ t) c)
      ≤ ∫⁻ b, Set.indicator Doneᶜ (fun _ => (1 : ℝ≥0∞)) b ∂((K ^ t) c) := by
        apply lintegral_mono
        intro b
        dsimp only
        by_cases hb : b ∈ Done
        · rw [hAbs b hb]
          exact zero_le'
        · have hb' : b ∈ (Doneᶜ : Set α) := hb
          rw [Set.indicator_of_mem hb']
          exact prob_le_one
    _ = (K ^ t) c Doneᶜ := by
        rw [lintegral_indicator hbad]
        simp

/-- General antitonicity: for `s ≤ t`, `(K^t) c Doneᶜ ≤ (K^s) c Doneᶜ`. -/
theorem bad_antitone_le (K : Kernel α α) [IsMarkovKernel K]
    {Done : Set α} (hDone : MeasurableSet Done)
    (hAbs : ∀ x ∈ Done, K x Doneᶜ = 0)
    (c : α) {s t : ℕ} (hst : s ≤ t) :
    (K ^ t) c Doneᶜ ≤ (K ^ s) c Doneᶜ := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hst
  clear hst
  induction d with
  | zero => simp
  | succ d ih =>
      calc (K ^ (s + (d + 1))) c Doneᶜ
          = (K ^ ((s + d) + 1)) c Doneᶜ := by ring_nf
        _ ≤ (K ^ (s + d)) c Doneᶜ := bad_antitone K hDone hAbs c (s + d)
        _ ≤ (K ^ s) c Doneᶜ := ih

/-! ## Part 2 — Tail sum and block form -/

/-- `expectedHitting` unfolds to the tail sum (definitional restatement). -/
theorem expectedHitting_eq_tsum (K : Kernel α α) (c : α) (Done : Set α) :
    expectedHitting K c Done = ∑' t : ℕ, (K ^ t) c Doneᶜ := rfl

/-- **Block form.** For `s ≠ 0`, the expected hitting time is bounded by `s` times
the tail sum sampled on the block boundaries:
`E[T] ≤ s · ∑' k, P(T > k·s)`.

Each `P(T > t)` for `t` in block `k` (i.e. `k·s ≤ t < (k+1)·s`) is bounded by its
block's left endpoint `P(T > k·s)` via antitonicity, and there are `s` units per
block. -/
theorem expectedHitting_le_block (K : Kernel α α) [IsMarkovKernel K]
    {Done : Set α} (hDone : MeasurableSet Done)
    (hAbs : ∀ x ∈ Done, K x Doneᶜ = 0)
    (c : α) (s : ℕ) (hs : s ≠ 0) :
    expectedHitting K c Done ≤ (s : ℝ≥0∞) * ∑' k : ℕ, (K ^ (k * s)) c Doneᶜ := by
  haveI : NeZero s := ⟨hs⟩
  rw [expectedHitting]
  -- Reindex t ↦ (k, j) with t = k·s + j, j < s, via Nat.divModEquiv.
  rw [← Equiv.tsum_eq (Nat.divModEquiv s).symm (fun t => (K ^ t) c Doneᶜ)]
  rw [ENNReal.tsum_prod']
  -- Bound the inner Fin s sum of P(T > k·s + j) by s · P(T > k·s), then pull `s` out.
  have hinner : ∀ k : ℕ,
      ∑' j : Fin s, (K ^ ((Nat.divModEquiv s).symm (k, j))) c Doneᶜ ≤
        (s : ℝ≥0∞) * (K ^ (k * s)) c Doneᶜ := by
    intro k
    have hkey : ∀ j : Fin s,
        (K ^ ((Nat.divModEquiv s).symm (k, j))) c Doneᶜ ≤ (K ^ (k * s)) c Doneᶜ := by
      intro j
      apply bad_antitone_le K hDone hAbs c
      simp only [Nat.divModEquiv_symm_apply]
      omega
    calc ∑' j : Fin s, (K ^ ((Nat.divModEquiv s).symm (k, j))) c Doneᶜ
        ≤ ∑' _ : Fin s, (K ^ (k * s)) c Doneᶜ := ENNReal.tsum_le_tsum hkey
      _ = (s : ℝ≥0∞) * (K ^ (k * s)) c Doneᶜ := by
          rw [ENNReal.tsum_const]
          simp
  calc ∑' (k : ℕ) (j : Fin s), (K ^ ((Nat.divModEquiv s).symm (k, j))) c Doneᶜ
      ≤ ∑' k : ℕ, (s : ℝ≥0∞) * (K ^ (k * s)) c Doneᶜ := ENNReal.tsum_le_tsum hinner
    _ = (s : ℝ≥0∞) * ∑' k : ℕ, (K ^ (k * s)) c Doneᶜ := by rw [ENNReal.tsum_mul_left]

/-! ## Part 3 — Geometric tail from uniform per-block success -/

/-- `Done` absorbing for one step lifts to absorbing for `m` steps:
`(K^m) x Doneᶜ = 0` for every `x ∈ Done`. -/
theorem pow_absorbing (K : Kernel α α) [IsMarkovKernel K]
    {Done : Set α} (hDone : MeasurableSet Done)
    (hAbs : ∀ x ∈ Done, K x Doneᶜ = 0)
    (m : ℕ) {x : α} (hx : x ∈ Done) :
    (K ^ m) x Doneᶜ = 0 := by
  have hbad : MeasurableSet (Doneᶜ : Set α) := hDone.compl
  induction m generalizing x with
  | zero =>
      -- K^0 = id, dirac x; x ∈ Done so x ∉ Doneᶜ.
      rw [show (K ^ 0) = Kernel.id from pow_zero K, Kernel.id_apply,
        Measure.dirac_apply' x hbad]
      have hxc : x ∉ (Doneᶜ : Set α) := by simpa using hx
      simp [hxc]
  | succ m ih =>
      -- Peel the first step: (K^(1+m)) x Doneᶜ = ∫⁻ b, (K^m) b Doneᶜ ∂(K x).
      rw [show m + 1 = 1 + m from by ring,
        Kernel.pow_add_apply_eq_lintegral K 1 m x hbad, pow_one]
      -- The integrand is 0 on Done (by IH) and K x is supported on Done (x ∈ Done).
      rw [lintegral_eq_zero_iff (Kernel.measurable_coe _ hbad)]
      rw [Filter.eventuallyEq_iff_exists_mem]
      refine ⟨Done, ?_, fun b hb => ih hb⟩
      rw [mem_ae_iff]
      have : K x Doneᶜ = 0 := hAbs x hx
      simpa using this

/-- **One-block geometric contraction (from arbitrary base `m`).** If from every
not-yet-done state the `s`-step kernel fails to reach `Done` with probability `≤ q`
(`∀ b ∈ Doneᶜ, (K^s) b Doneᶜ ≤ q`), and `Done` is absorbing, then appending a block
of `s` steps to any base horizon `m` contracts the not-done mass by a factor `q`:
`(K^(m+s)) c₀ Doneᶜ ≤ q · (K^m) c₀ Doneᶜ`. -/
theorem bad_block_contracts_from (K : Kernel α α) [IsMarkovKernel K]
    {Done : Set α} (hDone : MeasurableSet Done)
    (hAbs : ∀ x ∈ Done, K x Doneᶜ = 0)
    (s : ℕ) (q : ℝ≥0∞)
    (hblock : ∀ b ∈ (Doneᶜ : Set α), (K ^ s) b Doneᶜ ≤ q)
    (c₀ : α) (m : ℕ) :
    (K ^ (m + s)) c₀ Doneᶜ ≤ q * (K ^ m) c₀ Doneᶜ := by
  have hbad : MeasurableSet (Doneᶜ : Set α) := hDone.compl
  -- (K^(m + s)) c₀ Doneᶜ = ∫⁻ b, (K^s) b Doneᶜ ∂(K^m c₀).
  rw [Kernel.pow_add_apply_eq_lintegral K m s c₀ hbad]
  -- Pointwise: (K^s) b Doneᶜ ≤ q · 1_{Doneᶜ}(b).  On Done it is 0; on Doneᶜ it is ≤ q.
  calc ∫⁻ b, (K ^ s) b Doneᶜ ∂((K ^ m) c₀)
      ≤ ∫⁻ b, q * Set.indicator Doneᶜ (fun _ => (1 : ℝ≥0∞)) b ∂((K ^ m) c₀) := by
        apply lintegral_mono
        intro b
        dsimp only
        by_cases hb : b ∈ Done
        · rw [pow_absorbing K hDone hAbs s hb]; exact zero_le'
        · have hb' : b ∈ (Doneᶜ : Set α) := hb
          rw [Set.indicator_of_mem hb', mul_one]
          exact hblock b hb'
    _ = q * (K ^ m) c₀ Doneᶜ := by
        rw [lintegral_const_mul q (by
          exact (measurable_const.indicator hbad))]
        congr 1
        rw [lintegral_indicator hbad]
        simp

/-- One-block contraction along the `k·s` grid (special case of
`bad_block_contracts_from`): `(K^((k+1)·s)) c₀ Doneᶜ ≤ q · (K^(k·s)) c₀ Doneᶜ`. -/
theorem bad_block_contracts (K : Kernel α α) [IsMarkovKernel K]
    {Done : Set α} (hDone : MeasurableSet Done)
    (hAbs : ∀ x ∈ Done, K x Doneᶜ = 0)
    (s : ℕ) (q : ℝ≥0∞)
    (hblock : ∀ b ∈ (Doneᶜ : Set α), (K ^ s) b Doneᶜ ≤ q)
    (c₀ : α) (k : ℕ) :
    (K ^ ((k + 1) * s)) c₀ Doneᶜ ≤ q * (K ^ (k * s)) c₀ Doneᶜ := by
  rw [show (k + 1) * s = k * s + s from by ring]
  exact bad_block_contracts_from K hDone hAbs s q hblock c₀ (k * s)

/-- **Geometric tail.** Under uniform per-block success `q` (from every not-done
state, `s` steps fail to finish with probability `≤ q`) and `Done` absorbing,
the `k`-block not-done mass decays geometrically: `(K^(k·s)) c₀ Doneᶜ ≤ q^k`. -/
theorem bad_block_geometric (K : Kernel α α) [IsMarkovKernel K]
    {Done : Set α} (hDone : MeasurableSet Done)
    (hAbs : ∀ x ∈ Done, K x Doneᶜ = 0)
    (s : ℕ) (q : ℝ≥0∞)
    (hblock : ∀ b ∈ (Doneᶜ : Set α), (K ^ s) b Doneᶜ ≤ q)
    (c₀ : α) (k : ℕ) :
    (K ^ (k * s)) c₀ Doneᶜ ≤ q ^ k := by
  induction k with
  | zero =>
      simp only [Nat.zero_mul, pow_zero, pow_zero]
      calc (K ^ 0) c₀ Doneᶜ ≤ (K ^ 0) c₀ Set.univ := measure_mono (Set.subset_univ _)
        _ = 1 := by
            rw [show (K ^ 0) = Kernel.id from pow_zero K, Kernel.id_apply, measure_univ]
  | succ k ih =>
      calc (K ^ ((k + 1) * s)) c₀ Doneᶜ
          ≤ q * (K ^ (k * s)) c₀ Doneᶜ :=
            bad_block_contracts K hDone hAbs s q hblock c₀ k
        _ ≤ q * q ^ k := by gcongr
        _ = q ^ (k + 1) := by rw [pow_succ]; ring

/-- **Geometric expected-hitting bound.** Combining the block form with the
geometric tail: if `Done` is absorbing and from every not-done state the `s`-step
kernel fails with probability `≤ q` (`s ≠ 0`), then
`E[T] ≤ s · (1 - q)⁻¹`.

This is the backup expected-time shape (`s` = block length, `(1-q)⁻¹` = expected
number of blocks) consumed by Phase E2/E4. -/
theorem expectedHitting_geometric (K : Kernel α α) [IsMarkovKernel K]
    {Done : Set α} (hDone : MeasurableSet Done)
    (hAbs : ∀ x ∈ Done, K x Doneᶜ = 0)
    (s : ℕ) (hs : s ≠ 0) (q : ℝ≥0∞)
    (hblock : ∀ b ∈ (Doneᶜ : Set α), (K ^ s) b Doneᶜ ≤ q)
    (c₀ : α) :
    expectedHitting K c₀ Done ≤ (s : ℝ≥0∞) * (1 - q)⁻¹ := by
  calc expectedHitting K c₀ Done
      ≤ (s : ℝ≥0∞) * ∑' k : ℕ, (K ^ (k * s)) c₀ Doneᶜ :=
        expectedHitting_le_block K hDone hAbs c₀ s hs
    _ ≤ (s : ℝ≥0∞) * ∑' k : ℕ, q ^ k := by
        gcongr with k
        exact bad_block_geometric K hDone hAbs s q hblock c₀ k
    _ = (s : ℝ≥0∞) * (1 - q)⁻¹ := by rw [ENNReal.tsum_geometric]

/-! ## Part 4 — Conditioning-free split and combined corollary -/

/-- The `t`-step kernel mass of any set is `≤ 1`. -/
theorem kernel_pow_le_one (K : Kernel α α) [IsMarkovKernel K]
    (t : ℕ) (x : α) (S : Set α) :
    (K ^ t) x S ≤ 1 := by
  calc (K ^ t) x S ≤ (K ^ t) x Set.univ := measure_mono (Set.subset_univ _)
    _ ≤ 1 := by
        induction t with
        | zero =>
            rw [show (K ^ 0) = Kernel.id from pow_zero K, Kernel.id_apply, measure_univ]
        | succ t ih =>
            rw [Kernel.pow_succ_apply_eq_lintegral K t x MeasurableSet.univ]
            calc ∫⁻ y, K y Set.univ ∂((K ^ t) x)
                ≤ ∫⁻ _ : α, (1 : ℝ≥0∞) ∂((K ^ t) x) := by
                    apply lintegral_mono; intro y; simp [measure_univ]
              _ = (K ^ t) x Set.univ := by simp
              _ ≤ 1 := ih

/-- **Conditioning-free split.** For any horizon `t₀`,
`E[T] ≤ t₀ + ∑' t, P(T > t₀ + t)`.

The first `t₀` tail terms are each `≤ 1`; the remaining tail is shifted by `t₀`. -/
theorem expectedHitting_split (K : Kernel α α) [IsMarkovKernel K]
    (c : α) (Done : Set α) (t₀ : ℕ) :
    expectedHitting K c Done ≤
      (t₀ : ℝ≥0∞) + ∑' t : ℕ, (K ^ (t₀ + t)) c Doneᶜ := by
  rw [expectedHitting]
  -- ∑' t, a t = (∑_{i<t₀} a i) + ∑' t, a (t + t₀)
  rw [← ENNReal.summable.sum_add_tsum_nat_add' (f := fun t => (K ^ t) c Doneᶜ) (k := t₀)]
  gcongr
  · -- ∑_{i < t₀} a i ≤ t₀
    calc ∑ i ∈ Finset.range t₀, (K ^ i) c Doneᶜ
        ≤ ∑ _i ∈ Finset.range t₀, (1 : ℝ≥0∞) :=
          Finset.sum_le_sum (fun i _ => kernel_pow_le_one K i c _)
      _ = (t₀ : ℝ≥0∞) := by simp
  · -- ∑' t, a (t + t₀) = ∑' t, a (t₀ + t)
    rw [Nat.add_comm]

/-- **Block form of the shifted tail.** For `s ≠ 0`,
`∑' t, P(T > t₀ + t) ≤ s · ∑' k, P(T > t₀ + k·s)`. Same block argument as
`expectedHitting_le_block`, shifted by the base horizon `t₀`. -/
theorem tail_le_block (K : Kernel α α) [IsMarkovKernel K]
    {Done : Set α} (hDone : MeasurableSet Done)
    (hAbs : ∀ x ∈ Done, K x Doneᶜ = 0)
    (c : α) (t₀ s : ℕ) (hs : s ≠ 0) :
    ∑' t : ℕ, (K ^ (t₀ + t)) c Doneᶜ ≤
      (s : ℝ≥0∞) * ∑' k : ℕ, (K ^ (t₀ + k * s)) c Doneᶜ := by
  haveI : NeZero s := ⟨hs⟩
  rw [← Equiv.tsum_eq (Nat.divModEquiv s).symm (fun t => (K ^ (t₀ + t)) c Doneᶜ)]
  rw [ENNReal.tsum_prod']
  have hinner : ∀ k : ℕ,
      ∑' j : Fin s, (K ^ (t₀ + (Nat.divModEquiv s).symm (k, j))) c Doneᶜ ≤
        (s : ℝ≥0∞) * (K ^ (t₀ + k * s)) c Doneᶜ := by
    intro k
    have hkey : ∀ j : Fin s,
        (K ^ (t₀ + (Nat.divModEquiv s).symm (k, j))) c Doneᶜ ≤
          (K ^ (t₀ + k * s)) c Doneᶜ := by
      intro j
      apply bad_antitone_le K hDone hAbs c
      simp only [Nat.divModEquiv_symm_apply]
      omega
    calc ∑' j : Fin s, (K ^ (t₀ + (Nat.divModEquiv s).symm (k, j))) c Doneᶜ
        ≤ ∑' _ : Fin s, (K ^ (t₀ + k * s)) c Doneᶜ := ENNReal.tsum_le_tsum hkey
      _ = (s : ℝ≥0∞) * (K ^ (t₀ + k * s)) c Doneᶜ := by rw [ENNReal.tsum_const]; simp
  calc ∑' (k : ℕ) (j : Fin s), (K ^ (t₀ + (Nat.divModEquiv s).symm (k, j))) c Doneᶜ
      ≤ ∑' k : ℕ, (s : ℝ≥0∞) * (K ^ (t₀ + k * s)) c Doneᶜ := ENNReal.tsum_le_tsum hinner
    _ = (s : ℝ≥0∞) * ∑' k : ℕ, (K ^ (t₀ + k * s)) c Doneᶜ := by rw [ENNReal.tsum_mul_left]

/-- **Geometric tail from a base horizon.** Under uniform per-block success `q` and
`Done` absorbing, the not-done mass at time `t₀ + k·s` decays geometrically off its
value `δ := P(T > t₀)` at `t₀`: `(K^(t₀ + k·s)) c₀ Doneᶜ ≤ (K^t₀) c₀ Doneᶜ · q^k`. -/
theorem bad_block_geometric_from (K : Kernel α α) [IsMarkovKernel K]
    {Done : Set α} (hDone : MeasurableSet Done)
    (hAbs : ∀ x ∈ Done, K x Doneᶜ = 0)
    (s : ℕ) (q : ℝ≥0∞)
    (hblock : ∀ b ∈ (Doneᶜ : Set α), (K ^ s) b Doneᶜ ≤ q)
    (c₀ : α) (t₀ k : ℕ) :
    (K ^ (t₀ + k * s)) c₀ Doneᶜ ≤ (K ^ t₀) c₀ Doneᶜ * q ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
      calc (K ^ (t₀ + (k + 1) * s)) c₀ Doneᶜ
          = (K ^ ((t₀ + k * s) + s)) c₀ Doneᶜ := by rw [show t₀ + (k + 1) * s = (t₀ + k * s) + s from by ring]
        _ ≤ q * (K ^ (t₀ + k * s)) c₀ Doneᶜ :=
            bad_block_contracts_from K hDone hAbs s q hblock c₀ (t₀ + k * s)
        _ ≤ q * ((K ^ t₀) c₀ Doneᶜ * q ^ k) := by gcongr
        _ = (K ^ t₀) c₀ Doneᶜ * q ^ (k + 1) := by rw [pow_succ]; ring

/-- **Combined split + geometric corollary** (the exact shape Phase E4 consumes).

Suppose `Done` is absorbing and from every not-done state the `s`-step kernel
(`s ≠ 0`) fails to finish with probability `≤ q`. If, in addition, the not-done
mass at a horizon `t₀` is at most `δ` (`(K^t₀) c₀ Doneᶜ ≤ δ`), then

    E[T] ≤ t₀ + δ · s · (1 - q)⁻¹.

Here `t₀ = O(log n)` is the good-event horizon, `δ` is the whp failure
probability, and `s · (1-q)⁻¹` is the backup expected time. -/
theorem expectedHitting_split_geometric (K : Kernel α α) [IsMarkovKernel K]
    {Done : Set α} (hDone : MeasurableSet Done)
    (hAbs : ∀ x ∈ Done, K x Doneᶜ = 0)
    (s : ℕ) (hs : s ≠ 0) (q : ℝ≥0∞)
    (hblock : ∀ b ∈ (Doneᶜ : Set α), (K ^ s) b Doneᶜ ≤ q)
    (c₀ : α) (t₀ : ℕ) (δ : ℝ≥0∞) (hδ : (K ^ t₀) c₀ Doneᶜ ≤ δ) :
    expectedHitting K c₀ Done ≤ (t₀ : ℝ≥0∞) + δ * s * (1 - q)⁻¹ := by
  have htail : ∑' t : ℕ, (K ^ (t₀ + t)) c₀ Doneᶜ ≤ δ * s * (1 - q)⁻¹ := by
    calc ∑' t : ℕ, (K ^ (t₀ + t)) c₀ Doneᶜ
        ≤ (s : ℝ≥0∞) * ∑' k : ℕ, (K ^ (t₀ + k * s)) c₀ Doneᶜ :=
          tail_le_block K hDone hAbs c₀ t₀ s hs
      _ ≤ (s : ℝ≥0∞) * ∑' k : ℕ, δ * q ^ k := by
          gcongr with k
          calc (K ^ (t₀ + k * s)) c₀ Doneᶜ
              ≤ (K ^ t₀) c₀ Doneᶜ * q ^ k :=
                bad_block_geometric_from K hDone hAbs s q hblock c₀ t₀ k
            _ ≤ δ * q ^ k := by gcongr
      _ = (s : ℝ≥0∞) * (δ * (1 - q)⁻¹) := by rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric]
      _ = δ * s * (1 - q)⁻¹ := by ring
  calc expectedHitting K c₀ Done
      ≤ (t₀ : ℝ≥0∞) + ∑' t : ℕ, (K ^ (t₀ + t)) c₀ Doneᶜ :=
        expectedHitting_split K c₀ Done t₀
    _ ≤ (t₀ : ℝ≥0∞) + δ * s * (1 - q)⁻¹ := by gcongr

/-! ## Part 5 — Per-single-step progress (coupon-collector engine)

The lemmas below specialize the block engine to **single steps** (`s = 1`). They are
the form Phase E2 consumes: a uniform *one-step* success probability `p` over the
not-done class `Doneᶜ` (i.e. from every not-done state the kernel reaches `Done` in
one step with probability `≥ p`, equivalently fails with probability `≤ 1 - p`)
yields the expected-hitting bound `E[T] ≤ p⁻¹`. For a stage potential that strictly
decreases per useful interaction, `p` is the lower bound on the per-step probability
that the useful interaction fires; `p⁻¹` is then the expected number of interactions
for that potential level (the per-level term of the coupon-collector / harmonic sum).
-/

/-- **One-step success ⇒ expected hitting `≤ p⁻¹`.** If `Done` is absorbing and
from every not-done state the kernel reaches `Done` in a single step with
probability `≥ p` (`K b Doneᶜ ≤ 1 - p`), then `E[T] ≤ p⁻¹`.

This is `expectedHitting_geometric` at block length `s = 1` with failure `q = 1 - p`,
using `(1 - (1 - p))⁻¹ = p⁻¹`. -/
theorem expectedHitting_one_step (K : Kernel α α) [IsMarkovKernel K]
    {Done : Set α} (hDone : MeasurableSet Done)
    (hAbs : ∀ x ∈ Done, K x Doneᶜ = 0)
    (p : ℝ≥0∞) (hp : p ≤ 1)
    (hstep : ∀ b ∈ (Doneᶜ : Set α), K b Doneᶜ ≤ 1 - p)
    (c₀ : α) :
    expectedHitting K c₀ Done ≤ p⁻¹ := by
  have hblock : ∀ b ∈ (Doneᶜ : Set α), (K ^ 1) b Doneᶜ ≤ 1 - p := by
    intro b hb; rw [pow_one]; exact hstep b hb
  calc expectedHitting K c₀ Done
      ≤ ((1 : ℕ) : ℝ≥0∞) * (1 - (1 - p))⁻¹ :=
        expectedHitting_geometric K hDone hAbs 1 (by norm_num) (1 - p) hblock c₀
    _ = p⁻¹ := by
        rw [Nat.cast_one, one_mul, ENNReal.sub_sub_cancel (by norm_num) hp]

/-- **Monotone-potential one-step bound (general `p` form).** Same conclusion as
`expectedHitting_one_step` but stated with the success probability supplied as a
hypothesis `q := 1 - p` directly, avoiding the `p > 1` corner: from `Done`
absorbing and `∀ b ∈ Doneᶜ, K b Doneᶜ ≤ q` with `q < 1`,
`E[T] ≤ (1 - q)⁻¹`. -/
theorem expectedHitting_one_step_q (K : Kernel α α) [IsMarkovKernel K]
    {Done : Set α} (hDone : MeasurableSet Done)
    (hAbs : ∀ x ∈ Done, K x Doneᶜ = 0)
    (q : ℝ≥0∞)
    (hstep : ∀ b ∈ (Doneᶜ : Set α), K b Doneᶜ ≤ q)
    (c₀ : α) :
    expectedHitting K c₀ Done ≤ (1 - q)⁻¹ := by
  have hblock : ∀ b ∈ (Doneᶜ : Set α), (K ^ 1) b Doneᶜ ≤ q := by
    intro b hb; rw [pow_one]; exact hstep b hb
  calc expectedHitting K c₀ Done
      ≤ ((1 : ℕ) : ℝ≥0∞) * (1 - q)⁻¹ :=
        expectedHitting_geometric K hDone hAbs 1 (by norm_num) q hblock c₀
    _ = (1 - q)⁻¹ := by rw [Nat.cast_one, one_mul]

end ExactMajority
