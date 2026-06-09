/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Total-Time Composition for the Nonuniform Exact-Majority Protocol (Doty et al.)

This file builds the **assembly contract** (Avenue A1 of the Doty Theorem 3.1
time-half campaign): it locks the *total-time arithmetic* of the eleven-phase
convergence proof **independent of the per-phase content**.

Concretely, GIVEN eleven opaque `PhaseConvergence` instances for the
`NonuniformMajority L K` transition kernel — supplied as a hypothesis together
with per-phase time/error bounds and the chaining hypothesis — we conclude, via
`compose_n_phases`, the total bound

  `(K ^ T) c₀ {c | ¬ majorityStableEndpoint init c} ≤ E`

where the total interaction count `T = ∑ (phases i).t ≤ (∑ Cphase) · n · (L+1)`
(so `T = O(n · (L+1)) = O(n log n)` interactions, i.e. `T / n = O(L+1) =
O(log n)` parallel time) and the total error `E = ∑ (phases i).ε ≤ ∑ δ`.

The proof is `compose_n_phases` plus two `Finset.sum_le_sum` arithmetic facts.
It needs none of the per-phase content: when the eleven instances land (Avenue
A0 and siblings), the headline `O(log n)`-parallel whp bound drops out by
plugging them in.
-/

import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.PhaseConvergence
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.NonuniformMarkovChain
import Ripple.PopulationProtocol.Majority.ExactMajority.Analysis.StableEndpoints

namespace ExactMajority

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal

/-- The last phase index `10 : Fin 11`. Matches the `⟨m - 1, _⟩` last-phase
index used by `compose_n_phases` at `m = 11`. -/
private def lastPhase : Fin 11 := ⟨11 - 1, by omega⟩

/-! ## Arithmetic facts (independent of per-phase content) -/

/-- **Total-time arithmetic.** If every phase takes at most `Cphase i · n · (L+1)`
interactions, the total interaction count is at most `(∑ Cphase) · n · (L+1)`.
Pure monotone-sum reasoning. -/
theorem total_time_le
    {m : ℕ} {n L : ℕ} (t Cphase : Fin m → ℕ)
    (ht : ∀ i, t i ≤ Cphase i * n * (L + 1)) :
    (∑ i, t i) ≤ (∑ i, Cphase i) * n * (L + 1) := by
  calc (∑ i, t i)
      ≤ ∑ i, Cphase i * n * (L + 1) := Finset.sum_le_sum (fun i _ => ht i)
    _ = (∑ i, Cphase i) * n * (L + 1) := by
        simp [Finset.sum_mul]

/-- **Total-error arithmetic.** If every phase fails with probability at most
`δ i`, the union-bound total error is at most `∑ δ`. Stated in `ℝ≥0∞`. -/
theorem total_error_le
    {m : ℕ} (ε δ : Fin m → ℝ≥0)
    (hε : ∀ i, (ε i : ℝ≥0∞) ≤ (δ i : ℝ≥0∞)) :
    (∑ i, (ε i : ℝ≥0∞)) ≤ ∑ i, (δ i : ℝ≥0∞) :=
  Finset.sum_le_sum (fun i _ => hε i)

/-! ## The compose-all-phases skeleton -/

/-- **Doty time composition (assembly contract).**

Given eleven opaque `PhaseConvergence` instances for the `NonuniformMajority L K`
transition kernel, with

* per-phase time bounds `ht : ∀ i, (phases i).t ≤ Cphase i · n · (L+1)`,
* per-phase error bounds `hε : ∀ i, ((phases i).ε : ℝ≥0∞) ≤ (δ i : ℝ≥0∞)`,
* the chaining hypothesis `h_chain` (phase `i`'s `Post` implies phase `i+1`'s `Pre`),
* the start hypothesis `hx₀ : (phases 0).Pre c₀`, and
* the closing hypothesis `h_post` (the last phase's `Post` implies
  `majorityStableEndpoint init`),

the composed chain reaches `majorityStableEndpoint init` within
`T := ∑ (phases i).t` interactions with failure probability at most `∑ (phases i).ε`,
and moreover `T ≤ (∑ Cphase) · n · (L+1)` and `∑ (phases i).ε ≤ ∑ δ`.

This is purely the assembly arithmetic: it does not use any per-phase content. -/
theorem doty_time_composition
    {L K n : ℕ}
    (init c₀ : Config (AgentState L K))
    (Cphase : Fin 11 → ℕ) (δ : Fin 11 → ℝ≥0)
    (phases : Fin 11 → PhaseConvergence (NonuniformMajority L K).transitionKernel)
    (ht : ∀ i, (phases i).t ≤ Cphase i * n * (L + 1))
    (hε : ∀ i, ((phases i).ε : ℝ≥0∞) ≤ (δ i : ℝ≥0∞))
    (h_chain : ∀ (i : Fin 11) (hi : i.val + 1 < 11),
        ∀ x, (phases i).Post x → (phases ⟨i.val + 1, hi⟩).Pre x)
    (hx₀ : (phases ⟨0, by omega⟩).Pre c₀)
    (h_post : ∀ c, (phases lastPhase).Post c → majorityStableEndpoint (L := L) (K := K) init c) :
    -- total bound at the *actual* composed interaction count `∑ (phases i).t`
    ((NonuniformMajority L K).transitionKernel ^ (∑ i, (phases i).t)) c₀
        {c | ¬ majorityStableEndpoint (L := L) (K := K) init c}
      ≤ (∑ i, ((phases i).ε : ℝ≥0∞))
    ∧ -- total interactions: O(n · (L+1)) = O(n log n)  (parallel time O(L+1) = O(log n))
      (∑ i, (phases i).t) ≤ (∑ i, Cphase i) * n * (L + 1)
    ∧ -- total error: union bound ≤ ∑ δ
      (∑ i, ((phases i).ε : ℝ≥0∞)) ≤ ∑ i, (δ i : ℝ≥0∞) := by
  refine ⟨?_, ?_, ?_⟩
  · -- The composed convergence bound, via `compose_n_phases`.
    -- `compose_n_phases` concludes a bound on `{c | ¬ (phases ⟨11-1,_⟩).Post c}`;
    -- monotonicity in the measured set upgrades it to the stable-endpoint set
    -- using `h_post`.
    have h_compose :=
      compose_n_phases (K := (NonuniformMajority L K).transitionKernel)
        (m := 11) (by omega) phases h_chain c₀ hx₀
    -- `{c | ¬ MSE c} ⊆ {c | ¬ (phases last).Post c}`: contrapositive of `h_post`.
    have h_subset :
        {c | ¬ majorityStableEndpoint (L := L) (K := K) init c}
          ⊆ {c | ¬ (phases ⟨11 - 1, by omega⟩).Post c} := by
      intro c hc
      simp only [Set.mem_setOf_eq] at hc ⊢
      intro hPost
      exact hc (h_post c hPost)
    calc ((NonuniformMajority L K).transitionKernel ^ (∑ i, (phases i).t)) c₀
            {c | ¬ majorityStableEndpoint (L := L) (K := K) init c}
        ≤ ((NonuniformMajority L K).transitionKernel ^ (∑ i, (phases i).t)) c₀
            {c | ¬ (phases ⟨11 - 1, by omega⟩).Post c} := measure_mono h_subset
      _ ≤ (∑ i, ((phases i).ε : ℝ≥0∞)) := h_compose
  · -- Total-time arithmetic.
    exact total_time_le (fun i => (phases i).t) Cphase ht
  · -- Total-error arithmetic.
    exact total_error_le (fun i => (phases i).ε) δ hε

/-! ## Headline corollary: O(log n)-parallel whp bound -/

/-- **Headline (modulo the eleven opaque instances).**

Specializing the constants: if every per-phase constant satisfies `Cphase i ≤ C0`
and the total error budget is `∑ δ ≤ 1/n`, then the composed eleven-phase chain
reaches `majorityStableEndpoint init` within `T ≤ 11 · C0 · n · (L+1)` interactions
with failure probability at most `1/n`.

`T ≤ 11 · C0 · n · (L+1)` means `O(n · (L+1)) = O(n log n)` interactions, i.e.
`O(L+1) = O(log n)` parallel time; failure `≤ 1/n` is the with-high-probability
guarantee. The whole headline therefore reduces to producing the eleven
correctly-scaled phase instances. -/
theorem doty_time_headline
    {L K n C0 : ℕ}
    (init c₀ : Config (AgentState L K))
    (Cphase : Fin 11 → ℕ) (δ : Fin 11 → ℝ≥0)
    (phases : Fin 11 → PhaseConvergence (NonuniformMajority L K).transitionKernel)
    (ht : ∀ i, (phases i).t ≤ Cphase i * n * (L + 1))
    (hε : ∀ i, ((phases i).ε : ℝ≥0∞) ≤ (δ i : ℝ≥0∞))
    (h_chain : ∀ (i : Fin 11) (hi : i.val + 1 < 11),
        ∀ x, (phases i).Post x → (phases ⟨i.val + 1, hi⟩).Pre x)
    (hx₀ : (phases ⟨0, by omega⟩).Pre c₀)
    (h_post : ∀ c, (phases lastPhase).Post c → majorityStableEndpoint (L := L) (K := K) init c)
    (hC0 : ∀ i, Cphase i ≤ C0)
    (hδ : (∑ i, (δ i : ℝ≥0∞)) ≤ (1 / n : ℝ≥0∞)) :
    ((NonuniformMajority L K).transitionKernel ^ (∑ i, (phases i).t)) c₀
        {c | ¬ majorityStableEndpoint (L := L) (K := K) init c}
      ≤ (1 / n : ℝ≥0∞)
    ∧ (∑ i, (phases i).t) ≤ 11 * C0 * n * (L + 1) := by
  obtain ⟨h_bound, h_time, h_err⟩ :=
    doty_time_composition init c₀ Cphase δ phases ht hε h_chain hx₀ h_post
  refine ⟨?_, ?_⟩
  · -- failure ≤ ∑ ε ≤ ∑ δ ≤ 1/n
    calc ((NonuniformMajority L K).transitionKernel ^ (∑ i, (phases i).t)) c₀
            {c | ¬ majorityStableEndpoint (L := L) (K := K) init c}
        ≤ (∑ i, ((phases i).ε : ℝ≥0∞)) := h_bound
      _ ≤ ∑ i, (δ i : ℝ≥0∞) := h_err
      _ ≤ (1 / n : ℝ≥0∞) := hδ
  · -- T ≤ (∑ Cphase) · n · (L+1) ≤ (11·C0) · n · (L+1)
    calc (∑ i, (phases i).t)
        ≤ (∑ i, Cphase i) * n * (L + 1) := h_time
      _ ≤ (11 * C0) * n * (L + 1) := by
          have hsum : (∑ i, Cphase i) ≤ 11 * C0 := by
            calc (∑ i : Fin 11, Cphase i)
                ≤ ∑ _i : Fin 11, C0 := Finset.sum_le_sum (fun i _ => hC0 i)
              _ = 11 * C0 := by simp [Finset.sum_const, Finset.card_univ, mul_comm]
          gcongr
      _ = 11 * C0 * n * (L + 1) := by ring

end ExactMajority
