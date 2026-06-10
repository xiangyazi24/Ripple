/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Phase E4 — reachable-relative recovery ladder (`ReachableLadder`)

This append-only file makes the E4 recovery surface **reachability/invariant-relative**,
discharging the doctrine verdict recorded in `HANDOFF_HLADDER.md`:

> The all-backup route is DISHONEST (the protocol has no universal force-to-phase-10;
> states without clocks have no counter-drain route).  The paper-faithful route stands,
> but the current `hLadder` of `RecoveryBridges` is *universal* over `StableDoneᶜ` — it
> covers synthetic garbage `AgentState` configs that `init` can never reach.

We replace the universal ladder hypothesis by a **reachable-relative** one, so the
recovery classifier only ever has to classify states that `init` can actually reach.

## The reachability notion

The repo already carries the kernel reachability predicate: `Protocol.Reachable`
(`Basic/PopulationProtocol.lean:89`) is the reflexive-transitive closure
`Relation.ReflTransGen P.StepRel` of the deterministic one-step relation, and
`Probability/MarkovChain.lean` already proves the bridge to the stochastic kernel:

* `stepDistOrSelf_support_reachable : c' ∈ (P.stepDistOrSelf c).support → P.Reachable c c'`
  — every one-step *support* point is deterministically reachable, hence
* `transitionKernel_pow_not_reachable_eq_zero` — the reachability closure carries
  almost-sure kernel mass for all time.

So `ReachableFrom L K init c := (NonuniformMajority L K).Reachable init c` is the kernel
reachability predicate; its one-step closure fact `hReachClosed` (reachable states' kernel
mass stays reachable) is the generic support-preservation template at `t = 1`.

## Build

Single-file only:
  `lake env lean Ripple/PopulationProtocol/Majority/ExactMajority/Probability/ReachableLadder.lean`
from the project root (deps as cached oleans).  NEVER local `lake build`.

## Main results

* `ReachableFrom`, `reachableFrom_step_closed`, `reachableFrom_kernel_closed` — the
  reachability predicate + its one-step closure (deliverable 1).
* `expected_time_from_whp_and_recovery_on` — the `J`-invariant-relative split-geometric
  E1 composition (deliverable 2), mirroring `expectedHitting_seqcomp_on`'s pattern.
* `doty_recovery_bound_via_ladder_on_reachable`, `reachable_hLadder` — the reachable-
  relative recovery cap + the 4-way regime classification skeleton (deliverable 3).
* `doty_expected_time_reachable` — the final E4 theorem consuming the reachable-relative
  ladder + the two honest protocol residuals (deliverable 4).
-/

import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.RecoveryBridges

namespace ExactMajority

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators NNReal

/-! ## Deliverable 1 — the reachability predicate and its kernel closure

`Protocol.Reachable` is the kernel reachability notion already in the repo (the
reflexive-transitive closure of `StepRel`).  We name the `init`-rooted instance and
prove the two closure facts the invariant-relative engines consume:

* `reachableFrom_step_closed` — reachable-from-`init` is preserved across one *support*
  step (the `stepDistOrSelf` support-preservation hypothesis shape);
* `reachableFrom_kernel_closed` — the kernel one-step mass off the reachable set is `0`
  (the `Engine.InvClosed` / `expectedHitting_seqcomp_on` closure hypothesis `hClosed`),
  derived from the support closure via the generic preservation template at `t = 1`. -/

/-- **Reachable-from-`init`.**  The kernel reachability predicate of
`HANDOFF_HLADDER.md` §0: `c` is reachable from `init` under the deterministic step
relation (equivalently, a.e.-reachable under the stochastic kernel by
`transitionKernel_pow_not_reachable_eq_zero`). -/
def ReachableFrom (L K : ℕ) (init c : Config (AgentState L K)) : Prop :=
  (NonuniformMajority L K).Reachable init c

/-- **One-step support closure of `ReachableFrom`.**  If `c` is reachable from `init`
and `c'` is a one-step `stepDistOrSelf` support point of `c`, then `c'` is reachable
from `init` (compose `Reachable init c` with the single deterministic step
`Reachable c c'`).  This is the support-preservation hypothesis the generic kernel
template consumes. -/
theorem reachableFrom_step_closed {L K : ℕ} (init c c' : Config (AgentState L K))
    (hc : ReachableFrom L K init c)
    (hsupp : c' ∈ ((NonuniformMajority L K).stepDistOrSelf c).support) :
    ReachableFrom L K init c' :=
  Relation.ReflTransGen.trans hc
    (Protocol.stepDistOrSelf_support_reachable (NonuniformMajority L K) c c' hsupp)

/-- **Kernel one-step closure of `ReachableFrom`** (the `InvClosed` / `hClosed` shape).
From a reachable-from-`init` state, the kernel mass landing on the *non*-reachable set
is `0`.  Derived from `reachableFrom_step_closed` through the generic support-step
preservation template at `t = 1` (`K ^ 1 = K`).  This is exactly the invariant-closure
hypothesis the invariant-relative recovery/seqcomp engines consume with
`J := ReachableFrom L K init`. -/
theorem reachableFrom_kernel_closed {L K : ℕ} (init : Config (AgentState L K))
    (b : Config (AgentState L K)) (hb : ReachableFrom L K init b) :
    (NonuniformMajority L K).transitionKernel b
      {x | ¬ ReachableFrom L K init x} = 0 := by
  have h := Protocol.transitionKernel_pow_not_pred_eq_zero_of_stepDistOrSelf_support_preserved
    (NonuniformMajority L K) (ReachableFrom L K init)
    (fun c c' hc hsupp => reachableFrom_step_closed init c c' hc hsupp) b hb 1
  rwa [pow_one] at h

/-! ## Deliverable 2 — the `J`-invariant-relative split-geometric (E1 composition)

`DotyExpectedTime.expected_time_from_whp_and_recovery` is the conditioning-free split
that turns `(whp horizon δgood) + (uniform recovery cap B over Doneᶜ)` into the
expected-time bound `Tgood + δgood·sRecover·(1−1/2)⁻¹`.  Its recovery cap `hRecover` is
universal over `Doneᶜ`.  We provide the **`J`-invariant-relative** analogue: the
recovery cap is required only on `J`-states (and the whp start `c₀` satisfies `J`), with
`J` one-step closed so the block restart stays inside `J`.

The proof mirrors `expectedHitting_seqcomp_on`'s invariant-relative pattern: every
ingredient of the absolute split-geometric has a landed `_on` analogue in
`ExpectedHitting.lean` (`bad_block_contracts_from_on`, `bad_antitone_le_on`,
`pow_compl_inv_eq_zero_eh`, `bad_le_half_of_expectedHitting_on`).  We assemble the
`_on` block-geometric tail from these, then run the same `expectedHitting_split` shell. -/

section InvariantRelativeSplit

variable {α : Type*} [MeasurableSpace α] [DiscreteMeasurableSpace α]

/-- **Geometric tail from a base horizon (invariant-relative).**  The `J`-relative
analogue of `bad_block_geometric_from`: from a `J`-start `c₀` with `Done` `J`-absorbing
and uniform `J`-relative `s`-block failure `≤ q`, the not-done mass at `t₀ + k·s` decays
as `(K^t₀) c₀ Doneᶜ · q^k`.  Each block step is `bad_block_contracts_from_on` with the
base `J`-mass supplied by `pow_compl_inv_eq_zero_eh` (the `J`-start carries `J` a.e.
through every power). -/
theorem bad_block_geometric_from_on
    (K : Kernel α α) [IsMarkovKernel K]
    (J : α → Prop) (hClosed : ∀ b : α, J b → K b {x | ¬ J x} = 0)
    {Done : Set α} (hDone : MeasurableSet Done)
    (hAbs : ∀ x ∈ Done, J x → K x Doneᶜ = 0)
    (s : ℕ) (q : ℝ≥0∞)
    (hblock : ∀ b : α, J b → b ∈ (Doneᶜ : Set α) → (K ^ s) b Doneᶜ ≤ q)
    (c₀ : α) (hJc₀ : J c₀) (t₀ k : ℕ) :
    (K ^ (t₀ + k * s)) c₀ Doneᶜ ≤ (K ^ t₀) c₀ Doneᶜ * q ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
      have hJ_at : (K ^ (t₀ + k * s)) c₀ {x | ¬ J x} = 0 :=
        pow_compl_inv_eq_zero_eh K J hClosed c₀ hJc₀ (t₀ + k * s)
      calc (K ^ (t₀ + (k + 1) * s)) c₀ Doneᶜ
          = (K ^ ((t₀ + k * s) + s)) c₀ Doneᶜ := by
            rw [show t₀ + (k + 1) * s = (t₀ + k * s) + s from by ring]
        _ ≤ q * (K ^ (t₀ + k * s)) c₀ Doneᶜ :=
            bad_block_contracts_from_on K J hClosed hDone hAbs s q hblock c₀ (t₀ + k * s) hJ_at
        _ ≤ q * ((K ^ t₀) c₀ Doneᶜ * q ^ k) := by gcongr
        _ = (K ^ t₀) c₀ Doneᶜ * q ^ (k + 1) := by rw [pow_succ]; ring

/-- **Shifted-tail block bound (invariant-relative).**  The `J`-relative analogue of
`tail_le_block`: from a `J`-start, the shifted not-done tail is dominated by `s` times
its `s`-block subsequence.  The per-term antitonicity is `bad_antitone_le_on` (valid
from the `J`-start). -/
theorem tail_le_block_on
    (K : Kernel α α) [IsMarkovKernel K]
    (J : α → Prop) (hClosed : ∀ b : α, J b → K b {x | ¬ J x} = 0)
    {Done : Set α} (hDone : MeasurableSet Done)
    (hAbs : ∀ x ∈ Done, J x → K x Doneᶜ = 0)
    (c : α) (hJc : J c) (t₀ s : ℕ) (hs : s ≠ 0) :
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
      apply bad_antitone_le_on K J hClosed hDone hAbs c hJc
      simp only [Nat.divModEquiv_symm_apply]
      omega
    calc ∑' j : Fin s, (K ^ (t₀ + (Nat.divModEquiv s).symm (k, j))) c Doneᶜ
        ≤ ∑' _ : Fin s, (K ^ (t₀ + k * s)) c Doneᶜ := ENNReal.tsum_le_tsum hkey
      _ = (s : ℝ≥0∞) * (K ^ (t₀ + k * s)) c Doneᶜ := by rw [ENNReal.tsum_const]; simp
  calc ∑' (k : ℕ) (j : Fin s), (K ^ (t₀ + (Nat.divModEquiv s).symm (k, j))) c Doneᶜ
      ≤ ∑' k : ℕ, (s : ℝ≥0∞) * (K ^ (t₀ + k * s)) c Doneᶜ := ENNReal.tsum_le_tsum hinner
    _ = (s : ℝ≥0∞) * ∑' k : ℕ, (K ^ (t₀ + k * s)) c Doneᶜ := by rw [ENNReal.tsum_mul_left]

/-- **Combined split + geometric (invariant-relative).**  The `J`-relative analogue of
`expectedHitting_split_geometric`: from a `J`-start `c₀` with `Done` `J`-absorbing,
uniform `J`-relative `s`-block failure `≤ q` and whp horizon `(K^t₀) c₀ Doneᶜ ≤ δ`,

    E[T] ≤ t₀ + δ · s · (1 − q)⁻¹.

The split shell `expectedHitting_split` is hypothesis-free; only the tail estimate is
`J`-relative (assembled from `tail_le_block_on` + `bad_block_geometric_from_on`). -/
theorem expectedHitting_split_geometric_on
    (K : Kernel α α) [IsMarkovKernel K]
    (J : α → Prop) (hClosed : ∀ b : α, J b → K b {x | ¬ J x} = 0)
    {Done : Set α} (hDone : MeasurableSet Done)
    (hAbs : ∀ x ∈ Done, J x → K x Doneᶜ = 0)
    (s : ℕ) (hs : s ≠ 0) (q : ℝ≥0∞)
    (hblock : ∀ b : α, J b → b ∈ (Doneᶜ : Set α) → (K ^ s) b Doneᶜ ≤ q)
    (c₀ : α) (hJc₀ : J c₀) (t₀ : ℕ) (δ : ℝ≥0∞) (hδ : (K ^ t₀) c₀ Doneᶜ ≤ δ) :
    expectedHitting K c₀ Done ≤ (t₀ : ℝ≥0∞) + δ * s * (1 - q)⁻¹ := by
  have htail : ∑' t : ℕ, (K ^ (t₀ + t)) c₀ Doneᶜ ≤ δ * s * (1 - q)⁻¹ := by
    calc ∑' t : ℕ, (K ^ (t₀ + t)) c₀ Doneᶜ
        ≤ (s : ℝ≥0∞) * ∑' k : ℕ, (K ^ (t₀ + k * s)) c₀ Doneᶜ :=
          tail_le_block_on K J hClosed hDone hAbs c₀ hJc₀ t₀ s hs
      _ ≤ (s : ℝ≥0∞) * ∑' k : ℕ, δ * q ^ k := by
          gcongr with k
          calc (K ^ (t₀ + k * s)) c₀ Doneᶜ
              ≤ (K ^ t₀) c₀ Doneᶜ * q ^ k :=
                bad_block_geometric_from_on K J hClosed hDone hAbs s q hblock c₀ hJc₀ t₀ k
            _ ≤ δ * q ^ k := by gcongr
      _ = (s : ℝ≥0∞) * (δ * (1 - q)⁻¹) := by rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric]
      _ = δ * s * (1 - q)⁻¹ := by ring
  calc expectedHitting K c₀ Done
      ≤ (t₀ : ℝ≥0∞) + ∑' t : ℕ, (K ^ (t₀ + t)) c₀ Doneᶜ :=
        expectedHitting_split K c₀ Done t₀
    _ ≤ (t₀ : ℝ≥0∞) + δ * s * (1 - q)⁻¹ := by gcongr

/-- **Per-block half-failure from a `J`-relative recovery cap.**  The `J`-relative
analogue of `block_half_from_recovery_expected`: if every not-done `J`-state recovers in
expected time `≤ B` and `B·2 ≤ s`, the `s`-block fails with probability `≤ 1/2`, on
`J`-states.  This is `bad_le_half_of_expectedHitting_on`, packaged uniformly. -/
theorem block_half_from_recovery_expected_on
    (K : Kernel α α) [IsMarkovKernel K]
    (J : α → Prop) (hClosed : ∀ b : α, J b → K b {x | ¬ J x} = 0)
    {Done : Set α} (hDone : MeasurableSet Done)
    (hAbs : ∀ x ∈ Done, J x → K x Doneᶜ = 0)
    (B : ℝ≥0∞) (hBfin : B ≠ ⊤)
    (s : ℕ) (hspos : 0 < s)
    (hs : B * 2 ≤ (s : ℝ≥0∞))
    (hRecover : ∀ b : α, J b → b ∈ (Doneᶜ : Set α) → expectedHitting K b Done ≤ B) :
    ∀ b : α, J b → b ∈ (Doneᶜ : Set α) → (K ^ s) b Doneᶜ ≤ (1 / 2 : ℝ≥0∞) := by
  intro b hJb hb
  exact bad_le_half_of_expectedHitting_on K J hClosed hDone hAbs b hJb s hspos B hBfin
    (hRecover b hJb hb) hs

/-- **Expected time from the whp horizon plus a `J`-relative recovery cap (E1, `_on`).**

The invariant-relative analogue of `expected_time_from_whp_and_recovery` (blueprint §4.2,
the version `HANDOFF_HLADDER.md` §4 asks for): from a `J`-start `c₀` with `J` one-step
closed and `Done` `J`-absorbing, the whp failure mass `(K^Tgood) c₀ Doneᶜ ≤ δgood`, and a
recovery cap `expectedHitting K b Done ≤ B` for every *not-done `J`-state* `b` (block
`sRecover`, `B·2 ≤ sRecover`), gives

    E[T] ≤ Tgood + δgood · sRecover · (1 − 1/2)⁻¹.

`J`'s one-step closure keeps every block restart inside `J`, so the Markov half-tail bound
only ever needs the `J`-relative recovery cap — avoiding any demand on unreachable garbage
states.  Same proof shape as the absolute version, with the `_on` block half-failure +
`_on` split-geometric. -/
theorem expected_time_from_whp_and_recovery_on
    (K : Kernel α α) [IsMarkovKernel K]
    (J : α → Prop) (hClosed : ∀ b : α, J b → K b {x | ¬ J x} = 0)
    (c₀ : α) (hJc₀ : J c₀) {Done : Set α} (hDone : MeasurableSet Done)
    (hAbs : ∀ x ∈ Done, J x → K x Doneᶜ = 0)
    (Tgood sRecover : ℕ) (hsRecover : sRecover ≠ 0)
    (δgood B : ℝ≥0∞)
    (hBfin : B ≠ ⊤)
    (hspos : 0 < sRecover)
    (hs : B * 2 ≤ (sRecover : ℝ≥0∞))
    (hδ : (K ^ Tgood) c₀ Doneᶜ ≤ δgood)
    (hRecover : ∀ b : α, J b → b ∈ (Doneᶜ : Set α) → expectedHitting K b Done ≤ B) :
    expectedHitting K c₀ Done
      ≤ (Tgood : ℝ≥0∞) + δgood * sRecover * (1 - (1 / 2 : ℝ≥0∞))⁻¹ := by
  have hblock :
      ∀ b : α, J b → b ∈ (Doneᶜ : Set α) → (K ^ sRecover) b Doneᶜ ≤ (1 / 2 : ℝ≥0∞) :=
    block_half_from_recovery_expected_on K J hClosed hDone hAbs B hBfin sRecover hspos hs
      hRecover
  exact expectedHitting_split_geometric_on K J hClosed hDone hAbs
    sRecover hsRecover (1 / 2 : ℝ≥0∞) hblock c₀ hJc₀ Tgood δgood hδ

end InvariantRelativeSplit

end ExactMajority
