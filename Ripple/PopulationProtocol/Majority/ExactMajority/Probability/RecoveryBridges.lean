/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Phase E4 — recovery bridges (`RecoveryBridges`)

This append-only file attacks the two residuals left by `DotyExpectedTime.lean`:

1. **The progress-set → `StableDone` transfer** (the material residual).  The E3
   per-phase wrappers conclude `expectedHitting K c (Engine.potBelow Φ 1) ≤ bound`
   (expected time to drain the *current* phase's clock counters), not to reach the
   global `StableDone`.  We supply the honest tool: an **expected-hitting
   sequential-composition (tower) lemma**

       E[T to Done from c]  ≤  E[T to Mid from c]  +  sup_{y ∈ Mid} E[T to Done from y].

   The cross-term `sup_{y ∈ Mid} E[T to Done]` is exactly the band occupation already
   bounded by E1's `occupation_mid_le` / `occupation_mid_le_on`; the through-`Mid`
   term is `expectedHitting K c Mid`.  Telescoping this tower along the phase chain
   `Mid₀ ⊇ Mid₁ ⊇ … ⊇ StableDone` sums the per-phase E3 bounds into a `StableDone`
   expected-hitting cap — giving each `RecoveryClass` branch's witness from the E3
   facts + the phase-chain `Post`s, instead of carrying it as constructor data.

2. **`hClassify`** (the deterministic classification of every reachable not-done
   state).  We deliver the strongest *honest* classification reachable from the
   facts that exist, and state precisely what genuinely needs reachability facts not
   yet available.

## Build

Single-file only:
  `lake env lean Ripple/PopulationProtocol/Majority/ExactMajority/Probability/RecoveryBridges.lean`
from the project root (deps as cached oleans).  NEVER local `lake build`.

## Main results

* `expectedHitting_le_band_free` — the hypothesis-free band tower (Stage 1).
* `expectedHitting_seqcomp` / `expectedHitting_seqcomp_of_uniform` — the collapsed
  uniform sequential-composition cap consumed by the telescope.
* `expectedHitting_seqcomp_on` / `expectedHitting_seqcomp_on_of_uniform` — the
  invariant-relative analogues (the `_on` ladder).
-/

import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.DotyExpectedTime

namespace ExactMajority

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators NNReal

variable {α : Type*} [MeasurableSpace α]

/-! ## Stage 1 — the expected-hitting sequential-composition (tower) lemma

### What already exists (the engine is NOT missing)

The campaign's `ExpectedHitting.lean` (Part 6) already proves the band-occupation
engine `occupation_mid_le` / `occupation_mid_le_on` (the invariant-relative `_on`
ladder), and `Phase10ExpectedTime.lean:128` already proves the band *tower*
`expectedHitting_le_through_mid` (with the cross-term left as the explicit band
occupation `∑' t, (K^t) c (Mid ∩ Doneᶜ)`).  So the sequential-composition engine
existed; what was missing was the **collapsed uniform form** that composes the band
tower with the band-occupation cap into the single consumable inequality

    E[T to Done from c]  ≤  E[T to Mid from c]  +  B          (uniform `B` over `Mid`)

and its invariant-relative analogue.  We assemble exactly those here, reusing the
existing engine (no re-proof of the band split).

The band split holds with NO subset hypothesis (`Phase10ExpectedTime`'s tower carries
a defensive `Done ⊆ Mid`, which is unnecessary for the split itself); we restate the
hypothesis-free band tower under a fresh name so the collapsed forms below do not
inherit the subset side condition (the phase telescope's `Mid = potBelow Φ 1` does
contain `StableDone`, but threading that fact is the protocol residual we want to
isolate, not assume in the engine). -/

/-- **Hypothesis-free band tower.** For any `Mid`, `Done`,

    E[T to Done]  ≤  E[T to Mid]  +  ∑' t, (K^t) c (Mid ∩ Doneᶜ).

Pure mass split (`Doneᶜ ⊆ Midᶜ ∪ (Mid ∩ Doneᶜ)`), no `Done ⊆ Mid` needed.  The
cross-term is the `Mid ∩ Doneᶜ` band occupation. -/
theorem expectedHitting_le_band_free (K : Kernel α α)
    (c : α) (Mid Done : Set α) :
    expectedHitting K c Done
      ≤ expectedHitting K c Mid + ∑' t : ℕ, (K ^ t) c (Mid ∩ Doneᶜ) := by
  rw [expectedHitting_eq_tsum, expectedHitting_eq_tsum, ← ENNReal.tsum_add]
  refine ENNReal.tsum_le_tsum (fun t => ?_)
  have hsub : (Doneᶜ : Set α) ⊆ Midᶜ ∪ (Mid ∩ Doneᶜ) := by
    intro x hx
    by_cases hm : x ∈ Mid
    · exact Or.inr ⟨hm, hx⟩
    · exact Or.inl hm
  calc (K ^ t) c Doneᶜ
      ≤ (K ^ t) c (Midᶜ ∪ (Mid ∩ Doneᶜ)) := measure_mono hsub
    _ ≤ (K ^ t) c Midᶜ + (K ^ t) c (Mid ∩ Doneᶜ) := measure_union_le _ _

/-- **Sequential-composition cap (collapsed tower).**

If from every `Mid`-state the expected hitting time of `Done` is `≤ B`, then for any
start `c`,

    E[T to Done from c]  ≤  E[T to Mid from c]  +  B.

The honest progress-set ⟹ `Done` transfer: `Mid` = the intermediate hitting set (the
phase-`(p+1)` start window / next progress set), `E[T to Mid]` = time to finish the
current phase, `B` = the remaining expected time to `Done` from any `Mid`-entry.  The
cross-term is discharged by E1's `occupation_mid_le`. -/
theorem expectedHitting_seqcomp [DiscreteMeasurableSpace α]
    (K : Kernel α α) [IsMarkovKernel K]
    {Mid Done : Set α} (hMid : MeasurableSet Mid) (hDone : MeasurableSet Done)
    (B : ℝ≥0∞) (hB : ∀ y ∈ Mid, expectedHitting K y Done ≤ B)
    (c : α) :
    expectedHitting K c Done ≤ expectedHitting K c Mid + B := by
  calc expectedHitting K c Done
      ≤ expectedHitting K c Mid + ∑' t : ℕ, (K ^ t) c (Mid ∩ Doneᶜ) :=
        expectedHitting_le_band_free K c Mid Done
    _ ≤ expectedHitting K c Mid + B := by
        gcongr; exact occupation_mid_le K hMid hDone B hB c

/-- **Sequential composition with a uniform `Mid`-time cap.**

The fully-collapsed form consumed by the phase telescope: if `E[T to Mid from c] ≤ A`
and from every `Mid`-state `E[T to Done] ≤ B`, then `E[T to Done from c] ≤ A + B`. -/
theorem expectedHitting_seqcomp_of_uniform [DiscreteMeasurableSpace α]
    (K : Kernel α α) [IsMarkovKernel K]
    {Mid Done : Set α} (hMid : MeasurableSet Mid) (hDone : MeasurableSet Done)
    (A B : ℝ≥0∞) (c : α) (hA : expectedHitting K c Mid ≤ A)
    (hB : ∀ y ∈ Mid, expectedHitting K y Done ≤ B) :
    expectedHitting K c Done ≤ A + B := by
  calc expectedHitting K c Done
      ≤ expectedHitting K c Mid + B := expectedHitting_seqcomp K hMid hDone B hB c
    _ ≤ A + B := by gcongr

/-- **Sequential composition (invariant-relative).**

The `_on` ladder: from a `J`-start `c` (with `J` one-step-closed), if from every
`Mid`-state that *also* satisfies `J` the expected hitting time of `Done` is `≤ B`,
then `E[T to Done from c] ≤ E[T to Mid from c] + B`.  Uses E1's invariant-relative
band occupation `occupation_mid_le_on`. -/
theorem expectedHitting_seqcomp_on [DiscreteMeasurableSpace α]
    (K : Kernel α α) [IsMarkovKernel K]
    (J : α → Prop) (hClosed : ∀ b : α, J b → K b {x | ¬ J x} = 0)
    {Mid Done : Set α} (hMid : MeasurableSet Mid) (hDone : MeasurableSet Done)
    (B : ℝ≥0∞) (hB : ∀ y : α, J y → y ∈ Mid → expectedHitting K y Done ≤ B)
    (c : α) (hJc : J c) :
    expectedHitting K c Done ≤ expectedHitting K c Mid + B := by
  calc expectedHitting K c Done
      ≤ expectedHitting K c Mid + ∑' t : ℕ, (K ^ t) c (Mid ∩ Doneᶜ) :=
        expectedHitting_le_band_free K c Mid Done
    _ ≤ expectedHitting K c Mid + B := by
        gcongr; exact occupation_mid_le_on K J hClosed hMid hDone B hB c hJc

/-- **Sequential composition (invariant-relative, uniform `Mid`-time cap).**  The
collapsed `_on` form: `E[T to Mid] ≤ A`, `J`-relative `Mid`→`Done` cap `≤ B` ⟹
`E[T to Done] ≤ A + B`. -/
theorem expectedHitting_seqcomp_on_of_uniform [DiscreteMeasurableSpace α]
    (K : Kernel α α) [IsMarkovKernel K]
    (J : α → Prop) (hClosed : ∀ b : α, J b → K b {x | ¬ J x} = 0)
    {Mid Done : Set α} (hMid : MeasurableSet Mid) (hDone : MeasurableSet Done)
    (A B : ℝ≥0∞) (c : α) (hJc : J c) (hA : expectedHitting K c Mid ≤ A)
    (hB : ∀ y : α, J y → y ∈ Mid → expectedHitting K y Done ≤ B) :
    expectedHitting K c Done ≤ A + B := by
  calc expectedHitting K c Done
      ≤ expectedHitting K c Mid + B :=
        expectedHitting_seqcomp_on K J hClosed hMid hDone B hB c hJc
    _ ≤ A + B := by gcongr

/-! ## Stage 2 — clock-role preservation (the honest fact)

### What "clock-role preservation" actually is, honestly

The paper's "clocks are never destroyed" reads, in this formalization, as the
preservation of the engine invariant

    `AllClockGEpCard p n c  :=  (∀ a ∈ c, a.role = .clock ∧ p ≤ a.phase.val) ∧ c.card = n`

— **every** agent is a clock at phase `≥ p`, with fixed population `n`.  This is the
*post-role-split* regime (after Phase 0 turns the working population into clocks); it
is NOT a property of an arbitrary reachable not-done state (which may still hold
main/reserve roles).  The honest preservation fact is therefore:

> From a state satisfying `AllClockGEpCard p n`, the role+phase-floor invariant
> persists under the kernel for all time (`3 ≤ p`).

The campaign already proves the engine atom:

* `ConditionalPhaseProgress.AllClockGEp_absorbing` — `AllClockGEp p` is **one-step
  support closed** (`3 ≤ p`): the clock-clock per-pair fact `Transition_clock_pair`
  (a clock-clock interaction produces two clocks) plus the phase-`max` floor.
* `ConditionalPhaseProgress.AllClockGEpCard_InvClosed` — the kernel `InvClosed` form
  (support closure + card conservation `stepDistOrSelf_support_card_eq`).

`AllClockGEpCard_InvClosed` is *exactly* the `Engine.InvClosed` hypothesis the
invariant-relative telescope engine (`expectedHitting_seqcomp_on`, E1's `_on` ladder)
consumes — so for the per-phase telescope (Stage 3) the clock-role preservation we
need is already in hand.  Below we additionally package the **all-time** kernel-power
form (every `(K^t)`-reachable state a.e. satisfies the invariant), the form a future
`hClassify` derivation would consume, built from the same support closure via the
generic `transitionKernel_pow_not_pred_eq_zero_of_stepDistOrSelf_support_preserved`. -/

open ConditionalPhaseProgress in
/-- **`AllClockGEpCard p n` is one-step support closed** (re-export of the engine atom
as a plain support-step predicate, the shape the generic kernel-power preservation
template consumes).  `3 ≤ p`. -/
theorem allClockGEpCard_support_step_closed {L K : ℕ} (p n : ℕ) (hp : 3 ≤ p)
    (c c' : Config (AgentState L K))
    (hc : AllClockGEpCard (L := L) (K := K) p n c)
    (hsupp : c' ∈ ((NonuniformMajority L K).stepDistOrSelf c).support) :
    AllClockGEpCard (L := L) (K := K) p n c' :=
  ⟨AllClockGEp_absorbing (L := L) (K := K) p hp c c' hc.1 hsupp,
    by rw [Protocol.stepDistOrSelf_support_card_eq (NonuniformMajority L K) c c' hsupp]; exact hc.2⟩

open ConditionalPhaseProgress in
/-- **All-time clock-role preservation.** From an `AllClockGEpCard p n` start `c`
(`3 ≤ p`), the not-invariant mass under every kernel power vanishes: the trajectory
stays a.e. on `AllClockGEpCard p n` for all `t`.  Honest statement of "clocks are
never destroyed after Phase 0", at the kernel level.  Built from the support closure
`allClockGEpCard_support_step_closed` and the generic preservation template. -/
theorem allClockGEpCard_pow_preserved {L K : ℕ} (p n : ℕ) (hp : 3 ≤ p)
    (c : Config (AgentState L K))
    (hc : AllClockGEpCard (L := L) (K := K) p n c) (t : ℕ) :
    ((NonuniformMajority L K).transitionKernel ^ t) c
        {x | ¬ AllClockGEpCard (L := L) (K := K) p n x} = 0 :=
  Protocol.transitionKernel_pow_not_pred_eq_zero_of_stepDistOrSelf_support_preserved
    (NonuniformMajority L K) (AllClockGEpCard (L := L) (K := K) p n)
    (fun a b ha hb => allClockGEpCard_support_step_closed p n hp a b ha hb) c hc t

/-! ## Stage 3 — the per-phase telescope (`StableDone` cap from per-link caps)

The seqcomp tower composes a SINGLE intermediate set.  The phase chain has many: the
run must drain phase `p`'s clock counters (reach `S p := potBelow (clockCounterSumAt p) 1`),
then phase `p+1`'s, …, finally landing in `StableDone`.  We iterate the tower along a
descending ladder `S : ℕ → Set α` with `S k = Done`:

* per link `i < k`: from every `S i`-state the expected hitting time of the NEXT rung
  `S (i+1)` is `≤ b i` (this is exactly an E3/E2 per-phase factor, applied at the rung
  whose progress set is `S (i+1)`);

then from any `S i`-state the expected hitting time of `Done` is `≤ ∑_{i ≤ j < k} b j`,
and in particular from an `S 0`-start it is `≤ ∑ b`.

This is the honest progress-set ⟹ `StableDone` transfer for the recovery branches: the
`RecoveryClass` witness `expectedHitting … StableDone ≤ B` is *derived* by instantiating
the ladder with the campaign's per-phase progress sets and E3/E2 bounds, with
`Done = StableDone`, instead of being carried as constructor data.

The proof is a downward induction on the rung index using `expectedHitting_seqcomp`. -/

/-- **Expected hitting time from inside an absorbing set is `0`.**  If `Done` is
absorbing then every `Done`-state has `expectedHitting K y Done = 0` (the not-Done
tail is identically `0`). -/
theorem expectedHitting_eq_zero_of_mem [DiscreteMeasurableSpace α]
    (K : Kernel α α) [IsMarkovKernel K]
    {Done : Set α} (hDone : MeasurableSet Done)
    (hAbs : ∀ x ∈ Done, K x Doneᶜ = 0) {y : α} (hy : y ∈ Done) :
    expectedHitting K y Done = 0 := by
  rw [expectedHitting_eq_tsum]
  refine ENNReal.tsum_eq_zero.mpr (fun t => ?_)
  exact pow_absorbing K hDone hAbs t hy

/-- **Finite ladder telescope (`StableDone` cap from per-link caps).**

For a descending ladder `S : ℕ → Set α` of measurable sets with top rung `S k = Done`
(`Done` absorbing), and per-link uniform caps `∀ y ∈ S i, E[T to S (i+1)] ≤ b i`
(`i < k`), every `S i`-state hits `Done` in expected time `≤ ∑_{i ≤ j < k} b j`.

Each tower step `E[T to Done from y] ≤ E[T to S(i+1) from y] + sup_{S(i+1)} E[T to Done]`
(`expectedHitting_seqcomp`) has its cross-term supplied by the inductive hypothesis at
the next rung and its through-term by the per-link cap; the base `i = k` is
`E[T to Done from a Done-state] = 0` (absorption).  This is the iterated seqcomp that
turns the E3/E2 per-phase progress bounds into a single `StableDone` cap. -/
theorem expectedHitting_ladder_le [DiscreteMeasurableSpace α]
    (K : Kernel α α) [IsMarkovKernel K]
    (S : ℕ → Set α) (hS : ∀ i, MeasurableSet (S i))
    (k : ℕ) {Done : Set α} (hDone : MeasurableSet Done)
    (hAbs : ∀ x ∈ Done, K x Doneᶜ = 0) (hSk : S k = Done)
    (b : ℕ → ℝ≥0∞)
    (hlink : ∀ i, i < k → ∀ y ∈ S i, expectedHitting K y (S (i + 1)) ≤ b i)
    (i : ℕ) (hik : i ≤ k) :
    ∀ y ∈ S i, expectedHitting K y Done ≤ ∑ j ∈ Finset.Ico i k, b j := by
  -- Downward induction on the distance `d = k - i`, keeping `k` fixed.
  induction hd : k - i generalizing i with
  | zero =>
      intro y hy
      have hik0 : i = k := by omega
      rw [hik0, Finset.Ico_self, Finset.sum_empty]
      -- y ∈ S k = Done; absorption gives expectedHitting = 0.
      rw [hik0, hSk] at hy
      rw [expectedHitting_eq_zero_of_mem K hDone hAbs hy]
  | succ d ih =>
      intro y hy
      have hilt : i < k := by omega
      -- IH at rung i+1: every S(i+1)-state hits Done in ≤ ∑_{i+1 ≤ j < k} b j.
      have hih : ∀ z ∈ S (i + 1), expectedHitting K z Done
          ≤ ∑ j ∈ Finset.Ico (i + 1) k, b j := by
        intro z hz
        exact ih (i + 1) (by omega) (by omega) z hz
      -- Tower with Mid = S(i+1): E[T→Done] ≤ E[T→S(i+1)] + (∑_{i+1≤j<k} b j).
      have htower := expectedHitting_seqcomp K (hS (i + 1)) hDone
        (∑ j ∈ Finset.Ico (i + 1) k, b j) hih y
      -- through-term: E[T→S(i+1) from y] ≤ b i.
      have hthrough : expectedHitting K y (S (i + 1)) ≤ b i := hlink i hilt y hy
      -- re-fold the sum: b i + ∑_{i+1≤j<k} = ∑_{i≤j<k}.
      have hsum : b i + ∑ j ∈ Finset.Ico (i + 1) k, b j = ∑ j ∈ Finset.Ico i k, b j := by
        rw [Finset.sum_eq_sum_Ico_succ_bot hilt]
      calc expectedHitting K y Done
          ≤ expectedHitting K y (S (i + 1)) + ∑ j ∈ Finset.Ico (i + 1) k, b j := htower
        _ ≤ b i + ∑ j ∈ Finset.Ico (i + 1) k, b j := by gcongr
        _ = ∑ j ∈ Finset.Ico i k, b j := hsum

/-- **`StableDone` cap from an `S 0`-start (the consumed form).**

The telescope at rung `0`: from any `S 0`-state, `E[T to Done] ≤ ∑_{0 ≤ j < k} b j`.
This is the `RecoveryClass`-witness derivation: take `Done = StableDone`, `S j` the
campaign's per-phase progress sets ending at `StableDone`, and `b j` the E3/E2
per-phase bounds; the constructor data `expectedHitting … StableDone ≤ B` becomes a
theorem with `B = ∑ b j`. -/
theorem expectedHitting_telescope_from_start [DiscreteMeasurableSpace α]
    (K : Kernel α α) [IsMarkovKernel K]
    (S : ℕ → Set α) (hS : ∀ i, MeasurableSet (S i))
    (k : ℕ) {Done : Set α} (hDone : MeasurableSet Done)
    (hAbs : ∀ x ∈ Done, K x Doneᶜ = 0) (hSk : S k = Done)
    (b : ℕ → ℝ≥0∞)
    (hlink : ∀ i, i < k → ∀ y ∈ S i, expectedHitting K y (S (i + 1)) ≤ b i)
    (c : α) (hc : c ∈ S 0) :
    expectedHitting K c Done ≤ ∑ j ∈ Finset.range k, b j := by
  have h := expectedHitting_ladder_le K S hS k hDone hAbs hSk b hlink 0 (Nat.zero_le k) c hc
  rwa [Finset.range_eq_Ico]

end ExactMajority
