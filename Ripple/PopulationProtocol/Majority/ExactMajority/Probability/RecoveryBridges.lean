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

end ExactMajority
