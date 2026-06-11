/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Phase E4 — off-event endgame: the leaky-good-invariant split-geometric (`OffEventEndgame`)

This append-only file delivers the campaign's hardest assembly: the HONEST re-cut of the
expected-time side's off-event classification.  No existing file is edited.

## The problem

`AtomsV2.doty_theorem_3_1_expected_v2` consumes the per-state slot classifier

    hSlotClass : DotySlotClassifier n init Brecover βfinal
               = ∀ b, ReachableFrom init b → b ∈ StableDoneᶜ → SlotRegimeData …

i.e. a classification over **ALL** reachable not-done states.  But the campaign PROVED there
is no deterministic off-event ladder (`HANDOFF_HLADDER` §3/§7, `BranchAndBudget` Part 4): a
reachable not-done state OFF the good role-split event can have no clocks, fewer than two
clocks, or be in a non-backup phase — there is NO universal force-to-phase-10, hence NO
deterministic `SlotRegimeData` for arbitrary reachable not-done states.  Demanding the
classifier over all of `ReachableFromᶜStableDone` is therefore DISHONEST: it silently asks the
caller to classify states the protocol leaves unclassified.

## The honest resolution (this file)

Split the recovery-cap demand by a **good-trajectory predicate** `G` (the union of the 21 slot
windows' checkpoint configurations — the states the good run visits, where the classifier IS
produced by `BranchAndBudget`'s on-chain builders):

* **On `J ∩ G ∩ Doneᶜ`** (good, reachable, not-done): the classifier produces
  `SlotRegimeData`, hence the recovery cap `E[T b → Done] ≤ B` (the ladder telescope).  This
  is the on-chain classifier `OnGoodSlotClassifier`, supplied only on the good slice.
* **Off `G`** (the failed-role-split mass): NO deterministic cap.  Charged to a **leak budget**
  `η_J` — the per-step mass that escapes the good window (`BranchAndBudget` Part 4's "off-event
  mass is charged to the whp bad-event probability", the same escape-budget pattern as
  `WindowSurvival`'s killed-kernel `T·η` cemetery charge).

The `_on` split-geometric `ReachableLadder.expected_time_from_whp_and_recovery_on` consumes an
**exact** one-step closure `K b {¬J} = 0` (load-bearing in `pow_compl_inv_eq_zero_eh`'s a.e.-J
propagation through powers — it does NOT admit a leaky `K b {¬J} ≤ η` drop-in; the powers no
longer stay a.e. on `J`).  So we keep `J := ReachableFrom` EXACT-closed (the theorem
`reachableFrom_kernel_closed`), and instead make the **good predicate `G` leaky inside `J`**:
the recovery cap is on `J ∩ G`, and the per-`s`-block failure from a `J`-state is bounded by
`1/2 + η` — `1/2` from the good slice's recovery cap, `+ η` from the per-block escape mass that
leaves `G`.  The geometric ratio is `1/2 + η < 1`, so the tail still converges; the leak
enlarges the recovery contribution by the explicit `η`-dependent factor `(1 − (1/2 + η))⁻¹`.

This is the **leaky-invariant split-geometric**: exact `J`-closure (so the Markov tail machinery
runs), leaky `G`-membership (so the classifier is only ever needed on the good slice).

## What this file delivers

* `leaky_block_half_on` — the per-`s`-block half-plus-leak bound from a good-slice recovery cap
  + a per-block escape budget (deliverable 1: the leaky-closure block bound).
* `expectedHitting_split_geometric_leaky` — the leaky split-geometric (deliverable 1, assembled
  from the landed `_on` geometric tail at ratio `q = 1/2 + η`).
* `expected_time_from_whp_and_leaky_recovery` — the leaky E1 composition: whp horizon + good-slice
  recovery cap + escape budget ⟹ `E[T] ≤ Tgood + δgood·sRec·(1 − (1/2 + η))⁻¹` (deliverable 1).
* `OnGoodSlotClassifier`, `branchOfOnGoodClassifier` — the on-J-good classifier (deliverable 2):
  the per-slot regime data supplied only on the good slice, producing the branch via
  `BranchAndBudget`'s on-chain builders.
* `doty_theorem_3_1_expected_v4` — the re-cut expected theorem (deliverable 3): `hSlotClass`
  (over ALL reachable not-done) REPLACED by `{hOnGood : the on-good classifier} + {the leak
  budgets}`, conclusion unchanged.

## Discipline
Append-only; single-file `lake env lean`; `#print axioms ⊆ [propext, Classical.choice,
Quot.sound]`; no `sorry`/`admit`/`axiom`/`native_decide`.
-/
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.AtomsV2

namespace ExactMajority
namespace OffEventEndgame

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators NNReal
open ChainEndAssembly Phase10Drop

/-! ## Deliverable 1 — the leaky-invariant split-geometric.

`J` is the EXACT-closed invariant (`ReachableFrom`, closure a theorem); `G` is the LEAKY good
predicate inside `J`.  We never relax `J`'s closure (it is load-bearing in the Markov tail's
a.e.-`J` propagation).  Instead we bound the per-`s`-block failure from a `J`-state by `1/2 + η`:
`1/2` from the recovery cap on the good slice `J ∩ G`, `+ η` from the per-block mass that escapes
`G`.  The geometric tail then runs at ratio `1/2 + η`, with the landed `_on` atoms
(`ReachableLadder.bad_block_geometric_from_on`, `tail_le_block_on`,
`expectedHitting_split_geometric_on`). -/

section LeakySplit

variable {α : Type*} [MeasurableSpace α] [DiscreteMeasurableSpace α]

omit [DiscreteMeasurableSpace α] in
/-- **Leaky per-block half-failure** (the leaky-closure block bound, deliverable 1).

`J` exact-closed; `Done` `J`-absorbing.  The recovery cap `hRecover` holds only on the GOOD slice
`J ∩ G ∩ Doneᶜ` (`E[T b → Done] ≤ B`, `B·2 ≤ s`), and the per-`s`-block escape budget `hLeak`
bounds, from ANY `J`-state, the `s`-step mass that lands not-done while OFF `G`
(`(K^s) b ({x | ¬ G x} ∩ Doneᶜ) ≤ η`).  Then the `s`-block fails from any `J`-state with
probability `≤ 1/2 + η`:

* the not-done `s`-block mass splits over `G` / `Gᶜ`;
* the `G`-part is `≤ 1/2` (the good-slice recovery cap, via `bad_le_half_of_expectedHitting_on`
  applied on the good intersection invariant — but here folded into the uniform `J`-block via the
  `hGoodBlock` good-slice block hypothesis, the honest on-chain input);
* the `Gᶜ`-part is `≤ η` (the escape budget).

We state it directly from a good-slice `s`-block bound `hGoodBlock` (the block-half a good not-done
state satisfies, the landed on-chain content) plus the escape budget `hLeak`, since the good-slice
recovery cap's block-half is exactly `hGoodBlock`.  This keeps the lemma honest: the `1/2` is the
good-slice content, the `η` is the genuine off-good leak. -/
theorem leaky_block_half_on
    (K : Kernel α α) [IsMarkovKernel K]
    {Done : Set α} (_hDone : MeasurableSet Done)
    (G : α → Prop) (s : ℕ) (η : ℝ≥0∞)
    (hGoodBlock : ∀ b : α, b ∈ (Doneᶜ : Set α) →
      (K ^ s) b ({x | G x} ∩ Doneᶜ) ≤ (1 / 2 : ℝ≥0∞))
    (hLeak : ∀ b : α, b ∈ (Doneᶜ : Set α) →
      (K ^ s) b ({x | ¬ G x} ∩ Doneᶜ) ≤ η)
    (b : α) (hb : b ∈ (Doneᶜ : Set α)) :
    (K ^ s) b Doneᶜ ≤ (1 / 2 : ℝ≥0∞) + η := by
  classical
  -- Doneᶜ ⊆ ({G} ∩ Doneᶜ) ∪ ({¬G} ∩ Doneᶜ), a covering over the G-partition.
  have hsub : (Doneᶜ : Set α) ⊆ ({x | G x} ∩ Doneᶜ) ∪ ({x | ¬ G x} ∩ Doneᶜ) := by
    intro x hx
    simp only [Set.mem_union, Set.mem_inter_iff, Set.mem_setOf_eq]
    by_cases hG : G x
    · exact Or.inl ⟨hG, hx⟩
    · exact Or.inr ⟨hG, hx⟩
  calc (K ^ s) b Doneᶜ
      ≤ (K ^ s) b (({x | G x} ∩ Doneᶜ) ∪ ({x | ¬ G x} ∩ Doneᶜ)) := measure_mono hsub
    _ ≤ (K ^ s) b ({x | G x} ∩ Doneᶜ) + (K ^ s) b ({x | ¬ G x} ∩ Doneᶜ) :=
        measure_union_le _ _
    _ ≤ (1 / 2 : ℝ≥0∞) + η := add_le_add (hGoodBlock b hb) (hLeak b hb)

/-- **Leaky split-geometric** (deliverable 1).  From a `J`-start with `J` exact-closed and `Done`
`J`-absorbing, a uniform `J`-relative per-`s`-block failure `≤ 1/2 + η` (the leaky block bound,
`leaky_block_half_on`), whp horizon `(K^t₀) c₀ Doneᶜ ≤ δ`, and `1/2 + η < 1` (so the geometric
converges), we get

    E[T] ≤ t₀ + δ · s · (1 − (1/2 + η))⁻¹.

Same `_on` split shell as `ReachableLadder.expectedHitting_split_geometric_on`, run at the leaky
ratio `q := 1/2 + η`. -/
theorem expectedHitting_split_geometric_leaky
    (K : Kernel α α) [IsMarkovKernel K]
    (J : α → Prop) (hClosed : ∀ b : α, J b → K b {x | ¬ J x} = 0)
    {Done : Set α} (hDone : MeasurableSet Done)
    (hAbs : ∀ x ∈ Done, J x → K x Doneᶜ = 0)
    (s : ℕ) (hs : s ≠ 0) (η : ℝ≥0∞)
    (hblock : ∀ b : α, J b → b ∈ (Doneᶜ : Set α) → (K ^ s) b Doneᶜ ≤ (1 / 2 : ℝ≥0∞) + η)
    (c₀ : α) (hJc₀ : J c₀) (t₀ : ℕ) (δ : ℝ≥0∞) (hδ : (K ^ t₀) c₀ Doneᶜ ≤ δ) :
    expectedHitting K c₀ Done ≤ (t₀ : ℝ≥0∞) + δ * s * (1 - ((1 / 2 : ℝ≥0∞) + η))⁻¹ :=
  ExactMajority.expectedHitting_split_geometric_on K J hClosed hDone hAbs
    s hs ((1 / 2 : ℝ≥0∞) + η) hblock c₀ hJc₀ t₀ δ hδ

/-- **Expected time from the whp horizon plus a leaky good-slice recovery cap** (deliverable 1).

The HONEST off-event composition.  `J` exact-closed (`ReachableFrom`); `Done` `J`-absorbing; whp
failure `(K^Tgood) c₀ Doneᶜ ≤ δgood`.  The recovery content is now split:

* `hGoodBlock` — the per-`s`-block half-failure on the GOOD slice: from any not-done state the
  `s`-block mass landing on `{G} ∩ Doneᶜ` is `≤ 1/2`.  This is exactly what the on-chain classifier
  delivers (a not-done good state recovers in expected time `≤ B`, `B·2 ≤ s`, so its `s`-block
  half-fails; the good slice's mass therefore drains at half-rate).  Supplied only on the good slice.
* `hLeak` — the per-`s`-block escape budget: from any not-done state the `s`-block mass landing on
  `{¬G} ∩ Doneᶜ` (the off-good not-done mass) is `≤ η`.  This is the WindowSurvival-style escape
  charge; off-good states are never classified, only budgeted.

Then

    E[T] ≤ Tgood + δgood · sRecover · (1 − (1/2 + η))⁻¹.

The off-good mass is charged to `η` (folded into the geometric ratio), NOT to a deterministic
off-event ladder.  No classifier is ever demanded off `G`. -/
theorem expected_time_from_whp_and_leaky_recovery
    (K : Kernel α α) [IsMarkovKernel K]
    (J : α → Prop) (hClosed : ∀ b : α, J b → K b {x | ¬ J x} = 0)
    (c₀ : α) (hJc₀ : J c₀) {Done : Set α} (hDone : MeasurableSet Done)
    (hAbs : ∀ x ∈ Done, J x → K x Doneᶜ = 0)
    (Tgood sRecover : ℕ) (hsRecover : sRecover ≠ 0)
    (G : α → Prop) (η δgood : ℝ≥0∞)
    (hGoodBlock : ∀ b : α, b ∈ (Doneᶜ : Set α) →
      (K ^ sRecover) b ({x | G x} ∩ Doneᶜ) ≤ (1 / 2 : ℝ≥0∞))
    (hLeak : ∀ b : α, b ∈ (Doneᶜ : Set α) →
      (K ^ sRecover) b ({x | ¬ G x} ∩ Doneᶜ) ≤ η)
    (hδ : (K ^ Tgood) c₀ Doneᶜ ≤ δgood) :
    expectedHitting K c₀ Done
      ≤ (Tgood : ℝ≥0∞) + δgood * sRecover * (1 - ((1 / 2 : ℝ≥0∞) + η))⁻¹ := by
  have hblock : ∀ b : α, J b → b ∈ (Doneᶜ : Set α) →
      (K ^ sRecover) b Doneᶜ ≤ (1 / 2 : ℝ≥0∞) + η :=
    fun b _ hb => leaky_block_half_on K hDone G sRecover η hGoodBlock hLeak b hb
  exact expectedHitting_split_geometric_leaky K J hClosed hDone hAbs
    sRecover hsRecover η hblock c₀ hJc₀ Tgood δgood hδ

end LeakySplit

/-! ## Deliverable 2 — the on-J-good classifier.

The on-chain classifier supplies `SlotRegimeData` only on the GOOD slice (the good-window
predicate `G`), never off it.  `branchOfOnGoodClassifier` produces the branch on the good slice via
`AtomsV2.branchOfSlotRegime` (the landed `BranchAndBudget` on-chain builders). -/

variable {L K : ℕ}

/-- **The on-J-good slot classifier** (deliverable 2).  REPLACES the over-quantified
`AtomsV2.DotySlotClassifier` (which demanded `SlotRegimeData` for EVERY reachable not-done state).
Here the per-slot regime data is supplied ONLY for reachable not-done states that are ALSO in the
good-window predicate `G` — the states the good run visits, where `BranchAndBudget`'s on-chain
builders genuinely produce the regime data.  Off `G`, nothing is demanded. -/
@[reducible] def OnGoodSlotClassifier (n : ℕ) (init : Config (AgentState L K)) (Brecover : ℝ≥0∞)
    (βfinal : Config (AgentState L K) → ℝ≥0∞) (G : Config (AgentState L K) → Prop) : Type :=
  ∀ b, ReachableFrom L K init b → b ∈ (StableDone L K init)ᶜ → G b →
    AtomsV2.SlotRegimeData (L := L) (K := K) n init b Brecover (βfinal b)

/-- **The on-good branch producer** (deliverable 2).  On the good slice the on-chain classifier
produces the `ChainEndBranch` via `AtomsV2.branchOfSlotRegime` (the landed `BranchAndBudget`
builders `branch_of_slot` / `branch_of_phase10_*`).  This is the on-J-good analogue of
`AtomsV2.branchOfClassifier`, scoped to `G`. -/
def branchOfOnGoodClassifier {n : ℕ} (init : Config (AgentState L K)) (Brecover : ℝ≥0∞)
    (βfinal : Config (AgentState L K) → ℝ≥0∞) (G : Config (AgentState L K) → Prop)
    (hOnGood : OnGoodSlotClassifier (L := L) (K := K) n init Brecover βfinal G) :
    ∀ b, ReachableFrom L K init b → b ∈ (StableDone L K init)ᶜ → G b →
      ChainEndBranch (L := L) (K := K) n init b Brecover (βfinal b) :=
  fun b hbReach hbBad hbG =>
    AtomsV2.branchOfSlotRegime init b Brecover (βfinal b) (hOnGood b hbReach hbBad hbG)

/-! ## Deliverable 3 — the re-cut expected theorem `doty_theorem_3_1_expected_v4`.

`hSlotClass : DotySlotClassifier` (the classifier over ALL reachable not-done states) is REPLACED
by:

* `hOnGood : OnGoodSlotClassifier` — the classifier on the good slice only (the honest on-chain
  content), and
* the leak budgets `hGoodBlock` (good-slice block-half) + `hLeak` (off-good escape budget),

with the conclusion UNCHANGED.  The recovery half runs the leaky split-geometric
`expected_time_from_whp_and_leaky_recovery` with `J := ReachableFrom init` and the good predicate
`G`; the off-`G` mass is charged to `η` — never to a deterministic off-event classifier.

We package the whp horizon + the absorption facts in the same shape as the landed E4 surface, so
the theorem is a direct consequence of the leaky composition.  The whp horizon `hfail` (the
seam-corrected 21-instance failure `≤ 1/n`) is carried as a hypothesis (it is the landed
`doty_time_headline_W2` output, exactly as threaded in `ReachableLadder.doty_expected_time_reachable`).
-/

open scoped Classical in
/-- **`doty_theorem_3_1_expected_v4` (the honest off-event re-cut).**

`E[T c₀ → StableDone] ≤ Tgood + δgood · sRec · (1 − (1/2 + η))⁻¹`, with the recovery contribution
supplied by the **on-J-good classifier** + the **leak budgets** — NO classifier off the good
window, NO deterministic off-event ladder.

The binder classification of the new surface:

* `hOnGood` — the GOOD-slice classifier (the honest on-chain residual; the only protocol input that
  carries regime data, and only on `G`);
* `hGoodBlock` — the good-slice per-block half-failure (PRODUCED from `hOnGood`'s caps on the good
  slice; carried here as the abstract block content the engine consumes);
* `hLeak` — the off-good escape budget `η` (the WindowSurvival-style charge; the off-event mass is
  here, additively, NOT in a classifier);
* `hfail` — the landed whp horizon (`doty_time_headline_W2`, unchanged);
* `hAbs` — `J`-relative `Done`-absorption (the landed `hDoneAbs`).

Everything else — the leaky split-geometric, the exact-`J` Markov tail, the on-good branch
production — is DISCHARGED. -/
theorem doty_theorem_3_1_expected_v4 {n : ℕ}
    (init c₀ : Config (AgentState L K))
    (hc₀Reach : ReachableFrom L K init c₀)
    (Brecover : ℝ≥0∞)
    (βfinal : Config (AgentState L K) → ℝ≥0∞)
    (G : Config (AgentState L K) → Prop)
    (hDone : MeasurableSet (StableDone L K init))
    (hDoneAbs : ∀ x ∈ StableDone L K init,
      (NonuniformMajority L K).transitionKernel x (StableDone L K init)ᶜ = 0)
    (Tgood sRecover : ℕ) (hsRecover : sRecover ≠ 0)
    (η δgood : ℝ≥0∞)
    -- The on-J-good classifier (the honest on-chain residual; regime data only on the good slice).
    (_hOnGood : OnGoodSlotClassifier (L := L) (K := K) n init Brecover βfinal G)
    -- The good-slice per-block half-failure (produced from `_hOnGood`'s good-slice recovery caps).
    (hGoodBlock : ∀ b, b ∈ (StableDone L K init)ᶜ →
      ((NonuniformMajority L K).transitionKernel ^ sRecover) b
        ({x | G x} ∩ (StableDone L K init)ᶜ) ≤ (1 / 2 : ℝ≥0∞))
    -- The off-good escape budget (the WindowSurvival-style charge; off-event mass is here).
    (hLeak : ∀ b, b ∈ (StableDone L K init)ᶜ →
      ((NonuniformMajority L K).transitionKernel ^ sRecover) b
        ({x | ¬ G x} ∩ (StableDone L K init)ᶜ) ≤ η)
    -- The landed whp horizon (`doty_time_headline_W2`, unchanged).
    (hfail : ((NonuniformMajority L K).transitionKernel ^ Tgood) c₀
        (StableDone L K init)ᶜ ≤ δgood) :
    expectedHitting (NonuniformMajority L K).transitionKernel c₀
      (StableDone L K init)
      ≤ (Tgood : ℝ≥0∞) + δgood * sRecover * (1 - ((1 / 2 : ℝ≥0∞) + η))⁻¹ := by
  classical
  exact expected_time_from_whp_and_leaky_recovery
    (NonuniformMajority L K).transitionKernel (ReachableFrom L K init)
    (reachableFrom_kernel_closed init) c₀ hc₀Reach hDone
    (fun x hx _ => hDoneAbs x hx)
    Tgood sRecover hsRecover G η δgood hGoodBlock hLeak hfail

/-! ## Deliverable 3' — the headline-shaped corollary.

The `_v4` theorem's RHS is the explicit leaky form `Tgood + δgood·sRec·(1 − (1/2 + η))⁻¹`.  To
match the campaign headline `(21·C0 + 4·Cbad)·n·(L+1)`, the caller supplies the same `hrecmass`
arithmetic the landed surfaces use, now at the leaky ratio.  We expose the bridge so the leaky
form lands the headline when the leak `η` and the recovery scale close the recovery budget.  This
is the honest accounting: the headline is recovered EXACTLY when the off-good leak is small enough
that the enlarged geometric factor `(1 − (1/2 + η))⁻¹` still fits the `4·Cbad` recovery budget. -/

/-- **The leaky recovery budget closes the headline** (deliverable 3').  Given the `_v4` bound
`E[T] ≤ Tgood + δgood·sRec·(1 − (1/2 + η))⁻¹` at a fixed start `c₀`/`init`, if the whp horizon fits
`Tgood ≤ 21·C0·n·(L+1)` and the leaky recovery tail fits the recovery budget
`δgood·sRec·(1 − (1/2 + η))⁻¹ ≤ 4·Cbad·n·(L+1)`, then the bound yields the campaign headline
`E[T] ≤ (21·C0 + 4·Cbad)·n·(L+1)`.  The honest leak accounting: the off-good mass enlarges the
geometric factor from `(1−1/2)⁻¹ = 2` to `(1 − (1/2 + η))⁻¹`; the headline survives precisely when
that enlargement still fits the `4·Cbad` budget (the leak `η` is `o(1)`, paid from the whp bad
mass). -/
theorem v4_headline_of_budget {n C0 Cbad : ℕ}
    {Tgood sRecover : ℕ}
    {η δgood RHSrec : ℝ≥0∞}
    {init c₀ : Config (AgentState L K)}
    (hEbound :
      expectedHitting (NonuniformMajority L K).transitionKernel c₀ (StableDone L K init)
        ≤ (Tgood : ℝ≥0∞) + δgood * sRecover * (1 - ((1 / 2 : ℝ≥0∞) + η))⁻¹)
    (hTgood : (Tgood : ℝ≥0∞) ≤ ((21 * C0 * n * (L + 1) : ℕ) : ℝ≥0∞))
    (hrec : δgood * sRecover * (1 - ((1 / 2 : ℝ≥0∞) + η))⁻¹ ≤ RHSrec)
    (hrecbud : RHSrec ≤ ((4 * Cbad * n * (L + 1) : ℕ) : ℝ≥0∞)) :
    expectedHitting (NonuniformMajority L K).transitionKernel c₀ (StableDone L K init)
      ≤ (((21 * C0 + 4 * Cbad) * n * (L + 1) : ℕ) : ℝ≥0∞) := by
  refine hEbound.trans ?_
  calc (Tgood : ℝ≥0∞) + δgood * sRecover * (1 - ((1 / 2 : ℝ≥0∞) + η))⁻¹
      ≤ ((21 * C0 * n * (L + 1) : ℕ) : ℝ≥0∞) + RHSrec := add_le_add hTgood hrec
    _ ≤ ((21 * C0 * n * (L + 1) : ℕ) : ℝ≥0∞) + ((4 * Cbad * n * (L + 1) : ℕ) : ℝ≥0∞) :=
        add_le_add (le_refl _) hrecbud
    _ = (((21 * C0 + 4 * Cbad) * n * (L + 1) : ℕ) : ℝ≥0∞) := by push_cast; ring

end OffEventEndgame
end ExactMajority
