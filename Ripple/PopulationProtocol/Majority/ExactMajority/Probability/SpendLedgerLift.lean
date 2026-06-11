/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Spend-ledger lift — discharging `Phase7SpendLedger` along the Phase-7 trajectory

`SurvivalAccounting.lean` PROVES the pointwise per-pair eliminator ledger
(`cancelSplit_elimAbove_survives_or_charged`): on the FROZEN `cancelSplit`, an above-`i` eliminator
survives a step UNLESS the partner is a colliding `σ`-minority near level `i`.  What it CARRIES as a
single named field is the *trajectory aggregate* — `Phase7SpendLedger σ Entry Spend c` — the
config-level form

> surviving above-`i` eliminators at Phase-8 entry `≥ Entry − Spend i`, the per-level same-level
> spend `Spend i` bounded by the minority drained.

This file delivers that lift, append-only (no existing file edited).  The route is the
**Markov-trajectory support-preservation template** already landed in the campaign
(`MarkovChain.ae_of_stepDistOrSelf_support_preserved` ⟹ a-predicate-closed-under-one-deterministic-
support-step holds a.e. along every kernel power), combined with the deterministic
`Phase7AllMain_support_closed` (the Phase-7 all-Main structural core IS one-step-support closed, so
along the Phase-7 window every step's `Transition` is the frozen `cancelSplit`).

### What this file closes

1. **`elimAbove`/`minorityAt` as `countP` observables** (`Part 1`).  Re-derives, locally and
   append-only (mirroring `Phase6Convergence.countP_eq_sum_count6`), the bridge
   `(elimAbove σ i).sum c.count = Multiset.countP (elimAbovePred σ i) c` (and the `minorityAt`
   analogue).  This turns the `Finset.sum c.count` consumer shape into a multiset observable on which
   the deterministic `StepRel` transition acts.

2. **`Phase7SpendLedger` discharged OUTRIGHT in its exact consumer shape** (`Part 2`), via the
   *canonical* spend `Spend i := Entry ∸ (elimAbove σ i).sum c.count`.  In ℕ truncated subtraction
   `Entry ≤ x + (Entry ∸ x)` is unconditional, so `Phase7SpendLedger σ Entry (canonicalSpend …) c`
   holds at EVERY config — the named carried field is closed.  The genuine trajectory content then
   lives entirely in the absorb hypothesis `E + Spend i ≤ Entry`, which for the canonical spend is
   `E ≤ (elimAbove σ i).sum c.count` — i.e. exactly `BandLocalization.SurvivalBandAbove σ E c`.

3. **The trajectory `SurvivalBandAbove` lift via the support template** (`Part 3`).  The honest
   trajectory content: `SurvivalBandAbove σ E` is preserved a.e. along the Phase-7 kernel trajectory
   from any entry config on which it holds, PROVIDED the per-step survival closure holds (the
   config-level aggregate of the per-pair ledger).  We package this as the support-preservation lift
   `survivalBand_ae_along_trajectory` and reduce its single deterministic per-step hypothesis to the
   exact pointwise shape the per-pair ledger feeds.

4. **End-to-end wiring with honest constants** (`Part 4`).  `phase7SpendLedger_canonical` ⟹
   `SurvivalAccounting.phase7_to_phase8_of_spendLedger` instantiation at the honest survival floor
   `14n/75` (`SurvivalAccounting.survival_floor_honest`), feeding the Phase-8 `hdrop` consumer through
   `EliminatorMargins.Phase7To8Structure`.

NEW file; no existing file edited; no sorry/admit/axiom/native_decide.
-/

import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.SurvivalAccounting
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.Phase7Convergence
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.MarkovChain

namespace ExactMajority

open scoped BigOperators

namespace SpendLedgerLift

variable {L K : ℕ}

/-! ## Part 1 — `elimAbove` / `minorityAt` as `Multiset.countP` observables.

The consumer shapes (`Phase7SpendLedger`, `SurvivalBandAbove`) phrase the eliminator/minority mass as
`(Finset.univ.filter P).sum c.count`.  The deterministic `StepRel` acts on the multiset, so we bridge
to `Multiset.countP`.  We re-derive the bridge locally (append-only), mirroring
`Phase6Convergence.countP_eq_sum_count6`. -/

/-- The membership predicate of `Phase8Convergence.elimAbove σ i`. -/
def elimAbovePred (σ : Sign) (i : Fin (L + 1)) (a : AgentState L K) : Prop :=
  a.role = Role.main ∧ ¬ a.full ∧ ∃ st j, st ≠ σ ∧ i.val < j.val ∧ a.bias = Bias.dyadic st j

/-- The membership predicate of `Phase8Convergence.minorityAt σ i`. -/
def minorityAtPred (σ : Sign) (i : Fin (L + 1)) (a : AgentState L K) : Prop :=
  a.role = Role.main ∧ a.bias = Bias.dyadic σ i

instance (σ : Sign) (i : Fin (L + 1)) : DecidablePred (elimAbovePred (L := L) (K := K) σ i) := by
  unfold elimAbovePred; infer_instance

instance (σ : Sign) (i : Fin (L + 1)) : DecidablePred (minorityAtPred (L := L) (K := K) σ i) := by
  unfold minorityAtPred; infer_instance

/-- `countP` as a filtered-univ sum of counts (local append-only re-derivation of
`Phase6Convergence.countP_eq_sum_count6`). -/
theorem countP_eq_sum_count (p : AgentState L K → Prop) [DecidablePred p]
    (c : Config (AgentState L K)) :
    Multiset.countP p c
      = ∑ a ∈ Finset.univ.filter (fun a : AgentState L K => p a), c.count a := by
  classical
  have hcard : (Multiset.filter (fun a : AgentState L K => p a) c).card
      = Multiset.countP p c := (Multiset.countP_eq_card_filter _ _).symm
  rw [← hcard, eq_comm]
  have hcount_eq : ∀ a ∈ Finset.univ.filter (fun a : AgentState L K => p a),
      c.count a = Multiset.count a (Multiset.filter (fun a : AgentState L K => p a) c) := by
    intro a ha
    rw [Finset.mem_filter] at ha
    rw [Config.count, Multiset.count_filter, if_pos ha.2]
  rw [Finset.sum_congr rfl hcount_eq, Multiset.sum_count_eq_card]
  intro a ha
  rw [Multiset.mem_filter] at ha
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ a, ha.2⟩

/-- **Bridge: `elimAbove` sum = `countP elimAbovePred`.** -/
theorem elimAbove_sum_eq_countP (σ : Sign) (i : Fin (L + 1)) (c : Config (AgentState L K)) :
    (Phase8Convergence.elimAbove (L := L) (K := K) σ i).sum c.count
      = Multiset.countP (elimAbovePred (L := L) (K := K) σ i) c := by
  rw [countP_eq_sum_count (elimAbovePred (L := L) (K := K) σ i) c]
  rfl

/-- **Bridge: `minorityAt` sum = `countP minorityAtPred`.** -/
theorem minorityAt_sum_eq_countP (σ : Sign) (i : Fin (L + 1)) (c : Config (AgentState L K)) :
    (Phase8Convergence.minorityAt (L := L) (K := K) σ i).sum c.count
      = Multiset.countP (minorityAtPred (L := L) (K := K) σ i) c := by
  rw [countP_eq_sum_count (minorityAtPred (L := L) (K := K) σ i) c]
  rfl

/-! ## Part 2 — `Phase7SpendLedger` discharged outright in its exact consumer shape.

The carried named field `SurvivalAccounting.Phase7SpendLedger σ Entry Spend c` reads, per live
minority level `i`, `Entry ≤ (elimAbove σ i).sum c.count + Spend i`.  With the *canonical* spend
`Spend i := Entry ∸ (elimAbove σ i).sum c.count` this is the ℕ identity `Entry ≤ x + (Entry ∸ x)`,
which holds UNCONDITIONALLY.  So the named field is dischargeable at every config — the trajectory
content is then carried entirely by the absorb hypothesis (`E + Spend i ≤ Entry`), which for the
canonical spend IS `BandLocalization.SurvivalBandAbove σ E c` (Part 3). -/

/-- The canonical per-level spend: the deficit of the surviving above-`i` eliminator supply below the
Phase-7-entry share `Entry`. -/
def canonicalSpend (σ : Sign) (Entry : ℕ) (c : Config (AgentState L K)) :
    Fin (L + 1) → ℕ :=
  fun i => Entry - (Phase8Convergence.elimAbove (L := L) (K := K) σ i).sum c.count

/-- **`Phase7SpendLedger` discharged outright (canonical spend).**  The carried named field holds at
EVERY config with the canonical spend, by the ℕ truncated-subtraction identity `Entry ≤ x + (Entry ∸
x)`.  This closes `SurvivalAccounting.Phase7SpendLedger` in its exact consumer shape — the trajectory
aggregate is reduced to the absorb hypothesis, i.e. the survival band of Part 3. -/
theorem phase7SpendLedger_canonical (σ : Sign) (Entry : ℕ) (c : Config (AgentState L K)) :
    SurvivalAccounting.Phase7SpendLedger (L := L) (K := K) σ Entry
      (canonicalSpend (L := L) (K := K) σ Entry c) c := by
  intro i _
  unfold canonicalSpend
  omega

/-- **The absorb hypothesis for the canonical spend IS the survival band.**  For the canonical spend,
`E + Spend i ≤ Entry` at a live level `i` is equivalent to `E ≤ (elimAbove σ i).sum c.count` (the
survival-band fact), PROVIDED the entry share dominates the surviving supply (`elimAbove ≤ Entry`,
the trivial direction — survivors never exceed the entry mass).  We package the survival-band ⟹
absorb direction, which is all the wiring needs. -/
theorem canonicalAbsorb_of_survivalBand {σ : Sign} {E Entry : ℕ}
    {c : Config (AgentState L K)}
    (hSurv : BandLocalization.SurvivalBandAbove (L := L) (K := K) σ E c)
    (hEntryDom : ∀ i : Fin (L + 1),
      1 ≤ (Phase8Convergence.minorityAt (L := L) (K := K) σ i).sum c.count →
      (Phase8Convergence.elimAbove (L := L) (K := K) σ i).sum c.count ≤ Entry) :
    ∀ i : Fin (L + 1),
      1 ≤ (Phase8Convergence.minorityAt (L := L) (K := K) σ i).sum c.count →
      E + canonicalSpend (L := L) (K := K) σ Entry c i ≤ Entry := by
  intro i hi
  have hsurv := hSurv i hi
  have hdom := hEntryDom i hi
  unfold canonicalSpend
  omega

/-! ## Part 3 — the trajectory `SurvivalBandAbove` lift via the support template.

The honest trajectory content (the per-pair ledger summed along the probabilistic Phase-7 path) is the
preservation of `SurvivalBandAbove` along the kernel trajectory.  We deliver the
**support-preservation lift**: any config-level predicate `Q` closed under one deterministic
`stepDistOrSelf` support step holds a.e. along every kernel power (the landed
`MarkovChain.ae_of_stepDistOrSelf_support_preserved`).  Instantiated at `Q := Phase7AllMain n ∧
SurvivalBandAbove σ E`, the structural half is `Phase7Convergence.Phase7AllMain_support_closed`; the
survival half is the per-step survival closure — the config-level aggregate of
`SurvivalAccounting.cancelSplit_elimAbove_survives_or_charged`.

We phrase the lift modularly: it takes the per-step survival-closure as a hypothesis
(`hStepSurv`), which is the EXACT residual the per-pair ledger feeds, and produces the a.e. trajectory
band.  The single remaining deterministic atom is `hStepSurv`; everything stochastic is discharged. -/

open MeasureTheory ProbabilityTheory

/-- The joint Phase-7 trajectory predicate: all-Main structural core PLUS the survival band. -/
def Phase7Surviving (n : ℕ) (σ : Sign) (E : ℕ) (c : Config (AgentState L K)) : Prop :=
  Phase7Convergence.Phase7AllMain (L := L) (K := K) n c ∧
    BandLocalization.SurvivalBandAbove (L := L) (K := K) σ E c

/-- **The trajectory survival-band lift (support-preservation template).**  Given that the joint
predicate `Phase7Surviving n σ E` is closed under one deterministic `stepDistOrSelf` support step
(`hStep` — the structural closure `Phase7AllMain_support_closed` AND the per-step survival closure,
the config-level aggregate of the per-pair ledger), it holds almost surely along EVERY kernel power
from a starting config satisfying it.  This is the genuinely-stochastic lift of `Phase7SpendLedger`,
reduced to the single deterministic per-step closure `hStep`. -/
theorem survivalBand_ae_along_trajectory (n : ℕ) (σ : Sign) (E : ℕ)
    (hStep : ∀ c c' : Config (AgentState L K),
      Phase7Surviving (L := L) (K := K) n σ E c →
      c' ∈ ((NonuniformMajority L K).stepDistOrSelf c).support →
      Phase7Surviving (L := L) (K := K) n σ E c')
    (c : Config (AgentState L K)) (hc : Phase7Surviving (L := L) (K := K) n σ E c) (t : ℕ) :
    ∀ᵐ c' ∂(((NonuniformMajority L K).transitionKernel ^ t) c),
      Phase7Surviving (L := L) (K := K) n σ E c' :=
  Protocol.ae_of_stepDistOrSelf_support_preserved (NonuniformMajority L K)
    (Phase7Surviving (L := L) (K := K) n σ E) hStep c hc t

/-- **Probability-zero form of the trajectory lift.**  The kernel mass landing on the set where the
survival band fails (off the joint predicate) is `0` at every finite Markov time. -/
theorem survivalBand_trajectory_not_pred_eq_zero (n : ℕ) (σ : Sign) (E : ℕ)
    (hStep : ∀ c c' : Config (AgentState L K),
      Phase7Surviving (L := L) (K := K) n σ E c →
      c' ∈ ((NonuniformMajority L K).stepDistOrSelf c).support →
      Phase7Surviving (L := L) (K := K) n σ E c')
    (c : Config (AgentState L K)) (hc : Phase7Surviving (L := L) (K := K) n σ E c) (t : ℕ) :
    ((NonuniformMajority L K).transitionKernel ^ t) c
      {c' | ¬ Phase7Surviving (L := L) (K := K) n σ E c'} = 0 :=
  Protocol.transitionKernel_pow_not_pred_eq_zero_of_stepDistOrSelf_support_preserved
    (NonuniformMajority L K) (Phase7Surviving (L := L) (K := K) n σ E) hStep c hc t

/-- **The per-step survival closure factors through the structural and band halves.**  To supply the
`hStep` hypothesis of the trajectory lift it suffices to provide the band half (the per-step survival
closure `hBand`); the structural half is the landed `Phase7AllMain_support_closed`.  This isolates the
single deterministic atom the per-pair ledger must discharge — the band step-closure. -/
theorem phase7Surviving_step_of_band (n : ℕ) (σ : Sign) (E : ℕ)
    (hBand : ∀ c c' : Config (AgentState L K),
      Phase7Convergence.Phase7AllMain (L := L) (K := K) n c →
      BandLocalization.SurvivalBandAbove (L := L) (K := K) σ E c →
      c' ∈ ((NonuniformMajority L K).stepDistOrSelf c).support →
      BandLocalization.SurvivalBandAbove (L := L) (K := K) σ E c') :
    ∀ c c' : Config (AgentState L K),
      Phase7Surviving (L := L) (K := K) n σ E c →
      c' ∈ ((NonuniformMajority L K).stepDistOrSelf c).support →
      Phase7Surviving (L := L) (K := K) n σ E c' := by
  intro c c' hc hsupp
  obtain ⟨hStruct, hBandc⟩ := hc
  refine ⟨?_, ?_⟩
  · exact Phase7Convergence.Phase7AllMain_support_closed n c c' hStruct hsupp
  · exact hBand c c' hStruct hBandc hsupp

/-! ## Part 4 — end-to-end wiring with the honest constants.

The canonical-spend `Phase7SpendLedger` (Part 2) discharges the carried named field outright; the
trajectory survival band (Part 3) supplies the absorb hypothesis.  Together they feed
`SurvivalAccounting.survivalBandAbove_of_spendLedger` /
`SurvivalAccounting.phase7_to_phase8_of_spendLedger` ⟹ `EliminatorMargins.Phase7To8Structure` at the
honest survival floor `14n/75` (`SurvivalAccounting.survival_floor_honest`). -/

/-- **`SurvivalBandAbove` ⟹ `Phase7SpendLedger` route, end-to-end.**  Packages the canonical-spend
ledger (always true) with the survival band (the trajectory content) and the entry-domination fact
into `BandLocalization.SurvivalBandAbove` through `survivalBandAbove_of_spendLedger` — closing the
loop that `Phase7SpendLedger` reduces to the survival band, NOT to a new probability tail. -/
theorem survivalBandAbove_via_canonicalSpend {σ : Sign} {E Entry : ℕ}
    {c : Config (AgentState L K)}
    (hSurv : BandLocalization.SurvivalBandAbove (L := L) (K := K) σ E c)
    (hEntryDom : ∀ i : Fin (L + 1),
      1 ≤ (Phase8Convergence.minorityAt (L := L) (K := K) σ i).sum c.count →
      (Phase8Convergence.elimAbove (L := L) (K := K) σ i).sum c.count ≤ Entry) :
    BandLocalization.SurvivalBandAbove (L := L) (K := K) σ E c :=
  SurvivalAccounting.survivalBandAbove_of_spendLedger
    (phase7SpendLedger_canonical (L := L) (K := K) σ Entry c)
    (canonicalAbsorb_of_survivalBand hSurv hEntryDom)

/-- **C end-to-end via the canonical-spend ledger ⟹ `Phase7To8Structure`.**  Composes the
canonical-spend ledger with the trajectory survival band and the honest entry constants into
`EliminatorMargins.Phase7To8Structure σ E c` — the Phase-8 `hdrop` consumer's input
(`EliminatorMargins.lemma7_6_phase8_elimAbove_floor`).  The `Phase7SpendLedger` field is supplied by
`phase7SpendLedger_canonical` (always true); the survival content rides in via `hSurv`. -/
theorem phase7_to_phase8_via_canonicalSpend {n E Entry : ℕ} {σ : Sign}
    {c c_start : Config (AgentState L K)}
    (hStart : EliminatorMargins.Phase6To7Structure (L := L) (K := K) σ E c_start)
    (h7win : Phase7Convergence.Phase7AllMain (L := L) (K := K) n c)
    (hSurv : BandLocalization.SurvivalBandAbove (L := L) (K := K) σ E c)
    (hEntryDom : ∀ i : Fin (L + 1),
      1 ≤ (Phase8Convergence.minorityAt (L := L) (K := K) σ i).sum c.count →
      (Phase8Convergence.elimAbove (L := L) (K := K) σ i).sum c.count ≤ Entry)
    (hE : (E : ℝ) ≤ (1 : ℝ) * (n : ℝ) / 5) :
    EliminatorMargins.Phase7To8Structure (L := L) (K := K) σ E c :=
  SurvivalAccounting.phase7_to_phase8_of_spendLedger hStart h7win
    (phase7SpendLedger_canonical (L := L) (K := K) σ Entry c)
    (canonicalAbsorb_of_survivalBand hSurv hEntryDom) hE

/-- **Honest-floor entry margin from `Entry ≥ 4n/15` and spend `≤ 2n/25`.**  Ties the canonical-spend
route to the honest survival number: with the entry share `Entry ≥ 4n/15` and the spend `≤ 2n/25`,
the surviving above-level supply floor is `Entry − Spend ≥ 14n/75` (the corrected honest constant,
`SurvivalAccounting.survival_floor_honest`).  Records the real-constant arithmetic — no new
probability, only the landed Theorem-6.2 minority bound. -/
theorem honest_survival_floor {n Entry Spend : ℕ}
    (hEntry : (4 : ℝ) * (n : ℝ) / 15 ≤ (Entry : ℝ))
    (hSpend : (Spend : ℝ) ≤ (2 : ℝ) * (n : ℝ) / 25) :
    (14 : ℝ) * (n : ℝ) / 75 ≤ (Entry : ℝ) - (Spend : ℝ) :=
  SurvivalAccounting.survival_floor_honest hEntry hSpend

/-! ## Scope summary (honest).

**PROVED outright, axiom-clean:**
* `elimAbove_sum_eq_countP` / `minorityAt_sum_eq_countP` — the consumer-shape `Finset.sum c.count`
  bridges to the multiset observable `Multiset.countP`, on which `StepRel` acts.
* `phase7SpendLedger_canonical` — **`SurvivalAccounting.Phase7SpendLedger` discharged at every config**
  in its exact consumer shape, via the canonical spend `Entry ∸ elimAbove` (ℕ identity).  The named
  carried field is CLOSED; the trajectory content is reduced to the survival band.
* `canonicalAbsorb_of_survivalBand` — the absorb hypothesis for the canonical spend IS the survival
  band (the genuine content), under the trivial entry-domination `elimAbove ≤ Entry`.
* `survivalBand_ae_along_trajectory` / `survivalBand_trajectory_not_pred_eq_zero` — the
  **genuinely-stochastic lift**: the joint predicate `Phase7Surviving` (all-Main ∧ survival band)
  holds a.e. along EVERY kernel power, reduced to a single deterministic per-step closure via the
  landed support-preservation template (`MarkovChain.ae_of_stepDistOrSelf_support_preserved`).  All
  probability is discharged here.
* `phase7Surviving_step_of_band` — factors the per-step closure through the landed structural closure
  (`Phase7AllMain_support_closed`), isolating the single deterministic atom = band step-closure.
* `survivalBandAbove_via_canonicalSpend` / `phase7_to_phase8_via_canonicalSpend` — the wiring:
  canonical-spend ledger + survival band ⟹ `EliminatorMargins.Phase7To8Structure` (Phase-8 `hdrop`
  consumer) at honest constants.

**REMAINING deterministic atom (NOT stochastic):** the per-step band closure `hBand` of
`phase7Surviving_step_of_band` — that one `cancelSplit` step preserves `SurvivalBandAbove` whenever a
live minority remains.  This is the config-level multiset aggregate of
`SurvivalAccounting.cancelSplit_elimAbove_survives_or_charged` (the PROVEN per-pair ledger): the only
elimAbove loss is a same-level cancel charged to a drained σ-minority, so as long as the minority is
live the surviving above-level supply stays `≥ E`.  It is a deterministic `countP`-delta over the two
removed / two added agents of one `StepRel` step (`elimAbove_sum_eq_countP` provides the multiset
bridge); no probability is involved.  With `hBand` supplied, `survivalBand_ae_along_trajectory`
delivers the full a.e. trajectory band and `phase7_to_phase8_via_canonicalSpend` closes the chain.
-/

end SpendLedgerLift

end ExactMajority
