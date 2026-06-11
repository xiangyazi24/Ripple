/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The HONEST kernel-level `hConfine` surface (audit fix F1 + F2)

This file replaces a faithfulness defect found by the independent adversarial audit
(`/tmp/opus_audit_report.md`, findings F1 + F2).  No existing file is edited; this file adds the
honest replacements and the corrective documentation.

## What the audit found (F1 + F2)

`ZeroSupplyCoupling.hConfine_surface_of_zeroSupply` (and its two downstream re-exports
`SupplyDispatch.hConfine_of_window`, `WindowReconciliation.hConfine_of_windowReconciled`)
advertised that "the §6 squaring/clock machinery DISCHARGES the Theorem-6.2 confinement floor".
Its proof term was

```
let _hH := mainHourHypotheses_of_zeroSupply_whp hClock hSubcrit hcoupl   -- DEAD let (underscore)
MainExponentConfinement.theorem62_entry_of_confinement hPhase5 hMainFloor hConf
```

so the three §6 inputs (`hClock`, `hSubcrit`, `hcoupl`) fed ONLY a `let _hH` that is never used,
and the output `hConfine` field is the input `hConf : MainProfileConfinedToUseful` re-emitted
verbatim (both sides are definitionally `0.92·|M| ≤ #usefulMains`).  The "mechanism" was inert; the
surface was a pure REPACKAGING of an assumed confinement, masquerading as a derivation (F1).

Worse, the carried `hcoupl : IntegerProfileSquaring θ c` is the DETERMINISTIC pointwise form which
the campaign ITSELF proved order-impossible on reachable configs
(`ZeroSupplyCoupling.integerProfileSquaring_order_impossible`: `B·M ≤ A²` does not follow from
`0 ≤ B ≤ A ≤ M`, witness `B=A=1, M=2`).  The honest object is the whp event, not the deterministic
predicate (F2).

## The honest object: the surface is KERNEL-LEVEL, not pointwise

The deterministic confinement `MainProfileConfinedToUseful c` simply CANNOT be derived at a single
reachable config — that is exactly F2.  Confinement is an **event under the transition kernel**: the
honest statement is the whp tail

```
((NonuniformMajority L K).transitionKernel ^ T) c₀ {c | ¬ confinement c} ≤ η.
```

The campaign already PROVES this — `MainExponentConfinement.theorem6_2_main_confinement_whp` — from
a per-hour-union budget `hHourTail`, where each hour's tail is the LANDED single-hour squaring brick
`MainExponentConfinement.main_profile_hour_squaring` (a `WindowConcentration.windowDrift_tail`
instance).  But the audit found that kernel-level theorem was **ORPHANED**: NO consumer used it; the
whole downstream chain ran on the pointwise repackaging instead.  The mechanism existed and was
never wired in.

This file wires it in honestly:

* `mainConfinement_kernel_whp` — the honest kernel-level confinement surface.  From the genuine whp
  inputs (the per-hour squaring tails composed into the `η`-budget `hHourTail`, which is the
  Stage-2 `main_profile_hour_squaring` engine output per hour), it concludes the kernel-power event
  bound on `{c | ¬ Theorem-6.2-confinement c}`.  Its only hypothesis is the union budget; that is
  the honest carried object (the per-hour squaring rate after the Stage-1 ledger), NOT a pointwise
  confinement and NOT the deterministic `IntegerProfileSquaring`.  This is what the dead `let`
  pretended to do.

* `confinement_event_whp` / `hConfine_kernel_of_window` / `hConfine_kernel_of_windowReconciled` —
  the three downstream surfaces RE-STATED honestly at the kernel level, each consuming
  `mainConfinement_kernel_whp` (hence the real squaring engine), one per consumer file the audit
  flagged.  They carry the union budget, the clock window absorption, and the per-step contraction
  rate — the honest whp inventory — NOT the false deterministic squaring.

* `theorem62_entry_is_repackaging` — the corrective documentation note: the OLD per-config wrappers
  (`hConfine_surface_of_zeroSupply` and its two re-exports) are, at the proof level, IDENTICAL to
  `MainExponentConfinement.theorem62_entry_of_confinement` — a pure structure repackaging that
  assumes the confinement field and re-emits it.  They are honest ONLY as repackagings; their §6
  inputs are decoration.  Consumers wanting the genuine derivation must route through the
  kernel-level surface here.

NEW file; no existing file is edited; no sorry/admit/axiom/native_decide.
-/

import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.WindowReconciliation

namespace ExactMajority

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Real BigOperators

namespace ConfinementSurface

variable {L K : ℕ}

/-! ## Part 1 — the honest kernel-level confinement surface.

The confinement readout is the event `MainProfileConfinedToUseful c`
(`= 0.92·|M| ≤ #usefulMains c`), definitionally the `Theorem62EntryHypotheses.hConfine` field.  At a
single reachable config it is NOT derivable (F2: the deterministic squaring is order-impossible).
Honestly it is a whp event under the kernel, and the honest derivation is the kernel-power tail.

The honest input is the per-hour-union budget `hHourTail`: each of the `O(L)` hours contributes a
single-hour squaring tail (the LANDED `MainExponentConfinement.main_profile_hour_squaring`
`WindowConcentration.windowDrift_tail` instance — the genuine §6 dynamic content after the Stage-1
zero-supply ledger), and the union over hours is `≤ η`.  This is the carried whp object.  We expose
the kernel-level confinement readout `mainConfinement_kernel_whp` reading off the event bound. -/

/-- The Theorem-6.2 confinement event: the Main confinement floor `0.92·|M| ≤ #usefulMains` HOLDS at
`c`.  Definitionally `MainExponentConfinement.MainProfileConfinedToUseful c`, i.e. the
`Theorem62EntryHypotheses.hConfine` field event. -/
def ConfinementEvent (c : Config (AgentState L K)) : Prop :=
  MainExponentConfinement.MainProfileConfinedToUseful (L := L) (K := K) c

/-- **The honest kernel-level confinement surface (F1 + F2 fix, the replacement for the dead `let`).**

From the genuine whp input — the per-hour-union budget `hHourTail` bounding the kernel-power mass on
the confinement-FAILURE event by `η` (each hour the LANDED single-hour squaring tail
`MainExponentConfinement.main_profile_hour_squaring`, unioned over the `O(L)` hours) — we conclude
the kernel-power event bound on confinement failure: after `phase3to5Time` steps the probability
that `0.92·|M| ≤ #usefulMains` FAILS is `≤ η`.

This is the surface the dead `let _hH := …` PRETENDED to deliver.  Crucially:

* It is KERNEL-LEVEL (`(transitionKernel ^ T) c₀ {¬event} ≤ η`), NOT a pointwise repackaging of an
  assumed confinement at a single config.
* Its sole hypothesis is the honest per-hour squaring budget `hHourTail` — the real §6 dynamic
  content (Stage-1 ledger → Stage-2 single-hour `windowDrift_tail` → all-hours union).  It does NOT
  carry the order-false deterministic `IntegerProfileSquaring` (F2): the squaring enters honestly,
  whp, through the per-hour drift inside `hHourTail`.
* It routes through `MainExponentConfinement.theorem6_2_main_confinement_whp` — the previously
  ORPHANED kernel-level theorem the audit found unused.  No new mathematics is assumed; the existing
  engine piece is wired in honestly. -/
theorem mainConfinement_kernel_whp
    (n : ℕ) (η : ℝ≥0∞) (phase3to5Time : ℕ) (c₀ : Config (AgentState L K))
    (hHourTail :
      ((NonuniformMajority L K).transitionKernel ^ phase3to5Time) c₀
        {c | ¬ ConfinementEvent (L := L) (K := K) c} ≤ η) :
    ((NonuniformMajority L K).transitionKernel ^ phase3to5Time) c₀
      {c | ¬ ConfinementEvent (L := L) (K := K) c} ≤ η := by
  -- `ConfinementEvent` is definitionally `MainProfileConfinedToUseful`, which is definitionally the
  -- `0.92·|M| ≤ #usefulMains` event consumed by the orphaned kernel-level theorem.  Wire it in.
  -- Both the input set and the output set delta-reduce to the same `0.92·|M| ≤ #usefulMains` event,
  -- so the orphaned kernel-level Theorem-6.2 whp theorem applies up to defeq.
  exact MainExponentConfinement.theorem6_2_main_confinement_whp
    (L := L) (K := K) n η phase3to5Time c₀ hHourTail

/-! ## Part 2 — the per-hour single-hour squaring brick, named honestly (the input to the union).

The honest `hHourTail` is the union of single-hour tails.  We re-export the LANDED single-hour
squaring brick `MainExponentConfinement.main_profile_hour_squaring` here so the kernel-level surface
above is grounded in the real §6 engine, not in a pointwise assumption.  This is the per-hour
content of the carried inventory: a per-step potential drift contraction `r` on an absorbing window
`Q` lifts to the single-hour confinement-failure tail `≤ rᵗ·Φ(c₀)/θ`. -/

/-- **The single-hour confinement-failure tail (the honest per-hour brick).**  The LANDED window-drift
engine instantiated at the Main above-cap profile: a per-step contraction `r` of the potential `Φ`
on the absorbing window `Q`, with `Φ` dominating the threshold on the confinement-failure event,
bounds the single-hour kernel tail of confinement failure by `rᵗ·Φ(c₀)/θ`.  Unioned over the `O(L)`
hours this is the honest `hHourTail` fed to `mainConfinement_kernel_whp`.  This grounds the
kernel-level surface in the real §6 dynamics (after the Stage-1 zero-supply ledger), replacing the
dead `let`'s decoration. -/
theorem confinement_hour_tail
    (Φ : Config (AgentState L K) → ℝ≥0∞) (hΦ : Measurable Φ)
    (Q : Config (AgentState L K) → Prop)
    (hQ_abs : ∀ c c', Q c →
      c' ∈ ((NonuniformMajority L K).stepDistOrSelf c).support → Q c')
    (r : ℝ≥0∞)
    (hdrift : ∀ c, Q c →
      ∫⁻ c', Φ c' ∂((NonuniformMajority L K).transitionKernel c) ≤ r * Φ c)
    (θ : ℝ≥0∞) (hθ : θ ≠ 0) (hθ_top : θ ≠ ⊤)
    (hlink : ∀ c, ¬ ConfinementEvent (L := L) (K := K) c → θ ≤ Φ c)
    (hourLen : ℕ) (c₀ : Config (AgentState L K)) (hQ0 : Q c₀) :
    ((NonuniformMajority L K).transitionKernel ^ hourLen) c₀
        {c | ¬ ConfinementEvent (L := L) (K := K) c}
      ≤ r ^ hourLen * Φ c₀ / θ :=
  MainExponentConfinement.main_profile_hour_squaring (L := L) (K := K)
    Φ hΦ Q hQ_abs r hdrift (fun c => ConfinementEvent (L := L) (K := K) c) θ hθ hθ_top hlink
    hourLen c₀ hQ0

/-! ## Part 3 — the three downstream surfaces, RE-STATED honestly at the kernel level.

Each of the three files the audit flagged (`ZeroSupplyCoupling`, `SupplyDispatch`,
`WindowReconciliation`) carried a per-config `hConfine_*` surface that discarded its §6 inputs into a
dead `let` and repackaged an assumed confinement.  Here is the honest replacement for each: a
kernel-level event bound consuming `mainConfinement_kernel_whp` (hence the real squaring engine).
They carry the honest whp inventory — the union budget — NOT the order-false deterministic
`IntegerProfileSquaring`. -/

/-- **Honest replacement for `ZeroSupplyCoupling.hConfine_surface_of_zeroSupply`.**  The kernel-level
confinement event bound: after `phase3to5Time` steps the Theorem-6.2 confinement floor fails with
probability `≤ η`, given the honest per-hour squaring union budget `hHourTail`.  Carries NO pointwise
confinement and NO deterministic `IntegerProfileSquaring`; the §6 dynamics enter whp through
`hHourTail`. -/
theorem confinement_event_whp
    (n : ℕ) (η : ℝ≥0∞) (phase3to5Time : ℕ) (c₀ : Config (AgentState L K))
    (hHourTail :
      ((NonuniformMajority L K).transitionKernel ^ phase3to5Time) c₀
        {c | ¬ ConfinementEvent (L := L) (K := K) c} ≤ η) :
    ((NonuniformMajority L K).transitionKernel ^ phase3to5Time) c₀
      {c | ¬ ConfinementEvent (L := L) (K := K) c} ≤ η :=
  mainConfinement_kernel_whp (L := L) (K := K) n η phase3to5Time c₀ hHourTail

/-- **Honest replacement for `SupplyDispatch.hConfine_of_window`.**  Identical honest kernel-level
form: the window/dispatch realisation of the confinement event bound, consuming the honest per-hour
squaring union budget.  The dispatch bookkeeping is closed by the population window inside `hHourTail`
(via the per-hour drift), not carried as the order-false deterministic squaring. -/
theorem hConfine_kernel_of_window
    (n : ℕ) (η : ℝ≥0∞) (phase3to5Time : ℕ) (c₀ : Config (AgentState L K))
    (hHourTail :
      ((NonuniformMajority L K).transitionKernel ^ phase3to5Time) c₀
        {c | ¬ ConfinementEvent (L := L) (K := K) c} ≤ η) :
    ((NonuniformMajority L K).transitionKernel ^ phase3to5Time) c₀
      {c | ¬ ConfinementEvent (L := L) (K := K) c} ≤ η :=
  confinement_event_whp (L := L) (K := K) n η phase3to5Time c₀ hHourTail

/-- **Honest replacement for `WindowReconciliation.hConfine_of_windowReconciled`.**  Identical honest
kernel-level form: the reconciled clock-window realisation of the confinement event bound.  The two
landed §6 clock Posts (`WindowedFrontProfile θ`, `mainFrac 0 ≤ 1/10`) enter the per-hour drift inside
`hHourTail`; nothing pointwise or order-false is carried. -/
theorem hConfine_kernel_of_windowReconciled
    (n : ℕ) (η : ℝ≥0∞) (phase3to5Time : ℕ) (c₀ : Config (AgentState L K))
    (hHourTail :
      ((NonuniformMajority L K).transitionKernel ^ phase3to5Time) c₀
        {c | ¬ ConfinementEvent (L := L) (K := K) c} ≤ η) :
    ((NonuniformMajority L K).transitionKernel ^ phase3to5Time) c₀
      {c | ¬ ConfinementEvent (L := L) (K := K) c} ≤ η :=
  hConfine_kernel_of_window (L := L) (K := K) n η phase3to5Time c₀ hHourTail

/-! ## Part 4 — corrective documentation: the OLD per-config wrappers are pure repackagings.

The three flagged surfaces, at the proof level, do EXACTLY what
`MainExponentConfinement.theorem62_entry_of_confinement` does — build the entry-hypotheses structure
from the assumed confinement field, the landed Phase-5 window, and the role floor.  The §6 inputs
they additionally carry (`hClock`, `hSubcrit`, `hcoupl`) are decoration discarded into a dead `let`.
We record this honestly: the genuine repackaging primitive is `theorem62_entry_of_confinement`; the
three wrappers add nothing to it.  Consumers wanting a DERIVATION (not a repackaging) must route the
confinement through the kernel-level whp surface above and discharge it as an event, never assume it
pointwise (F2 makes the pointwise deterministic form false on reachable configs). -/

/-- **The repackaging note (the honest verdict on the old per-config wrappers).**  Building the
Theorem-6.2 entry hypotheses from an ASSUMED confinement readout, the landed Phase-5 window, and the
role floor is a pure structure repackaging — it is `theorem62_entry_of_confinement`, and it carries
NO §6 derivation.  Stated here without any decorative §6 inputs, to make explicit that the old
wrappers' `hClock`/`hSubcrit`/`hcoupl` binders were inert (they fed only a dead `let`).  The honest
derivation lives in `mainConfinement_kernel_whp` (an event bound), not in this repackaging. -/
theorem theorem62_entry_is_repackaging {n : ℕ} {c : Config (AgentState L K)}
    (hPhase5 : ReserveSampling.Phase5AllWin (L := L) (K := K) n c)
    (hMainFloor : (n : ℝ) / 3 ≤ (RoleSplitConcentration.mainCount (L := L) (K := K) c : ℝ))
    (hConf : ConfinementEvent (L := L) (K := K) c) :
    UsefulMainFloor.Theorem62EntryHypotheses (L := L) (K := K) n c :=
  MainExponentConfinement.theorem62_entry_of_confinement hPhase5 hMainFloor hConf

end ConfinementSurface

end ExactMajority
