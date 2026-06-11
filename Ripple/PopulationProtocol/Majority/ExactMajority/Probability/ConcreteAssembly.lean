/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Concrete 21-instance assembly with the EXACT seams (`ConcreteAssembly`)

This file closes the codex-audit F5 residual: `doty_time_headline_W2_inv_sq`
(`BudgetTightening.lean:159`) is POLYMORPHIC over `phases : Fin 21 → PhaseConvergenceW`,
with `h_chain`/`hx₀`/`h_post` left as free binders.  Nothing in the campaign actually
assembled the 21 *real* instances and discharged the 20 bridges.  Worse, the headline's
doc (`DotyTimeHeadline.lean:379`) routed assemblers to
`SeamEpidemics.seamEpidemicW_calibrated`, whose `Post` is only `allPhaseGe (p+1)` and
whose `εovershoot` is added by `le_self_add` but never consumed.  The TRUE strengthened
seam is `SeamNoOvershoot.seamEpidemicExactW`, whose `Post` is
`allPhaseGe (p+1) ∧ NoOvershoot p` and whose `convergence` CONSUMES both budgets via a
union bound.  The concrete assembly below FORCES the exact seam.

## What this file delivers (the honest scope)

1. `DotyAssembly` — a record packaging the concrete inputs of the 21-instance family:
   the 11 landed WORK `PhaseConvergenceW` instances (`work`, supplied by the caller as the
   concrete `Phase{1,4,5,6,7,8,10}` / `DrainCalibration` / `Phase7HonestDrain` constructions
   together with whatever named inputs each of those still carries — those inputs live INSIDE
   `work i` exactly as the campaign built them), the 10 SEAM phase parameters / horizons /
   budgets, and the 10 pairs of seam feeders (`hDrift`, `hNoOvershoot`) that
   `seamEpidemicExactW` consumes.  For destinations `{1,6,7,8}` the `hNoOvershoot` feeder is
   the landed `SeamNoOvershoot.hNoOvershoot_one_seam_honest` /
   `SeamPairAdapter`-chain output; for `{2,3,4,5,9}` it is the named per-seam guard.

2. `dotyPhases : DotyAssembly … → Fin 21 → PhaseConvergenceW K` — the interleave
   `[work₀, seam₀, work₁, seam₁, …, seam₉, work₁₀]`, even slot `2k ↦ work k`, odd slot
   `2k+1 ↦ seamEpidemicExactW (seamP k) …` (the EXACT seam, by construction).

3. The bridge lemmas (the deepest content):
   * `dotyPhases_bridge_work_to_seam` — `work k . Post ⟹ seam k . Pre`, the work↔seam
     boundary, discharged via `SeamEpidemics.exact_work_into_seam` /
     `SeamEpidemics.ge_work_into_seam` from the structural Pre components carried per work
     phase.  Carried gap: the advance trigger `advTriggered (p+1)` and the `allPhaseEq/Ge p`
     identification of `work k . Post` (named field `hWorkPostToWindow` / `hTrig`).
   * `dotyPhases_bridge_seam_to_work` — `seam k . Post ⟹ work (k+1) . Pre`, discharged via
     `SeamNoOvershoot.seamExact_into_exact_work` (the EXACT seam's `Post`, `allPhaseGe (p+1)
     ∧ NoOvershoot p`, yields `allPhaseEq (p+1)` pointwise with NO further timing input).
     Carried gap: the `allPhaseEq (p+1) ⟹ work (k+1) . Pre` structural identification
     (named field `hWindowToWorkPre`).

4. `doty_time_headline_CONCRETE` — `BudgetTightening.doty_time_headline_W2_inv_sq` applied
   to `dotyPhases asm`, making the headline's conditionality FINITE and inspectable: the
   surviving carried set is exactly the fields of `DotyAssembly` (listed in its docstring),
   no longer a polymorphic `phases`/`h_chain`/`h_post` triple.

This file is APPEND-ONLY: it imports and re-uses the landed surfaces and edits no existing
file.  Every bridge is a genuine pointwise implication; the named carried fields are the
structural-Pre gaps that are not yet wired in the campaign tree, each pinned to its
provenance in the field docstring.
-/

import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.BudgetTightening
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.SeamNoOvershoot

namespace ExactMajority

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal

namespace ConcreteAssembly

variable {L K : ℕ}

/-! ## Part A — index arithmetic for the `[work, seam, work, …]` interleave.

Slot `i : Fin 21` is a WORK slot iff `i.val` is even, a SEAM slot iff odd.  Work index
`k = i/2 : Fin 11`, seam index `k = i/2 : Fin 10`.  The successor of an even slot `2k` is
the odd slot `2k+1` (seam `k`); the successor of an odd slot `2k+1` is the even slot `2k+2`
(work `k+1`). -/

/-- The work index `i/2 : Fin 11` of slot `i : Fin 21`. -/
def workIdx (i : Fin 21) : Fin 11 := ⟨i.val / 2, by omega⟩

/-- The seam index `i/2 : Fin 10` of an odd slot `i : Fin 21` (`i.val` odd ⟹ `i/2 < 10`). -/
def seamIdx (i : Fin 21) (hodd : i.val % 2 = 1) : Fin 10 := ⟨i.val / 2, by omega⟩

@[simp] theorem workIdx_val (i : Fin 21) : (workIdx i).val = i.val / 2 := rfl

@[simp] theorem seamIdx_val (i : Fin 21) (hodd : i.val % 2 = 1) :
    (seamIdx i hodd).val = i.val / 2 := rfl

/-! ## Part B — the assembly record.

`DotyAssembly` packages the concrete 21-instance family.  The WORK instances are supplied
directly (each `work k` is the campaign's landed `PhaseConvergenceW`, carrying its own
internal drains).  The SEAM instances are built by `dotyPhases` from `seamEpidemicExactW`
applied to the per-seam parameters and feeders here — FORCING the exact seam.

The bridge data (`hTrig`, `hWorkPostToWindow`, `hWindowToWorkPre`) are the structural-Pre
gaps the campaign tree has not yet wired:

* `hTrig k` — the advance trigger `advTriggered (seamP k + 1)` on `work k . Post` configs.
  This is the per-work-phase strengthening the campaign carries as a named input
  (`DotyTimeHeadline.lean:317`, "advance-trigger strengthening").  Provenance: NOT yet a
  landed lemma; carried.
* `hWorkPostToWindow k` — identifies `work k . Post` with the seam's source window
  `allPhaseGe (seamP k) n`.  Provenance: each work phase's `Post` is the campaign's
  `Phase{i}…` window predicate; the `= allPhaseGe (seamP k) n` identification is the
  per-phase structural reading carried at `SeamEpidemics.lean:185` ("Pre reduces to
  `allPhaseEq i n ∧ structural component`").  Carried.
* `hWindowToWorkPre k` — identifies the seam's EXACT output window
  `allPhaseEq (seamP k + 1) n` with `work (k+1) . Pre`.  Provenance: same per-phase
  structural reading; for `≥`-window destinations (Phase 4's `Q4 = allPhaseGe 4`) the
  identification drops the overshoot exactness, otherwise it is the exact pin.  Carried. -/
structure DotyAssembly (n : ℕ) where
  /-- The 11 landed WORK `PhaseConvergenceW` instances (each with its internal drains). -/
  work : Fin 11 → PhaseConvergenceW (NonuniformMajority L K).transitionKernel
  /-- The 10 seam phase parameters `pₖ` (the source window threshold of seam `k`). -/
  seamP : Fin 10 → ℕ
  /-- The 10 seam horizons `tseamₖ`. -/
  seamT : Fin 10 → ℕ
  /-- The 10 seam epidemic budgets. -/
  εepidemic : Fin 10 → ℝ≥0
  /-- The 10 seam no-overshoot budgets. -/
  εovershoot : Fin 10 → ℝ≥0
  /-- Seam feeder: the generic-`p` advance-epidemic drift (`SeamEpidemics.seam_drift`). -/
  hDrift : ∀ (k : Fin 10) (c : Config (AgentState L K)),
      (SeamEpidemics.allPhaseGe (L := L) (K := K) (seamP k) n c ∧
        SeamEpidemics.advTriggered (L := L) (K := K) (seamP k + 1) c) →
      ((NonuniformMajority L K).transitionKernel ^ (seamT k)) c
          {c' | ¬ SeamEpidemics.allPhaseGe (L := L) (K := K) (seamP k + 1) n c'}
        ≤ (εepidemic k : ℝ≥0∞)
  /-- Seam feeder: per-seam no-overshoot tail.  For destinations `{1,6,7,8}` this is the
  landed `SeamNoOvershoot.hNoOvershoot_one_seam_honest` output; for `{2,3,4,5,9}` it is the
  named per-seam guard.  Either way it is the budget shape `seamEpidemicExactW` consumes. -/
  hNoOvershoot : ∀ (k : Fin 10) (c : Config (AgentState L K)),
      (SeamEpidemics.allPhaseGe (L := L) (K := K) (seamP k) n c ∧
        SeamEpidemics.advTriggered (L := L) (K := K) (seamP k + 1) c) →
      ((NonuniformMajority L K).transitionKernel ^ (seamT k)) c
          {c' | ¬ SeamNoOvershoot.NoOvershoot (L := L) (K := K) (seamP k) c'}
        ≤ (εovershoot k : ℝ≥0∞)
  /-- Bridge gap `hTrig`: the advance trigger on each work `Post`. -/
  hTrig : ∀ (k : Fin 10) (c : Config (AgentState L K)),
      (work ⟨k.val, by omega⟩).Post c →
      SeamEpidemics.advTriggered (L := L) (K := K) (seamP k + 1) c
  /-- Bridge gap `hWorkPostToWindow`: work `Post` ⟹ seam source window `allPhaseGe pₖ n`. -/
  hWorkPostToWindow : ∀ (k : Fin 10) (c : Config (AgentState L K)),
      (work ⟨k.val, by omega⟩).Post c →
      SeamEpidemics.allPhaseGe (L := L) (K := K) (seamP k) n c
  /-- Bridge gap `hWindowToWorkPre`: seam EXACT output window
  `allPhaseEq (pₖ+1) n` ⟹ work `(k+1)` `Pre`. -/
  hWindowToWorkPre : ∀ (k : Fin 10) (c : Config (AgentState L K)),
      SeamEpidemics.allPhaseEq (L := L) (K := K) (seamP k + 1) n c →
      (work ⟨k.val + 1, by omega⟩).Pre c

/-! ## Part C — the concrete 21-instance family. -/

/-- The `k`-th seam instance — the EXACT seam `seamEpidemicExactW`, NOT the calibrated
generic seam.  Its `Post` is `allPhaseGe (pₖ+1) n ∧ NoOvershoot pₖ` and its `convergence`
consumes BOTH `εepidemic k` and `εovershoot k`. -/
noncomputable def seamInstance {n : ℕ} (asm : DotyAssembly (L := L) (K := K) n)
    (k : Fin 10) : PhaseConvergenceW (NonuniformMajority L K).transitionKernel :=
  SeamNoOvershoot.seamEpidemicExactW (asm.seamP k) n (asm.seamT k)
    (asm.εepidemic k) (asm.εovershoot k) (asm.hDrift k) (asm.hNoOvershoot k)

/-- **The concrete 21-instance family** `[work₀, seam₀, …, seam₉, work₁₀]`.
Even slot `2k ↦ work k`; odd slot `2k+1 ↦ seamInstance k` (the EXACT seam). -/
noncomputable def dotyPhases {n : ℕ} (asm : DotyAssembly (L := L) (K := K) n) :
    Fin 21 → PhaseConvergenceW (NonuniformMajority L K).transitionKernel :=
  fun i =>
    if h : i.val % 2 = 0 then asm.work (workIdx i)
    else seamInstance asm (seamIdx i (by omega))

@[simp] theorem dotyPhases_even {n : ℕ} (asm : DotyAssembly (L := L) (K := K) n)
    (i : Fin 21) (h : i.val % 2 = 0) :
    dotyPhases asm i = asm.work (workIdx i) := by
  simp only [dotyPhases, dif_pos h]

@[simp] theorem dotyPhases_odd {n : ℕ} (asm : DotyAssembly (L := L) (K := K) n)
    (i : Fin 21) (h : i.val % 2 = 1) :
    dotyPhases asm i = seamInstance asm (seamIdx i h) := by
  simp only [dotyPhases, dif_neg (by omega : ¬ i.val % 2 = 0)]

/-! ## Part D — the bridges (`h_chain`).

The chain alternates work→seam (even slot `i = 2k`, successor odd `2k+1`) and
seam→work (odd slot `i = 2k+1`, successor even `2k+2`).  We prove each direction, then
glue into the headline's `h_chain` shape. -/

/-- **Work→seam bridge.**  `work k . Post ⟹ seamInstance k . Pre`.  The seam `Pre` is
`allPhaseGe pₖ n ∧ advTriggered (pₖ+1)`, supplied from the carried structural readings
`hWorkPostToWindow` and `hTrig` via `SeamEpidemics.exact_work_into_seam`'s `≥`-form
(`ge_work_into_seam`). -/
theorem bridge_work_to_seam {n : ℕ} (asm : DotyAssembly (L := L) (K := K) n)
    (k : Fin 10) (c : Config (AgentState L K))
    (hpost : (asm.work ⟨k.val, by omega⟩).Post c) :
    (seamInstance asm k).Pre c := by
  -- `seamInstance k . Pre = allPhaseGe pₖ n ∧ advTriggered (pₖ+1)`.
  refine ⟨asm.hWorkPostToWindow k c hpost, asm.hTrig k c hpost⟩

/-- **Seam→work bridge.**  `seamInstance k . Post ⟹ work (k+1) . Pre`.  The EXACT seam's
`Post` is `allPhaseGe (pₖ+1) n ∧ NoOvershoot pₖ`; `SeamNoOvershoot.seamExact_into_exact_work`
turns it into `allPhaseEq (pₖ+1) n` POINTWISE with no further timing input (this is exactly
why the exact seam is required — the calibrated generic seam's `Post` lacks `NoOvershoot`,
so this bridge would NOT close); the carried `hWindowToWorkPre` then identifies that exact
window with `work (k+1) . Pre`. -/
theorem bridge_seam_to_work {n : ℕ} (asm : DotyAssembly (L := L) (K := K) n)
    (k : Fin 10) (c : Config (AgentState L K))
    (hpost : (seamInstance asm k).Post c) :
    (asm.work ⟨k.val + 1, by omega⟩).Pre c := by
  -- `seamInstance k . Post = allPhaseGe (pₖ+1) n ∧ NoOvershoot pₖ` (definitional).
  have hwin : SeamEpidemics.allPhaseEq (L := L) (K := K) (asm.seamP k + 1) n c :=
    SeamNoOvershoot.seamExact_into_exact_work c hpost
  exact asm.hWindowToWorkPre k c hwin

/-- **The assembled `h_chain`.**  For every slot `i : Fin 21` with `i.val + 1 < 21`, the
slot `Post` implies the successor slot `Pre`.  Splits on the parity of `i`: even slot
`2k` uses `bridge_work_to_seam`, odd slot `2k+1` uses `bridge_seam_to_work`. -/
theorem dotyPhases_h_chain {n : ℕ} (asm : DotyAssembly (L := L) (K := K) n) :
    ∀ (i : Fin 21) (hi : i.val + 1 < 21),
      ∀ x, (dotyPhases asm i).Post x → (dotyPhases asm ⟨i.val + 1, hi⟩).Pre x := by
  intro i hi x hpost
  -- the `Fin 21` successor slot, with its value reduced (`Fin.val ⟨v,_⟩ = v`).
  have hjval : (⟨i.val + 1, hi⟩ : Fin 21).val = i.val + 1 := rfl
  rcases Nat.even_or_odd i.val with hev | hod
  · -- even slot `2k`: successor is the odd seam slot `2k+1`.
    have hi0 : i.val % 2 = 0 := Nat.even_iff.mp hev
    have hsucc1 : (⟨i.val + 1, hi⟩ : Fin 21).val % 2 = 1 := by rw [hjval]; omega
    rw [dotyPhases_even asm i hi0] at hpost
    rw [dotyPhases_odd asm ⟨i.val + 1, hi⟩ hsucc1]
    set k : Fin 10 := seamIdx ⟨i.val + 1, hi⟩ hsucc1 with hkdef
    -- `k.val = (i+1)/2 = i/2 = (workIdx i).val` (i even); identify the work slots.
    have hkw : (⟨k.val, by omega⟩ : Fin 11) = workIdx i := by
      apply Fin.ext
      have hkval : k.val = i.val / 2 := by rw [hkdef, seamIdx_val, hjval]; omega
      rw [Fin.val_mk, hkval, workIdx_val]
    have hbridge := bridge_work_to_seam asm k x
    rw [hkw] at hbridge
    exact hbridge hpost
  · -- odd slot `2k+1`: successor is the even work slot `2k+2`.
    have hi1 : i.val % 2 = 1 := Nat.odd_iff.mp hod
    have hsucc0 : (⟨i.val + 1, hi⟩ : Fin 21).val % 2 = 0 := by rw [hjval]; omega
    rw [dotyPhases_odd asm i hi1] at hpost
    rw [dotyPhases_even asm ⟨i.val + 1, hi⟩ hsucc0]
    set k : Fin 10 := seamIdx i hi1 with hkdef
    -- `(workIdx (i+1)).val = (i+1)/2 = i/2 + 1 = k.val + 1` (i odd); identify the work slots.
    have hkw : (⟨k.val + 1, by omega⟩ : Fin 11) = workIdx ⟨i.val + 1, hi⟩ := by
      apply Fin.ext
      have hkval : k.val = i.val / 2 := by rw [hkdef, seamIdx_val]
      rw [Fin.val_mk, hkval, workIdx_val, hjval]
      omega
    have hbridge := bridge_seam_to_work asm k x
    rw [hkw] at hbridge
    exact hbridge hpost

/-! ## Part E — the concrete headline.

`doty_time_headline_CONCRETE` instantiates `BudgetTightening.doty_time_headline_W2_inv_sq`
at `phases := dotyPhases asm`, discharging `h_chain` by `dotyPhases_h_chain`.  The remaining
hypotheses (`ht`, `hε`, `hx₀`, `h_post`, `hC0`, `hδ`) are the FINITE carried set, no longer
hidden behind a polymorphic `phases`.  Read off the surviving conditionality from the
arguments: it is exactly the per-slot scaling/budget data plus the start/close maps, with
the chain now CLOSED.

The carried set is therefore (inspectable, finite):
  * the fields of `asm` (`DotyAssembly`): the 11 work instances (each with its internal
    drains), the 10 exact-seam feeders (`hDrift`, `hNoOvershoot`), and the three structural
    bridge gaps (`hTrig`, `hWorkPostToWindow`, `hWindowToWorkPre`);
  * `ht`/`hC0` (per-slot time scaling, `Cphase i ≤ C0`);
  * `hε`/`hδ` (per-slot `n⁻²` budget — discharged by the campaign's calibrated budgets);
  * `hx₀` (the start `work₀ . Pre c₀`);
  * `h_post` (the close `work₁₀ . Post ⟹ majorityStableEndpoint`).
The `h_chain` binder — the 20 bridges — is GONE from the surviving set (closed here).

(The elaboration unifies `dotyPhases asm` against the polymorphic `phases` slot of
`doty_time_headline_W2_inv_sq`, reducing the `dite`-interleave at the endpoints `0` / `20`;
`maxHeartbeats` is raised for this benign defeq cost — no `native_decide`, no kernel work.) -/
set_option maxHeartbeats 0 in
theorem doty_time_headline_CONCRETE
    {L K n C0 : ℕ}
    (init c₀ : Config (AgentState L K))
    (asm : DotyAssembly (L := L) (K := K) n)
    (Cphase : Fin 21 → ℕ) (δ : Fin 21 → ℝ≥0)
    (ht : ∀ i, (dotyPhases asm i).t ≤ Cphase i * n * (L + 1))
    (hε : ∀ i, ((dotyPhases asm i).ε : ℝ≥0∞) ≤ (δ i : ℝ≥0∞))
    (hx₀ : (dotyPhases asm ⟨0, by omega⟩).Pre c₀)
    (h_post : ∀ c, (dotyPhases asm ⟨21 - 1, by omega⟩).Post c →
        majorityStableEndpoint (L := L) (K := K) init c)
    (hC0 : ∀ i, Cphase i ≤ C0)
    (hδ : ∀ i, (δ i : ℝ≥0∞) ≤ (1 / (n : ℝ≥0∞) ^ 2)) :
    ((NonuniformMajority L K).transitionKernel ^ (∑ i, (dotyPhases asm i).t)) c₀
        {c | ¬ majorityStableEndpoint (L := L) (K := K) init c}
      ≤ (21 : ℝ≥0∞) / (n : ℝ≥0∞) ^ 2
    ∧ (∑ i, (dotyPhases asm i).t) ≤ 21 * C0 * n * (L + 1) :=
  BudgetTightening.doty_time_headline_W2_inv_sq
    init c₀ Cphase δ (dotyPhases asm) ht hε
    (dotyPhases_h_chain asm) hx₀ h_post hC0 hδ

/-- **The headline at the realised seam budget.**  Specialises
`doty_time_headline_CONCRETE` to the case where the per-slot budget `δ` is read off the
instances themselves (`δ i = (dotyPhases asm i).ε`), each `≤ 1/n²` by the campaign's
calibration.  Records that, with the EXACT seams forced, the composite failure is the
honest `21/n²`. -/
set_option maxHeartbeats 0 in
theorem doty_time_headline_CONCRETE_self
    {L K n C0 : ℕ}
    (init c₀ : Config (AgentState L K))
    (asm : DotyAssembly (L := L) (K := K) n)
    (Cphase : Fin 21 → ℕ)
    (ht : ∀ i, (dotyPhases asm i).t ≤ Cphase i * n * (L + 1))
    (hx₀ : (dotyPhases asm ⟨0, by omega⟩).Pre c₀)
    (h_post : ∀ c, (dotyPhases asm ⟨21 - 1, by omega⟩).Post c →
        majorityStableEndpoint (L := L) (K := K) init c)
    (hC0 : ∀ i, Cphase i ≤ C0)
    (hεcal : ∀ i, ((dotyPhases asm i).ε : ℝ≥0∞) ≤ (1 / (n : ℝ≥0∞) ^ 2)) :
    ((NonuniformMajority L K).transitionKernel ^ (∑ i, (dotyPhases asm i).t)) c₀
        {c | ¬ majorityStableEndpoint (L := L) (K := K) init c}
      ≤ (21 : ℝ≥0∞) / (n : ℝ≥0∞) ^ 2
    ∧ (∑ i, (dotyPhases asm i).t) ≤ 21 * C0 * n * (L + 1) :=
  doty_time_headline_CONCRETE init c₀ asm Cphase
    (fun i => (dotyPhases asm i).ε) ht (fun _ => le_refl _) hx₀ h_post hC0 hεcal

end ConcreteAssembly

end ExactMajority
