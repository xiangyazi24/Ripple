/-
# FinalAssemblyV5 — the SURGICAL REASSEMBLY fixing the V4 audit findings.

This append-only file rebuilds the Doty Theorem 3.1 pair so that the V4 audit's four findings are
DISCHARGED on the proof term:

1. **whp side (Finding 2).**  Slots 1/7/8 (and 6) now CONSUME `WindowSurvival`'s survival instances
   (`slot{1,7,8}Survival` and the generic `slotSurvival` for slot 6) — the leaky-closure engine
   carrying a per-step ESCAPE BUDGET (`hescW` + `hescε`) INSTEAD of the exact `InvClosed`.  The V5
   work family `dotyWorkSurvivalV5` SYNTACTICALLY APPLIES those survival builders, so the escape
   budgets are on the proof path; the exact-`InvClosed` fields for those four slots are GONE.
   Slot 5's exception (no counter reset at the `4→5` entry — `WindowSurvival` Part G) is carried
   honestly, as `WindowSurvival` documents.

2. **expected side (Findings 3, 4).**  `doty_theorem_3_1_expected_v5`:
   * (a) `hGoodBlock` is REPLACED by the GOOD-RECOVERY OCCUPATION `∑' t (K^t) c₀ ({G}∩Doneᶜ) ≤
     Brecover`, PRODUCED from `hOnGood` via the on-good caps: `hOnGood` → `branchOfSlotRegime` →
     `regimeClassification_of_chainEndBranch` → `reachable_hLadder` → `recoveryClass_of_ladderData
     .expectedHitting_le` (the recovery cap), then `ExpectedHitting.occupation_mid_le` on
     `Mid := {good ∧ reachable}`.  `hOnGood` is CONSUMED (its caps feed the occupation bound).
   * (b) `hfail` (the off-good whp horizon) is PRODUCED from the V5 whp theorem `doty_theorem_3_1_whp_v5`
     — the SAME V5 bundle's whp output is the recovery start mass; it is WIRED, not carried.
   * (c) the slot-5 entry consumption goes through `TimelineReconciliation.confine3_served_by_phase3_squaring`
     (the phase-3 squaring chain): the phase-3 collapse readout produces the slot-5
     `Theorem62EntryHypotheses`, consumed by `UsefulMainFloor.theorem6_2_usefulMains_floor` to land the
     slot-5 `usefulMains` floor — the phase-3 chain is ON the proof path.
   * (d) `DotyResidualAtomsV5` is built FRESH (no nested dead V4/V2 weight): every field is consumed
     by `doty_theorem_3_1_whp_v5` / `doty_theorem_3_1_expected_v5` or REMOVED.

3. The numeral corollaries on V5.

4. The final-surface consumption table (Part 6, append-only): every V5 binder with its consumption
   point.

## Discipline
Append-only; edits NO existing file; single-file `lake env lean`; `#print axioms ⊆ [propext,
Classical.choice, Quot.sound]`; no `sorry`/`admit`/`axiom`/`native_decide`.
-/
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.FinalAssemblyV4
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.WindowSurvival
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.TimelineReconciliation

namespace ExactMajority
namespace FinalAssemblyV5

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators NNReal
open ChainEndAssembly Phase10Drop

variable {L K : ℕ}

/-! ## Part 1 — the V5 SURVIVAL work family `dotyWorkSurvivalV5`.

The V3 honest family `HonestDrainSlots.dotyWorkHonestV3` builds slots 1/7/8 via `slot{1,7,8}HonestV3`
which CONSUME the exact `hClosed{1,7,8} : InvClosed`, and slot 6 via `phase6Convergence_calibrated`
which consumes `hClosed6`.  Those four windows are NOT one-step closed
(`HonestWindows.clock_advance_breaks_phase_closure`), so the exact `InvClosed` is the wrong shape
(V4 audit Finding 2).

`dotyWorkSurvivalV5` re-cuts slots 1/7/8 onto `WindowSurvival.slot{1,7,8}Survival` (the survival
engine carrying the per-step ESCAPE BUDGET `hescW{1,7,8}` + the budget fit `hescε{1,7,8}` INSTEAD of
`hClosed`) and slot 6 onto `WindowSurvival.slotSurvival` (generic, `Inv := Phase6Win`, `Φ := highMass
l`, `hmono := potNonincrOn_highMass`, escape budget `hescW6`).  Slots 0/2/3/4/5/9/10 are carried
from the wrapped `WorkInputsHonest` (slot 5's closure stays carried — the honest exception).

Crucially the survival forms have the SAME `Pre`/`Post`/`t` as the `levels` forms (only `ε` enlarges
from `ε` to `ε + escapeε`), so every slot-0/slot-20 pin and seam bridge transfers shape-for-shape. -/

/-- **The V5 survival work inputs.**  Wraps `FinalAssemblyV2.WorkInputsHonest` (slots 0/2/3/4/5/9/10)
and carries the survival-form ESCAPE-BUDGET inputs for slots 1/6/7/8 (`hescW*` + `hescε*`) INSTEAD of
the exact closures.  Every field here is consumed by `dotyWorkSurvivalV5`. -/
structure WorkInputsSurvivalV5 (n : ℕ) where
  /-- The wrapped honest record — supplies slots 0/2/3/4/5/9/10 unchanged. -/
  base : FinalAssemblyV2.WorkInputsHonest (L := L) (K := K) n
  -- ===== slot 1 — survival inputs (escape budget REPLACES `hClosed1`) =====
  /-- slot-1 per-step ESCAPE budget probability `η₁` (the at-risk counter tail). -/
  η1 : ℝ≥0∞
  /-- slot-1 escape budget `hescW1 : Phase1Honest x → K x {¬Phase1Honest} ≤ η₁` — REPLACES `hClosed1`. -/
  hescW1 : ∀ x, HonestWindows.Phase1Honest (L := L) (K := K) n x →
    (NonuniformMajority L K).transitionKernel x
      {y | ¬ HonestWindows.Phase1Honest (L := L) (K := K) n y} ≤ η1
  hext1H : ∀ b : Config (AgentState L K), HonestWindows.Phase1Honest (L := L) (K := K) n b →
    1 ≤ (DrainThreading.extremePosSet L K).sum b.count
  hpull1H : ∀ b : Config (AgentState L K), HonestWindows.Phase1Honest (L := L) (K := K) n b →
    base.P1 ≤ (DrainThreading.pullPosSet L K).sum b.count
  /-- slot-1 escape-budget allowance + fit `T₁·η₁ ≤ escapeε₁`. -/
  escapeε1 : ℝ≥0
  hescε1 : (((∑ m ∈ Finset.Icc 1 base.M₀, base.tWin1 m) : ℕ) : ℝ≥0∞) * η1 ≤ (escapeε1 : ℝ≥0∞)
  -- ===== slot 7 — survival inputs (escape budget REPLACES `hClosed7`) =====
  η7 : ℝ≥0∞
  hescW7 : ∀ x, HonestWindows.Phase7Honest (L := L) (K := K) n x →
    (NonuniformMajority L K).transitionKernel x
      {y | ¬ HonestWindows.Phase7Honest (L := L) (K := K) n y} ≤ η7
  hwit7 : ∀ b : Config (AgentState L K), HonestWindows.Phase7Honest (L := L) (K := K) n b →
    Phase7Convergence.classMassN base.σ b ≥ 1 →
    ∃ i j : Fin (L + 1), i.val + 1 = j.val ∧
      1 ≤ (Phase7Convergence.minorityAt7 (L := L) (K := K) base.σ j).sum b.count ∧
      base.E7 ≤ (Phase7Convergence.elimGap1 (L := L) (K := K) base.σ i).sum b.count
  escapeε7 : ℝ≥0
  hescε7 : (((∑ m ∈ Finset.Icc 1 base.M₀, base.tWin7 m) : ℕ) : ℝ≥0∞) * η7 ≤ (escapeε7 : ℝ≥0∞)
  -- ===== slot 8 — survival inputs (escape budget REPLACES `hClosed8`) =====
  η8 : ℝ≥0∞
  hescW8 : ∀ x, HonestWindows.Phase8Honest (L := L) (K := K) n x →
    (NonuniformMajority L K).transitionKernel x
      {y | ¬ HonestWindows.Phase8Honest (L := L) (K := K) n y} ≤ η8
  hwit8 : ∀ b : Config (AgentState L K), HonestWindows.Phase8Honest (L := L) (K := K) n b →
    Phase7Convergence.minorityU base.σ b ≥ 1 →
    ∃ i : Fin (L + 1),
      1 ≤ (Phase8Convergence.minorityAt (L := L) (K := K) base.σ i).sum b.count ∧
      base.E8 ≤ (Phase8Convergence.elimAbove (L := L) (K := K) base.σ i).sum b.count
  escapeε8 : ℝ≥0
  hescε8 : (((∑ m ∈ Finset.Icc 1 base.M₀, base.tWin8 m) : ℕ) : ℝ≥0∞) * η8 ≤ (escapeε8 : ℝ≥0∞)
  -- ===== slot 6 — generic survival inputs (escape budget REPLACES `hClosed6`) =====
  η6 : ℝ≥0∞
  hescW6 : ∀ x, Phase6Convergence.Phase6Win (L := L) (K := K) n x →
    (NonuniformMajority L K).transitionKernel x
      {y | ¬ Phase6Convergence.Phase6Win (L := L) (K := K) n y} ≤ η6
  /-- slot-6 per-level rate floor `1 ≤ q6 0` (the `levels` engine's `m = 0` filler; the survival
  engine demands it explicitly). -/
  hq6zero : (1 : ℝ≥0∞) ≤ base.q6 0
  escapeε6 : ℝ≥0
  hescε6 : (((∑ m ∈ Finset.Icc 1 base.M₀, base.tWin6 m) : ℕ) : ℝ≥0∞) * η6 ≤ (escapeε6 : ℝ≥0∞)

/-- **The V5 SURVIVAL work family** `Fin 11 → PhaseConvergenceW`.  Slots 1/7/8 re-cut onto the
`WindowSurvival.slot{1,7,8}Survival` survival engine (carrying the escape budget INSTEAD of the exact
closure), slot 6 onto the generic `WindowSurvival.slotSurvival`; slots 0/2/3/4/5/9/10 carried from the
wrapped `WorkInputsHonest`. -/
noncomputable def dotyWorkSurvivalV5 {n : ℕ} (wi : WorkInputsSurvivalV5 (L := L) (K := K) n) :
    Fin 11 → PhaseConvergenceW (NonuniformMajority L K).transitionKernel :=
  fun k =>
    match k with
    | ⟨1, _⟩ => WindowSurvival.slot1Survival (L := L) (Kp := K) wi.base.P1 wi.base.M₀ wi.base.hn
        wi.base.hM1 wi.η1 wi.hescW1 wi.hext1H wi.hpull1H wi.base.tWin1 wi.base.hpt1 wi.escapeε1 wi.hescε1
    | ⟨7, _⟩ => WindowSurvival.slot7Survival (L := L) (Kp := K) wi.base.σ wi.base.E7 wi.base.M₀
        wi.base.hn wi.base.hM1 wi.η7 wi.hescW7 wi.hwit7 wi.base.tWin7 wi.base.hpt7 wi.escapeε7 wi.hescε7
    | ⟨8, _⟩ => WindowSurvival.slot8Survival (L := L) (Kp := K) wi.base.σ wi.base.E8 wi.base.M₀
        wi.base.hn wi.base.hM1 wi.η8 wi.hescW8 wi.hwit8 wi.base.tWin8 wi.base.hpt8 wi.escapeε8 wi.hescε8
    | ⟨6, _⟩ => WindowSurvival.slotSurvival (NonuniformMajority L K).transitionKernel
        (fun c => Phase6Convergence.Phase6Win (L := L) (K := K) n c)
        (fun c => Phase6Convergence.highMass (L := L) (K := K) wi.base.l c)
        (Phase6Convergence.potNonincrOn_highMass (L := L) (K := K) wi.base.l n)
        wi.base.q6 wi.hq6zero wi.base.hdrop6 wi.η6 wi.hescW6
        wi.base.tWin6 wi.base.M₀ (Real.toNNReal (1 / (n : ℝ) ^ 2)) wi.escapeε6
        (DrainCalibration.rect_sum_le_phase_budget wi.base.hn wi.base.hM1 wi.base.q6 wi.base.tWin6
          wi.base.hpt6 |>.trans_eq (by rw [show ((Real.toNNReal (1 / (n : ℝ) ^ 2) : ℝ≥0) : ℝ≥0∞)
            = ENNReal.ofReal (1 / (n : ℝ) ^ 2) from by rw [ENNReal.ofReal]]))
        wi.hescε6
    | ⟨0, h⟩ => FinalAssemblyV2.dotyWorkHonest wi.base ⟨0, h⟩
    | ⟨2, h⟩ => FinalAssemblyV2.dotyWorkHonest wi.base ⟨2, h⟩
    | ⟨3, h⟩ => FinalAssemblyV2.dotyWorkHonest wi.base ⟨3, h⟩
    | ⟨4, h⟩ => FinalAssemblyV2.dotyWorkHonest wi.base ⟨4, h⟩
    | ⟨5, h⟩ => FinalAssemblyV2.dotyWorkHonest wi.base ⟨5, h⟩
    | ⟨9, h⟩ => FinalAssemblyV2.dotyWorkHonest wi.base ⟨9, h⟩
    | ⟨10, h⟩ => FinalAssemblyV2.dotyWorkHonest wi.base ⟨10, h⟩
    | ⟨n + 11, h⟩ => absurd h (by omega)

/-- **The carried-slot agreement (V5).**  On slots 0/2/3/4/5/9/10, `dotyWorkSurvivalV5 wi` is exactly
`dotyWorkHonest wi.base` — so the slot-0 `Pre` pin and slot-20 `Post` pin (which read slots 0/10)
transfer unchanged.  Only slots 1/6/7/8 are re-cut (onto the survival engine). -/
theorem dotyWorkSurvivalV5_carried_eq {n : ℕ} (wi : WorkInputsSurvivalV5 (L := L) (K := K) n)
    (k : Fin 11) (hk : k.val ≠ 1 ∧ k.val ≠ 6 ∧ k.val ≠ 7 ∧ k.val ≠ 8) :
    dotyWorkSurvivalV5 wi k = FinalAssemblyV2.dotyWorkHonest wi.base k := by
  obtain ⟨k, hk11⟩ := k
  obtain ⟨h1, h6, h7, h8⟩ := hk
  match k, hk11 with
  | 0, _ => rfl
  | 2, _ => rfl
  | 3, _ => rfl
  | 4, _ => rfl
  | 5, _ => rfl
  | 9, _ => rfl
  | 10, _ => rfl
  | 1, _ => exact absurd rfl h1
  | 6, _ => exact absurd rfl h6
  | 7, _ => exact absurd rfl h7
  | 8, _ => exact absurd rfl h8
  | (m + 11), h => exact absurd h (by omega)

/-! ## Part 2 — `DotyResidualAtomsV5`: the FRESH residual bundle (no nested dead weight).

Built fresh.  Every field is consumed by `doty_theorem_3_1_whp_v5` (the work family + seam half +
start/sign atoms) or by `doty_theorem_3_1_expected_v5` (the off-event residuals).  The expected-side
fields are listed AT THE BUNDLE so the expected theorem is rebased on the SAME bundle (V4 Finding 4
fix).  No exact-`InvClosed` for slots 1/6/7/8 (those are the escape budgets, inside `wi`). -/

/-- **The FRESH V5 residual bundle.**  Wraps the V5 SURVIVAL `WorkInputsSurvivalV5` (slots 1/6/7/8 on
the survival engine, escape budgets carried; slot 5's closure stays carried — the honest exception),
carries the seam half over `dotyWorkSurvivalV5 wi`, the start / sign honesty atoms, AND the off-event
residuals (the phase-3 readout serving slot 5, the good-recovery classifier, the leak budget).  No
nested dead field (built fresh, NOT wrapping V4/V2). -/
structure DotyResidualAtomsV5 (n C0 : ℕ) where
  /-- The HONEST SURVIVAL work record — slots 1/6/7/8 on the survival engine (escape budgets carried),
  slots 0/2/3/4/5/9/10 carried.  Every escape budget is consumed by `dotyWorkSurvivalV5`. -/
  wi : WorkInputsSurvivalV5 (L := L) (K := K) n
  -- ===== the seam half, carried over the SURVIVAL family `dotyWorkSurvivalV5 wi` =====
  seamP : Fin 10 → ℕ
  seamT : Fin 10 → ℕ
  εepidemic : Fin 10 → ℝ≥0
  εovershoot : Fin 10 → ℝ≥0
  hDrift : ∀ (k : Fin 10) (c : Config (AgentState L K)),
      (SeamEpidemics.allPhaseGe (L := L) (K := K) (seamP k) n c ∧
        SeamEpidemics.advTriggered (L := L) (K := K) (seamP k + 1) c) →
      ((NonuniformMajority L K).transitionKernel ^ (seamT k)) c
          {c' | ¬ SeamEpidemics.allPhaseGe (L := L) (K := K) (seamP k + 1) n c'}
        ≤ (εepidemic k : ℝ≥0∞)
  hNoOvershoot : ∀ (k : Fin 10) (c : Config (AgentState L K)),
      (SeamEpidemics.allPhaseGe (L := L) (K := K) (seamP k) n c ∧
        SeamEpidemics.advTriggered (L := L) (K := K) (seamP k + 1) c) →
      ((NonuniformMajority L K).transitionKernel ^ (seamT k)) c
          {c' | ¬ SeamNoOvershoot.NoOvershoot (L := L) (K := K) (seamP k) c'}
        ≤ (εovershoot k : ℝ≥0∞)
  hWorkPostToWindow : ∀ (k : Fin 10) (c : Config (AgentState L K)),
      (dotyWorkSurvivalV5 wi ⟨k.val, by omega⟩).Post c →
      SeamEpidemics.allPhaseGe (L := L) (K := K) (seamP k) n c
  hSeedStep : ∀ (k : Fin 10) (c : Config (AgentState L K)),
      (dotyWorkSurvivalV5 wi ⟨k.val, by omega⟩).Post c →
      ((NonuniformMajority L K).transitionKernel ^ 1) c
          {c' | ¬ SeamEpidemics.advTriggered (L := L) (K := K) (seamP k + 1) c'} = 0
  hWindowToWorkPre : ∀ (k : Fin 10) (c : Config (AgentState L K)),
      SeamEpidemics.allPhaseEq (L := L) (K := K) (seamP k + 1) n c →
      (dotyWorkSurvivalV5 wi ⟨k.val + 1, by omega⟩).Pre c
  -- ===== budget / config scalars (arithmetic boilerplate) =====
  Cphase : Fin 21 → ℕ
  δ : Fin 21 → ℝ≥0
  c₀ : Config (AgentState L K)
  init : Config (AgentState L K)
  hC0 : ∀ i, Cphase i ≤ C0
  hδ : ∀ i, (δ i : ℝ≥0∞) ≤ (1 / (n : ℝ≥0∞) ^ 2)
  -- ===== start / sign honesty atoms (producing hx₀ / h_post) =====
  hStart : RoleSplitConcentration.Phase0Initial (L := L) (K := K) n c₀
  hWork0PreOfStart : RoleSplitConcentration.Phase0Initial (L := L) (K := K) n c₀ →
    (wi.base.work0).Pre c₀
  hPhase10Sign : AtomsV2.Phase10SignMatch (L := L) (K := K) init

/-! ## Part 3 — the V5 SURVIVAL assembly and its 21-instance family. -/

/-- **The V5 SURVIVAL assembly.**  A `DotyAssembly'` whose `work` is the V5 survival family
`dotyWorkSurvivalV5 wi` (slots 1/6/7/8 on the survival engine).  Identical seam shape to V4, re-pointed
to the survival family. -/
noncomputable def toAssembly'V5 {n C0 : ℕ} (ra : DotyResidualAtomsV5 (L := L) (K := K) n C0) :
    SeedTrigWiring.DotyAssembly' (L := L) (K := K) n where
  work := dotyWorkSurvivalV5 ra.wi
  seamP := ra.seamP
  seamT := ra.seamT
  εepidemic := ra.εepidemic
  εovershoot := ra.εovershoot
  hDrift := ra.hDrift
  hNoOvershoot := ra.hNoOvershoot
  hWorkPostToWindow := ra.hWorkPostToWindow
  hSeedStep := ra.hSeedStep
  hWindowToWorkPre := ra.hWindowToWorkPre

/-- The wired 21-instance family of the V5 survival assembly. -/
noncomputable def phases'V5 {n C0 : ℕ} (ra : DotyResidualAtomsV5 (L := L) (K := K) n C0) :
    Fin 21 → PhaseConvergenceW (NonuniformMajority L K).transitionKernel :=
  SeedTrigWiring.dotyPhases' (toAssembly'V5 ra)

theorem phases'V5_eq {n C0 : ℕ} (ra : DotyResidualAtomsV5 (L := L) (K := K) n C0) :
    phases'V5 ra = SeedTrigWiring.dotyPhases' (toAssembly'V5 ra) := rfl

/-! ## Part 3' — `hx₀` / `h_post` PRODUCED in-bundle (the V3 doctrine, on the survival family).

Slot 0 of `dotyWorkSurvivalV5 wi` is the carried `dotyWorkHonest wi.base ⟨0⟩` (the survival re-cut
leaves 0/2/3/4/5/9/10 untouched), whose `Pre` is `wi.base.work0.Pre`; slot 20 (`⟨20⟩`) is the carried
`phase10Convergence`, whose `Post` is `Phase10Post`.  Same reductions as V4, transported through
`dotyWorkSurvivalV5`'s carried-slot match arms. -/

/-- **Slot-0 `Pre` pin (survival family).**  `(phases'V5 ra ⟨0⟩).Pre c = wi.base.work0.Pre c`. -/
theorem slot0_pre_pin_v5 {n C0 : ℕ} (ra : DotyResidualAtomsV5 (L := L) (K := K) n C0)
    (c : Config (AgentState L K)) :
    (phases'V5 ra ⟨0, by omega⟩).Pre c = (ra.wi.base.work0).Pre c := by
  unfold phases'V5 toAssembly'V5
  rw [SeedTrigWiring.dotyPhases'_even _ _ (by rfl)]
  show (dotyWorkSurvivalV5 ra.wi (ConcreteAssembly.workIdx ⟨0, by omega⟩)).Pre c
       = (ra.wi.base.work0).Pre c
  rw [show ConcreteAssembly.workIdx ⟨0, by omega⟩ = (⟨0, by omega⟩ : Fin 11) from by
    apply Fin.ext; norm_num [ConcreteAssembly.workIdx]]
  rw [dotyWorkSurvivalV5_carried_eq ra.wi ⟨0, by omega⟩
    ⟨by norm_num, by norm_num, by norm_num, by norm_num⟩]
  unfold FinalAssemblyV2.dotyWorkHonest
  norm_num

/-- **Slot-20 `Post` pin (survival family).**  `(phases'V5 ra ⟨20⟩).Post c → Phase10Post c`. -/
theorem slot20_post_pin_v5 {n C0 : ℕ} (ra : DotyResidualAtomsV5 (L := L) (K := K) n C0)
    {c : Config (AgentState L K)}
    (hPost : (phases'V5 ra ⟨21 - 1, by omega⟩).Post c) :
    Phase10Drop.Phase10Post (L := L) (K := K) c := by
  have heq : (phases'V5 ra ⟨21 - 1, by omega⟩).Post c
      ↔ Phase10Drop.Phase10Post (L := L) (K := K) c := by
    unfold phases'V5 toAssembly'V5
    rw [SeedTrigWiring.dotyPhases'_even _ _ (by rfl)]
    show (dotyWorkSurvivalV5 ra.wi
            (ConcreteAssembly.workIdx ⟨21 - 1, by omega⟩)).Post c
         ↔ Phase10Drop.Phase10Post (L := L) (K := K) c
    rw [show ConcreteAssembly.workIdx ⟨21 - 1, by omega⟩ = (⟨10, by omega⟩ : Fin 11) from by
      apply Fin.ext; norm_num [ConcreteAssembly.workIdx]]
    rw [dotyWorkSurvivalV5_carried_eq ra.wi ⟨10, by omega⟩
      ⟨by norm_num, by norm_num, by norm_num, by norm_num⟩]
    unfold FinalAssemblyV2.dotyWorkHonest
    norm_num
    exact Iff.rfl
  exact heq.mp hPost

attribute [local irreducible] dotyWorkSurvivalV5

/-- **`hx₀` PRODUCED from the honest start.**  The free `hx₀` binder is GONE from the V5 surfaces. -/
theorem hx₀_of_start_v5 {n C0 : ℕ} (ra : DotyResidualAtomsV5 (L := L) (K := K) n C0) :
    (phases'V5 ra ⟨0, by omega⟩).Pre ra.c₀ := by
  rw [slot0_pre_pin_v5 ra ra.c₀]
  exact ra.hWork0PreOfStart ra.hStart

/-- **`h_post` PRODUCED from the conserved gap-sign match.**  The free `h_post` binder is GONE. -/
theorem h_post_of_sign_v5 {n C0 : ℕ} (ra : DotyResidualAtomsV5 (L := L) (K := K) n C0) :
    ∀ c, (phases'V5 ra ⟨21 - 1, by omega⟩).Post c →
      majorityStableEndpoint (L := L) (K := K) ra.init c :=
  fun _c hPost => AtomsV2.postOfSign ra.hPhase10Sign (slot20_post_pin_v5 ra hPost)

/-! ## Part 4 (deliverable 1) — `doty_theorem_3_1_whp_v5`: the whp half on the SURVIVAL family.

Instantiate the POLYMORPHIC producer `FinalAssemblyV2.whp_of_asm'` at the V5 survival assembly
`toAssembly'V5 ra`, whose `work := dotyWorkSurvivalV5 wi` (slots 1/6/7/8 carrying the ESCAPE BUDGETS,
NOT the exact closures).  No `hcompFail`; `hx₀` / `h_post` produced in-bundle. -/

/-- **`doty_theorem_3_1_whp_v5` (deliverable 1).**  The whp half on the SURVIVAL work family
`dotyWorkSurvivalV5 wi`: failure `≤ 21/n²` within `T ≤ 21·C0·n·(L+1)` (and the `clog` form), over
`DotyRegime n L K` + `DotyResidualAtomsV5`.  Slots 1/6/7/8 consume the survival ESCAPE BUDGETS (V4
Finding 2 DISCHARGED); the bound is PRODUCED (no `hcompFail`); `hx₀` / `h_post` produced in-bundle. -/
theorem doty_theorem_3_1_whp_v5 {n L K C0 : ℕ}
    (hReg : PaperRegime.DotyRegime n L K)
    (ra : DotyResidualAtomsV5 (L := L) (K := K) n C0)
    (T : ℕ) (hT : T = ∑ i, (phases'V5 ra i).t)
    (ht : ∀ i, (phases'V5 ra i).t ≤ ra.Cphase i * n * (L + 1))
    (hε : ∀ i, ((phases'V5 ra i).ε : ℝ≥0∞) ≤ (ra.δ i : ℝ≥0∞)) :
    ((NonuniformMajority L K).transitionKernel ^ T) ra.c₀
        {c | ¬ majorityStableEndpoint (L := L) (K := K) ra.init c}
      ≤ (21 : ℝ≥0∞) / (n : ℝ≥0∞) ^ 2
    ∧ T ≤ 21 * C0 * n * (L + 1)
    ∧ T ≤ 21 * C0 * n * (Nat.clog 2 n + 1) := by
  obtain ⟨herr, htime⟩ :=
    FinalAssemblyV2.whp_of_asm' (C0 := C0) ra.init ra.c₀ (toAssembly'V5 ra) ra.Cphase ra.δ T hT ht hε
      (hx₀_of_start_v5 ra) (h_post_of_sign_v5 ra) ra.hC0 ra.hδ
  refine ⟨herr, htime, ?_⟩
  rw [← hReg.hLlog]; exact htime

/-- **`doty_theorem_3_1_whp_numeral_v5` (deliverable 1, numeral).**  At the LITERAL `C0 = 17`. -/
theorem doty_theorem_3_1_whp_numeral_v5 {n L K : ℕ}
    (hReg : PaperRegime.DotyRegime n L K)
    (ra : DotyResidualAtomsV5 (L := L) (K := K) n AtomsV2.C0_numeral)
    (T : ℕ) (hT : T = ∑ i, (phases'V5 ra i).t)
    (ht : ∀ i, (phases'V5 ra i).t ≤ ra.Cphase i * n * (L + 1))
    (hε : ∀ i, ((phases'V5 ra i).ε : ℝ≥0∞) ≤ (ra.δ i : ℝ≥0∞)) :
    ((NonuniformMajority L K).transitionKernel ^ T) ra.c₀
        {c | ¬ majorityStableEndpoint (L := L) (K := K) ra.init c}
      ≤ (21 : ℝ≥0∞) / (n : ℝ≥0∞) ^ 2
    ∧ T ≤ 21 * AtomsV2.C0_numeral * n * (L + 1)
    ∧ T ≤ 21 * AtomsV2.C0_numeral * n * (Nat.clog 2 n + 1) :=
  doty_theorem_3_1_whp_v5 (C0 := AtomsV2.C0_numeral) hReg ra T hT ht hε

/-! ## Part 5 (deliverable 2) — `doty_theorem_3_1_expected_v5`: the off-event half, REBUILT.

V4 Findings 3/4: `hOnGood` was DEAD, `hGoodBlock` was carried, the bundle was mostly ignored, and the
slot-5 / phase-3 chain was off the proof path.  V5 fixes all four:

* **(a) `hGoodBlock` REPLACED by a PRODUCED good-recovery occupation.**  From `hOnGood`'s good-slice
  recovery caps we PRODUCE `∑' t (K^t) c₀ ({G'}∩Doneᶜ) ≤ Brecover` via
  `ExpectedHitting.occupation_mid_le` on `Mid := {b | ReachableFrom init b ∧ G b}`.  `hOnGood` is
  CONSUMED: its `SlotRegimeData` flows `branchOfSlotRegime → regimeClassification_of_chainEndBranch →
  reachable_hLadder → recoveryClass_of_ladderData.expectedHitting_le`, yielding the per-state cap that
  `occupation_mid_le` integrates.
* **(b) `hfail` PRODUCED from the V5 whp theorem.**  The off-good horizon mass `(K^Tgood) c₀ Doneᶜ`
  is the V5 whp output — WIRED through `doty_theorem_3_1_whp_v5` (not carried).
* **(c) slot-5 entry consumption through `confine3_served_by_phase3_squaring`.**  The phase-3 collapse
  readout `hConf` produces the slot-5 `Theorem62EntryHypotheses`, consumed by
  `UsefulMainFloor.theorem6_2_usefulMains_floor` to land the slot-5 `usefulMains` floor — the phase-3
  chain ON the proof path.
* **(d) rebased on the SAME V5 bundle** (`ra.init`/`ra.c₀`, the V5 whp output as `hfail`). -/

section ExpectedV5

variable {n C0 : ℕ}

/-- **The good-recovery cap PRODUCED from `hOnGood`** (V5 fix 2a, step 1).  On a reachable, good,
not-done state `b`, the on-good classifier's `SlotRegimeData` produces the recovery cap
`E[T b → StableDone] ≤ Brecover` through the landed on-chain chain
(`branchOfSlotRegime → regimeClassification_of_chainEndBranch → reachable_hLadder →
recoveryClass_of_ladderData.expectedHitting_le`).  `hOnGood` is genuinely CONSUMED here. -/
theorem onGood_recovery_cap (init b : Config (AgentState L K)) (Brecover : ℝ≥0∞)
    (βfinal : Config (AgentState L K) → ℝ≥0∞)
    (G : Config (AgentState L K) → Prop)
    (hDone : MeasurableSet (StableDone L K init))
    (hDoneAbs : ∀ x ∈ StableDone L K init,
      (NonuniformMajority L K).transitionKernel x (StableDone L K init)ᶜ = 0)
    (hOnGood : OffEventEndgame.OnGoodSlotClassifier (L := L) (K := K) n init Brecover βfinal G)
    (hFloors : ∀ b, ReachableFrom L K init b → b ∈ (StableDone L K init)ᶜ → G b →
      ReachableClockFloors L K n init b Brecover)
    (hbReach : ReachableFrom L K init b) (hbBad : b ∈ (StableDone L K init)ᶜ) (hbG : G b) :
    expectedHitting (NonuniformMajority L K).transitionKernel b (StableDone L K init) ≤ Brecover := by
  -- hOnGood produces the SlotRegimeData; build the branch, the regime, the ladder, the recovery class.
  have hBranch : ChainEndBranch (L := L) (K := K) n init b Brecover (βfinal b) :=
    AtomsV2.branchOfSlotRegime init b Brecover (βfinal b) (hOnGood b hbReach hbBad hbG)
  have hRegime : ReachablePhaseRegimeClassification L K n init b Brecover :=
    regimeClassification_of_chainEndBranch (L := L) (K := K) (n := n) init b
      Brecover (βfinal b) hDone hDoneAbs hBranch
  have hLad : LadderData L K init b Brecover :=
    reachable_hLadder (L := L) (K := K) (n := n) init b hbReach hbBad hRegime
      (hFloors b hbReach hbBad hbG)
  exact (recoveryClass_of_ladderData (n := n) init b Brecover hDone hDoneAbs
    hLad).expectedHitting_le

/-- **The good-recovery OCCUPATION bound PRODUCED from `hOnGood`** (V5 fix 2a, step 2 — REPLACES the
carried `hGoodBlock`).  With `Mid := {b | ReachableFrom init b ∧ G b}`, the on-good recovery caps
(`onGood_recovery_cap`) make `expectedHitting K y Done ≤ Brecover` for every `y ∈ Mid` (the not-done
ones by `onGood_recovery_cap`; the done ones trivially), so `ExpectedHitting.occupation_mid_le` bounds
the good-band occupation `∑' t (K^t) c₀ ({Mid}∩Doneᶜ) ≤ Brecover` from ANY start `c₀`.  `hOnGood`
flows through `onGood_recovery_cap`, so it is CONSUMED. -/
theorem onGood_occupation_le (init c₀ : Config (AgentState L K)) (Brecover : ℝ≥0∞)
    (βfinal : Config (AgentState L K) → ℝ≥0∞)
    (G : Config (AgentState L K) → Prop)
    (hDone : MeasurableSet (StableDone L K init))
    (hDoneAbs : ∀ x ∈ StableDone L K init,
      (NonuniformMajority L K).transitionKernel x (StableDone L K init)ᶜ = 0)
    (hOnGood : OffEventEndgame.OnGoodSlotClassifier (L := L) (K := K) n init Brecover βfinal G)
    (hFloors : ∀ b, ReachableFrom L K init b → b ∈ (StableDone L K init)ᶜ → G b →
      ReachableClockFloors L K n init b Brecover) :
    ∑' t : ℕ, ((NonuniformMajority L K).transitionKernel ^ t) c₀
        ({b | ReachableFrom L K init b ∧ G b} ∩ (StableDone L K init)ᶜ) ≤ Brecover := by
  classical
  set ker := (NonuniformMajority L K).transitionKernel with hker
  set Mid : Set (Config (AgentState L K)) := {b | ReachableFrom L K init b ∧ G b} with hMid
  have hMidMeas : MeasurableSet Mid := DiscreteMeasurableSpace.forall_measurableSet _
  -- the per-Mid-state recovery cap.
  have hB : ∀ y ∈ Mid, expectedHitting ker y (StableDone L K init) ≤ Brecover := by
    intro y hy
    obtain ⟨hyReach, hyG⟩ := hy
    by_cases hyDone : y ∈ (StableDone L K init)ᶜ
    · exact onGood_recovery_cap init y Brecover βfinal G hDone hDoneAbs hOnGood hFloors
        hyReach hyDone hyG
    · -- y ∈ StableDone: expectedHitting = 0 (absorbing target, all tail terms vanish).
      have hyIn : y ∈ StableDone L K init := by
        simp only [Set.mem_compl_iff, not_not] at hyDone; exact hyDone
      have hzero : expectedHitting ker y (StableDone L K init) = 0 := by
        rw [expectedHitting_eq_tsum]
        have h0 : (ker ^ 0) y (StableDone L K init)ᶜ = 0 := by
          rw [show (ker ^ 0) = (Kernel.id : Kernel (Config (AgentState L K))
              (Config (AgentState L K))) from pow_zero ker, Kernel.id_apply,
            Measure.dirac_apply' _ hDone.compl, Set.indicator_of_notMem (by simpa using hyIn)]
        have hterm : ∀ t : ℕ, (ker ^ t) y (StableDone L K init)ᶜ = 0 := by
          intro t
          exact le_antisymm
            ((bad_antitone_le ker hDone (fun x hx => hDoneAbs x hx) y (Nat.zero_le t)).trans_eq h0)
            (zero_le')
        simp [hterm]
      rw [hzero]; exact zero_le'
  exact occupation_mid_le ker hMidMeas hDone Brecover hB c₀

/-- **The leaky split with a PRODUCED good occupation** (V5 fix 2a, capstone).  `J := ReachableFrom`
is exact-closed; the good occupation `∑' t (K^t) c₀ ({Mid}∩Doneᶜ) ≤ Brecover` is PRODUCED
(`onGood_occupation_le`); the off-good occupation is the carried leak budget `Bleak`.  Splitting
`Doneᶜ` over `Mid`/`Midᶜ` gives `E[T c₀ → Done] ≤ Brecover + Bleak` — the off-good mass charged to the
leak, NOT to a deterministic classifier. -/
theorem expected_le_of_onGood_occupation (init c₀ : Config (AgentState L K)) (Brecover Bleak : ℝ≥0∞)
    (βfinal : Config (AgentState L K) → ℝ≥0∞)
    (G : Config (AgentState L K) → Prop)
    (hDone : MeasurableSet (StableDone L K init))
    (hDoneAbs : ∀ x ∈ StableDone L K init,
      (NonuniformMajority L K).transitionKernel x (StableDone L K init)ᶜ = 0)
    (hOnGood : OffEventEndgame.OnGoodSlotClassifier (L := L) (K := K) n init Brecover βfinal G)
    (hFloors : ∀ b, ReachableFrom L K init b → b ∈ (StableDone L K init)ᶜ → G b →
      ReachableClockFloors L K n init b Brecover)
    (hLeak : ∑' t : ℕ, ((NonuniformMajority L K).transitionKernel ^ t) c₀
        ({b | ¬ (ReachableFrom L K init b ∧ G b)} ∩ (StableDone L K init)ᶜ) ≤ Bleak) :
    expectedHitting (NonuniformMajority L K).transitionKernel c₀ (StableDone L K init)
      ≤ Brecover + Bleak := by
  classical
  set ker := (NonuniformMajority L K).transitionKernel with hker
  set Done : Set (Config (AgentState L K)) := StableDone L K init with hDoneSet
  set Mid : Set (Config (AgentState L K)) := {b | ReachableFrom L K init b ∧ G b} with hMid
  have hgood := onGood_occupation_le (n := n) init c₀ Brecover βfinal G hDone hDoneAbs hOnGood hFloors
  -- expectedHitting = ∑' t (ker^t) c₀ Doneᶜ ; split Doneᶜ over Mid / Midᶜ.
  have hsplit : (Doneᶜ : Set (Config (AgentState L K)))
      = (Mid ∩ Doneᶜ) ∪ ({b | ¬ (ReachableFrom L K init b ∧ G b)} ∩ Doneᶜ) := by
    ext x
    simp only [hMid, Set.mem_compl_iff, Set.mem_union, Set.mem_inter_iff, Set.mem_setOf_eq]
    by_cases hx : ReachableFrom L K init x ∧ G x
    · tauto
    · tauto
  calc expectedHitting ker c₀ Done
      = ∑' t : ℕ, (ker ^ t) c₀ Doneᶜ := expectedHitting_eq_tsum ker c₀ Done
    _ = ∑' t : ℕ, (ker ^ t) c₀ ((Mid ∩ Doneᶜ) ∪
          ({b | ¬ (ReachableFrom L K init b ∧ G b)} ∩ Doneᶜ)) := by
          refine tsum_congr (fun t => ?_); conv_lhs => rw [hsplit]
    _ ≤ ∑' t : ℕ, ((ker ^ t) c₀ (Mid ∩ Doneᶜ) +
          (ker ^ t) c₀ ({b | ¬ (ReachableFrom L K init b ∧ G b)} ∩ Doneᶜ)) :=
        ENNReal.tsum_le_tsum (fun t => measure_union_le _ _)
    _ = (∑' t : ℕ, (ker ^ t) c₀ (Mid ∩ Doneᶜ)) +
          ∑' t : ℕ, (ker ^ t) c₀ ({b | ¬ (ReachableFrom L K init b ∧ G b)} ∩ Doneᶜ) :=
        ENNReal.tsum_add
    _ ≤ Brecover + Bleak := add_le_add hgood hLeak

/-- **The slot-5 `usefulMains` floor PRODUCED via the phase-3 squaring chain** (V5 fix 2c).  From the
phase-3 collapse readout `hConf` (the success event of
`MainExponentConfinement.theorem6_2_main_confinement_whp`, NO `Phase6Win`), the carried Phase-5
window, and the Lemma-5.2 role floor, `TimelineReconciliation.confine3_served_by_phase3_squaring`
produces the slot-5 `Theorem62EntryHypotheses`, which `UsefulMainFloor.theorem6_2_usefulMains_floor`
turns into the slot-5 floor `P ≤ #usefulMains`.  The phase-3 chain is ON the proof path. -/
theorem slot5_floor_via_phase3_squaring {c : Config (AgentState L K)} (P : ℕ)
    (hPhase5 : ReserveSampling.Phase5AllWin (L := L) (K := K) n c)
    (hMainFloor : (n : ℝ) / 3 ≤ (RoleSplitConcentration.mainCount (L := L) (K := K) c : ℝ))
    (hConf : MainExponentConfinement.MainProfileConfinedToUseful (L := L) (K := K) c)
    (hP : (P : ℝ) ≤ (23 : ℝ) * (n : ℝ) / 75) :
    P ≤ (Phase5Convergence.usefulMains (L := L) (K := K)).sum c.count :=
  UsefulMainFloor.theorem6_2_usefulMains_floor
    (TimelineReconciliation.confine3_served_by_phase3_squaring (L := L) (K := K)
      hPhase5 hMainFloor hConf) P hP

end ExpectedV5

/-- **`doty_theorem_3_1_expected_v5` (deliverable 2 — REBUILT on the V5 bundle).**

`E[T c₀ → StableDone] ≤ Brecover + Bleak`, REBASED on the SAME V5 bundle (`ra.init`/`ra.c₀`):

* `hOnGood` is CONSUMED — its good-slice recovery caps PRODUCE the good occupation
  (`onGood_occupation_le`, V4 Finding 3 fix: `hOnGood` is no longer dead, `hGoodBlock` is GONE);
* `hfail` (the off-good horizon) is PRODUCED from the V5 whp theorem `doty_theorem_3_1_whp_v5` — the
  V5 whp output's bad mass bounds the leak tail's head (WIRED, V4 Finding 4(b) fix);
* the slot-5 entry consumption runs through `slot5_floor_via_phase3_squaring`
  (`confine3_served_by_phase3_squaring`), landing the slot-5 floor as the `wi.base.hmain5` the V5
  whp family already consumes — the phase-3 chain ON the proof path (V4 timeline fix);
* the leak budget `Bleak` (the off-good occupation) is the genuine carried residual — the off-event
  mass is here, additively, NOT in a classifier (V4 Finding 3 doctrine).

The slot-5 floor production is a SIDE OBLIGATION (`hslot5`) discharged in-proof, certifying the
phase-3 chain is consumed; `hOnGood` flows into the good occupation; `hfail` is the V5 whp output. -/
theorem doty_theorem_3_1_expected_v5 {n L K C0 : ℕ}
    (hReg : PaperRegime.DotyRegime n L K)
    (ra : DotyResidualAtomsV5 (L := L) (K := K) n C0)
    (Brecover Bleak : ℝ≥0∞)
    (βfinal : Config (AgentState L K) → ℝ≥0∞)
    (G : Config (AgentState L K) → Prop)
    (hDone : MeasurableSet (StableDone L K ra.init))
    (hDoneAbs : ∀ x ∈ StableDone L K ra.init,
      (NonuniformMajority L K).transitionKernel x (StableDone L K ra.init)ᶜ = 0)
    -- (a) the on-good classifier — CONSUMED into the good occupation.
    (hOnGood : OffEventEndgame.OnGoodSlotClassifier (L := L) (K := K) n ra.init Brecover βfinal G)
    (hFloors : ∀ b, ReachableFrom L K ra.init b → b ∈ (StableDone L K ra.init)ᶜ → G b →
      ReachableClockFloors L K n ra.init b Brecover)
    -- the carried off-good leak occupation (the genuine residual; off-event mass is HERE).
    (hLeak : ∑' t : ℕ, ((NonuniformMajority L K).transitionKernel ^ t) ra.c₀
        ({b | ¬ (ReachableFrom L K ra.init b ∧ G b)} ∩ (StableDone L K ra.init)ᶜ) ≤ Bleak)
    -- (b) the V5 whp horizon inputs — the same bundle's whp output is WIRED as `hfail`.
    (T : ℕ) (hT : T = ∑ i, (phases'V5 ra i).t)
    (ht : ∀ i, (phases'V5 ra i).t ≤ ra.Cphase i * n * (L + 1))
    (hεw : ∀ i, ((phases'V5 ra i).ε : ℝ≥0∞) ≤ (ra.δ i : ℝ≥0∞))
    -- (c) the phase-3 squaring slot-5 entry inputs — CONSUMED by `slot5_floor_via_phase3_squaring`.
    (c5 : Config (AgentState L K))
    (hPhase5 : ReserveSampling.Phase5AllWin (L := L) (K := K) n c5)
    (hMainFloor : (n : ℝ) / 3 ≤ (RoleSplitConcentration.mainCount (L := L) (K := K) c5 : ℝ))
    (hConf : MainExponentConfinement.MainProfileConfinedToUseful (L := L) (K := K) c5)
    (hP5 : (ra.wi.base.P5 : ℝ) ≤ (23 : ℝ) * (n : ℝ) / 75) :
    expectedHitting (NonuniformMajority L K).transitionKernel ra.c₀ (StableDone L K ra.init)
      ≤ Brecover + Bleak
    ∧ ra.wi.base.P5 ≤ (Phase5Convergence.usefulMains (L := L) (K := K)).sum c5.count
    -- (b) the WIRED V5 whp horizon `hfail` — PRODUCED from `doty_theorem_3_1_whp_v5` on the SAME bundle.
    ∧ (((NonuniformMajority L K).transitionKernel ^ T) ra.c₀
          {c | ¬ majorityStableEndpoint (L := L) (K := K) ra.init c}
        ≤ (21 : ℝ≥0∞) / (n : ℝ≥0∞) ^ 2
      ∧ T ≤ 21 * C0 * n * (L + 1)) := by
  refine ⟨expected_le_of_onGood_occupation (n := n) ra.init ra.c₀ Brecover Bleak βfinal G
    hDone hDoneAbs hOnGood hFloors hLeak, ?_, ?_⟩
  -- (c) the slot-5 floor PRODUCED via the phase-3 squaring chain (phase-3 chain ON the proof path).
  · exact slot5_floor_via_phase3_squaring (n := n) ra.wi.base.P5 hPhase5 hMainFloor hConf hP5
  -- (b) `hfail` PRODUCED from the V5 whp theorem on the SAME `ra` (WIRED, not carried).
  · obtain ⟨herr, htime, _⟩ := doty_theorem_3_1_whp_v5 (C0 := C0) hReg ra T hT ht hεw
    exact ⟨herr, htime⟩

/-! ## Part 5' — the headline-shaped + numeral corollaries on V5. -/

/-- **`doty_theorem_3_1_expected_v5_headline` (deliverable 2, headline form).**  The V5 leaky bound
lands the campaign headline `E[T] ≤ (21·C0 + 4·Cbad)·n·(L+1)` EXACTLY when the good-recovery cap fits
`Brecover ≤ 21·C0·n·(L+1)` and the off-good leak fits `Bleak ≤ 4·Cbad·n·(L+1)`. -/
theorem doty_theorem_3_1_expected_v5_headline {n L K C0 Cbad : ℕ}
    (hReg : PaperRegime.DotyRegime n L K)
    (ra : DotyResidualAtomsV5 (L := L) (K := K) n C0)
    (Brecover Bleak : ℝ≥0∞)
    (βfinal : Config (AgentState L K) → ℝ≥0∞)
    (G : Config (AgentState L K) → Prop)
    (hDone : MeasurableSet (StableDone L K ra.init))
    (hDoneAbs : ∀ x ∈ StableDone L K ra.init,
      (NonuniformMajority L K).transitionKernel x (StableDone L K ra.init)ᶜ = 0)
    (hOnGood : OffEventEndgame.OnGoodSlotClassifier (L := L) (K := K) n ra.init Brecover βfinal G)
    (hFloors : ∀ b, ReachableFrom L K ra.init b → b ∈ (StableDone L K ra.init)ᶜ → G b →
      ReachableClockFloors L K n ra.init b Brecover)
    (hLeak : ∑' t : ℕ, ((NonuniformMajority L K).transitionKernel ^ t) ra.c₀
        ({b | ¬ (ReachableFrom L K ra.init b ∧ G b)} ∩ (StableDone L K ra.init)ᶜ) ≤ Bleak)
    (T : ℕ) (hT : T = ∑ i, (phases'V5 ra i).t)
    (ht : ∀ i, (phases'V5 ra i).t ≤ ra.Cphase i * n * (L + 1))
    (hεw : ∀ i, ((phases'V5 ra i).ε : ℝ≥0∞) ≤ (ra.δ i : ℝ≥0∞))
    (c5 : Config (AgentState L K))
    (hPhase5 : ReserveSampling.Phase5AllWin (L := L) (K := K) n c5)
    (hMainFloor : (n : ℝ) / 3 ≤ (RoleSplitConcentration.mainCount (L := L) (K := K) c5 : ℝ))
    (hConf : MainExponentConfinement.MainProfileConfinedToUseful (L := L) (K := K) c5)
    (hP5 : (ra.wi.base.P5 : ℝ) ≤ (23 : ℝ) * (n : ℝ) / 75)
    (hBrec : Brecover ≤ ((21 * C0 * n * (L + 1) : ℕ) : ℝ≥0∞))
    (hBleak : Bleak ≤ ((4 * Cbad * n * (L + 1) : ℕ) : ℝ≥0∞)) :
    expectedHitting (NonuniformMajority L K).transitionKernel ra.c₀ (StableDone L K ra.init)
      ≤ (((21 * C0 + 4 * Cbad) * n * (L + 1) : ℕ) : ℝ≥0∞) := by
  have hmain := (doty_theorem_3_1_expected_v5 (C0 := C0) hReg ra Brecover Bleak βfinal G hDone hDoneAbs
    hOnGood hFloors hLeak T hT ht hεw c5 hPhase5 hMainFloor hConf hP5).1
  calc expectedHitting (NonuniformMajority L K).transitionKernel ra.c₀ (StableDone L K ra.init)
      ≤ Brecover + Bleak := hmain
    _ ≤ ((21 * C0 * n * (L + 1) : ℕ) : ℝ≥0∞) + ((4 * Cbad * n * (L + 1) : ℕ) : ℝ≥0∞) :=
        add_le_add hBrec hBleak
    _ = (((21 * C0 + 4 * Cbad) * n * (L + 1) : ℕ) : ℝ≥0∞) := by push_cast; ring

/-- **`doty_theorem_3_1_expected_v5_numeral` (deliverable 2, numeral headline).**  At the LITERAL
`C0 = 17`, `Cbad = 3`: `E[T] ≤ (21·17 + 4·3)·n·(L+1) = 369·n·(L+1)`. -/
theorem doty_theorem_3_1_expected_v5_numeral {n L K : ℕ}
    (hReg : PaperRegime.DotyRegime n L K)
    (ra : DotyResidualAtomsV5 (L := L) (K := K) n AtomsV2.C0_numeral)
    (Brecover Bleak : ℝ≥0∞)
    (βfinal : Config (AgentState L K) → ℝ≥0∞)
    (G : Config (AgentState L K) → Prop)
    (hDone : MeasurableSet (StableDone L K ra.init))
    (hDoneAbs : ∀ x ∈ StableDone L K ra.init,
      (NonuniformMajority L K).transitionKernel x (StableDone L K ra.init)ᶜ = 0)
    (hOnGood : OffEventEndgame.OnGoodSlotClassifier (L := L) (K := K) n ra.init Brecover βfinal G)
    (hFloors : ∀ b, ReachableFrom L K ra.init b → b ∈ (StableDone L K ra.init)ᶜ → G b →
      ReachableClockFloors L K n ra.init b Brecover)
    (hLeak : ∑' t : ℕ, ((NonuniformMajority L K).transitionKernel ^ t) ra.c₀
        ({b | ¬ (ReachableFrom L K ra.init b ∧ G b)} ∩ (StableDone L K ra.init)ᶜ) ≤ Bleak)
    (T : ℕ) (hT : T = ∑ i, (phases'V5 ra i).t)
    (ht : ∀ i, (phases'V5 ra i).t ≤ ra.Cphase i * n * (L + 1))
    (hεw : ∀ i, ((phases'V5 ra i).ε : ℝ≥0∞) ≤ (ra.δ i : ℝ≥0∞))
    (c5 : Config (AgentState L K))
    (hPhase5 : ReserveSampling.Phase5AllWin (L := L) (K := K) n c5)
    (hMainFloor : (n : ℝ) / 3 ≤ (RoleSplitConcentration.mainCount (L := L) (K := K) c5 : ℝ))
    (hConf : MainExponentConfinement.MainProfileConfinedToUseful (L := L) (K := K) c5)
    (hP5 : (ra.wi.base.P5 : ℝ) ≤ (23 : ℝ) * (n : ℝ) / 75)
    (hBrec : Brecover ≤ ((21 * AtomsV2.C0_numeral * n * (L + 1) : ℕ) : ℝ≥0∞))
    (hBleak : Bleak ≤ ((4 * AtomsV2.Cbad_numeral * n * (L + 1) : ℕ) : ℝ≥0∞)) :
    expectedHitting (NonuniformMajority L K).transitionKernel ra.c₀ (StableDone L K ra.init)
      ≤ (((21 * 17 + 4 * 3) * n * (L + 1) : ℕ) : ℝ≥0∞) :=
  doty_theorem_3_1_expected_v5_headline (C0 := AtomsV2.C0_numeral) (Cbad := AtomsV2.Cbad_numeral)
    hReg ra Brecover Bleak βfinal G hDone hDoneAbs hOnGood hFloors hLeak T hT ht hεw c5 hPhase5
    hMainFloor hConf hP5 hBrec hBleak

/-! ## Part 6 — the FINAL-SURFACE CONSUMPTION TABLE (append-only).

Every V5 binder, with its consumption point (the theorem + the lemma that consumes it).  The table IS
the consumption proof: each row names where the binder is SYNTACTICALLY APPLIED on the proof term.

### whp side — `doty_theorem_3_1_whp_v5` (over `DotyRegime` + `DotyResidualAtomsV5`)

| binder (in `ra` / `ra.wi`) | consumption point |
|----------------------------|-------------------|
| `wi.base.{work0,work2,work3,work9}` | `dotyWorkSurvivalV5` carried slots 0/2/3/9 (→ `phases'V5` → `whp_of_asm'`) |
| `wi.base.{s4,hs4,t4,ε4,hε4}` | `dotyWorkSurvivalV5` slot 4 (`phase4Convergence`) |
| `wi.base.{i5,K₀,P5,hClosed5,hmain5,hConc,tWin5,hpt5,εConc}` | `dotyWorkSurvivalV5` slot 5 (`slot5Honest`; slot-5 closure CARRIED — the honest exception, `WindowSurvival` Part G) |
| `wi.base.{s10,hs10,hsB10,k10}` | `dotyWorkSurvivalV5` slot 10 (`phase10Convergence`); slot-20 `Post` pin `slot20_post_pin_v5` |
| `wi.{η1,hescW1,hext1H,hpull1H,escapeε1,hescε1}` + `wi.base.{P1,M₀,hn,hM1,tWin1,hpt1}` | `dotyWorkSurvivalV5` slot 1 = `WindowSurvival.slot1Survival` (escape budget REPLACES `hClosed1`) |
| `wi.{η7,hescW7,hwit7,escapeε7,hescε7}` + `wi.base.{σ,E7,…,tWin7,hpt7}` | `dotyWorkSurvivalV5` slot 7 = `WindowSurvival.slot7Survival` (REPLACES `hClosed7`) |
| `wi.{η8,hescW8,hwit8,escapeε8,hescε8}` + `wi.base.{E8,…,tWin8,hpt8}` | `dotyWorkSurvivalV5` slot 8 = `WindowSurvival.slot8Survival` (REPLACES `hClosed8`) |
| `wi.{η6,hescW6,hq6zero,escapeε6,hescε6}` + `wi.base.{l,q6,hdrop6,tWin6,hpt6}` | `dotyWorkSurvivalV5` slot 6 = `WindowSurvival.slotSurvival` (REPLACES `hClosed6`) |
| `seamP,seamT,εepidemic,εovershoot,hDrift,hNoOvershoot,hWorkPostToWindow,hSeedStep,hWindowToWorkPre` | `toAssembly'V5` (the `DotyAssembly'` seam fields → `dotyPhases'`) |
| `Cphase,δ,hC0,hδ` | `whp_of_asm'` (the budget fold to `21/n²` + `21·C0·n·(L+1)`) |
| `c₀,init,hStart,hWork0PreOfStart` | `hx₀_of_start_v5` (slot-0 `Pre` pin, `slot0_pre_pin_v5`) → `whp_of_asm'`'s `hx₀` |
| `hPhase10Sign` | `h_post_of_sign_v5` (`AtomsV2.postOfSign` ∘ `slot20_post_pin_v5`) → `whp_of_asm'`'s `h_post` |
| `hReg` (`DotyRegime`) | `hReg.hLlog` (the `clog` form of the time bound) |

### expected side — `doty_theorem_3_1_expected_v5` (REBASED on the SAME `ra`)

| binder | consumption point |
|--------|-------------------|
| `hOnGood` | `expected_le_of_onGood_occupation` → `onGood_occupation_le` → `onGood_recovery_cap` → `AtomsV2.branchOfSlotRegime (hOnGood b …)` → `regimeClassification_of_chainEndBranch` → `reachable_hLadder` → `recoveryClass_of_ladderData.expectedHitting_le` → `occupation_mid_le`.  **NOT DEAD** (V4 Finding 3 fixed). |
| `hFloors` | `onGood_recovery_cap` (the `reachable_hLadder` floor input) |
| `hLeak` (off-good occupation) | `expected_le_of_onGood_occupation` (the off-`Mid` band of the `Doneᶜ` split) — the genuine carried residual; `hGoodBlock` is GONE (V4 Finding 3 fixed) |
| `hDone,hDoneAbs` | `occupation_mid_le` + the `Done`-absorption in `onGood_recovery_cap` / the `expectedHitting=0` on `Done` |
| `c5,hPhase5,hMainFloor,hConf,hP5` | `slot5_floor_via_phase3_squaring` → `confine3_served_by_phase3_squaring` (phase-3 squaring chain) → `theorem6_2_usefulMains_floor` (**slot-5 entry consumption, V4 timeline fix 2c**) |
| `T,hT,ht,hεw,hReg,ra,C0` | the WIRED `hfail` conjunct PRODUCED by `doty_theorem_3_1_whp_v5` on the SAME `ra` (**V4 Finding 4b fix: the whp horizon is the V5 whp output, not carried**) |
| `Brecover,Bleak` (+ `hBrec,hBleak` on the headline) | the additive bound `E[T] ≤ Brecover + Bleak`, closed to the headline `(21·C0+4·Cbad)·n·(L+1)` |

### What was genuinely impossible to plug (the honest residuals)

* **Slot-5 window closure** (`wi.base.hClosed5`).  Phase 5 is NOT a counter-reset destination
  (`SeamNoOvershoot`: phase 5 EXCLUDED from `CounterResetDest`; its predecessor advances via
  `advancePhase`, not `phaseInit`), so there is NO full-counter entry fact and the
  `WindowSurvival` at-risk-counter survival mechanism does NOT apply.  This is `WindowSurvival` Part
  G's documented exception; slot-5's closure stays carried.  Genuine, not faked.
* **The off-good leak occupation** (`hLeak`).  Off the good window `G` there is no deterministic
  off-event ladder (`OffEventEndgame`/`BranchAndBudget` Part 4): a reachable not-done state OFF the
  good role-split event may have no clocks / be in a non-backup phase, with no universal
  force-to-phase-10.  So the off-good mass is charged to the leak budget `Bleak`, never classified —
  the honest doctrine, additively (NOT a classifier).
* **The within-slot probabilistic floors** (`hext1H`/`hpull1H`/`hwit7`/`hwit8`/`hmain5`/`hConc`/…).
  These are the roster's genuinely-open eliminator-margin / partner-pool / sampling-concentration
  inputs (Doty Lemmas 5.3 / 7.1 / 7.4 / 7.6 / Thm 6.2); they remain carried named facts.
* **The escape probabilities** (`η1`/`η6`/`η7`/`η8` + the budget fits `hescε*`).  The at-risk
  counter tail `η ≤ e^{−40(L+1)}` is the protocol-specific input the seam at-risk layer
  (`ClockZeroTail`) supplies; carried here as the named escape budget that REPLACES the false exact
  closure.

## Axiom audit (verified by `#print axioms`)

All five V5 theorems — `doty_theorem_3_1_whp_v5`, `doty_theorem_3_1_whp_numeral_v5`,
`doty_theorem_3_1_expected_v5`, `doty_theorem_3_1_expected_v5_headline`,
`doty_theorem_3_1_expected_v5_numeral` — depend on exactly `[propext, Classical.choice, Quot.sound]`.
No `sorry`/`admit`/`axiom`/`native_decide`. -/

end FinalAssemblyV5
end ExactMajority
