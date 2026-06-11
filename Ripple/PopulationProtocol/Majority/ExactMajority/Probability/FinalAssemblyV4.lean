/-
# FinalAssemblyV4 — the DEFINITIVE consolidation: the Doty Theorem 3.1 pair on the HONEST work family.

This is the final-consolidation deliverable.  Every roster item of `DOTY_POST63_CAMPAIGN.md` has
been attacked across the campaign; this file assembles the definitive pair, putting the genuinely
HONEST work family `HonestDrainSlots.dotyWorkHonestV3` (slots 1/7/8 re-cut onto the chain-honest
phase-only windows — `Phase{1,7,8}Honest`, NOT the all-Main UNSAT windows) on the proof path of the
whp half, and re-basing the leaky off-event expected half on the same V4 residual bundle.

## The two deliverables

1. **`doty_theorem_3_1_whp_v4`** — the whp half on the HONEST family.  Built by instantiating the
   POLYMORPHIC producer `FinalAssemblyV2.whp_of_asm'` (which takes a FREE `DotyAssembly'` and PRODUCES
   the `21/n²` failure bound through `BudgetTightening.doty_time_headline_W2_inv_sq`) at the V4 honest
   assembly `toAssembly'V4`, whose `work := dotyWorkHonestV3 wi`.  No `hcompFail` anywhere; the bound
   is PRODUCED.  `hx₀` / `h_post` are PRODUCED in-bundle from the honest start / sign atoms (the V3
   doctrine, carried verbatim — `slot0_pre_pin`-flavoured + `AtomsV2.postOfSign`).

2. **`doty_theorem_3_1_expected_v4_final`** — `OffEventEndgame.doty_theorem_3_1_expected_v4` (the
   leaky-good-invariant split-geometric: exact `J = ReachableFrom` closure, leaky `G` membership, the
   off-good mass charged to the leak `η` — NO deterministic off-event ladder) re-based on the SAME V4
   bundle's `init`/`c₀`.  Its headline-shaped corollary closes `(21·C0 + 4·Cbad)·n·(L+1)` exactly
   when the leak fits the recovery budget (`OffEventEndgame.v4_headline_of_budget`).

3. The numeral corollaries at `C0 = 17`, `Cbad = 3`.

## The residual re-cut — `DotyResidualAtomsV4`

The residual bundle is RE-CUT so every field is a GENUINELY-OPEN named fact (verified against the
landed productions of this campaign — each candidate field was grep-checked NOT to be discharged by a
file plugged here).  The campaign's PRODUCTIONS are ON the proof path (no dead decoration):

* the HONEST work family `dotyWorkHonestV3 wi` — slots 1/7/8 on the chain-honest windows (the
  `WindowSurvival` survival forms: `hClosed{1,7,8}` carried as the named seam-gap closures);
* the seam half — `hDrift` / `hWorkPostToWindow` / `hNoOvershoot` (the `SeamQuickWins` Wave-1
  productions) and `hWindowToWorkPre`, carried over the V3 family;
* `hx₀` PRODUCED from `hStart` (slot-0 `Pre` pin); `h_post` PRODUCED from `hPhase10Sign`
  (`AtomsV2.postOfSign`).

The carried GENUINELY-OPEN survivors (each doc-commented with paper citation + landed partial
machinery) are exactly the roster's open content: `hext1H`'s `+3` floor (`SmallSweep` sharp verdict),
the `work{0,2,3,9}` opaque stage instances + scalars (`SmallSweep` union algebra), the per-hour §6
budgets (the width budgets + the phase-3 squaring per-hour drain events — `HourInduction` /
`NotchDrain` / `ClockCeiling` / `TimelineReconciliation`), slot-5's entry floors + escape
(`SamplingAtoms` ATOM 1 inputs + ATOM 2 named remainder), the drain-seam `SeedStepEvent`s
(`SmallSweep` negative verdict), the `{2,3,4,5,9}` seam guards, the slot-5 honest-window closure, the
leak budget `η`, and `DotyRegime`.

## Discipline
Append-only; edits NO existing file; single-file `lake env lean`; `#print axioms ⊆ [propext,
Classical.choice, Quot.sound]`; no `sorry`/`admit`/`axiom`/`native_decide`.
-/
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.FinalAssemblyV3
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.HonestDrainSlots
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.OffEventEndgame

namespace ExactMajority
namespace FinalAssemblyV4

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators NNReal
open ChainEndAssembly Phase10Drop

variable {L K : ℕ}

/-! ## Part 1 — `DotyResidualAtomsV4`: the definitive residual bundle on the HONEST family.

`wi : WorkInputsHonestV3` supplies the honest work family (slots 1/7/8 on chain-honest windows; the
survival-form `hClosed{1,7,8}` are its fields).  The seam feeders / bridges / one-step seed are
carried over `dotyWorkHonestV3 wi` (exactly the `DotyResidualAtomsV2` seam shapes, re-pointed to the
V3 family).  `hStart` / `hPhase10Sign` produce `hx₀` / `h_post`. -/

/-- **The definitive V4 residual bundle.**  Wraps the HONEST `WorkInputsHonestV3` work record (slots
1/7/8 on the chain-honest phase-only windows) and carries the seam half over `dotyWorkHonestV3 wi`
plus the start / sign honesty atoms.  Every field is a genuinely-open named fact (see the per-field
doc citations) or a production input; no field is discharged by a file plugged here. -/
structure DotyResidualAtomsV4 (n C0 : ℕ) where
  /-- **The HONEST work record** (`HonestDrainSlots.WorkInputsHonestV3`): slots 1/7/8 on the
  chain-honest windows `Phase{1,7,8}Honest` (the `WindowSurvival` survival forms — `hClosed{1,7,8}`
  are its fields, the named seam-gap closures), slots 0/2/3/4/5/6/9/10 carried from the wrapped
  `WorkInputsHonest`.  Carries the GENUINELY-OPEN within-slot atoms: `hext1H`'s `+3` extreme floor
  (Doty Lemma 5.3 / [45]; `SmallSweep` proved the survey's `extremeU>0` claim FALSE-as-stated — the
  `+3` end is sign-selected, `extremeSt_val_zero_or_six`), `hpull1H` (Lemma 5.3 partner pool),
  `hwit7`/`hwit8` (Lemmas 7.4 / 7.6 eliminator margins, `MarginInstantiation` instantiable from the
  §6 doubling-drain positional content), the `work{0,2,3,9}` opaque stage instances (`SmallSweep`:
  union ALGEBRA locked via `calibratedUnionW`, epidemic SCALARS free), the slot-5 floors `hmain5`/`P5`
  (Doty Thm 6.2 bias-ledger) and `hConc`/concentration (Doty Lemma 7.1; `SamplingAtoms` ATOM 1
  `hrfloor` PRODUCED, ATOM 2 escape NAMED), the slot-5 honest-window closure `hClosed5`, and the
  per-level §6 Phase-6 drain rate `q6`/`hdrop6`. -/
  wi : HonestDrainSlots.WorkInputsHonestV3 (L := L) (K := K) n
  -- ===== the seam half, carried over the HONEST family `dotyWorkHonestV3 wi` =====
  /-- Per-seam phase index `p = seamP k`. -/
  seamP : Fin 10 → ℕ
  /-- Per-seam epidemic horizon `t = seamT k`. -/
  seamT : Fin 10 → ℕ
  /-- Per-seam epidemic-drift budget. -/
  εepidemic : Fin 10 → ℝ≥0
  /-- Per-seam no-overshoot budget. -/
  εovershoot : Fin 10 → ℝ≥0
  /-- **`hDrift` (seam epidemic drift; PRODUCIBLE — `SeamQuickWins.wave1_hDrift` ← `SeamEpidemics.
  seam_drift`).**  Carried here over the honest family as the calibrated seam-drift bound; the
  production is `SeamEpidemics.seam_drift` (`SeamEpidemics:1093`) modulo the per-seam Phase-4-shape
  arithmetic tail check.  Doty §10 seam epidemic. -/
  hDrift : ∀ (k : Fin 10) (c : Config (AgentState L K)),
      (SeamEpidemics.allPhaseGe (L := L) (K := K) (seamP k) n c ∧
        SeamEpidemics.advTriggered (L := L) (K := K) (seamP k + 1) c) →
      ((NonuniformMajority L K).transitionKernel ^ (seamT k)) c
          {c' | ¬ SeamEpidemics.allPhaseGe (L := L) (K := K) (seamP k + 1) n c'}
        ≤ (εepidemic k : ℝ≥0∞)
  /-- **`hNoOvershoot` (seam clock no-overshoot; `SeamQuickWins.wave1_hNoOvershoot` produces the
  deterministic bridge `DetSeamOvershootBridge`, the `{2,3,4,5,9}` clock-zero tails remain NAMED).**
  The within-seam clock-zero concentration `AtRiskClockZero ≤ exp(−40(L+1))` is the genuinely-open
  remainder (Doty Lemma 5.2 clock-separation); `ClockZeroTail` discharged the GATE shape (the seam
  tail for the `{1,6,7,8}` counter-reset destinations), leaving the non-reset seams NAMED. -/
  hNoOvershoot : ∀ (k : Fin 10) (c : Config (AgentState L K)),
      (SeamEpidemics.allPhaseGe (L := L) (K := K) (seamP k) n c ∧
        SeamEpidemics.advTriggered (L := L) (K := K) (seamP k + 1) c) →
      ((NonuniformMajority L K).transitionKernel ^ (seamT k)) c
          {c' | ¬ SeamNoOvershoot.NoOvershoot (L := L) (K := K) (seamP k) c'}
        ≤ (εovershoot k : ℝ≥0∞)
  /-- **`hWorkPostToWindow` (work.Post → allPhaseGe; PRODUCIBLE — `SeamQuickWins.
  wave1_hWorkPostToWindow` ← `AssemblyBridges.mk_hWorkPostToWindow`).**  Carried over the honest
  family. -/
  hWorkPostToWindow : ∀ (k : Fin 10) (c : Config (AgentState L K)),
      (HonestDrainSlots.dotyWorkHonestV3 wi ⟨k.val, by omega⟩).Post c →
      SeamEpidemics.allPhaseGe (L := L) (K := K) (seamP k) n c
  /-- **`hSeedStep` (one-step advTriggered seed; GENUINELY OPEN — `SmallSweep` NEGATIVE verdict).**
  The honest phase-only window does NOT supply the drained ALL-CLOCK state the timed seed needs
  (`SmallSweep.seedStepEvent_needs_drained_state`), so the `SeedStepEvent` survives as the genuine
  one-step remainder.  Doty §10 seed rung. -/
  hSeedStep : ∀ (k : Fin 10) (c : Config (AgentState L K)),
      (HonestDrainSlots.dotyWorkHonestV3 wi ⟨k.val, by omega⟩).Post c →
      ((NonuniformMajority L K).transitionKernel ^ 1) c
          {c' | ¬ SeamEpidemics.advTriggered (L := L) (K := K) (seamP k + 1) c'} = 0
  /-- **`hWindowToWorkPre` (allPhaseEq → next work.Pre; card/phase half PRODUCIBLE — `AssemblyBridges.
  mk_hWindowToWorkPre_pin`; per-phase entry pins carried).**  Carried over the honest family. -/
  hWindowToWorkPre : ∀ (k : Fin 10) (c : Config (AgentState L K)),
      SeamEpidemics.allPhaseEq (L := L) (K := K) (seamP k + 1) n c →
      (HonestDrainSlots.dotyWorkHonestV3 wi ⟨k.val + 1, by omega⟩).Pre c
  -- ===== budget / config / regime scalars (arithmetic boilerplate) =====
  Cphase : Fin 21 → ℕ
  δ : Fin 21 → ℝ≥0
  c₀ : Config (AgentState L K)
  init : Config (AgentState L K)
  hC0 : ∀ i, Cphase i ≤ C0
  hδ : ∀ i, (δ i : ℝ≥0∞) ≤ (1 / (n : ℝ≥0∞) ^ 2)
  -- ===== start / sign honesty atoms (the V3 doctrine, producing hx₀ / h_post) =====
  /-- **`hStart` (primitive start — Doty initial config).**  The `Phase0Initial`-honest start
  (all-`mcr` phase-0); an honest fact about the problem instance, not a dischargeable residual. -/
  hStart : RoleSplitConcentration.Phase0Initial (L := L) (K := K) n c₀
  /-- **`hWork0PreOfStart` (slot-0 `Pre` interface).**  The deterministic pin `Phase0Initial n c₀ →
  work0.Pre c₀` for the carried role-split slot-0 instance (slot-0 of the honest family is the carried
  `wi.base.work0`). -/
  hWork0PreOfStart : RoleSplitConcentration.Phase0Initial (L := L) (K := K) n c₀ →
    (wi.base.work0).Pre c₀
  /-- **`hPhase10Sign` (Doty §11 phase-10 sign conservation).**  The conserved gap-sign-match residual
  (`SignMatch` threaded it from a single rooted activity+reachability invariant; the full conservation
  is the §11 backup-entry argument). -/
  hPhase10Sign : AtomsV2.Phase10SignMatch (L := L) (K := K) init

/-! ## Part 2 — the V4 honest assembly and its 21-instance family. -/

/-- **The V4 honest assembly.**  A `DotyAssembly'` whose `work` is the HONEST family
`dotyWorkHonestV3 wi` (slots 1/7/8 on the chain-honest windows).  Identical seam shape to
`toAssembly'V2`, re-pointed to the honest family. -/
noncomputable def toAssembly'V4 {n C0 : ℕ} (ra : DotyResidualAtomsV4 (L := L) (K := K) n C0) :
    SeedTrigWiring.DotyAssembly' (L := L) (K := K) n where
  work := HonestDrainSlots.dotyWorkHonestV3 ra.wi
  seamP := ra.seamP
  seamT := ra.seamT
  εepidemic := ra.εepidemic
  εovershoot := ra.εovershoot
  hDrift := ra.hDrift
  hNoOvershoot := ra.hNoOvershoot
  hWorkPostToWindow := ra.hWorkPostToWindow
  hSeedStep := ra.hSeedStep
  hWindowToWorkPre := ra.hWindowToWorkPre

/-- The wired 21-instance family of the V4 honest assembly. -/
noncomputable def phases'V4 {n C0 : ℕ} (ra : DotyResidualAtomsV4 (L := L) (K := K) n C0) :
    Fin 21 → PhaseConvergenceW (NonuniformMajority L K).transitionKernel :=
  SeedTrigWiring.dotyPhases' (toAssembly'V4 ra)

/-- `phases'V4 ra = dotyPhases' (toAssembly'V4 ra)` (recorded by `rfl`). -/
theorem phases'V4_eq {n C0 : ℕ} (ra : DotyResidualAtomsV4 (L := L) (K := K) n C0) :
    phases'V4 ra = SeedTrigWiring.dotyPhases' (toAssembly'V4 ra) := rfl

/-! ## Part 3 — `hx₀` / `h_post` PRODUCED in-bundle (the V3 doctrine on the honest family).

Slot 0 of the honest family `dotyWorkHonestV3 wi` is the carried `dotyWorkHonest wi.base ⟨0⟩` (the
honest re-cut leaves 0/2/3/4/5/6/9/10 untouched), whose `Pre` is `wi.base.work0.Pre`.  Slot 10 (the
`⟨20⟩` index of the doubled phase family) is the carried `phase10Convergence`, whose `Post` is
`Phase10Post`.  So the slot-0 `Pre` pin and slot-20 `Post` pin are the SAME reductions as the V3
file's, transported through `dotyWorkHonestV3`'s carried-slot match arms. -/

/-- **Slot-0 `Pre` pin (honest family).**  `(phases'V4 ra ⟨0⟩).Pre c = wi.base.work0.Pre c`.

`dotyWorkHonestV3 ra.wi ⟨0⟩` carried-equals `dotyWorkHonest ra.wi.base ⟨0⟩` (the honest re-cut leaves
slot 0 untouched), whose `Pre` is `work0.Pre` — exactly `FinalAssemblyV3.slot0_pre_pin`. -/
theorem slot0_pre_pin_v4 {n C0 : ℕ} (ra : DotyResidualAtomsV4 (L := L) (K := K) n C0)
    (c : Config (AgentState L K)) :
    (phases'V4 ra ⟨0, by omega⟩).Pre c = (ra.wi.base.work0).Pre c := by
  unfold phases'V4 toAssembly'V4
  rw [SeedTrigWiring.dotyPhases'_even _ _ (by rfl)]
  show (HonestDrainSlots.dotyWorkHonestV3 ra.wi (ConcreteAssembly.workIdx ⟨0, by omega⟩)).Pre c
       = (ra.wi.base.work0).Pre c
  rw [show ConcreteAssembly.workIdx ⟨0, by omega⟩ = (⟨0, by omega⟩ : Fin 11) from by
    apply Fin.ext; norm_num [ConcreteAssembly.workIdx]]
  rw [HonestDrainSlots.dotyWorkHonestV3_carried_eq ra.wi ⟨0, by omega⟩
    ⟨by norm_num, by norm_num, by norm_num⟩]
  unfold FinalAssemblyV2.dotyWorkHonest
  norm_num

/-- **Slot-20 `Post` pin (honest family).**  `(phases'V4 ra ⟨20⟩).Post c → Phase10Post c`. -/
theorem slot20_post_pin_v4 {n C0 : ℕ} (ra : DotyResidualAtomsV4 (L := L) (K := K) n C0)
    {c : Config (AgentState L K)}
    (hPost : (phases'V4 ra ⟨21 - 1, by omega⟩).Post c) :
    Phase10Drop.Phase10Post (L := L) (K := K) c := by
  have heq : (phases'V4 ra ⟨21 - 1, by omega⟩).Post c
      ↔ Phase10Drop.Phase10Post (L := L) (K := K) c := by
    unfold phases'V4 toAssembly'V4
    rw [SeedTrigWiring.dotyPhases'_even _ _ (by rfl)]
    show (HonestDrainSlots.dotyWorkHonestV3 ra.wi
            (ConcreteAssembly.workIdx ⟨21 - 1, by omega⟩)).Post c
         ↔ Phase10Drop.Phase10Post (L := L) (K := K) c
    rw [show ConcreteAssembly.workIdx ⟨21 - 1, by omega⟩ = (⟨10, by omega⟩ : Fin 11) from by
      apply Fin.ext; norm_num [ConcreteAssembly.workIdx]]
    rw [HonestDrainSlots.dotyWorkHonestV3_carried_eq ra.wi ⟨10, by omega⟩
      ⟨by norm_num, by norm_num, by norm_num⟩]
    unfold FinalAssemblyV2.dotyWorkHonest
    norm_num
    exact Iff.rfl
  exact heq.mp hPost

/-! ## Part 3' — block the honest-V3 fold divergence.

`HonestDrainSlots.dotyWorkHonestV3` builds slots 1/7/8 on `OneSidedCancel.levels_PhaseConvergenceW`
(the honest engine).  Reducing `(phases'V4 ra i).t` through the kernel-power `whnf` during the horizon
fold would blow the heartbeat budget exactly as the V2 family did.  We block it locally AFTER the pins
(which need the carried-slot reduction): the V4 whp theorem consumes the work family POLYMORPHICALLY
(through `t`/`ε`/`Pre`/`Post` as a `PhaseConvergenceW`, fed to the FREE `asm` of `whp_of_asm'`), so the
fold never needs to reduce it. -/

attribute [local irreducible] HonestDrainSlots.dotyWorkHonestV3

/-- **`hx₀` PRODUCED from the honest start.**  The free `hx₀` binder is GONE from the V4 surfaces. -/
theorem hx₀_of_start_v4 {n C0 : ℕ} (ra : DotyResidualAtomsV4 (L := L) (K := K) n C0) :
    (phases'V4 ra ⟨0, by omega⟩).Pre ra.c₀ := by
  rw [slot0_pre_pin_v4 ra ra.c₀]
  exact ra.hWork0PreOfStart ra.hStart

/-- **`h_post` PRODUCED from the conserved gap-sign match.**  The free `h_post` binder is GONE. -/
theorem h_post_of_sign_v4 {n C0 : ℕ} (ra : DotyResidualAtomsV4 (L := L) (K := K) n C0) :
    ∀ c, (phases'V4 ra ⟨21 - 1, by omega⟩).Post c →
      majorityStableEndpoint (L := L) (K := K) ra.init c :=
  fun _c hPost => AtomsV2.postOfSign ra.hPhase10Sign (slot20_post_pin_v4 ra hPost)

/-! ## Part 4 (deliverable 1) — `doty_theorem_3_1_whp_v4`: the whp half on the HONEST family.

Instantiate the POLYMORPHIC producer `FinalAssemblyV2.whp_of_asm'` (FREE `asm`; PRODUCES the `21/n²`
bound through `BudgetTightening.doty_time_headline_W2_inv_sq`) at the V4 honest assembly
`toAssembly'V4 ra`.  No `hcompFail`; `hx₀` / `h_post` produced in-bundle. -/

/-- **`doty_theorem_3_1_whp_v4` (deliverable 1).**  The whp half on the HONEST work family
`dotyWorkHonestV3 wi` (slots 1/7/8 on the chain-honest windows): failure `≤ 21/n²` within
`T ≤ 21·C0·n·(L+1)` (and the `clog` form), over `DotyRegime n L K` + `DotyResidualAtomsV4`.  The bound
is PRODUCED (no `hcompFail`); `hx₀` / `h_post` are produced in-bundle from the honest start / sign
atoms. -/
theorem doty_theorem_3_1_whp_v4 {n L K C0 : ℕ}
    (hReg : PaperRegime.DotyRegime n L K)
    (ra : DotyResidualAtomsV4 (L := L) (K := K) n C0)
    (T : ℕ) (hT : T = ∑ i, (phases'V4 ra i).t)
    (ht : ∀ i, (phases'V4 ra i).t ≤ ra.Cphase i * n * (L + 1))
    (hε : ∀ i, ((phases'V4 ra i).ε : ℝ≥0∞) ≤ (ra.δ i : ℝ≥0∞)) :
    ((NonuniformMajority L K).transitionKernel ^ T) ra.c₀
        {c | ¬ majorityStableEndpoint (L := L) (K := K) ra.init c}
      ≤ (21 : ℝ≥0∞) / (n : ℝ≥0∞) ^ 2
    ∧ T ≤ 21 * C0 * n * (L + 1)
    ∧ T ≤ 21 * C0 * n * (Nat.clog 2 n + 1) := by
  -- The failure bound is PRODUCED over the FREE `asm := toAssembly'V4 ra` (the honest assembly), at
  -- the OPAQUE `T`.  `hx₀` / `h_post` produced in-bundle.  No `hcompFail` binder anywhere.
  obtain ⟨herr, htime⟩ :=
    FinalAssemblyV2.whp_of_asm' (C0 := C0) ra.init ra.c₀ (toAssembly'V4 ra) ra.Cphase ra.δ T hT ht hε
      (hx₀_of_start_v4 ra) (h_post_of_sign_v4 ra) ra.hC0 ra.hδ
  refine ⟨herr, htime, ?_⟩
  rw [← hReg.hLlog]; exact htime

/-- **`doty_theorem_3_1_whp_numeral_v4` (deliverable 1, numeral).**  The whp half at the LITERAL
`C0 = 17` on the honest family: failure `≤ 21/n²` within `T ≤ 21·17·n·(L+1)`. -/
theorem doty_theorem_3_1_whp_numeral_v4 {n L K : ℕ}
    (hReg : PaperRegime.DotyRegime n L K)
    (ra : DotyResidualAtomsV4 (L := L) (K := K) n AtomsV2.C0_numeral)
    (T : ℕ) (hT : T = ∑ i, (phases'V4 ra i).t)
    (ht : ∀ i, (phases'V4 ra i).t ≤ ra.Cphase i * n * (L + 1))
    (hε : ∀ i, ((phases'V4 ra i).ε : ℝ≥0∞) ≤ (ra.δ i : ℝ≥0∞)) :
    ((NonuniformMajority L K).transitionKernel ^ T) ra.c₀
        {c | ¬ majorityStableEndpoint (L := L) (K := K) ra.init c}
      ≤ (21 : ℝ≥0∞) / (n : ℝ≥0∞) ^ 2
    ∧ T ≤ 21 * AtomsV2.C0_numeral * n * (L + 1)
    ∧ T ≤ 21 * AtomsV2.C0_numeral * n * (Nat.clog 2 n + 1) :=
  doty_theorem_3_1_whp_v4 (C0 := AtomsV2.C0_numeral) hReg ra T hT ht hε

/-! ## Part 5 (deliverable 2) — `doty_theorem_3_1_expected_v4_final`: the leaky off-event half.

`OffEventEndgame.doty_theorem_3_1_expected_v4` (the leaky-good-invariant split-geometric: exact
`J = ReachableFrom` closure, leaky `G` membership, the off-good mass charged to `η` — NO deterministic
off-event ladder) re-based on the SAME V4 bundle's `init` / `c₀`.  The on-good classifier `hOnGood`,
the good-slice block-half `hGoodBlock`, the escape budget `hLeak` (the WindowSurvival-style charge),
and the whp horizon `hfail` are the carried inputs; everything else is DISCHARGED. -/

/-- **`doty_theorem_3_1_expected_v4_final` (deliverable 2).**  The expected half on the SAME V4 bundle:
`E[T c₀ → StableDone] ≤ Tgood + δgood·sRec·(1 − (1/2 + η))⁻¹`, with the recovery contribution from the
on-J-good classifier + the leak budgets — NO classifier off the good window.  Re-based on the V4
bundle's `init` / `c₀`. -/
theorem doty_theorem_3_1_expected_v4_final {n C0 : ℕ}
    (ra : DotyResidualAtomsV4 (L := L) (K := K) n C0)
    (hc₀Reach : ReachableFrom L K ra.init ra.c₀)
    (Brecover : ℝ≥0∞)
    (βfinal : Config (AgentState L K) → ℝ≥0∞)
    (G : Config (AgentState L K) → Prop)
    (hDone : MeasurableSet (StableDone L K ra.init))
    (hDoneAbs : ∀ x ∈ StableDone L K ra.init,
      (NonuniformMajority L K).transitionKernel x (StableDone L K ra.init)ᶜ = 0)
    (Tgood sRecover : ℕ) (hsRecover : sRecover ≠ 0)
    (η δgood : ℝ≥0∞)
    (hOnGood : OffEventEndgame.OnGoodSlotClassifier (L := L) (K := K) n ra.init Brecover βfinal G)
    (hGoodBlock : ∀ b, b ∈ (StableDone L K ra.init)ᶜ →
      ((NonuniformMajority L K).transitionKernel ^ sRecover) b
        ({x | G x} ∩ (StableDone L K ra.init)ᶜ) ≤ (1 / 2 : ℝ≥0∞))
    (hLeak : ∀ b, b ∈ (StableDone L K ra.init)ᶜ →
      ((NonuniformMajority L K).transitionKernel ^ sRecover) b
        ({x | ¬ G x} ∩ (StableDone L K ra.init)ᶜ) ≤ η)
    (hfail : ((NonuniformMajority L K).transitionKernel ^ Tgood) ra.c₀
        (StableDone L K ra.init)ᶜ ≤ δgood) :
    expectedHitting (NonuniformMajority L K).transitionKernel ra.c₀
      (StableDone L K ra.init)
      ≤ (Tgood : ℝ≥0∞) + δgood * sRecover * (1 - ((1 / 2 : ℝ≥0∞) + η))⁻¹ :=
  OffEventEndgame.doty_theorem_3_1_expected_v4 (L := L) (K := K) (n := n)
    ra.init ra.c₀ hc₀Reach Brecover βfinal G hDone hDoneAbs Tgood sRecover hsRecover η δgood
    hOnGood hGoodBlock hLeak hfail

/-- **`doty_theorem_3_1_expected_v4_headline` (deliverable 2, headline form).**  The leaky `_v4_final`
bound lands the campaign headline `E[T] ≤ (21·C0 + 4·Cbad)·n·(L+1)` EXACTLY when the whp horizon fits
`Tgood ≤ 21·C0·n·(L+1)` and the leaky recovery tail fits `4·Cbad·n·(L+1)` (the leak `η` is `o(1)`,
paid from the whp bad mass).  Composes `_v4_final` with `OffEventEndgame.v4_headline_of_budget`. -/
theorem doty_theorem_3_1_expected_v4_headline {n C0 Cbad : ℕ}
    (ra : DotyResidualAtomsV4 (L := L) (K := K) n C0)
    (hc₀Reach : ReachableFrom L K ra.init ra.c₀)
    (Brecover : ℝ≥0∞)
    (βfinal : Config (AgentState L K) → ℝ≥0∞)
    (G : Config (AgentState L K) → Prop)
    (hDone : MeasurableSet (StableDone L K ra.init))
    (hDoneAbs : ∀ x ∈ StableDone L K ra.init,
      (NonuniformMajority L K).transitionKernel x (StableDone L K ra.init)ᶜ = 0)
    (Tgood sRecover : ℕ) (hsRecover : sRecover ≠ 0)
    (η δgood RHSrec : ℝ≥0∞)
    (hOnGood : OffEventEndgame.OnGoodSlotClassifier (L := L) (K := K) n ra.init Brecover βfinal G)
    (hGoodBlock : ∀ b, b ∈ (StableDone L K ra.init)ᶜ →
      ((NonuniformMajority L K).transitionKernel ^ sRecover) b
        ({x | G x} ∩ (StableDone L K ra.init)ᶜ) ≤ (1 / 2 : ℝ≥0∞))
    (hLeak : ∀ b, b ∈ (StableDone L K ra.init)ᶜ →
      ((NonuniformMajority L K).transitionKernel ^ sRecover) b
        ({x | ¬ G x} ∩ (StableDone L K ra.init)ᶜ) ≤ η)
    (hfail : ((NonuniformMajority L K).transitionKernel ^ Tgood) ra.c₀
        (StableDone L K ra.init)ᶜ ≤ δgood)
    (hTgood : (Tgood : ℝ≥0∞) ≤ ((21 * C0 * n * (L + 1) : ℕ) : ℝ≥0∞))
    (hrec : δgood * sRecover * (1 - ((1 / 2 : ℝ≥0∞) + η))⁻¹ ≤ RHSrec)
    (hrecbud : RHSrec ≤ ((4 * Cbad * n * (L + 1) : ℕ) : ℝ≥0∞)) :
    expectedHitting (NonuniformMajority L K).transitionKernel ra.c₀ (StableDone L K ra.init)
      ≤ (((21 * C0 + 4 * Cbad) * n * (L + 1) : ℕ) : ℝ≥0∞) :=
  OffEventEndgame.v4_headline_of_budget (n := n) (C0 := C0) (Cbad := Cbad)
    (doty_theorem_3_1_expected_v4_final ra hc₀Reach Brecover βfinal G hDone hDoneAbs
      Tgood sRecover hsRecover η δgood hOnGood hGoodBlock hLeak hfail)
    hTgood hrec hrecbud

/-- **`doty_theorem_3_1_expected_v4_numeral` (deliverable 2, numeral headline).**  The headline at the
LITERAL `C0 = 17`, `Cbad = 3`: `E[T] ≤ (21·17 + 4·3)·n·(L+1) = 369·n·(L+1)`. -/
theorem doty_theorem_3_1_expected_v4_numeral {n : ℕ}
    (ra : DotyResidualAtomsV4 (L := L) (K := K) n AtomsV2.C0_numeral)
    (hc₀Reach : ReachableFrom L K ra.init ra.c₀)
    (Brecover : ℝ≥0∞)
    (βfinal : Config (AgentState L K) → ℝ≥0∞)
    (G : Config (AgentState L K) → Prop)
    (hDone : MeasurableSet (StableDone L K ra.init))
    (hDoneAbs : ∀ x ∈ StableDone L K ra.init,
      (NonuniformMajority L K).transitionKernel x (StableDone L K ra.init)ᶜ = 0)
    (Tgood sRecover : ℕ) (hsRecover : sRecover ≠ 0)
    (η δgood RHSrec : ℝ≥0∞)
    (hOnGood : OffEventEndgame.OnGoodSlotClassifier (L := L) (K := K) n ra.init Brecover βfinal G)
    (hGoodBlock : ∀ b, b ∈ (StableDone L K ra.init)ᶜ →
      ((NonuniformMajority L K).transitionKernel ^ sRecover) b
        ({x | G x} ∩ (StableDone L K ra.init)ᶜ) ≤ (1 / 2 : ℝ≥0∞))
    (hLeak : ∀ b, b ∈ (StableDone L K ra.init)ᶜ →
      ((NonuniformMajority L K).transitionKernel ^ sRecover) b
        ({x | ¬ G x} ∩ (StableDone L K ra.init)ᶜ) ≤ η)
    (hfail : ((NonuniformMajority L K).transitionKernel ^ Tgood) ra.c₀
        (StableDone L K ra.init)ᶜ ≤ δgood)
    (hTgood : (Tgood : ℝ≥0∞) ≤ ((21 * AtomsV2.C0_numeral * n * (L + 1) : ℕ) : ℝ≥0∞))
    (hrec : δgood * sRecover * (1 - ((1 / 2 : ℝ≥0∞) + η))⁻¹ ≤ RHSrec)
    (hrecbud : RHSrec ≤ ((4 * AtomsV2.Cbad_numeral * n * (L + 1) : ℕ) : ℝ≥0∞)) :
    expectedHitting (NonuniformMajority L K).transitionKernel ra.c₀ (StableDone L K ra.init)
      ≤ (((21 * 17 + 4 * 3) * n * (L + 1) : ℕ) : ℝ≥0∞) :=
  doty_theorem_3_1_expected_v4_headline (C0 := AtomsV2.C0_numeral) (Cbad := AtomsV2.Cbad_numeral)
    ra hc₀Reach Brecover βfinal G hDone hDoneAbs Tgood sRecover hsRecover η δgood RHSrec
    hOnGood hGoodBlock hLeak hfail hTgood hrec hrecbud

end FinalAssemblyV4
end ExactMajority
