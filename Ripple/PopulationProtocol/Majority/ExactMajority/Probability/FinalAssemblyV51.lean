/-
# FinalAssemblyV51 — the V5.1 PATCH fixing the two V5-audit findings (F1 + F2).

This append-only file rebuilds the Doty Theorem 3.1 pair so that the V5 audit's two HIGH findings are
DISCHARGED on the proof term.  Everything else in V5 passed; only these two narrow defects remain.

**F1 — `DotyResidualAtomsV5` is not fresh.**  `WorkInputsSurvivalV5` nests the entire V2
`FinalAssemblyV2.WorkInputsHonest` as `base`, so an inhabitant of the V5 bundle still has to supply old
fields the V5 proof path never consumes — including the exact `hClosed6` closure V5 says it replaced,
and the dead all-Main / margin packages for the replaced slots.  The eight genuinely-dead `base` fields
(verified by grep — no proof use of any of them in V5):

  `hM₀`, `hext1`, `hpull1`, `hClosed6`, `hPhase6Post7`, `hE7`, `hPhase7Post8`, `hE8`.

FIX: `WorkInputsV51` is a TRULY-FRESH flat record carrying EXACTLY the live fields the V5 proof terms
consume — no nested `WorkInputsHonest`.  The carried slots 0/2/3/4/5/9/10 are restated AGAINST THE
FRESH FIELDS by calling the thin slot constructors DIRECTLY (`work0/2/3/9`, `phase4Convergence`,
`slot5Honest`, `phase10Convergence`) instead of routing through `dotyWorkHonest wi.base` (which demanded
the whole old record).  The replaced slots 1/6/7/8 call the same `WindowSurvival` survival builders as
V5.  Result: the eight dead fields are GONE from the residual surface.

**F2 — `hFloors` is a dead expected-side binder.**  V5's `onGood_recovery_cap` passes `hFloors` into
`ReachableLadder.reachable_hLadder`, whose binder is named `_hFloors` and is IGNORED (it pattern-matches
on the regime classification and returns the carried `LadderData`).  `ChainEndRecut.reachable_hLadder'`
is the landed de-deadweighted version (same extraction, no floor binder).  FIX: `onGood_recovery_cap_v51`
routes through `reachable_hLadder'`, and the expected theorem `doty_theorem_3_1_expected_v51` DROPS the
`hFloors` binder entirely.

## Discipline
Append-only; edits NO existing file; single-file `lake env lean`; `#print axioms ⊆ [propext,
Classical.choice, Quot.sound]`; no `sorry`/`admit`/`axiom`/`native_decide`.
-/
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.FinalAssemblyV5

namespace ExactMajority
namespace FinalAssemblyV51

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators NNReal
open ChainEndAssembly Phase10Drop

variable {L K : ℕ}

/-! ## Part 1 — `WorkInputsV51`: the TRULY-FRESH work inputs (no nested `WorkInputsHonest`).

Flat record carrying EXACTLY the live fields the V5 proof terms consume.  No `base`, hence none of the
eight dead V2 fields (`hM₀`, `hext1`, `hpull1`, `hClosed6`, `hPhase6Post7`, `hE7`, `hPhase7Post8`,
`hE8`).  Slots 1/6/7/8 on the `WindowSurvival` survival engine (escape budgets `hescW*` + `hescε*`
REPLACE the exact closures); slots 0/2/3/4/5/9/10 carried via the thin constructors directly. -/
structure WorkInputsV51 (n : ℕ) where
  -- ===== common scalars / regime data (consumed across many slots) =====
  /-- The dyadic minority sign (slots 7/8). -/
  σ : Sign
  /-- Common budget level `M₀`. -/
  M₀ : ℕ
  hn : 2 ≤ n
  hM1 : 1 ≤ M₀
  -- ===== slots 0/2/3/9 — carried finished instances =====
  work0 : PhaseConvergenceW (NonuniformMajority L K).transitionKernel
  work2 : PhaseConvergenceW (NonuniformMajority L K).transitionKernel
  work3 : PhaseConvergenceW (NonuniformMajority L K).transitionKernel
  work9 : PhaseConvergenceW (NonuniformMajority L K).transitionKernel
  -- ===== slot 1 — survival inputs (escape budget REPLACES `hClosed1`) =====
  /-- slot-1 partner-pool floor `P1 ≤ pullPos`. -/
  P1 : ℕ
  tWin1 : ℕ → ℕ
  /-- slot-1 per-step ESCAPE budget probability `η₁` (the at-risk counter tail). -/
  η1 : ℝ≥0∞
  /-- slot-1 escape budget `hescW1` — REPLACES `hClosed1`. -/
  hescW1 : ∀ x, HonestWindows.Phase1Honest (L := L) (K := K) n x →
    (NonuniformMajority L K).transitionKernel x
      {y | ¬ HonestWindows.Phase1Honest (L := L) (K := K) n y} ≤ η1
  hext1H : ∀ b : Config (AgentState L K), HonestWindows.Phase1Honest (L := L) (K := K) n b →
    1 ≤ (DrainThreading.extremePosSet L K).sum b.count
  hpull1H : ∀ b : Config (AgentState L K), HonestWindows.Phase1Honest (L := L) (K := K) n b →
    P1 ≤ (DrainThreading.pullPosSet L K).sum b.count
  hpt1 : ∀ m ∈ Finset.Icc 1 M₀, (FinalAssemblyV2.qHat P1 n m) ^ (tWin1 m) ≤
    (DrainCalibration.budgetNN M₀ n : ℝ≥0∞)
  escapeε1 : ℝ≥0
  hescε1 : (((∑ m ∈ Finset.Icc 1 M₀, tWin1 m) : ℕ) : ℝ≥0∞) * η1 ≤ (escapeε1 : ℝ≥0∞)
  -- ===== slot 4 — Phase-4 epidemic (carried scalar inputs) =====
  s4 : ℝ
  hs4 : 0 < s4
  t4 : ℕ
  ε4 : ℝ≥0
  hε4 : ENNReal.ofReal
          (1 - (((n - 1 : ℕ) : ℝ) / ((n : ℝ) * ((n : ℝ) - 1))) * (1 - Real.exp (-s4))) ^ t4 *
          ENNReal.ofReal (Real.exp (s4 * ((n : ℝ) - 1))) / 1
        ≤ (ε4 : ℝ≥0∞)
  -- ===== slot 5 — HONEST levels drain + concentration (closure CARRIED — the honest exception) =====
  i5 : Fin (L + 1)
  K₀ : ℕ
  /-- slot-5 biased-Main floor `P5 ≤ usefulMains` (Theorem 6.2 biased structure). -/
  P5 : ℕ
  tWin5 : ℕ → ℕ
  hClosed5 : OneSidedCancel.InvClosed (NonuniformMajority L K).transitionKernel
    (fun c => ReserveSampling.Phase5AllWin (L := L) (K := K) n c)
  hmain5 : ∀ b : Config (AgentState L K), ReserveSampling.Phase5AllWin (L := L) (K := K) n b →
    P5 ≤ (Phase5Convergence.usefulMains (L := L) (K := K)).sum b.count
  hpt5 : ∀ m ∈ Finset.Icc 1 M₀, (FinalAssemblyV2.qHat P5 n m) ^ (tWin5 m) ≤
    (DrainCalibration.budgetNN M₀ n : ℝ≥0∞)
  εConc : ℝ≥0
  hConc : ∀ c₀, ReserveSampling.Phase5AllWin (L := L) (K := K) n c₀ →
    ReserveSampling.unsampledReserveU (L := L) (K := K) c₀ ≤ M₀ →
    ((NonuniformMajority L K).transitionKernel ^ (∑ m ∈ Finset.Icc 1 M₀, tWin5 m)) c₀
      {c | ¬ Phase5Convergence.sampledFloor (L := L) (K := K) i5 K₀ c} ≤ (εConc : ℝ≥0∞)
  -- ===== slot 6 — generic survival inputs (escape budget REPLACES `hClosed6`) =====
  /-- The Phase-6 band level `l`. -/
  l : ℕ
  q6 : ℕ → ℝ≥0∞
  tWin6 : ℕ → ℕ
  hdrop6 : ∀ m, ∀ b : Config (AgentState L K),
    Phase6Convergence.Phase6Win (L := L) (K := K) n b →
    Phase6Convergence.highMass (L := L) (K := K) l b = m →
    (NonuniformMajority L K).transitionKernel b
      (OneSidedCancel.potBelow
        (fun c => Phase6Convergence.highMass (L := L) (K := K) l c) m)ᶜ ≤ q6 m
  hpt6 : ∀ m ∈ Finset.Icc 1 M₀, (q6 m) ^ (tWin6 m) ≤ (DrainCalibration.budgetNN M₀ n : ℝ≥0∞)
  η6 : ℝ≥0∞
  hescW6 : ∀ x, Phase6Convergence.Phase6Win (L := L) (K := K) n x →
    (NonuniformMajority L K).transitionKernel x
      {y | ¬ Phase6Convergence.Phase6Win (L := L) (K := K) n y} ≤ η6
  /-- slot-6 per-level rate floor `1 ≤ q6 0` (the survival engine's `m = 0` filler). -/
  hq6zero : (1 : ℝ≥0∞) ≤ q6 0
  escapeε6 : ℝ≥0
  hescε6 : (((∑ m ∈ Finset.Icc 1 M₀, tWin6 m) : ℕ) : ℝ≥0∞) * η6 ≤ (escapeε6 : ℝ≥0∞)
  -- ===== slot 7 — survival inputs (escape budget REPLACES `hClosed7`) =====
  /-- The Phase-7 eliminator-margin count `E7` (Lemma 7.4). -/
  E7 : ℕ
  tWin7 : ℕ → ℕ
  η7 : ℝ≥0∞
  hescW7 : ∀ x, HonestWindows.Phase7Honest (L := L) (K := K) n x →
    (NonuniformMajority L K).transitionKernel x
      {y | ¬ HonestWindows.Phase7Honest (L := L) (K := K) n y} ≤ η7
  hwit7 : ∀ b : Config (AgentState L K), HonestWindows.Phase7Honest (L := L) (K := K) n b →
    Phase7Convergence.classMassN σ b ≥ 1 →
    ∃ i j : Fin (L + 1), i.val + 1 = j.val ∧
      1 ≤ (Phase7Convergence.minorityAt7 (L := L) (K := K) σ j).sum b.count ∧
      E7 ≤ (Phase7Convergence.elimGap1 (L := L) (K := K) σ i).sum b.count
  hpt7 : ∀ m ∈ Finset.Icc 1 M₀, (FinalAssemblyV2.qHat E7 n m) ^ (tWin7 m) ≤
    (DrainCalibration.budgetNN M₀ n : ℝ≥0∞)
  escapeε7 : ℝ≥0
  hescε7 : (((∑ m ∈ Finset.Icc 1 M₀, tWin7 m) : ℕ) : ℝ≥0∞) * η7 ≤ (escapeε7 : ℝ≥0∞)
  -- ===== slot 8 — survival inputs (escape budget REPLACES `hClosed8`) =====
  /-- The Phase-8 above-level eliminator-margin count `E8` (Lemma 7.6). -/
  E8 : ℕ
  tWin8 : ℕ → ℕ
  η8 : ℝ≥0∞
  hescW8 : ∀ x, HonestWindows.Phase8Honest (L := L) (K := K) n x →
    (NonuniformMajority L K).transitionKernel x
      {y | ¬ HonestWindows.Phase8Honest (L := L) (K := K) n y} ≤ η8
  hwit8 : ∀ b : Config (AgentState L K), HonestWindows.Phase8Honest (L := L) (K := K) n b →
    Phase7Convergence.minorityU σ b ≥ 1 →
    ∃ i : Fin (L + 1),
      1 ≤ (Phase8Convergence.minorityAt (L := L) (K := K) σ i).sum b.count ∧
      E8 ≤ (Phase8Convergence.elimAbove (L := L) (K := K) σ i).sum b.count
  hpt8 : ∀ m ∈ Finset.Icc 1 M₀, (FinalAssemblyV2.qHat E8 n m) ^ (tWin8 m) ≤
    (DrainCalibration.budgetNN M₀ n : ℝ≥0∞)
  escapeε8 : ℝ≥0
  hescε8 : (((∑ m ∈ Finset.Icc 1 M₀, tWin8 m) : ℕ) : ℝ≥0∞) * η8 ≤ (escapeε8 : ℝ≥0∞)
  -- ===== slot 10 — Phase-10 block-geometric (carried scalar inputs) =====
  s10 : ℕ
  hs10 : 0 < s10
  hsB10 : (3 * (((n ^ 2 : ℕ) : ℝ≥0∞) * ENNReal.ofReal (1 + 2 * Real.log n))) * 2
    ≤ (s10 : ℝ≥0∞)
  k10 : ℕ

/-- **The V5.1 SURVIVAL work family** `Fin 11 → PhaseConvergenceW`, built from the FRESH
`WorkInputsV51`.  Slots 1/7/8 on `WindowSurvival.slot{1,7,8}Survival`, slot 6 on the generic
`WindowSurvival.slotSurvival`; slots 0/2/3/4/5/9/10 restated AGAINST THE FRESH FIELDS via the thin
constructors directly (no `dotyWorkHonest wi.base`, hence no dead V2 baggage). -/
noncomputable def dotyWorkSurvivalV51 {n : ℕ} (wi : WorkInputsV51 (L := L) (K := K) n) :
    Fin 11 → PhaseConvergenceW (NonuniformMajority L K).transitionKernel :=
  fun k =>
    match k with
    | ⟨0, _⟩ => wi.work0
    | ⟨1, _⟩ => WindowSurvival.slot1Survival (L := L) (Kp := K) wi.P1 wi.M₀ wi.hn
        wi.hM1 wi.η1 wi.hescW1 wi.hext1H wi.hpull1H wi.tWin1 wi.hpt1 wi.escapeε1 wi.hescε1
    | ⟨2, _⟩ => wi.work2
    | ⟨3, _⟩ => wi.work3
    | ⟨4, _⟩ =>
        Phase4Convergence.phase4Convergence (L := L) (K := K) n wi.hn wi.s4 wi.hs4 wi.t4 wi.ε4 wi.hε4
    | ⟨5, _⟩ =>
        FinalAssemblyV2.slot5Honest wi.i5 wi.K₀ wi.M₀ wi.P5 wi.hClosed5 wi.hn wi.hM1 wi.hmain5
          wi.tWin5 wi.hpt5 wi.εConc wi.hConc
    | ⟨6, _⟩ => WindowSurvival.slotSurvival (NonuniformMajority L K).transitionKernel
        (fun c => Phase6Convergence.Phase6Win (L := L) (K := K) n c)
        (fun c => Phase6Convergence.highMass (L := L) (K := K) wi.l c)
        (Phase6Convergence.potNonincrOn_highMass (L := L) (K := K) wi.l n)
        wi.q6 wi.hq6zero wi.hdrop6 wi.η6 wi.hescW6
        wi.tWin6 wi.M₀ (Real.toNNReal (1 / (n : ℝ) ^ 2)) wi.escapeε6
        (DrainCalibration.rect_sum_le_phase_budget wi.hn wi.hM1 wi.q6 wi.tWin6
          wi.hpt6 |>.trans_eq (by rw [show ((Real.toNNReal (1 / (n : ℝ) ^ 2) : ℝ≥0) : ℝ≥0∞)
            = ENNReal.ofReal (1 / (n : ℝ) ^ 2) from by rw [ENNReal.ofReal]]))
        wi.hescε6
    | ⟨7, _⟩ => WindowSurvival.slot7Survival (L := L) (Kp := K) wi.σ wi.E7 wi.M₀
        wi.hn wi.hM1 wi.η7 wi.hescW7 wi.hwit7 wi.tWin7 wi.hpt7 wi.escapeε7 wi.hescε7
    | ⟨8, _⟩ => WindowSurvival.slot8Survival (L := L) (Kp := K) wi.σ wi.E8 wi.M₀
        wi.hn wi.hM1 wi.η8 wi.hescW8 wi.hwit8 wi.tWin8 wi.hpt8 wi.escapeε8 wi.hescε8
    | ⟨9, _⟩ => wi.work9
    | ⟨10, _⟩ =>
        Phase10Drop.phase10Convergence (L := L) (K := K) n wi.hn wi.s10 wi.hs10 wi.hsB10 wi.k10
    | ⟨m + 11, h⟩ => absurd h (by omega)

/-! ## Part 2 — `DotyResidualAtomsV51`: the FRESH residual bundle.

Identical seam / scalar / start-sign / off-event surface to `DotyResidualAtomsV5`, but the work record
is the FRESH `WorkInputsV51` (no nested `WorkInputsHonest`).  Every field is consumed by
`doty_theorem_3_1_whp_v51` (work family + seam half + start/sign atoms) or by
`doty_theorem_3_1_expected_v51` (the off-event residuals). -/
structure DotyResidualAtomsV51 (n C0 : ℕ) where
  /-- The FRESH SURVIVAL work record — no nested V2 baggage. -/
  wi : WorkInputsV51 (L := L) (K := K) n
  -- ===== the seam half, carried over the SURVIVAL family `dotyWorkSurvivalV51 wi` =====
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
      (dotyWorkSurvivalV51 wi ⟨k.val, by omega⟩).Post c →
      SeamEpidemics.allPhaseGe (L := L) (K := K) (seamP k) n c
  hSeedStep : ∀ (k : Fin 10) (c : Config (AgentState L K)),
      (dotyWorkSurvivalV51 wi ⟨k.val, by omega⟩).Post c →
      ((NonuniformMajority L K).transitionKernel ^ 1) c
          {c' | ¬ SeamEpidemics.advTriggered (L := L) (K := K) (seamP k + 1) c'} = 0
  hWindowToWorkPre : ∀ (k : Fin 10) (c : Config (AgentState L K)),
      SeamEpidemics.allPhaseEq (L := L) (K := K) (seamP k + 1) n c →
      (dotyWorkSurvivalV51 wi ⟨k.val + 1, by omega⟩).Pre c
  -- ===== budget / config scalars =====
  Cphase : Fin 21 → ℕ
  δ : Fin 21 → ℝ≥0
  c₀ : Config (AgentState L K)
  init : Config (AgentState L K)
  hC0 : ∀ i, Cphase i ≤ C0
  hδ : ∀ i, (δ i : ℝ≥0∞) ≤ (1 / (n : ℝ≥0∞) ^ 2)
  -- ===== start / sign honesty atoms (producing hx₀ / h_post) =====
  hStart : RoleSplitConcentration.Phase0Initial (L := L) (K := K) n c₀
  hWork0PreOfStart : RoleSplitConcentration.Phase0Initial (L := L) (K := K) n c₀ →
    (wi.work0).Pre c₀
  hPhase10Sign : AtomsV2.Phase10SignMatch (L := L) (K := K) init

/-! ## Part 3 — the V5.1 assembly and its 21-instance family. -/

/-- **The V5.1 SURVIVAL assembly.**  A `DotyAssembly'` whose `work` is `dotyWorkSurvivalV51 wi`. -/
noncomputable def toAssembly'V51 {n C0 : ℕ} (ra : DotyResidualAtomsV51 (L := L) (K := K) n C0) :
    SeedTrigWiring.DotyAssembly' (L := L) (K := K) n where
  work := dotyWorkSurvivalV51 ra.wi
  seamP := ra.seamP
  seamT := ra.seamT
  εepidemic := ra.εepidemic
  εovershoot := ra.εovershoot
  hDrift := ra.hDrift
  hNoOvershoot := ra.hNoOvershoot
  hWorkPostToWindow := ra.hWorkPostToWindow
  hSeedStep := ra.hSeedStep
  hWindowToWorkPre := ra.hWindowToWorkPre

/-- The wired 21-instance family of the V5.1 survival assembly. -/
noncomputable def phases'V51 {n C0 : ℕ} (ra : DotyResidualAtomsV51 (L := L) (K := K) n C0) :
    Fin 21 → PhaseConvergenceW (NonuniformMajority L K).transitionKernel :=
  SeedTrigWiring.dotyPhases' (toAssembly'V51 ra)

theorem phases'V51_eq {n C0 : ℕ} (ra : DotyResidualAtomsV51 (L := L) (K := K) n C0) :
    phases'V51 ra = SeedTrigWiring.dotyPhases' (toAssembly'V51 ra) := rfl

/-! ## Part 3' — `hx₀` / `h_post` PRODUCED in-bundle (on the fresh family).

Slot 0 of `dotyWorkSurvivalV51 wi` is the carried `wi.work0` (the fresh family's slot-0 arm is literally
`wi.work0`), whose `Pre` is `wi.work0.Pre` BY `rfl`; slot 20 (`⟨20⟩`) is `phase10Convergence`, whose
`Post` is `Phase10Post` BY `rfl`.  No `dotyWorkHonest` detour, so the pins are direct. -/

/-- **Slot-0 `Pre` pin (fresh family).**  `(phases'V51 ra ⟨0⟩).Pre c = wi.work0.Pre c`. -/
theorem slot0_pre_pin_v51 {n C0 : ℕ} (ra : DotyResidualAtomsV51 (L := L) (K := K) n C0)
    (c : Config (AgentState L K)) :
    (phases'V51 ra ⟨0, by omega⟩).Pre c = (ra.wi.work0).Pre c := by
  unfold phases'V51 toAssembly'V51
  rw [SeedTrigWiring.dotyPhases'_even _ _ (by rfl)]
  show (dotyWorkSurvivalV51 ra.wi (ConcreteAssembly.workIdx ⟨0, by omega⟩)).Pre c
       = (ra.wi.work0).Pre c
  rw [show ConcreteAssembly.workIdx ⟨0, by omega⟩ = (⟨0, by omega⟩ : Fin 11) from by
    apply Fin.ext; norm_num [ConcreteAssembly.workIdx]]
  rfl

/-- **Slot-20 `Post` pin (fresh family).**  `(phases'V51 ra ⟨20⟩).Post c → Phase10Post c`. -/
theorem slot20_post_pin_v51 {n C0 : ℕ} (ra : DotyResidualAtomsV51 (L := L) (K := K) n C0)
    {c : Config (AgentState L K)}
    (hPost : (phases'V51 ra ⟨21 - 1, by omega⟩).Post c) :
    Phase10Drop.Phase10Post (L := L) (K := K) c := by
  have heq : (phases'V51 ra ⟨21 - 1, by omega⟩).Post c
      ↔ Phase10Drop.Phase10Post (L := L) (K := K) c := by
    unfold phases'V51 toAssembly'V51
    rw [SeedTrigWiring.dotyPhases'_even _ _ (by rfl)]
    show (dotyWorkSurvivalV51 ra.wi
            (ConcreteAssembly.workIdx ⟨21 - 1, by omega⟩)).Post c
         ↔ Phase10Drop.Phase10Post (L := L) (K := K) c
    rw [show ConcreteAssembly.workIdx ⟨21 - 1, by omega⟩ = (⟨10, by omega⟩ : Fin 11) from by
      apply Fin.ext; norm_num [ConcreteAssembly.workIdx]]
    show (Phase10Drop.phase10Convergence (L := L) (K := K) n ra.wi.hn ra.wi.s10 ra.wi.hs10
            ra.wi.hsB10 ra.wi.k10).Post c ↔ Phase10Drop.Phase10Post (L := L) (K := K) c
    exact Iff.rfl
  exact heq.mp hPost

attribute [local irreducible] dotyWorkSurvivalV51

/-- **`hx₀` PRODUCED from the honest start.**  The free `hx₀` binder is GONE. -/
theorem hx₀_of_start_v51 {n C0 : ℕ} (ra : DotyResidualAtomsV51 (L := L) (K := K) n C0) :
    (phases'V51 ra ⟨0, by omega⟩).Pre ra.c₀ := by
  rw [slot0_pre_pin_v51 ra ra.c₀]
  exact ra.hWork0PreOfStart ra.hStart

/-- **`h_post` PRODUCED from the conserved gap-sign match.**  The free `h_post` binder is GONE. -/
theorem h_post_of_sign_v51 {n C0 : ℕ} (ra : DotyResidualAtomsV51 (L := L) (K := K) n C0) :
    ∀ c, (phases'V51 ra ⟨21 - 1, by omega⟩).Post c →
      majorityStableEndpoint (L := L) (K := K) ra.init c :=
  fun _c hPost => AtomsV2.postOfSign ra.hPhase10Sign (slot20_post_pin_v51 ra hPost)

/-! ## Part 4 (deliverable 1) — `doty_theorem_3_1_whp_v51`: the whp half on the FRESH family. -/

/-- **`doty_theorem_3_1_whp_v51` (deliverable 1).**  The whp half on the FRESH survival work family
`dotyWorkSurvivalV51 wi`: failure `≤ 21/n²` within `T ≤ 21·C0·n·(L+1)` (and the `clog` form), over
`DotyRegime n L K` + `DotyResidualAtomsV51`.  No nested V2 baggage; slots 1/6/7/8 consume the survival
ESCAPE BUDGETS; the bound is PRODUCED (no `hcompFail`); `hx₀` / `h_post` produced in-bundle. -/
theorem doty_theorem_3_1_whp_v51 {n L K C0 : ℕ}
    (hReg : PaperRegime.DotyRegime n L K)
    (ra : DotyResidualAtomsV51 (L := L) (K := K) n C0)
    (T : ℕ) (hT : T = ∑ i, (phases'V51 ra i).t)
    (ht : ∀ i, (phases'V51 ra i).t ≤ ra.Cphase i * n * (L + 1))
    (hε : ∀ i, ((phases'V51 ra i).ε : ℝ≥0∞) ≤ (ra.δ i : ℝ≥0∞)) :
    ((NonuniformMajority L K).transitionKernel ^ T) ra.c₀
        {c | ¬ majorityStableEndpoint (L := L) (K := K) ra.init c}
      ≤ (21 : ℝ≥0∞) / (n : ℝ≥0∞) ^ 2
    ∧ T ≤ 21 * C0 * n * (L + 1)
    ∧ T ≤ 21 * C0 * n * (Nat.clog 2 n + 1) := by
  obtain ⟨herr, htime⟩ :=
    FinalAssemblyV2.whp_of_asm' (C0 := C0) ra.init ra.c₀ (toAssembly'V51 ra) ra.Cphase ra.δ T hT ht hε
      (hx₀_of_start_v51 ra) (h_post_of_sign_v51 ra) ra.hC0 ra.hδ
  refine ⟨herr, htime, ?_⟩
  rw [← hReg.hLlog]; exact htime

/-- **`doty_theorem_3_1_whp_numeral_v51` (deliverable 1, numeral).**  At the LITERAL `C0 = 17`. -/
theorem doty_theorem_3_1_whp_numeral_v51 {n L K : ℕ}
    (hReg : PaperRegime.DotyRegime n L K)
    (ra : DotyResidualAtomsV51 (L := L) (K := K) n AtomsV2.C0_numeral)
    (T : ℕ) (hT : T = ∑ i, (phases'V51 ra i).t)
    (ht : ∀ i, (phases'V51 ra i).t ≤ ra.Cphase i * n * (L + 1))
    (hε : ∀ i, ((phases'V51 ra i).ε : ℝ≥0∞) ≤ (ra.δ i : ℝ≥0∞)) :
    ((NonuniformMajority L K).transitionKernel ^ T) ra.c₀
        {c | ¬ majorityStableEndpoint (L := L) (K := K) ra.init c}
      ≤ (21 : ℝ≥0∞) / (n : ℝ≥0∞) ^ 2
    ∧ T ≤ 21 * AtomsV2.C0_numeral * n * (L + 1)
    ∧ T ≤ 21 * AtomsV2.C0_numeral * n * (Nat.clog 2 n + 1) :=
  doty_theorem_3_1_whp_v51 (C0 := AtomsV2.C0_numeral) hReg ra T hT ht hε

/-! ## Part 5 (deliverable 2) — `doty_theorem_3_1_expected_v51`: the off-event half (F2 fix).

The on-good recovery cap routes through `ChainEndRecut.reachable_hLadder'` (the de-deadweighted ladder
skeleton, NO floor binder) instead of `ReachableLadder.reachable_hLadder` (which IGNORED its `_hFloors`
argument).  Consequently the `hFloors` binder is DROPPED from `onGood_recovery_cap_v51`, from the
occupation lemma, and from the expected theorem. -/

section ExpectedV51

variable {n C0 : ℕ}

/-- **The good-recovery cap PRODUCED from `hOnGood`, no `hFloors`** (F2 fix).  Identical to V5's
`onGood_recovery_cap` but the ladder is extracted via `ChainEndRecut.reachable_hLadder'`, which takes NO
floor argument (the floor data already lives inside the regime classification's carried `LadderData`).
`hOnGood` is genuinely CONSUMED; `hFloors` is GONE. -/
theorem onGood_recovery_cap_v51 (init b : Config (AgentState L K)) (Brecover : ℝ≥0∞)
    (βfinal : Config (AgentState L K) → ℝ≥0∞)
    (G : Config (AgentState L K) → Prop)
    (hDone : MeasurableSet (StableDone L K init))
    (hDoneAbs : ∀ x ∈ StableDone L K init,
      (NonuniformMajority L K).transitionKernel x (StableDone L K init)ᶜ = 0)
    (hOnGood : OffEventEndgame.OnGoodSlotClassifier (L := L) (K := K) n init Brecover βfinal G)
    (hbReach : ReachableFrom L K init b) (hbBad : b ∈ (StableDone L K init)ᶜ) (hbG : G b) :
    expectedHitting (NonuniformMajority L K).transitionKernel b (StableDone L K init) ≤ Brecover := by
  have hBranch : ChainEndBranch (L := L) (K := K) n init b Brecover (βfinal b) :=
    AtomsV2.branchOfSlotRegime init b Brecover (βfinal b) (hOnGood b hbReach hbBad hbG)
  have hRegime : ReachablePhaseRegimeClassification L K n init b Brecover :=
    regimeClassification_of_chainEndBranch (L := L) (K := K) (n := n) init b
      Brecover (βfinal b) hDone hDoneAbs hBranch
  have hLad : LadderData L K init b Brecover :=
    ChainEndRecut.reachable_hLadder' (L := L) (K := K) (n := n) init b hbReach hbBad hRegime
  exact (recoveryClass_of_ladderData (n := n) init b Brecover hDone hDoneAbs
    hLad).expectedHitting_le

/-- **The good-recovery OCCUPATION bound PRODUCED from `hOnGood`, no `hFloors`** (F2 fix).  With
`Mid := {b | ReachableFrom init b ∧ G b}`, the per-state recovery caps (`onGood_recovery_cap_v51`) make
`expectedHitting K y Done ≤ Brecover` for every `y ∈ Mid`, so `ExpectedHitting.occupation_mid_le` bounds
the good-band occupation `∑' t (K^t) c₀ ({Mid}∩Doneᶜ) ≤ Brecover`. -/
theorem onGood_occupation_le_v51 (init c₀ : Config (AgentState L K)) (Brecover : ℝ≥0∞)
    (βfinal : Config (AgentState L K) → ℝ≥0∞)
    (G : Config (AgentState L K) → Prop)
    (hDone : MeasurableSet (StableDone L K init))
    (hDoneAbs : ∀ x ∈ StableDone L K init,
      (NonuniformMajority L K).transitionKernel x (StableDone L K init)ᶜ = 0)
    (hOnGood : OffEventEndgame.OnGoodSlotClassifier (L := L) (K := K) n init Brecover βfinal G) :
    ∑' t : ℕ, ((NonuniformMajority L K).transitionKernel ^ t) c₀
        ({b | ReachableFrom L K init b ∧ G b} ∩ (StableDone L K init)ᶜ) ≤ Brecover := by
  classical
  set ker := (NonuniformMajority L K).transitionKernel with hker
  set Mid : Set (Config (AgentState L K)) := {b | ReachableFrom L K init b ∧ G b} with hMid
  have hMidMeas : MeasurableSet Mid := DiscreteMeasurableSpace.forall_measurableSet _
  have hB : ∀ y ∈ Mid, expectedHitting ker y (StableDone L K init) ≤ Brecover := by
    intro y hy
    obtain ⟨hyReach, hyG⟩ := hy
    by_cases hyDone : y ∈ (StableDone L K init)ᶜ
    · exact onGood_recovery_cap_v51 init y Brecover βfinal G hDone hDoneAbs hOnGood
        hyReach hyDone hyG
    · have hyIn : y ∈ StableDone L K init := by
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

/-- **The leaky split with a PRODUCED good occupation, no `hFloors`** (F2 fix, capstone).  Splitting
`Doneᶜ` over `Mid`/`Midᶜ` gives `E[T c₀ → Done] ≤ Brecover + Bleak`, the off-good mass charged to the
leak budget `Bleak`. -/
theorem expected_le_of_onGood_occupation_v51 (init c₀ : Config (AgentState L K))
    (Brecover Bleak : ℝ≥0∞)
    (βfinal : Config (AgentState L K) → ℝ≥0∞)
    (G : Config (AgentState L K) → Prop)
    (hDone : MeasurableSet (StableDone L K init))
    (hDoneAbs : ∀ x ∈ StableDone L K init,
      (NonuniformMajority L K).transitionKernel x (StableDone L K init)ᶜ = 0)
    (hOnGood : OffEventEndgame.OnGoodSlotClassifier (L := L) (K := K) n init Brecover βfinal G)
    (hLeak : ∑' t : ℕ, ((NonuniformMajority L K).transitionKernel ^ t) c₀
        ({b | ¬ (ReachableFrom L K init b ∧ G b)} ∩ (StableDone L K init)ᶜ) ≤ Bleak) :
    expectedHitting (NonuniformMajority L K).transitionKernel c₀ (StableDone L K init)
      ≤ Brecover + Bleak := by
  classical
  set ker := (NonuniformMajority L K).transitionKernel with hker
  set Done : Set (Config (AgentState L K)) := StableDone L K init with hDoneSet
  set Mid : Set (Config (AgentState L K)) := {b | ReachableFrom L K init b ∧ G b} with hMid
  have hgood := onGood_occupation_le_v51 (n := n) init c₀ Brecover βfinal G hDone hDoneAbs hOnGood
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

end ExpectedV51

/-- **`doty_theorem_3_1_expected_v51` (deliverable 2 — REBUILT on the FRESH bundle, no `hFloors`).**

`E[T c₀ → StableDone] ≤ Brecover + Bleak`, on the FRESH V5.1 bundle (`ra.init`/`ra.c₀`):

* `hOnGood` is CONSUMED — its good-slice recovery caps PRODUCE the good occupation
  (`onGood_occupation_le_v51` → `onGood_recovery_cap_v51` → `ChainEndRecut.reachable_hLadder'`, the
  de-deadweighted ladder skeleton with NO floor binder — F2 fixed: `hFloors` is GONE);
* `hfail` (the off-good horizon) is PRODUCED from `doty_theorem_3_1_whp_v51` on the SAME `ra` (WIRED);
* the slot-5 entry consumption runs through `FinalAssemblyV5.slot5_floor_via_phase3_squaring`
  (`confine3_served_by_phase3_squaring`), landing the slot-5 floor — the phase-3 chain ON the proof path;
* the leak budget `Bleak` (the off-good occupation) is the genuine carried residual.

The `hFloors` binder of V5's expected theorem is DROPPED (F2). -/
theorem doty_theorem_3_1_expected_v51 {n L K C0 : ℕ}
    (hReg : PaperRegime.DotyRegime n L K)
    (ra : DotyResidualAtomsV51 (L := L) (K := K) n C0)
    (Brecover Bleak : ℝ≥0∞)
    (βfinal : Config (AgentState L K) → ℝ≥0∞)
    (G : Config (AgentState L K) → Prop)
    (hDone : MeasurableSet (StableDone L K ra.init))
    (hDoneAbs : ∀ x ∈ StableDone L K ra.init,
      (NonuniformMajority L K).transitionKernel x (StableDone L K ra.init)ᶜ = 0)
    -- (a) the on-good classifier — CONSUMED into the good occupation (no `hFloors`).
    (hOnGood : OffEventEndgame.OnGoodSlotClassifier (L := L) (K := K) n ra.init Brecover βfinal G)
    (hLeak : ∑' t : ℕ, ((NonuniformMajority L K).transitionKernel ^ t) ra.c₀
        ({b | ¬ (ReachableFrom L K ra.init b ∧ G b)} ∩ (StableDone L K ra.init)ᶜ) ≤ Bleak)
    -- (b) the V5.1 whp horizon inputs — the same bundle's whp output is WIRED as `hfail`.
    (T : ℕ) (hT : T = ∑ i, (phases'V51 ra i).t)
    (ht : ∀ i, (phases'V51 ra i).t ≤ ra.Cphase i * n * (L + 1))
    (hεw : ∀ i, ((phases'V51 ra i).ε : ℝ≥0∞) ≤ (ra.δ i : ℝ≥0∞))
    -- (c) the phase-3 squaring slot-5 entry inputs.
    (c5 : Config (AgentState L K))
    (hPhase5 : ReserveSampling.Phase5AllWin (L := L) (K := K) n c5)
    (hMainFloor : (n : ℝ) / 3 ≤ (RoleSplitConcentration.mainCount (L := L) (K := K) c5 : ℝ))
    (hConf : MainExponentConfinement.MainProfileConfinedToUseful (L := L) (K := K) c5)
    (hP5 : (ra.wi.P5 : ℝ) ≤ (23 : ℝ) * (n : ℝ) / 75) :
    expectedHitting (NonuniformMajority L K).transitionKernel ra.c₀ (StableDone L K ra.init)
      ≤ Brecover + Bleak
    ∧ ra.wi.P5 ≤ (Phase5Convergence.usefulMains (L := L) (K := K)).sum c5.count
    ∧ (((NonuniformMajority L K).transitionKernel ^ T) ra.c₀
          {c | ¬ majorityStableEndpoint (L := L) (K := K) ra.init c}
        ≤ (21 : ℝ≥0∞) / (n : ℝ≥0∞) ^ 2
      ∧ T ≤ 21 * C0 * n * (L + 1)) := by
  refine ⟨expected_le_of_onGood_occupation_v51 (n := n) ra.init ra.c₀ Brecover Bleak βfinal G
    hDone hDoneAbs hOnGood hLeak, ?_, ?_⟩
  · exact FinalAssemblyV5.slot5_floor_via_phase3_squaring (n := n) ra.wi.P5 hPhase5 hMainFloor hConf hP5
  · obtain ⟨herr, htime, _⟩ := doty_theorem_3_1_whp_v51 (C0 := C0) hReg ra T hT ht hεw
    exact ⟨herr, htime⟩

/-! ## Part 5' — the headline-shaped + numeral corollaries on V5.1. -/

/-- **`doty_theorem_3_1_expected_v51_headline` (deliverable 2, headline form).**  The V5.1 leaky bound
lands the campaign headline `E[T] ≤ (21·C0 + 4·Cbad)·n·(L+1)` when `Brecover ≤ 21·C0·n·(L+1)` and
`Bleak ≤ 4·Cbad·n·(L+1)`.  No `hFloors` binder (F2 fixed). -/
theorem doty_theorem_3_1_expected_v51_headline {n L K C0 Cbad : ℕ}
    (hReg : PaperRegime.DotyRegime n L K)
    (ra : DotyResidualAtomsV51 (L := L) (K := K) n C0)
    (Brecover Bleak : ℝ≥0∞)
    (βfinal : Config (AgentState L K) → ℝ≥0∞)
    (G : Config (AgentState L K) → Prop)
    (hDone : MeasurableSet (StableDone L K ra.init))
    (hDoneAbs : ∀ x ∈ StableDone L K ra.init,
      (NonuniformMajority L K).transitionKernel x (StableDone L K ra.init)ᶜ = 0)
    (hOnGood : OffEventEndgame.OnGoodSlotClassifier (L := L) (K := K) n ra.init Brecover βfinal G)
    (hLeak : ∑' t : ℕ, ((NonuniformMajority L K).transitionKernel ^ t) ra.c₀
        ({b | ¬ (ReachableFrom L K ra.init b ∧ G b)} ∩ (StableDone L K ra.init)ᶜ) ≤ Bleak)
    (T : ℕ) (hT : T = ∑ i, (phases'V51 ra i).t)
    (ht : ∀ i, (phases'V51 ra i).t ≤ ra.Cphase i * n * (L + 1))
    (hεw : ∀ i, ((phases'V51 ra i).ε : ℝ≥0∞) ≤ (ra.δ i : ℝ≥0∞))
    (c5 : Config (AgentState L K))
    (hPhase5 : ReserveSampling.Phase5AllWin (L := L) (K := K) n c5)
    (hMainFloor : (n : ℝ) / 3 ≤ (RoleSplitConcentration.mainCount (L := L) (K := K) c5 : ℝ))
    (hConf : MainExponentConfinement.MainProfileConfinedToUseful (L := L) (K := K) c5)
    (hP5 : (ra.wi.P5 : ℝ) ≤ (23 : ℝ) * (n : ℝ) / 75)
    (hBrec : Brecover ≤ ((21 * C0 * n * (L + 1) : ℕ) : ℝ≥0∞))
    (hBleak : Bleak ≤ ((4 * Cbad * n * (L + 1) : ℕ) : ℝ≥0∞)) :
    expectedHitting (NonuniformMajority L K).transitionKernel ra.c₀ (StableDone L K ra.init)
      ≤ (((21 * C0 + 4 * Cbad) * n * (L + 1) : ℕ) : ℝ≥0∞) := by
  have hmain := (doty_theorem_3_1_expected_v51 (C0 := C0) hReg ra Brecover Bleak βfinal G hDone hDoneAbs
    hOnGood hLeak T hT ht hεw c5 hPhase5 hMainFloor hConf hP5).1
  calc expectedHitting (NonuniformMajority L K).transitionKernel ra.c₀ (StableDone L K ra.init)
      ≤ Brecover + Bleak := hmain
    _ ≤ ((21 * C0 * n * (L + 1) : ℕ) : ℝ≥0∞) + ((4 * Cbad * n * (L + 1) : ℕ) : ℝ≥0∞) :=
        add_le_add hBrec hBleak
    _ = (((21 * C0 + 4 * Cbad) * n * (L + 1) : ℕ) : ℝ≥0∞) := by push_cast; ring

/-- **`doty_theorem_3_1_expected_v51_numeral` (deliverable 2, numeral headline).**  At the LITERAL
`C0 = 17`, `Cbad = 3`: `E[T] ≤ (21·17 + 4·3)·n·(L+1) = 369·n·(L+1)`. -/
theorem doty_theorem_3_1_expected_v51_numeral {n L K : ℕ}
    (hReg : PaperRegime.DotyRegime n L K)
    (ra : DotyResidualAtomsV51 (L := L) (K := K) n AtomsV2.C0_numeral)
    (Brecover Bleak : ℝ≥0∞)
    (βfinal : Config (AgentState L K) → ℝ≥0∞)
    (G : Config (AgentState L K) → Prop)
    (hDone : MeasurableSet (StableDone L K ra.init))
    (hDoneAbs : ∀ x ∈ StableDone L K ra.init,
      (NonuniformMajority L K).transitionKernel x (StableDone L K ra.init)ᶜ = 0)
    (hOnGood : OffEventEndgame.OnGoodSlotClassifier (L := L) (K := K) n ra.init Brecover βfinal G)
    (hLeak : ∑' t : ℕ, ((NonuniformMajority L K).transitionKernel ^ t) ra.c₀
        ({b | ¬ (ReachableFrom L K ra.init b ∧ G b)} ∩ (StableDone L K ra.init)ᶜ) ≤ Bleak)
    (T : ℕ) (hT : T = ∑ i, (phases'V51 ra i).t)
    (ht : ∀ i, (phases'V51 ra i).t ≤ ra.Cphase i * n * (L + 1))
    (hεw : ∀ i, ((phases'V51 ra i).ε : ℝ≥0∞) ≤ (ra.δ i : ℝ≥0∞))
    (c5 : Config (AgentState L K))
    (hPhase5 : ReserveSampling.Phase5AllWin (L := L) (K := K) n c5)
    (hMainFloor : (n : ℝ) / 3 ≤ (RoleSplitConcentration.mainCount (L := L) (K := K) c5 : ℝ))
    (hConf : MainExponentConfinement.MainProfileConfinedToUseful (L := L) (K := K) c5)
    (hP5 : (ra.wi.P5 : ℝ) ≤ (23 : ℝ) * (n : ℝ) / 75)
    (hBrec : Brecover ≤ ((21 * AtomsV2.C0_numeral * n * (L + 1) : ℕ) : ℝ≥0∞))
    (hBleak : Bleak ≤ ((4 * AtomsV2.Cbad_numeral * n * (L + 1) : ℕ) : ℝ≥0∞)) :
    expectedHitting (NonuniformMajority L K).transitionKernel ra.c₀ (StableDone L K ra.init)
      ≤ (((21 * 17 + 4 * 3) * n * (L + 1) : ℕ) : ℝ≥0∞) :=
  doty_theorem_3_1_expected_v51_headline (C0 := AtomsV2.C0_numeral) (Cbad := AtomsV2.Cbad_numeral)
    hReg ra Brecover Bleak βfinal G hDone hDoneAbs hOnGood hLeak T hT ht hεw c5 hPhase5
    hMainFloor hConf hP5 hBrec hBleak

/-! ## Part 6 — the V5.1 CONSUMPTION TABLE (append-only; updated for F1 + F2).

The table now audits EVERY field on the FRESH `WorkInputsV51` (there is no nested `WorkInputsHonest`, so
no field escapes the audit — F1 fixed).  The eight dead V2 fields (`hM₀`, `hext1`, `hpull1`, `hClosed6`,
`hPhase6Post7`, `hE7`, `hPhase7Post8`, `hE8`) are GONE from the residual surface.  The expected side has
NO `hFloors` binder (F2 fixed).

### whp side — `doty_theorem_3_1_whp_v51` (over `DotyRegime` + `DotyResidualAtomsV51`)

| binder (in `ra` / `ra.wi`) | consumption point |
|----------------------------|-------------------|
| `wi.{σ,M₀,hn,hM1}` | common scalars / regime data threaded into slots 1/5/6/7/8 builders |
| `wi.{work0,work2,work3,work9}` | `dotyWorkSurvivalV51` carried slots 0/2/3/9 (literal arms) → `phases'V51` → `whp_of_asm'` |
| `wi.{P1,tWin1,η1,hescW1,hext1H,hpull1H,hpt1,escapeε1,hescε1}` | `dotyWorkSurvivalV51` slot 1 = `WindowSurvival.slot1Survival` (escape budget REPLACES `hClosed1`) |
| `wi.{s4,hs4,t4,ε4,hε4}` | `dotyWorkSurvivalV51` slot 4 = `Phase4Convergence.phase4Convergence` |
| `wi.{i5,K₀,P5,tWin5,hClosed5,hmain5,hpt5,εConc,hConc}` | `dotyWorkSurvivalV51` slot 5 = `FinalAssemblyV2.slot5Honest` (slot-5 closure CARRIED — the honest exception, `WindowSurvival` Part G) |
| `wi.{l,q6,tWin6,hdrop6,hpt6,η6,hescW6,hq6zero,escapeε6,hescε6}` | `dotyWorkSurvivalV51` slot 6 = `WindowSurvival.slotSurvival` (escape budget REPLACES `hClosed6`) |
| `wi.{E7,tWin7,η7,hescW7,hwit7,hpt7,escapeε7,hescε7}` | `dotyWorkSurvivalV51` slot 7 = `WindowSurvival.slot7Survival` (REPLACES `hClosed7`) |
| `wi.{E8,tWin8,η8,hescW8,hwit8,hpt8,escapeε8,hescε8}` | `dotyWorkSurvivalV51` slot 8 = `WindowSurvival.slot8Survival` (REPLACES `hClosed8`) |
| `wi.{s10,hs10,hsB10,k10}` | `dotyWorkSurvivalV51` slot 10 = `Phase10Convergence.phase10Convergence`; slot-20 `Post` pin `slot20_post_pin_v51` |
| `seamP,seamT,εepidemic,εovershoot,hDrift,hNoOvershoot,hWorkPostToWindow,hSeedStep,hWindowToWorkPre` | `toAssembly'V51` (the `DotyAssembly'` seam fields → `dotyPhases'`) |
| `Cphase,δ,hC0,hδ` | `whp_of_asm'` (the budget fold to `21/n²` + `21·C0·n·(L+1)`) |
| `c₀,init,hStart,hWork0PreOfStart` | `hx₀_of_start_v51` (slot-0 `Pre` pin `slot0_pre_pin_v51`) → `whp_of_asm'`'s `hx₀` |
| `hPhase10Sign` | `h_post_of_sign_v51` (`AtomsV2.postOfSign` ∘ `slot20_post_pin_v51`) → `whp_of_asm'`'s `h_post` |
| `hReg` (`DotyRegime`) | `hReg.hLlog` (the `clog` form of the time bound) |

### expected side — `doty_theorem_3_1_expected_v51` (REBASED on the SAME `ra`, NO `hFloors`)

| binder | consumption point |
|--------|-------------------|
| `hOnGood` | `expected_le_of_onGood_occupation_v51` → `onGood_occupation_le_v51` → `onGood_recovery_cap_v51` → `AtomsV2.branchOfSlotRegime (hOnGood b …)` → `regimeClassification_of_chainEndBranch` → **`ChainEndRecut.reachable_hLadder'`** (NO floor binder, F2 fix) → `recoveryClass_of_ladderData.expectedHitting_le` → `occupation_mid_le`.  **CONSUMED.** |
| ~~`hFloors`~~ | **DROPPED** (F2 fix) — `reachable_hLadder` IGNORED it; `reachable_hLadder'` never took it. Floor data lives inside the regime classification's carried `LadderData`. |
| `hLeak` (off-good occupation) | `expected_le_of_onGood_occupation_v51` (the off-`Mid` band of the `Doneᶜ` split) — the genuine carried residual |
| `hDone,hDoneAbs` | `occupation_mid_le` + the `Done`-absorption in `onGood_recovery_cap_v51` / the `expectedHitting=0` on `Done` |
| `c5,hPhase5,hMainFloor,hConf,hP5` | `FinalAssemblyV5.slot5_floor_via_phase3_squaring` → `confine3_served_by_phase3_squaring` (phase-3 squaring chain) → `theorem6_2_usefulMains_floor` |
| `T,hT,ht,hεw,hReg,ra,C0` | the WIRED `hfail` conjunct PRODUCED by `doty_theorem_3_1_whp_v51` on the SAME `ra` |
| `Brecover,Bleak` (+ `hBrec,hBleak` on the headline) | the additive bound `E[T] ≤ Brecover + Bleak`, closed to the headline `(21·C0+4·Cbad)·n·(L+1)` |

### What was genuinely impossible to plug (the honest residuals — unchanged from V5)

* **Slot-5 window closure** (`wi.hClosed5`).  Phase 5 is NOT a counter-reset destination, so the
  `WindowSurvival` at-risk-counter survival mechanism does NOT apply (`WindowSurvival` Part G); slot-5's
  closure stays carried.
* **The off-good leak occupation** (`hLeak`).  Off the good window `G` there is no deterministic ladder;
  the off-good mass is charged to the leak budget `Bleak`, never classified — the honest doctrine.
* **The within-slot probabilistic floors** (`hext1H`/`hpull1H`/`hwit7`/`hwit8`/`hmain5`/`hConc`/…).
  These are the roster's genuinely-open eliminator-margin / partner-pool / sampling-concentration inputs
  (Doty Lemmas 5.3 / 7.1 / 7.4 / 7.6 / Thm 6.2); carried named facts.
* **The escape probabilities** (`η1`/`η6`/`η7`/`η8` + the budget fits `hescε*`).  The at-risk counter
  tail is the protocol-specific input carried as the named escape budget REPLACING the false exact
  closure.

## Axiom audit (verified by `#print axioms`)

All seven V5.1 theorems — `doty_theorem_3_1_whp_v51`, `doty_theorem_3_1_whp_numeral_v51`,
`onGood_recovery_cap_v51`, `doty_theorem_3_1_expected_v51`, `doty_theorem_3_1_expected_v51_headline`,
`doty_theorem_3_1_expected_v51_numeral` — depend on exactly `[propext, Classical.choice, Quot.sound]`.
No `sorry`/`admit`/`axiom`/`native_decide`. -/

end FinalAssemblyV51
end ExactMajority
