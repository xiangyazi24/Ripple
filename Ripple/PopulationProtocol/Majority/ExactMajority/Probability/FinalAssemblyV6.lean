/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# FinalAssemblyV6 — the V6 ASSEMBLY consuming the six POST63 atom packages (A–F).

This append-only file rebuilds the Doty Theorem 3.1 pair on a SHRUNK residual bundle
`DotyResidualAtomsV6`.  Every `WorkInputsV51` field that one of the six packages PRODUCES is supplied
to the V5.1 bundle BY CALLING the package's producer on the proof path (verifiable by `grep` of the
proof term of `toWorkInputsV51`), NOT carried.  The V6 residual therefore carries ONLY:

  (a) the genuinely-open inputs the producers still require (each package documents its remainder):
      * Pkg A: the `+3` sign witness `hwit1`, the entry/gap predicate `hentry1` with gap `g`
        (`P1 := (n - g + 3) / 4`), the rectangle-calibration data for slot 1;
      * Pkg B: the role-window bridges `hAll7/hStruct7`, `hAll8/hStruct8` and the per-level budget
        comparisons for slots 7/8;
      * Pkg C: the POINTWISE phase-3 confinement at `b` (`hConf5`) + the Main-role floor `hMainFloor5`
        + `hP5` — C's honest remainder (the whp kernel event does NOT yield pointwise `hmain5`);
      * Pkg D: the one-step escape tails `hηtail*` + budget fits `hfit*`, and the positive-level
        phase-6 drain rate `qpos6`/`hdrop6pos`/`hpt6pos`;
      * Pkg E: the slot-5 width/survival export + the sampled-class atoms;
      * Pkg F: the work-slot constructor inputs, the rooted phase-10 entry, the seed-event family,
        and the per-seam no-overshoot regime data;
      * the carried slot-5 closure `hClosed5` (Phase 5 is the documented non-reset exception).
  (b) `DotyRegime` (threaded as `hReg`).
  (c) arithmetic / boilerplate (the seam half, budget scalars, start/sign atoms not produced above).

The V6 theorems `doty_theorem_3_1_whp_v6` / `_expected_v6` + numeral corollaries reach the SAME
conclusions (`≤ 21/n²`, `369·n·(L+1)`) as V5.1 by routing through `toResidualV51` and the landed
V5.1 theorems.

## Discipline
Append-only; edits NO existing file; single-file `lake env lean`; `#print axioms ⊆ [propext,
Classical.choice, Quot.sound]`; no `sorry`/`admit`/`axiom`/`native_decide`.
-/
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.FinalAssemblyV51
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.PkgAAtoms
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.PkgBAtoms
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.PkgCAtoms
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.PkgDAtoms
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.PkgEAtoms
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.PkgFAtoms

namespace ExactMajority
namespace FinalAssemblyV6

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators NNReal

variable {L K : ℕ}

/-! ## Part 1 — `DotyResidualAtomsV6`: the SHRUNK residual bundle.

Carries the producer-input remainders only.  The produced V51 fields are NOT carried here; they are
manufactured in `toWorkInputsV51` / `toResidualV51` by calling the package producers. -/
structure DotyResidualAtomsV6 (n C0 : ℕ) where
  -- ===== common scalars / regime data =====
  σ : Sign
  M₀ : ℕ
  hn : 2 ≤ n
  hM1 : 1 ≤ M₀
  -- ===== slot 1 — Pkg A producer inputs (REPLACE `hext1H`/`hpull1H`/`hpt1`) =====
  /-- slot-1 entry gap `g`; the slot-1 floor is fixed at `P1 := (n - g + 3) / 4`. -/
  g : ℕ
  /-- Pkg A remainder: the sharp `+3` sign witness on the honest window (`hext1H` input). -/
  hwit1 : ∀ b : Config (AgentState L K),
    HonestWindows.Phase1Honest (L := L) (K := K) n b → ∃ a ∈ b, DrainThreading.extremePos a
  /-- Pkg A remainder: the honest-window entry/gap predicate (`hpull1H` input). -/
  hentry1 : ∀ b : Config (AgentState L K),
    HonestWindows.Phase1Honest (L := L) (K := K) n b →
      PartnerMargin.EntrySumPinned (L := L) (K := K) n g b
  tWin1 : ℕ → ℕ
  /-- Pkg A remainder: the slot-1 rectangle real-fraction calibration data (`hpt1` input). -/
  α1 : ℕ → ℝ
  hM₀1 : (M₀ : ℝ) ≤ n
  hα01 : ∀ m ∈ Finset.Icc 1 M₀, 0 < α1 m
  hα11 : ∀ m ∈ Finset.Icc 1 M₀, α1 m ≤ 1
  hq01 : ∀ m ∈ Finset.Icc 1 M₀, 0 ≤ PkgAAtoms.qRectReal ((n - g + 3) / 4) n
  hq1 : ∀ m ∈ Finset.Icc 1 M₀,
    PkgAAtoms.qRectReal ((n - g + 3) / 4) n ≤ 1 - α1 m * (m : ℝ) / n
  hT1 : ∀ m ∈ Finset.Icc 1 M₀,
    (3 / α1 m) * ((n : ℝ) / (m : ℝ)) * Real.log n ≤ tWin1 m
  -- ===== slot 1 — escape inputs (Pkg D `hescε1`; `η1`/`hescW1` carried) =====
  η1 : ℝ≥0∞
  hescW1 : ∀ x, HonestWindows.Phase1Honest (L := L) (K := K) n x →
    (NonuniformMajority L K).transitionKernel x
      {y | ¬ HonestWindows.Phase1Honest (L := L) (K := K) n y} ≤ η1
  escapeε1 : ℝ≥0
  c1 : ℕ
  L01 : ℕ
  hηtail1 : η1 ≤ ENNReal.ofReal (Real.exp (-(c1 * (L01 + 1) : ℕ)))
  hfit1 : ((((∑ m ∈ Finset.Icc 1 M₀, tWin1 m) : ℕ) : ℝ≥0∞) *
      ENNReal.ofReal (Real.exp (-(c1 * (L01 + 1) : ℕ)))) ≤ (escapeε1 : ℝ≥0∞)
  -- ===== slot 0/2/3/9 — Pkg F constructor inputs (REPLACE carried `work0/2/3/9`) =====
  -- work0 (role-split two-stage)
  w0stage1 : PhaseConvergenceW (NonuniformMajority L K).transitionKernel
  w0stage15 : PhaseConvergenceW (NonuniformMajority L K).transitionKernel
  w0stage2 : PhaseConvergenceW (NonuniformMajority L K).transitionKernel
  w0chain1 : ∀ x, w0stage1.Post x → w0stage15.Pre x
  w0chain2 : ∀ x, w0stage15.Post x → w0stage2.Pre x
  -- work2 (calibrated union)
  w2s : ℝ
  w2hs : 0 < w2s
  w2t : ℕ
  w2ε : ℝ≥0
  w2hε : ENNReal.ofReal
      (1 - (((n - 1 : ℕ) : ℝ) / ((n : ℝ) * ((n : ℝ) - 1))) * (1 - Real.exp (-w2s))) ^ w2t *
      ENNReal.ofReal (Real.exp (w2s * ((n : ℝ) - 1))) / 1 ≤ (w2ε : ℝ≥0∞)
  -- work3 (bounded-horizon clock)
  w3mC : ℕ
  w3hmC : 2 ≤ w3mC
  w3hLK : 0 < K * (L + 1)
  w3hLK1 : 0 < K * (L + 1) - 1
  w3tseed : ℕ
  w3tbulk : ℕ
  w3htbulk : 0 < w3tbulk
  w3εbulk : ℝ≥0
  w3hεb : ClockKilledMinute.minuteRate n w3mC ^ w3tbulk *
      ENNReal.ofReal (Real.exp (Real.log 2 * (ClockRealBulk.bulkHi w3mC : ℝ))) / 1
        ≤ (w3εbulk : ℝ≥0∞)
  w3c₀ : Config (AgentState L K)
  w3εside : ℝ≥0∞
  w3hside : ∀ T τ, τ < (L + 1) *
      EarlyDripMarked.Mhour (L := L) (K := K) w3tseed w3tbulk →
    (ClockKilledMinute.realκ L K ^ τ) w3c₀
      (ClockUnconditional.Sgood (L := L) (K := K) n w3mC T)ᶜ ≤ w3εside
  w3εtot : ℝ≥0
  w3hεtot : ClockBudgets.εclock L K w3tbulk (w3εbulk : ℝ≥0∞) w3εside ≤ (w3εtot : ℝ≥0∞)
  -- work9 (calibrated union)
  w9s : ℝ
  w9hs : 0 < w9s
  w9t : ℕ
  w9ε : ℝ≥0
  w9hε : ENNReal.ofReal
      (1 - (((n - 1 : ℕ) : ℝ) / ((n : ℝ) * ((n : ℝ) - 1))) * (1 - Real.exp (-w9s))) ^ w9t *
      ENNReal.ofReal (Real.exp (w9s * ((n : ℝ) - 1))) / 1 ≤ (w9ε : ℝ≥0∞)
  -- ===== slot 4 — Phase-4 epidemic (carried scalar inputs) =====
  s4 : ℝ
  hs4 : 0 < s4
  t4 : ℕ
  ε4 : ℝ≥0
  hε4 : ENNReal.ofReal
          (1 - (((n - 1 : ℕ) : ℝ) / ((n : ℝ) * ((n : ℝ) - 1))) * (1 - Real.exp (-s4))) ^ t4 *
          ENNReal.ofReal (Real.exp (s4 * ((n : ℝ) - 1))) / 1
        ≤ (ε4 : ℝ≥0∞)
  -- ===== slot 5 — Pkg C/E producer inputs + carried closure =====
  i5 : Fin (L + 1)
  hiL5 : i5.val < L
  K₀ : ℕ
  /-- slot-5 biased-Main floor `P5`; the floor is fixed at `P5 := ⌊23 n / 75⌋` via `hP5lt`. -/
  P5 : ℕ
  tWin5 : ℕ → ℕ
  /-- carried slot-5 closure (Phase 5 = documented non-reset exception, Pkg D remainder). -/
  hClosed5 : OneSidedCancel.InvClosed (NonuniformMajority L K).transitionKernel
    (fun c => ReserveSampling.Phase5AllWin (L := L) (K := K) n c)
  hP5 : (P5 : ℝ) ≤ (23 : ℝ) * (n : ℝ) / 75
  /-- Pkg C remainder: the Main-role floor on every Phase-5 window. -/
  hMainFloor5 : ∀ b : Config (AgentState L K),
    ReserveSampling.Phase5AllWin (L := L) (K := K) n b →
      (n : ℝ) / 3 ≤ (RoleSplitConcentration.mainCount (L := L) (K := K) b : ℝ)
  /-- Pkg C remainder: the POINTWISE phase-3 confinement event on every Phase-5 window (C's honest
  residual — the whp kernel event does not yield this pointwise). -/
  hConf5 : ∀ b : Config (AgentState L K),
    ReserveSampling.Phase5AllWin (L := L) (K := K) n b →
      MainExponentConfinement.MainProfileConfinedToUseful (L := L) (K := K) b
  /-- Pkg A producer for slot-5 budget (same rectangle calibration shape). -/
  α5 : ℕ → ℝ
  hα05 : ∀ m ∈ Finset.Icc 1 M₀, 0 < α5 m
  hα15 : ∀ m ∈ Finset.Icc 1 M₀, α5 m ≤ 1
  hq05 : ∀ m ∈ Finset.Icc 1 M₀, 0 ≤ PkgAAtoms.qRectReal P5 n
  hq5 : ∀ m ∈ Finset.Icc 1 M₀,
    PkgAAtoms.qRectReal P5 n ≤ 1 - α5 m * (m : ℝ) / n
  hT5 : ∀ m ∈ Finset.Icc 1 M₀,
    (3 / α5 m) * ((n : ℝ) / (m : ℝ)) * Real.log n ≤ tWin5 m
  -- Pkg E producer inputs for `εConc`/`hConc`
  e5s : ℝ
  e5hs : 0 ≤ e5s
  e5reserveFloor : ℕ
  e5classFloor : ℕ
  e5hbudget : e5reserveFloor * e5classFloor ≤ n * (n - 1)
  e5hres : ∀ c, ReserveSampling.Phase5AllWin (L := L) (K := K) n c →
    e5reserveFloor ≤ (Phase5Convergence.unsampledReserves (L := L) (K := K)).sum c.count
  e5hcls : ∀ c, ReserveSampling.Phase5AllWin (L := L) (K := K) n c →
    e5classFloor ≤ (Phase5Convergence.classMainStates (L := L) (K := K) σ i5).sum c.count
  εConc : ℝ≥0
  e5hbridge : ∀ c, ReserveSampling.Phase5AllWin (L := L) (K := K) n c →
    SampledClassTail.sampledClassPot (L := L) (K := K) i5 e5s c
        < ENNReal.ofReal (Real.exp (-(e5s * (K₀ : ℝ)))) →
    (NonuniformMajority L K).transitionKernel c
      (SampledClassTail.sampledClassGate (L := L) (K := K) n)ᶜ = 0
  e5β : ℝ≥0∞
  e5hwidth : PkgEAtoms.phase5WidthSurvivalExport (L := L) (K := K) n e5s i5 K₀
    (∑ m ∈ Finset.Icc 1 M₀, tWin5 m) e5β
  e5hε : ∀ c₀, ReserveSampling.Phase5AllWin (L := L) (K := K) n c₀ →
    (ENNReal.ofReal (1 - SamplingAtoms.rateFloor e5reserveFloor e5classFloor n
            * (1 - Real.exp (-e5s))) ^ (∑ m ∈ Finset.Icc 1 M₀, tWin5 m)
          * SampledClassTail.sampledClassPot (L := L) (K := K) i5 e5s c₀ + 0)
        / ENNReal.ofReal (Real.exp (-(e5s * (K₀ : ℝ))))
      + (((∑ m ∈ Finset.Icc 1 M₀, tWin5 m) : ℕ) : ℝ≥0∞) * e5β ≤ (εConc : ℝ≥0∞)
  -- ===== slot 6 — Pkg D padded rate inputs (REPLACE `q6`/`hdrop6`/`hpt6`/`hq6zero`) =====
  l : ℕ
  /-- the positive-level phase-6 drain rate (level `0` padded to `1` by `q6D`). -/
  qpos6 : ℕ → ℝ≥0∞
  tWin6 : ℕ → ℕ
  hdrop6pos : ∀ m, 1 ≤ m → ∀ b : Config (AgentState L K),
    Phase6Convergence.Phase6Win (L := L) (K := K) n b →
    Phase6Convergence.highMass (L := L) (K := K) l b = m →
    (NonuniformMajority L K).transitionKernel b
      (OneSidedCancel.potBelow
        (fun c => Phase6Convergence.highMass (L := L) (K := K) l c) m)ᶜ ≤ qpos6 m
  hpt6pos : ∀ m ∈ Finset.Icc 1 M₀,
    (qpos6 m) ^ (tWin6 m) ≤ (DrainCalibration.budgetNN M₀ n : ℝ≥0∞)
  η6 : ℝ≥0∞
  hescW6 : ∀ x, Phase6Convergence.Phase6Win (L := L) (K := K) n x →
    (NonuniformMajority L K).transitionKernel x
      {y | ¬ Phase6Convergence.Phase6Win (L := L) (K := K) n y} ≤ η6
  escapeε6 : ℝ≥0
  c6 : ℕ
  L06 : ℕ
  hηtail6 : η6 ≤ ENNReal.ofReal (Real.exp (-(c6 * (L06 + 1) : ℕ)))
  hfit6 : ((((∑ m ∈ Finset.Icc 1 M₀, tWin6 m) : ℕ) : ℝ≥0∞) *
      ENNReal.ofReal (Real.exp (-(c6 * (L06 + 1) : ℕ)))) ≤ (escapeε6 : ℝ≥0∞)
  -- ===== slot 7 — Pkg B producer inputs (REPLACE `hwit7`/`hpt7`) =====
  E7 : ℕ
  tWin7 : ℕ → ℕ
  hE7 : (E7 : ℝ) ≤ (4 : ℝ) * (n : ℝ) / 15
  hAll7 : ∀ b : Config (AgentState L K),
    HonestWindows.Phase7Honest (L := L) (K := K) n b →
    Phase7Convergence.Phase7AllMain (L := L) (K := K) n b
  hStruct7 : ∀ b : Config (AgentState L K),
    HonestWindows.Phase7Honest (L := L) (K := K) n b →
    EliminatorMargins.Phase6To7Structure (L := L) (K := K) σ E7 b
  hq07 : 0 ≤ 1 - (E7 : ℝ) / ((n : ℝ) * ((n : ℝ) - 1))
  hrate7 : ∀ m ∈ Finset.Icc 1 M₀,
    1 - (E7 : ℝ) / ((n : ℝ) * ((n : ℝ) - 1)) ≤ 1 - (4 / 15 : ℝ) * (m : ℝ) / n
  hTw7 : ∀ m ∈ Finset.Icc 1 M₀,
    (3 / (4 / 15 : ℝ)) * ((n : ℝ) / (m : ℝ)) * Real.log n ≤ tWin7 m
  η7 : ℝ≥0∞
  hescW7 : ∀ x, HonestWindows.Phase7Honest (L := L) (K := K) n x →
    (NonuniformMajority L K).transitionKernel x
      {y | ¬ HonestWindows.Phase7Honest (L := L) (K := K) n y} ≤ η7
  escapeε7 : ℝ≥0
  c7 : ℕ
  L07 : ℕ
  hηtail7 : η7 ≤ ENNReal.ofReal (Real.exp (-(c7 * (L07 + 1) : ℕ)))
  hfit7 : ((((∑ m ∈ Finset.Icc 1 M₀, tWin7 m) : ℕ) : ℝ≥0∞) *
      ENNReal.ofReal (Real.exp (-(c7 * (L07 + 1) : ℕ)))) ≤ (escapeε7 : ℝ≥0∞)
  -- ===== slot 8 — Pkg B producer inputs (REPLACE `hwit8`/`hpt8`) =====
  E8 : ℕ
  tWin8 : ℕ → ℕ
  hE8 : (E8 : ℝ) ≤ (1 : ℝ) * (n : ℝ) / 5
  hAll8 : ∀ b : Config (AgentState L K),
    HonestWindows.Phase8Honest (L := L) (K := K) n b →
    Phase8Convergence.Phase8AllMain (L := L) (K := K) n b
  hStruct8 : ∀ b : Config (AgentState L K),
    HonestWindows.Phase8Honest (L := L) (K := K) n b →
    EliminatorMargins.Phase7To8Structure (L := L) (K := K) σ E8 b
  hq08 : 0 ≤ 1 - (E8 : ℝ) / ((n : ℝ) * ((n : ℝ) - 1))
  hrate8 : ∀ m ∈ Finset.Icc 1 M₀,
    1 - (E8 : ℝ) / ((n : ℝ) * ((n : ℝ) - 1)) ≤ 1 - (14 / 75 : ℝ) * (m : ℝ) / n
  hTw8 : ∀ m ∈ Finset.Icc 1 M₀,
    (3 / (14 / 75 : ℝ)) * ((n : ℝ) / (m : ℝ)) * Real.log n ≤ tWin8 m
  η8 : ℝ≥0∞
  hescW8 : ∀ x, HonestWindows.Phase8Honest (L := L) (K := K) n x →
    (NonuniformMajority L K).transitionKernel x
      {y | ¬ HonestWindows.Phase8Honest (L := L) (K := K) n y} ≤ η8
  escapeε8 : ℝ≥0
  c8 : ℕ
  L08 : ℕ
  hηtail8 : η8 ≤ ENNReal.ofReal (Real.exp (-(c8 * (L08 + 1) : ℕ)))
  hfit8 : ((((∑ m ∈ Finset.Icc 1 M₀, tWin8 m) : ℕ) : ℝ≥0∞) *
      ENNReal.ofReal (Real.exp (-(c8 * (L08 + 1) : ℕ)))) ≤ (escapeε8 : ℝ≥0∞)
  -- ===== slot 10 — Phase-10 block-geometric (carried scalar inputs) =====
  s10 : ℕ
  hs10 : 0 < s10
  hsB10 : (3 * (((n ^ 2 : ℕ) : ℝ≥0∞) * ENNReal.ofReal (1 + 2 * Real.log n))) * 2
    ≤ (s10 : ℝ≥0∞)
  k10 : ℕ
  -- ===== seam half (carried — boilerplate) =====
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
  -- seam glue (Post→window / seed-step / window→pre) restated against the produced family
  c₀ : Config (AgentState L K)
  init : Config (AgentState L K)
  -- ===== budget / config scalars =====
  Cphase : Fin 21 → ℕ
  δ : Fin 21 → ℝ≥0
  hC0 : ∀ i, Cphase i ≤ C0
  hδ : ∀ i, (δ i : ℝ≥0∞) ≤ (1 / (n : ℝ≥0∞) ^ 2)
  -- ===== start / sign — Pkg F producer inputs (REPLACE `hWork0PreOfStart`/`hPhase10Sign`) =====
  hStart : RoleSplitConcentration.Phase0Initial (L := L) (K := K) n c₀
  /-- Pkg F input for `hWork0PreOfStart`: stage-1 pre from the honest start. -/
  hStagePre0 : RoleSplitConcentration.Phase0Initial (L := L) (K := K) n c₀ → w0stage1.Pre c₀
  /-- Pkg F inputs for `hPhase10Sign`: the rooted phase-10 entry data. -/
  hInitValid : validInitial init
  hAllRoot : ∀ a ∈ init, a.phase.val = 10
  hActRoot : hasActiveAgent init
  hReach10 : ∀ c, Phase10Drop.Phase10Post (L := L) (K := K) c →
    (NonuniformMajority L K).Reachable init c

/-! ## Part 2 — `toWorkInputsV51`: build `WorkInputsV51` by CALLING the package producers.

Each produced field is supplied by a package producer; the rest are carried verbatim.  This is the
consumption surface: grep this definition's body for the producer names. -/
noncomputable def toWorkInputsV51 {n C0 : ℕ} (ra : DotyResidualAtomsV6 (L := L) (K := K) n C0) :
    FinalAssemblyV51.WorkInputsV51 (L := L) (K := K) n where
  σ := ra.σ
  M₀ := ra.M₀
  hn := ra.hn
  hM1 := ra.hM1
  -- slots 0/2/3/9 — Pkg F constructors
  work0 := PkgFAtoms.work0_of_two_stage (L := L) (K := K)
    ra.w0stage1 ra.w0stage15 ra.w0stage2 ra.w0chain1 ra.w0chain2
  work2 := PkgFAtoms.work2_calibratedUnion (L := L) (K := K) n ra.hn ra.w2s ra.w2hs ra.w2t ra.w2ε ra.w2hε
  work3 := PkgFAtoms.work3_phase3_bounded (L := L) (K := K) n ra.w3mC ra.hn ra.w3hmC ra.w3hLK ra.w3hLK1
    ra.w3tseed ra.w3tbulk ra.w3htbulk ra.w3εbulk ra.w3hεb ra.w3c₀ ra.w3εside ra.w3hside ra.w3εtot ra.w3hεtot
  work9 := PkgFAtoms.work9_calibratedUnion (L := L) (K := K) n ra.hn ra.w9s ra.w9hs ra.w9t ra.w9ε ra.w9hε
  -- slot 1 — Pkg A producers + Pkg D escape
  P1 := (n - ra.g + 3) / 4
  tWin1 := ra.tWin1
  η1 := ra.η1
  hescW1 := ra.hescW1
  hext1H := PkgAAtoms.hext1H_of_extremePos_witness_honest (L := L) (K := K) n ra.hwit1
  hpull1H := PkgAAtoms.hpull1H_of_entry_on_honest (L := L) (K := K) n ra.g ra.hentry1
  hpt1 := PkgAAtoms.hpt1_of_rect_calibration (P1 := (n - ra.g + 3) / 4) ra.tWin1 ra.α1
    ra.hn ra.hM1 ra.hM₀1 ra.hα01 ra.hα11 ra.hq01 ra.hq1 ra.hT1
  escapeε1 := ra.escapeε1
  hescε1 := PkgDAtoms.hescε1_of_tail_fit ra.c1 ra.L01 ra.M₀ ra.tWin1 ra.η1
    ra.escapeε1 ra.hηtail1 ra.hfit1
  -- slot 4
  s4 := ra.s4
  hs4 := ra.hs4
  t4 := ra.t4
  ε4 := ra.ε4
  hε4 := ra.hε4
  -- slot 5 — Pkg C `hmain5`, Pkg A budget, Pkg E concentration, carried closure
  i5 := ra.i5
  K₀ := ra.K₀
  P5 := ra.P5
  tWin5 := ra.tWin5
  hClosed5 := ra.hClosed5
  hmain5 := PkgCAtoms.hmain5_of_pointwise_confinement (L := L) (K := K) ra.hP5 ra.hMainFloor5 ra.hConf5
  hpt5 := PkgAAtoms.hpt1_of_rect_calibration (P1 := ra.P5) ra.tWin5 ra.α5
    ra.hn ra.hM1 ra.hM₀1 ra.hα05 ra.hα15 ra.hq05 ra.hq5 ra.hT5
  εConc := ra.εConc
  hConc := PkgEAtoms.hConc_field_of_atoms_and_widthSurvival (L := L) (K := K) ra.σ ra.i5 ra.hiL5
    n ra.hn ra.e5s ra.e5hs ra.e5reserveFloor ra.e5classFloor ra.e5hbudget ra.e5hres ra.e5hcls
    ra.K₀ ra.M₀ ra.tWin5 ra.εConc ra.e5hbridge ra.e5β ra.e5hwidth ra.e5hε
  -- slot 6 — Pkg D padded rate + escape
  l := ra.l
  q6 := PkgDAtoms.q6D ra.qpos6
  tWin6 := ra.tWin6
  hdrop6 := PkgDAtoms.hdrop6_padded_from_positive (L := L) (K := K) ra.l ra.qpos6 ra.hdrop6pos
  hpt6 := PkgDAtoms.hpt6_padded_from_positive (M₀ := ra.M₀) (qpos := ra.qpos6) (tWin6 := ra.tWin6)
    (budget := (DrainCalibration.budgetNN ra.M₀ n : ℝ≥0∞)) ra.hpt6pos
  η6 := ra.η6
  hescW6 := ra.hescW6
  hq6zero := PkgDAtoms.hq6zero_padded ra.qpos6
  escapeε6 := ra.escapeε6
  hescε6 := PkgDAtoms.hescε6_of_tail_fit ra.c6 ra.L06 ra.M₀ ra.tWin6 ra.η6
    ra.escapeε6 ra.hηtail6 ra.hfit6
  -- slot 7 — Pkg B producers + Pkg D escape
  E7 := ra.E7
  tWin7 := ra.tWin7
  η7 := ra.η7
  hescW7 := ra.hescW7
  hwit7 := PkgBAtoms.hwit7_of_phase6To7Structure_honest (L := L) (K := K) ra.hE7 ra.hAll7 ra.hStruct7
  hpt7 := PkgBAtoms.hpt7_budget_alpha ra.tWin7 ra.hn ra.hM1 ra.hM₀1 ra.hq07 ra.hrate7 ra.hTw7
  escapeε7 := ra.escapeε7
  hescε7 := PkgDAtoms.hescε7_of_tail_fit ra.c7 ra.L07 ra.M₀ ra.tWin7 ra.η7
    ra.escapeε7 ra.hηtail7 ra.hfit7
  -- slot 8 — Pkg B producers + Pkg D escape
  E8 := ra.E8
  tWin8 := ra.tWin8
  η8 := ra.η8
  hescW8 := ra.hescW8
  hwit8 := PkgBAtoms.hwit8_of_phase7To8Structure_honest (L := L) (K := K) ra.hE8 ra.hAll8 ra.hStruct8
  hpt8 := PkgBAtoms.hpt8_budget_recut ra.tWin8 ra.hn ra.hM1 ra.hM₀1 ra.hq08 ra.hrate8 ra.hTw8
  escapeε8 := ra.escapeε8
  hescε8 := PkgDAtoms.hescε8_of_tail_fit ra.c8 ra.L08 ra.M₀ ra.tWin8 ra.η8
    ra.escapeε8 ra.hηtail8 ra.hfit8
  -- slot 10
  s10 := ra.s10
  hs10 := ra.hs10
  hsB10 := ra.hsB10
  k10 := ra.k10

/-- The produced V5.1 work family on the V6 residual. -/
noncomputable abbrev workV6 {n C0 : ℕ} (ra : DotyResidualAtomsV6 (L := L) (K := K) n C0) :
    Fin 11 → PhaseConvergenceW (NonuniformMajority L K).transitionKernel :=
  FinalAssemblyV51.dotyWorkSurvivalV51 (L := L) (K := K) (toWorkInputsV51 ra)

/-! ## Part 3 — `toResidualV51`: build the V5.1 residual from the V6 residual.

The three seam-glue fields (`hWorkPostToWindow`, `hSeedStep`, `hWindowToWorkPre`) reference the
PRODUCED work family `workV6 ra`, so they are taken as explicit arguments (`hPost2Win`, the seed-event
family `hSeedEvent` from which Pkg F PRODUCES `hSeedStep`, and `hWin2Pre`) rather than carried inside
`DotyResidualAtomsV6` — that mirrors how V5.1's expected theorem takes its phase-3 entry inputs as
theorem arguments.  `hWork0PreOfStart` and `hPhase10Sign` are PRODUCED by Pkg F producers
(`hWork0PreOfStart_of_work0_eq` at `hwork0 := rfl`, and `hPhase10Sign_of_rooted`). -/
noncomputable def toResidualV51 {n C0 : ℕ} (ra : DotyResidualAtomsV6 (L := L) (K := K) n C0)
    (hPost2Win : ∀ (k : Fin 10) (c : Config (AgentState L K)),
      (workV6 ra ⟨k.val, by omega⟩).Post c →
      SeamEpidemics.allPhaseGe (L := L) (K := K) (ra.seamP k) n c)
    (hSeedEvent : ∀ k : Fin 10,
      SmallSweep.SeedStepEvent (L := L) (K := K) (ra.seamP k)
        ((workV6 ra ⟨k.val, by omega⟩).Post))
    (hWin2Pre : ∀ (k : Fin 10) (c : Config (AgentState L K)),
      SeamEpidemics.allPhaseEq (L := L) (K := K) (ra.seamP k + 1) n c →
      (workV6 ra ⟨k.val + 1, by omega⟩).Pre c) :
    FinalAssemblyV51.DotyResidualAtomsV51 (L := L) (K := K) n C0 where
  wi := toWorkInputsV51 ra
  seamP := ra.seamP
  seamT := ra.seamT
  εepidemic := ra.εepidemic
  εovershoot := ra.εovershoot
  hDrift := ra.hDrift
  hNoOvershoot := ra.hNoOvershoot
  hWorkPostToWindow := hPost2Win
  -- Pkg F PRODUCES `hSeedStep` from the per-seam seed-event family.
  hSeedStep := PkgFAtoms.hSeedStep_v51_of_event (L := L) (K := K) (toWorkInputsV51 ra) ra.seamP hSeedEvent
  hWindowToWorkPre := hWin2Pre
  Cphase := ra.Cphase
  δ := ra.δ
  c₀ := ra.c₀
  init := ra.init
  hC0 := ra.hC0
  hδ := ra.hδ
  hStart := ra.hStart
  -- Pkg F PRODUCES `hWork0PreOfStart` (work0 is literally the role-split slot, so `hwork0 := rfl`).
  hWork0PreOfStart := PkgFAtoms.hWork0PreOfStart_of_work0_eq (L := L) (K := K)
    ra.w0stage1 ra.w0stage15 ra.w0stage2 ra.w0chain1 ra.w0chain2 rfl ra.hStagePre0
  -- Pkg F PRODUCES `hPhase10Sign` from the rooted phase-10 entry data.
  hPhase10Sign := PkgFAtoms.hPhase10Sign_of_rooted (L := L) (K := K)
    ra.hInitValid ra.hAllRoot ra.hActRoot ra.hReach10

/-- The wired 21-instance family on the V6 residual (via the produced V5.1 residual). -/
noncomputable def phasesV6 {n C0 : ℕ} (ra : DotyResidualAtomsV6 (L := L) (K := K) n C0)
    (hPost2Win : ∀ (k : Fin 10) (c : Config (AgentState L K)),
      (workV6 ra ⟨k.val, by omega⟩).Post c →
      SeamEpidemics.allPhaseGe (L := L) (K := K) (ra.seamP k) n c)
    (hSeedEvent : ∀ k : Fin 10,
      SmallSweep.SeedStepEvent (L := L) (K := K) (ra.seamP k)
        ((workV6 ra ⟨k.val, by omega⟩).Post))
    (hWin2Pre : ∀ (k : Fin 10) (c : Config (AgentState L K)),
      SeamEpidemics.allPhaseEq (L := L) (K := K) (ra.seamP k + 1) n c →
      (workV6 ra ⟨k.val + 1, by omega⟩).Pre c) :
    Fin 21 → PhaseConvergenceW (NonuniformMajority L K).transitionKernel :=
  FinalAssemblyV51.phases'V51 (L := L) (K := K) (toResidualV51 ra hPost2Win hSeedEvent hWin2Pre)

/-! ## Part 4 — the V6 theorems.  Same conclusions as V5.1, on the SHRUNK bundle. -/

/-- **`doty_theorem_3_1_whp_v6`.**  The whp half on the SHRUNK V6 residual: failure `≤ 21/n²` within
`T ≤ 21·C0·n·(L+1)` (and the `clog` form).  Routes through `doty_theorem_3_1_whp_v51` on the produced
`toResidualV51 ra …`; the producer-supplied V51 fields appear in the proof term of `toWorkInputsV51`
(grep). -/
theorem doty_theorem_3_1_whp_v6 {n L K C0 : ℕ}
    (hReg : PaperRegime.DotyRegime n L K)
    (ra : DotyResidualAtomsV6 (L := L) (K := K) n C0)
    (hPost2Win : ∀ (k : Fin 10) (c : Config (AgentState L K)),
      (workV6 ra ⟨k.val, by omega⟩).Post c →
      SeamEpidemics.allPhaseGe (L := L) (K := K) (ra.seamP k) n c)
    (hSeedEvent : ∀ k : Fin 10,
      SmallSweep.SeedStepEvent (L := L) (K := K) (ra.seamP k)
        ((workV6 ra ⟨k.val, by omega⟩).Post))
    (hWin2Pre : ∀ (k : Fin 10) (c : Config (AgentState L K)),
      SeamEpidemics.allPhaseEq (L := L) (K := K) (ra.seamP k + 1) n c →
      (workV6 ra ⟨k.val + 1, by omega⟩).Pre c)
    (T : ℕ)
    (hT : T = ∑ i, (phasesV6 ra hPost2Win hSeedEvent hWin2Pre i).t)
    (ht : ∀ i, (phasesV6 ra hPost2Win hSeedEvent hWin2Pre i).t ≤ ra.Cphase i * n * (L + 1))
    (hε : ∀ i, ((phasesV6 ra hPost2Win hSeedEvent hWin2Pre i).ε : ℝ≥0∞) ≤ (ra.δ i : ℝ≥0∞)) :
    ((NonuniformMajority L K).transitionKernel ^ T) ra.c₀
        {c | ¬ majorityStableEndpoint (L := L) (K := K) ra.init c}
      ≤ (21 : ℝ≥0∞) / (n : ℝ≥0∞) ^ 2
    ∧ T ≤ 21 * C0 * n * (L + 1)
    ∧ T ≤ 21 * C0 * n * (Nat.clog 2 n + 1) :=
  FinalAssemblyV51.doty_theorem_3_1_whp_v51 (C0 := C0) hReg
    (toResidualV51 ra hPost2Win hSeedEvent hWin2Pre) T hT ht hε

/-- **`doty_theorem_3_1_whp_numeral_v6`.**  At the LITERAL `C0 = 17`. -/
theorem doty_theorem_3_1_whp_numeral_v6 {n L K : ℕ}
    (hReg : PaperRegime.DotyRegime n L K)
    (ra : DotyResidualAtomsV6 (L := L) (K := K) n AtomsV2.C0_numeral)
    (hPost2Win : ∀ (k : Fin 10) (c : Config (AgentState L K)),
      (workV6 ra ⟨k.val, by omega⟩).Post c →
      SeamEpidemics.allPhaseGe (L := L) (K := K) (ra.seamP k) n c)
    (hSeedEvent : ∀ k : Fin 10,
      SmallSweep.SeedStepEvent (L := L) (K := K) (ra.seamP k)
        ((workV6 ra ⟨k.val, by omega⟩).Post))
    (hWin2Pre : ∀ (k : Fin 10) (c : Config (AgentState L K)),
      SeamEpidemics.allPhaseEq (L := L) (K := K) (ra.seamP k + 1) n c →
      (workV6 ra ⟨k.val + 1, by omega⟩).Pre c)
    (T : ℕ)
    (hT : T = ∑ i, (phasesV6 ra hPost2Win hSeedEvent hWin2Pre i).t)
    (ht : ∀ i, (phasesV6 ra hPost2Win hSeedEvent hWin2Pre i).t ≤ ra.Cphase i * n * (L + 1))
    (hε : ∀ i, ((phasesV6 ra hPost2Win hSeedEvent hWin2Pre i).ε : ℝ≥0∞) ≤ (ra.δ i : ℝ≥0∞)) :
    ((NonuniformMajority L K).transitionKernel ^ T) ra.c₀
        {c | ¬ majorityStableEndpoint (L := L) (K := K) ra.init c}
      ≤ (21 : ℝ≥0∞) / (n : ℝ≥0∞) ^ 2
    ∧ T ≤ 21 * AtomsV2.C0_numeral * n * (L + 1)
    ∧ T ≤ 21 * AtomsV2.C0_numeral * n * (Nat.clog 2 n + 1) :=
  doty_theorem_3_1_whp_v6 (C0 := AtomsV2.C0_numeral) hReg ra hPost2Win hSeedEvent hWin2Pre T hT ht hε

/-- **`doty_theorem_3_1_expected_v6`.**  The off-event half on the SHRUNK V6 residual: routes through
`doty_theorem_3_1_expected_v51` on `toResidualV51 ra …`.  The slot-5 entry, on-good classifier, and
leak budget are the V5.1 expected-side inputs; `ra.wi.P5` is `ra.P5` by construction. -/
theorem doty_theorem_3_1_expected_v6 {n L K C0 : ℕ}
    (hReg : PaperRegime.DotyRegime n L K)
    (ra : DotyResidualAtomsV6 (L := L) (K := K) n C0)
    (hPost2Win : ∀ (k : Fin 10) (c : Config (AgentState L K)),
      (workV6 ra ⟨k.val, by omega⟩).Post c →
      SeamEpidemics.allPhaseGe (L := L) (K := K) (ra.seamP k) n c)
    (hSeedEvent : ∀ k : Fin 10,
      SmallSweep.SeedStepEvent (L := L) (K := K) (ra.seamP k)
        ((workV6 ra ⟨k.val, by omega⟩).Post))
    (hWin2Pre : ∀ (k : Fin 10) (c : Config (AgentState L K)),
      SeamEpidemics.allPhaseEq (L := L) (K := K) (ra.seamP k + 1) n c →
      (workV6 ra ⟨k.val + 1, by omega⟩).Pre c)
    (Brecover Bleak : ℝ≥0∞)
    (βfinal : Config (AgentState L K) → ℝ≥0∞)
    (G : Config (AgentState L K) → Prop)
    (hDone : MeasurableSet (StableDone L K ra.init))
    (hDoneAbs : ∀ x ∈ StableDone L K ra.init,
      (NonuniformMajority L K).transitionKernel x (StableDone L K ra.init)ᶜ = 0)
    (hOnGood : OffEventEndgame.OnGoodSlotClassifier (L := L) (K := K) n ra.init Brecover βfinal G)
    (hLeak : ∑' t : ℕ, ((NonuniformMajority L K).transitionKernel ^ t) ra.c₀
        ({b | ¬ (ReachableFrom L K ra.init b ∧ G b)} ∩ (StableDone L K ra.init)ᶜ) ≤ Bleak)
    (T : ℕ)
    (hT : T = ∑ i, (phasesV6 ra hPost2Win hSeedEvent hWin2Pre i).t)
    (ht : ∀ i, (phasesV6 ra hPost2Win hSeedEvent hWin2Pre i).t ≤ ra.Cphase i * n * (L + 1))
    (hεw : ∀ i, ((phasesV6 ra hPost2Win hSeedEvent hWin2Pre i).ε : ℝ≥0∞) ≤ (ra.δ i : ℝ≥0∞))
    (c5 : Config (AgentState L K))
    (hPhase5 : ReserveSampling.Phase5AllWin (L := L) (K := K) n c5)
    (hMainFloor : (n : ℝ) / 3 ≤ (RoleSplitConcentration.mainCount (L := L) (K := K) c5 : ℝ))
    (hConf : MainExponentConfinement.MainProfileConfinedToUseful (L := L) (K := K) c5)
    (hP5 : (ra.P5 : ℝ) ≤ (23 : ℝ) * (n : ℝ) / 75) :
    expectedHitting (NonuniformMajority L K).transitionKernel ra.c₀ (StableDone L K ra.init)
      ≤ Brecover + Bleak
    ∧ ra.P5 ≤ (Phase5Convergence.usefulMains (L := L) (K := K)).sum c5.count
    ∧ (((NonuniformMajority L K).transitionKernel ^ T) ra.c₀
          {c | ¬ majorityStableEndpoint (L := L) (K := K) ra.init c}
        ≤ (21 : ℝ≥0∞) / (n : ℝ≥0∞) ^ 2
      ∧ T ≤ 21 * C0 * n * (L + 1)) :=
  FinalAssemblyV51.doty_theorem_3_1_expected_v51 (C0 := C0) hReg
    (toResidualV51 ra hPost2Win hSeedEvent hWin2Pre) Brecover Bleak βfinal G hDone hDoneAbs
    hOnGood hLeak T hT ht hεw c5 hPhase5 hMainFloor hConf hP5

/-- **`doty_theorem_3_1_expected_v6_numeral`.**  At the LITERAL `C0 = 17`, `Cbad = 3`:
`E[T] ≤ (21·17 + 4·3)·n·(L+1) = 369·n·(L+1)`. -/
theorem doty_theorem_3_1_expected_v6_numeral {n L K : ℕ}
    (hReg : PaperRegime.DotyRegime n L K)
    (ra : DotyResidualAtomsV6 (L := L) (K := K) n AtomsV2.C0_numeral)
    (hPost2Win : ∀ (k : Fin 10) (c : Config (AgentState L K)),
      (workV6 ra ⟨k.val, by omega⟩).Post c →
      SeamEpidemics.allPhaseGe (L := L) (K := K) (ra.seamP k) n c)
    (hSeedEvent : ∀ k : Fin 10,
      SmallSweep.SeedStepEvent (L := L) (K := K) (ra.seamP k)
        ((workV6 ra ⟨k.val, by omega⟩).Post))
    (hWin2Pre : ∀ (k : Fin 10) (c : Config (AgentState L K)),
      SeamEpidemics.allPhaseEq (L := L) (K := K) (ra.seamP k + 1) n c →
      (workV6 ra ⟨k.val + 1, by omega⟩).Pre c)
    (Brecover Bleak : ℝ≥0∞)
    (βfinal : Config (AgentState L K) → ℝ≥0∞)
    (G : Config (AgentState L K) → Prop)
    (hDone : MeasurableSet (StableDone L K ra.init))
    (hDoneAbs : ∀ x ∈ StableDone L K ra.init,
      (NonuniformMajority L K).transitionKernel x (StableDone L K ra.init)ᶜ = 0)
    (hOnGood : OffEventEndgame.OnGoodSlotClassifier (L := L) (K := K) n ra.init Brecover βfinal G)
    (hLeak : ∑' t : ℕ, ((NonuniformMajority L K).transitionKernel ^ t) ra.c₀
        ({b | ¬ (ReachableFrom L K ra.init b ∧ G b)} ∩ (StableDone L K ra.init)ᶜ) ≤ Bleak)
    (T : ℕ)
    (hT : T = ∑ i, (phasesV6 ra hPost2Win hSeedEvent hWin2Pre i).t)
    (ht : ∀ i, (phasesV6 ra hPost2Win hSeedEvent hWin2Pre i).t ≤ ra.Cphase i * n * (L + 1))
    (hεw : ∀ i, ((phasesV6 ra hPost2Win hSeedEvent hWin2Pre i).ε : ℝ≥0∞) ≤ (ra.δ i : ℝ≥0∞))
    (c5 : Config (AgentState L K))
    (hPhase5 : ReserveSampling.Phase5AllWin (L := L) (K := K) n c5)
    (hMainFloor : (n : ℝ) / 3 ≤ (RoleSplitConcentration.mainCount (L := L) (K := K) c5 : ℝ))
    (hConf : MainExponentConfinement.MainProfileConfinedToUseful (L := L) (K := K) c5)
    (hP5 : (ra.P5 : ℝ) ≤ (23 : ℝ) * (n : ℝ) / 75)
    (hBrec : Brecover ≤ ((21 * AtomsV2.C0_numeral * n * (L + 1) : ℕ) : ℝ≥0∞))
    (hBleak : Bleak ≤ ((4 * AtomsV2.Cbad_numeral * n * (L + 1) : ℕ) : ℝ≥0∞)) :
    expectedHitting (NonuniformMajority L K).transitionKernel ra.c₀ (StableDone L K ra.init)
      ≤ (((21 * 17 + 4 * 3) * n * (L + 1) : ℕ) : ℝ≥0∞) :=
  FinalAssemblyV51.doty_theorem_3_1_expected_v51_numeral hReg
    (toResidualV51 ra hPost2Win hSeedEvent hWin2Pre) Brecover Bleak βfinal G hDone hDoneAbs
    hOnGood hLeak T hT ht hεw c5 hPhase5 hMainFloor hConf hP5 hBrec hBleak

/-! ## Part 5 — the V6 CONSUMPTION TABLE.

Every V51 field a package PRODUCES is supplied to the V5.1 bundle by CALLING the package producer in
`toWorkInputsV51` / `toResidualV51` (grep the proof terms).  The V6 residual carries ONLY the
producer-input remainders + carried fields.

### V51 field → package producer → proof-term call site (in `toWorkInputsV51` unless noted)

| V51 field            | package producer                                         | call site |
|----------------------|----------------------------------------------------------|-----------|
| `work0`              | `PkgFAtoms.work0_of_two_stage`                            | `toWorkInputsV51.work0` |
| `work2`              | `PkgFAtoms.work2_calibratedUnion`                        | `toWorkInputsV51.work2` |
| `work3`              | `PkgFAtoms.work3_phase3_bounded`                         | `toWorkInputsV51.work3` |
| `work9`              | `PkgFAtoms.work9_calibratedUnion`                        | `toWorkInputsV51.work9` |
| `hext1H`             | `PkgAAtoms.hext1H_of_extremePos_witness_honest`          | `toWorkInputsV51.hext1H` |
| `hpull1H`            | `PkgAAtoms.hpull1H_of_entry_on_honest`                   | `toWorkInputsV51.hpull1H` (`P1 := (n-g+3)/4`) |
| `hpt1`               | `PkgAAtoms.hpt1_of_rect_calibration`                     | `toWorkInputsV51.hpt1` |
| `hescε1`             | `PkgDAtoms.hescε1_of_tail_fit`                           | `toWorkInputsV51.hescε1` |
| `hmain5`             | `PkgCAtoms.hmain5_of_pointwise_confinement`              | `toWorkInputsV51.hmain5` |
| `hpt5`               | `PkgAAtoms.hpt1_of_rect_calibration` (at `P5`)           | `toWorkInputsV51.hpt5` |
| `hConc`/`εConc`      | `PkgEAtoms.hConc_field_of_atoms_and_widthSurvival`       | `toWorkInputsV51.hConc` |
| `q6`/`hdrop6`/`hpt6`/`hq6zero` | `PkgDAtoms.q6D`/`hdrop6_padded_from_positive`/`hpt6_padded_from_positive`/`hq6zero_padded` | `toWorkInputsV51.{q6,hdrop6,hpt6,hq6zero}` |
| `hescε6`             | `PkgDAtoms.hescε6_of_tail_fit`                           | `toWorkInputsV51.hescε6` |
| `hwit7`              | `PkgBAtoms.hwit7_of_phase6To7Structure_honest`          | `toWorkInputsV51.hwit7` |
| `hpt7`               | `PkgBAtoms.hpt7_budget_alpha`                            | `toWorkInputsV51.hpt7` |
| `hescε7`             | `PkgDAtoms.hescε7_of_tail_fit`                           | `toWorkInputsV51.hescε7` |
| `hwit8`              | `PkgBAtoms.hwit8_of_phase7To8Structure_honest`          | `toWorkInputsV51.hwit8` |
| `hpt8`               | `PkgBAtoms.hpt8_budget_recut`                            | `toWorkInputsV51.hpt8` |
| `hescε8`             | `PkgDAtoms.hescε8_of_tail_fit`                           | `toWorkInputsV51.hescε8` |
| `hSeedStep`          | `PkgFAtoms.hSeedStep_v51_of_event`                       | `toResidualV51.hSeedStep` |
| `hWork0PreOfStart`   | `PkgFAtoms.hWork0PreOfStart_of_work0_eq` (`hwork0 := rfl`)| `toResidualV51.hWork0PreOfStart` |
| `hPhase10Sign`       | `PkgFAtoms.hPhase10Sign_of_rooted`                      | `toResidualV51.hPhase10Sign` |

### Genuinely-open inputs carried in `DotyResidualAtomsV6` (the package remainders)

* Pkg A: `hwit1` (+3 sign witness), `g`/`hentry1` (entry/gap pinned), `α1`/`hM₀1`/`hα01`/`hα11`/`hq01`/`hq1`/`hT1` (slot-1 rectangle calibration), `α5`/… (slot-5 budget calibration).
* Pkg B: `hE7`/`hAll7`/`hStruct7` and `hq07`/`hrate7`/`hTw7` (slot 7); `hE8`/`hAll8`/`hStruct8` and `hq08`/`hrate8`/`hTw8` (slot 8).
* Pkg C: `hP5`/`hMainFloor5`/`hConf5` — the POINTWISE phase-3 confinement at `b` (C's honest residual; the whp kernel event does not yield pointwise `hmain5`).
* Pkg D: `η{1,6,7,8}`/`hescW{1,6,7,8}` (the carried escape probabilities), `hηtail*`/`hfit*` (budget fits), `qpos6`/`hdrop6pos`/`hpt6pos` (positive-level phase-6 drain rate).
* Pkg E: `e5*` (sampled-class atoms) + `e5hwidth` (the slot-5 width/survival export).
* Pkg F: the work-slot constructor inputs `w0*`/`w2*`/`w3*`/`w9*`, the rooted phase-10 entry `hInitValid`/`hAllRoot`/`hActRoot`/`hReach10`, `hStagePre0`; the seed-event family and seam-glue (`hPost2Win`/`hSeedEvent`/`hWin2Pre`) passed as theorem args.
* `hClosed5`: the carried slot-5 closure (Phase 5 = documented non-reset exception, Pkg D remainder).
* `DotyRegime` (`hReg`), the seam half (`hDrift`/`hNoOvershoot`), budget scalars, `hStart`.

## Axiom audit (verified by `#print axioms`)

The four V6 theorems — `doty_theorem_3_1_whp_v6`, `doty_theorem_3_1_whp_numeral_v6`,
`doty_theorem_3_1_expected_v6`, `doty_theorem_3_1_expected_v6_numeral` — depend on exactly
`[propext, Classical.choice, Quot.sound]`.  No `sorry`/`admit`/`axiom`/`native_decide`. -/

end FinalAssemblyV6
end ExactMajority
