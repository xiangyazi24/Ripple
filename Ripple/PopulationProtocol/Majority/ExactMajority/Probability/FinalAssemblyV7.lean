/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# FinalAssemblyV7 — the V7 ASSEMBLY: V6 re-cut with the HONEST A/B producers.

This append-only file is a re-cut of `FinalAssemblyV6`.  It edits NO existing file.  The ONLY change
from V6 is the **slot-1 / slot-7 / slot-8 partner-floor / eliminator-margin wiring**: V6's
`toWorkInputsV51` consumed the AUDITED-DEFECT producers

  * `PkgAAtoms.hpull1H_of_entry_on_honest`   (false all-Main bridge via `PartnerMargin.EntrySumPinned`,
    whose definition bakes in `Phase1AllMain` — globally unsatisfiable on the live chain),
  * `PkgBAtoms.hwit7_of_phase6To7Structure_honest`  (false `Phase7Honest n b → Phase7AllMain n b`),
  * `PkgBAtoms.hwit8_of_phase7To8Structure_honest`  (false `Phase8Honest n b → Phase8AllMain n b`).

V7 replaces those three wires with the HONEST redos from `PkgA2HonestFloor` / `PkgB2HonestMargin`,
which carry NO all-Main bridge anywhere (grep-verifiable — the defect producer names do NOT appear in
any V7 proof term):

  * `hpull1H` ← `PkgA2HonestFloor.hpull1H_of_honestEntry` at the honest floor `P1 = (mc − g + 3)/4`,
    from `Phase1Honest` + `|centredBiasSum| ≤ g` + the chain-carried Main-count floor `mc ≤ mainCount`;
  * `hext1H`  ← `PkgA2HonestFloor.hext1H_of_extremePos_witness` (already honest, re-exported;
    reads only the Main witness `∃ a ∈ b, extremePos a`);
  * `hwit7`   ← `PkgB2HonestMargin.hwit7_honest` from `hMainMass7` (the §6/§7 mass↔Main-minority carry)
    + the carried §6 Post `hStruct7`;
  * `hwit8`   ← `PkgB2HonestMargin.hwit8_honest` from the carried §7 Post `hStruct8` ALONE (ZERO extra).

The new honest inputs `mc`, `g`, `hMainMass7` enter `DotyResidualAtomsV7` as CARRIED residual fields
with paper/chain provenance (each documented below).  The defective bundle fields `hE7`/`hAll7`/`hE8`/
`hAll8` (the all-Main bridge premises the defect producers consumed) are DROPPED — they were used by
NOTHING except the defect producers.

C/D/E/F keep V6's wiring UNCHANGED (they were conditional-honest carries, NOT defects).  For C the
pointwise `hmain5` stays a CARRIED field, doc-commented HONESTLY: it is THE genuine residual — the whp
confinement event does not yield the pointwise `hmain5` (`MainExponentConfinement` /
`ConfinementSurface:36`), so this needs pointwise success at `b` — an OPEN paper-probability gap.  V7
does NOT pretend it is produced.

The V7 theorems `doty_theorem_3_1_whp_v7` / `_expected_v7` + numeral corollaries reach the SAME
conclusions (`≤ 21/n²`, `369·n·(L+1)`) as V6/V5.1 by routing through `toResidualV51` and the landed
V5.1 theorems.

## Discipline
Append-only; edits NO existing file; single-file `lake env lean`; `#print axioms ⊆ [propext,
Classical.choice, Quot.sound]`; no `sorry`/`admit`/`axiom`/`native_decide`.
-/
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.FinalAssemblyV6
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.PkgA2HonestFloor
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.PkgB2HonestMargin

namespace ExactMajority
namespace FinalAssemblyV7

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators NNReal

variable {L K : ℕ}

/-! ## Part 1 — `DotyResidualAtomsV7`: the V6 residual with the HONEST A/B inputs.

Identical to `DotyResidualAtomsV6` EXCEPT:
  * slot 1 — the Pkg-A defect input `hentry1 : … → EntrySumPinned` is replaced by the HONEST entry
    `hHonestEntry1 : … → PkgA2HonestFloor.HonestEntry n g mc b`, and the new chain-carried Main-count
    floor `mc` is added.  The floor scalar is now `P1 := (mc − g + 3)/4` (absolute population count
    DERIVED relative to `mainCount` via `mc`), and the slot-1 rectangle calibration `hq01/hq1` reads
    `qRectReal ((mc − g + 3)/4) n` to match;
  * slot 7 — the Pkg-B defect inputs `hE7`/`hAll7` (the all-Main bridge premises) are DROPPED, and the
    §6/§7 chain carry `hMainMass7 : classMassN σ ≥ 1 → minorityU σ ≥ 1` on the honest window is added;
  * slot 8 — the Pkg-B defect inputs `hE8`/`hAll8` are DROPPED (the honest `hwit8` needs `hStruct8`
    ALONE). -/
structure DotyResidualAtomsV7 (n C0 : ℕ) where
  -- ===== common scalars / regime data =====
  σ : Sign
  M₀ : ℕ
  hn : 2 ≤ n
  hM1 : 1 ≤ M₀
  -- ===== slot 1 — Pkg A2 HONEST producer inputs (REPLACE the defect `hentry1`) =====
  /-- slot-1 entry gap `g`; the honest slot-1 floor is fixed at `P1 := (mc − g + 3) / 4`. -/
  g : ℕ
  /-- Pkg A2 input: the chain-carried Main-count floor `mc ≤ mainCount` on every Phase-1 honest window
  (threaded from `RoleSplitConcentration.RoleSplitGood`, which forces `mainCount ≥ n/3`).  With
  `mc = ⌈n/3⌉` and `g = εn` the honest floor `(mc − g + 3)/4` is `Θ(n)` — paper-faithful
  `q = 1 − Θ(1/n)`. -/
  mc : ℕ
  /-- Pkg A2 remainder: the sharp `+3` sign witness on the honest window (`hext1H` input). -/
  hwit1 : ∀ b : Config (AgentState L K),
    HonestWindows.Phase1Honest (L := L) (K := K) n b → ∃ a ∈ b, DrainThreading.extremePos a
  /-- Pkg A2 remainder: the HONEST Phase-1 entry (`hpull1H` input), NO all-Main bridge.  Carries the
  three chain-honest facts `PkgA2HonestFloor.HonestEntry n g mc b` = phase-only window +
  `|centredBiasSum| ≤ g` (conserved opinion gap) + `mc ≤ mainCount` (chain-carried Main floor). -/
  hHonestEntry1 : ∀ b : Config (AgentState L K),
    HonestWindows.Phase1Honest (L := L) (K := K) n b →
      PkgA2HonestFloor.HonestEntry (L := L) (K := K) n g mc b
  tWin1 : ℕ → ℕ
  /-- Pkg A remainder: the slot-1 rectangle real-fraction calibration data (`hpt1` input), at the
  HONEST floor `(mc − g + 3)/4`. -/
  α1 : ℕ → ℝ
  hM₀1 : (M₀ : ℝ) ≤ n
  hα01 : ∀ m ∈ Finset.Icc 1 M₀, 0 < α1 m
  hα11 : ∀ m ∈ Finset.Icc 1 M₀, α1 m ≤ 1
  hq01 : ∀ m ∈ Finset.Icc 1 M₀, 0 ≤ PkgAAtoms.qRectReal ((mc - g + 3) / 4) n
  hq1 : ∀ m ∈ Finset.Icc 1 M₀,
    PkgAAtoms.qRectReal ((mc - g + 3) / 4) n ≤ 1 - α1 m * (m : ℝ) / n
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
  -- ===== slot 0/2/3/9 — Pkg F constructor inputs (UNCHANGED from V6) =====
  w0stage1 : PhaseConvergenceW (NonuniformMajority L K).transitionKernel
  w0stage15 : PhaseConvergenceW (NonuniformMajority L K).transitionKernel
  w0stage2 : PhaseConvergenceW (NonuniformMajority L K).transitionKernel
  w0chain1 : ∀ x, w0stage1.Post x → w0stage15.Pre x
  w0chain2 : ∀ x, w0stage15.Post x → w0stage2.Pre x
  w2s : ℝ
  w2hs : 0 < w2s
  w2t : ℕ
  w2ε : ℝ≥0
  w2hε : ENNReal.ofReal
      (1 - (((n - 1 : ℕ) : ℝ) / ((n : ℝ) * ((n : ℝ) - 1))) * (1 - Real.exp (-w2s))) ^ w2t *
      ENNReal.ofReal (Real.exp (w2s * ((n : ℝ) - 1))) / 1 ≤ (w2ε : ℝ≥0∞)
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
  w9s : ℝ
  w9hs : 0 < w9s
  w9t : ℕ
  w9ε : ℝ≥0
  w9hε : ENNReal.ofReal
      (1 - (((n - 1 : ℕ) : ℝ) / ((n : ℝ) * ((n : ℝ) - 1))) * (1 - Real.exp (-w9s))) ^ w9t *
      ENNReal.ofReal (Real.exp (w9s * ((n : ℝ) - 1))) / 1 ≤ (w9ε : ℝ≥0∞)
  -- ===== slot 4 — Phase-4 epidemic (carried scalar inputs, UNCHANGED) =====
  s4 : ℝ
  hs4 : 0 < s4
  t4 : ℕ
  ε4 : ℝ≥0
  hε4 : ENNReal.ofReal
          (1 - (((n - 1 : ℕ) : ℝ) / ((n : ℝ) * ((n : ℝ) - 1))) * (1 - Real.exp (-s4))) ^ t4 *
          ENNReal.ofReal (Real.exp (s4 * ((n : ℝ) - 1))) / 1
        ≤ (ε4 : ℝ≥0∞)
  -- ===== slot 5 — Pkg C/E producer inputs + carried closure (UNCHANGED from V6) =====
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
  /-- **THE GENUINE RESIDUAL (Pkg C).**  The pointwise phase-3 confinement event on every Phase-5
  window.  This is CARRIED, not produced: the whp confinement event `⊬` this pointwise `hmain5`
  (`MainExponentConfinement` / `ConfinementSurface:36`); it needs pointwise success at `b` — an OPEN
  paper-probability gap.  V7 does NOT pretend it is produced. -/
  hConf5 : ∀ b : Config (AgentState L K),
    ReserveSampling.Phase5AllWin (L := L) (K := K) n b →
      MainExponentConfinement.MainProfileConfinedToUseful (L := L) (K := K) b
  /-- Pkg A producer for slot-5 budget (same rectangle calibration shape, UNCHANGED). -/
  α5 : ℕ → ℝ
  hα05 : ∀ m ∈ Finset.Icc 1 M₀, 0 < α5 m
  hα15 : ∀ m ∈ Finset.Icc 1 M₀, α5 m ≤ 1
  hq05 : ∀ m ∈ Finset.Icc 1 M₀, 0 ≤ PkgAAtoms.qRectReal P5 n
  hq5 : ∀ m ∈ Finset.Icc 1 M₀,
    PkgAAtoms.qRectReal P5 n ≤ 1 - α5 m * (m : ℝ) / n
  hT5 : ∀ m ∈ Finset.Icc 1 M₀,
    (3 / α5 m) * ((n : ℝ) / (m : ℝ)) * Real.log n ≤ tWin5 m
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
  -- ===== slot 6 — Pkg D padded rate inputs (UNCHANGED from V6) =====
  l : ℕ
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
  -- ===== slot 7 — Pkg B2 HONEST producer inputs (DROP `hE7`/`hAll7`; ADD `hMainMass7`) =====
  E7 : ℕ
  tWin7 : ℕ → ℕ
  /-- Pkg B2 remainder: the §6/§7 mass↔Main-minority carry on the honest window (the surviving σ-class
  MASS `classMassN σ ≥ 1` is Main-carried, i.e. yields a positive Main minority COUNT `minorityU σ ≥ 1`).
  This is the chain-honest replacement for the dropped all-Main bridge `hAll7`; unlike that bridge it
  IS satisfiable on the chain (the audited package buried exactly this content inside the unsatisfiable
  `Phase7AllMain`). -/
  hMainMass7 : ∀ b : Config (AgentState L K),
    HonestWindows.Phase7Honest (L := L) (K := K) n b →
    Phase7Convergence.classMassN σ b ≥ 1 →
    Phase7Convergence.minorityU (L := L) (K := K) σ b ≥ 1
  /-- Pkg B2 remainder: the carried §6 Post `Phase6To7Structure σ E7` on the honest window
  (gap-1 eliminator ≥ E7 at each live minority level). -/
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
  -- ===== slot 8 — Pkg B2 HONEST producer inputs (DROP `hE8`/`hAll8`; `hwit8` needs `hStruct8` ALONE) =====
  E8 : ℕ
  tWin8 : ℕ → ℕ
  /-- Pkg B2 remainder: the carried §7 Post `Phase7To8Structure σ E8` on the honest window
  (above-level survival ≥ E8 at each live minority level).  The honest `hwit8` is keyed directly off
  the Main minority COUNT `minorityU σ ≥ 1`, so it needs NO mass carry — `hStruct8` alone, ZERO extra
  hypothesis (no all-Main bridge). -/
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
  -- ===== slot 10 — Phase-10 block-geometric (carried scalar inputs, UNCHANGED) =====
  s10 : ℕ
  hs10 : 0 < s10
  hsB10 : (3 * (((n ^ 2 : ℕ) : ℝ≥0∞) * ENNReal.ofReal (1 + 2 * Real.log n))) * 2
    ≤ (s10 : ℝ≥0∞)
  k10 : ℕ
  -- ===== seam half (carried — boilerplate, UNCHANGED) =====
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
  c₀ : Config (AgentState L K)
  init : Config (AgentState L K)
  -- ===== budget / config scalars (UNCHANGED) =====
  Cphase : Fin 21 → ℕ
  δ : Fin 21 → ℝ≥0
  hC0 : ∀ i, Cphase i ≤ C0
  hδ : ∀ i, (δ i : ℝ≥0∞) ≤ (1 / (n : ℝ≥0∞) ^ 2)
  -- ===== start / sign — Pkg F producer inputs (UNCHANGED) =====
  hStart : RoleSplitConcentration.Phase0Initial (L := L) (K := K) n c₀
  hStagePre0 : RoleSplitConcentration.Phase0Initial (L := L) (K := K) n c₀ → w0stage1.Pre c₀
  hInitValid : validInitial init
  hAllRoot : ∀ a ∈ init, a.phase.val = 10
  hActRoot : hasActiveAgent init
  hReach10 : ∀ c, Phase10Drop.Phase10Post (L := L) (K := K) c →
    (NonuniformMajority L K).Reachable init c

/-! ## Part 2 — `toWorkInputsV51`: build `WorkInputsV51` by CALLING the producers.

Identical to V6 EXCEPT the slot-1 `hext1H`/`hpull1H` and slot-7/8 `hwit7`/`hwit8` wires, which now
call the HONEST `PkgA2HonestFloor` / `PkgB2HonestMargin` producers.  The defective
`PkgAAtoms.hpull1H_of_entry_on_honest` / `PkgBAtoms.hwit7_…` / `PkgBAtoms.hwit8_…` do NOT appear. -/
noncomputable def toWorkInputsV51 {n C0 : ℕ} (ra : DotyResidualAtomsV7 (L := L) (K := K) n C0) :
    FinalAssemblyV51.WorkInputsV51 (L := L) (K := K) n where
  σ := ra.σ
  M₀ := ra.M₀
  hn := ra.hn
  hM1 := ra.hM1
  -- slots 0/2/3/9 — Pkg F constructors (UNCHANGED from V6)
  work0 := PkgFAtoms.work0_of_two_stage (L := L) (K := K)
    ra.w0stage1 ra.w0stage15 ra.w0stage2 ra.w0chain1 ra.w0chain2
  work2 := PkgFAtoms.work2_calibratedUnion (L := L) (K := K) n ra.hn ra.w2s ra.w2hs ra.w2t ra.w2ε ra.w2hε
  work3 := PkgFAtoms.work3_phase3_bounded (L := L) (K := K) n ra.w3mC ra.hn ra.w3hmC ra.w3hLK ra.w3hLK1
    ra.w3tseed ra.w3tbulk ra.w3htbulk ra.w3εbulk ra.w3hεb ra.w3c₀ ra.w3εside ra.w3hside ra.w3εtot ra.w3hεtot
  work9 := PkgFAtoms.work9_calibratedUnion (L := L) (K := K) n ra.hn ra.w9s ra.w9hs ra.w9t ra.w9ε ra.w9hε
  -- slot 1 — Pkg A2 HONEST producers (floor `P1 = (mc − g + 3)/4`) + Pkg D escape
  P1 := (ra.mc - ra.g + 3) / 4
  tWin1 := ra.tWin1
  η1 := ra.η1
  hescW1 := ra.hescW1
  hext1H := PkgA2HonestFloor.hext1H_of_extremePos_witness (L := L) (K := K) n ra.hwit1
  hpull1H := PkgA2HonestFloor.hpull1H_of_honestEntry (L := L) (K := K) n ra.g ra.mc ra.hHonestEntry1
  hpt1 := PkgAAtoms.hpt1_of_rect_calibration (P1 := (ra.mc - ra.g + 3) / 4) ra.tWin1 ra.α1
    ra.hn ra.hM1 ra.hM₀1 ra.hα01 ra.hα11 ra.hq01 ra.hq1 ra.hT1
  escapeε1 := ra.escapeε1
  hescε1 := PkgDAtoms.hescε1_of_tail_fit ra.c1 ra.L01 ra.M₀ ra.tWin1 ra.η1
    ra.escapeε1 ra.hηtail1 ra.hfit1
  -- slot 4 (UNCHANGED)
  s4 := ra.s4
  hs4 := ra.hs4
  t4 := ra.t4
  ε4 := ra.ε4
  hε4 := ra.hε4
  -- slot 5 — Pkg C `hmain5`, Pkg A budget, Pkg E concentration, carried closure (UNCHANGED from V6)
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
  -- slot 6 — Pkg D padded rate + escape (UNCHANGED from V6)
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
  -- slot 7 — Pkg B2 HONEST producer (NO all-Main bridge) + Pkg D escape
  E7 := ra.E7
  tWin7 := ra.tWin7
  η7 := ra.η7
  hescW7 := ra.hescW7
  hwit7 := PkgB2HonestMargin.hwit7_honest (L := L) (K := K) ra.hMainMass7 ra.hStruct7
  hpt7 := PkgBAtoms.hpt7_budget_alpha ra.tWin7 ra.hn ra.hM1 ra.hM₀1 ra.hq07 ra.hrate7 ra.hTw7
  escapeε7 := ra.escapeε7
  hescε7 := PkgDAtoms.hescε7_of_tail_fit ra.c7 ra.L07 ra.M₀ ra.tWin7 ra.η7
    ra.escapeε7 ra.hηtail7 ra.hfit7
  -- slot 8 — Pkg B2 HONEST producer (NO all-Main bridge, `hStruct8` ALONE) + Pkg D escape
  E8 := ra.E8
  tWin8 := ra.tWin8
  η8 := ra.η8
  hescW8 := ra.hescW8
  hwit8 := PkgB2HonestMargin.hwit8_honest (L := L) (K := K) ra.hStruct8
  hpt8 := PkgBAtoms.hpt8_budget_recut ra.tWin8 ra.hn ra.hM1 ra.hM₀1 ra.hq08 ra.hrate8 ra.hTw8
  escapeε8 := ra.escapeε8
  hescε8 := PkgDAtoms.hescε8_of_tail_fit ra.c8 ra.L08 ra.M₀ ra.tWin8 ra.η8
    ra.escapeε8 ra.hηtail8 ra.hfit8
  -- slot 10 (UNCHANGED)
  s10 := ra.s10
  hs10 := ra.hs10
  hsB10 := ra.hsB10
  k10 := ra.k10

/-- The produced V5.1 work family on the V7 residual. -/
noncomputable abbrev workV7 {n C0 : ℕ} (ra : DotyResidualAtomsV7 (L := L) (K := K) n C0) :
    Fin 11 → PhaseConvergenceW (NonuniformMajority L K).transitionKernel :=
  FinalAssemblyV51.dotyWorkSurvivalV51 (L := L) (K := K) (toWorkInputsV51 ra)

/-! ## Part 3 — `toResidualV51`: build the V5.1 residual from the V7 residual.

Identical to V6: the three seam-glue fields reference the PRODUCED work family `workV7 ra`, so they
are explicit theorem arguments; `hWork0PreOfStart` and `hPhase10Sign` are PRODUCED by Pkg F producers
(both UNCHANGED from V6). -/
noncomputable def toResidualV51 {n C0 : ℕ} (ra : DotyResidualAtomsV7 (L := L) (K := K) n C0)
    (hPost2Win : ∀ (k : Fin 10) (c : Config (AgentState L K)),
      (workV7 ra ⟨k.val, by omega⟩).Post c →
      SeamEpidemics.allPhaseGe (L := L) (K := K) (ra.seamP k) n c)
    (hSeedEvent : ∀ k : Fin 10,
      SmallSweep.SeedStepEvent (L := L) (K := K) (ra.seamP k)
        ((workV7 ra ⟨k.val, by omega⟩).Post))
    (hWin2Pre : ∀ (k : Fin 10) (c : Config (AgentState L K)),
      SeamEpidemics.allPhaseEq (L := L) (K := K) (ra.seamP k + 1) n c →
      (workV7 ra ⟨k.val + 1, by omega⟩).Pre c) :
    FinalAssemblyV51.DotyResidualAtomsV51 (L := L) (K := K) n C0 where
  wi := toWorkInputsV51 ra
  seamP := ra.seamP
  seamT := ra.seamT
  εepidemic := ra.εepidemic
  εovershoot := ra.εovershoot
  hDrift := ra.hDrift
  hNoOvershoot := ra.hNoOvershoot
  hWorkPostToWindow := hPost2Win
  hSeedStep := PkgFAtoms.hSeedStep_v51_of_event (L := L) (K := K) (toWorkInputsV51 ra) ra.seamP hSeedEvent
  hWindowToWorkPre := hWin2Pre
  Cphase := ra.Cphase
  δ := ra.δ
  c₀ := ra.c₀
  init := ra.init
  hC0 := ra.hC0
  hδ := ra.hδ
  hStart := ra.hStart
  hWork0PreOfStart := PkgFAtoms.hWork0PreOfStart_of_work0_eq (L := L) (K := K)
    ra.w0stage1 ra.w0stage15 ra.w0stage2 ra.w0chain1 ra.w0chain2 rfl ra.hStagePre0
  hPhase10Sign := PkgFAtoms.hPhase10Sign_of_rooted (L := L) (K := K)
    ra.hInitValid ra.hAllRoot ra.hActRoot ra.hReach10

/-- The wired 21-instance family on the V7 residual (via the produced V5.1 residual). -/
noncomputable def phasesV7 {n C0 : ℕ} (ra : DotyResidualAtomsV7 (L := L) (K := K) n C0)
    (hPost2Win : ∀ (k : Fin 10) (c : Config (AgentState L K)),
      (workV7 ra ⟨k.val, by omega⟩).Post c →
      SeamEpidemics.allPhaseGe (L := L) (K := K) (ra.seamP k) n c)
    (hSeedEvent : ∀ k : Fin 10,
      SmallSweep.SeedStepEvent (L := L) (K := K) (ra.seamP k)
        ((workV7 ra ⟨k.val, by omega⟩).Post))
    (hWin2Pre : ∀ (k : Fin 10) (c : Config (AgentState L K)),
      SeamEpidemics.allPhaseEq (L := L) (K := K) (ra.seamP k + 1) n c →
      (workV7 ra ⟨k.val + 1, by omega⟩).Pre c) :
    Fin 21 → PhaseConvergenceW (NonuniformMajority L K).transitionKernel :=
  FinalAssemblyV51.phases'V51 (L := L) (K := K) (toResidualV51 ra hPost2Win hSeedEvent hWin2Pre)

/-! ## Part 4 — the V7 theorems.  Same conclusions as V6/V5.1, on the HONEST-A/B bundle. -/

/-- **`doty_theorem_3_1_whp_v7`.**  The whp half on the HONEST-A/B V7 residual: failure `≤ 21/n²`
within `T ≤ 21·C0·n·(L+1)` (and the `clog` form).  Routes through `doty_theorem_3_1_whp_v51` on the
produced `toResidualV51 ra …`; the HONEST producer-supplied V51 fields (`hext1H`/`hpull1H`/`hwit7`/
`hwit8`) appear in the proof term of `toWorkInputsV51` (grep). -/
theorem doty_theorem_3_1_whp_v7 {n L K C0 : ℕ}
    (hReg : PaperRegime.DotyRegime n L K)
    (ra : DotyResidualAtomsV7 (L := L) (K := K) n C0)
    (hPost2Win : ∀ (k : Fin 10) (c : Config (AgentState L K)),
      (workV7 ra ⟨k.val, by omega⟩).Post c →
      SeamEpidemics.allPhaseGe (L := L) (K := K) (ra.seamP k) n c)
    (hSeedEvent : ∀ k : Fin 10,
      SmallSweep.SeedStepEvent (L := L) (K := K) (ra.seamP k)
        ((workV7 ra ⟨k.val, by omega⟩).Post))
    (hWin2Pre : ∀ (k : Fin 10) (c : Config (AgentState L K)),
      SeamEpidemics.allPhaseEq (L := L) (K := K) (ra.seamP k + 1) n c →
      (workV7 ra ⟨k.val + 1, by omega⟩).Pre c)
    (T : ℕ)
    (hT : T = ∑ i, (phasesV7 ra hPost2Win hSeedEvent hWin2Pre i).t)
    (ht : ∀ i, (phasesV7 ra hPost2Win hSeedEvent hWin2Pre i).t ≤ ra.Cphase i * n * (L + 1))
    (hε : ∀ i, ((phasesV7 ra hPost2Win hSeedEvent hWin2Pre i).ε : ℝ≥0∞) ≤ (ra.δ i : ℝ≥0∞)) :
    ((NonuniformMajority L K).transitionKernel ^ T) ra.c₀
        {c | ¬ majorityStableEndpoint (L := L) (K := K) ra.init c}
      ≤ (21 : ℝ≥0∞) / (n : ℝ≥0∞) ^ 2
    ∧ T ≤ 21 * C0 * n * (L + 1)
    ∧ T ≤ 21 * C0 * n * (Nat.clog 2 n + 1) :=
  FinalAssemblyV51.doty_theorem_3_1_whp_v51 (C0 := C0) hReg
    (toResidualV51 ra hPost2Win hSeedEvent hWin2Pre) T hT ht hε

/-- **`doty_theorem_3_1_whp_numeral_v7`.**  At the LITERAL `C0 = 17`. -/
theorem doty_theorem_3_1_whp_numeral_v7 {n L K : ℕ}
    (hReg : PaperRegime.DotyRegime n L K)
    (ra : DotyResidualAtomsV7 (L := L) (K := K) n AtomsV2.C0_numeral)
    (hPost2Win : ∀ (k : Fin 10) (c : Config (AgentState L K)),
      (workV7 ra ⟨k.val, by omega⟩).Post c →
      SeamEpidemics.allPhaseGe (L := L) (K := K) (ra.seamP k) n c)
    (hSeedEvent : ∀ k : Fin 10,
      SmallSweep.SeedStepEvent (L := L) (K := K) (ra.seamP k)
        ((workV7 ra ⟨k.val, by omega⟩).Post))
    (hWin2Pre : ∀ (k : Fin 10) (c : Config (AgentState L K)),
      SeamEpidemics.allPhaseEq (L := L) (K := K) (ra.seamP k + 1) n c →
      (workV7 ra ⟨k.val + 1, by omega⟩).Pre c)
    (T : ℕ)
    (hT : T = ∑ i, (phasesV7 ra hPost2Win hSeedEvent hWin2Pre i).t)
    (ht : ∀ i, (phasesV7 ra hPost2Win hSeedEvent hWin2Pre i).t ≤ ra.Cphase i * n * (L + 1))
    (hε : ∀ i, ((phasesV7 ra hPost2Win hSeedEvent hWin2Pre i).ε : ℝ≥0∞) ≤ (ra.δ i : ℝ≥0∞)) :
    ((NonuniformMajority L K).transitionKernel ^ T) ra.c₀
        {c | ¬ majorityStableEndpoint (L := L) (K := K) ra.init c}
      ≤ (21 : ℝ≥0∞) / (n : ℝ≥0∞) ^ 2
    ∧ T ≤ 21 * AtomsV2.C0_numeral * n * (L + 1)
    ∧ T ≤ 21 * AtomsV2.C0_numeral * n * (Nat.clog 2 n + 1) :=
  doty_theorem_3_1_whp_v7 (C0 := AtomsV2.C0_numeral) hReg ra hPost2Win hSeedEvent hWin2Pre T hT ht hε

/-- **`doty_theorem_3_1_expected_v7`.**  The off-event half on the HONEST-A/B V7 residual: routes
through `doty_theorem_3_1_expected_v51` on `toResidualV51 ra …`. -/
theorem doty_theorem_3_1_expected_v7 {n L K C0 : ℕ}
    (hReg : PaperRegime.DotyRegime n L K)
    (ra : DotyResidualAtomsV7 (L := L) (K := K) n C0)
    (hPost2Win : ∀ (k : Fin 10) (c : Config (AgentState L K)),
      (workV7 ra ⟨k.val, by omega⟩).Post c →
      SeamEpidemics.allPhaseGe (L := L) (K := K) (ra.seamP k) n c)
    (hSeedEvent : ∀ k : Fin 10,
      SmallSweep.SeedStepEvent (L := L) (K := K) (ra.seamP k)
        ((workV7 ra ⟨k.val, by omega⟩).Post))
    (hWin2Pre : ∀ (k : Fin 10) (c : Config (AgentState L K)),
      SeamEpidemics.allPhaseEq (L := L) (K := K) (ra.seamP k + 1) n c →
      (workV7 ra ⟨k.val + 1, by omega⟩).Pre c)
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
    (hT : T = ∑ i, (phasesV7 ra hPost2Win hSeedEvent hWin2Pre i).t)
    (ht : ∀ i, (phasesV7 ra hPost2Win hSeedEvent hWin2Pre i).t ≤ ra.Cphase i * n * (L + 1))
    (hεw : ∀ i, ((phasesV7 ra hPost2Win hSeedEvent hWin2Pre i).ε : ℝ≥0∞) ≤ (ra.δ i : ℝ≥0∞))
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

/-- **`doty_theorem_3_1_expected_v7_numeral`.**  At the LITERAL `C0 = 17`, `Cbad = 3`:
`E[T] ≤ (21·17 + 4·3)·n·(L+1) = 369·n·(L+1)`. -/
theorem doty_theorem_3_1_expected_v7_numeral {n L K : ℕ}
    (hReg : PaperRegime.DotyRegime n L K)
    (ra : DotyResidualAtomsV7 (L := L) (K := K) n AtomsV2.C0_numeral)
    (hPost2Win : ∀ (k : Fin 10) (c : Config (AgentState L K)),
      (workV7 ra ⟨k.val, by omega⟩).Post c →
      SeamEpidemics.allPhaseGe (L := L) (K := K) (ra.seamP k) n c)
    (hSeedEvent : ∀ k : Fin 10,
      SmallSweep.SeedStepEvent (L := L) (K := K) (ra.seamP k)
        ((workV7 ra ⟨k.val, by omega⟩).Post))
    (hWin2Pre : ∀ (k : Fin 10) (c : Config (AgentState L K)),
      SeamEpidemics.allPhaseEq (L := L) (K := K) (ra.seamP k + 1) n c →
      (workV7 ra ⟨k.val + 1, by omega⟩).Pre c)
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
    (hT : T = ∑ i, (phasesV7 ra hPost2Win hSeedEvent hWin2Pre i).t)
    (ht : ∀ i, (phasesV7 ra hPost2Win hSeedEvent hWin2Pre i).t ≤ ra.Cphase i * n * (L + 1))
    (hεw : ∀ i, ((phasesV7 ra hPost2Win hSeedEvent hWin2Pre i).ε : ℝ≥0∞) ≤ (ra.δ i : ℝ≥0∞))
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

/-! ## Part 5 — the V7 CONSUMPTION TABLE.

Every V51 field a package PRODUCES is supplied to the V5.1 bundle by CALLING the package producer in
`toWorkInputsV51` / `toResidualV51` (grep the proof terms).  The V7 residual carries ONLY the
producer-input remainders + carried fields.  The slot-1/7/8 producers are now the **HONEST** redos
(`PkgA2HonestFloor` / `PkgB2HonestMargin`); the false-bridge producers
(`PkgAAtoms.hpull1H_of_entry_on_honest`, `PkgBAtoms.hwit7_of_phase6To7Structure_honest`,
`PkgBAtoms.hwit8_of_phase7To8Structure_honest`) appear in NO V7 proof term (grep-verifiable absent).

### V51 field → package producer → call site → PRODUCED-honest vs CARRIED-residual

| V51 field            | package producer                                         | call site | class |
|----------------------|----------------------------------------------------------|-----------|-------|
| `work0`              | `PkgFAtoms.work0_of_two_stage`                            | `toWorkInputsV51.work0` | PRODUCED |
| `work2`              | `PkgFAtoms.work2_calibratedUnion`                        | `toWorkInputsV51.work2` | PRODUCED |
| `work3`              | `PkgFAtoms.work3_phase3_bounded`                         | `toWorkInputsV51.work3` | PRODUCED |
| `work9`              | `PkgFAtoms.work9_calibratedUnion`                        | `toWorkInputsV51.work9` | PRODUCED |
| `hext1H`             | **`PkgA2HonestFloor.hext1H_of_extremePos_witness`** (HONEST, no bridge) | `toWorkInputsV51.hext1H` | **PRODUCED-honest** |
| `hpull1H`            | **`PkgA2HonestFloor.hpull1H_of_honestEntry`** (HONEST, `P1 := (mc−g+3)/4`) | `toWorkInputsV51.hpull1H` | **PRODUCED-honest** |
| `hpt1`               | `PkgAAtoms.hpt1_of_rect_calibration` (at `(mc−g+3)/4`)   | `toWorkInputsV51.hpt1` | PRODUCED |
| `hescε1`             | `PkgDAtoms.hescε1_of_tail_fit`                           | `toWorkInputsV51.hescε1` | PRODUCED |
| `hmain5`             | `PkgCAtoms.hmain5_of_pointwise_confinement`              | `toWorkInputsV51.hmain5` | PRODUCED (from the CARRIED-residual `hConf5`) |
| `hpt5`               | `PkgAAtoms.hpt1_of_rect_calibration` (at `P5`)           | `toWorkInputsV51.hpt5` | PRODUCED |
| `hConc`/`εConc`      | `PkgEAtoms.hConc_field_of_atoms_and_widthSurvival`       | `toWorkInputsV51.hConc` | PRODUCED |
| `q6`/`hdrop6`/`hpt6`/`hq6zero` | `PkgDAtoms.q6D`/`hdrop6_padded_from_positive`/`hpt6_padded_from_positive`/`hq6zero_padded` | `toWorkInputsV51.{q6,hdrop6,hpt6,hq6zero}` | PRODUCED |
| `hescε6`             | `PkgDAtoms.hescε6_of_tail_fit`                           | `toWorkInputsV51.hescε6` | PRODUCED |
| `hwit7`              | **`PkgB2HonestMargin.hwit7_honest`** (HONEST, no bridge) | `toWorkInputsV51.hwit7` | **PRODUCED-honest** |
| `hpt7`               | `PkgBAtoms.hpt7_budget_alpha` (clean, never all-Main)    | `toWorkInputsV51.hpt7` | PRODUCED |
| `hescε7`             | `PkgDAtoms.hescε7_of_tail_fit`                           | `toWorkInputsV51.hescε7` | PRODUCED |
| `hwit8`              | **`PkgB2HonestMargin.hwit8_honest`** (HONEST, no bridge, `hStruct8` alone) | `toWorkInputsV51.hwit8` | **PRODUCED-honest** |
| `hpt8`               | `PkgBAtoms.hpt8_budget_recut` (clean, never all-Main)    | `toWorkInputsV51.hpt8` | PRODUCED |
| `hescε8`             | `PkgDAtoms.hescε8_of_tail_fit`                           | `toWorkInputsV51.hescε8` | PRODUCED |
| `hSeedStep`          | `PkgFAtoms.hSeedStep_v51_of_event`                       | `toResidualV51.hSeedStep` | PRODUCED |
| `hWork0PreOfStart`   | `PkgFAtoms.hWork0PreOfStart_of_work0_eq` (`hwork0 := rfl`)| `toResidualV51.hWork0PreOfStart` | PRODUCED |
| `hPhase10Sign`       | `PkgFAtoms.hPhase10Sign_of_rooted`                      | `toResidualV51.hPhase10Sign` | PRODUCED |

### CARRIED-residual inputs in `DotyResidualAtomsV7` (the package remainders)

* Pkg A2 (HONEST): `hwit1` (+3 sign witness), `g`/`mc`/`hHonestEntry1` (the HONEST entry — phase-only
  window + conserved gap `g` + chain-carried Main floor `mc ≤ mainCount`, NO all-Main), `α1`/…/`hT1`
  (slot-1 rectangle calibration at `(mc−g+3)/4`), `α5`/… (slot-5 budget calibration).
* Pkg B2 (HONEST): `hMainMass7` (the §6/§7 mass↔Main-minority carry) + `hStruct7` and the slot-7 budget
  comparisons; `hStruct8` ALONE (no `hAll8`, no `hE8`) + the slot-8 budget comparisons.
* **Pkg C — THE GENUINE RESIDUAL:** `hConf5` is CARRIED, not produced — the whp confinement event
  `⊬` the pointwise `hmain5` (`ConfinementSurface:36`); it needs pointwise success at `b`, an OPEN
  paper-probability gap.  (`hP5`/`hMainFloor5` also carried.)
* Pkg D: `η{1,6,7,8}`/`hescW{1,6,7,8}`, `hηtail*`/`hfit*`, `qpos6`/`hdrop6pos`/`hpt6pos`.
* Pkg E: `e5*` + `e5hwidth`.
* Pkg F: `w0*`/`w2*`/`w3*`/`w9*`, `hInitValid`/`hAllRoot`/`hActRoot`/`hReach10`, `hStagePre0`; the
  seed-event family / seam-glue (`hPost2Win`/`hSeedEvent`/`hWin2Pre`) passed as theorem args.
* `hClosed5`: carried slot-5 closure (Phase 5 = documented non-reset exception, Pkg D remainder).
* `DotyRegime` (`hReg`), the seam half (`hDrift`/`hNoOvershoot`), budget scalars, `hStart`.

### DROPPED relative to V6 (the all-Main bridge premises — used by NOTHING but the defect producers)
`hE7`, `hAll7`, `hE8`, `hAll8`.

## False-bridge absence (grep-verifiable)

`PkgAAtoms.hpull1H_of_entry_on_honest`, `PkgAAtoms.hpull1H_of_allMain_and_gap_on_honest`,
`PkgBAtoms.hwit7_of_phase6To7Structure_honest`, `PkgBAtoms.hwit8_of_phase7To8Structure_honest`,
`PartnerMargin.EntrySumPinned`, `Phase7AllMain`, `Phase8AllMain` appear in NO V7 proof term (only in
this documentation as the named DEFECT).

## Axiom audit (verified by `#print axioms`)

The four V7 theorems — `doty_theorem_3_1_whp_v7`, `doty_theorem_3_1_whp_numeral_v7`,
`doty_theorem_3_1_expected_v7`, `doty_theorem_3_1_expected_v7_numeral` — depend on exactly
`[propext, Classical.choice, Quot.sound]`.  No `sorry`/`admit`/`axiom`/`native_decide`. -/

end FinalAssemblyV7
end ExactMajority
