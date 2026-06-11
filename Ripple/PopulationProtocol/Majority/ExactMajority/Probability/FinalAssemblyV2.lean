/-
# FinalAssemblyV2 — the F1+F2+F3-corrected end-to-end Doty Theorem 3.1 whp half.

This file is the re-cut of `FinalAssembly.lean` answering the final adversarial audit
(`/tmp/codex_final_audit.md`).  It fixes three findings, append-only, editing no existing file.

## F1 (CRITICAL) — `hcompFail` PRODUCED, not carried.

`FinalAssembly.doty_theorem_3_1_whp` carried `hcompFail` (the assembled bad-event bound at the sum
horizon) as a FREE binder — tautological, since it is essentially the conclusion.  Here the failure
bound is **produced** from the 21-instance composition itself: `DotyTimeHeadline.doty_time_composition_W2`
applied at the concrete family `phases'V2 ra` delivers `.1` — the failure mass at the LITERAL sum
horizon `∑ i, (phases'V2 ra i).t` — and `hT : T = ∑ …` folds it to the opaque `T` via the safe
rewrite direction (`rw [hT]`, the horizon SUBTERM only; never the divergent re-unification of the
whole kernel-power application against the `Fin 21` sum).  `doty_time_headline_CONCRETE'` itself
ALREADY invokes `doty_time_composition_W2` internally and is landed/axiom-clean, so re-invoking it at
the same concrete family elaborates without divergence (Route a of the documented attack — the
ConcreteAssembly heartbeat wall is on a DIFFERENT unification, not this one).  `hcompFail` is GONE
from `doty_theorem_3_1_whp_v2`.

## F2+F3 — the work family made HONEST (levels engine; the dead per-level inputs put ON the path).

`AssemblyWiring.dotyWorkConcrete` instantiated slots 1/5/7/8 with the CRUDE single-step `potDone`
rate (`DrainCalibration.phase{1,5,7,8}Convergence_calibrated`), which `DrainRates.lean` itself
documents as "structurally vacuous for `Φ ≥ 2`", coinciding with the honest floor only at level
`m = 1`.  The honest per-level machinery was landed but DEAD on the path:
`DrainRates.hdrop{1,5,7,8}_of_chain` (the levels-engine per-level rates), `AssemblyWiring.slot{7,8}_levels_hdrop`
(consuming the eliminator margins `hPhase6Post7`/`hPhase7Post8`).

`dotyWorkHonest` builds slots 1/5/7/8 on `OneSidedCancel.levels_PhaseConvergenceW` (the same engine
Phase 6 uses), consuming the per-level rates + the genuine margins + the per-level budget, with the
SAME `Pre`/`Post` as the crude slots (both engines have `Pre = Inv ∧ Φ ≤ M₀`, `Post = Inv ∧ Φ = 0`),
so every downstream bridge / seam connects unchanged.  `WorkInputsHonest` is the re-cut residual
record: the crude `hstep1/5/7/8` are DROPPED, replaced by the genuinely-probabilistic per-level
inputs the honest instances consume (the structural floors `hext`/`hpull`/`hmain5`, the eliminator
margins `hPhase6Post7`/`hPhase7Post8` — wired through `slot{7,8}_levels_hdrop` — the per-level
budgets `hpt{1,5,7,8}`, and the sampling concentration `hConc`).

## Discipline

Append-only; edits NO existing file.  Single-file `lake env lean` build; `#print axioms` for every
new declaration ⊆ `[propext, Classical.choice, Quot.sound]`; no `sorry`/`admit`/`axiom`/
`native_decide`.
-/
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.SeedTrigWiring
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.PaperRegime
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.DrainRates
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.BudgetTightening

namespace ExactMajority
namespace FinalAssemblyV2

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators NNReal

variable {L K : ℕ}

/-! ## Part 0 — the guarded per-level rate `qHat`.

`levels_PhaseConvergenceW` requires the per-level drop binder `hdrop` at EVERY `m` (including `m = 0`),
but the landed `DrainRates.hdrop{5,7,8}_of_chain` are guarded by `1 ≤ m` (the honest floor is only
defined for a positive active mass).  `qHat E n` is the per-level rate `levelRate E n` capped at `1`
for `m = 0`; since `potBelow Φ 0 = ∅` (every config is "not below 0"), the `m = 0` binder is the
trivial probability bound `K b univ ≤ 1`, and the failure budget — a sum over `Icc 1 M₀` — never sees
`m = 0`, so `qHat` agrees with `levelRate` everywhere the budget reads.  This is the standard
level-engine padding, not a weakening: the honest per-level rate is used at every `m ≥ 1`. -/

/-- The guarded per-level drain rate: `1` at level `0`, the honest `levelRate E n m` at `m ≥ 1`. -/
noncomputable def qHat (E n : ℕ) : ℕ → ℝ≥0∞ :=
  fun m => if 1 ≤ m then DrainRates.levelRate E n m else 1

theorem qHat_eq_on_pos (E n m : ℕ) (hm : 1 ≤ m) : qHat E n m = DrainRates.levelRate E n m := by
  simp [qHat, hm]

theorem qHat_zero (E n : ℕ) : qHat E n 0 = 1 := by simp [qHat]

/-- The `m = 0` binder is trivial: `K b (potBelow Φ 0)ᶜ ≤ 1 = qHat E n 0` (any probability ≤ 1). -/
theorem qHat_zero_bound {α : Type*} [MeasurableSpace α] {Kr : ProbabilityTheory.Kernel α α}
    [IsMarkovKernel Kr] (E n : ℕ) (Φ : α → ℕ) (b : α) :
    Kr b (OneSidedCancel.potBelow Φ 0)ᶜ ≤ qHat E n 0 := by
  rw [qHat_zero]
  exact le_trans (measure_mono (Set.subset_univ _)) (by simp [prob_le_one])

/-- The level-sum budget at `qHat` reduces to `ENNReal.ofReal (1/n²)` via `rect_sum_le_phase_budget`
(the sum is over `Icc 1 M₀`, where `qHat = levelRate`, so the budget calibration applies). -/
theorem qHat_sum_budget {E n M₀ : ℕ} (hn : 2 ≤ n) (hM1 : 1 ≤ M₀) (tWin : ℕ → ℕ)
    (hpt : ∀ m ∈ Finset.Icc 1 M₀, (qHat E n m) ^ (tWin m) ≤ (DrainCalibration.budgetNN M₀ n : ℝ≥0∞)) :
    (∑ m ∈ Finset.Icc 1 M₀, (qHat E n m) ^ (tWin m))
      ≤ ((Real.toNNReal (1 / (n : ℝ) ^ 2) : ℝ≥0) : ℝ≥0∞) := by
  have h := DrainCalibration.rect_sum_le_phase_budget hn hM1 (qHat E n) tWin hpt
  rwa [show ((Real.toNNReal (1 / (n : ℝ) ^ 2) : ℝ≥0) : ℝ≥0∞)
      = ENNReal.ofReal (1 / (n : ℝ) ^ 2) from by rw [ENNReal.ofReal]]

/-! ## Part 1 — the four honest levels-engine slots (1, 5, 7, 8).

Each is `OneSidedCancel.levels_PhaseConvergenceW` over the SAME `Inv`/`Φ` as the crude slot (so the
`Pre = Inv ∧ Φ ≤ M₀`, `Post = Inv ∧ Φ = 0` profile matches the crude family exactly and the bridges
connect), with:
* `hClosed`/`hmono` the PROVED structural inputs (`invClosed_*`/`potNonincrOn_*`);
* `hdrop` the LANDED per-level rate (`DrainRates.hdrop{1,5,7,8}_of_chain`) padded at `m = 0`;
* the per-level budget `hpt` carried (the genuinely-probabilistic geometric-tail input). -/

/-- **Honest slot 1** — `extremeU` averaging drain on the LEVELS engine (Lemma 5.3 / [45]).  Consumes
the per-level rate `DrainRates.hdrop1_of_chain` (from the +3 extreme witness `hext` and the partner
pool floor `hpull`); the crude single-step `potDone` rate is GONE. -/
noncomputable def slot1Honest {n : ℕ} (P1 M₀ : ℕ) (hn : 2 ≤ n) (hM1 : 1 ≤ M₀)
    (hext : ∀ b : Config (AgentState L K), Phase1Convergence.Phase1AllMain n b →
      1 ≤ (DrainThreading.extremePosSet L K).sum b.count)
    (hpull : ∀ b : Config (AgentState L K), Phase1Convergence.Phase1AllMain n b →
      P1 ≤ (DrainThreading.pullPosSet L K).sum b.count)
    (tWin1 : ℕ → ℕ)
    (hpt1 : ∀ m ∈ Finset.Icc 1 M₀, (qHat P1 n m) ^ (tWin1 m) ≤ (DrainCalibration.budgetNN M₀ n : ℝ≥0∞)) :
    PhaseConvergenceW (NonuniformMajority L K).transitionKernel :=
  OneSidedCancel.levels_PhaseConvergenceW
    (NonuniformMajority L K).transitionKernel
    (fun c => Phase1Convergence.Phase1AllMain (L := L) (K := K) n c)
    (Phase1Convergence.invClosed_phase1AllMain n)
    (fun c => Phase1Convergence.extremeU c)
    (Phase1Convergence.potNonincrOn_extremeU n)
    (qHat P1 n)
    (by
      intro m b hInv hbm
      rcases Nat.eq_zero_or_pos m with hm0 | hmpos
      · subst hm0; exact qHat_zero_bound _ _ _ _
      · rw [qHat_eq_on_pos _ _ _ hmpos]
        exact DrainRates.hdrop1_of_chain hn P1 hext hpull m b hInv hbm)
    tWin1 M₀ (Real.toNNReal (1 / (n : ℝ) ^ 2)) (qHat_sum_budget hn hM1 tWin1 hpt1)

/-- The slot-7 per-level drop floor from the eliminator margin, INLINED (replicates
`AssemblyWiring.slot7_levels_hdrop` without a `WorkInputs` wrapper, so the margin field is consumed
directly).  At any `Inv7Sum` config with `classMassN σ = m ≥ 1`, the gap-1 eliminator margin
`hPhase6Post7` gives the per-level drop floor `≤ levelRate E7 n m`. -/
theorem slot7_hdrop_direct {n : ℕ} (σ : Sign) (E7 : ℕ) (hn : 2 ≤ n)
    (hE7 : (E7 : ℝ) ≤ (4 : ℝ) * (n : ℝ) / 15)
    (hPhase6Post7 : ∀ b : Config (AgentState L K),
      Phase7Convergence.Inv7Sum (L := L) (K := K) n b →
      EliminatorMargins.Phase6To7Structure (L := L) (K := K) σ E7 b)
    {m : ℕ} (hmpos : 1 ≤ m) (b : Config (AgentState L K))
    (hInv : Phase7Convergence.Inv7Sum n b) (hbm : Phase7Convergence.classMassN σ b = m) :
    (NonuniformMajority L K).transitionKernel b
        (OneSidedCancel.potBelow (Phase7Convergence.classMassN σ) m)ᶜ
      ≤ DrainRates.levelRate E7 n m := by
  have hb7 : Phase7Convergence.Phase7AllMain (L := L) (K := K) n b := hInv.1
  have hmass : 1 ≤ Phase7Convergence.classMassN σ b := by omega
  have hfloor :
      ∃ i j : Fin (L + 1),
        i.val + 1 = j.val ∧
        1 ≤ (Phase7Convergence.minorityAt7 (L := L) (K := K) σ j).sum b.count ∧
        E7 ≤ (Phase7Convergence.elimGap1 (L := L) (K := K) σ i).sum b.count :=
    EliminatorMargins.lemma7_4_phase7_elimGap1_floor σ hb7 E7 (hPhase6Post7 b hInv) hmass hE7
  exact EliminatorMargins.phase7_hdrop_wired_from_lemma7_4 σ n m hn b hb7 hbm hmpos E7 hfloor

/-- The slot-8 per-level drop floor from the above-level eliminator margin, INLINED (replicates
`AssemblyWiring.slot8_levels_hdrop`). -/
theorem slot8_hdrop_direct {n : ℕ} (σ : Sign) (E8 : ℕ) (hn : 2 ≤ n)
    (hE8 : (E8 : ℝ) ≤ (1 : ℝ) * (n : ℝ) / 5)
    (hPhase7Post8 : ∀ b : Config (AgentState L K),
      Phase8Convergence.Phase8AllMain (L := L) (K := K) n b →
      EliminatorMargins.Phase7To8Structure (L := L) (K := K) σ E8 b)
    {m : ℕ} (hmpos : 1 ≤ m) (b : Config (AgentState L K))
    (hb8 : Phase8Convergence.Phase8AllMain n b) (hbm : Phase7Convergence.minorityU σ b = m) :
    (NonuniformMajority L K).transitionKernel b
        (OneSidedCancel.potBelow (Phase7Convergence.minorityU σ) m)ᶜ
      ≤ DrainRates.levelRate E8 n m := by
  have hmin : 1 ≤ Phase7Convergence.minorityU σ b := by omega
  have hexists :
      ∃ i : Fin (L + 1),
        1 ≤ (Phase8Convergence.minorityAt (L := L) (K := K) σ i).sum b.count ∧
        E8 ≤ (Phase8Convergence.elimAbove (L := L) (K := K) σ i).sum b.count := by
    obtain ⟨i, hmini⟩ := EliminatorMargins.exists_minorityAt_of_minorityU_pos σ b hmin
    exact ⟨i, hmini, EliminatorMargins.lemma7_6_phase8_elimAbove_floor σ hb8 E8
      (hPhase7Post8 b hb8) i hmini hE8⟩
  exact EliminatorMargins.phase8_hdrop_wired_from_lemma7_6 σ n m hn b hb8 hbm hmpos E8 hexists

/-- **Honest slot 7** — `classMassN` eliminator drain on the LEVELS engine (Doty Lemma 7.4).  Consumes
the gap-1 eliminator margin `hPhase6Post7` directly (the PROVED minority witness is inside
`slot7_hdrop_direct`).  The crude `hstep7` rate is GONE; the eliminator margin is now ON the proof
path. -/
noncomputable def slot7Honest {n : ℕ} (σ : Sign) (E7 M₀ : ℕ) (hn : 2 ≤ n) (hM1 : 1 ≤ M₀)
    (hE7 : (E7 : ℝ) ≤ (4 : ℝ) * (n : ℝ) / 15)
    (hPhase6Post7 : ∀ b : Config (AgentState L K),
      Phase7Convergence.Inv7Sum (L := L) (K := K) n b →
      EliminatorMargins.Phase6To7Structure (L := L) (K := K) σ E7 b)
    (tWin7 : ℕ → ℕ)
    (hpt7 : ∀ m ∈ Finset.Icc 1 M₀, (qHat E7 n m) ^ (tWin7 m) ≤ (DrainCalibration.budgetNN M₀ n : ℝ≥0∞)) :
    PhaseConvergenceW (NonuniformMajority L K).transitionKernel :=
  OneSidedCancel.levels_PhaseConvergenceW
    (NonuniformMajority L K).transitionKernel
    (fun c => Phase7Convergence.Inv7Sum (L := L) (K := K) n c)
    (Phase7Convergence.invClosed_Inv7Sum n)
    (fun c => Phase7Convergence.classMassN σ c)
    (Phase7Convergence.potNonincrOn_classMassN σ n)
    (qHat E7 n)
    (by
      intro m b hInv hbm
      rcases Nat.eq_zero_or_pos m with hm0 | hmpos
      · subst hm0; exact qHat_zero_bound _ _ _ _
      · rw [qHat_eq_on_pos _ _ _ hmpos]
        exact slot7_hdrop_direct σ E7 hn hE7 hPhase6Post7 hmpos b hInv hbm)
    tWin7 M₀ (Real.toNNReal (1 / (n : ℝ) ^ 2)) (qHat_sum_budget hn hM1 tWin7 hpt7)

/-- **Honest slot 8** — `minorityU` eliminator drain on the LEVELS engine (Doty Lemma 7.6).  Consumes
the above-level eliminator margin `hPhase7Post8` directly.  The crude `hstep8` rate is GONE; the
margin is ON the proof path. -/
noncomputable def slot8Honest {n : ℕ} (σ : Sign) (E8 M₀ : ℕ) (hn : 2 ≤ n) (hM1 : 1 ≤ M₀)
    (hE8 : (E8 : ℝ) ≤ (1 : ℝ) * (n : ℝ) / 5)
    (hPhase7Post8 : ∀ b : Config (AgentState L K),
      Phase8Convergence.Phase8AllMain (L := L) (K := K) n b →
      EliminatorMargins.Phase7To8Structure (L := L) (K := K) σ E8 b)
    (tWin8 : ℕ → ℕ)
    (hpt8 : ∀ m ∈ Finset.Icc 1 M₀, (qHat E8 n m) ^ (tWin8 m) ≤ (DrainCalibration.budgetNN M₀ n : ℝ≥0∞)) :
    PhaseConvergenceW (NonuniformMajority L K).transitionKernel :=
  OneSidedCancel.levels_PhaseConvergenceW
    (NonuniformMajority L K).transitionKernel
    (fun c => Phase8Convergence.Phase8AllMain (L := L) (K := K) n c)
    (Phase8Convergence.invClosed_phase8AllMain n)
    (fun c => Phase7Convergence.minorityU σ c)
    (Phase8Convergence.potNonincrOn_minorityU σ n)
    (qHat E8 n)
    (by
      intro m b hInv hbm
      rcases Nat.eq_zero_or_pos m with hm0 | hmpos
      · subst hm0; exact qHat_zero_bound _ _ _ _
      · rw [qHat_eq_on_pos _ _ _ hmpos]
        exact slot8_hdrop_direct σ E8 hn hE8 hPhase7Post8 hmpos b hInv hbm)
    tWin8 M₀ (Real.toNNReal (1 / (n : ℝ) ^ 2)) (qHat_sum_budget hn hM1 tWin8 hpt8)

/-! ## Part 2 — the honest slot 5 (levels drain ∘ sampling concentration).

Slot 5 is the composite drain (`unsampledReserveU → 0`) ∩ concentration (`sampledFloor`).  The honest
build replaces the crude drain (`ReserveSampling.phase5SampledConvergence`, crude `potDone`) with the
LEVELS drain on `unsampledReserveU` (consuming `DrainRates.hdrop5_of_chain`), then composes with the
carried sampling concentration `hConc` at the levels horizon `∑ tWin5 m` — mirroring
`Phase5Convergence.phase5Convergence`, with the same `Pre`/`Post` profile
(`Pre = Phase5AllWin ∧ unsampledReserveU ≤ M₀`, `Post = Phase5AllWin ∧ ReserveSampleGood`). -/

/-- The honest levels drain for `unsampledReserveU` (slot-5 drain half), consuming
`DrainRates.hdrop5_of_chain` (the biased-Main floor `hmain5`).  Post `= Phase5AllWin ∧
unsampledReserveU = 0 = ReserveSampled`. -/
noncomputable def slot5DrainLevels {n : ℕ} (P5 M₀ : ℕ)
    (hClosed5 : OneSidedCancel.InvClosed (NonuniformMajority L K).transitionKernel
      (fun c => ReserveSampling.Phase5AllWin (L := L) (K := K) n c))
    (hn : 2 ≤ n) (hM1 : 1 ≤ M₀)
    (hmain5 : ∀ b : Config (AgentState L K), ReserveSampling.Phase5AllWin (L := L) (K := K) n b →
      P5 ≤ (Phase5Convergence.usefulMains (L := L) (K := K)).sum b.count)
    (tWin5 : ℕ → ℕ)
    (hpt5 : ∀ m ∈ Finset.Icc 1 M₀, (qHat P5 n m) ^ (tWin5 m) ≤ (DrainCalibration.budgetNN M₀ n : ℝ≥0∞)) :
    PhaseConvergenceW (NonuniformMajority L K).transitionKernel :=
  OneSidedCancel.levels_PhaseConvergenceW
    (NonuniformMajority L K).transitionKernel
    (fun c => ReserveSampling.Phase5AllWin (L := L) (K := K) n c)
    hClosed5
    (fun c => ReserveSampling.unsampledReserveU (L := L) (K := K) c)
    (ReserveSampling.potNonincrOn_unsampledReserveU n)
    (qHat P5 n)
    (by
      intro m b hInv hbm
      rcases Nat.eq_zero_or_pos m with hm0 | hmpos
      · subst hm0; exact qHat_zero_bound _ _ _ _
      · rw [qHat_eq_on_pos _ _ _ hmpos]
        exact DrainRates.hdrop5_of_chain hn P5 hmain5 m hmpos b hInv hbm)
    tWin5 M₀ (Real.toNNReal (1 / (n : ℝ) ^ 2)) (qHat_sum_budget hn hM1 tWin5 hpt5)

/-- **Honest slot 5** — the levels drain composed with the sampling concentration `hConc` (Lemma 7.1)
at the levels horizon `∑ tWin5 m`.  `Pre = Phase5AllWin ∧ unsampledReserveU ≤ M₀`,
`Post = Phase5AllWin ∧ ReserveSampleGood i5 K₀`.  The crude reserve-drain rate `hstep5` is GONE. -/
noncomputable def slot5Honest {n : ℕ} (i5 : Fin (L + 1)) (K₀ M₀ P5 : ℕ)
    (hClosed5 : OneSidedCancel.InvClosed (NonuniformMajority L K).transitionKernel
      (fun c => ReserveSampling.Phase5AllWin (L := L) (K := K) n c))
    (hn : 2 ≤ n) (hM1 : 1 ≤ M₀)
    (hmain5 : ∀ b : Config (AgentState L K), ReserveSampling.Phase5AllWin (L := L) (K := K) n b →
      P5 ≤ (Phase5Convergence.usefulMains (L := L) (K := K)).sum b.count)
    (tWin5 : ℕ → ℕ)
    (hpt5 : ∀ m ∈ Finset.Icc 1 M₀, (qHat P5 n m) ^ (tWin5 m) ≤ (DrainCalibration.budgetNN M₀ n : ℝ≥0∞))
    (εConc : ℝ≥0)
    (hConc : ∀ c₀, ReserveSampling.Phase5AllWin (L := L) (K := K) n c₀ →
      ReserveSampling.unsampledReserveU (L := L) (K := K) c₀ ≤ M₀ →
      ((NonuniformMajority L K).transitionKernel ^ (∑ m ∈ Finset.Icc 1 M₀, tWin5 m)) c₀
        {c | ¬ Phase5Convergence.sampledFloor (L := L) (K := K) i5 K₀ c} ≤ (εConc : ℝ≥0∞)) :
    PhaseConvergenceW (NonuniformMajority L K).transitionKernel where
  Pre c := ReserveSampling.Phase5AllWin (L := L) (K := K) n c ∧
    ReserveSampling.unsampledReserveU (L := L) (K := K) c ≤ M₀
  Post c := ReserveSampling.Phase5AllWin (L := L) (K := K) n c ∧
    Phase5Convergence.ReserveSampleGood (L := L) (K := K) i5 K₀ c
  t := ∑ m ∈ Finset.Icc 1 M₀, tWin5 m
  ε := Real.toNNReal (1 / (n : ℝ) ^ 2) + εConc
  convergence := by
    intro c₀ hPre
    obtain ⟨hwin, hbud⟩ := hPre
    set P5d := slot5DrainLevels P5 M₀ hClosed5 hn hM1 hmain5 tWin5 hpt5 with hP5d
    have hsampled := P5d.convergence c₀ ⟨hwin, hbud⟩
    have hcover : {c : Config (AgentState L K) |
        ¬ (ReserveSampling.Phase5AllWin (L := L) (K := K) n c ∧
            Phase5Convergence.ReserveSampleGood (L := L) (K := K) i5 K₀ c)}
          ⊆ {c | ¬ P5d.Post c} ∪ {c | ¬ Phase5Convergence.sampledFloor (L := L) (K := K) i5 K₀ c} := by
      intro c hc
      simp only [Set.mem_setOf_eq, Set.mem_union] at hc ⊢
      by_cases hfloor : Phase5Convergence.sampledFloor (L := L) (K := K) i5 K₀ c
      · left; intro hContra
        exact hc ⟨hContra.1, hContra.2, hfloor⟩
      · exact Or.inr hfloor
    calc ((NonuniformMajority L K).transitionKernel ^ (∑ m ∈ Finset.Icc 1 M₀, tWin5 m)) c₀
            {c | ¬ (ReserveSampling.Phase5AllWin (L := L) (K := K) n c ∧
              Phase5Convergence.ReserveSampleGood (L := L) (K := K) i5 K₀ c)}
        ≤ ((NonuniformMajority L K).transitionKernel ^ (∑ m ∈ Finset.Icc 1 M₀, tWin5 m)) c₀
            ({c | ¬ P5d.Post c} ∪ {c | ¬ Phase5Convergence.sampledFloor (L := L) (K := K) i5 K₀ c}) :=
          measure_mono hcover
      _ ≤ ((NonuniformMajority L K).transitionKernel ^ (∑ m ∈ Finset.Icc 1 M₀, tWin5 m)) c₀
            {c | ¬ P5d.Post c}
          + ((NonuniformMajority L K).transitionKernel ^ (∑ m ∈ Finset.Icc 1 M₀, tWin5 m)) c₀
            {c | ¬ Phase5Convergence.sampledFloor (L := L) (K := K) i5 K₀ c} := measure_union_le _ _
      _ ≤ (Real.toNNReal (1 / (n : ℝ) ^ 2) : ℝ≥0∞) + (εConc : ℝ≥0∞) := by
          gcongr
          · exact hsampled
          · exact hConc c₀ hwin hbud
      _ = ((Real.toNNReal (1 / (n : ℝ) ^ 2) + εConc : ℝ≥0) : ℝ≥0∞) := by rw [ENNReal.coe_add]

/-! ## Part 3 — `WorkInputsHonest`: the F2/F3 re-cut residual record.

The crude `hstep1/5/7/8` fields of `AssemblyWiring.WorkInputs` are DROPPED.  In their place are the
genuinely-probabilistic per-level inputs the honest instances consume: the structural floors
(`hext1`/`hpull1`/`hmain5`), the eliminator margins (`hPhase6Post7`/`hPhase7Post8`, threaded through
`slot{7,8}_levels_hdrop`), the per-level budgets (`hpt1/5/7/8`), and the sampling concentration
(`hConc`).  The structural slots (0/2/3/4/6/9/10) are carried exactly as in `WorkInputs`. -/
structure WorkInputsHonest (n : ℕ) where
  /-- The dyadic minority sign. -/
  σ : Sign
  /-- The Phase-5 sampled reserve hour. -/
  i5 : Fin (L + 1)
  /-- The Phase-5/6 sampled-reserve floor `K₀`. -/
  K₀ : ℕ
  /-- The Phase-6 band level `l`. -/
  l : ℕ
  /-- The Phase-7 eliminator-margin count `E7` (Lemma 7.4). -/
  E7 : ℕ
  /-- The Phase-8 above-level eliminator-margin count `E8` (Lemma 7.6). -/
  E8 : ℕ
  /-- Common budget level `M₀`. -/
  M₀ : ℕ
  hn : 2 ≤ n
  hM1 : 1 ≤ M₀
  hM₀ : (M₀ : ℝ) ≤ n
  -- slot 0 / 2 / 3 / 9 — carried finished instances (unchanged from `WorkInputs`).
  work0 : PhaseConvergenceW (NonuniformMajority L K).transitionKernel
  work2 : PhaseConvergenceW (NonuniformMajority L K).transitionKernel
  work3 : PhaseConvergenceW (NonuniformMajority L K).transitionKernel
  work9 : PhaseConvergenceW (NonuniformMajority L K).transitionKernel
  -- slot 1 — HONEST levels inputs (crude `hstep1` DROPPED).
  /-- slot-1 partner-pool floor `P1 ≤ pullPos`. -/
  P1 : ℕ
  tWin1 : ℕ → ℕ
  /-- slot-1 structural floor: `≥ 1` saturated extreme on every in-window config (PERSISTENCE-carried). -/
  hext1 : ∀ b : Config (AgentState L K), Phase1Convergence.Phase1AllMain n b →
    1 ≤ (DrainThreading.extremePosSet L K).sum b.count
  /-- slot-1 partner-pool floor `P1 ≤ pullPos` (Lemma 5.3 / [45]; PERSISTENCE-carried). -/
  hpull1 : ∀ b : Config (AgentState L K), Phase1Convergence.Phase1AllMain n b →
    P1 ≤ (DrainThreading.pullPosSet L K).sum b.count
  /-- slot-1 per-level geometric-tail budget. -/
  hpt1 : ∀ m ∈ Finset.Icc 1 M₀, (qHat P1 n m) ^ (tWin1 m) ≤ (DrainCalibration.budgetNN M₀ n : ℝ≥0∞)
  -- slot 4 — Phase-4 epidemic (carried scalar inputs, unchanged).
  s4 : ℝ
  hs4 : 0 < s4
  t4 : ℕ
  ε4 : ℝ≥0
  hε4 : ENNReal.ofReal
          (1 - (((n - 1 : ℕ) : ℝ) / ((n : ℝ) * ((n : ℝ) - 1))) * (1 - Real.exp (-s4))) ^ t4 *
          ENNReal.ofReal (Real.exp (s4 * ((n : ℝ) - 1))) / 1
        ≤ (ε4 : ℝ≥0∞)
  -- slot 5 — HONEST levels drain + concentration (crude `hstep5` DROPPED).
  /-- slot-5 biased-Main floor `P5 ≤ usefulMains` (Theorem 6.2 biased structure). -/
  P5 : ℕ
  tWin5 : ℕ → ℕ
  hClosed5 : OneSidedCancel.InvClosed (NonuniformMajority L K).transitionKernel
    (fun c => ReserveSampling.Phase5AllWin (L := L) (K := K) n c)
  /-- slot-5 biased-Main floor (PERSISTENCE-carried; Theorem 6.2). -/
  hmain5 : ∀ b : Config (AgentState L K), ReserveSampling.Phase5AllWin (L := L) (K := K) n b →
    P5 ≤ (Phase5Convergence.usefulMains (L := L) (K := K)).sum b.count
  /-- slot-5 per-level geometric-tail budget. -/
  hpt5 : ∀ m ∈ Finset.Icc 1 M₀, (qHat P5 n m) ^ (tWin5 m) ≤ (DrainCalibration.budgetNN M₀ n : ℝ≥0∞)
  /-- slot-5 sampling-concentration budget `εConc` (Lemma 7.1). -/
  εConc : ℝ≥0
  /-- slot-5 sampling concentration at the LEVELS horizon `∑ tWin5 m` (Lemma 7.1). -/
  hConc : ∀ c₀, ReserveSampling.Phase5AllWin (L := L) (K := K) n c₀ →
    ReserveSampling.unsampledReserveU (L := L) (K := K) c₀ ≤ M₀ →
    ((NonuniformMajority L K).transitionKernel ^ (∑ m ∈ Finset.Icc 1 M₀, tWin5 m)) c₀
      {c | ¬ Phase5Convergence.sampledFloor (L := L) (K := K) i5 K₀ c} ≤ (εConc : ℝ≥0∞)
  -- slot 6 — Phase-6 band drain (levels engine; carried as in `WorkInputs`).
  q6 : ℕ → ℝ≥0∞
  tWin6 : ℕ → ℕ
  hClosed6 : OneSidedCancel.InvClosed (NonuniformMajority L K).transitionKernel
    (fun c => Phase6Convergence.Phase6Win (L := L) (K := K) n c)
  hdrop6 : ∀ m, ∀ b : Config (AgentState L K),
    Phase6Convergence.Phase6Win (L := L) (K := K) n b →
    Phase6Convergence.highMass (L := L) (K := K) l b = m →
    (NonuniformMajority L K).transitionKernel b
      (OneSidedCancel.potBelow
        (fun c => Phase6Convergence.highMass (L := L) (K := K) l c) m)ᶜ ≤ q6 m
  hpt6 : ∀ m ∈ Finset.Icc 1 M₀, (q6 m) ^ (tWin6 m) ≤ (DrainCalibration.budgetNN M₀ n : ℝ≥0∞)
  -- slot 7 — HONEST levels eliminator drain (crude `hstep7` DROPPED; margin ON the path).
  tWin7 : ℕ → ℕ
  /-- slot-7 eliminator-margin (Lemma 7.4 `Phase6To7Structure`); PERSISTENCE-carried, consumed by
  `slot7_levels_hdrop` (minority witness PROVED). -/
  hPhase6Post7 : ∀ b : Config (AgentState L K),
    Phase7Convergence.Inv7Sum (L := L) (K := K) n b →
    EliminatorMargins.Phase6To7Structure (L := L) (K := K) σ E7 b
  hE7 : (E7 : ℝ) ≤ (4 : ℝ) * (n : ℝ) / 15
  hpt7 : ∀ m ∈ Finset.Icc 1 M₀, (qHat E7 n m) ^ (tWin7 m) ≤ (DrainCalibration.budgetNN M₀ n : ℝ≥0∞)
  -- slot 8 — HONEST levels eliminator drain (crude `hstep8` DROPPED; margin ON the path).
  tWin8 : ℕ → ℕ
  /-- slot-8 above-level eliminator-margin (Lemma 7.6 `Phase7To8Structure`); PERSISTENCE-carried,
  consumed by `slot8_levels_hdrop`. -/
  hPhase7Post8 : ∀ b : Config (AgentState L K),
    Phase8Convergence.Phase8AllMain (L := L) (K := K) n b →
    EliminatorMargins.Phase7To8Structure (L := L) (K := K) σ E8 b
  hE8 : (E8 : ℝ) ≤ (1 : ℝ) * (n : ℝ) / 5
  hpt8 : ∀ m ∈ Finset.Icc 1 M₀, (qHat E8 n m) ^ (tWin8 m) ≤ (DrainCalibration.budgetNN M₀ n : ℝ≥0∞)
  -- slot 10 — Phase-10 block-geometric (carried scalar inputs, unchanged).
  s10 : ℕ
  hs10 : 0 < s10
  hsB10 : (3 * (((n ^ 2 : ℕ) : ℝ≥0∞) * ENNReal.ofReal (1 + 2 * Real.log n))) * 2
    ≤ (s10 : ℝ≥0∞)
  k10 : ℕ

/-! ## Part 4 — the honest work family `dotyWorkHonest`. -/

/-- **The honest WORK family** `Fin 11 → PhaseConvergenceW`.  Slots 1/5/7/8 are on the LEVELS engine
(consuming the per-level rates + the eliminator margins + the per-level budgets); slots 0/2/3/4/6/9/10
are exactly as in `dotyWorkConcrete`.  Pre/Post per slot match the crude family, so all bridges
connect. -/
noncomputable def dotyWorkHonest {n : ℕ} (wi : WorkInputsHonest (L := L) (K := K) n) :
    Fin 11 → PhaseConvergenceW (NonuniformMajority L K).transitionKernel :=
  fun k =>
    match k with
    | ⟨0, _⟩ => wi.work0
    | ⟨1, _⟩ => slot1Honest wi.P1 wi.M₀ wi.hn wi.hM1 wi.hext1 wi.hpull1 wi.tWin1 wi.hpt1
    | ⟨2, _⟩ => wi.work2
    | ⟨3, _⟩ => wi.work3
    | ⟨4, _⟩ =>
        Phase4Convergence.phase4Convergence (L := L) (K := K) n wi.hn wi.s4 wi.hs4 wi.t4 wi.ε4 wi.hε4
    | ⟨5, _⟩ =>
        slot5Honest wi.i5 wi.K₀ wi.M₀ wi.P5 wi.hClosed5 wi.hn wi.hM1 wi.hmain5 wi.tWin5 wi.hpt5
          wi.εConc wi.hConc
    | ⟨6, _⟩ =>
        DrainCalibration.phase6Convergence_calibrated (L := L) (K := K) wi.l n wi.M₀ wi.q6 wi.tWin6
          wi.hClosed6 wi.hdrop6 wi.hn wi.hM1 wi.hpt6
    | ⟨7, _⟩ =>
        slot7Honest wi.σ wi.E7 wi.M₀ wi.hn wi.hM1 wi.hE7 wi.hPhase6Post7 wi.tWin7 wi.hpt7
    | ⟨8, _⟩ =>
        slot8Honest wi.σ wi.E8 wi.M₀ wi.hn wi.hM1 wi.hE8 wi.hPhase7Post8 wi.tWin8 wi.hpt8
    | ⟨9, _⟩ => wi.work9
    | ⟨10, _⟩ =>
        Phase10Drop.phase10Convergence (L := L) (K := K) n wi.hn wi.s10 wi.hs10 wi.hsB10 wi.k10

/-! ## Part 5 — `DotyResidualAtomsV2`: the V2 residual bundle (bridges over `dotyWorkHonest`). -/

/-- **The V2 residual atom list.**  Same surface as `FinalAssembly.DotyResidualAtoms`, but the work
family is the HONEST `dotyWorkHonest wih` (slots 1/5/7/8 on the levels engine) and the crude
`hstep1/5/7/8` are gone (they live nowhere — `WorkInputsHonest` dropped them).  The seam feeders /
bridges / one-step seed are carried over `dotyWorkHonest`. -/
structure DotyResidualAtomsV2 (n C0 : ℕ) where
  /-- The honest WORK-slot residual record (levels engine on 1/5/7/8). -/
  wih : WorkInputsHonest (L := L) (K := K) n
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
      (dotyWorkHonest wih ⟨k.val, by omega⟩).Post c →
      SeamEpidemics.allPhaseGe (L := L) (K := K) (seamP k) n c
  hSeedStep : ∀ (k : Fin 10) (c : Config (AgentState L K)),
      (dotyWorkHonest wih ⟨k.val, by omega⟩).Post c →
      ((NonuniformMajority L K).transitionKernel ^ 1) c
          {c' | ¬ SeamEpidemics.advTriggered (L := L) (K := K) (seamP k + 1) c'} = 0
  hWindowToWorkPre : ∀ (k : Fin 10) (c : Config (AgentState L K)),
      SeamEpidemics.allPhaseEq (L := L) (K := K) (seamP k + 1) n c →
      (dotyWorkHonest wih ⟨k.val + 1, by omega⟩).Pre c
  Cphase : Fin 21 → ℕ
  δ : Fin 21 → ℝ≥0
  c₀ : Config (AgentState L K)
  init : Config (AgentState L K)
  hC0 : ∀ i, Cphase i ≤ C0
  hδ : ∀ i, (δ i : ℝ≥0∞) ≤ (1 / (n : ℝ≥0∞) ^ 2)

/-- The honest assembly built from `DotyResidualAtomsV2`. -/
noncomputable def toAssembly'V2 {n C0 : ℕ} (ra : DotyResidualAtomsV2 (L := L) (K := K) n C0) :
    SeedTrigWiring.DotyAssembly' (L := L) (K := K) n where
  work := dotyWorkHonest ra.wih
  seamP := ra.seamP
  seamT := ra.seamT
  εepidemic := ra.εepidemic
  εovershoot := ra.εovershoot
  hDrift := ra.hDrift
  hNoOvershoot := ra.hNoOvershoot
  hWorkPostToWindow := ra.hWorkPostToWindow
  hSeedStep := ra.hSeedStep
  hWindowToWorkPre := ra.hWindowToWorkPre

@[simp] theorem toAssembly'V2_work {n C0 : ℕ} (ra : DotyResidualAtomsV2 (L := L) (K := K) n C0) :
    (toAssembly'V2 ra).work = dotyWorkHonest ra.wih := rfl

/-- The wired 21-instance family of the honest assembly. -/
noncomputable def phases'V2 {n C0 : ℕ} (ra : DotyResidualAtomsV2 (L := L) (K := K) n C0) :
    Fin 21 → PhaseConvergenceW (NonuniformMajority L K).transitionKernel :=
  SeedTrigWiring.dotyPhases' (toAssembly'V2 ra)

/-- `phases'V2 ra = dotyPhases' (toAssembly'V2 ra)` (recorded by `rfl` BEFORE the irreducibility
attribute, so the `dotyPhases'`-stated headline can be fed the `phases'V2`-stated hypotheses through a
cheap `▸` cast — the cast only rewrites the symbolic family in non-kernel-power subterms). -/
theorem phases'V2_eq {n C0 : ℕ} (ra : DotyResidualAtomsV2 (L := L) (K := K) n C0) :
    phases'V2 ra = SeedTrigWiring.dotyPhases' (toAssembly'V2 ra) := rfl

/-- The re-cut chain map stated over `phases'V2` (so it feeds the composition without unfolding
`phases'V2` — the fold divergence stays blocked).  Recorded before irreducibility. -/
theorem phases'V2_h_chain {n C0 : ℕ} (ra : DotyResidualAtomsV2 (L := L) (K := K) n C0) :
    ∀ (i : Fin 21) (hi : i.val + 1 < 21),
      ∀ x, (phases'V2 ra i).Post x → (phases'V2 ra ⟨i.val + 1, hi⟩).Pre x :=
  SeedTrigWiring.dotyPhases'_h_chain (toAssembly'V2 ra)

-- Block the kernel-power `whnf` from unfolding the heavy honest-slot definitions during the horizon
-- fold (the documented ConcreteAssembly divergence: reducing `(phases'V2 ra i).t` through the
-- `levels_PhaseConvergenceW` honest slots / the seam instances blows the heartbeat budget).  The work
-- family is consumed POLYMORPHICALLY (through `t`/`ε`/`Pre`/`Post` as a `PhaseConvergenceW`), so the
-- composition and the bridges (which take the work `Post`/`Pre` as carried hypotheses) never need to
-- reduce it.  `phases'V2_eq` reconnects to `dotyPhases'` where the headline needs it.
attribute [irreducible] dotyWorkHonest


/-! ## Part 6 — `doty_theorem_3_1_whp_v2`: the F1+F2+F3-corrected whp half.

`hcompFail` is PRODUCED (F1) from `doty_time_composition_W2` at the concrete honest family; the work
family is the levels-engine `dotyWorkHonest` (F2/F3).  The only remaining binders are the regime, the
residual atoms, the budget/time arithmetic, the start pin, and the endpoint bridge. -/

/-- **The F1 whp half PRODUCED over an ABSTRACT assembly, at the OPAQUE horizon `T`.**  The engineering
attack on the kernel-power obstruction, executed where it is tractable — over a FREE
`asm : DotyAssembly'`, and via the LANDED in-file `.1`-producer `BudgetTightening.doty_time_headline_
W2_inv_sq` (which extracts the composition's failure-side `.1` and chains it to `21/n²` INSIDE its own
file, where the kernel-power `whnf` is transparent).

`whp_of_asm'` instantiates that producer at `dotyPhases' asm` and folds both clauses to the OPAQUE `T`
through the abstract horizon-fold `fold_pair_to_T` (whose `rw [hT]; exact …` is the landed
`AssemblyBridges.hcompFail_of_composition` idiom — `hpair` arrives as a FREE hypothesis, so the fold
is syntactic).  Because `asm` is free and the produced bound is supplied to `fold_pair_to_T` as an
opaque hypothesis (never re-projected in this file), the divergent ConcreteAssembly whnf — which fires
only when a CONCRETE unfolded family's kernel-power is matched in place — never triggers.

The conclusion is at the opaque `T`, so the concrete theorem CONSUMES it cheaply (the crude landed
`doty_time_headline_CONCRETE'` is consumable at a concrete family for exactly this reason: its output
is at opaque `T`).  `hcompFail` is a free binder NOWHERE. -/
theorem fold_pair_to_T {n C0 : ℕ} {S : ℕ} (init c₀ : Config (AgentState L K))
    (hpair :
      ((NonuniformMajority L K).transitionKernel ^ S) c₀
          {c | ¬ majorityStableEndpoint (L := L) (K := K) init c}
        ≤ (21 : ℝ≥0∞) / (n : ℝ≥0∞) ^ 2
      ∧ S ≤ 21 * C0 * n * (L + 1))
    (T : ℕ) (hT : T = S) :
    ((NonuniformMajority L K).transitionKernel ^ T) c₀
        {c | ¬ majorityStableEndpoint (L := L) (K := K) init c}
      ≤ (21 : ℝ≥0∞) / (n : ℝ≥0∞) ^ 2
    ∧ T ≤ 21 * C0 * n * (L + 1) := by
  subst hT; exact hpair

theorem whp_of_asm' {n C0 : ℕ} (init c₀ : Config (AgentState L K))
    (asm : SeedTrigWiring.DotyAssembly' (L := L) (K := K) n)
    (Cphase : Fin 21 → ℕ) (δ : Fin 21 → ℝ≥0)
    (T : ℕ) (hT : T = ∑ i, (SeedTrigWiring.dotyPhases' asm i).t)
    (ht : ∀ i, (SeedTrigWiring.dotyPhases' asm i).t ≤ Cphase i * n * (L + 1))
    (hε : ∀ i, ((SeedTrigWiring.dotyPhases' asm i).ε : ℝ≥0∞) ≤ (δ i : ℝ≥0∞))
    (hx₀ : (SeedTrigWiring.dotyPhases' asm ⟨0, by omega⟩).Pre c₀)
    (h_post : ∀ c, (SeedTrigWiring.dotyPhases' asm ⟨21 - 1, by omega⟩).Post c →
        majorityStableEndpoint (L := L) (K := K) init c)
    (hC0 : ∀ i, Cphase i ≤ C0)
    (hδ : ∀ i, (δ i : ℝ≥0∞) ≤ (1 / (n : ℝ≥0∞) ^ 2)) :
    ((NonuniformMajority L K).transitionKernel ^ T) c₀
        {c | ¬ majorityStableEndpoint (L := L) (K := K) init c}
      ≤ (21 : ℝ≥0∞) / (n : ℝ≥0∞) ^ 2
    ∧ T ≤ 21 * C0 * n * (L + 1) :=
  fold_pair_to_T (C0 := C0) init c₀
    (BudgetTightening.doty_time_headline_W2_inv_sq (C0 := C0) init c₀ Cphase δ
      (SeedTrigWiring.dotyPhases' asm) ht hε (SeedTrigWiring.dotyPhases'_h_chain asm) hx₀ h_post
      hC0 hδ)
    T hT

theorem doty_theorem_3_1_whp_v2 {n L K C0 : ℕ}
    (hReg : PaperRegime.DotyRegime n L K)
    (ra : DotyResidualAtomsV2 (L := L) (K := K) n C0)
    (T : ℕ) (hT : T = ∑ i, (phases'V2 ra i).t)
    (ht : ∀ i, (phases'V2 ra i).t ≤ ra.Cphase i * n * (L + 1))
    (hε : ∀ i, ((phases'V2 ra i).ε : ℝ≥0∞) ≤ (ra.δ i : ℝ≥0∞))
    (hx₀ : (phases'V2 ra ⟨0, by omega⟩).Pre ra.c₀)
    (h_post : ∀ c, (phases'V2 ra ⟨21 - 1, by omega⟩).Post c →
        majorityStableEndpoint (L := L) (K := K) ra.init c) :
    ((NonuniformMajority L K).transitionKernel ^ T) ra.c₀
        {c | ¬ majorityStableEndpoint (L := L) (K := K) ra.init c}
      ≤ (21 : ℝ≥0∞) / (n : ℝ≥0∞) ^ 2
    ∧ T ≤ 21 * C0 * n * (L + 1)
    ∧ T ≤ 21 * C0 * n * (Nat.clog 2 n + 1) := by
  -- F1: the failure bound is PRODUCED, not carried.  `whp_of_asm'` does the full production+fold over a
  -- FREE `asm` (so the `.1` extraction / fold are symbolic), concluding at the OPAQUE `T`.  We
  -- INSTANTIATE it at `asm := toAssembly'V2 ra` (the honest assembly): pure substitution of an
  -- already-checked proof; the `(K^T)…` output is consumed with `T` opaque — cheap.  `hcompFail` GONE.
  obtain ⟨herr, htime⟩ :=
    whp_of_asm' (C0 := C0) ra.init ra.c₀ (toAssembly'V2 ra) ra.Cphase ra.δ T hT ht hε hx₀ h_post
      ra.hC0 ra.hδ
  refine ⟨herr, htime, ?_⟩
  rw [← hReg.hLlog]; exact htime

end FinalAssemblyV2
end ExactMajority
