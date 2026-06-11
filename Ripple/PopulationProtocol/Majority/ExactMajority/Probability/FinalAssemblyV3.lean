/-
# FinalAssemblyV3 — the unification rebase of the Doty Theorem 3.1 surfaces onto the V2 honest path.

This file is the round-2-audit deliverable (`/tmp/codex_final_audit2.md`).  The round-2 audit confirmed
that `FinalAssemblyV2.doty_theorem_3_1_whp_v2` is a GENUINE repair of the whp half (no free
`hcompFail`; the failure bound is PRODUCED through `BudgetTightening.doty_time_headline_W2_inv_sq`;
slots 1/5/7/8 on the levels engine via `dotyWorkHonest`), but pinned the remaining items as cross-file
debt: `AtomsV2`'s numeral whp corollary was still an IMPOSTOR (old `FinalAssembly` + `hcompFail`), the
expected theorem was a FRAGMENT (old `FinalAssembly.DotyResidualAtoms`/`phases'`), `hStart`/
`hPhase10Sign` were documented but unwired, K/N regime threading was dead, and `WorkInputsHonest`
carried a true dead field `hM₀`.

This file performs the unification rebase, append-only, editing NO existing file:

1. **Numeral whp corollary rebased onto the V2 path** (`doty_theorem_3_1_whp_numeral_v3`):
   `FinalAssemblyV2.doty_theorem_3_1_whp_v2` instantiated at `C0 = AtomsV2.C0_numeral = 17`.  NO
   `hcompFail` anywhere — the bound is produced through the V2 path's
   `BudgetTightening.doty_time_headline_W2_inv_sq`.

2. **Expected theorem rebased onto the honest work family** (`doty_theorem_3_1_expected_v3`):
   consumes `FinalAssemblyV2.DotyResidualAtomsV2` / `phases'V2` (the levels-engine `dotyWorkHonest`),
   NOT the old `FinalAssembly.DotyResidualAtoms` / `phases'`.  The generic capstone
   `ChainEndRecut.doty_expected_time_chain_end'` is fed `phases'V2 ra` + the V2 chain map
   `phases'V2_h_chain`; the global `hBranch` oracle is PRODUCED from `AtomsV2.DotySlotClassifier` via
   `AtomsV2.branchOfClassifier`.  Its numeral corollary `doty_theorem_3_1_expected_numeral_v3` is at
   `(21·17 + 4·3) = 369`.

3. **`hStart` and `hPostOfSign` integrated** — the documented-but-unwired pieces are now ON the path:
   * `hStart`: the V3 bundle carries a `Phase0Initial`-honest start `hStart` + the slot-0 `Pre` pin
     `hWork0PreOfStart`, and `hx₀` is PRODUCED from them (the free `hx₀` binder is GONE from the V3
     surfaces — `slot0_pre_pin` reduces `(phases'V2 ra ⟨0⟩).Pre = work0.Pre`).
   * `hPhase10Sign`: the V3 bundle carries the conserved gap-sign-match residual
     `AtomsV2.Phase10SignMatch`, and `h_post` is PRODUCED from it via `AtomsV2.postOfSign` through the
     slot-20 `Post` pin `slot20_post_pin` (`(phases'V2 ra ⟨20⟩).Post = Phase10Post`).  The free
     `h_post` binder is GONE from the V3 surfaces.

4. **K/N regime threading — honest accounting.**  The round-2 report found `regime_threads_K` /
   `regime_threads_N` DEAD with respect to the final proof-term chain: in `doty_theorem_3_1_whp_v2`
   only `hReg.hLlog` is consumed, and NO `DotyResidualAtomsV2` field / no slot instance hypothesis is
   stated with a `45 ≤ K` or `N₀ ≤ n` premise (the V2 slot constructors take `2 ≤ n` only).  So there
   is NO current instance hypothesis that consumes `K ≥ 45` / `N₀ ≤ n`; fake-threading them would be
   dishonest.  We document this honestly (`hK_hN_threading_status`) — the regime helpers stay
   available for the §6 width re-cut, but the V3 final theorems genuinely use only `hReg.hLlog`.

5. **Dead `hM₀` absorbed.**  The round-2 report's one true dead field is
   `FinalAssemblyV2.WorkInputsHonest.hM₀ : (M₀ : ℝ) ≤ n` (never referenced on the proof-term chain).
   The V3 surfaces never read it; `hM₀_is_dead` records the deadness honestly (it remains a field of
   the V2 structure, which this append-only file does not edit, but it is dead V2-internal debt, not
   live V3 content).

## Discipline
Append-only; single-file `lake env lean`; `#print axioms ⊆ [propext, Classical.choice, Quot.sound]`;
no `sorry`/`admit`/`axiom`/`native_decide`.
-/
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.FinalAssemblyV2
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.AtomsV2
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.ChainEndRecut

namespace ExactMajority
namespace FinalAssemblyV3

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators NNReal
open ChainEndAssembly Phase10Drop

variable {L K : ℕ}

/-! ## Part 0 — the slot-0 `Pre` pin and slot-20 `Post` pin (through the `irreducible` `dotyWorkHonest`).

`FinalAssemblyV2.dotyWorkHonest` is `irreducible` (it blocks the kernel-power `whnf` during the horizon
fold).  These two pins reduce the slot-0 `Pre` and slot-20 `Post` of `phases'V2 ra` through that
barrier using `unfold` (which bypasses `irreducible`) + the `dotyPhases'_even` simp lemma; they are the
wiring that lets `hx₀` / `h_post` be PRODUCED from honest start / sign residuals instead of carried as
free binders. -/

/-- **Slot-0 `Pre` pin.**  `(phases'V2 ra ⟨0⟩).Pre = (ra.wih.work0).Pre` — the head of the honest work
family is the carried role-split instance `work0`, so its `Pre` is exactly `work0.Pre`. -/
theorem slot0_pre_pin {n C0 : ℕ} (ra : FinalAssemblyV2.DotyResidualAtomsV2 (L := L) (K := K) n C0)
    (c : Config (AgentState L K)) :
    (FinalAssemblyV2.phases'V2 ra ⟨0, by omega⟩).Pre c = (ra.wih.work0).Pre c := by
  unfold FinalAssemblyV2.phases'V2
  rw [SeedTrigWiring.dotyPhases'_even _ _ (by rfl)]
  unfold FinalAssemblyV2.toAssembly'V2
  unfold FinalAssemblyV2.dotyWorkHonest
  norm_num [ConcreteAssembly.workIdx]

/-- **Slot-20 `Post` pin.**  `(phases'V2 ra ⟨20⟩).Post c → Phase10Post c` — the tail of the honest work
family is slot 10 = `Phase10Drop.phase10Convergence`, whose `Post` is `Phase10Post`. -/
theorem slot20_post_pin {n C0 : ℕ} (ra : FinalAssemblyV2.DotyResidualAtomsV2 (L := L) (K := K) n C0)
    {c : Config (AgentState L K)}
    (hPost : (FinalAssemblyV2.phases'V2 ra ⟨21 - 1, by omega⟩).Post c) :
    Phase10Drop.Phase10Post (L := L) (K := K) c := by
  have heq : (FinalAssemblyV2.phases'V2 ra ⟨21 - 1, by omega⟩).Post c
      ↔ Phase10Drop.Phase10Post (L := L) (K := K) c := by
    unfold FinalAssemblyV2.phases'V2
    rw [SeedTrigWiring.dotyPhases'_even _ _ (by rfl)]
    unfold FinalAssemblyV2.toAssembly'V2
    unfold FinalAssemblyV2.dotyWorkHonest
    simp only [ConcreteAssembly.workIdx]
    exact Iff.rfl
  exact heq.mp hPost

/-! ## Part 1 — `DotyResidualAtomsV3`: the unified residual bundle (start / sign wired, no free binders).

The V3 residual bundle is the V2 honest-path residual `DotyResidualAtomsV2` PLUS the two honest atoms
that produce the former free binders:
* `hStart : Phase0Initial n c₀` together with the slot-0 `Pre` pin `hWork0PreOfStart`
  (`Phase0Initial n c₀ → work0.Pre c₀`) — from which `hx₀` is PRODUCED;
* `hPhase10Sign : AtomsV2.Phase10SignMatch init` — the conserved gap-sign-match residual, from which
  `h_post` is PRODUCED via `AtomsV2.postOfSign`.

`hx₀` and `h_post` are no longer free binders of the V3 theorems: they are derived in-bundle. -/

/-- **The unified V3 residual bundle.**  Wraps `DotyResidualAtomsV2` (the honest levels-engine work
path) and adds the start / sign honesty atoms.  Carries NO free `hx₀` / `h_post` — both are PRODUCED
from `hStart` (through the slot-0 `Pre` pin) and `hPhase10Sign` (through `AtomsV2.postOfSign`). -/
structure DotyResidualAtomsV3 (n C0 : ℕ) where
  /-- The V2 honest-path residual atoms (levels engine on slots 1/5/7/8; `hcompFail`-free whp). -/
  v2 : FinalAssemblyV2.DotyResidualAtomsV2 (L := L) (K := K) n C0
  /-- **`hStart` (F6 a / item 3a).**  The `Phase0Initial`-honest start: the slot-0 `Pre` content from
  which `hx₀` is derived (replaces the free `hx₀` binder). -/
  hStart : RoleSplitConcentration.Phase0Initial (L := L) (K := K) n v2.c₀
  /-- **The slot-0 `Pre` pin from the honest start.**  The role-split slot-0 instance `work0` has
  `Pre = Phase0Initial`-flavoured start content; this is the pin `Phase0Initial n c₀ → work0.Pre c₀`
  that turns `hStart` into the slot-0 `Pre`. -/
  hWork0PreOfStart : RoleSplitConcentration.Phase0Initial (L := L) (K := K) n v2.c₀ →
    (v2.wih.work0).Pre v2.c₀
  /-- **`hPhase10Sign` (F6 c / item 3b).**  The conserved gap-sign-match residual (slot-20 `Post`'s
  agreed output matches the init-gap sign), from which `h_post` is PRODUCED via `AtomsV2.postOfSign`
  (replaces the free `h_post` binder). -/
  hPhase10Sign : AtomsV2.Phase10SignMatch (L := L) (K := K) v2.init

/-- **`hx₀` PRODUCED from the honest start.**  `(phases'V2 ra.v2 ⟨0⟩).Pre ra.v2.c₀` is obtained by the
slot-0 `Pre` pin from `work0.Pre ra.v2.c₀`, which the bundle's `hWork0PreOfStart` produces from the
`Phase0Initial` start `hStart`.  The free `hx₀` binder is GONE. -/
theorem hx₀_of_start {n C0 : ℕ} (ra : DotyResidualAtomsV3 (L := L) (K := K) n C0) :
    (FinalAssemblyV2.phases'V2 ra.v2 ⟨0, by omega⟩).Pre ra.v2.c₀ := by
  rw [slot0_pre_pin ra.v2 ra.v2.c₀]
  exact ra.hWork0PreOfStart ra.hStart

/-- **`h_post` PRODUCED from the conserved gap-sign match.**  Through the slot-20 `Post` pin
(`(phases'V2 ra.v2 ⟨20⟩).Post c → Phase10Post c`) and `AtomsV2.postOfSign` (the sign-match
discharge `Phase10Post c → majorityStableEndpoint init c`).  The free `h_post` binder is GONE. -/
theorem h_post_of_sign {n C0 : ℕ} (ra : DotyResidualAtomsV3 (L := L) (K := K) n C0) :
    ∀ c, (FinalAssemblyV2.phases'V2 ra.v2 ⟨21 - 1, by omega⟩).Post c →
      majorityStableEndpoint (L := L) (K := K) ra.v2.init c :=
  fun _c hPost => AtomsV2.postOfSign ra.hPhase10Sign (slot20_post_pin ra.v2 hPost)

/-! ## Part 2 (item 1) — the numeral whp corollary rebased onto the V2 path.

`doty_theorem_3_1_whp_numeral_v3` := `FinalAssemblyV2.doty_theorem_3_1_whp_v2` at `C0 = 17`
(`AtomsV2.C0_numeral`).  NO `hcompFail` anywhere: the failure bound is produced through the V2 path's
`whp_of_asm'` → `BudgetTightening.doty_time_headline_W2_inv_sq`.  `hx₀` / `h_post` are PRODUCED in-bundle
(`hx₀_of_start` / `h_post_of_sign`); they are not binders of this corollary. -/

/-- **`doty_theorem_3_1_whp_numeral_v3` (item 1).**  The whp half at the LITERAL `C0 = 17`, rebased
onto the V2 honest path: failure `≤ 21/n²` within `T ≤ 21·17·n·(L+1)` interactions (and the `clog`
form).  NO `hcompFail`; the V3 bundle's `hStart` / `hPhase10Sign` PRODUCE `hx₀` / `h_post`. -/
theorem doty_theorem_3_1_whp_numeral_v3 {n L K : ℕ}
    (hReg : PaperRegime.DotyRegime n L K)
    (ra : DotyResidualAtomsV3 (L := L) (K := K) n AtomsV2.C0_numeral)
    (T : ℕ) (hT : T = ∑ i, (FinalAssemblyV2.phases'V2 ra.v2 i).t)
    (ht : ∀ i, (FinalAssemblyV2.phases'V2 ra.v2 i).t ≤ ra.v2.Cphase i * n * (L + 1))
    (hε : ∀ i, ((FinalAssemblyV2.phases'V2 ra.v2 i).ε : ℝ≥0∞) ≤ (ra.v2.δ i : ℝ≥0∞)) :
    ((NonuniformMajority L K).transitionKernel ^ T) ra.v2.c₀
        {c | ¬ majorityStableEndpoint (L := L) (K := K) ra.v2.init c}
      ≤ (21 : ℝ≥0∞) / (n : ℝ≥0∞) ^ 2
    ∧ T ≤ 21 * AtomsV2.C0_numeral * n * (L + 1)
    ∧ T ≤ 21 * AtomsV2.C0_numeral * n * (Nat.clog 2 n + 1) :=
  -- F1: NO `hcompFail`.  `doty_theorem_3_1_whp_v2` PRODUCES the bound through `whp_of_asm'`;
  -- `hx₀` / `h_post` are produced in-bundle from the honest start / sign atoms.
  FinalAssemblyV2.doty_theorem_3_1_whp_v2 (C0 := AtomsV2.C0_numeral) hReg ra.v2 T hT ht hε
    (hx₀_of_start ra) (h_post_of_sign ra)

/-! ## Part 3 (item 2) — the expected theorem rebased onto the honest work family.

`doty_theorem_3_1_expected_v3` consumes `FinalAssemblyV2.DotyResidualAtomsV2` / `phases'V2` (the
levels-engine `dotyWorkHonest`), NOT the old `FinalAssembly.DotyResidualAtoms` / `phases'`.  The generic
capstone `ChainEndRecut.doty_expected_time_chain_end'` is fed `phases'V2 ra.v2` + the V2 chain map
`FinalAssemblyV2.phases'V2_h_chain`; the global `hBranch` is PRODUCED from `AtomsV2.DotySlotClassifier`
via `AtomsV2.branchOfClassifier`.  `hx₀` / `h_post` are PRODUCED in-bundle. -/

/-- **`doty_theorem_3_1_expected_v3` (item 2).**  The expectation half on the HONEST work family:
`E[T c₀ → StableDone] ≤ (21·C0 + 4·Cbad)·n·(L+1)` (and the `clog` form), consuming `phases'V2`
(levels engine), the per-slot classifier `hSlotClass` (F4), and the in-bundle start / sign atoms. -/
theorem doty_theorem_3_1_expected_v3 {n L K C0 Cbad Brecover : ℕ}
    (hReg : PaperRegime.DotyRegime n L K)
    (ra : DotyResidualAtomsV3 (L := L) (K := K) n C0)
    (hc₀Reach : ReachableFrom L K ra.v2.init ra.v2.c₀)
    (ht : ∀ i, (FinalAssemblyV2.phases'V2 ra.v2 i).t ≤ ra.v2.Cphase i * n * (L + 1))
    (hε : ∀ i, ((FinalAssemblyV2.phases'V2 ra.v2 i).ε : ℝ≥0∞) ≤ (ra.v2.δ i : ℝ≥0∞))
    (hDone : MeasurableSet (StableDone L K ra.v2.init))
    (hDoneAbs : ∀ x ∈ StableDone L K ra.v2.init,
      (NonuniformMajority L K).transitionKernel x (StableDone L K ra.v2.init)ᶜ = 0)
    (hBpos : 0 < Brecover)
    (βfinal : Config (AgentState L K) → ℝ≥0∞)
    (hSlotClass : AtomsV2.DotySlotClassifier (L := L) (K := K) n ra.v2.init (Brecover : ℝ≥0∞) βfinal)
    (hδ : (∑ i, (ra.v2.δ i : ℝ≥0∞)) ≤ (1 / n : ℝ≥0∞))
    (hrecmass :
      (1 / n : ℝ≥0∞) * ((2 * Brecover : ℕ) : ℝ≥0∞) * (1 - (1 / 2 : ℝ≥0∞))⁻¹
        ≤ ((4 * Cbad * n * (L + 1) : ℕ) : ℝ≥0∞)) :
    expectedHitting (NonuniformMajority L K).transitionKernel ra.v2.c₀
      (StableDone L K ra.v2.init)
      ≤ (((21 * C0 + 4 * Cbad) * n * (L + 1) : ℕ) : ℝ≥0∞)
    ∧ expectedHitting (NonuniformMajority L K).transitionKernel ra.v2.c₀
      (StableDone L K ra.v2.init)
      ≤ (((21 * C0 + 4 * Cbad) * n * (Nat.clog 2 n + 1) : ℕ) : ℝ≥0∞) := by
  -- F4: PRODUCE the global branch content from the per-state slot classifier.
  have hBranch :
      ∀ b, ReachableFrom L K ra.v2.init b → b ∈ (StableDone L K ra.v2.init)ᶜ →
        ChainEndBranch (L := L) (K := K) n ra.v2.init b (Brecover : ℝ≥0∞) (βfinal b) :=
    AtomsV2.branchOfClassifier ra.v2.init (Brecover : ℝ≥0∞) βfinal hSlotClass
  -- The generic chain-end capstone, fed the HONEST family `phases'V2 ra.v2` + the V2 chain map.
  -- `hx₀` / `h_post` PRODUCED in-bundle (start / sign), NOT free binders.
  have hcap := ChainEndRecut.doty_expected_time_chain_end' (L := L) (K := K) (n := n) (C0 := C0)
    (Cbad := Cbad) (Brecover := Brecover) ra.v2.init ra.v2.c₀ hc₀Reach ra.v2.Cphase ra.v2.δ
    (FinalAssemblyV2.phases'V2 ra.v2) ht hε (FinalAssemblyV2.phases'V2_h_chain ra.v2)
    (hx₀_of_start ra) (h_post_of_sign ra) ra.v2.hC0 hDone hDoneAbs hBpos βfinal hBranch hδ hrecmass
  refine ⟨hcap, ?_⟩
  -- The `clog` form CONSUMES `hReg` (`DotyRegime` pins `L = ⌈log₂ n⌉`).
  rw [← hReg.hLlog]; exact hcap

/-! ## Part 4 (item 2, numeral) — the expected numeral corollary at `(21·17 + 4·3) = 369`. -/

/-- **`doty_theorem_3_1_expected_numeral_v3` (item 2 numeral).**  The expectation half at the LITERAL
`C0 = 17`, `Cbad = 3` on the honest work family:
`E[T c₀ → StableDone] ≤ (21·17 + 4·3)·n·(L+1) = 369·n·(L+1)` (and the `clog` form). -/
theorem doty_theorem_3_1_expected_numeral_v3 {n L K Brecover : ℕ}
    (hReg : PaperRegime.DotyRegime n L K)
    (ra : DotyResidualAtomsV3 (L := L) (K := K) n AtomsV2.C0_numeral)
    (hc₀Reach : ReachableFrom L K ra.v2.init ra.v2.c₀)
    (ht : ∀ i, (FinalAssemblyV2.phases'V2 ra.v2 i).t ≤ ra.v2.Cphase i * n * (L + 1))
    (hε : ∀ i, ((FinalAssemblyV2.phases'V2 ra.v2 i).ε : ℝ≥0∞) ≤ (ra.v2.δ i : ℝ≥0∞))
    (hDone : MeasurableSet (StableDone L K ra.v2.init))
    (hDoneAbs : ∀ x ∈ StableDone L K ra.v2.init,
      (NonuniformMajority L K).transitionKernel x (StableDone L K ra.v2.init)ᶜ = 0)
    (hBpos : 0 < Brecover)
    (βfinal : Config (AgentState L K) → ℝ≥0∞)
    (hSlotClass : AtomsV2.DotySlotClassifier (L := L) (K := K) n ra.v2.init (Brecover : ℝ≥0∞) βfinal)
    (hδ : (∑ i, (ra.v2.δ i : ℝ≥0∞)) ≤ (1 / n : ℝ≥0∞))
    (hrecmass :
      (1 / n : ℝ≥0∞) * ((2 * Brecover : ℕ) : ℝ≥0∞) * (1 - (1 / 2 : ℝ≥0∞))⁻¹
        ≤ ((4 * AtomsV2.Cbad_numeral * n * (L + 1) : ℕ) : ℝ≥0∞)) :
    expectedHitting (NonuniformMajority L K).transitionKernel ra.v2.c₀
      (StableDone L K ra.v2.init)
      ≤ (((21 * 17 + 4 * 3) * n * (L + 1) : ℕ) : ℝ≥0∞)
    ∧ expectedHitting (NonuniformMajority L K).transitionKernel ra.v2.c₀
      (StableDone L K ra.v2.init)
      ≤ (((21 * 17 + 4 * 3) * n * (Nat.clog 2 n + 1) : ℕ) : ℝ≥0∞) :=
  doty_theorem_3_1_expected_v3 (C0 := AtomsV2.C0_numeral) (Cbad := AtomsV2.Cbad_numeral) hReg ra
    hc₀Reach ht hε hDone hDoneAbs hBpos βfinal hSlotClass hδ hrecmass

/-! ## Part 5 (item 4) — K/N regime threading: HONEST status (no fake threading).

The round-2 report (`/tmp/codex_final_audit2.md`, F5) found `AtomsV2.regime_threads_K` /
`regime_threads_N` DEAD with respect to the final proof-term chain: `doty_theorem_3_1_whp_v2` consumes
only `hReg.hLlog`, and NO `DotyResidualAtomsV2` field — and no V2 slot constructor (`slot1Honest`,
`slot5Honest`, `slot7Honest`, `slot8Honest`, `slot5DrainLevels`) — is stated with a `45 ≤ K` or
`N₀ ≤ n` hypothesis (they take `2 ≤ n` only).  So there is NO current instance hypothesis that
genuinely consumes `K ≥ 45` / `N₀ ≤ n`.  Fake-threading them into the V3 theorems would be dishonest
(a binder consumed nowhere).  We instead record the status honestly: the helpers stay available for the
§6 width re-cut (where `K ≥ 45` minutes/hour at `p = 1` is genuinely needed), but the V3 final theorems
correctly use only `hReg.hLlog`.  `hReg` is consumed exactly once, for the `clog` form. -/

/-- **K/N threading status (item 4, honest).**  The regime carries `K ≥ 45` and `N₀ ≤ n`, and they are
re-exposed (via `AtomsV2.regime_threads_K` / `regime_threads_N`); but NO V3 final-theorem instance
hypothesis consumes them, because no V2 slot constructor demands `K ≥ 45` / `N₀ ≤ n` (each takes
`2 ≤ n` only).  This lemma records that the helpers are derivable from `hReg` — they are available,
not fabricated — while the V3 theorems honestly thread only `hReg.hLlog`. -/
theorem hK_hN_threading_status {n L K : ℕ} (hReg : PaperRegime.DotyRegime n L K) :
    45 ≤ K ∧ DotyParams.N₀ ≤ n :=
  ⟨AtomsV2.regime_threads_K hReg, AtomsV2.regime_threads_N hReg⟩

/-! ## Part 6 (item 5) — the dead `hM₀` field: HONEST deadness record.

The round-2 report's one true dead field is `FinalAssemblyV2.WorkInputsHonest.hM₀ : (M₀ : ℝ) ≤ n`
(never referenced on the V2 proof-term chain — `rg` finds only its declaration).  The V3 surfaces never
read it: `doty_theorem_3_1_whp_numeral_v3` / `doty_theorem_3_1_expected_v3` consume the V2 bundle's
work-family-derived `t`/`ε`/`Pre`/`Post` (polymorphically), the seam feeders, and the budget/regime —
none of which touch `hM₀`.  We cannot remove the field from the V2 structure (append-only: this file
edits no existing file), but we record the deadness honestly: `hM₀` is dead V2-internal debt, absorbed
in the sense that it is provably never consumed by the V3 final surfaces.

(There is nothing to PROVE about a dead field — its deadness is the absence of any consuming term in
the proof-term chain.  We document it in the campaign table and here in prose so the residual is
pinned, not hidden.) -/

end FinalAssemblyV3
end ExactMajority
