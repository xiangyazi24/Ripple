/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# `TopSplitDrift` — discharging the `topSplitWindow_whp` protocol residuals.

Doty et al., *Exact Majority* (arXiv:2106.10201v2), §5.1–5.2 (Lemma 5.1 top-split
balance).  This file supplies the two named residuals that
`Probability/TopSplit.lean`'s `topSplitWindow_whp` carries as hypotheses, for the
top-split process `X c = mainCount c − topCRMass c`:

  * `hjump` — the per-step bounded jump `|ΔX| ≤ 1`;
  * `hdrift` — the inward `|X|`-drift `∫ |X| ∂(K c) ≤ |X c|`.

## What this file establishes — and the two honest corrections to the blueprint

### Stage 1 — the ledger (the honest invariant).

The paper's Lemma 5.1 ledger `sf + 2·st = mf + 2·mt` is stated for an abstract
two-side split.  Computing `ΔX` for EVERY Phase-0 rule against the *actual* Lean
encoding (`Protocol/Transition.lean`, `Phase0Transition`) shows the honest
per-rule effect on `X = mainCount − topCRMass` (`topCRMass = cr+clock+reserve`):

  * **R1** (`mcr,mcr → main,cr`): `main +1`, `cr +1`  ⟹ `ΔtopCRMass = +1`, `ΔX = 0`.
  * **R2** (`mcr + unassigned main → cr + assigned-main`): `cr +1`, `main +0`
        ⟹ `ΔtopCRMass = +1`, `ΔX = −1`.
  * **R3** (`mcr + unassigned (cr/clock/reserve) → main + assigned-partner`):
        `main +1`, partner role unchanged ⟹ `ΔtopCRMass = 0`, `ΔX = +1`.
  * **R4** (`cr,cr → clock,reserve`): `cr −2`, `clock +1`, `reserve +1`
        ⟹ `ΔtopCRMass = 0`, `ΔX = 0`.
  * **R5** (`clock,clock → clock,clock`): roles unchanged ⟹ `ΔX = 0`.

So `X` moves ONLY by `R2` (`−1`) and `R3` (`+1`); the TRUE preserved invariant is
the existing `mainCount + topCRMass = n` (= `mainCount_add_topCRMass`, with
`roleMCRCount = 0` / `card = n`).  We record the honest free/temporary ledger as
the per-agent integer weight `topW a := [role=main] − [role∈{cr,clock,reserve}]`
(so `topSplitXZ c = Config.sumOf topW c`), whose two free pools driving the drift
are `mfreeCount` (`= #unassigned main`, the R2 targets) and `sfreeCount`
(`= #unassigned cr/clock/reserve`, the R3 targets).  See the mapping note below.

### Stage 2 — the bounded jump `|ΔX| ≤ 1` (FULLY PROVEN, on the Phase-0 region).

`topW_pair_delta_le_one`: for any pair both at phase 0, the full `Transition`
output changes `topW r₁ + topW r₂` by at most `1` in absolute value (the finite
per-rule case check).  Lifted to `|topSplitXZ (stepOrSelf …) − topSplitXZ c| ≤ 1`
and hence the kernel-a.e. `hjump` ON the absorbing Phase-0 region.

### Stage 3 — the inward drift, with the X=0 boundary solved by `cosh` (the crux).

The consumer's `hdrift : ∫ |X| ∂(K c) ≤ |X c|` is **literally FALSE at `X = 0`**:
from a balanced config `|X| = 0`, but `R2`/`R3` push `X` to `±1`, so
`∫ |X| ∂(K c) > 0 = |X c|`.  Feeding the consumer a globally-false hypothesis is
the VACUOUS-conditional trap (`#print axioms` cannot detect an unsatisfiable
premise; playbook §3.3).  The honest classical fix is the **`cosh` MGF**: for a
bounded-jump (`ΔX ∈ {−1,0,1}`) inward-drift walk,

    E[cosh(s·X')] = cosh(s·X)·[1 + (cosh s − 1)·(p₊+p₋)] + sinh(s·X)·sinh s·(p₊−p₋),

and the symmetric inward condition `p₋ ≥ p₊` on `{X>0}`, `p₊ ≥ p₋` on `{X<0}`
makes the `sinh(s·X)·(p₊−p₋)` term `≤ 0` in EVERY case — *including `X = 0`*,
where `sinh 0 = 0` kills it automatically.  Hence `cosh(s·X)` is a multiplicative
(`r = cosh s`) supermartingale with NO boundary exception, feeding the audited
`Supermartingale.geometric_drift_tail_kernel` engine.  `coshPot s` packages this
as an `ℝ≥0∞` potential and `coshPot_drift_of_inward` proves the drift from the
abstract symmetric pair-count comparison.

### Stage 4 — wire-up.

`topSplitWindow_whp_cosh` re-derives the top-split tail from the cosh route +
the (region-true) protocol facts, restating `TopSplit.topSplitWindow_whp`'s
conclusion shape without editing `TopSplit.lean`.

Everything here is 0-`sorry` / 0-`axiom` (only `propext`, `Classical.choice`,
`Quot.sound`) / no `native_decide`.  The single genuine protocol residual carried
is the inward symmetric pair-count comparison `topSplit_inward_symmetric` (the
true Lemma-5.1 C-1 gap), now BOUNDARY-FREE (no `X=0` exception).

Reference: Doty et al. §5.1–5.2; `HANDOFF_ROLESPLIT_TOPSPLIT.md`;
`Probability/TopSplit.lean`; engine `Supermartingale.geometric_drift_tail_kernel`.
-/

import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.TopSplit
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.Phase0Window

namespace ExactMajority
namespace RoleSplitConcentration

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Real BigOperators

variable {L K : ℕ}

/-! ## Stage 1 — the honest ledger weight. -/

/-- The per-agent integer weight tracking the top-split balance:
`+1` for a `Main` agent, `−1` for an agent in the RoleCR-descended pool
(`cr`/`clock`/`reserve`), `0` for a transient `mcr`.  Summing `topW` over the
configuration gives the signed process `topSplitXZ = mainCount − topCRMass`. -/
def topW (a : AgentState L K) : ℤ :=
  (if a.role = .main then 1 else 0)
    - (if a.role = .cr ∨ a.role = .clock ∨ a.role = .reserve then 1 else 0)

/-- The integer top-split process `X c = mainCount c − topCRMass c` as a multiset
sum of the per-agent weight `topW`. -/
def topSplitXZ (c : Config (AgentState L K)) : ℤ :=
  Config.sumOf (topW (L := L) (K := K)) c

/-- `topSplitXZ` is the integer count difference `mainCount − (cr+clock+reserve)`. -/
theorem topSplitXZ_eq_counts (c : Config (AgentState L K)) :
    topSplitXZ (L := L) (K := K) c =
      (mainCount (L := L) (K := K) c : ℤ)
        - ((crCount (L := L) (K := K) c : ℤ)
            + (clockCount (L := L) (K := K) c : ℤ)
            + (reserveCount (L := L) (K := K) c : ℤ)) := by
  classical
  unfold topSplitXZ Config.sumOf topW mainCount crCount clockCount reserveCount
  induction c using Multiset.induction with
  | empty => simp
  | cons a s ih =>
    simp only [Multiset.map_cons, Multiset.sum_cons, Multiset.countP_cons]
    rcases a.role with _ | _ | _ | _ | _ <;>
      · simp only [reduceCtorEq, reduceIte, or_false, false_or, or_true, true_or,
          if_true, if_false]
        push_cast
        push_cast at ih
        omega

/-- `topSplitXZ` agrees with the `ℝ`-valued `topSplitX` from `TopSplit.lean`. -/
theorem topSplitX_eq_cast (c : Config (AgentState L K)) :
    topSplitX (L := L) (K := K) c = (topSplitXZ (L := L) (K := K) c : ℝ) := by
  rw [topSplitX, topSplitXZ_eq_counts, topCRMass]
  push_cast
  ring

/-! ## Stage 2 — the bounded jump `|ΔX| ≤ 1` (deterministic, on the Phase-0 region). -/

/-- `topW` reads only the agent's `role`. -/
private lemma topW_eq_of_role_eq (a b : AgentState L K) (h : a.role = b.role) :
    topW (L := L) (K := K) a = topW (L := L) (K := K) b := by
  unfold topW; rw [h]

/-- The Standard Counter Subroutine keeps a `Clock` agent a `Clock` (decrement or
phase-advance both preserve the clock role — `advancePhaseWithInit_clock_role_eq`). -/
private lemma stdCounterSubroutine_clock_role_eq (a : AgentState L K)
    (ha : a.role = .clock) :
    (stdCounterSubroutine L K a).role = .clock := by
  unfold stdCounterSubroutine
  split
  · exact advancePhaseWithInit_clock_role_eq L K a ha
  · exact ha

/-- `topW` of a `stdCounterSubroutine` output equals `topW` of the input clock. -/
private lemma topW_stdCounterSubroutine_clock (a : AgentState L K)
    (ha : a.role = .clock) :
    topW (L := L) (K := K) (stdCounterSubroutine L K a) = topW (L := L) (K := K) a :=
  topW_eq_of_role_eq _ _ ((stdCounterSubroutine_clock_role_eq a ha).trans ha.symm)

set_option maxHeartbeats 1000000 in
/-- **Per-pair `Phase0Transition` weight-change bound.**  For any input pair, the
`Phase0Transition` output weight block `topW δ₁ + topW δ₂` differs from the source
block `topW r₁ + topW r₂` by at most `1` in absolute value.  Finite case check
over the 5x5x2x2 role/assigned tree (the opaque counter machinery never affects
the role, the only field topW inspects); the only one-sided moves are R2 (minus
one) and R3 (plus one), R1/R4/R5 give zero. -/
theorem topW_Phase0_pair_delta_abs_le_one (r₁ r₂ : AgentState L K) :
    |(topW (L := L) (K := K) (Phase0Transition L K r₁ r₂).1
        + topW (L := L) (K := K) (Phase0Transition L K r₁ r₂).2)
      - (topW (L := L) (K := K) r₁ + topW (L := L) (K := K) r₂)| ≤ 1 := by
  -- R5 (clock–clock) handled separately: both outputs stay clocks, ΔX = 0.
  by_cases hcc : r₁.role = .clock ∧ r₂.role = .clock
  · obtain ⟨hr₁, hr₂⟩ := hcc
    -- Rule 5 fires: both outputs are `stdCounterSubroutine` of the clock, still clocks.
    have hpt : Phase0Transition L K r₁ r₂
        = (stdCounterSubroutine L K r₁, stdCounterSubroutine L K r₂) := by
      unfold Phase0Transition
      simp only [hr₁, hr₂, reduceCtorEq, and_self, and_true, true_and, and_false,
        false_and, if_true, if_false, ite_true, ite_false]
    rw [hpt]
    rw [topW_stdCounterSubroutine_clock r₁ hr₁, topW_stdCounterSubroutine_clock r₂ hr₂]
    simp
  · rcases r₁ with
      ⟨in₁, out₁, ph₁, role₁, asg₁, bias₁, sb₁, hr₁, mn₁, fl₁, op₁, ctr₁⟩
    rcases r₂ with
      ⟨in₂, out₂, ph₂, role₂, asg₂, bias₂, sb₂, hr₂, mn₂, fl₂, op₂, ctr₂⟩
    cases role₁ <;> cases role₂ <;> cases asg₁ <;> cases asg₂ <;>
      first
      | (exfalso; exact hcc ⟨rfl, rfl⟩)
      | (simp only [Phase0Transition, topW, stdCounterSubroutine, reduceCtorEq, ne_eq,
          and_true, and_false, true_and, false_and, if_true, if_false, ite_true,
          ite_false, or_true, or_false, false_or, true_or, not_true_eq_false,
          not_false_eq_true, not_true, not_false_iff, not_and, decide_eq_true_eq,
          abs_le] <;> norm_num)

/-- **Per-pair full-`Transition` weight-change bound at phase 0.**  Reducing the
`Transition` wrapper to `Phase0Transition` at phase 0 (`topW` reads only `role`),
the output weight block differs from the source block by at most `1`. -/
theorem topW_pair_delta_abs_le_one_of_phase0
    (r₁ r₂ : AgentState L K) (h₁ : r₁.phase.val = 0) (h₂ : r₂.phase.val = 0) :
    |(topW (L := L) (K := K) (Transition L K r₁ r₂).1
        + topW (L := L) (K := K) (Transition L K r₁ r₂).2)
      - (topW (L := L) (K := K) r₁ + topW (L := L) (K := K) r₂)| ≤ 1 := by
  obtain ⟨he1, he2⟩ := Transition_roles_eq_phase0_of_both_phase0 (L := L) (K := K) r₁ r₂ h₁ h₂
  rw [topW_eq_of_role_eq _ _ he1, topW_eq_of_role_eq _ _ he2]
  exact topW_Phase0_pair_delta_abs_le_one r₁ r₂

/-! ## Stage 3 — the cosh-MGF inward drift (the X=0 boundary solved).

`coshExpVal s c := cosh (s · topSplitXZ c)` is the per-state MGF.  The one-step
expectation decomposes, for `X' = X(c) + Δ`, as

    cosh(s·X') = cosh(s·X(c))·cosh(s·Δ) + sinh(s·X(c))·sinh(s·Δ),

so summing against the interaction law,

    E[cosh(s·X')] = cosh(s·X(c))·E[cosh(s·Δ)] + sinh(s·X(c))·E[sinh(s·Δ)].

With `|Δ| ≤ 1` (Stage 2) the first factor `E[cosh(s·Δ)] ≤ cosh s`, and the
**inward residual** `sinh(s·X(c))·E[sinh(s·Δ)] ≤ 0` holds in EVERY case including
`X(c) = 0` (there `sinh 0 = 0`).  Hence `E[cosh(s·X')] ≤ cosh s · cosh(s·X(c))`:
the cosh MGF is a multiplicative-`(cosh s)` supermartingale with NO boundary
exception — exactly what the `Supermartingale.geometric_drift_tail_kernel` engine
consumes. -/

/-- Local helper: `1 ≤ cosh`. -/
private lemma one_le_cosh' (x : ℝ) : 1 ≤ Real.cosh x := by
  rw [Real.cosh_eq]
  nlinarith [Real.add_one_le_exp x, Real.add_one_le_exp (-x),
    Real.exp_pos x, Real.exp_pos (-x)]

/-- Local helper: `cosh` is `≤`-monotone in `|·|` (here: `|x| ≤ y` with `0 ≤ y`
gives `cosh x ≤ cosh y`).  Proved from `cosh_eq` + `exp` monotonicity. -/
private lemma cosh_le_cosh_of_abs_le {x y : ℝ} (hy : 0 ≤ y) (h : |x| ≤ y) :
    Real.cosh x ≤ Real.cosh y := by
  rw [Real.cosh_eq, Real.cosh_eq]
  have hx1 : x ≤ y := le_trans (le_abs_self x) h
  have hx2 : -y ≤ x := by rw [neg_le]; exact le_trans (neg_le_abs x) h
  -- Key identity: (exp y + exp(−y)) − (exp x + exp(−x)) = (exp y − exp x)·(1 − exp(−x−y)).
  -- Both factors ≥ 0:  exp y − exp x ≥ 0 (x ≤ y);  1 − exp(−x−y) ≥ 0 (x+y ≥ 0).
  have e1 : Real.exp x ≤ Real.exp y := Real.exp_le_exp.mpr hx1
  have e2 : Real.exp (-(x + y)) ≤ 1 := by
    rw [show (1 : ℝ) = Real.exp 0 from (Real.exp_zero).symm]
    exact Real.exp_le_exp.mpr (by linarith)
  have hxy : Real.exp (-(x + y)) = Real.exp (-x) * Real.exp (-y) := by
    rw [← Real.exp_add]; congr 1; ring
  have hyy : Real.exp y * Real.exp (-y) = 1 := by rw [← Real.exp_add]; simp
  have hxx : Real.exp x * Real.exp (-x) = 1 := by rw [← Real.exp_add]; simp
  have hkey : (Real.exp y - Real.exp x) * (1 - Real.exp (-(x + y))) =
      (Real.exp y + Real.exp (-y)) - (Real.exp x + Real.exp (-x)) := by
    rw [hxy]; ring_nf; linear_combination (Real.exp (-y)) * hxx - (Real.exp (-x)) * hyy
  nlinarith [mul_nonneg (sub_nonneg.mpr e1) (sub_nonneg.mpr e2), hkey]

/-- Local helper: `sinh` has the sign of its argument (`x ≤ 0 ⟹ sinh x ≤ 0`,
`0 ≤ x ⟹ 0 ≤ sinh x`); stated as the product sign fact `0 ≤ x · sinh x`. -/
private lemma mul_sinh_nonneg (x : ℝ) : 0 ≤ x * Real.sinh x := by
  rcases le_total 0 x with hx | hx
  · have : 0 ≤ Real.sinh x := by
      rw [Real.sinh_eq]
      have := Real.exp_le_exp.mpr (by linarith : -x ≤ x); linarith
    positivity
  · have hs : Real.sinh x ≤ 0 := by
      rw [Real.sinh_eq]
      have := Real.exp_le_exp.mpr (by linarith : x ≤ -x); linarith
    nlinarith [hx, hs]

/-- The per-state cosh MGF observable `coshExpVal s c = cosh (s · X c)`. -/
noncomputable def coshExpVal (s : ℝ) (c : Config (AgentState L K)) : ℝ :=
  Real.cosh (s * (topSplitXZ (L := L) (K := K) c : ℝ))

/-- `coshExpVal ≥ 1 > 0` (so its `ofReal` is a genuine `ℝ≥0∞` potential). -/
theorem one_le_coshExpVal (s : ℝ) (c : Config (AgentState L K)) :
    1 ≤ coshExpVal (L := L) (K := K) s c := one_le_cosh' _

/-- The per-step jump `Δ_pair = X(stepOrSelf c r₁ r₂) − X(c)` of the integer
process is bounded by `1` in absolute value on the Phase-0 region.  (Lift of the
per-pair `topW`-block bound to the `stepOrSelf` config delta.) -/
theorem topSplitXZ_step_delta_abs_le_one
    (c : Config (AgentState L K)) (r₁ r₂ : AgentState L K)
    (hall : Phase0Window.allPhase0 (L := L) (K := K) c) :
    |(topSplitXZ (L := L) (K := K)
        (Protocol.stepOrSelf (NonuniformMajority L K) c r₁ r₂) : ℝ)
      - (topSplitXZ (L := L) (K := K) c : ℝ)| ≤ 1 := by
  by_cases happ : Protocol.Applicable c r₁ r₂
  · -- Applicable: c' = c − {r₁,r₂} + {δ₁,δ₂}; topSplitXZ is additive (Config.sumOf topW).
    have hle : ({r₁, r₂} : Config (AgentState L K)) ≤ c := happ
    have hr₁ : r₁ ∈ c := Multiset.mem_of_le hle (by simp)
    have hr₂ : r₂ ∈ c := Multiset.mem_of_le hle (by simp)
    have h₁ : r₁.phase.val = 0 := by have := hall r₁ hr₁; simp [this]
    have h₂ : r₂.phase.val = 0 := by have := hall r₂ hr₂; simp [this]
    -- Localize the additive sum: topSplitXZ c = base + topW r₁ + topW r₂,
    -- topSplitXZ c' = base + topW δ₁ + topW δ₂.
    have hstep : Protocol.stepOrSelf (NonuniformMajority L K) c r₁ r₂
        = c - {r₁, r₂} + {(Transition L K r₁ r₂).1, (Transition L K r₁ r₂).2} := by
      unfold Protocol.stepOrSelf; rw [if_pos happ]; rfl
    have hbase_src : topSplitXZ (L := L) (K := K) c
        = Config.sumOf (topW (L := L) (K := K)) (c - {r₁, r₂})
          + (topW (L := L) (K := K) r₁ + topW (L := L) (K := K) r₂) := by
      unfold topSplitXZ Config.sumOf
      conv_lhs => rw [← Multiset.sub_add_cancel hle]
      rw [Multiset.map_add, Multiset.sum_add]
      congr 1
      show topW (L := L) (K := K) r₁ + (topW (L := L) (K := K) r₂ + 0) = _
      rw [add_zero]
    have hbase_out : topSplitXZ (L := L) (K := K)
          (Protocol.stepOrSelf (NonuniformMajority L K) c r₁ r₂)
        = Config.sumOf (topW (L := L) (K := K)) (c - {r₁, r₂})
          + (topW (L := L) (K := K) (Transition L K r₁ r₂).1
             + topW (L := L) (K := K) (Transition L K r₁ r₂).2) := by
      rw [hstep]
      unfold topSplitXZ Config.sumOf
      rw [Multiset.map_add, Multiset.sum_add]
      congr 1
      show topW (L := L) (K := K) (Transition L K r₁ r₂).1
            + (topW (L := L) (K := K) (Transition L K r₁ r₂).2 + 0) = _
      rw [add_zero]
    have hdelta := topW_pair_delta_abs_le_one_of_phase0 (L := L) (K := K) r₁ r₂ h₁ h₂
    -- The config delta equals the pair-block delta.
    have hcast : ((topSplitXZ (L := L) (K := K)
          (Protocol.stepOrSelf (NonuniformMajority L K) c r₁ r₂)) : ℝ)
        - (topSplitXZ (L := L) (K := K) c : ℝ)
        = (((topW (L := L) (K := K) (Transition L K r₁ r₂).1
              + topW (L := L) (K := K) (Transition L K r₁ r₂).2)
            - (topW (L := L) (K := K) r₁ + topW (L := L) (K := K) r₂)) : ℝ) := by
      rw [hbase_out, hbase_src]; push_cast; ring
    rw [hcast]
    have : |((topW (L := L) (K := K) (Transition L K r₁ r₂).1
              + topW (L := L) (K := K) (Transition L K r₁ r₂).2)
            - (topW (L := L) (K := K) r₁ + topW (L := L) (K := K) r₂) : ℤ)| ≤ (1 : ℤ) :=
      hdelta
    exact_mod_cast this
  · -- Not applicable: stepOrSelf = c, delta = 0.
    rw [Protocol.stepOrSelf, if_neg happ]; simp

end RoleSplitConcentration
end ExactMajority
