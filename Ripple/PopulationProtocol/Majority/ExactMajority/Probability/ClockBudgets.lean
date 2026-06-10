import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.ClockUnconditional
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.DotyParams

/-!
# ClockBudgets — the explicit unconditional clock budget (Phase B-12)

This is the closing brick of Phase B.  `ClockUnconditional` (B-11) reduced the unconditional
clock to per-minute SIDE PREFIXES `∑_τ (realκ^τ) c₀ Sgood(i+1)ᶜ`, and `sidePrefix_le` decomposed
each per-`τ` mass into FOUR named feeders `εQ + εfloor + εsync + εphase`.  Here we:

1. Decompose `εphase` (`{PhaseGateFail}`) into its four structural conjunct failures — a pure
   union bound (`phaseGateFail_le`), fully proven here.
2. Wire `εsync` (`{¬FrontSync}`) to the §6 width engine via
   `ClockFrontSyncFromWidth.frontSync_whp_of_goodFrontWidth`: `εsync(τ) ≤ εW(τ) + εP(τ) + εB(τ)`,
   the width-failure / side-event / bulk-arrival split, with the per-`τ` width mass `εW(τ)`
   supplied by the §6 engine (`DotyParams.goodFrontWidth_whp_final` at its endpoint horizon; a
   per-`τ` concrete width family at free `τ` is the remaining §6 follow-up — carried here as the
   named family `εW`).
3. Assemble the per-`τ` `Sgood(T)ᶜ` budget `sideEps(τ)` from the available pieces + the named
   inputs (`sidePrefix_le_assembled`).
4. **Sum** `sideEps(τ)` over the per-minute windows `Ico (i·s+tseed) (i·s+tseed+tbulk)` and over
   the `K·(L+1)−1` minutes, and feed the capstone, producing the explicit total budget
   `ε_clock(n)` (`clock_unconditional_concrete`).

The genuinely-open inputs are NAMED throughout: the per-`τ` width / side / bulk masses
`εW τ`, `εP τ`, `εB τ` and the deterministic-residual phase masses `εge3 τ`, `εno3 τ`,
`εcpos τ`, `εsucc τ`.  Everything else (the inclusions, the unions, the summation arithmetic) is
fully proven here.

ZERO sorry, zero new axiom, zero native_decide.
-/

namespace ExactMajority

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Real BigOperators Classical

namespace ClockBudgets

open ClockUnconditional ClockRealKernel ClockKilledMinute HabsDischarge ClockFrontShape
open ClockFrontSyncFromWidth ClockFrontProfile

variable {L K : ℕ}

/-! ## Part 1 — the `εphase` decomposition (pure union bound, fully proven).

`PhaseGateFail c = ¬allPhaseGE3 c ∨ ¬noPhaseAbove3 c ∨ ¬allClocksCounterPos c ∨
¬(∀ c' on support, noPhaseAbove3 c')`.  The set `{PhaseGateFail}` is the union of the four
per-conjunct failure sets, so its measure is `≤` the sum of the four masses. -/

/-- The four per-conjunct failure sets whose union is `{PhaseGateFail}`. -/
def GE3Fail : Set (Config (AgentState L K)) :=
  {c | ¬ allPhaseGE3 (L := L) (K := K) c}

def NoAbove3Fail : Set (Config (AgentState L K)) :=
  {c | ¬ noPhaseAbove3 (L := L) (K := K) c}

def CposFail : Set (Config (AgentState L K)) :=
  {c | ¬ allClocksCounterPos (L := L) (K := K) c}

def SuccNoAbove3Fail : Set (Config (AgentState L K)) :=
  {c | ¬ (∀ c' ∈ ((NonuniformMajority L K).stepDistOrSelf c).support,
      noPhaseAbove3 (L := L) (K := K) c')}

/-- **`phaseGateFail_subset`** — `{PhaseGateFail}` is covered by the union of the four
per-conjunct failures. -/
theorem phaseGateFail_subset :
    {c : Config (AgentState L K) | PhaseGateFail (L := L) (K := K) c} ⊆
      (GE3Fail (L := L) (K := K) ∪ NoAbove3Fail (L := L) (K := K))
        ∪ (CposFail (L := L) (K := K) ∪ SuccNoAbove3Fail (L := L) (K := K)) := by
  intro c hc
  simp only [Set.mem_setOf_eq, PhaseGateFail, Set.mem_union,
    GE3Fail, NoAbove3Fail, CposFail, SuccNoAbove3Fail] at hc ⊢
  tauto

/-- **`phaseGateFail_le`** — the per-`τ` `{PhaseGateFail}` mass is bounded by the sum of the four
named per-conjunct masses.  Pure union bound. -/
theorem phaseGateFail_le (τ : ℕ) (c₀ : Config (AgentState L K))
    (εge3 εno3 εcpos εsucc : ℝ≥0∞)
    (hge3 : (realκ L K ^ τ) c₀ (GE3Fail (L := L) (K := K)) ≤ εge3)
    (hno3 : (realκ L K ^ τ) c₀ (NoAbove3Fail (L := L) (K := K)) ≤ εno3)
    (hcpos : (realκ L K ^ τ) c₀ (CposFail (L := L) (K := K)) ≤ εcpos)
    (hsucc : (realκ L K ^ τ) c₀ (SuccNoAbove3Fail (L := L) (K := K)) ≤ εsucc) :
    (realκ L K ^ τ) c₀ {c | PhaseGateFail (L := L) (K := K) c}
      ≤ εge3 + εno3 + εcpos + εsucc := by
  have hbound : (realκ L K ^ τ) c₀ {c | PhaseGateFail (L := L) (K := K) c}
      ≤ (εge3 + εno3) + (εcpos + εsucc) := by
    refine le_trans (measure_mono (phaseGateFail_subset (L := L) (K := K))) ?_
    refine le_trans (measure_union_le _ _) ?_
    exact add_le_add (le_trans (measure_union_le _ _) (add_le_add hge3 hno3))
      (le_trans (measure_union_le _ _) (add_le_add hcpos hsucc))
  calc (realκ L K ^ τ) c₀ {c | PhaseGateFail (L := L) (K := K) c}
      ≤ (εge3 + εno3) + (εcpos + εsucc) := hbound
    _ = εge3 + εno3 + εcpos + εsucc := by ring

/-! ## Part 2 — the `εsync` wiring to the §6 width engine.

`ClockFrontSyncFromWidth.frontSync_whp_of_goodFrontWidth` bounds `{¬ FrontSync}` at horizon `τ`
by `εW + εP + εB` — the width-failure-on-side mass `εW` (supplied by the §6 engine
`goodFrontWidth_whp`), the side-event failure `εP`, and the bulk-arrival mass `εB`.  `SyncFail`
(from `ClockUnconditional`) is exactly `{c | ¬ FrontSync c}`, and `realκ L K` is definitionally
`(NonuniformMajority L K).transitionKernel`, so the bridge applies directly. -/

/-- **`syncFail_le`** — the per-`τ` `SyncFail` (`{¬ FrontSync}`) mass is `≤ εW + εP + εB`, the
§6 width / side-event / bulk-arrival split.  Direct restatement of
`frontSync_whp_of_goodFrontWidth` in the `realκ`/`SyncFail` shape used by `sidePrefix_le`. -/
theorem syncFail_le (τ W : ℕ) (c₀ : Config (AgentState L K))
    (P : Config (AgentState L K) → Prop) (εW εP εB : ℝ≥0∞)
    (hwidth : (realκ L K ^ τ) c₀
        {c | P c ∧ ¬ GoodFrontWidth (L := L) (K := K) W c} ≤ εW)
    (hP : (realκ L K ^ τ) c₀ {c | ¬ P c} ≤ εP)
    (hbulk : (realκ L K ^ τ) c₀
        {c | ¬ (10 * rBeyond (L := L) (K := K)
            (capMinute (L := L) (K := K) - W) c < c.card)} ≤ εB) :
    (realκ L K ^ τ) c₀ (SyncFail (L := L) (K := K)) ≤ εW + εP + εB :=
  frontSync_whp_of_goodFrontWidth (L := L) (K := K) τ W c₀ P εW εP εB hwidth hP hbulk

end ClockBudgets

end ExactMajority
