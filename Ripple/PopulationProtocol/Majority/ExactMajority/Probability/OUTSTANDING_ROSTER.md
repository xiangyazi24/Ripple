# OUTSTANDING ROSTER — what's left to make doty_theorem_3_1 FULLY unconditional

**Target.** `doty_theorem_3_1` conditional ONLY on `validInitial c₀` + `DotyRegime` + `card c₀ = n`
(zero carried residual).

**Already discharged (this run, all axiom-clean, committed):** the vacuity disproofs; the contracting
engine; all 11 gaps; the capstone (non-vacuous headline); the cascade structure (seam advance, conserved
invariants, per-phase Post structures, per-phase floors); Lemma 5.1; the 11 work instances CONCRETE
(`workConstructed`); slots 2/4/9/10 fully regime-closed; the contracting slots' BUDGET + STRUCT floors
(species caps + regime arithmetic ≤ 1/(3n²)); the reachability-conditioned clock tail
(`mgf_depletion_tail_reachable`).

---

## TIER 1 — the LINCHPIN (closes the most)  — REFINED 2026-06-13: clock COUNT decouples from C-A

**L1. The clock-count cap on the reachable trajectory.**  KEY FINDING (2026-06-13): the clock-count
cap that the depletion tail needs (`hcap_reach`) is DETERMINISTIC and uses ONLY `allPhaseGE3`, NOT
`FrontSync`/`Q_mix.crossedT` — so it DECOUPLES from the hard §6 front-shape concentration (C-A).
Reason: `HabsDischarge.clockCount_pair_eq` shows roles are never created/destroyed once both interacting
agents are at phase ≥ 3, so clock-count is conserved by every transition; `allPhaseGE3` is one-step closed.
- LANDED (this run, `ClockCapReachable.lean`): `clockCount_stepRel` + `allPhaseGE3_stepRel` (StepRel-closed),
  `clockGE3Inv_reachable` (ReflTransGen propagation), `count_le_clockCount` (the count bridge,
  `count_filter_of_pos`), and `hcap_reach_of_entry` — supplies `ReachableClockTail.mgf_depletion_tail_reachable`'s
  `hcap_reach` at `m := mC` from the phase-3 entry invariant `ClockGE3Inv mC c₀ = (clockCount c₀ = mC ∧ allPhaseGE3 c₀)`.
  ⟹ the clock per-τ depletion cap is regime-CLOSED to the bare phase-3 entry invariant, WITHOUT C-A.
- ENTRY ESTABLISHED (this run, `clockGE3_entry_of_roleSplitGood`, axiom-clean): from `RoleSplitGood η n c`
  (the phase-0 whp role-split event, |Clock| ≥ n/5, `clockCount_linear_of_RoleSplitGood`) + `allPhaseGE3 c`
  (the phase-3 seam postcondition), get `∃ mC, ClockGE3Inv mC c ∧ mC ≥ n/5` with realized `mC = clockCount c`.
- FULL CHAIN LANDED: `clockGE3_entry_of_roleSplitGood` → `clockGE3Inv_reachable` → `clock_perτ_from_entry`
  (the `hClockPerτ` input `clock_prefix_fit` consumes) → contracting slots' clock-depletion budget.
- L1 IS CLOSED to two EXISTING carried residuals: `RoleSplitGood` (phase-0 whp, landed via
  `phase0_roleSplit_whp`) + `allPhaseGE3` at the phase-3 entry (the carried `hge_all`). The clock COUNT
  no longer needs ANY front-shape (C-A); only the clock TIMING does.

---

## TIER 2 — the genuine concentration residuals (the truly-open paper content)

**C-A. FrontSync front-shape maintenance** (`ClockFrontWidth.hcap_all` = `FrontSyncConc.hwin_all` =
the named `rEnvelope_maintained`). The DEEPEST remaining residual; full skeleton now mapped in
`../CLOCK_FRONTSHAPE_ROADMAP.md` (Doty §6, ChatGPT-cross-checked 2026-06-13).
- The ENTIRE clock chain reduces to this ONE input: `rBeyond (cap−1) c ≤ Bcap` on reachable FrontSync
  configs. Everything else is PROVEN (per-level squaring `rBeyond_seed_le_rBeyondSq`, union bound
  `frontSync_union_horizon`, 1/poly budget, `FrontSyncConcentration_remaining` discharge).
- CRITICAL CORRECTION: the naive deterministic within-envelope maintenance is FALSE — Doty's Lemma 6.3
  carries an ESSENTIAL early-drip ghost term `d_{≥i+1}` (a single lucky drip breaks the bare recurrence
  at tiny tail masses). The honest transfer is a cumulative-tail theorem WITH the early-drip ghost, valid
  only in `n^{−0.45} ≤ c_{≥i} ≤ 0.1`, anchored at the subcritical entry.
- LEANER BYPASS for Theorem 3.1 (recommended): formalize the hour-level `ClockHourGood` (Thm 6.9 hour
  length/gap + Lemma 6.10's clean Azuma supermartingale `Φ = m_{>h} − 1.1 c_{>h}`); the majority part needs
  only `c_{≥r+2} ≤ 10^{−4}` (the two-level tail), not the full envelope. Ripple's `DiscreteFreedman`/
  `bernstein_optimal` are the Azuma tools. See roadmap §"LEANER bypass" for the priority-ordered plan.

**C-B. Role-split phase-0 stages.** work⟨0⟩ = `roleSplitW_of_two_stage` of 3 stages:
- Stage-1 Lemma-5.1 Chernoff: the LOWER-tail is DONE (`Lemma51Discharge.assignable_floor_lower_tail`).
  REMAINING: the per-step rate `q` (counted) + `hstep` (gate-Lipschitz) inputs of `Stage1FloorResidual`.
- Stage-2 εfloor: provably ZERO (`stage2_killedEscape_eq_zero`, landed).
- The 2 chain links + the Janson hitting horizons (regime arithmetic).

**C-C. §10 seam-entry concentration.** The `buildSeamHalf`/`SeamGlue` inputs not yet regime-closed:
- the seed-step events `hSeedStep`/`SeedStepEvent` (needs the drained-counter state, `seedStepEvent_needs_drained_state`);
- the no-overshoot timing carry `hPreToNoOvershoot` (seam-entry phase/clock separation).
(hDrift = 1/n² and the no-overshoot cumulative tail are DONE.)

---

## TIER 3 — mechanical / arithmetic (armed, no new math)

**M1.** Wire the regime-closed slots into `workFromRegime`: contracting 1/5/6/7/8 (via
`work{N}_clockstruct_gated` once L1 closes the clock cap) + landed 2/4/9/10 + 0/3 + seam.
**M2.** `faithfulResidual_of_valid` / `faithfulWorkSeamCore_of_valid` → `doty_theorem_3_1` with zero
carried residual (the false `hReach10` is already eliminated; the `whnf` budget/Esum lift is already in place).
**M3.** `hcard : card c₀ = n` — fold `n := card c₀` (then `rfl`) or carry as a legitimate population-size
precondition (`validInitial` is per-agent, does not pin `card`).

---

## Summary of genuine remaining math
- **L1** (clock-structure entry) — structural/reachability; mostly landed closure, needs the phase-3 entry.
- **C-A** (FrontSync O(log log n) width) — the hardest open concentration.
- **C-B** (role-split q/hstep + horizons) — counted/arithmetic; Lemma 5.1 done.
- **C-C** (seam seed/timing) — two §10 inputs.
- Everything else is mechanical wiring (M1–M3).
