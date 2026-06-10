# Doty Thm 3.1 time half — the post-Lemma-6.3 campaign plan

_Drafted 2026-06-09 evening, while agent 3 closes the last Lemma-6.3 wiring item (hB).
Position at drafting: windowedFrontProfile_whp + goodFrontWidth_whp + climbBound_whp landed on the
real kernel (0-sorry, axiom-clean, uisai2-verified ×3). This file plans everything from there to
the unconditional Theorem 3.1 time half._

## Where the campaign stands

PROVEN (real kernel, whp, modulo the hB instantiation in flight):
- The §6 coupled time-window engine: per-level squaring recurrence (Thm 6.5 windowed form),
  GoodFrontWidth = the moving-frame width invariant, ClimbBound. This was the deep core.
- Lemma 6.10 hour coupling (HourCouplingV2, Azuma) — proven earlier, not yet wired.
- Phases 2 & 9 untimed PhaseConvergence instances.
- The abstract AND transferred real-kernel per-minute clock machinery (ClockReal* chain) — but its
  FrontSync maintenance still consumes the FALSE `hwin_all`; that consumption is what Phase B fixes.
- Correctness half: complete (stable_majority_correct).

## Phase B — the clock rewire (drop `hwin_all`)  [first; ~12–18 bricks]

Goal: the real-kernel per-hour O(log n) clock as an unconditional whp theorem.
1. **Fix the concrete parameters ONCE, up front**: θn(n), tt(n), w(n), KK(n), Tcap, the scale
   floor N₀ (currently n ≥ 25641, θn ≥ 30000 carried abstractly). Every later discharge uses these;
   choosing them first avoids rework. Deliverable: a `DotyParams`-style structure or a fixed set of
   defs + the norm_num facts they satisfy.
2. Discharge the carried scale hypotheses of windowedFrontProfile_whp_packaged / goodFrontWidth_whp /
   climbBound_whp at those parameters → clean whp statements with hypotheses `N₀ ≤ n` only.
3. Rethread the FrontSync consumers: FrontSyncConc / ClockFrontWidth / ClockEnvMaint /
   ClockFullJoint currently carry `hwin_all` (FALSE as ∀-reachable). Replace the input with the
   GoodFrontWidth-whp event via `frontSync_of_goodWidth_of_bulk_below` (deterministic glue, proven)
   + a horizon union. NOTE: not a find-replace — the existing statements are shaped for a
   deterministic invariant; they need whp-event versions (mirror how real_front_squares_whp wraps
   its event). Audit each consumer file for what it actually needs.
4. Re-derive `clock_real_faithful_O_log_n` (the composed per-hour clock) on the rewired inputs;
   retire the false-hypothesis variants; update `clock_honest_verdict`.

## Phase C — the timed phase instances  [the volume; ~25–35 bricks; PARALLELIZABLE]

A1's `compose_n_phases` (PhaseConvergence.lean) needs 11 instances; 2 & 9 exist. Remaining:
- Phase 3 = the clock itself → falls out of Phase B (the big one).
- Phases 0, 1: initialization + role assignment + smallBias counters. Includes the **clock-count
  Θ(n)** concentration (the role split) — an input the clock constants implicitly need; make it
  explicit here.
- Phases 4, 5, 6, 7, 8, 10: per-phase epidemics / counter timeouts at constant fraction — A0-style
  analyses on existing machinery (ConstantDensityEpidemic, WindowConcentration, stdCounter timing,
  the new gated engines where rates are conditional).
PARALLELIZATION: each phase analysis goes in ITS OWN new file (Phase4Convergence.lean, …) so
multiple subagents can run concurrently without single-file races. Phase 2/9's existing instance
(Phase2Convergence.lean) is the template.
Risk note: phases 5–8 interact with Reserve agents & sampling (paper §7.1) — read the paper section
before speccing each; do not guess the per-phase event structure.

## Phase D — composition  [~8–12 bricks]

1. Wire Lemma 6.10 (hour_coupling_v2) + the Phase-B clock into the phase-3 timed instance
   (hours advance together ⟹ the phase-3 window closes in O(log n)).
2. `compose_n_phases` with all 11 instances → `doty_time_headline` UNCONDITIONAL:
   stabilization in O(log n) parallel time whp. Update every honest-verdict marker.

## Phase E — expected time  [~8–15 bricks]  — SCOPED 2026-06-10 (paper read done)

Paper's argument (§7 wrap-up, "We finally justify that the expected stabilization time is
O(n log n) [interactions]"): three-event split AT TIME 0, not a from-any-reachable-config restart:
- **Good** (whp ≥ 1 − O(1/n²)): all phase whp-events hold → stabilize in O(log n) parallel time.
- **Bad-with-big-clock** (prob ≤ O(1/n²), |C| ≥ 0.24n by Lemma 5.2 whp): timed phases still
  advance via counters in expected O(log n) each (Thm 6.9 + Chernoff on counter rounds), untimed
  phases pass by epidemic expected O(log n) → reach backup Phase 10, which stabilizes in expected
  O(n log n) parallel time (**Lemma 7.7**). Contribution O(1/n²)·O(n log n) = o(1).
- **Tiny-clock** (|C| = o(n); note |C| ≥ 2 always by Lemma 5.2's deterministic part, and |C| is
  FIXED after Phase 0): probability super-polynomially small; conditional time at most poly(n)
  (counter decrements at rate ≥ |C|/n ≥ 2/n). Negligible product.

Lean bricks:
- **E1** `Probability/ExpectedHitting.lean` (NEW): hitting-time expectation toolkit on kernel
  powers. E[T] = ∑_t P(T > t) (or block form E[T] ≤ s·∑_k P(T > k·s)); the geometric-tail lemma
  (∀ config in a closed class, P(not done in s steps) ≤ q ⟹ P(T > k·s) ≤ q^k ⟹ E[T] ≤ s/(1−q));
  the conditioning-free split E[T] ≤ t₀ + ∑_{t≥t₀} P(T>t). Generic, no protocol content.
  **DONE 2026-06-10** (0-sorry, axiom-clean = [propext, Classical.choice, Quot.sound] on all 13
  thms; single-file EXIT_0). Generic over `K : Kernel α α` `[IsMarkovKernel K]` + fixed measurable
  `Done` set + absorption hyp `∀ x ∈ Done, K x Doneᶜ = 0` (matches GeometricDrift's generic style,
  so it applies directly to `(NonuniformMajority L K).transitionKernel`). Design choice: closure
  class is taken to be `Doneᶜ` itself — the per-block hypothesis is `∀ b ∈ Doneᶜ, (K^s) b Doneᶜ ≤ q`
  ("from every not-done state, s steps finish w.p. ≥ 1−q"), no separate invariant-class bookkeeping
  needed. `expectedHitting K c Done := ∑' t, (K^t) c Doneᶜ` (= E[T] under the standard tail-sum
  identity). Delivered (signatures abbreviated, all in namespace `ExactMajority`):
  - `expectedHitting` (def), `expectedHitting_eq_tsum`.
  - `bad_antitone` / `bad_antitone_le` — `(K^t) c Doneᶜ` antitone in `t` from absorption (Lemma 0).
  - `pow_absorbing` — `Done` absorbing for 1 step ⟹ absorbing for m steps.
  - `expectedHitting_le_block` — `E[T] ≤ s · ∑' k, (K^(k·s)) c Doneᶜ` (block form, `s ≠ 0`).
  - `bad_block_contracts_from` / `bad_block_contracts` — `(K^(m+s)) c₀ Doneᶜ ≤ q·(K^m) c₀ Doneᶜ`.
  - `bad_block_geometric` — `(K^(k·s)) c₀ Doneᶜ ≤ q^k`.
  - `expectedHitting_geometric` — `E[T] ≤ s · (1−q)⁻¹`.
  - `kernel_pow_le_one`, `expectedHitting_split` — `E[T] ≤ t₀ + ∑' t, (K^(t₀+t)) c Doneᶜ`.
  - `tail_le_block`, `bad_block_geometric_from` — shifted-base block + geometric helpers.
  - `expectedHitting_split_geometric` — **Phase-E4 capstone**: hyps `(K^t₀) c₀ Doneᶜ ≤ δ` +
    per-block `q` (`s≠0`) ⟹ `E[T] ≤ t₀ + δ·s·(1−q)⁻¹`. Nothing left out.
- **E2** Lemma 7.7: Phase-10 backup expected O(n log n) parallel time. Correctness-side
  infrastructure exists (Analysis/Phase10Backup.lean: signed sums, active counts). Probability
  side: cancel/spread reactions at rate ≥ activeCount²/n²-style → coupon-collector/geometric
  sums. Uses E1's geometric-tail on the active-count potential.
  **GENERIC ENGINE 100% CLOSED 2026-06-10** (E2-6/7/8: arbitrary-start occupation + capstone +
  harmonic eval, NO residual hypothesis; remaining = pure protocol instantiation, 2 bricks B1/B2 below;
  0-sorry, axiom-clean = [propext, Classical.choice, Quot.sound]; single-file EXIT_0).
  Convention: all bounds in INTERACTION COUNTS (= kernel steps); parallel time = interactions/n,
  so cancel = O(n²), coupon stages = O(n² log n) each. Delivered:
  - `ExpectedHitting.lean` (appended, generic): `expectedHitting_one_step` (one-step success ≥ p ⇒
    E[T] ≤ p⁻¹), `expectedHitting_one_step_q` (failure ≤ q ⇒ E[T] ≤ (1-q)⁻¹). SHAs ceb63d86.
  - `Probability/Phase10ExpectedTime.lean` (NEW). Generic `Coupon` section over `K : Kernel α α`,
    `Φ : α → ℕ`, `Done = potDone Φ = {Φ = 0}`:
    * `potDone/potAbove/potBelow` (+ measurable/compl), `compl_potDone`.
    * **chaining** `bad_split_through_mid`, `expectedHitting_le_through_mid`
      (`Done ⊆ Mid` ⇒ E[hit Done] ≤ E[hit Mid] + ∑ₜ P(Mid∖Done at t)). SHA d101ca6f.
    * **occupation engine** `PotNonincr K Φ` (one step never raises Φ), `potBelow_absorbing`,
      `pow_above_eq_zero_of_start_le` ({Φ>m} stays 0-mass from Φc≤m), `level_occ_contract`,
      `level_occ_geometric`, `level_occ_expectedHitting` (CONSTRAINED start Φc≤m ⇒
      E[hit {Φ<m}] ≤ (1-q)⁻¹). SHA 3c8ad20b.
    * **coupon assembly** `occLevel`, `expectedHitting_eq_tsum_occLevel` (exact occupation
      decomposition E[hit Done] = ∑'ₘ occLevel(m+1)), `coupon_expectedHitting_le_of_occBounds`
      (per-level occ ≤ (1-qₘ)⁻¹ + high-level vanishing ⇒ E[hit Done] ≤ ∑_{m=1}^M (1-qₘ)⁻¹,
      the harmonic sum). SHA e2e1849e.
  - **E2-6** SHA e47ef68c: BLOCKER CLOSED. `occLevel_le` (arbitrary-start level occupation ≤
    (1-q)⁻¹). Route taken: NOT a pathwise strong-Markov σ-algebra — induct on the time-TRUNCATED
    occupation `occLevelUpTo t = ∑_{i<t}(K^i)c{Φ=m}`, uniform-in-c bound `≤(1-q)⁻¹` for every t
    (`occLevelUpTo_le`): Φc≤m subcase = constrained `occLevel_le_of_start_le` (partial ≤ tsum);
    Φc>m subcase = i=0 term vanishes + ONE Chapman-Kolmogorov step pushes ∑ onto successors,
    ∫ over Markov kernel Kc gives IH·(Kc univ)=IH. tsum limit via `ENNReal.tsum_eq_iSup_nat`+`iSup_le`.
    No PotNonincr needed in the Φc>m branch (pure CK). 0-sorry axiom-clean.
  - **E2-7** SHA 93b9e3dc: `coupon_expectedHitting_le` — generic capstone FULLY discharged (hocc by
    occLevel_le, hhi by new `occLevel_eq_zero_of_high`). No residual hypothesis. E[hit {Φ=0}] ≤
    ∑_{m=1}^M (1-qₘ)⁻¹ from just PotNonincr + hdrop + Φc≤M. 0-sorry axiom-clean.
  - **E2-8** SHA d1149f62: `coupon_sum_le_of_uniform` + `coupon_expectedHitting_le_uniform` — harmonic
    eval (crude): uniform per-level ceiling (1-qₘ)⁻¹≤r ⇒ E[hit] ≤ M·r (=O(n³) for M=O(n),r=n(n-1));
    sharp n(n-1)Hₙ=O(n²logn) is a constant refinement of the same ∑1/m, orthogonal to engine.
    0-sorry axiom-clean. **GENERIC PROBABILITY/COUPON ENGINE NOW 100% CLOSED end-to-end.**
  - **REMAINING = pure protocol instantiation** (2 bricks, both in Analysis/Phase10Backup land; engine
    carries no further obligation). Precise goals (also in Phase10ExpectedTime.lean tail doc):
    (B1) `PotNonincr K Φ` (Φ∈{activeBCount,wrongACount}): support template
    (Phase0Convergence.phaseBelowCount_step_le) ⇒ per-pair `Φ{Transition r₁ r₂}≤Φ{r₁,r₂}` via
    countP additivity. **SCOPING CAVEAT** (newly pinned): per-pair bound is FALSE for the full
    kernel — enterPhase10/epidemic entry create active-B. Holds only on phase-10-restricted
    subdynamics ⇒ must run stages on absorbed/restricted kernel under all-phase-10 invariant, OR
    add a PotNonincr-relative-to-invariant engine variant. Invariant-threading = brick 1.
    (B2) per-level drop qₘ=1-m/(n(n-1)): needs real-kernel analogue of step_advance_prob
    (interactionPMF(r₁,r₂) mass lower bound for an applicable AgentState pair, via stepDist=map
    scheduledStep interactionPMF as in ClockOLogN/ClockFaithful) + class-aggregation: SUM that
    mass over the Finset of active-A×active-B useful pairs to reach ≥m/(n(n-1)) (state-multiplicity).
    Brick 2 = largest. Stage chaining via expectedHitting_le_through_mid, majority/tie via backupSignal.
  - **E2-10** SHA abb46a67: **B1 GENERIC invariant-relative engine DELIVERED** (design choice =
    invariant-threading, NOT restricted-kernel — cheaper, reuses abstract InvClosed instead of
    building a new kernel). New in Phase10ExpectedTime.lean (Coupon section): `InvClosed K Inv`
    (∀b, Inv b → K b {¬Inv}=0), `PotNonincrOn Inv K Φ` (drop only at Inv-states), and the full `_on`
    ladder: `pow_not_inv_eq_zero`, `pow_above_eq_zero_of_start_le_on`, `potBelow_absorbing_on`,
    `level_occ_contract_on`, `level_occ_geometric_on`, `occLevel_le_of_start_le_on`,
    `occLevelUpTo_le_on`, `occLevel_le_on`, `occLevel_eq_zero_of_high_on`, capstones
    `coupon_expectedHitting_le_on` + `coupon_expectedHitting_le_uniform_on` (E[hit {Φ=0}] ≤ M·r
    under InvClosed + PotNonincrOn + Inv-start at level ≤M + uniform ceiling r). Proofs mirror the
    unconditional ones; differ only by intersecting null sets with {¬Inv} (null via pow_not_inv).
    0-sorry axiom-clean [propext,Classical.choice,Quot.sound]. Inv intended = Phase10EpidemicPost
    (closure proof already worked out at Invariants.lean:7378-7400, re-derivable in-file from public
    Transition_left/right_phase_eq_10).
  - **E2-11** SHA 592b63c4: B2 cancel-stage per-pair drop, in-file (no Analysis edit). `applicable_of_mem_ne`
    (public re-derivation via Multiset.cons_le_of_notMem), `activeBCount_post_cancel_lt` (re-derives the
    Analysis-private per-pair drop from public Phase10Transition_activeA_activeB_outputs_T + countP_sub/add),
    `scheduledStep_activeA_activeB_in_drop` (an active-A/active-B pair lands in dropTarget activeBCount).
    Imports Phase10Backup + Phase0Convergence. 0-sorry axiom-clean.
  - **E2-12** SHA 84dbaa6a: B2 class-aggregation rectangle. `activeABPairs` (Finset = filter IsActiveA ×ˢ
    filter IsActiveB), `sum_interactionCount_activeAB = activeACount·activeBCount` via public
    `ClockRealMixed.sum_interactionCount_cross_disjoint` (disjoint A/B classes) + `HourCouplingV2.countP_eq_sum_count`.
    THIS RESOLVES the "state-multiplicity subtlety" — aggregate over the whole rectangle, not a fixed pair.
    0-sorry axiom-clean.
  - **E2-13** SHA 44afcd9d: **B2 cancel-stage DROP PROBABILITY DELIVERED**. `presentActiveABPairs`,
    `sum_interactionProb_presentActiveAB` (present-pair sum = full rectangle = activeACount·activeBCount/totalPairs,
    absent pairs interactionCount 0), `activeBCount_drop_prob`: on all-phase-10 with activeACount≥1,
    `transitionKernel c (dropTarget activeBCount c) ≥ activeBCount c / (n(n-1))`. Route = ClockOLogN preimage
    pattern via public `stepDistOrSelf_toMeasure_ge` + `PMF.toMeasure_apply_finset`. 0-sorry axiom-clean.
  - **CRITICAL SCOPING REFINEMENT (E2-13 discovery, supersedes the B1 caveat above).** The
    `PotNonincrOn Phase10EpidemicPost K activeBCount` hypothesis the engine needs is **FALSE even on
    all-phase-10 configs**: `Phase10Transition` Block 2 (active converts passive) makes a passive agent
    ADOPT an active-B partner's output → a NEW active-B. So activeBCount can INCREASE under phase-10 when
    both active-A AND active-B are present. The honest non-increase invariant is sharper:
      * **cancel stage** (Φ=activeBCount): NOT non-increasing under any phase-10-only invariant. The
        correct monotone is that the signed sum `activeACount−activeBCount` is CONSERVED
        (`phase10Transition_preserves_signedContribution`, public). In majority-A (signed sum = g > 0
        fixed), `activeBCount` is bounded by `activeACount = activeBCount + g` and DROPS to 0 by the cancel
        reaction; the engine should run on `Φ = activeBCount` with `Inv = {AllPhase10 ∧ signed sum = g}` —
        but non-increase still needs the no-spread argument. SIMPLEST FIX: the cancel stage is a single
        descent to activeBCount=0; use the E1 supermartingale/hitting bound directly with the conserved
        signed sum, OR add `activeBCount ≤ activeACount` to Inv and prove block-2 spread of B requires a
        passive partner which when present means activeACount also can spread (net signed conserved).
      * **coupon stages** (Φ=wrongACount, AFTER activeBCount=0): clean. `Inv = {AllPhase10 ∧ activeBCount=0}`
        is support-closed (no B present + signed sum = activeACount ≥ 0 ⇒ no B reappears: block-2 only
        spreads the present active outputs, all A/T) and under it `wrongACount` IS non-increasing (only A
        spreads / absorbs). This is the engine's clean instantiation. The activeBCount_drop_prob route
        (E2-13) transfers verbatim to wrongACount via the analogous public output lemmas
        (Phase10Transition_activeA_nonActiveB_outputs_A) — same rectangle aggregation, active-A × not-A.
    NET: B1 generic engine + B2 drop-probability machinery are DONE and axiom-clean. The remaining
    instantiation = (i) choose Inv per stage (cancel: signed-sum-conserved; coupon: AllPhase10∧activeBCount=0),
    (ii) prove `InvClosed` + `PotNonincrOn` for the COUPON stage (clean, no-B-spread), (iii) handle the
    cancel stage via conserved signed sum (the activeBCount monotone is subtler than a plain PotNonincrOn).
    All `_on` engine lemmas + the drop-probability lemma are reusable as-is.
  - **E2-14** SHA aedcbe8e: B2 coupon-stage per-pair drop (`wrongACount_post_convert_lt`,
    `scheduledStep_activeA_wrongB_in_drop`) via public `Phase10Transition_activeA_nonActiveB_outputs_A`.
  - **E2-15** SHA 7aae202f: **B2 coupon-stage DROP PROBABILITY DELIVERED**. `WrongNotActiveB` class,
    `activeAWrongPairs`, `sum_interactionCount_activeAWrong = activeACount·wrongNotBCount`,
    `wrongNotBCount_eq_wrongACount_of_no_activeB` (post-cancel bridge), `wrongACount_drop_prob`:
    on all-phase-10 with activeBCount=0 & activeACount≥1, `kernel c (dropTarget wrongACount c) ≥
    wrongACount c/(n(n-1))`. Both stages' drop probabilities now axiom-clean.
  - **FURTHER SCOPING REFINEMENT (E2-15 discovery).** `wrongACount` is ALSO not cleanly non-increasing
    even under {AllPhase10 ∧ activeBCount=0}: `Phase10Transition` Block 2 lets an active-**T** spread T
    onto a passive whose output is A → that agent becomes output-T (≠A), so `wrongACount` INCREASES.
    The honest three-stage invariant chain (matches Doty's order):
      1. **cancel** Φ=activeBCount, Inv₁={AllPhase10}, drop via `activeBCount_drop_prob` (DONE). Monotone
         subtlety: activeBCount not non-increasing (B-spread) — use conserved signed sum
         (activeACount−activeBCount=g>0, `phase10Transition_preserves_signedContribution` public) so
         activeBCount≤activeACount and the cancel reaction is the only signed-sum-preserving move that
         changes the pair; alternatively bound the cancel hitting time by the E1 one-step engine on the
         {activeBCount>0} event directly (drop prob ≥ activeBCount/(n²) ≥ 1/(n²)).
      2. **absorb-T** Φ=activeTCount, Inv₂={AllPhase10 ∧ activeBCount=0}, useful pairs active-A×active-T
         (active-A absorbs active-T → both A; `Phase10Transition_activeA_nonActiveB_outputs_A` covers it).
         The drop-probability lemma transfers verbatim (swap WrongNotActiveB→IsActiveT). Under Inv₂,
         activeTCount IS non-increasing (no A→T move when no active-B; active-T only gets absorbed).
      3. **convert-passive** Φ=wrongACount, Inv₃={AllPhase10 ∧ activeBCount=0 ∧ activeTCount=0}, useful
         pairs active-A×{output≠A} (`wrongACount_drop_prob`, DONE, holds under Inv₃ a fortiori). Under
         Inv₃ (only active-A and passives left) wrongACount IS non-increasing (active-A only spreads A).
    **REMAINING for full E2 capstone** (all engine + all drop-prob lemmas done):
      (a) prove `InvClosed K Invᵢ` for i=2,3 (Inv₂ closure: no B reappears from no-B — block-2 spreads
          only present active outputs {A,T}; Inv₃ closure: additionally no active-T reappears once gone,
          since A-spread makes A and T-absorb makes A). Re-derivable in-file from public per-pair output
          lemmas + the support template `ae_of_stepDistOrSelf_support_preserved`.
      (b) prove `PotNonincrOn Invᵢ K Φᵢ` per-pair (the full output case-analysis on Phase10Transition,
          ~the private activeBCount/wrongACount _lt lemmas generalized to ≤ for all pair types under Invᵢ).
      (c) instantiate `coupon_expectedHitting_le_uniform_on` per stage with qₘ=1−m/(n(n-1)) (from the
          drop-prob lemmas: `K b (potBelow Φ m)ᶜ = 1 − K b (dropTarget) ≤ 1 − m/(n(n-1))` when Φ b=m),
          chain via `expectedHitting_le_through_mid`, majority/tie split on `backupSignal` sign.
    The probability/coupon/drop machinery carries NO further obligation; remaining is (a)+(b) per-pair
    monotonicity case-analysis (Analysis-style, re-derivable in-file) + (c) mechanical assembly.
  - **E2-16..23 SHAs 54f5ccb6 / cb0e1dca / cb10e1ad / c533e026 / d362e165 / 42dfafdc / 0fcc7ad2 / fa6a1fee
    / (chaining commit below).  THREE-STAGE ASSEMBLY DELIVERED (majority case), 0-sorry axiom-clean
    [propext,Classical.choice,Quot.sound] on every theorem (verified via #print axioms).**
    KEY CORRECTION TO THE DOCTRINE: `activeBCount` IS non-increasing on all-phase-10 (no extra invariant
    needed). The doctrine's repeated "Block-2 B-spread creates a new active-B" concern (lines ~180-189,
    214-217) is FALSE per the actual `Phase10Transition` def: Block 2 (active→passive spread) sets the
    converted partner's `output` but leaves `full := false`, so it never creates a new active source.
    Brute-force `Transition_activeBCount_le` (full output × full case analysis) compiles directly. The
    conserved-signed-sum workaround for the cancel stage is therefore UNNECESSARY for monotonicity.
    Delivered in `Probability/Phase10ExpectedTime.lean` (single-file EXIT_0, append-only; no Analysis edit):
      * Per-pair monotonicity `Transition_{activeBCount,activeTCount,wrongACount}_le` (brute force;
        activeTCount needs no-active-B in pair, wrongACount needs no-active-B & no-active-T).
      * Kernel-lift template `countP_scheduledStep_le` + `potNonincrOn_of_countP_step`; from these,
        `PotNonincrOn` for all 3 stages (`potNonincrOn_{activeBCount,activeTCount,wrongACount}`).
      * `InvClosed` for `AllPhase10`/`Inv2`/`Inv3` AND for the richer majority invariants `S1/S2/S3`
        (which additionally carry `card = n` and `0 < phase10ActiveSignedSum`, conserved per-step via
        `phase10ActiveSignedSum_stepRel_eq` + `stepDistOrSelf_support_card_eq`).
      * q-wiring: `qLevel n m = 1 − m/(n(n−1))`, `drop_compl_le` (complement via `measure_compl` +
        Markov `measure_univ`), `qLevel_uniform_ceiling` ((1−qLevel)⁻¹ ≤ n(n−1) for 1≤m≤M≤n(n−1)).
      * NEW drop-prob `activeTCount_drop_prob` (active-A × active-T rectangle; mirrors
        `wrongACount_drop_prob` verbatim — the doctrine's "swap WrongNotActiveB→IsActiveT" prediction).
      * THREE STAGE BOUNDS (full `coupon_expectedHitting_le_uniform_on` instantiations on the REAL kernel):
        `stage1_expectedHitting_le` (cancel, activeBCount), `stage2_expectedHitting_le` (absorb-T,
        activeTCount), `stage3_expectedHitting_le` (convert-passive, wrongACount). Each gives
        `E[hit {Φ=0}] ≤ M·n(n−1)` (crude; harmonic refinement to n(n−1)Hₙ orthogonal).
      * CAPSTONE `phase10_expected_stabilization_S3`: from an `S3` start (final coupon regime, all 3
        potentials simultaneously monotone), `E[hit {wrongACount=0}] ≤ M·n(n−1)` (all outputs = majority A).
      * Set-nesting `done3_subset_done1/done2` (`wrongACount=0 ⟹ activeBCount=activeTCount=0`).
      * `phase10_expected_stabilization_chain` (S1 start): machine-checked decomposition
        `E[hit Done₃] ≤ M·n(n−1) + ∑ₜ (K^t) c (Done₁ ∩ Done₃ᶜ)` via `expectedHitting_le_through_mid`
        + `stage1_expectedHitting_le`. The stage-1 term is fully bounded.
  - **PRECISE REMAINING OBLIGATION for the unconditional S1→stabilization bound** (the ONE open piece):
    bound the cross-term `∑ₜ (K^t) c (Done₁ ∩ Done₃ᶜ)` = occupation of `{activeBCount=0, wrongACount>0}`
    from an `S1` start. This is NOT closable by the existing `_on` engine (it needs `S2`/`S3` AT THE
    START `c`, but `c` is only `S1`) nor by the unconditional engine (activeTCount/wrongACount are not
    globally monotone). It needs a **strong-Markov restart / sequential-composition lemma**:
    `∑ₜ (K^t) c (Mid ∩ Doneᶜ) ≤ sup_{y∈Mid} expectedHitting K y Done` (× expected visits — but here
    `Done₁ = {activeBCount=0}` is ABSORBING under `S1` since `activeBCount` is non-increasing, so the
    run enters `S2` at its first `Done₁`-visit and stays; hence the occupation of `{activeBCount=0,…}`
    equals a single stage-2-then-stage-3 hitting time from the entry config, with NO re-entry). Concretely:
    add `expectedHitting_restart_le : Done absorbing ⇒ ∑ₜ (K^t) c (Done ∩ Eᶜ) ≤ sup_{y∈Done∩closure}
    expectedHitting K y E` to `ExpectedHitting.lean`, then chain stage2 (E := Done₂, on S2) + stage3
    (E := Done₃, on S3) off the `Done₁`-entry config. This is ~3-5 generic lemmas, no new protocol content.
  - **TIE CASE** (`backupSignal = 0`, i.e. `phase10ActiveSignedSum = 0`): NOT yet delivered. Same engine,
    but `1 ≤ activeACount` fails (signed sum 0 ⟹ activeACount = activeBCount, possibly both 0). The cancel
    stage still drives activeBCount→0 (drop prob ≥ activeBCount/n² still holds while activeBCount>0, paired
    with the EQUAL number of active-A), then all-T spreads (Φ = wrongTCount under the all-T invariant). The
    majority-case deliverables (above) are the requested "majority-case capstone + document" fallback.
- **E3** Conditional progress: from any config with |C| ≥ 2 (post-Phase-0), each timed phase ends
  within expected O(n/|C| · log n)-shape time (counter always ticks); gives both the bad-event
  O(log n) (|C| ≥ 0.24n) and the tiny-clock poly(n) bound from ONE parameterized lemma.
- **E4** The time-0 three-event split + summation: good whp event (Phase D headline) + Lemma 5.2
  clock-count concentration (Phase C, phases 0/1 line) + E2 + E3 → `doty_expected_time_O_log_n`.
Dependencies: E1, E2 are independent of Phases B–D (parallelizable NOW); E4 needs D's headline +
C's clock-count concentration.

## Phase F — audit, headline, release  [~6–10 bricks]

1. Repo-wide independent audit: axioms per theorem (not just the newest), no undischarged
   `_of_X`-style reduction hypotheses smuggling assumptions, no vacuous `True := trivial` markers
   standing in for content.
2. The single clean headline `theorem doty_thm31_time` with hypotheses `N₀ ≤ n` + protocol
   assumptions only.
3. Release per the standing 铁律: canonical → xiangyazi24/Ripple main 推平, verified tag,
   REPO_COPIES.md reconciliation. Blog 027 time-claim un-retraction (it was retracted 2026-06-06;
   the claim becomes true again — write the correction honestly, referencing the retraction).
4. DNA32 poster material refresh (deadline 2026-05-25 has passed — check what the poster actually
   needed; the showcase value remains for the Ho-Lin Chen project foundation).

## Order & rationale

B → C(parallel) → D → E → F. B first because every later phase consumes the clock and the
parameter choices; C parallelizes once B's parameters are fixed; D is pure composition; E has the
one scoping unknown (start its paper-read during C's parallel waits); F is hygiene + shipping.

## What we are explicitly NOT doing (scope fence)

- Space optimality (the paper's state-count side beyond state_count_poly_bound) — out of scope.
- The Θ(n log n)-interactions-vs-parallel-time conversion subtleties beyond what the existing
  parallel-time wrappers already handle.
- SSEM (Kanaya et al.) — separate, already complete.

## OVERNIGHT COORDINATION (2026-06-10 night; multiple windows live)

Line assignments to avoid file races (each line owns its files exclusively):
- **family (this line): Phase B** — DotyParams + scale-hypothesis discharge (incl. the hB ladder
  ceiling facts) in a NEW file `Probability/DotyParams.lean`, then the FrontSync consumer rethread
  (FrontSyncConc/ClockFrontWidth/ClockEnvMaint/ClockFullJoint edits) — these existing files are
  family-line-owned tonight.
- **family2 / family3 (when they come up): Phase C phase instances** — ONE NEW FILE PER PHASE
  (Phase4Convergence.lean, Phase5Convergence.lean, …), template = Phase2Convergence.lean. Suggested
  split: family2 takes phases 0/1 (+ the clock-count Θ(n) role-split concentration), family3 takes
  4/5/6 (read paper §7.1 FIRST for 5/6 Reserve-agent structure). Phases 7/8/10 next. Do NOT touch
  EarlyDripMarked.lean, ClockFrontProfile.lean, or any family-line file.
- Commit per lemma, push, sync-ripple-wip.sh, 0-sorry/axiom-clean discipline as per the doctrine.
- ChatGPT consults run from the family line (the family tab holds the repo connector); other lines
  request consults by writing questions into /tmp/gpt_requests_<line>.md and pinging family chat.

## Phase B step 3 — ARCHITECTURE SETTLED (2026-06-10 night, family line)

Findings (verified in code, not speculation):
1. **post_absorbing is dead weight in composition.** `compose_two_phases`/`compose_n_phases`
   never USE the field — only re-package it. → `PhaseConvergenceW` (no absorption) +
   `composeW_two/n_phases` + `PhaseConvergence.toW` landed in
   `Probability/PhaseConvergenceWeak.lean` (B-3b, identical proofs).
2. **Endpoint bridge landed** (`Probability/ClockFrontSyncFromWidth.lean`, B-3a): general
   level-i emptiness `rBeyond_eq_zero_of_goodWidth_of_bulk_below` + measure-union bridges
   `frontSync_whp_of_goodFrontWidth` / `capFeederEmpty_whp_of_goodFrontWidth` (abstract side
   event P matching goodFrontWidth_whp's carried conjunct).
3. **The remaining crux is clock_real_step's INTERNAL habs_mix** (ClockRealBulk ~353/423,
   ClockRealMixed ~1118: the drift windows must be absorbing ALONG the leg). Route:
   **killed kernel.** `GatedDrift.real_le_killed` (GatedGeometricDrift.lean:139) is the
   UNCONDITIONAL coupling `(K^t) x {bad} ≤ (killK^t) (some x) {none ∨ some bad}`; with
   measure_union_le this gives the master decomposition
     real {¬Post at leg end} ≤ killed {some ¬Post} + killed {none}
   — (a) `killed {some ¬Post}`: re-run clock_real_step's seed/bulk MGF on `killK κ Q_mix-gate`
   where the window is absorbing BY CONSTRUCTION (killK_drift pattern);
   (b) `killed {none}` = escape mass = Q_mix breach along the leg, bounded by per-step squared
   cap-seed on width-good configs + per-leg width re-certification (goodFrontWidth_whp_concrete
   at minute boundaries via the B-3a bridge). NO new coupling machinery needed.
4. Outstanding for step 3: classify every habs_mix use inside clock_real_step's callees
   (drift-absorbing vs endpoint-transport — ChatGPT letter 2 in flight, task output
   /tmp/gpt_a_phaseB2.out), then `clock_real_step_gated` + minuteStepPhaseW instances +
   composeW. Escape-budget arithmetic at DotyParams' concrete parameters.

## Phase B step 3 — horizon/start audit results (ChatGPT letter 4, family3, 2026-06-10 ~4am)

1. **Checkpoint prefixes are free**: windowedFrontProfile_whp at τ = j·w is the SAME theorem with
   KK := j (hsmall at w·j follows from hsmall at w·KK since j ≤ KK and the base > 1 — check
   direction when wiring). Remainders τ = j·w + r need ONE generic lemma
   `checkpoint_composition_prefix` (invariant_union_bound's split + a terminal r-block; hrem input
   `∀ x, Inv x → (Kk^r) x {¬Inv} ≤ δr`). No new probability.
2. **ClimbBound side is already horizon-free** (climb_real_tail/climbBound_whp take free t; the
   DotyParams wrapper kept t free).
3. **Start conditions (the real crux)**: recInv does NOT follow from Q_mix + AllClockP3 + card.
   All-clean lift ⟹ MarkInv (markInv_of_clean) + taintedCount = 0, but recInv only via
   window-closed (recInv_of_window_closed: ¬AllClockP3 ∨ rBeyond > n/10). At a mid-run minute
   boundary with AllClockP3 ∧ open window, a FRESH all-clean lift fails recInv (cleanAbove = full
   tail ⟹ recurrence inequality false in the window). ⟹ **Design: ONE marked chain per clock run**,
   started at the phase-3 entry (where ¬AllClockP3 ⟹ recInv all T via h0_params), maintained whp
   by the §6 engine itself (window_failure_le per window); the per-minute escape accounting reads
   real-kernel prefix events off this single chain via markedK_pow_erase (horizon/event free) +
   checkpoint prefixes. Do NOT re-lift per minute.
4. Targets sketched by the letter: wfpPrefixBound/climbPrefixBound defs + goodFrontWidth_whp_prefix
   (∀ τ ≤ M family). New-lemma list: checkpoint_composition_prefix (+ a δRem r-horizon window bound,
   supplied as input).

## Phase B step 3 — WIDTH-PREFIX MACHINERY DELIVERED (B-8, 2026-06-10)

New file `Probability/WidthPrefix.lean` (namespace `ExactMajority.EarlyDripMarked`, raw parameters
`θn n cc w …`; touches only this new file). All 4 deliverables 0-sorry, axiom-clean
([propext, Classical.choice, Quot.sound] per theorem), single-file EXIT_0.

- **B-8a** `checkpoint_composition_prefix` (SHA db58674e): generic `(Kk^(w*j+r)) x₀ {¬Inv} ≤ j·δ + δr`
  from per-window `δ` (`hwindow`) + per-remainder `δr` (`hrem`), both from invariant starts. Proof =
  `checkpoint_composition` (j-window prefix) + ONE Chapman–Kolmogorov remainder block
  (`pow_add_apply_eq_lintegral` at `m=w*j, n=r`, Inv/¬Inv split mirroring `invariant_union_bound`).
- **B-8b** `windowedFrontProfile_whp_checkpoint` + `hsmall_mono` (SHA 128ef118): the `KK := j` wrapper
  of `windowedFrontProfile_whp` at `j ≤ KK`, horizon `w·j`. `hsmall` at `w·j` DERIVED from the one at
  `w·KK` via `pow_le_pow_right₀` (base `1+4/n ≥ 1`, exponent `w·j ≤ w·KK`) — direction confirmed.
- **B-8c** `windowedFrontProfile_whp_prefix` (SHA 1646e199): the remainder version at `τ = w·j + r`.
  Built a full prefix chain mirroring the engine: `front_squares_whp_prefix` →
  `real_front_squares_whp_prefix` (via `markedK_pow_erase`) → `real_front_union_prefix` →
  `windowedFrontProfile_whp_prefix`. The `{¬recInv}` mass uses `checkpoint_composition_prefix`
  (`hwindow` = `window_failure_le`/`hB` at power `w`; `hRem` = the `r`-horizon `{¬recInv}` bound,
  **delivered as the INPUT-HYPOTHESIS version** `δRem` exactly per the audit — the engine fixes `w`,
  so the `r`-horizon `hB`-shape is an input). Taint tail (`tainted_marked_tail_explicit`) and MarkInv
  null (`markInv_ae_pow`) are horizon-parametric, instantiated at `w·j + r`; only `hsmall` at
  `w·j + r` needed. RHS per-level term: `(j·δ T + δRem T) + escape_τ + tail_τ`.
- **B-8d** `goodFrontWidth_whp_at` (SHA 65cb9c26): per-`τ` width glue. `goodFrontWidth_whp` is already
  free-`t`; this wrapper feeds the climb side from `climbBound_whp` (free-t, `c₀ := eraseConfig mc₀`)
  directly and takes the `WindowedFrontProfile` mass `wfpB` as input (supplied by B-8b at `τ = w·j` or
  B-8c at `τ = w·j + r`). Result: per-`τ` `GoodFrontWidth (frontWidthBound n + W₂)`-whp family,
  RHS `wfpB + (gated climb-tail sum at τ)`.

FOLLOW-UP (other line, DotyParams.lean): the CONCRETE-parameter prefix family — instantiate B-8b/c/d
at DotyParams' θn/w/KK/Tcap/σ and discharge `δRem T` (the `r`-horizon window bound) + the `∀ τ ≤ M`
union budget. This file leaves all parameters raw; the δRem discharge is the only genuinely-new
probabilistic obligation (an `r`-horizon analog of the `w`-window `window_failure_le`/`hB` ladder).

## Phase B step 3 — the COMPLETE prefix ladder (letter 4 full version; acceptance spec for the
WidthPrefix brick)

Five wrapper lemmas, no new probability (1-2 generic, 3-5 are copies of existing proofs with the
prefix lemma substituted):
1. `checkpoint_composition_prefix` — j full windows via checkpoint_composition + one terminal
   r-block (split intermediate state on Inv; charge δRem on Inv, complement absorbed in prior mass).
2. `recurrence_checkpoint_prefix` — specialize to Inv := recInv, Kk := markedK; window_failure_le
   for both block types (full-w and remainder-r; the r-horizon hB input may be carried as δRem).
3. `front_squares_whp_prefix` — copy front_squares_whp; recurrence_checkpoint →
   recurrence_checkpoint_prefix; markInv_ae_pow at τ; tainted_marked_tail_explicit at t := τ.
4. `real_front_union_prefix` — copy real_front_union; markedK_pow_erase at τ; union over T < Tcap.
5. `windowedFrontProfile_whp_prefix` — copy windowedFrontProfile_whp; deterministic subset
   (windowedFrontProfile_of_not_bad) unchanged; real_front_union → real_front_union_prefix.
Then `goodFrontWidth_whp_prefix` (∀ τ ≤ M family): wfpPrefixBound (j := τ/w, r := τ%w; per-T sum of
j·δWin T + δRem T r + killK-none at τ + tainted MGF at τ) + climbPrefixBound (already free-t side).
Pure-wrapper facts: climbBound side free in t; markedK_pow_erase free; neg conjunct droppable via
neg_params. The only open engineering point: supplying hBrem (r-horizon per-window engine at the
scale hypotheses, or a coarse uniform δRem for partial windows).

## Phase B step 3 — letter 2 full version addenda (2026-06-10)

- DONE already: kill_escape_le_prefix_union (B-7, single side-set S form — instantiate S :=
  W ∧ B ∧ P and split the prefix sums by set-inclusion at the caller), PhaseConvergenceW (B-3b),
  endpoint bridges (B-3a), prefix machinery (WidthPrefix brick in flight).
- OPTIONAL polish (not on critical path): exact survivor projection
  `killK_pow_someSet_eq_liveK_pow` via sub-Markov `liveK := piecewise G K (const 0)` — the Option
  analogue of markedK_pow_erase; our killed_alive_le_real is the inequality version and suffices.
- The killed minute phase skeleton (names locked): Qgate/κQ abbrevs, killedMinutePre/Post (none ∈
  Post — escape paid separately, drift never bounds it), clock_killed_stepW :
  PhaseConvergenceW (κQ n mC T) via composeW_two_phases of killed seed/bulk legs (alive branch =
  rSeedPot_contracts_seed / rSeedPot_contracts_bulk; off-gate successor = none ∈ Post),
  clock_real_step_gated (real_le_killed + split none ∪ alive-bad + hesc), clock_real_step_gatedW
  (PhaseConvergenceW on the REAL kernel, ε = εseed+εbulk+εesc as ℝ≥0) — feeds composeW_n_phases
  exactly where faithfulMinutePhases sat. ε_leg := M·qQ + ∑_{τ<M}(εW+εP+εB)(τ); qQ = 0 if the
  phase/counter side gates are deterministic on the good event, else folded into εP.
- HIGH-RISK unknown still open (letter 3, family2, in flight): whether
  WindowConcentration.windowDrift_PhaseConvergence and the seed/bulk drift lemmas are
  kernel-parametric (instantiable at κQ) or hard-code the real kernel (→ minimal generalization
  needed).

## Phase B step 4 — ASSEMBLY DESIGN (self-derived 2026-06-10 morning; family2 letter lost to the
bridge truncation bug — this section is the design of record)

The central mismatch: clock_real_step_gatedW's hesc_all is ∀-start, but escape budgets are
start-dependent and the width family is global-start. Resolution — two observations:

1. **The killed-phase part (εseed+εbulk) IS start-uniform** (clock_killed_stepW holds from any
   alive Pre-config) — no mismatch there. Only the ESCAPE part is start-dependent.
2. **Escape telescopes globally.** Per-leg escape from leg-start configs, INTEGRATED over the
   time-t_i distribution (which is all the composition ever uses — compose_two_phases only
   consumes convergence inside ∫⁻ y in {Post_i}, ... ∂((K^t_i) c₀)), re-expands via
   Chapman-Kolmogorov into GLOBAL-time per-step terms:
     ∫ P(escape during leg i | start y) d((K^{t_i}) c₀)(y)
       ≤ ∑_{τ ∈ [t_i, t_i+M_i)} (K^τ) c₀ {¬S} + M_i·q
   (same proof pattern as kill_escape_le_prefix_union, with the prefix now from the GLOBAL start).
   Summing legs: total escape ≤ H·q + ∑_{τ<H} (K^τ) c₀ {¬S} — ONE global prefix sum, fed by
   goodFrontWidth_whp_at (WidthPrefix) + the endpoint bridges + neg_params.

Implementation pieces (one new file, ClockWeakAssembly.lean-style):
A. **Averaged composition** `composeW_legs_avg`: like composeW_n_phases but each leg's convergence
   hypothesis is the AVERAGED form
     ∫⁻ y in {Pre_i}, (K^{M_i}) y {¬Post_i} ∂((K^{t_i}) c₀) ≤ ε_i
   (the existing compose proof already only uses this — re-cut the proof to expose it), OR
   equivalently keep composeW_n_phases and define leg phases with ε_i := εseed+εbulk+εesc_i where
   εesc_i is the leg's global-window escape budget; then the only new lemma is:
B. **Global-start leg escape** `leg_escape_global`: for x₀ with the run measure, leg window
   [t, t+M): ∫⁻ y, [(killK_now κ G_T)^M (some y) {none}] ∂((K^t) x₀) ≤ M·q + ∑_{τ∈[t,t+M)} (K^τ) x₀ {¬S}
   — proof: integrate kill_now_escape_le_prefix_union's per-start statement and collapse
   ∫ (K^σ) y Sᶜ d((K^t) x₀)(y) = (K^{t+σ}) x₀ Sᶜ (Chapman-Kolmogorov), plus ∫ M·q ≤ M·q.
C. The minute-T gate varies per leg (G_T = Q_mix n mC T) — handled naturally since each leg does
   its OWN real_le_killed_now transfer inside the averaged convergence; no time-varying killed
   kernel needed.
D. Cross-minute chain: Q_mix_succ_of_post unchanged (deterministic).
E. Side gates (HabsDischarge phase/counter): fold into S (the side event of the escape accounting)
   or discharge deterministically where the existing theorems already do; audit at implementation.
Endpoint: clock_real_faithful_all_minutes_W with budget L₀·(εseed+εbulk) + H·q + ∑_{τ<H} global
side-failure prefixes; then the O(log n) wrapper. Retire the habs_mix_all consumers per the
letter-1 dead-code list.

---

## Phase B-9 — KILLED-MINUTE BRICK DELIVERED (2026-06-10, 0-sorry axiom-clean)

Three new files (commits 2026418c, a45eb3c6, bd72da46; pushed main + opus-wip):

1. `Probability/GatedKillNow.lean` — the IMMEDIATE-kill kernel `killK_now K G`: from `some x`
   (`x∈G`) push `K x` through `gateMap G = fun y => if y∈G then some y else none` (off-gate
   successors die in the SAME step). Delivered: IsMarkovKernel, `killK_now_none`/`_ungated`/
   `_some_gated`, `none_absorbing_now`, **`alive_support_gate`** (the FIX: any positive-mass
   alive successor lies in G — stated as `0 < killK_now o {some c'} → c'∈G`, since
   `Measure.support` is not in Mathlib), **`real_le_killed_now`**, **`killed_now_alive_le_real`**,
   **`kill_now_escape_le_prefix_union`** (simpler than the lagged version: escape registers
   immediately, no carried ungated-alive mass).

2. `Probability/KernelWindowDrift.lean` — Kernel-parametric WEAK window-drift builder:
   `kernel_lintegral_decay`, `kernel_measure_ge_thresh`, `kernel_windowDrift_tail`,
   **`kernelWindowDrift_PhaseConvergenceW`**. PORT of WindowConcentration's bodies, Protocol→Kernel,
   strong→weak.
   DEVIATION: uses the UNCONDITIONAL one-step drift `∀x, ∫Φ∂(Kx) ≤ r·Φx` instead of the
   blueprint's `hQ_abs`+a.e.-invariance form — because `Measure.support` is not first-class in
   Mathlib, and the killed kernel's drift IS unconditional (0 off-gate / at cemetery). Strictly
   cleaner; reuses no a.e. machinery.

3. `Probability/ClockKilledMinute.lean` — the minute skeleton, all holes filled:
   `Qset`/`QbulkSet`/`κQ_now`/`κQ_now_bulk`, `SeedPre/Post`, `BulkPre/Post`, `optLift`,
   `seedΦ`/`bulkΦ`/`minuteRate`, `killed_int_le_real`(+`_bulk`), `real_int_zero_of_finished`,
   **`killed_seed_drift`**, **`killed_bulk_drift`** (unconditional; alive branch reduces killed
   integral to the gate-filtered real integral ≤ real unguarded `rSeedPot_contracts_seed/bulk`;
   finished branch = 0 via `hmono_mix_discharged`), **`killedSeedPhase`**, **`killedBulkPhase`**
   (via `kernelWindowDrift_PhaseConvergenceW`, θ=1, link = `not_finished_imp_rSeedPot_ge_one`),
   **`clock_killed_seed_stepW`**, **`clock_killed_bulk_stepW`**, **`clock_real_seed_step_gated`**
   (real transfer via `real_le_killed_now` + `{none}∪{some bad}` split).

### Post-shape choice: NUMERICAL-ONLY killed Post.
`SeedPost c := seedLo mC ≤ rBeyond(T+1) c`, `BulkPost c := bulkHi mC ≤ rBeyond(T+1) c` — NO
`Q_mix` conjunct. Reason: full `Q_mix` one-step closure (`habs_mix`) is UNPROVEN (rests on
`HabsDischarge.ClockPhase3_remaining_synchronization`, the front-shape synchronization, a
multi-step reachability fact). The killed kernel FILTERS successors through the gate
(`alive_support_gate`), so alive successors lie in `Q_mix` by construction — we never need the
real dynamics to preserve `Q_mix`. The unguarded `rSeedPot` links to the numerical threshold
only. The `Q_mix` endpoint conjunct is recovered by consumers from the side gates.

### DEVIATION: two kernels, not one composed minute.
SEED gates on `Q_mix` (`κQ_now`); BULK gates on the STRONGER `QbulkWin` (`κQ_now_bulk`) because
`rSeedPot_contracts_bulk` consumes the `mC/10` infected floor `hlo`, which an alive `Q_mix`-only
successor need NOT satisfy. A single-kernel `composeW_two_phases` would need ONE gate that tracks
the `mC/10` floor for ALL alive successors — exactly the unproven front-shape floor invariant.
So the blueprint's `clock_killed_stepW` (one composed minute) is delivered as TWO separate
per-leg tails (`clock_killed_seed_stepW`/`clock_killed_bulk_stepW`) plus the seed-leg real
transfer; consumers chain the legs at the real-kernel level. This is the precise residual obstruction.

---

## Phase B-10 — WEAK ASSEMBLY DELIVERED (2026-06-10, 0-sorry axiom-clean)

New file `Probability/ClockWeakAssembly.lean` (namespace `ExactMajority.ClockWeakAssembly`;
imports `ClockKilledMinute` + `ClockRealHours`). All theorems
`#print axioms ⊆ [propext, Classical.choice, Quot.sound]`, single-file EXIT_0. SHAs on main:

- **B-10a** (922e2aeb) `leg_escape_global` + `kill_now_escape_prefix_all`: the telescoped
  global gate-escape. `∫ (killK_now K G ^ M)(some y){none} ∂((K^t)x₀) ≤ M·q + ∑_{τ∈Ico t (t+M)}
  (K^τ)x₀ Sᶜ`. Per-start `kill_now_escape_le_prefix_union` EXTENDED to ALL starts (ungated
  y∉G: σ=0 prefix term =1 dominates, M≥1; M=0 escape=0), then integrate + Chapman–Kolmogorov
  collapse `∫ (K^σ)y Sᶜ ∂((K^t)x₀) = (K^{t+σ})x₀ Sᶜ`. SIDE-SET **S = G** (Gᶜ=Sᶜ, hSG:=rfl).
- **B-10b** (60a9a716 seed, 2fe83829 bulk) `clock_real_{seed,bulk}_leg_avg` +
  `killed_{seed,bulk}_avg_le` + `killed_{seed,bulk}_ungated_post_zero`: the averaged real leg.
  Routes real mass through `real_le_killed_now`, splits killed target `{none ∨ some-bad} =
  {none} ∪ {¬optLift Post}`, escape→`leg_escape_global`, post-integral→`εleg` (on the gate via
  killed convergence; on the complement the ungated killed walk dies into `none ∉ {¬optLift
  Post}`, mass 0, requires 0<M).
- **B-10c** (a1fba6ae) `clock_real_minute_avg`: the assembled real minute. CK-glue at the seed
  offset + `clock_real_bulk_leg_avg` at leg-start `Tstart+tseed`. **Minute = the bulk leg
  started after the seed phase.**
- **B-10d** (6ea4cac0) `minuteFailW` (`Fin L₀` family) + `clock_real_faithful_all_minutes_W`:
  union-bounded endpoint over all minutes. Budget `∑_i (εbulk + tbulk·q + per-minute prefix)`.
- **B-10e** (a7952051) `clock_real_faithful_O_log_n_W`: the O(log n) wrapper at L₀=K·(L+1).

### THE SIDE-SET S (settled — answers the assembly-design open question)
**S = G = QbulkSet n mC T = {QbulkWin} = {Q_mix n mC T ∧ mC/10 ≤ rBeyond (T+1)}** (per minute,
gate at level T). The boundary `Q_mix` re-establishment AND the `mC/10` floor re-establishment
both charge to `(realκ^τ) c₀ QbulkSetᶜ` at τ=Tstart+tseed (inside the per-minute prefix sum).

### DEVIATIONS from the ASSEMBLY DESIGN (all strictly cleaner / honest, nothing dropped)
1. **No separate εseed budget term; no seed escape budget.** The averaged/global telescoping
   makes the seed leg's `εseed` UNNECESSARY as an additive term — the seed leg manifests as the
   WINDOW OFFSET (the bulk leg's prefix runs over τ ≥ Tstart+tseed, post-seed times only). All
   seed-related failure (floor not yet crossed) is in the SAME `QbulkSetᶜ` prefix. (Design item
   A's `composeW_legs_avg` re-cut is therefore NOT needed: a single CK-glue + the bulk
   averaged leg gives the minute directly.)
2. **No deterministic cross-minute `composeW_n_phases` chain.** `Q_mix_succ_of_post` needs the
   FULL `Q_mix n mC T` at the boundary, which the NUMERICAL-only `BulkPost` does NOT carry
   (same residual as B-9's two-kernel split / the unproven front-shape synchronization). Each
   minute is a STANDALONE averaged-global bound; "all minutes" is the UNION bound
   (`clock_real_faithful_all_minutes_W`), not a composed chain.
3. **Per-minute side-set varies** (design item C): `S_T = QbulkSet n mC T` tracks the level T;
   no single fixed-S global prefix. Endpoint budget is the honest double sum.

### `clock_real_faithful_O_log_n_W` HYPOTHESIS LIST (final)
`(n mC : ℕ) (hn : 2 ≤ n) (hmC : 2 ≤ mC) (hLK : 0 < K*(L+1)) (tseed tbulk : ℕ) (htbulk : 0 <
tbulk) (εbulk : ℝ≥0) (hεb : minuteRate^tbulk · ofReal(exp(log2·bulkHi mC)) / 1 ≤ εbulk) (q :
ℝ≥0∞) (hstep : ∀ T, ∀ x∈QbulkSet n mC T, realκ x QbulkSetᶜ ≤ q) (c₀ : Cfg L K)`. Conclusion:
union-bound failure ≤ ∑_i (εbulk + tbulk·q + per-minute QbulkSet(i)ᶜ prefix). `habs_mix` is
GONE. The OLD `ClockRealFaithfulHours` assembly is NOT deleted (later cleanup).

### RESIDUAL (NOT discharged here — for the DotyParams / WidthPrefix follow-up line)
- `hstep` (per-step gate-escape rate q) — the §6 drip-only excess-counter one-step bound.
- The per-minute side prefixes `∑_{τ∈window_i} (realκ^τ) c₀ QbulkSet(i)ᶜ` — discharged by
  `WidthPrefix.goodFrontWidth_whp_at` + endpoint bridges + DotyParams (seed drip ⟹ mC/10 floor
  whp by Tstart+tseed ⟹ post-seed prefix whp-small). This file leaves all parameters raw.

## Phase C-1 — RoleSplitConcentration witness (Lemma 5.2 progress field) — STATUS

`RoleSplitConcentration.lean` `roleSplitTail_le` (Phase0Initial + RoleSplitMilestone ⟹
tail ≤ 1/n²) was already delivered (C-1c). The one named remaining input is the
`RoleSplitMilestone` witness over the REAL kernel. C-1d/C-1e findings:

**REAL-KERNEL STAGE-1 MILESTONE PHASE ALREADY EXISTS** in `Analysis/Phase0Convergence.lean`:
`phase0MilestonePhase n hn : MilestonePhase (NonuniformMajority L K)`, 0-sorry, with the
`progress` field discharged against the ACTUAL protocol transitions via
`interactionPMF_toMeasure_mcr_phase0_ge → stepDistOrSelf_toMeasure_ge` (the
`countP_eq_sum_count`/class-aggregation mass route). Milestones = `mcrCount`-threshold
decrements of Stage 1 (`RoleMCR,RoleMCR → Main,RoleCR`, paper Lemma 5.1).
`p i = M(M−1)/(n(n−1))`, M from n down to 2.

**TASKS 1 (per-step rates) and 2 (milestone family) are therefore ALREADY DONE** by the
predecessor — over the real kernel, axiom-clean. C-1d added the bridges into the
RoleSplitConcentration interface:
- `roleMCRCount_eq_mcrCount` (countP = filter.card).
- `mcrCount_le_one_of_phase0Post` : `phase0MilestonePhase.Post c` (+ carried card=n,
  all-MCR-phase-0 invariants) ⟹ `mcrCount c ≤ 1` (the last threshold).
- `phase0_milestone_jansonTail` : `phase0MilestonePhase` pushed straight through
  `milestone_hitting_time_bound` (real-kernel Stage-1 Janson tail).

**TASK 3 (balance) — the transitions ARE deterministic 1:1**: Rule 1 (two MCR → one Main
+ one CR) and Rule 4 (two CR → one Clock + one Reserve) are deterministic 1:1 in
`Phase0Transition` (Transition.lean L356–404). So the count-balance is EXACT counting, NOT
Azuma/MGF — once Stage 2 is wired, `|Clock| = |Reserve| = #Rule4-firings` deterministically
(parity ≤ initial), `|Main| = #Rule1-firings`. No in-house drift engine needed for balance.

**BLOCKER (precise) — the witness `potential` field is UNSATISFIABLE for the single-chain
Stage-1 phase.** `roleSplitTail_le_inv_sq` consumes `hpot : log n ≤ pMin · meanTime`. For
`phase0MilestonePhase`:
  * `pMin ≤ 2/(n(n−1)) = Θ(1/n²)` — FORMALIZED as `phase0MilestonePhase_pMin_le_two_div`
    (C-1e, the easy `iInf_le` at the near-empty `M=2` milestone), 0-sorry axiom-clean.
  * `meanTime = Σ 1/p_i = (n−1)²` (telescoping; not yet formalized — gap below).
  * ⟹ `pMin · meanTime = 2(n−1)/n → 2 < log n` for all n ≥ 8. POTENTIAL FAILS.

This is the prompt's own thesis confirmed formally: the naive per-decrement single-chain
Janson with the worst-case `pMin` gives a `Θ(1)` potential, not `Θ(log n)`. The paper's
`Θ(log n)` comes from the COUPON/parallel-time analysis (sum of heterogeneous geometric
waiting times whose COLLECTIVE potential is `Θ(log n)`), already half-built abstractly in
`Phase10ExpectedTime.lean` (`coupon_expectedHitting_le*`). The RoleSplitMilestone witness
must be assembled NOT from a uniform-pMin Janson bound but from the coupon decomposition.

**REMAINING GAPS into the witness (ordered):**
1. Stage-2 milestone family over the real kernel: `RoleCR,RoleCR → Clock,Reserve` (Rule 4)
   at rate `Θ(l²/n²)` — the analogue of `phase0_mcrCount_decrease_prob` for `crCount`
   (reuse `stepDistOrSelf_toMeasure_ge` + an `interactionPMF_toMeasure_cr_*_ge` clone).
2. Either (a) replace the uniform-pMin Janson tail with the coupon decomposition so the
   `Θ(log n)` potential is reachable, OR (b) supply a milestone phase whose `pMin·meanTime`
   genuinely ≥ log n (requires non-uniform p — the coupon route).
3. `post_sound : Post ⊆ RoleSplitGood` — Stage-1 Post gives `mcrCount ≤ 1` (need = 0: parity
   cleanup via the phase-end `RoleCR → Reserve` rule); Stage-2 Post gives the Clock/Reserve
   Θ(n) floors and the Main n/2±εn window via the deterministic 1:1 counts (pure omega).

## Phase C-1 (relay 2) — RESOLUTION of the critical math question

**The pinned obstruction was a MODELING gap in the predecessor's milestone phase, NOT a
property of the protocol. Answer (a) is correct: the protocol HAS one-sided MCR conversion.**

### The paper quote (Lemma 5.1, the Phase-0 top-level split reactions, paper line 2311)

> "Lemma 5.1. Consider the reactions
>   U, U → S_f, M_f
>   S_f, U → S_t, M_f
>   M_f, U → M_t, S_f
> starting with n U agents. … This converges to u = 0 in expected time at most 2.5 ln n and
> in 12.5 ln n time with high probability 1 − O(1/n²)."

with the proof's rate computation:

> "The probability of decreasing u is at least 2(u/n)(1/5), so the number of interactions it
> takes to decrement u is stochastically dominated by a geometric random variable with
> probability p = 2u/(5n). Then the number of interactions for u to decrease from 2n/3 down
> to 0 is dominated by a sum T of geometric random variables with mean
> E[T] = Σ_{u=1}^{2n/3} 5n/(2u) ∼ (5/2) n ln n."

And Lemma 5.2 (paper line 2391) states exactly the role-split postcondition we target:

> "Lemma 5.2. For any ε > 0, with high probability 1 − O(1/n²), by the end of Phase 0,
> |RoleMCR| = 0, (n/2)(1−ε) ≤ |M| ≤ (n/2)(1+ε) and |C|,|R| ≥ (n/4)(1−ε)."

### What this means for the Lean obstruction

The decrement rate is **`p = 2u/(5n) = Θ(u/n)`, NOT `Θ(u²/n²)`**. The `Θ(u/n)` comes from
the SECOND and THIRD reactions of Lemma 5.1 — `S_f,U → S_t,M_f` and `M_f,U → M_t,S_f` — i.e.
an MCR meeting an *already-assigned* RoleCR or Main agent and being one-sidedly converted.
These are precisely **Rules 2 and 3 of `Phase0Transition`** (Protocol/Transition.lean
L364–386, paper pseudocode Lines 4–9), which the Lean protocol ALREADY formalizes:
  * Rule 2 (L364–374, paper Lines 4–6): MCR meets unassigned Main → MCR becomes RoleCR.
  * Rule 3 (L375–386, paper Lines 7–9): MCR meets unassigned RoleCR (non-Main) → MCR becomes Main.
Each decreases `mcrCount` by 1, and the number of such (MCR, assignable-target) ordered pairs
is `u · (#unassigned assignable targets)`. By Lemma 5.1's Chernoff step, `s_f + m_f > n/5`
holds for all future interactions once `u < 2n/3` (the count `s_f + m_f` is non-decreasing),
so the assignable-target count is `Θ(n)` and the per-step decrease probability is `Θ(u/n)`.

**The predecessor's `phase0_mcrCount_decrease_prob` (Phase0Convergence.lean L1672) bounds the
decrease probability using ONLY the MCR–MCR good set** (Rule 1, `Σ count·(M−1) = M(M−1)`),
hence `p ≥ M(M−1)/(n(n−1)) = Θ(M²/n²)` and `pMin = Θ(1/n²)`. That bound is CORRECT but WEAK:
it omits the Rule-2/Rule-3 one-sided good pairs. The honest fix is a STRONGER decrease bound
adding the (MCR × assignable-target) good set, giving `p ≥ Θ(M·n/5 / n²) = Θ(M/n)`, hence a
milestone phase with `pMin = Θ(1/n)`, `meanTime = Σ 5n/(2M) = Θ(n ln n)`, and
`pMin · meanTime = Θ(ln n)` — the potential is SATISFIED.

**FAITHFUL FORM (final):** `RoleSplitGood` and `roleSplitTail` are kept exactly as the
predecessor stated them (paper-faithful to Lemma 5.2: `|RoleMCR| = 0`, the M window, the
C,R floors). The witness's `RoleSplitMilestone.mp.p` must be the `Θ(M/n)` family, not the
predecessor's `Θ(M²/n²)` `phase0MilestonePhase`. The in-file `RoleSplitGood` already encodes
`roleMCRCount = 0` as the target, so NO definition change is needed — only the milestone
family's rate. All C-1c/d/e lemmas are untouched (prompt's "keep predecessors' lemmas intact").

### Honest scope assessment for this relay

Proving the `Θ(M/n)` decrease bound over the real kernel requires the **`s_f + m_f > n/5`
concentration invariant** (Lemma 5.1's Chernoff step) as a hypothesis on the configs the
milestone phase visits — that count is NOT determined by `mcrCount` alone, so a milestone
phase keyed only on `mcrCount` cannot carry it. The faithful witness therefore needs the
invariant threaded as a carried predicate (an `assignableCount c ≥ n/5` side condition,
discharged by a separate epidemic-style monotonicity lemma — the analogue of `informedU`
already used in Phase 2/4). This relay delivers the **count-level building blocks** (the
one-sided assignable-target good set, the `assignableCount` definition, and the
`Θ(M·assignable/n²)` mass bound over the real kernel) and wires what is mechanically
reachable; the full carried-invariant milestone is the precise documented next gap.

---

## Phase C-4: Phase4Convergence (tie detection / non-tie continuation) — COMPLETE

File: `Probability/Phase4Convergence.lean` (NEW, 0-sorry, axioms ⊆ [propext, Classical.choice, Quot.sound], no native_decide). Single-file `lake env lean` EXIT_0.

The actual Phase-4 rule (`Protocol/Transition.lean:1042`): a phase-4 agent with a
**big bias** (`bias = .dyadic _ i` with `i.val < L`, i.e. `|bias| > 2^{-L}`) is a witness;
meeting any partner advances BOTH to phase 5 (`advancePhase`). With no big bias the
transition is the identity.

### Honest predicate choices (vs HANDOFF sketch placeholders)
The sketch named `TieAllMinExp`/`Phase3StructuredNonTiePost`/`StableTieOutput`/`Phase5Pre`,
none of which exist. Replaced with honest in-file predicates read off the real rule:
- `noBigBias a` — bias `.zero` or `.dyadic _ i` with `¬ i.val < L` (mirrors the `private`
  `StableEndpoints.phase4NoBigBias`).
- `StableTie4 c` — `∀ a ∈ c, phase=4 ∧ output=T ∧ noBigBias a` (mirrors the `private`
  `StableEndpoints.phase4TieWith`) — the tie `Post`.
- `advancedP a := 5 ≤ a.phase.val`, `advancedU c := countP advancedP`, `advFinished n c := n ≤ advancedU c` — non-tie `Post`.
- `Q4 n c := card=n ∧ ∀ a, 4 ≤ a.phase.val` — non-tie window; `Qwin4 := Q4 ∧ 1 ≤ advancedU` (window + epidemic seed).

### Mechanism
- **Tie branch**: genuinely deterministic. With no big bias the guard never fires;
  `Transition_preserves_tie_pair` ⟹ `StableTie4_stepOrSelf`/`_absorbing` ⟹
  `StableTie4_pow_tail` (`(K^t) c {¬StableTie4} = 0` by induction). ε = 0.
- **Non-tie branch**: the phase-`max` epidemic baked into `phaseEpidemicUpdate`. "informed"
  = `phase ≥ 5`; a mixed (advanced, phase-4) pair sends BOTH outputs to `phase ≥ 5`
  (`Transition_*_phase_ge_pair_max`, public, from `Invariants.lean`). This is the SAME engine
  as `Phase2Convergence`'s opinion epidemic, ported with `advancedU` as the monotone count:
  `advancedP_pair_mono/_advances`, `advancedU_ge_monotone`, the DERIVED rectangle prob
  `advanced_advance_prob` (`≥ m(n−m)/(n(n−1))`), the exponential deficit drift
  `phase4AdvancedDrift`, and the keystone `windowDrift_PhaseConvergence` →
  `phase4NonTieConvergence : PhaseConvergence`.

### Deliverables (theorems)
- `phase4NonTieConvergence (n) (hn:2≤n) (s) (hs:0<s) (t) (ε) (hε) : PhaseConvergence (NonuniformMajority L K).transitionKernel` — Pre = `Qwin4 n`, Post = `Qwin4 n ∧ advFinished n`.
- `phase4Convergence (n) (hn:2≤n) (s) (hs:0<s) (t) (ε) (hε) : PhaseConvergenceW (NonuniformMajority L K).transitionKernel` — the **unified instance**: Pre = `StableTie4 ∨ Qwin4 n`, Post = `StableTie4 ∨ advFinished n`. Tie branch contributes failure 0; ε is the non-tie geometric tail `r^t·exp(s(n−1))` with `r = 1 − ((n−1)/(n(n−1)))(1−e^{−s})`.

### Honest carried assumption (the one documented gap, by design)
The non-tie Pre carries the epidemic **source seed** `1 ≤ advancedU c` (`∃ a, phase ≥ 5`),
exactly as `Phase3Convergence`'s Pre carries `∃ a, 4 ≤ a.phase`. The **witness-bootstrap**
(one witness pair firing to CREATE the first phase-5 agent in O(n) steps, before the spread)
is NOT in this file — it is the upstream/composition's job to supply the source, matching the
repo's established Phase-3 design. This is a deliberate scope boundary, not a sorry: the
witness-firing lemma (per-step `≥ #witness·(n−1)/(n(n−1))` from the `hasBigBias‖` guard) is
the precise next atom if a self-seeding non-tie instance is wanted.

Commits: C-4a bc51ff8d (tie determinism) · C-4b 98654cb3 (epidemic kinematics) ·
C-4c ad50d020 (rectangle prob) · C-4d 33b1a660 (sync prob) · C-4e 2bad00f8 (window+potential) ·
C-4f 2e3acf05 (drift) · C-4g c84645cf (non-tie PhaseConvergence) · C-4h 8edab1f6 (unified).
