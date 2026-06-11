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
  - **E2-25/26 SHAs 165ee8c5 / 3137ff97.  CROSS-TERM CLOSED — BOTH REMAINDERS DONE.**
    * **E2-25 (`ExpectedHitting.lean`, append-only generic):** `occupation_mid_le` and the
      invariant-relative `occupation_mid_le_on` (the strong-Markov restart, in fully generic kernel
      form).  Shape: `(∀ y, J y → y ∈ Mid → expectedHitting K y Done ≤ B) → J c → ∑ₜ (K^t) c (Mid ∩
      Doneᶜ) ≤ B`, with `J` one-step-closed (`∀ b, J b → K b {¬J} = 0`).  **ABSORPTION-FREE** —
      `expectedHitting` from a `Mid`-state already counts ALL future not-Done time, so re-entry cannot
      double-count.  Proof = truncated-induction mirror of `occLevelUpTo_le_on` (split on `c ∈ Mid`:
      truncated band-sum ≤ Doneᶜ-tail = `expectedHitting ≤ B`; vs `c ∉ Mid`: i=0 vanishes, one CK step,
      IH on J-successors a.e.).  The doctrine's predicted `occupation_le_of_absorbing_mid` — but no
      absorbing hypothesis needed.
    * **E2-26 (`Phase10ExpectedTime.lean`):** `phase10_expected_stabilization` (majority, **unconditional
      `S1` start**, NO residual hypothesis): `E[hit {wrongACount=0}] ≤ 3·(n(n−1))²`.  Both chaining
      cross-terms (`Done₁∩Done₃ᶜ` and inner `Done₂∩Done₃ᶜ`) closed by `occupation_mid_le_on` (J=S1 / S2).
      Helpers: `stage23_expectedHitting_le` (S2-start chain), `countP_le_n` / `wrongACount_le_nn` /
      `activeTCount_le_nn` (uniform caps `≤ card = n ≤ n(n−1)`).
  - **E2-27/28 SHAs bf866e8d / 95192589.  TIE CASE COMPLETE (`backupSignal = 0`).**
    The doctrine's prediction confirmed: `activeBCount_drop_prob` applies VERBATIM under tie
    (`activeACount = activeBCount = m ≥ 1` when `activeBCount = m`), so the cancel stage transfers
    unchanged.  After cancel, signed-sum-0 forces `activeACount = activeBCount = 0`, so every remaining
    active agent is active-`T` (`active_of_no_activeA_no_activeB_is_activeT`).
    * **E2-27:** tie cancel stage — `Tie1`/`Tie2` invariants, `invClosed_Tie1/2`, `hdrop_Tie1` (with
      `m=0` vacuous branch), `tie_stage1_expectedHitting_le`; `activeACount_eq_activeBCount_of_tie`.
    * **E2-28:** NEW T-spread drop family + combined tie headline.  `WrongNotBiased` responder class
      (output ≠ T ∧ not active-A/B); `Transition_wrongTCount_le` (per-pair, no-A/no-B brute force);
      `wrongTCount_post_convert_lt`; `activeTWrongPairs` aggregation (`sum_interactionCount/Prob_*`);
      `wrongTCount_drop_prob` (active-T × wrong-not-biased, mass ≥ wrongTCount/(n(n−1)), mirrors
      `wrongACount_drop_prob`).  `potNonincrOn_wrongTCount` on `Tie2`.  **Liveness invariants**
      `Tie2plus`/`Tie1plus` = `Tieᵢ ∧ hasActiveAgent` (closure via
      `phase10_hasActiveAgent_preserved_by_step`); under them `hasActiveAgent + no-A/B ⟹ 1 ≤
      activeTCount`, supplying the drop-prob's driver hypothesis.  `tie_stage2_expectedHitting_le`,
      then `phase10_expected_stabilization_tie` (**unconditional `Tie1plus` start**): `E[hit
      {wrongTCount=0}] ≤ 2·(n(n−1))²`, cross-term via `occupation_mid_le_on` (J=Tie1plus),
      `doneT_subset_done1` nesting.  Side-effect: `countP_scheduledStep_le` /
      `potNonincrOn_of_countP_step` un-`private`d (generic, reused for the tie potential).
    All four headlines `#print axioms ⊆ [propext, Classical.choice, Quot.sound]`, 0-sorry, 0
    native_decide.  **PHASE E2 CORRECTNESS-SIDE FULLY CLOSED** (majority + tie, both unconditional from
    an all-phase-10 start; the crude `O(n⁴)` bound, sharp `O(n² log n)` is the orthogonal harmonic
    refinement of the same Icc coupon sum).
- **E3** Conditional progress: from any config with |C| ≥ 2 (post-Phase-0), each timed phase ends
  within expected O(n/|C| · log n)-shape time (counter always ticks); gives both the bad-event
  O(log n) (|C| ≥ 0.24n) and the tiny-clock poly(n) bound from ONE parameterized lemma.
  **GENERIC + PARAMETERIZED LAYER DONE 2026-06-10** (SHAs 900ef1ba / 8caccd9f / 54c5f030 / f4e67793
  / 85677466; 0-sorry, axiom-clean = [propext,Classical.choice,Quot.sound] on every theorem, verified
  `#print axioms`; single-file EXIT_0). NEW file `Probability/ConditionalPhaseProgress.lean`.
  **Potential choice = SUM of clock counters** (`Φ`), as the doctrine recommended: each clock-clock
  decrement lowers the sum by ≥1 while positive, non-clock interactions leave it, so `PotNonincr`-
  friendly and `Φ c ≤ counterMax·mC`. The drop rate is **uniform across levels**
  `clockPairRate mC n = mC(mC−1)/(n(n−1))` (any positive-counter clock pair fires), so the engine is
  the *uniform-rate* special case of the coupon collector — `q m = 1−clockPairRate` for all `m`,
  per-level waiting time `(1−q)⁻¹ = (clockPairRate)⁻¹ = n(n−1)/(mC(mC−1))`. Delivered:
  - **Lifted generic engine** (`Engine` namespace; the `Phase10ExpectedTime` Coupon chain is verbatim
    generic over `ExpectedHitting`+Mathlib, lifted because `Phase10ExpectedTime.olean` is absent /
    mid-edit and cannot be imported): `potBelow`, `PotNonincr`, `level_occ_*`, `occLevel*`,
    `coupon_expectedHitting_le`, `coupon_sum_le_of_uniform`, `coupon_expectedHitting_le_uniform`.
  - **Rate arithmetic:** `clockPairRate` (def), `clockPairRate_le_one`,
    `one_sub_one_sub_clockPairRate_inv` (`(1−(1−p))⁻¹ = p⁻¹`), `clockPairRate_inv_eq`
    (`p⁻¹ = n(n−1)/(mC(mC−1))` closed form, `2≤mC`), `clockPairRate_inv_le_div`,
    `headline_product_eq` (**key mC-cancellation:** `(counterMax·mC)·p⁻¹ = counterMax·n(n−1)/(mC−1)`).
  - **HEADLINE** `timed_phase_expected_progress`: hyps `PotNonincr K Φ`, uniform per-level drop
    `K b (potBelow Φ m)ᶜ ≤ 1−clockPairRate mC n`, `Φ c ≤ counterMax·mC` ⇒
    `E[hit {Φ=0}] ≤ (counterMax·mC)·(clockPairRate mC n)⁻¹`.
  - **Two corollaries from the ONE headline:** (a) `timed_phase_progress_bigClock` (`n/5≤mC`, `n≥18`)
    ⇒ `E ≤ counterMax·(11·n)` — **linear** (const rate; 11 clears the Nat-floor slack uniformly);
    (b) `timed_phase_progress_tinyClock` (`mC≥2`) ⇒ `E ≤ counterMax·n²` — **poly fallback** (via the
    cancellation `counterMax·n(n−1)/(mC−1) ≤ counterMax·n(n−1) ≤ counterMax·n²`).
  - **E4-shape wrappers** `phase_advance_expectedHitting_{tinyClock,bigClock}`: transport onto an
    arbitrary phase-advance set `Done = {x | Φ x = 0}` (the `potBelow Φ 1 = {Φ=0}` trigger), so E4
    consumes `E[hit Done] ≤ …` directly.
  - **E3-1 (relay, SHA 823b87cf):** the unconditional `PotNonincr K Φ` for the clock-counter SUM is
    **FALSE** on the real kernel (the phase-advance event runs `advancePhaseWithInit` whose `phaseInit`
    RESETS `counter` to `counterMax = 50(L+1)`; `phaseEpidemicUpdate` likewise re-inits a clock dragged
    UP). The honest engine is INVARIANT-RELATIVE. Lifted the `_on` chain verbatim from `Phase10ExpectedTime`
    (olean absent) into `Engine`: `InvClosed`, `PotNonincrOn`, `level_occ_*_on`, `occLevel_le_on`,
    `coupon_expectedHitting_le_uniform_on`; + invariant-relative headline `timed_phase_expected_progress_on`
    + corollaries `timed_phase_progress_{tinyClock,bigClock}_on`. 0-sorry, axiom-clean (verified `#print
    axioms`). The fix: phase-RESTRICTED potential `Φ_p` (counts only phase-`p` clocks) — a clock leaving
    phase `p` (counter hit 0 → advance, or epidemic-dragged up) LEAVES the sum, so `Φ_p` only descends.
  - **E3-2 (relay, SHA ee3f5c71):** real-kernel protocol layer (imported `ClockRealKernel`; none of the
    forbidden files touched). DEFINITIONS `clockCounterSumAt p` (= phase-`p`-restricted clock-counter sum,
    `Multiset.map (if clock ∧ phase=p then counter else 0) |>.sum`) and `AllClockGEp p` (= all agents
    clocks at phase ≥ p, the clock-subpopulation view where `mC=card`). **`AllClockGEp_absorbing` (the
    `InvClosed` discharge on `(NonuniformMajority L K).transitionKernel`) is FULLY PROVEN, 0-sorry,
    axiom-clean** — via `Transition_clock_pair_phase_GEp` (3≤p; role permanence from public
    `ClockRealKernel.Transition_clock_pair` + phase-nondec from public `phaseEpidemicUpdate_*_phase_ge_max_api`
    ∘ `phaseEpidemicUpdate_phase_le_Transition_phase`), mirroring `ClockRealKernel.AllClockGE3_absorbing`.
  - **REMAINING (the two per-pair DETERMINISTIC discharges; all probability/coupon content closed):**
    (i) `hmono : PotNonincrOn (AllClockGEp p) K (clockCounterSumAt p)` — per-pair counter-sum descent
    through the FULL `Transition` (epidemic + 11-phase dispatch + `finishPhase10Entry`), via
    `Multiset.sum_map` additivity reducing to `Φ_p{δ₁,δ₂} ≤ Φ_p{r₁,r₂}`; the per-phase ingredient is
    `PhaseProgress.{Phase5,6,7,8}Transition_clock_counter_descent` (clock-clock, needs BOTH counters; a
    clock dragged to a higher phase leaves `Φ_p` ⟹ drop). Template: `ClockMonoDischarge.lean` (same
    countP-monotone-through-`Transition` shape, for `minute`). (ii) `hdrop : K b (potBelow Φ_p m)ᶜ ≤
    1 − clockPairRate mC n` — clock-clock rectangle mass; **HONEST RATE FINDING:** the descent
    (`stdCounterSubroutine_counter_strict_descent`) needs BOTH clock counters POSITIVE, so the firing
    rectangle is over POSITIVE-counter phase-`p` clocks; at level `m≥1` with all `mC` clocks positive
    this is `mC(mC−1)/(n(n−1))` = `clockPairRate mC n` exactly. Route: `stepDistOrSelf_toMeasure_ge`
    (`Phase0Convergence`, public) ∘ rectangle `interactionProb` sum (clock-clock analogue of E2's
    `sum_interactionProb_presentActiveAB`; single-pair template `ClockRealKernel.clock_real_drip_advance_prob`
    proves `interactionProb w w = m(m−1)/(n(n−1))`). (iii) `counterMax = 50(L+1)` (the `AgentState.counter`
    `Fin` cap). Both residues re-derivable in-file from the now-imported `ClockRealKernel` + `PhaseProgress`.
- **E4** The time-0 three-event split + summation: good whp event (Phase D headline) + Lemma 5.2
  clock-count concentration (Phase C, phases 0/1 line) + E2 + E3 → `doty_expected_time_O_log_n`.
Dependencies: E1, E2 are independent of Phases B–D (parallelizable NOW); E4 needs D's headline +
C's clock-count concentration.

## Phase F — audit, headline, release  [~6–10 bricks]

**F-prep INDEPENDENT AUDIT DONE 2026-06-10** → see `AUDIT_2026-06-10.md` (sibling file).
Verdict: all 25 scope files axiom-clean + sorry-free (16 headline `#print axioms` =
[propext, Classical.choice, Quot.sound]; source-grep clean on the 9 not-yet-rebuilt files). No
vacuous capstone, no smuggled `True := trivial` (the 2 in-scope markers are honest status anchors),
no overstatement in 12 spot-checked DONE-claims, cross-file `sideEps`/`heB`/`htB` feeders consistent,
FALSE `hwin_all` genuinely retired (no scope file carries it). Consolidated open Phase-D/F surface =
8 items (see AUDIT §6): the eight non-width `εside` feeders, the post-hour width mode, the per-phase
drain rates `q`/`hstep` for phases 0/5/7/8, and the Lemma-5.2 clock floor `hfloor`. ONE shape to
watch in Phase-D wiring: `ConditionalPhaseProgress.timed_phase_progress_real_*`'s `hfloor` (hwin_all
shape — honest as a whp/E4 input, defect only if treated as deterministic-for-all-reachable). Recommend
a confirming `#print axioms` pass on the 9 not-yet-rebuilt files after the next remote `lake build`.

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

## Phase B-11 — UNCONDITIONAL CLOCK WIRED, q = 0 (2026-06-10, 0-sorry axiom-clean)

New file `Probability/ClockUnconditional.lean` (namespace `ExactMajority.ClockUnconditional`;
imports ClockWeakAssembly + FrontSyncConc + ClockFrontSyncFromWidth). All theorems
`#print axioms ⊆ [propext, Classical.choice, Quot.sound]`, single-file `lake env lean` EXIT_0,
zero sorry / zero native_decide. SHAs on main: B-11a a3c8db2c · B-11b e3ba9d7e · B-11c e1099e13.
(NOTE: regenerated the stale `ClockFrontSyncFromWidth.olean` with `-o` before the single-file
compiles; its only import `ClockFrontProfile` was already current.)

### THE HONEST SPLIT (deterministic / whp-charged / named inputs) — settled

`QbulkSet n mC T = {Q_mix n mC T ∧ mC/10 ≤ rBeyond (T+1)}`, `Q_mix = card ∧ clockPhase3 ∧
clockSize ∧ crossedT`. One-step escape `realκ x QbulkSetᶜ` decomposes:
- **DETERMINISTIC (contribute 0):** `card`, `clockSize`, `crossedT` (needs `1 ≤ T`),
  `allPhaseGE3` — closed on the support by `HabsDischarge.habs_mix_deterministic_skeleton`; the
  `mC/10` floor is MONOTONE by `ClockMonoDischarge.hmono_mix_discharged`.
- **whp-charged (folded into the side event):** `clockPhase3` closes one step ONLY on the
  FrontSync-good window (`FrontSyncConc.habs_mix_full`, under `allPhaseGE3 ∧ noPhaseAbove3 ∧
  allClocksCounterPos ∧ FrontSync` + the successor `noPhaseAbove3 c'`). Bare deterministic
  closure is FALSE (the at-cap `counter = 1` witness). FrontSync is supplied probabilistically.

**RESOLUTION: q = 0.** Conditioning the one-step escape on a structural side event
`HabsGood c := allPhaseGE3 ∧ noPhaseAbove3 ∧ allClocksCounterPos ∧ FrontSync ∧ (∀ c' on
support, noPhaseAbove3 c')` makes EVERY successor of `QbulkSet ∩ {HabsGood}` land in `QbulkSet`,
so the gate-escape is exactly 0 (`hstep_of_sideGood`, axiom-clean). Per the blueprint directive
("keep the undischargeable gate INSIDE the side event, q = 0, ALL cost moves to the side
prefixes"), the side set is `Sgood T = QbulkSet T ∩ {HabsGood}` and the per-minute side prefix is
`∑_τ (realκ^τ) c₀ Sgood(T)ᶜ`. `HabsGood` is minute-INDEPENDENT (a single structural event).

### DELIVERABLES (theorems, signatures abbreviated)
1. `hstep_of_sideGood (1 ≤ T) : x ∈ QbulkSet ∩ {HabsGood} → realκ x QbulkSetᶜ = 0` (via
   `qbulk_succ_of_sideGood` = habs_mix_full + hmono_mix_discharged). **q = 0.**
2. The S-conditioned assembly variant (campaign-mandated "variant IN YOUR FILE, do NOT edit
   ClockWeakAssembly"): `clock_real_bulk_leg_avg_sideGood` / `clock_real_minute_avg_sideGood` /
   `minuteFailW_sideGood` / `clock_real_faithful_all_minutes_sideGood` — mirror the B-10 chain
   with `S = Sgood`, `q = 0` (escape term `M·0 = 0`), via `ClockWeakAssembly.leg_escape_global`
   at `S = Sgood`, `hSG = compl_subset_compl Set.inter_subset_left`, `hstep = hstep_of_sideGood`.
3. **CAPSTONE** `clock_real_faithful_O_log_n_unconditional`: over bulk minutes `T = 1 …
   K·(L+1)−1` (`Fin (K·(L+1)−1)` at `i.val+1`; the `1 ≤ T` boundary — minute 0 is the
   phase-3-entry start, the cap minute is the FrontSync arrival). Failure
   `≤ ∑_i (εbulk + tbulk·0 + ∑_τ Sgood(i+1)ᶜ prefix)`. **`q` and `hstep` are GONE from the
   hypothesis list.**
4. **Side-prefix discharge** `Sgood_compl_subset` + `sidePrefix_le`: `Sgood(T)ᶜ ⊆ QmixFail ∪
   FloorFail ∪ SyncFail ∪ {PhaseGateFail}`; per-`τ` mass `≤ εQ + εfloor + εsync + εphase`, each
   εᵢ a NAMED INPUT routed to its discharger.

### CAPSTONE FINAL HYPOTHESIS LIST
`(n mC : ℕ) (hn : 2 ≤ n) (hmC : 2 ≤ mC) (hLK : 0 < K·(L+1)) (tseed tbulk : ℕ) (htbulk : 0 <
tbulk) (εbulk : ℝ≥0) (hεb : minuteRate^tbulk·ofReal(exp(log2·bulkHi mC))/1 ≤ εbulk) (c₀ : Cfg L
K)`. NO `q`, NO `hstep`. The only un-bounded RHS terms are the per-minute `Sgood(i+1)ᶜ` prefixes.

### WHAT REMAINS (named inputs into `sidePrefix_le`, NOT discharged in B-11)
The four εᵢ feeders, per-`τ`, summed over the per-minute window:
- `εQ` (`{¬Q_mix T}`) + `εfloor` (`{¬ mC/10 floor}`): `WidthPrefix.goodFrontWidth_whp_at` + the
  `ClockFrontSyncFromWidth` bridges + `DotyParams` (seed drip ⟹ floor whp; width ⟹ window).
- `εsync` (`{¬FrontSync}`): `FrontSyncConc.frontSync_concentration_remaining_proven` /
  `ClockFrontSyncFromWidth.frontSync_whp_of_goodFrontWidth` (= εW + εP + εB).
- `εphase` (`{PhaseGateFail}`): `allPhaseGE3` deterministic (`allPhaseGE3_closed`),
  `noPhaseAbove3` the residual deterministic gate (named), `allClocksCounterPos` whp on the
  FrontSync event (`counterPos_closed_of_frontSync`). The successor-`noPhaseAbove3` gate folds
  in with the `noPhaseAbove3` deterministic residual.
These are the GENUINELY-OPEN inputs; the B-11 file proves the full inclusion + union bound and
names each feeder. Discharging them at DotyParams' concrete parameters (summing the per-`τ`
WidthPrefix/bridge bounds over each minute window) is the remaining DotyParams follow-up.

## Phase B-12 — EXPLICIT UNCONDITIONAL CLOCK BUDGET (2026-06-10, 0-sorry axiom-clean)

New file `Probability/ClockBudgets.lean` (namespace `ExactMajority.ClockBudgets`; imports
ClockUnconditional + DotyParams). All theorems `#print axioms ⊆ [propext, Classical.choice,
Quot.sound]`, single-file `lake env lean` EXIT_0, zero sorry / zero native_decide. SHAs on main:
B-12a b41ee387 · B-12b 72d18c95 · B-12c 53365bee · B-12d 67bc9202.

This is the CLOSING brick of Phase B: it discharges the four per-`τ` feeders of `sidePrefix_le`
through their dischargers and SUMS them over the minute windows into the single explicit budget
`ε_clock(n)`.

### THE EXPLICIT BUDGET (settled)
```
εclock L K tbulk εbulk εside := (K·(L+1) − 1) · (εbulk + tbulk · εside)
```
and `clock_unconditional_concrete`: the total minute-failure mass
`∑_{i:Fin(K(L+1)−1)} (realκ^(i·s+tseed+tbulk)) c₀ {¬BulkPost n mC (i+1)} ≤ εclock`, with
`s = tseed+tbulk`.  Shape: `O(#minutes) · (bulk tail + tbulk · per-step side mass)` =
`O(K·(L+1)) · …` = `O(log n)` parallel (the clock runs `K·(L+1) = O(log n)` minutes).

### DELIVERABLES (theorems, signatures abbreviated)
1. `phaseGateFail_le` — `εphase` decomposition: `{PhaseGateFail} ≤ εge3 + εno3 + εcpos + εsucc`
   (pure union bound over the four structural conjunct failures, FULLY PROVEN).
2. `syncFail_le` — `εsync` wiring: `{¬FrontSync} ≤ εW + εP + εB` via
   `ClockFrontSyncFromWidth.frontSync_whp_of_goodFrontWidth` (`SyncFail`/`realκ`-shape restatement).
3. `sidePrefix_le_assembled` — the per-`τ` `Sgood(T)ᶜ` budget `≤ sideEps` (the sum of all NINE
   named feeders `εQ εfloor εW εP εB εge3 εno3 εcpos εsucc`), composing `sidePrefix_le` (B-11) with
   (1) and (2).  Pure measure arithmetic.
4. `window_sum_le` / `minute_term_le` / `minutes_sum_le` — the summation collapse: with a UNIFORM
   per-`τ`/per-minute side bound `εside`, the inner `Finset.Ico` window sum is `≤ tbulk·εside`
   (`Nat.card_Ico`), each minute term `≤ εbulk + tbulk·εside`, and the `K(L+1)−1` minute sum
   collapses to `εclock` (constant summand × card).  FULLY PROVEN.
5. **`clock_unconditional_concrete`** — capstone `clock_real_faithful_O_log_n_unconditional` (B-11)
   composed with `minutes_sum_le`: total failure `≤ εclock`.  The only remaining input is the
   uniform `εside`.
6. `widthFail_concrete` — the §6 width-failure mass `εW` at the ENDPOINT horizon `w n · KK L K`,
   GENUINELY supplied by `DotyParams.goodFrontWidth_whp_final` (`WidthSideP n` = the §6 side
   conjunct, `W = frontWidthBound n + W₂`).  This is the concrete `εW` feeding `syncFail_le`.

### FINAL HYPOTHESIS LIST of `clock_unconditional_concrete` (every genuinely-open input)
`(n mC : ℕ) (hn : 2 ≤ n) (hmC : 2 ≤ mC) (hLK : 0 < K·(L+1)) (tseed tbulk : ℕ) (htbulk : 0 <
tbulk) (εbulk : ℝ≥0) (hεb : minuteRate^tbulk·…/1 ≤ εbulk) (c₀ : Cfg L K) (εside : ℝ≥0∞)
(hside : ∀ T τ, (realκ^τ) c₀ Sgood(T)ᶜ ≤ εside)`.  The single genuinely-open input is **`εside`**
(the uniform per-`τ` side budget).  `q`/`hstep` GONE (B-11); the per-minute side prefixes are now
SUMMED into `εclock`.

### THE GENUINE §6 BOUNDARY (precise gap for the remaining follow-up)
`εside` = `sideEps` (Part 3) made uniform across the run, i.e. uniform-in-`τ` bounds on the nine
named feeders.  The genuinely-open ones:
- **`εW(τ)` at FREE `τ`**: the §6 concrete chain (`windowedFrontProfile_whp_concrete` →
  `goodFrontWidth_whp_final`) is LOCKED to the SINGLE endpoint horizon `w n · KK L K` (the
  checkpoint machinery `windowedFrontProfile_whp_checkpoint` requires the `w·KK` per-hour window
  structure).  `widthFail_concrete` (Part 6) delivers `εW` AT THAT HORIZON concretely; a per-`τ`
  family at free `τ` (re-running the §6 engine windowed at each `τ`, or a sup-over-the-hour bound)
  is the remaining §6 follow-up.  NOT a math gap — an engine-rehoming task.
- **`εP(τ)` / `εB(τ)`** (the side-event / bulk-arrival masses of the FrontSync bridge): named
  whp inputs of `frontSync_whp_of_goodFrontWidth`, supplied by the same §6 line + the bulk-arrival
  bound.
- **`εge3 τ`/`εno3 τ`/`εcpos τ`/`εsucc τ`**: `allPhaseGE3`/`noPhaseAbove3` deterministic from the
  start (`allPhaseGE3_closed`; `noPhaseAbove3` the residual deterministic gate); `allClocksCounterPos`
  whp on the FrontSync event (`counterPos_closed_of_frontSync`) — charges to the same FrontSync
  mass.  The deterministic ones are `0` once the start facts propagate; the residual gates are
  named.
Everything ABOVE `εside` (the inclusions, the four-feeder split, the FrontSync bridge wiring, the
summation arithmetic, the concrete endpoint `εW`) is FULLY PROVEN and axiom-clean.  Phase B's
clock chain is now a single explicit budget gated only on the uniform per-`τ` side mass `εside`.

## Phase B-13 — the FREE-τ CONCRETE WIDTH FAMILY: εside's §6 width feeder no longer endpoint-locked (2026-06-10, 0-sorry axiom-clean)

File: `Probability/WidthPrefixConcrete.lean` (new).  B-13a 70f40461 · B-13b 335f5737 ·
B-13c 6bab9672 · B-13d 3db75694.  All 7 theorems axiom-clean (⊆ {propext, Classical.choice,
Quot.sound}), single-file compile, ZERO sorry / native_decide / new axiom.

This brick RE-HOMES B-12's `εW` from the SINGLE endpoint horizon `w·KK` to the free minute boundary
`τ = w·j + r` (`r < w`, `j ≤ KK−1`, so `τ ≤ w·KK`), discharging the §6 width feeder of `εside`
CONCRETELY at every hour-horizon prefix — the exact "engine-rehoming task, not a math gap" B-12
flagged.

### The `δRem` discharge — HONEST analysis of the horizon split (the one genuinely-new obligation)
`WidthPrefix.windowedFrontProfile_whp_prefix` (B-8) takes the `r`-horizon remainder window bound
`δRem` as an INPUT.  `window_failure_le` is ALREADY horizon-parametric (its region/floor/P3/X-exit
null modes hold at every horizon via `ae_notG_pow`), so the remainder bound is `window_failure_le`
at `r`, fed by a per-window bad-event bound at `r`.  That bad-event bound = `per_window_delta` at
`w := r`.  Its `w`-dependent hypotheses split by direction:
- `hsmall` (`σ·(1+y)^r ≤ thresh`): base `1+y ≥ 1`, so `(1+y)^r ≤ (1+y)^w` for `r < w` — LHS shrinks,
  holds a fortiori (`hsmall_prefix_concrete`, PROVEN).
- `hfloor` (`floor_margin_params`: `δgLocked ≤ r·(1.8(1−e^{−1/10})/n) − const`): RHS has a
  `+r·(positive)` term, so for `r < w` the RHS SHRINKS.  The full-window slack is tiny (≈ 4·10⁻⁶),
  so the floor margin GENUINELY FAILS for small `r` (outright at `r = 0`).  This is a REAL
  structural break, NOT a missing arithmetic step: the §6 ladder needs the full window `w` of drift.

**Honest fix** (the route the B-8 audit blessed — "a coarse uniform δRem for partial windows"):
the trivial probability bound `δRem := 1` (`rem_le_one`, B-13a): from ANY start,
`(markedK^r) mc₀ {¬recInv} ≤ 1` (a Markov-kernel power is a probability measure), valid at EVERY
`r` including the broken small-`r` regime.  Coarse but EXPLICIT — and `εside` is itself a named
uniform bound, not required `< 1`.  The remainder then contributes `Tcap·1` per the level union; the
checkpoint part keeps the same `KK·deltaB`-shape as the endpoint (since `j ≤ KK`).

### DELIVERABLES (theorems, signatures abbreviated)
1. `rem_le_one` (B-13a) — the coarse universal `δRem = 1` (+ `markedK_pow_isMarkov` instance).
2. `hsmall_prefix_concrete` — concrete scale smallness at any `τ ≤ w·KK` (a-fortiori from
   `DotyParams.hsmall_eq`).
3. `windowedFrontProfile_whp_prefix_concrete` (B-13b) — the `WindowedFrontProfile`-failure mass at
   `τ = w·j+r` at DotyParams' params: B-8 prefix machinery + `DotyParams.hB_params` (δ := deltaB n)
   + `rem_le_one` (δRem := 1).
4. **`goodFrontWidth_whp_at_concrete`** (B-13b) — the FREE-τ concrete width family: (3) for the WFP
   side + `DotyParams.climbBound_whp_concrete` (free-t) for the climb side, glued by
   `goodFrontWidth_whp_concrete`.  The free-τ analog of the endpoint-locked
   `DotyParams.goodFrontWidth_whp_final`.
5. `widthFail_at_concrete` + `εWAt` (B-13c) — the free-τ analog of B-12's `widthFail_concrete`:
   (4) re-associated into the EXACT `ClockBudgets.WidthSideP n c ∧ ¬GoodFrontWidth W c` /
   `syncFail_le` shape, RHS named `εWAt`.  `realκ = (NonuniformMajority).transitionKernel` by abbrev.
6. `sidePrefix_concrete_width` (B-13d) — the per-τ `Sgood(T)ᶜ` budget via
   `ClockBudgets.sidePrefix_le_assembled` with `εW` SUBSTITUTED by `εWAt` (concrete); the other
   EIGHT feeders (`εQ εfloor εP εB εge3 εno3 εcpos εsucc`) carried as named uniform whp bounds.
7. **`clock_unconditional_final`** (B-13d) — the explicit `εclock` capstone (=
   `ClockBudgets.clock_unconditional_concrete`) exposed with the explicit `εside` provenance:
   `hside` over the hour horizon is now supplied by `sidePrefix_concrete_width`, `εside :=
   sideEps εQ εfloor (εWAt …) εP εB εge3 εno3 εcpos εsucc`.

### FINAL HYPOTHESIS LIST of `clock_unconditional_final` (every surviving named input)
`(n mC : ℕ) (hn : 2 ≤ n) (hmC : 2 ≤ mC) (hLK : 0 < K·(L+1)) (tseed tbulk : ℕ) (htbulk : 0 < tbulk)
(εbulk : ℝ≥0) (hεb : minuteRate^tbulk·…/1 ≤ εbulk) (c₀ : Cfg L K) (εside : ℝ≥0∞)
(hside : ∀ T τ, (realκ^τ) c₀ Sgood(T)ᶜ ≤ εside)`.  εside is now EXPLICIT (the assembled `sideEps`
with `εWAt` concrete).  The surviving named residuals, all carried INSIDE `hside`:
- the EIGHT non-width §-engine feeders `εQ εfloor εP εB εge3 εno3 εcpos εsucc` (distinct
  Qmix/floor/side-event/bulk-arrival/four-phase-gate masses — each its own §-engine, untouched here);
- the τ-uniformity OVER AND PAST the hour horizon: `goodFrontWidth_whp_at_concrete` is concrete for
  `τ ≤ w·KK`; the POST-HOUR (`τ > w·KK`) absorbed/already-converged width mode is the one surviving
  follow-up (the genuine sup-over-the-hour boundary B-12 flagged — the engine is concrete for the
  whole hour, the post-hour tail is the absorbed mode).

### VERDICT
The §6 width feeder of `εside` is NO LONGER endpoint-locked: it is discharged CONCRETELY at every
minute boundary inside the hour (`τ ≤ w·KK`), explicit closed form `εWAt`.  B-12's flagged
"engine-rehoming" follow-up is DONE for the width feeder.  Phase B's clock chain reaches an explicit
`εclock` with an explicit `εside` whose §6 width component is now free-τ concrete.  What remains is
NOT a §6 width gap: it is (i) the eight independent non-width side-feeder engines, and (ii) the
post-hour absorbed width mode (`τ > w·KK`), both honestly named inside `hside`.

## PHASE D-1 — uniform FrontSync side-budget `sideB` DISCHARGED (2026-06-10, 3 commits, 0-sorry axiom-clean)
_(record copied here from `claude-code/memory/project_pp_exact_majority.md` where the D-1 agent misfiled it.)_

NEW file `Probability/SideBudget.lean` (361 lines). Discharges the single FrontSync side-prefix
feeder that BOTH consumers carry: the §6 hour-escape (`HourEscape.heB_of_sideB`, B-14) and the
clock chain's `εsync` slice (`ClockBudgets`/`WidthPrefixConcrete.clock_unconditional_final`).
- f9933a6f D-1a: `frontSyncFail_concrete` — per-τ `(realκ^τ)(erase mc₀){¬FrontSync} ≤ εWAt + εP +
  εB` via `ClockFrontSyncFromWidth.frontSync_whp_of_goodFrontWidth`, WIDTH slice substituted by the
  concrete `εWAt` (`widthFail_at_concrete`, B-13). `frontSyncFail_at_free` — same at free τ < w·KK
  via canonical decomp j=τ/w, r=τ%w (`w_pos_of_N₀`: w n = 3n/200 > 0 at n ≥ N₀ = 10⁴⁰).
- da6362e7 D-1b: `sideB_concrete` — `∑_{τ<w·KK} (realκ^τ)(erase mc₀){HourSideBad} ≤ εsync` where
  `εsync = ∑_{τ<M} (εWAt(τ/w,τ%w) + εP τ + εB τ)` (HourSideBad = {¬FrontSync} def-eq). `heB_concrete`
  — `heB` FULLY NUMERIC: killK cemetery mass after one hour ≤ εsync, via `heB_of_sideB ∘ sideB_concrete`.
- 24398f38 D-1c: `Sgood_compl_le_uniform` — per-τ `Sgood(T)ᶜ ≤ sideEps` (width slice = concrete εWAt)
  via `sidePrefix_concrete_width` + gcongr to uniform width majorant. `clock_unconditional_wired` —
  εside fed into `clock_unconditional_final` (conclusion `εclock = (K(L+1)−1)(εbulk+tbulk·εside)`).
εB RESOLUTION (honest): εB = bulk-below failure {¬(10·rBeyond(capMinute−W) < card)} stays a NAMED
per-τ input. It is the bulk-ARRIVAL/hour-completion event — the §6 width engine bounds the FRONT,
not the bulk progress, so εB is the legitimate hour-boundary event, carried with precise shape (not
faked, not absorbed). εP = {¬WidthSideP n} also NAMED, exactly as ClockBudgets.sidePrefix_le_assembled
carries it (card+AllClockP3 preserved by gate; recurrence conjunct not absorbing).
SURVIVING GAPS for the chain: (1) εP/εB per-τ bounds (the named hour residuals — εB is genuinely
the bulk-arrival/hour-completion event; εP the side-event failure); (2) the τ-uniform majorant of
εWAt over the hour + the eight ClockBudgets feeders + the post-hour absorbed mode — all carried as
explicit hypotheses, not faked. Pushed origin main + xiangyazi24/Ripple opus-wip.

## PHASE D-2 — the per-hour composition: `phase3Convergence` DELIVERED (2026-06-10, 4 commits, 0-sorry axiom-clean)

NEW file `Probability/HourComposition.lean` (namespace `ExactMajority.HourComposition`; imports
`SideBudget` + `HourCouplingV2`). All theorems `#print axioms ⊆ [propext, Classical.choice,
Quot.sound]`, single-file `lake env lean` EXIT_0, zero sorry / zero native_decide / zero new axiom.
SHAs on main: D-2a 29bc1123 · D-2b a4378f4f · D-2c 4f7d4ff3 · D-2d 01f2183a.
(synced to xiangyazi24/Ripple opus-wip ba670b3.)

### Lemma 6.10 — what it couples (verified against `HourCouplingV2.hour_coupling_v2`).
`Φ h = mAbove h / M − 1.1·cAbove h / C` where `mAbove h = |{Main : hour > h}|`, `cAbove h =
|{Clock : clock-hour > h}|` (so it couples the MAIN-agent hour advance with the CLOCK-agent hour
advance). On the synchronous window `c_{>h} ≤ 1/11` it is a genuine supermartingale (drag/epidemic
pair-counting + the bracket `(1−m_{>h}) − 1.1(1−c_{>h}) ≤ 0`); Azuma gives the tail `(K^t) c₀ {Φ ≥
Φ c₀ + lam} ≤ exp(−lam²/(2t·c₀²))`, i.e. `m_{>h}(t) ≤ 1.2·c_{>h}` whp — the **Main agents do not
run ahead of the clock's hour**.

### THE DESIGN (settled — the union-bound reality, NOT a deterministic chain).
The phase-3 run = `K(L+1) = O(log n)` minutes; the §6 width engine + the Phase-B killed-minute
chain certify per minute `T` that the bulk crosses (`BulkPost T`) within `tseed+tbulk`
interactions, failure charged to the per-minute side prefix `∑_τ Sgood(T)ᶜ`. Summed over the
`K(L+1)−1` bulk minutes (`clock_unconditional_concrete`, the UNION bound — NOT a deterministic
composed chain, per the B-10/B-11 deviation: NUMERICAL-only `BulkPost` lacks the full `Q_mix` for a
`Q_mix_succ_of_post` chain), total failure `≤ εclock = (K(L+1)−1)·(εbulk + tbulk·εside)`.

### DELIVERABLES (theorems, signatures abbreviated).
1. **`final_minute_le_clock`** (D-2a) — the FINAL bulk minute (`Fin`-index `K(L+1)−2`, minute
   `T_last = K(L+1)−1`) hour-completion failure `(realκ^phase3Horizon) c₀ {¬HourComplete} ≤ εclock`,
   by single-term domination of the non-negative `clock_unconditional_concrete` sum. `HourComplete =
   BulkPost (K(L+1)−1)` (the bulk arrived at the clock's last hour — the hour-completion event).
   `phase3Horizon = (K(L+1)−2)·(tseed+tbulk) + tseed + tbulk = O(log n)·n` interactions.
2. **`phase3Convergence`** (D-2b) — the phase-3 CLOCK timed instance as a `PhaseConvergenceW
   (NonuniformMajority L K).transitionKernel`: `Pre = {c₀}`, `Post = HourComplete`, `t =
   phase3Horizon`, `ε = εtot` (an `ℝ≥0` upper bound on `εclock`). `convergence = final_minute_le_clock`.
   Matches `composeW_n_phases`'s interface (the `Phase2Convergence.phase2Convergence` template).
3. **`main_not_ahead_of_clock`** (D-2c) — Lemma 6.10 wired as the hour-ENTRY re-establishment: on
   the synchronous `Regime`, `(K^t) c₀ {Φ ≥ Φ c₀ + lam} ≤ exp(…)` — the Main population tracks the
   clock across hours, so the next hour's gated start re-establishes faithfully from the previous
   hour's completion. (= `HourCouplingV2.hour_coupling_v2`, exposed in the composition namespace.)
4. **`phase3Convergence_explicit`** (D-2d) — the explicit-budget variant: `εside := sideEps εQ
   εfloor εWu εP εB εge3 εno3 εcpos εsucc` (the §6 nine named feeders, width slice the concrete
   `εWAt`-majorant `εWu`), `ε = εclock(…, sideEps)`. The single carried input `hside` (τ-uniform
   `Sgood(T)ᶜ ≤ sideEps`) is supplied per-`τ` over the hour by `SideBudget.Sgood_compl_le_uniform`.

### THE BURN-IN / HOUR-ENTRY RE-ESTABLISHMENT — resolved precisely (no separate analysis needed).
* **No separate deterministic cross-hour chaining lemma.** The per-hour/minute composition is the
  UNION bound (B-10/B-11); each hour's marked chain starts fresh from the gated `mc₀ ∈ taintedGate n`
  (`recInv` hour-entry), the union sums per-hour budgets.
* **The burn-in IS the §6 width engine, already inside `εside`.** The per-hour marked-chain escape
  budget `heB` (`HourEscape.heB_of_sideB`) is discharged concretely by `SideBudget.heB_concrete` to
  `εsync = ∑_{τ<w·KK}(εWAt + εP + εB)`; `heB` feeds `EarlyDripMarked.windowedFrontProfile_whp_concrete`
  / `DotyParams.goodFrontWidth_whp_*` → the §6 width whp → the `εWAt` slice of the clock's `Sgood(T)ᶜ`
  prefix (`Sgood_compl_le_uniform`). The recurrence-invariant restart is thus already part of `εside`.
* **What hour-completion gives the next hour.** `HourComplete = BulkPost (K(L+1)−1)` is the GOOD
  branch of D-1's named `εB` residual: within hour `h`, either the bulk stays below (side budgets
  apply, charged in `εclock`) or the bulk arrives (`BulkPost` — hour completes, next hour re-establishes
  from `recInv`). The composition charges NOTHING extra for the boundary (the `εB` slice is inside
  `εside`); Lemma 6.10 (`main_not_ahead_of_clock`) guarantees the Mains do not run ahead.

### FINAL phase3 INSTANCE STATUS.
`phase3Convergence` / `phase3Convergence_explicit` ARE the deliverable `PhaseConvergenceW` for the
phase-3 (CLOCK) timed phase, on the real protocol kernel, matching `composeW_n_phases`'s interface.
`t = O(log n)·n` interactions (`/n = O(log n)` parallel), `ε = εclock = O(#minutes)·(bulk + side)`.

### PRECISE GAPS (surviving named inputs into `phase3Convergence`'s `hside`, all carried honestly).
The ONLY open input is `hside : ∀ T τ, (realκ^τ) c₀ Sgood(T)ᶜ ≤ εside` — the τ-uniform side bound.
Its provenance (per `SideBudget.Sgood_compl_le_uniform` + `ClockBudgets.sidePrefix_le_assembled`):
- the §6 WIDTH feeder `εWAt` — DISCHARGED concretely at every prefix horizon `τ = w·j+r ≤ w·KK`
  (B-13 + D-1); the only residual is the τ-uniform MAJORANT over the run (the documented
  sup-over-the-hour boundary) + the post-hour (`τ > w·KK`) absorbed width mode;
- the EIGHT non-width §-engine feeders `εQ εfloor εP εB εge3 εno3 εcpos εsucc` (distinct
  Qmix/floor/side-event/bulk-arrival/four-phase-gate masses), each its own §-engine, carried as
  named uniform whp inputs — the same eight residuals B-12/B-13/D-1 flagged.
These are NOT new gaps: they are exactly the surviving residuals from B-12/B-13/D-1, now threaded
through the phase-3 timed instance. Everything ABOVE `hside` (the final-minute domination, the
`PhaseConvergenceW` packaging, the Lemma-6.10 hour coupling, the explicit `sideEps`/`εclock` budget)
is FULLY PROVEN and axiom-clean. The phase-3 instance is ready for `compose_n_phases` (Phase D step 2)
once the other ten instances + the uniform `hside` discharge land.

## PHASE D-3 — the eleven-phase composition headline `doty_time_headline_W` DELIVERED (2026-06-10, 0-sorry axiom-clean)

NEW file `Probability/DotyTimeHeadline.lean` (namespace `ExactMajority`; imports
`PhaseConvergenceWeak` + `NonuniformMarkovChain` + `Analysis/StableEndpoints` — the minimal
closure, 23 transitive Ripple-local oleans). All four theorems `#print axioms ⊆ [propext,
Classical.choice, Quot.sound]`; single-file `lake env lean` EXIT_0; zero sorry / zero
native_decide / zero new axiom. SHA on main: cd24a347.

### What landed.
- `total_time_le_W` / `total_error_le_W` — the per-phase scaling arithmetic (`∑ t_i ≤
  (∑ Cphase)·n·(L+1)`; union budget `∑ ε ≤ ∑ δ`), independent of per-phase content.
- **`doty_time_composition_W`** — the WEAK-structure assembly contract over `composeW_n_phases`
  (`m = 11`). Given eleven `PhaseConvergenceW (NonuniformMajority L K).transitionKernel`
  instances + per-phase time/error bounds + chain maps `h_chain : Post_i ⟹ Pre_{i+1}` + start
  `hx₀` + closing map `h_post : Post_10 ⟹ majorityStableEndpoint init`, concludes the
  composed `(K^(∑t_i)) c₀ {¬ majorityStableEndpoint init} ≤ ∑ ε_i` together with
  `∑ t_i ≤ (∑ Cphase)·n·(L+1)` and `∑ ε ≤ ∑ δ`. Pure C-K assembly; no per-phase content used.
- **`doty_time_headline_W`** — the capstone. Specialising `Cphase i ≤ C0`, `∑ δ ≤ 1/n`:
  from `(phases 0).Pre c₀`, within `T ≤ 11·C0·n·(L+1) = O(n log n)` interactions
  (`O(L+1) = O(log n)` parallel time), the run reaches `majorityStableEndpoint init` with
  failure `≤ 1/n`. The final `Post` is `majorityStableEndpoint = phase2Consensus ∨ phase4Tie
  ∨ phase9Consensus ∨ phase10MajorityWitness` (stabilized at 2 ∨ at 4 ∨ at 9 ∨ reached 10's
  unanimity) — the stabilize-early branches threaded as disjuncts per the paper's structure.

### Design — why the weak-structure opaque-instance form is the honest Phase-D single theorem.
The campaign's Phase-B rewire retired the strong structure's `post_absorbing` (it forced the
FALSE `habs_mix` on the faithful clock minutes). Every real phase instance is therefore a
`PhaseConvergenceW`; the strong Phase-2/9 instance lifts via `PhaseConvergence.toW`. The
eleven instances all live on the SAME kernel family `(NonuniformMajority L K).transitionKernel`
(verified: `phase1Convergence`, `phase2Convergence.toW`, `phase3Convergence`,
`phase4Convergence`, `phase5Convergence`, `phase6Convergence'`, `phase7Convergence''`,
`phase8Convergence`, `phase10Convergence`, RoleSplit's 3-stage Phase-0). So `composeW_n_phases`
over the `Fin 11` family applies directly. This is the genuine Phase-D deliverable: the single
theorem with the COMPLETE named-input surface, distinct from `TimeComposition.doty_time_headline`
(which is the same shape but over the STRONG structure that the rewire retired).

### THE SURVIVING-INPUT INVENTORY (the honest Phase-D surface).
`doty_time_headline_W` is UNCONDITIONAL beyond exactly these named hypotheses (no axiom beyond
[propext, Classical.choice, Quot.sound], no sorry, no native_decide):
1. **The eleven instances** `phases : Fin 11 → PhaseConvergenceW K` — each a proven
   `PhaseConvergenceW` in its file. Per-instance Pre/Post (verified):
   - 0: RoleSplit (3-stage), Post `RoleSplitStage2Good` (`roleMCR=0 ∧ crCount≤1`). NB: the
     Phase-0 instance is itself a sub-composition (`phase0_roleSplit_whp_two_stage`,
     `composeW_n_phases` at m=3) — packaging it as a single `PhaseConvergenceW` with the
     role-count Post is the one instance still assembled FROM its stages; carried here as the
     family member `phases 0`. `Phase0Window.phase0_window_whp` supplies the clock-floor tail
     `{¬ noClockAtZero}` feeder (the Lemma-5.2 clock floor), not a standalone instance.
   - 1: `Phase1AllMain n ∧ extremeU ≤ M₀` → `Phase1AllMain n ∧ NoExtreme`.
   - 2: `Qwin U v n` → `Qwin U v n ∧ oFinished U n` (strong, `.toW`).
   - 3: `{c = c₀}` (clock-entry) → `HourComplete n mC`.
   - 4: `StableTie4 ∨ Qwin4 n` → `StableTie4 ∨ advFinished n` (the tie / non-tie disjunction).
   - 5: `Phase5AllWin n ∧ unsampledReserveU ≤ M₀` → `Phase5AllWin n ∧ ReserveSampleGood i K₀`.
   - 6: `Phase6Win n ∧ highMass l ≤ M₀` → `Phase6Win n ∧ highMass l = 0`.
   - 7: `Inv7Sum n ∧ classMassN σ ≤ M₀` → `Inv7Sum n ∧ classMassN σ = 0`.
   - 8: `Phase8AllMain n ∧ minorityU σ ≤ M₀` → `Phase8AllMain n ∧ minorityU σ = 0`.
   - 9: `Qwin U' v' n` → `Qwin U' v' n ∧ oFinished U' n` (second opinion union, `.toW`).
   - 10: `S1 n ∨ Tie1plus n` → `Phase10Post` (unanimous output).
2. **The chain maps** `h_chain : Post_i ⟹ Pre_{i+1}` — the ten deterministic structural
   bridges (phase-advance + carried floors: Phase 0's role counts → 1's window; Theorem-6.2
   structure from Phase 3 → 4/5/6's Pres; `ReserveSampleGood` from 5 → 6; the tie/non-tie
   disjunction threaded through 4→5). Carried as named input — each bridge is a
   deterministic-reachable `Analysis/` invariant; supplying all ten IS the honest Phase-D
   surface (NOT find-replace: the Posts as defined carry their own structural fact, and the
   cross-phase advance facts are the named deterministic bridges).
3. **The start** `hx₀ : (phases 0).Pre c₀` — validInitial → role-split-entry.
4. **The closing map** `h_post : Post_10 ⟹ majorityStableEndpoint init`.
5. **The per-phase carried drains** (folded into each instance, hence into `phases`): the
   `q`/`hstep` drain rates for 0/1/5/6/7/8 (the `OneSidedCancel` rectangle floors, [45]/Lemma
   7.x atoms); Phase 3's `hside` (τ-uniform `Sgood(T)ᶜ ≤ sideEps`, §6 nine named feeders, width
   slice via `εWAt`); Phase 5's `hConc`; the Lemma-5.2 clock floor. The consolidated
   B-12/B-13/D-1/D-2 residuals, threaded not re-opened.
6. **The scaling** `ht : t_i ≤ Cphase_i·n·(L+1)`, `hC0 : Cphase i ≤ C0`, `hδ : ∑ δ ≤ 1/n`.

### LARGEST CLOSED SUBSET / precise gaps.
CLOSED (proven, axiom-clean): the entire composition arithmetic + the C-K assembly +
the headline scaling — i.e. given the eleven instances + chain maps + h_post, the O(log n)
parallel-time whp stabilization is FULLY PROVEN. PRECISE GAP: the eleven instances and the ten
chain maps and h_post are the named-input surface (items 1–4 above). The single non-find-replace
work remaining to make this CLOSED-with-no-hypotheses is (a) packaging Phase 0's 3-stage into one
`PhaseConvergenceW` with role-count Post, and (b) discharging the ten deterministic chain maps
from the `Analysis/` invariants — both deterministic-reachable, both deferred to a follow-up
(Phase F) per the campaign's "carry the gap as a named side hypothesis, documented" doctrine.

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
one-sided assignable-target good set, the `assignableCount` definition, and the real-kernel
config-level `mcrCount` decrement for the one-sided good set) and wires what is mechanically
reachable; the `Θ(M·assignable/n²)` interactionPMF mass bound and the carried-invariant
milestone are the precise documented next gaps (exact signatures below).

### Phase C-1 (relay 2) — DELIVERED LEMMAS (all 0-sorry, axioms ⊆ [propext,Classical.choice,Quot.sound])

In `RoleSplitConcentration.lean` (after `phase0MilestonePhase_pMin_le_two_div`):
- `IsAssignable a` / `assignableCount c` — the one-sided conversion target predicate/count.
- `Phase0Transition_first_no_mcr_of_mcr_main` / `_of_mcr_cr` — Rule-2/Rule-3 s-side effect:
  MCR meets unassigned Main / RoleCR ⟹ s-output non-MCR. (C-1a, C-1b)
- `Phase0Transition_second_no_mcr_of_main_mcr` / `_of_cr_mcr` — t-side mirrors. (C-1b)
- `mcrCount_singleton'` / `mcrCount_pair'` — local pair-count helpers (upstream is private).
- `Phase0Transition_mcrCount_pair_lt_of_one_sided` + concrete `_of_mcr_assignable` /
  `_of_assignable_mcr` — pair-level `1→0` `mcrCount` drop per one-sided conversion. (C-1c)
- `phaseEpidemicUpdate_eq_self_of_both_phase0` + `Transition_roles_eq_phase0_of_both_phase0`
  — both `Transition` wrappers are role-identities at phase 0. (C-1d)
- `mcrCount_config_decrease_of_mcr_assignable` / `_of_assignable_mcr` — **real-kernel
  config-level** `mcrCount` strict decrement for the one-sided good set, the analogue of
  `mcrCount_config_decrease_of_phase0_mcr_pair` (Phase0Convergence) for the `Θ(M/n)` route. (C-1d/e)
- `assignableCount_pred_iff` — Bool↔Prop bridge for the mass/Finset-filter route. (C-1f)
Commits: C-1a 9ecbdc83 · C-1b 6aef813b · C-1c 1791b52c · C-1d e36b907d · C-1e fc42dce4 · C-1f 908d087e.

### Phase C-1 (relay 2) — PRECISE REMAINING GAP (exact next-lemma signatures)

The count-level chain is closed up to the **real-kernel config decrement**.  The mass bound
and milestone assembly remain.  Exact next atoms:

1. **Cross-class interaction-count sum** (the easy `s₁≠s₂` analogue of the private
   `sum_interactionCount_mcr`):
   `∑_{s₁ : role=mcr} ∑_{s₂ : assignable} c.interactionCount s₁ s₂ = mcrCount c · assignableCount c`.
   Here `mcr ≠ main,cr ⟹ s₁≠s₂`, so each term is `count s₁ · count s₂` (NO `−1`), giving the
   clean product.  Re-derive `mcrCount_singleton'`-style `sum_count = mcrCount`/`assignableCount`.

2. **One-sided interactionPMF mass bound** (clone `interactionPMF_toMeasure_mcr_phase0_ge`):
   `(c.interactionPMF hc).toMeasure {p | (p.1 mcr∧phase0∧p.2 assignable) ∨ (p.1 assignable∧p.2 mcr∧phase0) ∧ Applicable}
     ≥ ofReal((2·M·assignable)/(n(n−1)))`  (factor 2 = both ordered directions).

3. **Strengthened decrease prob** (clone `phase0_mcrCount_decrease_prob`, chaining #1+#2 through
   `stepDistOrSelf_toMeasure_ge` + the config-decrement lemmas above):
   `stepDistOrSelf c |>.toMeasure {c' | mcrCount c' < mcrCount c} ≥ ofReal((2·M·assignable)/(n(n−1)))`.

4. **The carried `assignableCount ≥ n/5` invariant.** `assignableCount` is NOT a function of
   `mcrCount`, so a milestone phase keyed on `mcrCount` alone cannot carry it.  Need an
   epidemic-style monotonicity lemma (analogue of Phase-2/4 `informedU`): once `mcrCount < 2n/3`,
   `assignableCount` is non-decreasing AND `≥ n/5` (Lemma 5.1's `s_f+m_f > n/5` Chernoff step —
   this is the ONE genuinely probabilistic ingredient, a Chernoff/Azuma bound on the early-phase
   split, not derivable by pure counting).  Thread it as a side predicate in a new milestone
   phase `phase0MilestonePhaseOneSided` whose `p i = (2·M·(n/5))/(n(n−1)) = Θ(M/n)`, giving
   `pMin = Θ(1/n)`, `meanTime = Σ_{M=2}^{n} (n(n−1))/(2·M·(n/5)) = Θ(n log n)`,
   `pMin·meanTime = Θ(log n) ≥ log n` — **the potential the witness needs**.

5. **Assemble `RoleSplitMilestone`** from `phase0MilestonePhaseOneSided` + the Stage-2 crCount
   family (campaign gap 1) + `post_sound` (deterministic 1:1 counts) ⟹ `roleSplitTail_le_inv_sq`
   ⟹ `phase0_roleSplit_whp_inv_sq`.

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

### Phase C-1 (relay 3) — DELIVERED: full one-sided/combined mass route (gap atoms #1–#3)

All in `RoleSplitConcentration.lean`, 0-sorry, 0 native_decide, axioms ⊆
[propext, Classical.choice, Quot.sound] (single-file EXIT_0, per-theorem #print axioms).

- **C-1g** SHA afb1d426: cross-class interaction-count sum.  `isAssignableBool`,
  `assignableCount_eq_countP`, `mcrF`/`assignF` Finsets, `sum_count_mcrF` /
  `sum_count_assignF` (filter-card identities), `sum_interactionCount_assignF_right`
  (per-MCR-initiator, **no −1** since mcr≠assignable), and the capstone
  `sum_interactionCount_mcr_assign : ∑_{mcrF}∑_{assignF} interactionCount =
  mcrCount·assignableCount`.  Gap atom #1.
- **C-1h** SHA 5cc360c7: one-sided PMF mass + decrease prob (atoms #2,#3).
  `applicable_of_pos_iCount'` (local), `interactionPMF_toMeasure_mcr_assign_ge`
  (mass of MCR×assignable applicable good set ≥ mcrCount·assignableCount/(card(card−1))),
  `phase0_mcrCount_decrease_prob_oneSided` (stepDistOrSelf mass on {mcrCount decreases}
  ≥ mcrCount·assignableCount/(n(n−1)) via stepDistOrSelf_toMeasure_ge +
  mcrCount_config_decrease_of_mcr_assignable).
- **C-1i** SHA 95524b2e: COMBINED rate (the paper's p = 2u/5n).
  `sum_interactionCount_mcrF_right` / `sum_interactionCount_mcr_mcr` (MCR×MCR diagonal,
  M(M−1), re-derived local), `mcrF_disjoint_assignF`, `sum_interactionCount_mcr_combined`
  (mcrF ×ˢ (mcrF∪assignF) = M(M−1)+M·assignable), `interactionPMF_toMeasure_mcr_combined_ge`,
  and `phase0_mcrCount_decrease_prob_combined`: stepDistOrSelf mass on {mcrCount decreases}
  ≥ [M(M−1) + M·assignable]/(n(n−1)).

### Phase C-1 (relay 3) — COUNT-IDENTITY FINDING (settles the prompt's hypothesis)

The prompt conjectured `mcrCount + assignableCount = n` on phase-0 configs, which would
make the Chernoff floor invariant unnecessary (pure-counting floor).  **This is FALSE.**
`Role` has FIVE constructors (main, reserve, clock, mcr, cr — Basic/Role.lean).
`assignableCount` counts only **unassigned** main/cr at phase 0.  Three populations are
neither MCR nor assignable: (i) reserve/clock agents (created by Stage-2 Rule 4: cr,cr →
clock,reserve); (ii) **assigned** main/cr agents — and `Phase0Transition` Rules 2,3
explicitly set `assigned := true` on the partner (Transition.lean L364–386), so the
one-sided conversion itself *removes* agents from the assignable pool; (iii) high-phase
agents.  So neither the identity nor a clean monotone `mcrCount + assignableCount = n`
holds, and the `assignableCount ≥ n/5` floor is a GENUINE probabilistic (Chernoff /
Lemma 5.1) ingredient, not derivable by counting.  Confirmed: Rule 1 (mcr,mcr→main,cr)
creates 2 *unassigned* assignables; Rules 2,3 consume one assignable (set assigned) per
MCR converted.

### Phase C-1 (relay 3) — PRECISE REMAINING GAP (atoms #4,#5) — STRUCTURAL BLOCKER

The combined per-step rate `[M(M−1)+M·assignable]/(n(n−1))` is delivered.  Reaching
`pMin = Θ(1/n)` from it needs `assignableCount ≥ n/5` AT THE ADVERSARIAL config.  But
`MilestonePhase.progress` (JansonHitting.lean L48–51) demands the rate `≥ p i`
**unconditionally** at *every* config with milestones `<i` reached and `i` unreached —
there is no slot to carry a side invariant.  For the last milestone (threshold 2), the
config `mcrCount = 2, assignableCount = 0` (all other agents reserve/clock) satisfies the
`progress` antecedent yet has combined rate `2/(n(n−1)) = Θ(1/n²)`, so `progress` with
`p i = Θ(1/n)` is FALSE there.  **The plain `MilestonePhase` cannot carry the floor — this
is the same modeling limitation the predecessor hit, now pinned precisely.**

To close atoms #4,#5, ONE of:
  (A) an **invariant-relative milestone** variant `MilestonePhaseOn` (carry a support-closed
      `Inv` — e.g. `assignableCount ≥ n/5 ∧ AllPhase0`; weaken `progress` to Inv-states;
      thread `Inv` through `milestone_hitting_time_bound`'s MGF chain — mirrors the E2
      `PotNonincrOn`/`coupon_expectedHitting_le_on` `_on`-ladder pattern), PLUS
  (B) the genuinely-probabilistic Chernoff lemma `assignableCount ≥ n/5` whp on the early
      phase-0 split (Lemma 5.1's `s_f + m_f > n/5` step) — NOT in the codebase; needs a
      Chernoff/Azuma bound on the assigned-pool growth.  This is the ONE irreducible
      probabilistic ingredient flagged since relay 1.
Then instantiate `RoleSplitMilestone` (atom #5): Stage-1 milestone via (A)+(B) at combined
rate, Stage-2 crCount family (cr,cr→clock,reserve at Θ(l²/n²), Corollary 4.4), `post_sound`
(deterministic 1:1 counts), → `roleSplitTail_le_inv_sq` → `phase0_roleSplit_whp_inv_sq`.
All the per-step *mass/rate* obligations are now discharged; the gap is (A) milestone-engine
extension + (B) the Chernoff floor.

## Phase C-7 / C-8 — one-sided cancellation (Phases 7 & 8) on the OneSidedCancel engine

Two new files instantiate the generic `OneSidedCancel` engine (form b, crude
uniform drain) for the minority-elimination phases.  Both deliver a real
`PhaseConvergenceW (NonuniformMajority L K).transitionKernel` with the engine's
`hmono` discharged from the actual transition rules; the per-step drain `hstep`
(and, for Phase 7 only, the full `InvClosed`) are carried as honest hypotheses
resting on the documented atoms below.

### Honest predicate / potential choices (vs HANDOFF sketch placeholders)
The sketch named `Phase6PostCore`/`Phase7PostCore`/`NoMinorityAtOrAboveL2`/
`IsMinority`/`NoMinority`/`initialMainCount` — none exist in the repo.  Replaced
with honest in-file predicates read off the real `cancelSplit` / `absorbConsume`
rules:
- `minoritySt σ a := a.role = .main ∧ ∃ i, a.bias = .dyadic σ i` — the Doty `B`-pool
  (minority sign σ a parameter); `minorityU σ c := countP (minoritySt σ) c`.
- `Inv7Main σ n c := card=n ∧ (∀a∈c, phase=7 ∧ role=main) ∧ MinorityHiIdx σ c` —
  Phase-7 window with the **index ordering** `MinorityHiIdx σ` (every σ-Main at
  exponent index ≥ every majority Main's index = Doty's "majority has larger mass").
- `Phase8AllMain n c := card=n ∧ ∀a∈c, phase=8 ∧ role=main` — Phase-8 window (no
  ordering needed: `absorbConsume` is sign-preserving).
- `NoMinority σ c := minorityU σ c = 0` = engine `potDone (minorityU σ)` — the
  honest `Post` (cancellation/consumption drains the WHOLE minority pool to 0).

### The honest mathematical core (the hard part, fully proved & axiom-clean)
**Phase 7 — `cancelSplit` minority non-increase.**  The gap-2 branch
`+2^{-i}, −2^{-j}  →  ±2^{-(i+1)}, ±2^{-(i+2)}` (j=i+2) copies the smaller-index
agent's sign onto BOTH outputs.  So the σ-count can only rise if the minority is the
smaller-index (higher-magnitude) agent — which the carried `MinorityHiIdx` ordering
forbids.  `cancelSplit_minorityU_pair_le` proves per-pair non-increase under that
ordering by exhausting all five `cancelSplit` branches against the index hypothesis
(C-7b).  **Phase 8 — `absorbConsume` minority non-increase** is UNCONDITIONAL: every
branch zeroes one bias or is identity, never flips a sign, so no ordering is needed
(`absorbConsume_minorityU_pair_le`, C-8b).

These per-pair facts lift through `Transition` (the reductions
`Transition_eq_{cancelSplit,absorbConsume}_of_phase{7,8}_main`: phase-7/8 epidemic =
id, phase-preserving rule, finishPhase10Entry = id; not-both-main leaves Mains
untouched) → config step (`minorityU_stepOrSelf_le`) → kernel support
(`minorityU_le_on_support`) → the engine's `PotNonincrOn`
(`potNonincrOn_minorityU`, typechecks against `OneSidedCancel.PotNonincrOn`).

### InvClosed
- **Phase 8: FULL** `invClosed_phase8AllMain` (typechecks against
  `OneSidedCancel.InvClosed`) — `absorbConsume` preserves phase + role, every pair on
  the window is both-Main, card via `reachable_card_eq`.  No documented gap.
- **Phase 7: structural core proved** (`Phase7AllMain_support_closed`: card+phase+role
  via `cancelSplit_phase`/`cancelSplit_role`).  The remaining atom is
  **`MinorityHiIdx σ` closure under `cancelSplit`** (gap-1 lowers the survivor's index
  by 1, gap-2 produces two fresh indices i+1,i+2) — exposed as the `hClosed` hypothesis
  of `phase7Convergence`.

### Remaining atoms (documented boundary, by design — both files 0-sorry)
1. **The drain `hstep`** (both files): per-step failure-to-consume ≤ q from the
   eliminator floor — the Phase-4 `advanced_advance_prob_of_rect` analogue
   (eliminator-state × minority-state interaction-count rectangle → probability).
   The eliminator floor is the carried Doty Lemma 7.4/7.6 fact (≥0.8|M| majority vs
   ≤0.2|M| minority).  **Phase 8 shrinking-eliminator handling**: `absorbConsume` sets
   the consumer `full := true` (it drops from the eliminator pool), but Φ=minorityU is
   non-increasing regardless of `full` (consumption only zeroes biases — proved
   unconditionally), and the floor enters ONLY through `q`; the honest invariant is
   non-full-majority ≥ minority-remaining + margin (Lemma 7.6).
2. **Phase 7 `MinorityHiIdx` closure** (Phase 7 only) — see above.

### Deliverables (theorems)
- `Phase7Convergence.phase7Convergence (σ n) (hClosed) (q) (hstep) (M₀ t ε) (hε)
  : PhaseConvergenceW (NonuniformMajority L K).transitionKernel` — Pre = `Inv7Main n σ
  ∧ minorityU σ ≤ M₀`, Post = `Inv7Main n σ ∧ minorityU σ = 0`.
- `Phase8Convergence.phase8Convergence (σ n) (q) (hstep) (M₀ t ε) (hε)
  : PhaseConvergenceW (NonuniformMajority L K).transitionKernel` — Pre = `Phase8AllMain
  n ∧ minorityU σ ≤ M₀`, Post = `Phase8AllMain n ∧ minorityU σ = 0`.  FULL InvClosed
  (no hClosed hypothesis needed).
Each `#print axioms ⊆ [propext, Classical.choice, Quot.sound]`; single-file EXIT_0.

### Three-window chaining (Phase 7 levels −l, −(l+1), −(l+2))
The paper's three successive elimination windows compose via
`composeW_two_phases` (twice) on the three `phase7Convergence` instances at the
three index levels (the Pre/Post `minorityU σ ≤ M₀ → = 0` chain links directly).
Documented; not assembled here pending the per-level drain `q m` from the rectangle.

Commits: C-7a 33e84eae (predicate+reduction) · C-7b 10863f44 (cancelSplit pair
non-increase) · C-7c 6a3fdebc (MinorityHiIdx + not-both-main) · C-7d f11bb389
(Transition both-main pair) · C-7e 1c69fc85 (config+support non-increase) ·
C-7f 2d6d24ab (kernel PotNonincrOn) · C-7g c2e709e6 (structural closure) ·
C-7h 85eb8280 (phase7Convergence) · C-8a 4ed79373 (reduction) · C-8b 70b3ffb1
(absorbConsume pair) · C-8c 09544472 (full non-increase chain) · C-8d 1ded5789
(FULL InvClosed) · C-8e 1a930fe5 (phase8Convergence).

### Phase C-7i…C-8j (relay 4) — the DRAIN RECTANGLE LAYER (the `hstep`/`hdrop` floor)

Built the full drain chain for both phases, end-to-end down to the carried eliminator
floor.  Both files compile single-file EXIT_0, every new theorem axiom-clean (⊆
[propext, Classical.choice, Quot.sound]).

**Phase 8 (`absorbConsume`, unconditional):**
- **C-8f** SHA 20e4369b `absorbConsume_minorityU_pair_drop`: per-pair strict drain —
  `s`=σ-minority@i, `t`=opposite-sign Main@j with `j>i`, `¬t.full` ⇒ second consume
  branch zeroes `s` ⇒ pair σ-count drops by 1 (`+1 ≤`).
- **C-8g** SHA 72662b7e `minorityU_stepOrSelf_drop`: lift to config — an applicable
  (minority@i, elim@>i,¬full) pair drops global `minorityU σ` by 1.
- **C-8h** SHA 44431bda `drop_prob_of_rect`: the Φ-AGNOSTIC drop-rectangle bound — the
  DUAL of `Phase4Convergence.advanced_advance_prob_of_rect`, targeting the DECREASE
  event `{c' | Φ c'+1 ≤ Φ c}`.  Rect `R` of per-cell-drop pairs ⇒ drop-prob ≥
  N/(n(n−1)), N ≤ ∑_R interactionCount.  (Later relocated to Phase 7, see C-7j.)
- **C-8i** SHA e9f07b11 `minorityU_drop_prob_rect`: per-level rect `minorityAt(i) ×ˢ
  elimAbove(i)` (cross pairs distinct via index i vs >i) ⇒ drop-prob ≥
  #min(i)·#elim(>i)/(n(n−1)).
- **C-8j** SHA 6b265ccc `minorityU_hdrop_of_floor`: the engine `hdrop` from a
  drop-probability floor `p`.  Drop-success event `{Φ c'+1 ≤ m} = potBelow Φ m`;
  `transitionKernel` is Markov (total mass 1) ⇒ failure `K b (potBelow Φ m)ᶜ = 1 −
  success ≤ 1 − p`.  This is the level-decomposed-engine (form a) `hdrop` shape.

**Phase 7 (`cancelSplit` gap-1, drop direction needs only gap-1 geometry):**
- **C-7i** SHA 9ff3831f `cancelSplit_minorityU_pair_drop` + `minorityU_stepOrSelf_drop`:
  gap-1 cell — `s`=σ.flip-elim@i, `t`=σ-minority@j=i+1 ⇒ gap-1 branch zeroes the
  larger-index agent `t` (minority) ⇒ drops by 1; lifted to config.
- **C-7j** SHA 582a5011: shared generic `drop_prob_of_rect` +
  `sum_interactionCount_cross_disjoint7` now live in Phase 7 (imported by Phase 8);
  `minorityU_drop_prob_rect7` (rect `elimGap1(i) ×ˢ minorityAt7(j)`, i+1=j) +
  `minorityU_hdrop_of_floor7` (the Phase-7 hdrop bridge).

**What remains (the genuine documented boundary — the carried floor `p`):**
The engine `hdrop`/`hstep` is now `1 − p`-shaped where `p = #min·#elim/(n(n−1))` is the
rectangle floor.  Supplying a CONCRETE non-trivial `p` (the level-m drain rate) requires
the carried eliminator floor `#elim ≥ margin` and `#min ≥ 1` — Doty Lemma 7.4/7.6's
`≥0.8|M|` majority vs `≤0.2|M|` minority — which is a CARRIED INVARIANT, not derivable
from the transition rule.  The mathematical layer from rule → per-cell drop → rectangle
→ drop-probability → engine `hdrop` is now FULLY PROVED; only the floor's numeric value
is the carried Doty input.

### Phase C-7 (relay 4) — FINDING: `MinorityHiIdx` is NOT closed under `cancelSplit`

The Phase-7 `hClosed` atom (the `MinorityHiIdx σ` closure carried as a hypothesis of
`phase7Convergence`) is **NOT provable as stated** — `MinorityHiIdx` is genuinely not
one-step closed.  Counterexample mechanism: `MinorityHiIdx` permits a σ-Main and a
σ.flip-Main coexisting at the SAME index (they form a gap-0 pair satisfying `i ≤ i`).
A gap-1 fire on a DIFFERENT σ.flip-Main@i with a σ-Main@i+1 RAISES that majority agent's
index to i+1, which then exceeds the coexisting σ-Main still at index i ⇒ ordering
violated.  Strict separation and fixed-threshold variants fail identically (cancelSplit
RAISES the surviving majority's index toward the minority levels — the survivor lands on
the consumed minority's vacated level, where another minority may sit).  This matches the
campaign's own §6 note (line 199): the cancel stage uses a CONSERVED SIGNED SUM, not an
index ordering, for |B| monotonicity.  **Conclusion:** Phase-7 `minorityU` non-increase
genuinely needs the ordering per-pair (gap-2 sign-copy), but the ordering invariant is
fragile; the correct closed Phase-7 invariant is the signed-sum potential, a different
construction.  The drain rectangle (C-7i/j) is INDEPENDENT of `hClosed` — it needs only
the gap-1 cell geometry, so it stands regardless.

### Phase C-7k…C-7m (relay 5) — REBUILT the Phase-7 invariant layer on the CONSERVED SIGNED SUM

The relay-5 work replaces the broken `MinorityHiIdx`-carrying `Inv7Main` with the
genuinely-closed signed-sum invariant.  All in `Phase7Convergence.lean`, single-file
EXIT_0, every new theorem `#print axioms ⊆ [propext, Classical.choice, Quot.sound]`.
Phase8Convergence.lean (importer) still EXIT_0, untouched.

- **C-7k** SHA `45419405` — signed-mass infra + `cancelSplit_agentSignedMass_pair_eq`.
  `biasSignedMass L : Bias L → ℤ` = the `2^L`-scaled signed dyadic mass (`±2^{L-i}` for
  `dyadic ± i`, integer since `i ≤ L`); `agentSignedMass`, `phase7SignedSum c = ∑`.
  Per-pair conservation across ALL FIVE `cancelSplit` branches (gap-0 `+x−x=0`; gap-1
  `2^{L-i}−2^{L-(i+1)}=2^{L-(i+1)}`; gap-2 `2^{L-i}−2^{L-(i+2)}=2^{L-(i+1)}+2^{L-(i+2)}`),
  proved by `cases ss <;> cases st <;> simp_all [biasSignedMass] <;> simp only [pow_succ] <;> ring`.
- **C-7l** SHA `5ebe7148` — config+support conservation + `invClosed_Inv7Sum` (the
  discharged `hClosed`).  `phase7SignedSum_stepOrSelf_eq` lifts the per-pair identity
  through the `c−{r₁,r₂}+{out₁,out₂}` step decomposition (mirror of
  `phase10ActiveSignedSum_stepRel_eq`'s `add_left_comm` arithmetic), self-case identity;
  `phase7SignedSum_support_eq` lifts to the kernel support; `Inv7Sum n c := Phase7AllMain
  n c ∧ 0 < phase7SignedSum c`; `invClosed_Inv7Sum` discharges the
  `OneSidedCancel.InvClosed` shape (off-support mass 0 via the Phase-8 disjoint-support
  pattern, on-support both conjuncts stable).
- **C-7m** SHA `d49510fc` — the residual gap as a HARD per-pair fact +
  the rebuilt instance.  `gap2_minorityU_rise_compatible_with_pos_sum`: a gap-2 cancel
  on (σ-minority @ smaller index `i`, σ.flip @ `i+2`) makes BOTH outputs σ-minority
  (pair `minorityU` RISES +1) WHILE conserving the signed mass — so `0 < phase7SignedSum`
  CANNOT supply per-pair `minorityU` non-increase.  `phase7Convergence'`: the rebuilt
  `PhaseConvergenceW` on `Inv7Sum` with `hClosed = invClosed_Inv7Sum n` now INTERNAL
  (proved, not carried); `Pre = Inv7Sum ∧ minorityU ≤ M₀`, `Post = Inv7Sum ∧ minorityU = 0`.

**Net status of the Phase-7 `phase7Convergence'` instance** (relay 5):
- `hClosed` — **DISCHARGED** (`invClosed_Inv7Sum n`, fully internal).
- `hmono : PotNonincrOn Inv7Sum K minorityU` — **carried** (honest residual).  This is
  strictly stronger than `0 < signedSum`: `gap2_minorityU_rise_compatible_with_pos_sum`
  proves the gap-2 minority rise is signed-sum-conserving, so per-pair `minorityU`
  monotonicity genuinely needs the per-pair ordering content (the minority at the
  SMALLER magnitude / LARGER index) ON TOP of the signed-sum invariant.  The
  signed-sum is the right *closed* potential for `hClosed`; it is not by itself the
  monotonicity certificate.  The old `Inv7Main` carried `MinorityHiIdx` to get `hmono`
  but then could not close it — relay 5 trades that for a closed invariant + an honest
  carried `hmono`.
- `hstep` — carried (the eliminator floor, unchanged from relay 4; rectangle layer is
  independent of the invariant choice).

**Precise remaining gap (for the next relay).**  To discharge `hmono` honestly one
needs a configurational invariant that (i) is one-step closed and (ii) implies, on every
both-Main pair, that the σ-minority sits at the larger index (so the gap-2 sign-copy
never lands on a majority agent).  Candidate: carry `Inv7Sum` PLUS a SEPARATE
"minority-mass-bounded" fact `phase7MinoritySignedMass ≤ phase7MajoritySignedMass − margin`
(the per-level Doty Lemma 7.4 floor as a signed-mass inequality, not an index ordering) —
this is conserved/monotone by the same `cancelSplit_agentSignedMass_pair_eq` machinery
restricted to each sign class, and DOES force the per-pair ordering.  Not yet built; the
signed-mass split by sign class is the natural next atom.

### Phase C-7n…C-7p (relay 6) — `hmono` DISCHARGED via the SIGN-CLASS MASS potential

Relay 6 closes the residual `hmono` gap, NOT by carrying an extra inequality, but by
**replacing the potential**: the engine is driven by the σ-class MASS `classMassN σ`
(non-increasing) instead of the count `minorityU σ` (which the relay-5 obstruction showed
can RISE).  All in `Phase7Convergence.lean`, single-file EXIT_0, Phase8 importer EXIT_0,
every new theorem `#print axioms ⊆ [propext, Classical.choice, Quot.sound]`.

**Licensed-check outcome (global vs per-level potential).**  Verified against the paper
(`/tmp/doty_paper.txt`).  Lemma 7.4 is a MASS-floor (`|M'| ≥ 0.8|M|` because the only way
to lose a majority agent is cancelling against minority, bounded by the minority MASS
`β_ ≤ 0.004|M|2^{-l}`); Lemma 7.5 is SUCCESSIVE per-level elimination
(`|B_{-l}|→0`, then `|B_{-(l+1)}|→0`, then `|B_{-(l+2)}|→0`).  **Both a global `minorityU`
and any per-level `minorityAt7 i` potential need `PotNonincrOn` for THAT Φ, and BOTH are
broken by the identical gap-2 sign-copy** (the engine `crude_PhaseConvergenceW`
structurally requires `hmono` — it makes `{Φ ≤ m}` absorbing).  Switching to per-level does
NOT dodge the obstruction.  The genuinely non-increasing object is the **σ-class mass**:
the paper's own Lemma 7.4 mass argument.  So: built the mass potential, NOT a per-level
count.  Documented.

- **C-7n** SHA `739da267` — `biasClassMass σ`/`agentClassMass σ`/`classMass σ`
  (nonnegative `2^L`-scaled σ-class dyadic mass) + `cancelSplit_classMass_pair_le`:
  per-pair σ-class mass NON-INCREASE in EVERY `cancelSplit` branch, NO index-ordering
  hypothesis.  Crucial gap-2 branch (the relay-5 obstruction): the smaller-index class
  GAINS `2^{L-(i+1)}+2^{L-(i+2)} = 2^{L-i}-2^{L-(i+2)}` and LOSES `2^{L-i}`, net DROP
  `2^{L-(i+2)}` — the minority *mass* DROPS exactly where its *count* rises.
- **C-7o** SHA `e88d93e4` — `classMass_stepOrSelf_le`/`classMass_support_le` (config &
  support lift, mirror of `phase7SignedSum_stepOrSelf_eq` with `=`→`≤`), the ℕ-potential
  `classMassN σ := (classMass σ).toNat`, `potNonincrOn_classMassN` (**the engine `hmono`
  on `Inv7Sum`, DISCHARGED**), and the bridge `minorityU_eq_zero_of_classMassN_zero`
  (`classMass σ c = 0` ⟹ `minorityU σ c = 0`, since each σ-Main contributes mass `≥ 1`).
- **C-7p** SHA `1f4b7654` — `phase7Convergence''`: the CLEANED engine on `Inv7Sum` with
  `Φ = classMassN σ`, **BOTH** `hClosed = invClosed_Inv7Sum n` **AND**
  `hmono = potNonincrOn_classMassN σ n` PROVED INTERNAL (no longer carried).
  `phase7Convergence''_post_noMinority`: `Post` (`Inv7Sum ∧ classMassN σ = 0`) ⟹
  `NoMinority σ`.

**Net status (relay 6).**
- `hClosed` — DISCHARGED (`invClosed_Inv7Sum n`).
- `hmono`   — **DISCHARGED** (`potNonincrOn_classMassN σ n`).  The relay-5 residual is
  closed: the obstruction was to the COUNT, not the MASS.
- `hstep`   — carried, **now phrased on `classMassN σ`** (a σ-class-MASS drain, the Doty
  Lemma 7.4/7.5 floor as a mass drain), in `phase7Convergence''`.

**Precise remaining gap (for the next relay).**  The drain rectangle layer (C-7i/j,
`minorityU_drop_prob_rect7`) proves a *count* drop per gap-1 cell; the cleaned engine's
`hstep` needs a *mass* drop.  The re-derivation is mechanical: a gap-1 cancel
(minority@i+1, majority@i) removes the minority agent, dropping `classMassN σ` by
`2^{L-(i+1)}` (its mass) — so the per-pair `classMass`-drop building block
(`cancelSplit_classMass_pair_drop`, gap-1, `+2^{L-(i+1)} ≤`) plus the existing
`drop_prob_of_rect` machinery re-instantiated for `classMassN` yields the carried `hstep`.
The signed/count rectangle geometry is unchanged; only the potential in the cells differs.
Three-window chaining (Lemma 7.5's `B_{-l}→B_{-(l+1)}→B_{-(l+2)}`) then chains three
`phase7Convergence''` instances at the per-level mass budgets.

### Phase C-1 (relay 4) — GAP (A) CLOSED + GAP (B) PINNED DETERMINISTICALLY

**Gap (A) — the invariant-relative milestone engine — COMPLETE (0-sorry, axiom-clean).**
Commits: C-1j (in 85eb8280, bundled by a concurrent agent) + C-1k 60eba6a5 + C-1m 718b0d5a.
New generic engine `MilestonePhaseOn` in RoleSplitConcentration.lean (own namespace):
- structure with side invariant `Inv`, one-step-closure `inv_closed`, and
  `progress_on` required ONLY at `Inv`-configs (the slot the plain `MilestonePhase`
  lacks).  `toDummyMP` (milestone := fun _ _ => True) borrows the pure-MGF
  optimisation `janson_exponential_tail_from_mgf` verbatim (pMin/meanTime depend
  only on (k,p), so `rfl`-equal).
- full Inv-relative MGF chain re-derived (JansonHitting privates not exported):
  `mgfFactor`/`partialMGF`/`truncMGF`, `partialMGF_one_step_contraction_on`
  (the only place `progress_on` is consumed — with `Inv c` exactly available),
  `truncMGF_contracts_on`, `lintegral_geometric_decay_on` (induction using
  `inv_closed` to stay in `Inv`, mass 0 off `Inv`), `milestone_tail_bound_via_mgf_on`
  (Markov), capstone `milestone_hitting_time_bound_on` — SAME
  `exp(-pMin·meanTime·(λ-1-ln λ))` tail as the plain engine.
- assembled discharge: `roleSplitTail_le_milestoneTail_on` → `_jansonExp_on` →
  `roleSplitTail_le_inv_sq_on` (1/n² budget from a floor-carrying witness).
Mirrors the E2 `InvClosed`/`PotNonincrOn` `_on`-ladder, lifted to the Janson engine.

**Gap (B) — the floor — PINNED: deterministic skeleton FAILS in this encoding,
Chernoff is genuinely needed (0-sorry, axiom-clean).** Commit C-1l 1acd65ae.
Tried the prompt's deterministic regime-split FIRST; proved the per-rule
`assignableCount` delta at the transition level, which SETTLES the route:
- `assignable_rule2_s_stays`: Rule 2 (MCR + unassigned Main) makes the MCR a
  FRESH unassigned CR (role=cr, ¬assigned, phase 0) → Rule 2 CONSERVES, Δ = 0.
- `assignable_rule3_s_assigned`: Rule 3 (MCR + unassigned RoleCR) makes the MCR an
  ASSIGNED Main → Rule 3 CONSUMES, Δ = −1.
Net per-rule: R1 +2, R2 0, R3 −1, R4 −2.  So `assignableCount` is NOT monotone in
THIS encoding — unlike the paper's reaction 3 `Mf,U → Mt,Sf` which creates a fresh
unassigned `Sf` and conserves the pool (the paper's "sf+mf can never decrease").
The divergence is Rule 3: our encoding marks the converted MCR as an *assigned*
Main rather than producing a fresh *unassigned* RoleCR.  Therefore the clean
deterministic floor does NOT transfer; Gap (B) needs the genuine Chernoff floor
(`assignableCount ≥ n/5` whp on the early split, paper Lemma 5.1's Chernoff step) —
the ONE irreducible probabilistic ingredient flagged since relay 1.  This is now a
*proven* fact, not a guess.

**REMAINING to finish Lemma 5.2** (exact inputs to `roleSplitTail_le_inv_sq_on`):
  (i) construct the `MilestonePhaseOn` witness: milestone = `mcrCount` thresholds,
      `Inv` = `assignableCount ≥ n/5 ∧ AllPhase0` (or the paper's `sf+mf > n/5`
      monotone surrogate — note R3 means `assignableCount` itself is not the right
      monotone, so `Inv` should be a CHERNOFF-established floor, carried by
      `inv_closed` once established), `progress_on` = combined rate `Θ(M/n)` from
      `phase0_mcrCount_decrease_prob_combined` (already delivered) restricted to
      `Inv`-configs where `assignableCount ≥ n/5` makes the rate `≥ Θ(M/n)`,
      `inv_closed` = the floor is one-step-closed (needs the Chernoff floor to be a
      closed invariant — i.e. once `≥ n/5`, the regime where it can't drop below).
  (ii) Gap (B) Chernoff: `assignableCount ≥ n/5` whp while `u ≥ 2n/3` (paper's
       fraction-½-top-reaction Chernoff).  Via in-house MGF/drift (NOT axiomatised).
  (iii) Stage-2 (cr,cr→clock,reserve at Θ(l²/n²), Corollary 4.4): own milestone
        family, same diagonal pattern; chain stages via composition.
All per-step *mass/rate* obligations and the *engine* (Gap A) are now discharged;
the genuine open work is (ii) the Chernoff floor + (i) wiring it as `inv_closed`.

### Phase C-1 (relay 5) — FLOOR→RATE BRIDGE DELIVERED + INV_CLOSED WALL PROVEN STRUCTURAL

Commits: C-1n 69a8e2af (floor→rate bridge) · C-1o 7421b90b (floorRate p-field validity).

**Task (i) mechanical core — DELIVERED (0-sorry, axiom-clean ⊆ [propext,Classical.choice,Quot.sound]).**
- `phase0_mcrCount_decrease_prob_floor (c n a₀) (card=n) (n≥2) (mcr⇒phase0)
  (a₀ ≤ assignableCount c) : stepDistOrSelf-mass {mcrCount drops} ≥
  ofReal((mcrCount·a₀)/(n(n−1)))`.  Drops the diagonal `M(M−1) ≥ 0` term off
  `phase0_mcrCount_decrease_prob_combined` and keeps the floor-driven `M·a₀` term.
  This is EXACTLY the `progress_on` rate the `MilestonePhaseOn` engine consumes —
  the mechanical wiring that *consumes* a floor once supplied.  The floor enters
  as an abstract `a₀ ≤ assignableCount c` hypothesis (no `n/5` baked in).
- `floorRate n a₀ M := (M·a₀)/(n(n−1))` + `floorRate_pos` (M≥1,a₀≥1,n≥2) +
  `floorRate_le_one` (M≤n, a₀≤n−1).  These are the `MilestonePhaseOn.hp_pos` /
  `hp_le_one` fields for the floor-driven `p i`.  (`a₀ ≈ n/5 ≤ n−1` for n≥2, so
  `floorRate_le_one` covers the Chernoff floor; the high-M milestones where
  M·a₀ might exceed n(n−1) are carried by the diagonal term, not floorRate.)

**THE `inv_closed` WALL IS STRUCTURAL — PROVEN, NOT A GUESS.**  The inherited
`MilestonePhaseOn.inv_closed` demands DETERMINISTIC one-step closure
(`transitionKernel c {c'|¬Inv c'} = 0`).  A whp Chernoff floor CANNOT satisfy this:
1. **No deterministic floor exists.**  `Phase0Initial` ⟹ ALL n agents are MCR ⟹
   `assignableCount = 0` at t=0 (`IsAssignable` needs role∈{main,cr}, but all are mcr).
   The assignable pool is *created* by R1 (+2 per firing), so it grows from 0 — there
   is no deterministic relation `mcrCount large ⟹ assignableCount ≥ a₀` to lean on.
   Combined with relay-4's proven non-monotonicity (R3 `assignable_rule3_s_assigned`
   marks the converted MCR ASSIGNED, Δassignable = −1), `assignableCount ≥ a₀` is
   neither initially-true nor deterministically-closed for any a₀ ≥ 1.
2. **The leak-relaxation does NOT reduce to a union bound.**  Relaxing `inv_closed`
   to a per-step leak ε (mass ≤ ε on ¬Inv) FAILS cleanly because `truncMGF` is NOT
   bounded by 1 off `Inv`: `partialMGF = ∏ mgfFactor` with each factor ≥ 1, so the
   leak set carries the FULL (unbounded) MGF, not ε.  Bounding the leak contribution
   needs the chain to not re-enter ¬Inv with large MGF — a genuine coupling/absorption
   argument (the paper's actual Lemma 5.1 joint-process Chernoff), NOT mechanical wiring.

**PRECISE REMAINING GAP (the irreducible probabilistic core, unchanged in nature
from relay 1, now bounded tightly).**  To finish Lemma 5.2 one needs a NEW engine
that threads the floor probabilistically — either:
  (a) a joint (mcrCount, assignableCount) Chernoff/Azuma showing
      `assignableCount ≥ n/5 whp throughout the Stage-1 horizon`, fed as a separate
      union-bound budget term `εfloor ≤ exp(−Θ(n))` ADDED to the `1/n²` Janson tail
      (NOT through `Inv`); the `MilestonePhaseOn` engine then runs on the EVENT
      `{floor holds throughout}` where `progress_on` is valid by C-1n; or
  (b) a coupling absorbing the ¬Inv excursions.
Both are the paper's Lemma 5.1 probabilistic content; neither is assemblable from
the delivered count/rate atoms.  C-1n + C-1o discharge the ENTIRE rate side: given
the floor as a hypothesis (`a₀ ≤ assignableCount c`), the `Θ(M/n)` progress rate
and its `hp_pos`/`hp_le_one` validity are now mechanical.  The open atom is the
SINGLE Chernoff floor (`assignableCount ≥ n/5 whp`), and its wiring is now (a):
a union term, because the engine's deterministic `inv_closed` provably cannot host it.

**Stage 2 (task 3) — NOT STARTED** (blocked behind Stage-1 floor for the chained
assembly; the crCount milestone family is mechanically analogous to Stage-1's
diagonal R1 part once the Stage-1 floor route is fixed, but the crCount floor
itself flows from the Stage-1 assignable→cr output, so it sits downstream of (a)).

### Phase C-1 (relay 6) — KILLED-KERNEL ROUTE: inv_closed DISSOLVED, floor as additive union (0-sorry, axiom-clean)

Commits: C-1p bac180d5 · C-1q 26dcd5c2 · C-1r cbc23cb1 · C-1s 50c780f0 · C-1t 83b7beb6
· C-1u 121394c2 · C-1v dfcaf6b4 · C-1w 082a6873 · C-1x 0c0356e3 · C-1y 4754d53c · C-1z e51febe7.

**THE RESOLUTION of relay-5's structural inv_closed wall — DELIVERED.**  Relay 5 proved the
deterministic `MilestonePhaseOn.inv_closed` provably cannot host a whp floor.  Relay 6
realises route (a) — the floor as an additive union term — via the immediate-kill gated
kernel `GatedDrift.killK_now` (GatedKillNow.lean, inherited).  `RoleSplitConcentration.lean`
now imports GatedKillNow and adds the full route:

1. **Structural decomposition (C-1p/q/r).**  `real_bad_le_escape_add_killedAliveBad`:
   `(K^t) x {bad} ≤ killed{none} + killed{alive-bad}` (via `real_le_killed_now` +
   subadditivity).  `killedEscape_le_prefix` re-exports `kill_now_escape_le_prefix_union`
   (εfloor ≤ t·q + ∑_{τ<t}(K^τ)x Sᶜ).  `real_bad_le_killedAliveBad_add_escape` assembles
   them.  `killedAliveBad_le_killedAliveNotGood`: alive-bad ⊆ alive-(¬good) when good⊃¬bad.

2. **Kernel-generic milestone engine `KernelMilestone` (C-1s–C-1y) — THE NEW ENGINE.**
   The protocol-bound `MilestonePhaseOn` uses `P.stepDistOrSelf.support`; `killK_now` is a
   bare `Kernel (Option α) (Option α)`.  Re-derived the ENTIRE Janson MGF tail over an
   ABSTRACT Markov kernel `Q : Kernel β β` ([DiscreteMeasurableSpace β] [Countable β]),
   with kernel positive-mass support (`0 < Q c {c'}`) replacing PMF support and — crucially
   — **NO `Inv`/`inv_closed` field**: `progress`/`milestone_monotone` are GLOBAL, so the
   contraction holds at every state (cemetery included).  Pieces:
   - `measure_compl_eq_zero_of_singleton` (the PMF-free support→ae bridge: on a countable
     discrete space, zero singleton-masses ⟹ null set; replaces
     `PMF.toMeasure_apply_eq_zero_iff`).
   - `mgfFactor`/`partialMGF`/`truncMGF` + `partialMGF_mono_of_support`/`_drop_reached`
     (kernel support), `post_absorbing` (via the null-set bridge), `firstUnreached`
     selectors, `partialMGF_pointwise_bound`, `partialMGF_one_step_contraction` (where
     `progress` is consumed; reuses `MilestonePhaseOn.mgf_contraction_identity`),
     `truncMGF_contracts`, `lintegral_geometric_decay` (plain induction — NO inv-closure
     threading), `not_post_subset_ge_one`, `pMin_pos`/`pMin_le`,
     `milestone_tail_bound_via_mgf`, CAPSTONE `milestone_hitting_time_bound` (same Janson
     tail `exp(−pMin·meanTime·(λ−1−ln λ))`, host `Protocol P` borrows the pure-MGF opt via
     `toDummyMP`, all `(k,p)`-determined rfl-equal).

3. **Stage-1 union assembly (C-1z).**  `killedAliveNotGood_le_janson`: a `KernelMilestone
   (killK_now K G)` witness whose `Post (some y) ⟹ good y` bounds killed-alive-(¬good) by
   the Janson tail.  `real_bad_le_janson_add_escape` (HEADLINE):
     `(K^t) c₀ {¬good} ≤ exp(−pMin·meanTime·(λ−1−ln λ)) + (t·q + ∑_{τ<t}(K^τ)c₀ Sᶜ)`.
   The floor enters ONLY as the additive escape budget; `inv_closed` is DISSOLVED into the
   `killK_now` construction (`alive_support_gate` makes alive⟹gated by construction, which
   the witness's `progress` exploits).  Per-theorem `#print axioms ⊆ [propext,
   Classical.choice, Quot.sound]`; single-file EXIT_0.

**Warm-up / gate design (chosen).**  Gate `G` := the floor region {assignableCount ≥ floor}
∪ the milestone region.  c₀ (all-MCR, assignableCount = 0) is handled by the side-set `S`
machinery of `kill_now_escape_le_prefix_union`: `S` = the favourable-drift regime, the
prefix `∑ (K^τ)c₀ Sᶜ` term absorbs the warm-up where the floor is not yet established (the
early R1-dominated phase where assignable grows from 0).  The engine clock effectively
starts once gated; the escape prefix is the honest warm-up cost.

**εfloor final form.**  `εfloor = t·q + ∑_{τ<t}(K^τ)c₀ Sᶜ`, where `q` = per-step
gate-exit (floor-breach) probability on the favourable regime `S` (the Chernoff per-step
rate), and the prefix is the mass of having left `S`.  Both are `n^{-2}`-shape, unioned
with the `1/n²` Janson budget of the alive-bad term.

**Stage-1 status: STRUCTURALLY COMPLETE up to one concrete construction.**  Everything
abstract is discharged 0-sorry axiom-clean.  The SINGLE remaining atom is now sharply
isolated: construct the concrete `KernelMilestone (killK_now K G)` witness for the role
split — define the lifted mcrCount-threshold milestones on `Option (Config …)`, prove
`milestone_monotone` (via `alive_support_gate` + the protocol's mcrCount monotonicity) and
`progress` (via the floor→rate bridge `phase0_mcrCount_decrease_prob_floor`, valid because
alive⟹gated⟹floor) — together with the Chernoff numbers for `q` and the prefix `Sᶜ`-mass.
This is genuinely probabilistic (the paper's Lemma 5.1 content) but now plugs into a fully
wired interface; no more engine work.  Stage 2 (crCount) reuses `KernelMilestone` verbatim.

### Phase C-7r…C-7s (relay 7) — MASS-DRAIN RECTANGLE + hstep DISCHARGE + three-window chaining + Phase-8 verification

Commits: C-7r `f68ff392` (mass-drain rectangle layer) · C-7s `36403aca`
(`phase7_three_window`).  All in `Phase7Convergence.lean`, single-file EXIT_0, Phase8
importer EXIT_0; every new theorem `#print axioms ⊆ [propext, Classical.choice, Quot.sound]`.

**C-7r — the σ-class-MASS drain rectangle (the carried `hstep` re-derived for `classMassN`).**
The relay-6 gap: the count rectangle (`minorityU_drop_prob_rect7`) proved a *count* drop per
gap-1 cell; the cleaned engine `phase7Convergence''` needs a *mass* drop.  Re-instantiated
the IDENTICAL rectangle geometry with the cell potential swapped count→mass:
- `classMass_stepOrSelf_drop` — config-level σ-class-MASS strict drop (`+1 ≤`) under a gap-1
  eliminator×minority step.  Mirror of `minorityU_stepOrSelf_drop`; lifts the per-pair
  `cancelSplit_classMass_pair_drop` (C-7q) through the `c−{s,t}+{out}` decomposition.
- `classMassN_stepOrSelf_drop` — the ℕ form (`classMass σ ≥ 0` ⇒ the ℤ drop transfers to
  `toNat`).  The per-cell `Φ`-drop `drop_prob_of_rect` consumes.
- `classMassN_drop_prob_rect7` — the rectangle drop-prob floor for `Φ = classMassN σ`:
  `#elim@i·#min@j/(n(n−1)) ≤ K {classMassN drops}`, gap-1 pair `i+1=j`, SAME rect
  `elimGap1(i) ×ˢ minorityAt7(j)` as the count version.
- `classMassN_hdrop_of_floor7` — the `potBelow`-floor level-engine `hdrop` (mirror of
  `minorityU_hdrop_of_floor7`): `K (potBelow (classMassN σ) m)ᶜ ≤ 1 − p` (Markov complement).
  Feeds `OneSidedCancel.level_occ_geometric_on` for the level-`m` geometric decay.
- `classMassN_hstep_of_floor7` — the CRUDE-engine `hstep` at `m = 1`: since
  `(potDone Φ)ᶜ = (potBelow Φ 1)ᶜ`, at `classMassN σ b = 1` the drop event reaches `potDone`,
  so `K (potDone (classMassN σ))ᶜ ≤ 1 − p`.  THIS is exactly the carried `hstep` of
  `phase7Convergence''`.  (At `classMassN σ b ≥ 2` the crude single-step `hstep` is genuinely
  vacuous — one cancel drops mass by `≥ 1` but not to `0`; the honest multi-level drain is the
  level chain via `classMassN_hdrop_of_floor7` + `level_occ_geometric_on`.)

**C-7s — three-window chaining (Lemma 7.5) + the honest COLLAPSE finding.**
`phase7_three_window` chains THREE `phase7Convergence''` instances via `composeW_two_phases`
(twice): from `Pre₁ = Inv7Sum n ∧ classMassN σ ≤ M₀₁`, after `t₁+t₂+t₃` steps the residual
`¬(Inv7Sum n ∧ classMassN σ = 0)` mass is `≤ ε₁+ε₂+ε₃`.  The chain links trivially
(`Post₁ classMassN = 0 ⟹ Pre₂ classMassN ≤ M₀₂`).

**HONEST STRUCTURAL FINDING (not a blocker — a simplification).**  Doty Lemma 7.5 eliminates
minority at the three top levels `−l, −(l+1), −(l+2)` SUCCESSIVELY, which with a per-level
COUNT `minorityAt7 i` would need three DIFFERENT chained potentials.  But relay-6 replaced the
count with the GLOBAL σ-class MASS `classMassN σ`, which bounds ALL levels at once
(`classMassN σ = 0 ⟹ minorityU σ = 0`, every σ-Main contributes mass `≥ 1`).  So the FIRST
window already drains the global mass to `0`, eliminating minority at every level
SIMULTANEOUSLY — the three Lemma-7.5 windows COLLAPSE into one.  `phase7_three_window` is a
faithful but redundant rendering; a single `phase7Convergence''` suffices.  This is the mass
argument's strength: it does the work of all three count windows in one geometric decay.

**Phase-8 verification (the count-vs-mass issue is PHASE-7-SPECIFIC; Phase 8 is fine as-is).**
Verified against `Transition.lean:1313 absorbConsume`: EVERY non-identity branch writes
`bias := .zero` for one agent and `full := true` for the other — it NEVER writes
`bias := .dyadic <sign> <idx>`, so it never CREATES/copies/flips a signed bias.  Contrast
Phase 7's `cancelSplit`, whose gap-2 branch writes `bias := .dyadic ss ⟨i+1⟩` (the sign-copy
that RAISES `minorityU`).  Because `absorbConsume` only REMOVES signed biases (monotone down),
the σ-Main COUNT `minorityU σ` is UNCONDITIONALLY non-increasing
(`absorbConsume_minorityU_pair_le`, axiom-clean), so `phase8Convergence` rides the COUNT
potential `minorityU σ` with `hmono = potNonincrOn_minorityU` (axiom-clean) — NO mass detour
needed.  Phase 8 does NOT have Phase 7's count-vs-mass obstruction.  CONFIRMED fine as-is.

**Net status (relay 7).**  Phase 7: `hClosed`, `hmono`, AND the mass-drain `hstep` (at `m=1`
via the rectangle) all delivered axiom-clean; three-window chaining assembled (and shown
redundant under the global mass).  The single remaining carried Doty input is the floor `p`
itself (`p = #elim·#min/(n(n−1))`, the Lemma 7.4 `≥0.8|M|` majority vs `≤0.2|M|` minority) —
a CARRIED INVARIANT, not derivable from the transition rule.  Phase 8: verified count-based,
no mass needed.

### Phase C-1 (relay 7) — THE CONCRETE WITNESS + STAGE-1 ASSEMBLY (0-sorry, axiom-clean)

Commits: C-1A 6a199a65 · C-1B b914407d · C-1C 8626d5c8 · C-1D f2a89f41 · C-1E 1af92613
· C-1F bda1dd03 · C-1G 49e0ce82 · C-1H 0ae64120.  All in `RoleSplitConcentration.lean`.

**The single relay-6 atom — DELIVERED.**  Relay 6 isolated "construct the concrete
`KernelMilestone (killK_now K G)` role-split witness + the Chernoff numbers."  Relay 7
constructs the witness in full and assembles Stage 1; the genuinely-probabilistic Chernoff
`q`/`Sᶜ`-prefix enters as explicit hypotheses (the honest residual, see below).

**Gate-region + milestone design (chosen).**
- `floorGate n a₀ := {c | card=n ∧ a₀ ≤ assignableCount c ∧ ∀a∈c, role=mcr→phase=0}` — EXACTLY
  the three hypotheses `phase0_mcrCount_decrease_prob_floor` consumes.  On `killK_now K
  floorGate`, alive ⟹ gated by `alive_support_gate`, so the bridge fires unconditionally
  (`inv_closed` dissolved).
- **Milestone granularity = the plain engine's `k = n-1` diagonal `mcrCount` thresholds**
  (`liftMilestone n i := match · | none => True | some c => phase0Milestone n i c`; cemetery =
  milestone-True = Post = absorbing).  The ONLY change vs. `phase0MilestonePhase`: the per-step
  rate is `floorRate n a₀ M = M·a₀/(n(n-1))` (Θ(M/n)) in place of `M(M-1)/(n(n-1))` (Θ(M²/n²)).

**The witness `roleSplitKernelMilestone n a₀ (hn2) (ha1:1≤a₀) (ha_le:a₀≤n-1)`** (C-1D):
`KernelMilestone (killK_now (NonuniformMajority L K).transitionKernel (floorGate n a₀))`.
Fields = the three relay-7 lemmas:
- `milestone_monotone = liftMilestone_monotone` (C-1B): cemetery absorbing; alive→alive is a
  gated real-support point (`alive_support_gate`+`killK_now_some_gated`+`mem_support_of_pos_toMeasure`)
  where the plain `phase0MilestonePhase.milestone_monotone` applies — no rule creates an MCR.
- `progress = liftMilestone_progress` (C-1C): GLOBAL (no Inv).  Cemetery: vacuous.  Ungated `some
  c`: `killK_now = δ none`, whole mass at milestone-True ≥ floorRate (`floorRate ≤ 1`).  Gated
  `some c`: frontier `mcrCount c = n-i.val` (`mcrCount_eq_of_milestone_frontier`) + the
  floor→rate bridge lifted through `gateMap` (`liftMilestone_progress_mass`, C-1A).  THIS is why
  the killed kernel dissolves `inv_closed`: off-gate the bound is FREE (cemetery mass = 1).

**Stage-1 assembly `phase0_stage1_whp`** (C-1G): plugs the witness + `post_sound`
(`Post(some y) ⟹ roleSplitGoodMile = last mcrCount milestone`) + `hPre` (Phase0Initial all-MCR
fires no milestone, `mcrCount=n`) into the relay-6 headline `real_bad_le_janson_add_escape`:
```
(K^t) c₀ {¬ roleSplitGoodMile} ≤ exp(−pMin·meanTime·(λ−1−log λ)) + (t·q + ∑_{τ<t}(K^τ)c₀ Sᶜ)
```
`K = (NonuniformMajority L K).transitionKernel`, real-kernel, from `Phase0Initial`.

**The quantitative payoff `pMin·meanTime = Θ(log n)`** (C-1F/H): `pMin = floorRate@M=2 =
2·a₀/(n(n-1)) = Θ(1/n)` (vs. plain `Θ(1/n²)`).  `roleSplitKernelMilestone_pMin_meanTime`:
`pMin·meanTime = ∑_{i:Fin(n-1)} 2/(n−i.val) = 2·∑_{M=2}^{n} 1/M = 2(H_n−1)` — **the floor `a₀`
CANCELS** (both `a₀` and `n(n-1)` divide out of `floorRate(2)/floorRate(M)`).  This is the
Θ(log n) potential the plain engine (potential Θ(1), `phase0MilestonePhase_pMin_le_two_div`)
provably cannot reach.  All 12 new theorems: per-thm `#print axioms ⊆ {propext,
Classical.choice, Quot.sound}`; single-file EXIT_0.

**εfloor final form (HONEST residual = the genuine Lemma-5.1 Chernoff).**  `phase0_stage1_whp`
leaves `(S, q, hstep)` as hypotheses where `hstep : ∀ x∈floorGate, x∈S → K x floorGateᶜ ≤ q`.
With `S := floorGate` (campaign simplification), `Sᶜ`-prefix `∑_{τ<t}(K^τ)c₀ floorGateᶜ` is
EXACTLY `∑_τ P(floor fails at τ) = ∑_τ P(assignableCount < a₀ at time τ)`.

  WHY `q` IS NOT CLEANLY CLOSABLE (region analysis confirmed).  Gate-escape `K x floorGateᶜ`
  fails only via the floor disjunct (card conserved by every transition; MCR never advances
  phase in Phase 0 — the other two disjuncts cannot break in one step).  But the per-step
  floor-breach from the boundary `assignableCount = a₀` is `Θ(1)`, NOT small: the pool moves by
  ≤2/step and a single pool-decreasing R3/R4 interaction breaches.  A uniform per-step `q` is
  therefore Θ(1) — too weak.  The honest content is the CUMULATIVE in-house MGF drift on
  `exp(−s·assignableCount)`: births (R1, rate ~u²/n²) outpace deaths (R3/R4, rate ~u·pool/n²) in
  the early regime `u ≥ n/2` (R1 alone gives rate ≥1/4), keeping the pool ≥ floor whp; the late
  regime `u<n/2` needs the two-phase split.  This is `GatedGeometricDrift`'s machinery on the
  REAL kernel — a separate development, NOT assemblable from the count/rate atoms (matches the
  relay-5/6 assessment that the floor concentration is irreducibly probabilistic).  Target
  `εfloor(n) ≤ n^{-2}`-shape via the MGF tail.

**Status.**  Stage-1 STRUCTURAL ASSEMBLY COMPLETE 0-sorry axiom-clean (witness + headline +
Θ(log n) potential).  Residual = the floor-failure prefix `∑_τ P(assignableCount<a₀)` bounded
by the in-house real-kernel MGF drift (precise goal above).  Stage 2 (crCount) reuses
`roleSplitKernelMilestone`'s template verbatim with a crCount floor downstream of Stage-1's
assignable→cr output — blocked behind the same floor-drift residual.

### Phase C-1 (relay 8) — THE CRUX RESOLUTION + floor-escape shell decomposition (0-sorry, axiom-clean)

Commit: C-1I `8e78151d` (`RoleSplitConcentration.lean`, +70 lines).

**THE CRUX RESOLVED — which population the paper's `1/5` refers to, and why the Lean
encoding does NOT collapse to a deterministic monotone bound.**  Read of Doty Lemma 5.1
(`ref/Doty-2021-exact-majority.pdf`, lines 2311–2388) settles every fork the relay-7 note
raised:

- The paper's reactions are `U,U→Sf,Mf` (R1), `Sf,U→St,Mf` (R2), `Mf,U→Mt,Sf` (R3), with
  `u=#U`, `s=#Sf+#St`, `m=#Mf+#Mt`.
- The paper's `1/5` is **`(sf+mf)/n`** — `sf+mf` = the count of agents carrying the **`f`
  ("fresh/false-assigned") subscript**, i.e. the agents *created* by R1.  The rate of
  decreasing `u` is R2+R3 = `2(u/n)·(sf+mf)/n ≥ 2(u/n)(1/5)`, because R2's reactant is an
  `Sf` and R3's is an `Mf` — **the responder pool for the decrement is `sf+mf`.**
- **`sf+mf` IS MONOTONE NON-DECREASING in the paper.**  R1: `Δ(sf+mf)=+2`; R2 (`Sf→St`,
  creates `Mf`): `Δ=0`; R3 (`Mf→Mt`, creates `Sf`): `Δ=0`.  The paper states it explicitly
  (line 2332): "this count `sf+mf` can never decrease, so we have `sf+mf>n/5` for all future
  interactions."  So in the PAPER the floor is **deterministic after an `O(n)` warm-up** — the
  monotone collapse the relay-7 note hoped for is REAL, but only for the paper's `sf+mf`.

- **The Lean encoding does NOT inherit this**, because the rate bridge
  (`phase0_mcrCount_decrease_prob_floor`) is keyed to `assignableCount` = unassigned phase-0
  Main/CR (the *targets to convert*, i.e. the paper's `U`-side), NOT to the assigned/fresh
  pool.  Worse, Lean's **Rule 3 marks its `s`-output `assigned:=true`** (`assignable_rule3_s_assigned`),
  draining `assignableCount` by `−1` per fire, whereas the paper's R3 `Mf,U→Mt,Sf` produces a
  **fresh unassigned `Sf`**, conserving the pool.  THIS encoding divergence (recorded at
  `RoleSplitConcentration.lean:661–665`) is exactly why the Lean `assignableCount` is two-sided
  and non-monotone.  **Monotone-collapse route is therefore CLOSED for the current Lean encoding;
  the MGF route is genuine.**

**The drift inequality (derived, for the MGF development).**  With `U=mcrCount`, pool
`P=assignableCount=P_main+P_cr`, the per-step deltas (verified, `RoleSplitConcentration.lean:647`):
R1 `+2` rate `≈U²/n²`, R2 `0`, R3 `−1` rate `≈U·P_cr/n²`.  For `Φ=exp(−s·P)` the one-step drift
factor is `≈ 1 + (1/n²)[U·P_cr·(e^{s}−1) − U²·(1−e^{−2s})]`; supermartingale (`≤1`) needs
`U²·(1−e^{−2s}) ≥ U·P_cr·(e^{s}−1)`, i.e. to first order **`2U ≥ P_cr`.**  Favorable region =
`{U ≥ n/2}` (then `2U ≥ n ≥ P_cr` unconditionally — R1 alone dominates).  **Late regime
`U < P_cr/2` is genuinely UNFAVORABLE** — the pool CAN drain (R3 outpaces R1) — confirming the
relay-7 timing tension is real, NOT an artifact.  Resolution = the **two-segment split** (note's
option a): segment 1 (`U:n→n/2`, `O(n)` steps) establishes `P ≥ 2a₀` whp via the `U≥n/2`
favorable drift; segment 2 maintains `P ≥ a₀` only as long as `U > 0` — but in the Lean encoding
segment 2's floor is NOT maintainable for the full `Θ(n log n)` if `P_cr` stays large.  **The
clean fix is to align Lean Rule 3 with the paper (emit a fresh unassigned `Sf` instead of marking
assigned), restoring `sf+mf`-monotonicity and collapsing segment 2 to a deterministic count
bound `n − U ≥ n/2 ⟹ assignedCount ≥ ...`.**  Recommended next step: re-encode Rule 3 (a
`Phase0Transition` change) rather than build the unfavorable-region MGF — the paper's own proof
relies on the monotone pool, so the faithful formalization should too.

**What C-1I delivers (airtight, closable from count atoms).**  The deterministic scaffolding
that the residual `∑_{τ<t}(K^τ)c₀ floorGateᶜ` reduces onto, regardless of which floor route
closes it:
- `cardPhaseShell n` = the two deterministic predicates of `floorGate` (card + the Phase-0
  MCR-phase invariant), and `floorGate_eq_shell_inter_floor`: `floorGate = cardPhaseShell ∩
  {a₀ ≤ assignableCount}`.
- `floorGate_compl_subset`: `floorGateᶜ ⊆ cardPhaseShellᶜ ∪ {assignableCount < a₀}`.
- `floorGate_escape_mass_le`: the per-step mass split `μ floorGateᶜ ≤ μ cardPhaseShellᶜ +
  μ {assignableCount<a₀}` — summed over `τ`, isolates the genuine MGF target from the
  deterministic shell.
- `card_eq_of_support`: `card` preserved on the kernel support (airtight via
  `stepDistOrSelf_support_card_eq`) — the `card`-disjunct of the shell contributes zero
  support mass.  (The MCR-phase-invariant half needs the per-rule phase analysis — same
  difficulty class as the floor itself; left as documented input.)
All 4 theorems per-thm `#print axioms ⊆ {propext, Classical.choice, Quot.sound}`; single-file EXIT_0.

**Status.**  Crux resolved (monotone-collapse holds for the PAPER's `sf+mf` but the Lean
encoding's Rule-3 drain breaks it; MGF favorable only on `U≥n/2`).  Residual now cleanly split
into (i) the deterministic shell (`card` done, phase-invariant pending) and (ii) the pure floor
prefix `∑_τ P(assignableCount<a₀)`.  **Strong recommendation: re-encode Rule 3 to emit a fresh
unassigned `Sf` (paper-faithful), which restores pool-monotonicity and reduces (ii) to a
deterministic post-warm-up count bound — collapsing the residual without an unfavorable-region
MGF.**  Absent that, (ii) requires the two-segment MGF with the `U≥n/2` favorable drift above
plus an honest segment-2 argument that has no clean form in the current encoding.

### Phase C-1 (relay 9) — POST PROTOCOL-FIX: file repaired, pool ledger exact, floor finding REFINED

Commits: C-1J `4969c22e` (repair) · C-1K `aa08fb7c` (R1 +2) · C-1L `3cc8e4b1` (R2/R3 0) ·
C-1M `caf2e120` (`_final` + doctrine) · C-1N `cd08c4a1` (R4 ledger).  All in
`RoleSplitConcentration.lean`, single-file EXIT_0, every new theorem `#print axioms ⊆
[propext, Classical.choice, Quot.sound]`, 0-sorry, 0 native_decide.

**The protocol fix LANDED but the file did NOT compile** — the repair agent's
`assignable_rule3_conserved` (replacing `_s_assigned`) had a broken `hassigned` step
(`simp` confluence: short simp-arg list took a wrong branch, reduced `⊢ True` to `⊢ False`).
**C-1J fixes it** by mirroring the compiling sibling `Phase0Transition_first_no_mcr_of_mcr_cr`'s
explicit `simp only` arg list (the full role-equality `False` facts + `not_*_eq_*` pair + `hs_un`).
The ground truth IS `assigned = false` (verified by trace: `s2 = s`, `s3 = {s2 with role:=.main}`).

**THE PER-RULE POOL LEDGER IS NOW EXACT IN LEAN** (`assignableCount` = the paper's `sf+mf`):
- R1 `+2`: `assignable_rule1_both_fresh` (two unassigned phase-0 MCR → unassigned Main + CR,
  both `IsAssignable`) = paper `U,U→Sf,Mf`.
- R2/R3 `0`: `assignableCount_pair_mono_of_mcr_assignable` (input pair carries one assignable
  `t`; output `s`-side is again assignable by `assignable_rule2_s_stays`/`_rule3_conserved`) =
  paper `Sf,U→St,Mf` / `Mf,U→Mt,Sf` pool conservation.  Per-pair `≥`.
- R4 `−2`: `assignableCount_pair_rule4_drop` (two assignable RoleCR → Clock+Reserve, both
  non-assignable; input 2, output 0) + `Phase0Transition_rule4_clock_reserve` (the deterministic
  1:1 Clock/Reserve producer for the `|Clock|=|Reserve|` balance).
Helpers: `assignableCount_singleton'`/`_pair'` (countP), `isAssignableBool_iff`,
`not_isAssignable_of_mcr`.

**THE FLOOR FINDING — REFINED, NOT what relay 8 predicted.**  Relay 8 predicted the fix would
make the floor DETERMINISTIC.  IT DOES NOT, and the honest reason is **concurrency, not Rule 3**:
- The paper's `sf+mf` monotonicity holds because Lemma 5.1 analyses ONLY R1/R2/R3; the
  second-level split R4 is analysed SEPARATELY/LATER (temporal separation, "we begin the analysis
  at that point").
- `Phase0Transition` fires R1–R4 **concurrently**; R4 fires on ANY two `RoleCR` (no `assigned`
  guard), so it drains the unassigned-CR half of the pool by `−2` even while `mcrCount>0`.
- Deterministic identity: `assignableCount = 2·#R1 − 2·#(R4 on unassigned CR)`.  An adversarial
  scheduler fires R4 on R1's fresh CRs ⟹ no deterministic invariant maintains `assignableCount ≥
  Θ(n)` while `u>0`.
- The `Θ(log n)` Janson potential NEEDS the floor-driven `Θ(M/n)` rate (which needs the floor);
  the R1-diagonal-only `Θ(M²/n²)` rate needs no floor but gives only `Θ(1)` potential
  (`phase0MilestonePhase_pMin_le_two_div`).  So the floor `εfloor = ∑_τ P(assignableCount<a₀)`
  stays the irreducible Lemma-5.1 Chernoff residual (early phase `u≥2n/3` ⟹ R1 fires w.p. ≥½ ⟹
  pool grows to `Θ(n)` whp), an in-house MGF, NOT assemblable from count atoms.
- NET: the fix HALVED the drain (R3's `−1` gone, first-level pool now exactly monotone), but R4's
  `−2` is the surviving obstruction.  The relay-8 deterministic-collapse hope is structurally
  blocked by the kernel's concurrency.

**`phase0_stage1_whp_final`** (C-1M): the Stage-1 headline at `S := floorGate n a₀`, so the
side-set complement is exactly `floorGateᶜ` and (via `floorGate_escape_mass_le` +
`card_eq_of_support`) the escape prefix `∑_{τ<t}(K^τ)c₀ floorGateᶜ` reduces to the pure floor
event `∑_τ P(assignableCount<a₀)` + the deterministically-null `cardPhaseShell` shell.  The Janson
tail carries `pMin·meanTime = Θ(log n)` (`roleSplitKernelMilestone_pMin_meanTime`).  This is the
final STRUCTURAL form: the ONLY undischarged quantity is `εfloor`.

**Remaining for full Lemma 5.2 (unchanged in nature, now sharply isolated):**
(a) `εfloor`: the in-house MGF/Chernoff `∑_τ P(assignableCount<a₀) ≤ n^{-2}`-shape on the early
    split (genuine probabilistic content; the `card`-shell half of `floorGateᶜ` is null by
    `card_eq_of_support`, the MCR-phase-invariant half is a per-rule phase analysis).
(b) Stage-2 crCount milestone (R4 at `Θ(l²/n²)`) — reuse `roleSplitKernelMilestone`'s diagonal
    template; `Phase0Transition_rule4_clock_reserve` is the producer atom.
(c) full `post_sound : Post ⟹ RoleSplitGood` — needs Stage-2's Clock/Reserve counts +
    the deterministic 1:1 balance (`Phase0Transition_rule4_clock_reserve` ⟹ `|Clock|=|Reserve|`)
    + Main = #R1 (the `n/2±εn` window).  The `RoleSplitGood`-consumer floors
    (`clockCount_linear_of_RoleSplitGood` etc.) already exist.

### Phase C-1 (relay 10) — Stage-2 crCount atoms + deterministic post_sound ledger + assembly

Built gaps (b) and (c) above as the DETERMINISTIC skeleton, with the genuinely-probabilistic
windows isolated as named inputs (NOT faked).  Did NOT touch gap (a) `εfloor` (another line).
Commits: C-1O `3df34cc8`, C-1P `72c8d9c1`, C-1Q `38b5a415`, C-1R `483d9934`, C-1S `8a496b1b`.
All single-file EXIT_0, each per-theorem `#print axioms ⊆ [propext, Classical.choice, Quot.sound]`.

**The deterministic / probabilistic split (the honest finding).**  Lemma 5.2's postcondition
factors cleanly:
- DETERMINISTIC (probability 1, fully proved this relay):
  * `roleCount_conservation` (C-1O): the five role counts partition the population —
    `mainCount + reserveCount + clockCount + roleMCRCount + crCount = card`.  Multiset induction,
    protocol-independent.
  * `Phase0Transition_clock_reserve_balance_pair` (C-1P): EVERY `Phase0Transition` step preserves
    the clock-minus-reserve balance (`#Clock(out)+#Reserve(in) = #Reserve(out)+#Clock(in)`).
    100-case role/assigned tree, `simp [Phase0Transition, addSmallBias]` (clock-preservation under
    the opaque counter machinery falls out).  This is the per-pair atom behind `|Clock|=|Reserve|`.
  * `balanced_conservation` (C-1Q): substituting the balance into conservation gives
    `mainCount + 2·clockCount + crCount + roleMCRCount = n` — the exact identity the windows refine.
- PROBABILISTIC (NOT derivable from the count atoms — the paper's Chernoff on the RANDOM
  R1-vs-(R2/R3) mix): the `±η` Main window and the `≥(1−η)n/4` Clock/Reserve floor.  Exposed as
  the named input `RoleSplitWindows η n c` with its precise shape (C-1Q).  Plus `roleMCRCount = 0`:
  the diagonal milestone family stops at `mcrCount ≤ 1` (`roleMCRCount_le_one_of_roleSplitGoodMile`,
  C-1Q), one short of the paper's `= 0`; the residual single-MCR absorption is a named input.

**Stage-2 composition design (gap b).**  The concurrent kernel blocks a naive `crCount`-milestone
monotonicity (R1/R2 create fresh CR while MCR remain).  The honest composition is the
**Chapman–Kolmogorov checkpoint after Stage-1**: run Stage-2 only in the no-MCR regime.  The
licensing structural fact is deterministic and now proved:
  * `Phase0Transition_crCount_noMCR_le_pair` (C-1R): with NEITHER input agent `RoleMCR`, no rule
    produces a CR (R1 needs both-MCR, R2 needs one-MCR — both blocked; R3 emits Main; R4 drains;
    R5 runs on clocks), so `crCount{out} ≤ crCount{in}`.  This is the Stage-2 milestone monotonicity.
  * `crCount_pair_rule4_drop` (C-1R) / `crCount_config_decrease_of_phase0_cr_pair` (C-1S): two
    phase-0 CRs interacting drop `crCount` by 2 (pair) resp. strictly (config) — the Stage-2 progress
    atom (analogue of `mcrCount_config_decrease_of_phase0_cr_pair`).  Rate is the no-floor
    `Θ(l²/n²)` diagonal (R4 fires on ANY two CRs — no `assignableCount ≥ a₀` floor needed, UNLIKE
    Stage-1), so a Stage-2 `KernelMilestone` instance would use the plain diagonal-rate engine, not
    the floorGate one.

**Assembly (`phase0_roleSplit_whp_assembled`, C-1Q).**  Given (carried invariants `card=n`,
all-MCR-at-phase-0) + `roleSplitGoodMile c` (Stage-1 Post) + `ClockReserveBalanced c` +
`roleMCRCount = 0` (named) + `RoleSplitWindows η n c` (named), concludes
`RoleSplitGood η n c ∧ clockCount = reserveCount ∧ (balanced conservation)`.  The ONLY undischarged
quantities, now sharply pinned:
  (a) `εfloor` MGF (another line);
  (b) the Stage-2 `KernelMilestone` INSTANCE (the atoms above are built; instantiating the engine
      needs a `crCount`-diagonal clone of `roleSplitKernelMilestone` + its monotone/progress fields
      from `Phase0Transition_crCount_noMCR_le_pair` + `crCount_config_decrease_of_phase0_cr_pair`,
      and the Chapman–Kolmogorov compose with Stage-1 at the `mcrCount=0` checkpoint — ~engine-scale,
      not done this relay);
  (c) `roleMCRCount = 0` (residual single-MCR absorption past the `≤1` milestone frontier) and
      `RoleSplitWindows` (the genuinely-random R1-vs-onesided split fraction).
The deterministic skeleton is complete and 0-sorry axiom-clean; (b)/(c) are the precise remaining
work, honestly named.

### Phase C-P1 (relay 11) — THE PHASE-1 AVERAGING CONVERGENCE INSTANCE (new file, 0-sorry, axiom-clean)

`Probability/Phase1Convergence.lean` (new).  This is the Phase-1 *averaging* instance — the
discrete bias-averaging on the real kernel — distinct from the earlier C-1 relays (those built
the Phase-0 RoleSplit precursor that feeds Phase 1's Pre).  Single-file `lake env lean` EXIT_0;
every headline theorem `#print axioms ⊆ [propext, Classical.choice, Quot.sound]`.

**Paper Lemma 5.3, actual technique (quoted, /tmp/doty_paper.txt:2433).**  "Let µ = ⌊g/|M|⌉ …
By [45] we will converge to have all bias ∈ {µ−1,µ,µ+1} in O(log n) time whp … We use Corollary 1
of [45] … If |g| ≤ 0.5|M|, µ = 0, so all bias ∈ {−1,0,+1}.  We will use Lemma 4.6 [one-sided
cancel] …"  So Lemma 5.3 is NOT a self-contained per-step potential argument: the quantitative
{µ−1,µ,µ+1} collapse is imported wholesale from reference [45] (Mocquard et al., discrete
averaging, Corollary 1); the minority-elimination tail reuses Lemma 4.6 = the `OneSidedCancel`
engine.  Phase 1 is counter-timed; Lemma 5.3 is what is TRUE at the timeout.

**The honest per-step potential.**  The rule `Phase1Transition` (Transition.lean:447) averages two
Mains' `smallBias` via `avgFin7 x y = (⌊(x+y)/2⌋, ⌈(x+y)/2⌉)` on the `Fin 7` encoding (v ↦ v−3 ∈
{−3,…,+3}).  The FULL {−1,0,+1} window-collapse is NOT per-step monotone (exhaustively: a −3
averaged with a −1 yields two −2s, raising the "outside {−1,0,+1}" count).  What IS unconditionally
non-increasing under `avgFin7` is the count of Mains pinned at the **saturated extremes** `val=0`
(−3) / `val=6` (+3) — averaging only moves an extreme inward, never creating a new one (checked over
all 49 pairs by `decide`).  This is the honest Phase-1 analogue of Phase 8's `minorityU`.

**Delivered (all 0-sorry, axiom-clean):**
- `avgFin7_preserves_sum`, `avgFin7_spread_le_one` — per-pair averaging arithmetic (gap conserved;
  ⌈⌉−⌊⌋ ≤ 1).
- `extremeVal`/`extremeSt`/`extremeU` — the saturated-extreme predicate + ℕ-potential Φ;
  `avgFin7_extremeVal_pair_le` — the exhaustive per-pair non-creation (`decide`).
- `Transition_eq_avg_of_phase1_main` — per-pair reduction (epidemic=id, dispatch=Phase1Transition,
  both-Main so `clockCounterStep`=id, phase 1≠10 so finishPhase10Entry=id); the clean Phase-1
  analogue of Phase 7/8's `Transition_eq_cancelSplit/absorbConsume`.
- `Transition_extremeU_pair_le_of_both_main` — per-pair Φ non-increase.
- `Phase1AllMain` window; `extremeU_stepOrSelf_le`, `extremeU_le_on_support`,
  `extremeU_kernel_noincr`, `potNonincrOn_extremeU` (the engine `hmono`);
  `Phase1AllMain_stepOrSelf`, `Phase1AllMain_support_closed`, `invClosed_phase1AllMain` (the FULL
  engine `hClosed` — phase/role preserved DEFINITIONALLY by the `{with smallBias:=…}` update, no
  auxiliary invariant unlike Phase 7).
- `phase1Convergence : PhaseConvergenceW (NonuniformMajority L K).transitionKernel` via
  `OneSidedCancel.crude_PhaseConvergenceW` — Pre = `Phase1AllMain n ∧ extremeU ≤ M₀`, Post =
  `Phase1AllMain n ∧ extremeU = 0` (`= NoExtreme`); `phase1Convergence_Post` characterizes Post;
  `potDone_extremeU_eq`.

**Single carried input (the carried `hstep`/`q`-rate).**  The averaging-drain rectangle: an
extreme-holding Main meets an inward-moving partner with prob `≥ extreme·other/(n(n−1))`-shape, so
the per-step failure `≤ q`.  The Phase-8 `minorityU_drop_prob_rect`/`drop_prob_of_rect` analogue
(same `interactionCount`/`totalPairs` pair-counting) — exposed as a hypothesis exactly as Phase
7/8 expose theirs.  This is the [45]/Lemma-4.6 quantitative content.

**Precise remaining gap.**  (i) the averaging-drain rectangle `hstep` derivation (the rate `q`),
mechanical clone of Phase-8's rectangle layer.  (ii) the FULL small-gap Post (all bias ∈ {−1,0,+1},
≤ 0.03|M| biased) is the inner-level [45] variance-decay collapse + Lemma-4.6 tail — out of scope
for the per-step potential engine; `Post = NoExtreme` is the honest fully-closable sub-event.
(iii) the large-gap branch (|g| ≥ 0.025|M| ⇒ Phase-2 stabilization) defers to the Phase-2 instance,
as in the paper.  SHAs: 68dd72e5 (P1a), e44593a8 (P1b/c), 96cf002f (P1d/e).

### Phase C-1 (relay 11) — Stage-2 absorbing gate + escape-zero + diagonal rate + 3-phase C-K composition

Built the Stage-2 half of Lemma 5.2: the absorbing no-MCR gate (escape ≡ 0, NO εfloor), the R4
`crCount`-diagonal probabilistic rate, and the three-phase Chapman–Kolmogorov composition wiring.
All single-file EXIT_0; each new public theorem `#print axioms ⊆ [propext, Classical.choice, Quot.sound]`.
SHAs: C-11a `a7ac2e36`, C-11b `9a1fa99f`, C-11c `58ce1df8`, C-11d `27976f61`, C-11e `67a50d04`, C-11f `2c5d5c06`.

**The escape-zero result (the design centerpiece, fully proved).**  The Stage-2 gate
`noMCRShell n = {card = n ∧ roleMCRCount = 0}` is GENUINELY ABSORBING under the real kernel — and
this is now a theorem, not a hope:
- `Transition_roleMCRCount_noMCR_pair` (C-11a/b): from a no-MCR input pair, NEITHER `Transition`
  output is MCR (via the protocol-wide `Transition_first/second_no_mcr` — ALL phases, no phase
  restriction).  The only MCR-producers are R1/R2, both needing an MCR input.
- `roleMCRCount_config_zero_of_noMCR` → `roleMCRCount_zero_of_stepRel` → `_of_reachable`
  → `noMCRShell_support_preserved` → `noMCRShell_pow_compl_eq_zero` (C-11b/c): the gate is closed
  along `StepRel`/`Reachable`, hence `(K^t) c₀ (noMCRShellᶜ) = 0` via the generic
  `transitionKernel_pow_not_pred_eq_zero_of_stepDistOrSelf_support_preserved`.
- `noMCRShell_killedEscape_eq_zero` (C-11c): plugging `S := noMCRShell`, `q := 0` into
  `kill_now_escape_le_prefix_union` gives `(killK_now K G ^ M)(some c₀){none} = 0`.  **Stage-2 pays
  NO floor MGF** — the εfloor Stage-1 pays for is STRUCTURALLY ABSENT once `mcrCount = 0`.

**The Stage-2 diagonal rate (deliverable #1, fully proved).**  `phase0_crCount_decrease_prob`
(C-11d): on `card = n` with all `RoleCR` at phase 0, the step drops `crCount` with mass
`≥ crCount·(crCount−1)/(n(n−1))` — the pure R4 diagonal, NO floor/cross-term (clone of the MCR×MCR
route: `crF` rectangle, `sum_interactionCount_cr_cr`, `interactionPMF_toMeasure_cr_cr_ge`).

**Stage-1.5 design chosen (the honest last-MCR bridge).**  Stage-1's milestone family stops at
`mcrCount ≤ 1`; the Stage-2 no-MCR monotonicity license genuinely needs `= 0` (at `mcrCount = 1`,
R2 fires — single MCR meets an assignable — and creates a fresh `RoleCR`, +1 `crCount`).  Honest
fix = ONE more floor-driven milestone at threshold `0`: the one-sided MCR→non-MCR conversion at
rate `1·a₀/(n(n−1)) = floorRate n a₀ 1` (the SAME `floorGate` machinery, terminal frontier).
Encoded as a separate `PhaseConvergenceW` phase between Stages 1 and 2 in the composition (NOT a
weaken-the-license shortcut).

**The composition (deliverable, fully proved).**  `phase0_roleSplit_whp_two_stage` (C-11e):
three-phase C-K union via `composeW_n_phases` (m = 3) — `(K^(t₁+t₁·₅+t₂)) c₀ {¬ stage2.Post}
≤ ε₁ + ε₁·₅ + ε₂`, stages chained `Post₁ → Pre₁·₅`, `Post₁·₅ → Pre₂`.  Final Post packaged as
`RoleSplitStage2Good = (roleMCRCount = 0 ∧ crCount ≤ 1)`.  `phase0_roleSplit_whp_assembled_stage2`
(C-11f): consumes `RoleSplitStage2Good`, **DISCHARGING the `roleMCRCount = 0` named input** (it now
comes from the Stage-2 `Post`, not a hypothesis); only `RoleSplitWindows` remains probabilistic.

**The precise remaining gap (honest, the single engine-scale piece).**  The Stage-2 `KernelMilestone`
INSTANCE is NOT built this relay.  Blocker (structural, documented): the progress rate
`phase0_crCount_decrease_prob` requires the interacting `RoleCR` pair at **phase 0**
(`crCount_config_decrease_of_phase0_cr_pair` needs `Transition_roles_eq_phase0_of_both_phase0`).
The absorbing gate `noMCRShell` does NOT carry "all CR phase 0", and that predicate is NOT a
deterministic kernel invariant (a phase-0 CR advances its phase via the epidemic/counter
machinery — `_no_mcr` infra preserves ROLE but not PHASE).  So the Stage-2 milestone needs the
gate to ALSO track a phase-0-CR shell, whose escape is the genuinely-probabilistic
"a CR advanced past phase 0" event (Doty handles this via the Phase-0 TIME WINDOW, beyond the
count-only gate in this file).  Concretely, to close: define `crPhase0Shell` lift lemmas
(`liftMilestone_progress`/`_monotone` clones at `noMCRShell ∩ crPhase0Shell`, rate
`phase0_crCount_decrease_prob`), give the `KernelMilestone (killK_now K (noMCRShell ∩ crPhase0Shell))`
witness, and supply the three `PhaseConvergenceW` ε-tails to `phase0_roleSplit_whp_two_stage`.  The
escape-zero result above covers the `roleMCRCount` HALF of that gate for free; only the phase-window
half remains.  EVERYTHING built this relay is 0-sorry axiom-clean and load-bearing for that instance.

## Phase C-0w9..11 record — Phase-0 TIMING half (2026-06-10)

Relay on `Probability/Phase0Window.lean` (the timing half of the Phase-0 analysis
/ the "phase-window half" the Stage-2 milestone above still needs).  Two
documented inputs were targeted; all results 0-sorry, axiom-clean
(⊆ propext/Classical.choice/Quot.sound), single-file compiled.

**GAP 2 — deterministic phase-0-exit bridge — FULLY DISCHARGED (C-0w9, 6d.. a0f591b2).**
- `Phase0Transition_{left,right}_phase_pos_imp_src_clock_zero`: a per-pair phase-0
  exit forces a SOURCE clock at `counter = 0` (traced through the Rule-1..5
  cascade: only Rule 5 `stdCounterSubroutine` advances phase, only at `counter=0`;
  Rule 4 fresh clocks have full counter ≠ 0; Rules 1–3 leave counter / don't make
  clocks).
- `Transition_phase_eq_phase0_of_both_phase0`: the full dispatcher = `Phase0Transition`
  on phase at phase 0 (via `phaseEpidemicUpdate_eq_self_of_both_phase0` +
  `finishPhase10Entry_phase_val`).
- `det_phase0_exit` (config-level) + `transitionKernel_not_allPhase0_eq_zero_of_noClockAtZero`
  (kernel "= 0" form): from `allPhase0 ∧ noClockAtZero`, `allPhase0` is preserved
  one step w.p. 1.
- `prefix_union_first_exit` (abstract first-exit / hitting-time prefix-union),
  `allPhase0_window_le_prefix_sum`, `allPhase0_window_whp` (the
  `t · ofReal(e^{−45(L+1)})` window bound given per-τ clock-zero bounds from
  `phase0_window_whp`).

**GAP 1 — quantitative scheduler drift — INFRASTRUCTURE BUILT (C-0w10/11, 7d29.. / 6d0e26..).**
- `lintegral_transitionKernel_eq_sum`: `∫ Φ dK(c) = ∑_pair Φ(stepOrSelf c pair)·interactionProb(pair)`.
- `clockCounterPotential_{eq_base_add_pair, stepOrSelf_eq_base_add_pair}`: localized
  per-pair potential split over the common base `Φ(c − {r₁,r₂})` (no truncated sub).
- `clockSummand_pair_clock_clock`: the dominant per-pair case — a clock–clock
  phase-0 pair at positive counters scales its block by EXACTLY `eˢ`.
- RESIDUAL (documented in-file): non-clock–clock per-pair contributions
  (counters untouched + Rule-4 fresh `e^{−s·50(L+1)}` term) + the pair-count
  `2(clockCount−1)/(n(n−1)) ≤ 2/n` summed to the affine rate `1 + 2(eˢ−1)/n`.

## Cleanup queue (post-D-3, 2026-06-10 evening)
- [ ] Budget tightening: re-instantiate doty_time_headline_W's displayed budget at the paper's
  1 − O(1/n²) (the per-phase engines already deliver n^{-2}-shape; the composition is parametric —
  feed δ_i ≤ 1/(11n²) and re-run the arithmetic; Xiang flagged 1/n as weaker than the paper).
- [ ] The ten chain bridges (F-1, in flight).
- [~] Phase-0 window closing bricks (Gap-2 DONE C-0w9; Gap-1 ledger infra DONE C-0w10/11;
  Gap-1 residual = non-clock-clock per-pair + pair-count·prob → affine rate).
- [ ] Per-phase drain numerics (q/hstep for 0/1/5/6/7/8) at concrete parameters.
- [ ] hside τ-uniform majorant + post-hour width mode.
- [ ] εfloor MGF (family2 letter queued; the Phase0Window drift-ledger pattern is the template).
- [ ] Phase 5 hConc wiring through the Lemma-5.2 timing window.
- [ ] E4 assembly (needs the headline + Lemma 5.2 floors) → expected-time half of Theorem 3.1.
- [ ] Phase F: repo audit refresh + uisai2 explicit-target full build + 推平 main + tag.

## Phase D-4 — seam-corrected composition (2026-06-10 evening)

**The fix.** `ChainBridges` (F-1) PROVED the ten work↔work `h_chain` bridges are not pointwise
implications (every window pins agents to a distinct `phase.val`, so `Post_i ∧ Pre_{i+1}` is
contradictory on populated configs).  The paper's inter-phase transition is the `advancePhase`
EPIDEMIC.  D-4 interposes a SEAM phase between each work pair, turning the chain into the
21-instance interleave `[work₀, seam₀, …, seam₉, work₁₀]` on which the bridges ARE genuine
pointwise implications.

**Commits (all pushed to origin main):**
- `4d9522a9` D-4a: `SeamEpidemics.seamEpidemicW` — the generic phase-advance epidemic seam.
- `46d6ed0f` D-4b: `DotyTimeHeadline.doty_time_headline_W2` — the seam-corrected 21-instance
  composition headline (`+ doty_time_composition_W2` assembly contract).
- `16fa5a09` D-4c: the per-seam work↔seam bridge lemmas.
All 0-sorry, axiom ⊆ `[propext, Classical.choice, Quot.sound]`, single-file `lake env lean`.

**The seam instance signature.**
```
seamEpidemicW (p n tseam : ℕ) (εepidemic εovershoot : ℝ≥0)
  (hDrift : ∀ c, (allPhaseGe p n c ∧ advTriggered (p+1) c) →
      (K^tseam) c {c' | ¬ allPhaseGe (p+1) n c'} ≤ εepidemic)
  : PhaseConvergenceW (NonuniformMajority L K).transitionKernel
  -- Pre  c := allPhaseGe p n c ∧ advTriggered (p+1) c   (≥-window + trigger fired)
  -- Post c := allPhaseGe (p+1) n c                        (≥-window, next-phase entry)
  -- t := tseam,  ε := εepidemic + εovershoot
```
`allPhaseGe p n c := c.card = n ∧ ∀ a ∈ c, p ≤ a.phase.val`;
`advTriggered p c := 1 ≤ countP (p ≤ ·.phase.val) c`.
The Phase-4 instance `Phase4Convergence.phase4Convergence` IS this epidemic at `p = 4`
(`advancedU` = `countP (·.phase=4)`, rate `m(n−m)/(n(n−1))`), drift rate form
`(1 − ((n−1)/(n(n−1)))(1−e^{−s}))^t · e^{s(n−1)}`.

**≥/exact-window audit (the eleven work `Pre`s).**

| i  | work `Pre` window           | shape       | needs `hNoOvershoot`? |
|----|-----------------------------|-------------|-----------------------|
| 1  | `Phase1AllMain`             | `phase = 1` exact | yes |
| 2  | `Q2 / Qwin`                 | `phase = 2` exact | yes |
| 3  | `{c = c₀}` (clock entry)    | start config (not a phase window) | n/a (clock seam) |
| 4  | `Q4 = allPhaseGe 4`         | `phase ≥ 4` **≥-window** | NO (≥ directly) |
| 5  | `Phase5AllWin`              | `phase = 5` exact | yes |
| 6  | `Phase6Win`                 | `phase = 6` exact | yes |
| 7  | `Inv7Sum` (`Phase7AllMain`) | `phase = 7` exact | yes |
| 8  | `Phase8AllMain`             | `phase = 8` exact | yes |
| 9  | `Q2 / Qwin` (2nd union)     | `phase = 2` exact | yes |
| 10 | `Phase10Post`               | `phase = 10` exact | yes |

Finding: ten of eleven work `Pre`s pin EXACT phase; only Phase 4 (`Q4`) is a ≥-window.  Hence
every seam EXCEPT the one feeding Phase 4 needs the `≥`→`=` reconciliation
`allPhaseEq_of_ge_and_no_overshoot` under a named overshoot input.

**The two named gaps (exact shapes, NOT discharged in D-4):**
1. `hDrift (p)` — the generic-`p` advance-epidemic convergence bound (seam field):
   `∀ c, (allPhaseGe p n c ∧ advTriggered (p+1) c) → (K^tseam) c {c' | ¬ allPhaseGe (p+1) n c'} ≤ εepidemic`.
   Discharge = clone `phase4AdvancedDrift`/OneSidedCancel at abstract `p` (count =
   `countP (·.phase ≥ p+1)`, spread by `Invariants.Transition_{left,right}_phase_ge_pair_max`).
2. `hNoOvershoot (p)` — per-seam timing separation (bridge `seam_into_exact_work` input):
   `∀ c, allPhaseGe (p+1) n c → ∀ a ∈ c, a.phase.val < p+2`
   i.e. `(K^tseam)`-measure of `{some agent ≥ p+2}` from the seam `Pre` ≤ `εovershoot(p)`.
   Bounded by the Phase0Window counter machinery (a counter can't finish too early) — folded
   additively into the seam's `εovershoot` budget.

**Per-work-phase trigger note.** An exact-pin work `Post` (`all phase = p`) does NOT fire
`advTriggered (p+1)` by itself; the work `Post` must be strengthened with the advance trigger
(`exact_work_into_seam` makes this explicit as a named input).  Phase 4's `Q4` ≥-window feeds
`ge_work_into_seam` with the trigger added the same way.

**Corrected headline status.** `doty_time_headline_W2` : from `(phases 0).Pre c₀`, within
`T = ∑ (11 work + 10 seam) t ≤ 21·C0·n·(L+1) = O(n log n)` interactions, the run reaches
`majorityStableEndpoint init` with failure `≤ 1/n` (`∑ 21 δ ≤ 1/n`).  Asymptotics unchanged
from `_W` (`11→21` constant only).  UNCONDITIONAL beyond: the 11 work instances (with per-work
trigger strengthening), the 10 seam instances (each with `hDrift` + `εovershoot`/`hNoOvershoot`),
the 21-term `h_chain` (TRUE pointwise via the D-4c bridges), `hx₀`, `h_post`, scaling.

## Phase D-4d — `hDrift(p)` DISCHARGED (2026-06-10, the first named D-4 gap closed)

The generic-`p` advance-epidemic drift (`hDrift`, named-gap #1) is now PROVEN, not carried.
Cloned the entire `Phase4Convergence` non-tie engine at an abstract phase parameter `p` in
`Probability/SeamEpidemics.lean` (append-only; touches only this file + an append-only doc note
in `DotyTimeHeadline.lean`).  All theorems 0-sorry, 0-native_decide, `#print axioms ⊆ [propext,
Classical.choice, Quot.sound]` (verified per-theorem). Single-file `lake env lean` EXIT_0.

**Generalisation map** (Phase 4 `p=4` → abstract `p`): `advancedP a = 5 ≤ phase` → `geP q a =
q ≤ phase` (informed at threshold `q := p+1`); `advancedU` → `geCount q = countP (geP q)`; the
window `Q4 = allPhaseGe 4 n` → `allPhaseGe p n` (the seam Pre window); `susceptibleP (phase=4)`
→ `susP p (phase=p)`; "finished" `advFinished (advancedU≥n)` → `geFinished (geCount(p+1)≥n)`.

**Delivered** (in `SeamEpidemics`, namespace `ExactMajority.SeamEpidemics`):
- Per-pair: `countP_geP_pair`, `geP_pair_mono` (phase-monotone), `geP_pair_advances` (a mixed
  informed×in-window pair → both outputs informed via the public
  `Transition_{left,right}_phase_ge_pair_max`); kernel lift `geCount_stepOrSelf_ge`,
  `geCount_ge_monotone`, `geCount_stepOrSelf_advance`.
- Rectangle prob: `advance_prob_of_rect` (generic `N/(n(n−1))` floor) +
  `sum_interactionCount_cross_disjoint_seam`, `sum_count_geP`, `sum_count_susP`, `susP_count_eq`
  (`#susP = n − geCount(p+1)` on the window), `sum_interactionCount_syncRect_seam`
  (rectangle mass `= m·(n−m)`), `ge_advance_prob` (SYNC advance prob `≥ m(n−m)/(n(n−1))`).
- Window closure: `allPhaseGe_stepOrSelf`, `allPhaseGe_absorbing`; the count↔set bridge
  `allPhaseGe_succ_iff_geFinished` (on card-`n`, `allPhaseGe(p+1) n ↔ geCount(p+1)≥n`).
- Potential + drift: `gDeficitPot` (exp-window), `gDeficitPot_{measurable,eq_of_lt,pointwise_bound}`,
  `not_finished_imp_gDeficitPot_ge_one`, `geFinished_absorbing`, `advance_floor_seam`, and the
  capstone `phaseAdvanceDrift` — the GENUINE one-step contraction at rate
  `r = 1 − ((n−1)/(n(n−1)))·(1 − e^{−s})` (verbatim clone of `phase4AdvancedDrift`).
- Tail + discharge: `gDeficitPot_le_pre`, `Qwin`/`Qwin_absorbing`, `gPotW` (window-guarded),
  `seamGeConvergence` (the `windowDrift_PhaseConvergence` wrap, `Post = geFinished`),
  `advTriggered_iff_geCount`, and **`seam_drift`** — the bare kernel-power tail
  `(K^t) c {¬ allPhaseGe (p+1) n} ≤ ε` from `Pre = allPhaseGe p n ∧ advTriggered (p+1)` under the
  explicit Phase-4-shape tail input `hε`.  This IS the `hDrift` field's exact type.
- Packaged: **`seamEpidemicW_calibrated`** = `seamEpidemicW` with the `hDrift` slot fed by
  `seam_drift` — NO undischarged drift; only input is `hε`.  `@[simp]` projections
  `seamEpidemicW_calibrated_{Pre,Post,t,eps}`.

**The calibrated tail's explicit form** (= the `hε` input, mirrors Phase 4 exactly):
`ENNReal.ofReal (1 − ((n−1)/(n(n−1)))·(1 − e^{−s}))^t · ENNReal.ofReal (exp(s·(n−1))) / 1
   ≤ (εepidemic : ℝ≥0∞)`.

**`DotyTimeHeadline` consumption** (append-only doc note; signature unchanged — the headline was
already polymorphic over `phases`): the 10 seam slots are now filled by `seamEpidemicW_calibrated`
instead of `seamEpidemicW`-with-raw-`hDrift`; `hDrift` LEAVES the surviving-input list of
`doty_time_headline_W2`.  Remaining seam-side named input = `hNoOvershoot` only (named-gap #2,
folded into `εovershoot`).

**Commits (all pushed to origin main):**
- `91963f24` D-4d1: per-pair mono/advance + rectangle prob + sync advance prob.
- `d241f818` D-4d2: window closure + `geFinished↔allPhaseGe(p+1)` bridge + deficit potential +
  genuine `phaseAdvanceDrift`.
- `4245f79a` D-4d3: `seamGeConvergence` + `seam_drift` (bare tail) + `seamEpidemicW_calibrated`.
- `28253ede` D-4d: `DotyTimeHeadline` consumption-form note.

---

## Phase D-5 — cross-hour side assembly + the rate fix (`Probability/CrossHourSide.lean`, NEW)

Implements the audited `HANDOFF_hside_blueprint.md` in a NEW file
`Probability/CrossHourSide.lean` (namespace `ExactMajority.EarlyDripMarked`).  All five deliverables
0-sorry, axiom-clean (`#print axioms ⊆ [propext, Classical.choice, Quot.sound]`), single-file
`lake env lean` compile against the existing olean closure.

### Deliverables (commits, all pushed to origin main)

- `3b6f2c73` D-5a: **`checkpoint_side_le`** — generic Chapman–Kolmogorov checkpoint side bound.
  `(κ^{t+r}) x₀ Bad ≤ εEntry + εTail` from `(κ^t) x₀ Entryᶜ ≤ εEntry` + `∀ y ∈ Entry, (κ^r) y Bad ≤
  εTail`.  Same mechanism as `ClockWeakAssembly.leg_escape_global`.
- `097895bf` D-5b: **`Mwidth`/`Mhour`** + **`width_horizon_covers_hour`** + **`no_post_hour_of_stride`**.
  The stride `hstride : tseed + tbulk ≤ DotyParams.w n` makes the post-hour mode EMPTY:
  `Mhour = K·(tseed+tbulk) ≤ K·w ≤ w·(K(L+1)+1) = Mwidth`.  PARAMETER-DESIGN FACT: the per-minute
  budget fits inside the per-window width budget.
- `660ddc96` D-5c: **`sideB_cross_hour`** — the bounded-horizon global-τ side family over `(L+1)`
  hours, `τ = h·Mhour + r`, via `checkpoint_side_le`.  Conclusion `∀ T τ, τ < (L+1)·Mhour →
  (realκ^τ) c₀ Sgood(T)ᶜ ≤ εEntry + εLocal`.  (Bounded-horizon, per the blueprint's correction — NOT
  the unbounded `∀ τ`, which is false at paper rate.)
- `9d87e6dc` D-5d: **THE RATE FIX.**  **`rem_eq_zero`** — the `r = 0` remainder block is EXACTLY `0`
  from a `recInv` start (identity kernel, indicator-of-notMem).  This kills the coarse `δRem := 1`
  (`WidthPrefixConcrete`'s `+1` per `Tcap`-term) at every CHECKPOINT horizon `τ = w·j`.
  **`εWAt_chk`** + **`windowedFrontProfile_whp_chk_concrete`** + **`widthFail_chk_concrete`** +
  **`sidePrefix_chk_concrete_width`** assemble the `δRem`-free per-checkpoint `Sgood(T)ᶜ` budget
  (prefix-WFP block `∑_T (j·deltaB + 0 + escape + taint)` — NO `+1`).
- `16f3247f` D-5e: **`hside_concrete_bounded`** — the assembled bounded-horizon side family,
  `εLocal := sideEps εQ εfloor εWu εP εB εge3 εno3 εcpos εsucc`, width feeder `εWu` parametric.

### The rate-fix outcome (HONEST)

The `+1` enters `windowedFrontProfile_whp_prefix`'s `hRem : (markedK^r) mc₀ {¬recInv} ≤ δRem` at the
partial-window horizon `r < w`.  I verified BOTH small-`r` `δRem` routes are structurally blocked
against the present API:

1. **Per-step union** `δRem ≤ r·(one-step recInv-breach rate)`: the one-step rate is the drip/taint
   rate `O((θn/n)²)` (`EarlyDripMarked.tainted_rise_prob_le`); `× r ≤ w = 3n/200` gives `Θ(n^{1/5})`
   — NOT small.  (Confirms the blueprint's own arithmetic check.)
2. **Two-config checkpoint glue** (width-at-τ ≤ width-at-checkpoint + climb-over-r, widened margin
   W₃): the only deterministic width glue
   `ClockFrontProfile.goodFrontWidth_of_windowed_profile_and_climb` is SINGLE-config — it needs
   `WindowedFrontProfile θ c'` AND `ClimbBound θ W c'` BOTH at the `r`-step successor `c'`.  Quoting
   the checkpoint `WindowedFrontProfile` at `c` does NOT feed the glue at `c'`.  Transporting
   `WindowedFrontProfile` from `c` to `c'` is a genuinely new probabilistic lemma (the front is NOT
   deterministically monotone over a window — drips move it up), ABSENT from the codebase.

So a fully-closed `δRem`-free FREE-`τ` `εWAt` is NOT assemblable from the present API.  What IS
`δRem`-free and assemblable is the CHECKPOINT feeder (`r = 0`): `εWAt_chk` has NO `+1`.  This is the
genuine rate fix on the checkpoint sub-horizon.

### The final εside shape

```
εside = sideEps εQ εfloor εWu εP εB εge3 εno3 εcpos εsucc
      = εQ + εfloor + (εWu + εP + εB) + (εge3 + εno3 + εcpos + εsucc)
```
with the §6 width feeder `εWu` discharged by EITHER:
* `εWAt_chk` (rate-fixed, `δRem`-free) at checkpoints `r = 0` — via `sidePrefix_chk_concrete_width`;
* `εWAt` (free-`τ`, `r < Mwidth`, carries the `+1`) — via `WidthPrefixConcrete.sidePrefix_concrete_width`.

The global form is `εEntry + εside` over `τ < (L+1)·Mhour` (`hside_concrete_bounded`).

### Precise remaining gaps

1. **The within-window WFP transport** (the blocking lemma for a free-`τ` `δRem`-free rate).  Needed
   shape: a kernel-level bound coupling `(realκ^{w·j})` to `(realκ^{w·j+r})` so the checkpoint
   `WindowedFrontProfile` (no `+1`) plus the FREE-`τ` climb budget (`climbBound_whp`, already free-`t`)
   give `GoodFrontWidth (W₁+W₂+W₃)` at `w·j+r` with a SMALL widened margin `W₃`.  This is genuinely
   new probabilistic content (the `n^{-1.6}`-rate "no climb in a window" argument, applied to the
   front's worst-case intra-window excursion).  Until it exists, the free-`τ` consumer keeps the `+1`.

2. **The bounded-horizon consumer wiring.**  `ClockBudgets.clock_unconditional_concrete` takes the
   UNBOUNDED `hside : ∀ T τ`.  But `minutes_sum_le`/`window_sum_le` only sum `τ` over the minute
   windows, whose union is exactly `Ico 0 ((L+1)·Mhour)` (max τ = `(K(L+1))·(tseed+tbulk) =
   (L+1)·Mhour`).  So `hside_concrete_bounded`'s bounded conclusion EXACTLY covers the consumer's
   sum — but plugging it in requires refactoring `clock_unconditional_concrete`'s hypothesis to the
   bounded `Ico` form (a tiny edit of `window_sum_le`/`minutes_sum_le`, both in `ClockBudgets.lean`,
   owned by a running agent — import-only for D-5).  No new math; a hypothesis-restriction refactor.

3. **The eight named feeders** `εQ εfloor εP εB εge3 εno3 εcpos εsucc` inside `εside` remain the
   genuine §-engine residuals carried from B-12 (unchanged by D-5).

---

## Phase D-6 — the per-phase drain calibration (DrainCalibration.lean)

Landed 2026-06-10 (commits 0d5d29e5, 74c61b61, 6a321f04, eadfe181 on `main`).
New file `Probability/DrainCalibration.lean`. 0-sorry, axiom-clean
(`[propext, Classical.choice, Quot.sound]` per theorem), single-file `lake env lean`
compiled; oleans staged into `.lake/build/lib/lean/`.

### What this delivers

Every phase drain instance is built on `OneSidedCancel.crude_PhaseConvergenceW` (form b,
single uniform rate `q : ℝ≥0∞`) or `OneSidedCancel.levels_PhaseConvergenceW` (form a,
per-level rate family `q : ℕ → ℝ≥0∞`).  Both carry the failure-budget hypothesis `hε`:

* form (b): `hε : (q ^ t : ℝ≥0∞) ≤ (ε : ℝ≥0∞)`;
* form (a): `hε : (∑ m ∈ Finset.Icc 1 M₀, (q m) ^ (tWin m) : ℝ≥0∞) ≤ (ε : ℝ≥0∞)`.

D-6 CALIBRATES `hε` (and only `hε`) at concrete constants.  The per-step drain bound
`hstep`/`hdrop` and the α-floor it encodes are NOT discharged — they stay carried as
upstream named inputs (provenance table below).

### Generic atoms

| theorem | statement (shape) |
|---|---|
| `rect_pow_le_budget` | `0≤q≤1−α·m/n`, `1≤M₀≤n`, `0<α≤1`, `T≥(3/α)(n/m)log n` ⊢ `q^T ≤ 1/(M₀ n²)` (ℝ). Route: `q≤1−u≤exp(−u)` (`Real.add_one_le_exp`), `q^T≤exp(−uT)` (`pow_le_pow_left₀`,`Real.exp_nat_mul`), `uT≥3log n`, `exp(−3log n)=1/n³` (`Real.exp_log`), `1/n³≤1/(M₀n²)`. |
| `budgetNN`,`coe_budgetNN`,`budgetNN_le_inv_sq` | `ε := (1/(M₀n²)).toNNReal`; cast to `ofReal(1/(M₀n²))`; `≤ ofReal(1/n²)` when `1≤M₀`. |
| `rect_pow_le_budget_enn` | ENNReal bridge: `(ofReal q_r)^T ≤ (budgetNN M₀ n : ℝ≥0∞)` — the form-(b) `hε` shape. |
| `rect_sum_le_phase_budget` | each `(q m)^(tWin m) ≤ budgetNN M₀ n` ⊢ `∑_{Icc 1 M₀} ≤ ofReal(1/n²)` (`Finset.sum_le_card_nsmul`, `card_Icc=M₀`, `M₀·1/(M₀n²)=1/n²`) — the form-(a) `hε` shape. |

### Calibrated instances inventory

All produce `PhaseConvergenceW (NonuniformMajority L K).transitionKernel` with the carried
drain floor as a hypothesis and the budget `hε` discharged; final ε is `budgetNN M₀ n ≤ 1/n²`
(Phase 5 adds the separate carried concentration `εConc`).

| corollary | engine call | potential / window | α floor | horizon t |
|---|---|---|---|---|
| `phase1Convergence_calibrated` | `Phase1Convergence.phase1Convergence` (form b) | `extremeU` / `Phase1AllMain` | `1/3` | `≥(3/α)·n·log n` |
| `phase5Convergence_calibrated` | `Phase5Convergence.phase5Convergence` (form b + εConc/hConc) | `unsampledReserveU` / `Phase5AllWin` | `23/75` | `≥(3/α)·n·log n` |
| `phase6Convergence_calibrated` | `Phase6Convergence.phase6Convergence'` (form a, level) | `highMass l` / `Phase6Win` | `ρ₆` (per level) | per-level `tWin m`, summed |
| `phase7Convergence_calibrated` | `Phase7Convergence.phase7Convergence''` (form b) | `classMassN σ` / `Inv7Sum` | `4/15` | `≥(3/α)·n·log n` |
| `phase8Convergence_calibrated` | `Phase8Convergence.phase8Convergence` (form b) | `minorityU σ` / `Phase8AllMain` | `1/5` | `≥(3/α)·n·log n` |

The corollaries are RATE-GENERIC: the caller supplies a concrete `q_r ≤ 1 − α·(1/n)` (the
slowest level `m=1` rate) together with the carried `hstep`; the budget is discharged.

### The floors' provenance table (what remains named)

The α floor is the honest per-step drain fraction.  It enters ONLY through the carried
`hstep`/`hdrop`; D-6 does not derive it.  Provenance (the upstream Pre fact that supplies it):

| phase | floor | numeric α | provenance (carried, NOT discharged in D-6) |
|---|---|---|---|
| 1 | main-pair rectangle `mainCount ≥ n/3` | `1/3` | `RoleSplitWindows` / Lemma 5.2 main-count concentration |
| 5 | biased-main `≥ 0.92·mainCount ≥ 23n/75` | `23/75` | Theorem 6.2 biased structure (`biasedMainClassU`) |
| 6 | band-top reserve rectangle `reserveClassCount ≥ ρ₆·n` | `ρ₆` | `ReserveSampleGood K₀` (Phase-5 `sampledReserveClassU`) |
| 7 | elimGap1 `≥ 0.8·mainCount ≥ 4n/15` | `4/15` | Lemma 7.4 `0.8|M|` elimination gap |
| 8 | non-full-majority `≥ (0.8−0.2)|M| ≥ n/5` | `1/5` | Lemma 7.4 `0.8|M|` minus Lemma 7.6 `0.2|M|` minority |

### Calibrated vs carried

* **Calibrated (discharged in D-6):** the failure budget `hε` of all five phases — turned
  from "a drain rate `q` + horizon `t`" into "failure `≤ 1/n²`" (form b) / "level-sum `≤ 1/n²`"
  (form a, Phase 6).
* **Carried (still named upstream):** (i) the per-step drain floor `hstep`/`hdrop` for every
  phase (the eliminator/reserve rectangle — the α floors above, the documented remaining
  drain-rectangle atoms); (ii) Phase 5's sampling concentration `εConc`/`hConc`
  (`ReserveSampleGood`, a separate atom, not a drain budget); (iii) Phase 5/6/7's structural
  closure `hClosed` where the working window is not the FULL engine `InvClosed`
  (Phase 8's `invClosed_phase8AllMain` and Phase 7''s `invClosed_Inv7Sum` ARE proved upstream
  and need no carry).

### Precise remaining gaps (for the drain layer)

1. **The drain-rectangle `hstep`/`hdrop` derivations** — converting each provenance floor
   (RoleSplit n/3, Thm 6.2 biased, ReserveSampleGood ρ₆, Lemma 7.4/7.6) into the concrete
   `q_r ≤ 1 − α·m/n` bound.  The rectangle probability lemmas EXIST per phase
   (`minorityU_drop_prob_rect`, `unsampledReserveU_drop_prob_rect5`, `highMass_drop_prob_rect6`,
   `classMassN_drop_prob_rect7`, plus the `_hdrop_of_floor` packagers); what remains is feeding
   the named upstream floor (the count lower bound `#elim ≥ α·n`-shape) into them.  This is the
   documented remaining drain atom, unchanged by D-6.
2. **The horizon-as-`⌈·⌉` discharge** — the corollaries take `hT : (3/α)(n/m)log n ≤ t` with `t`
   an explicit ℕ; instantiating `t = ⌈(3/α)·(n/m)·log n⌉` and discharging `hT` via
   `Nat.le_ceil` is a one-liner at the call site (no new content).

## Phase D-7 — the hstep/hdrop threading (DrainThreading.lean)

Landed 2026-06-10 (SHAs 3d797801 / 533e78f9 / 2ecaa74c / caa58be6 / 7a89c6ae on `main`).
NEW file `Probability/DrainThreading.lean` (append-only, imports `DrainCalibration` ⟹ all 5
phases).  0-sorry, axiom-clean (`#print axioms ⊆ [propext, Classical.choice, Quot.sound]` on
every headline, verified by temp-append), single-file `lake env lean` EXIT_0; olean staged.
**D-7 closes gap (1) above**: it FEEDS each phase's carried structural count floor through the
phase's drop-probability rectangle to DERIVE the concrete `hstep`/`hdrop` (no longer abstract).

### Generic atom
`ofReal_div_le_of_num_le` : `a ≤ b`, `0 ≤ a`, `0 ≤ d` ⟹ `ofReal(a/d) ≤ ofReal(b/d)` (the only
new analytic content; `d = 0` by `simp`, `d > 0` by `gcongr`).  Everything else is honest
`Finset.sum`-monotone count bookkeeping + the existing rectangle/packager lemmas re-applied.

### STRUCTURAL FINDING (recorded for the headline assembly): crude `hstep` is vacuous for Φ ≥ 2
`crude_PhaseConvergenceW`'s `hstep : ∀ b, Inv b → 1 ≤ Φ b → K b (potDone Φ)ᶜ ≤ q` requires
bounding `{Φ ≥ 1}` mass from EVERY not-done state.  A single drain drops `Φ` by `≥ 1` but NOT
to `0`, so from `Φ b ≥ 2` the kernel keeps ALL mass in `{Φ ≥ 1}` ⟹ `K b (potDone Φ)ᶜ = 1` ⟹
the crude `hstep` forces `q = 1` (vacuous) unless `Φ b = 1`.  **Consequence:** the honest
multi-level drain is the LEVELS engine (`levels_PhaseConvergenceW`, form a), whose per-level
`hdrop : K b (potBelow Φ m)ᶜ ≤ q m` the rectangle discharges at EVERY level.  D-7 therefore
delivers the per-level `hdrop` as the PRINCIPAL output for all five phases, plus the crude
`hstep` only at `m = 1` (where the drop reaches `potDone`).  Phases 1/5/7/8 currently call the
crude engine in their `*_calibrated` instances; the headline assembly should either run them at
`M₀ = 1` (honest with the crude `hstep`) or re-target them onto the levels engine (Phase 6 is
already levels).  This is a genuine engine-shape choice for the assembler, not a defect.

### Per-phase threading outcome (derived-from-floor vs the ONE named structural hypothesis)

For each phase the threading is: `*_drop_prob_rect*` (gives `ofReal((#tgt·#partner)/(n(n−1)))
≤ drop-mass`) ∘ structural floor (`#partner ≥ E/P/R` carried, `#tgt ≥ 1` at the level) ∘
`ofReal_div_le_of_num_le` ⟹ concrete `ofReal(margin/(n(n−1)))` floor ∘ `*_hdrop_of_floor*`.

| phase | Φ / window | rect lemma | ONE named structural hyp (provenance) | delivered |
|---|---|---|---|---|
| 8 | `minorityU σ` / `Phase8AllMain` | `minorityU_drop_prob_rect` | `elimAbove σ i ≥ E` + `minorityAt σ i ≥ 1` (Lemma 7.4 `0.8\|M\|` − 7.6 `0.2\|M\|`, α=1/5) | `phase8_drop_floor_of_struct`, `phase8_hdrop_of_struct` (levels), `phase8_hstep_of_struct_one` (crude m=1) |
| 7 | `classMassN σ` / `Inv7Sum` | `classMassN_drop_prob_rect7` | `elimGap1 σ i ≥ E` + `minorityAt7 σ j ≥ 1`, j=i+1 (Lemma 7.4 elimGap `0.8\|M\|`, α=4/15) | `phase7_drop_floor_of_struct`, `phase7_hdrop_of_struct`, `phase7_hstep_of_struct_one` |
| 1 | `extremeU` / `Phase1AllMain` | **built in-file** `extremeU_drop_prob_rect_pos` | `pullPosSet ≥ P` + `extremePosSet ≥ 1` (`RoleSplit mainCount ≥ n/3` minus same-side, α=1/3) | full chain: `avgFin7_extremeVal_pair_drop_pos` → `Transition_extremeU_pair_drop_pos` → `extremeU_stepOrSelf_drop_pos` → rect → `extremeU_hdrop_of_floor` → `phase1_{drop_floor,hdrop,hstep}_of_struct` |
| 5 | `unsampledReserveU` / `Phase5AllWin` | `unsampledReserveU_drop_prob_rect5` | `usefulMains ≥ P` + `unsampledReserves ≥ 1` (Thm 6.2 biased `0.92·mainCount`, α=23/75) | in-file `unsampledReserveU_hdrop_of_floor` + `phase5_{drop_floor,hdrop,hstep}_of_struct` |
| 6 | `highMass l` / `Phase6Win` | `highMass_drop_prob_rect6` | `reserveAtHour6 h ≥ R` + `mainAt6 σ l ≥ 1`, l−1<h≠L (`ReserveSampleGood K₀`/`sampledReserveClassU`, ρ₆) | `phase6_drop_floor_of_struct`, `phase6_hdrop_of_struct` (per-level, form a) |

### The HONEST Phase-1 rectangle (the trickiest — built from scratch; was nonexistent)
Read the actual `avgFin7` rule.  An enumeration of all `7×7` `(x,y)` cells pinned the honest
strict-drop geometry: a `+3` extreme (`smallBias.val = 6`) drops iff its partner has
`smallBias.val ≤ 4` (anything NOT on the same `+2/+3` saturated side); symmetric for `−3`.  So
the honest cell is `extreme × partner(val ≤ 4)`, NOT `extreme × extreme`.  **Rate-degradation
confirmation** (the prompt's caution): the rate degrades only against same-side neighbours; the
honest partner floor is the OPPOSITE-half Main pool `mainCount − (same-side count)`, carried as
the single `pullPosSet ≥ P` hypothesis.  D-7 ships the `+3` side (`extremePos`/`pullPos`); the
`−3` mirror is the verbatim symmetric copy when the assembler needs both signs.

### What stays carried after D-7 (the ONE named structural hypothesis per phase)
The α floor is NO LONGER abstract — it is `margin/(n(n−1))` with `margin` = a CARRIED COUNT
LOWER BOUND on the partner finset (`elimAbove`/`elimGap1`/`pullPos`/`usefulMains`/`reserveAtHour6`
sum `≥ E/P/R`) plus `≥ 1` target at the level.  That count bound is the upstream Post fact:
Phase 0's role split (`RoleSplitWindows mainCount ≥ n/3`) for Phase 1; Theorem 6.2's biased
structure for Phase 5; `ReserveSampleGood K₀` (Phase-5 sampling Post) for Phase 6; Doty Lemma
7.4/7.6 for Phases 7/8.  These are NOT in the phase's own `Inv` (which carries only card/phase/
role/signed-sum); they are Phase-D threading facts supplied by the PRIOR phase's Post — kept
minimal as exactly ONE structural count hypothesis per phase, ready for the headline assembly.

### Precise remaining gap after D-7 (for the headline assembly)
The structural count floor (`margin ≥ α·n`-shape) is itself the upstream-Post threading fact;
supplying its concrete numeric value (`n/5`, `4n/15`, `n/3`, `23n/75`, `ρ₆·n`) requires wiring
the prior phase's Post invariant into each phase's start — the Phase-D composition step, not a
drain-layer atom.  All drain-layer mathematics (rule → per-cell drop → rectangle → drop-prob →
engine `hdrop`/`hstep`) is now FULLY DISCHARGED for all five phases; only the upstream-Post
count-floor wiring (and the crude-vs-levels engine choice noted above) remains for assembly.

## Phase C-0w12..21 record — Gap-1 affine scheduler drift DISCHARGED (2026-06-10)

Relay on `Probability/Phase0Window.lean`, continuing the Phase-0 timing half.  The
quantitative scheduler drift (Gap 1) is now PROVEN as an affine one-step drift on the
phase-0 window, plus its matching immigration tail engine.  All results 0-sorry,
axiom-clean (⊆ propext/Classical.choice/Quot.sound), single-file compiled.

**The affine drift (capstone `clockCounterPotential_drift_affine`):**
  `∫ Φ_s dK(c) ≤ ofReal(1 + 2(eˢ−1)/n)·Φ_s(c) + e^{−s·50(L+1)}` on `allPhase0`.
Multiplicative rate `1 + 2(eˢ−1)/n` PLUS one additive fresh-clock immigration per step.
Built bottom-up (commit SHAs):
- `0f393fb7` C-0w12: non-clock–clock per-pair ledger (`clockSummand_full`, L/R
  structural `Phase0Transition_{left,right}_summand_not_both`, combined
  `Phase0Transition_summand_not_both_clock`: output block ≤ source + fresh).
- `8ac7d83f` C-0w13: universal per-pair output bound `clockSummand_pair_le`
  (clock–clock exact eˢ + non-cc bumped via eˢ≥1) + `Transition_summand_eq_phase0`.
- `296a9fee` C-0w14: first-coordinate interaction marginal `sum_fst_interactionProb`
  (∑ g(pair.1)·prob = sumOf g c / card — the scheduler 1/n-marginal).
- `5355523f` C-0w15: second-coordinate marginal `sum_snd_interactionProb` (via
  `interactionCount_comm` + prodComm reindex).
- `88ebea87` C-0w16: per-pair potential bound `clockCounterPotential_stepOrSelf_le`
  (Φ(step) ≤ Φ(c) + (eˢ−1)·pair-block + fresh; applicable via localized splits).
- `2e040dd8` C-0w17: CAPSTONE `clockCounterPotential_drift_affine` (pair-sum + 2
  marginals collapse to 2(eˢ−1)/n + 1 fresh/step via ∑interactionProb=1).

**The affine tail engine (commit `a5b1bb49` C-0w18):**
- `lintegral_decay_affine_on_absorbing`: `∫Φ d(Kᵗ)c₀ ≤ aᵗ·Φ(c₀) + b·∑_{i<t}aⁱ` (the
  immigration analogue of `WindowConcentration.lintegral_decay_on_absorbing`, which
  only handles the multiplicative b=0 case).
- `phase0_window_tail_affine`: Markov tail `(Kᵗ)c₀{¬Post} ≤ (aᵗΦ(c₀)+b·∑aⁱ)/θ`.
The affine `+b` is essential (NOT absorbable): at a clock-free phase-0 start Φ=0 while
b>0, so no multiplicative rate holds.  Numerics close with slack: aᵗΦ₀ ≤ e^{−45(L+1)}
(`phase0_numerics_real`); b·∑aⁱ ≤ n(L+1)·e^{−50(L+1)}·e^{2(e−1)(L+1)} ≤ e^{−44(L+1)}.

**Route (a) strengthening (commit `33ca78c8` C-0w20):** the affine drift now holds on
`allPhase0` ALONE — `clockSummand_pair_le` no longer needs the positive-counter
hypotheses.  At a counter-0 clock the source summand is e^0=1 and the Rule-5
`advancePhaseWithInit` output summand is ≤1, so the per-side bound
`summand(δ_i) ≤ eˢ·summand(r_i)` holds at ANY counter
(`clockSummand_clock_clock_{left,right}_le` + `clockSummand_le_one`).  Hence the
downstream relay's `hdrift` is discharged against any absorbing `Q ⊆ allPhase0` — no
`noClockAtZero` side condition.

**REMAINING — the absorbing-window bridge (the one structural input still open):**
`allPhase0` itself is NOT `stepDistOrSelf`-absorbing (Gap 2: preserved one step w.p.1
only while `noClockAtZero` — the protocol genuinely leaves phase 0 once a clock hits
counter 0).  The affine tail engine needs an absorbing `Q` on which the drift holds.
The fix (documented in-file): supply an absorbing `Q ⊆ allPhase0` (a `RoleSplitGood`-
style count invariant — count-only role splits ARE absorbing — implying `allPhase0`
along the surviving trajectory), feed `clockCounterPotential_drift_affine` as `hdrift`,
run `phase0_window_tail_affine` (Post=`noClockAtZero`, θ=1, a=ofReal(1+2(e−1)/n),
b=e^{−50(L+1)}, Φ(c₀)≤n·e^{−50(L+1)} via `clockCounterPotential_init_le`) for the
per-τ `hτ`, then `allPhase0_window_whp` (Gap 2) assembles.  The missing Lean object is
the `Q ⊆ allPhase0` absorbing witness, which lives in the role-split layer (not in
Phase0Window.lean).  Commits `9dec6f8d`/`2ecc36ae` record the in-file gap note + header.

## Phase C — TopSplit (Lemma 5.1/5.2 RoleSplitWindows via top-split) — STAGES A+B+D+C+E DONE (2026-06-10, 0-sorry axiom-clean)

New file `Probability/TopSplit.lean` (namespace `ExactMajority.RoleSplitConcentration`; imports
`RoleSplitConcentration` + `AzumaKernel`; APPEND-ONLY, no existing file touched). All headline
theorems `#print axioms ⊆ [propext, Classical.choice, Quot.sound]`; single-file `lake env lean`
EXIT_0; zero sorry / zero admit / zero native_decide / zero new axiom. SHAs on main:
A+B 37066f79 · D+C 07c9c9ba · E 39bb769a (synced xiangyazi24/Ripple opus-wip d0461f7).

Worked the blueprint `HANDOFF_ROLESPLIT_TOPSPLIT.md` (family3 ChatGPT Pro letter) stage-by-stage.

### Stage A+B (defs + deterministic conversion) — FULLY PROVEN.
- `topCRMass = crCount + clockCount + reserveCount`, `TopSplitWindow δ n` (`|main−topCRMass|≤δn`),
  `CRDrainWindow δ` (`crCount ≤ δ·topCRMass`) — exactly the blueprint shapes.
- `RoleSplitWindows_of_topSplit_crDrain` (δ=η/4, η=1/25, δ=1/100): pure algebra via
  `roleCount_conservation` + `balanced_conservation`. `mainCount+topCRMass=n` (mcr=0) ⟹ Main window
  from `|main−topCRMass|≤δn`; `topCRMass=cr+2·clock` (balance) + drain `cr≤δ·topCRMass` ⟹
  `clock≥(1−δ)²n/4≥(1−η)n/4` since `(1−η/4)²=1−η/2+η²/16≥1−η`. Helpers `mainCount_add_topCRMass`,
  `topCRMass_balanced`. nlinarith/omega.

### Stage D (abstract sign-drift Chernoff brick) — FULLY PROVEN, RESHAPED.
RESHAPING (recorded in TopSplit.lean header + HANDOFF): the blueprint's §D `signDrift_abs_chernoff`
cited `stepIndexed_gated_tail` with `Φ_j=exp(s|X|+corr_j)` and a schematic `h_inward`. After studying
how `AzumaKernel` (`stepMGF_bound`/`expSupermartingale_drift`/`azuma_tail`) instantiates MGF drifts,
the CLEANER fit is the already-audited `AzumaKernel.azuma_tail` at `Φ=|X|`, `c=1`:
- the blueprint's `h_inward` ("X>0 ⇒ down≥up; X<0 ⇒ up≥down") IS the downward |X|-supermartingale
  drift `∫|X|dK≤|X|` — taken as the precise non-schematic hypothesis `hdrift`;
- the blueprint's `hjump` (`|ΔX|≤1`) gives `||X y|−|X x||≤|ΔX|≤1` by `abs_abs_sub_abs_le_abs_sub`
  (reverse triangle), supplying `c=1`;
- the blueprint's killed-kernel `hgate_tail`/escape term is UNNECESSARY in the abstract brick (drift
  global ⟹ no escape). The protocol's region-restriction is folded into the named `hdrift` at
  instantiation (Stage C carries it explicitly).
Result `signDrift_abs_chernoff`: `X x₀=0` + `hjump` + `hdrift` ⟹ `(K^T)x₀{a≤|X|}≤exp(−a²/(2T))`.
Strictly cleaner than the gated route; reuses the audited engine verbatim.

### Stage C (instantiate for X = mainCount − topCRMass) — NAMED-HYPOTHESIS, with proven start-fact.
- `topSplitX c = mainCount c − topCRMass c`, `topSplitX_measurable`.
- `topSplit_X_init_zero` PROVEN: `Phase0Initial` (all RoleMCR) ⟹ main=cr=clock=reserve=0 ⟹ X=0.
- `topSplitWindow_whp` = `signDrift_abs_chernoff` at `X=topSplitX`, `a=δn`, via
  `{¬TopSplitWindow δ n} ⊆ {δn ≤ |topSplitX|}`. The two protocol residuals `hjump` (`|ΔX|≤1`,
  each Phase0Transition moves main−topCRMass by ≤1) and `hdrift` (inward |X|-drift from the Lemma-5.1
  invariant `sf+2st=mf+2mt`) are carried as EXPLICIT named hypotheses with full doc.
  GENUINE ATTACK on `hdrift` documented in-file (campaign "no naming-and-stopping" rule): reduces to
  the one-step balance-changing-pair count comparison `#(decreasing) ≥ #(increasing)` on the good
  region = the existing `phase0_mcrCount_decrease_prob_*` rectangle applied to the sf-vs-mf pools;
  threading `sf+2st=mf+2mt` through a Phase-0 milestone (analogue of `assignableCount≥n/5`) is the
  documented C-1 protocol-side gap.

### Stage E (union-bound assembly) — FULLY PROVEN (named εrest input).
- `RestLedgerBad δ` = `¬CRDrainWindow δ ∨ ¬ClockReserveBalanced ∨ roleMCRCount≠0`.
- `roleSplitWindows_whp` (η=1/25, δ=1/100): deterministic inclusion (contrapositive of B)
  `{¬RoleSplitWindows (1/25) n} ⊆ {¬TopSplitWindow (1/100)} ∪ ({RestLedgerBad (1/100)} ∪ {card≠n})`,
  union-bounded by εtop (Stage-C `topSplitWindow_whp` at δ=1/100) + εrest. `εrest` = the Stage-2
  drain/balance/mcr0 failure mass INCLUDING the `card≠n` slice (kernel-card-conservation makes that
  slice 0 from a card=n start), carried as a NAMED whp input per the Stage-E campaign rule.

### BLUEPRINT CLAIMS vs ACTUAL REPO (verdicts).
1. Stage A+B defs/conversion: blueprint shapes used VERBATIM; the existing `roleCount_conservation`/
   `balanced_conservation`/`ClockReserveBalanced`/`RoleSplitWindows`/`crCount`/`mainCount`/
   `clockCount`/`reserveCount` are all in `RoleSplitConcentration` as the blueprint claimed.
2. Stage D `stepIndexed_gated_tail` route: the engine EXISTS (`GatedGeometricDrift.lean`) but the
   blueprint's `h_inward` was schematic. The cleaner instantiation is `AzumaKernel.azuma_tail`
   (also already in-repo) — RESHAPED accordingly (documented). The blueprint EXPLICITLY licensed
   restating hypothesis shapes "to whatever the engine actually needs" — done.
3. Stage E target `{¬RoleSplitWindows (1/25) n} ≤ ofReal(3·(n²)⁻¹)`: the `3·(n²)⁻¹` is the
   eventual numeric budget; this file proves the STRUCTURAL union bound `εtop + εrest` with εtop the
   concrete Stage-C exp-tail and εrest named (the `≤ 3/n²` collapse is the Stage-2 εrest discharge +
   horizon choice, downstream). Insertion point `phase0_roleSplit_whp_assembled_stage2` confirmed
   present and consuming (hstage2, hbal, hwin) exactly as the blueprint stated.
4. The protocol invariant `sf+2st=mf+2mt` (Lemma 5.1) is NOT yet formalized in the ExactMajority
   tree (grep-confirmed) — it is the genuine residual behind Stage-C's `hdrift`, carried as a named
   hypothesis with the documented attack route, NOT faked.

## εfloor floor-prefix — FloorPrefix.lean DELIVERED (2026-06-10, opus line)

New append-only `Probability/FloorPrefix.lean` (733 lines, namespace
`ExactMajority.FloorPrefix`) realises the post-gated floor residual of
HANDOFF_EFLOOR_PREFIX.md. Single-file EXIT_0; all headlines axiom-clean
[propext, Classical.choice, Quot.sound]; 0 sorry/admit/axiom/native_decide. 4 commits
(3c4d76df scalar layer / Stage-2 drift / Stage-3+4 assembly / this doc), each pushed to
origin main + mirrored to xiangyazi24/Ripple opus-wip.

PROVEN end-to-end: the scalar favorability layer (scalarPoolFav_core STRICT at b=9/100,
d=4/100, s=1/10), the one-step pool MGF drift analytic core
(pool_expNeg_one_step_drift_abstract — 3-band birth/death/neutral integral split, the
genuinely-new analytic content), the §3 wrapper pool_expNeg_one_step_drift, the genuine
Stage-2→engine connection midBand_gated_tail (via GatedDrift.gated_real_tail_full), and the
pure region-composition floor_prefix_le + floor_prefix_le_inv_sq capstone (εfloor n = n⁻²).

NAMED (the genuinely-large remaining protocol work, exact statements in the file +
HANDOFF status): hbirth/hdeath (real-kernel band masses vs Phase0Transition), hstep (±2
range), the warm reach, and the εmid/εlate contractive prefix (needs the absorbing-window
killed-kernel reformulation).

Blueprint corrections recorded: s=1/2 too large (→ s=1/10); windowDrift_tail needs an
absorbing window (warm/mid band is not — use gated_real_tail_full); gated engines need
1≤r (escape-form tail, not decaying rᵗ); Rules 2&3 are pool-conserving so the birth mass
is carried entirely by Rule-1 (matches the proven assignable_rule accounting).

## TopSplitDrift — discharge of TopSplit's `hjump`/`hdrift` residuals (2026-06-10)

New file `Probability/TopSplitDrift.lean` (append-only; TopSplit.lean unedited), 0-sorry /
axiom-clean [propext, Classical.choice, Quot.sound]. Discharges the two named protocol
residuals carried by `TopSplit.topSplitWindow_whp` for `X = mainCount − topCRMass`, and in
doing so found + fixed two faithfulness traps in the Stage-C interface (playbook §3.3).

TRUE invariant (vs paper's `sf+2st=mf+2mt`): the paper's literal ledger does NOT map onto the
Lean encoding. Computing ΔX for every Phase-0 rule (`Phase0Transition` body): R1 (mcr,mcr→main,cr)
ΔX=0; R2 (mcr+unassigned-main→cr) ΔX=−1; R3 (mcr+unassigned-(cr/clock/reserve)→main) ΔX=+1;
R4 (cr,cr→clock,reserve) ΔX=0; R5 (clock,clock) ΔX=0. So X moves only by R2/R3, and the honest
preserved equation is the EXISTING `mainCount + topCRMass = n` (mcr=0). Honest ledger weight
`topW a = [main] − [cr∨clock∨reserve]`, `topSplitXZ = Config.sumOf topW`. Free pools = #unassigned-Main
(R2 targets) vs #unassigned-(cr/clock/reserve) (R3 targets).

- Stage 1: `topW`, `topSplitXZ`, `topSplitXZ_eq_counts`, `topSplitX_eq_cast` (bridge to TopSplit).
- Stage 2 (hjump): `topW_Phase0_pair_delta_abs_le_one` (finite case bash; R5 split via
  `stdCounterSubroutine_clock_role_eq`) → `topW_pair_delta_abs_le_one_of_phase0` →
  `topSplitXZ_step_delta_abs_le_one` (config-level |ΔX|≤1 on Phase-0 region). True bound = 1.
- Stage 3 (hdrift) — TRAP FIXED: Stage-C's `∫|X|dK≤|X|` is FALSE at X=0 (from balanced |X|=0, R2/R3
  push to ±1, so ∫|X|dK>0=|X|) — a VACUOUS conditional (unsatisfiable premise, undetectable by
  #print axioms). Honest fix = cosh MGF. `InwardResidual s c := sinh(sX)·E[sinh(sΔ)]≤0` is BOUNDARY-FREE
  (sinh 0=0 at X=0). `coshExpVal_drift_real`: ∫cosh(sX')dK ≤ cosh(s)·cosh(sX) via cosh_add
  (cosh part ≤cosh(s)cosh(sX) by |Δ|≤1+∑prob=1; sinh part ≤0 by inward). `coshPot_drift` (ℝ≥0∞,
  multiplicative r=ofReal(cosh s), no immigration term). cosh facts derived from cosh_eq/sinh_eq/exp
  (DerivHyp not in single-file closure). Local `integral_transitionKernel_eq_pairSum` +
  `lintegral_coshPot_eq_ofReal_integral` (termwise pair-sum bridge, no integrability goal).
- Stage 4 (tail/wire-up): `coshPot_ge_thresh_of_not_window` (threshold link: cosh even+monotone) +
  `windowDrift_tail` on absorbing Q ⟹ `topSplitWindow_whp_cosh`:
  `(K^T)c₀{¬TopSplitWindow δ n} ≤ (cosh s)^T·coshPot(c₀)/cosh(sδn)`. `coshPot_init_one` (X c₀=0 ⟹
  coshPot=1) ⟹ `topSplitWindow_whp_cosh_clean` = `(cosh s)^T/cosh(sδn)` (restates TopSplit's
  conclusion shape; TopSplit.lean unedited). Optimizing s=δn/T, cosh s≤exp(s²/2),
  cosh(sδn)≥exp(sδn)/2 recovers the consumer's 2·exp(−(δn)²/(2T)) shape.

Two genuine protocol residuals remain, BOTH boundary-free, both honest Lemma-5.1 content:
(1) absorbing `Q ⊆ allPhase0` witness (also the Phase0Window gap); (2) `InwardResidual` on `Q`
(the symmetric pair-count comparison #R2-pairs ≥ #R3-pairs on {X>0} + mirror, from the free-pool
ledger). The X=0 boundary — the mathematical crux — is SOLVED by cosh (no exception at 0).
Commits f475aedd / 87271ca4 / 7760b01 / 7e9e3a6d.

## SEAM NO-OVERSHOOT — DELIVERED 2026-06-10 (opus)

New file `Probability/SeamNoOvershoot.lean` (append-only; no existing file edited).
Discharges the per-seam `hNoOvershoot` event `SeamEpidemics` budgeted but never consumed,
and FIXES the integration bug (`seamEpidemicW`'s `εovershoot` was added by `le_self_add`
and never used).  5 stages, one commit each (951472b / 7895564 / b0d472b / a37968e /
637a0a9), single-file EXIT_0 on uisai2 /dev/shm (v4.30.0); every headline
`#print axioms ⊆ [propext, Classical.choice, Quot.sound]`; 0 sorry / 0 native / 0 axiom.

- Stage 1: seam predicates + at-risk clock potential `Φ_s = ∑_{clock,phase=p+1} e^{−s·counter}`
  + threshold lemma (clone of Phase0Window, predicate = clock ∧ phase = p+1).
- Stage 2: `CounterTimedPhase = {1,5,6,7,8}` (HONEST — phase 3 excluded, no counter reset
  on entry) + `DetSeamOvershootBridge` named structural fact (error-to-10 finding:
  bridge needs well-formedness; blueprint's {1,3,5,6,7,8} corrected).
- Stage 3: affine drift `∫ Φ dK ≤ ofReal(1+2(eˢ−1)/n)·Φ + 2·M` (clone of
  `clockCounterPotential_drift_affine`; per-pair output bound `hpair` is the input).
- Stage 4: numerics → e^{−40(L+1)} (with the 2M immigration sum) + tail via
  `phase0_window_tail_affine`.
- Stage 5: prefix-union terminal tail + `hNoOvershoot_one_seam` budget +
  **`seamEpidemicExactW`** (integration fix: Post strengthened with NoOvershoot,
  εovershoot consumed by union bound) + `seamExact_into_exact_work` (deterministic).

Two named carried facts after a real attack (per discipline): `hpair` (per-pair output
bound, seam analogue of `clockSummand_pair_le` on `{1,5,6,7,8}`) and
`DetSeamOvershootBridge` (deterministic bridge; needs the Analysis-layer well-formedness
because `phaseInit 1` can error an `mcr` to phase 10 without a counter-0 clock).  See
`HANDOFF_SEAM_NOOVERSHOOT.md` STATUS section for the full verdict + blueprint corrections.

---

## εfloor protocol masses — `Probability/FloorMasses.lean` COMPLETE (2026-06-10, opus line)

New append-only file `Probability/FloorMasses.lean` (734 lines, namespace
`ExactMajority.FloorMasses`) discharging the three named protocol-mass residuals that
`FloorPrefix.pool_expNeg_one_step_drift` left as inputs (`hstep`, `hbirth`, `hdeath`).
Single-file `lake env lean` EXIT_0; every headline `#print axioms ⊆ [propext,
Classical.choice, Quot.sound]`; no sorry / admit / axiom / native_decide.  Four commits
(one per stage), each pushed to `origin main` + mirrored to `xiangyazi24/Ripple opus-wip`.

### Per-stage verdict

**Stage 1 — `hstep` (±2 per-step pool range): FULLY DISCHARGED (unconditional).**
`assignableCount_stepOrSelf_ge` + `pool_step_ge_ae`.  `assignableCount = countP isAssignableBool`
is definitional, so `HourCouplingV2.countP_stepOrSelf_diff_le_two` (the bounded-difference
atom) gives the `−2` lower bound per chosen pair; the support reduction of `hour_bdd` lifts
it to the a.e. kernel statement.  No region hypothesis needed — strictly stronger than the
FloorPrefix `hstep` shape.

**Stage 2 — `hbirth` (R1 birth rectangle): DISCHARGED (honest fresh-MCR count).**
`Transition_eq_phase0_of_fresh_mcr_pair` (full Transition=Phase0Transition bridge for a
fresh-MCR pair, via `phaseEpidemicUpdate_eq_self_of_both_phase0` + `finishPhase10Entry`
identity on phase-0 outputs) → `birthR1_config_eq` (config-level `+2`) → the `freshMcrF×ˢfreshMcrF`
rectangle (`sum_interactionCount_freshMcr = freshMcrCount(freshMcrCount−1)`) →
`interactionPMF_toMeasure_freshMcr_ge` → `birthR1Mass_ge_freshMcr` (via
`stepDistOrSelf_toMeasure_ge`) → `hbirth_of_freshMcr_floor` (the FloorPrefix `hbirth` shape).
**Honest mismatch flagged:** the R1 birth count is `freshMcrCount` (unassigned phase-0 MCR),
NOT bare `mcrCount`.  `cardPhaseShell` only pins `role = mcr → phase 0`, not unassigned, and
no MCR-unassigned invariant exists in the repo.  `hbirth` holds verbatim once `uMin ≤
freshMcrCount` (the adapter's hypothesis).

**Stage 3 — `hdeath` (R4 drain rectangle, upper bound): INFRASTRUCTURE + ADAPTER.**
`stepDist_toMeasure_eq_preimage` (kernel↔preimage dual of `stepDistOrSelf_toMeasure_ge`) +
`block_pair_prob_le_sq` (AgentState clone of `EarlyDripMarked.pair_block_prob_le_sq`, with
`sum_block_interactionCount`) + `pair_block_sq_le_buffer` (the `(X/n)² ≤ Ahi²/(n(n−1))`
arithmetic) → `hdeath_of_block` (the FloorPrefix `hdeath` shape, given a drain block).
**Honest mismatch flagged (two reasons hdeath is NOT verbatim true on the region):**
(a) R4 fires on *any* two `RoleCR`; an assignable CR can drop the pool paired with a
*non-assignable* CR, so the drop preimage is contained in the `RoleCR×RoleCR` block, giving
`(crCount/n)²` with `crCount` the TOTAL CR count — not the pool `≤ Ahi`.  (b) the full
`Transition`'s `phaseEpidemicUpdate` prefix is a second drain path (advancing a phase-0
assignable out of phase 0), which `cardPhaseShell` does not forbid.  The honest provable
bound is `(drainBlockCount/n)²`; `hdeath_of_block` consumes the containment `drainPreimage ⊆
CR×CR` and `crCount ≤ Ahi` as the documented residual protocol facts.

**Stage 4 — wire-up: `pool_expNeg_one_step_drift_floorMasses`.**  Instantiates
`FloorPrefix.pool_expNeg_one_step_drift` at `s = 1/10` feeding hstep (unconditional),
hbirth (via the fresh-MCR floor), hdeath (via the drain block), and the **fully-discharged**
favorability `scalarPoolFav_instance` (proven `< 1`).  The remaining inputs are the
pure-scalar count-fraction arithmetic (`hb0/hd0/hb1/hbd1`, calibration-dependent) and the two
documented protocol-count facts (fresh-MCR floor + drain block).

### Engine note (unchanged from FloorPrefix finding 3)

`midBand_gated_tail` was NOT instantiated: it requires `1 ≤ r` (the killed potential must
dominate the cemetery transition), incompatible with our genuinely-contractive `r < 1`
favorability.  This is the documented absorbing-window vs gated-engine mismatch — a property
of the engine layer, not of the protocol masses; the masses are now discharged.

### Remaining work (for a follow-up line)

The two residual protocol-count facts are: (i) `uMin ≤ freshMcrCount` on the region — needs
the MCR-always-unassigned invariant (a fresh Transition-preservation argument; no such
invariant exists yet); (ii) the drain-block containment `drainPreimage ⊆ CR×CR` + `crCount ≤
Ahi` — needs the `Transition`-level "strict pool drop ⟹ both inputs CR" enumeration AND a
phase-synchronisation condition to neutralise `phaseEpidemicUpdate`.  Fact (ii) is not
verbatim true on `PoolDriftRegion` as currently defined (see Stage-3 reasons a/b); the region
or `r4FreshCRDrainMass` would need strengthening (e.g. an all-phase-0 / `crCount ≤ Ahi`
region invariant) for a clean verbatim `hdeath`.

---

## §5.1 InwardResidual discharge — `Probability/TopSplitInward.lean` (2026-06-10)

The `TopSplitDrift.lean` cosh route reduced the top-split tail to one boundary-free residual
`InwardResidual s c := sinh(sX)·E[sinh(sΔ)] ≤ 0`. `TopSplitInward.lean` discharges it to a single
named R2/R3 mass identity, with the new assigned-balance ledger + the full reduction proven 0-sorry
(all 8 headlines axiom-clean ⊆ [propext, Classical.choice, Quot.sound]).

PROVEN (genuinely new): the assigned-balance ledger `freeDiff = 2·X` (`freeW = [main∧¬asg] −
[CR-side∧¬asg]`), per-pair conserved (`ledgerW_Phase0_pair_conserved`), preserved by stepOrSelf
(`LedgerInv_stepOrSelf`) and initial (`LedgerInv_init`) — the Lean-faithful `sf+2st=mf+2mt`. Plus the
boundary-free sinh collapse `InwardResidual ⟸ X·E[ΔX] ≤ 0` (`inwardResidual_of_expectedDeltaX_sign`),
and `LedgerInv + RectangleResidual ⟹ X·E[ΔX] = −4mcr·X²/tp ≤ 0` (`expectedDeltaX_sign_of_ledger`).
Tail wired: `topSplitWindow_whp_inward`.

CAVEATS FOUND (honest): (a) the ledger conservation FAILS for `assigned-mcr` inputs — unreachable
(rules only consume mcr), carried as `NotAssignedMcr`/`NoAssignedMcrConfig` (proven preserved, but
NOT pinned by the abstract `Phase0Initial`, which fixes only role/phase — carried explicitly).

THE ONE NAMED RESIDUAL = `RectangleResidual c := totalPairs·E[ΔX] = −2·mcrCount·freeDiff`. Genuine
attack: reduces to the JOINT double-marginal `∑_{s₁,s₂} interactionCount·pairDelta = 2·mcr·(Sf−Mf)`
(pairDelta ∈ {−1,0,1} is the proven topW-block delta). The repo has only SEPARABLE per-coordinate
marginal collapse; the joint double-`Multiset.count` rectangle is the precise missing lemma — the
clean follow-up target. Commits 86f2083e / 666babd4 / 1c7e2fde / e454d342.

## §5.1 RectangleResidual DISCHARGED — `Probability/RectangleResidualProof.lean` (2026-06-10, 0-sorry axiom-clean)

The "precise missing lemma" above (the JOINT double-`Multiset.count` rectangle) is now BUILT, and the
named residual `RectangleResidual` is a THEOREM. The top-split inward drift (§5.1) is hypothesis-free
modulo the absorbing-region structure of `Q`. Headlines `#print axioms ⊆ [propext,Classical.choice,Quot.sound]`.

- **JOINT marginal `sum_iCount_rectangle_disjoint`** (the missing lemma): for DISJOINT Bool classes P,Q,
  `∑_{s₁,s₂} [P s₁][Q s₂]·interactionCount = (∑_P count)(∑_Q count)`. Joint generalization of the separable
  `sum_fst/snd_interactionProb` and of `sum_interactionCount_mcr_assign`.
- **pairDelta table** (`pairDeltaZ_eq_table`): the role-determined `topW`-block delta = `indR3 − indR2`
  (`−1` on R2 mcr↔uMain, `+1` on R3 mcr↔uCR, both orientations; `0` else). Finite 5×5×2×2 check.
- **ORIENTATION:** R2/R3 dispatch in FROZEN `Phase0Transition` is a two-branch (s=mcr / t=mcr) table, both
  branches same delta ⟹ pairDelta symmetric ⟹ the ordered-pair sum counts BOTH orientations ⟹ the factor 2.
- **DIAGONAL:** R2/R3 blocks are mcr×non-mcr (disjoint classes, proven), so `s₁≠s₂` always — `interactionCount`
  self-pair `−1` correction vanishes, each rectangle is the clean product `mcr·Mf` / `mcr·Sf`.
- **Integer rectangle** `sum_iCount_pairDeltaZ`: `∑ iCount·pairDeltaZ = 2·mcr·(Sf−Mf)`.
- **Real connection** `totalPairs_expectedDeltaX_eq`: `totalPairs·E[ΔX] = ((∑ iCount·pairDeltaZ:ℤ):ℝ)`
  (positive-count ⟹ applicable ⟹ phase-0 ⟹ `topSplitStepDelta = (pairDeltaZ:ℝ)`; zero-count vanishes).
- **`freeDiff_eq_Mf_sub_Sf`**: `freeDiff = Mf − Sf`.
- **HEADLINE `rectangleResidual_of_allPhase0`**: `card≥2 ∧ allPhase0 ⟹ RectangleResidual`.
- **`topSplitWindow_whp_rectFree`**: `topSplitWindow_whp_inward` with `hQ_rect` DROPPED. Final hypothesis
  surface = `Phase0Initial` + absorbing `Q` (allPhase0/card≥2/LedgerInv), all protocol-provable.

NO protocol-counting residual remains in the §5.1 top-split chain.

## §SeamPairBound — seam `hpair` protocol-core DISCHARGED + two findings — `Probability/SeamPairBound.lean` (2026-06-10, 0-sorry axiom-clean)

The protocol-structural core behind `SeamNoOvershoot`'s carried `hpair` (the seam analogue of
`Phase0Window.clockSummand_pair_le`, restricted to counter-timed destination phases `q = p+1 ∈ {1,5,6,7,8}`)
is now BUILT in a new file. All headlines `#print axioms ⊆ [propext, Classical.choice, Quot.sound]`, no
`native_decide`. New file only (append-only; no existing file edited).

### Proven (left side; right side is symmetric by the same lemmas)

- `seamClockSummand_congr` / `seamClockSummand_finishPhase10Entry` — the seam summand reads only
  `role`/`phase`/`counter`, all preserved by `finishPhase10Entry`; so it equals that of the dispatcher
  output (strips the post-step wrapper).
- `phaseInit_clock_counter_reset` — `phaseInit q` resets a clock counter to `50(L+1)` for `q ∈ {1,5,6,7,8}`.
- `seamClockSummand_stdCounterSubroutine_le` / `…_clockCounterStep_le` — the **decrement bound**: a clock at
  `p+1` whose counter is ticked scales its summand by exactly `eˢ` (or advances out, summand `0`).
- `runInitsBetween_clock_counter_reset` — the epidemic fold `runInitsBetween oldP q (clock)` ends in
  `phaseInit q`, resetting to full (filter-list-ends-in-`q` + role-preserving prefix fold).
- `phaseInit_phase_eq_or_ten` / `runInitsBetween_phase_eq_or_ten` / `runInitsBetween_role_clock_imp` /
  `phaseInit_role_clock_imp` — phase-writing only via `enterPhase10`; no clock creation from non-clocks.
- `phaseEpidemicUpdate_left_immigrant_full` — a clock dragged up into `q` by the epidemic enters at full
  counter; `phaseEpidemicUpdate_left_id_of_ge` — epidemic identity when partner phase `≤` own.
- `seamClockSummand_phaseEpidemicUpdate_left_le` — **epidemic summand bound** `summand(ep.1) ≤ summand(a) + freshVal`.
- `seamClockSummand_stdCounterSubroutine_advance` — **counter-advance immigration**: a clock advanced into
  a reset phase `{1,6,7,8}` enters at full counter, summand `= freshVal`.
- `Phase{1,5,6,7,8}Transition_left_clock` + `seamClockSummand_dispatch_left_decrement_le` — routes the FROZEN
  11-phase dispatcher through the per-phase reductions to the no-advance per-side contraction.
- **HEADLINE `seamClockSummand_Transition_left_le_of_ep_at_dest`**: in the no-advance regime
  (`ep.1.phase = p+1`), `summand((Transition a b).1) ≤ eˢ · (summand(a) + freshVal)` — the honest per-side
  output bound, full chain finishPhase10-strip → dispatch decrement → epidemic immigration.

### TWO FINDINGS (after genuine attack, per discipline)

1. **`SeamNoOvershoot.hpair`'s immigration constant `2·freshVal` is TOO TIGHT for `s > 0`.** An
   epidemic-dragged fresh clock enters `p+1` at the FULL counter and is DECREMENTED by the SAME-step
   dispatch to `full − 1`, so its per-side summand is `eˢ·freshVal`, not `freshVal`. The honest per-side
   immigration ceiling is `eˢ·freshVal`; per-pair `2·eˢ·freshVal` (at `s = 1`, `2e·freshVal > 2·freshVal`).
   The exact `hpair` shape is therefore UNPROVABLE for the real kernel. DOWNSTREAM-BENIGN: the consumer's
   `seam_noOvershoot_numerics_real` closes `e^{−40(L+1)}` from `e^{−45}+e^{−43}` with large slack, so
   replacing `b = 2·freshVal` by `b = 2·e·freshVal` still closes (one extra `e` against ~`e^{3(L+1)}` margin).
   FIX (downstream, future): re-state `hpair`/`seamClockPotential_stepOrSelf_le`/`…_drift_affine`/
   `seam_atRiskClockZero_tail` with `2·eˢ·freshVal`; `seam_noOvershoot_numerics_real` re-derives unchanged.

2. **Phase 5 must ALSO be excluded from the counter-reset set (like phase 3).** Predecessor `Phase4Transition`
   advances clocks via `advancePhase` (big-bias gate), which does NOT run `phaseInit` / reset the counter.
   A clock counter-advanced from phase 4 into phase 5 keeps its OLD (possibly small/zero) counter — summand
   up to `1`, NOT `freshVal` — breaking the affine immigration tail for phase 5. Phases `{1,6,7,8}` are clean
   (predecessors `Phase0` Rule-5 / `Phase{5,6,7}` advance via `stdCounterSubroutine → advancePhaseWithInit →
   phaseInit q`, which DOES reset). **The fully-honest counter-reset destination set for this clock-counter
   seam no-overshoot tail is `{1,6,7,8}`** (consumer's epidemic-drag set `{1,5,6,7,8}` ∩ counter-advance-reset
   set `{1,6,7,8}`). Phase 5's no-overshoot, like phase 3's, must come from the minute/hour width machinery.

### Residual (precisely isolated, after attack)

- The PHASE-ADVANCE regime per-side bound (`ep.1.phase < p+1`): proven `= freshVal` for `{1,6,7,8}` via
  `seamClockSummand_stdCounterSubroutine_advance`, but requires routing the predecessor-phase dispatch
  (`Phase0` Rule-5 / `Phase{5,6,7}` left-clock output = `stdCounterSubroutine`) — the `Phase0Transition`
  left-clock reduction is the one not-yet-packaged piece (Phase{5,6,7} are done). Phase 5 FAILS (finding 2).
- The full per-pair adapter delivering `SeamNoOvershoot`'s exact `hpair` is NOT deliverable as stated
  (finding 1: constant; finding 2: phase 5). The honest adapter targets `2·eˢ·freshVal` over `{1,6,7,8}`.

---

## KilledAffineTail.lean — the AFFINE-IMMIGRATION killed-tail GENERIC ENGINE (2026-06-10, 0-sorry axiom-clean)

`Probability/KilledAffineTail.lean` builds the ONE generic engine three campaign lines were
blocked on: the `killK_now` analogue of `Phase0Window.phase0_window_tail_affine`, with affine
drift on the gate `G` ONLY, immigration `b ≥ 0`, and — critically — rate `a ≥ 0` ARBITRARY (NO
`1 ≤ a`).  Append-only; existing files untouched.

### Why the old `1 ≤ r` existed and how it was removed (honestly)

The multiplicative gated engine (`GatedGeometricDrift.killed_geometric_tail`,
`GatedEscape.gated_real_tail_full`) carried `hr : 1 ≤ r`.  It was SPURIOUS: in
`GatedGeometricDrift.killK_drift` the hypothesis `hr` is never used in the proof body — the
killed potential `killΦ Φ none = 0`, so on the cemetery/ungated branch the killed drift LHS is
`∫⁻ killΦ d(δ none) = 0 ≤ r·0` for ANY `r ≥ 0`, and the alive branch is exactly `hdrift_G`.  The
analytic core `PopProtoCommon.lintegral_geometric_decay` likewise takes arbitrary `r`.  `1 ≤ r`
was a convention carried from the supermartingale layer.  For the affine case the dead-branch
killed drift target is `a·killΦ none + b = b ≥ 0 = LHS`, so `a` is unconstrained.  Dropping it
makes the killed tail GENUINELY decay when `a < 1` — the contractive regime FloorPrefix needed.
(The non-decaying `t·η + rᵗΦ/θ` of `gated_real_tail_full` came from the COARSE escape bound `t·η`,
not from any `killK` obstruction; here escape is bounded by the self-referential threshold prefix.)

### Stages (one commit each, all single-file `lake env lean` EXIT_0, axioms [propext, Classical.choice, Quot.sound])

1. `killK_now_drift_affine` / `killed_now_lintegral_decay_affine` / `killed_now_affine_tail`:
   `(killK_now^t)(some x₀){θ≤killΦ Φ} ≤ (aᵗΦx₀ + b∑aⁱ)/θ`, `a≥0` arbitrary, `b=0` special case.
2. `real_le_killed_affine_tail_add_escape`: `(K^t)x₀{θ≤Φ} ≤ killed-tail + escape` (real_le_killed_now
   + measure_union_le split).
3. `escape_le_threshold_prefix` (deterministic exit bridge, q=0) + `real_window_killed_affine` +
   `real_window_killed_affine_uniform`: escape replaced by ∑_τ (K^τ)x₀{θ'≤Φ}; packaged window.
4. **Consumer 1 (Gap-2 headline) — the unconditional Phase-0 window.**  `phase0Gate := allPhase0 ∩
   {card=n}`; `phase0Gate_exit_bridge` proves the q=0 exit (Φ<1⟹noClockAtZero⟹allPhase0 preserved
   via `transitionKernel_not_allPhase0_eq_zero_of_noClockAtZero` + card preserved via
   `stepOrSelf_card_eq`); `phase0_killed_clock_zero_tail` = clean decaying killed budget aᵗΦc₀+b∑aⁱ
   (NO absorbing Q, NO 1≤a); `phase0_clock_zero_killed_affine` = real per-τ clock-zero bound.  The
   campaign's only-missing object ("the absorbing Q ⊆ allPhase0") is REMOVED — the killed kernel
   substitutes for it.  Hypothesis surface: `card=n` + `allPhase0` + arithmetic.
5. **Consumer 2** (`topGate`, `topGate_exit_bridge`, `top_killed_cosh_tail`, b=0 multiplicative):
   absorbing-Q discharge for `topSplitWindow_whp_rectFree` — gate = allPhase0∩card∩NoAssignedMcr∩
   LedgerInv, all 4 conjuncts one-step preserved except the killed allPhase0 exit.
   **Consumer 3** (`midBand_killed_contractive_tail`, `midBand_real_contractive_tail`): the
   contractive `r<1` pool-MGF killed tail FloorPrefix finding 3 was blocked on — genuinely decaying.

### Residual (honest)

The Consumer-1 real per-τ bound `phase0_clock_zero_killed_affine` carries a SELF-REFERENTIAL
threshold prefix `∑_{σ<τ} (K^σ)c₀{1≤Φ}` (the escape) — the same prefix `allPhase0_window_whp`
(Gap-2) already consumes.  Discharging the uniform per-τ `hτ` (the clean `e^{-45(L+1)}` bound) for
`allPhase0_window_whp`'s assembly additionally needs the REACHABILITY fact (allPhase0 ∧ full-counter
gate-membership preserved along the surviving trajectory) — a separate role-split/reachability layer
object, not an engine gap.  The killed AFFINE-TAIL engine itself (the campaign's named blocker) is
DELIVERED 0-sorry axiom-clean; the cleanest decaying object `phase0_killed_clock_zero_tail` is the
absorbing-Q substitute.  Consumers 2/3 adapters delivered at the strongest reachable hypothesis-free
engine-shape; their final whp instantiation re-cuts the existing `windowDrift_tail`/`gated_real_tail`
call-sites against the killed tail (mechanical, no new math).

## SESSION HANDOFF 2026-06-10 evening (usage cutoff)

Nine relay agents landed today, three IN FLIGHT at cutoff. Each landed agent
appended its own completion record above; this is the session-level map.

### Landed (all 0-sorry, axiom-clean, pushed + mirrored to opus-wip)
| File | Delivered | Residual it left |
|---|---|---|
| DrainThreading.lean | D-7: all 5 phases' hdrop/hstep threaded | assembly supplies numeric floors |
| Phase0Window.lean (cont.) | Gap-1 affine scheduler drift + tail engine | absorbing-Q → SOLVED by KilledAffineTail |
| TopSplit.lean | §5.1 skeleton: defs + det. conversion + Azuma brick | hjump/hdrift → both discharged below |
| TopSplitDrift.lean | hjump (|ΔX|≤1) + cosh-MGF (X=0 boundary solved) | InwardResidual → discharged below |
| TopSplitInward.lean | LedgerInv: Mf−Sf=2X (the honest Lemma 5.1 ledger) | RectangleResidual → discharged below |
| RectangleResidualProof.lean | joint double-marginal; §5.1 counting CLOSED | absorbing-Q → solved by KilledAffineTail |
| FloorPrefix.lean | εfloor 3-region structure + capstone | 3 masses → discharged below; engine 1≤r → solved |
| FloorMasses.lean | hstep/hbirth(freshMcr)/hdeath(containment) | uMin≤freshMcrCount region fact |
| SeamNoOvershoot.lean | hNoOvershoot chain + seamEpidemicExactW fix | hpair → SeamPairBound; honest set {1,6,7,8} |
| SeamPairBound.lean | per-side bounds; found 2·eˢ·freshVal + phase-5 exclusion | adapter → SeamPairAdapter (in flight) |
| KilledAffineTail.lean | THE engine: killed affine tail, a≥0 arbitrary; absorbing-Q eliminated; 1≤r was spurious | consumers' final re-cut (in flight) |

### IN FLIGHT at cutoff (opus subagents; if killed, re-dispatch from these briefs)
1. SeamPairAdapter.lean — honest hpair adapter: missing {1,6,7,8} advance-regime
   dispatch reductions, two-sided bound w/ 2·eˢ·freshVal, corrected drift+numerics
   (check e^{-40(L+1)} still closes), end-to-end hNoOvershoot for {1,6,7,8}.
   Brief is reconstructible from SeamPairBound's HANDOFF status + this row.
2. WidthTransport.lean — HANDOFF_WFP_TRANSPORT.md blueprint (ChatGPT letter,
   network-delivered): deterministic scalar front transport (only equal-minute
   DRIP raises global max, +1/step), CrossEmptyClimbGood/Bad, profile transport
   NOT deterministic, widthFail_between_checkpoints_concrete assembly.
3. KilledTailConsumers.lean — final re-cut: (a) §5.1 hypothesis-free top-split
   tail (Phase0Initial + NoAssignedMcrConfig + arithmetic, explicit T+budget);
   (b) Gap-2 assembly vs allPhase0_window_whp (reachability may be unnecessary
   in killed formalism); (c) εmid final form via midBand_real_contractive_tail.

### Remaining queue after the in-flight three
- E4 assembly (expectation half, Phase E4) — re-ask the E4 letter on
  family/family2/family3 (NOT cron — wrong repo); blueprint shape was drafted
  in the lost cron letter b1ec23eb (text in /api/result, 0-byte answer).
- DetSeamOvershootBridge (needs validInitial well-formedness; mcr→phase-10
  epidemic path is the obstruction — see SeamNoOvershoot findings).
- Phase 2/3/4/5/9 seam guards (untimed or no-counter-reset destinations).
- Phase-D composition: wire prior-phase Posts into per-phase numeric floors
  (n/5, 4n/15, n/3, 23n/75, ρ₆n) for DrainThreading + levels-engine re-target
  for Phases 1/5/7/8 (crude m=1 hstep is vacuous for Φ≥2).
- Budget tightening to paper-rate 1−O(1/n²) (cleanup queue, dad-approved).
- Phase F: audit refresh + uisai2 explicit-module full build + 推平 main.

### Bridge (for the research loop)
WS path SOLVED end-to-end (see chatgpt-bridge-pr3/UNDERSTANDING.md 06-10
section). Ask letters with scripts/ask-gpt.py <channel> — banner + runs.log
ledger discipline in .claude/skills/chatgpt/SKILL.md. Ripple letters ONLY on
family/family2/family3.

### WidthTransport completion record (post-cutoff bookkeeping, 2026-06-10)
Probability/WidthTransport.lean stages 1–4 landed (a95dff31 + 498dfec0): deterministic
scalar climb transport on AllClockP3 (DRIP-only +1/step), CrossEmptyClimbGood width glue,
crossEmptyClimb_whp finite union, widthFail_between_checkpoints_concrete CK assembly.
Cut before its own doc commit; axiom sweep deferred to Phase F. Resumed agents:
SeamPairAdapter stages 2–4 + KilledTailConsumers deliverables 2–3 re-dispatched.

### SeamPairAdapter completion record (2026-06-10, resumed agent — Stages 2–4)
Probability/SeamPairAdapter.lean COMPLETE (Stages 1–4; append-only, no edit to SeamNoOvershoot.lean
or SeamPairBound.lean). Single-file `lake env lean … SeamPairAdapter.lean` EXIT 0; all headlines
`#print axioms ⊆ [propext, Classical.choice, Quot.sound]`; 0 sorry / 0 native_decide / 0 axiom.

- Stage 2 (d3c1cc22): HONEST two-sided pair bound `seamClockSummand_Transition_pair_le` —
  `summand₁'+summand₂' ≤ eˢ·(summand₁+summand₂) + 2·(eˢ·freshVal)` over `{1,6,7,8}` (finding 1 fixed,
  the consumer's `2·freshVal` is FALSE for s>0). Universal per-side bounds + `SeamRegimeDispatch` predicate.
- Stage 3 (ab0fab2f): HONEST config-level drift `seamClockPotential_drift_affine_honest` with
  `b = 2·(eˢ·freshVal)`, via generic-immigration clones reusing the public lintegral pair-sum engine.
- Stage 4 (1d347fad): HONEST numerics `seam_noOvershoot_numerics_honest` (immigration `2·e·e^{−50(L+1)}`)
  STILL closes to `e^{−40(L+1)}` (predecessor optimism VERIFIED, no weakening); end-to-end
  `seam_atRiskClockZero_tail_honest` / `seam_noOvershoot_tail_honest` / `hNoOvershoot_one_seam_honest`
  plug into the SAME `seamEpidemicExactW` integration point.

Honest two-sided constant: `2·eˢ·freshVal`. Numerics landed: `e^{−40(L+1)}`. Excluded destinations
`{2,4,9}` (untimed) and `{3,5}` (no counter reset on entry) handled by named per-phase guards
(CounterResetDest excludes them; width/work-phase machinery owns their no-overshoot), not faked.

### KilledTailConsumers Deliverables 2 & 3 completion record (2026-06-10, resumed line)
`Probability/KilledTailConsumers.lean` Deliverables 2 (Gap-2 / Phase-0 window) and 3 (εmid) landed
(commits d09a2b74, bd3b8e96), append-only on top of predecessor's Deliverable 1 (top-split tail,
b94a951d). Single-file `lake env lean … KilledTailConsumers.lean` EXIT 0; every headline
`#print axioms ⊆ [propext, Classical.choice, Quot.sound]`; 0 sorry/admit/axiom/native_decide.

- **Deliverable 3 (εmid FINAL form):** `FloorPrefix.midBand_floorFail_prefix_floorMasses` — the
  mid-band floor-failure prefix ≤ aggregate GENUINELY-DECAYING contractive killed tail (`rᵗ`,
  `r = floorMassesRate < 1`) + aggregate gate-exit escape. Wires `FloorMasses.
  pool_expNeg_one_step_drift_floorMasses` (s=1/10, b=0, proven-`<1` favorability) through
  `KilledAffineTail.midBand_real_contractive_tail` per step (threshold link
  `floorFail_subset_poolExpNeg_thresh`: `{pool<a₀} ⊆ {exp(-s·a₀) ≤ poolExpNeg s}`). FINDING 3
  (the `1 ≤ r` blocker) fully discharged into an εmid headline. FloorMasses region hypotheses
  (`uMin ≤ freshMcrCount`, drain-block `Sblk`/`hSstep`/`hblock`) kept EXPLICIT where protocol-open.

- **Deliverable 2 (Gap-2 / Phase-0 window):** `phase0_killed_window_unconditional` — the strongest
  UNCONDITIONAL killed-side window. The leading drift term VANISHES at `Phase0Initial` because every
  agent is RoleMCR ⟹ `Φ_clock(c₀)=0` (`clockCounterPotential_eq_zero_of_allMcr`), so the killed
  surviving-trajectory clock-zero mass is governed PURELY by fresh-clock immigration
  `b·∑aⁱ` — no absorbing Q, no hτ, no escape reachability. Numerically-closed form
  `phase0_killed_window_unconditional_closed`. The genuine Gap-2 residual is precisely isolated:
  `gap2_allPhase0_window_whp_of_reachability` shows Gap-2 reduces to `Gap2_reachability_target`
  (the absorbing-drift-region maintenance in the role-split layer), NOT an engine gap — the killed
  formalism relocates the reachability need (escape = real side masses, non-contracting recursion
  since `{¬noClockAtZero} ⊆ {1≤Φ_clock}`), it does not remove it.

### Phase E4 completion record (2026-06-10, expected-time half of Theorem 3.1)
Probability/DotyExpectedTime.lean COMPLETE (Stages 1–4; append-only, no edit to any existing
file). Single-file `lake env lean … DotyExpectedTime.lean` EXIT 0, zero warnings; all 7 headlines
`#print axioms ⊆ [propext, Classical.choice, Quot.sound]`; 0 sorry / 0 admit / 0 axiom / 0 native_decide.

Honest conditioning-free shape (per ChatGPT-Pro blueprint HANDOFF_E4_EXPECTED_TIME.md): the start
`c₀` is deterministic in the kernel formalism, so NO conditional-expectation split. Instead
`E[T] ≤ Tgood + δgood·sRecover·(1−q)⁻¹` via E1's `expectedHitting_split_geometric`, with the
good/bad classification pushed INSIDE the recovery cap.

- Stage 1 (2b9f0986): `block_half_from_recovery_expected` (= E1 `bad_le_half_of_expectedHitting`
  lifted uniform-over-`Doneᶜ`) + `expected_time_from_whp_and_recovery` (= E1
  `expectedHitting_split_geometric` at `q = 1/2`). Pure ExpectedHitting compositions, no protocol content.
- Stage 2 (2b9f0986): `StableDone` + `RecoveryClass` (4-way disjunction
  bigClockTimed/tinyClockTimed/phase10Majority/phase10Tie) + `doty_recovery_expected_bound`.
  Each `RecoveryClass` branch carries its `expectedHitting … StableDone ≤ B` witness as EXPLICIT
  constructor data — because the E2/E3 wrappers land on PROGRESS sets
  (`Engine.potBelow (clockCounterSumAt p) 1`, `potBelow wrongACount 1`), and the transfer
  progress-set ⟹ StableDone is the documented protocol residual. `hClassify` (deterministic
  classification of arbitrary reachable not-done states) stays a named hypothesis.
- Stage 3 (2b9f0986): `doty_expected_time` — top-level assembly against the REAL
  `doty_time_headline_W2` interface. `hhead.1` (whp bad-set mass `≤ 1/n`) and `hhead.2`
  (`Tgood ≤ 21·C0·n·(L+1)`) destructure cleanly; the headline's bad set
  `{c | ¬ majorityStableEndpoint init c}` is defeq to `(StableDone)ᶜ` (rfl via `compl_StableDone`).
- Stage 4 (2b9f0986): `doty_harith_concrete` + `doty_expected_time_concrete` — concrete corollary
  with `Cexp = 21·C0 + 4·Cbad`, `sRecover = 2·Brecover`. Recovery contribution
  `(1/n)·(2·Brecover)·2 = 4·Brecover/n`; the single open numeric side condition
  `4·Brecover/n ≤ 4·Cbad·n·(L+1)` is the EXPLICIT hypothesis `hrecmass` (blueprint §3 estimate).

Blueprint-vs-repo signature drift recorded: (a) `doty_time_headline_W2` uses `(phases lastPhaseW2)`
(private `lastPhaseW2 := ⟨21-1, _⟩`) in `h_post`; the blueprint's `⟨21-1, by omega⟩` is defeq (Fin
proof irrelevance), used verbatim. (b) E3 wrappers are named
`timed_phase_progress_real_bigClock/_tinyClock` and conclude on `Engine.potBelow (clockCounterSumAt p) 1`,
NOT on `StableDone` — hence the carried-witness design of `RecoveryClass`. (c) E2 stabilization
headlines (`phase10_expected_stabilization_O_nsq_log`, tie analogue) live in
`ExactMajority.Phase10Drop`, S1/Tie1plus there. (d) The blueprint `set K0`/`set Tgood` in
`doty_expected_time` rewrites inside `phases`'s kernel-indexed type (`phases✝` mismatch); fixed by
computing `hhead` before any abbreviation and inlining the kernel.

## GAP-2 CLOSED — the first-escape decomposition (2026-06-10, single line)

New file `Probability/Gap2Reachability.lean` (append-only; no existing file edited; imports
`KilledTailConsumers`). Single-file `lake env lean` EXIT_0 on uisai2 (/dev/shm, v4.30.0). All
five headlines `#print axioms ⊆ [propext, Classical.choice, Quot.sound]`; 0-sorry, 0-axiom, no
native_decide.

**The residual the predecessor isolated** (`KilledTailConsumers` Deliverable 2) was
`Gap2_reachability_target`: a uniform per-σ bound on the REAL clock-zero prefix masses
`(K^σ) c₀ {1 ≤ Φ_clock}`. The predecessor's note found the killed engine's escape bound
`escape_le_threshold_prefix` self-referential — it charges escape at horizon τ to
`∑_{σ<τ} (K^σ) c₀ {1 ≤ Φ}`, the SAME REAL masses (`{¬noClockAtZero} ⊆ {1 ≤ Φ}`), so the
recursion does not contract.

**The fix (this file): the KILLED-prefix escape bound.** The cemetery mass is GENERATED by
the surviving (killed) trajectory: the per-step cemetery increment is the killed alive mass
at step σ times the one-step exit probability, and exit — by the deterministic bridge
`phase0Gate_exit_bridge` (`det_phase0_exit`) — requires `1 ≤ Φ` AT THE LAST ALIVE STATE,
which is a KILLED-chain state. Hence

  `(killK_now^M)(some x₀){none} ≤ ∑_{σ<M} (killK_now^σ)(some x₀){θ' ≤ killΦ Φ}`

(`killed_escape_le_killed_threshold_prefix`, generic in `GatedDrift`) — the **killed**-prefix
analogue of the campaign's real-prefix `escape_le_threshold_prefix`. Same immediate-kill
induction as `kill_now_escape_le_prefix_union`, but the per-step exit increment telescopes
through `killK_now` (NOT `K`), so the prefix is killed threshold masses. These genuinely
decay (`phase0_killed_window_unconditional`: `Φ_clock(c₀)=0` at the all-MCR start collapses
each to the pure-immigration budget `b·∑aⁱ`), so the sum is a finite sum of decaying budgets
— the contraction the real-prefix bound lacked.

**Deliverables (all axiom-clean, EXIT_0):**
- `GatedDrift.killed_escape_le_killed_threshold_prefix` — the killed-prefix escape (the missing
  engine piece). `GatedDrift.real_le_killed_threshold_add_escape` — `real{θ≤Φ} ≤
  killed{θ≤killΦ} + escape` (union split stopped before the affine envelope).
- `Phase0Window.gap2_real_bad_le_killed_threshold_prefix` — the first-escape decomposition:
  `(K^τ) c₀ {1≤Φ_clock} ≤ ∑_{σ≤τ} killed{1≤killΦ at σ}`, NO self-reference.
- `Phase0Window.gap2_reachability_target_discharged` — **`Gap2_reachability_target` PROVEN**
  at `ε(t) = (t+1)·b·∑_{i<t}aⁱ`, hypothesis surface `Phase0Initial n c₀` + arithmetic.
- `Phase0Window.allPhase0_window_unconditional` — **the capstone**, fed through the campaign's
  conditional close `gap2_allPhase0_window_whp_of_reachability`:
    `(K^t) c₀ {¬allPhase0} ≤ t·(t+1)·b·∑_{i<t}aⁱ`,  `b = ofReal(e^{−s·50(L+1)})`,
    `a = ofReal(1+2(eˢ−1)/n)`, hypothesis surface = `Phase0Initial n c₀` + `0≤s` + `2≤n` ONLY.
  Gap-2's reachability/maintenance residual is GONE — relocated by the killed formalism and now
  ELIMINATED by the first-escape decomposition.

**Numerics landing:** the budget is the honest pure-immigration form `t·(t+1)·b·∑_{i<t}aⁱ` with
`b = e^{−s·50(L+1)}` (a clock at counter 0 = a Rule-4 fresh clock at full counter `50(L+1)`
drained down, charged per step). At `s=1`, `b = e^{−50(L+1)}`; the `e^{−45(L+1)}`-flavoured
campaign target follows by the geometric-sum closure (`∑aⁱ ≤ t·e^{2(e−1)(L+1)}`-scale absorbed
into the `t·(t+1)` prefactor), supplied as the explicit numeric input where the conditional
route used it. The closed-form headline is left in the explicit `b·∑aⁱ` shape so downstream
consumers pick the exact prefactor; no exponent was weakened to close — the closure is the
exact decomposition, not an estimate.

---

## E4 RecoveryBridges — seqcomp engine + telescope + honest hClassify (append-only)

`Probability/RecoveryBridges.lean` (append-only; imports `DotyExpectedTime`) attacks the
two `DotyExpectedTime` residuals. Single-file EXIT 0; 9 headlines axiom-clean ⊆
`[propext, Classical.choice, Quot.sound]`; 0 sorry/admit/axiom/native_decide.
Commits: `da04fda5` (S1), `76901cc1` (S2), `0330a8c8` (S3), `f58c45d8` (S4).

- **S1 seqcomp cap.** `expectedHitting_seqcomp : E[T→Done] ≤ E[T→Mid] + sup_{Mid}E[T→Done]`
  collapses the existing band tower (`Phase10ExpectedTime.expectedHitting_le_through_mid`)
  with the existing band occupation (`occupation_mid_le`/`_on`). The engine partly
  existed; the collapsed uniform form (+ `_of_uniform`, `_on`, hypothesis-free
  `expectedHitting_le_band_free`) was new.
- **S2 clock preservation.** `AllClockGEpCard p n` (post-role-split: all-clocks-at-phase-≥p,
  card n) one-step support closed → a.e. preserved for all kernel time
  (`allClockGEpCard_pow_preserved`). NOT a property of arbitrary reachable states.
- **S3 telescope.** `expectedHitting_ladder_le` / `expectedHitting_telescope_from_start`:
  iterated seqcomp down a ladder to an absorbing `Done` gives `E[T→Done] ≤ ∑ β j` — the
  progress-set ⟹ StableDone transfer, deriving each RecoveryClass cap from E3/E2 facts.
- **S4 hClassify + final surface.** `recoveryClass_of_ladder` derives the RecoveryClass
  witness (theorem, not data); `doty_recovery_bound_via_ladder` reduces the recovery cap
  to `hLadder` (every not-done state starts a bounded ladder), strictly weaker than the
  carried `hClassify`. `doty_expected_time_via_ladder` is the final E4 surface (same
  `(21·C0+4·Cbad)·n·(L+1)` bound, recovery cap supplied not assumed). The sole remaining
  protocol residual is `hLadder` = deterministic phase-regime classification of reachable
  not-done states + per-phase clock floors (whp via Lemma 5.2, not a deterministic
  invariant). Everything above it is discharged.

---

## SeamOvershootBridge (2026-06-10): `DetSeamOvershootBridge p` discharged under `W`

New append-only file `Probability/SeamOvershootBridge.lean` PROVES
`SeamNoOvershoot.DetSeamOvershootBridge p` (the deterministic first-overshoot guard the
seam no-overshoot chain carried as `hdet`) for counter-reset destinations
`p+1 ∈ {1,6,7,8}`, under the minimal well-formedness side condition
`W = WfAgent (no mcr + smallBias ∈ {2,3,4})` — the condition the obstruction
(`HANDOFF_SEAM_NOOVERSHOOT.md` finding 2: `phaseInit 1` sends `mcr` to phase 10) requires.

* `det_seam_overshoot_bridge_of_wf` — bridge under `Wf c`.
* `detSeamOvershootBridge_of_wf` — wire-up: `(∀ c, Wf c) → DetSeamOvershootBridge p`.
* `hNoOvershoot_one_seam_wf` — budget wrapper with the bridge eliminated.

`W` is one-step preserved on the seam region and its provenance is the phase-0 EXIT
(`RoleSplitConcentration.RoleSplitStage2Good`: `mcr = 0`).  Honest per-phase `+1` bounds for
phases `0–8` (both sides), epidemic no-error identity, dispatcher bound, advance
characterization, and source-tracing — all 0-sorry, axiom-clean
(`[propext, Classical.choice, Quot.sound]`), no `native_decide`.  The residual seam
no-overshoot surface is now: timing/initial-potential + seam-region `Wf` (from the Analysis
reachability invariants) + `CounterResetDest (p+1)` + arithmetic; `DetSeamOvershootBridge p`
is no longer an assumption.

---

## Phase D — composition residual: per-phase floor wiring (`Probability/PhaseFloors.lean`, NEW)

The Phase-D composition residual queue item ("wire prior-phase Posts into per-phase numeric
floors") is delivered.  `DrainThreading` (D-7) gave each of the five drain phases an engine
`hdrop` carrying ONE structural count floor as a NAMED hypothesis; this file supplies each floor
from its provenance source's Post (where landed) or from the named missing theorem (where the
provenance count lower bound is not yet landed), and re-delivers the `hdrop` with the floor wired.

NEW append-only file `Probability/PhaseFloors.lean` (namespace `ExactMajority.PhaseFloors`;
touches only this new file).  All 7 theorems 0-sorry, 0-native_decide,
`#print axioms ⊆ [propext, Classical.choice, Quot.sound]` (verified per-theorem).  Single-file
`lake env lean` EXIT_0.

### The five-phase wiring table

| phase | floor (DrainThreading hyp)              | floor source theorem (provenance)                                     | seam transport (attr the seam doesn't touch)      | wired instance / status |
|-------|-----------------------------------------|------------------------------------------------------------------------|---------------------------------------------------|-------------------------|
| **6** | `K₀ ≤ reserveAtHour6 i .sum count`      | **LANDED**: Phase-5 Post `ReserveSampleGood i K₀` ⇒ `sampledFloor i K₀` = `K₀ ≤ sampledReserveClassU i`; `reserveAtHour6_sum_eq_classU` (= at `h:=i`) | `countP(role=reserve ∧ hour=i)` — advance epidemic changes only `phase`; Reserve `role`/`hour` (sampled record) phase-advance-invariant | **`phase6_hdrop_wired`** — FULLY WIRED (R:=K₀ from chain, no carried R). Floor extraction `phase6_reserve_floor_of_phase5Post`. |
| **1** | `P ≤ pullPosSet .sum count` (+`1≤extremePosSet`) | **PARTIAL**: RoleSplit Lemma 5.2 `mainCount_lower_of_RoleSplitGood` (`n/3 ≤ mainCount`); genuine adapter `mainCount_eq_pullPos_add_saturatedPos` (`mainCount = pullPosSet + saturatedPosSet`). **Missing link**: saturated-positive-side bound `saturatedPos ≤ n/3 − P`. | `countP(role=main ∧ smallBias≤4)` — same-phase work transition preserves (Phase-1 averaging keeps role; only `smallBias` averaged) | **`phase1_hdrop_wired`** — ADAPTER from named floor `P ≤ pullPosSet`. Main-decomposition reduces missing link to saturated-side bound. |
| **5** | `P ≤ usefulMains .sum count` (+`1≤unsampledReserves`) | **NOT LANDED**: Theorem 6.2 `biasedMainLtL ≥ 0.92·mainCount ≥ 23n/75` — referenced in `DrainCalibration`/`ReserveSampling` doctrine, carried, never proven. | `countP(biasedMainLtL)` — `biasedMainClass` phase-5-conserved (`biasedMainClassU_support_eq`) | **`phase5_hdrop_wired`** — ADAPTER from named missing floor `P ≤ usefulMains` (Thm 6.2 output, `P:=⌈23n/75⌉`). |
| **7** | `E ≤ elimGap1 σ i .sum count` (+`1≤minorityAt7 σ j`) | **NOT LANDED**: Lemma 7.4 `0.8·mainCount` eliminator majority — the landed `lemma_7_5_phase_seven_minority` is a whp minority-SURVIVAL upper bound, NOT an eliminator lower bound. | gap-1 eliminator `countP` — same-phase | **`phase7_hdrop_wired`** — ADAPTER from named missing floor `E ≤ elimGap1` (Lemma 7.4 output). |
| **8** | `E ≤ elimAbove σ i .sum count` (+`1≤minorityAt σ i`) | **NOT LANDED**: Lemmas 7.4–7.6 eliminator margin (`0.8|M|` − `0.2|M|`) — landed `lemma_7_6_phase_eight_eliminates` is a whp minority-survival upper bound. | `elimAbove`/`minorityAt` `countP` — same-phase | **`phase8_hdrop_wired`** — ADAPTER from named missing floors `E ≤ elimAbove` + `1 ≤ minorityAt` (Lemmas 7.4–7.6 output). |

### Status summary

- **1 of 5 floors FULLY WIRED** (Phase 6): the only phase whose provenance count lower bound is a
  landed theorem (the Phase-5 `Post`'s `sampledFloor` conjunct).  The reserve floor flows from the
  prior phase's actual Post with no carried numeric input.
- **4 of 5 ADAPTER-PENDING** (Phases 1/5/7/8): the provenance count lower bounds (RoleSplit
  `mainCount` → `pullPos` count-shape; Theorem 6.2 biased-Main; Lemma 7.4–7.6 eliminator) are NOT
  landed as count lower-bound theorems.  Phase 1 has the genuine Main-decomposition adapter
  reducing its gap to the saturated-side bound; Phases 5/7/8 deliver the `hdrop` from the named
  missing floor hypothesis (no faking).  The precise missing links:
  - Phase 1: `saturatedPosSet .sum count ≤ n/3 − P` (saturated `+2/+3` side small — driven down by
    Phase-1 averaging, cf. `extremeU` non-increase).
  - Phase 5: Theorem 6.2 biased-Main concentration `⌈23n/75⌉ ≤ usefulMains .sum count`.
  - Phase 7: Lemma 7.4 `E ≤ elimGap1 σ i .sum count` (`0.8·mainCount` eliminator floor).
  - Phase 8: Lemmas 7.4–7.6 `E ≤ elimAbove σ i .sum count` (eliminator margin).

**Commit** (pushed to origin main): `Doty Phase-D PhaseFloors: wire prior-phase Posts into
per-phase drain floors`.

---

## Theorem 6.2 useful-Main floor (Phase-5 entry) — DELIVERED 2026-06-10

NEW append-only file `Probability/UsefulMainFloor.lean` (namespace
`ExactMajority.UsefulMainFloor`; touches only this new file). Delivers the highest-leverage
missing count floor of the four-floors handoff: the Phase-5 `usefulMains ≥ P` floor consumed by
`PhaseFloors.phase5_hdrop_wired` (`hmain : P ≤ usefulMains.sum count`).

Single-file `lake env lean` EXIT_0. All 5 headlines axiom-clean
(`#print axioms ⊆ [propext, Classical.choice, Quot.sound]`); 0 sorry/admit/axiom/native_decide.

### Provenance audit — no landed export confines Main exponents

| candidate source | what it carries | confinement count? |
|---|---|---|
| `ReserveSampling.Phase5AllWin n c` | `card = n ∧ ∀ a, phase = 5` (pure phase window) | NO — no bias/exponent profile |
| Phase-3/4 `Post` (`advFinished`/`StableTie4`) | `phaseBelowCount 5 = 0` / `noBigBias` for ALL (tie = OPPOSITE extreme, all at cap index `= L`) | NO — Thm 6.2 is the non-tie branch |
| `mainCount_lower_of_RoleSplitGood` | `n/3 ≤ mainCount` (Lemma 5.2 role split) | NO — silent on exponent distribution |
| §6 width machinery (`ClockFrontProfile`/`WidthTransport`/`CrossHourSide`/`FrontTailDecay`) | CLOCK minute-front concentration `O(log log n)` (Thm 6.5/6.9/6.12) | NO — clock field, not Main bias-exponent count (it is the enabling mechanism, not the count) |

Genuine attack (documented in file header): deriving `0.92·|M| ≤ #usefulMains` from the landed
clock-front exports alone is not possible — it requires the full Phase-3 bias-ledger collapse
(Thm 6.5 `c≥(i+1) < p·c≥i²` squaring applied to the *Main* exponent profile, plus the
total-mass-above `µ(>−l) ≤ 0.002|M|2^{−l}` and minority-mass `β⁻ ≤ 0.004|M|2^{−l}` bounds,
union-bounded over `O(log n)` hours). That inductive collapse is the genuinely-new probabilistic
content of Theorem 6.2.

### Closed vs carried

- **CLOSED (proven, axiom-clean):**
  - `main_iff_useful_or_satExp` — a Main is exactly `biasedMainLtL` (index `< L`) xor
    `satExpMain` (unbiased / cap index `= L`).
  - `usefulMains_satExpMains_disjoint`, `mainCount_eq_usefulMains_add_satExp` — the genuine Main
    decomposition `mainCount = #usefulMains + #satExpMains` (Phase-5 analogue of
    `PhaseFloors.mainCount_eq_pullPos_add_saturatedPos`).
  - `theorem6_2_usefulMains_floor` — the blueprint-shape headline: from `Theorem62EntryHypotheses`
    + `(P ≤ 23n/75)`, conclude `P ≤ #usefulMains`, via `23n/75 = 0.92·(n/3) ≤ 0.92·|M| ≤ #usefulMains`.
- **CARRIED (ONE named fact, paper provenance):** the Theorem-6.2 confinement
  `0.92·|M| ≤ #usefulMains`, as the `hConfine` field of the `structure Theorem62EntryHypotheses`
  (other fields `hPhase5`, `hMainFloor` are the landed chain facts). Provenance:
  arXiv:2106.10201v2 Theorem 6.2 — `|M'| ≥ 0.92|M|` whp `1−O(1/n²)`, where
  `M' = {majority Mains at exponents −l,−(l+1),−(l+2)} ⊆ usefulMains` since the confined exponents
  `l, l+1, l+2` are all `< L`.

### Wired adapter

`phase5_hdrop_wired_from_theorem6_2` supplies the `PhaseFloors.phase5_hdrop_wired` floor directly
from `Theorem62EntryHypotheses` + `P ≤ 23n/75`. The blueprint's `Theorem62EntryHypotheses`
placeholder is now a concrete `structure`, with the chain mapping documented in the file header.

## Phase-7/8 eliminator-margin floor package (`Probability/EliminatorMargins.lean`, NEW) — DELIVERED 2026-06-10

Per `HANDOFF_FOUR_FLOORS.md` §3/§4. New append-only file; no existing file edited.
Single-file `lake env lean Probability/EliminatorMargins.lean` EXIT_0; all 9 headlines
`#print axioms` ⊆ `[propext, Classical.choice, Quot.sound]`; 0 sorry/admit/axiom/native_decide.

### Group 1 — deterministic minority-witness adapters (priority 1, fully closed)

- `exists_minorityAt_of_minorityU_pos` (Phase 8): `1 ≤ minorityU σ c ⟹ ∃ i, 1 ≤ minorityAt σ i .sum count`.
  Pure `Multiset.countP_pos` witness extraction (unfold `minorityU`, take the witness exponent `i`,
  the witness agent lands in `minorityAt σ i` with `count ≥ 1`).
- `exists_minorityAt7_of_minorityU_pos` (Phase 7 count form): same extraction targeting `minorityAt7`.
- `exists_minorityAt7_of_classMassN_pos` (Phase 7 MASS form): the form the Phase-7 drain actually
  consumes (the drain drives `classMassN σ → 0`, the count can RISE under a gap-2 fire). From
  `Phase7AllMain` + `classMassN σ c ≥ 1`, the class-mass ledger gives a positive-mass agent
  (`agentClassMass ≥ 1 ⟹ bias = dyadic σ i`); the window forces `role = main`, so it witnesses
  `minorityAt7 σ i`. Helper `bias_dyadic_of_agentClassMass_pos`.
- `phase1_pullPos_floor_of_mainCount_and_saturated_bound` (Phase 1 arithmetic wrapper): pure ℕ
  `omega` from the landed `PhaseFloors.mainCount_eq_pullPos_add_saturatedPos` — from
  `P + #saturatedPos ≤ mainCount` conclude `P ≤ #pullPos`. Reduces the missing link to the
  saturated-side bound (the remaining Phase-1 averaging burden, named in HANDOFF §1).

### Group 2 — eliminator-margin structures + floor lemmas (priority 3)

Provenance audit (verified against the actual theorems, matching the `PhaseFloors` audit): the
landed `Analysis/Invariants.lemma_7_5_phase_seven_minority` / `lemma_7_6_phase_eight_eliminates`
are minority-survival/absorbing UPPER bounds (whp `1−O(1/n²)` that no minority survives), NOT
eliminator-count LOWER bounds. So the eliminator floors `elimGap1 ≥ E` / `elimAbove ≥ E` are
genuinely not derivable from a landed Post.

Per discipline ("define the predicate honestly, prove what IS derivable, carry the precise
remainder named"):

- `Phase6To7Structure σ E c` / `Phase7To8Structure σ E c` are honest carriers of EXACTLY the
  Doty Lemma-7.4 / 7.6 eliminator margin (the precise named remainder):
  - `Phase6To7Structure`: every minority level `j` (`1 ≤ #minorityAt7 σ j`) has a gap-1 partner
    level `i = j−1` with `E ≤ #elimGap1 σ i`.
  - `Phase7To8Structure`: every minority level `i` (`1 ≤ #minorityAt σ i`) has `E ≤ #elimAbove σ i`
    (non-`full` σ-eliminators strictly above).
- `lemma7_4_phase7_elimGap1_floor` (blueprint §3 shape): from `Phase7AllMain` + `Phase6To7Structure`
  + `classMassN σ c ≥ 1`, derives the full existential `∃ i j, i+1=j ∧ 1 ≤ #minorityAt7 σ j ∧
    E ≤ #elimGap1 σ i`. The minority-witness half is PROVED (Group 1 mass-form witness); the
    eliminator half is the carried structure field.
- `lemma7_6_phase8_elimAbove_floor` (blueprint §4 shape): from `Phase7To8Structure` at a given
  minority level `i`, conclude `E ≤ #elimAbove σ i`. (The `minorityAt ≥ 1` witness for the level
  comes from Group 1's `exists_minorityAt_of_minorityU_pos`.)

The paper-constant real bounds (`E ≤ 4n/15`, `E ≤ n/5`) are carried as documenting hypotheses.

### Group 3 — wiring adapters (blueprint exact shapes)

- `phase7_hdrop_wired_from_lemma7_4`: repackages the existential gap-1 floor into
  `PhaseFloors.phase7_hdrop_wired`.
- `phase8_hdrop_wired_from_lemma7_6`: repackages the existential above-level floor into
  `PhaseFloors.phase8_hdrop_wired`.

### Closed vs the precise named remainder

- **CLOSED (proven, axiom-clean):** all four Group-1 deterministic adapters; both Group-2 floor
  lemmas' minority-witness halves; both Group-3 wirings; the helper lemmas. The Phase-7/8 drop
  rectangles were already landed (`phase7/8_drop_floor_of_struct` in `DrainThreading`), so no new
  transition-probability content was needed — confirming the blueprint's "count-structure theorem,
  rectangle already landed" classification.
- **CARRIED (precise named remainder):** the eliminator-count LOWER bounds themselves — the
  `Phase6To7Structure` gap-1 margin (`E ≤ #elimGap1 σ (j−1)` at each minority level `j`) and the
  `Phase7To8Structure` above-level margin (`E ≤ #elimAbove σ i` at each minority level `i`). These
  are the Doty Lemma 7.4 `0.8·|M|` / Lemma 7.6 `0.8|M|−0.2|M|` eliminator-majority floors, which
  no landed Post exports (the landed Lemmas 7.5/7.6 are survival upper bounds). They are now
  honest named predicate fields, not faked.

---

## 2026-06-10 — Three cores Brick 0 + B + C (`Probability/MarginLedgers.lean`)

New append-only file delivering the shared exponent-profile algebra (Brick 0) and the B/C
deterministic eliminator-margin ledgers, per `HANDOFF_THREE_CORES.md`. Single-file `lake env lean`
EXIT_0; all headlines axiom-clean `[propext, Classical.choice, Quot.sound]`; no
sorry/admit/axiom/native_decide. Three commits (cffb4662 Brick 0, a3650f55 Brick B, ed65736e
Brick C), each pushed to `main` + mirrored to `xiangyazi24/Ripple opus-wip`.

* **Brick 0 (fully closed).** `mainAtExp`/`majorityAtExp`/`minorityAtExp` + `main_profile_partition`
  (`mainCount = majorityProfileMass + minorityProfileMass + zeroMainCount`). `mainAtExp` is
  definitionally `Phase7.minorityAt7` and `Phase8.minorityAt`. Flat ↔ per-exponent profile-mass
  bridge via `Finset.sum_biUnion` fibered over the bias exponent. Zero carried fields.
* **Brick B (ledger closed; 1 carried field).** `phase6_to_phase7_eliminator_margin_of_confinement`
  fills `EliminatorMargins.Phase6To7Structure σ E c` for `E ≤ 4n/15` from `MainConfinementProfile`
  (0.92 / 0.12 / n/3) + `Phase6Win` + carried `Phase6HighMassDrained`. The GLOBAL budget
  `majorityProfileMass ≥ 4n/15` is PROVED (`majorityProfileMass_floor`, the 0.92−0.12 = 0.8,
  0.8·n/3 = 4n/15 residue ledger over Brick 0's partition). Only the per-level gap-1 routing is
  carried (the eliminator LOWER bound the landed survival-UPPER Posts omit).
* **Brick C (ledger closed; 1 carried field).** `phase7_to_phase8_eliminator_margin_of_phase7`
  fills `EliminatorMargins.Phase7To8Structure σ E c` for `E ≤ n/5` from B's Phase-7-entry margin
  (`c_start`) + `Phase7AllMain` + carried `Phase7SurvivalUpperBounds`. Real attack on FROZEN
  `cancelSplit`: same-level cancel is the ONLY eliminator loss; gap-1 increments/preserves; gap-2
  preserves/grows the σ-opposite supply. `lemma_7_5/7_6` are survival-UPPER (absorbing zero-mass),
  not eliminator LOWER bounds, so the surviving above-level count is carried as ONE precise named
  field after the attack.

B/C outputs `#check`-verified to be the exact `EliminatorMargins.Phase6To7Structure` /
`Phase7To8Structure` consumer shapes; existing adapters consume them unchanged. Constants verified:
0.92, 0.12, 0.8, 4n/15 = 0.8·(n/3), n/5. Brick A (Theorem 6.2 confinement) stays carried in
`UsefulMainFloor.hConfine`.

## Phase-1 averaging collapse floor (`Probability/AveragingCollapse.lean`, NEW) — DELIVERED 2026-06-10

The last of the four floors (`HANDOFF_FOUR_FLOORS.md` §1). The Phase-1 saturated-side floor: whp
over the Phase-1 window the saturated-positive Mains (`smallBias.val ≥ 5`) stay `≤ n/3 − P`, so
`pullPosSet ≥ P` via the landed `PhaseFloors.mainCount_eq_pullPos_add_saturatedPos` and the wrapper
`EliminatorMargins.phase1_pullPos_floor_of_mainCount_and_saturated_bound`.

NEW file, append-only; no existing file edited. Single-file `lake env lean` EXIT_0; every headline
`#print axioms ⊆ [propext, Classical.choice, Quot.sound]`; no sorry/admit/axiom/native_decide.
Four stages, one commit each.

### The honest self-contained route (no [45] import): second-moment contraction

The paper imports the quantitative collapse to `{µ−1,µ,µ+1}` from reference [45] wholesale. Instead
of formalizing [45]'s variance-decay argument, we use the genuine mechanism the blueprint pointed
at ("a cosh/variance contraction potential"). The FROZEN `avgFin7` rule
(`Protocol/Transition.lean`) replaces two Mains' `smallBias` values `x,y : Fin 7` by
`(⌊(x+y)/2⌋, ⌈(x+y)/2⌉)`.

**The exact per-rule integer ledger** (computed over all 7×7 = 49 pairs, both parities; centred at
the encoding origin 3 where `smallBiasInt = v − 3`):

- sum preserved: `x' + y' = x + y`;
- centred second moment drops by EXACTLY `⌊(x.val − y.val)²/2⌋`:
  `(x−3)² + (y−3)² − (x'−3)² − (y'−3)² = ⌊(x−y)²/2⌋ ≥ 0`.
  Even parity: drop `= (Δ)²/2`. Odd parity: drop `= ((Δ)²−1)/2`. (The centred drop equals the raw
  `Σ v²` drop because the linear term cancels under the preserved sum.)

So `Φ = secondMomentN = Σ_{phase-1 Mains}(smallBias.val − 3)²` is **deterministically**
non-increasing under every averaging interaction — the variance literally never rises. This is a
per-step ℕ-monotone (NOT merely a supermartingale in expectation), so it plugs straight into the
SAME `OneSidedCancel` level engine that `Phase1Convergence` already uses for `extremeU`. Which
potential worked: **the plain centred second moment**; no cosh / exponential change of variable was
needed because the contraction is already a deterministic ℕ-monotone.

### The saturated-count conversion (fully proved, exact) — and why µ is irrelevant

A saturated-positive Main has `smallBias.val ≥ 5`, hence `(smallBias.val − 3)² ≥ 4`
(`sqDist3N_ge_four_of_saturated`). Summing, `4·#saturatedPos ≤ secondMomentN`
(`four_mul_saturatedPos_le_secondMoment`). So `secondMomentN ≤ 4·(n − P)` forces
`#saturatedPos ≤ n − P`. The blueprint's design question (a) "what IS the mean µ" **dissolves**:
centring at the fixed encoding origin 3 already gives squared distance `≥ 4` for every saturated
value, regardless of the true mean — no mean estimate, no `Phase1Convergence.Pre`/initialGap
reasoning needed. (Design question (b) "two clusters at distance 1 stall the variance" is also moot
here: the saturated side only needs distance from a FIXED center 3, and distance-1 odd-sum pairs DO
move mass via floor/ceil, consistent with the exact `⌊(x−y)²/2⌋` drop — but the floor argument never
relies on a variance-drop RATE, only on the deterministic non-increase + the carried drain rate.)

### The four stages

1. (`avgFin7_sqDist3_pair_le` / `avgFin7_sqDist3_pair_drop`) the exact Fin-7 second-moment ledger,
   both parities, by exhaustive `decide`. `sqDist3N v := (if v.val ≤ 3 then 3 − v.val else
   v.val − 3)²`.
2. (`secondMomentN`, `potNonincrOn_secondMomentN`) the config potential and its deterministic
   one-step `PotNonincrOn` on the `Phase1AllMain` window — reduces each interaction to
   `Phase1Convergence.Transition_eq_avg_of_phase1_main` then applies the per-pair ledger; lifted to
   the kernel exactly as `extremeU_stepOrSelf_le` / `potNonincrOn_extremeU`.
3. (`four_mul_saturatedPos_le_secondMoment`, `saturatedPos_le_of_secondMoment_le`,
   `secondMoment_level_tail`) the saturated-count conversion + the whp tail through the landed
   `OneSidedCancel.level_tail` (potential non-increasing on a closed window, carried per-level drain
   rate `q`): `(K^t) c {secondMomentN ≥ m}ᶜ-complement ≤ (q m)^t`.
4. (`mainCount_eq_n_of_window`, `phase1_pullPos_floor_of_secondMoment_le`,
   `phase1_pullPos_floor_whp`) the wired floor. On the window `mainCount = card = n`; the "good"
   event `{secondMomentN ≤ 4(n−P)}` deterministically gives `P ≤ pullPosSet` via the wrapper; the
   failure event `{¬ P ≤ pullPosSet}` is covered by `{¬window} ∪ {secondMomentN ≥ 4(n−P)+1}`, the
   first having `0` mass (window closure), the second `≤ (q m)^t` (stage 3 tail).

### Carried remainder (exactly one named atom, paper provenance)

The per-level second-moment drain rate `q : ℕ → ℝ≥0∞` (the `hdrop` hypothesis of
`secondMoment_level_tail` / `phase1_pullPos_floor_whp`). This is the SAME atom
`Phase1Convergence.phase1Convergence` carries for `extremeU`: the per-interaction probability that a
distant pair averages strictly inward, `≥ (pair count)/(n(n−1))`-shape, the quantitative content the
paper imports from reference [45] (Mocquard et al., discrete averaging, Corollary 1). Exposed as a
hypothesis exactly as Phases 1/7/8 expose theirs; everything STRUCTURAL around it (the ledger, the
deterministic non-increase, the conversion, the tail, the wiring) is discharged 0-sorry.

Commits: stage 1 `03ecd031`, stage 2 `83557382`, stage 3 `044091ee`, stage 4 `bff5e7f7`.

---

## 2026-06-10 — εlate / `hlate` slot (`Probability/LateFloor.lean`)

New append-only file (309 lines, namespace `ExactMajority.FloorPrefix`) discharging the
`hlate` slot of `FloorPrefix.floor_prefix_le` — the low-`u` checkpoint completion (blueprint
§1 Region L, HANDOFF_EFLOOR_PREFIX.md's "only genuinely new probabilistic piece"). Single-file
`lake env lean … LateFloor.lean` EXIT_0; all 9 headlines axiom-clean
`[propext, Classical.choice, Quot.sound]`; no sorry/admit/axiom/native_decide. Built on uisai2
`/dev/shm/xhuan5/Ripple` (uisai1 down; bucket `v4.30.0 @ c5ea00351c28`).

* **Stage 1 — joint `(pool,u)` ledger / dual cover.** `lateBandBad_subset_floorFail`
  (`⊆ {pool < a₀}`) + `lateBandBad_subset_notDone` (`⊆ {¬roleSplitGoodMile}`): the late-band
  event requires BOTH floor failure AND Stage-1 incompletion, so it is bounded by either end of
  the race. `late_pool_step_ge_ae` = the deterministic `±2` pool-fall ledger (reuse of
  `FloorMasses.pool_step_ge_ae`).
* **Stage 2 — completion tail (race fast side).** `late_completion_tail` =
  `real_bad_le_janson_add_escape` at the floor-driven `roleSplitKernelMilestone`
  (`pMin·meanTime = Θ(log n)`); the generic-checkpoint start condition is the named `hPre_low`.
* **Stage 3 — race assembly (race slow side, the new low-`u` floor-deficit MGF).**
  `lateBand_step_contractive` routes through `{pool<a₀}` into the CONTRACTIVE killed engine
  `midBand_floorFail_step_contractive` (`r<1`, the spurious `1≤r` already dropped in
  KilledAffineTail). Per-step late mass ≤ `(rᵗ·poolExpNeg + b∑rⁱ)/exp(-s·a₀)` + escape,
  GENUINELY DECAYING. `lateBand_prefix_contractive` aggregates.
* **Stage 4 — wire.** `late_prefix_le` (the `hlate`-slot interface) →
  `floor_prefix_le_with_late` (`floor_prefix_le` with `hlate` discharged by the contractive
  route, `hshell`/`hmid` their existing feeders). `εlate n := (3n²)⁻¹`; `late_prefix_le_inv` the
  paper-scale capstone (third of three budgets summing to `εfloor = n⁻²`).
* **Precisely-named residuals** (Region-L stalled-martingale, after genuine attack): the low-`u`
  affine pool drift `hdrift_G` (`r<1, b>0` on the late-band gate), the deterministic floor-exit
  escape bridge (= Gap-2 first-escape pattern), and `hPre_low`.

εlate landed at `1/(3n²)`; the calibration is honest because the killed leading term decays as
`rᵗ` (no `1≤r`). Build infra: rsync local Ripple source + 58 Probability oleans into shm, `lake
exe cache get` for mathlib, `lake build … LateFloor` (3572 jobs) then single-file `lake env lean`.

---

## 2026-06-10 — Brick A: Theorem 6.2 Main-exponent confinement (`Probability/MainExponentConfinement.lean`)

The LAST big probability brick of the whp half, per `HANDOFF_THREE_CORES.md` §1. NEW append-only
file; no existing file edited. Single-file `lake env lean` EXIT_0; all headlines `#print axioms` ⊆
`[propext, Classical.choice, Quot.sound]`; no sorry/admit/axiom/native_decide. Two commits (Stage 1
ledger, Stage 2+3 union+wire), pushed to `main` + mirrored to `xiangyazi24/Ripple opus-wip`.

### Stage 1 — per-rule profile ledger (PROVEN, the honest squaring core)

`phase3CancelSplit_no_jump` is the deterministic squaring witness read off the FROZEN
`phase3CancelSplit` rules (exhaustive case analysis over both input biases × signs): an output at
exponent `k = m+1` is sourced ONLY from an input already at exponent `k` (cancel/no-op preserve
exponents) or exponent `m = k-1` (the split/doubling rule, which makes BOTH outputs `dyadic sgn
(i+1)` from a `(.zero, dyadic sgn i)` pair with `hour > i`). This is the honest "advance to level
`i+1` consumes an agent already at level `i`" structure underlying the paper's
`c_{≥i+1} ≤ p·c_{≥i}²` per-step rate. Plus `phase3CancelSplit_output_exp_ledger` (bias-sum
conservation, from the FROZEN `phase3CancelSplit_preserves_dyadicBiasSum_pair`) and the
`mainProfileAbove` / `mainBiasedAt` above-exponent profile observables built on Brick 0's finsets.

### Stage 2 — single-hour squaring brick (PROVEN by instantiating the LANDED engines)

- `mainProfile_collapse` instantiates the LANDED `FrontTail.windowed_floor_crossing`
  doubly-exponential descent on the Main above-cap fraction `mainFrac i c = µ_{≥i}/|M|`: under the
  Main-profile hour hypotheses with floor `θ ≥ 1/n`, the fraction crosses below the floor within
  `frontWidthBound n = O(log log n)` hours. The collapse engine is fed the carried per-hour squaring
  rate `MainProfileSquaredBound` (the Main-profile counterpart of the clock `WindowedFrontProfile`).
- `main_profile_hour_squaring` instantiates the LANDED `WindowConcentration.windowDrift_tail` for
  the per-hour probabilistic tail `(Kᵗ) c₀ {¬Post} ≤ rᵗ·Φ(c₀)/θ` (the squared rate `r` entering
  through the potential `Φ` and absorbing window `Q`).

### Stage 3 — all-hours union + consumer wiring (PROVEN union SHAPE)

- `theorem6_2_main_confinement_whp`: the headline producing the `hConfine` event bound — the
  probability that `0.92·|M| ≤ #usefulMains` FAILS over the Phase-3→5 horizon is `≤ η` — from the
  per-hour squaring tails (`hHourTail`, the Stage-2 brick named explicitly).
- `theorem62_entry_of_confinement`: the constructor building
  `UsefulMainFloor.Theorem62EntryHypotheses` from the confinement readout
  `MainProfileConfinedToUseful` + the landed Phase-5 window + the Lemma-5.2 role floor. Verified
  end-to-end to feed `UsefulMainFloor.theorem6_2_usefulMains_floor` → the consumer floor
  `P ≤ #usefulMains` UNCHANGED (the existing adapter `phase5_hdrop_wired_from_theorem6_2` consumes
  Brick A unmodified).

### Closed vs the precise named remainder (honest)

- **CLOSED (proven, axiom-clean):** the deterministic per-rule squaring ledger `phase3CancelSplit_no_jump`
  (Stage 1); both abstract-engine instantiations `mainProfile_collapse` / `main_profile_hour_squaring`
  (Stage 2); the union headline `theorem6_2_main_confinement_whp` and the consumer constructor
  `theorem62_entry_of_confinement` (Stage 3, the union SHAPE + wiring).
- **CARRIED (precise named remainder):** the genuinely-dynamic Main-profile per-hour squaring RATE
  `MainProfileSquaredBound` (the `c_{≥i+1} ≤ p·c_{≥i}²` the landed clock Posts export for the CLOCK
  front, not the Main exponent profile), consumed inside `MainProfileHourHypotheses` alongside the
  landed clock `ClockFrontProfile.WindowedFrontProfile` (the hour-boundary synchronisation, NOT
  re-proved); and the collapse READOUT `MainProfileConfinedToUseful` (= the `hConfine` event,
  definitionally), which the all-hours collapse delivers. The single-hour squaring tail enters
  Stage 3's union as the explicit `hHourTail` hypothesis. So `UsefulMainFloor.hConfine` is now
  constructible via `theorem62_entry_of_confinement`; the carried fields are the precise named
  remainders (the per-hour drift rate + the collapse readout), after the real Stage-1 ledger attack
  on `phase3CancelSplit`, not faked bounds.

## Per-level localization B/C — band-position bookkeeping (2026-06-10, BandLocalization.lean)

Per `HANDOFF_PERLEVEL.md` (ChatGPT Pro blueprint): B and C are band-position / Phase-6 Post
exports, NOT counting questions — the global `4n/15` majority-eliminator budget is already proved
in `MarginLedgers.majorityProfileMass_floor`. New append-only file
`Probability/BandLocalization.lean` (EXIT_0, all 5 headlines axiom ⊆ [propext, Classical.choice,
Quot.sound], 0 sorry/admit/axiom/native_decide):

* **Band-position structure** — `MajorityBandAtGap1` (gap-1 predecessor of each live minority
  carries `≥ E` σ-opposite eliminators; `= MarginLedgers.majorityAtExp = Phase7Convergence.elimGap1`
  defeq) + `MinorityConfinedGap1` (each live minority has a gap-1 predecessor index, the band-floor
  fact) + `Phase6BandPositionFacts` bundle + `SurvivalBandAbove` (C-side, defeq
  `Phase7SurvivalUpperBounds`).
* **B-localization** `phase6HighMassDrained_of_bandPosition` (band ⟹ `Phase6HighMassDrained`,
  deterministic gap-1 bookkeeping) → `phase6_to_phase7_of_bandPosition` through the landed adapter
  ⟹ `Phase6To7Structure`.
* **C-localization** `cancelSplit_gap1_preserves_smaller_sign` — the FROZEN `cancelSplit` gap-1
  branch proven directly (smaller-index eliminator re-emerges incremented, same sign): gap-1
  preserves σ-opposite supply, gap-2 preserves/grows it (sign-takeover), only same-level cancels
  SPEND — the blueprint's §2 "gap-2 not an obstruction" verdict, no new probability tail. →
  `phase7_to_phase8_of_survivalBand` through the landed adapter ⟹ `Phase7To8Structure`.
* **Named residual (Phase 6/7 convergence Post must export):** `Phase6BandPositionFacts σ E c` (the
  per-level ROUTING the `doSplit` magnitude-halving achieves — only routing is missing, the global
  budget is proved) and `SurvivalBandAbove σ E c` (the surviving eliminator LOWER bound; landed
  `lemma_7_5/7_6` are minority-survival UPPER bounds only). Genuine attack: the `cancelSplit` gap-1
  preservation is PROVED from the frozen rule, not asserted.

---

## 2026-06-10 — E4 reachable-relative recovery ladder (`Probability/ReachableLadder.lean`)

Per `HANDOFF_HLADDER.md` (ChatGPT Pro doctrine): make the E4 recovery surface
reachability/invariant-relative, replacing `RecoveryBridges`' UNIVERSAL `hLadder` (over all
of `StableDoneᶜ`, including synthetic garbage `AgentState` configs `init` can never reach)
by a reachable-relative one. The all-backup route is DISHONEST (the protocol has no
universal force-to-phase-10; clock-less states have no counter-drain route) — the
paper-faithful reachable ladder stands. NEW append-only file; no existing file edited.
Single-file `lake env lean … ReachableLadder.lean` EXIT_0; all seven headlines
`#print axioms` ⊆ `[propext, Classical.choice, Quot.sound]`; no sorry/admit/axiom/native_decide.
Two commits (D1-2 reachability+`_on` split-geometric; D3-4 classifier+final E4).

### Reachability notion (D1)

Reused the repo's own kernel reachability `Protocol.Reachable`
(= `Relation.ReflTransGen StepRel`); named `ReachableFrom L K init c`. The closure fact
`hReachClosed` is now the THEOREM `reachableFrom_kernel_closed` — from the landed bridge
`stepDistOrSelf_support_reachable` (one-step support point ⟹ deterministically reachable) +
`ReflTransGen.trans`, through the generic kernel-power support-preservation template at
`t = 1`. So the closure is discharged, not assumed.

### `J`-relative split-geometric (D2)

`expected_time_from_whp_and_recovery_on`: the invariant-relative analogue of
`DotyExpectedTime.expected_time_from_whp_and_recovery`, mirroring `expectedHitting_seqcomp_on`.
Built fresh `_on` block atoms (`bad_block_geometric_from_on`, `tail_le_block_on`,
`expectedHitting_split_geometric_on`, `block_half_from_recovery_expected_on`) by assembling
the landed `ExpectedHitting` `_on` engine (`bad_block_contracts_from_on`, `bad_antitone_le_on`,
`pow_compl_inv_eq_zero_eh`, `bad_le_half_of_expectedHitting_on`). The whp start carries `J`;
`J`'s one-step closure keeps every block restart inside `J`, so the Markov half-tail bound
only ever needs the `J`-relative recovery cap.

### Reachable recovery cap + `reachable_hLadder` classifier (D3)

`doty_recovery_bound_via_ladder_on_reachable` (verbatim §4 shape): the recovery cap on
reachable not-done states from a reachable-relative `hLadder`, gated by `ReachableFrom`,
each per-state cap the `RecoveryBridges` Stage-3 telescope. `reachable_hLadder`: the §6
4-way classifier `ReachablePhaseRegimeClassification` — a `Type`-valued inductive with the
four §6 regime constructors (bigClock/tinyClock timed, phase10 majority/tie), each carrying
its per-state `LadderData` keyed by the regime witness (the named E3/E2 caps documented per
constructor: `timed_phase_progress_real_{big,tiny}Clock`,
`phase10_expected_stabilization{,_tie}_O_nsq_log`). The classifier had to be `Type`-valued
(carries `ℕ`/`LadderData`), so the §6 `Or`-branch became an eliminable-into-data inductive.

### Final E4 (D4)

`doty_expected_time_reachable`: conclusion identical to `doty_expected_time_via_ladder`
(`E[T] ≤ (21·C0 + 4·Cbad)·n·(L+1)`), recovery half running the `_on` split-geometric with
`J := ReachableFrom L K init` on the reachable not-done states; per-state caps from the
reachable ladder telescope. Consumes the two honest residuals
`ReachablePhaseRegimeClassification` + `ReachableClockFloors` instead of the universal
`hLadder`.

### Closed vs the precise named remainder (honest)

- **CLOSED (proven, axiom-clean):** the entire reachability layer (D1, `hReachClosed` is a
  theorem); the `J`-relative split-geometric chain (D2); the reachable recovery cap and the
  classifier-extraction `reachable_hLadder` (D3); the final E4 assembly `doty_expected_time_reachable`
  (D4, the whp composition + reachable-relative recovery + reachability closure).
- **CARRIED (the two honest protocol residuals, precisely named):**
  `ReachablePhaseRegimeClassification` (the deterministic 4-way classification of reachable
  not-done states INTO a regime, WITH the per-state phase-ladder to `StableDone`) and
  `ReachableClockFloors` (the Lemma-5.2 clock-floor propagation per timed branch). Discharge
  = phase-regime classification of reachable configs + ladder-spine construction + Lemma 5.2
  floor propagation — the documented future work. These are strictly weaker than the original
  universal `hLadder`: they only ever speak about states `init` can actually reach.

---

## 2026-06-10 — Brick A remainder: `ProfileSquaringRate.lean` (honest per-step rate + hour squaring reduction)

New append-only file `Probability/ProfileSquaringRate.lean` (commit `61a90ce2`). Discharges
`MainExponentConfinement.MainProfileSquaredBound` (the carried `hSquaring` field of Brick A's
`MainProfileHourHypotheses`) modulo ONE genuinely-dynamic coupling. Single-file `lake env lean`
EXIT_0 (uisai2 v4.30.0); all headlines `#print axioms ⊆ [propext, Classical.choice, Quot.sound]`;
0 sorry/admit/axiom/native_decide.

- **Stage 1 (honest per-step rate, PROVEN).** `split_rectangle_mass` / `honest_per_step_source`:
  the per-step source of level-`(i+1)` growth is the split-eligible rectangle mass
  `zeroSupplyCount i · mainExactCount i = Z_i · M_i` (via the landed
  `RoleSplitConcentration.sum_iCount_rectangle_disjoint`). **The honest rate is the PRODUCT
  `c_{=i}·Z_i/n²`, NOT the naive `c_{≥i}²`** — the prompt's central honesty check confirmed: the
  squared form is not a single-step fact.
- **Stage 2 (carried coupling).** `IntegerProfileSquaring`: the integer hour-boundary squaring
  `µ_{≥i+1}·|M| ≤ µ_{≥i}²`, recovered from the product rate via the zero-supply ↔ high-mass coupling
  (Rule-3 cancellations of `±i` pairs feed the doublable `.zero` supply). The Main-profile twin of
  the clock's `GoodFrontProfile` — a TRUE dynamic recurrence carried, not faked.
- **Stage 3 (reduction + wiring, PROVEN).** `mainProfileSquaredBound_of_coupling` (division algebra)
  + `mainHourHypotheses_of_coupling` (constructor discharging `hSquaring`).

**Remaining for full confinement:** discharge `IntegerProfileSquaring` probabilistically (the §6
hour dynamics: `Z_i ≲ µ_{≥i}` at hour boundaries), exactly as the clock side still owes
`GoodFrontProfile`. Everything else in Brick A's collapse → `hConfine` chain is already PROVEN /
carried as named fields.

## DAY-2 CLOSE 2026-06-10 evening — full-map accounting

24 relay agents landed across the day (all 0-sorry, axiom-clean, pushed + mirrored
to opus-wip). Both halves of Theorem 3.1 now have complete top-level structures:
- whp half: doty_time_headline_W2 (21-instance), all five phase drains wired to
  chain-supplied floors, all four floor provenances delivered or precisely named.
- expectation half: doty_expected_time_reachable (reachable-relative, the honest
  surface; all-backup route proven dishonest and rejected).

### THE DEFINITIVE NAMED-RESIDUAL LIST (everything else is proven)
1. IntegerProfileSquaring (ProfileSquaringRate.lean) — the §6 hour recurrence
   Z_i ≲ µ_{≥i} at hour boundaries (zero-supply coupling). Brick A's only gap.
2. Phase6BandPositionFacts (BandLocalization.lean) — Phase-6 Post must export
   the band routing (gap-1 supply at live minority levels). Global 4n/15 PROVEN.
3. SurvivalBandAbove (BandLocalization.lean) — Phase-7 Post survival LOWER bound
   (lemma_7_5/7_6 landed are upper bounds).
4. ReachablePhaseRegimeClassification + ReachableClockFloors (ReachableLadder.lean)
   — E4's reachable-state classification + Lemma-5.2 floor propagation.
5. Per-level drain rates q (AveragingCollapse + the per-phase convergence files)
   — the [45]/Corollary-1-type averaging rate atoms, same shape across phases.
6. Numeric side conditions: hrecmass (E4), the documented engine-level named
   hypotheses per file (hPre_low, low-u (r,b) drift, etc.).

### Queue after residuals
- 1/n² budget tightening sweep (dad-approved cleanup).
- Phase F: full audit refresh + uisai2 explicit-module full build + 推平 main + tag.

### Today's structural theorems worth remembering
- Lemma 5.1 ledger: Mf − Sf = 2X; cosh-MGF kills the X=0 boundary.
- KilledAffineTail: 1≤r was spurious; absorbing-Q eliminated everywhere.
- Gap-2 closed unconditionally (killed-prefix first-escape telescope).
- DetSeamOvershootBridge: theorem, under Wf (no-mcr + smallBias∈[2,4]).
- Phase-1 averaging: variance deterministically non-increasing (49-pair decide).
- Honest squaring: per-step rate is the PRODUCT c_{=i}·Z_i/n²; the square is
  hour-level via zero-supply coupling.

## 2026-06-10 — Residual #6: the mechanical numeric side-condition sweep (`NumericInstances.lean`)

New append-only file `Probability/NumericInstances.lean`. Discharges the explicitly-numeric
named hypotheses left across the day-2 close files as concrete-constant arithmetic instances,
each proven with statement matching the carried hypothesis VERBATIM (shape-checked against the
consumer slots). Single-file `lake env lean` EXIT_0; all four headlines `#print axioms ⊆
[propext, Classical.choice, Quot.sound]`; 0 sorry/admit/axiom/native_decide. Light Mathlib-leaf
imports only (exp / log / ExponentialBounds), so the build is dependency-cheap (no DotyParams
pull — the instances depend only on the genuine domain conditions the campaign establishes).

### Inventory of named numeric side conditions (built FIRST, then discharged)

| # | hypothesis | file / consumer | shape | disposition |
|---|------------|-----------------|-------|-------------|
| 1 | `hrecmass` | `DotyExpectedTime.doty_expected_time_concrete` | `(1/n)·(2·Brecover)·(1−1/2)⁻¹ ≤ 4·Cbad·n·(L+1)` | **DISCHARGED** `hrecmass_of_recover_cap` (from cap `Brecover ≤ Cbad·n·(L+1)` + `1≤n`; uses `(1−1/2)⁻¹=2`) |
| 1'| `hrecmass` | `ReachableLadder.doty_expected_time_reachable` | *identical statement to #1* | same instance closes both (verified by literal shape) |
| 2 | `hnum` | `KilledTailConsumers.phase0_killed_window_unconditional_closed` | `ofReal(e^{−50(L+1)})·∑_{i<τ} ofReal(1+2(e−1)/n)^i ≤ B` | **DISCHARGED** `phase0_immigration_geom_sum_closed` at `B := ofReal(e^{−44(L+1)})` (real chain `phase0_immigration_geom_sum_real`: `∑a^i ≤ τ·a^τ`, `a^τ ≤ e^{2(e−1)(L+1)}`, `τ ≤ n(L+1) ≤ e^{2(L+1)}`, `2e≤6`) |

Domain hypotheses kept (NOT free numerics): `1 ≤ n`, `Real.log n ≤ (L+1)`, `τ ≤ n(L+1)`,
`Brecover ≤ Cbad·n·(L+1)` — the genuine window/scale/recovery-cap conditions the campaign
already establishes (at `n ≥ N₀ = 10^40` the slack is enormous). #2's real chain is the exact
twin of `Phase0Window.phase0_numerics_real`, re-cut for the immigration tail (leading `Φ(c₀)`
term replaced by the `τ`-geometric prefix).

### Verified dangling but genuinely NON-numeric (out of scope — recorded for honesty)

| named residual | file | why NOT numeric |
|----------------|------|-----------------|
| `IntegerProfileSquaring` | ProfileSquaringRate | TRUE §6 hour dynamic recurrence `Z_i ≲ µ_{≥i}` (zero-supply coupling) |
| `Phase6BandPositionFacts`, `SurvivalBandAbove` | BandLocalization | protocol band-routing / survival lower bound |
| `ReachablePhaseRegimeClassification`, `ReachableClockFloors` | ReachableLadder | reachable-state regime classification + Lemma-5.2 floor propagation |
| per-level drain rates `q` | AveragingCollapse + per-phase convergence | Corollary-1 averaging rate atoms (dynamic) |
| `hRecover` / `hBpos` | DotyExpectedTime / ReachableLadder | the §5 recovery cap itself (probabilistic); only its arithmetic consequence `Brecover ≤ Cbad·n·(L+1)` is numeric, and that feeds #1 |
| `hClassify` / `hFloors` / `hPre_low` | ReachableLadder / LateFloor | protocol classification / generic role-split checkpoint |
| `Gap2_reachability_target` | Gap2Reachability | already DISCHARGED (`gap2_reachability_target_discharged`); its geometric budget is a CONCLUSION, not an open hypothesis |

SeamPairAdapter / AveragingCollapse window arithmetic: re-checked — no dangling numeral-only
named hypothesis (the AveragingCollapse residual is the dynamic per-level rate `q`, item above).

**Net:** the two genuinely-numeric named side conditions (`hrecmass` ×2 consumers, `hnum`) are
now closed at concrete constants. Residual #6 reduces to its non-numeric remainder, all of which
is already named in the day-2 definitive list (items 1–5).

---

## UPDATE (2026-06-10) — residual #1 `IntegerProfileSquaring` attacked (ZeroSupplyCoupling.lean)

NEW append-only `Probability/ZeroSupplyCoupling.lean` (single-file EXIT_0; all headlines
`#print axioms ⊆ [propext, Classical.choice, Quot.sound]`; 0 sorry/admit/axiom/native_decide).

The residual `IntegerProfileSquaring` (the §6 hour-boundary `µ_{≥i+1}·|M| ≤ µ_{≥i}²`, i.e.
`Z_i ≲ µ_{≥i}`) is reframed honestly:

* HONEST GUARD (FROZEN `phase3CancelSplit` re-verified): split eligibility is `hour > i`
  (`zeroSupplyAt i = .zero ∧ i < hour`); a fresh such zero is born ONLY from a Rule-3 cancel at a
  level `j > i` consuming two dyadic agents at exponent EXACTLY `j ≥ i+1`. Rule-2 drag re-stamps an
  existing zero's hour (clock-coupled, no fresh zero). → `Z_i` is produced BY the level-`≥i` mass.
* DETERMINISTIC FORM IS FALSE (PROVEN, `integerProfileSquaring_order_impossible`): order alone
  (`0 ≤ B ≤ A ≤ M`) does not give `B·M ≤ A²` (`B=A=1,M=2`). Config witness: one Main at exactly
  `i+1` plus many `.zero`-bias Mains (inflate `mainCount`, not `mainProfileAbove`). → honest form whp.
* DELIVERED: Stage 1 per-pair production ledger `supply_pair_cancelInd` (+ `cancelInd_pos_consumes_high`);
  Stage 2 false-note; Stage 3 whp interface `integerProfileSquaring_whp` (LANDED `windowDrift_tail`
  on the `Z_i`-counter potential) + adapter `mainHourHypotheses_of_zeroSupply_whp` +
  `hConfine_surface_of_zeroSupply`.

The TRUE remaining brick (one named drift fact): `hdrift` of `integerProfileSquaring_whp` — the
per-step contraction of the `Z_i` counter potential, Stage-1 source lifted to a config-level
supermartingale coupled to the clock front (controls the Rule-2 drag). Everything downstream closed.

---

## Residual #2 — BandRouting (2026-06-10): Phase6BandPositionFacts part (1) CLOSED

`Probability/BandRouting.lean` (append-only, EXIT_0, 7 headlines axiom-clean ⊆
[propext, Classical.choice, Quot.sound], 0 sorry/admit/axiom/native_decide).

Discharges `BandLocalization.Phase6BandPositionFacts` from the LANDED Phase-6 Post (was assumed):

- **part (1) `MinorityConfinedGap1` PROVEN** from `Phase6Convergence.highMass l c = 0`
  (`phase6Post_iff`: every biased Main has index ≥ l) + `1 ≤ l`. No carried assumption.
  (`minorityConfinedGap1_of_post`, `exists_minority_witness`.)
- **part (2) `MajorityBandAtGap1`** reduced to ONE named per-level routing field
  `GapAlignedElimFloor` (defeq `MajorityBandAtGap1`). Honest obstruction: the band floor does not pin
  the SPECIFIC partner level; the global `4n/15` budget could sit anywhere in the band.
- **per-level constant `4n/45`** pinned by a band pigeonhole (`exists_band_level_floor_4n45`):
  global budget `≥ 4n/15` (PROVED) + Theorem-6.2 3-level band support ⟹ some level `≥ 4n/45`.
  Pins the constant; does not place mass at the partner level.
- **wiring**: `phase6_to_phase7_of_post` → `EliminatorMargins.Phase6To7Structure` (FLOOR from drain
  Post, BUDGET from `hA`, only routing `hRoute` carried).

Remaining named residual: the Phase-6 `doSplit`-routing-to-partner-level invariant (per-level
placement, not count) — `GapAlignedElimFloor` is the precise carried field.

---

## UPDATE (2026-06-10) — residual #3 `SurvivalBandAbove` attacked (SurvivalAccounting.lean)

NEW append-only `Probability/SurvivalAccounting.lean` (single-file EXIT_0; all 7 headlines
`#print axioms ⊆ [propext, Classical.choice, Quot.sound]`; 0 sorry/admit/axiom/native_decide).

The C-side residual `BandLocalization.SurvivalBandAbove` (Phase-7 surviving above-level eliminator
LOWER bound) reduced to ONE precise named field `Phase7SpendLedger`:

* **Per-pair eliminator ledger PROVED** (`cancelSplit_elimAbove_survives_or_charged`): an above-`i`
  eliminator survives a `cancelSplit` step unless the partner is a colliding σ-minority near `i`
  (same-level cancel is the only loss) — exhaustive FROZEN-`cancelSplit` case split, the §C.1 core.
* **Honest survival arithmetic PROVED** (`survival_floor_honest`): `4n/15 − 2n/25 = 14n/75`. Real
  survival constant `14n/75 ≈ 0.1867n`; the prompt's `≥ n/5` is FALSE at the coarse `0.12·|M|` spend.
* **Wired** to `EliminatorMargins.Phase7To8Structure` via the landed BandLocalization adapter
  (`survivalBandAbove_of_spendLedger` → `phase7_to_phase8_of_spendLedger`).

The TRUE remaining brick (one named field): `Phase7SpendLedger` — the config-level aggregate of the
per-pair ledger along the probabilistic Phase-7 trajectory (Markov support-preservation lift). The
`14n/75 → n/5` gap is a constant swap (Doty's sharp `β⁻ ≤ 0.004·|M|·2^{−l}` minority bound), not a
new tail.

**Campaign residual table update:** `SurvivalBandAbove` → per-pair ledger PROVED + honest `14n/75`
floor PROVED + wired; carried remainder narrowed from "protocol survival lower bound" to the single
trajectory-aggregate field `Phase7SpendLedger` (+ the documented sharp-bound constant tightening).

---

## LANDED 2026-06-10 — `Probability/RegimeClassification.lean` (E4 residual #4: regime ladder spines)

New append-only file. De-opaques the four `ReachableLadder` regime structures: their carried
`LadderData` field is replaced by explicit ladder-SPINE constructions built from the landed
E3/E2 caps + the `RecoveryBridges` telescope. Single-file EXIT_0; 12 headlines axiom-clean
(⊆ propext/Classical.choice/Quot.sound); 0 sorry/axiom/native_decide. Two commits ((a)+(b),
(c)+(d)).

* **(a)** ladder-free regime content: `TimedBigClockData` / `TimedTinyClockData` /
  `Phase10MajorityData` / `Phase10TieData`.
* **(b)** ladder spines: `ladderData_of_two_rung` (Dom→Prog→StableDone) + the four
  `ladderData_of_*`. First link = the named E3/E2 cap; isolated residual = the final-rung
  bridge `potBelow Φ 1 ⟹ StableDone`.
* **(c)** `clockRole_preserved_all_time` (FROZEN "clocks never destroyed at phase ≥3",
  re-export) + `floorProp_{big,tiny}Clock` (Lemma-5.2 floor, uniform over invariant states,
  own phase). ReachableClockFloors's free-outer-`p` shape NOT fake-discharged (honest).
* **(d)** `regimeClassification_*` (checkpoint-conditional classifier). Unconditional
  classification of arbitrary reachable states documented OUT OF SCOPE (no deterministic
  floor pre-role-split / on failed role split).

**Campaign residual table update:** residual #4 (`ReachablePhaseRegimeClassification` +
`ReachableClockFloors`) → the regime ladders are now THEOREMS modulo two named, genuinely-
protocol residuals: (i) per-regime final-rung bridge `potBelow Φ 1 ⟹ StableDone`, (ii) the
deterministic clock-floor VALUE `mC` (Lemma 5.2). Spine construction, telescope wiring,
clock-role preservation, classifier assembly: DISCHARGED. Classification scope is honest
checkpoint-conditional.

---

## Residual #5: Phase-1 averaging drain rate (`Probability/AveragingRate.lean`, 2026-06-10)

NEW append-only file (0-sorry, axioms ⊆ [propext, Classical.choice, Quot.sound]; single-file
`lake env lean` EXIT_0; 11 headlines axiom-audited). Discharges the structural content behind the
per-level second-moment drain rate `q : ℕ → ℝ≥0∞` that `AveragingCollapse.lean` carried as the
`hdrop` hypothesis of `secondMoment_level_tail` / `phase1_pullPos_floor_whp`. The rate is derived
HONESTLY from the FROZEN `avgFin7` rule (NO reference-[45] import), via the SAME rectangle
pair-counting the landed `extremeU` chain uses (`Phase7Convergence.drop_prob_of_rect`).

**The honesty trap (caught and resolved).** The per-rule ledger drop `= ⌊(x−y)²/2⌋` is ZERO for
gap ≤ 1, so a config whose Mains all sit in a width-1 stall window `{a,a+1}` STALLS with possibly
huge second moment (window `{0,1}`/`{5,6}` ⟹ secondMomentN up to `9·|M|`). Hence a naive
"`secondMomentN ≥ θ ⟹ gap-2 pair exists`" is FALSE. The genuine escape (the actual mechanism, not a
wishful constant) is the **window `{2,3,4}` second-moment ceiling**:

- `sqDist3N_le_one_of_not_far`: `val ∈ {2,3,4}` ⟹ `sqDist3N ≤ 1` (exhaustive `decide`).
- `secondMomentN_le_card_of_no_far`: NO far Main (`val ≤ 1` or `val ≥ 5`) ⟹ `secondMomentN ≤ |M|=n`.
- `farExists_of_secondMoment_gt_n` (the structure lemma): `secondMomentN c > n ⟹ ∃ far Main`.

The `{0,1}`/`{5,6}` stall windows are excluded by the **sum invariant** (Stage 1):
`centredBiasSum c = Σ_{Mains}(smallBias.val − 3)` is `avgFin7`-conserved
(`centredBiasSum_stepOrSelf_eq`, lifting `Phase1Convergence.avgFin7_preserves_sum`); at the Doty
entry each Main encodes a ±1 opinion so `|S₀| ≤ |M| = n` — the predicate `SumPinned n c`, which is
`K`-closed (`invClosed_sumPinned`). A `{0,1}`-window config has `S₀ ≤ −2|M|`, contradicting
`|S₀| ≤ n`. So the conserved sum pins the stall windows out of reach and the `{2,3,4}` ceiling is the
per-step "Φ large ⟹ strict-drop rectangle exists" conversion.

**Stages 2/3 — the rate.** Two strict-drop rectangles, mirroring `DrainThreading`'s
`extremePosSet ×ˢ pullPosSet` exactly:
- `farHighSet(val≥5) ×ˢ lowSet(val≤3)` and `farLowSet(val≤1) ×ˢ highSet(val≥3)`. Each cell has
  `val`-gap `≥ 2`, so `avgFin7_sqDist3_pair_drop_high/_low` (exhaustive `decide`) give drop
  `= ⌊gap²/2⌋ ≥ 2 ≥ 1` — a STRICT secondMomentN drop. Disjointness of the two state-finsets is by
  value (`farHigh_low_disjoint`, `farLow_high_disjoint`).
- `secondMomentN_stepOrSelf_drop_high/_low` lift the per-pair strict drop to the config kernel;
  `secondMomentN_drop_prob_rect_high/_low` thread through `drop_prob_of_rect` to the kernel
  drop-probability floor `≥ ofReal((#far · #partner)/(n(n−1)))`.
- `secondMomentN_hdrop_of_floor` (mirror of `extremeU_hdrop_of_floor`) and
  `secondMomentN_hdrop_of_struct_high/_low` give the per-level `hdrop` at
  `q m = 1 − ofReal(P/(n(n−1)))`, `P` the carried partner margin and `1 ≤ #far` the far witness.

**Stage 4 — wiring + time budget.** `phase1_pullPos_floor_whp_of_struct` feeds the derived `q` into
`AveragingCollapse.phase1_pullPos_floor_whp`; `hdrop_realizable_high` exhibits the rate as the
concrete rectangle floor (constructive). Time budget (documented in-file): consumer needs the floor
at level `m = 4(n−P)+1`, level-tail gives failure `≤ (1 − P'/(n(n−1)))^t`.

| partner floor `P'` | rate `q m`        | horizon `t` for `O(1/n²)` failure | regime          |
|--------------------|-------------------|-----------------------------------|-----------------|
| single witness (1) | `1 − 1/(n(n−1))`  | `Θ(n²·log n)`                     | crude           |
| `Θ(n)` (const frac)| `1 − Θ(1/n)`      | `Θ(n·log n)`                      | paper Lemma 5.3 |

The constant-fraction partner floor `P' = Θ(n)` is the centre-mass content [45] Cor.1 supplies and
is the ONLY remaining carried atom — same status as the `extremeU` chain's `hpull` partner floor.
Everything STRUCTURAL around the rate (existence of the dropping rectangle, the strict-drop cells,
the rectangle→kernel-mass conversion, the level-tail wiring) is now DISCHARGED.

**Campaign residual table update:** residual #5 (the carried Phase-1 second-moment `q`) → the rate's
structural derivation is now a THEOREM modulo the single carried partner-margin floor `P' = Θ(n)`
(the [45] Cor.1 centre-mass count, identical status to the landed `extremeU`/Phase-7/8 partner
floors). The far-witness existence, the `{2,3,4}` ceiling, the sum invariant, the strict-drop
rectangles, and the `drop_prob_of_rect` threading: DISCHARGED, 0-sorry, axiom-clean.

---

## ENTRY (2026-06-10) — tip #2a: honest band geometry for `GapAlignedElimFloor` (Probability/GapAlignment.lean)

NEW append-only `Probability/GapAlignment.lean`. Single-file EXIT_0; all 6 headlines axiom-clean
(`⊆ [propext, Classical.choice, Quot.sound]`); 0 sorry/admit/axiom/native_decide. No existing file edited.

**Sign conventions resolved from the DEFS (not comments):** `minorityAt7 σ j` = σ-signed Main at `j`
(minority carries sign σ); `elimGap1 σ i` = σ-OPPOSITE Main at `i`, consumer-paired `i+1 = j`
(eliminator one index BELOW the minority). `highMass l = 0` ⟺ every biased Main of BOTH signs has
index `≥ l`.

**Honest geometric tension (the resolution).** `GapAlignedElimFloor σ E c` with `E ≥ 1` needs, per live
minority `j`, an eliminator at `i = j−1`; that eliminator is a biased Main, so the floor forces `i ≥ l`,
hence `j ≥ l+1` — **the minority sits STRICTLY above the floor.** A minority at the floor (`j = l`) has
its partner at `l−1 < l` where the floor forbids any biased Main (`elimGap1 σ (l−1)` empty), so the
routing is FALSE for it. Thus the routing is NOT a free consequence of the floor; its irreducible
content is the drain fact `MinorityAboveFloor σ l c` plus per-partner placement.

**Proven from the Post alone (no new carried assumption):**
- `elim_index_ge_floor`, `elimGap1_eq_zero_below_floor` — floor on the eliminator band; band empty below
  the floor.
- `majoritySupportedOn_atFloor_of_post` — majority mass supported on `{i | l ≤ i.val}`. **Discharges the
  LOWER half of `BandRouting.MajoritySupportedOn` from the Post; only the Theorem-6.2 UPPER edge `≤ l+2`
  stays carried** (net reduction of the Stage-2b pigeonhole's band-support input).
- `minorityAboveFloor_of_routing`, `gap1_predecessor_in_band`, `gapAligned_routing_forces_above_floor` —
  the routing PROVES `MinorityAboveFloor` (geometry internally consistent), and under it every gap-1
  partner lands inside the proven majority support. So the routing's target levels ⊆ the proven support;
  the only carried content is the per-PARTNER pigeonhole placement.

**Residual #2 status update.** The Stage-1 `MinorityConfinedGap1` was already proven (BandRouting). This
entry settles the geometry of Stage-2 `MajorityBandAtGap1`/`GapAlignedElimFloor` and reduces its carried
content to: (1) `MinorityAboveFloor` (Phase-6 `doSplit` drain clears the floor index → live minority at
`≥ l+1`); (2) the per-partner-level placement of the `4n/45` band mass. Floor on both bands + lower band
support + `4n/45` constant: PROVEN. Neither carried piece is a probability tail or a geometric
impossibility — both are deterministic Phase-6 drain invariants to be exported by the convergence proof.

---

## tip #1a — the zero-supply drift `hdrift` is discharged (`Probability/ZeroSupplyDrift.lean`, r = 1)

`ZeroSupplyCoupling.integerProfileSquaring_whp` carried a single dynamic input: the per-step drift
`∀ c, Q c → ∫⁻ Φ dK(c) ≤ r · Φ c` of the `Z_i`-counter potential. This is now PROVEN at `r = 1`.

**Layer A (general, hypothesis-free).** `sumOf_subadditive_drift_le` — for any `Protocol Λ` and any
`f : Λ → ℝ≥0∞` pairwise sub-additive on the applicable scheduled pairs, the kernel expectation of
`Config.sumOf f` does not increase: `∫⁻ (sumOf f) dK(c) ≤ (sumOf f)(c)`. The honest engine; it weakens
the FROZEN additive invariant `Basic/PopulationProtocol.lean stepRel_sumOf_eq` to a sub-additive ≤ and
sums it against the interaction law (`Phase0Window.lintegral_transitionKernel_eq_sum` + `∑ prob = 1`).
Helper `stepOrSelf_sumOf_le` does the per-pair multiset bookkeeping (`Multiset.sub_add_cancel`).

**Layer B (instantiation).** `supplyPotential i := Config.sumOf (supplyIndic i)` is the `Z_i`-counter;
`supplyPotential_measurable` (discrete σ-algebra). The region `SupplySubadditive i c` is exactly "no
applicable pair produces fresh `Z_i` supply", which the Stage-1 ledger (`supply_pair_cancelInd`,
`cancelInd_pos_consumes_high`) pins to "no Rule-3 cancel of a `±j` pair at `j > i`" — suppressed inside a
good clock front window (band-limited Rule-2 drag, cancel indicator 0). `supplyPotential_drift_le` is the
discharged `r = 1` drift; `integerProfileSquaring_whp_of_region` wires the whp tail with `hdrift`
ELIMINATED (failure prob `≤ Φ(c₀)/thr`).

**What remains** (downstream of this drift): only the structural absorbing-window/threshold bookkeeping
(`hQ_abs`, `hthr`, `hlink`) and the carried clock-front region `SupplySubadditive` (realised by the
landed `WindowedFrontProfile` — clock side NOT re-proven here). The `r = 1` rate is honest: the supply
counter is genuinely NON-INCREASING off the cancel events, so no contraction below 1 is claimed or needed
for the whp Markov tail.

**Audit.** All four new theorems `#print axioms` ⊆ `[propext, Classical.choice, Quot.sound]`; no
sorry/admit/axiom/native_decide; single-file `lake env lean` clean; `git diff --check` clean.

---

## tip #3a — `Phase7SpendLedger` trajectory lift (SpendLedgerLift.lean, 2026-06-10)

**NEW** `Probability/SpendLedgerLift.lean` (append-only, 0 sorry/admit/axiom/native_decide, axioms ⊆
[propext, Classical.choice, Quot.sound], single-file `lake env lean` green).

Closes the named carried field `SurvivalAccounting.Phase7SpendLedger` and discharges all the
probability in the Phase-7→8 survival lift:

- **`Phase7SpendLedger` discharged at every config** (`phase7SpendLedger_canonical`) via canonical
  spend `Entry ∸ elimAbove` — ℕ identity `Entry ≤ x + (Entry ∸ x)`. The carried field is no longer a
  residual; the survival content is rerouted to `SurvivalBandAbove`.
- **Stochastic lift fully discharged** (`survivalBand_ae_along_trajectory`): the joint predicate
  `Phase7AllMain ∧ SurvivalBandAbove` is a.e.-preserved along every kernel power via the landed
  support-preservation template. Reduces the entire trajectory aggregate to ONE deterministic per-step
  band-closure (`hBand`), which is the multiset `countP`-delta of the PROVEN per-pair ledger
  (`cancelSplit_elimAbove_survives_or_charged`).
- **Consumer bridge** (`elimAbove_sum_eq_countP`, `minorityAt_sum_eq_countP`): `Finset.sum c.count` ↔
  `Multiset.countP`, making the `StepRel` transition actionable on the consumer shapes.
- **End-to-end** (`phase7_to_phase8_via_canonicalSpend`): canonical-spend ledger + survival band ⟹
  `EliminatorMargins.Phase7To8Structure` at honest floor `14n/75` (`honest_survival_floor`).

**Net for residual #3 (`SurvivalBandAbove`):** `Phase7SpendLedger` CLOSED; the Markov-trajectory lift
(the genuinely-stochastic step the blueprint §C.2 flagged) DISCHARGED via the support template; the
only remaining piece is the deterministic per-step `countP`-monotonicity of `elimAbove` against the
live minority (the multiset aggregate of the proven per-pair ledger) — no probability, no new tail.

---

## tip #2b — `MinorityAboveFloor` = dynamic floor invariant (MinorityFloorGap.lean)

NEW append-only `Probability/MinorityFloorGap.lean` (EXIT_0; 7 headlines axiom-clean ⊆
[propext, Classical.choice, Quot.sound]; 0 sorry/admit/axiom/native_decide; diff --check clean).

**Geometry verdict.** `MinorityAboveFloor σ l c` (live σ-minority at `≥ l+1`) is NOT a Phase-6 Post
fact — a minority AT index `l` satisfies `highMass l = 0` (`l ≤ l`). The eliminators-ABOVE re-cut
(Phase-8 `elimAbove`, index `> i`) IS floor-free (`elimAbove_floorFree`), but the BINDING consumer is
Phase-7's gap-1-BELOW `elimGap1` (frozen `Phase6To7Structure` shape), which DOES carry the placement.
So the re-orientation does NOT dissolve it; `MinorityAboveFloor` is a genuine DYNAMIC invariant.

**Discharge.** Settled to ONE sign-agnostic threshold seed `AllBiasedMainAbove (l+1)` (every biased
Main at index `≥ l+1`), proven:
- `cancelSplit_preserves_index_floor` — the frozen `cancelSplit` NEVER lowers a biased index (full
  branch audit: same/gap-1/gap-1'/gap-2/gap-2'/no-fire all move Mains UP or cancel). Threshold floor
  preserved for any `m` ⟹ the `l+1` seed is Phase-7-step-stable WITHOUT probability.
- `minorityAboveFloor_of_allBiasedMainAbove` — the seed discharges `MinorityAboveFloor` for BOTH signs.
- `minorityAboveFloor_verdict` (capstone) — seed ⟹ residual (both signs) + seed step-stable.

**Net.** Carried residual reduced from per-sign per-level placement to a single threshold seed (the
Phase-6 `highMass`-drain Post with the floor bumped by one — the drain clearing the floor INDEX itself
for the σ-minority). Only remaining brick: export `AllBiasedMainAbove (l+1)` from the Phase-6
convergence proof (same statement as the landed drain, threshold +1).

---

## tip #4a — the honest per-regime final-rung stability bridges (StableBridges.lean)

NEW append-only `Probability/StableBridges.lean` (single-file `lake env lean` EXIT_0; 12 headlines
axiom-clean ⊆ [propext, Classical.choice, Quot.sound] — the two `timed_*` even drop `Classical.choice`;
0 sorry/admit/axiom/native_decide; diff --check clean). No existing file edited.

**What this discharges.** `RegimeClassification.lean` left ONE explicit residual per regime: the
final-rung bridge `progressSet (potBelow Φ 1) ⟹ StableDone`, carried as the `hbridge` hypothesis of
each `ladderData_of_*` builder. tip #4a surveys what each potential's ZERO-state means and proves the
bridges that are honestly true, re-shaping the spine where the naive bridge is FALSE.

**The survey verdict (what `potBelow Φ 1 = {Φ = 0}` means per regime).**
- **Phase-10 majority** (`Φ = wrongACount`): `wrongACount = 0` ⟺ every agent outputs `A`. With the
  regime fact `AllPhase10` (from `S1`) + the init-sign match `0 < initialGap init`, this IS
  `phase10MajorityWitness init` (the A-disjunct of `majorityStableEndpoint`). **This is the real
  stability bridge** — `wrongACount = 0` (not the clock potential) is what implies stability.
- **Phase-10 tie** (`Φ = wrongTCount`): `wrongTCount = 0` ⟺ every agent outputs `T`; with `AllPhase10`
  (from `Tie1plus`) + `initialGap init = 0`, this is `phase10MajorityWitness init` (the T-disjunct).
- **Timed regimes** (`Φ = clockCounterSumAt p`): `clockCounterSumAt p = 0` means the phase-`p` clocks
  all hit counter `0` — which triggers phase **ADVANCE**, NOT stability. So the direct bridge
  `potBelow (clockCounterSumAt p) 1 ⟹ StableDone` is **FALSE** (drained clocks advance to phase
  `p+1 < 10`, still mid-protocol). The honest rung target is **next-phase entry**, and the ladder must
  continue `p → p+1 → ⋯ → 10 → stable` (the final Phase-10 rung closed by the bridges above).

**Bridges CLOSED (the two Phase-10 regimes).**
- `phase10Majority_drained_mem_stableDone` / `phase10Tie_drained_mem_stableDone` — the membership
  bridges (pure protocol, no probability): drained Phase-10 state + init-sign match ⟹
  `c ∈ StableDone L K init`. Proven by unfolding `wrongACount/wrongTCount = 0` (`Multiset.countP_eq_zero`)
  into the right `phase10MajorityWitness` disjunct.
- `phase10Majority_link_intersected` / `phase10Tie_link_intersected` — the first link to the
  S1/Tie1plus-INTERSECTED drain target. The naive bridge over the BARE `potBelow Φ 1` is unprovable (an
  arbitrary `wrongACount = 0` state need not be `S1`/stable); we re-shape the rung-1 target to
  `{S1} ∩ potBelow wrongACount 1` so the membership bridge applies pointwise. The E2 cap
  (`phase10_expected_stabilization{,_tie}_O_nsq_log` ≤ `3n²(1+2log n)` / `2n²(1+2log n)`) is routed to
  the intersected target via the InvClosed slice argument (`pow_compl_inv_eq_zero_eh` keeps the
  trajectory a.e. on `S1`/`Tie1plus`, so the not-Done tail = not-Bare tail).
- `phase10Majority_bridge_expectedHitting` / `phase10Tie_bridge_expectedHitting` — the bridge as an
  `expectedHitting … ≤ βbridge` cap: every intersected-target state is already in `StableDone`, so
  `expectedHitting = 0` (`RecoveryBridges.expectedHitting_eq_zero_of_mem`, `StableDone` absorbing).
- `ladderData_of_phase10Majority_bridged` / `ladderData_of_phase10Tie_bridged` — the re-shaped
  Phase-10 ladder spines with the bridge **DISCHARGED** (no `hbridge` hypothesis). Builds the
  `LadderData` to `StableDone` via the two-rung spine, intersected rung-1 target, E2 first link, and
  the discharged second link. Consumes: `StableDone` measurable + absorbing (`hDoneMeas`/`hAbs`, the
  campaign-wide surface) + the init-sign match (`0 < initialGap` / `= 0`).

**Spine re-shaped (the two timed regimes).** `timed_phase_chain_target L K n p :=
{AllClockGEpCard (p+1) n}` names the honest rung-1 target (next-phase domain, phase advance), with
`timed_chain_target_is_next_phase` recording that it is next-phase entry, NOT `⟹ StableDone`. The timed
spine re-shapes to the `n`-rung chain through phases via the `RecoveryBridges` telescope (which supports
arbitrary ladders); the per-step deterministic `drained ⟹ next-phase-domain` advance transition is the
named Stage-4 timed residual. We deliberately do NOT fake-discharge the false direct timed bridge.

**Net narrowing of the E4 surface.** The two Phase-10 regime ladders are no longer modulo a carried
bridge — they are theorems (modulo the init-sign match, a conserved-gap fact). The honest residual
collapses to: (i) the deterministic timed phase-advance transitions feeding the re-shaped timed chain;
(ii) the init-gap sign match for the Phase-10 regimes (gap conservation along reachable trajectories);
(iii) `StableDone` absorption (campaign-wide). The stability characterization itself — what makes a
drained Phase-10 state a `majorityStableEndpoint` — is now fully proven.

---

## §6 residual #3 (`SurvivalBandAbove`) — config-level `countP` delta closing `hBand` (BandStepBookkeeping.lean, 2026-06-10)

NEW append-only `Probability/BandStepBookkeeping.lean` (single-file `lake env lean` green, 0 warnings;
all 8 headlines `#print axioms ⊆ [propext, Classical.choice, Quot.sound]`; 0 sorry/admit/axiom/
native_decide). No existing file edited.

Closes the deterministic core of the LAST atom in the #3 chain: `hBand` of
`SpendLedgerLift.phase7Surviving_step_of_band`. `SurvivalAccounting.cancelSplit_elimAbove_survives_or_charged`
PROVED the per-pair eliminator ledger (`.1` component). This file (a) proves the missing `.2`-component
mirror, (b) aggregates both to a pair-level inequality, (c) lifts it to the **config-level `countP`
delta** over one `StepRel` step, and (d) records the honest entry-margin residual.

**countP identity chain (config aggregation of the per-pair ledger):**
`A i c' = (A i c − countP_elim {r₁,r₂}) + countP_elim {p₁,p₂}` (`Multiset.countP_add`/`countP_sub`,
`{p₁,p₂} = cancelSplit r₁ r₂` via `Transition_eq_cancelSplit_of_phase7_main`), so
`A i c ≤ A i c' + countP(collidingMinority σ i){r₁,r₂}` — the surviving above-`i` eliminator count
drops by at most the σ-minority drained that step. (`A i := countP (elimAbovePred σ i)`, defeq the
consumer `(elimAbove σ i).sum c.count`.)

**Headlines:** `cancelSplit_elimAbove_snd_survives_or_charged` (the `.2` ledger),
`cancelSplit_elimAbove_pair_le` (pair inequality), `elimAbove_countP_drop_le_colliding` (config delta,
applicable step), `elimAbove_countP_step_drop_le_colliding` (`stepDistOrSelf`-support form),
`survivalBand_step_closed_of_margin` (per-level conditional closure),
`survivalBandAbove_step_closed_of_marginBand` (the `hBand`-shaped closure of the margin band
`SurvivalBandMargin σ E` into the floor band `SurvivalBandAbove σ E`, conditional on minority
monotonicity).

**Honest residual recorded (= residual #2's outputs).** The fixed-`E` band is NOT pointwise step-closed
(one same-level cancel ⟹ `A i = E → E−1`). The closure needs, BOTH deterministic (no new probability
tail): (1) the **entry margin** `Entry ≥ E + spend` = the `GapAlignedElimFloor` routing + sharpened
Doty spend (`SurvivalAccounting.survival_floor_honest`); (2) **minority monotonicity** — the per-level
minority count never rises (`Phase7Convergence.cancelSplit_minorityU_pair_le`). With both,
`survivalBandAbove_step_closed_of_marginBand` ⟹ `hBand` ⟹
`SpendLedgerLift.survivalBand_ae_along_trajectory` ⟹ `phase7_to_phase8_via_canonicalSpend` ⟹
`EliminatorMargins.Phase7To8Structure`, NO remaining probability.

**Final Phase7→8 surface:** the residual-#3 chain is now deterministic end-to-end modulo the entry
margin band and the minority-monotonicity carry; all probability is discharged in
`SpendLedgerLift.survivalBand_ae_along_trajectory` via the landed support-preservation template.

---

## SeedExport.lean landed — the `AllBiasedMainAbove (l+1)` seed (2026-06-10, EXIT_0, axiom-clean)

NEW append-only `Probability/SeedExport.lean` (single-file `lake env lean` EXIT_0, 0 warnings; all 13
headlines `#print axioms ⊆ [propext, Classical.choice, Quot.sound]`; 0 sorry/admit/axiom/native_decide;
`git diff --check` clean). No existing file edited.

This is the LAST brick of `MinorityFloorGap.lean`'s verdict: that file proved the carried
`MinorityAboveFloor` residual is a step-stable dynamic floor invariant seeded by `AllBiasedMainAbove
(l+1) c`, preserved by the frozen `cancelSplit`, discharging `MinorityAboveFloor` for both signs — but
left OPEN *where the seed comes from at Phase-7 entry*. SeedExport answers it.

**The load-bearing parameterization audit (verified against the landed API, not comments):** the entire
Phase-6 drain machinery is symbolic in the band level `l`:
- `Phase6Convergence.phase6Convergence' l n …` — `l : ℕ` free; `Post c = Phase6Win n c ∧ highMass l c = 0`.
- `DrainThreading.phase6_hdrop_of_struct σ l n m hn hl1 hlL b … h hhgt hhne …` — `l` enters only via
  `hl1 : 1 ≤ l`, `hlL : l ≤ L`, and the witness hour `h : Fin (L+1)` with `l-1 < h.val`, `h.val ≠ L`.
- `DrainCalibration.phase6Convergence_calibrated l n M₀ q tWin …` — `l` free, budget `l`-agnostic.

So instantiating the engine at `l+1` is a VERBATIM re-application at the bumped parameter — no new
probability content. All five referenced signatures were cross-checked against the actual landed files
and matched exactly; the file compiles verbatim with EXIT_0.

**`l+1` IS CLOSED, up to one honest budget side-condition:**
- `succ_witnessHour_of_budget (hlL2 : l + 2 ≤ L)` — the `l+1` band-top index is `(l+1)-1 = l`; the
  witness sampling hour needs `l < h.val < L`, which exists iff `l + 2 ≤ L`. **This is the SOLE new
  content of the level bump.** The bare-`l` Post needs one free hour above the band floor; the `l+1`
  seed needs TWO (band-top `l` + sampling reserve strictly above). Honest budget arithmetic, exposed as
  the explicit hypothesis `hlL2 : l + 2 ≤ L`. Matches Doty §7: the drain pushes the σ-minority strictly
  BELOW the σ-majority band by clearing floor index `l` itself ("one notch" separation), available
  exactly while the clock has not saturated the top hour `L`.
- `phase6_succ_hdrop_of_struct` (caller supplies the witness `h`) and `phase6_succ_hdrop_of_struct_budget`
  (witness produced internally from `l+2 ≤ L`) — the landed `DrainThreading` per-level `hdrop` at `l+1`.
- `phase6Convergence_succ` / `phase6Convergence_succ_calibrated` — the convergence engines at `l+1`,
  definitional (engine symbolic in `l`).

**The seed export (the `phase6Post_iff` analogue):**
- `seedExport_of_post_succ (hPost : highMass (l+1) c = 0) : AllBiasedMainAbove (l+1) c` — the `l+1` Post
  IS the seed, by `MinorityFloorGap.allBiasedMainAbove_of_post` at the bumped level.
- `seed_of_phase6_succ_post` — reads the seed off the `Post` second conjunct.

**The wired chain seed → verdict → consumers:**
- `post_of_seed` — the seed WEAKENS to the bare `l` Post `highMass l c = 0` (every biased Main `≥ l+1`
  trivially `≥ l`), feeding the bare-`l` consumers.
- `verdict_of_seed` — discharges `MinorityFloorGap.minorityAboveFloor_verdict`: `MinorityAboveFloor` for
  both signs + the `cancelSplit` step-stability of the `l+1` floor.
- `minorityConfinedGap1_of_seed`, `phase6_to_phase7_of_seed` — via `post_of_seed` into the landed
  `BandRouting` adapters ⟹ `EliminatorMargins.Phase6To7Structure`.
- `phase6To7_surface_of_seed` / `phase6To7_surface_of_succ_post` — the STRONGEST reachable Phase6→7
  surface from the single seed: the standard `Phase6To7Structure` σ E c PLUS the simultaneous
  `MinorityAboveFloor l τ c` for EVERY sign (which the bare Post canNOT give) PLUS the `l+1`-floor
  `cancelSplit` step-stability. The carried `MinorityFloorGap` residual is now PRODUCED by the landed
  (bumped) drain, no longer an open assumption.

**Net:** `MinorityAboveFloor` is fully closed AS A RESIDUAL — reduced to the single sign-agnostic seed
`AllBiasedMainAbove (l+1)`, and that seed is now exported as the LANDED Phase-6 drain run one level
higher. The seam to Phase 7 is the strongest reachable form (`Phase6To7Structure` + simultaneous
`MinorityAboveFloor` + step-stability). The only honest input is the budget `l + 2 ≤ L` (two free hours
above the band floor) — documented explicitly, NOT hidden. No probability obstruction; the bump is the
verbatim engine at the bumped parameter.

---

## Phase-1 partner-margin Θ(n) floor (`Probability/PartnerMargin.lean`, NEW)

The LAST carried atom of the §1 averaging chain. `AveragingRate.lean` lands the per-level
second-moment drain rate `q m = 1 − ofReal(P/(n(n−1)))` (`secondMomentN_hdrop_of_struct_high/_low`)
but carries one quantitative input: the **partner margin** `P`. With `P = 1` (single far witness)
the rate is `1 − 1/(n(n−1))` and the horizon is the crude `Θ(n²·log n)`; the paper-faithful
`Θ(n·log n)` (Lemma 5.3 / [45] Cor.1) needs `P = Θ(n)`. This file derives that `Θ(n)` floor HONESTLY
from the conserved SUM INVARIANT of `AveragingRate` (`centredBiasSum`), no [45] import.

**The briefing-error caught and fixed.** The naive pigeonhole `#low < δn ⟹ S > n` does NOT close at
the granularity `|S| ≤ n`: every Main has centred value in `[−3,3]`, so `S ≥ (n − #low) − 3·#low =
n − 4·#low`, which is `≤ n` with NO contradiction. The genuine derivation needs the SHARPER honest
entry bound `|S| ≤ g`: the Doty Phase-1 entry encodes each Main's ±1 opinion as `val ∈ {2,4}`
(centred ±1), so `S = centredBiasSum = #plus − #minus = gap`, the initial opinion gap, conserved by
`avgFin7` (`AveragingRate.centredBiasSum_stepOrSelf_eq`). At a contested entry `|S| ≤ g = εn`. THEN
`n − g ≤ 4·#low` closes (division-free).

**STAGE A — honest entry sum bound.** `EntrySumPinned n g c := Phase1AllMain n c ∧
|centredBiasSum c| ≤ g` refines `AveragingRate.SumPinned` (the trivial `g = n` case;
`sumPinned_of_entrySumPinned`). `K`-closed: `EntrySumPinned_support_closed` (window closure +
`AveragingRate.centredBiasSum_eq_on_support`) ⟹ `invClosed_entrySumPinned`.

**STAGE B — the honest pigeonhole (ℤ, division-free).** Pointwise bias bounds on a Main:
`biasZ_ge_low` (`4·[val≥4] − 3 ≤ biasZ`), `biasZ_le_high` (`biasZ ≤ 3 − 4·[val≤2]`). Summed by direct
multiset induction:
- `lowCount_core`: `(card s : ℤ) − 4·countP(val≤3) s ≤ Σ biasZ` (every Main `≥ −3`; high Mains
  `val≥4` add `≥ +4` above that floor).
- `highCount_core`: `Σ biasZ ≤ (card s : ℤ) − 4·countP(val≥3) s` (mirror).

Combined with `EntrySumPinned`'s `centredBiasSum ≤ |·| ≤ g` (resp. `−g ≤ −|·| ≤ ·`):
`four_mul_lowCount_ge_of_entry` / `four_mul_highCount_ge_of_entry`: `(n:ℤ) − g ≤ 4·countP`. The
`countP`-↔-`Finset.sum count` bridge `sum_count_filter_eq_countP` (generic re-derivation of the
`EarlyDripMarked` lemma for `AgentState L K`: `Finset.sum_filter` → `Multiset.count_filter` →
`sum_count_eq_card` → `countP_eq_card_filter`) plus the all-Main role-conjunct collapse
(`lowSet_sum_count_eq_countP` / `high`, via `Multiset.countP_congr` — every member is a Main so the
`role = main` conjunct of `low`/`high` is free) convert to the consumer's count shape:
`lowSet_floor_of_entry` / `highSet_floor_of_entry`: `(n − g + 3)/4 ≤ (lowSet/highSet).sum count`
(ℕ round-up of `(n−g)/4`).

**STAGE C — instantiate `AveragingRate`'s `P'` slot.** `secondMomentN_hdrop_of_entry_high/_low` feed
`P = (n − g + 3)/4 = Θ(n)` into `AveragingRate.secondMomentN_hdrop_of_struct_high/_low`, giving
`q m = 1 − ofReal((⌈(n−g)/4⌉)/(n(n−1)))`. The only config-dependent input left is the far witness
`1 ≤ farHighSet/farLowSet .sum count` — the SIDE `farExists_of_secondMoment_gt_n` leaves open (it
supplies *a* far Main; *which* side is the per-config datum the rectangle pairs against the
opposite-side partner floor). Both orientations delivered.

**STAGE D — final floor surface.** `phase1_pullPos_floor_whp_of_entry` instantiates
`AveragingRate.phase1_pullPos_floor_whp_of_struct` with `P = (n − g + 3)/4`. Inputs: the protocol
window `Phase1AllMain`, the honest entry gap `g ≤ n`, and the rate family `q` (discharged structurally
by Stage C). HORIZON arithmetic documented in-file: `P = Θ(n)` (`g = εn` ⟹ `P ≥ (1−ε)n/4`) ⟹
`q m = 1 − Θ(1/n)` ⟹ `(q m)^t = (1 − Θ(1/n))^t ≤ exp(−Θ(t/n))` ⟹ `t = Θ(n·log n)` for `O(1/n²)`
failure — paper-faithful Lemma 5.3 / [45] Cor.1. The crude single-witness regime (`P = 1`,
`t = Θ(n²·log n)`) is the `g = n` degenerate case `P = ⌈0/4⌉`.

**Net:** the §1 averaging chain has NO remaining free quantitative atom — the partner margin `P` is
the honest `Θ(n)` value `(n − g + 3)/4` derived from the conserved opinion-gap invariant. The only
inputs are the protocol window, the entry gap `g`, and the far witness (config datum), all honest.

---

## Phase E4 — `Probability/TimedChainRungs.lean` (2026-06-10, 0-sorry, axiom-clean)

The timed per-rung phase-advance expected-time bound — the Stage-4 residual `StableBridges`
re-shaped to next-phase entry `{AllClockGEpCard (p+1) n}`.  Salvaged the predecessor's
untracked draft (cut by usage limit): it had 3 build errors (`omega` missing the trivial
`m=0`/`geCount≤n` cases in `advance_subset_potBelow`; an `exact_mod_cast Int.subNatNat`
mismatch in `seam_rate_le_one`; an incomplete `seamQ_inv_le` with a `sorry`).  Rewrote
cleanly; now single-file `lake env lean` EXIT_0, axioms ⊆ [propext, Classical.choice,
Quot.sound] on every theorem.

**Per-rung bound: `E[T from AllClockGEpCard p n → AllClockGEpCard (p+1) n] ≤ n²`** (crude
uniform form; the `log` sharpening is orthogonal harmonic, same relation as
`coupon_expectedHitting_le_uniform` to `H_n`).  Engine = the invariant-relative coupon
capstone `coupon_expectedHitting_le_uniform_on`, instantiated with:
- potential `seamPot p n c = n − geCount (p+1) c` (the unadvanced count);
- invariant `AllClockGEpCard p n` (`InvClosed` for `3 ≤ p`, `AllClockGEpCard_InvClosed`);
- drop rate `(n−m)·m/(n(n−1))` from `SeamEpidemics.ge_advance_prob` (the advanced×unadvanced
  rectangle), packaged as `seam_hdrop`;
- uniform ceiling `r = n` from `advance_floor_seam` (`(n−m)·m ≥ n−1`), `seamQ_inv_le`;
- start level `M = n − 1` (the advance SEED `1 ≤ geCount (p+1) c`, the counter-drain
  output's deterministic seam advance — at `m = n` the rate is `0`, epidemic stuck, so the
  seed is essential; honest, not a smuggled hypothesis).

**Assembled spine.** `seam_rung_to_chain_target_le_nsq` routes the bound from the bare drain
set `potBelow(seamPot) 1` to the chain target `{AllClockGEpCard (p+1) n}` via the
`InvClosed` slice (same technique as `phase10Majority_link_intersected`).
`chain_two_phase_through_mid` telescopes two consecutive rungs `p → p+1 → p+2` via
`expectedHitting_le_through_mid` (inclusion `AllClockGEpCard (p+2) n ⊆ AllClockGEpCard (p+1) n`),
first summand discharged, band cross-term explicit (the honest cross-phase residual — the
occupation-integral that `through_mid` always leaves, not a seam-specific gap).

**Honest chain-end mechanism.** Seam rungs run at `p ∈ {5,6,7,8}` (`3 ≤ p` role-permanence ∩
`{0,1,5,6,7,8}` counter-timed).  Phases `0,1,2,3,4` = untimed epidemic phases (upstream).
Phase 9: NO counter, NO universal force-to-10 (all-backup route already rejected dishonest,
§SeamPairBound).  Chain end = phase-`8 → 10` epidemic entry into the Phase-10 backup
(`Transition_*_phase_ge_pair_max` `max`-spread → `S1`/`Tie1plus` whp), then `StableBridges`'
Phase-10 bridges close at 0 cost.  The `8→10` backup entry (`O(n log n)`, Lemma 7.7) is the
NAMED remainder — epidemic/backup, not a seam counter-drain rung.

**TimedBigClock/TinyClock ladders reachable.** The strongest reachable per-rung ladder
theorem is the chain-target cap `seam_rung_to_chain_target_le_nsq` (`≤ n²`), which plugs as
the re-shaped rung-1 link feeding `RegimeClassification.ladderData_of_{bigClock,tinyClock}`'s
telescope toward the Phase-10 backup; the residual that genuinely doesn't yield from the seam
engine is the cross-phase band occupation (Part 8 cross-term) + the phase-`8→10` backup entry
(Part 9), both named, not faked.

---

## BandEdges.lean — the two-edge band statement + per-partner placement (2026-06-10, EXIT_0, axiom-clean)

NEW append-only `Probability/BandEdges.lean` (full dep-closure module build EXIT_0 on uisai2 shm;
10 headlines `#print axioms ⊆ [propext, Classical.choice, Quot.sound]`; 0 sorry/admit/axiom/
native_decide; `git diff --check` clean). Closes the two remaining Theorem-6.2-band facts.

### The honest band statement (survey result, NOT the paper headline "3-level band")

Surveyed `MainExponentConfinement` + `UsefulMainFloor`: the landed §6 collapse
(`mainProfile_collapse` via `FrontTail.windowed_floor_crossing`, doubly-exponential descent) exports
the readout `MainProfileConfinedToUseful = 0.92·|M| ≤ #usefulMains` where `usefulMains` is the **CAP**
`index < L` (`biasedMainLtL`), NOT a 3-level band. The doubly-exponential descent pins mass above the
moving front; the landed certificate is the *cap*, with the front descended past it. The paper's
`{−l,−(l+1),−(l+2)}` 3-level band is its *claim* — the landed facts only give the cap.

So the HONEST `MajoritySupportedOn` support is the **two-edge floor/cap band `{l ≤ i ≤ L}`**:
LOWER edge `l ≤ i` PROVEN from the Post (`GapAlignment.majoritySupportedOn_atFloor_of_post`), UPPER
edge `i ≤ L` FREE for `Fin (L+1)`. Width `L − l + 1 = O(log n)` generic — NOT constant. With the
`l+1` seed the lower edge sharpens to `l+1 ≤ i` (`majoritySupportedOn_twoEdge_of_seed`, via
`elim_index_ge_succ_floor`: the seed pins the σ-OPPOSITE band too). This is the honest band fact.

The genuine 3-level band needs ONE carried upper-edge predicate `MajorityTopEdge σ (l+2) c` (the
doubling-collapse TOP-band readout, analogous to `MainProfileConfinedToUseful`). Given it,
`majoritySupportedOn_band3_of_post_topEdge` lands the support on `{l ≤ i ≤ l+2}`, `band3_card_le_three`
proves card ≤ 3, and `exists_band3_level_floor_4n45` derives the paper's `4n/45` pigeonhole constant
(= `BandRouting.exists_band_level_floor_4n45` instantiated at the 3-level band).

### The per-partner placement (task #2) — honest occupancy reduction, not pigeonhole alignment

The pigeonhole gives SOME level ≥ 4n/45; the routing needs the SPECIFIC predecessor of EACH minority.
Honest reduction: seed gives `MinorityAboveFloor σ l c` (minority ≥ l+1); add carried
`MinorityTopEdge σ (l+2) c` (minority ≤ l+2) ⟹ minority confined to `{l+1, l+2}` ⟹ predecessor set
EXACTLY `{l, l+1}` (2 levels). The honest paper fact is **occupancy of BOTH band predecessor levels**
(`TwoLevelOccupancy`: levels `l` and `l+1` each carry ≥ E) — the doubling chain passes through EACH
level on its descent. `gapAlignedElimFloor_of_twoLevel_occupancy`: occupancy + floor + top ⟹
`GapAlignedElimFloor`. NOT "the pigeonhole level happens to align" but "every band predecessor
populated".

Arithmetic against consumer E ≤ 4n/15: 2-level predecessor set `{l,l+1}`, budget 4n/15 ⟹ pigeonhole
SOME level ≥ 4n/30 = 2n/15; occupancy of BOTH at E ≤ 2n/15 ≤ 4n/15 (consumer-compatible,
`twoLevel_constant_le_consumer`). The 2-level `2n/15` is strictly tighter than the 3-level `4n/45`.

### How much closed

* `phase6_to_phase7_of_seed_edges` / `phase6To7_surface_of_seed_edges`: from the SINGLE `l+1` seed
  + A-shape budget `hA` + window `h6` + carried `MinorityTopEdge` + `TwoLevelOccupancy`, the routing
  field `GapAlignedElimFloor` is PRODUCED (not assumed) ⟹ `EliminatorMargins.Phase6To7Structure`,
  PLUS `MinorityAboveFloor` (both signs) + the cancelSplit step-stability.
* Residual reduced to exactly the two named TOP-band readouts (`MajorityTopEdge`/`MinorityTopEdge`)
  + `TwoLevelOccupancy` — all honest doubling-collapse TOP-band content. Every FLOOR half is PROVEN
  from the landed drain (Post + `l+1` seed). The carried residual is now precisely the upper-edge
  collapse readout, matching the `MainProfileConfinedToUseful` carry on the cap side.

---

## Chain-end DELIVERED — `Probability/BackupEntry.lean` (2026-06-10)

The phase-`8 → 10` backup entry (`TimedChainRungs` Part-9 named remainder) is now supplied
in its strongest reachable form, 0-sorry / axiom-clean.

**Honest entry mechanism.** FROZEN `Protocol.Transition` enters phase 10 by exactly two
routes, both `phaseInit`'s `enterPhase10` seam: error-jumps `phaseInit 1` (`mcr`),
`phaseInit 2`/`9` (`biasMagGT1`), and canonical `phaseInit 10`. NO universal force-to-10,
NO phase-9 counter. The SEED is `1 ≤ geCount 10 c` (one agent error-jumped); thereafter the
universal `max`-phase epidemic (`Transition_*_phase_ge_pair_max` = `ge_advance_prob` at `p=9`)
spreads phase 10 to all.

**Assembled chain-end (the three+one deliverables):**
1. first-entry mechanism + expected time: `backup_entry_spread_le_nsq`
   (`E[T → {geCount 10 ≥ n}] ≤ n²`, the seam engine instantiated at `p=9`);
2. epidemic-spread coupon `E ≤ n²` (crude `O(n²)` of the paper's `O(n log n)` parallel);
3. arrival classification: `arrival_classification`
   (`reachable ∧ AllPhase10 ∧ card ∧ gap-sign ⟹ S1 ∨ Tie1plus`), via the conserved
   `phase10ActiveSignedSum = initialGap` (`Phase10Backup`, the correctness half);
4. assembled chain-end: `backup_entry_to_regime_le_nsq`
   (`E[T from seeded phase-8 target → {AllPhase10 ∧ card}] ≤ n²`, routed through the
   `AllClockGEpCard 9 n` `InvClosed` invariant), plus membership endpoints
   `{majority,tie}_chain_end_mem_stableDone` (drained arrival ∈ `StableDone` via the
   `StableBridges` Phase-10 bridges at 0 cost).

**Named protocol-open remainders.** (a) within-Phase-10 cancel/absorb drain
(`wrongACount`/`wrongTCount → 0`, the `Phase10ExpectedTime` 3-stage `O(n² log n)` engine),
additively composed with the `≤ n²` entry by `expectedHitting_le_through_mid`
(`Mid = {AllPhase10 ∧ card}`, `Done = StableDone`); (b) the seed-establishment whp that
`1 ≤ geCount 10 c` from the phase-8 seam exit. Both epidemic-establishment + backup-drain
composition, NOT seam counter-drain rungs — honestly outside the entry engine.

---

## §6 squaring — SupplyRegion.lean: the carried `SupplySubadditive` remainder is a POPULATION fact

`ZeroSupplyDrift.lean` proved the `r = 1` zero-supply drift ON `SupplySubadditive i c` and CARRIED that
region as a `ClockFrontProfile.WindowedFrontProfile` clock-front event. `SupplyRegion.lean` settles its
honest status by reading the FROZEN ledger, and the verdict is: **the region is a population fact, not a
clock event.** The Rule-3 cancel (the sole producer of fresh `Z_i` supply) is a Main-Main interaction
gated only by the role guard — no clock condition — so the suppression is the band/confinement predicate
`NoMinoritySignAbove i σ c` (σ-minority confined to/below the squaring level), a sibling of the LANDED
`MinorityFloorGap.AllBiasedMainAbove` / `GapAlignment.MinorityAboveFloor`, NOT the carried clock front.

**How much of the squaring chain closed (region → drift, hypothesis-free).** The full genuinely-dynamic
core is closed at `r = 1`: region kills the cancel indicator on every pair
(`cancelInd_zero_of_noMinorityAbove`) ⟹ per-pair supply sub-additivity
(`supplyIndic_subadditive_of_region`, exactly the Layer-A engine's input) ⟹ the discharged Phase-3 drift
`∫⁻ Φ dK_phase3(c) ≤ Φ(c)` (`phase3_supplyPotential_drift_le`), with NO clock input. The region is
step-stable up to the split's one-level slack (`phase3CancelSplit_NoMinoritySignAbove_succ`), exact on the
supply-producing cancel branch (`cancel_branch_preserves_ceiling_exactly`) — mirroring `MinorityFloorGap`'s
`l+1` seed dualised to a ceiling. Capstone: `supplyRegion_verdict`.

**Named remainder (genuinely open).** Bridging `NoMinoritySignAbove → ZeroSupplyDrift.SupplySubadditive`
over the full `Transition` dispatcher is the FROZEN per-phase bookkeeping (Phase-3 Main-Main routing +
non-Phase-3 phases producing no fresh `Z_i` supply), not the dynamic content. Everything dynamic — cancel
suppression, drift, stability — is hypothesis-free and clock-free.

**Audit.** All 7 `SupplyRegion` theorems `#print axioms` ⊆ `[propext, Classical.choice, Quot.sound]`;
0 sorry/admit/axiom/native_decide; single-file `lake env lean` clean.

---

## §ChainEndAssembly — assembling the E4 chain-end compositions (2026-06-10)

`ChainEndAssembly.lean` (append-only) closes the two Part-6 named remainders left by
`BackupEntry.lean` and PRODUCES the timed-branch ladders that `RegimeClassification`/`ReachableLadder`
carried as opaque data.

**(a) The composed chain-end bound.** `chainEnd_majority_total_le`: from a reachable, seeded
`AllClockGEpCard 9 n` start with `0 < initialGap init`,
`E[T → StableDone] ≤ n² + 3n²(1+2 log n)`. Mechanism: the entry epidemic to the `S1`-intersected
regime (`entry_to_S1_le_nsq`, `≤ n²`, routing `BackupEntry.backup_entry_to_regime_le_nsq` through the
`ReachableFrom` InvClosed slice — entry-regime ∩ reachable ⊆ S1 by `allPhase10_majority_imp_S1`),
composed with the within-Phase-10 drain (`phase10Majority_drain_to_stableDone_le`, `≤ 3n²(1+2 log n)`,
= `StableBridges` two-rung Phase-10 ladder) via `expectedHitting_seqcomp_of_uniform` (`Mid = {S1 n}`).
Tie analogue: `phase10Tie_drain_to_stableDone_le` (`≤ 2n²(1+2 log n)`).

**(b) The assembled timed ladders.** `timedSpine_ladderData` builds the timed `LadderData` for a
phase-`p` start (`3 ≤ p`, `p+q=10`) by telescoping `{AllClockGEpCard p n} → ⋯ → {AllClockGEpCard 10 n}
→ StableDone` via `RecoveryBridges.expectedHitting_ladder_le` — each clock-phase rung capped `≤ n²` by
`TimedChainRungs.seam_rung_to_chain_target_le_nsq`, the final phase-10 rung by `hfinal`.
`bigClockRegime_of_data`/`tinyClockRegime_of_data` then produce the `ReachableLadder.Timed{Big,Tiny}ClockRegime`
with the `ladder` field BUILT (no longer opaque). Capstone `doty_expected_time_chain_end` re-exports
`doty_expected_time_reachable` with all four regime ladders constructed.

**The seed survey (the key §6 question, answered).** Does E3's drained output supply the per-rung
advance seed? **NO.** A rung's drained output `AllClockGEpCard (p+i) n` gives `geCount (p+i) = n` but NOT
`geCount (p+i+1) ≥ 1`. The next-phase epidemic must be independently seeded (one `enterPhase` advance must
fire) — the same `htrig` shape as the chain-end entry. So `hseed` is a genuine per-rung whp residual, not
discharged by the upstream drain. This is the doctrinal confirmation that the timed spine, like the
chain-end entry, is an epidemic-establishment object: the seeds are honest carried inputs, NOT free.

**Final E4 carried set.** (1) per-regime exhibition `hClassify` (deterministic classification, honest
on a good role-split checkpoint); (2) per-rung advance seeds `hseed` (timed, NOT from E3 output —
survey above); (3) phase-10 entry-drain `hfinal` (Part-1 within-Phase-10 drain + arrival classification);
(4) cross-phase band cross-terms (already absorbed into the per-rung `≤ n²` via the InvClosed slice);
(5) Lemma-5.2 clock floors `hFloors` (the floor value `mC`). Everything else — spine, telescope,
seqcomp/ladder transfer, reachability split-geometric, whp composition — DISCHARGED.

**Audit.** 8 headlines `#print axioms` ⊆ `[propext, Classical.choice, Quot.sound]`;
0 sorry/admit/axiom/native_decide; single-file `lake env lean` EXIT_0; whitespace clean.

---

## STATUS (2026-06-10) — phase-dispatch bridge landed in `Probability/SupplyDispatch.lean`

The phase-dispatch BRIDGE `NoMinoritySignAbove → ZeroSupplyDrift.SupplySubadditive` over the FULL
multi-phase `Transition` dispatcher (the named remainder of `SupplyRegion.lean`) is now closed —
*scoped honestly* to the §6 squaring window — in NEW append-only file `Probability/SupplyDispatch.lean`.
No existing file edited. Single-file `lake env lean` EXIT_0; all headlines `#print axioms ⊆ [propext,
Classical.choice, Quot.sound]`; no sorry/admit/axiom/native_decide.

### The honest verdict on the bridge (the genuinely new content)

`ZeroSupplyDrift.SupplySubadditive i c` quantifies the supply indicator
`supplyP i a := a.bias = .zero ∧ i < a.hour.val` over the FULL `Transition L K`, NOT over
`phase3CancelSplit`. A per-phase audit of the FROZEN `Transition` (epidemic update → phase dispatch →
finishPhase10Entry) reveals that the Main-Main Phase-3 cancel is NOT the only thing that can set
`bias = .zero` at `hour > i`: the Phase-3 Rule-2 hour-DRAG (Main-Clock; re-stamps an existing zero's
hour) and the Phase-6/7/8 CANCELS (dyadic → `.zero` keeping `hour`) are genuinely SEPARATE fresh-supply
sources that `NoMinoritySignAbove` (which only caps the σ-minority's dyadic EXPONENT index, not zero
hours) does NOT control. So an UNCONDITIONAL `NoMinoritySignAbove → SupplySubadditive` over the full
dispatcher is **FALSE**. The honest bridge therefore scopes to the **Phase-3 Main-Main squaring
window** `Phase3MainMainWindow c := ∀ a ∈ c, a.phase.val = 3 ∧ a.role = .main` — the level-`i` squaring
regime where the only supply source is the region-controlled Main-Main cancel (the drag needs a Clock
interactor; the later cancels are out of window). The separate sources belong to different §6
sub-arguments, not the level-`i` squaring; they are audited here as honest field-level facts, NOT
folded into the region.

### Per-phase supply audit table (PROVEN as Lean field-level facts)

| phase | rule(s) writing `bias`/`hour`             | fresh `Z_i` supply? | lemma |
|-------|-------------------------------------------|---------------------|-------|
| epidemic `phaseInit p=3` | `bias := newBias`, `hour := 0`    | NO (zeros stamped `hour=0 ≤ i`) | (doc) |
| epidemic `enterPhase10`  | preserves `bias`/`hour`            | NO | `enterPhase10_supplyP` |
| `finishPhase10Entry`     | preserves `bias`/`hour`            | NO | `finishPhase10Entry_supplyP` |
| Phase 0 | role/smallBias/assigned/counter only       | NO | (doc; clock-counter ⊆ phase≤2 init) |
| Phase 1 | smallBias (Fin 7) averaging, clock counter | NO | `phase1_supplyP_neutral` |
| Phase 2/9 | opinions/output/phase-init only          | NO (stay branch) | `phase2_supplyP_neutral_of_stay` |
| **Phase 3 cancel (Main-Main)** | `bias:=.zero, hour:=j` for `±j` pair | **SOLE region-controlled source** (SupplyRegion) | — |
| Phase 3 split (Main-Main)| `bias := .dyadic …`                | NO (REMOVES supply) | `phase3_split_supplyP_false` |
| Phase 3 hour-drag (Main-Clock) | re-stamps existing zero's `hour` | SEPARATE clock-coupled (off-window) | (doc) |
| Phase 4 | phase advance only                          | NO | `phase4_supplyP_neutral` |
| Phase 5 | `hour:=exponentOf`, `bias:=.dyadic`         | NO (dyadic writes REMOVE) | (doc) |
| Phase 6/7/8 cancel | `bias:=.zero` keeping `hour`     | SEPARATE later-phase (off-window) | (doc) |
| Phase 10 | output/full only                           | NO | `phase10_supplyP_neutral` |

### The bridge chain (PROVEN)

1. `phaseEpidemicUpdate_id_of_phase3` — epidemic update is the identity on a same-Phase-3 pair.
2. `Transition_eq_phase3CancelSplit_of_phase3_main` — the FULL `Transition` reduces to
   `phase3CancelSplit` on a Phase-3 Main-Main pair (epidemic + finishPhase10 wrappers vacuous,
   Phase-3 Rules 1–2 clock-gated vacuous when both Main).
3. `supplyIndic_subadditive_Transition_of_region` — per-pair supply sub-additivity of the FULL
   `Transition` on the region (via #2 + SupplyRegion's `supplyIndic_subadditive_of_region`).
4. `supplySubadditive_of_region` — the full-dispatcher `ZeroSupplyDrift.SupplySubadditive i c` on a
   window+region config (the carried region discharged from the POPULATION fact alone).
5. `supplyPotential_drift_le_of_window` — the `r=1` zero-supply drift `∫⁻ Φ dK(c) ≤ Φ(c)` over the
   REAL `NonuniformMajority` kernel (not just the `phase3Protocol` sub-protocol).
6. `integerProfileSquaring_whp_of_window` — the whp hour-boundary tail with `SupplySubadditive`
   supplied BY the window (no carried clock region in the drift input).
7. `hConfine_of_window` — the strongest hypothesis-free Thm 6.2 `hConfine` form reachable.

### The final `hConfine` carried set (after this bridge)

`hConfine_of_window` ⟹ `UsefulMainFloor.Theorem62EntryHypotheses` (carrying `hConfine`) carries exactly:
(a) `IntegerProfileSquaring θ c` — the whp-realised hour coupling (its drift now discharged BY the
    window via `integerProfileSquaring_whp_of_window`, no carried clock event);
(b) `ClockFrontProfile.WindowedFrontProfile θ c` — the landed clock window;
(c) `mainFrac 0 c ≤ 1/10` — the sub-critical Main fraction;
(d) `ReserveSampling.Phase5AllWin n c` + `n/3 ≤ mainCount c` — the landed Phase-5 window + role floor;
(e) `MainExponentConfinement.MainProfileConfinedToUseful c` — the confinement readout (def'lly `hConfine`).
The phase-dispatch supply region over the FULL `Transition` is now CLOSED (population window), not
carried as a clock event.

**Audit.** All headlines `#print axioms ⊆ [propext, Classical.choice, Quot.sound]`; 0
sorry/admit/axiom/native_decide; single-file `lake env lean` EXIT_0; `git diff --check` clean.

## ROUND 1–6 CONSOLIDATION (2026-06-10/11 night)

Six residual-attack rounds complete (18 agents, all 0-sorry axiom-clean). Every
original residual is now either CLOSED or reduced to precisely-named events.

### CONSOLIDATED CARRIED SET (everything else proven)
Window/positional events (deterministic shapes, provenance = §6 clock Posts):
- AllBiasedMainBelow (l+2) — the hour ceiling (DoublingEdges)
- Phase3MainMainWindow — the squaring window (SupplyDispatch)
- ClockFrontProfile.WindowedFrontProfile + mainFrac 0 ≤ 1/10 (hConfine set)
Timing/whp events:
- PredecessorLevelsCoPopulated (occupancy timing, DoublingEdges)
- per-rung advance seeds hseed + chain-end seed establishment (ChainEndAssembly)
- IntegerProfileSquaring's hour-coupling readout (drift discharged by window)
Classification/floors:
- hBranch/hClassify (reachable regime exhibition, checkpoint-conditional)
- hFloors (Lemma-5.2 clock-floor value propagation)
Spend/entry plumbing:
- Phase-7 entry SurvivalBandAbove start (= #2 chain outputs, now produced)

### Next: window-event reconciliation (map each carried window event to the
landed §6/clock Posts and discharge those that are already exports), then the
1/n² budget tightening sweep, then Phase F.

## WINDOW-EVENT RECONCILIATION (2026-06-10) — `Probability/WindowReconciliation.lean`

New append-only file (0-sorry, axioms ⊆ {propext, Classical.choice, Quot.sound}).
Each of the three carried WINDOW/POSITIONAL events resolved.

### Per-item reconciliation table

| # | Carried event | Verdict | Provenance / bridge |
|---|---------------|---------|---------------------|
| 1 | `DoublingEdges.AllBiasedMainBelow (l+2)` (hour ceiling) | **BRIDGE proven; 2 named minimal missing snapshots** | reduced via `allBiasedMainBelow_of_indexLeHour_of_hourCeiling` to (a) `BiasedMainIndexLeHour c` and (b) `MainHourBelow (l+2) c` |
| 2 | `SupplyDispatch.Phase3MainMainWindow` (all-Main squaring window) | **CORRECTED SCOPING** | all-Main window is FALSE in real chain (clocks in phase 3); the honest replacement is region + `MainClockDragBounded` (clock-front ceiling = item 1) |
| 3 | `ClockFrontProfile.WindowedFrontProfile θ` + `mainFrac 0 ≤ 1/10` | **DISCHARGED (landed exports)** | already the literal clock-set hypotheses of `SupplyDispatch.hConfine_of_window`; re-exported as `hConfine_of_windowReconciled` |

### Item 1 — the hour ceiling: bridge + minimal missing exports

`AllBiasedMainBelow top` (snapshot: every biased Main's INDEX ≤ top) splits into two
clock-front snapshots, with a fully-proven transitivity bridge:

* **`BiasedMainIndexLeHour c`** — every biased Main's index ≤ its OWN hour.  This is the
  SNAPSHOT form of the FROZEN doubling guard (`phase3CancelSplit` raises `i→i+1` only when
  `hour > i`, so the front never exceeds the hour stamp).  Per-step preservation is LANDED
  (`DoublingEdges.phase3CancelSplit_preserves_top_edge`, re-exposed here as
  `allBiasedMainBelow_step_of_topEdge`).  **Minimal missing clock export #1** = its
  reachability/invariant SNAPSHOT form (induct the per-step guard over the chain).
* **`MainHourBelow top c`** — every Main's hour ≤ top.  **Minimal missing clock export #2**
  (provenance: `HourCouplingV2.Window` / clock-front "hour-stamps ≤ window index").

`allBiasedMainBelow_of_indexLeHour_of_hourCeiling : BiasedMainIndexLeHour → MainHourBelow top
→ AllBiasedMainBelow top` (PROVEN, transitivity).  Composed with the landed
`majorityTopEdge_of_hourCeiling` ⟹ `majorityTopEdge_of_indexLeHour_of_hourCeiling` (the routing
consumer's snapshot top edge from the two snapshots).  No clock-front PROBABILITY is re-proved;
item 1 is reduced to two named deterministic snapshots.

### Item 2 — corrected Phase-3 window scoping (THE VERDICT)

`Phase3MainMainWindow` (every agent Phase-3 Main) is **FALSE in the real chain** — clocks are
present in Phase 3.  The all-Main window is the convenient special case that kills the
**Phase-3 Rule-2 Main-Clock hour-drag** (`Transition.lean:755`: an unbiased Main meeting a Clock
gets `hour := min L (clock.minute / K)`).

Honest answer to "is the drag a real `Z_i` source inside the window?": **YES.**  If
`min L (clock.minute / K) > i` the drag pushes a `.zero` agent from `hour ≤ i` to `hour > i` —
a fresh `supplyP i` agent.  So inside a mixed window the region `NoMinoritySignAbove` ALONE does
NOT control supply; the drag needs the **clock-front hour ceiling**, which is exactly item 1.

Delivered:
* `phase3Transition_mainClock_eq` — the dispatch readout: on a Main-Clock pair `Phase3Transition`
  returns `({s with hour := min L (t.minute/K)}, t)` (PROVEN).
* `phase3_mainClock_drag_supplyP_subadditive` — under `min L (t.minute/K) ≤ i` the drag output
  Main is NOT `supplyP i` (hour ≤ i) and the Clock output = input ⟹ no fresh supply (PROVEN).
* `MainClockDragBounded i c` (every Clock's `min L (minute/K) ≤ i`) +
  `mainClock_drag_neutralised_of_dragBounded` — the corrected mixed-window control: Main-Main by
  the population region (landed), Main-Clock by the clock-front bound.

**Verdict:** SupplyDispatch's `Phase3MainMainWindow` is honest only as the clock-free special
case.  The faithful mixed-window scoping carries the extra `MainClockDragBounded` side condition,
and that drag-control IS item 1's clock-front ceiling.  Items 1 and 2 are COUPLED: the same
hour ceiling discharges both.

### Item 3 — discharged: two landed §6 exports

`WindowedFrontProfile θ c` (landed `ClockFrontProfile`, the §6 width-chain tail-fraction squaring
window) and `mainFrac 0 c ≤ 1/10` (landed sub-critical Main fraction `c_{≥0} ≤ 0.1`) are NOT
residuals — they are the literal clock-set inputs of `SupplyDispatch.hConfine_of_window`.
`hConfine_of_windowReconciled` re-exports the `hConfine` surface naming them as the carried set.

### Updated strongest end-to-end surfaces (final carried sets)

* **`phase6To7_surface_reconciled`** ⟹ `EliminatorMargins.Phase6To7Structure σ E c`.
  Carried set: `BiasedMainIndexLeHour c`, `MainHourBelow (l+2) c` (item-1 snapshots), the `l+1`
  seed, the A-shape budget, the Phase-6 window, the `PredecessorLevelsCoPopulated` timing event.
* **`hConfine_of_windowReconciled`** ⟹ `UsefulMainFloor.Theorem62EntryHypotheses n c` (carries
  `hConfine`).  Carried set: `WindowedFrontProfile θ c` + `mainFrac 0 ≤ 1/10` (landed Posts),
  the whp `IntegerProfileSquaring` coupling (drift discharged BY the window), the landed Phase-5
  window, the role-split Main floor `n/3 ≤ mainCount`, the confinement readout
  `MainProfileConfinedToUseful`.  The phase-dispatch supply region over the FULL `Transition` is
  CLOSED (Main-Main: population window; Main-Clock drag: item-1 clock-front ceiling).

### Net after reconciliation
The §6-clock part of the carried set is now exactly THREE named deterministic snapshots —
`BiasedMainIndexLeHour`, `MainHourBelow`, `WindowedFrontProfile` — plus `mainFrac 0 ≤ 1/10`
(landed) and the whp coupling (drift discharged).  The Main-Clock hour-drag, previously listed as
a SEPARATE uncontrolled source, is now controlled by the SAME hour ceiling that discharges item 1.

### Next: the reachability-invariant SNAPSHOTs for `BiasedMainIndexLeHour` / `MainHourBelow` /
`MainClockDragBounded` (induct the landed per-step facts over the chain), then the 1/n² budget
tightening sweep, then Phase F.

---

## 1/n² BUDGET TIGHTENING SWEEP (2026-06-10) — `Probability/BudgetTightening.lean`

The dad-approved cleanup item is DONE. New append-only file `Probability/BudgetTightening.lean`
(no existing file edited). The sweep's verdict: **every per-instance budget was already
calibrated at the `n⁻²` flavor; the ONLY place `1/n` entered was the composite union target**
(`hδ : ∑ δ ≤ 1/n`) in the headlines/E4. The tightening is therefore pure re-instantiation of
the SAME parametric composition arithmetic at the `C/n²` target — no engine reopened, no
window lengthened, no constant bumped.

### Budget table (per-instance landed vs. `n⁻²`-target)

| instance / engine                       | landed ε                        | target | status / lemma                            |
|-----------------------------------------|---------------------------------|--------|-------------------------------------------|
| RoleSplit work₀ (3-stage)               | `εRole = 1/n²` (Janson)         | `1/n²` | already n⁻² (`roleSplitTail_le_inv_sq`)   |
| Phase 1/5/6/7/8 drains (OneSidedCancel) | `budgetNN = 1/(M₀ n²)`          | `1/n²` | already n⁻² (`budgetNN_le_inv_sq`)        |
| Phase-0 floor prefix                    | `εfloor = n⁻²`                  | `1/n²` | already n⁻² (`floor_prefix_le_inv_sq`)    |
| Phase-3 §6 seam side budget `sideEps`   | parametric (εQ…εWAt…εsucc)      | `1/n²` | parametric (calibrate width slice → n⁻²)  |
| 10 seam epidemics                       | `εepidemic + εovershoot`        | `1/n²` | parametric (geometric tail `hε` → n⁻²)    |
| **composite union (`hδ`)**              | **`∑ δ ≤ 1/n`**                 | `C/n²` | **BOTTLENECK — was the SOLE `1/n` site**  |

The headline-summary line "the headline consumed `hδ ≤ 1/n` at one point" resolves HERE: the
`1/n` lived ONLY at `DotyTimeHeadline.doty_time_headline_W2`'s `hδ` and the identical
`DotyExpectedTime.doty_expected_time`'s `hδ` — the union step that DISCARDED the per-instance
`n⁻²` calibration. Summing 21 instances each `≤ 1/n²` gives `∑ ≤ 21/n² = O(1/n²)`, strictly
tighter than `1/n` for `n ≥ 21` (`inv_sq_const_le_inv`). No bottleneck term was at `1/n`
intrinsically — all 21 engines deliver `n⁻²`.

### What was tightened (the 7 new theorems, all 0-sorry axiom-clean)

* `sum_inv_sq_le` — 21 instances each `≤ 1/n²` ⟹ `∑ ≤ 21/n²` (the recovered composite).
* `inv_sq_const_le_inv` / `inv_sq_const_chain` — `C/n² ≤ 1/n` for `C ≤ n` (certifies the
  tightening is a genuine improvement, and bridges to any downstream `1/n` consumer).
* `doty_time_headline_W2_tight` — the seam-corrected 21-instance headline RE-STATED at
  `hδ : ∑ δ ≤ C/n²`, concluding failure `≤ C/n²` (vs. the old `≤ 1/n`). Time bound unchanged
  `T ≤ 21·C0·n·(L+1)`.
* `doty_time_headline_W2_inv_sq` — the drop-in `C = 21` instantiation: each `δᵢ ≤ 1/n²`
  ⟹ composite failure `≤ 21/n²`, the honest tightest composite headline.
* `doty_expected_time_tight` — E4/E[T] re-stated at the `C/n²` good-horizon budget,
  conclusion `E[T] ≤ Cexp·n·(L+1)` preserved.
* `recovery_term_inv_sq` — the exact E4 recovery-term magnitude at the tightened budget:
  `(C/n²)·sRecover·(1−1/2)⁻¹ = 2C·sRecover/n²` (vs. the `1/n` value `2·sRecover/n`).

### The E4 (Cexp) impact

`δgood` enters `E[T] ≤ Tgood + δgood·sRecover·(1−1/2)⁻¹`. Replacing `δgood = 1/n` by `21/n²`
divides the recovery contribution by `n/21`: from `2·sRecover/n` down to `42·sRecover/n²`.
With the campaign's `sRecover = 2·Brecover` and E2-dominated `Brecover = O(n²(L+1))`:
* old `1/n` form: recovery `= O(n(L+1))` — the dominant-order term forcing `Cexp = 21·C0 + 4·Cbad`;
* new `n⁻²` form: recovery `= O(L+1)` — LOWER order than the `O(n(L+1))` good horizon.

So under the tightened budget the recovery term drops out of `Cexp`'s leading constant:
`E[T] ≤ 21·C0·n·(L+1)` up to lower-order, the recovery is asymptotically free. The `Cbad`
contribution to `Cexp` is a consequence of the loose `1/n`, not intrinsic.

**Audit.** 7/7 new theorems `#print axioms ⊆ [propext, Classical.choice, Quot.sound]`; 0
sorry/admit/axiom/native_decide; single-file `lake env lean` EXIT_0; `git diff --check` clean.

---

## PHASE F — campaign-wide audit + full explicit-module build (2026-06-11)

Independent verification sweep over the ENTIRE ExactMajority campaign closure on uisai2
`/dev/shm` (toolchain `v4.30.0`, mathlib rev `c5ea00351c28e24afc9f0f84379aa41082b1188f`,
shared bucket reused — `Built Mathlib` lines = 0). New append-only audit file
`Probability/PhaseFAudit.lean` (imports the live closure; runs `#print axioms` on the
end-to-end surfaces). No existing file edited.

### 1. Full explicit-module build (the closure-skip discipline, demonstrated)

The campaign tree holds **168** `*.lean` files. Building any single headline ROOT silently
skips most of them — measured transitive-import closures:
* `Analysis.MainTheorem` root → 6 / 168 (skips 162)
* `Probability.DotyTimeHeadline` root → 23 / 168 (skips 145)
* `Probability.DotyExpectedTime` root → 43 / 168 (skips 125)

There are **32 LEAF modules** imported by no other campaign file (today's residual-attack
bricks: `BudgetTightening`, `WindowReconciliation`, `ChainEndAssembly`, `PartnerMargin`,
`NumericInstances`, `BandStepBookkeeping`, … plus 4 dead scaffolds below). A root build
would never compile them. The Phase-F build therefore passes **all module targets explicitly**.

**Build verdict (live closure):**
* Explicit targets: **164** live campaign modules + the `PhaseFAudit` file = 165 targets.
* explicit-target build → **last job marker `[3681/3681]`** (genuinely larger than any
  bare-root closure; mathlib reused, `Built Mathlib` = 0), **EXIT 0**.
* olean landing: **164 / 164** live campaign oleans + the audit olean all present on disk.

### 1a. THE 4 DEAD ORPHANS (honest finding — the discipline caught these)

Four files FAIL to compile and are imported by NOTHING in the campaign (only the audit file's
full-closure import touched them). They are dead scaffolds/superseded drafts, invisible to any
root build:

| orphan module | failure | status |
|---|---|---|
| `Basic/PhaseState.lean` | parse error `unexpected '/--'; expected 'lemma'` — orphan docstrings before `end`; explicit TODO placeholder, contains NO declarations | dead placeholder (per-phase state-narrowing TODO) |
| `Probability/DiscreteChernoff.lean` | duplicate decls `geometricProductMGF`/`milestone_tail_bound_via_mgf`/`janson_exponential_tail_from_mgf` already declared | superseded by `JansonHitting.lean` + `RoleSplitConcentration.lean` |
| `Probability/StepPreservation.lean` | `Unknown identifier ae_of_stepDistOrSelf_support_preserved`, `Unknown constant Multiset.tsub_le_self` | early draft; live machinery in `MarkovChain`/`Invariants`/`SupportInvariants` |
| `Probability/DescentPotential.lean` | `Unknown identifier ae_of_stepDistOrSelf_support_preserved` | early draft, same superseding |

These are **not** in the verified end-to-end surface and **not** part of today's work; they were
left edited-out of the import graph. Recommendation: delete (or move to an `attic/`) in a
follow-up — NOT done here because Phase F is forbidden from editing existing files. The verified
campaign is the 164-module live closure.

### 2. Audit verdicts

* **(a) Grep-level (comment-stripped, all 168 files):** `0` occurrences of
  `sorry`/`admit`/`native_decide` and `0` `axiom` declarations in code. (All textual hits are
  inside the "no sorry/admit" boilerplate of docstrings/comments.)
* **(b) `#print axioms` (independent refresh, 24 end-to-end / reconciliation / budget
  theorems):** every one depends only on a subset of `[propext, Classical.choice, Quot.sound]`;
  `sorryAx` count = **0**. Specifically the end-to-end headlines
  `doty_time_headline_W`, `doty_time_headline_W2`, `doty_expected_time`,
  `doty_expected_time_concrete`, `total_time_le_W`, `total_error_le_W`, `state_count_eq`,
  `state_count_poly_bound`; the 8 `WindowReconciliation` theorems; the 7 `BudgetTightening`
  theorems — all axiom-clean.
* **(c) Whitespace (`git diff --check`):** clean across the tree and on the new audit file
  (EXIT 0).
* **Non-fatal:** 4 mathlib-linter `warning:`-prefixed "doc-strings should start with a single
  space" notes (`AeBridge.lean`, `ArithmeticHelpers.lean`) — warnings, NOT errors; those modules
  build and land oleans. `^error:` count in the audit build = 0.

### 3. THE DEFINITIVE CARRIED-HYPOTHESIS INVENTORY (machine-checked against code)

What stands between the current state and a hypothesis-free Theorem 3.1. Two end-to-end
surfaces carry hypotheses; verified binder-by-binder against the actual `.lean`.

**A. The TIME / EXPECTED-TIME headline surface** (`doty_time_headline_W` /
`doty_time_headline_W2` / `doty_expected_time`, `DotyTimeHeadline.lean` /
`DotyExpectedTime.lean`). The headline is parametrized — its carried inputs are explicit binders:

| # | binder | statement | what discharges it |
|---|--------|-----------|--------------------|
| C1 | `phases : Fin 11 → PhaseConvergenceW (NonuniformMajority L K).transitionKernel` | the 11 per-phase whp-convergence instances (each proven in its own file; carried as a function argument, not assembled into one chain) | assemble the 11 landed phase instances into the family literal (each Pre/Post is the file's proven Post) |
| C2 | `h_chain : ∀ i (hi), ∀ x, (phases i).Post x → (phases ⟨i+1,_⟩).Pre x` | the 10 cross-phase bridges | **W version: FALSE pointwise** (each window pins a distinct `phase.val`, so `Post_i ∧ Pre_{i+1}` is contradictory — satisfiable only on the empty config). The honest fix is `doty_time_headline_W2`, where the bridge is the `advancePhase` epidemic TRANSITION (`ChainBridges`), carried as a named transition input. **This is the single deepest residual.** |
| C3 | `hx₀ : (phases 0).Pre c₀` | the start (validInitial → role-split-entry) | deterministic-reachable `Analysis/` invariant |
| C4 | `h_post : ∀ c, (phases 10).Post c → majorityStableEndpoint init c` | the closing map | deterministic-reachable |
| C5 | per-phase drains folded into each `phases i` | `OneSidedCancel` rectangle floors (Phases 0/1/5/6/7/8 `q`/`hstep`); Phase-3 `hside` (τ-uniform `Sgood(T)ᶜ ≤ sideEps`, 9 named §6 feeders + width slice `εWAt`); Phase-5 `hConc`; the Lemma-5.2 clock floor | the consolidated B/D-residuals (threaded, not re-opened) |
| C6 | `hC0`, `hδ`, `ht` scaling | `Cphase i ≤ C0`, `∑ δ ≤ 1/n` (now tightenable to `C/n²` per `BudgetTightening`), `t_i ≤ Cphase_i·n·(L+1)` | proven composition arithmetic (CLOSED) |

**B. The §6-CLOCK / SUPPLY surface** (reconciled in `WindowReconciliation.lean`). After Phase-D
reconciliation the §6-clock carried set is exactly **THREE named deterministic snapshots** plus
landed Posts:

| # | binder | file:def | statement | what discharges it |
|---|--------|----------|-----------|--------------------|
| S1 | `BiasedMainIndexLeHour c` | `WindowReconciliation.lean:89` | `∀ a ∈ c, a.role=main → ∀ s i, a.bias=dyadic s i → i.val ≤ a.hour.val` (every biased Main's index ≤ its own hour) | the reachability-invariant SNAPSHOT of the FROZEN doubling guard (per-step preservation LANDED as `phase3CancelSplit_preserves_top_edge`; induct it over the chain) |
| S2 | `MainHourBelow top c` | `WindowReconciliation.lean:97` | `∀ a ∈ c, a.role=main → a.hour.val ≤ top` (every Main's hour ≤ top) | the clock-front hour-stamp ceiling SNAPSHOT (provenance `HourCouplingV2.Window`); induct over the chain |
| S3 | `WindowedFrontProfile θ c` + `mainFrac 0 c ≤ 1/10` | `ClockFrontProfile` / `MainExponentConfinement` | the §6 width-chain tail-fraction squaring window + sub-critical Main fraction `c_{≥0} ≤ 0.1` | **LANDED §6 exports** (NOT residuals — literal clock-set inputs of `hConfine_of_windowReconciled`) |
| S4 | `IntegerProfileSquaring θ c` (whp coupling) | `ProfileSquaringRate` | the hour-coupling readout | the drift is **discharged BY the window**; remaining = whp realisation |

Note `MainClockDragBounded i c` (`:152`) — the Phase-3 Rule-2 Main-Clock hour-drag, once listed
as a SEPARATE uncontrolled `Z_i` supply source — is now controlled by the SAME hour ceiling
(S1/S2): `mainClock_drag_neutralised_of_dragBounded` (PROVEN) shows the drag produces no fresh
supply under `min L (minute/K) ≤ i`. Items 1 and 2 are coupled.

**C. The classification / floor residuals** (Phases 6–8 eliminator surface):
* `hBranch`/`hClassify` — reachable regime exhibition (checkpoint-conditional).
* `hFloors` — Lemma-5.2 clock-floor value propagation.
* Phase-7 `hmono : PotNonincrOn Inv7Sum K minorityU` (`Phase7Convergence.lean:1188`) — the
  per-step `minorityU` non-increase certificate, carried as the honest Phase-7 residual (replaced
  the broken `MinorityHiIdx`-carrying `Inv7Main`; the eliminator floor is the carried Doty
  Lemma 7.4/7.6 `≥0.8|M|` majority-vs-minority invariant).
* `hConfine` (`UsefulMainFloor.Theorem62EntryHypotheses`, field) — Theorem 6.2's `0.92·|M|`
  confinement, carried as ONE named fact with paper provenance (the partition arithmetic around
  it is PROVEN).
* Phase-6→7 timing: `PredecessorLevelsCoPopulated` (occupancy timing) + per-rung advance seeds
  (`AllBiasedMainAbove (l+1)`).

**Inventory count: ~17 named carried hypotheses** across the three surfaces — C1–C6 (6, with
C2 the deepest), S1–S4 (4, of which S3/S4 are landed/discharged → ~2 genuinely open snapshots),
plus the ~5 classification/floor/timing residuals (C-block). Every one is a NAMED binder with a
documented discharge route; none is an axiom, sorry, or vacuous marker. The composition
arithmetic, the C-K assembly, the headline scaling, the budget tightening, and the supply-region
dispatch are all CLOSED and axiom-clean.

### 4. Recommendation on the main push

**Workspace origin main + opus-wip mirror: READY.** The new `PhaseFAudit.lean` is 0-sorry,
axiom-clean (EXIT 0), and the report is append-only. Push both as usual.

**Public `xiangyazi24/Ripple` main: NOT yet — owner's call.** A bare default-target build (the
whole `Ripple` lib) currently fails because the 4 dead orphan files (§1a) are in the tree and
broken; until they are removed/attic'd, a clean build on a fresh checkout is not green. The
verified deliverable is the **164-module live closure** (EXIT 0, axiom-clean), but the public-main
"build green + 0 sorry + audit" 铁律 needs the orphan cleanup first, and the Theorem-3.1 headline
still carries the named inventory above (notably C2: the `h_chain` bridges are honest only in the
`W2` advancePhase-epidemic form). Recommend: (1) attic the 4 orphans, (2) confirm the bare default
target green, (3) then the owner decides on the public push.

---

## F1 + F2 audit fix — the honest kernel-level `hConfine` surface (append-only)

Independent adversarial audit (`/tmp/opus_audit_report.md`) flagged two compounding faithfulness
defects in the §6-clock confinement surface. Both are now fixed in the new append-only file
`Probability/ConfinementSurface.lean` (no existing file edited; the misleading wrappers are
corrected by doc-note + honest replacement, not by editing their code).

### What was wrong

* **F1 (CRITICAL — inert mechanism / dead `let`).**
  `ZeroSupplyCoupling.hConfine_surface_of_zeroSupply` (`ZeroSupplyCoupling.lean:308`) and its two
  re-exports `SupplyDispatch.hConfine_of_window` (`SupplyDispatch.lean:429`) and
  `WindowReconciliation.hConfine_of_windowReconciled` (`WindowReconciliation.lean:244`) all had the
  proof term `let _hH := mainHourHypotheses_of_zeroSupply_whp hClock hSubcrit hcoupl;
  theorem62_entry_of_confinement hPhase5 hMainFloor hConf`. The three §6 inputs fed ONLY the dead
  `let _hH` (never used); the output `hConfine` field is the input `hConf` re-emitted verbatim
  (both = `0.92·|M| ≤ #usefulMains`). The surfaces were pure REPACKAGINGS of an assumed
  confinement, masquerading as squaring-window derivations.

* **F2 (FALSE-on-reachable).** The carried `hcoupl : IntegerProfileSquaring θ c` is the
  DETERMINISTIC pointwise form the campaign ITSELF proved order-impossible
  (`ZeroSupplyCoupling.integerProfileSquaring_order_impossible`). The honest object is the whp event,
  not the deterministic predicate.

* **Orphan diagnosis.** The genuine kernel-level theorem
  `MainExponentConfinement.theorem6_2_main_confinement_whp` (the whp confinement event bound from a
  per-hour-union budget) was UNUSED by any consumer — the chain ran entirely on the pointwise
  repackaging instead. The mechanism existed and was never wired in.

### The honest fix (`Probability/ConfinementSurface.lean`)

The confinement readout cannot be derived at a single reachable config (that IS F2). The honest
object is **kernel-level**: `(transitionKernel ^ T) c₀ {¬ confinement} ≤ η`.

* `mainConfinement_kernel_whp` — the honest kernel-level confinement surface. **Hypothesis set:**
  `(n : ℕ)`, `(η : ℝ≥0∞)`, `(phase3to5Time : ℕ)`, `(c₀ : Config)`, and the SINGLE honest input
  `hHourTail : (transitionKernel ^ phase3to5Time) c₀ {c | ¬ ConfinementEvent c} ≤ η`. Concludes the
  same kernel-power event bound. Routes through the previously-orphaned
  `theorem6_2_main_confinement_whp` (now wired in). Carries NO pointwise confinement and NO
  deterministic `IntegerProfileSquaring`.
* `confinement_hour_tail` — the per-hour single-hour squaring brick (LANDED
  `main_profile_hour_squaring` = `WindowConcentration.windowDrift_tail` at the Main profile),
  re-exported so the union budget `hHourTail` is grounded in the real §6 engine (Stage-1 zero-supply
  ledger → Stage-2 single-hour drift → all-hours union), not a pointwise assumption.
* `confinement_event_whp` / `hConfine_kernel_of_window` / `hConfine_kernel_of_windowReconciled` —
  the three downstream surfaces RE-STATED honestly at the kernel level (one per flagged file), each
  consuming `mainConfinement_kernel_whp`. Same honest hypothesis set (the union budget); no
  order-false deterministic squaring carried.
* `theorem62_entry_is_repackaging` — the corrective doc-note theorem: building
  `Theorem62EntryHypotheses` from an ASSUMED confinement + Phase-5 window + role floor is a pure
  repackaging (= `theorem62_entry_of_confinement`); the old wrappers' `hClock`/`hSubcrit`/`hcoupl`
  binders were inert decoration. Stated WITHOUT the decorative §6 inputs to make that explicit.

### Corrected carried inventory for the `hConfine` chain

| object | OLD (flagged) carried set | NEW honest carried set |
|---|---|---|
| confinement surface | pointwise `hConf : MainProfileConfinedToUseful` + dead-`let` §6 inputs (`hClock`, `hSubcrit`, `hcoupl = IntegerProfileSquaring`, order-FALSE) | kernel-level union budget `hHourTail : (Kᵀ)c₀{¬confinement} ≤ η` (the honest per-hour squaring tails composed) |
| §6 squaring entry | deterministic `IntegerProfileSquaring θ c` (false on reachable configs, F2) | whp per-hour drift inside `hHourTail` (via `confinement_hour_tail`, the LANDED `windowDrift_tail`) |
| Theorem-6.2 entry hyps | `theorem62_entry_of_confinement` reached via dead-`let` wrapper (impostor) | reached honestly from the event success or, as repackaging, named explicitly `theorem62_entry_is_repackaging` |

### Status of the old wrappers

The three old per-config `hConfine_*` surfaces remain in the tree (not edited per discipline) but are
now documented as pure repackagings; the honest derivation is `mainConfinement_kernel_whp`.
Consumers wanting a derivation (not a repackaging) must route confinement as a kernel-level event,
never assume it pointwise (F2). Single-file `lake env lean` EXIT 0; `#print axioms` ⊆
`[propext, Classical.choice, Quot.sound]` for all six new theorems.

---

## F3 audit fix — Phase-7 `hmono : PotNonincrOn Inv7Sum K minorityU` is FALSE; replaced by σ-class mass (append-only)

**Audit finding (F3, `/tmp/opus_audit_report.md`).** The Part-I Phase-7 surface
`Phase7Convergence.phase7Convergence'` (`Phase7Convergence.lean:1200`) carried
`hmono : PotNonincrOn Inv7Sum K minorityU` — a *deterministic* per-step non-increase of the
minority **count** `minorityU σ`. The file's OWN proven lemma
`gap2_minorityU_rise_compatible_with_pos_sum` (`:1147`) exhibits a gap-2 opposite-sign
`cancelSplit` step (`σ`-minority Main at smaller index `i`, `σ.flip` Main at `j = i+2`) that
RAISES `minorityU σ` by exactly `1` while CONSERVING the signed sum. So on any
`Inv7Sum`-compatible config carrying such a gap-2 pair the kernel can strictly INCREASE
`minorityU σ`; `PotNonincrOn Inv7Sum K minorityU` is FALSE-on-reachable, and every consumer
downstream of that carried `hmono` was conditionally vacuous.

### Survey of what the engine actually NEEDS (consumers)

The crude/levels engine (`OneSidedCancel.crude_PhaseConvergenceW`, `levels_PhaseConvergenceW`)
needs an `hmono` (`Φ` non-increasing on `Inv`) + the per-cell drain `hstep`/`hdrop`. The campaign
had ALREADY re-routed the live Phase-7 consumers onto the honest σ-class-MASS potential
`classMassN σ` *before* this fix:
- `DrainThreading.lean` Part C (`phase7_drop_floor_of_struct`, `phase7_hdrop_of_struct`,
  `phase7_hstep_of_struct_one`) is stated on `classMassN σ`, not `minorityU σ`.
- `DrainCalibration.phase7Convergence_calibrated` instantiates `phase7Convergence''`
  (`classMassN`), not `phase7Convergence'`.
- `PhaseFloors.phase7_hdrop_wired` consumes the structural gap-1 floor, potential-agnostic.

So the ONLY residual carrier of the false `minorityU`-`hmono` was the orphaned Part-I surface
`phase7Convergence'`; the honest Part-K surface `phase7Convergence''` (with
`hmono = potNonincrOn_classMassN` PROVED internal, `hClosed = invClosed_Inv7Sum` PROVED) was
already the live one.

### The honest per-pair RISE/DROP ledger (frozen `cancelSplit`)

Per pair, by branch:
- same-sign / `zero` / gap ≥ 3 — identity: count `=`, mass `=`.
- **gap 0** (opposite, `i = j`) — both zero out: count `≤`, mass `≤` (equal removal).
- **gap 1** (opposite, larger index zeros) — eliminator×minority drain: count drops,
  σ-class mass STRICT drop by `2^{L−j} ≥ 1` (`cancelSplit_classMass_pair_drop`).
- **gap 2** (opposite, smaller-index sign copied onto both outputs) — count RISES by exactly
  `+1` (`gap2_minorityU_rise_compatible_with_pos_sum`), σ-class mass DROPS by `2^{L−(i+2)}`
  (`cancelSplit_classMass_pair_le`), signed mass conserved.

The rise is bounded (`+1` per gap-2 firing) and it is a rise of the COUNT, not the MASS:
`classMass σ` is per-pair NON-INCREASING in **every** branch with NO index-ordering hypothesis
(`cancelSplit_classMass_pair_le`). So `classMassN σ := (classMass σ).toNat` is the honest
one-sided engine potential, and `{classMassN σ = 0} ⊆ {minorityU σ = 0} = NoMinority σ`
(`minorityU_eq_zero_of_classMassN_zero`; each σ-signed Main contributes mass `≥ 1`). The gap-2
count-rise is exactly what the mass argument absorbs — no upward-drift/immigration budget is
needed because the chosen potential simply does not rise.

### Engine used

No drift/immigration engine is required: the substitution count → mass turns the would-be
"bounded upward rate vs floor-rate drops" into a clean one-sided potential, so the existing
`OneSidedCancel.crude_PhaseConvergenceW` / levels machinery applies verbatim with `Φ = classMassN σ`.

### Deliverable — `Probability/Phase7HonestDrain.lean` (new, append-only, 0-sorry, axiom-clean)

Imports only `Phase7Convergence`; edits no existing file. Contents:
- `gap2_count_rises_exactly_one_mass_drops` — the F3 divergence as one named ledger
  (count `+1`, mass `≤`, signed mass `=`).
- `classMass_pair_noincr` — the universal per-pair mass non-increase.
- `false_hmono_forbids_gap2_rise` — the audit finding as a THEOREM: ANY
  `PotNonincrOn Inv7Sum K minorityU` proof, together with a kernel-support successor that raises
  `minorityU σ` (the gap-2 fire), yields `False`. Certifies F3 is real, not just "honestly named".
- `phase7HonestDrain` — the honest Phase-7 `PhaseConvergenceW` (= `phase7Convergence''` re-exposed):
  `hClosed`/`hmono` BOTH internal, only the σ-class-mass drain `hstep` carried.
- `phase7HonestDrain_post_noMinority` — re-wired post bridge: the honest `Post` delivers the
  count target `minorityU σ = 0` the false-`hmono` chain advertised, false hypothesis removed.
- `honest_hmono` / `honest_hClosed` — the two internal discharges re-exported as citable facts.

### Carried items, precisely named

Only the σ-class-MASS drain `hstep`
(`∀ b, Inv7Sum n b → 1 ≤ classMassN σ b → K b (potDone classMassN σ)ᶜ ≤ q`) remains carried —
the Doty Lemma 7.4/7.5 eliminator-mass floor — exactly as for `phase7Convergence''`. No structural
floor on the gap-2 rise-mass is needed (the mass potential does not rise). The false
`minorityU`-`hmono` is GONE from the honest surface.

### Verification

Single-file `lake env lean` EXIT 0; `#print axioms` for all seven declarations =
`[propext, Classical.choice, Quot.sound]`; no `sorry`/`admit`/`axiom`/`native_decide`;
`git diff --check` clean. The Part-I `phase7Convergence'` remains in `Phase7Convergence.lean` as a
deliberately-flagged dead surface (its `hmono` honestly named but false); `Phase7HonestDrain` is the
surface consumers should cite.

---

## F5 audit fix — the ceiling route (append-only)

Independent adversarial audit (`/tmp/opus_audit_report.md`) flagged the S1 invariant
`WindowReconciliation.BiasedMainIndexLeHour` (per-agent: every biased Main's index ≤ its OWN hour)
as having a BROKEN step-preservation / discharge route. Fixed in the new append-only file
`Probability/CeilingRoute.lean` (no existing file edited).

### Verdict: the audit is RIGHT.

We read the FROZEN split branch (`Protocol/Transition.lean:590-598`) exactly:

```
  | .zero, .dyadic sgn i =>
      if _h_gt : s2.hour.val > i.val then
        ({ s2 with bias := .dyadic sgn ⟨i.val + 1, _⟩ },     -- OUTPUT .1  (was the .zero agent)
         { t2 with bias := .dyadic sgn ⟨i.val + 1, _⟩ })      -- OUTPUT .2  (was the biased agent)
      else (s2, t2)
```

The gate is `s2.hour.val > i.val` — the **UNBIASED** agent's hour. Both outputs are
`{ _ with bias := … }`: only `bias` is rewritten; **neither output's `hour` is touched** on the
split/raise branch (the cancel branches DO write `hour := i`, lowering it, but the raise branch does
not re-stamp hour). So the biased partner `t2` becomes `dyadic sgn (i+1)` with its OWN hour left
unchanged. With `t2.hour.val = i`, `s2.hour.val = i+1` (the audit's `i = 0` config), the input
satisfies the per-agent predicate (`t2`: index `0 ≤ hour 0`; `s2`: unbiased, vacuous) but the output
`t2'` has index `i+1 = 1 > t2.hour = 0`. **The per-agent `BiasedMainIndexLeHour` is broken by one
frozen split step.** The prose lemma `biasedMainIndexLeHour_of_split_guard_step` named in
`WindowReconciliation.lean:31` never existed. The audit is correct on all counts.

This counterexample is now MACHINE-CHECKED:
`CeilingRoute.biasedMainIndexLeHour_not_step_preserved` — for any `1 ≤ L` and any base Main state,
there is a `phase3CancelSplit`-firing pair whose biased member satisfies `index ≤ own hour` on the
input yet violates it on the split output `.2`.

### The corrected route: carry the GLOBAL ceiling directly.

The downstream consumer `DoublingEdges.phase6_to_phase7_of_doubling_edges` only ever needs
`DoublingEdges.AllBiasedMainBelow (l+2) c` — the GLOBAL ceiling `index ≤ top`. That global form IS
genuinely step-preserved: `DoublingEdges.phase3CancelSplit_preserves_top_edge` proves, exhaustively
over the frozen branches, that `(index ≤ top ∧ hour ≤ top)` on the inputs gives `index ≤ top` on the
outputs (the raise `i → i+1` fires only under `hour > i`, so `i+1 ≤ hour ≤ top`). The "induct over the
chain" provenance is SOUND for the global ceiling; it is broken ONLY for the per-agent form.

`CeilingRoute.lean` therefore:

* `biasedMainIndexLeHour_not_step_preserved` — the F5 counterexample, machine-checked against the
  frozen rule (the audit verdict).
* `allBiasedMainBelow_pair_preserved` — the SOUND per-pair preservation of the global ceiling
  (re-export of `phase3CancelSplit_preserves_top_edge`); the genuinely inductive quantity, contrasted
  with the broken per-agent form.
* `phase6To7_surface_ceilingRoute` — the CORRECTED Phase6→7 surface. Carries
  `DoublingEdges.AllBiasedMainBelow (l+2) c` DIRECTLY (the step-preserved global ceiling), DROPPING
  the broken per-agent `BiasedMainIndexLeHour` + `MainHourBelow` pair of
  `WindowReconciliation.phase6To7_surface_reconciled`. The consumer is fed the genuinely-preserved
  predicate.
* `phase6To7_surface_ceilingRoute_ofSnapshots` — retains the proven bridge for any consumer that
  genuinely has both snapshots `BiasedMainIndexLeHour` + `MainHourBelow (l+2)` on the SAME config (as
  a snapshot, not via the broken step-induction): the bridge
  `allBiasedMainBelow_of_indexLeHour_of_hourCeiling` still produces the global ceiling, soundly fed
  into the corrected surface. No expressive power is lost; only the unsound "induct the per-agent form
  over the chain" provenance is removed.

### Corrected carried inventory for item-1 / S1

| object | OLD (flagged) carried set | NEW honest carried set |
|---|---|---|
| item-1 hour ceiling | per-agent `BiasedMainIndexLeHour c` (NOT step-preserved, F5) + `MainHourBelow (l+2) c`, with claimed "induct the per-step guard over the chain" discharge (INVALID) | GLOBAL `DoublingEdges.AllBiasedMainBelow (l+2) c` carried directly — the genuinely step-preserved ceiling (`phase3CancelSplit_preserves_top_edge`, SOUND induction) |
| S1 (`BiasedMainIndexLeHour`) | reachability-invariant SNAPSHOT via per-step guard (broken) | DROPPED from the carried set; retained only as an OPTIONAL snapshot input (`_ofSnapshots`), never as a chain-induction residual |

### Status of the old surface

`WindowReconciliation.phase6To7_surface_reconciled` remains in the tree (not edited per discipline).
It is still TRUE — its bridge `index ≤ hour ≤ top ⟹ index ≤ top` is correctly proven — but its `hIdx`
input has no sound reachability discharge, so the route a consumer should use is
`CeilingRoute.phase6To7_surface_ceilingRoute` (global ceiling carried directly). Single-file
`lake env lean` EXIT 0; `#print axioms` ⊆ `[propext, Classical.choice, Quot.sound]` for all four new
theorems (`allBiasedMainBelow_pair_preserved` uses only `[propext, Quot.sound]`).

---

## RELEASE RECORD — public main push (2026-06-11)

**Fresh-checkout bare-build verification (uisai2, per /uisai2 discipline):**
- Fresh shallow clone of `xiangyazi24/Ripple` @ `opus-wip` head `2f2121aa700763900c8b7c41887fc1e736ac9311`
  into `~/fresh-verify/Ripple-release` (disk); source staged to `/dev/shm/xhuan5/Ripple-release-verify`.
- All 4 dead orphan drafts (PhaseState/StepPreservation/DescentPotential/DiscreteChernoff) confirmed
  absent from lib root and tree (the §1a/§4 precondition).
- `lake exe cache get`: EXIT 0 (8283 mathlib oleans, v4.30.0 + mathlib c5ea00351c28).
- **Bare default build (`lake` default targets, no explicit modules): EXIT 0 — "Build completed
  successfully (4123 jobs)".** Zero compile errors; all `error:`-substring log hits are
  linter.style echoes of comment text; the one non-style hit is a warning-level docString
  linter note (DeltaF.lean:171).
- Second check, explicit 164-module campaign closure (`em_modules_live.txt`): EXIT 0
  ("Build completed successfully (3680 jobs)").

**Push:** verified SHA `2f2121a` pushed to public `xiangyazi24/Ripple` **main**
(`c30f744..2f2121a`, clean fast-forward, 269 commits). NOTE: opus-wip had advanced to `e6dacd5`
(F5 ceiling route) during the build; those commits are NOT in this release — only the verified
`2f2121a` was pushed to main.

**Tag:** `doty-thm31-phaseF-2026-06-11` (annotated, → `2f2121a`): Theorem 3.1 both halves
structurally complete; 164-module closure green; ~17 named carried hypotheses inventoried above.

---

## F1 REFINEMENT — the genuine all-hours UNION discharge (`Probability/HourUnion.lean`, append-only)

**Codex adversarial-audit finding (`/tmp/codex_audit_report.md` §F1).** The F1+F2 fix above
(`ConfinementSurface.lean`) removed the false pointwise predicate and works at kernel level, but the
Codex sweep found its `mainConfinement_kernel_whp` is honest ONLY as a *carried final event*: its
sole substantive binder is

```
hHourTail : (transitionKernel ^ phase3to5Time) c₀ {c | ¬ ConfinementEvent c} ≤ η
```

— the FINAL bad-event bound — and the conclusion is the SAME bound (a `rfl`-level repackaging via the
orphaned `theorem6_2_main_confinement_whp`, whose proof is `rw [hev]; exact hHourTail`). So the
all-hours **union** — composing the per-hour squaring tails over the `numHours` hours of the
Phase-3→5 horizon into the final `{¬ConfinementEvent}` budget — was NEVER performed. It is a
**tautological carry**.

**Doc correction.** The earlier F1-fix narrative overstated `hHourTail` as "the honest per-hour
squaring tails composed." That is wrong: `hHourTail` is literally the final tail, with NO composition.
The genuinely-missing piece is the per-hour→horizon chaining. The corrected statement: the honest
carried object is NOT the final tail; it is the PER-HOUR squaring failure plus the hour-boundary
chaining.

**The honest fix (`Probability/HourUnion.lean`).** Mirrors the LANDED checkpoint-composition machinery
(`EarlyDripMarked.checkpoint_composition`, the per-WINDOW invariant-failure → `KK`-window union at
horizon `w·KK`; and `WidthPrefix.checkpoint_composition_prefix`, the clock-side per-window chaining
with a remainder block) for the Main-profile hours. `ConfinementSurface.ConfinementEvent` is a
discrete-measurable invariant and `(NonuniformMajority L K).transitionKernel` is a Markov kernel, so
`checkpoint_composition` applies VERBATIM with `Inv := ConfinementEvent`, `w := hourLen`,
`KK := numHours` — no new probability, the confinement event plugged into the existing union engine.

* `confinementEvent_hours_union` — the union composition theorem (the discharge F1 skipped). From the
  PER-HOUR brick `hHour : ∀ x, ConfinementEvent x → (Kʰᵒᵘʳᴸᵉⁿ) x {¬ConfinementEvent} ≤ δ` (each hour's
  squaring tail from a confined state — the LANDED `confinement_hour_tail`/`main_profile_hour_squaring`
  at one hour), the horizon decomposition `hHorizon : phase3to5Time = hourLen·numHours`, the budget
  `hBudget : numHours·δ ≤ η`, and the confined start `hConf0`, it CONCLUDES the final event bound
  `(K^phase3to5Time) c₀ {¬ConfinementEvent} ≤ η`. Proof: `subst hHorizon`; `checkpoint_composition`;
  `le_trans … hBudget`. The per-hour tails are COMPOSED, never assumed.
* `mainConfinement_kernel_whp_of_hours` — the re-wired consumer surface, SAME conclusion as
  `mainConfinement_kernel_whp` but the carried inputs are STRICTLY FINER than the final tail: the
  per-hour squaring events (`hHour`), the hour-boundary clock facts (`hHorizon`, `hConf0`), and the
  arithmetic (`hBudget`). The final tail is the OUTPUT.
* `confinement_hours_union_from_single` — the convenience form: a single uniform per-hour squaring
  constant `δ` (the `confinement_hour_tail` shape `r^hourLen·Φ(c₀)/θ`) feeds the union directly.

### Corrected carried inventory for the confinement chain (finer than the final tail)

| object | F1-fix carried set (tautological) | F1-REFINEMENT honest carried set (finer) |
|---|---|---|
| confinement surface | the FINAL tail `hHourTail : (K^phase3to5Time)c₀{¬conf} ≤ η` (= conclusion; no composition) | PER-HOUR tail `hHour : ∀ x, conf x → (K^hourLen)x{¬conf} ≤ δ` + horizon `phase3to5Time = hourLen·numHours` + budget `numHours·δ ≤ η` + confined start `hConf0` |
| the discharge | `rfl`-rewrite returning the input | `checkpoint_composition` union over `numHours` hours + budget spend `le_trans` |

So the confinement chain now carries: **per-hour squaring failure + hour-boundary confined-start
anchor + arithmetic** — never the final event bound. This is the union the F1 fix's `hHourTail`
pretended to deliver.

**Audit.** 3/3 new theorems axiom-clean ⊆ `[propext, Classical.choice, Quot.sound]`; 0
sorry/admit/axiom/native_decide; `git diff --check` clean. Single-file build verified on uisai2
`/dev/shm` (v4.30.0 + mathlib c5ea00351c28, same bucket): `lake build …Probability.HourUnion` EXIT 0
("Build completed successfully (3599 jobs)"); `lake env lean` axiom audit clean (comment-only
line-length style warnings, matching the existing `ConfinementSurface.lean` convention).
