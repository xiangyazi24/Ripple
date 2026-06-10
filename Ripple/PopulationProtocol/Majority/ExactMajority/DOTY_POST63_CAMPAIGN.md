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
