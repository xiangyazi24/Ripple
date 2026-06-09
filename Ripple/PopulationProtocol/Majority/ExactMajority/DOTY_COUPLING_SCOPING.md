# Doty time-half — post-C5 frontier: clock→main hour-sync coupling (the honest remaining gap)

Status as of C4 committed, C5 (clock's own two-sided timing) in flight. This doc records the GENUINE
remaining work between "clock timing done" and "expected-time O(log n) headline" — written so the next
avenue builds REAL PhaseConvergence instances (the A0 way), NOT assumed-hypothesis skeletons (the C2 way
Xiang rejected: "我要的是论文的版本，不是带条件，带缺陷的版本").

## What is genuinely PROVEN kernel-level (the spine)
- A0 `Phase2TimeConvergence.lean`: `epidemicPhaseConvergence` — the REAL PhaseConvergence-construction
  template (Pre/Post/t/ε with genuine `post_absorbing` + `convergence`). `epidemic_phase_logn_scale`: t/n ≤
  11(log n+1), ε=1/n.
- F `WindowConcentration.lean`: per-step contraction on an absorbing window → PhaseConvergence (the framework
  that turns "define Φ + one-step drift" into a phase instance).
- S1/S2/S2b/S3: the clock's bulk (0.1→0.9 epidemic), front squaring (real scheduler kernel), early-drip
  (coupled to front width).
- C3 `ClockFaithful.lean`: clock per-minute UPPER + composed `clock_faithful_O_log_n_upper` (m minutes →
  O(log n), chaining DEFINITIONALLY discharged — no assumed h_chain).
- C4 `FrontShapeInduction.lean`: clock per-minute LOWER (`clock_step_lower`/`_strict`, genuine non-crossing
  from front-shape; early-drip←front-width COUPLED not assumed).
- C5 `ClockHourBounds.lean` (in flight): Thm 6.8 two-sided per-minute + Thm 6.9 hour bounds +
  `all_hours_O_log_n` (clock reaches hour L=⌈log₂n⌉ in O(log n) parallel time).
- A1 `TimeComposition.lean`: `doty_time_headline` — GIVEN 11 PhaseConvergence instances on
  `NonuniformMajority L K` (with t ≤ Cphase·n·(L+1), ε ≤ δ, chaining, Pre₀, Post→stable), concludes
  T ≤ 11·C0·n·(L+1) interactions = O(log n) parallel time, failure ≤ 1/n. The OUTER composition skeleton —
  real, but its phase hypotheses are the input.

## The GAP (what A1's phase hypotheses need, and is NOT yet built)
A1 consumes 11 `PhaseConvergence (NonuniformMajority L K).transitionKernel` instances. Building them is the
remaining probabilistic content:
- **Untimed phases (2,4,6,8,9):** end almost immediately (Doty: "untimed, end almost immediately"). Their
  PhaseConvergence has small t and is driven by a fast absorbing-set argument — likely buildable via F
  (framework) + existing DeterministicChain reachability. TRACTABLE — do these first.
- **Timed phases (1,3,5,7 — the split/cancel phases):** t comes from the CLOCK HOURS (C5's
  `all_hours_O_log_n` / Thm 6.9). Each timed phase's `convergence` needs:
  (i) the clock provides L=⌈log₂n⌉ synchronous hours each O(1) parallel time (C5 — DONE once C5 lands);
  (ii) **the Main agents track the clock**: split reactions ±1/2ⁱ,0→ gated by `Cbi/kc,Oj→...,Obi/kc`
       (k=45 min/hour, p=1) so biased agents do not split "too many too quickly" (Doty §6.2 lines 489-502);
  (iii) **"not too far ahead" (Lemma 6.10 supermartingale Φ(t)=m_{>h}(t)−1.1·c_{>h}(t)):** the small
       fraction of too-fast Clock agents cannot drag too many Main/O agents above hour h. This is the
       cross-protocol coupling — the genuinely hard, NOT-yet-built atom.
  (iv) per-phase Main-state convergence (Lemma 5.3 etc.: end of Phase 1 → three consecutive exponents;
       Phase 3 → biased agents at exponents −l,−(l+1),−(l+2)). The split/cancel averaging analysis.

## Avenue plan (挨个做, after C5 lands — build REAL instances, no assumed B/h_chain)
1. **D1 (untimed phases):** build PhaseConvergence for an untimed Main phase via F (absorbing set reached
   fast). Establishes the Main-kernel PhaseConvergence pattern. Tractable.
2. **D2 (clock→main bridge product):** the cross-protocol coupling. Define the product configuration
   (Clock minutes × Main exponents), state the split-gating, and prove Lemma 6.10's Φ supermartingale via
   the existing Azuma/supermartingale infra (Theorem 4.2 in paper; check Ripple's Probability/ for the
   Azuma lemma). This is the hard frontier — grind it for real or document the exact atom that blocks.
3. **D3 (timed phase instances):** with C5's hour timing + D2's not-too-far-ahead, build the timed-phase
   PhaseConvergence (t = clock hours, convergence = per-phase split/cancel + D2). One per timed phase.
4. **D4 (instantiate A1):** feed D1+D3's 11 instances into `doty_time_headline` → the whp O(log n) headline.
5. **D5 (expected time):** whp O(log n) path (D4) + rare Phase-10 backup (unconditional correctness from
   DeterministicChain `stable_majority_correct`, weighted by negligible prob) → E[parallel time]=O(log n).

## ACCURATE FRONTIER (revised after surveying existing Analysis/ + Probability/ infra)
Earlier this doc under-estimated what is already built. The TRUE state:

### Already built & 0-sorry (REAL, on the actual NonuniformMajority kernel)
- `Analysis/Phase3Convergence.lean`: `phase3PotentialExt` + `phase3PotentialExt_drift` (one-step drift) +
  `phase3TieConvergence : PhaseConvergence (NonuniformMajority L K).transitionKernel` — a GENUINE phase
  instance (Phase-3 tie case, Pre=Phase3TiePre, Post=Phase3TiePost, t=Θ(n²(n-1)log n) interactions,
  ε=1/n²). NOTE: this is the SLOW tie/backup-routed bound, not the fast O(log n) main path.
- `Probability/SupermartingaleHitting.lean`: `DriftPhase` structure + `DriftPhase.toPhaseConvergence` — the
  "potential Φ + one-step drift (∫Φ∂K ≤ r·Φ) + absorbing Post → PhaseConvergence" machine. The genuine way
  to build instances.
- `Probability/Supermartingale.lean`: Theorem 4.2 geometric-drift tail (the Azuma/supermartingale infra
  Lemma 6.10 needs).
- `Analysis/PhaseProgress.lean`: clock-counter descent lemmas (PhaseN clock_counter_descent/_strict/
  zero_advances) — the `counter`/`minute` advance mechanics inside NonuniformMajority.
- `Analysis/Phase0Convergence.lean`: mcrCount/phaseBelowCount monotonicity, all-phase transition lemmas.
- `Analysis/DeterministicChain.lean`: `stable_majority_correct` — unconditional EXISTENTIAL correctness
  (the backup that makes expected time finite regardless of the fast path).

### The REAL remaining gaps (the honest D-frontier)
1. **Clock-transfer projection (LINCHPIN).** C3/C4/C5 prove the ABSTRACT `clockProto (Minute L₀=Fin(L₀+1))`.
   The real protocol's clock is the `AgentState.minute : Fin(K·(L+1)+1)` field inside `NonuniformMajority`.
   They are NOT connected. Need: the `minute`-marginal dynamics of `NonuniformMajority` match `clockProto`
   (a projection/coupling — clock agents' minute drip+epidemic is a sub-dynamics; rate carries the
   clock-fraction 1/c²), so `all_hours_O_log_n` TRANSFERS to "the protocol's clock reaches hour L in
   O(log n) parallel time." Until this exists, C3/C4/C5 are valuable but unconnected to the headline.
2. **Hour-tracking coupling (Lemma 6.10).** Φ=m_{>h}−1.1·c_{>h} supermartingale (via Supermartingale Thm
   4.2) → Main agents' `hour` doesn't run ahead of Clock `minute` → split reactions gated correctly.
3. **Fast timed-phase instances.** The O(log n) main-path PhaseConvergence for the timed phases (3,5,7),
   t = clock hours (from #1), convergence = split/cancel averaging (phase3PotentialExt_drift extended to the
   non-tie main case) gated by #2. The existing phase3TieConvergence is only the slow tie branch.
4. **Untimed-phase instances (2,4,6,8,9).** Fast absorbing convergence via DriftPhase/framework. Tractable.
5. **Assemble 11 into A1** (`doty_time_headline`) → whp O(log n).
6. **Expected-time wrapper:** whp O(log n) (#5) + rare slow path (phase3TieConvergence / Phase-10 backup,
   negligible prob, finite by `stable_majority_correct`) → E[parallel time]=O(log n).

This is a multi-avenue campaign (essentially the rest of Doty §5-6 timing). #1 is the linchpin everything
downstream needs; attack it first.

## STRUCTURAL FINDING (2026-06-07, autonomous run — counter vs minute)
Investigating keystone (c) revealed the real protocol has TWO separate timing mechanisms, easy to conflate:
- **`minute`/`hour`** (drip+epidemic, Phase 3 Rule 1): synchronizes the SPLIT reactions WITHIN Phase 3
  (split allowed only if an O agent has hour ≥ exponent). This is the §6 clock (C3/C4/C5 abstract; D-lynch
  real-kernel).
- **`counter`** (stdCounterSubroutine: decrement; counter=0 ⟹ advancePhaseWithInit, phase+1): gates the
  advance BETWEEN phases (3→4→5…). On entering a timed phase, clock agents get counter ← 50·(L+1).
Consequence for keystone (c) "clock at minute < cap ⟹ phase exactly 3": phase-4 entry is COUNTER-gated, NOT
minute-gated. So (c) ⟺ "counter (50(L+1)) reaches 0 only after the clock completes (minute = cap = K(L+1) =
45(L+1))" — the paper's constant-tuning ("we tune constants so hour i lasts long enough"). This is a
PROBABILISTIC TIMING relationship (counter decrements vs minute advances at interaction-dependent rates), NOT
a syntactic reachability invariant. So (c) is intertwined with the timed-phase timing itself — it cannot be
cleanly discharged separately by syntactic induction. Honest consequence: carry (c) as a labeled hypothesis
(D-lynch-3 does); its discharge is part of the full timed-phase analysis (avenue f), not a standalone step.
This also means avenues (c) and (d)/(e)/(f) are more coupled than the doctrine's clean layering assumed.

## COURSE-CORRECTION (2026-06-07) — (a)/(d) targeted FULL crossing (wrong scale); redo as BULK
After building (a) clock_real_advance_mixed and (d) clock_real_all_minutes, careful re-analysis found a real
flaw in the TARGET (the lemmas are 0-sorry and the per-pair facts/counting are correct and reusable, but the
chosen Post is the wrong decomposition):
- `clock_real_advance_mixed` Post = `rBeyond(T+1) = mC` (ALL mC clocks cross level T = FULL crossing). Full
  crossing of one level is an epidemic 0→all = Θ(n log n) interactions = O(log n) PARALLEL **per level** ⟹
  Θ(log²n) over L₀=Θ(log n) levels. That is exactly C5's honest Θ(log²n) verdict, NOT the paper's O(log n).
- `hfrontier_mix` (γ·mC ≤ mC − rBeyond(T+1), "front stays wide") is FALSE near level completion (m=mC−1 ⟹
  mC−m=1 < γmC). The uniform-contraction windowDrift needs it on the narrow-front tail it must traverse, so it
  is NOT a true ∀-config invariant — the (a)/(d) "O(log n)" rests on a non-dischargeable hypothesis.
- ROOT CAUSE: uniform geometric drift to FULL crossing can't capture the slow narrow-front tail; and full
  crossing is the wrong scale anyway.
- FIX (the faithful decomposition, = C3's): target **0.9-BULK crossing** `hi·mC ≤ rBeyond(T+1)` (a constant
  fraction beyond), via the constant-fraction epidemic (S1-style), wide front throughout ⟹ uniform c² holds,
  O(1) parallel per minute ⟹ O(log n) total. The seed (0→0.1) and the lagging tail (0.9→1) are handled by the
  hour structure / next levels, exactly as C3/C4/C5 do abstractly. `hfrontier_mix` is then NOT needed.
- REUSABLE from (a)/(d)/(hmono): Transition_clock_pair, the per-pair drip/sync/epidemic advance lemmas, the
  full-denominator c² pair-counting (sum_interactionCount_mixedRect), Q_mix_succ_of_post chaining, and
  hmono_mix_discharged. Only the Post target (full→bulk) and the contraction packaging change.
- HONEST STATUS of (a)/(d): 0-sorry but mislabeled "O(log n)"; they are the FULL-crossing (Θ(log²n)) structure
  conditional on a false-near-completion hfrontier. Superseded by the bulk-crossing rework. Not deleted (reusable
  lemmas), but clock_real_O_log_n must NOT be cited as the O(log n) clock until reworked.

## SECOND course-correction (2026-06-07) — Q_mix FLOOR is full-crossing → forces a FALSE hyp; fix = 0.9-floor
After (a')/(a'')/(d'), the composition (d') exposed the deeper root of the same error: `Q_mix.crossedT` =
`rBeyond T = mC` (FULL crossing of the current level) — inherited from the all-clocks (c=1) D-lynch-3 design.
- Chaining minute T→T+1 via `Q_mix_succ_of_post` needs `rBeyond(T+1) = mC` (full) for the NEXT window's
  crossedT, but the bulk step only delivers `bulkHi mC = 0.9mC ≤ rBeyond(T+1)`. (d') bridged this by carrying
  `hcross_full_all : Q_mix ∧ 0.9mC ≤ rBeyond(T+1) → mC ≤ rBeyond(T+1)`.
- **`hcross_full_all` is FALSE** (given rBeyond T = mC and 0.9mC ≤ rBeyond(T+1) ≤ mC, rBeyond(T+1) need not = mC
  — could be 0.95mC). Same failure mode as the earlier false `hfrontier_mix`. So (d')'s O(log n), while
  0-sorry, rests on a false hypothesis → NOT usable as-is.
- ROOT: the WHOLE clock chain treats FULL crossing (rBeyond = mC) as the floor/target, an artifact of the
  c=1 all-clocks origin. C5's faithful clock uses the 0.9 threshold (`CrossedB = hi ≤ beyond`) as floor —
  chaining definitional, no full-crossing.
- FIX (the foundational one): weaken `Q_mix.crossedT` from `rBeyond T = mC` to `bulkHi mC ≤ rBeyond T`
  (0.9-floor). Then: (i) chaining minute T→T+1 is DEFINITIONAL (Post 0.9 = next Pre 0.9), no hcross_full;
  (ii) susceptible counts (mC − rBeyond(T+1)) use `Q_mix.clockSize` (clockCount = mC, ALREADY present), not
  crossedT — so (a')/(a'') frontier floors still hold; (iii) only `habs_mix` (window closure) remains carried.
  Reusable: ALL per-pair lemmas, c² counting, both frontier floors, hmono, the prob derivation — only the
  window predicate's floor field changes (full → 0.9), propagated through (a')/(a'')/(d').
- LESSON: the two clock-layer course-corrections (full→bulk TARGET, full→0.9 FLOOR) are one root error
  (c=1 full-crossing habit). After the floor fix, the real-kernel clock should be O(log n) carrying ONLY the
  single deterministic habs_mix.

## HARD RULE (the C2 lesson)
Every phase instance's `convergence` and `post_absorbing` must be GENUINE (proven from the kernel /
framework), never an assumed hypothesis. If D2 (Lemma 6.10 coupling) genuinely needs a Mathlib/infra atom
not present, document the EXACT atom + the failing tactic chain — do NOT wrap it as an axiom or a free
hypothesis and call the headline done. Report the honest two-sided ledger to Xiang at each avenue close.
