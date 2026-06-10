# Doty §6 Lemma 6.3 / Theorem 6.5 — the coupled time-window engine (the genuine remaining core)

## The finding (deep dive 2026-06-09, definitive)
The clock O(log n) — abstract AND real — reduces to controlling the front-tail/feeder counts, and EVERY
existing formalization carries this as a conditional feeder bound (`hwin` / `hwin_all` / `FrontFeederWindow` /
`earlyDrip_kernel_bound`'s `hwin : beyond(T+1)=0 → beyond T ≤ B`). As a standalone ∀-reachable deterministic
statement that bound is FALSE (sync pumps the feeder while the level above stays empty). The unconditional
truth is Doty Lemma 6.3 / Theorem 6.5 — a COUPLED, self-consistent, 0.1-parallel-time-window large-deviation
argument. There is no step-wise-union shortcut (the front envelope window is not step-closed).

## Ingredients that already EXIST (unconditional, reusable)
- `EarlyDripBound.earlyDrip_mgf_one_step` — the UNCONDITIONAL scale-free one-step MGF contraction:
  `∫ exp(s·N') dK(c) ≤ (1 + q(e^s−1))·exp(s·N c)` for a rare +1-increment count `N`, increment prob `≤ q`.
  This is the large-deviation engine. The catch: for `N = beyond(T+1)`, `q ≈ (beyond T / n)²` depends on the
  feeder `beyond T`, which is the coupling.
- `ConstantDensityEpidemic.constantDensity_epidemic_O1_parallel` — UNCONDITIONAL bulk epidemic: informed grows
  `lo n → hi n` (0.1→0.9) with failure `≤ (199/200)^t · 2^(hi−lo)`. The x-growth of Lemma 6.3.
- `ClockFrontShape.real_front_advance_squares` — UNCONDITIONAL one-step seeding squaring (empty level T+1
  seeded ≤ (frac T)²) on the REAL kernel.
- `WindowConcentration.windowDrift_PhaseConvergence` / `windowGrowth_PhaseConvergence` — the window-drift
  concentration framework (already used for S1).
- `ClockFrontProfile` (this session): `GoodFrontWidth ⟸ GoodFrontProfile` (det, PROVEN); `GoodFrontProfile`
  = the Thm 6.5 recurrence `frac(T+1) ≤ (frac T)²` is the residual.

## The correct unconditional mechanism (stopped MGF over bulk-arrival)
The early-drip `beyond(T+1)` is small NOT because the feeder is bounded always, but because it is small
*before the bulk arrives at T*. Define the stopping time
  `τ_T := first step at which beyond(T) ≥ θ·n`   (θ a threshold, paper uses scales n^{−0.45}).
Before `τ_T`, `beyond T < θ·n`, so the per-step drip rate `q ≤ θ²`, and the MGF supermartingale
`exp(s·beyond(T+1))` accumulates factor `≤ (1 + θ²(e^s−1))` per step over the `O(n)` steps of the window —
giving `beyond(T+1) ≤ O(n·θ²·…)` = the early-drip bound `O(n^{−0.85})` at the right scales, UNCONDITIONALLY
(θ is in the stopping-time definition, not an assumed feeder bound). After `τ_T` the bulk has arrived at T,
which (via the epidemic) means the hour is progressing — completion, not a bad event.

## Decomposition into provable lemmas (the build order)
1. **`stoppedMGF_tail`** (kernel, generic): for a rare +1-count `N` with per-step increment prob `≤ q` ON A
   GATING EVENT `G` (e.g. `beyond T < θn`), the stopped process `exp(s·N)` over steps where `G` holds is a
   supermartingale with factor `(1+q(e^s−1))`; hence `Pr[N_τ ≥ a] ≤ e^{−sa}·(1+q(e^s−1))^H`. Build from
   `earlyDrip_mgf_one_step` (already proven the one-step factor) + a product/induction over the horizon
   GATED on `G` (mirror `frontSync_union_horizon`'s induction structure, but multiplicative MGF not additive).
2. **`earlyDrip_unconditional`**: instantiate (1) with `N = beyond(T+1)`, `G = {beyond T < θn}`, `q = θ²`
   (from `real_front_advance_squares`/the drip rate), `θ` at the paper scale → `beyond(T+1) ≤ O(n^{0.15})` whp
   over the pre-arrival window, with NO `hwin`. Discharges `earlyDrip_kernel_bound`'s `hwin`.
3. **`bulk_arrival_epidemic`**: the bulk `c_{≥T}` reaches `θ → 0.9` in O(1) parallel time
   (from `constantDensity_epidemic_O1_parallel`, transferred to the minute marginal). Gives `τ_T` is reached
   within O(1) parallel time once seeded — the x-growth.
4. **`frontProfile_recurrence`** (Thm 6.5 / `GoodFrontProfile`): combine (2)+(3): `c_{≥i+1} ≤ (c_{≥i})²`
   holds whp over the run, because the next level is only early-dripped (bounded by (2)) until the bulk
   arrives (3), and the seeding squares. Assemble into `GoodFrontProfile` whp.
5. **Rewire**: feed `GoodFrontProfile` (4) → `GoodFrontWidth` (`ClockFrontProfile.goodFrontWidth_of_profile`,
   PROVEN) → clock FrontSync unconditional (drop the false `hwin_all`).

## Progress
- **Brick 1 DONE** (commit fe0d02d4): `MGFHorizon.earlyDrip_mgf_tail` — the ungated MGF→tail engine
  `(K^t) c₀ {a ≤ earlyDripCount T} ≤ (1+q(e^s−1))^t·exp(s·N₀)/exp(s·a)` (s>0), composing the proven
  `earlyDrip_mgf_one_step` (one-step factor) into `geometric_drift_tail` (horizon). 0-sorry, axiom-clean.
  Carries the explicit `hrate : ∀c, K c {N c < N·} ≤ ofReal q` (UNGATED) hypothesis.

## Brick 2 progress (GatedGeometricDrift.lean, 0-sorry, axiom-clean)
- **2a DONE** (commit 52e79b5d): `killK K G` (cemetery extension on `Option α`) + `IsMarkovKernel` +
  `killK_drift` — GIVEN drift only on gate `G` (`hdrift_G`) and `1≤r`, the KILLED drift holds at EVERY `o`
  unconditionally (off-gate the killed integral is 0). The crux that makes the gated drift unconditional.
- **2b DONE** (commit 23198044): `killed_geometric_tail` = `killK_drift` → `geometric_drift_tail`:
  `(killK K G ^ t)(some x){o | θ ≤ killΦ Φ o} ≤ r^t·Φ x/θ` = the gated-survivor tail.
- **2c DONE** (commit f27ac0ac): `real_le_killed` — `(K^t) x {bad} ≤ (killK^t)(some x){none ∨ some-bad}`,
  the coupling (induction on t; helpers `killK_none`, `none_absorbing`, `killK_some_gated`).
- **2d DONE** (commit a3ffccf7): `gated_real_tail` — `(K^t) x {θ≤Φ} ≤ (killK^t)(some x){none} + r^t·Φx/θ`
  = escape mass (gate left = bulk arrived, benign) + killed geometric tail.  **Brick 2 (gated engine) COMPLETE.**
- **NEXT (brick 3)**: instantiate `gated_real_tail` for the early-drip. KEY SUBTLETY (worked out): the rate
  bound `earlyDrip_prob_le_sq` (`≤ (beyond T/n)²`) holds ONLY when `beyond(T+1) = 0` (empty) — once seeded, SYNC
  grows `beyond(T+1)` (rate `∝ beyond(T+1)·below/n²`, not squared). So `Φ = exp(s·beyond(T+1))` does NOT satisfy
  the gated drift on `{beyond T<θn}` alone (sync term unbounded), and gating on `beyond(T+1)=0` conflates the
  escape with the bad event. The genuine fix = Doty's drip-ONLY EXCESS counter `d_{≥i+1}` (counts only DRIP
  arrivals into `≥ i+1`, excluding bulk-sync arrivals); its increment rate is the squared drip term
  `≤ (beyond T/n)²` ALWAYS (no sync, since `d` ignores sync moves). Steps: (i) define `d_{≥T+1}` (a config→ℕ
  counter that rises by 1 only on a same-minute-`T` drip into `T+1`); (ii) prove its rate `≤ (beyond T/n)²` and
  `d` rises `≤1`/step (so `earlyDrip_mgf_one_step` applies with `Φ=exp(s·d)`); (iii) `gated_real_tail` with
  `G={beyond T<θn}` → `d_{≥T+1}` small whp on the gate; (iv) escape `{none}` = `P[beyond T≥θn]` = bulk arrived,
  via `ConstantDensityEpidemic`. Then `c_{≥T+1} ≤ (bulk-sync part) + d_{≥T+1}` feeds Lemma 6.3 → `GoodFrontProfile`.

## Brick 2 (ORIGINAL PLAN) — the GATED geometric drift tail (discharge `hrate` via the bulk-arrival gate)
`earlyDrip_mgf_tail`'s `hrate` (rate ≤ q at EVERY config) is false with small q: the early-drip rate
`q ≈ (feeder/n)²` is small only while the feeder is small = before the bulk arrives at the level. Need a
GATED version where the drift holds only on a gate `G`. Plan (generic, reusable — build in a new file
`GatedGeometricDrift.lean`):
- **Killed-kernel construction.** Extend the state to `Option α` (cemetery `none`). Define `K_kill : Kernel
  (Option α) (Option α)`: on `some x` with `G x`, `K_kill = K x` (mapped into `some`); on `some x` with
  `¬G x`, `K_kill = δ none` (killed); on `none`, `δ none`. Extend `Φ̂ none = 0`, `Φ̂ (some x) = Φ x`.
- With `r ≥ 1`: `∫⁻ Φ̂ dK_kill (some x) ≤ r·Φ̂ (some x)` holds UNCONDITIONALLY — on `G` it is `hdrift` (the
  gated drift), off `G` LHS = `Φ̂ none = 0 ≤ r·Φ x`. So `lintegral_geometric_decay`/`geometric_drift_tail`
  apply to `K_kill` with no gate.
- **Relate to `K`.** The survived mass `(K_kill^t)(some x){some y | a ≤ N y}` lower-bounds nothing we want;
  rather it EQUALS the `K`-measure of trajectories that stay in `G` for all `t` steps AND end with `N ≥ a`.
  So `(K^t) x {y | a ≤ N y ∧ stayed-in-G} ≤ (K_kill^t)(some x){· | a ≤ N} ≤ r^t·Φ x/θ`. The complement
  `{left G by t}` = the bulk arrived at the level = handled by the epidemic (brick 3), benign.
- Deliver `gated_geometric_tail` (generic) + `earlyDrip_gated_tail` (instantiate `G = {beyond T < θn}`,
  `q = θ²`). This DISCHARGES `earlyDrip_kernel_bound`'s `hwin` unconditionally.

(Alternative if the killed-kernel `Option α` plumbing is heavy: use `geometric_drift_tail_random_variable`
on the explicit clockProto trajectory space with the stopping time `τ = first exit from G`, optional
stopping. Killed-kernel is preferred — fully generic, no trajectory-space construction.)

### REFINEMENT (2026-06-09, after reading earlyDrip_prob_le_sq) — the right object is BINARY empty-maintenance
`earlyDrip_prob_le_sq` bounds the seed rate `≤ (beyond T/n)²` ONLY when `earlyDripCount T c = 0` (the early
front is EMPTY). So the rate is controlled only from empty — the MGF *count-growth* (brick 1's `hrate` at
every config) does NOT apply to the early-drip once the count is ≥1 (sync can grow it). Brick 1
(`earlyDrip_mgf_tail`) is a correct reusable engine but the early-drip does not satisfy its ∀-config `hrate`.
The CORRECT object is the BINARY "front stays empty" (`earlyDripCount T = 0` maintained), via an ADDITIVE
union bound (à la `earlyDrip_kernel_bound`/`frontSync_union_horizon`: `P[ever seeded] ≤ t·q`, `q ≤ (B/n)²`).
The crux is the feeder gate `beyond T ≤ B`: `frontSync_union_horizon` requires the window `W` MAINTAINED
while Good holds, but the gate (`beyond T ≤ B` = bulk-not-arrived) is NOT maintained — the bulk arrives and
that is BENIGN (progress), not a breach. THIS is the precise obstruction. The killed-kernel handles benign
gate-failure: kill (→ cemetery) when `beyond T > B`; on alive states the seed rate `< (B/n)²`, and the
additive union over the killed walk gives `P[front seeded ∧ stayed gated] ≤ t·(B/n)²`. Brick 2 = the
killed-kernel ADDITIVE union bound (binary), NOT the MGF. Need: killed kernel on `Option α` (Kernel.piecewise
+ map + const dirac none) + a generic additive union (mirror `frontSync_union_horizon` for a generic kernel,
or apply it to the killed kernel) + the "killed agrees with K on gated paths" relation.

## BRICK 3 REVISION (2026-06-09, new session) — the 10th false shape caught BEFORE proving: unrestricted GoodFrontProfile

Paper verification (Doty-2021-exact-majority.txt lines 1795-1955) + ChatGPT brick-3 consult (route 1a,
/tmp/gpt_q_brick3.out archived) established TWO corrections to the plan above:

1. **The drip-only excess counter d (the "NEXT (brick 3)" plan above) is NOT Doty's d.** Paper def
   (lines 1807-1812): `D_{≥i+1}` = agents that moved above minute i via a drip WHILE `c_{≥i} < n^{-0.45}`,
   PLUS agents brought above minute i via an epidemic reaction with another early-drip agent. The epidemic
   descendants MUST be counted (else sync-from-tainted arrivals land in the clean part y and break the
   y < 0.9px² recurrence). Drip-only undercounts. The faithful object needs the marked kernel (ChatGPT
   route 1a: per-agent Bool taint, markedK, projection theorem back to the real kernel).

2. **The unrestricted `GoodFrontProfile` (∀T squaring) is itself a FALSE residual** — the 10th false shape,
   caught before building on it. Thm 6.5 asserts the squaring ONLY on `n^{-0.4} ≤ c_{≥i} ≤ 0.1` (line 2810
   ↦ txt 1895). Below the window it genuinely fails whp: the first drip into a fresh level T+1 with feeder
   count B < √n gives frac(T+1) = 1/n > (B/n)², and integrating the seeding rate (count²/n per parallel
   unit) along the front's epidemic growth (e^{2τ}) shows seeding typically fires exactly at the B ≈ √n
   borderline — Θ(1) violations per level, Θ(log n) per run. The paper handles sub-window levels by the
   CLIMB argument instead (Thm 6.5 proof: drips above the n^{-0.4} point fire at rate ≤ p·n^{-1.6}; climbing
   log log n levels in the O(log log n) window has probability n^{-ω(1)}).

**Brick 3.1 DONE (this commit, 0-sorry, axiom-clean):** the faithful windowed residual pair + glue, in
ClockFrontProfile.lean:
- `FrontTail.windowed_doubly_exp` + `FrontTail.windowed_floor_crossing` — the windowed collapse: under
  squaring gated on `[θ, 1/10]`, a subcritical start crosses any floor θ ≥ 1/card within
  frontWidthBound(card) levels.
- `WindowedFrontProfile θ c` — the faithful Thm 6.5 recurrence (squaring only on the window).
- `ClimbBound θ W₂ c` — `frac k < θ → rBeyond (k+W₂) = 0` (run-long form; follows from the paper's
  stopping-time form by minute-monotonicity).
- `goodFrontWidth_of_windowed_profile_and_climb` — GoodFrontWidth (W₁+W₂) ⟸ WindowedFrontProfile ∧
  ClimbBound, W₁ = frontWidthBound card. REPLACES goodFrontWidth_of_profile (kept, but its unrestricted
  hypothesis is whp-undischargeable; do not build on it).

**Brick 3.2 DONE (ClimbTail.lean, 0-sorry, axiom-clean, REAL kernel):** the gated climb tail.
- `mgf_one_step` — the GENERIC one-step MGF contraction (kernel-generic earlyDrip_mgf_one_step,
  any probability measure, a.e. hypotheses) — reusable for the marked kernel too.
- `climbN k c` — climb height via the antitone-threshold trick: #{j ∈ [k+2, capMinute] :
  rBeyond j c > 0} = (leading edge) − (k+1) truncated, NO max-minute function needed (the filtered
  set is an initial segment). Combinatorics: rises ≤1/step (only a frontier drip crosses a new
  threshold — per-pair `transition_p3_minute_le_succ_max` caps outputs at max(inputs)+1);
  `rBeyond_frontier_succ_eq_zero` (frontier empty) feeds `real_front_advance_squares` →
  `climb_prob_le_sq`: rise rate ≤ (B'/n)² on {rBeyond(k+1) ≤ B'}.
- `climbPot` — TRUNCATED potential exp(s·climbN) frozen to 0 once θn ≤ rBeyond k. The freeze +
  rBeyond-monotonicity make the drift hold on the UNION gate climbGate = {card=n ∧ AllClockP3} ∩
  ({rBeyond(k+1) ≤ B'} ∪ {θn ≤ rBeyond k}) — killing happens EXACTLY on the dangerous event
  {rBeyond(k+1) > B' ∧ rBeyond k < θn} (or hour-window exit, benign).
- `climb_real_tail` (capstone, via brick-2 gated_real_tail): (K^t) c₀ {rBeyond k < θn ∧
  0 < rBeyond(k+W₂)} ≤ escape + r^t·climbPot c₀/e^{s(W₂−1)}, r = 1+(B'/n)²(e^s−1). At paper scales
  (B'/n = n^{-0.8}, s = Θ(log n), W₂ = Θ(loglog n)) the tail term is n^{-ω(1)}.
- REMAINING for ClimbBound whp: bound the escape mass (= the brick-3.4 tainted-set deliverable
  P[rBeyond(k+1) > B' while rBeyond k < θn]) + instantiate scales + union over k and the horizon.
- 3.3 **DONE (EarlyDripMarked.lean, 0-sorry, axiom-clean)** — the marked kernel + the FULL projection
  bridge, on the REAL kernel (not the abstract clock): MarkedAgent = AgentState × Bool; markFor (Doty's
  positional rule: below T+1 → false; already above → keep; drip-crossing → gate value g; sync-crossing →
  inherit leader's mark); preBulkGate (g computed from the ERASED config — config-dependent kernel, legal
  for kernels though not for protocols); markedK via the SAME interactionPMF over marked states.
  Projection: interactionPMF_map_proj (the scheduler fiber identity Σ_{b₁,b₂} interactionCount = erased
  interactionCount — ordered distinct-agent pairs partition exactly along marks, diagonal count(count−1)
  works out), erase_markedStep (the step projects), markedK_map_erase (one-step measure-level), and
  **markedK_pow_erase: (markedK^t) mc₀ (erase⁻¹ A) = (K^t)(erase mc₀) A** — every marked-world whp
  statement about erased events transfers verbatim.
- 3.4a **DONE (same file, Part 5, 0-sorry axiom-clean)** — the deterministic taint bookkeeping, with a
  KEY simplification over the planned count-equality induction: instead of inducting
  "taintedCount = rBeyond(T+1)" along the gated trajectory, define cleanAbove (above-T ∧ unmarked) and
  prove (i) `aboveCount_eq_tainted_add_clean`: aboveCount = taintedCount + cleanAbove given MarkInv
  (pure countP algebra); (ii) `rBeyond_erase_eq_aboveCount` on AllClockP3; (iii) `markInv_step`
  (marks live above T — preserved UNCONDITIONALLY, by the mark-rule guard); (iv)
  **`cleanAbove_zero_step`: within-gate purity is DETERMINISTICALLY absorbing** — gate open ∧
  cleanAbove = 0 ⟹ cleanAbove = 0 on the whole one-step support (a clean above-T output needs a clean
  above-T ancestor / closed gate / sub-T minute — all four markFor branches excluded; the sync branch
  uses transition_p3_sync_minute). Pre-gate "c_{≥T+1} = d" (paper's base case) is the corollary, no
  probabilistic induction needed.
- 3.4b **DONE (EarlyDripMarked.lean Parts 6-7, 0-sorry axiom-clean)** — the taintedCount rise structure:
  (i) `markFor_true_cases` + sharp `markFor_true_crossing_cases` (inherited ∨ gated-drip-seed ∨
  epidemic-from-tainted); (ii) `at_most_one_crossing` (per Phase3 branch); (iii)
  `taintedCount_le_succ_on_support` (rises ≤1/step — feeds mgf_one_step); (iv) scheduler block bounds:
  `sum_block_interactionCount` (X(X−1) identity), `pair_block_prob_le_sq` (≤(X/n)²),
  `fst/snd_block_prob_le` (EXACT X/n via row+column sums), `markedK_apply_pair` (kernel→pair-law
  pullback), `tainted_rise_subset` ({rise} ⊆ same-minute-T-pair ∪ tainted-member-pair), and the
  capstone **`tainted_rise_prob_le`: P[taintedCount rises] ≤ (count@T/n)² + 2·taintedCount/n** —
  the exact two-phase rate (drip seed + branching) of Doty's d-analysis. NOTE: the bound is at the
  exact minute-T count (count@T ≤ rBeyond T ∘ erase via countP mono, T-level only — sharper than θ²;
  gate-conditioning enters when instantiating on {rBeyond T < θn}).
- 3.4c-i **DONE (GatedGeometricDrift.lean, 0-sorry axiom-clean)** — the STEP-INDEXED gated engine:
  `lintegral_stepIndexed_decay` (potential family Φ_j with ∫Φ_{j+1}dK ≤ Φ_j contracts E[Φ_t(X_t)] ≤
  Φ_0(x); induction generalizes over the SHIFTED family) + `stepIndexed_gated_tail` ((K^t)x{θ ≤ Φ_t} ≤
  escape + Φ_0 x/θ; killed drift needs NO r ≥ 1 side condition). This is the time-dependent-MGF
  engine for branching rates: instantiate Φ_j = exp(s_j·taintedCount + b_j) with s_j ≥ s_{j+1} +
  2(e^{s_{j+1}}−1)/n (slope absorbs branching 2N/n) and b_j ≥ b_{j+1} + θ²(e^{s_{j+1}}−1) (intercept
  absorbs drip-seed immigration); s_0/s_t ratio over a window of length t costs (1+4/n)^t ≈ e^{4t/n}
  = polyloglog for t = O(n loglog n).
- 3.4c-ii **DONE (EarlyDripMarked.lean Parts 8-9, 0-sorry axiom-clean)** — the instantiation:
  `tainted_rise_subset_gate_false` + `tainted_rise_prob_le_of_gate_false` (gate closed ⟹ NO drip
  marks — branch 3 self-kills — so P[rise] ≤ 2·tainted/n); `countT_le_rBeyond_erase`;
  `taintedPot_drift` (Φ_j = exp(s_j·taintedCount + b_j) is a one-step supermartingale on the
  hour-window gate taintedGate = {card = n ∧ AllClockP3∘erase}, GIVEN the slope recursion
  s_{j+1} + 2(e^{s_{j+1}}−1)/n ≤ s_j and intercept recursion b_{j+1} + (θn/n)²(e^{s_{j+1}}−1) ≤ b_j;
  the per-state rate (θn/n)² + 2N/n is uniform over the window because the mark rule stops drip
  seeds post-gate); capstone **`tainted_marked_tail`: (markedK^t) mc₀ {a ≤ taintedCount} ≤
  hour-escape + Φ_0(mc₀)/exp(s_t·a + b_t)** via stepIndexed_gated_tail.
- 3.4c-iii **DONE (EarlyDripMarked.lean Part 10, 0-sorry axiom-clean)** — the explicit sequences:
  `exp_sub_one_le_two_mul` (e^x − 1 ≤ 2x on [0,1/2], via exp_bound_div_one_sub_of_interval);
  geometric slope s_j = σρ^{(t:ℤ)−j} (ρ = 1+4/n, INTEGER exponent so the recursion holds at every j),
  linear intercept b_j = β((t:ℤ)−j), β = 2σρ^t(θn/n)²; capstone **`tainted_marked_tail_explicit`:
  P[taintedCount ≥ a at t] ≤ hour-escape + exp(σρ^t·N₀ + 2σρ^t(θn/n)²t − σa)** given σρ^t ≤ 1/2.
  Paper scales: θn/n = n^{-0.45}, t = O(n loglog n) (so ρ^t = e^{O(loglog n)} = polylog — pick
  σ = 1/(2ρ^t) = Θ(1/polylog)), a = n^{0.15}: exponent = O(n^{0.1}·polylog) − n^{0.15}/polylog
  = −n^{0.15−o(1)} → tail e^{-n^{0.15−o(1)}} = n^{-ω(1)} ✓. **BRICK 3.4 COMPLETE** (a, b, c-i—iii).
  REMAINING: numeric scale plug-in when assembling 3.5 + the hour-escape mass + 3.5: Lemma 6.3's
  window recurrence (clean part y ≤ 0.9px² via cleanAbove machinery + bulk epidemic
  ConstantDensityEpidemic) → WindowedFrontProfile whp + ClimbBound whp (escape of climb_real_tail =
  this 3.4 deliverable) → goodFrontWidth_of_windowed_profile_and_climb → rewire the clock. the constant-rate gated MGF
  CANNOT close the post-seed phase — sync-from-tainted has rate ∝ taintedCount/n (branching), and
  gating on {tainted ≤ M} makes the worst-case rate M/n accumulate to M·loglog n over the O(n loglog n)
  window — useless. The faithful tool is the paper's two-phase split: (a) pre-bulk drip count via the
  additive union bound (≤ t·(θ)² seeds, = O(n^{-0.89})·n agents); (b) post-seed epidemic growth bounded
  by TIME: growing n^{-0.89} → n^{-0.85} needs Ω(log n) time > O(log log n) window (epidemic upper
  concentration, the dual of ConstantDensityEpidemic). Alternative engine if (b)'s per-step form is
  needed: TIME-DEPENDENT MGF (s_j = s·e^{-λ(t-j)/n} supermartingale, generalizing geometric_drift_tail
  to a step-indexed potential) — handles branching with only polyloglog loss on the window.
- 3.5 `WindowedFrontProfile` whp — Lemma 6.3's 0.1-window induction assembling (a)+(b)+bulk epidemic
  (ConstantDensityEpidemic) + Chernoff on window drips; then rewire the clock onto
  goodFrontWidth_of_windowed_profile_and_climb.

## BRICK 3.5 DESIGN (scoped 2026-06-09 end-of-session; next session starts here)

KEY STRUCTURAL FINDING: `cleanAbove` has the SAME rise structure as `taintedCount` — a clean-above
output is inherited-clean, a POST-gate drip crossing (g = false ⟹ branch 3 yields false = clean), or
a sync crossing from a clean-above leader. So P[cleanAbove rises] ≤ [¬gate]·(count@T/n)² +
2·cleanAbove/n — the mirror image of the tainted rate (gate-complementary seed terms). The whole
time-dependent-MGF machine (taintedPot_drift / tainted_marked_tail) applies verbatim with clean in
place of tainted.

Brick list:
- 3.5a: `cleanAbove_rise_prob_le` (mirror tainted_rise_prob_le with the complementary gate) +
  REFACTOR opportunity: extract the generic "affine-rate counter tail" (counter rises ≤1/step with
  rate ≤ A + 2N/n on a gate ⟹ explicit-sequence tail) from Parts 9-10, instantiate twice.
- 3.5b: the sharper exp bound e^x − 1 ≤ (1+ε)x (small x) — **REQUIRED, not an optimization**: the
  crude ρ = 1+4/n gives per-0.1-window branching e^{0.4} ≈ 1.49, hopeless. **AND a constants alarm
  (END-OF-SESSION FINDING, verify against the PDF before coding 3.5d):** the txt-extracted printed
  chain 1.23·(0.9·0.84² + 0.11) = 0.916 > 0.9 does NOT close — in fact 1.23(c·0.7056 + 0.11) ≤ c
  forces c ≥ 1.024, impossible for ANY c < 1. Either the txt constants are OCR-corrupted (0.8 for
  0.84 closes easily: c ≥ 0.635) or the paper has a slip. RESOLUTION EITHER WAY: derive OUR OWN
  small-window constants — window w (parallel time), x-growth g = e^{-1.8w} (epidemic rate ≥ 2·0.9
  at x ≤ 0.1), y-branch f = e^{2w}, drips ≤ 1.1w·px²n: the induction f(c·g² + 1.1w) ≤ c becomes, as
  w → 0, c·(1.6w) ≥ 1.1w i.e. c ≥ 0.6875 + O(w) — CLOSES COMFORTABLY at c = 0.9 with small w (e.g.
  w = 0.02: f ≈ 1.041, g² ≈ 0.931, 1.041(0.9·0.931 + 0.022) = 0.895 < 0.9 ✓). So 3.5d should be
  parameterized by w with our own verified arithmetic, not the paper's printed constants.
- 3.5c: the epidemic LOWER growth bound for x = frac T over a 0.1-window (x(t−0.1) < 0.84x(t) whp,
  paper Lemma 4.5 inversion) — from the existing Epidemic/EpidemicTime machinery (check
  `advance_prob_ge`-style lower bounds at general fractions x ≤ 0.1, NOT just the 0.1→0.9 crossing;
  the real-kernel transfer pattern is in ClockRealBulk/ClockRealSeed).
- 3.5d: the 0.1-window induction: stopping times t^θ_{≥T} (gate break) and t^{0.1}_{≥T}; per-window:
  y(t_k) ≤ 1.23·(y(t_{k−1}) + 0.11·x_k²·n) whp (3.5a window tail) and x_{k−1} ≥ 0.84·x_k whp (3.5c);
  the arithmetic 1.23(0.9p(0.84x)² + 0.11px²) < 0.9px² closes the induction (paper line ~1850).
  Number of windows = O(loglog n) — needs the t^{0.1}−t^θ window-length input (Lemma 6.4 per-minute
  O(1), the coupled induction's other leg; may need to carry it as a hypothesis first and discharge
  in the joint minute-induction).
- 3.5e: assemble: rBeyond(T+1) = tainted + clean (3.4a decomposition) ≤ n^{0.15} + 0.9px²n ≤ px²n on
  the window (x² ≥ n^{-0.8} makes the d-term negligible) → WindowedFrontProfile whp; plug the d-tail
  into climb_real_tail's escape → ClimbBound whp; feed goodFrontWidth_of_windowed_profile_and_climb →
  GoodFrontWidth whp → frontSync_of_goodWidth_of_bulk_below → rewire ClockFrontWidth/ClockEnvMaint
  off the FALSE hwin_all. Union over levels T (≤ capMinute) and the horizon.

## Build routing / discipline
Single-file `lake env lean` to iterate locally; full module build → uisai1 `scripts/remote-build.sh`. Each
lemma: 0-sorry, `#print axioms` = [propext, Classical.choice, Quot.sound]; verify each statement is TRUE
before proving (9+ false-shapes caught this campaign — the stopping-time gate is exactly where a 10th could
hide; the gate `G` must be in the stopping-time/event, NOT an assumed feeder bound). Single coherent line
(no parallel codex on this — it is deeply coupled). Commit per lemma.

## 3.5c LEDGER (2026-06-09 session end-stretch; commits through f729c623)
DONE (all in EarlyDripMarked.lean, 0-sorry axiom-clean):
- mgf_one_step_lower (Part 14): monotone counter, rise prob ≥ r ⟹ ∫exp(−sN) ≤ (1−r(1−e^{−s}))exp(−sn₀).
- countGE_eq_rBeyond_erase + mixed_pair_raises (Part 15): mixed (above,below) pair always raises the
  erased tail (sync geometry + role preservation + countP accounting).
- sync_rise_prob_ge: P[erased tail rises] ≥ 2X(n−X)/(n(n−1)) EXACTLY (mixed-block sum; every
  positive-prob block pair lands in the rise set via support_pair_le).
- rBeyond_erase_monotone (Part 16): erased tail monotone along the marked chain (the hmono input).
- one_sub_exp_neg_ge: (1−s)s ≤ 1−e^{−s} (lower-rate retention).
REMAINING 3.5c-iv (the growth-tail assembly — NEXT): mirror of the upper machinery with the
DECREASING potential Φ_j = exp(−s_j·X): gate {X ≤ n/10} (so rate ≥ 2X·0.9n/n² ≈ 1.8X/n; escape = X
passed n/10 = even better growth, benign); drift via mgf_one_step_lower at the X-dependent rate +
one_sub_exp_neg_ge; the X-dependence absorbed by GEOMETRIC s_j (INCREASING in j; s_w = σ);
conclusion P[X_w ≤ g·X₀] ≤ escape + exp(−X₀(s_0 − σg)): choose g < s_0/σ. Then 3.5d: per-window
induction y_k ≤ f(y_{k−1} + drips) ∧ X_{k−1} ≥ g·X_k composed over O(loglog n) windows with the
OWN-CONSTANTS arithmetic (w = 0.02 closes at c = 0.9, see the constants alarm above).

## 3.5c COMPLETE (commit 1deae243) + 3.5d DESIGN (the window-induction composition)
3.5c-iv done: growthGate {10X ≤ n} + growth_rate_ge (≥1.8X/n via sync_rise_prob_ge reduction) +
growthPot_drift (decreasing potential exp(−s_j X), INCREASING slope recursion s_j ≤ s_{j+1} +
1.8(1−e^{−s_{j+1}})/n) + growth_marked_tail (P[X_w ≤ a] ≤ sub-bulk escape + exp(−s_0X₀ + s_w a)).
ALL of 3.5c is now in EarlyDripMarked.lean, 0-sorry axiom-clean.

3.5d — the per-window induction (next, fresh-context work):
- Induction STATE at window k: the pair (X_k, Y_k) = (rBeyond T ∘ erase, cleanAbove) at the window
  boundary, with INVARIANT Y_k ≤ c·X_k²/n (count form of y ≤ c·p·x², p = 1 worst case, c = 0.9).
- Per-window step (w·n kernel steps, w = 0.02): three tail inputs at the window boundary configs:
  (i) clean_marked_tail with the explicit (1+ε)-sequences: Y_{k+1} ≤ f·(Y_k + 1.1w·X_{k+1}²/n) whp,
      f = e^{(2+ε)w} (uses exp_sub_one_le_mul; X capped by the cleanGate at X₁ := X_{k+1}-bound);
  (ii) growth_marked_tail: X_k ≤ g⁻¹·X_{k+1} whp viewed backwards (the feeder grew by ≥ e^{1.6w'}…
      choose g = e^{-1.7w} with margin);
  (iii) the arithmetic f(c·g² + 1.1w) ≤ c at w = 0.02, c = 0.9 (verified: 1.041(0.9·0.931+0.022)
      = 0.895 < 0.9 ✓ — re-verify in Lean with rational arithmetic, norm_num).
- COMPOSITION: chain via the Markov property (Kernel.pow_add conditional split, the
  earlyDrip_kernel_bound induction pattern): P[invariant fails by window K] ≤ Σ_k (per-window
  failures). Number of windows: carry as a parameter W₃ (= O(loglog n), discharged by the
  minute-induction later — do NOT hardcode).
- Union with the tainted tail (d ≤ n^{0.15} whp) via aboveCount_eq_tainted_add_clean →
  rBeyond(T+1) ≤ c·X²/n + n^{0.15} → WindowedFrontProfile θ (θ = n^{-0.4}: the d-term is negligible
  since X²/n ≥ n^{-0.8}·n = n^{0.2} ≫ n^{0.15}).
- THEN 3.5e: ClimbBound whp (climb_real_tail escape := the tainted tail at level k+1) + union over
  levels/horizon + goodFrontWidth_of_windowed_profile_and_climb + rewire FrontSync consumers.

## 3.5d KEY DESIGN UNLOCK (deterministic-threshold split) + ledger through commit 18eee70c
- clean_marked_tail_explicit DONE (ε-parameterized ρ = 1+2(1+ε)/n, per-window y-tail).
- growth_marked_tail_const DONE — IMPORTANT SIMPLIFICATION: the growth direction needs NO geometric
  sequences; the CONSTANT slope σ satisfies the recursion trivially and gives P[X_w ≤ a] ≤ escape +
  exp(−σ(X₀−a)), already exponentially small in the missing growth (X₀ ≥ θn in the window). The
  γ-geometric sharpening is unnecessary for the induction.
- THE SPLIT that makes the window induction composable with DETERMINISTIC thresholds: the per-window
  bad event {Y_w > c·X_w²/n} (random threshold!) splits as
    {Y_w > c·X_w²/n} ⊆ {X_w ≤ a} ∪ {Y_w > c·a²/n}
  for ANY deterministic a (on {X_w > a}: c·X_w²/n > c·a²/n). Choose a := growth-target(X₀)
  (deterministic given the window-start config). So the per-window failure ≤ growth-tail(a) +
  clean-tail(c·a²/n) + the two escapes — all at deterministic thresholds, and the checkpoint
  composition is the standard conditional-split induction over kernel powers (earlyDrip_kernel_bound
  pattern): P[Inv fails by checkpoint K+1] ≤ P[fails by K] + sup_{Inv-configs} P[per-window fail].
- NEXT concrete bricks: (i) per_window_step lemma (the split + the two tails + arithmetic
  f(c·g² + 1.1w) ≤ c at the chosen w, c, ε, σ); (ii) checkpoint_induction (Markov-property chaining
  at horizon multiples of w); (iii) instantiate scales → WindowedFrontProfile whp.

## 3.5d-iii THE CLOSING ARGUMENT (worked out end-of-stretch; commits through 7670c7e2)
DONE: per_window_step (3.5d-i, the deterministic-threshold split + two tails) and
invariant_union_bound + checkpoint_composition (3.5d-ii, the generic window-kernel chaining).
THE REMAINING SUBTLETY AND ITS RESOLUTION (fully determined, implement next):
- The clean tail's drip-seed term uses the GATE CAP X₁ for the whole window, but X varies within
  the window; a global cap (n/10) swamps small-X windows. The paper uses the window-END value
  (backward-anchored windows) — random in the forward formal composition.
- RESOLUTION = monotonicity + dyadic split on the end value: partition the window outcomes by
  {G^m·X₀ < X_w ≤ G^{m+1}·X₀} (m = 0, 1, …, ≤ log_G n terms). On slice m, BY MONOTONICITY the
  trajectory NEVER exceeded G^{m+1}X₀, so the clean tail at gate X₁ := G^{m+1}X₀ applies with NO
  escape term (needs a "stayed-in-gate" refinement of real_le_killed: if the gate is monotone-exit,
  (K^w) x {bad ∧ end-in-gate} ≤ (killK^w)(some x){some-bad} — no {none} term).
- ARITHMETIC per slice (cc = 0.9, f = (1+2.1w)-ish branching, drips ≤ 1.1w·X₁²/n):
  m = 0: f(cc + 1.1G²w) ≤ cc·g² needs g ≥ 1 + 1.66w with G ≈ 1.03 — the growth tail
  (rate ≥ 1.8X/n at x ≤ 0.1) provides g = e^{1.7w}-ish: closes with margin ≈ 0.04w (TIGHT — use
  w = 0.015 and recheck constants in Lean with norm_num; if too tight, sharpen the sync rate to
  2(1−x)X/n ≈ 2X/n for small x).
  m ≥ 1: f(cc/G^{2m} + 1.1G²w) ≤ cc — the G^{2m} slack dominates; easy for w ≤ 0.017.
  The dyadic union adds a factor ≤ log_G n ≪ the exponential tails.
- LEMMA LIST: (a) stayed_in_gate_coupling (monotone-exit refinement of real_le_killed);
  (b) per_window_step_dyadic (the m-th slice bound); (c) window_constants (norm_num arithmetic at
  w = 0.015, G = 1.03, cc = 0.9); (d) the assembled per-window δ + checkpoint_composition feed →
  the recurrence invariant whp over the level-T window; (e) union over T + horizon →
  WindowedFrontProfile.

## 3.5d-iii(b) ARCHITECTURE DECISION (after real_le_killed_of_monotone, commit 314888a8)
The slice coupling (no-escape) works for PURE monotone gates {M ≤ X₁}; mixing in the hour window
H = {card = n ∧ AllClockP3∘erase} per slice would need a two-cemetery kernel to separate benign
H-exits from monotone exits. INSTEAD: kill at the hour window ONCE, globally — define
markedKH := killK markedK H at the TOP of the window-composition analysis; on the H-killed chain
every alive state satisfies AllClockP3∘erase + card = n automatically, so taintedGate/cleanGate/
growthGate reduce to their X-components (pure monotone gates), the slice analysis uses
real_le_killed_of_monotone directly, and ONE global hour-escape term appears in the final transfer
(benign: hour completed). All existing on-gate drift lemmas remain valid as inputs (they prove the
drift exactly on AllClockP3 ∧ card states). Implement as: (i) markedKH + its Markov instance +
the lifted drift lemmas (mechanical wrappers); (ii) the dyadic slice bound on markedKH via
real_le_killed_of_monotone + the extracted stepIndexed killed tail; (iii) window_constants norm_num;
(iv) per-window δ + checkpoint_composition → the recurrence invariant whp; (v) transfer back
through the H-kill and the projection bridge → WindowedFrontProfile.

## 3.5d LEDGER FINAL (2026-06-09 evening; 40 commits; HEAD 5b9c6249; uisai2 FULL-BUILD GREEN ×2)
uisai2 verification: BOTH runs green ("Build completed successfully (4123 jobs)") — the entire tree
including all 40 commits. (Watch out: grep-verdicts misfire on style-linter noise; trust lake's own
success line.)
3.5d machinery COMPLETE through the per-window bound:
- per_window_step / invariant_union_bound / checkpoint_composition (the spine);
- real_le_killed_of_absorbing + ae_notG_pow (zero-escape coupling, absorbing-complement gates);
- stepIndexed_killed_tail; slice-gate absorbing inputs (GE3 region, phase4 permanence, monotone X);
- slice_clean_tail_explicit + slice_growth_tail (ZERO-ESCAPE tails both directions);
- ladder_locate / ladder_bad_subset (the dyadic ladder split);
- **per_window_ladder (capstone): P[per-window Lemma 6.3 failure] ≤ e^{−σg(X₀−a0)} +
  Σ_m e^{σρ^w Y₀ + (a_{m+1}/n)²(1+ε)σρ^w w − σ Yt_m} — pure exponentials, NO escape terms.**
REMAINING for Lemma 6.3 (next session, fully determined):
(1) the UNIFORM δ over invariant states: instantiate the ladder geometrically (a m = G^m·a 0,
    a 0 = the growth target g·X₀), Yt m = ⌈cc(a m)²/n⌉+…, and bound the RHS uniformly over
    Inv-states (θn ≤ X₀ ≤ n/10, Y₀ ≤ cc·X₀²/n) — the slice-m exponent must be ≤ −Ω(n^{0.1}) per
    the m=0 tight case (margin 0.04w) and m≥1 easy cases; norm_num at w, G, cc per the doctrine
    constants section (w = 0.015, G = 1.03, cc = 0.9);
(2) checkpoint_composition at the window kernel with Inv := {recurrence ∧ region} and the uniform δ;
(3) the assembly: tainted_marked_tail_explicit (d ≤ n^{0.15}) + aboveCount decomposition →
    rBeyond(T+1) ≤ cc·X²/n + n^{0.15} ≤ X²/n at window scales → the per-level recurrence whp;
(4) union over levels T ≤ capMinute and the horizon; transfer through markedK_pow_erase →
    WindowedFrontProfile whp. Then 3.5e: ClimbBound whp (climb_real_tail escape := tainted tail) +
    goodFrontWidth_of_windowed_profile_and_climb → rewire the clock off hwin_all.

## 3.5e FINDING (2026-06-09 fresh session) — the 11th false/incomplete shape: the existing
##   `growth_marked_tail` certifies the WRONG direction; the recurrence needs an UPWARD growth tail.
CHECKED BEFORE PROVING (numeric + paper re-read, definitive):
- The per-window recurrence Y ≤ cc·X²/n is preserved ONLY if X GREW: worst-case
  `f·(cc + drips) ≤ cc·g²` forces the growth factor `g = X_{end}/X_{start} ≥ g_min ≈ 1.0245 > 1`
  (at wp = 0.015, cc = 0.9, eps = 0.02). With g ≤ 1 (anti-shrink) the LHS f(cc+drips) > cc ≥ cc·g²
  ALWAYS — the y-branching f > 1 strictly grows Y while cc·X²/n does not grow, invariant breaks.
  This matches the PAPER (Doty txt 1820): the leg used is `x(t−0.1) < 0.84·x(t)` — backward-anchored
  UPWARD growth `x(end) ≥ x(start)/0.84`, certified by the epidemic LOWER bound (Lem 4.5/Thm 4.3),
  NOT by an anti-shrink supermartingale.
- BUT the only X-growth tool in EarlyDripMarked is `growth_marked_tail`/`growth_marked_tail_const`,
  whose exponent is `exp(σ(a − X₀))` — small ONLY for `a < X₀` (anti-SHRINK: "X did not drop below a").
  It CANNOT certify `P[X_w < g·X₀]` small for g > 1. So `slice_growth_tail` (the floor branch of
  `per_window_ladder`) and the geometric ladder `a m = G^m·a0, a0 = g·X₀` of LEDGER-FINAL step (1)
  are INCOMPATIBLE: floor needs a0 < X₀ (anti-shrink), slices need a0 ≥ √RW·X₀ > X₀ (clean closes).
  Numerically the m=0,1 slice exponents are POSITIVE (≈ +115, +27 at a0 = X₀) — useless.
- THE MISSING TOOL (buildable, NOT in the DONE list): an UPWARD growth tail that RETAINS the
  contraction factor `ρ < 1` that `growthPot_drift` already produces (line ~2919:
  `e^{−r(1−e^{−s})}` with r = 1.8X/n) but that `growth_marked_tail` THROWS AWAY (constant slope makes
  the recursion `s ≤ s + 1.8(1−e^{−s})/n` slack, discarding ρ). Gating `X ≥ X₀` (monotone, from
  `rBeyond_erase_monotone`) makes r ≥ 1.8X₀/n uniform, so over w = wp·n steps
    E[exp(−sX_w)] ≤ exp(−1.8(X₀/n)(1−e^{−s})·w)·exp(−sX₀) = exp(−1.8X₀(1−e^{−s})wp − sX₀),
  Markov at a = g·X₀ gives `P[X_w ≤ g·X₀] ≤ exp(−X₀·δ)`, δ = 1.8(1−e^{−s})wp − s(g−1) > 0
  for g−1 < 1.8wp(1−e^{−s})/s. CLOSES at g = g_min: best δ ≈ 1.1e-4 @ s = 0.096, wp = 0.015,
  cc = 0.9, eps = 0.02 (margin is structurally ~9%, wp-independent: (g_min−1)/(1.8wp) ≈ 0.91).
  Tail = exp(−δ·X₀) ≤ exp(−n^{0.55}·1e-4) = n^{−ω(1)} since X₀ ≥ θn ≥ n^{0.55}. ✓
- REVISED LEDGER-FINAL step (1): FIRST build `growth_marked_tail_up` (the upward tail, retaining ρ,
  gated on X ≥ X₀ via the monotone region), THEN instantiate the ladder with `a 0 = g·X₀`
  (g = g_min > 1, so a0 > X₀; floor branch = `P[X_w ≤ g·X₀]` = the UPWARD tail, small) and slices
  `a m = G^m·a0` geometric above a0. Re-derive the uniform δ. Constants this session:
  wp = 0.015 (kernel steps w = ⌊3n/200⌋), cc = 9/10, eps = 1/50, s = σ_grow chosen ~0.096, G ≈ 1.03.
  This replaces `slice_growth_tail` in the floor branch of `per_window_ladder` with the upward tail.

## 3.5e LOCKED CONSTANTS (2026-06-09, verified numerically across n = 10^4…10^7, finite-n RW)
The uniform-δ instantiation of `per_window_ladder_up` uses (ALL re-verifiable by norm_num + the
standard exp bounds `exp(u) ≤ 1+u+u²/2+u³/2` upper / `1−e^{−sg} ≥ sg−sg²/2` lower):
- wp = 3/200 (= 0.015 parallel time); kernel window w = ⌊3n/200⌋.
- cc = 9/10 (the recurrence constant y ≤ cc·x²·p, p = 1 worst case).
- ε = 1/200 (the clean-tail (1+ε)-sharpening; small ε WIDENS the slice margin — at ε = 0.005 the
  worst slice bracket is −8e-4, 6× the ε = 0.02 margin of −1.3e-4).
- g = 1.0246 (growth floor a 0 = ⌈g·X₀⌉ > X₀, the UPWARD growth target).
- G = 1.005 (ladder ratio a m = ⌈G^m·a 0⌉; small G reduces the drip overcount).
- sg = 1/10 (growth-tail slope); σ ≤ ε/((1+ε)·RW) ≈ 0.0048 (global MGF scale; hsmall).
THE TWO BINDING MARGINS (both robust across finite n):
- slice bracket(m) := cc·RW − cc·G^{2m}g² + G^{2m+2}g²(1+ε)·RW·wp ≤ −8e-4 < 0 ∀m
  (RW = (1+2(1+ε)/n)^w ≤ exp(2(1+ε)wp); slice exp = σ·(X₀²/n)·bracket(m) ≤ −Ω(σ·n^{0.1})).
- growth δ := 1.8(1−e^{−sg})wp − sg(g−1) ≥ +1.05e-4 > 0
  (floor exp = −X₀·δ ≤ −Ω(n^{0.55})).
WHY w cannot widen the slice margin: g−1 ≈ 1.66wp (recurrence floor) must fit under the growth
ceiling 1.8wp·(1−e^{−sg})/sg; the gap is ~0.14wp, INDEPENDENT of w (both legs scale linearly), so
shrinking w shrinks both margins proportionally. The widening levers are ε↓ (slice) and the ladder
ratio G↓ (drip overcount), NOT w. The m=0 slice is intrinsically the tight one (~1e-4 at ε=0.02);
ε = 1/200 buys the comfortable −8e-4. The growth δ ~1e-4 is the residual tightest margin — it is the
0.14wp structural gap and cannot be widened without sharpening growth_rate_ge from 1.8 to 2(1−x).

## 3.5e SESSION LEDGER (2026-06-09 late; steps 1–2 machinery COMPLETE, conditional on hB)
Compiled, 0-sorry, axiom-clean, in EarlyDripMarked.lean (commits 16f28552, 00e0276d, 5268d45f,
11155bed, b8461bd5, 1cfc400d, 55acacac/3.5e-8; a parallel session then added 3.5e-9):
- slice_growth_tail_up (Part 27b): the UPWARD growth tail (the 11th-shape fix) — increasing
  backward slope s_j = σ + (w−j)·c, c = 1.8(1−e^{−σ})/n RETAINS the contraction;
  tail = exp(−(σ+w·c)X₀ + σ·a), small even for a = g·X₀, g > 1.
- per_window_ladder_up (Part 28b): per_window_ladder with the upward floor.
- window_constants_slice / window_constants_growth (Part 29): the two norm_num closing gates at
  the locked rationals (wp = 3/200, cc = 9/10, ε = 1/200, g = 5123/5000, G = 201/200, sg = 1/10).
- floor_exp_le + slice_exp_le + slice_sum_le + per_window_delta (Parts 29–30, step 1 capstone):
  per-window failure from an invariant start ≤ exp(−δg·X₀+σg) + M·exp(σ·Q·(A−B)), Q = X₀²/n.
- hourRegion(+ae_step) / notP3_ae_step / recInv / window_failure_le / recurrence_checkpoint
  (Part 31, step 2): Inv := card ∧ GE3 ∧ (P3 → 10X≤n → (θn≤X ∧ Y≤ccX²/n)); the window-exit and
  region-exit failure modes are NULL (ae_notG_pow instances: region-absorbing, X-monotone,
  phase-4 permanence); checkpoint failure ≤ K·δ GIVEN hB (the per-mc₀ bad-event bound).

## 3.5e THE hB DISCHARGE — the TWO-REGIME design (numerically verified this session; NOT yet in Lean)
hB (recurrence_checkpoint's input) must bound, for every Inv window-open start (θn ≤ X₀ ≤ n/10,
Y₀ ≤ cc·X₀²/n), the bad event at the LADDER for that X₀. The ceiling a0 = ⌈g·X₀⌉ breaks
ha0 : 10·a0 ≤ n near the window top (g > 1!). RESOLUTION = split at X₀ ⋚ 4n/41 (= n/10.25):
- REGIME 1 (θn ≤ X₀ ≤ 4n/41): full ladder a_m = ⌈G^m·g·X₀⌉, M with a_M ≥ n/10
  (M = ⌈log_G(n/(10·g·θn))⌉ fixed, ladder-monotone). ha0: 10(g·(4n/41)+1) ≤ n ⟺ n ≥ 25641
  (scale hyp). hYt: Yt_m := ⌊cc·a_m²/n⌋ ≤ cc·a_m²/n + 1 ✓. hfloor: floor_exp_le +
  window_constants_growth (margin 1.05e-4). hslice: slice_exp_le + window_constants_slice;
  the ⌈⌉ rounding inflates the drip cap by (1+1/(g·θn))² ≤ 1+3/θn — absorbed by scale hyp
  θn ≥ 30000 (3/θn ≤ 1e-4 ≪ slice margin 3.65e-4). RW ≤ RWb via (1+x)^w ≤ e^{wx} ≤ 1/(1−wx)
  (Real.add_one_le_exp pow + exp_bound_div_one_sub_of_interval), needs w/n ≤ 3/200 i.e.
  w := ⌊3n/200⌋.
- REGIME 2 (4n/41 < X₀ ≤ n/10): the band is thinner than one growth factor — X exits the window
  (10X > n) whp within w steps, so M := 0, single floor a0 := aM := ⌊n/10⌋ (ha0 ✓ trivially).
  Floor exponent ≤ n·[σg(1/10 − 4/41) − (3/200)(18/10)(19/200)(4/41)] = n·(1/4100 − 4104/16400000)
  = −6.34e-6·n < 0 — pure-rational norm_num (uses 1−e^{−1/10} ≥ 19/200 from sg − sg²/2).
  Regimes OVERLAP (n/10.257 < n/10.246): both are covered at the boundary.
- The uniform δconst := ofReal(exp(−δg·θn + σg)) + M·ofReal(exp(σ·(θn²/n)·(A−B)))
  + ofReal(exp(−(63/10^7)·n + σg)), bounding both regimes (X₀ ≥ θn, Q ≥ θn²/n, A−B < 0).
REMAINING (in order): (i) the hB lemma per the regimes above (the last big arithmetic);
(ii) step 3 wiring INTO recurrence_checkpoint + tainted_marked_tail_explicit (a parallel session
committed front_squares_count/recurrence_combine — check before duplicating); (iii) step 4: union
over T ≤ capMinute + horizon, transfer through markedK_pow_erase, bridge counts → frac form of
ClockFrontProfile.WindowedFrontProfile (frac = rBeyond/card; 10X ≤ n ↔ frac ≤ 1/10 at card = n).
NOTE 2026-06-09: TWO sessions wrote this file tonight (3.5e-8/-9 overlap was benign but real);
keep the single-line discipline — check git log -3 BEFORE each append.

## STEPS 2–4 DONE (2026-06-09 fresh session; commits 55acacac..bafef960; EarlyDripMarked.lean,
## all 0-sorry axiom-clean [propext, Classical.choice, Quot.sound]; single-file lake env lean GREEN)

The 4-step assembly plan (LEDGER FINAL steps 2,3,4) is now formalized end-to-end on the REAL kernel.
STEP 1 (`per_window_delta`, the uniform per-window δ) + the previous-session `recInv`/`window_failure_le`
(Part 31) were the inputs.  New theorems (in build order):

STEP 2 — the checkpoint induction:
- `region_ae_pow` (generic stay-in-region a.e. through kernel powers) + `markInv_ae_step/_pow`.
- `recurrence_checkpoint` (Part 31 capstone): chains the previous-session `window_failure_le`
  (which already handles all three exit modes — region/window/floor — via `ae_notG_pow`, and whose
  live-window bad event is exactly `per_window_delta`'s) through `checkpoint_composition`.
  Conclusion: from a `recInv` start, `(markedK^{w·KK}) mc₀ {¬recInv} ≤ KK·δ`, the run-long
  recurrence-invariant failure bound.  `δ` is the per-window bad-event bound (= `per_window_delta`'s
  RHS at the live window-open invariant states; supplied as the `hB` hypothesis).

STEP 3 — the per-level recurrence:
- `recurrence_combine` + `front_squares_count`: the DECOMPOSITION `rBeyond(T+1)∘erase = taintedCount
  + cleanAbove` (via `rBeyond_erase_eq_aboveCount` on P3 + `aboveCount_eq_tainted_add_clean` under
  MarkInv) ⟹ `rBeyond(T+1) ≤ cc·X²/n + tt`; with the negligibility hypothesis `cc·X²/n + tt ≤ X²/n`
  ⟹ count-form squaring `rBeyond(T+1)·n ≤ X²`.
- `front_bad_subset` + `front_squares_whp` (Part 33 capstone): the bad event {in-window ∧ ¬square}
  ⊆ {¬recInv} ∪ {taintedCount ≥ tt+1} ∪ {¬MarkInv}; bounded by `KK·δ` (recurrence_checkpoint) +
  the taint tail `tainted_marked_tail_explicit` (the `{¬MarkInv}` mass is NULL via `markInv_ae_pow`).
  Conclusion: P[in-window-at-T yet front fails to square] ≤ KK·δ + (hour-escape + taint-tail).

STEP 4 — union + real-kernel transfer:
- `realFrontBad T` (the real-config per-level bad set) + `markedFrontBad_eq_preimage` (the marked
  bad event = `erase⁻¹(realFrontBad)`, since every condition is erase-measurable) +
  `real_front_squares_whp`: transfer `front_squares_whp` to the REAL kernel verbatim via
  `markedK_pow_erase`.
- `real_front_union`: union the real per-level failure over `T < Tcap`, bounded by the per-level sum.
- `windowedFrontProfile_of_not_bad` (the deterministic bridge, imports `ClockFrontProfile`): the
  union complement (+ region facts + per-floor negligibility) ⟹ `WindowedFrontProfile θ c` (Doty
  Thm 6.5's windowed recurrence shape).  Uses `ClimbTail.rBeyond_eq_zero_of_cap_lt` for levels past
  the cap (trivially out of the window since `frac = 0 < θ`).
- `windowedFrontProfile_whp` (STEP 4 CAPSTONE): assembles the union bound + the bridge into the
  real-kernel statement
    P[ card=n ∧ AllClockP3 ∧ (per-floor negligibility) ∧ ¬WindowedFrontProfile θ ]  ≤  Σ_{T<Tcap}
      ( KK·δ T  +  hour-escape_T  +  taint-tail_T ).

THE EXACT REMAINING GAP (all DETERMINISTIC/SCALE plug-ins; no new probabilistic engine needed):
1. The per-window δ: discharge `hB` (the `recurrence_checkpoint`/`front_squares_whp` input) from
   `per_window_delta` at the LOCKED constants — i.e. supply the geometric ladder `a m = ⌈G^m·a0⌉`,
   `a0 = ⌈g·X₀⌉`, `Yt`, and `δ = exp(−δg·X₀+σg) + M·exp(σ·Q·(A−B))` and show it ≤ a uniform value
   over `recInv`-states via `floor_exp_le`/`slice_exp_le`/`slice_sum_le`/`window_constants_*` (all
   already proven; only the scale arithmetic `θn ≤ X₀ ≤ n/10`, `Q = X₀²/n` plug-in remains).  Note
   `recInv` carries `θn ≤ X` and `10X ≤ n` (the window), and `per_window_delta` needs
   `card=n ∧ AllClockGE3` — `recInv`'s region — so the wiring is immediate; the floor `a0 > X₀`
   makes the recurrence-failure bad event's `X ≤ aM` cap honest (aM := a M).
2. The negligibility `∀ T, θ ≤ frac T → cc·X²/n + tt ≤ X²/n`: at θ = n^{-0.4}, tt = n^{0.15},
   cc = 9/10: `(1−cc)X² = X²/10 ≥ (θn)²/10 = n^{1.2}/10 ≫ tt·n = n^{1.15}` — pure norm_num/scale
   arithmetic on the final config (carry as the `hnegc` END-config property; it holds deterministically
   on every config with `frac T ≥ θ`).
3. The per-level start hypotheses `∀ T < Tcap, recInv T mc₀ ∧ MarkInv T mc₀`: the all-clean,
   all-window-open initial config (every agent at minute 0, mark = false) satisfies `MarkInv T`
   trivially (no tainted agents) and `recInv T` vacuously-or-at-floor; this is the natural Doty
   start.  (Could be packaged as an `initConfig` lemma.)
4. The tail-sum is `n^{−ω(1)}`: each `KK·δ T = O(n loglog n)·exp(−Ω(n^{0.1}))`, hour-escape =
   bulk-not-arrived (ConstantDensityEpidemic, benign), taint-tail = exp(−n^{0.15−o(1)}); summed over
   `Tcap = O(log n)` levels stays `n^{−ω(1)}` — the doctrine's LOCKED-CONSTANTS margins.
5. Rewire: feed `WindowedFrontProfile` (whp, from windowedFrontProfile_whp's complement) +
   `ClimbBound` (whp, the ClimbTail deliverable, escape := the taint tail) into
   `goodFrontWidth_of_windowed_profile_and_climb` → `GoodFrontWidth` whp →
   `frontSync_of_goodWidth_of_bulk_below` → drop the FALSE `hwin_all` in the clock.

All five remaining items are scale-arithmetic/wiring with NO new probabilistic content — the coupled
time-window engine (the genuine core that caught 11 false shapes) is fully formalized and transferred
to the real kernel.

## THE FIVE ITEMS — STATUS (2026-06-09 relay session; commits 2beb3a94..c1630926; EarlyDripMarked.lean,
## all 0-sorry axiom-clean [propext, Classical.choice, Quot.sound]; single-file lake env lean GREEN)

All five remaining items delivered as compilable, axiom-clean Lean theorems.  Build order / commits:

- **Item 3 (2beb3a94)** — initial-start dischargers (Part 38):
  `markInv_of_clean` (all marks false ⟹ MarkInv, taint = 0; axioms [propext] only),
  `taintedCount_of_clean`, `recInv_of_window_closed` (the genuine Doty start: in-region but
  `¬P3 ∨ ¬(10X≤n)` ⟹ recInv vacuous), `recInv_of_floor` (the at-floor case).  These supply the
  per-level `h0`/`hmark` inputs of `windowedFrontProfile_whp`.  NOTE: the all-minute-0 start is NOT
  AllClockP3, so recInv holds via `recInv_of_window_closed` (the window is not yet open) — the
  natural Doty start; `recInv_of_floor` covers the in-window levels.

- **Item 2 (78b177de)** — `negligibility_le` (Part 39): `cc·X²/n + tt ≤ X²/n` from `θn≤X`, `cc≤1`,
  `0<n`, and the carried scale fact `tt·n ≤ (1−cc)(θn)²`.  This is exactly
  `windowedFrontProfile_of_not_bad`'s/`front_squares_count`'s `hneg` (the `d`-term absorption).  At
  paper scales `(1−cc)(θn)² = n^{1.2}/10 ≫ n^{1.15} = tt·n`.

- **Item 4 (24cc7d28)** — tail-sum packaging (Part 40): `front_tail_term_le`/`front_tail_sum_le`
  collapse `windowedFrontProfile_whp`'s `Σ_{T<Tcap}(KK·δ T + esc_T + tail_T)` to the single form
  `Tcap·(KK·dB + eB + tB)` given uniform per-level bounds.  Capstone
  `windowedFrontProfile_whp_packaged` composes it with `windowedFrontProfile_whp` directly.

- **Item 5 (9cf23255 + 645690e6)** — the glue wiring, COMPLETE both sides (Parts 41–42):
  - `goodFrontWidth_bad_subset` + `goodFrontWidth_whp`: on the real kernel, `GoodFrontWidth(W₁+W₂)`
    failure (W₁ = frontWidthBound n) ≤ `WindowedFrontProfile` tail (item 4) + `ClimbBound`-failure
    mass, via the deterministic `ClockFrontProfile.goodFrontWidth_of_windowed_profile_and_climb`.
  - `climbBound_bad_subset` + `climbBound_whp`: the `ClimbBound`-failure mass ≤ `Σ_{k≤capMinute}`
    `ClimbTail.climb_real_tail`'s gated tail (escape + contraction).  At `card=n`, `θ=θn/n`:
    `frac k < θ ↔ rBeyond k < θn`; the climb past W₂ forces `k ≤ capMinute`
    (`climbN_ge_of_beyond_pos`).  This is the exact `climbB` input of `goodFrontWidth_whp`.
    ⟹ item 5 has NO residual — `GoodFrontWidth` whp is fully wired off the false `hwin_all`.

- **Item 1 (e739c82d + c1630926)** — the `hB` discharge (Parts 43, the last big arithmetic):
  - bricks `δgLocked`(+`δgLocked_pos`, the +1.05e-4 growth margin via `window_constants_growth`),
    `floor_discharge` (produces `per_window_delta`'s `hfloor` via `floor_exp_le`),
    `slice_discharge` (produces `hslice` per rung via `slice_exp_le`, all at the locked constants
    wp=3/200, cc=9/10, ε=1/200, g=5123/5000, G=201/200, sg=1/10).
  - `perWindowDelta_uniform`: monotonizes `per_window_delta`'s `X₀`-dependent RHS
    `exp(−δg·X₀+σg)+M·exp(σ(X₀²/n)·AB)` to the floor value at `X₀=θn` (uses `δgLocked>0`, `AB<0`).
  - capstone `hB_discharge`: delivers EXACTLY the `hB` shape of `recurrence_checkpoint`/
    `front_squares_whp`/`windowedFrontProfile_whp`, with the UNIFORM `δ = exp(−δgLocked·θn+1/10) +
    M·exp(σ·(θn²/n)·AB)`.  σg is locked to sg = 1/10 (the growth slope), cc = 9/10.

THE EXACT REMAINING RESIDUAL (item 1 only; the precise ceiling/scale plug-in, no probabilistic or
wiring content):  `hB_discharge` CARRIES, as hypotheses to be discharged at the numeric plug-in:
(a) the per-`mc₀` geometric ladder `a mc₀ m = ⌈G^m·⌈g·X₀⌉⌉`, `M`, `Yt mc₀ m = ⌊cc·a²/n⌋` and the
    rounding facts `ha0 : 10·a mc₀ 0 ≤ n` (the two-regime 4n/41 split, n≥25641), `haM : a mc₀ M = aM`,
    `hYtcap`;
(b) `hfloor` (the `floor_discharge` shape) — the window-length margin `δgLocked ≤ w·cg − sg(g−1)`
    with `w = ⌊3n/200⌋` (needs `w/n ≳ 0.01439`, holds for n ≳ 1639; `floor_discharge` is the proven
    composer, only the `w/n` lower bound remains);
(c) `hsliceB` (the `slice_discharge` shape) — per rung the drip cap (with ⌈⌉ inflation ≤ 1+3/θn,
    θn≥30000), `RW ≤ RWb` (via (1+x)^w ≤ 1/(1−wx)), the threshold lower bound `cc·Gm·g²·Q ≤ Yt`;
(d) the two locked margins `δgLocked_pos` (PROVEN) and `hAB` (= `window_constants_slice`'s `A<B`,
    PROVEN as a norm_num gate — instantiate `g,G,RWb` at the locked rationals and `hAB` is immediate).
All of (a)–(c) are pure ℕ-ceiling/finite-n-scale arithmetic on the explicit ladder; (d) is already a
proven norm_num gate.  Items 2–5 have NO residual.  The genuine probabilistic engine + all wiring
(checkpoint induction → per-level recurrence → real-kernel union → WindowedFrontProfile whp → glue →
GoodFrontWidth whp) is fully formalized and axiom-clean.
