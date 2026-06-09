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
  = polyloglog for t = O(n loglog n). REMAINING 3.4c-ii: the instantiation — one-step drift of the
  indexed potential from tainted_rise_prob_le (per-x rate q = (count@T/n)² + 2·tainted/n fed to
  mgf_one_step pointwise) + the explicit s_j/b_j sequences + the window gate; then the d-bound. the constant-rate gated MGF
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

## Build routing / discipline
Single-file `lake env lean` to iterate locally; full module build → uisai1 `scripts/remote-build.sh`. Each
lemma: 0-sorry, `#print axioms` = [propext, Classical.choice, Quot.sound]; verify each statement is TRUE
before proving (9+ false-shapes caught this campaign — the stopping-time gate is exactly where a 10th could
hide; the gate `G` must be in the stopping-time/event, NOT an assumed feeder bound). Single coherent line
(no parallel codex on this — it is deeply coupled). Commit per lemma.
