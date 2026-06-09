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
- **2c NEXT**: couple `killK^t` to `K^t` — `(K^t) x {θ≤Φ} ≤ (killK^t)(some x){θ≤killΦ} + (K^t) x {left G by t}`
  (real walk = stayed-gated [matched by killK] ∪ left-gate [benign, bulk arrived]). An induction relating the
  two kernels' powers. Then instantiate `G={beyond T<θn}`, `r=1` (binary empty) or the MGF `r`, discharge `hwin`.

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

## Build routing / discipline
Single-file `lake env lean` to iterate locally; full module build → uisai1 `scripts/remote-build.sh`. Each
lemma: 0-sorry, `#print axioms` = [propext, Classical.choice, Quot.sound]; verify each statement is TRUE
before proving (9+ false-shapes caught this campaign — the stopping-time gate is exactly where a 10th could
hide; the gate `G` must be in the stopping-time/event, NOT an assumed feeder bound). Single coherent line
(no parallel codex on this — it is deeply coupled). Commit per lemma.
