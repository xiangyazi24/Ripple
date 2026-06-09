# Doty time-half — establish CapRelWithinEnvFeeder (the genuine §6 front-shape core, with sync)

Directive: 闷头跑，绝对不退缩，不 over-claim. The clock rests on ONE carried window
`ClockCapRecur.CapRelWithinEnvFeeder f₀` = `capRelFrac 2 c ≤ env f₀ (cap−2)` ≈ "level cap−2 essentially empty"
(env(cap−2) ≪ 1/n). This is the leading-front subcriticality at the seeding boundary. The empty-seed squaring
`rBeyond_seed_le_rBeyondSq` is EXHAUSTED for it (the m→m+1 increment at an occupied level has a SYNC term
∝ rBeyond(T+1)·(n−rBeyond(T+1)) that does NOT square). This is the genuine Doty Theorem 6.5 core. ESTABLISH it
(do not assume it) or precisely characterize the irreducible obstruction.

## What's true and the genuine mechanism (think carefully first)
- `rBeyond(cap−2)` increments only when a clock crosses minute cap−3 → ≥cap−2. SYNC within the front
  (cap−2 → cap−1) does NOT change `rBeyond(cap−2)` (the clock stays ≥cap−2). So `rBeyond(cap−2)` increments via:
  (a) DRIP at cap−3 (2 clocks same minute cap−3 → one to cap−2): prob ∝ (clocks at cap−3)² — squares; or
  (b) SYNC cap−3 → ≥cap−2 (a clock at ≤cap−3 meets a clock at ≥cap−2): prob ∝ (clocks ≤cap−3)·rBeyond(cap−2).
  The SYNC term (b) is the obstruction — linear in rBeyond(cap−2), so it doesn't doubly-exp collapse by itself.
- BUT: term (b) requires a clock ALREADY at ≥cap−2 to sync TO. If `rBeyond(cap−2)=0`, term (b) is 0 (no sync
  target) ⟹ increment is drip-only (squares). So `rBeyond(cap−2)=0` is a FIXED POINT of the increment: once
  empty, it stays empty except via drip (squared, doubly-exp tiny). This is the key: the leading-front is
  ABSORBING-empty up to the drip-squared leak.
- So `CapRelWithinEnvFeeder` (≈ rBeyond(cap−2)=0) is maintained whp: starting empty (Phase-3 init, all clocks at
  minute 0), the only way to occupy cap−2 is the drip-squared seed (≤ (rBeyond(cap−3)/n)²), and the level-union
  (already proven, `feeder_narrow_concentration`) bounds the cumulative drip-seed prob over the horizon. The SYNC
  term only acts ONCE cap−2 is occupied — which the drip-squared bound shows is whp-never (for the top levels).

## Task (NEW file Probability/ClockBulkFront.lean only)
1. `feeder_empty_absorbing_up_to_drip`: on the kernel support, `rBeyond(cap−2) c = 0` ⟹ the one-step prob that
   `rBeyond(cap−2)` becomes ≥1 is ≤ (rBeyond(cap−3)/n)² (drip-only; the sync term vanishes because no clock is at
   ≥cap−2 to sync to). PROVE from `rBeyond_seed_le_rBeyondSq` (this is its hypothesis — feeder empty ⟹ seed
   squares; here generalized to: empty cap−2 ⟹ only drip can occupy it, sync needs an occupant). If
   `rBeyond_seed_le_rBeyondSq` already gives exactly this (seed from empty ≤ square), CITE it directly.
2. `capRelWithinEnvFeeder_concentration`: from the empty start + the absorbing-up-to-drip step, the horizon
   union (reuse `frontSync_union_horizon` / `feeder_narrow_concentration`) gives `rBeyond(cap−2)=0` whp over the
   run ⟹ `CapRelWithinEnvFeeder` holds whp, bounded by `H·(drip-squared)` = 1/poly. DISCHARGE the carried window
   (no longer an assumption) — GIVEN only the next-level drip-feeder bound `rBeyond(cap−3)` small, which recurses
   ONE more level (or bottoms at the bulk-top, the genuine final bulk condition).
3. Wire to `ClockCapRecur.clock_frontSync_via_capRel` so the clock FrontSync-whp carries one fewer assumption
   (CapRelWithinEnvFeeder discharged to the next drip-level, or to the bulk-top). HONEST: report exactly what
   remains (the next drip-level recursion, or the bulk-top, or fully closed).

## BUILD ROUTING
Iterate with `nice -n 15 env LEAN_NUM_THREADS=2 ~/.elan/bin/lake env lean <file>` (single-file, allowed locally).
Full module build: `~/.openclaw/workspace/scripts/remote-build.sh Ripple` (uisai1) OR ONE local
`lake build ...ClockBulkFront` ONLY after `memory_pressure` shows >50% free, run ALONE. No concurrent builds.
Working dir: cd /Users/huangx/.openclaw/workspace/projects/Ripple

## HARD RULES (绝对不退缩, 不 over-claim)
NEW file ClockBulkFront.lean only (may edit ClockCapRecur.lean to rewire — sole writer); do NOT weaken proven
lemmas; do NOT touch other files. The absorbing-up-to-drip step + the concentration MUST be genuinely proven,
NEVER assumed. The KEY realization: empty-feeder ⟹ sync term vanishes (no sync target) ⟹ drip-only ⟹ squares —
this is what makes the empty-seed squaring actually sufficient (the sync obstruction only bites at occupied
levels, which the drip-squared concentration shows are whp-unreached at the top). If this realization is WRONG
(sync can occupy an empty cap−2 some other way), STOP and report exactly how. Do NOT add a 10th false hyp. No
sorry/admit/new axiom/native_decide. Verify #print axioms (lake env temp importer, delete): [propext,
Classical.choice, Quot.sound]. Do NOT git. Final message: the absorbing-up-to-drip step (proven?), the
concentration (discharges CapRelWithinEnvFeeder to what residual?), whether the clock now carries fewer/no
structural assumptions, build verdict, #print axioms, HONEST status.
