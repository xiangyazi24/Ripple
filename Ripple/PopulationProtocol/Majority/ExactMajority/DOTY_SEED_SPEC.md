# Doty time-half — Avenue (a''): real-kernel SEED crossing 0→0.1mC (drip), completing per-minute clock_step

Directive: 挨个做，绝对不退缩，不 over-claim. (a') built the EPIDEMIC half (sync, 0.1mC→0.9mC). The per-minute
clock step (= C3 `clock_step_upper` = seedPhase + epidemicPhase) needs the SEED half: drip grows the next level
from 0 to 0.1mC. (a'') builds it, then clock_step = seed ++ epidemic.

## The target (drip seed, where the drip product floor is genuinely true)
Level being seeded = `S` (e.g. S = T+2 when chaining; abstractly just "the next level"). Pre: the floor with
`mC/10 ≤ rBeyond S` already... NO — seed goes FROM 0: Pre = floor with the PRIOR level crossed so that ≥0.9mC
clocks sit at minute ≥ S−1 (the drip source), and `rBeyond S` starts at 0; Post: `mC/10 ≤ rBeyond S` (0.1mC
seeded). Mechanism: two clocks at the SAME minute (S−1) drip → one advances to ≥ S (`rDrip_pair_advances` /
`rDripDistinct_pair_advances` in ClockRealAdvance.lean — drip fires on EQUAL minute, distinct states OK).
- While `rBeyond S < mC/10`, the count of clocks at minute exactly S−1 is `rBeyond (S−1) − rBeyond S ≥ 0.9mC −
  0.1mC = 0.8mC` (using the floor `rBeyond (S−1) ≥ 0.9mC`). So drip pairs ≥ ~0.8mC·(0.8mC−1), advance prob
  ≥ Θ((mC/n)²) = Θ(c²), GENUINELY UNIFORM on the seed window [0, 0.1mC] — PROVE this product floor (it is
  genuinely true here, even easier than (a')'s).

## Task (NEW file Probability/ClockRealSeed.lean + the per-minute composition)
1. `clock_real_advance_seed` : PhaseConvergence (NonuniformMajority L K).transitionKernel, Pre = floor ∧
   `9*mC/10 ≤ rBeyond (S−1)` (prior level crossed, drip source present), Post = `mC/10 ≤ rBeyond S` (0.1mC
   seeded), via windowDrift with the DRIP advance prob + the proven seed product floor. Mirror (a')
   `clock_real_advance_bulk` exactly but: mechanism = drip (rDrip*), window = [0, mC/10], source-count floor
   `rBeyond(S−1) − rBeyond S ≥ 0.8mC`. Reuse hmono_mix_discharged, clock_real_advance_prob_mixed/the drip
   counting, the proven product-floor pattern from ClockRealBulk.lean.
2. `clock_real_step` : compose `clock_real_advance_seed ++ clock_real_advance_bulk` (compose_two_phases) into
   one per-minute phase: Pre = level S−1 crossed (9mC/10 beyond S−1), Post = level S bulk-crossed (9mC/10 beyond
   S). Chaining seed.Post (0.1mC beyond S) → bulk.Pre (0.1mC beyond S) is DEFINITIONAL/genuine. t = tseed +
   tbulk = O(n/c²) interactions = O(1) parallel; ε = εseed + εbulk = exp(−Θ(mC)). THIS is the faithful per-minute
   O(1) clock step (the real-kernel analog of C3 clock_step_upper), replacing the full-crossing (a).

## HARD RULES (automode, 绝对不退缩, 不 over-claim)
NEW file ClockRealSeed.lean only; do NOT edit existing files, do NOT weaken proven lemmas. No
sorry/admit/new axiom/native_decide. The seed product floor (source count ≥ 0.8mC on [0,0.1mC]) MUST be PROVEN
(genuinely true), NOT assumed. clock_real_step's chaining must be genuine. Only carry habs_mix (window closure)
— same single deterministic hyp as (a'); nothing new false. Iterate `lake build
Ripple.PopulationProtocol.Majority.ExactMajority.Probability.ClockRealSeed` until clean. Do NOT git. Final
message: clock_real_advance_seed + clock_real_step signatures verbatim, the proven seed product-floor lemma,
build verdict, #print axioms (must be [propext, Classical.choice, Quot.sound]), HONEST status: seed floor proven
(not assumed)? clock_real_step is the genuine O(1)/minute faithful step? what's carried (should be only
habs_mix)? Do not over-claim. If rate-limited, report on-disk WIP.
