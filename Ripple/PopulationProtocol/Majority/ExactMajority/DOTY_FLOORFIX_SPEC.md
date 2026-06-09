# Doty time-half — FLOOR FIX: Q_mix.crossedT full→0.9, eliminate the FALSE hcross_full_all

Directive: 挨个做，绝对不退缩，不 over-claim. The clock chain (a')/(a'')/(d') rests on `Q_mix.crossedT =
(rBeyond T c = mC)` (FULL crossing), an artifact of the c=1 all-clocks origin. This forces (d') to carry
`hcross_full_all` which is FALSE (0.9-crossing does not imply full). FIX: weaken the floor to 0.9, matching C5's
faithful clock. After the fix the chain is O(log n) carrying ONLY `habs_mix` (window closure), no false hyp.

## The change
In `Probability/ClockRealMixed.lean`, the `Q_mix` structure field `crossedT : rBeyond T c = mC` becomes
`crossedT : 9 * mC / 10 ≤ rBeyond T c` (the 0.9 floor; inline `9*mC/10` since `bulkHi` lives downstream in
ClockRealBulk). KEEP `clockSize : clockCount c = mC` (it supplies the TOTAL clock count for susceptible/frontier
counts — this is what replaces the full-crossing floor in the counting).

## Propagate (edit the dependent files; you are sole writer of all of them this run)
For each downstream use of `crossedT` (the old `rBeyond T = mC`):
- Susceptible/total counts: replace reliance on `rBeyond T = mC` with `clockSize` (`clockCount c = mC`) +
  `rBeyond (T+1) c ≤ clockCount c` (rBeyond_le_clockCount). Susceptible-for-sync = `mC − rBeyond(T+1)` comes
  from clockSize, NOT from crossedT. Frontier-for-drip (minute exactly T) = `rBeyond T − rBeyond(T+1)`; on the
  seed window use the 0.9 floor `rBeyond T ≥ 0.9mC` ⟹ frontier ≥ 0.9mC − rBeyond(T+1) ≥ 0.8mC. The frontier
  floors (`bulk_frontier_floor`, `seed_frontier_floor`) should still go through (re-derive counts from
  clockSize + 0.9-floor as needed).
- Chaining (the payoff): `ClockRealHours.Q_mix_succ_of_post` and `ClockRealFaithfulHours` chaining now need
  only `0.9mC ≤ rBeyond(T+1)` (= bulk Post) to establish `Q_mix(T+1).crossedT` (= `0.9mC ≤ rBeyond(T+1)`) —
  DEFINITIONAL/`rfl`-level. DELETE `hcross_full_all` from `clock_real_faithful_all_minutes` /
  `clock_real_faithful_O_log_n`. The result then carries only `habs_mix_all`.

## Files to touch (in dependency order; rebuild each before the next)
1. `ClockRealMixed.lean` — change crossedT; fix its own proofs (sum_interactionCount_mixedRect, the prob lemma,
   rSeedPot_contracts_mixed, clock_real_advance_mixed, Q_mix_succ_of_post if here) to use clockSize.
2. `ClockMonoDischarge.lean` — likely unaffected (uses clockPhase3, not crossedT) — just rebuild to confirm.
3. `ClockRealBulk.lean` — clock_real_advance_bulk; bulk_frontier_floor counts from clockSize + window.
4. `ClockRealSeed.lean` — clock_real_advance_seed (seed frontier from 0.9-floor), clock_real_step.
5. `ClockRealHours.lean` — Q_mix_succ_of_post becomes definitional/rfl-level (only 0.9 needed).
6. `ClockRealFaithfulHours.lean` — DELETE hcross_full_all; chaining definitional; carry only habs_mix_all.

## HARD RULES (automode, 绝对不退缩, 不 over-claim)
Edit ONLY the six ClockReal*/ClockMono* files above (you are sole writer). Do NOT touch any OTHER file (not
PhaseConvergence, not Transition, not Audit, not C3/C5 files). Do NOT weaken the per-pair lemmas (they are
floor-agnostic — reuse verbatim). No sorry/admit/new axiom/native_decide. The goal: the whole chain builds,
`clock_real_faithful_O_log_n` carries ONLY `habs_mix_all` (no hcross_full_all, no false hyp), 0-sorry, axioms
clean. Build each file with `lake build <module>` in dependency order; final `lake build
...Probability.ClockRealFaithfulHours`. Do NOT git. If a count genuinely cannot be re-derived from clockSize +
0.9-floor (i.e., something truly needed full crossing), STOP and report the exact spot — do NOT re-introduce a
false hyp. Final message: the new Q_mix.crossedT, the updated clock_real_faithful_O_log_n signature (showing
ONLY habs_mix_all carried), per-file build verdicts, #print axioms (must be [propext, Classical.choice,
Quot.sound]), HONEST status: hcross_full_all eliminated? only habs_mix carried now? any count that still needs
full crossing? Be precise. If rate-limited, report which files compile on disk.
