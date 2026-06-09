# Doty time-half — SYNC FIX: bulk uses SYNC (susceptible via clockSize), 0.9-floor, no full crossing

Directive: 挨个做，绝对不退缩，不 over-claim. The prior floor-fix attempt correctly STOPPED: it found the bulk
advance uses the DRIP frontier (clocks at minute exactly T = `rBeyond T − rBeyond(T+1)`, which equals `mC − m`
ONLY under full crossing `rBeyond T = mC`). So full crossing was genuinely needed by the BULK rate, not just the
floor field. THE REAL FIX (verified sound): the bulk must use the SYNC mechanism, where the susceptible count is
`mC − rBeyond(T+1)` from `clockSize` (clockCount = mC) — NO full crossing. The seed stays DRIP. This is exactly
C3's seed=drip + epidemic=SYNC split; the current (a') wrongly made the bulk a drip.

## The math (verified — both seed and bulk work on the 0.9-floor, neither needs full crossing)
- **BULK (sync), window `rBeyond(T+1) = m ∈ [0.1mC, 0.9mC]`:** infected = clocks at minute ≥ T+1 (count `m`);
  susceptible = clocks at minute ≤ T (count `mC − m`, from `clockSize` + `rBeyond_le_clockCount`, NO crossing).
  An infected meets a susceptible → sync pulls susceptible up to ≥ T+1 → rBeyond(T+1)++ (`rEpidemic_pair_advances`).
  Rectangle = `m·(mC − m) ≥ 0.1mC · 0.1mC = 0.01mC²` (pure arithmetic on the window). Advance prob ≥
  `0.01mC²/(n(n−1)) = Θ(c²)`. NO full crossing.
- **SEED (drip), window `rBeyond(T+1) = m ∈ [0, 0.1mC]`:** frontier = clocks at minute exactly T =
  `rBeyond T − rBeyond(T+1) ≥ 0.9mC − 0.1mC = 0.8mC` (using the 0.9-floor `rBeyond T ≥ 0.9mC`, NOT full).
  Drip among them advances. Rectangle ≥ `0.8mC·(0.8mC−1)`. NO full crossing.

## The change (6 files, dependency order; sole writer)
1. `ClockRealMixed.lean`: `Q_mix.crossedT : rBeyond T c = mC` → `9*mC/10 ≤ rBeyond T c`; `Q_mix.clockPhase3`:
   DROP the `T ≤ a.minute.val` pointwise clause (keep `a.role = .clock → a.phase.val = 3`). The total/susceptible
   counts now come from `clockSize` + `rBeyond_le_clockCount`. Fix the c² rectangle: provide a SYNC variant —
   susceptible = `mC − rBeyond(T+1)` (minute ≤ T, via clockSize), advancing by `rEpidemic_pair_advances`
   (infected at minute ≥ T+1 exists since m ≥ 0.1mC in bulk). Keep the drip variant for the seed.
2. `ClockMonoDischarge.lean`: rebuild (uses clockPhase3's phase part + role permanence — should survive;
   if it used the minute clause, re-derive minute-nondecrease from the per-pair lemmas which are floor-agnostic).
3. `ClockRealBulk.lean`: `clock_real_advance_bulk` — switch to the SYNC rectangle (susceptible mC−m via
   clockSize); `bulk_frontier_floor` (mC−m ≥ 0.1mC for m<0.9mC) is pure arithmetic, keep. Drop any `rBeyond T=mC`
   use.
4. `ClockRealSeed.lean`: `clock_real_advance_seed` — DRIP, frontier `rBeyond T − rBeyond(T+1) ≥ 0.8mC` from the
   0.9-floor; `clock_real_step` = seed ++ bulk.
5. `ClockRealHours.lean`: `Q_mix_succ_of_post` now needs only `0.9mC ≤ rBeyond(T+1)` (= bulk Post) for the next
   crossedT — definitional/easy. No full crossing.
6. `ClockRealFaithfulHours.lean`: DELETE `hcross_full_all`; chaining from the 0.9 Post; carry ONLY `habs_mix_all`.

## HARD RULES (automode, 绝对不退缩, 不 over-claim)
Edit ONLY the six ClockReal*/ClockMono* files (sole writer). Do NOT touch other files; do NOT weaken the
floor-agnostic per-pair lemmas (Transition_clock_pair, rEpidemic_pair_advances, rDrip*). No
sorry/admit/new axiom/native_decide. The bulk MUST use SYNC with susceptible from clockSize (no full crossing);
the seed MUST use the 0.9-floor frontier (no full crossing). GOAL: whole chain builds, `clock_real_faithful_O_log_n`
carries ONLY `habs_mix_all` (NO hcross_full_all, NO full-crossing requirement anywhere), 0-sorry, axioms clean.
Build each file in order; final `lake build ...ClockRealFaithfulHours`. Do NOT git. If the SYNC rectribute
genuinely cannot be built (e.g. rEpidemic_pair_advances can't be summed over the susceptible set), report the
EXACT spot — do NOT fall back to drip+full-crossing. Final message: new Q_mix.crossedT + clockPhase3, the SYNC
bulk rectangle lemma, updated clock_real_faithful_O_log_n signature (ONLY habs_mix_all), per-file build verdicts,
#print axioms (must be [propext, Classical.choice, Quot.sound]), HONEST status: hcross_full eliminated? full
crossing gone everywhere? only habs_mix carried? If rate-limited, report which files compile on disk.
