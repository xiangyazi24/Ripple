# Doty time-half — close the mutual induction: gap-bound + bulk-position → FrontSync for the run

Directive: 闷头跑，绝对不退缩，不 over-claim (Xiang fully delegated). The joint induction
(ClockJointInduction.clock_real_O_log_n_joint_closed) maintains FrontSync GIVEN the bulk-top narrowness. The
remaining is the bulk-top narrowness itself, ≡ "front leading edge LE < cap throughout the run". Close it from
the clock's OWN advance: (a) the front stays only O(log log n) AHEAD of the bulk (gap-bound, from the proven
empty-absorbing: the front advances by DRIP-squared = RARE, slower than the bulk's EPIDEMIC); (b) the bulk
leading edge ≤ minutes-crossed (from the composition clock_real_faithful_O_log_n). Together: LE ≤ bulkLE + W <
cap while bulkLE < cap−W, which holds for the whole O(log n) run until completion.

## ⛔ ANTI-REGRESSION (read first)
Do NOT import/use FrontAllLevels.lean or ClockFrontIter.lean (absolute-low). Use the cap-relative
ClockJointInduction / ClockCapRelFront / ClockBulkFront. The front is the MOVING leading edge; "front empty above
LE" is by definition of LE, NOT "rBeyond(frontWidthBound)=0 from the bottom".

## The structure
- Gap-bound (front-shape): `LE(c) − bulkLE(c) ≤ W = frontWidthBound n = O(log log n)`, where LE = max occupied
  clock minute, bulkLE = the 0.9-bulk top minute. From the empty-absorbing (ClockBulkFront / capRel_feeder_
  doubly_exp): levels more than W above the bulk are empty whp (the front squares down). So LE ≤ bulkLE + W.
- Bulk-position: bulkLE advances by ≤1 per minute-step; after the composition over m minutes
  (clock_real_faithful_O_log_n / clock_real_step composed), bulkLE ≈ m (the bulk crosses one minute per
  seed+epidemic block). So bulkLE < cap − W for m < cap − W = the first O(log n) minutes.
- Therefore LE ≤ bulkLE + W < cap ⟹ FrontSync holds throughout the run (until the final O(log log n) minutes =
  completion, where LE reaches cap = the clock done). Discharge the bulk-top narrowness from these two PROVEN
  ingredients, closing the joint induction.

## Task (NEW file Probability/ClockGapBulk.lean only)
1. `gap_bound`: `LE ≤ bulkLE + W` whp (from the empty-absorbing front-shape). Reuse capRel_feeder_doubly_exp /
   ClockBulkFront. Cap-relative.
2. `bulk_position_bound`: bulkLE ≤ (minutes crossed) from the per-minute composition (clock_real_faithful_O_log_n
   establishes the bulk crosses minute m after the m-th block; bulkLE ≤ m).
3. `frontSync_of_gap_and_position`: combine → FrontSync (LE < cap) for the run (bulkLE + W < cap). Discharge the
   bulk-top narrowness `capRelFrac W ≤ ρ₀` (≡ bulkLE < cap−W).
4. `clock_real_O_log_n_closed`: feed into clock_real_O_log_n_joint_closed → the real-kernel O(log n) clock
   UNCONDITIONAL whp (NO structural hyp beyond Phase-3 start + ε/t budget). OR, if the gap/position connection
   genuinely needs a piece not yet built, prove the maximal clean prefix and STOP at the EXACT cap-relative
   residual.

## BUILD ROUTING
`nice -n 15 env LEAN_NUM_THREADS=2 ~/.elan/bin/lake env lean <file>` (single-file). Full: `scripts/remote-build.sh
Ripple` (uisai1) OR ONE local lake-build ALONE after memory_pressure >50% free. No concurrent builds.
cd ~/.openclaw/workspace/projects/Ripple

## HARD RULES (绝对不退缩, 不 over-claim)
NEW file ClockGapBulk.lean only; do NOT weaken proven lemmas; do NOT touch other files. ⛔ NO absolute-low
regression (no FrontAllLevels; LE is the moving leading edge). The gap-bound + position MUST be genuinely proven
(from the empty-absorbing + the composition), NEVER assumed. Do NOT add a false hyp (9+ caught; 0 more). If the
mutual connection genuinely can't close (the bulk-position needs FrontSync circularly), prove the maximal clean
prefix and name the EXACT residual. No sorry/admit/new axiom/native_decide. Verify #print axioms (lake env temp
importer, delete): [propext, Classical.choice, Quot.sound]. Do NOT git. Final message: gap_bound + position
(genuine?); whether the clock is NOW unconditional whp (theorem VERBATIM, NO structural hyp) OR the exact
cap-relative residual; build verdict; #print axioms; HONEST status; confirm NO absolute-low regression.
