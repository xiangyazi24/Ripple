# Doty time-half — CAP-RELATIVE front-shape (fix the mis-index) → bound the cap-1 feeder → FrontSync whp

Directive: 挨个做，绝对不退缩，不 over-claim. The front-width concentration was MIS-INDEXED (FrontAllLevels
tracked the absolute-low `frontWidthBound = O(log log n)` from the bottom = the START regime, false for the
advancing clock). FIX: formulate the front-shape CAP-RELATIVE — the top `frontWidthBound = O(log log n)` levels
(`cap − frontWidthBound .. cap`) are doubly-exp narrow, so the cap-1 feeder is tiny, so the FrontSync breach
(`real_front_advance_squares_cap`: breach ≤ (cap-1 feeder/n)²) is `1/poly`.

## The correct cap-relative structure
- FrontSync breaks when a clock reaches `cap`. PROVEN bound (`ClockFrontShape.real_front_advance_squares_cap`):
  breach ≤ `(frontMinuteCount(cap-1) c / card)²`. So we need the **cap-1 feeder** `frontMinuteCount(cap-1)` (or
  `rBeyond(cap-1)`) to be small.
- The per-level squaring `rBeyond_seed_le_rBeyondSq`: seeding level `j+1` from empty ≤ `(rBeyond j / n)²`. Iterate
  UPWARD toward the cap: `rBeyond(cap-1) ≤ (rBeyond(cap-2)/n)²·n ≤ … ≤ n·(rBeyond(cap-W)/n)^(2^(W-1))` where
  `W = frontWidthBound n`. With `W = O(log log n)` and the **bulk-top fraction** `ρ := rBeyond(cap-W)/n` bounded
  `≤ ρ₀ < 1`, this is `≤ n·ρ₀^(2^(W-1)) < 1` ⟹ `rBeyond(cap-1) = 0` (empty feeder) ⟹ breach 0 ⟹ FrontSync.
- So the cap-1 feeder is doubly-exp small GIVEN the bulk-top fraction `ρ ≤ ρ₀ < 1` — the front near the cap is
  narrow because each level squares down from the bulk-top. The residual is the **bulk-top fraction bound**
  `rBeyond(cap - frontWidthBound) ≤ ρ₀·n` (true while the clock runs — the bulk has not all reached within
  `O(log log n)` of the cap), NOT the false absolute-low `rBeyond(frontWidthBound)=0`.

## Task (NEW file Probability/ClockCapRelFront.lean only)
1. `capRel_feeder_doubly_exp`: from the bulk-top fraction bound `rBeyond(cap - W) c ≤ ρ₀·n` (ρ₀ a fixed constant
   `<1`) + `AllClockP3`, iterate `rBeyond_seed_le_rBeyondSq` UPWARD over the `W = frontWidthBound n` levels
   `cap-W .. cap` to get `rBeyond(cap-1) c = 0` (the cap-1 feeder empty), via the doubly-exp envelope collapse
   (`env i = ρ₀^(2^i)`, `front_shape_collapse`'s `env W < 1/n`). GENUINE iteration, not assumed.
2. `capRel_frontSync_concentration`: feed the empty cap-1 feeder into the breach bound
   (`real_front_advance_squares_cap` ⟹ breach 0 when feeder empty) + the horizon union → FrontSync holds whp,
   bounding the breach by the CAP-RELATIVE quantity (the bulk-top fraction), NOT the absolute-low level.
3. Discharge `ClockFrontShape.FrontSyncConcentration_remaining` (or wire to the clock) carrying ONLY the
   cap-relative bulk-top fraction bound `hbulktop : rBeyond(cap - frontWidthBound) ≤ ρ₀·n` (honestly named — TRUE
   while the clock runs; it is the genuine bulk condition, NOT the false start-regime hyp). Report whether the
   clock FrontSync whp now rests on this cap-relative bulk condition (correct) instead of the mis-indexed one.

## HARD RULES (automode, 绝对不退缩, 不 over-claim)
NEW file ClockCapRelFront.lean only; do NOT edit existing files (the mis-indexed FrontAllLevels stays as-is,
superseded — note it in a doc comment in your new file, do not delete). The upward squaring iteration MUST be
genuinely proven (iterate the PROVEN rBeyond_seed_le_rBeyondSq + the doubly-exp envelope), NEVER assumed. The
carried residual MUST be the CAP-RELATIVE bulk-top fraction (TRUE while running), NOT the false absolute-low
level — do NOT re-introduce the mis-index, do NOT add a 10th false hyp. No sorry/admit/new axiom/native_decide.
If the upward iteration needs a per-level bound the empty-seed squaring doesn't give (the m→m+1 issue resurfacing
at the top levels), prove the maximal clean prefix and STOP at the EXACT residual. Iterate `lake build
Ripple.PopulationProtocol.Majority.ExactMajority.Probability.ClockCapRelFront` until clean. Do NOT git. Final
message: the cap-relative feeder bound (genuinely iterated?), the FrontSync concentration (now cap-relative?),
the carried residual (the true bulk-top fraction, or a smaller named piece), build verdict, #print axioms (must
be [propext, Classical.choice, Quot.sound]), HONEST status: is the front-shape now CORRECTLY formulated
(cap-relative) and does FrontSync-whp rest on the true bulk condition? If rate-limited, report on-disk WIP.
