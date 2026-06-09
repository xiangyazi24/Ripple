# Doty time-half — FULL lock-step joint induction (break the circularity) → close the clock

Directive: 闷头跑，绝对不退缩，不 over-claim (Xiang fully delegated). CONFIRMED: sequential reduction CYCLES
(FrontSync ← S-small ← bulk-position ← clock-advance ← habs ← FrontSync). The ONLY resolution is a FULL
lock-step joint invariant maintaining ALL of {FrontSync, bulk-advance, S-small} TOGETHER, each step using the
others. ClockJointInduction's J = Q_mix ∧ noPhaseAbove3 ∧ allClocksCounterPos ∧ FrontSync maintained FrontSync
GIVEN S-small (carried hfeeder_all). EXTEND J with S-small and maintain it lock-step from J's own components.

## The lock-step invariant (extend ClockJointInduction.J)
`Jfull(c) := J(c) ∧ Ssmall(c)` where `Ssmall(c) := gapFrac W c ≤ ρ₀` (band count cap−W..cap subcritical ≡
CapRelWithinEnvelope / bulk leading edge below cap−W). One-step maintenance of Jfull (the crux — all from Jfull's
OWN components, NO external assumption):
- FrontSync maintained: from Ssmall (band sparse ⟹ empty leading-edge feeder ⟹ drip-squared breach 0), the PROVEN
  ClockBulkFront/capRel empty-absorbing. (Already in ClockJointInduction given hfeeder_all — now hfeeder_all comes
  from Ssmall ∈ Jfull.)
- bulk advances: clock_real_step, given FrontSync ∈ Jfull (habs_mix_full).
- Ssmall maintained: the band count gapFrac W increments via (a) drip into the band ≤ drip-squared (front-shape,
  from Ssmall's own front-narrowness), and (b) the bulk reaching cap−W — but bulk-position ∈ Jfull keeps the bulk
  below cap−W for the bounded horizon (clock_real_step advances ≤1 min/block, < cap−W blocks). So Ssmall stays
  ≤ ρ₀ each step. THIS is the piece that was carried — now maintained from Jfull's bulk-position + front-shape.

## Task (NEW file Probability/ClockLockstep.lean only; may edit ClockJointInduction.lean to extend J — sole writer)
1. `Jfull` (J ∧ Ssmall, cap-relative — Ssmall via gapFrac W / the band count, MOVING leading edge, NOT
   absolute-low).
2. `lockstep_step_maintains`: one step preserves Jfull, with Ssmall maintained from the bulk-position
   (clock_real_step ≤1 min/block) + the drip-squared band-feed (empty-absorbing) — both already proven; combine
   them so Ssmall closes WITHOUT the external hfeeder_all. GENUINE, no carried S-small assumption.
3. Iterate over the K(L+1) horizon → FrontSync ∧ bulk-Post hold whp throughout → `clock_real_O_log_n_unconditional`:
   the real-kernel O(log n) clock UNCONDITIONAL whp (NO structural hyp beyond Phase-3 start + ε/t). OR, if Ssmall
   maintenance genuinely needs a piece not yet built (the band-feed drip-squared vs the horizon), prove the
   maximal clean prefix and STOP at the EXACT cap-relative residual.

## ⛔ ANTI-REGRESSION + BUILD
NO FrontAllLevels/ClockFrontIter (absolute-low). Ssmall is the cap-relative band count (gapFrac W / bulk LE below
cap−W), MOVING leading edge. Build: `lake env lean <file>` single-file local; full build `scripts/remote-build.sh
Ripple` (uisai1) OR ONE local lake-build ALONE after memory_pressure >50% free. No concurrent. cd
~/.openclaw/workspace/projects/Ripple

## HARD RULES (绝对不退缩, 不 over-claim)
NEW file ClockLockstep.lean only (may edit ClockJointInduction.lean to extend J). The Ssmall maintenance MUST be
genuinely proven from Jfull's bulk-position + the empty-absorbing — NEVER assumed/carried. Do NOT add a false hyp
(9+ caught; 0 more). NO absolute-low regression. If the lock-step genuinely can't close Ssmall (the band-feed
needs the m→m+1 sync count that isn't bounded), prove the maximal prefix and name the EXACT residual. No
sorry/admit/new axiom/native_decide. #print axioms (lake env temp importer, delete): [propext, Classical.choice,
Quot.sound]. Do NOT git. Final message: Jfull + lockstep_step_maintains (Ssmall maintained from components, not
carried?); whether the clock is NOW unconditional whp (theorem VERBATIM, NO structural hyp) OR the exact
cap-relative residual; build verdict; #print axioms; HONEST status; confirm NO absolute-low regression.
