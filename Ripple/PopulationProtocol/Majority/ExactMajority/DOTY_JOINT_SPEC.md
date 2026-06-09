# Doty time-half — the JOINT clock-front induction (cap-relative; ANTI-REGRESSION) → close the clock

Directive: 闷头跑，绝对不退缩，不 over-claim (Xiang fully delegated). The clock is reduced to the joint
clock-front induction. TWO prior agents REGRESSED to the mis-indexed ABSOLUTE-LOW formulation (FrontAllLevels:
rBeyond(frontWidthBound) with frontWidthBound=O(log log n) FROM THE BOTTOM = "all clocks below minute
O(log log n)" = the START regime, FALSE for the advancing clock). DO NOT regress. Build the joint induction
CAP-RELATIVE, around the MOVING leading edge.

## ⛔ ANTI-REGRESSION (read first)
- Do NOT import or use `FrontAllLevels.lean` or its `rBeyond (frontWidthBound n)` absolute-low collapse, or
  `JointClockFront` from ClockFrontIter (both are the mis-indexed absolute-low form).
- The clock ADVANCES: clocks move from minute 0 toward `capMinute = K(L+1)`. So `rBeyond(T)` for any FIXED low T
  grows to ≈mC as the clock runs — a "fixed low level stays empty" statement is FALSE. The front-shape is about
  the MOVING leading edge (the max occupied minute), NOT a fixed absolute level.

## The correct (cap-relative) joint structure
- Leading edge `LE(c)` = max occupied clock minute. FrontSync = LE < capMinute (no clock at the cap).
- Front-narrow (cap-relative): above LE is empty (by def); the front squares DOWN from LE — creating a new minute
  above the current LE needs a same-minute DRIP at LE (prob ≤ (count at LE / n)²), so LE advances by ≤1 per step
  with drip-squared prob. This is the PROVEN empty-absorbing (`ClockBulkFront.feeder_empty_absorbing_up_to_drip`
  / `seed_pair_real`: above an empty level, sync can't seed it, drip-only, squares) — applied at the LEADING
  EDGE (which IS empty above), NOT a fixed absolute level.
- Clock advance: `clock_real_step` brings the bulk up (epidemic 0.1→0.9 per minute), advancing the bulk leading
  edge through O(log n) minutes in O(log n) parallel (`clock_real_faithful_O_log_n`).
- JOINT INVARIANT J(c): (a) the clock/bulk structure (Q_mix-style, the bulk crossing minutes) ∧ (b) FrontSync
  (LE < cap) ∧ (c) front-narrow (the front above the bulk is O(log log n) wide / the leading edge is within
  O(log log n) of the bulk top). Maintain J one step: (b) from (c) via empty-absorbing at LE; the bulk advances
  via clock_real_step; (c) maintained because LE advances only by drip-squared (slow) while the bulk advances by
  epidemic — so the gap LE − bulktop stays O(log log n).

## Task (NEW file Probability/ClockJointInduction.lean only)
1. Define the joint invariant J cap-relatively (around the leading edge / bulk top, NOT a fixed absolute level).
2. Prove one-step maintenance of J (combine clock_real_step + the cap-relative empty-absorbing at LE + the
   gap-stays-O(log log n) drip-vs-epidemic argument). GENUINE, no false/absolute-low hyp.
3. Iterate over the O(log n) horizon → FrontSync holds whp throughout the clock's run until completion →
   `clock_real_O_log_n_joint_closed`: the real-kernel O(log n) clock UNCONDITIONAL whp (NO structural hyp beyond
   the Phase-3 start + ε/t). OR, if the joint maintenance genuinely needs a piece not yet built, prove the
   maximal clean prefix and STOP at the EXACT cap-relative residual (NOT an absolute-low one).

## BUILD ROUTING
`nice -n 15 env LEAN_NUM_THREADS=2 ~/.elan/bin/lake env lean <file>` (single-file). Full: `scripts/remote-build.sh
Ripple` (uisai1) OR ONE local lake-build ALONE after memory_pressure >50% free. No concurrent builds.
cd ~/.openclaw/workspace/projects/Ripple

## HARD RULES (绝对不退缩, 不 over-claim)
NEW file ClockJointInduction.lean only; do NOT weaken proven lemmas; do NOT touch other files. The joint
maintenance MUST be genuinely proven, NEVER assumed. ⛔ Do NOT regress to the absolute-low formulation (no
FrontAllLevels, no fixed-low rBeyond(frontWidthBound) "stays empty"). Do NOT add a false hyp (9+ caught; 0 more).
If the joint induction genuinely needs the bulk advance ⟷ front narrow mutual piece you can't yet prove,
STOP and name the EXACT cap-relative residual. No sorry/admit/new axiom/native_decide. Verify #print axioms
(lake env temp importer, delete): [propext, Classical.choice, Quot.sound]. Do NOT git. Final message: the joint
invariant (cap-relative, around the moving LE — NOT absolute-low?); one-step maintenance (genuine?); whether the
clock is NOW unconditional whp (theorem VERBATIM, NO structural hyp) OR the exact cap-relative residual; build
verdict; #print axioms; HONEST status. Confirm explicitly you did NOT use the absolute-low FrontAllLevels form.
