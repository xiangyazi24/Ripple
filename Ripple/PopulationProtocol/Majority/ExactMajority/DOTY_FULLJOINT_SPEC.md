# Doty time-half — COMPLETE coupled lock-step: maintain Ssmall_occupied from front-shape ∈ J → close the clock

Directive: 闷头跑，绝对不退缩，不 over-claim (Xiang fully delegated). Exhaustive analysis (drip-squaring,
sync-multiplicative, branching) confirms: the irreducible core is the COMPLETE coupled lock-step. ClockLockstep
maintained the EMPTY band + FrontSync + bulk-position, but CARRIED CapRelRecurrence (occupied-band Ssmall) and
the front-shape laggards. The CLOSE: maintain Ssmall_occupied (band ≤ ρ₀) FROM the front-shape laggards-few,
which is ITSELF maintained in the joint — so all four conjuncts (FrontSync ∧ bulk-position ∧ front-shape ∧
Ssmall) close together, NO carried CapRelRecurrence.

## The complete invariant Jall
`Jall(c) := FrontSync c ∧ BulkPos c ∧ FrontShape c ∧ Ssmall c` where:
- `FrontSync c` = no clock at capMinute (moving leading edge < cap).
- `BulkPos c` = the bulk leading edge below cap−W (the bulk Post position, PROVEN advancing via clock_real_step).
- `FrontShape c` = laggards few at EACH front level: ∀ j ∈ [bulktop, cap), rBeyond(j) c ≤ ⌊n·envelope(j−bulktop)⌋
  (the doubly-exp front mass per level — the empty-absorbing/squaring maintains this).
- `Ssmall c` = band count gapFrac W c ≤ ρ₀ (the OCCUPIED band, ≤ ρ₀, not just empty).

One-step maintenance of Jall (the crux — Ssmall_occupied from FrontShape ∈ Jall, NOT carried):
- FrontSync ← Ssmall/FrontShape (empty-ish feeder squares the breach), PROVEN empty-absorbing.
- BulkPos: bulk advances ≤1 min/block (clock_real_step given FrontSync ∈ Jall), stays below cap−W for the horizon.
- FrontShape maintained: each front level's mass ≤ envelope, via the per-level empty-absorbing/squaring (the feed
  into level j ≤ (mass at j−1)², the doubly-exp, given FrontShape ∈ Jall one level down — the level-uniform
  recursion bottoms at the bulktop where BulkPos bounds it).
- **Ssmall_occupied maintained (THE CLOSE):** band count increments via drip (≤ laggards², laggards = front mass
  at cap−W−1 ≤ envelope ∈ FrontShape) + sync (∝ laggards·band, laggards few ∈ FrontShape). Both ∝ the FEW
  laggards (FrontShape ∈ Jall). So the band grows slowly (immigration laggards² + multiplication laggards·band,
  both tiny), bounded ≤ ρ₀ over the horizon via a multiplicative/Gronwall bound (azuma_tail / geometric_drift on
  exp(s·band) with the laggards-bounded drift). This MAINTAINS Ssmall from FrontShape ∈ Jall — NOT carried as
  CapRelRecurrence.

## Task (NEW file Probability/ClockFullJoint.lean only; may edit ClockLockstep.lean / ClockJointInduction.lean to extend J — sole writer)
1. `Jall` (the four-conjunct complete invariant, cap-relative, moving leading edge).
2. `fulljoint_step_maintains`: one step preserves Jall, with Ssmall_occupied maintained from FrontShape's
   laggards-few (the sync+drip feed bound) — NOT carried. The FrontShape maintained by the level-uniform
   empty-absorbing recursion bottoming at BulkPos. Combine the PROVEN pieces (clock_real_step, empty-absorbing,
   gap-bound, bulk-position, azuma_tail) so all four close.
3. Iterate over the K(L+1) horizon → `clock_real_O_log_n_FINAL`: real-kernel O(log n) clock UNCONDITIONAL whp,
   NO structural hyp beyond Phase-3 start + ε/t. OR, if Ssmall_occupied genuinely can't be maintained from
   FrontShape (the sync multiplicative bound needs a piece not in azuma_tail), prove the maximal clean prefix and
   STOP at the EXACT residual.

## ⛔ ANTI-REGRESSION + BUILD
NO FrontAllLevels/ClockFrontIter (absolute-low). All quantities cap-relative (moving leading edge / band /
bulktop). Build: `lake env lean <file>` single-file; full `scripts/remote-build.sh Ripple` (uisai1) OR ONE local
lake-build ALONE after memory_pressure >50%. No concurrent. cd ~/.openclaw/workspace/projects/Ripple

## HARD RULES (绝对不退缩, 不 over-claim)
NEW file ClockFullJoint.lean (may edit ClockLockstep/ClockJointInduction to extend J). Ssmall_occupied MUST be
maintained from FrontShape's laggards-few (sync+drip feed via azuma_tail/Gronwall), NEVER carried as
CapRelRecurrence/∀c. Do NOT add a false hyp (9+ caught; 0 more). NO absolute-low regression. If the sync
multiplicative bound genuinely can't close (azuma_tail doesn't fit the band-count process), prove the maximal
prefix and name the EXACT residual. No sorry/admit/new axiom/native_decide. #print axioms (lake env temp
importer, delete): [propext, Classical.choice, Quot.sound]. Do NOT git. Final message: Jall +
fulljoint_step_maintains (Ssmall_occupied maintained from FrontShape, NOT carried?); whether the clock is NOW
unconditional whp (theorem VERBATIM, NO structural hyp) OR the EXACT residual; build verdict; #print axioms;
HONEST status; confirm NO absolute-low regression.
