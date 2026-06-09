# Doty time-half — iterate front-emptiness recursion over W levels → connect to clock progress

Directive: 闷头跑，绝对不退缩，不 over-claim (Xiang fully delegated). The clock now carries an emptiness window
(ClockBulkFront.clock_frontSync_via_capRel_bulk): FrontSync-whp given the front empty near the cap. The proven
per-level empty-absorbing step (feeder_empty_absorbing_up_to_drip) recurses level-uniformly. ITERATE it over all
W=frontWidthBound n=O(log log n) front levels to close the front-emptiness, bottoming at the base case
(leading edge below cap-W). Then CONNECT the base case to the clock's own progress (clock_real_step), or report
the joint clock-front induction as the genuine deepest residual.

## The structure
- Inductive step (PROVEN, level-uniform): empty at depth d (rBeyond(cap-d)=0) given within-envelope/empty at
  depth d+1, via feeder_empty_absorbing_up_to_drip + the level-union (rBeyond_seed_le_rBeyondSq, sync vanishes on
  empty). Generalize/iterate over d=1..W.
- Base case (depth W): env(cap-W) < 1/n (front_shape_collapse) ⟹ within-envelope at depth W ⟺ empty ⟺ leading
  edge below cap-W (no clock in the top W minutes). This is the clock-PROGRESS condition.
- Connect: clock_real_faithful_O_log_n / clock_real_step establishes the clock advances its leading edge minute
  by minute, reaching the cap in O(log n) parallel time; so the leading edge is below cap-W for the first cap-W
  minutes (= O(log n), most of the run). If this connection closes cleanly, FrontSync holds whp throughout the
  run until the final O(log log n) minutes (= clock completion) ⟹ the clock is unconditional whp. If it needs a
  JOINT induction (clock-advances ∧ front-empty mutually — Doty §6's intertwined core), report that precisely.

## Task (NEW file Probability/ClockFrontIter.lean only; may edit ClockBulkFront.lean to rewire — sole writer)
1. `front_empty_all_levels`: iterate the proven empty-absorbing step over d=1..W → front empty at all top W
   levels whp, GIVEN the base case (leading edge below cap-W). Level-uniform iteration (reuse
   level_union_concentration + feeder_empty_absorbing_up_to_drip).
2. Attempt the connection: from clock_real_faithful_O_log_n (clock reaches cap in O(log n)) + the bulk leading-edge
   progress, derive "leading edge below cap-W for the first cap-W minutes" ⟹ FrontSync whp throughout the run ⟹
   clock unconditional whp (NO carried structural assumption, only ε/t budget). If the connection genuinely needs
   the joint clock-front induction, prove the maximal clean prefix and STOP at the exact joint-induction statement.
3. Deliver either `clock_real_O_log_n_fully_unconditional` (no structural hyp) OR the precisely-named joint
   residual.

## BUILD ROUTING
Iterate with `nice -n 15 env LEAN_NUM_THREADS=2 ~/.elan/bin/lake env lean <file>` (single-file). Full build:
`~/.openclaw/workspace/scripts/remote-build.sh Ripple` (uisai1) OR ONE local lake-build run ALONE after
memory_pressure >50% free. No concurrent builds. cd ~/.openclaw/workspace/projects/Ripple

## HARD RULES (绝对不退缩, 不 over-claim)
NEW file ClockFrontIter.lean only (may edit ClockBulkFront.lean to rewire). The iteration MUST be genuinely
proven (iterate the PROVEN per-level step), NEVER assumed. Do NOT add a false hyp — 9 issues caught this session;
do NOT add a 10th. If the clock-progress connection needs the joint induction, name it PRECISELY and STOP — do
NOT fake the connection. No sorry/admit/new axiom/native_decide. Verify #print axioms (lake env temp importer,
delete): [propext, Classical.choice, Quot.sound]. Do NOT git. Final message: the W-level iteration (genuine?);
whether the clock is NOW fully unconditional whp (give the theorem VERBATIM, confirm NO structural hyp) OR the
precise joint clock-front induction residual; build verdict; #print axioms; HONEST status.
