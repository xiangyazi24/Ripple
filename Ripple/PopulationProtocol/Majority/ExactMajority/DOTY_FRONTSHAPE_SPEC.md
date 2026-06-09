# Doty time-half — front-shape on the real kernel → allClocksCounterPos → complete habs → complete clock

Directive: 挨个做，绝对不退缩，不 over-claim. habs is reduced (HabsDischarge.lean) to ONE obligation:
`allClocksCounterPos` one-step closure (every clock counter ≥ 1, preserved). The counter is set to 50·(L+1) on
phase-3 entry and decrements ONLY at the cap (stdCounterSubroutine when minute = K(L+1)). So counter stays ≥ 1
until a clock has done ≥ 50(L+1) cap-interactions — which can't happen before the others catch up IF the clocks
are SYNCHRONIZED (front-shape: all clocks within O(log log n) minutes of the max). This is Doty's front-shape
(Theorem 6.5 / footnote 9) — the doubly-exponential front tail — on the REAL NonuniformMajority kernel.

## Reuse
- Abstract C4 `Probability/FrontShapeInduction.lean`: `FrontShapeAt`, `frontShape_step` (front tail
  c≥i+1 < p·c≥i² via real_front_squaring), `front_width_at`/`frontWidth_loglog` (O(log log n) width),
  `front_emptied_real`. This is the abstract front-shape — TRANSFER its conclusion to the real kernel.
- The real-kernel drift technique (ClockRealBulk/Seed/Mixed): per-pair lemmas (Transition_clock_pair,
  rDrip/rEpidemic advances), windowDrift, the c² pair-counting. The front-shape is the OTHER direction
  (growth-SUPPRESSION of the front tail) — use windowDrift's dual `windowGrowth`/S2b `real_front_squaring`.
- HabsDischarge.lean: `allClocksCounterPos`, `noPhaseAbove3`, `ClockPhase3_remaining_synchronization`,
  `habs_mix_deterministic_skeleton` (the 3 discharged closures). Build on these.
- AzumaKernel.azuma_tail if a concentration step is needed for the front width.

## Task (NEW file Probability/ClockFrontShape.lean only)
1. Define the real-kernel front quantity: `frontWidth c` = (max clock minute) − (the minute below which 0.9mC
   clocks sit), or reuse rBeyond's doubly-exp front tail. State the front-shape invariant `FrontSync c`
   (clocks within O(log log n) of the bulk; equivalently the front tail beyond the bulk is < 1 agent).
2. Prove `FrontSync` is maintained (the front tail squares each minute — reuse abstract `real_front_squaring`
   transferred via the per-pair drip lemma `dripPair_prob_le_sq`/`frontTail_kernel_one_step_le_beyondSq`).
3. Derive `allClocksCounterPos` closure FROM `FrontSync`: under synchronization, before any clock does 50(L+1)
   cap-decrements, the bulk reaches the cap, so the run completes — counter stays ≥ 1 throughout the clock's
   advancement. Discharge `ClockPhase3_remaining_synchronization`.
4. Assemble `habs_mix_full` : Q_mix (+ FrontSync as the now-PROVEN-maintained invariant) one-step closed →
   the real-kernel clock `clock_real_faithful_O_log_n` carries NO undischarged hyp (FrontSync is maintained,
   not assumed).

## HARD RULES (automode, 绝对不退缩, 不 over-claim)
NEW file ClockFrontShape.lean only; do NOT edit existing files, do NOT weaken proven lemmas. The front-shape
maintenance MUST be genuinely proven (transfer the abstract real_front_squaring to the real kernel via the
per-pair drip-squaring lemma), NOT assumed. allClocksCounterPos closure MUST be DERIVED from FrontSync + the
counter mechanics, never assumed. No sorry/admit/new axiom/native_decide. THIS IS GENUINELY HARD (C4-on-real-
kernel + the counter-vs-front timing). If a step genuinely needs a multi-step reachability beyond what transfers
cleanly, prove the maximal clean prefix and STOP at the EXACT remaining sub-lemma (name it precisely, like
HabsDischarge did) — do NOT fake it, do NOT introduce a false hyp. Iterate `lake build
Ripple.PopulationProtocol.Majority.ExactMajority.Probability.ClockFrontShape` until clean. Do NOT git. Final
message: FrontSync def, the front-shape maintenance lemma (proven via transferred squaring?), the
allClocksCounterPos-closure derivation, whether habs is now FULLY discharged or reduced to a smaller named
sub-lemma, build verdict, #print axioms (must be [propext, Classical.choice, Quot.sound]), HONEST status. If
rate-limited, report on-disk WIP.
