# Doty time-half — discharge FrontSyncConcentration → UNCONDITIONAL real-kernel clock (final clock piece)

Directive: 挨个做，绝对不退缩，不 over-claim. The real-kernel clock carries habs, reduced (ClockFrontShape.lean)
to ONE genuine probabilistic sub-lemma `FrontSyncConcentration_remaining`: FrontSync (no clock at the cap
prematurely) survives the O(log n)-minute horizon. Discharge it → clock becomes UNCONDITIONAL.

## The content (genuine front-width concentration)
FrontSync breaks when a clock seeds the cap-front (minute ≥ cap) before the bulk arrives. Per-minute breach prob
≤ (frontMinuteCount(cap−1)/n)² (PROVEN: `ClockFrontShape.real_front_advance_squares_cap`). FrontSync holds whp
because the LEADING front stays O(log log n) wide (the doubly-exponential front tail) until the bulk reaches the
cap — so the clocks at minute cap−1 are few until the run completes, making the squared seed prob tiny, and the
union over the O(log n) horizon stays < ε.

## Reuse
- `ClockFrontShape.lean`: `real_front_advance_squares` / `_cap` (per-minute breach ≤ square — PROVEN),
  `FrontSync`, `frontSync_iff_rBeyond_cap_zero`, `counterPos_closed_of_frontSync`, `habs_clockPhase3_of_frontSync`,
  `FrontSyncConcentration_remaining` (the Prop to discharge).
- Abstract C4 `FrontShapeInduction.lean`: `frontWidth_loglog` / `front_width_at` / `front_emptied_real`
  (the front beyond `frontWidthBound n` is empty — the O(log log n) width). TRANSFER this width bound so the
  cap-front's feeder (minute cap−1) is small until the bulk arrives.
- `FrontTailKernel.lean`: `frontTail_kernel_O1_parallel` / the doubly-exp arithmetic.
- `AzumaKernel.azuma_tail` and/or a plain union bound over the horizon minutes.

## Task (NEW file Probability/FrontSyncConc.lean only)
1. Bound the per-minute FrontSync-breach probability by the squared front-feeder fraction
   (`real_front_advance_squares_cap`), and bound the front-feeder count by the O(log log n) front width
   (transfer `frontWidth_loglog`) until the bulk reaches the cap.
2. Union/Azuma over the O(log n)-minute horizon H: `Σ_{minutes} breach_prob < ε` for ε = 1/poly, using the
   doubly-exponential decay. PROVE `FrontSyncConcentration_remaining n mC H ε` for the real horizon H = Θ(log n),
   ε = 1/poly.
3. Wire: with `FrontSyncConcentration_remaining` proven + `habs_clockPhase3_of_frontSync` +
   `habs_mix_deterministic_skeleton`, deliver `habs_mix_full` (Q_mix one-step closure holds whp over the run) →
   `clock_real_unconditional` : the real-kernel `clock_real_faithful_O_log_n` with habs DISCHARGED (carrying no
   undischarged structural hyp, only the standard ε/t budget).

## HARD RULES (automode, 绝对不退缩, 不 over-claim)
NEW file FrontSyncConc.lean only; do NOT edit existing files, do NOT weaken proven lemmas. The concentration MUST
be genuinely proven (squared breach prob + transferred O(log log n) width + union/Azuma), NEVER assumed. Do NOT
add any false/undischargeable hyp (5 such were caught this session — do not add a 6th). No
sorry/admit/new axiom/native_decide. THIS IS THE GENUINELY HARD front-width concentration on the real kernel —
if a step needs a transfer that doesn't go through cleanly, prove the maximal clean prefix and STOP at the EXACT
remaining sub-lemma (name it precisely). Iterate `lake build
Ripple.PopulationProtocol.Majority.ExactMajority.Probability.FrontSyncConc` until clean. Do NOT git. Final
message: the breach-prob bound, the union/horizon concentration, whether `FrontSyncConcentration_remaining` is
PROVEN (and hence the clock is UNCONDITIONAL via habs_mix_full / clock_real_unconditional) or reduced to a
smaller named sub-lemma, build verdict, #print axioms (must be [propext, Classical.choice, Quot.sound]), HONEST
status. If rate-limited, report on-disk WIP.
