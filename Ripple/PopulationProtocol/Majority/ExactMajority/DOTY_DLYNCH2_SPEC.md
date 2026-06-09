# Doty time-half — Avenue D-lynch-2: discharge the witness → UNCONDITIONAL clock-minute advance

Directive: 挨个做，绝对不退缩，不 over-claim. D-lynch (ClockRealKernel.lean) proved the clock-minute DRIP drift on
the real NonuniformMajority kernel, but `clock_real_advance` is CONDITIONAL on an undischarged `witnessOf`
input: "≥2 clocks with IDENTICAL full state (count w ≥ 2) at minute exactly T in the unfinished regime." That
witness is over-restrictive and not always true. D-lynch-2 DISCHARGES it, making the advance UNCONDITIONAL.

## Why the witness is dischargeable (the math — verify against Transition.lean Rule 1, lines ~734-748)
The Phase-3 both-Clock transition (Rule 1): `if s.minute ≠ t.minute then BOTH ← max minute (EPIDEMIC sync);
else if s.minute.val < cap then first ← minute+1 (DRIP)`. Crucially DRIP fires on EQUAL MINUTE — it does NOT
require identical full state. So the advance of `rBeyond (T+1)` (count of clocks at minute ≥ T+1) is guaranteed
in the unfinished floor regime (rBeyond T c = n, rBeyond (T+1) c = m < n ⟹ exactly n−m ≥ 1 clocks at minute
exactly T), by EITHER mechanism:
- **Case n−m ≥ 2** (≥2 clocks at minute exactly T): a DRIP pair fires (equal minute T, both clocks, T < cap)
  → one advances to T+1 → rBeyond(T+1) increases. Probability ≥ (pairs at minute T)/totalPairs.
- **Case n−m = 1** (exactly 1 clock at minute T, the other m ≥ 1 clocks at minute ≥ T+1): the lone T-clock
  meets a higher clock → EPIDEMIC sync → it jumps to ≥ T+1 → rBeyond(T+1) increases. Probability ≥
  (1·m ordered pairs)/totalPairs.
Either way there is a guaranteed positive-probability advance from the floor invariant ALONE — no witness.

## Task (EDIT the EXISTING Probability/ClockRealKernel.lean — you are its sole writer; or add a sibling file
## Probability/ClockRealAdvance.lean importing it, your choice — but the END RESULT is an UNCONDITIONAL theorem)
Reuse everything already proven in ClockRealKernel.lean (Transition_clock_pair, rBeyond, rBeyondGE3_ge_monotone,
rSeedPot, the drip lemmas rDrip_pair_advances / clock_real_drip_advance_prob, AllClockGE3_absorbing, the
windowDrift packaging). Do NOT weaken or delete any proven lemma.
1. Add an EPIDEMIC-sync advance lemma: in Phase 3, an unequal-minute clock pair (s.minute = T, t.minute > T,
   both clocks) syncs the T-clock up to t.minute > T, strictly increasing `rBeyond (T+1)` membership. Mirror the
   existing drip lemma `rDrip_pair_advances` (look at Transition_phase3_clock_minute_sync_decreases in
   PhaseProgress.lean for the per-pair sync fact).
2. Generalize the advance-probability lower bound so it counts ALL minute-T clock pairs (drip) and/or the
   T-clock × higher-clock pairs (epidemic), giving a uniform lower bound `≥ 2/(n(n−1))`-scale advance prob in
   BOTH the n−m≥2 and n−m=1 cases — DERIVED from interactionCount/totalPairs (the 1/c² pair-counting, as
   already done for drip). The existing `clock_real_drip_advance_prob` is the template.
3. **Discharge the witness:** prove `rFloorInv` (or a witness-free variant `rFloorInv'`) holds from the bare
   floor facts `c.card = n ∧ AllClockGE3 c ∧ rBeyond T c = n` ALONE (no witnessOf input), by the case split
   above. The key counting fact: rBeyond T c = n ∧ rBeyond (T+1) c = m < n ⟹ exactly n−m clocks at minute T
   (use `rBeyond` = countP at minute ≥ T minus at minute ≥ T+1), and n−m ≥ 1.
4. Deliver `clock_real_advance_uncond : PhaseConvergence (NonuniformMajority L K).transitionKernel` with NO
   witnessOf hypothesis — Pre/Post/t/ε as before but the floor invariant carries no witness. This is the
   genuine UNCONDITIONAL real-kernel clock-minute advance (one minute level).

## HARD RULES (automode, NO effort cap; 绝对不退缩; 不 over-claim)
Do NOT introduce sorry/admit/new axiom/native_decide. Do NOT weaken existing proven results. The witness MUST
be genuinely discharged (proven from the floor invariant), NOT re-assumed under a new name. If the n−m=1
epidemic case needs a sync-advance lemma not yet present, BUILD it from the per-pair sync fact — do not skip the
case and silently keep the drip-only witness. Iterate `lake build`/`lake env lean` until clean. If a genuine
counting identity is missing, build it honestly or STOP and report the EXACT atom with the failing tactic chain.
Do NOT git. Build: `nice -n 15 env LEAN_NUM_THREADS=2 ~/.elan/bin/lake build
Ripple.PopulationProtocol.Majority.ExactMajority.Probability.ClockRealKernel` (or your new module). Final
message: the new epidemic-sync lemma, the discharged-witness lemma (floor facts ⟹ rFloorInv with NO witness
input), the `clock_real_advance_uncond` signature verbatim, build verdict, `#print axioms` (must be
[propext, Classical.choice, Quot.sound]), and HONEST status: is the advance now fully unconditional, or does an
exact sub-case remain.
