# Doty time-half — habs: discharge the deterministic closures of Q_mix; scope the phase-3 synchronization

Directive: 挨个做，绝对不退缩，不 over-claim. `habs_mix` (the one carried hyp of the real-kernel clock) is the
one-step closure of `Q_mix n mC T` on the kernel support. Q_mix = `card=n ∧ clockPhase3 (clocks at phase EXACTLY
3) ∧ clockSize (clockCount=mC) ∧ crossedT (9mC/10 ≤ rBeyond T)`. Discharge what's deterministic; precisely scope
the hard residual.

## What's deterministic (DISCHARGE these — should be clean)
- `card = n`: transitions preserve total card.
- `clockSize` (clockCount = mC): clock ROLE is permanent (a clock never becomes non-clock; reuse the public
  per-phase role-preservation lemmas / hmono's role facts), so clockCount is invariant.
- `crossedT` (9mC/10 ≤ rBeyond T): `rBeyond T` is non-decreasing — REUSE `hmono_mix_discharged` (already proven)
  or its `rBeyond T` analog. So the 0.9-floor at level T is preserved.

## The hard residual — `clockPhase3` closure (SCOPE it precisely, prove if clean, else report)
A phase-3 clock leaves phase 3 ONLY via `stdCounterSubroutine`, which fires ONLY for two clocks at the SAME
minute AT THE CAP (`Transition_phase3_clock_cap`: `¬ minute < K(L+1)`), and advances phase only when `counter=0`
(else it just decrements counter, staying phase 3). Plus the epidemic-phase-max can spread phase 4 once any
agent is at phase 4.
So clockPhase3 is preserved one step UNLESS some clock is at the cap with counter 0 (or a phase-4 agent already
exists to spread). Determine the cleanest sufficient invariant:
  Option A: add `maxClockMinute < K(L+1)` (no clock at the cap) to the window — then no cap-escape, clockPhase3
    closed. BUT check: is `maxClockMinute < cap` preserved? (a drip/sync can push a clock to the cap — so NO,
    not one-step closed by itself; it degrades at the boundary.)
  Option B: add `allClocksCounterPos` (every clock counter ≥ 1) — then stdCounterSubroutine only decrements,
    never advances phase, clockPhase3 closed. Check its closure (counter decrements only at cap; needs the
    counter-vs-minute timing to stay ≥ 1 until the clock completes).
This is the front-shape/synchronization content (clocks reach the cap together at the end, not early). It is
likely a reachability invariant beyond one-step closure.

## Task (NEW file Probability/HabsDischarge.lean only)
1. Prove the deterministic closures: `qmix_card_closed`, `qmix_clockSize_closed`, `qmix_crossedT_closed`
   (the 3 easy fields), reusing role-permanence + hmono.
2. Attempt `clockPhase3` closure under the cleanest added invariant (Option A or B). If it closes cleanly with a
   TRUE added invariant whose own closure you can also prove, deliver `habs_mix_discharged` (Q_mix' one-step
   closed, Q_mix' = Q_mix + the added true invariant). If the added invariant's closure genuinely needs a
   reachability/front-shape argument beyond one step, STOP at that exact point and REPORT: which 3 fields are
   discharged, the exact added invariant needed, and the precise reachability sub-lemma that remains (the
   synchronization fact "clocks reach the cap together / counter stays positive until completion").

## HARD RULES (automode, 绝对不退缩, 不 over-claim)
NEW file HabsDischarge.lean only; do NOT edit existing files, do NOT weaken proven lemmas. Discharge the
deterministic closures genuinely (reuse hmono/role-permanence). For clockPhase3, do NOT assume/fake it — either
prove it under a TRUE added invariant (with that invariant's closure also proven) or STOP and report the exact
remaining reachability sub-lemma. No sorry/admit/new axiom/native_decide. Iterate `lake build
Ripple.PopulationProtocol.Majority.ExactMajority.Probability.HabsDischarge` until clean. Do NOT git. Final
message: the 3 deterministic-closure lemma statements (proven?), the clockPhase3 status (proven under invariant X
with X's closure proven / STOPPED at exact reachability sub-lemma Y), build verdict, #print axioms (must be
[propext, Classical.choice, Quot.sound]), HONEST status. This bounds habs: either discharged, or reduced to ONE
precisely-named synchronization sub-lemma. If rate-limited, report on-disk WIP.
