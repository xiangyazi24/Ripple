# Doty time-half — Avenue D-lynch-3: MIXED-regime clock advance (genuine 1/c², on the execution path)

Directive: 挨个做，绝对不退缩，不 over-claim. D-lynch/D-lynch-2 proved the clock-minute advance on the real kernel
but in the ALL-CLOCKS regime (`AllClockMinT3`: every agent a phase-3 clock) — which never arises in the real
protocol (clocks are a constant FRACTION coexisting with Main/Reserve agents). D-lynch-3 moves to the MIXED
regime: clocks are a sub-population of size m_C, Main/Reserve agents coexist, and the clock-minute advance rate
is genuinely ∝ (m_C/n)² = c² (Doty's 1/c² factor, now NON-trivial). This is the on-execution-path linchpin.

## What to reuse (all proven in ClockRealKernel.lean / ClockRealAdvance.lean — open them)
The per-pair facts are AGENT-OTHER-AGNOSTIC and reusable verbatim:
- `Transition_clock_pair` — a clock-clock pair keeps both clocks + minute non-decreasing across ALL 11 phases
  + epidemic-drag + Phase-10 entry. Holds regardless of the rest of the population.
- `rDrip_pair_advances`, `rDripDistinct_pair_advances`, `rEpidemic_pair_advances(')` — per-pair minute advance
  (drip on equal minute / epidemic sync), regardless of other agents.
- `rBeyond (T) c` = countP of agents with (role=clock ∧ minute ≥ T); `rBeyondGE3_ge_monotone`;
  `rSeedPot` window form; `windowDrift_PhaseConvergence` (kernel-generic F).
- `exists_clock_minute_eqT`, `exists_advancing_pairSet` — the counting that found an advancing pair.

## The MIXED-regime design
- Potential: same `rBeyond`/`rSeedPot` (counts CLOCK agents at minute ≥ T — Main agents contribute 0, fine).
- Window `Q_mix c`: `c.card = n` ∧ **(clock-role agents are at phase 3)** [NOT all agents — Main/Reserve
  unconstrained] ∧ **clockCount c = m_C** (carry the clock population size) ∧ rBeyond T c = m_C (all m_C clocks
  at minute ≥ T, the level-T floor for the clock sub-population).
- Drift: in the unfinished regime (rBeyond (T+1) c < m_C) there is ≥1 clock at minute exactly T; an advancing
  clock-clock pair exists (drip if ≥2 at T among clocks, else epidemic with a higher clock). The advance
  probability = (advancing clock-clock ordered pairs)/(totalPairs n(n−1)) ≥ **c_lb² · const** where
  c_lb = m_C/n is the clock fraction. DERIVE this from interactionCount/totalPairs exactly as D-lynch-2 did,
  but with the denominator the FULL n(n−1) (not clock-only) — THIS is where the genuine 1/c² appears.
- Package via `windowDrift_PhaseConvergence` into `clock_real_advance_mixed : PhaseConvergence
  (NonuniformMajority L K).transitionKernel`, contraction r = 1 − Θ((m_C/n)²·(1−e^{−s})).

## Honest hypotheses (carry as EXPLICIT, clearly-labeled inputs — to be discharged in separate avenues)
These are GENUINE protocol invariants (true in real executions); carry them as named hypotheses, do NOT hide
them, do NOT assume the contraction itself (that must be derived):
1. `hphase3 : (Q_mix window) clocks at phase exactly 3` and its one-step closure `habs_mix` — the phase-3
   window. (Discharge later via the cap-boundary reachability invariant.)
2. `hclock_lb : γ * n ≤ clockCount c` for a fixed fraction γ (e.g. from Phase-0 clock creation). The
   contraction factor is then ≥ Θ(γ²). (Discharge later via Phase-0 analysis.)
The contraction probability bound MUST be derived by pair-counting from these structural facts — never assumed.

## HARD RULES (automode, NO effort cap; 绝对不退缩; 不 over-claim)
NEW file `Probability/ClockRealMixed.lean` (imports ClockRealKernel + ClockRealAdvance); do NOT edit existing
files, do NOT weaken any proven lemma. No sorry/admit/new axiom/native_decide. The c² advance probability MUST
be genuinely derived from interactionCount/totalPairs with the full n(n−1) denominator (the real fraction) —
this is the whole point, the trivial c=1 case is already done. The structural hypotheses (phase-3 window,
clock-count bound) are carried as explicit named inputs, clearly labeled in the theorem signature and a doc
comment, flagged for separate discharge — NOT hidden, NOT the contraction itself. Iterate build until clean.
If a counting identity is missing, build it or STOP and report the exact atom + failing tactic chain. Do NOT
git. Build: `nice -n 15 env LEAN_NUM_THREADS=2 ~/.elan/bin/lake build
Ripple.PopulationProtocol.Majority.ExactMajority.Probability.ClockRealMixed`. Final message: the Q_mix window,
the mixed drift statement, the `clock_real_advance_mixed` signature verbatim (showing the explicit carried
hypotheses), build verdict, `#print axioms` (must be [propext, Classical.choice, Quot.sound]), and HONEST
status: is the c² genuinely derived (not c=1 trivial)? exactly which structural hypotheses are carried and why
each is true-but-deferred? Be precise, do not over-claim.
