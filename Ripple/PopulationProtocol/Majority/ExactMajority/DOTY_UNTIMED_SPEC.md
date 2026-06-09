# Doty time-half — Avenue (f-untimed): Phase-2 opinion-union epidemic PhaseConvergence on the real kernel

Directive: 挨个做，绝对不退缩，不 over-claim. The untimed phases (2,4,6,8,9) are 5 of A1's 11 phase instances;
they are clock-INDEPENDENT (no minute/hour), so they don't need the clock-timing (habs). Phase 2 (opinion
propagation by epidemic union) is the template; Phase 9 is identical. Build a genuine PhaseConvergence for it on
the REAL NonuniformMajority kernel, reusing the now-proven windowDrift + epidemic machinery.

## The mechanism (Phase 2 = opinion-set epidemic)
`opinionsUnion (x y : Fin 8) : Fin 8` is the bitwise union of opinion-sign sets (Protocol/Transition.lean:455).
`Phase2Transition` sets both agents' `opinions` to the union (line 533). This is a MONOTONE epidemic: the set
only grows, converging to the global union `U = ⋃ a∈c, a.opinions`. Post = every Phase-2 agent has `opinions = U`.
Reuse existing: `Phase2Transition_advances_of_union_has_opposite_signs` (PhaseProgress.lean:1660),
`opinionsUnion` lemmas in DeterministicChain (hasMinusOne/hasPlusOne_opinionsUnion_*),
`Phase2Transition_*_phase_ne_four_of_phase_two` (no spurious phase-4).

## Task (NEW file Probability/Phase2Convergence.lean only)
1. Potential: `opinionDeficit U c` = number of Phase-2 agents with `opinions ≠ U` (or `opinions ⊊ U`); the
   ℝ≥0∞/exponential-window form `Φ` for windowDrift. U = the global union (fixed on the absorbing window).
2. Window Q = `card = n ∧ (the global union U is stable)` — since union only grows, U is reached and then fixed;
   pick Q so that on it U is the absorbing maximum. Prove `Q` one-step closed.
3. Drift: a Phase-2 agent with `opinions ⊊ U` meets an agent whose union pushes it toward U → deficit drops.
   The advance probability ≥ Θ(1/n)-scale (an under-informed agent meets an informative partner; mirror A0's
   epidemicProto unit-coverage OR the real-kernel pair-counting). Prove `∫⁻ Φ ∂K ≤ r·Φ` on Q. Reuse the
   windowDrift_PhaseConvergence builder (kernel-generic) + interactionCount/totalPairs counting.
4. `phase2Convergence : PhaseConvergence (NonuniformMajority L K).transitionKernel`, Pre = (Phase-2 entered,
   card=n), Post = (every Phase-2 agent has opinions = U), t = O(n log n) interactions (untimed phases end fast,
   Janson-style O(log n) parallel), ε = 1/poly. This is one of A1's 11 phase instances, GENUINELY built.

## HARD RULES (automode, 绝对不退缩, 不 over-claim)
NEW file Phase2Convergence.lean only; do NOT edit existing files, do NOT weaken proven lemmas. The convergence
MUST be genuinely derived (drift from the opinion-union mechanism + pair-counting), never assumed. No
sorry/admit/new axiom/native_decide. If the global-union U absorbing argument needs an invariant, build it; if a
counting/union lemma is missing, build it or STOP and report the exact atom. Iterate `lake build
Ripple.PopulationProtocol.Majority.ExactMajority.Probability.Phase2Convergence` until clean. Do NOT git. Final
message: phase2Convergence signature verbatim, the opinion-deficit drift lemma, build verdict, #print axioms
(must be [propext, Classical.choice, Quot.sound]), HONEST status: convergence genuinely derived? what (if
anything) is carried? Note this is clock-INDEPENDENT (no habs/clock hyp). If rate-limited, report on-disk WIP.
