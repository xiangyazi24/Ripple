# ExactMajority — UNDERSTANDING

Last updated: 2026-05-23 (brainstorm session, 3 rounds with Gemini 3.1 Pro + uis-life Claude)

## What This Is

Lean 4 formalization of Doty et al.'s exact majority population protocol
("A time and space optimal stable population protocol solving exact majority",
arXiv:2106.10201v2, 2022), within the Ripple project.

## Current State: 78 sorry, framework redesign in progress

### Framework-Level Problem (2026-05-23 brainstorm conclusion)

The original architecture used `DescentKernelOn` (in `HittingTimeBound.lean`),
which requires single-step strict descent for ALL states satisfying the invariant.
This is **mathematically impossible** for the Doty protocol because:

1. **Reachable stuck states exist**: e.g., 1 clock + 1 cr + 6 main/reserve.
   No single interaction can decrease any reasonable potential. The protocol's
   actual progress relies on amortized analysis over O(L log n) steps.

2. **∀ᵐ statements are mathematically false**: Doty's results give
   `μ{¬P} ≤ 1/n²`, not `μ{¬P} = 0`. The `AeBridge.ae_of_measure_compl_le`
   was a sorry-for-falsehood.

3. **JansonGeometric.lean (1898 lines, 0 sorry) was never used**: The main
   probabilistic tool for Doty's analysis (geometric waiting time concentration)
   was fully proven but never connected to the protocol.

### New Architecture: PhaseConvergence

Replace `DescentKernelOn` with `PhaseConvergence`:

```
structure PhaseConvergence (K : Kernel Ω Ω) where
  Pre  : Ω → Prop       -- precondition (from previous phase)
  Post : Ω → Prop       -- postcondition (for next phase)
  t    : ℕ              -- time bound
  ε    : ℝ≥0            -- failure probability
  post_absorbing : ∀ x, Post x → K x {y | Post y} = 1
  convergence : ∀ x, Pre x → (K ^ t) x {y | ¬Post y} ≤ (ε : ℝ≥0∞)
```

Composition via union bound:
- Time: t_total = Σ t_i
- Error: ε_total = Σ ε_i

Each phase uses its own proof technique:
- Phase 0: Janson geometric (role allocation)
- Phase 1-3: Epidemic coupling (clock synchronization)
- Phase 4-10: Conditional descent/drift (bias convergence, conditional on good Phase 0)

### Transition.lean Bugs (must fix)

1. **Phase 1 dead-end**: `phaseInit p=1` has no clock counter init;
   `Phase1Transition` has no counter update or advance rule.
2. **Phase 10 reachability FALSE**: Protocol also stabilizes at Phase 2/4/9.
   Fixed by `majorityStableEndpoint` (disjunctive).
3. **Phase 0 role allocation**: Needs multiset multiplicity formulation.

## File Layout

### Probability tools (ALL 0 sorry, keep as-is)
- `JansonGeometric.lean` (1898 lines) — Janson tail bounds for geometric sums
- `Epidemic.lean` (121 lines) — Epidemic concentration (Lemma 4.5)
- `Supermartingale.lean` (188 lines) — Multiplicative drift (Theorem 4.2)
- `EpidemicTime.lean` (117 lines) — Epidemic expected time
- `MarkovChain.lean` (142 lines) — Generic Markov kernel + ae preservation
- `Scheduler.lean` (202 lines) — Uniform random scheduler
- `DescentPotential.lean` (39 lines) — Deterministic descent (useful for Phase 4-10)

### Framework (being rewritten)
- `PhaseConvergence.lean` — NEW: replaces HittingTimeBound.lean
- `JansonHitting.lean` — NEW: bridge from Janson to protocol events
- `HittingTimeBound.lean` — DEPRECATED (DescentKernelOn is wrong)

### Protocol definition
- `Transition.lean` — State machine (11 phases, needs bug fixes)
- `../Basic/*.lean` — Agent state, roles, bias, etc.

### Analysis (needs rewrite to use PhaseConvergence)
- `Invariants.lean` — Phase monotonicity + per-phase invariants
- `Invariants_7_patch.lean` — DEPRECATED (uses old DescentKernel)
- `Invariants_5_1_patch.lean` — DEPRECATED
- `DescentProofs.lean` — DEPRECATED (can't close under DescentKernelOn)
- `MainTheorem.lean` — Top-level cardinality + composition

### To delete
- `AeBridge.lean` — Contains false `ae_of_measure_compl_le`

## Priority Queue

1. **P0**: Delete AeBridge falsehood, reformulate ∀ᵐ → measure bounds
2. **P1**: Create PhaseConvergence.lean + compose_two_phases
3. **P2**: Fix Transition.lean Phase 1 + Phase 10 bugs
4. **P3**: Create JansonHitting.lean (bridge Janson → protocol events)
5. **P4**: Phase-specific convergence instantiations

## Session Log

- 2026-05-23: Three-way brainstorm (Opus 4.6 + Gemini 3.1 Pro + uis-life Claude).
  Consensus: DescentKernelOn wrong, PhaseConvergence needed, ∀ᵐ is false,
  Janson unused. Task split: uis-life→Phase A, agy→PhaseConvergence draft,
  Opus→UNDERSTANDING+JansonHitting.
