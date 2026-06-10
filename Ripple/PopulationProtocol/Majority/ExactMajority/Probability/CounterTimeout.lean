/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Generic counter-timeout wrapper for timed phases (Doty et al., Phase C)

Every *timed* phase of the Doty exact-majority protocol (phases 0, 1, 5, 6, 7, 8)
is driven by the **shared standard counter subroutine** running on the `Clock`
agents.  The phase advances once every clock counter has been decremented down to
`0`.  The deterministic core — "a clock-clock interaction with positive counters
strictly decrements the combined counter, and a zero counter advances the phase" —
already lives in `Analysis/PhaseProgress.lean`
(`stdCounterSubroutine_counter_strict_descent`, `stdCounterSubroutine_zero_advances`).

This file provides the **probabilistic timeout wrapper** that turns that
deterministic decrement into a *whp finish in `C·n·log n` interactions* statement,
in a form parametric enough that each timed phase instantiates it.

## Engine

We reuse the block-geometric hitting machinery of `Probability/ExpectedHitting.lean`.
The single quantitative input each phase must supply is the **per-block
contraction**

    hblock : ∀ b ∈ Doneᶜ, (K ^ s) b Doneᶜ ≤ q          (q < 1, s = block length)

i.e. "from any not-yet-finished configuration, a block of `s` interactions fails
to finish the phase with probability at most `q`".  The phase derives this from
(i) the carried clock floor `clockCount ≥ cFrac·n`, (ii) the per-pair decrement
event (a clock-clock meeting fires with probability `≥ (cFrac·n)²-shape / n²`),
and (iii) the counter cap `counter ≤ counterMax`, via the deterministic
`PhaseProgress` facts.  Given that single input, this file delivers:

* `counterTimeout_tail` — the whp tail `(K^(numBlocks·s)) c₀ Doneᶜ ≤ q ^ numBlocks`;
* `counterTimeout_PhaseConvergenceW` — packaged as a `PhaseConvergenceW K` instance
  with horizon `t = numBlocks·s` and failure `ε = q ^ numBlocks` (the `C·n·log n`
  shape: `numBlocks = Θ(log n)`, `s = Θ(n)`);
* `counterTimeout_PhaseConvergenceW_of_pre` — the predicate-shaped variant whose
  `Pre`/`Post` discharge `Done := {y | Post y}` and the absorption/contraction from
  a phase-entry hypothesis, the form the per-phase files (0/1/5/6/7/8) plug into;
* `counterTimeout_chain` — the chaining corollary into `composeW_two_phases`, so a
  timed phase composes with whatever phase follows it.

`Done` is the **phase-advance trigger** ("all clock counters hit `0`, phase
advanced").  It must be absorbing under `K` (once advanced, the phase epidemic and
the next phase's rule never send any agent back), which is the deterministic
closure each phase already owns.

ZERO sorry, zero axiom (beyond `propext`/`Classical.choice`/`Quot.sound`),
zero `native_decide`.
-/

import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.ExpectedHitting
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.PhaseConvergenceWeak

namespace ExactMajority

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal

namespace CounterTimeout

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ## Part 1 — The whp finish tail from a per-block contraction

The single fact each timed phase supplies is the per-block contraction `hblock`.
Everything probabilistic is then a thin wrapper over
`ExactMajority.bad_block_geometric`. -/

/-- **Counter-timeout whp tail.**  Let `Done` be the (measurable, absorbing) phase-
advance trigger.  If from every not-yet-finished configuration a block of `s`
interactions fails to finish the phase with probability at most `q`
(`hblock`), then after `numBlocks` such blocks the phase is unfinished with
probability at most `q ^ numBlocks`:

    (K ^ (numBlocks * s)) c₀ Doneᶜ ≤ q ^ numBlocks.

With `s = Θ(n)` (so that one block lets every clock meet another whp) and
`numBlocks = Θ(log n)`, the horizon `numBlocks * s = Θ(n log n)` interactions and
the failure `q ^ numBlocks = n^{-Θ(1)}`. -/
theorem counterTimeout_tail (K : Kernel Ω Ω) [IsMarkovKernel K]
    {Done : Set Ω} (hDone : MeasurableSet Done)
    (hAbs : ∀ x ∈ Done, K x Doneᶜ = 0)
    (s : ℕ) (q : ℝ≥0∞)
    (hblock : ∀ b ∈ (Doneᶜ : Set Ω), (K ^ s) b Doneᶜ ≤ q)
    (c₀ : Ω) (numBlocks : ℕ) :
    (K ^ (numBlocks * s)) c₀ Doneᶜ ≤ q ^ numBlocks :=
  bad_block_geometric K hDone hAbs s q hblock c₀ numBlocks

end CounterTimeout

end ExactMajority
