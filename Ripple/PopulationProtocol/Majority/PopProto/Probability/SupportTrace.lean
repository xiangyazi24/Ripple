/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Finite Support Traces

This file packages finite paths through the support of the approximate-majority
Markov kernel.  It lifts one-step support invariants, such as preservation of
having at least one opinionated agent, to finite stochastic executions.
-/

import Ripple.PopulationProtocol.Majority.PopProto.Invariant.Absorbing

namespace PopProto

namespace Config

variable {n : ℕ}

/-- Endpoint of a finite trace whose elements are successive configurations. -/
def supportTraceEndpoint : Config n → List (Config n) → Config n
  | c, [] => c
  | _, c' :: rest => supportTraceEndpoint c' rest

/-- A finite trace through the support of the one-step approximate-majority
kernel. -/
def supportTrace (hn : n ≥ 2) : Config n → List (Config n) → Prop
  | _, [] => True
  | c, c' :: rest => c' ∈ (c.stepDist hn).support ∧ supportTrace hn c' rest

/-- Having at least one opinionated agent is preserved along every finite
support trace. -/
theorem supportTraceEndpoint_hasOpinion
    (hn : n ≥ 2) (c : Config n) (trace : List (Config n))
    (htrace : supportTrace hn c trace) (hop : c.hasOpinion) :
    (supportTraceEndpoint c trace).hasOpinion := by
  induction trace generalizing c with
  | nil =>
      exact hop
  | cons c' rest ih =>
      rcases htrace with ⟨hsupp, hrest⟩
      exact ih c' hrest (hasOpinion_of_stepDist_support c hn hop hsupp)

/-- A finite support trace starting from an opinionated configuration cannot
end at the all-blank configuration. -/
theorem supportTraceEndpoint_not_allB
    (hn : n ≥ 2) (c : Config n) (trace : List (Config n))
    (htrace : supportTrace hn c trace) (hop : c.hasOpinion) :
    ¬(supportTraceEndpoint c trace).allB := by
  intro hallB
  have hop_end := supportTraceEndpoint_hasOpinion hn c trace htrace hop
  unfold hasOpinion opinionated at hop_end
  unfold allB at hallB
  omega

/-- Initial configurations of positive size stay away from all-blank along
every finite stochastic support trace. -/
theorem initial_supportTraceEndpoint_not_allB
    (hn : n ≥ 2) {a : ℕ} (h : a ≤ n)
    (trace : List (Config n))
    (htrace : supportTrace hn (initial n a h) trace) :
    ¬(supportTraceEndpoint (initial n a h) trace).allB :=
  supportTraceEndpoint_not_allB hn (initial n a h) trace htrace
    (initial_hasOpinion h (by omega))

end Config
end PopProto
