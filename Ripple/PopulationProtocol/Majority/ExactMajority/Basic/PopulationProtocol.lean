/-
Generic population protocol model.

A population protocol is a pair P = (Λ, δ) where Λ is a finite state set and
δ : Λ × Λ → Λ × Λ is a (possibly randomized) transition function. A configuration
is a multiset of size n over Λ. Reachability c ⇒ c' holds when some sequence of
applicable transitions takes c to c'.

This file provides the generic infrastructure shared by any population protocol,
independent of the specific Doty et al. exact majority protocol. Future research
work building on top of exact majority can reuse these definitions.

Reference: Doty, Eftekhari, Gąsieniec, Severson, Stachowiak, Uznański,
"A time and space optimal stable population protocol solving exact majority"
(arXiv:2106.10201v2), §2.1.
-/

import Mathlib.Data.Multiset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Basic

namespace ExactMajority

/-- A (deterministic) population protocol on state set `Λ`. -/
structure Protocol (Λ : Type*) [Fintype Λ] [DecidableEq Λ] where
  /-- Transition function on ordered pairs of states. -/
  δ : Λ → Λ → Λ × Λ

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]

/-- A configuration is a multiset of agent states. The population size is
its cardinality. -/
abbrev Config (Λ : Type*) := Multiset Λ

/-- Population size of a configuration. -/
def Config.size (c : Config Λ) : ℕ := c.card

/-- Count of agents in state `s`. -/
def Config.count [DecidableEq Λ] (c : Config Λ) (s : Λ) : ℕ := Multiset.count s c

namespace Protocol

variable (P : Protocol Λ)

/-- A transition `α : r₁, r₂ → p₁, p₂` is applicable to `c` if `c` contains both
`r₁` and `r₂` as a (multiset) submultiset. -/
def Applicable (c : Config Λ) (r₁ r₂ : Λ) : Prop :=
  {r₁, r₂} ≤ c

/-- One-step reachability: `c ⇒_α c'` for transition α applied to states r₁, r₂. -/
def StepRel (c c' : Config Λ) : Prop :=
  ∃ r₁ r₂, Applicable c r₁ r₂ ∧
    let (p₁, p₂) := P.δ r₁ r₂
    c' = c - {r₁, r₂} + {p₁, p₂}

/-- Reachability: reflexive-transitive closure of `StepRel`. -/
def Reachable (c c' : Config Λ) : Prop :=
  Relation.ReflTransGen P.StepRel c c'

end Protocol

/-- Output partition for a Boolean-valued (with tie) population protocol.
Λ is partitioned into states outputting A, B, or T. -/
structure OutputPartition (Λ : Type*) [Fintype Λ] where
  isA : Λ → Bool
  isB : Λ → Bool
  isT : Λ → Bool
  partition : ∀ s, (isA s).toNat + (isB s).toNat + (isT s).toNat = 1

/-- A configuration has a defined output `u` if all agents agree on output `u`. -/
def OutputPartition.output (part : OutputPartition Λ)
    (u : Bool × Bool × Bool) (c : Config Λ) : Prop :=
  ∀ s ∈ c, (part.isA s, part.isB s, part.isT s) = u

/-- A configuration `c` is **stable** with respect to an output partition iff
there exists a single output triple `u` such that every agent in `c` outputs
`u` AND every reachable configuration `c'` continues to have all agents
output the same `u`.

Paper §2.2: "we say `o` is stable if `φ(o)` is defined and, for all `o₂` such
that `o ⇒ o₂`, `φ(o) = φ(o₂)`." -/
def Protocol.IsStable (P : Protocol Λ) (part : OutputPartition Λ)
    (c : Config Λ) : Prop :=
  ∃ u, part.output u c ∧ ∀ c', P.Reachable c c' → part.output u c'

/-- A protocol **stably computes** a target predicate `target : Config → Bool ×
Bool × Bool` (mapping initial configs to their intended majority verdict)
if every initial configuration `init` satisfying the validity predicate has
some reachable configuration `o` that is `IsStable` with output equal to
`target init`.

Paper §2.2: "The protocol stably computes majority if, for any valid initial
configuration `i`, for all `c` such that `i ⇒ c`, there is a stable `o` such
that `c ⇒ o` and `φ(o) = M(i)`." -/
def Protocol.StablyComputes (P : Protocol Λ) (part : OutputPartition Λ)
    (valid : Config Λ → Prop)
    (target : Config Λ → Bool × Bool × Bool) : Prop :=
  ∀ init, valid init → ∀ c, P.Reachable init c →
    ∃ o, P.Reachable c o ∧
      part.output (target init) o ∧
      P.IsStable part o

end ExactMajority
