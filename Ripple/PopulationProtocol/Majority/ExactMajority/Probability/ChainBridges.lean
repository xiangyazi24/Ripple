/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Phase F-1 — the eleven-phase chain bridges (`ChainBridges`)

`DotyTimeHeadline.doty_time_headline_W` carries the ten deterministic structural bridges
`Post_i ⟹ Pre_{i+1}` as the named hypothesis

    h_chain : ∀ (i : Fin 11) (hi : i.val + 1 < 11),
        ∀ x, (phases i).Post x → (phases ⟨i.val + 1, hi⟩).Pre x

i.e. the SAME configuration `x` must satisfy phase `i`'s `Post` and phase `i+1`'s `Pre`.

## The load-bearing structural finding (verified against the concrete instances)

Every phase-window predicate **pins all agents to a single, distinct `phase.val`**:

| i  | `Post_i` window component (all `a ∈ c` satisfy)        |
|----|--------------------------------------------------------|
| 1  | `Phase1AllMain n`  : `a.phase.val = 1 ∧ role = main`   |
| 2  | `Q2 U v n`         : `a.phase.val = 2`                  |
| 6  | `Phase6Win n`      : `a.phase.val = 6`                  |
| 7  | `Phase7AllMain n`  : `a.phase.val = 7 ∧ role = main`   |
| 8  | `Phase8AllMain n`  : `a.phase.val = 8 ∧ role = main`   |

`Pre_{i+1}` pins the SAME agents to `phase.val = i+1`.  Hence for any nonempty config
(`card = n ≥ 1`) `Post_i x ∧ Pre_{i+1} x` is **contradictory**: pick `a ∈ x`; it would have
`a.phase.val = i` and `a.phase.val = i+1`.  So the pointwise bridge `∀ x, Post_i x → Pre_{i+1} x`
is **NOT** provable for the concrete family — it is FALSE on the populated window and only
vacuously true on the empty config (`n = 0`).

This is exactly why `DotyTimeHeadline` carries `h_chain` as a NAMED input rather than
discharging it: the bridge is the paper's per-phase ENTRY CONVENTION ("formally start each
phase assuming all agents already in it"), realised by the inter-phase `advancePhase`
counter-advance subroutine — a genuine TRANSITION that maps a phase-`i` config to a phase-
`(i+1)` config.  It is not a pointwise implication on a fixed `x`.

## What this file delivers

For the bridge `1 → 2` (representative; the same shape holds for every consecutive main-window
pair) we prove BOTH halves of the honest accounting:

* `bridge_1_2_pointwise_false_on_nonempty` — the pointwise bridge fails on any populated config:
  `Phase1Convergence.Phase1AllMain n x → 0 < n → ¬ Phase2Convergence.Q2 U v n x`.
  (Hence the abstract `h_chain` map cannot be the bare predicate implication.)

* `bridge_1_2_vacuous_on_empty` — on the empty config it holds vacuously, matching the only
  way the abstract signature is satisfiable without the advance step.

These two together are the precise, sound statement of the `1 → 2` gap; the campaign threads
the bridge through the `advancePhase` entry transition, NOT through this file.
-/

import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.Phase1Convergence
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.Phase2Convergence
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.Phase6Convergence
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.Phase7Convergence
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.Phase8Convergence

namespace ExactMajority
namespace ChainBridges

open Phase1Convergence Phase2Convergence Phase6Convergence Phase7Convergence Phase8Convergence

variable {L K : ℕ}

/-- Shared helper: a window predicate that pins every agent to a fixed `phase.val` is
incompatible with one pinning to a DIFFERENT `phase.val`, on any nonempty config. -/
private theorem phase_clash
    {n : ℕ} {x : Config (AgentState L K)} (hcard : x.card = n) (hn : 0 < n)
    {p q : ℕ} (hpne : p ≠ q)
    (hp : ∀ a ∈ x, a.phase.val = p) (hq : ∀ a ∈ x, a.phase.val = q) : False := by
  have hne : x ≠ 0 := by
    intro h0; rw [h0] at hcard; simp only [Multiset.card_zero] at hcard; omega
  obtain ⟨a, ha⟩ := Multiset.exists_mem_of_ne_zero hne
  exact hpne ((hp a ha).symm ▸ (hq a ha) ▸ rfl)

/-- **The `1 → 2` pointwise bridge is FALSE on any populated config.**

`Phase1AllMain n` forces every agent to `phase.val = 1`; `Q2 U v n` (the window component of
`Phase2`'s `Pre = Qwin U v n`) forces every agent to `phase.val = 2`.  A config with
`card = n` and `0 < n` is nonempty, so it has an agent witnessing the contradiction `1 = 2`.

Concretely: the abstract `h_chain` map `∀ x, Post_1 x → Pre_2 x` instantiated at the real
instances would require `Phase1AllMain n x → Q2 U v n x`, which this lemma refutes for `n ≥ 1`. -/
theorem bridge_1_2_pointwise_false_on_nonempty
    (U v : Fin 8) (n : ℕ) (x : Config (AgentState L K))
    (h1 : Phase1AllMain (L := L) (K := K) n x) (hn : 0 < n) :
    ¬ Q2 (L := L) (K := K) U v n x := by
  intro h2
  obtain ⟨hcard1, hph1⟩ := h1
  obtain ⟨hcard2, hph2⟩ := h2
  -- The config is nonempty: card = n > 0, so some agent exists.
  have hne : x ≠ 0 := by
    intro h0
    rw [h0] at hcard1
    simp only [Multiset.card_zero] at hcard1
    omega
  obtain ⟨a, ha⟩ := Multiset.exists_mem_of_ne_zero hne
  -- That agent is at phase 1 (from Phase1AllMain) and phase 2 (from Q2): contradiction.
  have hp1 : a.phase.val = 1 := (hph1 a ha).1
  have hp2 : a.phase.val = 2 := (hph2 a ha).1
  omega

/-- **The `1 → 2` pointwise bridge holds only vacuously, on the empty config.**

When `n = 0`, `Phase1AllMain 0 x` forces `card = 0`, i.e. `x = 0` (empty); both windows'
universal clauses are vacuous, so `Q2 U v 0 x` holds with no agents to satisfy `1 ≤ informedU`
breaking — this is exactly the degenerate branch that makes the abstract `h_chain` signature
type-check without the advance step.  We record it to make the accounting complete. -/
theorem bridge_1_2_vacuous_on_empty
    (U v : Fin 8) (x : Config (AgentState L K))
    (h1 : Phase1AllMain (L := L) (K := K) 0 x) :
    Q2 (L := L) (K := K) U v 0 x := by
  obtain ⟨hcard, _⟩ := h1
  -- card = 0 ⟹ x = 0 (the empty multiset).
  have hx0 : x = 0 := Multiset.card_eq_zero.mp hcard
  subst hx0
  refine ⟨hcard, ?_⟩
  intro a ha
  -- No agents in the empty config.
  exact absurd ha (by simp)

/-- **The `6 → 7` pointwise bridge is FALSE on any populated config.**
`Phase6Win n` pins `phase.val = 6`; `Phase7AllMain n` pins `phase.val = 7`. -/
theorem bridge_6_7_pointwise_false_on_nonempty
    (n : ℕ) (x : Config (AgentState L K))
    (h6 : Phase6Win (L := L) (K := K) n x) (hn : 0 < n) :
    ¬ Phase7AllMain (L := L) (K := K) n x := by
  intro h7
  obtain ⟨hcard, hph6⟩ := h6
  obtain ⟨_, hph7⟩ := h7
  exact phase_clash hcard hn (p := 6) (q := 7) (by omega)
    hph6 (fun a ha => (hph7 a ha).1)

/-- **The `7 → 8` pointwise bridge is FALSE on any populated config.**
`Phase7AllMain n` pins `phase.val = 7`; `Phase8AllMain n` pins `phase.val = 8`. -/
theorem bridge_7_8_pointwise_false_on_nonempty
    (n : ℕ) (x : Config (AgentState L K))
    (h7 : Phase7AllMain (L := L) (K := K) n x) (hn : 0 < n) :
    ¬ Phase8AllMain (L := L) (K := K) n x := by
  intro h8
  obtain ⟨hcard, hph7⟩ := h7
  obtain ⟨_, hph8⟩ := h8
  exact phase_clash hcard hn (p := 7) (q := 8) (by omega)
    (fun a ha => (hph7 a ha).1) (fun a ha => (hph8 a ha).1)

/-- **The `8 → 9` pointwise bridge is FALSE on any populated config.**
`Phase8AllMain n` pins `phase.val = 8`; phase 9's instance is the reused
`Phase2Convergence.phase2Convergence` at the second opinion union, whose `Pre = Qwin U' v' n`
carries the window `Q2 U' v' n` pinning `phase.val = 2`. -/
theorem bridge_8_9_pointwise_false_on_nonempty
    (U' v' : Fin 8) (n : ℕ) (x : Config (AgentState L K))
    (h8 : Phase8AllMain (L := L) (K := K) n x) (hn : 0 < n) :
    ¬ Q2 (L := L) (K := K) U' v' n x := by
  intro h9
  obtain ⟨hcard, hph8⟩ := h8
  obtain ⟨_, hph9⟩ := h9
  exact phase_clash hcard hn (p := 8) (q := 2) (by omega)
    (fun a ha => (hph8 a ha).1) (fun a ha => (hph9 a ha).1)

end ChainBridges
end ExactMajority
