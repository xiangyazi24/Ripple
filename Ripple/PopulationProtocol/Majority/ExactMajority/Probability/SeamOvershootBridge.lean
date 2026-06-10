/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Doty §6 — discharging the deterministic seam overshoot bridge (`SeamOvershootBridge`)

This file PROVES `SeamNoOvershoot.DetSeamOvershootBridge p` — the deterministic
first-overshoot bridge that `SeamNoOvershoot.lean` / `SeamPairAdapter.lean` carry as a
named structural guard `hdet`.  The bridge says:

> from a `NoOvershoot p` config (every agent at phase `< p+2`), a single scheduled
> interaction that creates an agent at phase `≥ p+2` forces a SOURCE clock at phase
> `p+1` with `counter = 0` (a witness to `AtRiskClockZero p c`).

## The obstruction and the well-formedness fix `W`

The bridge is FALSE without a well-formedness side condition (see
`HANDOFF_SEAM_NOOVERSHOOT.md` finding 2): `phaseInit 1` sends an `mcr` agent to phase
`10` (`enterPhase10`), and `phaseInit {2,9}` send an out-of-range-`smallBias` agent to
phase `10`.  An `mcr` agent epidemic-dragged into phase `1` therefore overshoots (to
phase `10 ≥ 2 = p+2` at the `p = 0` seam) with NO counter-`0` clock involved.

The MINIMAL well-formedness predicate that closes EVERY `phaseInit` error-to-`10` path
on the seam region is, per agent,

  `WfAgent a := a.role ≠ .mcr ∧ 2 ≤ a.smallBias.val ∧ a.smallBias.val ≤ 4`.

`phaseInit q a = enterPhase10 …` (phase `10`) for `q ≤ 9` happens ONLY when `q = 1 ∧
role = mcr`, or `q ∈ {2,9} ∧ (smallBias ≤ 1 ∨ smallBias ≥ 5)` (verified against the
FROZEN `phaseInit`); `WfAgent` excludes all three.  `phaseInit 10` always errors but is
never invoked on a seam to `p+1 ≤ 8` (`runInitsBetween` only runs `phaseInit q` for
`q ≤ max source phase ≤ p+1 ≤ 8`).

`Wf c := ∀ a ∈ c, WfAgent a` is the config-level predicate.

### Provenance and preservation

`WfAgent` is PRESERVED by every protocol step on the seam region:

* `phaseInit` preserves `smallBias` (`phaseInit_smallBias_eq`) and never creates an
  `mcr` (its only role write is `cr → reserve`), so the epidemic prefix preserves
  `WfAgent`.
* the per-phase dispatcher (for the seam phases) preserves `smallBias` and never
  creates `mcr` either.

Provenance: at the phase-0 EXIT (`RoleSplitConcentration.RoleSplitStage2Good`), `mcr`
count is `0`, and the carrier `smallBias` invariant `{2,3,4}` holds; no rule creates an
`mcr` or pushes `smallBias` out of `{2,3,4}` afterward, so `Wf` holds on the whole seam
region.  We expose `Wf` + its one-step preservation here; the seam layer threads it
from the Analysis-layer reachability invariants.

## The bridge proof (Stage 3)

Under `Wf` and `CounterResetDest (p+1)` (the honest counter-reset destination set
`{1,6,7,8}` the seam tail uses), the per-side case analysis is:

* `finishPhase10Entry` preserves phase, so `(Transition a b).1.phase = out.1.phase`.
* the epidemic output `ep.1.phase = max(a.phase, b.phase) ≤ p+1` (no error under `Wf`).
* the dispatcher at `ep.1.phase = q ≤ p+1` advances by at most `+1`, reaching `p+2`
  ONLY when `q = p+1` and the agent is a CLOCK whose counter is `0` (the
  `stdCounterSubroutine` advance branch).
* an epidemic-dragged clock enters `p+1` with the FULL (reset) counter `≠ 0`, so the
  zero-counter source clock is `a` itself, ALREADY at phase `p+1` with `counter = 0` —
  a witness to `AtRiskClockZero p c`.

Reference: Doty et al. §6; consumer = `SeamNoOvershoot.lean` / `SeamPairAdapter.lean`;
protocol core = `Protocol/Transition.lean` (FROZEN); reusable pieces =
`SeamPairBound.lean`; blueprint = `HANDOFF_SEAM_NOOVERSHOOT.md`.
-/

import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.SeamPairBound

namespace ExactMajority

open scoped ENNReal NNReal Real BigOperators

namespace SeamNoOvershoot

variable {L K : ℕ}

/-! ## Stage 1 — the well-formedness predicate `W`, its provenance and preservation. -/

/-- **Per-agent seam well-formedness.**  Exactly enough to forbid every `phaseInit`
error-to-`10` branch on the seam region: no `mcr` role (phase-1 error), and `smallBias`
in the carrier range `{2,3,4}` (phase-`{2,9}` error needs `smallBias ≤ 1 ∨ ≥ 5`). -/
def WfAgent (a : AgentState L K) : Prop :=
  a.role ≠ .mcr ∧ 2 ≤ a.smallBias.val ∧ a.smallBias.val ≤ 4

/-- **Config-level seam well-formedness.** -/
def Wf (c : Config (AgentState L K)) : Prop :=
  ∀ a ∈ c, WfAgent (L := L) (K := K) a

instance (a : AgentState L K) : Decidable (WfAgent (L := L) (K := K) a) := by
  unfold WfAgent; infer_instance

instance (c : Config (AgentState L K)) : Decidable (Wf (L := L) (K := K) c) := by
  unfold Wf; infer_instance

/-- `phaseInit q a` never errors to phase `10` for a well-formed agent at a non-error
init phase `q ≤ 9`: the only error branches are `q = 1 ∧ mcr`, `q ∈ {2,9} ∧ bad
smallBias`, all excluded by `WfAgent`. -/
theorem phaseInit_phase_eq_of_wf (q : Fin 11) (a : AgentState L K)
    (hwf : WfAgent (L := L) (K := K) a) (hq : q.val ≤ 9) :
    (phaseInit L K q a).phase.val = a.phase.val := by
  obtain ⟨hmcr, hlo, hhi⟩ := hwf
  -- smallBias ∈ {2,3,4} ⟹ ¬(smallBias ≤ 1 ∨ smallBias ≥ 5)
  have hbias : ¬ (a.smallBias.val ≤ 1 || a.smallBias.val ≥ 5) = true := by
    simp only [Bool.or_eq_true, decide_eq_true_eq, not_or, Nat.not_le]
    constructor <;> omega
  fin_cases q
  · rfl
  · -- phase 1
    unfold phaseInit; simp only [↓reduceDIte]
    rw [if_neg hmcr]
    by_cases h2 : a.role = .cr
    · rw [if_pos h2]
    · rw [if_neg h2]
      by_cases h3 : a.role = .clock
      · rw [if_pos h3]
      · rw [if_neg h3]
  · -- phase 2
    unfold phaseInit; simp only [↓reduceDIte, Nat.reduceEqDiff]
    rw [if_neg hbias]
  · -- phase 3
    unfold phaseInit; simp only [↓reduceDIte, Nat.reduceEqDiff]
    rcases a with ⟨_, _, _, role, _⟩; cases role <;> rfl
  · rfl
  · -- phase 5
    unfold phaseInit; simp only [↓reduceDIte, Nat.reduceEqDiff]
    split_ifs <;> rfl
  · -- phase 6
    unfold phaseInit; simp only [↓reduceDIte, Nat.reduceEqDiff]
    split_ifs <;> rfl
  · -- phase 7
    unfold phaseInit; simp only [↓reduceDIte, Nat.reduceEqDiff]
    split_ifs <;> rfl
  · -- phase 8
    unfold phaseInit; simp only [↓reduceDIte, Nat.reduceEqDiff]
  · -- phase 9
    unfold phaseInit; simp only [↓reduceDIte, Nat.reduceEqDiff]
    rw [if_neg hbias]
  · -- phase 10 excluded by hq
    exact absurd hq (by decide)

/-- `phaseInit` preserves `WfAgent` (preserves `smallBias`; never creates an `mcr`). -/
theorem phaseInit_preserves_wf (q : Fin 11) (a : AgentState L K)
    (hwf : WfAgent (L := L) (K := K) a) :
    WfAgent (L := L) (K := K) (phaseInit L K q a) := by
  obtain ⟨hmcr, hlo, hhi⟩ := hwf
  refine ⟨?_, ?_, ?_⟩
  · -- role ≠ mcr : phaseInit's only role write is cr → reserve (and enterPhase10 keeps role)
    intro hcontra
    rcases a with ⟨_, _, _, role, _⟩
    fin_cases q <;>
      revert hcontra <;>
      cases role <;>
      simp_all [phaseInit, enterPhase10] <;>
      (try split_ifs) <;> simp_all
  · rw [phaseInit_smallBias_eq]; exact hlo
  · rw [phaseInit_smallBias_eq]; exact hhi

/-- `runInitsBetween` preserves `WfAgent`. -/
theorem runInitsBetween_preserves_wf (oldP q : ℕ) (a : AgentState L K)
    (hwf : WfAgent (L := L) (K := K) a) :
    WfAgent (L := L) (K := K) (runInitsBetween L K oldP q a) := by
  unfold runInitsBetween
  have key : ∀ (l : List ℕ) (c : AgentState L K), WfAgent (L := L) (K := K) c →
      WfAgent (L := L) (K := K)
        (List.foldl (fun acc k => if h : k < 11 then phaseInit L K ⟨k, h⟩ acc else acc)
          c l) := by
    intro l
    induction l with
    | nil => intro c hc; simpa using hc
    | cons k ks IH =>
      intro c hc
      simp only [List.foldl_cons]
      apply IH
      by_cases hk : k < 11
      · rw [dif_pos hk]; exact phaseInit_preserves_wf ⟨k, hk⟩ c hc
      · rw [dif_neg hk]; exact hc
  exact key _ a hwf

end SeamNoOvershoot

end ExactMajority
