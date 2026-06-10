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

/-! ## Stage 2 — the epidemic no-error phase identity and the per-side overshoot
case analysis.

Under `Wf`, the epidemic does NOT error to phase `10` on the seam region (`runInitsBetween`
only runs `phaseInit q` for `q ≤ max source phase ≤ 9`, and a well-formed agent's
`phaseInit q` preserves the phase for `q ≤ 9`).  Hence the epidemic output phase equals
the source max, and the dispatcher's per-side overshoot is forced into the clock-counter
advance branch. -/

/-- `runInitsBetween oldP newP` preserves the phase of a well-formed agent when the
destination `newP ≤ 9` (every `phaseInit q` in the fold runs at `q ≤ newP ≤ 9`, none of
which error under `WfAgent`; and `WfAgent` is fold-invariant). -/
theorem runInitsBetween_phase_eq_of_wf (oldP newP : ℕ) (a : AgentState L K)
    (hwf : WfAgent (L := L) (K := K) a) (hnew : newP ≤ 9) :
    (runInitsBetween L K oldP newP a).phase.val = a.phase.val := by
  unfold runInitsBetween
  -- every k in the filter list has k ≤ newP ≤ 9
  have key : ∀ (l : List ℕ), (∀ x ∈ l, x ≤ 9) →
      ∀ (c : AgentState L K), WfAgent (L := L) (K := K) c →
      (List.foldl (fun acc k => if h : k < 11 then phaseInit L K ⟨k, h⟩ acc else acc)
        c l).phase.val = c.phase.val := by
    intro l
    induction l with
    | nil => intro _ c _; rfl
    | cons k ks IH =>
      intro hbound c hc
      simp only [List.foldl_cons]
      by_cases hk : k < 11
      · rw [dif_pos hk]
        have hk9 : (⟨k, hk⟩ : Fin 11).val ≤ 9 := hbound k (List.mem_cons_self ..)
        rw [IH (fun x hx => hbound x (List.mem_cons_of_mem k hx))
              (phaseInit L K ⟨k, hk⟩ c) (phaseInit_preserves_wf ⟨k, hk⟩ c hc)]
        exact phaseInit_phase_eq_of_wf ⟨k, hk⟩ c hc hk9
      · rw [dif_neg hk]
        exact IH (fun x hx => hbound x (List.mem_cons_of_mem k hx)) c hc
  apply key
  · intro x hx
    rw [List.mem_filter] at hx
    have := hx.2
    simp only [decide_eq_true_eq] at this
    omega
  · exact hwf

/-- **The epidemic no-error phase identity (left).**  Under `WfAgent a` and `WfAgent b`,
if both source phases are `≤ 9`, the left epidemic output phase equals the source max
(no error to `10` from either side). -/
theorem phaseEpidemicUpdate_left_phase_eq_max_of_wf (a b : AgentState L K)
    (hwfa : WfAgent (L := L) (K := K) a) (hwfb : WfAgent (L := L) (K := K) b)
    (ha9 : a.phase.val ≤ 9) (hb9 : b.phase.val ≤ 9) :
    (phaseEpidemicUpdate L K a b).1.phase.val = max a.phase.val b.phase.val := by
  unfold phaseEpidemicUpdate
  set p := max a.phase b.phase with hp
  have hpval : p.val = max a.phase.val b.phase.val := by rw [hp]; rfl
  have hp9 : p.val ≤ 9 := by rw [hpval]; omega
  have hwfa' : WfAgent (L := L) (K := K) ({ a with phase := p } : AgentState L K) := by
    obtain ⟨h1, h2, h3⟩ := hwfa; exact ⟨h1, h2, h3⟩
  have hwfb' : WfAgent (L := L) (K := K) ({ b with phase := p } : AgentState L K) := by
    obtain ⟨h1, h2, h3⟩ := hwfb; exact ⟨h1, h2, h3⟩
  have hs' : (runInitsBetween L K a.phase.val p.val ({ a with phase := p })).phase.val
      = p.val :=
    runInitsBetween_phase_eq_of_wf a.phase.val p.val _ hwfa' hp9
  have ht' : (runInitsBetween L K b.phase.val p.val ({ b with phase := p })).phase.val
      = p.val :=
    runInitsBetween_phase_eq_of_wf b.phase.val p.val _ hwfb' hp9
  -- the error branch needs s'.phase = 10 ∨ t'.phase = 10; both are p.val ≤ 9 — false.
  have herr_false :
      ¬ ((a.phase.val < 10 ∨ b.phase.val < 10) ∧
        ((runInitsBetween L K a.phase.val p.val ({ a with phase := p })).phase.val = 10 ∨
          (runInitsBetween L K b.phase.val p.val ({ b with phase := p })).phase.val = 10)) := by
    rintro ⟨-, hor⟩
    rcases hor with h | h
    · rw [hs'] at h; omega
    · rw [ht'] at h; omega
  simp only [herr_false, if_false]
  exact hs'

/-! ### The phase-advancing primitives advance by at most `+1` (under `Wf` for the
`phaseInit` step). -/

/-- `advancePhase` advances the phase by at most `+1`. -/
theorem advancePhase_phase_le_succ (a : AgentState L K) :
    (advancePhase L K a).phase.val ≤ a.phase.val + 1 := by
  unfold advancePhase
  split
  · simp
  · omega

/-- `advancePhaseWithInit` advances a well-formed agent's phase by at most `+1` when the
result phase is `≤ 9` (so `phaseInit` does not error): `advancePhase` adds at most `1`,
then `phaseInit` preserves it. -/
theorem advancePhaseWithInit_phase_le_succ_of_wf (a : AgentState L K)
    (hwf : WfAgent (L := L) (K := K) a) (hle : a.phase.val ≤ 8) :
    (advancePhaseWithInit L K a).phase.val ≤ a.phase.val + 1 := by
  unfold advancePhaseWithInit
  -- WfAgent is preserved by advancePhase (role/smallBias untouched)
  have hwf' : WfAgent (L := L) (K := K) (advancePhase L K a) := by
    obtain ⟨h1, h2, h3⟩ := hwf
    refine ⟨?_, ?_, ?_⟩ <;> (unfold advancePhase; split <;> simp_all)
  have hadv : (advancePhase L K a).phase.val ≤ a.phase.val + 1 := advancePhase_phase_le_succ a
  have hadv9 : (advancePhase L K a).phase.val ≤ 9 := by omega
  rw [phaseInit_phase_eq_of_wf (advancePhase L K a).phase (advancePhase L K a) hwf' hadv9]
  exact hadv

/-- `stdCounterSubroutine` advances a well-formed agent's phase by at most `+1` (when
`phase ≤ 8`): decrement keeps the phase; counter-`0` advance is `advancePhaseWithInit`,
`≤ +1`. -/
theorem stdCounterSubroutine_phase_le_succ_of_wf (a : AgentState L K)
    (hwf : WfAgent (L := L) (K := K) a) (hle : a.phase.val ≤ 8) :
    (stdCounterSubroutine L K a).phase.val ≤ a.phase.val + 1 := by
  unfold stdCounterSubroutine
  split_ifs with h
  · exact advancePhaseWithInit_phase_le_succ_of_wf a hwf hle
  · simp

/-- `clockCounterStep` advances a well-formed agent's phase by at most `+1`. -/
theorem clockCounterStep_phase_le_succ_of_wf (a : AgentState L K)
    (hwf : WfAgent (L := L) (K := K) a) (hle : a.phase.val ≤ 8) :
    (clockCounterStep L K a).phase.val ≤ a.phase.val + 1 := by
  unfold clockCounterStep
  split_ifs
  · exact stdCounterSubroutine_phase_le_succ_of_wf a hwf hle
  · simp

/-! ### Per-phase left-output `+1` bound (under `Wf`).

Every per-phase rule's LEFT output advances the phase ONLY through
`stdCounterSubroutine` / `clockCounterStep` / `advancePhaseWithInit` applied to a
well-formed agent (the role/smallBias-touching pre-steps set `role` to a non-`mcr` value
and preserve `smallBias`), so the advance is `≤ +1`.  We prove the bound phase-by-phase
for the phases the seam can dispatch (`q ≤ 8`). -/

/-- Phase 1 left output advances by `≤ +1` (it is `clockCounterStep` of a well-formed
agent, modulo a `smallBias`-only averaging pre-step). -/
theorem Phase1Transition_left_phase_le_succ_of_wf (a b : AgentState L K)
    (hwf : WfAgent (L := L) (K := K) a) (hle : a.phase.val ≤ 8) :
    (Phase1Transition L K a b).1.phase.val ≤ a.phase.val + 1 := by
  by_cases hmain : a.role = .main ∧ b.role = .main
  · -- main–main: the averaged agent has role = main ≠ clock, so clockCounterStep is id.
    have hccs : (clockCounterStep L K
        ({ a with smallBias := (avgFin7 a.smallBias b.smallBias).1 } : AgentState L K)).phase.val
        = a.phase.val := by
      unfold clockCounterStep
      rw [if_neg (show ¬ (({ a with smallBias := (avgFin7 a.smallBias b.smallBias).1 }
        : AgentState L K).role = .clock) from by rw [show _ = a.role from rfl, hmain.1]; decide)]
    have hval : (Phase1Transition L K a b).1.phase.val ≤ a.phase.val + 1 := by
      simp only [Phase1Transition, hmain, and_self, if_true]
      rw [hccs]
    exact hval
  · have hval : (Phase1Transition L K a b).1.phase.val
        = (clockCounterStep L K a).phase.val := by
      simp only [Phase1Transition, hmain, if_false]
    rw [hval]
    exact clockCounterStep_phase_le_succ_of_wf a hwf hle

/-- Phase 4 left output advances by `≤ +1` (`advancePhase` or identity). -/
theorem Phase4Transition_left_phase_le_succ (a b : AgentState L K) :
    (Phase4Transition L K a b).1.phase.val ≤ a.phase.val + 1 := by
  unfold Phase4Transition; dsimp; split_ifs <;>
    first
      | exact advancePhase_phase_le_succ a
      | omega

end SeamNoOvershoot

end ExactMajority
