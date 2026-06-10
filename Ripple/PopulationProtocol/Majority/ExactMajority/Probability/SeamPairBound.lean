/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Doty §6 — the SEAM per-pair output bound (`hpair`)

PROBE FILE — discharging `SeamNoOvershoot`'s carried `hpair`.
-/

import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.SeamNoOvershoot

namespace ExactMajority

open scoped ENNReal NNReal Real BigOperators

namespace SeamNoOvershoot

variable {L K : ℕ}

/-- A clock summand at counter `c` equals `ofReal(exp(-s·c))` (clock + phase=p+1). -/
example (p : ℕ) (s : ℝ) (a : AgentState L K)
    (hrole : a.role = .clock) (hphase : a.phase.val = p + 1) :
    seamClockSummand (L := L) (K := K) p s a
      = ENNReal.ofReal (Real.exp (-(s * (a.counter.val : ℝ)))) := by
  unfold seamClockSummand
  rw [if_pos ⟨hrole, hphase⟩]

/-- A non-(clock-at-p+1) summand is 0. -/
example (p : ℕ) (s : ℝ) (a : AgentState L K)
    (h : ¬ (a.role = .clock ∧ a.phase.val = p + 1)) :
    seamClockSummand (L := L) (K := K) p s a = 0 := by
  unfold seamClockSummand
  rw [if_neg h]

/-- freshVal = clock summand at full counter. -/
example (p : ℕ) (s : ℝ) (a : AgentState L K)
    (hrole : a.role = .clock) (hphase : a.phase.val = p + 1)
    (hctr : a.counter.val = 50 * (L + 1)) :
    seamClockSummand (L := L) (K := K) p s a = freshVal (L := L) s := by
  unfold seamClockSummand freshVal
  rw [if_pos ⟨hrole, hphase⟩, hctr]

/-- `seamClockSummand` reads only `role`, `phase.val`, `counter.val`. -/
theorem seamClockSummand_congr (p : ℕ) (s : ℝ) (a a' : AgentState L K)
    (hrole : a.role = a'.role) (hphase : a.phase.val = a'.phase.val)
    (hctr : a.counter.val = a'.counter.val) :
    seamClockSummand (L := L) (K := K) p s a
      = seamClockSummand (L := L) (K := K) p s a' := by
  unfold seamClockSummand
  rw [hrole, hphase, hctr]

/-- `seamClockSummand` is invariant under `finishPhase10Entry` (which preserves
`role`/`phase.val`/`counter`). -/
theorem seamClockSummand_finishPhase10Entry (p : ℕ) (s : ℝ)
    (before after : AgentState L K) :
    seamClockSummand (L := L) (K := K) p s (finishPhase10Entry L K before after)
      = seamClockSummand (L := L) (K := K) p s after := by
  apply seamClockSummand_congr
  · simp
  · simp
  · rw [finishPhase10Entry_counter]


/-- For a counter-reset destination phase `q ∈ {1,5,6,7,8}`, `phaseInit q` resets
a clock's counter to the full `50(L+1)`. -/
theorem phaseInit_clock_counter_reset (q : Fin 11) (a : AgentState L K)
    (ha : a.role = .clock) (hq : CounterTimedPhase q.val) :
    (phaseInit L K q a).counter.val = 50 * (L + 1) := by
  unfold phaseInit
  rcases hq with h | h | h | h | h <;>
    rw [h] <;>
    simp only [ha, reduceCtorEq, ↓reduceDIte, ↓reduceIte] <;>
    norm_num

end SeamNoOvershoot

end ExactMajority
