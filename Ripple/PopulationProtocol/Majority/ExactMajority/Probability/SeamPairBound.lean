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

/-- When the responder's phase is `≤` the initiator's, the epidemic leaves the
initiator's `counter`/`role` untouched (`runInitsBetween p p = id`, and both
epidemic branches preserve `after`'s `counter`/`role`); the phase is either
`a.phase` (non-error) or `10` (the error-to-backup branch). -/
theorem phaseEpidemicUpdate_left_id_of_ge (a b : AgentState L K)
    (hba : b.phase.val ≤ a.phase.val) :
    (phaseEpidemicUpdate L K a b).1.counter = a.counter
    ∧ (phaseEpidemicUpdate L K a b).1.role = a.role
    ∧ ((phaseEpidemicUpdate L K a b).1.phase = a.phase
        ∨ (phaseEpidemicUpdate L K a b).1.phase.val = 10) := by
  unfold phaseEpidemicUpdate
  have hmax : max a.phase b.phase = a.phase := by
    apply max_eq_left; exact Fin.le_def.mpr hba
  simp only [hmax]
  have hself : runInitsBetween L K a.phase.val a.phase.val { a with phase := a.phase }
      = a := by
    rw [runInitsBetween_self_api]
  split_ifs with h
  · rw [hself]
    refine ⟨by simp, by simp, ?_⟩
    by_cases ha10 : a.phase.val < 10
    · right
      exact phase10EpidemicEntry_phase_val_of_before_lt_10 (L := L) (K := K) a a ha10
    · left
      have : ¬ a.phase.val < 10 := ha10
      have hval : (phase10EpidemicEntry L K a a).phase.val = a.phase.val := by
        simp [phase10EpidemicEntry, this]
      exact Fin.ext hval
  · rw [hself]; exact ⟨rfl, rfl, Or.inl rfl⟩

/-- Symmetric right-side version of `phaseEpidemicUpdate_left_id_of_ge`. -/
theorem phaseEpidemicUpdate_right_id_of_ge (a b : AgentState L K)
    (hab : a.phase.val ≤ b.phase.val) :
    (phaseEpidemicUpdate L K a b).2.counter = b.counter
    ∧ (phaseEpidemicUpdate L K a b).2.role = b.role
    ∧ ((phaseEpidemicUpdate L K a b).2.phase = b.phase
        ∨ (phaseEpidemicUpdate L K a b).2.phase.val = 10) := by
  unfold phaseEpidemicUpdate
  have hmax : max a.phase b.phase = b.phase := by
    apply max_eq_right; exact Fin.le_def.mpr hab
  simp only [hmax]
  have hself : runInitsBetween L K b.phase.val b.phase.val { b with phase := b.phase }
      = b := by
    rw [runInitsBetween_self_api]
  split_ifs with h
  · rw [hself]
    refine ⟨by simp, by simp, ?_⟩
    by_cases hb10 : b.phase.val < 10
    · right
      exact phase10EpidemicEntry_phase_val_of_before_lt_10 (L := L) (K := K) b b hb10
    · left
      have hval : (phase10EpidemicEntry L K b b).phase.val = b.phase.val := by
        simp [phase10EpidemicEntry, hb10]
      exact Fin.ext hval
  · rw [hself]; exact ⟨rfl, rfl, Or.inl rfl⟩

/-- For a clock initiator, the Phase-1 dispatch leaves the LEFT output equal to
`clockCounterStep` (the main–main averaging pre-step never touches a clock). -/
theorem Phase1Transition_left_clock (c t : AgentState L K) (hc : c.role = .clock) :
    (Phase1Transition L K c t).1 = clockCounterStep L K c := by
  unfold Phase1Transition
  have hnm : ¬ (c.role = .main ∧ t.role = .main) := by
    rintro ⟨h, _⟩; rw [hc] at h; exact absurd h (by decide)
  simp only [hnm, if_false]

/-- For a clock initiator, the Phase-5 dispatch leaves the LEFT output equal to
`stdCounterSubroutine` (the reserve/main sampling pre-step never touches a clock). -/
theorem Phase5Transition_left_clock (c t : AgentState L K) (hc : c.role = .clock) :
    (Phase5Transition L K c t).1 = stdCounterSubroutine L K c := by
  unfold Phase5Transition
  simp only [hc, reduceCtorEq, false_and, and_false, ↓reduceIte]

/-- For a clock initiator, the Phase-6 dispatch leaves the LEFT output equal to
`stdCounterSubroutine`. -/
theorem Phase6Transition_left_clock (c t : AgentState L K) (hc : c.role = .clock) :
    (Phase6Transition L K c t).1 = stdCounterSubroutine L K c := by
  unfold Phase6Transition
  simp only [hc, reduceCtorEq, false_and, and_false, ↓reduceIte]

/-- For a clock initiator, the Phase-7 dispatch leaves the LEFT output equal to
`stdCounterSubroutine` (the main–main cancel pre-step never touches a clock). -/
theorem Phase7Transition_left_clock (c t : AgentState L K) (hc : c.role = .clock) :
    (Phase7Transition L K c t).1 = stdCounterSubroutine L K c := by
  unfold Phase7Transition
  simp only [hc, reduceCtorEq, false_and, ↓reduceIte]

/-- For a clock initiator, the Phase-8 dispatch leaves the LEFT output equal to
`stdCounterSubroutine` (the main–main absorb pre-step never touches a clock). -/
theorem Phase8Transition_left_clock (c t : AgentState L K) (hc : c.role = .clock) :
    (Phase8Transition L K c t).1 = stdCounterSubroutine L K c := by
  unfold Phase8Transition
  simp only [hc, reduceCtorEq, false_and, ↓reduceIte]

/-- **Decrement bound for `stdCounterSubroutine` on a clock at the destination
phase.**  If `c` is a clock at phase `p+1`, then
`seamClockSummand p s (stdCounterSubroutine c) ≤ eˢ · seamClockSummand p s c`
(for `s ≥ 0`): a positive-counter clock decrements (`exp(-s(k-1)) = eˢ·exp(-sk)`),
a zero-counter clock advances out of phase `p+1` (output summand `0`). -/
theorem seamClockSummand_stdCounterSubroutine_le (p : ℕ) (s : ℝ) (hs : 0 ≤ s)
    (c : AgentState L K) (hrole : c.role = .clock) (hphase : c.phase.val = p + 1) :
    seamClockSummand (L := L) (K := K) p s (stdCounterSubroutine L K c)
      ≤ ENNReal.ofReal (Real.exp s) * seamClockSummand (L := L) (K := K) p s c := by
  have he1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (Real.exp s) := by
    rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal (Real.one_le_exp hs)
  have hsrc : seamClockSummand (L := L) (K := K) p s c
      = ENNReal.ofReal (Real.exp (-(s * (c.counter.val : ℝ)))) := by
    unfold seamClockSummand; rw [if_pos ⟨hrole, hphase⟩]
  -- any seam summand is ≤ 1 (exp(-s·counter) ≤ exp(0) = 1 for s ≥ 0).
  have hle_one : ∀ a : AgentState L K,
      seamClockSummand (L := L) (K := K) p s a ≤ 1 := by
    intro a
    unfold seamClockSummand
    by_cases hcond : a.role = .clock ∧ a.phase.val = p + 1
    · rw [if_pos hcond, ← ENNReal.ofReal_one]
      apply ENNReal.ofReal_le_ofReal
      rw [show (1 : ℝ) = Real.exp 0 from (Real.exp_zero).symm]
      apply Real.exp_le_exp.mpr
      have : (0 : ℝ) ≤ s * (a.counter.val : ℝ) := by positivity
      linarith
    · rw [if_neg hcond]; exact zero_le'
  unfold stdCounterSubroutine
  by_cases hctr : c.counter.val = 0
  · -- advance: source summand = 1 (counter 0), so eˢ·source = eˢ ≥ 1 ≥ output summand.
    rw [dif_pos hctr]
    have hsrc1 : seamClockSummand (L := L) (K := K) p s c = 1 := by
      rw [hsrc, hctr]; simp
    rw [hsrc1, mul_one]
    exact le_trans (hle_one _) he1
  · -- decrement
    rw [dif_neg hctr]
    have hout_role : ({ c with counter := ⟨c.counter.val - 1, by omega⟩ } : AgentState L K).role = .clock := hrole
    have hout_phase : ({ c with counter := ⟨c.counter.val - 1, by omega⟩ } : AgentState L K).phase.val = p + 1 := hphase
    have hout : seamClockSummand (L := L) (K := K) p s
        { c with counter := ⟨c.counter.val - 1, by omega⟩ }
        = ENNReal.ofReal (Real.exp (-(s * ((c.counter.val - 1 : ℕ) : ℝ)))) := by
      unfold seamClockSummand; rw [if_pos ⟨hout_role, hout_phase⟩]
    rw [hout, hsrc]
    rw [← ENNReal.ofReal_mul (Real.exp_nonneg _), ← Real.exp_add]
    apply ENNReal.ofReal_le_ofReal
    apply Real.exp_le_exp.mpr
    have h1 : (1 : ℕ) ≤ c.counter.val := Nat.one_le_iff_ne_zero.mpr hctr
    have hcast : ((c.counter.val - 1 : ℕ) : ℝ) = (c.counter.val : ℝ) - 1 := by
      rw [Nat.cast_sub h1]; simp
    rw [hcast]; nlinarith [hs]

/-- `clockCounterStep` on a clock at the destination phase satisfies the same
decrement bound (it IS `stdCounterSubroutine` on a clock). -/
theorem seamClockSummand_clockCounterStep_le (p : ℕ) (s : ℝ) (hs : 0 ≤ s)
    (c : AgentState L K) (hrole : c.role = .clock) (hphase : c.phase.val = p + 1) :
    seamClockSummand (L := L) (K := K) p s (clockCounterStep L K c)
      ≤ ENNReal.ofReal (Real.exp s) * seamClockSummand (L := L) (K := K) p s c := by
  unfold clockCounterStep
  rw [if_pos hrole]
  exact seamClockSummand_stdCounterSubroutine_le p s hs c hrole hphase

/-! ### Immigration: a clock dragged up into a reset-destination phase has full counter.

The epidemic's `runInitsBetween oldP q` ends by applying `phaseInit q` (q is the
maximum of `(oldP, q] ∩ [0,10]`).  For `q ∈ {1,5,6,7,8}`, `phaseInit q` resets a
clock's counter to full `50(L+1)`.  We prove that the filter list ends in `q`, then
that the fold's last step is `phaseInit q`, then the reset. -/

/-- The `(oldP, q] ∩ range 11` filter list ends in `q` when `oldP < q ≤ 10`: the
underlying `range 11` is `Sorted (· < ·)`, filter preserves order, and `q` is the
unique maximal satisfier. -/
theorem runInitsBetween_clock_counter_reset (oldP : ℕ) (q : ℕ)
    (a : AgentState L K) (ha : a.role = .clock) (hlt : oldP < q)
    (hq : CounterTimedPhase q) :
    (runInitsBetween L K oldP q a).counter.val = 50 * (L + 1) := by
  -- `q ∈ {1,5,6,7,8}`, `oldP < q`; the filter list ends in `q`, the fold applies
  -- `phaseInit q` last (clock role preserved through the prefix), resetting to full.
  have key : ∀ (lst : List ℕ), lst = (List.range 11).filter (fun k => oldP < k ∧ k ≤ q) →
      ∃ pre : List ℕ, lst = pre ++ [q] ∧ ∀ x ∈ pre, x < q := by
    intro lst hlst
    refine ⟨(List.range 11).filter (fun k => oldP < k ∧ k ≤ q - 1), ?_, ?_⟩
    · rw [hlst]
      rcases hq with h | h | h | h | h <;> subst h <;>
        (interval_cases oldP <;> decide)
    · intro x hx
      rw [List.mem_filter] at hx
      simp only [decide_eq_true_eq] at hx
      omega
  obtain ⟨pre, hpre, hprelt⟩ := key _ rfl
  unfold runInitsBetween
  rw [hpre, List.foldl_append]
  simp only [List.foldl_cons, List.foldl_nil]
  have hq11 : q < 11 := by rcases hq with h | h | h | h | h <;> omega
  rw [dif_pos hq11]
  -- the prefix fold preserves the clock role (folding `phaseInit` keeps clocks clocks)
  have hrole : ∀ (l : List ℕ) (c : AgentState L K), c.role = .clock →
      (List.foldl (fun acc k => if h : k < 11 then phaseInit L K ⟨k, h⟩ acc else acc)
        c l).role = .clock := by
    intro l
    induction l with
    | nil => intro c hc; simpa using hc
    | cons k ks IH =>
      intro c hc
      simp only [List.foldl_cons]
      apply IH
      by_cases hk : k < 11
      · rw [dif_pos hk]; exact phaseInit_clock_role_eq L K ⟨k, hk⟩ c hc
      · rw [dif_neg hk]; exact hc
  apply phaseInit_clock_counter_reset ⟨q, hq11⟩ _ (hrole pre a ha) hq

end SeamNoOvershoot

end ExactMajority
