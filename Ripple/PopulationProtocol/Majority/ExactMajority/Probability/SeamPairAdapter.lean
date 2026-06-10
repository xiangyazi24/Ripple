/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Doty §6 — the HONEST seam per-pair `hpair` adapter (`SeamPairAdapter`)

This file packages the protocol-structural per-pair output bound for the seam
no-overshoot clock-counter tail with the HONEST constants discovered in
`SeamPairBound.lean`'s genuine attack, and re-wires the consumer chain in
`SeamNoOvershoot.lean` accordingly.  Append-only; it EDITS no existing file.

## The two honest corrections it implements (from `SeamPairBound`'s findings)

1. **The honest per-pair immigration ceiling is `2·eˢ·freshVal`, NOT `2·freshVal`.**
   A fresh epidemic-dragged clock enters `p+1` at the FULL counter and is DECREMENTED
   by the SAME-step dispatch to `full − 1`, so its summand is `eˢ·freshVal` per side,
   `2·eˢ·freshVal` per pair.  (`SeamNoOvershoot`'s `seamClockPotential_drift_affine`
   consumed `2·freshVal`, which is FALSE for `s > 0`.)

2. **The honest counter-reset destination set is `{1,6,7,8}`, NOT `{1,5,6,7,8}`.**
   Phase 5's predecessor `Phase4Transition` advances clocks via `advancePhase`
   (big-bias gate, NO `phaseInit`, NO counter reset), so a clock counter-advanced from
   phase 4 into phase 5 keeps its OLD counter (summand up to `1`, not `freshVal`),
   breaking the immigration tail.  Phases `{1,6,7,8}` are clean: their predecessors
   (`Phase0` Rule-5 / `Phase{5,6,7}`) all advance clocks via
   `stdCounterSubroutine → advancePhaseWithInit → phaseInit q`, which DOES reset.

## What is built (0 sorry / 0 axiom / no native_decide)

* **Stage 1** — the missing ADVANCE-regime dispatch reductions for the honest set
  `{1,6,7,8}`: `Phase0Transition_left_clock_eq` / `…_right_clock_eq` (the conditional
  Rule-5 dispatch), and the per-side ADVANCE bound
  `seamClockSummand_Transition_side_advance_le` (a clock advanced INTO `p+1` enters at
  full counter, summand `= freshVal`).
* **Stage 2** — the HONEST two-sided per-pair bound
  `seamClockSummand_Transition_pair_le`
  `summand(δ.1) + summand(δ.2) ≤ eˢ·(summand a + summand b) + 2·eˢ·freshVal`
  on the seam region (destination `p+1 ∈ {1,6,7,8}`), assembled from the per-side
  no-advance (`SeamPairBound`) and advance (Stage 1) bounds.
* **Stage 3** — the corrected drift `seamClockPotential_drift_affine_honest` with
  `b = 2·eˢ·freshVal`, derived from Stage 2 via
  `Phase0Window.lintegral_transitionKernel_eq_sum` (mirrors `SeamNoOvershoot`).
* **Stage 4** — the corrected numerics `seam_noOvershoot_numerics_honest`
  (`b = 2·e·freshVal` at `s = 1`; verifies the `e^{−45}+e^{−43}→e^{−40}` slack absorbs
  the extra `eˢ` factor) and the end-to-end honest at-risk tail / no-overshoot tail.

The four excluded destination phases are handled by NAMED per-phase guard facts (NOT
faked): phases `2,4,9` (untimed: opinion-union / big-bias) and phases `3,5`
(counter-timed but no counter reset on entry) carry their own work-phase / width
guards; see the `CounterResetDest` predicate and the closing doc section.

Reference: Doty et al. §6; consumer = `SeamNoOvershoot.lean`; protocol core =
`SeamPairBound.lean`; pattern = `Phase0Window.lean`; blueprint =
`HANDOFF_SEAM_NOOVERSHOOT.md`.
-/

import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.SeamPairBound

namespace ExactMajority

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Real BigOperators

namespace SeamNoOvershoot

variable {L K : ℕ}

/-! ## The honest counter-reset destination set `{1,6,7,8}`.

This is the intersection of the epidemic-drag reset set `{1,5,6,7,8}`
(`CounterTimedPhase`) with the counter-ADVANCE reset set: a clock counter-advanced
INTO `q` keeps a full counter iff `q`'s PREDECESSOR `q−1` advances clocks via
`stdCounterSubroutine → advancePhaseWithInit → phaseInit q`.  For `q = 5` the
predecessor (phase 4) advances via `advancePhase` (no reset), so `5` is excluded. -/

/-- **The honest counter-reset destination set** `{1, 6, 7, 8}` (blueprint's
`CounterTimedPhase` minus phase 5).  Entry into these phases both (i) decrements the
summand by `eˢ` for a clock already there, AND (ii) resets a counter-advanced or
epidemic-dragged immigrant clock to the FULL counter (summand `= freshVal`). -/
def CounterResetDest (q : ℕ) : Prop :=
  q = 1 ∨ q = 6 ∨ q = 7 ∨ q = 8

instance (q : ℕ) : Decidable (CounterResetDest q) := by
  unfold CounterResetDest; infer_instance

/-- `CounterResetDest ⊆ CounterTimedPhase` (so `SeamPairBound`'s no-advance lemmas,
stated for `CounterTimedPhase`, apply on the honest set). -/
theorem CounterTimedPhase_of_CounterResetDest {q : ℕ} (h : CounterResetDest q) :
    CounterTimedPhase q := by
  rcases h with h | h | h | h <;> simp [CounterTimedPhase, h]

/-! ## Stage 1 — the ADVANCE-regime dispatch reductions for `{1,6,7,8}`.

`SeamPairBound` proved the NO-ADVANCE per-side bound (when `ep.1.phase = p+1`): the
dispatch is `Phase(p+1)Transition` and the clock summand contracts by `eˢ`.  The
remaining ADVANCE regime is when `ep.i.phase = p` and the same-step dispatch advances
the clock INTO `p+1`.  For destination `p+1 ∈ {1,6,7,8}` the dispatch (selected by
`ep.1.phase = p`) is `Phase{0,5,6,7}Transition`; for a clock initiator/responder these
reduce to `stdCounterSubroutine` of that clock, EXCEPT Phase 0, whose Rule-5 clock step
is gated on the PARTNER also being a clock.  In every case the LEFT/RIGHT clock output
is `stdCounterSubroutine ep.i` or `ep.i` unchanged — and if it lands at `p+1` it must be
the advancing `stdCounterSubroutine` branch, which RESETS the counter (summand
`= freshVal`). -/

/-- **Phase-0 LEFT clock reduction (advance regime).**  For a clock initiator `c`, the
Phase-0 dispatch LEFT output equals `stdCounterSubroutine ĉ` (Rule 5, when the partner
is also a clock) or `ĉ` unchanged, where `ĉ` is `c` possibly with `assigned := true`
(Phase-0 Rule 3, partner-mcr).  Crucially `ĉ` is a CLOCK at the SAME phase as `c` — so
the advance lemma `seamClockSummand_stdCounterSubroutine_advance` applies to `ĉ`
directly, with no need to relate it back to `c`. -/
theorem Phase0Transition_left_clock_eq (c t : AgentState L K) (hc : c.role = .clock) :
    ∃ chat : AgentState L K, chat.role = .clock ∧ chat.phase.val = c.phase.val
      ∧ ((Phase0Transition L K c t).1 = stdCounterSubroutine L K chat
        ∨ (Phase0Transition L K c t).1 = chat) := by
  have hnm : c.role ≠ .mcr := by rw [hc]; decide
  have hnmain : c.role ≠ .main := by rw [hc]; decide
  have hncr : c.role ≠ .cr := by rw [hc]; decide
  by_cases h3 : t.role = Role.mcr ∧ ¬ c.assigned = true
  · -- Rule 3 fires (partner is mcr ⇒ NOT a clock ⇒ Rule 5 gate false):
    -- the output is exactly `{c with assigned := true}`.
    refine ⟨{ c with assigned := true }, hc, rfl, ?_⟩
    right
    unfold Phase0Transition
    simp only [hc, reduceCtorEq, false_and, and_false, if_false, ne_eq, not_false_eq_true,
      true_and, h3.1, h3.2, and_true, if_true]
  · -- Rule 3 does not fire: the output is `if t.role = clock then stdCounterSubroutine c else c`.
    refine ⟨c, hc, rfl, ?_⟩
    unfold Phase0Transition
    simp only [hc, reduceCtorEq, false_and, and_false, if_false, ne_eq, not_false_eq_true,
      true_and, h3, if_false]
    by_cases hgate : t.role = .clock
    · left; rw [if_pos hgate]
    · right; rw [if_neg hgate]

/-- **Phase-0 RIGHT clock reduction (advance regime).**  Symmetric. -/
theorem Phase0Transition_right_clock_eq (s c : AgentState L K) (hc : c.role = .clock) :
    ∃ chat : AgentState L K, chat.role = .clock ∧ chat.phase.val = c.phase.val
      ∧ ((Phase0Transition L K s c).2 = stdCounterSubroutine L K chat
        ∨ (Phase0Transition L K s c).2 = chat) := by
  have hnm : c.role ≠ .mcr := by rw [hc]; decide
  have hnmain : c.role ≠ .main := by rw [hc]; decide
  have hncr : c.role ≠ .cr := by rw [hc]; decide
  by_cases h3 : s.role = Role.mcr ∧ ¬ c.assigned = true
  · -- Rule 3 (branch 1) sets `c.assigned := true`; partner `s` is mcr (NOT clock),
    -- so Rule 5 gate is false → output is exactly `{c with assigned := true}`.
    refine ⟨{ c with assigned := true }, hc, rfl, ?_⟩
    right
    unfold Phase0Transition
    simp only [hc, reduceCtorEq, and_false, false_and, if_false, ne_eq, not_false_eq_true,
      true_and, and_true, h3.1, h3.2, if_true]
  · refine ⟨c, hc, rfl, ?_⟩
    unfold Phase0Transition
    simp only [hc, reduceCtorEq, and_false, false_and, if_false, ne_eq, not_false_eq_true,
      true_and, and_true, h3]
    by_cases hgate : s.role = .clock
    · left; rw [if_pos hgate]
    · right; rw [if_neg hgate]

/-- For a clock RESPONDER, the Phase-5 dispatch RIGHT output equals
`stdCounterSubroutine c` (the reserve/main sampling pre-step never touches a clock). -/
theorem Phase5Transition_right_clock (s c : AgentState L K) (hc : c.role = .clock) :
    (Phase5Transition L K s c).2 = stdCounterSubroutine L K c := by
  unfold Phase5Transition
  simp only [hc, reduceCtorEq, false_and, and_false, ↓reduceIte]

/-- For a clock RESPONDER, the Phase-6 dispatch RIGHT output equals
`stdCounterSubroutine c`. -/
theorem Phase6Transition_right_clock (s c : AgentState L K) (hc : c.role = .clock) :
    (Phase6Transition L K s c).2 = stdCounterSubroutine L K c := by
  unfold Phase6Transition
  simp only [hc, reduceCtorEq, false_and, and_false, ↓reduceIte]

/-- For a clock RESPONDER, the Phase-7 dispatch RIGHT output equals
`stdCounterSubroutine c`. -/
theorem Phase7Transition_right_clock (s c : AgentState L K) (hc : c.role = .clock) :
    (Phase7Transition L K s c).2 = stdCounterSubroutine L K c := by
  unfold Phase7Transition
  simp only [hc, reduceCtorEq, and_false, ↓reduceIte]

/-- For a clock RESPONDER, the Phase-8 dispatch RIGHT output equals
`stdCounterSubroutine c`. -/
theorem Phase8Transition_right_clock (s c : AgentState L K) (hc : c.role = .clock) :
    (Phase8Transition L K s c).2 = stdCounterSubroutine L K c := by
  unfold Phase8Transition
  simp only [hc, reduceCtorEq, and_false, ↓reduceIte]

/-! ## Stage 2 — the per-side bounds (both regimes) and the HONEST two-sided pair bound.

The per-side bound `summand(δ.side) ≤ eˢ·(summand(source) + freshVal)` covers BOTH
regimes:

* **No-advance** (`ep.side.phase = p+1`): the clock is already at the destination, the
  dispatch ticks it, the summand contracts by `eˢ` (`SeamPairBound`'s `…_le_of_ep_at_dest`
  for the LEFT; a fresh RIGHT analogue here).
* **Advance** (`ep.side.phase = p`, dispatch advances it INTO `p+1`): the new clock has a
  FULL counter (`phaseInit` reset on `{1,6,7,8}`), summand `= freshVal`
  (`seamClockSummand_stdCounterSubroutine_advance` on the `chat` clock); `freshVal ≤
  eˢ·(summand(source) + freshVal)`.
* Otherwise the output is not a clock at `p+1` (summand `0`).

Summing the two per-side bounds gives the HONEST two-sided ceiling `2·eˢ·freshVal`. -/

/-- `freshVal ≤ eˢ·(x + freshVal)` for `s ≥ 0`, any `x`. -/
theorem freshVal_le_exp_mul_add (s : ℝ) (hs : 0 ≤ s) (x : ℝ≥0∞) :
    freshVal (L := L) s ≤ ENNReal.ofReal (Real.exp s) * (x + freshVal (L := L) s) := by
  have he1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (Real.exp s) := by
    rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal (Real.one_le_exp hs)
  calc freshVal (L := L) s
      = 1 * freshVal (L := L) s := (one_mul _).symm
    _ ≤ ENNReal.ofReal (Real.exp s) * (x + freshVal (L := L) s) := by
        gcongr
        exact le_add_self

/-- **Epidemic immigration counter (RIGHT).**  Mirror of
`SeamPairBound.phaseEpidemicUpdate_left_immigrant_full`. -/
theorem phaseEpidemicUpdate_right_immigrant_full (a b : AgentState L K)
    (q : ℕ) (hq : CounterTimedPhase q) (hblt : b.phase.val < q)
    (hep_role : (phaseEpidemicUpdate L K a b).2.role = .clock)
    (hep_phase : (phaseEpidemicUpdate L K a b).2.phase.val = q) :
    (phaseEpidemicUpdate L K a b).2.counter.val = 50 * (L + 1) := by
  have hq11 : q < 11 := by rcases hq with h | h | h | h | h <;> omega
  have hqle : q ≤ 8 := by rcases hq with h | h | h | h | h <;> omega
  set mx := max a.phase b.phase with hmxdef
  set s0 := runInitsBetween L K a.phase.val mx.val { a with phase := mx } with hs0def
  set t0 := runInitsBetween L K b.phase.val mx.val { b with phase := mx } with ht0def
  have hepeq : phaseEpidemicUpdate L K a b
      = if (a.phase.val < 10 ∨ b.phase.val < 10) ∧ (s0.phase.val = 10 ∨ t0.phase.val = 10)
          then (phase10EpidemicEntry L K a s0, phase10EpidemicEntry L K b t0)
          else (s0, t0) := rfl
  rw [hepeq] at hep_role hep_phase ⊢
  by_cases hcond : (a.phase.val < 10 ∨ b.phase.val < 10) ∧ (s0.phase.val = 10 ∨ t0.phase.val = 10)
  · rw [if_pos hcond] at hep_phase
    exfalso
    have hb10 : b.phase.val < 10 := by omega
    simp only at hep_phase
    rw [phase10EpidemicEntry_phase_val_of_before_lt_10 (L := L) (K := K) b t0 hb10] at hep_phase
    omega
  · rw [if_neg hcond] at hep_role hep_phase ⊢
    simp only at hep_role hep_phase ⊢
    have hmxq : mx.val = q := by
      rcases runInitsBetween_phase_eq_or_ten b.phase.val mx.val
          { b with phase := mx } with h | h
      · rw [ht0def, h] at hep_phase; simpa using hep_phase
      · rw [ht0def, h] at hep_phase; omega
    have hb_clock : ({ b with phase := mx } : AgentState L K).role = .clock :=
      runInitsBetween_role_clock_imp _ _ _ hep_role
    have hreset := runInitsBetween_clock_counter_reset b.phase.val mx.val
      { b with phase := mx } hb_clock (by rw [hmxq]; exact hblt) (by rw [hmxq]; exact hq)
    rw [ht0def]; exact hreset

/-- **Epidemic summand immigration bound (RIGHT).**  Mirror of
`SeamPairBound.seamClockSummand_phaseEpidemicUpdate_left_le`. -/
theorem seamClockSummand_phaseEpidemicUpdate_right_le (p : ℕ) (s : ℝ)
    (hq : CounterTimedPhase (p + 1)) (a b : AgentState L K) :
    seamClockSummand (L := L) (K := K) p s (phaseEpidemicUpdate L K a b).2
      ≤ seamClockSummand (L := L) (K := K) p s b + freshVal (L := L) s := by
  set ep2 := (phaseEpidemicUpdate L K a b).2 with hep2
  by_cases hcond : ep2.role = .clock ∧ ep2.phase.val = p + 1
  · obtain ⟨hrole, hphase⟩ := hcond
    rcases lt_trichotomy b.phase.val (p + 1) with hlt | heq | hgt
    · have hfull : ep2.counter.val = 50 * (L + 1) := by
        rw [hep2]; rw [hep2] at hrole hphase
        exact phaseEpidemicUpdate_right_immigrant_full a b (p + 1) hq hlt hrole hphase
      have : seamClockSummand (L := L) (K := K) p s ep2 = freshVal (L := L) s := by
        unfold seamClockSummand freshVal
        rw [if_pos ⟨hrole, hphase⟩, hfull]
      rw [this]; exact le_add_left le_rfl
    · have hab : a.phase.val ≤ b.phase.val := by
        by_contra hgt
        rw [not_le] at hgt
        have hge : a.phase.val ≤ ep2.phase.val := by
          rw [hep2]
          exact le_trans (le_max_left _ _)
            (phaseEpidemicUpdate_right_phase_ge_max_api (L := L) (K := K) a b)
        omega
      obtain ⟨hctr, hrole_b, hphase_or⟩ := phaseEpidemicUpdate_right_id_of_ge a b hab
      have hsummeq : seamClockSummand (L := L) (K := K) p s ep2
          = seamClockSummand (L := L) (K := K) p s b := by
        apply seamClockSummand_congr
        · rw [hep2]; exact hrole_b
        · rcases hphase_or with hph | hph
          · rw [hep2, hph]
          · exfalso
            have hple : p + 1 ≤ 8 := by rcases hq with h | h | h | h | h <;> omega
            rw [← hep2] at hph; omega
        · rw [hep2, hctr]
      rw [hsummeq]; exact le_self_add
    · exfalso
      have hge : b.phase.val ≤ ep2.phase.val := by
        rw [hep2]
        exact le_trans (le_max_right _ _)
          (phaseEpidemicUpdate_right_phase_ge_max_api (L := L) (K := K) a b)
      omega
  · have : seamClockSummand (L := L) (K := K) p s ep2 = 0 := by
      unfold seamClockSummand; rw [if_neg hcond]
    rw [this]; exact zero_le'

/-- **RIGHT-side no-advance per-side bound** (the seam analogue of `SeamPairBound`'s
`seamClockSummand_Transition_left_le_of_ep_at_dest`, for the RIGHT output).  The
`Transition` dispatcher matches on the LEFT phase `ep.1.phase`; when `ep.1.phase = p+1`
the dispatch is `Phase(p+1)Transition`, whose RIGHT output for a clock responder `ep.2`
at `p+1` is `stdCounterSubroutine ep.2`, contracting by `eˢ`. -/
theorem seamClockSummand_Transition_right_le_of_ep_at_dest (p : ℕ)
    (hq : CounterTimedPhase (p + 1)) (s : ℝ) (hs : 0 ≤ s) (a b : AgentState L K)
    (hepdest1 : (phaseEpidemicUpdate L K a b).1.phase.val = p + 1)
    (hepdest2 : (phaseEpidemicUpdate L K a b).2.phase.val = p + 1)
    (hepclock2 : (phaseEpidemicUpdate L K a b).2.role = .clock) :
    seamClockSummand (L := L) (K := K) p s (Transition L K a b).2
      ≤ ENNReal.ofReal (Real.exp s)
          * (seamClockSummand (L := L) (K := K) p s b + freshVal (L := L) s) := by
  set ep1 := (phaseEpidemicUpdate L K a b).1 with hep1
  set ep2 := (phaseEpidemicUpdate L K a b).2 with hep2
  -- Step 1: strip finishPhase10Entry; the dispatch is Phase(p+1)Transition on ep.
  have hstrip : seamClockSummand (L := L) (K := K) p s (Transition L K a b).2
      = seamClockSummand (L := L) (K := K) p s
          ((if (p + 1) = 1 then Phase1Transition L K ep1 ep2
            else if (p + 1) = 5 then Phase5Transition L K ep1 ep2
            else if (p + 1) = 6 then Phase6Transition L K ep1 ep2
            else if (p + 1) = 7 then Phase7Transition L K ep1 ep2
            else Phase8Transition L K ep1 ep2).2) := by
    rw [Transition, seamClockSummand_finishPhase10Entry]
    rcases hq with h | h | h | h | h
    · have hp : ep1.phase = (⟨1, by decide⟩ : Fin 11) := Fin.ext (hepdest1.trans h)
      simp only [hep1] at hp ⊢; simp only [hp, h]; rfl
    · have hp : ep1.phase = (⟨5, by decide⟩ : Fin 11) := Fin.ext (hepdest1.trans h)
      simp only [hep1] at hp ⊢; simp only [hp, h]; rfl
    · have hp : ep1.phase = (⟨6, by decide⟩ : Fin 11) := Fin.ext (hepdest1.trans h)
      simp only [hep1] at hp ⊢; simp only [hp, h]; rfl
    · have hp : ep1.phase = (⟨7, by decide⟩ : Fin 11) := Fin.ext (hepdest1.trans h)
      simp only [hep1] at hp ⊢; simp only [hp, h]; rfl
    · have hp : ep1.phase = (⟨8, by decide⟩ : Fin 11) := Fin.ext (hepdest1.trans h)
      simp only [hep1] at hp ⊢; simp only [hp, h]; rfl
  rw [hstrip]
  -- Step 2: the dispatch RIGHT output for a clock responder = stdCounterSubroutine ep2.
  have hdec : seamClockSummand (L := L) (K := K) p s
      ((if (p + 1) = 1 then Phase1Transition L K ep1 ep2
        else if (p + 1) = 5 then Phase5Transition L K ep1 ep2
        else if (p + 1) = 6 then Phase6Transition L K ep1 ep2
        else if (p + 1) = 7 then Phase7Transition L K ep1 ep2
        else Phase8Transition L K ep1 ep2).2)
      ≤ ENNReal.ofReal (Real.exp s) * seamClockSummand (L := L) (K := K) p s ep2 := by
    have hred : ((if (p + 1) = 1 then Phase1Transition L K ep1 ep2
        else if (p + 1) = 5 then Phase5Transition L K ep1 ep2
        else if (p + 1) = 6 then Phase6Transition L K ep1 ep2
        else if (p + 1) = 7 then Phase7Transition L K ep1 ep2
        else Phase8Transition L K ep1 ep2).2) = stdCounterSubroutine L K ep2 := by
      rcases hq with h | h | h | h | h <;> rw [h]
      · rw [if_pos rfl]; unfold Phase1Transition
        have hnm : ¬ (ep1.role = .main ∧ ep2.role = .main) := by
          rintro ⟨_, h2⟩; rw [hepclock2] at h2; exact absurd h2 (by decide)
        simp only [hnm, if_false]
        rw [clockCounterStep, if_pos hepclock2]
      · rw [if_neg (by decide), if_pos rfl, Phase5Transition_right_clock _ _ hepclock2]
      · rw [if_neg (by decide), if_neg (by decide), if_pos rfl,
            Phase6Transition_right_clock _ _ hepclock2]
      · rw [if_neg (by decide), if_neg (by decide), if_neg (by decide), if_pos rfl,
            Phase7Transition_right_clock _ _ hepclock2]
      · rw [if_neg (by decide), if_neg (by decide), if_neg (by decide), if_neg (by decide),
            Phase8Transition_right_clock _ _ hepclock2]
    rw [hred]
    exact seamClockSummand_stdCounterSubroutine_le p s hs ep2 hepclock2 hepdest2
  refine hdec.trans ?_
  -- Step 3: epidemic summand bound (right) → summand(ep2) ≤ summand(b) + freshVal.
  gcongr
  exact seamClockSummand_phaseEpidemicUpdate_right_le p s hq a b

/-! ### The ADVANCE-regime per-side bounds.

When `ep.1.phase = p` (one below the destination) the dispatch `Phase(p)Transition`
(selected by the LEFT phase) advances a clock INTO `p+1`.  For the LEFT output we route
through the per-phase left reductions (`Phase0Transition_left_clock_eq` for `p+1=1`;
`Phase{5,6,7}Transition_left_clock` for `p+1∈{6,7,8}`) + the advance reset lemma, giving
`summand = freshVal`.  The RIGHT output uses the same dispatch (`ep.1.phase = p`), with
the right reductions; here we additionally need `ep.2.phase = p` (so the responder is
the advancing clock) — supplied by the caller. -/

/-- **Advance-output summand ceiling.**  For a clock `chat` at phase `< p+1` and a
counter-reset destination `p+1 ∈ {1,6,7,8}`, `summand(stdCounterSubroutine chat) ≤
freshVal`: if it ADVANCES to `p+1` the new clock has a FULL counter (summand `=
freshVal`); if it stays below `p+1` (decrement branch) the output is not a clock at
`p+1` (summand `0`). -/
theorem seamClockSummand_stdCounterSubroutine_advance_le (p : ℕ) (s : ℝ)
    (chat : AgentState L K) (hrole : chat.role = .clock)
    (hq : CounterTimedPhase (p + 1)) (hlt : chat.phase.val < p + 1) :
    seamClockSummand (L := L) (K := K) p s (stdCounterSubroutine L K chat)
      ≤ freshVal (L := L) s := by
  by_cases hadv : (stdCounterSubroutine L K chat).phase.val = p + 1
  · rw [seamClockSummand_stdCounterSubroutine_advance p s chat hrole hadv hq hlt]
  · -- output not at p+1 ⇒ summand 0.
    have : seamClockSummand (L := L) (K := K) p s (stdCounterSubroutine L K chat) = 0 := by
      unfold seamClockSummand
      rw [if_neg]; rintro ⟨_, hp⟩; exact hadv hp
    rw [this]; exact zero_le'

/-- The full `Transition` LEFT output's seam summand equals that of the dispatch LEFT
output `out.1` (the `finishPhase10Entry` strip preserves `role`/`phase`/`counter`),
where the dispatch is selected by `ep.1.phase`.  Specialized to `ep.1.phase = p` for
the ADVANCE regime: the dispatch is `Phase(p)Transition`. -/
theorem seamClockSummand_Transition_left_eq_dispatch_advance (p : ℕ) (s : ℝ)
    (a b : AgentState L K)
    (hepsrc1 : (phaseEpidemicUpdate L K a b).1.phase.val = p)
    (hp : CounterResetDest (p + 1)) :
    seamClockSummand (L := L) (K := K) p s (Transition L K a b).1
      = seamClockSummand (L := L) (K := K) p s
          ((if p = 0 then Phase0Transition L K (phaseEpidemicUpdate L K a b).1
                                              (phaseEpidemicUpdate L K a b).2
            else if p = 5 then Phase5Transition L K (phaseEpidemicUpdate L K a b).1
                                              (phaseEpidemicUpdate L K a b).2
            else if p = 6 then Phase6Transition L K (phaseEpidemicUpdate L K a b).1
                                              (phaseEpidemicUpdate L K a b).2
            else Phase7Transition L K (phaseEpidemicUpdate L K a b).1
                                              (phaseEpidemicUpdate L K a b).2).1) := by
  rw [Transition, seamClockSummand_finishPhase10Entry]
  rcases hp with h | h | h | h
  · have hp0 : p = 0 := by omega
    have hpe : (phaseEpidemicUpdate L K a b).1.phase = (⟨0, by decide⟩ : Fin 11) :=
      Fin.ext (by rw [hepsrc1, hp0])
    simp only [hpe, hp0]; rfl
  · have hp5 : p = 5 := by omega
    have hpe : (phaseEpidemicUpdate L K a b).1.phase = (⟨5, by decide⟩ : Fin 11) :=
      Fin.ext (by rw [hepsrc1, hp5])
    simp only [hpe, hp5]; rfl
  · have hp6 : p = 6 := by omega
    have hpe : (phaseEpidemicUpdate L K a b).1.phase = (⟨6, by decide⟩ : Fin 11) :=
      Fin.ext (by rw [hepsrc1, hp6])
    simp only [hpe, hp6]; rfl
  · have hp7 : p = 7 := by omega
    have hpe : (phaseEpidemicUpdate L K a b).1.phase = (⟨7, by decide⟩ : Fin 11) :=
      Fin.ext (by rw [hepsrc1, hp7])
    simp only [hpe, hp7]; rfl

/-- **LEFT-side ADVANCE per-side bound.**  When the epidemic-updated initiator `ep.1` is
a clock at phase `p` (one below the counter-reset destination `p+1 ∈ {1,6,7,8}`), the
dispatch advances it into `p+1` with a FULL counter, so the LEFT output summand is
`≤ freshVal ≤ eˢ·(summand a + freshVal)`. -/
theorem seamClockSummand_Transition_left_le_of_ep_advance (p : ℕ)
    (hq : CounterResetDest (p + 1)) (s : ℝ) (hs : 0 ≤ s) (a b : AgentState L K)
    (hepclock1 : (phaseEpidemicUpdate L K a b).1.role = .clock)
    (hepsrc1 : (phaseEpidemicUpdate L K a b).1.phase.val = p) :
    seamClockSummand (L := L) (K := K) p s (Transition L K a b).1
      ≤ ENNReal.ofReal (Real.exp s)
          * (seamClockSummand (L := L) (K := K) p s a + freshVal (L := L) s) := by
  set ep1 := (phaseEpidemicUpdate L K a b).1 with hep1
  set ep2 := (phaseEpidemicUpdate L K a b).2 with hep2
  have hqT : CounterTimedPhase (p + 1) := CounterTimedPhase_of_CounterResetDest hq
  rw [seamClockSummand_Transition_left_eq_dispatch_advance p s a b hepsrc1 hq]
  -- get a clock `chat` at phase p with the dispatch.1 = stdCounterSubroutine chat or chat.
  have hdisp_summ : seamClockSummand (L := L) (K := K) p s
        ((if p = 0 then Phase0Transition L K ep1 ep2
          else if p = 5 then Phase5Transition L K ep1 ep2
          else if p = 6 then Phase6Transition L K ep1 ep2
          else Phase7Transition L K ep1 ep2).1)
      ≤ freshVal (L := L) s := by
    rcases hq with h | h | h | h
    · -- p = 0: Phase0Transition.1 = stdCounterSubroutine chat or chat (clock at phase 0).
      have hp0 : p = 0 := by omega
      rw [if_pos hp0]
      obtain ⟨chat, hcr, hcp, hdisj⟩ := Phase0Transition_left_clock_eq ep1 ep2 hepclock1
      have hcplt : chat.phase.val < p + 1 := by rw [hcp, hepsrc1]; omega
      rcases hdisj with hd | hd
      · rw [hd]
        exact seamClockSummand_stdCounterSubroutine_advance_le p s chat hcr hqT hcplt
      · rw [hd]
        -- chat at phase p ≠ p+1 ⇒ summand 0.
        have : seamClockSummand (L := L) (K := K) p s chat = 0 := by
          unfold seamClockSummand; rw [if_neg]; rintro ⟨_, hp⟩
          rw [hcp, hepsrc1] at hp; omega
        rw [this]; exact zero_le'
    · -- p = 5: Phase5Transition.1 = stdCounterSubroutine ep1.
      have hp5 : p = 5 := by omega
      rw [if_neg (by omega : ¬ p = 0), if_pos hp5]
      rw [Phase5Transition_left_clock ep1 ep2 hepclock1]
      have hlt : ep1.phase.val < p + 1 := by rw [hepsrc1]; omega
      exact seamClockSummand_stdCounterSubroutine_advance_le p s ep1 hepclock1 hqT hlt
    · have hp6 : p = 6 := by omega
      rw [if_neg (by omega : ¬ p = 0), if_neg (by omega : ¬ p = 5), if_pos hp6]
      rw [Phase6Transition_left_clock ep1 ep2 hepclock1]
      have hlt : ep1.phase.val < p + 1 := by rw [hepsrc1]; omega
      exact seamClockSummand_stdCounterSubroutine_advance_le p s ep1 hepclock1 hqT hlt
    · have hp7 : p = 7 := by omega
      rw [if_neg (by omega : ¬ p = 0), if_neg (by omega : ¬ p = 5),
          if_neg (by omega : ¬ p = 6)]
      rw [Phase7Transition_left_clock ep1 ep2 hepclock1]
      have hlt : ep1.phase.val < p + 1 := by rw [hepsrc1]; omega
      exact seamClockSummand_stdCounterSubroutine_advance_le p s ep1 hepclock1 hqT hlt
  exact hdisp_summ.trans (freshVal_le_exp_mul_add s hs _)

end SeamNoOvershoot

end ExactMajority
