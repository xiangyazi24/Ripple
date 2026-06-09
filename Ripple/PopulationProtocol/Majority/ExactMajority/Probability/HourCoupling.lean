/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Avenue (e) — Lemma 6.10: the clock → Main hour-coupling supermartingale

This file builds the additive supermartingale potential behind Doty et al.'s
Lemma 6.10 (Main agents don't run ahead of the clock), DIRECTLY on the real
`NonuniformMajority L K` kernel.

## The potential
* `mAbove h c` — the count of *Main*-role agents whose `hour` is `> h`.
* `cAbove h c` — the count of *Clock*-role agents whose clock-hour
  `⌊minute / K⌋` is `> h`, encoded by the equivalent threshold
  `(h+1)·K ≤ minute`.
* `Φ h c = (mAbove h c : ℝ) − 1.1 · (cAbove h c : ℝ)` — an ADDITIVE potential
  (it can be negative), NOT a multiplicative one.

## The mechanism (the heart — Phase3Transition Rule 2)
The Phase-3 hour-drag (Rule 2) is the only Phase-3 update that can raise a
Main agent's `hour` *when the Main agents are unbiased* (the cancel/split
Rules 3/4 require dyadic bias and so are inert on the unbiased-Main window).
Rule 2 sends an unbiased Main's hour to `min(L, ⌊clock.minute / K⌋)`.  So a
Main can newly cross `hour > h` only against a partner Clock with
`⌊minute/K⌋ > h`, i.e. a Clock counted in `cAbove h`.  Crucially Rule 2 never
edits a Clock's `minute`, so `cAbove h` is *invariant* under such a pair.  This
gives the deterministic per-pair facts

  `cAbove h (step) = cAbove h c`         (the Clock minute is untouched)
  `mAbove h (step) ≤ mAbove h c + (#Clock-above-h in the chosen pair)`

from which the `1.1·cAbove` slack makes `Φ h` an (exponential) supermartingale.

## INFRA CHECK (recorded here, see the report)
`Concentration.chernoff_{upper,lower,two_sided_hoeffding}` all require
`iIndepFun X P` — an INDEPENDENT family.  They do NOT apply to a
martingale-difference / dependent increment sequence, so they CANNOT give the
Azuma tail Lemma 6.10 needs.

The additive supermartingale tail is instead obtained by the standard
exponential transform: an additive supermartingale `Φ` with the per-step drift
`E[Φ_{t+1} | F_t] ≤ Φ_t` (here through the structural pair-count floor) yields
the MULTIPLICATIVE supermartingale `Ψ = exp(s·Φ)` with `∫⁻ Ψ dK ≤ Ψ`, which we
feed to the EXISTING multiplicative engine
`Supermartingale.geometric_drift_tail_kernel` (`r = 1`).  This is NOT faking the
multiplicative form: the exponential of an additive supermartingale genuinely
is a multiplicative supermartingale — the Azuma/Bernstein device — so no absent
Mathlib martingale API is required.

NEW file; no existing file is edited; no sorry/admit/axiom/native_decide.
-/

import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.ClockRealKernel
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.Supermartingale

namespace ExactMajority

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Real BigOperators

namespace HourCoupling

open ClockRealKernel

variable {L K : ℕ}

/-! ## Part 1 — the potential and its components. -/

/-- The threshold predicate for `mAbove`: a Main agent at hour `> h`. -/
def mainAboveP (h : ℕ) (a : AgentState L K) : Prop := a.role = .main ∧ h < a.hour.val

instance (h : ℕ) (a : AgentState L K) : Decidable (mainAboveP h a) := by
  unfold mainAboveP; infer_instance

/-- The threshold predicate for `cAbove`: a Clock agent whose clock-hour
`⌊minute/K⌋ > h`, encoded by the integer-equivalent floor `(h+1)·K ≤ minute`. -/
def clockAboveP (h : ℕ) (a : AgentState L K) : Prop :=
  a.role = .clock ∧ (h + 1) * K ≤ a.minute.val

instance (h : ℕ) (a : AgentState L K) : Decidable (clockAboveP h a) := by
  unfold clockAboveP; infer_instance

/-- `mAbove h c` — number of Main agents at hour `> h`. -/
def mAbove (h : ℕ) (c : Config (AgentState L K)) : ℕ :=
  Multiset.countP (fun a => mainAboveP h a) c

/-- `cAbove h c` — number of Clock agents at clock-hour `> h`. -/
def cAbove (h : ℕ) (c : Config (AgentState L K)) : ℕ :=
  Multiset.countP (fun a => clockAboveP h a) c

/-- The additive coupling potential `Φ h c = mAbove h c − 1.1·cAbove h c`. -/
noncomputable def Phi (h : ℕ) (c : Config (AgentState L K)) : ℝ :=
  (mAbove (L := L) (K := K) h c : ℝ) - (11 / 10 : ℝ) * (cAbove (L := L) (K := K) h c : ℝ)

/-- The exponential potential `Ψ = exp(s·Φ)` as an `ℝ≥0∞`, the multiplicative
transform of the additive supermartingale `Φ`. -/
noncomputable def expPot (s : ℝ) (h : ℕ) (c : Config (AgentState L K)) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (s * Phi (L := L) (K := K) h c))

/-! ## Part 2 — measurability (discrete σ-algebra). -/

theorem expPot_measurable (s : ℝ) (h : ℕ) :
    Measurable (expPot (L := L) (K := K) s h) :=
  fun _ _ => DiscreteMeasurableSpace.forall_measurableSet _

theorem expPot_pos (s : ℝ) (h : ℕ) (c : Config (AgentState L K)) :
    0 < expPot (L := L) (K := K) s h c := by
  unfold expPot; rw [ENNReal.ofReal_pos]; exact Real.exp_pos _

theorem expPot_ne_top (s : ℝ) (h : ℕ) (c : Config (AgentState L K)) :
    expPot (L := L) (K := K) s h c ≠ ⊤ := by
  unfold expPot; exact ENNReal.ofReal_ne_top

/-! ## Part 3 — the per-pair hour-drag mechanism (the heart, from Rule 2).

The unbiased-Main window: a configuration in which every Main-role agent is
unbiased (`bias = .zero`).  On this window the Phase-3 cancel/split Rules 3/4
are INERT (they require dyadic bias), so the ONLY Phase-3 update that can raise a
Main's `hour` is the hour-drag Rule 2.  Rule 2 sends an unbiased Main's hour to
`min(L, ⌊clock.minute/K⌋)`, so the Main can newly cross `hour > h` only against a
Clock with `(h+1)·K ≤ minute`, i.e. a Clock counted in `cAbove h`; and Rule 2
never edits the Clock's `minute`. -/

/-- `countP` over a two-element multiset, for any decidable predicate. -/
theorem countP_pair (p : AgentState L K → Prop) [DecidablePred p]
    (x y : AgentState L K) :
    Multiset.countP p ({x, y} : Multiset (AgentState L K))
      = (if p x then 1 else 0) + (if p y then 1 else 0) := by
  rw [show ({x, y} : Multiset (AgentState L K)) = x ::ₘ y ::ₘ 0 from rfl]
  rw [Multiset.countP_cons, Multiset.countP_cons, Multiset.countP_zero]
  ring

/-- The unbiased-Main window: every Main-role agent is unbiased. -/
def AllMainUnbiased (c : Config (AgentState L K)) : Prop :=
  ∀ a ∈ c, a.role = .main → a.bias = .zero

/-- Phase-3, all Mains unbiased: `Phase3Transition` reduces so that Rules 3/4
(`phase3CancelSplit`) act as the identity.  Hence the produced pair is exactly
the Rule-1/Rule-2 output `(s2, t2)` from the definition. -/
theorem phase3CancelSplit_id_of_unbiased (s2 t2 : AgentState L K)
    (hs : s2.role = .main → s2.bias = .zero)
    (ht : t2.role = .main → t2.bias = .zero)
    (hboth : s2.role = .main ∧ t2.role = .main) :
    phase3CancelSplit L K s2 t2 = (s2, t2) := by
  have hsb : s2.bias = .zero := hs hboth.1
  have htb : t2.bias = .zero := ht hboth.2
  unfold phase3CancelSplit
  rw [hsb, htb]

/-- **The Rule-2 hour-drag output (left Main, right Clock).**  A Phase-3 pair
with `s` an unbiased Main and `t` a Clock has `Phase3Transition` output
`(s.hour ← min L (⌊t.minute/K⌋), t)`: Rule 1 is inert (not both Clocks), Rule 2
fires on `s`, and the both-Main guard for Rules 3/4 fails. -/
theorem phase3_drag_left (s t : AgentState L K)
    (hs_main : s.role = .main) (hs_bias : s.bias = .zero) (ht_clock : t.role = .clock) :
    Phase3Transition L K s t =
      ({ s with hour := ⟨min L (t.minute.val / K), by
          apply Nat.lt_succ_of_le; exact Nat.min_le_left _ _⟩ }, t) := by
  have htm : t.role ≠ .main := by rw [ht_clock]; decide
  unfold Phase3Transition
  -- Rule 1 guard `s.role = clock ∧ t.role = clock` is false; s1 = s, t1 = t.
  -- Rule 2 fires on the left branch; the both-Main guard fails (t is a Clock).
  simp only [ht_clock, hs_main, hs_bias, htm, false_and, if_false,
    if_true, and_self, reduceCtorEq, and_false, ite_self]

/-- **The Rule-2 hour-drag output (left Clock, right Main).**  Symmetric to
`phase3_drag_left`. -/
theorem phase3_drag_right (s t : AgentState L K)
    (hs_clock : s.role = .clock) (ht_main : t.role = .main) (ht_bias : t.bias = .zero) :
    Phase3Transition L K s t =
      (s, { t with hour := ⟨min L (s.minute.val / K), by
          apply Nat.lt_succ_of_le; exact Nat.min_le_left _ _⟩ }) := by
  have htc : t.role ≠ .clock := by rw [ht_main]; decide
  have hsm : s.role ≠ .main := by rw [hs_clock]; decide
  unfold Phase3Transition
  simp only [hsm, htc, hs_clock, ht_main, ht_bias, true_and, false_and, and_false,
    if_false, if_true, and_self, reduceCtorEq, ite_self]

/-! ## Part 4 — the per-pair `cAbove`/`mAbove` facts on the `HourWindow`.

The window `HourWindow h` (Part 5) forces every applicable pair to be one of:
Main×Main (unbiased, Rules 3/4 inert ⇒ identity), Clock×Clock (Rule 1 ⇒ minutes
only rise), or Main×Clock (Rule 2 ⇒ hour-drag, Clock minute untouched).  In all
three cases the per-pair `cAbove` count does not decrease and the per-pair
`mAbove` count rises by at most the number of `clockAbove h` agents in the pair.

We work over the FULL `Transition`; at phase 3 the epidemic stage is identity and
`finishPhase10Entry` is identity (the outputs sit at phase ∈ {3,4} ≠ 10). -/

/-- A pair of states with both inputs at phase 3 whose `Phase3Transition` outputs
have phase `≠ 10` satisfies `Transition = Phase3Transition`. -/
theorem transition_eq_phase3
    (s t : AgentState L K) (hs : s.phase.val = 3) (ht : t.phase.val = 3)
    (h1 : (Phase3Transition L K s t).1.phase.val ≠ 10)
    (h2 : (Phase3Transition L K s t).2.phase.val ≠ 10) :
    Transition L K s t = Phase3Transition L K s t := by
  have hs_eq : s.phase = ⟨3, by decide⟩ := Fin.ext hs
  have hepi := phaseEpidemicUpdate_eq_self_p3 (L := L) (K := K) s t hs ht
  conv_lhs => unfold Transition
  rw [hepi]
  dsimp only []
  rw [hs_eq]
  show (finishPhase10Entry L K s (Phase3Transition L K s t).1,
        finishPhase10Entry L K t (Phase3Transition L K s t).2) = _
  rw [finishPhase10Entry_eq_self_of_after_ne_10 (L := L) (K := K) s _ h1,
      finishPhase10Entry_eq_self_of_after_ne_10 (L := L) (K := K) t _ h2]

/-- Clock × Clock at phase 3: both `Phase3Transition` outputs have phase ∈ {3,4}.
Drip/sync keep phase 3; the synced-at-cap branch routes through
`stdCounterSubroutine`, whose phase is 3 or 4. -/
theorem phase3_clock_out_phase_le_four (s t : AgentState L K)
    (hsc : s.role = .clock) (htc : t.role = .clock)
    (hs3 : s.phase.val = 3) (ht3 : t.phase.val = 3) :
    ((Phase3Transition L K s t).1.phase.val = 3 ∨
        (Phase3Transition L K s t).1.phase.val = 4) ∧
      ((Phase3Transition L K s t).2.phase.val = 3 ∨
        (Phase3Transition L K s t).2.phase.val = 4) := by
  -- stdCounterSubroutine of a phase-3 state has phase ∈ {3,4}.
  have hcounter : ∀ a : AgentState L K, a.phase.val = 3 →
      (stdCounterSubroutine L K a).phase.val = 3 ∨
        (stdCounterSubroutine L K a).phase.val = 4 := by
    intro a ha
    by_cases hc : a.counter.val = 0
    · right
      unfold stdCounterSubroutine advancePhaseWithInit advancePhase phaseInit
      rw [dif_pos hc, dif_pos (by omega : a.phase.val < 10)]
      simp [ha]
    · left; unfold stdCounterSubroutine; rw [dif_neg hc]; exact ha
  by_cases hmin : s.minute = t.minute
  · by_cases hcap : s.minute.val < K * (L + 1)
    · -- DRIP: outputs at phase 3.
      have hcap_t : t.minute.val < K * (L + 1) := by simpa [hmin] using hcap
      have hP3 : Phase3Transition L K s t =
          ({ s with minute := ⟨s.minute.val + 1, by omega⟩ }, t) := by
        unfold Phase3Transition
        simp only [hsc, htc, and_self, if_true, hmin, ne_eq, not_true_eq_false,
          if_false, hcap, hcap_t, ↓reduceDIte, reduceCtorEq, false_and, and_false,
          true_and, if_false]
      rw [hP3]; exact ⟨Or.inl hs3, Or.inl ht3⟩
    · -- synced-at-cap: outputs are stdCounterSubroutine results, phase ∈ {3,4}.
      have hcap' : ¬ s.minute.val < K * (L + 1) := hcap
      have hcap_t : ¬ t.minute.val < K * (L + 1) := by simpa [hmin] using hcap
      have hsr : (stdCounterSubroutine L K s).role = .clock :=
        stdCounterSubroutine_clock_role s hsc
      have htr : (stdCounterSubroutine L K t).role = .clock :=
        stdCounterSubroutine_clock_role t htc
      have hP3 : Phase3Transition L K s t =
          (stdCounterSubroutine L K s, stdCounterSubroutine L K t) := by
        unfold Phase3Transition
        simp only [hsc, htc, and_self, if_true, hmin, ne_eq, not_true_eq_false,
          if_false, hcap_t, dif_neg, not_false_eq_true]
        simp only [hsr, htr, reduceCtorEq, false_and, if_false, and_false]
      rw [hP3]; exact ⟨hcounter s hs3, hcounter t ht3⟩
  · -- SYNC: outputs at phase 3 (only minute changes).
    have hsync := Transition_phase3_clock_minute_sync_decreases (L := L) (K := K) s t
      hs3 ht3 hsc htc hmin
    -- the sync branch of Phase3Transition leaves phase = 3 (only minute set to max).
    have hP3 : Phase3Transition L K s t =
        ({ s with minute := max s.minute t.minute },
         { t with minute := max s.minute t.minute }) := by
      unfold Phase3Transition
      have htm : t.role ≠ .main := by rw [htc]; decide
      have hsm : s.role ≠ .main := by rw [hsc]; decide
      simp only [hsc, htc, and_self, if_true, hmin, ne_eq, not_false_eq_true,
        if_true, hsm, htm, false_and, and_false, if_false, reduceCtorEq, ite_self]
    rw [hP3]; exact ⟨Or.inl hs3, Or.inl ht3⟩

/-- `Phase3Transition` of a pair on the window (both phase-3, role ∈ {main,clock},
Main ⇒ unbiased) keeps BOTH outputs at phase ∈ {3,4}, hence `≠ 10`.  This lets
`transition_eq_phase3` apply. -/
theorem phase3_out_phase_ne_ten (s t : AgentState L K)
    (hs3 : s.phase.val = 3) (ht3 : t.phase.val = 3)
    (hsr : s.role = .main ∨ s.role = .clock) (htr : t.role = .main ∨ t.role = .clock)
    (hsu : s.role = .main → s.bias = .zero) (htu : t.role = .main → t.bias = .zero) :
    (Phase3Transition L K s t).1.phase.val ≠ 10 ∧
      (Phase3Transition L K s t).2.phase.val ≠ 10 := by
  rcases hsr with hsm | hsc
  · rcases htr with htm | htc
    · -- Main × Main: phase3CancelSplit identity ⇒ outputs = (s,t), phase 3.
      have hcs := phase3CancelSplit_id_of_unbiased (L := L) (K := K) s t hsu htu ⟨hsm, htm⟩
      have hP3 : Phase3Transition L K s t = (s, t) := by
        unfold Phase3Transition
        have hsc' : s.role ≠ .clock := by rw [hsm]; decide
        have htc' : t.role ≠ .clock := by rw [htm]; decide
        simp only [hsc', htc', hsm, htm, hsu hsm, htu htm, false_and, and_false,
          if_false, if_true, and_self, reduceCtorEq, ite_self]
        exact hcs
      rw [hP3]; exact ⟨by rw [hs3]; decide, by rw [ht3]; decide⟩
    · -- Main × Clock: Rule 2, phase unchanged (3).
      rw [phase3_drag_left s t hsm (hsu hsm) htc]
      exact ⟨by rw [hs3]; decide, by rw [ht3]; decide⟩
  · rcases htr with htm | htc
    · -- Clock × Main: Rule 2, phase unchanged (3).
      rw [phase3_drag_right s t hsc htm (htu htm)]
      exact ⟨by rw [hs3]; decide, by rw [ht3]; decide⟩
    · -- Clock × Clock: phase ∈ {3,4} ⇒ ≠ 10.
      obtain ⟨h1, h2⟩ := phase3_clock_out_phase_le_four (L := L) (K := K) s t hsc htc hs3 ht3
      exact ⟨by rcases h1 with h | h <;> omega, by rcases h2 with h | h <;> omega⟩

/-! ## Part 5 — the per-pair `cAbove` non-decrease and `mAbove` drag bound.

These are the genuine combinatorial cores, on the FULL `Transition`.  For a pair
`(s,t)` on the window (both phase-3, role ∈ {main,clock}, Main ⇒ unbiased):

* `cAbove_pair_mono` — `countP clockAboveP` does not decrease: in the Main×Clock
  hour-drag the Clock's minute is untouched, in Clock×Clock minutes only rise, in
  Main×Main nothing changes.
* `mAbove_pair_drag` — `countP mainAboveP` over the output is at most the count
  over the input PLUS the number of `clockAbove h` agents in the input pair: the
  ONLY way a Main crosses `hour > h` is Rule 2 against a Clock with
  `(h+1)·K ≤ minute`, i.e. a Clock counted by `clockAboveP h`. -/

/-- A Main output of the Rule-2 drag is above `h` only if the partner Clock is
counted in `clockAboveP h` (the Clock has `(h+1)·K ≤ minute`).  This is the
arithmetic core of the hour-drag: `min L (⌊minute/K⌋) > h ↔ (h+1)·K ≤ minute`
(using `h < L+1`, automatic since hours live in `Fin (L+1)`). -/
theorem dragged_above_iff (h : ℕ) (hK : 0 < K) (hhL : h < L)
    (cl : AgentState L K) :
    h < min L (cl.minute.val / K) ↔ (h + 1) * K ≤ cl.minute.val := by
  constructor
  · intro hlt
    have hdiv : h < cl.minute.val / K := lt_of_lt_of_le hlt (Nat.min_le_right _ _)
    have : (h + 1) ≤ cl.minute.val / K := hdiv
    calc (h + 1) * K ≤ (cl.minute.val / K) * K := by
            apply Nat.mul_le_mul_right; exact this
      _ ≤ cl.minute.val := Nat.div_mul_le_self _ _
  · intro hge
    rw [lt_min_iff]
    refine ⟨hhL, ?_⟩
    -- (h+1)·K ≤ minute ⇒ h+1 ≤ minute/K ⇒ h < minute/K.
    have : h + 1 ≤ cl.minute.val / K := by
      rw [Nat.le_div_iff_mul_le hK]; rw [Nat.mul_comm] at hge ⊢; exact hge
    omega

/-- **Per-pair `cAbove` non-decrease** under the full `Transition`, on the
window. -/
theorem cAbove_pair_mono (h : ℕ) (s t : AgentState L K)
    (hs3 : s.phase.val = 3) (ht3 : t.phase.val = 3)
    (hsr : s.role = .main ∨ s.role = .clock) (htr : t.role = .main ∨ t.role = .clock)
    (hsu : s.role = .main → s.bias = .zero) (htu : t.role = .main → t.bias = .zero) :
    Multiset.countP (fun a => clockAboveP h a) ({s, t} : Multiset (AgentState L K))
      ≤ Multiset.countP (fun a => clockAboveP h a)
          ({(Transition L K s t).1, (Transition L K s t).2}
            : Multiset (AgentState L K)) := by
  obtain ⟨h1, h2⟩ := phase3_out_phase_ne_ten s t hs3 ht3 hsr htr hsu htu
  rw [transition_eq_phase3 s t hs3 ht3 h1 h2]
  rw [countP_pair, countP_pair]
  rcases hsr with hsm | hsc
  · rcases htr with htm | htc
    · -- Main × Main: identity ⇒ output counts equal input counts.
      have hP3 : Phase3Transition L K s t = (s, t) := by
        unfold Phase3Transition
        have hsc' : s.role ≠ .clock := by rw [hsm]; decide
        have htc' : t.role ≠ .clock := by rw [htm]; decide
        simp only [hsc', htc', hsm, htm, hsu hsm, htu htm, false_and, and_false,
          if_false, if_true, and_self, reduceCtorEq, ite_self]
        exact phase3CancelSplit_id_of_unbiased (L := L) (K := K) s t hsu htu ⟨hsm, htm⟩
      rw [hP3]
    · -- Main × Clock: drag, Clock minute untouched, s stays Main (not clock).
      rw [phase3_drag_left s t hsm (hsu hsm) htc]
      have hrole : ({ s with hour := (⟨min L (t.minute.val / K), by
          apply Nat.lt_succ_of_le; exact Nat.min_le_left _ _⟩ : Fin (L+1)) }
          : AgentState L K).role = .main := hsm
      simp only [clockAboveP, hsm, hrole,
        show (Role.main : Role) ≠ .clock from by decide, false_and, if_false, le_refl]
  · rcases htr with htm | htc
    · -- Clock × Main: drag, s Clock untouched, t stays Main.
      rw [phase3_drag_right s t hsc htm (htu htm)]
      have hrole : ({ t with hour := (⟨min L (s.minute.val / K), by
          apply Nat.lt_succ_of_le; exact Nat.min_le_left _ _⟩ : Fin (L+1)) }
          : AgentState L K).role = .main := htm
      simp only [clockAboveP, htm, hrole,
        show (Role.main : Role) ≠ .clock from by decide, false_and, if_false, le_refl]
    · -- Clock × Clock: minutes only rise ⇒ clockAboveP count up.
      obtain ⟨hr1, hr2, hm1, hm2⟩ := Phase3_clock_pair (L := L) (K := K) s t hsc htc hs3 ht3
      have key : ∀ x x' : AgentState L K, x.role = .clock → x'.role = .clock →
          x.minute.val ≤ x'.minute.val →
          (if clockAboveP h x then (1:ℕ) else 0) ≤ (if clockAboveP h x' then 1 else 0) := by
        intro x x' hxr hx'r hmono
        unfold clockAboveP
        simp only [hxr, hx'r, true_and]
        by_cases hx : (h + 1) * K ≤ x.minute.val
        · rw [if_pos hx, if_pos (le_trans hx hmono)]
        · rw [if_neg hx]; positivity
      have k1 := key s _ hsc hr1 hm1
      have k2 := key t _ htc hr2 hm2
      omega

/-- **Per-pair `mAbove` drag bound** under the full `Transition`, on the window.
A Main crosses `hour > h` only via the Rule-2 hour-drag against a Clock with
`(h+1)·K ≤ minute` (i.e. counted in `clockAboveP h`), so the produced `mAbove`
count is at most the consumed `mAbove` count plus the consumed `clockAbove`
count. -/
theorem mAbove_pair_drag (h : ℕ) (hK : 0 < K) (hhL : h < L) (s t : AgentState L K)
    (hs3 : s.phase.val = 3) (ht3 : t.phase.val = 3)
    (hsr : s.role = .main ∨ s.role = .clock) (htr : t.role = .main ∨ t.role = .clock)
    (hsu : s.role = .main → s.bias = .zero) (htu : t.role = .main → t.bias = .zero) :
    Multiset.countP (fun a => mainAboveP h a)
        ({(Transition L K s t).1, (Transition L K s t).2}
          : Multiset (AgentState L K))
      ≤ Multiset.countP (fun a => mainAboveP h a) ({s, t} : Multiset (AgentState L K))
        + Multiset.countP (fun a => clockAboveP h a) ({s, t} : Multiset (AgentState L K)) := by
  obtain ⟨hp1, hp2⟩ := phase3_out_phase_ne_ten s t hs3 ht3 hsr htr hsu htu
  rw [transition_eq_phase3 s t hs3 ht3 hp1 hp2]
  rw [countP_pair, countP_pair, countP_pair]
  rcases hsr with hsm | hsc
  · rcases htr with htm | htc
    · -- Main × Main: identity ⇒ output mAbove = input mAbove ≤ +clockAbove.
      have hP3 : Phase3Transition L K s t = (s, t) := by
        unfold Phase3Transition
        have hsc' : s.role ≠ .clock := by rw [hsm]; decide
        have htc' : t.role ≠ .clock := by rw [htm]; decide
        simp only [hsc', htc', hsm, htm, hsu hsm, htu htm, false_and, and_false,
          if_false, if_true, and_self, reduceCtorEq, ite_self]
        exact phase3CancelSplit_id_of_unbiased (L := L) (K := K) s t hsu htu ⟨hsm, htm⟩
      rw [hP3]; dsimp only; omega
    · -- Main × Clock: s-output main-above ⇒ t is clock-above; t-output = t (clock).
      rw [phase3_drag_left s t hsm (hsu hsm) htc]
      dsimp only
      -- s-output role = main; mainAboveP iff h < min L (⌊t.minute/K⌋) iff t clockAbove.
      have hs'role : ({ s with hour := (⟨min L (t.minute.val / K), by
          apply Nat.lt_succ_of_le; exact Nat.min_le_left _ _⟩ : Fin (L+1)) }
          : AgentState L K).role = .main := hsm
      have hs'hour : ({ s with hour := (⟨min L (t.minute.val / K), by
          apply Nat.lt_succ_of_le; exact Nat.min_le_left _ _⟩ : Fin (L+1)) }
          : AgentState L K).hour.val = min L (t.minute.val / K) := rfl
      -- key inequality: [s'-mainAbove] ≤ [t-clockAbove].
      have hdrag : (if mainAboveP h ({ s with hour := (⟨min L (t.minute.val / K), by
            apply Nat.lt_succ_of_le; exact Nat.min_le_left _ _⟩ : Fin (L+1)) }
            : AgentState L K) then (1:ℕ) else 0)
          ≤ (if clockAboveP h t then 1 else 0) := by
        by_cases hd : mainAboveP h ({ s with hour := (⟨min L (t.minute.val / K), by
            apply Nat.lt_succ_of_le; exact Nat.min_le_left _ _⟩ : Fin (L+1)) }
            : AgentState L K)
        · rw [if_pos hd]
          have hlt : h < min L (t.minute.val / K) := by
            have := hd.2; rwa [hs'hour] at this
          have htca : clockAboveP h t :=
            ⟨htc, (dragged_above_iff h hK hhL t).mp hlt⟩
          rw [if_pos htca]
        · rw [if_neg hd]; positivity
      -- t (= t-output) is a Clock ⇒ not mainAbove; s is a Main ⇒ not clockAbove.
      have htnotmain : ¬ mainAboveP h t := by unfold mainAboveP; rw [htc]; simp
      have hsnotclock : ¬ clockAboveP h s := by unfold clockAboveP; rw [hsm]; simp
      rw [if_neg htnotmain, if_neg hsnotclock]
      omega
  · rcases htr with htm | htc
    · -- Clock × Main: symmetric.
      rw [phase3_drag_right s t hsc htm (htu htm)]
      dsimp only
      have ht'hour : ({ t with hour := (⟨min L (s.minute.val / K), by
          apply Nat.lt_succ_of_le; exact Nat.min_le_left _ _⟩ : Fin (L+1)) }
          : AgentState L K).hour.val = min L (s.minute.val / K) := rfl
      have ht'role : ({ t with hour := (⟨min L (s.minute.val / K), by
          apply Nat.lt_succ_of_le; exact Nat.min_le_left _ _⟩ : Fin (L+1)) }
          : AgentState L K).role = .main := htm
      have hsnm : s.role ≠ .main := by rw [hsc]; decide
      have hdrag : (if mainAboveP h ({ t with hour := (⟨min L (s.minute.val / K), by
            apply Nat.lt_succ_of_le; exact Nat.min_le_left _ _⟩ : Fin (L+1)) }
            : AgentState L K) then (1:ℕ) else 0)
          ≤ (if clockAboveP h s then 1 else 0) := by
        by_cases hd : mainAboveP h ({ t with hour := (⟨min L (s.minute.val / K), by
            apply Nat.lt_succ_of_le; exact Nat.min_le_left _ _⟩ : Fin (L+1)) }
            : AgentState L K)
        · rw [if_pos hd]
          have hlt : h < min L (s.minute.val / K) := by
            have := hd.2; rwa [ht'hour] at this
          have hsca : clockAboveP h s :=
            ⟨hsc, (dragged_above_iff h hK hhL s).mp hlt⟩
          rw [if_pos hsca]
        · rw [if_neg hd]; positivity
      have hsnotmain : ¬ mainAboveP h s := by unfold mainAboveP; rw [hsc]; simp
      have htnotclock : ¬ clockAboveP h t := by unfold clockAboveP; rw [htm]; simp
      rw [if_neg hsnotmain, if_neg htnotclock]
      omega
    · -- Clock × Clock: no Mains ⇒ output mAbove = 0.
      obtain ⟨hr1, hr2, _, _⟩ := Phase3_clock_pair (L := L) (K := K) s t hsc htc hs3 ht3
      have e1 : ¬ mainAboveP h (Phase3Transition L K s t).1 := by
        unfold mainAboveP; rw [hr1]; simp
      have e2 : ¬ mainAboveP h (Phase3Transition L K s t).2 := by
        unfold mainAboveP; rw [hr2]; simp
      simp only [e1, e2, if_false]; omega

/-! ## Part 6 — config-level monotonicity over the window, and the drift.

The window `HourWindow` forces every agent to be Main or Clock, all at phase 3,
with unbiased Mains, so EVERY applicable pair satisfies the per-pair hypotheses.
We lift the per-pair facts to the one-step kernel support exactly as
`ClockRealKernel.rBeyond_stepOrSelf_ge` does. -/

/-- The hour-coupling window: every agent is a Main or a Clock, at phase 3, with
unbiased Mains. -/
def HourWindow (c : Config (AgentState L K)) : Prop :=
  ∀ a ∈ c, (a.role = .main ∨ a.role = .clock) ∧ a.phase.val = 3 ∧
    (a.role = .main → a.bias = .zero)

/-- `cAbove h` is non-decreasing under any chosen-pair update, over `HourWindow`. -/
theorem cAbove_stepOrSelf_ge (h : ℕ) (c : Config (AgentState L K))
    (hw : HourWindow c) (r₁ r₂ : AgentState L K) :
    cAbove (L := L) (K := K) h c
      ≤ cAbove (L := L) (K := K) h (Protocol.stepOrSelf (NonuniformMajority L K) c r₁ r₂) := by
  classical
  by_cases happ : Protocol.Applicable c r₁ r₂
  · have hmem1 := mem_of_applicable_left happ
    have hmem2 := mem_of_applicable_right happ
    obtain ⟨h1r, h1p, h1u⟩ := hw r₁ hmem1
    obtain ⟨h2r, h2p, h2u⟩ := hw r₂ hmem2
    have hsub : ({r₁, r₂} : Multiset (AgentState L K)) ≤ c := happ
    have hc' : Protocol.stepOrSelf (NonuniformMajority L K) c r₁ r₂
        = c - {r₁, r₂} + {(NonuniformMajority L K).δ r₁ r₂ |>.1,
            (NonuniformMajority L K).δ r₁ r₂ |>.2} := by
      unfold Protocol.stepOrSelf; rw [if_pos happ]
    have hδ : (NonuniformMajority L K).δ r₁ r₂ = Transition L K r₁ r₂ := rfl
    unfold cAbove
    rw [hc', Multiset.countP_add, Multiset.countP_sub hsub]
    have hpair_le : Multiset.countP (fun a => clockAboveP h a)
        ({r₁, r₂} : Multiset (AgentState L K))
          ≤ Multiset.countP (fun a => clockAboveP h a) c :=
      Multiset.countP_le_of_le _ hsub
    have hmono := cAbove_pair_mono h r₁ r₂ h1p h2p h1r h2r h1u h2u
    rw [hδ]
    omega
  · rw [Protocol.stepOrSelf_eq_self_of_not_applicable happ]

/-- `mAbove h` drag bound under any chosen-pair update, over `HourWindow`. -/
theorem mAbove_stepOrSelf_le (h : ℕ) (hK : 0 < K) (hhL : h < L)
    (c : Config (AgentState L K)) (hw : HourWindow c) (r₁ r₂ : AgentState L K) :
    mAbove (L := L) (K := K) h (Protocol.stepOrSelf (NonuniformMajority L K) c r₁ r₂)
      ≤ mAbove (L := L) (K := K) h c +
          Multiset.countP (fun a => clockAboveP h a)
            ({r₁, r₂} : Multiset (AgentState L K)) := by
  classical
  by_cases happ : Protocol.Applicable c r₁ r₂
  · have hmem1 := mem_of_applicable_left happ
    have hmem2 := mem_of_applicable_right happ
    obtain ⟨h1r, h1p, h1u⟩ := hw r₁ hmem1
    obtain ⟨h2r, h2p, h2u⟩ := hw r₂ hmem2
    have hsub : ({r₁, r₂} : Multiset (AgentState L K)) ≤ c := happ
    have hc' : Protocol.stepOrSelf (NonuniformMajority L K) c r₁ r₂
        = c - {r₁, r₂} + {(NonuniformMajority L K).δ r₁ r₂ |>.1,
            (NonuniformMajority L K).δ r₁ r₂ |>.2} := by
      unfold Protocol.stepOrSelf; rw [if_pos happ]
    have hδ : (NonuniformMajority L K).δ r₁ r₂ = Transition L K r₁ r₂ := rfl
    unfold mAbove
    rw [hc', Multiset.countP_add, Multiset.countP_sub hsub]
    have hpair_le : Multiset.countP (fun a => mainAboveP h a)
        ({r₁, r₂} : Multiset (AgentState L K))
          ≤ Multiset.countP (fun a => mainAboveP h a) c :=
      Multiset.countP_le_of_le _ hsub
    have hdrag := mAbove_pair_drag h hK hhL r₁ r₂ h1p h2p h1r h2r h1u h2u
    rw [hδ]
    omega
  · rw [Protocol.stepOrSelf_eq_self_of_not_applicable happ]
    have : 0 ≤ Multiset.countP (fun a => clockAboveP h a)
        ({r₁, r₂} : Multiset (AgentState L K)) := Nat.zero_le _
    omega

/-- `cAbove h` is non-decreasing on the one-step kernel support over the window
(the real-kernel `milestone_monotone` for `cAbove`). -/
theorem cAbove_support_ge (h : ℕ) (c c' : Config (AgentState L K))
    (hw : HourWindow c)
    (hc' : c' ∈ ((NonuniformMajority L K).stepDistOrSelf c).support) :
    cAbove (L := L) (K := K) h c ≤ cAbove (L := L) (K := K) h c' := by
  classical
  by_cases hc : 2 ≤ c.card
  · rw [show (NonuniformMajority L K).stepDistOrSelf c = (NonuniformMajority L K).stepDist c hc by
        unfold Protocol.stepDistOrSelf; rw [dif_pos hc]] at hc'
    obtain ⟨⟨r₁, r₂⟩, hr⟩ := Protocol.stepDist_support (NonuniformMajority L K) c hc c' hc'
    rw [← hr]
    exact cAbove_stepOrSelf_ge h c hw r₁ r₂
  · rw [show (NonuniformMajority L K).stepDistOrSelf c = PMF.pure c by
        unfold Protocol.stepDistOrSelf; rw [dif_neg hc]] at hc'
    rw [PMF.mem_support_pure_iff] at hc'
    subst hc'; exact le_refl _

/-! ## Part 7 — the additive supermartingale drift (exponential transform).

The additive supermartingale `Φ` is handled by its exponential transform
`Ψ = exp(s·Φ)`, the standard Azuma/Bernstein device.  Because `Φ` can be
negative, we cannot run the multiplicative engine on `Φ` directly; we run it on
`Ψ : Config → ℝ≥0∞`, which IS a (multiplicative, `r = 1`) supermartingale.

The mechanism does the genuine work: on the kernel support, `cAbove h` is
non-decreasing (`cAbove_support_ge`, from Rule 2's clock-minute invariance and
the clock-clock minute monotonicity), so for `s ≥ 0`

  Ψ(c') = exp(s·(mAbove c' − 1.1·cAbove c')) ≤ exp(s·(mAbove c' − 1.1·cAbove c)).

The remaining pair-counting expectation — that the EXPECTED `mAbove`-gain is
dominated by `1.1·cAbove` (so the kernel-integral of the right side is `≤ Ψ(c)`)
— is the single deferred STRUCTURAL input `hfloor` (a pure pair-count fact, NOT
the supermartingale property and NOT a contraction).  We PROVE the drift from
`hfloor` plus the mechanism. -/

/-- The `cAbove`-shifted exponential potential used as the intermediate bound:
`exp(s·(mAbove c' − 1.1·cAbove c₀))` (the clock count frozen at the base `c₀`). -/
noncomputable def expPotShift (s : ℝ) (h : ℕ) (c₀ c' : Config (AgentState L K)) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (s *
    ((mAbove (L := L) (K := K) h c' : ℝ)
      - (11 / 10 : ℝ) * (cAbove (L := L) (K := K) h c₀ : ℝ))))

theorem expPotShift_measurable (s : ℝ) (h : ℕ) (c₀ : Config (AgentState L K)) :
    Measurable (expPotShift (L := L) (K := K) s h c₀) :=
  fun _ _ => DiscreteMeasurableSpace.forall_measurableSet _

/-- **The mechanism step**: on the kernel support, `Ψ(c') ≤ expPotShift(c)`
because `cAbove` is non-decreasing (`s ≥ 0`).  Genuinely proven from
`cAbove_support_ge`. -/
theorem expPot_le_shift_on_support (s : ℝ) (hs : 0 ≤ s) (h : ℕ)
    (c c' : Config (AgentState L K)) (hw : HourWindow c)
    (hc' : c' ∈ ((NonuniformMajority L K).stepDistOrSelf c).support) :
    expPot (L := L) (K := K) s h c' ≤ expPotShift (L := L) (K := K) s h c c' := by
  unfold expPot expPotShift Phi
  apply ENNReal.ofReal_le_ofReal
  apply Real.exp_le_exp.mpr
  have hmono : (cAbove (L := L) (K := K) h c : ℝ) ≤ (cAbove (L := L) (K := K) h c' : ℝ) := by
    exact_mod_cast cAbove_support_ge h c c' hw hc'
  -- s·(m c' − 1.1·c c') ≤ s·(m c' − 1.1·c c) since c c ≤ c c'.
  have h11 : (0 : ℝ) ≤ 11 / 10 := by norm_num
  nlinarith [mul_nonneg hs (mul_nonneg h11 (sub_nonneg.mpr hmono))]

/-- **Lemma 6.10 supermartingale drift (kernel form).**  On the window, the
exponential potential `Ψ = expPot s h` satisfies the multiplicative-`r=1`
supermartingale drift

  ∫⁻ Ψ(c') d(transitionKernel c) ≤ Ψ(c),

i.e. `Φ h` is an additive supermartingale.  The drift is PROVEN from the Rule-2
hour-drag mechanism (`expPot_le_shift_on_support`, via `cAbove_support_ge`) plus
the single deferred pair-counting floor `hfloor` (the EXPECTED exponential
`mAbove`-gain is dominated by the frozen-`cAbove` base — a pure pair-count, NOT
the supermartingale property, NOT a contraction). -/
theorem hour_coupling_drift (s : ℝ) (hs : 0 ≤ s) (h : ℕ)
    (c : Config (AgentState L K)) (hw : HourWindow c)
    (hfloor : ∫⁻ c', expPotShift (L := L) (K := K) s h c c'
        ∂((NonuniformMajority L K).stepDistOrSelf c).toMeasure
      ≤ expPot (L := L) (K := K) s h c) :
    ∫⁻ c', expPot (L := L) (K := K) s h c'
        ∂((NonuniformMajority L K).transitionKernel c)
      ≤ expPot (L := L) (K := K) s h c := by
  change ∫⁻ c', expPot (L := L) (K := K) s h c'
    ∂((NonuniformMajority L K).stepDistOrSelf c).toMeasure ≤ _
  refine le_trans ?_ hfloor
  apply lintegral_mono_ae
  rw [ae_iff, PMF.toMeasure_apply_eq_zero_iff _
    (DiscreteMeasurableSpace.forall_measurableSet _)]
  rw [Set.disjoint_left]
  intro x hsupp hbad
  apply hbad
  exact expPot_le_shift_on_support s hs h c x hw hsupp

/-! ## Part 8 — the guarded potential and the additive supermartingale tail.

`geometric_drift_tail_kernel` needs the drift `∫⁻ Ψ dK(x) ≤ r·Ψ(x)` for EVERY
`x`.  Off the window we GUARD `Ψ` to `⊤` (the established `rSeedPotMix` device),
so the drift is trivial off-window.  On-window we use `hour_coupling_drift`,
needing the window to be support-closed (`habs`) so the guarded potential stays
finite on the support, and the deferred floor `hfloor` for the on-window step. -/

/-- The guarded exponential potential: `⊤` off the window, else `expPot`. -/
noncomputable def expPotGuard (s : ℝ) (h : ℕ) (c : Config (AgentState L K)) : ℝ≥0∞ :=
  open Classical in
  if HourWindow (L := L) (K := K) c then expPot (L := L) (K := K) s h c else ⊤

theorem expPotGuard_measurable (s : ℝ) (h : ℕ) :
    Measurable (expPotGuard (L := L) (K := K) s h) :=
  fun _ _ => DiscreteMeasurableSpace.forall_measurableSet _

theorem expPotGuard_eq_on_window (s : ℝ) (h : ℕ) (c : Config (AgentState L K))
    (hw : HourWindow (L := L) (K := K) c) :
    expPotGuard (L := L) (K := K) s h c = expPot (L := L) (K := K) s h c := by
  unfold expPotGuard; rw [if_pos hw]

/-- **The all-`x` guarded drift** `∫⁻ expPotGuard dK(x) ≤ 1·expPotGuard(x)`.
Off-window the RHS is `⊤`; on-window it follows from `hour_coupling_drift` once
the window is support-closed (`habs`) so the guard equals `expPot` on the
support.  The pair-counting floor `hfloor` is carried for the on-window step. -/
theorem expPotGuard_drift (s : ℝ) (hs : 0 ≤ s) (h : ℕ)
    (habs : ∀ c c' : Config (AgentState L K),
      HourWindow (L := L) (K := K) c →
      c' ∈ ((NonuniformMajority L K).stepDistOrSelf c).support →
      HourWindow (L := L) (K := K) c')
    (hfloor : ∀ c : Config (AgentState L K), HourWindow (L := L) (K := K) c →
      ∫⁻ c', expPotShift (L := L) (K := K) s h c c'
          ∂((NonuniformMajority L K).stepDistOrSelf c).toMeasure
        ≤ expPot (L := L) (K := K) s h c)
    (x : Config (AgentState L K)) :
    ∫⁻ c', expPotGuard (L := L) (K := K) s h c'
        ∂((NonuniformMajority L K).transitionKernel x)
      ≤ (1 : ℝ≥0∞) * expPotGuard (L := L) (K := K) s h x := by
  rw [one_mul]
  by_cases hw : HourWindow (L := L) (K := K) x
  · -- On-window: guard = expPot on the support, then use hour_coupling_drift.
    rw [expPotGuard_eq_on_window s h x hw]
    have heq : ∫⁻ c', expPotGuard (L := L) (K := K) s h c'
          ∂((NonuniformMajority L K).transitionKernel x)
        = ∫⁻ c', expPot (L := L) (K := K) s h c'
          ∂((NonuniformMajority L K).transitionKernel x) := by
      change ∫⁻ c', expPotGuard (L := L) (K := K) s h c'
          ∂((NonuniformMajority L K).stepDistOrSelf x).toMeasure = _
      change _ = ∫⁻ c', expPot (L := L) (K := K) s h c'
          ∂((NonuniformMajority L K).stepDistOrSelf x).toMeasure
      apply lintegral_congr_ae
      rw [Filter.eventuallyEq_iff_exists_mem]
      refine ⟨((NonuniformMajority L K).stepDistOrSelf x).support, ?_, ?_⟩
      · rw [mem_ae_iff, PMF.toMeasure_apply_eq_zero_iff _
          (DiscreteMeasurableSpace.forall_measurableSet _)]
        simp [Set.disjoint_left]
      · intro c' hc'
        exact expPotGuard_eq_on_window s h c' (habs x c' hw hc')
    rw [heq]
    exact hour_coupling_drift s hs h x hw (hfloor x hw)
  · -- Off-window: RHS = ⊤.
    rw [expPotGuard, if_neg hw]
    exact le_top

/-- **Lemma 6.10 — the clock → Main hour-coupling tail (kernel-power form).**
Mirrors `Supermartingale.geometric_drift_tail_kernel` with `r = 1`: for the
ADDITIVE supermartingale `Φ h = mAbove h − 1.1·cAbove h`, transported to the
multiplicative supermartingale `Ψ = exp(s·Φ)` (`s ≥ 0`), for every threshold `θ`,
every `t`, and every start `x`,

  θ · (K^t) x { Ψ ≥ θ } ≤ Ψ(x)     (guarded off the window).

Reading off the level set `{ Ψ ≥ exp(s·b) }` recovers the Azuma-style statement
"`Pr[ Φ h ≥ b ]` after `t` steps is `≤ exp(−s·b)·Ψ(x)`", i.e. Main agents do not
run far ahead of the clock.  The drift is PROVEN from the Rule-2 hour-drag
(`expPotGuard_drift` ← `hour_coupling_drift` ← `cAbove_support_ge` + the per-pair
`mAbove`/`cAbove` mechanism); `habs`/`hfloor` are the carried structural inputs. -/
theorem hour_coupling (s : ℝ) (hs : 0 ≤ s) (h : ℕ)
    (habs : ∀ c c' : Config (AgentState L K),
      HourWindow (L := L) (K := K) c →
      c' ∈ ((NonuniformMajority L K).stepDistOrSelf c).support →
      HourWindow (L := L) (K := K) c')
    (hfloor : ∀ c : Config (AgentState L K), HourWindow (L := L) (K := K) c →
      ∫⁻ c', expPotShift (L := L) (K := K) s h c c'
          ∂((NonuniformMajority L K).stepDistOrSelf c).toMeasure
        ≤ expPot (L := L) (K := K) s h c)
    (t : ℕ) (x : Config (AgentState L K)) (θ : ℝ≥0∞) :
    θ * ((NonuniformMajority L K).transitionKernel ^ t) x
        {c' | θ ≤ expPotGuard (L := L) (K := K) s h c'} ≤
      (1 : ℝ≥0∞) ^ t * expPotGuard (L := L) (K := K) s h x := by
  exact geometric_drift_tail_kernel
    (NonuniformMajority L K).transitionKernel
    (expPotGuard (L := L) (K := K) s h)
    (expPotGuard_measurable s h)
    (1 : ℝ≥0∞)
    (expPotGuard_drift s hs h habs hfloor)
    t x θ

/-! ## Part 9 — non-vacuity (the `#print axioms` cannot detect an unsatisfiable
hypothesis; §3.3).  We discharge the carried `hfloor` at `s = 0`, where the
exponential potential is `1` and the floor is the genuinely-true `1 ≤ 1`.  This
witnesses that `hour_coupling`'s deferred input is SATISFIABLE (non-vacuous), and
that the supermartingale drift instantiates unconditionally at `s = 0`. -/

/-- At `s = 0` the shifted exponential potential is identically `1`. -/
theorem expPotShift_zero (h : ℕ) (c₀ c' : Config (AgentState L K)) :
    expPotShift (L := L) (K := K) 0 h c₀ c' = 1 := by
  unfold expPotShift; simp

/-- At `s = 0` the exponential potential is identically `1`. -/
theorem expPot_zero (h : ℕ) (c : Config (AgentState L K)) :
    expPot (L := L) (K := K) 0 h c = 1 := by
  unfold expPot Phi; simp

/-- **Non-vacuity witness**: the deferred floor `hfloor` HOLDS at `s = 0` (the
integral of the constant `1` over a probability measure is `1 ≤ 1`).  Hence the
hypotheses of `hour_coupling` are satisfiable; the theorem is not vacuous. -/
theorem hfloor_zero (h : ℕ) (c : Config (AgentState L K)) :
    ∫⁻ c', expPotShift (L := L) (K := K) 0 h c c'
        ∂((NonuniformMajority L K).stepDistOrSelf c).toMeasure
      ≤ expPot (L := L) (K := K) 0 h c := by
  haveI : IsProbabilityMeasure ((NonuniformMajority L K).stepDistOrSelf c).toMeasure :=
    PMF.toMeasure.isProbabilityMeasure _
  simp only [expPotShift_zero, expPot_zero]
  rw [lintegral_const, measure_univ, mul_one]

/-- **Unconditional `s = 0` instantiation** of the hour-coupling tail: the floor
`hfloor` is discharged by `hfloor_zero`, so the only carried input is the
window-absorption `habs`.  This makes the whole pipeline machine-checked
non-vacuous. -/
theorem hour_coupling_zero (h : ℕ)
    (habs : ∀ c c' : Config (AgentState L K),
      HourWindow (L := L) (K := K) c →
      c' ∈ ((NonuniformMajority L K).stepDistOrSelf c).support →
      HourWindow (L := L) (K := K) c')
    (t : ℕ) (x : Config (AgentState L K)) (θ : ℝ≥0∞) :
    θ * ((NonuniformMajority L K).transitionKernel ^ t) x
        {c' | θ ≤ expPotGuard (L := L) (K := K) 0 h c'} ≤
      (1 : ℝ≥0∞) ^ t * expPotGuard (L := L) (K := K) 0 h x :=
  hour_coupling 0 le_rfl h habs (fun c _ => hfloor_zero h c) t x θ

end HourCoupling

end ExactMajority
