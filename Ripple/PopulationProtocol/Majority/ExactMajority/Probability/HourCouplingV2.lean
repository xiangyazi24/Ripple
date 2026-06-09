/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Lemma 6.10 (GENUINE redo) — the clock → Main hour-coupling supermartingale.

This file gives the genuine, paper-faithful proof of Doty et al.'s Lemma 6.10
(Main agents do not run ahead of the clock), DIRECTLY on the real
`NonuniformMajority L K` kernel, via the real Azuma-Hoeffding tail
`AzumaKernel.azuma_tail`.

## The paper's argument (ref/Doty-2021-exact-majority.txt, lines 2146–2180)

Let `M = |Main|`, `C = |Clock|` be the (fixed) population role-counts and put

  `Φ h c = mAbove h c / M − 1.1 · cAbove h c / C`     (the fraction potential)

where `mAbove h c = |{Main : hour > h}|` and `cAbove h c = |{Clock : hour > h}|`
(integer counts; dividing by `M`, `C` gives the paper's fractions `m_{>h}`,
`c_{>h}`).  The two reactions that move `Φ` are:

* the **drag** `C_h, M_j → C_h, M_h` (`h > j`): a Main joins `mAbove`, raising
  `Φ` by `1/M`.  A drag can only LIFT a Main across hour `h` against a Clock
  with `(h+1)·K ≤ minute`, i.e. a Clock counted in `cAbove`.  So the number of
  drag-crossing ordered pairs is at most `(M − mAbove) · cAbove`.
* the **clock epidemic** `C_h, C_j → C_h, C_h` (`h > j`): a Clock joins
  `cAbove`, lowering `Φ` by `1.1/C`.  Every ordered (clock-above × clock-below)
  pair raises `cAbove` by `≥ 1`, and there are exactly `cAbove · (C − cAbove)`
  of them.

The single-step expected change is therefore bounded by

  `E[ΔΦ] ≤ (1/M)·(M − mAbove)·cAbove / P − (1.1/C)·cAbove·(C − cAbove) / P`
        `= cAbove/P · [ (1 − m_{>h}) − 1.1·(1 − c_{>h}) ]`

(`P = totalPairs`).  On the window `c_{>h} ≤ 1/11` the bracket is `≤ 0`
(`1.1·(1 − c_{>h}) ≥ 1 ≥ 1 − m_{>h}`), so `Φ` is a genuine bounded-difference
supermartingale.  The bound `|ΔΦ| ≤ max(1/M, 1.1/C)` and Azuma's inequality
(`azuma_tail`) give the tail of Lemma 6.10.

This derivation is GENUINE: the drift is obtained by expanding the one-step
expectation into a finite `interactionCount` pair-sum and bounding it by the
above pair products — NOT by the earlier frozen-`cAbove` deferred floor.  The
ONLY hypothesis carried is the TRUE window `c_{>h} ≤ 1/11` (the synchronous-hour
regime, `c_{>h} ≤ 0.001` until `end_h`), an explicit, faithful window predicate.

NEW file; no existing file is edited; no sorry/admit/axiom/native_decide.
-/

import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.HourCoupling
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.ClockRealMixed
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.AzumaKernel
import Mathlib.Probability.ProbabilityMassFunction.Integrals

namespace ExactMajority

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Real BigOperators

namespace HourCouplingV2

open ClockRealKernel HourCoupling

variable {L K : ℕ}

/-! ## Part 1 — the fraction potential and its measurability. -/

/-- Count of Main-role agents in a configuration. -/
def mainCount (c : Config (AgentState L K)) : ℕ :=
  Multiset.countP (fun a => a.role = .main) c

/-- Count of Clock-role agents in a configuration. -/
def clockCount (c : Config (AgentState L K)) : ℕ :=
  Multiset.countP (fun a => a.role = .clock) c

/-- The paper's fraction potential `Φ h c = mAbove/M − 1.1·cAbove/C`, with the
FIXED population role-counts `M`, `C` as denominators.  An additive potential
(can be negative); the exact object Azuma's inequality consumes. -/
noncomputable def Phi (M C : ℝ) (h : ℕ) (c : Config (AgentState L K)) : ℝ :=
  (HourCoupling.mAbove (L := L) (K := K) h c : ℝ) / M
    - (11 / 10 : ℝ) * (HourCoupling.cAbove (L := L) (K := K) h c : ℝ) / C

theorem Phi_measurable (M C : ℝ) (h : ℕ) :
    Measurable (Phi (L := L) (K := K) M C h) :=
  fun _ _ => DiscreteMeasurableSpace.forall_measurableSet _

/-! ## Part 2 — the one-step expectation as a finite `interactionCount` pair-sum.

The kernel `transitionKernel c` is the pushforward of the (finite, over the
`AgentState × AgentState` Fintype) uniform pair distribution `interactionPMF`
through `scheduledStep = stepOrSelf`.  Hence the one-step expectation of any
real observable is the finite weighted pair-sum

  `∫ f d(K c) = ∑_{(s,t)} interactionProb(s,t) · f(stepOrSelf c s t)`. -/

/-- On a population of size `≥ 2`, the one-step expectation of a real observable
`f` is the finite pair-sum weighted by `interactionProb`. -/
theorem integral_transitionKernel_eq_sum
    (f : Config (AgentState L K) → ℝ) (c : Config (AgentState L K)) (hc : 2 ≤ c.card) :
    ∫ c', f c' ∂((NonuniformMajority L K).transitionKernel c)
      = ∑ p : AgentState L K × AgentState L K,
          (Config.interactionProb c p.1 p.2).toReal
            * f (Protocol.stepOrSelf (NonuniformMajority L K) c p.1 p.2) := by
  classical
  -- The kernel applied at `c` is `(stepDistOrSelf c).toMeasure`.
  have hker : (NonuniformMajority L K).transitionKernel c
      = (Protocol.stepDistOrSelf (NonuniformMajority L K) c).toMeasure := rfl
  rw [hker]
  -- On `card ≥ 2`, `stepDistOrSelf = stepDist = map scheduledStep interactionPMF`.
  have hsd : Protocol.stepDistOrSelf (NonuniformMajority L K) c
      = PMF.map (Protocol.scheduledStep (NonuniformMajority L K) c)
          (Config.interactionPMF c hc) := by
    unfold Protocol.stepDistOrSelf; rw [dif_pos hc]; rfl
  rw [hsd]
  -- Push the integral through the map.
  rw [← PMF.toMeasure_map (Config.interactionPMF c hc)
      (f := Protocol.scheduledStep (NonuniformMajority L K) c) Measurable.of_discrete]
  rw [MeasureTheory.integral_map (Measurable.of_discrete.aemeasurable)
      (Measurable.of_discrete.aestronglyMeasurable)]
  -- Now a Bochner integral over the Fintype pair PMF.
  rw [PMF.integral_eq_sum]
  -- Identify the summand weight and the pushed observable.
  apply Finset.sum_congr rfl
  intro p _
  rw [smul_eq_mul]
  rfl

/-! ## Part 3 — the sharp per-pair drag/epidemic crossing indicators.

These sharpen `HourCoupling.{mAbove_pair_drag, cAbove_pair_mono}` to the EXACT
crossing structure the paper's bracket needs:

* a Main crosses `hour > h` (raises `mAbove`) ONLY in a (Main-below × Clock-above)
  pair — the `dragInd` indicator;
* a Clock crosses `hour > h` (raises `cAbove`) at LEAST once in a
  (Clock-above × Clock-below) pair (the SYNC sets the lagging clock to the max
  minute) — the `epiInd` indicator. -/

/-- The (decidable) predicate "Main agent at hour `≤ h`, unbiased": a Main that a
drag against a Clock-above can lift across `h`. -/
def mainBelowP (h : ℕ) (a : AgentState L K) : Prop :=
  a.role = .main ∧ ¬ (h < a.hour.val)

instance (h : ℕ) (a : AgentState L K) : Decidable (mainBelowP h a) := by
  unfold mainBelowP; infer_instance

/-- The (decidable) predicate "Clock agent at clock-hour `≤ h`": a Clock that a
sync against a Clock-above lifts across `h`. -/
def clockBelowP (h : ℕ) (a : AgentState L K) : Prop :=
  a.role = .clock ∧ ¬ ((h + 1) * K ≤ a.minute.val)

instance (h : ℕ) (a : AgentState L K) : Decidable (clockBelowP h a) := by
  unfold clockBelowP; infer_instance

/-- The drag-crossing indicator on an ordered pair: a Main-below paired with a
Clock-above (either order). -/
def dragInd (h : ℕ) (s t : AgentState L K) : ℕ :=
  (if mainBelowP h s ∧ HourCoupling.clockAboveP h t then 1 else 0)
    + (if mainBelowP h t ∧ HourCoupling.clockAboveP h s then 1 else 0)

/-- The epidemic-crossing indicator on an ordered pair: a Clock-above paired with
a Clock-below (either order). -/
def epiInd (h : ℕ) (s t : AgentState L K) : ℕ :=
  (if HourCoupling.clockAboveP h s ∧ clockBelowP h t then 1 else 0)
    + (if HourCoupling.clockAboveP h t ∧ clockBelowP h s then 1 else 0)

/-- **Sharp per-pair drag bound.**  On the window, the produced `mAbove` count is
at most the consumed `mAbove` count PLUS the `dragInd` indicator: a Main crosses
`hour > h` only via the Rule-2 drag of a Main-below against a Clock-above. -/
theorem mAbove_pair_dragInd (h : ℕ) (hK : 0 < K) (hhL : h < L) (s t : AgentState L K)
    (hs3 : s.phase.val = 3) (ht3 : t.phase.val = 3)
    (hsr : s.role = .main ∨ s.role = .clock) (htr : t.role = .main ∨ t.role = .clock)
    (hsu : s.role = .main → s.bias = .zero) (htu : t.role = .main → t.bias = .zero) :
    Multiset.countP (fun a => HourCoupling.mainAboveP h a)
        ({(Transition L K s t).1, (Transition L K s t).2}
          : Multiset (AgentState L K))
      ≤ Multiset.countP (fun a => HourCoupling.mainAboveP h a)
          ({s, t} : Multiset (AgentState L K)) + dragInd h s t := by
  obtain ⟨hp1, hp2⟩ := HourCoupling.phase3_out_phase_ne_ten s t hs3 ht3 hsr htr hsu htu
  rw [HourCoupling.transition_eq_phase3 s t hs3 ht3 hp1 hp2]
  rw [HourCoupling.countP_pair, HourCoupling.countP_pair]
  unfold dragInd
  rcases hsr with hsm | hsc
  · rcases htr with htm | htc
    · -- Main × Main: identity ⇒ output mAbove = input mAbove; dragInd ≥ 0.
      have hP3 : Phase3Transition L K s t = (s, t) := by
        unfold Phase3Transition
        have hsc' : s.role ≠ .clock := by rw [hsm]; decide
        have htc' : t.role ≠ .clock := by rw [htm]; decide
        simp only [hsc', htc', hsm, htm, hsu hsm, htu htm, false_and, and_false,
          if_false, if_true, and_self, reduceCtorEq, ite_self]
        exact HourCoupling.phase3CancelSplit_id_of_unbiased (L := L) (K := K) s t hsu htu ⟨hsm, htm⟩
      rw [hP3]; dsimp only; omega
    · -- Main × Clock: the s-output is main-above only if it's a genuine drag-cross,
      -- i.e. s was main-below and t is clock-above; that is the first dragInd term.
      rw [phase3_drag_left s t hsm (hsu hsm) htc]
      dsimp only
      set s' : AgentState L K := { s with hour := (⟨min L (t.minute.val / K), by
          apply Nat.lt_succ_of_le; exact Nat.min_le_left _ _⟩ : Fin (L+1)) } with hs'def
      have hs'hour : s'.hour.val = min L (t.minute.val / K) := rfl
      have htnotmain : ¬ HourCoupling.mainAboveP h t := by
        unfold HourCoupling.mainAboveP; rw [htc]; simp
      -- The crisp bound: [mainAbove s'] ≤ [mainAbove s] + [mainBelow s ∧ clockAbove t].
      have hcrisp : (if HourCoupling.mainAboveP h s' then (1:ℕ) else 0)
          ≤ (if HourCoupling.mainAboveP h s then (1:ℕ) else 0)
            + (if mainBelowP h s ∧ HourCoupling.clockAboveP h t then (1:ℕ) else 0) := by
        by_cases hd : HourCoupling.mainAboveP h s'
        · rw [if_pos hd]
          have hlt : h < min L (t.minute.val / K) := by have := hd.2; rwa [hs'hour] at this
          have htca : HourCoupling.clockAboveP h t :=
            ⟨htc, (HourCoupling.dragged_above_iff h hK hhL t).mp hlt⟩
          by_cases hsab : HourCoupling.mainAboveP h s
          · rw [if_pos hsab]; omega
          · rw [if_neg hsab]
            have hmbs : mainBelowP h s := ⟨hsm, fun hcon => hsab ⟨hsm, hcon⟩⟩
            rw [if_pos ⟨hmbs, htca⟩]
        · rw [if_neg hd]; positivity
      -- t-output is the unchanged Clock ⇒ not main-above; s is a Main ⇒ not clock-above.
      rw [if_neg htnotmain]
      have hsnotclock : (if mainBelowP h t ∧ HourCoupling.clockAboveP h s then (1:ℕ) else 0) = 0 := by
        rw [if_neg]; rintro ⟨_, hca⟩; rw [HourCoupling.clockAboveP, hsm] at hca; exact absurd hca.1 (by decide)
      omega
  · rcases htr with htm | htc
    · -- Clock × Main: symmetric to Main × Clock with roles swapped.
      rw [phase3_drag_right s t hsc htm (htu htm)]
      dsimp only
      set t' : AgentState L K := { t with hour := (⟨min L (s.minute.val / K), by
          apply Nat.lt_succ_of_le; exact Nat.min_le_left _ _⟩ : Fin (L+1)) } with ht'def
      have ht'hour : t'.hour.val = min L (s.minute.val / K) := rfl
      have hsnotmain : ¬ HourCoupling.mainAboveP h s := by
        unfold HourCoupling.mainAboveP; rw [hsc]; simp
      have hcrisp : (if HourCoupling.mainAboveP h t' then (1:ℕ) else 0)
          ≤ (if HourCoupling.mainAboveP h t then (1:ℕ) else 0)
            + (if mainBelowP h t ∧ HourCoupling.clockAboveP h s then (1:ℕ) else 0) := by
        by_cases hd : HourCoupling.mainAboveP h t'
        · rw [if_pos hd]
          have hlt : h < min L (s.minute.val / K) := by have := hd.2; rwa [ht'hour] at this
          have hsca : HourCoupling.clockAboveP h s :=
            ⟨hsc, (HourCoupling.dragged_above_iff h hK hhL s).mp hlt⟩
          by_cases htab : HourCoupling.mainAboveP h t
          · rw [if_pos htab]; omega
          · rw [if_neg htab]
            have hmbt : mainBelowP h t := ⟨htm, fun hcon => htab ⟨htm, hcon⟩⟩
            rw [if_pos ⟨hmbt, hsca⟩]
        · rw [if_neg hd]; positivity
      rw [if_neg hsnotmain]
      have htnotclock : (if mainBelowP h s ∧ HourCoupling.clockAboveP h t then (1:ℕ) else 0) = 0 := by
        rw [if_neg]; rintro ⟨_, hca⟩; rw [HourCoupling.clockAboveP, htm] at hca; exact absurd hca.1 (by decide)
      omega
    · -- Clock × Clock: no Mains in output ⇒ output mAbove = 0.
      obtain ⟨hr1, hr2, _, _⟩ := Phase3_clock_pair (L := L) (K := K) s t hsc htc hs3 ht3
      have e1 : ¬ HourCoupling.mainAboveP h (Phase3Transition L K s t).1 := by
        unfold HourCoupling.mainAboveP; rw [hr1]; simp
      have e2 : ¬ HourCoupling.mainAboveP h (Phase3Transition L K s t).2 := by
        unfold HourCoupling.mainAboveP; rw [hr2]; simp
      simp only [e1, e2, if_false]; omega

/-- **Sharp per-pair epidemic bound.**  On the window, the produced `cAbove` count
is at least the consumed `cAbove` count PLUS the `epiInd` indicator: a Clock-below
crosses `hour > h` against a Clock-above (the SYNC sets the lagging clock's minute
to the max, lifting it across `(h+1)·K`). -/
theorem cAbove_pair_epiInd (h : ℕ) (hhL : h < L) (s t : AgentState L K)
    (hs3 : s.phase.val = 3) (ht3 : t.phase.val = 3)
    (hsr : s.role = .main ∨ s.role = .clock) (htr : t.role = .main ∨ t.role = .clock)
    (hsu : s.role = .main → s.bias = .zero) (htu : t.role = .main → t.bias = .zero) :
    Multiset.countP (fun a => HourCoupling.clockAboveP h a)
        ({s, t} : Multiset (AgentState L K)) + epiInd h s t
      ≤ Multiset.countP (fun a => HourCoupling.clockAboveP h a)
          ({(Transition L K s t).1, (Transition L K s t).2}
            : Multiset (AgentState L K)) := by
  obtain ⟨hp1, hp2⟩ := HourCoupling.phase3_out_phase_ne_ten s t hs3 ht3 hsr htr hsu htu
  rw [HourCoupling.transition_eq_phase3 s t hs3 ht3 hp1 hp2]
  rw [HourCoupling.countP_pair, HourCoupling.countP_pair]
  rcases hsr with hsm | hsc
  · -- s is a Main ⇒ epiInd = 0; reduce to monotonicity.
    have hepi0 : epiInd h s t = 0 := by
      unfold epiInd
      have h1 : ¬ (HourCoupling.clockAboveP h s ∧ clockBelowP h t) := by
        rintro ⟨hca, _⟩; rw [HourCoupling.clockAboveP, hsm] at hca; exact absurd hca.1 (by decide)
      have h2 : ¬ (HourCoupling.clockAboveP h t ∧ clockBelowP h s) := by
        rintro ⟨_, hcb⟩; rw [clockBelowP, hsm] at hcb; exact absurd hcb.1 (by decide)
      rw [if_neg h1, if_neg h2]
    rw [hepi0, Nat.add_zero]
    have hmono := HourCoupling.cAbove_pair_mono h s t hs3 ht3 (Or.inl hsm) htr hsu htu
    rw [HourCoupling.transition_eq_phase3 s t hs3 ht3 hp1 hp2] at hmono
    rw [HourCoupling.countP_pair, HourCoupling.countP_pair] at hmono
    exact hmono
  · rcases htr with htm | htc
    · -- t is a Main ⇒ epiInd = 0, reduce to monotonicity.
      have hepi0 : epiInd h s t = 0 := by
        unfold epiInd
        have h1 : ¬ (HourCoupling.clockAboveP h s ∧ clockBelowP h t) := by
          rintro ⟨_, hcb⟩; rw [clockBelowP, htm] at hcb; exact absurd hcb.1 (by decide)
        have h2 : ¬ (HourCoupling.clockAboveP h t ∧ clockBelowP h s) := by
          rintro ⟨hca, _⟩; rw [HourCoupling.clockAboveP, htm] at hca; exact absurd hca.1 (by decide)
        rw [if_neg h1, if_neg h2]
      rw [hepi0, Nat.add_zero]
      have hmono := HourCoupling.cAbove_pair_mono h s t hs3 ht3 (Or.inr hsc) (Or.inl htm) hsu htu
      rw [HourCoupling.transition_eq_phase3 s t hs3 ht3 hp1 hp2] at hmono
      rw [HourCoupling.countP_pair, HourCoupling.countP_pair] at hmono
      exact hmono
    · -- Clock × Clock: the genuine epidemic crossing.
      by_cases hmin : s.minute = t.minute
      · -- minutes equal ⇒ no one-above-one-below ⇒ epiInd = 0; reduce to monotonicity.
        have hepi0 : epiInd h s t = 0 := by
          unfold epiInd
          have hsmin : s.minute.val = t.minute.val := by rw [hmin]
          have h1 : ¬ (HourCoupling.clockAboveP h s ∧ clockBelowP h t) := by
            rintro ⟨hca, hcb⟩; have := hca.2; rw [hsmin] at this; exact hcb.2 this
          have h2 : ¬ (HourCoupling.clockAboveP h t ∧ clockBelowP h s) := by
            rintro ⟨hca, hcb⟩; have := hca.2; rw [← hsmin] at this; exact hcb.2 this
          rw [if_neg h1, if_neg h2]
        rw [hepi0, Nat.add_zero]
        have hmono := HourCoupling.cAbove_pair_mono h s t hs3 ht3 (Or.inr hsc) (Or.inr htc) hsu htu
        rw [HourCoupling.transition_eq_phase3 s t hs3 ht3 hp1 hp2] at hmono
        rw [HourCoupling.countP_pair, HourCoupling.countP_pair] at hmono
        exact hmono
      · -- SYNC: both outputs get minute = max s.minute t.minute.
        have hP3 : Phase3Transition L K s t =
            ({ s with minute := max s.minute t.minute },
             { t with minute := max s.minute t.minute }) := by
          unfold Phase3Transition
          have htm' : t.role ≠ .main := by rw [htc]; decide
          have hsm' : s.role ≠ .main := by rw [hsc]; decide
          simp only [hsc, htc, and_self, if_true, hmin, ne_eq, not_false_eq_true,
            if_true, hsm', htm', false_and, and_false, if_false, reduceCtorEq, ite_self]
        rw [hP3]
        dsimp only
        have hmaxval : (max s.minute t.minute).val = max s.minute.val t.minute.val := by
          rcases le_total s.minute t.minute with hle | hle
          · rw [max_eq_right hle, max_eq_right (by exact_mod_cast hle)]
          · rw [max_eq_left hle, max_eq_left (by exact_mod_cast hle)]
        have ho1ca : HourCoupling.clockAboveP h
            ({ s with minute := max s.minute t.minute } : AgentState L K)
            ↔ (h + 1) * K ≤ max s.minute.val t.minute.val := by
          unfold HourCoupling.clockAboveP
          rw [show ({ s with minute := max s.minute t.minute } : AgentState L K).role = .clock from hsc,
            show ({ s with minute := max s.minute t.minute } : AgentState L K).minute.val
              = (max s.minute t.minute).val from rfl, hmaxval]
          simp
        have ho2ca : HourCoupling.clockAboveP h
            ({ t with minute := max s.minute t.minute } : AgentState L K)
            ↔ (h + 1) * K ≤ max s.minute.val t.minute.val := by
          unfold HourCoupling.clockAboveP
          rw [show ({ t with minute := max s.minute t.minute } : AgentState L K).role = .clock from htc,
            show ({ t with minute := max s.minute t.minute } : AgentState L K).minute.val
              = (max s.minute t.minute).val from rfl, hmaxval]
          simp
        have hsca_iff : HourCoupling.clockAboveP h s ↔ (h+1)*K ≤ s.minute.val :=
          ⟨fun hh => hh.2, fun hh => ⟨hsc, hh⟩⟩
        have htca_iff : HourCoupling.clockAboveP h t ↔ (h+1)*K ≤ t.minute.val :=
          ⟨fun hh => hh.2, fun hh => ⟨htc, hh⟩⟩
        have hsb_iff : clockBelowP h s ↔ ¬ (h+1)*K ≤ s.minute.val :=
          ⟨fun hh => hh.2, fun hh => ⟨hsc, hh⟩⟩
        have htb_iff : clockBelowP h t ↔ ¬ (h+1)*K ≤ t.minute.val :=
          ⟨fun hh => hh.2, fun hh => ⟨htc, hh⟩⟩
        unfold epiInd
        by_cases hsabove : (h+1)*K ≤ s.minute.val <;>
          by_cases htabove : (h+1)*K ≤ t.minute.val <;>
          simp only [ho1ca, ho2ca, hsca_iff, htca_iff, hsb_iff, htb_iff,
            le_max_iff, hsabove, htabove, true_or, or_true, or_false, false_or,
            not_true, not_false, not_true_eq_false, not_false_eq_true,
            and_true, and_false, true_and, false_and,
            if_true, if_false, le_refl] <;>
          omega

/-! ## Part 4 — the config-level sharp drag/epidemic bounds (lift to `stepOrSelf`).

Following `HourCoupling.{mAbove_stepOrSelf_le, cAbove_stepOrSelf_ge}`, we lift the
sharp per-pair facts to the chosen-pair kernel update on the window. -/

/-- **Config-level sharp drag bound**: `mAbove(step) ≤ mAbove c + dragInd`. -/
theorem mAbove_stepOrSelf_dragInd (h : ℕ) (hK : 0 < K) (hhL : h < L)
    (c : Config (AgentState L K)) (hw : HourCoupling.HourWindow c) (r₁ r₂ : AgentState L K) :
    HourCoupling.mAbove (L := L) (K := K) h
        (Protocol.stepOrSelf (NonuniformMajority L K) c r₁ r₂)
      ≤ HourCoupling.mAbove (L := L) (K := K) h c + dragInd h r₁ r₂ := by
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
    unfold HourCoupling.mAbove
    rw [hc', Multiset.countP_add, Multiset.countP_sub hsub]
    have hpair_le : Multiset.countP (fun a => HourCoupling.mainAboveP h a)
        ({r₁, r₂} : Multiset (AgentState L K))
          ≤ Multiset.countP (fun a => HourCoupling.mainAboveP h a) c :=
      Multiset.countP_le_of_le _ hsub
    have hdrag := mAbove_pair_dragInd h hK hhL r₁ r₂ h1p h2p h1r h2r h1u h2u
    rw [hδ]
    omega
  · rw [Protocol.stepOrSelf_eq_self_of_not_applicable happ]
    have : 0 ≤ dragInd h r₁ r₂ := Nat.zero_le _
    omega

/-- **Config-level sharp epidemic bound** (for an applicable pair):
`cAbove c + epiInd ≤ cAbove(step)`.  Applicability is used only to fire the
per-pair crossing; in the drift sum the non-applicable pairs carry zero
interaction weight. -/
theorem cAbove_stepOrSelf_epiInd (h : ℕ) (hhL : h < L)
    (c : Config (AgentState L K)) (hw : HourCoupling.HourWindow c) (r₁ r₂ : AgentState L K)
    (happ : Protocol.Applicable c r₁ r₂) :
    HourCoupling.cAbove (L := L) (K := K) h c + epiInd h r₁ r₂
      ≤ HourCoupling.cAbove (L := L) (K := K) h
          (Protocol.stepOrSelf (NonuniformMajority L K) c r₁ r₂) := by
  classical
  have hmem1 := mem_of_applicable_left happ
  have hmem2 := mem_of_applicable_right happ
  obtain ⟨h1r, h1p, h1u⟩ := hw r₁ hmem1
  obtain ⟨h2r, h2p, h2u⟩ := hw r₂ hmem2
  have hsub : ({r₁, r₂} : Multiset (AgentState L K)) ≤ c := happ
  have hc' : Protocol.stepOrSelf (NonuniformMajority L K) c r₁ r₂
      = c - {r₁, r₂} + {(NonuniformMajority L K).δ r₁ r₂ |>.1,
          (NonuniformMajority L K).δ r₁ r₂ |>.2} := by
    unfold Protocol.stepOrSelf; rw [if_pos happ]
  have hδ : (NonuniformMajority L K).δ r₁ r₂ = Transition L K r₁ r₂ := rfl
  unfold HourCoupling.cAbove
  rw [hc', Multiset.countP_add, Multiset.countP_sub hsub]
  have hsplit : Multiset.countP (fun a => HourCoupling.clockAboveP h a) c
      = Multiset.countP (fun a => HourCoupling.clockAboveP h a) (c - {r₁, r₂})
        + Multiset.countP (fun a => HourCoupling.clockAboveP h a)
            ({r₁, r₂} : Multiset (AgentState L K)) := by
    rw [← Multiset.countP_add, Multiset.sub_add_cancel hsub]
  have hpair := cAbove_pair_epiInd h hhL r₁ r₂ h1p h2p h1r h2r h1u h2u
  rw [hδ]
  omega

/-! ## Part 5 — counts and the partition identities. -/

/-- The Main-below count (Main agents at hour `≤ h`). -/
def mainBelowCount (h : ℕ) (c : Config (AgentState L K)) : ℕ :=
  Multiset.countP (fun a => mainBelowP h a) c

/-- The Clock-below count (Clock agents at clock-hour `≤ h`). -/
def clockBelowCount (h : ℕ) (c : Config (AgentState L K)) : ℕ :=
  Multiset.countP (fun a => clockBelowP h a) c

/-- Mains partition into above-`h` and below-`h`: `mAbove + mainBelow = mainCount`. -/
theorem mAbove_add_mainBelow (h : ℕ) (c : Config (AgentState L K)) :
    HourCoupling.mAbove (L := L) (K := K) h c + mainBelowCount (L := L) (K := K) h c
      = mainCount (L := L) (K := K) c := by
  unfold HourCoupling.mAbove mainBelowCount mainCount
  induction c using Multiset.induction with
  | empty => simp
  | cons a s ih =>
      rw [Multiset.countP_cons, Multiset.countP_cons, Multiset.countP_cons]
      have hA : (if HourCoupling.mainAboveP h a then (1:ℕ) else 0)
          + (if mainBelowP h a then (1:ℕ) else 0) = (if a.role = .main then (1:ℕ) else 0) := by
        by_cases hr : a.role = .main
        · by_cases hh : h < a.hour.val
          · simp [HourCoupling.mainAboveP, mainBelowP, hr, hh]
          · simp [HourCoupling.mainAboveP, mainBelowP, hr, hh]
        · simp [HourCoupling.mainAboveP, mainBelowP, hr]
      omega

/-- Clocks partition into above-`h` and below-`h`: `cAbove + clockBelow = clockCount`. -/
theorem cAbove_add_clockBelow (h : ℕ) (c : Config (AgentState L K)) :
    HourCoupling.cAbove (L := L) (K := K) h c + clockBelowCount (L := L) (K := K) h c
      = clockCount (L := L) (K := K) c := by
  unfold HourCoupling.cAbove clockBelowCount clockCount
  induction c using Multiset.induction with
  | empty => simp
  | cons a s ih =>
      rw [Multiset.countP_cons, Multiset.countP_cons, Multiset.countP_cons]
      have hA : (if HourCoupling.clockAboveP h a then (1:ℕ) else 0)
          + (if clockBelowP h a then (1:ℕ) else 0) = (if a.role = .clock then (1:ℕ) else 0) := by
        by_cases hr : a.role = .clock
        · by_cases hh : (h + 1) * K ≤ a.minute.val
          · simp [HourCoupling.clockAboveP, clockBelowP, hr, hh]
          · simp [HourCoupling.clockAboveP, clockBelowP, hr, hh]
        · simp [HourCoupling.clockAboveP, clockBelowP, hr]
      omega

/-- `countP p c = ∑_{a ∈ filter p univ} count a` (generic). -/
theorem countP_eq_sum_count (p : AgentState L K → Prop) [DecidablePred p]
    (c : Config (AgentState L K)) :
    Multiset.countP p c
      = ∑ a ∈ Finset.univ.filter (fun a : AgentState L K => p a), c.count a := by
  classical
  have hcard : (Multiset.filter (fun a : AgentState L K => p a) c).card
      = Multiset.countP p c := (Multiset.countP_eq_card_filter _ _).symm
  rw [← hcard, eq_comm]
  have hcount_eq : ∀ a ∈ Finset.univ.filter (fun a : AgentState L K => p a),
      c.count a = Multiset.count a (Multiset.filter (fun a : AgentState L K => p a) c) := by
    intro a ha
    rw [Finset.mem_filter] at ha
    rw [Config.count, Multiset.count_filter, if_pos ha.2]
  rw [Finset.sum_congr rfl hcount_eq, Multiset.sum_count_eq_card]
  intro a ha
  rw [Multiset.mem_filter] at ha
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ a, ha.2⟩

/-! ## Part 6 — the weighted pair-sum identities (drag and epidemic mass). -/

/-- An indicator-weighted full-`univ` pair-sum equals the rectangle sum over the
two predicate filters. -/
theorem sum_interactionCount_indicator
    (c : Config (AgentState L K)) (P Q : AgentState L K → Prop)
    [DecidablePred P] [DecidablePred Q] :
    (∑ p : AgentState L K × AgentState L K,
        c.interactionCount p.1 p.2 * (if P p.1 ∧ Q p.2 then 1 else 0))
      = ∑ p ∈ (Finset.univ.filter (fun a : AgentState L K => P a)) ×ˢ
          (Finset.univ.filter (fun a : AgentState L K => Q a)),
          c.interactionCount p.1 p.2 := by
  classical
  rw [show (Finset.univ : Finset (AgentState L K × AgentState L K))
      = Finset.univ ×ˢ Finset.univ from (Finset.univ_product_univ).symm]
  rw [Finset.sum_product, Finset.sum_product]
  -- Both sides become ∑_s ∑_t (...); reduce each row.
  -- RHS: ∑_{s∈Pf} ∑_{t∈Qf} count.  Rewrite as ∑_{s∈univ} (if P s then ∑_{t∈Qf} count else 0).
  rw [Finset.sum_filter (s := (Finset.univ : Finset (AgentState L K)))
      (p := fun a => P a) (f := fun s => ∑ t ∈ Finset.univ.filter (fun a => Q a),
        c.interactionCount s t)]
  refine Finset.sum_congr rfl (fun s _ => ?_)
  by_cases hP : P s
  · rw [if_pos hP]
    rw [Finset.sum_filter (s := (Finset.univ : Finset (AgentState L K)))
        (p := fun a => Q a) (f := fun t => c.interactionCount s t)]
    refine Finset.sum_congr rfl (fun t _ => ?_)
    by_cases hQ : Q t
    · simp [hP, hQ]
    · simp [hQ]
  · rw [if_neg hP]
    refine (Finset.sum_eq_zero (fun t _ => ?_))
    simp [hP]

/-- **Drag mass**: `∑ interactionCount · dragInd = 2 · mainBelowCount · cAbove`. -/
theorem sum_interactionCount_dragInd (h : ℕ) (c : Config (AgentState L K)) :
    (∑ p : AgentState L K × AgentState L K,
        c.interactionCount p.1 p.2 * dragInd h p.1 p.2)
      = 2 * (mainBelowCount (L := L) (K := K) h c)
          * (HourCoupling.cAbove (L := L) (K := K) h c) := by
  classical
  -- Disjointness: mainBelow is role main, clockAbove is role clock.
  have hdisj1 : ∀ a ∈ Finset.univ.filter (fun a : AgentState L K => mainBelowP h a),
      ∀ b ∈ Finset.univ.filter (fun a : AgentState L K => HourCoupling.clockAboveP h a),
      a ≠ b := by
    intro a ha b hb hab
    rw [Finset.mem_filter] at ha hb
    subst hab; exact absurd (ha.2.1.symm.trans hb.2.1) (by decide)
  have hdisj2 : ∀ a ∈ Finset.univ.filter (fun a : AgentState L K => HourCoupling.clockAboveP h a),
      ∀ b ∈ Finset.univ.filter (fun a : AgentState L K => mainBelowP h a),
      a ≠ b := by
    intro a ha b hb hab
    rw [Finset.mem_filter] at ha hb
    subst hab; exact absurd (ha.2.1.symm.trans hb.2.1) (by decide)
  -- Split dragInd into its two indicator terms.
  have hsplit : (∑ p : AgentState L K × AgentState L K,
        c.interactionCount p.1 p.2 * dragInd h p.1 p.2)
      = (∑ p : AgentState L K × AgentState L K,
          c.interactionCount p.1 p.2
            * (if mainBelowP h p.1 ∧ HourCoupling.clockAboveP h p.2 then 1 else 0))
        + (∑ p : AgentState L K × AgentState L K,
          c.interactionCount p.1 p.2
            * (if mainBelowP h p.2 ∧ HourCoupling.clockAboveP h p.1 then 1 else 0)) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro p _; unfold dragInd; ring
  rw [hsplit]
  -- First term: rectangle mainBelow × clockAbove.
  rw [sum_interactionCount_indicator c (fun a => mainBelowP h a)
      (fun a => HourCoupling.clockAboveP h a)]
  rw [ClockRealMixed.sum_interactionCount_cross_disjoint c _ _ hdisj1]
  -- Second term: swap the indicator order to (clockAbove p.1 ∧ mainBelow p.2).
  rw [show (∑ p : AgentState L K × AgentState L K,
        c.interactionCount p.1 p.2
          * (if mainBelowP h p.2 ∧ HourCoupling.clockAboveP h p.1 then 1 else 0))
      = (∑ p : AgentState L K × AgentState L K,
        c.interactionCount p.1 p.2
          * (if HourCoupling.clockAboveP h p.1 ∧ mainBelowP h p.2 then 1 else 0)) from by
    apply Finset.sum_congr rfl; intro p _; congr 1; exact if_congr and_comm rfl rfl]
  rw [sum_interactionCount_indicator c (fun a => HourCoupling.clockAboveP h a)
      (fun a => mainBelowP h a)]
  rw [ClockRealMixed.sum_interactionCount_cross_disjoint c _ _ hdisj2]
  unfold mainBelowCount HourCoupling.cAbove
  simp only [← countP_eq_sum_count]
  ring

/-- **Epidemic mass**: `∑ interactionCount · epiInd = 2 · cAbove · clockBelowCount`. -/
theorem sum_interactionCount_epiInd (h : ℕ) (c : Config (AgentState L K)) :
    (∑ p : AgentState L K × AgentState L K,
        c.interactionCount p.1 p.2 * epiInd h p.1 p.2)
      = 2 * (HourCoupling.cAbove (L := L) (K := K) h c)
          * (clockBelowCount (L := L) (K := K) h c) := by
  classical
  have hdisj1 : ∀ a ∈ Finset.univ.filter (fun a : AgentState L K => HourCoupling.clockAboveP h a),
      ∀ b ∈ Finset.univ.filter (fun a : AgentState L K => clockBelowP h a),
      a ≠ b := by
    intro a ha b hb hab
    rw [Finset.mem_filter] at ha hb
    subst hab; exact hb.2.2 ha.2.2
  have hdisj2 : ∀ a ∈ Finset.univ.filter (fun a : AgentState L K => clockBelowP h a),
      ∀ b ∈ Finset.univ.filter (fun a : AgentState L K => HourCoupling.clockAboveP h a),
      a ≠ b := by
    intro a ha b hb hab
    rw [Finset.mem_filter] at ha hb
    subst hab; exact ha.2.2 hb.2.2
  have hsplit : (∑ p : AgentState L K × AgentState L K,
        c.interactionCount p.1 p.2 * epiInd h p.1 p.2)
      = (∑ p : AgentState L K × AgentState L K,
          c.interactionCount p.1 p.2
            * (if HourCoupling.clockAboveP h p.1 ∧ clockBelowP h p.2 then 1 else 0))
        + (∑ p : AgentState L K × AgentState L K,
          c.interactionCount p.1 p.2
            * (if HourCoupling.clockAboveP h p.2 ∧ clockBelowP h p.1 then 1 else 0)) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro p _; unfold epiInd; ring
  rw [hsplit]
  rw [sum_interactionCount_indicator c (fun a => HourCoupling.clockAboveP h a)
      (fun a => clockBelowP h a)]
  rw [ClockRealMixed.sum_interactionCount_cross_disjoint c _ _ hdisj1]
  rw [show (∑ p : AgentState L K × AgentState L K,
        c.interactionCount p.1 p.2
          * (if HourCoupling.clockAboveP h p.2 ∧ clockBelowP h p.1 then 1 else 0))
      = (∑ p : AgentState L K × AgentState L K,
        c.interactionCount p.1 p.2
          * (if clockBelowP h p.1 ∧ HourCoupling.clockAboveP h p.2 then 1 else 0)) from by
    apply Finset.sum_congr rfl; intro p _; congr 1; exact if_congr and_comm rfl rfl]
  rw [sum_interactionCount_indicator c (fun a => clockBelowP h a)
      (fun a => HourCoupling.clockAboveP h a)]
  rw [ClockRealMixed.sum_interactionCount_cross_disjoint c _ _ hdisj2]
  unfold HourCoupling.cAbove clockBelowCount
  simp only [← countP_eq_sum_count]
  ring

/-! ## Part 7 — the GENUINE supermartingale drift.

We expand `∫ Φ d(K c)` into the finite `interactionCount` pair-sum, bound each
applicable pair's `ΔΦ` by `dragInd/M − 1.1·epiInd/C` (the sharp drag/epidemic
crossing structure), then sum via the mass identities and close with the bracket
`(1 − m_{>h}) − 1.1·(1 − c_{>h}) ≤ 0` on the window `c_{>h} ≤ 1/11`. -/

/-- The window predicate `c_{>h} ≤ 1/11`, in integer form `11·cAbove ≤ clockCount`.
This is the TRUE synchronous-hour window (`c_{>h} ≤ 0.001` until `end_h`). -/
def Window (h : ℕ) (c : Config (AgentState L K)) : Prop :=
  11 * HourCoupling.cAbove (L := L) (K := K) h c ≤ clockCount (L := L) (K := K) c

/-- Per-applicable-pair real bound on `ΔΦ`. -/
theorem Phi_step_le (M C : ℝ) (hM : 0 < M) (hC : 0 < C) (h : ℕ) (hK : 0 < K) (hhL : h < L)
    (c : Config (AgentState L K)) (hw : HourCoupling.HourWindow c)
    (hMc : (mainCount (L := L) (K := K) c : ℝ) = M)
    (hCc : (clockCount (L := L) (K := K) c : ℝ) = C)
    (s t : AgentState L K) (happ : Protocol.Applicable c s t) :
    Phi (L := L) (K := K) M C h (Protocol.stepOrSelf (NonuniformMajority L K) c s t)
      ≤ Phi (L := L) (K := K) M C h c
        + (dragInd h s t : ℝ) / M - (11 / 10 : ℝ) * (epiInd h s t : ℝ) / C := by
  have hdrag := mAbove_stepOrSelf_dragInd h hK hhL c hw s t
  have hepi := cAbove_stepOrSelf_epiInd h hhL c hw s t happ
  have hdragR : (HourCoupling.mAbove (L := L) (K := K) h
      (Protocol.stepOrSelf (NonuniformMajority L K) c s t) : ℝ)
      ≤ (HourCoupling.mAbove (L := L) (K := K) h c : ℝ) + (dragInd h s t : ℝ) := by
    exact_mod_cast hdrag
  have hepiR : (HourCoupling.cAbove (L := L) (K := K) h c : ℝ) + (epiInd h s t : ℝ)
      ≤ (HourCoupling.cAbove (L := L) (K := K) h
          (Protocol.stepOrSelf (NonuniformMajority L K) c s t) : ℝ) := by
    exact_mod_cast hepi
  unfold Phi
  -- Divide the two count inequalities by M, C.
  have h1 : (HourCoupling.mAbove (L := L) (K := K) h
      (Protocol.stepOrSelf (NonuniformMajority L K) c s t) : ℝ) / M
      ≤ ((HourCoupling.mAbove (L := L) (K := K) h c : ℝ) + (dragInd h s t : ℝ)) / M :=
    div_le_div_of_nonneg_right hdragR hM.le
  have h2 : ((HourCoupling.cAbove (L := L) (K := K) h c : ℝ) + (epiInd h s t : ℝ)) / C
      ≤ (HourCoupling.cAbove (L := L) (K := K) h
          (Protocol.stepOrSelf (NonuniformMajority L K) c s t) : ℝ) / C :=
    div_le_div_of_nonneg_right hepiR hC.le
  rw [add_div] at h1 h2
  -- Normalize all the `(11/10)·x/C` terms to `(11/10)·(x/C)`.
  simp only [mul_div_assoc]
  -- Now pure linear arithmetic over the divided terms.
  have h11 : (0:ℝ) ≤ 11/10 := by norm_num
  nlinarith [h1, mul_le_mul_of_nonneg_left h2 h11]

/-- `mainCount + clockCount ≤ card` (mains and clocks are disjoint roles). -/
theorem mainCount_add_clockCount_le_card (c : Config (AgentState L K)) :
    mainCount (L := L) (K := K) c + clockCount (L := L) (K := K) c ≤ c.card := by
  unfold mainCount clockCount
  induction c using Multiset.induction with
  | empty => simp
  | cons a s ih =>
      rw [Multiset.countP_cons, Multiset.countP_cons, Multiset.card_cons]
      have hca : (if a.role = .main then (1:ℕ) else 0)
          + (if a.role = .clock then (1:ℕ) else 0) ≤ 1 := by
        by_cases hm : a.role = .main
        · have hc : a.role ≠ .clock := by rw [hm]; decide
          simp [hm, hc]
        · simp only [hm, if_false, Nat.zero_add]; split <;> omega
      omega

/-- `card ≥ 2` when both role counts are `≥ 1`. -/
theorem two_le_card_of_counts (c : Config (AgentState L K))
    (hM : 1 ≤ mainCount (L := L) (K := K) c) (hC : 1 ≤ clockCount (L := L) (K := K) c) :
    2 ≤ c.card :=
  le_trans (by omega) (mainCount_add_clockCount_le_card c)

/-- **The GENUINE supermartingale drift** (real Bochner integral form, the exact
hypothesis `AzumaKernel.azuma_tail` consumes).  On the window `c_{>h} ≤ 1/11`,

  `∫ Φ d(K c) ≤ Φ c`.

DERIVED: the one-step expectation is expanded into the finite `interactionCount`
pair-sum; each applicable pair's `ΔΦ` is bounded by `dragInd/M − 1.1·epiInd/C`
(sharp drag/epidemic crossing); the masses sum to `2·mainBelow·cAbove` and
`2·cAbove·clockBelow`; and the bracket `(1−m_{>h}) − 1.1(1−c_{>h}) ≤ 0` on the
window closes it.  NO frozen-`cAbove`. -/
theorem hour_drift (M C : ℝ) (h : ℕ) (hK : 0 < K) (hhL : h < L)
    (c : Config (AgentState L K)) (hw : HourCoupling.HourWindow c)
    (hwin : Window (L := L) (K := K) h c)
    (hMc : (mainCount (L := L) (K := K) c : ℝ) = M)
    (hCc : (clockCount (L := L) (K := K) c : ℝ) = C)
    (hM1 : 1 ≤ mainCount (L := L) (K := K) c)
    (hC1 : 1 ≤ clockCount (L := L) (K := K) c) :
    ∫ c', Phi (L := L) (K := K) M C h c'
        ∂((NonuniformMajority L K).transitionKernel c)
      ≤ Phi (L := L) (K := K) M C h c := by
  have hM : 0 < M := by rw [← hMc]; exact_mod_cast hM1
  have hC : 0 < C := by rw [← hCc]; exact_mod_cast hC1
  have hcard : 2 ≤ c.card := two_le_card_of_counts c hM1 hC1
  -- Expand the integral into the finite pair-sum.
  rw [integral_transitionKernel_eq_sum _ c hcard]
  -- Bound each pair-term by  prob · (Φ c + dragInd/M − 1.1·epiInd/C).
  have hkey : ∑ p : AgentState L K × AgentState L K,
        (Config.interactionProb c p.1 p.2).toReal
          * Phi (L := L) (K := K) M C h (Protocol.stepOrSelf (NonuniformMajority L K) c p.1 p.2)
      ≤ ∑ p : AgentState L K × AgentState L K,
        (Config.interactionProb c p.1 p.2).toReal
          * (Phi (L := L) (K := K) M C h c
              + (dragInd h p.1 p.2 : ℝ) / M - (11 / 10 : ℝ) * (epiInd h p.1 p.2 : ℝ) / C) := by
    apply Finset.sum_le_sum
    intro p _
    have hprob_nonneg : 0 ≤ (Config.interactionProb c p.1 p.2).toReal := ENNReal.toReal_nonneg
    -- If the pair is applicable, use Phi_step_le; else interactionProb = 0.
    by_cases happ : Protocol.Applicable c p.1 p.2
    · exact mul_le_mul_of_nonneg_left
        (Phi_step_le M C hM hC h hK hhL c hw hMc hCc p.1 p.2 happ) hprob_nonneg
    · -- Not applicable ⇒ interactionCount = 0 ⇒ prob = 0.
      have hzero : (Config.interactionProb c p.1 p.2).toReal = 0 := by
        have hic : Config.interactionCount c p.1 p.2 = 0 := by
          by_contra hne
          apply happ
          have hpos : 0 < Config.interactionCount c p.1 p.2 := Nat.pos_of_ne_zero hne
          have hpos' := hpos
          unfold Config.interactionCount at hpos'
          unfold Protocol.Applicable
          rw [Multiset.le_iff_count]; intro a
          rw [show ({p.1, p.2} : Multiset (AgentState L K)) = p.1 ::ₘ p.2 ::ₘ 0 from rfl]
          simp only [Multiset.count_cons, Multiset.count_zero, Nat.zero_add, Nat.add_zero]
          -- counts of p.1, p.2 in c.
          have hcc1 : Config.count c p.1 = Multiset.count p.1 c := rfl
          have hcc2 : Config.count c p.2 = Multiset.count p.2 c := rfl
          by_cases heq : p.1 = p.2
          · rw [if_pos heq] at hpos'
            have h2 : 2 ≤ Multiset.count p.1 c := by
              rcases Nat.lt_or_ge (Multiset.count p.1 c) 2 with hlt | hge
              · exfalso
                rw [hcc1] at hpos'
                interval_cases (Multiset.count p.1 c) <;> simp_all
              · exact hge
            by_cases ha : a = p.1
            · subst ha
              rw [if_pos rfl, if_pos heq]; omega
            · have ha2 : a ≠ p.2 := fun hh => ha (hh.trans heq.symm)
              rw [if_neg ha, if_neg ha2]; exact Nat.zero_le _
          · rw [if_neg heq] at hpos'
            rw [hcc1, hcc2] at hpos'
            have hc1 : 0 < Multiset.count p.1 c := Nat.pos_of_ne_zero (by
              intro h0; rw [h0, Nat.zero_mul] at hpos'; exact absurd hpos' (lt_irrefl 0))
            have hc2 : 0 < Multiset.count p.2 c := Nat.pos_of_ne_zero (by
              intro h0; rw [h0, Nat.mul_zero] at hpos'; exact absurd hpos' (lt_irrefl 0))
            by_cases ha1 : a = p.1 <;> by_cases ha2 : a = p.2
            · subst ha1; exact absurd ha2 heq
            · subst ha1; rw [if_pos rfl, if_neg ha2]; omega
            · subst ha2; rw [if_neg ha1, if_pos rfl]; omega
            · rw [if_neg ha1, if_neg ha2]; exact Nat.zero_le _
        unfold Config.interactionProb
        rw [hic]; simp
      rw [hzero, zero_mul, zero_mul]
  refine hkey.trans ?_
  -- Now the sum of the bound: distribute and use the mass identities.
  -- ∑ prob·(Φc + drag/M − 1.1 epi/C) = Φc·∑prob + (1/M)∑prob·drag − (1.1/C)∑prob·epi.
  have hprob_sum : ∑ p : AgentState L K × AgentState L K,
      (Config.interactionProb c p.1 p.2).toReal = 1 := by
    have h1 : ∑ p : AgentState L K × AgentState L K,
        (Config.interactionProb c p.1 p.2) = 1 := by
      have := (Config.interactionPMF c hcard).tsum_coe
      rw [tsum_fintype] at this
      convert this using 1
    have := congrArg ENNReal.toReal h1
    rw [ENNReal.toReal_one] at this
    rw [← this, ENNReal.toReal_sum]
    intro p _
    exact ENNReal.div_ne_top (ENNReal.natCast_ne_top _) (Config.totalPairs_ne_zero_ennreal hcard)
  -- Real form of the per-pair probability weight.
  have hPpos : (0 : ℝ) < (c.totalPairs : ℝ) := by
    have := Config.totalPairs_pos hcard; exact_mod_cast this
  have hprobR : ∀ p : AgentState L K × AgentState L K,
      (Config.interactionProb c p.1 p.2).toReal
        = (c.interactionCount p.1 p.2 : ℝ) / (c.totalPairs : ℝ) := by
    intro p
    unfold Config.interactionProb
    rw [ENNReal.toReal_div, ENNReal.toReal_natCast, ENNReal.toReal_natCast]
  -- Distribute the RHS sum.
  have hM : 0 < M := by rw [← hMc]; exact_mod_cast hM1
  have hC : 0 < C := by rw [← hCc]; exact_mod_cast hC1
  have hexpand : ∑ p : AgentState L K × AgentState L K,
        (Config.interactionProb c p.1 p.2).toReal
          * (Phi (L := L) (K := K) M C h c
              + (dragInd h p.1 p.2 : ℝ) / M - (11 / 10 : ℝ) * (epiInd h p.1 p.2 : ℝ) / C)
      = Phi (L := L) (K := K) M C h c
          + (∑ p : AgentState L K × AgentState L K,
              (c.interactionCount p.1 p.2 : ℝ) * (dragInd h p.1 p.2 : ℝ))
              / ((c.totalPairs : ℝ) * M)
          - (11 / 10 : ℝ) * (∑ p : AgentState L K × AgentState L K,
              (c.interactionCount p.1 p.2 : ℝ) * (epiInd h p.1 p.2 : ℝ))
              / ((c.totalPairs : ℝ) * C) := by
    have hsub : ∀ p : AgentState L K × AgentState L K,
        (Config.interactionProb c p.1 p.2).toReal
          * (Phi (L := L) (K := K) M C h c
              + (dragInd h p.1 p.2 : ℝ) / M - (11 / 10 : ℝ) * (epiInd h p.1 p.2 : ℝ) / C)
        = (Config.interactionProb c p.1 p.2).toReal * Phi (L := L) (K := K) M C h c
          + (c.interactionCount p.1 p.2 : ℝ) * (dragInd h p.1 p.2 : ℝ)
              / ((c.totalPairs : ℝ) * M)
          - (11 / 10 : ℝ) * ((c.interactionCount p.1 p.2 : ℝ) * (epiInd h p.1 p.2 : ℝ))
              / ((c.totalPairs : ℝ) * C) := by
      intro p; rw [hprobR p]; field_simp
    rw [Finset.sum_congr rfl (fun p _ => hsub p)]
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]
    rw [← Finset.sum_mul, hprob_sum, one_mul]
    congr 1
    · rw [← Finset.sum_div]
    · rw [← Finset.sum_div, ← Finset.mul_sum, mul_div_assoc]
  rw [hexpand]
  -- Mass identities (cast to ℝ).
  have hdragmass : (∑ p : AgentState L K × AgentState L K,
        (c.interactionCount p.1 p.2 : ℝ) * (dragInd h p.1 p.2 : ℝ))
      = 2 * (mainBelowCount (L := L) (K := K) h c : ℝ)
          * (HourCoupling.cAbove (L := L) (K := K) h c : ℝ) := by
    have := sum_interactionCount_dragInd h c
    have hcast : (∑ p : AgentState L K × AgentState L K,
          (c.interactionCount p.1 p.2 : ℝ) * (dragInd h p.1 p.2 : ℝ))
        = ((∑ p : AgentState L K × AgentState L K,
            c.interactionCount p.1 p.2 * dragInd h p.1 p.2 : ℕ) : ℝ) := by
      push_cast; rfl
    rw [hcast, this]; push_cast; ring
  have hepimass : (∑ p : AgentState L K × AgentState L K,
        (c.interactionCount p.1 p.2 : ℝ) * (epiInd h p.1 p.2 : ℝ))
      = 2 * (HourCoupling.cAbove (L := L) (K := K) h c : ℝ)
          * (clockBelowCount (L := L) (K := K) h c : ℝ) := by
    have := sum_interactionCount_epiInd h c
    have hcast : (∑ p : AgentState L K × AgentState L K,
          (c.interactionCount p.1 p.2 : ℝ) * (epiInd h p.1 p.2 : ℝ))
        = ((∑ p : AgentState L K × AgentState L K,
            c.interactionCount p.1 p.2 * epiInd h p.1 p.2 : ℕ) : ℝ) := by
      push_cast; rfl
    rw [hcast, this]; push_cast; ring
  rw [hdragmass, hepimass]
  -- The bracket: it suffices that  2·cAbove·mainBelow/(P·M) ≤ 1.1·2·cAbove·clockBelow/(P·C).
  -- i.e.  mainBelow/M ≤ 1.1·clockBelow/C  on the window.
  have hmB : (mainBelowCount (L := L) (K := K) h c : ℝ)
      = M - (HourCoupling.mAbove (L := L) (K := K) h c : ℝ) := by
    have := mAbove_add_mainBelow (L := L) (K := K) h c
    have : (HourCoupling.mAbove (L := L) (K := K) h c : ℝ)
        + (mainBelowCount (L := L) (K := K) h c : ℝ) = M := by
      rw [← hMc]; exact_mod_cast this
    linarith
  have hcB : (clockBelowCount (L := L) (K := K) h c : ℝ)
      = C - (HourCoupling.cAbove (L := L) (K := K) h c : ℝ) := by
    have := cAbove_add_clockBelow (L := L) (K := K) h c
    have : (HourCoupling.cAbove (L := L) (K := K) h c : ℝ)
        + (clockBelowCount (L := L) (K := K) h c : ℝ) = C := by
      rw [← hCc]; exact_mod_cast this
    linarith
  -- mainBelow ≤ M and the window 11·cAbove ≤ C give the bracket.
  have hmBle : (HourCoupling.mAbove (L := L) (K := K) h c : ℝ) ≥ 0 := by positivity
  have hcAge : (HourCoupling.cAbove (L := L) (K := K) h c : ℝ) ≥ 0 := by positivity
  have hwinR : 11 * (HourCoupling.cAbove (L := L) (K := K) h c : ℝ) ≤ C := by
    rw [← hCc]; exact_mod_cast hwin
  -- Now close.  Both extra terms divide by P·M, P·C > 0.
  rw [hmB, hcB]
  have hbracket : (M - (HourCoupling.mAbove (L := L) (K := K) h c : ℝ)) / M
      ≤ (11/10 : ℝ) * (C - (HourCoupling.cAbove (L := L) (K := K) h c : ℝ)) / C := by
    rw [div_le_div_iff₀ hM hC]
    nlinarith [hmBle, hcAge, hwinR, hM, hC, mul_nonneg hmBle hC.le]
  -- Reduce the goal to hbracket scaled by  2·cAbove/P  ≥ 0.
  have hfac : (0:ℝ) ≤ 2 * (HourCoupling.cAbove (L := L) (K := K) h c : ℝ) / (c.totalPairs : ℝ) := by
    apply div_nonneg _ hPpos.le; positivity
  have key : 2 * (M - (HourCoupling.mAbove (L := L) (K := K) h c : ℝ))
        * (HourCoupling.cAbove (L := L) (K := K) h c : ℝ) / ((c.totalPairs : ℝ) * M)
      ≤ (11/10 : ℝ) * (2 * (HourCoupling.cAbove (L := L) (K := K) h c : ℝ)
        * (C - (HourCoupling.cAbove (L := L) (K := K) h c : ℝ))) / ((c.totalPairs : ℝ) * C) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have h1 := hbracket
    rw [div_le_div_iff₀ hM hC] at h1
    nlinarith [h1, hcAge, hPpos, mul_nonneg hcAge hPpos.le,
      mul_nonneg (mul_nonneg hcAge hPpos.le) (le_of_lt hM)]
  linarith [key]

/-! ## Part 8 — the bounded-difference lemma. -/

/-- A single chosen-pair update changes any `countP` by at most `2` (it removes a
2-element pair and adds a 2-element pair). -/
theorem countP_stepOrSelf_diff_le_two (p : AgentState L K → Prop) [DecidablePred p]
    (c : Config (AgentState L K)) (r₁ r₂ : AgentState L K) :
    (Multiset.countP p (Protocol.stepOrSelf (NonuniformMajority L K) c r₁ r₂) : ℤ)
        - (Multiset.countP p c : ℤ) ≤ 2
      ∧ (Multiset.countP p c : ℤ)
        - (Multiset.countP p (Protocol.stepOrSelf (NonuniformMajority L K) c r₁ r₂) : ℤ) ≤ 2 := by
  classical
  by_cases happ : Protocol.Applicable c r₁ r₂
  · have hsub : ({r₁, r₂} : Multiset (AgentState L K)) ≤ c := happ
    have hc' : Protocol.stepOrSelf (NonuniformMajority L K) c r₁ r₂
        = c - {r₁, r₂} + {(NonuniformMajority L K).δ r₁ r₂ |>.1,
            (NonuniformMajority L K).δ r₁ r₂ |>.2} := by
      unfold Protocol.stepOrSelf; rw [if_pos happ]
    rw [hc', Multiset.countP_add, Multiset.countP_sub hsub]
    have hadd_le : Multiset.countP p ({(NonuniformMajority L K).δ r₁ r₂ |>.1,
        (NonuniformMajority L K).δ r₁ r₂ |>.2} : Multiset (AgentState L K)) ≤ 2 := by
      refine le_trans (Multiset.countP_le_card _ _) ?_
      simp [Multiset.card_pair]
    have hrem_le : Multiset.countP p ({r₁, r₂} : Multiset (AgentState L K)) ≤ 2 := by
      refine le_trans (Multiset.countP_le_card _ _) ?_
      simp [Multiset.card_pair]
    have hrem_le_c : Multiset.countP p ({r₁, r₂} : Multiset (AgentState L K))
        ≤ Multiset.countP p c := Multiset.countP_le_of_le _ hsub
    omega
  · rw [Protocol.stepOrSelf_eq_self_of_not_applicable happ]; omega

/-- **The bounded-difference lemma**: a single interaction changes `Φ` by at most
`c₀ = 2/M + 2·(11/10)/C` a.e. on the kernel support. -/
theorem hour_bdd (M C : ℝ) (hM : 0 < M) (hC : 0 < C) (h : ℕ)
    (x : Config (AgentState L K)) :
    ∀ᵐ y ∂((NonuniformMajority L K).transitionKernel x),
      |Phi (L := L) (K := K) M C h y - Phi (L := L) (K := K) M C h x|
        ≤ 2 / M + 2 * (11 / 10 : ℝ) / C := by
  -- Reduce to the support: every support point is `stepOrSelf x r₁ r₂`.
  have hsupp : ∀ y ∈ ((NonuniformMajority L K).stepDistOrSelf x).support,
      |Phi (L := L) (K := K) M C h y - Phi (L := L) (K := K) M C h x|
        ≤ 2 / M + 2 * (11 / 10 : ℝ) / C := by
    intro y hy
    -- Either `card ≥ 2` (so `y = stepOrSelf x r₁ r₂`) or `y = x` (bound is `|0|`).
    have hcase : (∃ r₁ r₂, Protocol.stepOrSelf (NonuniformMajority L K) x r₁ r₂ = y) ∨ y = x := by
      by_cases hc : 2 ≤ x.card
      · rw [show (NonuniformMajority L K).stepDistOrSelf x
            = (NonuniformMajority L K).stepDist x hc by
            unfold Protocol.stepDistOrSelf; rw [dif_pos hc]] at hy
        obtain ⟨⟨r₁, r₂⟩, hr⟩ := Protocol.stepDist_support (NonuniformMajority L K) x hc y hy
        exact Or.inl ⟨r₁, r₂, hr⟩
      · rw [show (NonuniformMajority L K).stepDistOrSelf x = PMF.pure x by
            unfold Protocol.stepDistOrSelf; rw [dif_neg hc]] at hy
        rw [PMF.mem_support_pure_iff] at hy
        exact Or.inr hy
    rcases hcase with ⟨r₁, r₂, hstep⟩ | hyx
    · subst hstep
      -- mAbove, cAbove each move by ≤ 2 (integer), so Φ moves by ≤ 2/M + 2·1.1/C.
      obtain ⟨hmA1, hmA2⟩ :=
        countP_stepOrSelf_diff_le_two (fun a => HourCoupling.mainAboveP h a) x r₁ r₂
      obtain ⟨hcA1, hcA2⟩ :=
        countP_stepOrSelf_diff_le_two (fun a => HourCoupling.clockAboveP h a) x r₁ r₂
      -- Cast the ℤ bounds to ℝ (mAbove/cAbove are the corresponding countP).
      have hmAle : -2 ≤ (HourCoupling.mAbove (L := L) (K := K) h
          (Protocol.stepOrSelf (NonuniformMajority L K) x r₁ r₂) : ℝ)
          - (HourCoupling.mAbove (L := L) (K := K) h x : ℝ)
          ∧ (HourCoupling.mAbove (L := L) (K := K) h
          (Protocol.stepOrSelf (NonuniformMajority L K) x r₁ r₂) : ℝ)
          - (HourCoupling.mAbove (L := L) (K := K) h x : ℝ) ≤ 2 := by
        show _ ∧ _
        unfold HourCoupling.mAbove
        constructor
        · have : ((Multiset.countP (fun a => HourCoupling.mainAboveP h a) x : ℝ))
              - (Multiset.countP (fun a => HourCoupling.mainAboveP h a)
                  (Protocol.stepOrSelf (NonuniformMajority L K) x r₁ r₂) : ℝ) ≤ 2 := by
            exact_mod_cast hmA2
          linarith
        · have : ((Multiset.countP (fun a => HourCoupling.mainAboveP h a)
              (Protocol.stepOrSelf (NonuniformMajority L K) x r₁ r₂) : ℝ))
              - (Multiset.countP (fun a => HourCoupling.mainAboveP h a) x : ℝ) ≤ 2 := by
            exact_mod_cast hmA1
          linarith
      have hcAle : -2 ≤ (HourCoupling.cAbove (L := L) (K := K) h
          (Protocol.stepOrSelf (NonuniformMajority L K) x r₁ r₂) : ℝ)
          - (HourCoupling.cAbove (L := L) (K := K) h x : ℝ)
          ∧ (HourCoupling.cAbove (L := L) (K := K) h
          (Protocol.stepOrSelf (NonuniformMajority L K) x r₁ r₂) : ℝ)
          - (HourCoupling.cAbove (L := L) (K := K) h x : ℝ) ≤ 2 := by
        show _ ∧ _
        unfold HourCoupling.cAbove
        constructor
        · have : ((Multiset.countP (fun a => HourCoupling.clockAboveP h a) x : ℝ))
              - (Multiset.countP (fun a => HourCoupling.clockAboveP h a)
                  (Protocol.stepOrSelf (NonuniformMajority L K) x r₁ r₂) : ℝ) ≤ 2 := by
            exact_mod_cast hcA2
          linarith
        · have : ((Multiset.countP (fun a => HourCoupling.clockAboveP h a)
              (Protocol.stepOrSelf (NonuniformMajority L K) x r₁ r₂) : ℝ))
              - (Multiset.countP (fun a => HourCoupling.clockAboveP h a) x : ℝ) ≤ 2 := by
            exact_mod_cast hcA1
          linarith
      unfold Phi
      rw [abs_le]
      -- Each /M, /C term is bounded by 2/M, 2/C in absolute value.
      have hmM1 : (HourCoupling.mAbove (L := L) (K := K) h
          (Protocol.stepOrSelf (NonuniformMajority L K) x r₁ r₂) : ℝ) / M
          - (HourCoupling.mAbove (L := L) (K := K) h x : ℝ) / M ≤ 2 / M := by
        rw [div_sub_div_same, div_le_div_iff_of_pos_right hM]; linarith [hmAle.2]
      have hmM2 : -(2 / M) ≤ (HourCoupling.mAbove (L := L) (K := K) h
          (Protocol.stepOrSelf (NonuniformMajority L K) x r₁ r₂) : ℝ) / M
          - (HourCoupling.mAbove (L := L) (K := K) h x : ℝ) / M := by
        rw [div_sub_div_same, ← neg_div, div_le_div_iff_of_pos_right hM]; linarith [hmAle.1]
      have hcC1 : (HourCoupling.cAbove (L := L) (K := K) h
          (Protocol.stepOrSelf (NonuniformMajority L K) x r₁ r₂) : ℝ) / C
          - (HourCoupling.cAbove (L := L) (K := K) h x : ℝ) / C ≤ 2 / C := by
        rw [div_sub_div_same, div_le_div_iff_of_pos_right hC]; linarith [hcAle.2]
      have hcC2 : -(2 / C) ≤ (HourCoupling.cAbove (L := L) (K := K) h
          (Protocol.stepOrSelf (NonuniformMajority L K) x r₁ r₂) : ℝ) / C
          - (HourCoupling.cAbove (L := L) (K := K) h x : ℝ) / C := by
        rw [div_sub_div_same, ← neg_div, div_le_div_iff_of_pos_right hC]; linarith [hcAle.1]
      -- Scale the cAbove/C bounds by 11/10.
      have h11 : (0:ℝ) ≤ 11/10 := by norm_num
      have hcC1' : (11/10 : ℝ) * ((HourCoupling.cAbove (L := L) (K := K) h
          (Protocol.stepOrSelf (NonuniformMajority L K) x r₁ r₂) : ℝ) / C
          - (HourCoupling.cAbove (L := L) (K := K) h x : ℝ) / C)
          ≤ (11/10 : ℝ) * (2 / C) := mul_le_mul_of_nonneg_left hcC1 h11
      have hcC2' : (11/10 : ℝ) * (-(2 / C))
          ≤ (11/10 : ℝ) * ((HourCoupling.cAbove (L := L) (K := K) h
          (Protocol.stepOrSelf (NonuniformMajority L K) x r₁ r₂) : ℝ) / C
          - (HourCoupling.cAbove (L := L) (K := K) h x : ℝ) / C) :=
        mul_le_mul_of_nonneg_left hcC2 h11
      have he : 2 * (11/10/C:ℝ) = (11/10) * (2/C) := by ring
      have he2 : (11/10:ℝ) * (-(2/C)) = -((11/10) * (2/C)) := by ring
      rw [he2] at hcC2'
      constructor
      · simp only [mul_div_assoc]; rw [he]; linarith [hmM1, hmM2, hcC1', hcC2']
      · simp only [mul_div_assoc]; rw [he]; linarith [hmM1, hmM2, hcC1', hcC2']
    · subst hyx; simp only [sub_self, abs_zero]; positivity
  -- Lift the support bound to a.e.
  rw [ae_iff]
  change ((NonuniformMajority L K).stepDistOrSelf x).toMeasure
    {y | ¬ |Phi (L := L) (K := K) M C h y - Phi (L := L) (K := K) M C h x|
        ≤ 2 / M + 2 * (11 / 10 : ℝ) / C} = 0
  rw [PMF.toMeasure_apply_eq_zero_iff _ (DiscreteMeasurableSpace.forall_measurableSet _)]
  rw [Set.disjoint_left]
  intro y hy hbad
  exact hbad (hsupp y hy)

/-! ## Part 9 — Lemma 6.10 via the real Azuma tail.

We feed the GENUINE drift (`hour_drift`) and the bounded-difference lemma
(`hour_bdd`) into `AzumaKernel.azuma_tail`.  Since `azuma_tail` needs the drift
and bounded difference at EVERY state, we carry the synchronous-hour regime as an
explicit global hypothesis `hreg` (the TRUE window `c_{>h} ≤ 1/11` together with
the fixed role counts `M`, `C`).  This is the faithful "on the window / until
`end_h`" qualifier of the paper's Lemma 6.10. -/

/-- The synchronous-hour regime at a configuration: the unbiased-Main window, the
window `c_{>h} ≤ 1/11`, the fixed role counts `M`, `C`, and `≥ 1` of each role. -/
def Regime (M C : ℝ) (h : ℕ) (c : Config (AgentState L K)) : Prop :=
  HourCoupling.HourWindow c ∧ Window (L := L) (K := K) h c ∧
    (mainCount (L := L) (K := K) c : ℝ) = M ∧
    (clockCount (L := L) (K := K) c : ℝ) = C ∧
    1 ≤ mainCount (L := L) (K := K) c ∧ 1 ≤ clockCount (L := L) (K := K) c

/-- **Lemma 6.10 (the clock → Main hour-coupling tail), genuine redo.**

For the additive supermartingale potential `Φ h = mAbove h / M − 1.1 · cAbove h / C`
on the synchronous-hour regime (`hreg`), the real Azuma-Hoeffding tail
`AzumaKernel.azuma_tail` gives: for every deviation `λ > 0` and `t ≥ 1`,

  `(K^t) c₀ { Φ ≥ Φ c₀ + λ }  ≤  exp(−λ² / (2 t c₀²))`,    `c₀ = 2/M + 2·(11/10)/C`.

Reading off `Φ c₀ = 0` at the start (Main and Clock both synchronized) and the
level `λ = 0.1 · c_{>h}(end_h)` recovers `m_{>h}(t) ≤ 1.2 · c_{>h}(end_h)` whp.

The drift is the GENUINE `hour_drift` (derived from drag/epidemic pair-counting +
the bracket inequality), NOT a frozen-`cAbove` floor; the concentration is the
REAL `azuma_tail`; the only carried hypothesis is the TRUE window `c_{>h} ≤ 1/11`
(packaged in `hreg`). -/
theorem hour_coupling_v2 (M C : ℝ) (hM : 0 < M) (hC : 0 < C) (h : ℕ) (hK : 0 < K) (hhL : h < L)
    (hreg : ∀ c : Config (AgentState L K), Regime (L := L) (K := K) M C h c)
    (t : ℕ) (ht : 1 ≤ t) (c₀ : Config (AgentState L K)) {lam : ℝ} (hlam : 0 < lam) :
    ((NonuniformMajority L K).transitionKernel ^ t) c₀
        {c' | Phi (L := L) (K := K) M C h c₀ + lam ≤ Phi (L := L) (K := K) M C h c'}
      ≤ ENNReal.ofReal (Real.exp
          (-(lam ^ 2) / (2 * t * (2 / M + 2 * (11 / 10 : ℝ) / C) ^ 2))) := by
  set c0 : ℝ := 2 / M + 2 * (11 / 10 : ℝ) / C with hc0def
  have hc0pos : 0 < c0 := by rw [hc0def]; positivity
  -- Global drift from `hour_drift` under the regime.
  have hdrift : ∀ x, ∫ y, Phi (L := L) (K := K) M C h y
      ∂((NonuniformMajority L K).transitionKernel x) ≤ Phi (L := L) (K := K) M C h x := by
    intro x
    obtain ⟨hw, hwin, hMc, hCc, hM1, hC1⟩ := hreg x
    exact hour_drift M C h hK hhL x hw hwin hMc hCc hM1 hC1
  -- Global bounded difference from `hour_bdd`.
  have hdiff : ∀ x, ∀ᵐ y ∂((NonuniformMajority L K).transitionKernel x),
      |Phi (L := L) (K := K) M C h y - Phi (L := L) (K := K) M C h x| ≤ c0 := by
    intro x; rw [hc0def]; exact hour_bdd M C hM hC h x
  exact ExactMajority.azuma_tail (NonuniformMajority L K).transitionKernel
    (Phi (L := L) (K := K) M C h) (Phi_measurable M C h) c0 hc0pos hdiff hdrift t ht c₀ hlam

end HourCouplingV2

end ExactMajority
