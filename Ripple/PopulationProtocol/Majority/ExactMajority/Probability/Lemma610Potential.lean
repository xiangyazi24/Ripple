/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# `Lemma610Potential` — the Doty Lemma 6.10 supermartingale potential (Phase-3 clock-pull bound).

Doty et al. (arXiv:2106.10201v2) Lemma 6.10 bounds the fraction of Main agents "pulled ahead" of the
current synchronous hour `h` by fast Clock agents, during the Phase-3 synchronized-averaging window
`t ∈ [0, end_h]`.  It is a PHASE-3-ONLY lemma: `M_0 := #Main` and `C_0 := #Clock` are FIXED parameters
captured at Phase-3 entry (the Reserve→Main split is Phase 6, handled by Doty §7 — NOT here).

The fixed-`n` potential (ChatGPT-cross-checked 2026-06-13), `Ψ = m_0·Φ_Doty`:

  `Ψ_h(x) = M_{>h}(x)/n − (11/10)·(M_0/C_0)·C_{>h}(x)/n`

where `M_{>h}` = #{Main with hour > h} and `C_{>h}` = #{Clock with hour > h} = #{Clock with minute
`≥ (h+1)·K`} (clock hour = minute / K).  The clock coefficient is `(11/10)(M_0/C_0)`, NOT `(11/10)/c_0`
(the latter is too strong on the clock term, losing a factor `1/m_0`).

This file defines the counts and the potential.  The drift (`E[ΔΨ] ≤ 0` on `c_{>h} ≤ 0.001`), the
bounded increment (`|ΔΨ| ≤ 11/(2n)`), the stopped kernel, and the Azuma tail follow.
NO sorry / admit / axiom / native_decide.
-/

import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.ClockRealKernel

namespace ExactMajority

namespace Lemma610

open ClockRealKernel

variable {L K : ℕ}

/-! ## Part 1 — the beyond-hour counts. -/

/-- A Main agent ahead of synchronous hour `h` (`hour > h`). -/
def mainBeyondHourP (h : ℕ) (a : AgentState L K) : Prop := a.role = .main ∧ h < a.hour.val

instance (h : ℕ) (a : AgentState L K) : Decidable (mainBeyondHourP h a) := by
  unfold mainBeyondHourP; infer_instance

/-- `M_{>h}` — the number of Main agents at hour `> h`. -/
def mainBeyondHour (h : ℕ) (c : Config (AgentState L K)) : ℕ :=
  Multiset.countP (fun a => mainBeyondHourP h a) c

/-- `C_{>h}` — Clock agents at hour `> h`.  A clock's hour is `minute / K`, so `hour > h ↔ minute ≥
(h+1)·K`; hence `C_{>h} = rBeyond ((h+1)·K)` (the cumulative clock-minute tail). -/
def clockBeyondHour (h : ℕ) (c : Config (AgentState L K)) : ℕ :=
  rBeyond (L := L) (K := K) ((h + 1) * K) c

/-- The total Main count (the fixed `M_0` at Phase-3 entry). -/
def mainTotal (c : Config (AgentState L K)) : ℕ :=
  Multiset.countP (fun a => a.role = .main) c

/-- `M_{>h} ≤ M_0`: the beyond-hour Main agents are among all Main agents. -/
theorem mainBeyondHour_le_mainTotal (h : ℕ) (c : Config (AgentState L K)) :
    mainBeyondHour (L := L) (K := K) h c ≤ mainTotal (L := L) (K := K) c := by
  unfold mainBeyondHour mainTotal
  rw [Multiset.countP_eq_card_filter, Multiset.countP_eq_card_filter]
  apply Multiset.card_le_card
  apply Multiset.monotone_filter_right
  intro a ha
  exact ha.1

/-! ## Part 2 — the fixed-`n` potential `Ψ_h`. -/

/-- The Doty Lemma-6.10 potential in fixed-`n` form (`M_0, C_0` = the Phase-3-entry Main/Clock
counts, `n` = population).  `Ψ_h = M_{>h}/n − (11/10)·(M_0/C_0)·C_{>h}/n`.  All denominators are the
globally fixed `n` plus the two fixed entry constants `M_0, C_0` — NO state-dependent role count. -/
noncomputable def Psi (h M0 C0 n : ℕ) (c : Config (AgentState L K)) : ℝ :=
  (mainBeyondHour (L := L) (K := K) h c : ℝ) / (n : ℝ)
    - (11 / 10) * ((M0 : ℝ) / (C0 : ℝ))
        * (clockBeyondHour (L := L) (K := K) h c : ℝ) / (n : ℝ)

/-! ## Part 3 — the bounded increment (`diff_stopped`).

A single scheduler step replaces at most two agents (`c' = c − {r₁,r₂} + {o₁,o₂}`), so ANY `countP`
observable changes by at most `2`.  Hence `M_{>h}` and `C_{>h}` each change by `≤ 2` per step, and
`Ψ_h` changes by `≤ (2/n)(1 + (11/10)(M_0/C_0))` — the `O(1/n)` bounded-difference Azuma input.  (The
tight Doty bound `11/(2n)` needs the per-reaction "changes one count only" analysis; this `O(1/n)`
form already gives the `exp(−Ω(n))` tail.) -/

/-- **General one-step `countP` stability.**  For any decidable predicate `p` and any one-step
successor `c'` of `c`, `countP p` changes by at most `2` (a step swaps `≤ 2` agents). -/
theorem countP_stepDistOrSelf_diff_le (p : AgentState L K → Prop) [DecidablePred p]
    (c c' : Config (AgentState L K))
    (hc' : c' ∈ ((NonuniformMajority L K).stepDistOrSelf c).support) :
    Multiset.countP p c' ≤ Multiset.countP p c + 2 ∧
      Multiset.countP p c ≤ Multiset.countP p c' + 2 := by
  classical
  by_cases hc : 2 ≤ c.card
  · rw [show (NonuniformMajority L K).stepDistOrSelf c = (NonuniformMajority L K).stepDist c hc by
        unfold Protocol.stepDistOrSelf; rw [dif_pos hc]] at hc'
    obtain ⟨⟨r₁, r₂⟩, hr⟩ := Protocol.stepDist_support (NonuniformMajority L K) c hc c' hc'
    rw [← hr]
    simp only [Protocol.scheduledStep]
    by_cases happ : Protocol.Applicable c r₁ r₂
    · have hsub : ({r₁, r₂} : Multiset (AgentState L K)) ≤ c := happ
      have hc'eq : Protocol.stepOrSelf (NonuniformMajority L K) c r₁ r₂
          = c - {r₁, r₂} + {(Transition L K r₁ r₂).1, (Transition L K r₁ r₂).2} := by
        unfold Protocol.stepOrSelf; rw [if_pos happ]; rfl
      rw [hc'eq, Multiset.countP_add, Multiset.countP_sub hsub]
      have hpair : Multiset.countP p ({r₁, r₂} : Multiset (AgentState L K)) ≤ 2 :=
        le_trans (Multiset.countP_le_card p _) (by simp)
      have hout : Multiset.countP p
          ({(Transition L K r₁ r₂).1, (Transition L K r₁ r₂).2} : Multiset (AgentState L K)) ≤ 2 :=
        le_trans (Multiset.countP_le_card p _) (by simp)
      have hle : Multiset.countP p ({r₁, r₂} : Multiset (AgentState L K))
          ≤ Multiset.countP p c := Multiset.countP_le_of_le _ hsub
      omega
    · rw [Protocol.stepOrSelf_eq_self_of_not_applicable happ]; omega
  · rw [show (NonuniformMajority L K).stepDistOrSelf c = PMF.pure c by
        unfold Protocol.stepDistOrSelf; rw [dif_neg hc]] at hc'
    rw [PMF.mem_support_pure_iff] at hc'; subst hc'; omega

/-- The real-valued `|Δ countP| ≤ 2` corollary. -/
theorem abs_countP_step_diff_le (p : AgentState L K → Prop) [DecidablePred p]
    (c c' : Config (AgentState L K))
    (hc' : c' ∈ ((NonuniformMajority L K).stepDistOrSelf c).support) :
    |(Multiset.countP p c' : ℝ) - (Multiset.countP p c : ℝ)| ≤ 2 := by
  obtain ⟨h1, h2⟩ := countP_stepDistOrSelf_diff_le p c c' hc'
  rw [abs_le]
  constructor <;>
  · have h1' : (Multiset.countP p c' : ℝ) ≤ (Multiset.countP p c : ℝ) + 2 := by exact_mod_cast h1
    have h2' : (Multiset.countP p c : ℝ) ≤ (Multiset.countP p c' : ℝ) + 2 := by exact_mod_cast h2
    linarith

/-- **`diff_stopped` (the bounded increment).**  `|Ψ_h(c') − Ψ_h(c)| ≤ (2/n)(1 + (11/10)(M_0/C_0))`
for any one-step successor `c'`.  Both `M_{>h}` and `C_{>h}` are `countP`s, each changing by `≤ 2`. -/
theorem Psi_step_diff_le (h M0 C0 n : ℕ) (hn : 0 < n) (hC0 : 0 < C0)
    (c c' : Config (AgentState L K))
    (hc' : c' ∈ ((NonuniformMajority L K).stepDistOrSelf c).support) :
    |Psi (L := L) (K := K) h M0 C0 n c' - Psi (L := L) (K := K) h M0 C0 n c|
      ≤ (2 / (n : ℝ)) * (1 + (11 / 10) * ((M0 : ℝ) / (C0 : ℝ))) := by
  have hM := abs_countP_step_diff_le (fun a => mainBeyondHourP h a) c c' hc'
  have hCb := abs_countP_step_diff_le (fun a => clockBeyondP (L := L) (K := K) ((h + 1) * K) a) c c' hc'
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hC0pos : (0 : ℝ) < (C0 : ℝ) := by exact_mod_cast hC0
  have hMnn : (0 : ℝ) ≤ (M0 : ℝ) := Nat.cast_nonneg _
  -- ΔΨ = ΔM/n − (11/10)(M0/C0)·ΔC/n.
  have hexpand : Psi (L := L) (K := K) h M0 C0 n c' - Psi (L := L) (K := K) h M0 C0 n c
      = ((mainBeyondHour (L := L) (K := K) h c' : ℝ) - mainBeyondHour (L := L) (K := K) h c) / n
        - (11 / 10) * ((M0 : ℝ) / C0)
            * ((clockBeyondHour (L := L) (K := K) h c' : ℝ)
                - clockBeyondHour (L := L) (K := K) h c) / n := by
    unfold Psi; ring
  rw [hexpand]
  have hMc : |(mainBeyondHour (L := L) (K := K) h c' : ℝ) - mainBeyondHour (L := L) (K := K) h c| ≤ 2 := by
    unfold mainBeyondHour; exact hM
  have hCc : |(clockBeyondHour (L := L) (K := K) h c' : ℝ) - clockBeyondHour (L := L) (K := K) h c| ≤ 2 := by
    unfold clockBeyondHour rBeyond; exact hCb
  set coef : ℝ := (11 / 10) * ((M0 : ℝ) / C0) with hcoefdef
  have hcoef : (0 : ℝ) ≤ coef := by rw [hcoefdef]; positivity
  set DM : ℝ := (mainBeyondHour (L := L) (K := K) h c' : ℝ) - mainBeyondHour (L := L) (K := K) h c with hDMdef
  set DC : ℝ := (clockBeyondHour (L := L) (K := K) h c' : ℝ) - clockBeyondHour (L := L) (K := K) h c with hDCdef
  -- goal: |DM/n − coef·DC/n| ≤ (2/n)(1+coef).
  rw [show DM / n - coef * DC / n = (DM - coef * DC) / n by ring, abs_div, abs_of_pos hnpos,
    div_le_iff₀ hnpos]
  have hnum : |DM - coef * DC| ≤ 2 + coef * 2 := by
    calc |DM - coef * DC| ≤ |DM| + |coef * DC| := abs_sub _ _
      _ = |DM| + coef * |DC| := by rw [abs_mul, abs_of_nonneg hcoef]
      _ ≤ 2 + coef * 2 := by
          have := mul_le_mul_of_nonneg_left hCc hcoef
          linarith [hMc]
  have hrhs : (2 / (n : ℝ)) * (1 + coef) * n = 2 + coef * 2 := by
    field_simp
  rw [hrhs]; exact hnum

end Lemma610

end ExactMajority
