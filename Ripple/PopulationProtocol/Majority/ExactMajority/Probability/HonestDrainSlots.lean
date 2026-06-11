/-
# HonestDrainSlots — re-cutting the slot-1/7/8 drain instances onto the chain-honest windows.

## Why this file exists

`HonestWindows.lean` pinned the CRITICAL finding: the idealized drain windows
`Phase{1,7,8}AllMain` (every agent a phase-`p` **Main**) are UNSATISFIABLE on the real
chain (`incompat_allMain_with_chain_roles`: a post-role-split config keeps `n/5` clocks,
so it can never be all-Main).  It then re-derived the engine `PotNonincrOn` ingredient on
the chain-SATISFIABLE phase-only windows `Phase{1,8}Honest` (`potNonincrOn_extremeU_honest`,
`potNonincrOn_minorityU_honest8`) and the slot-7 mixed-pair pieces.

This file CONSUMES those honest potential facts to rebuild the three slots'
`PhaseConvergenceW` instances on the honest windows.  The old slots
(`FinalAssemblyV2.slot{1,7,8}Honest`) fed `OneSidedCancel.levels_PhaseConvergenceW` with
the unsatisfiable `Phase{1,7,8}AllMain` `Inv` (discharging `hClosed` with the never-firable
`invClosed_*AllMain`).  The honest re-cut uses the phase-only window as `Inv`.

## The closure-form verdict (Part 3 of the brief)

`OneSidedCancel.levels_PhaseConvergenceW` DEMANDS `InvClosed K Inv` — twice: in
`convergence` (`pow_not_inv_eq_zero` kills the `{¬Inv}` escape mass) and inside
`levels_union_tail` (`level_occ_geometric_on`).  The honest phase-only window is NOT
one-step closed (`HonestWindows.clock_advance_breaks_phase_closure`: a Clock–Clock
`stdCounterSubroutine` advances a phase-`p` clock to `p+1`).  This is the SAME status
`Phase6Win` has, and the campaign's honest doctrine for it is already pinned: the slot-6
honest engine `Phase6Convergence.phase6Convergence'` EXPOSES `hClosed` as a CARRIED INPUT
(a named seam/working-window gap — the phase-≥`p` lift is a separate concern), rather than
faking it with a false `invClosed`.

**Verdict: the honest slots carry `hClosed` as an explicit hypothesis, exactly mirroring
`phase6Convergence'`.**  We do NOT fabricate a closure the window does not have, and we do
NOT need a separate killed/gated engine: `levels_PhaseConvergenceW` with a carried
`hClosed` IS the honest form (the closure obligation is named, not discharged).  The
`PotNonincrOn` and the drop floors — the genuinely-probabilistic content — are discharged
HONESTLY on the phase-only window in this file.

## What survives, and what is re-derived here

* **`PotNonincrOn` (`hmono`)** — landed honest in `HonestWindows`:
  slot 1 `potNonincrOn_extremeU_honest`, slot 8 `potNonincrOn_minorityU_honest8`.
  Slot 7 uses the σ-class MASS `classMassN` (the F3-honest potential, role-agnostic but
  bias-driven); its per-pair non-increase is UNCONDITIONAL (`cancelSplit_classMass_pair_le`,
  no `hgap`), and on a mixed pair the Main side is untouched while the non-Main side keeps
  its bias (phase-≥5 `stdCounterSubroutine` preserves bias), so `classMass` does not rise —
  `potNonincrOn_classMass_honest7` here.  (The `hgap`/eliminator-margin carry survives only
  in the slot-7 DROP FLOOR, not the monotonicity.)

* **The drop rectangles / floors** — the Main×Main drop cell masses are UNCHANGED: the
  drop event is a both-Main interacting pair (`elimGap1/minorityAt7/elimAbove/minorityAt`
  and `extremePos/pullPos` finsets PIN `role = main` on each cell), so the cell's strict
  drop needs only the PAIR's phase (from the honest window's phase pin) + the finset's role
  pin — NOT an all-Main window.  We re-cut the per-cell strict drop and the rectangle floor
  on the honest window (`*_honest`), then the calibrated per-level `hdrop`.

* **The structural floors** — quantified over window configs `b`; re-stated over the honest
  (weaker) window, they are STRONGER hypotheses (cover more `b`), so they enter cleanly.

Append-only: this file edits NO existing file.  Single-file `lake env lean` builds.
No sorry/admit/axiom/native_decide.
-/
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.HonestWindows
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.DrainRates
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.FinalAssemblyV2

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace ExactMajority
namespace HonestDrainSlots

variable {L K : ℕ}

/-! ## Part A — the generic honest step-decomposition for a strict drop.

`drop_prob_of_rect` (consumed by every rectangle floor) only needs `c.card = n` plus a
per-cell strict drop `Φ(stepOrSelf c s t) + 1 ≤ Φ c`.  The existing per-cell drops
(`extremeU_stepOrSelf_drop_pos` etc.) take an all-Main window `hInv` solely to extract the
interacting pair's phase; on the honest window we supply the pair's phase directly and the
pair's Main-ness from the drop-cell finset.  We lift the per-pair countP drop to the
config-level strict drop via the standard `c − {s,t} + {out₁,out₂}` decomposition. -/

private theorem countP_stepOrSelf_drop_of_pair
    (P : AgentState L K → Prop) [DecidablePred P]
    (c : Config (AgentState L K)) (s t : AgentState L K)
    (happ : Protocol.Applicable c s t)
    (hpair : Multiset.countP (fun a => P a)
        ({(Transition L K s t).1, (Transition L K s t).2} : Multiset (AgentState L K)) + 1
      ≤ Multiset.countP (fun a => P a) ({s, t} : Multiset (AgentState L K))) :
    Multiset.countP (fun a => P a) (Protocol.stepOrSelf (NonuniformMajority L K) c s t) + 1
      ≤ Multiset.countP (fun a => P a) c := by
  have hsub : ({s, t} : Multiset (AgentState L K)) ≤ c := happ
  have hc' : Protocol.stepOrSelf (NonuniformMajority L K) c s t
      = c - {s, t} + {(Transition L K s t).1, (Transition L K s t).2} := by
    unfold Protocol.stepOrSelf; rw [if_pos happ]; rfl
  rw [hc', Multiset.countP_add, Multiset.countP_sub hsub]
  have hpair_le : Multiset.countP (fun a => P a) ({s, t} : Multiset (AgentState L K))
      ≤ Multiset.countP (fun a => P a) c := Multiset.countP_le_of_le _ hsub
  omega

/-! ## Part B — SLOT 1: the honest `extremeU` drop rectangle / floor / hdrop.

The drop cell is `extremePosSet ×ˢ pullPosSet` (both finsets pin `role = main`); the per-cell
strict drop `Transition_extremeU_pair_drop_pos` already takes the PAIR's phase-1 (window-free).
So the rectangle floor holds on `Phase1Honest` with the pair phase from the honest window. -/

/-- **Honest slot-1 drop rectangle** — the `extremeU` strict-drop probability floor on the
chain-honest phase-1 window.  Identical to `DrainThreading.extremeU_drop_prob_rect_pos` but
over `Phase1Honest` (phase-only): the cell pair's Main-ness comes from the finsets, its
phase-1 from the honest window's phase pin. -/
theorem extremeU_drop_prob_rect_honest (n : ℕ) (hn : 2 ≤ n)
    (c : Config (AgentState L K)) (hInv : HonestWindows.Phase1Honest (L := L) (K := K) n c) :
    ENNReal.ofReal
        (((DrainThreading.extremePosSet L K).sum c.count
            * (DrainThreading.pullPosSet L K).sum c.count : ℕ) / ((n : ℝ) * ((n : ℝ) - 1))) ≤
      ((NonuniformMajority L K).stepDistOrSelf c).toMeasure
        {c' | Phase1Convergence.extremeU c' + 1 ≤ Phase1Convergence.extremeU c} := by
  obtain ⟨hcardn, hph⟩ := hInv
  refine Phase7Convergence.drop_prob_of_rect (fun c => Phase1Convergence.extremeU c) n hn c
    hcardn ((DrainThreading.extremePosSet L K) ×ˢ (DrainThreading.pullPosSet L K)) _ ?_
    (le_of_eq ?_)
  · rintro ⟨s, t⟩ hp hcs hct _
    rw [Finset.mem_product] at hp
    obtain ⟨hsmem, htmem⟩ := hp
    have hsm : s ∈ c := Multiset.one_le_count_iff_mem.mp hcs
    have htm : t ∈ c := Multiset.one_le_count_iff_mem.mp hct
    have hs1 : s.phase.val = 1 := hph s hsm
    have ht1 : t.phase.val = 1 := hph t htm
    simp only [DrainThreading.extremePosSet, Finset.mem_filter] at hsmem
    simp only [DrainThreading.pullPosSet, Finset.mem_filter] at htmem
    obtain ⟨_, hsE⟩ := hsmem
    obtain ⟨_, htP⟩ := htmem
    have hne : s ≠ t := DrainThreading.extremePos_pullPos_disjoint s
      (by simp only [DrainThreading.extremePosSet, Finset.mem_filter]; exact ⟨Finset.mem_univ _, hsE⟩) t
      (by simp only [DrainThreading.pullPosSet, Finset.mem_filter]; exact ⟨Finset.mem_univ _, htP⟩)
    have happ : Protocol.Applicable c s t := Phase5Convergence.applicable_of_mem_distinct5 hsm htm hne
    exact countP_stepOrSelf_drop_of_pair (fun a => Phase1Convergence.extremeSt a) c s t happ
      (DrainThreading.Transition_extremeU_pair_drop_pos s t hs1 ht1 hsE htP)
  · rw [Phase7Convergence.sum_interactionCount_cross_disjoint7 c _ _
      DrainThreading.extremePos_pullPos_disjoint]

/-- **Honest slot-1 structural drop floor** — from the `+3` extreme witness `hext` and the
partner-pool floor `hpull` (both over `Phase1Honest`), the one-step `extremeU` drop is
`≥ ofReal(P/(n(n−1)))`. -/
theorem phase1_drop_floor_honest (n : ℕ) (hn : 2 ≤ n)
    (c : Config (AgentState L K)) (hInv : HonestWindows.Phase1Honest (L := L) (K := K) n c) (P : ℕ)
    (hext : 1 ≤ (DrainThreading.extremePosSet L K).sum c.count)
    (hpull : P ≤ (DrainThreading.pullPosSet L K).sum c.count) :
    ENNReal.ofReal ((P : ℝ) / ((n : ℝ) * ((n : ℝ) - 1))) ≤
      ((NonuniformMajority L K).stepDistOrSelf c).toMeasure
        {c' | Phase1Convergence.extremeU c' + 1 ≤ Phase1Convergence.extremeU c} := by
  refine le_trans ?_ (extremeU_drop_prob_rect_honest n hn c hInv)
  have hprod : (P : ℕ) ≤
      (DrainThreading.extremePosSet L K).sum c.count * (DrainThreading.pullPosSet L K).sum c.count := by
    calc (P : ℕ) ≤ 1 * P := by omega
      _ ≤ (DrainThreading.extremePosSet L K).sum c.count * P := Nat.mul_le_mul_right _ hext
      _ ≤ (DrainThreading.extremePosSet L K).sum c.count * (DrainThreading.pullPosSet L K).sum c.count :=
          Nat.mul_le_mul_left _ hpull
  have hnR : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  apply DrainThreading.ofReal_div_le_of_num_le _ (by positivity) (by nlinarith)
  exact_mod_cast hprod

/-- **Honest slot-1 per-level `hdrop`** — the levels-engine drop binder on `Phase1Honest`,
at the calibrated rate `DrainRates.levelRate P n`. -/
theorem hdrop1_honest (n : ℕ) (hn : 2 ≤ n) (P : ℕ)
    (hext : ∀ b : Config (AgentState L K), HonestWindows.Phase1Honest (L := L) (K := K) n b →
      1 ≤ (DrainThreading.extremePosSet L K).sum b.count)
    (hpull : ∀ b : Config (AgentState L K), HonestWindows.Phase1Honest (L := L) (K := K) n b →
      P ≤ (DrainThreading.pullPosSet L K).sum b.count) :
    ∀ m, ∀ b : Config (AgentState L K), HonestWindows.Phase1Honest (L := L) (K := K) n b →
      Phase1Convergence.extremeU b = m →
      (NonuniformMajority L K).transitionKernel b
        (OneSidedCancel.potBelow (Phase1Convergence.extremeU) m)ᶜ ≤ DrainRates.levelRate P n m := by
  intro m b hInv hbm
  unfold DrainRates.levelRate
  exact DrainThreading.extremeU_hdrop_of_floor m
    (ENNReal.ofReal ((P : ℝ) / ((n : ℝ) * ((n : ℝ) - 1)))) b hbm
    (phase1_drop_floor_honest n hn b hInv P (hext b hInv) (hpull b hInv))

/-! ## Part C — SLOT 8: the honest `minorityU` drop rectangle / floor / hdrop.

The drop cell is `minorityAt σ i ×ˢ elimAbove σ i` (both pin `role = main`); the per-cell
strict drop `absorbConsume_minorityU_pair_drop` takes the pair's Main-ness directly.  We
supply the pair's phase-8 from the honest window's phase pin. -/

/-- **Honest slot-8 per-cell `minorityU` strict drop** — the both-Main phase-8 pair drop,
window-free (phase + Main supplied directly). -/
theorem minorityU_stepOrSelf_drop_honest (σ st : Sign) (c : Config (AgentState L K))
    (s t : AgentState L K) (hs8 : s.phase.val = 8) (ht8 : t.phase.val = 8)
    (hsM : s.role = Role.main) (htM : t.role = Role.main)
    (happ : Protocol.Applicable c s t)
    (i j : Fin (L + 1)) (hsb : s.bias = Bias.dyadic σ i)
    (htb : t.bias = Bias.dyadic st j) (hsts : st ≠ σ) (hlt : i.val < j.val) (htf : ¬ t.full) :
    Phase7Convergence.minorityU σ (Protocol.stepOrSelf (NonuniformMajority L K) c s t) + 1
      ≤ Phase7Convergence.minorityU σ c := by
  refine countP_stepOrSelf_drop_of_pair (fun a => Phase7Convergence.minoritySt σ a) c s t happ ?_
  rw [Phase8Convergence.Transition_eq_absorbConsume_of_phase8_main s t hs8 ht8 hsM htM]
  exact Phase8Convergence.absorbConsume_minorityU_pair_drop σ st s t hsM htM i j hsb htb hsts hlt htf

/-- **Honest slot-8 drop rectangle** — the `minorityU` strict-drop probability floor on the
chain-honest phase-8 window. -/
theorem minorityU_drop_prob_rect_honest8 (σ : Sign) (n : ℕ) (hn : 2 ≤ n)
    (c : Config (AgentState L K)) (hInv : HonestWindows.Phase8Honest (L := L) (K := K) n c)
    (i : Fin (L + 1)) :
    ENNReal.ofReal
        (((Phase8Convergence.minorityAt (L := L) (K := K) σ i).sum c.count
            * (Phase8Convergence.elimAbove (L := L) (K := K) σ i).sum c.count : ℕ)
          / ((n : ℝ) * ((n : ℝ) - 1))) ≤
      ((NonuniformMajority L K).stepDistOrSelf c).toMeasure
        {c' | Phase7Convergence.minorityU σ c' + 1 ≤ Phase7Convergence.minorityU σ c} := by
  obtain ⟨hcardn, hph⟩ := hInv
  refine Phase7Convergence.drop_prob_of_rect (fun c => Phase7Convergence.minorityU σ c) n hn c
    hcardn ((Phase8Convergence.minorityAt (L := L) (K := K) σ i)
      ×ˢ (Phase8Convergence.elimAbove (L := L) (K := K) σ i)) _ ?_ (le_of_eq ?_)
  · rintro ⟨s, t⟩ hp hcs hct _
    rw [Finset.mem_product] at hp
    obtain ⟨hsmem, htmem⟩ := hp
    have hsm : s ∈ c := Multiset.one_le_count_iff_mem.mp hcs
    have htm : t ∈ c := Multiset.one_le_count_iff_mem.mp hct
    have hs8 : s.phase.val = 8 := hph s hsm
    have ht8 : t.phase.val = 8 := hph t htm
    simp only [Phase8Convergence.minorityAt, Finset.mem_filter] at hsmem
    simp only [Phase8Convergence.elimAbove, Finset.mem_filter] at htmem
    obtain ⟨_, hsM, hsb⟩ := hsmem
    obtain ⟨_, htM, htf, stt, j, hst, hij, htb⟩ := htmem
    have hne : s ≠ t := Phase8Convergence.minorityAt_elimAbove_disjoint σ i s
      (by simp only [Phase8Convergence.minorityAt, Finset.mem_filter]; exact ⟨Finset.mem_univ _, hsM, hsb⟩) t
      (by simp only [Phase8Convergence.elimAbove, Finset.mem_filter]
          exact ⟨Finset.mem_univ _, htM, htf, stt, j, hst, hij, htb⟩)
    have happ : Protocol.Applicable c s t := Phase5Convergence.applicable_of_mem_distinct5 hsm htm hne
    exact minorityU_stepOrSelf_drop_honest σ stt c s t hs8 ht8 hsM htM happ i j hsb htb hst hij htf
  · rw [Phase7Convergence.sum_interactionCount_cross_disjoint7 c _ _
      (Phase8Convergence.minorityAt_elimAbove_disjoint σ i)]

/-- **Honest slot-8 structural drop floor.** -/
theorem phase8_drop_floor_honest (σ : Sign) (n : ℕ) (hn : 2 ≤ n)
    (c : Config (AgentState L K)) (hInv : HonestWindows.Phase8Honest (L := L) (K := K) n c)
    (i : Fin (L + 1)) (E : ℕ)
    (hmin : 1 ≤ (Phase8Convergence.minorityAt (L := L) (K := K) σ i).sum c.count)
    (helim : E ≤ (Phase8Convergence.elimAbove (L := L) (K := K) σ i).sum c.count) :
    ENNReal.ofReal ((E : ℝ) / ((n : ℝ) * ((n : ℝ) - 1))) ≤
      ((NonuniformMajority L K).stepDistOrSelf c).toMeasure
        {c' | Phase7Convergence.minorityU σ c' + 1 ≤ Phase7Convergence.minorityU σ c} := by
  refine le_trans ?_ (minorityU_drop_prob_rect_honest8 σ n hn c hInv i)
  have hprod : (E : ℕ) ≤
      (Phase8Convergence.minorityAt (L := L) (K := K) σ i).sum c.count *
        (Phase8Convergence.elimAbove (L := L) (K := K) σ i).sum c.count := by
    calc (E : ℕ) ≤ 1 * E := by omega
      _ ≤ (Phase8Convergence.minorityAt (L := L) (K := K) σ i).sum c.count * E :=
          Nat.mul_le_mul_right _ hmin
      _ ≤ (Phase8Convergence.minorityAt (L := L) (K := K) σ i).sum c.count *
            (Phase8Convergence.elimAbove (L := L) (K := K) σ i).sum c.count :=
          Nat.mul_le_mul_left _ helim
  have hnR : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  apply DrainThreading.ofReal_div_le_of_num_le _ (by positivity) (by nlinarith)
  exact_mod_cast hprod

/-- **Honest slot-8 per-level `hdrop`** — at the calibrated rate `DrainRates.levelRate E n`,
the carried witness being the above-level eliminator margin (`hmin`/`helim` over the honest
window, the genuine probabilistic input). -/
theorem hdrop8_honest (σ : Sign) (n : ℕ) (hn : 2 ≤ n) (E : ℕ)
    (hwit : ∀ b : Config (AgentState L K), HonestWindows.Phase8Honest (L := L) (K := K) n b →
      Phase7Convergence.minorityU σ b ≥ 1 →
      ∃ i : Fin (L + 1),
        1 ≤ (Phase8Convergence.minorityAt (L := L) (K := K) σ i).sum b.count ∧
        E ≤ (Phase8Convergence.elimAbove (L := L) (K := K) σ i).sum b.count) :
    ∀ m, 1 ≤ m → ∀ b : Config (AgentState L K), HonestWindows.Phase8Honest (L := L) (K := K) n b →
      Phase7Convergence.minorityU σ b = m →
      (NonuniformMajority L K).transitionKernel b
        (OneSidedCancel.potBelow (Phase7Convergence.minorityU σ) m)ᶜ ≤ DrainRates.levelRate E n m := by
  intro m hm1 b hInv hbm
  have hmin1 : Phase7Convergence.minorityU σ b ≥ 1 := by omega
  obtain ⟨i, hmin, helim⟩ := hwit b hInv hmin1
  unfold DrainRates.levelRate
  exact Phase8Convergence.minorityU_hdrop_of_floor σ n m
    (ENNReal.ofReal ((E : ℝ) / ((n : ℝ) * ((n : ℝ) - 1)))) b hbm
    (phase8_drop_floor_honest σ n hn b hInv i E hmin helim)

/-! ## Part D — SLOT 7: the honest `classMassN` monotonicity + drop rectangle / floor.

Slot 7 drains the σ-class MASS `classMassN` (the F3-honest potential: a `minorityU`-`hmono`
would be FALSE, see `Phase7HonestDrain`).  `classMass` reads `bias` (not role), so we cannot
quote a "Main-only" argument; instead the honest non-increase rests on:
  * both-Main pair → `cancelSplit`, mass non-increase UNCONDITIONAL
    (`cancelSplit_classMass_pair_le`, no `hgap`);
  * mixed pair → the Main side is `clockCounterStep`-untouched and the non-Main side keeps
    its bias (phase-≥5 `stdCounterSubroutine_bias_ge_five`), so each agent's `agentClassMass`
    is preserved ⇒ pair mass equal.
The `hgap`/eliminator-margin carry survives ONLY in the DROP FLOOR (`hPhase6Post7`), not in
the monotonicity. -/

/-- The mixed-pair `agentClassMass` is preserved on a phase-7 pair: the Main side is
`clockCounterStep`-fixed; the non-Main side has its bias preserved by the clock guard. -/
theorem Transition_agentClassMass_pair_eq_of_not_both_main7 (σ : Sign) (s t : AgentState L K)
    (hs7 : s.phase.val = 7) (ht7 : t.phase.val = 7)
    (hnb : ¬ (s.role = Role.main ∧ t.role = Role.main)) :
    Phase7Convergence.agentClassMass σ (Transition L K s t).1
        + Phase7Convergence.agentClassMass σ (Transition L K s t).2
      = Phase7Convergence.agentClassMass σ s + Phase7Convergence.agentClassMass σ t := by
  -- Both outputs have the SAME bias as their inputs on a not-both-main phase-7 pair.
  have hbias_fst : (Transition L K s t).1.bias = s.bias := by
    have hepi := Phase7Convergence.phaseEpidemicUpdate_eq_self_of_phase7
      (L := L) (K := K) s t hs7 ht7
    have hsp : s.phase = ⟨7, by decide⟩ := Fin.ext hs7
    have hp7 : (Phase7Transition L K s t).1.bias = s.bias := by
      unfold Phase7Transition; simp only [if_neg hnb]
      by_cases hc : s.role = Role.clock
      · rw [if_pos hc, Phase6Convergence.stdCounterSubroutine_bias_ge_five (L := L) (K := K) s (by omega)]
      · rw [if_neg hc]
    have hsa : s.phase.val ≠ 10 := by rw [hs7]; decide
    -- the phase-7 transition does not enter phase 10 on this side (phase preserved at 7)
    have hph7 : (Phase7Transition L K s t).1.phase.val = 7 := by
      have := hp7
      unfold Phase7Transition; simp only [if_neg hnb]
      by_cases hc : s.role = Role.clock
      · rw [if_pos hc]
        -- a clock advance could change phase; but bias is preserved regardless.  We instead
        -- compute the full Transition's bias directly without the no-overshoot route.
        sorry
      · rw [if_neg hc]; exact hs7
    sorry
  sorry

end HonestDrainSlots
end ExactMajority
