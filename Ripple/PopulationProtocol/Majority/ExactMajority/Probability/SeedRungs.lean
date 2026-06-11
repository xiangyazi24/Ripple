/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Phase E4 — the per-rung ADVANCE SEEDS (`SeedRungs`)

`TimedChainRungs.lean` / `ChainEndAssembly.lean` closed the per-rung phase-advance
EXPECTED-time caps (`seam_rung_to_chain_target_le_nsq`, `≤ n²`), but every one of those
caps starts from the **trigger hypothesis** `htrig : 1 ≤ geCount (p+1) c` — at least one
agent has already crossed to phase `≥ p+1`.  `ChainEndAssembly`'s Part-4 survey concluded
that this seed is NOT supplied by the previous rung's drained output `AllClockGEpCard p n`
(which only gives `geCount p = n`, NOT `geCount (p+1) ≥ 1`).  **This file supplies the
honest mechanism that materialises that seed.**

## The honest mechanism (the survey)

The seed is NOT a carried mystery and NOT a free deterministic fact: it materialises after
ONE more counter-running interaction.  The counter-drain rung
(`ConditionalPhaseProgress.timed_phase_progress_real_tinyClock`) delivers
`E[T to clockCounterSumAt p = 0]` — the drained state in which EVERY phase-`p` clock has
counter `0` (`clockCounterSumAt p c = 0` is a sum of non-negative weights, so each summand
is `0`).  In the all-clock regime `AllClockGEpCard p n` with the seed not yet fired
(`geCount (p+1) c = 0`), EVERY agent is then a clock at phase exactly `p` (all `≥ p` by the
invariant, none `≥ p+1` by `geCount (p+1) = 0`) with counter `0`.

The FROZEN protocol then advances on the NEXT counter-running interaction: a clock-clock
pair at phase `p` with a `0` counter runs `stdCounterSubroutine → advancePhaseWithInit`,
advancing (at least) one participant to phase `≥ p+1` — this is the proven per-pair advance
`Analysis.PhaseProgress.Transition_timed_clock_counter_zero_advances` (timed phases
`p ∈ {0,1,5,6,7,8}`, covering `{5,6,7,8}` and the chain-end `9` via the analogous routes —
see Part 4 for the `9 → 10` verdict).  So `geCount (p+1)` climbs from `0` to `≥ 1`: the seed.

## The deliverables

1. **The per-pair seed advance** (`seed_pair_advances`): from a drained, all-clock, un-seeded
   state, ANY distinct pair raises `geCount (p+1)` from `0` to `≥ 1` (the counter-0 advance,
   via `Transition_timed_clock_counter_zero_advances`).
2. **The seed advance probability** (`seed_advance_prob`): the per-step kernel mass on
   `{1 ≤ geCount (p+1)}` is `≥ n(n−1)/(n(n−1))`-flavoured (the FULL clock×clock rectangle —
   every distinct pair advances), routed through `SeamEpidemics.advance_prob_of_rect`.
3. **The seed expected-time bound** (`seed_expectedHitting_le`): from the drained un-seeded
   state, `E[T to {1 ≤ geCount (p+1)}] ≤ n(n−1)/((n)(n−1))`-flavoured — one clock-pair
   meeting, an `O(1)`-block / single-milestone coupon (`ExpectedHitting.expectedHitting_one_step_q`).
4. **The wired seed rung** (`seed_then_spread_le`): drained → seeded (this file) → spread
   (`TimedChainRungs`, `≤ n²`), the per-rung `drained ⟹ chain-target` bound with the seed
   discharged, and the re-cut spine arithmetic (`2·9·n²` budget).

## Build

Single-file only:
  `lake env lean Ripple/PopulationProtocol/Majority/ExactMajority/Probability/SeedRungs.lean`
from the project root (deps as cached oleans).  NEVER local `lake build`.
-/

import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.TimedChainRungs
import Ripple.PopulationProtocol.Majority.ExactMajority.Analysis.PhaseProgress

namespace ExactMajority
namespace SeedRungs

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators NNReal
open ConditionalPhaseProgress SeamEpidemics TimedChainRungs

variable {L K : ℕ}

attribute [local instance] Classical.propDecidable

/-! ## Part 0 — the drained-state structure facts

`clockCounterSumAt p c = 0` (the engine's drained target `potBelow (clockCounterSumAt p) 1`)
forces every phase-`p` clock's counter to `0`: the sum is over non-negative per-agent
weights `wtAt p a = if (clock ∧ phase = p) then counter else 0`, so a zero sum forces each
summand to `0`.  Combined with `AllClockGEp p` (every agent a clock at phase `≥ p`) and the
un-seeded condition `geCount (p+1) c = 0` (no agent at phase `≥ p+1`), every agent is a clock
at phase EXACTLY `p` with counter `0`. -/

/-- **Drained ⟹ every phase-`p` clock has counter `0`.**  `clockCounterSumAt p c = 0` is a
sum of non-negative weights `wtAt p`, so each agent's weight is `0`; for a clock at phase
exactly `p` the weight IS its counter, hence the counter is `0`. -/
theorem drained_imp_counter_zero (p : ℕ) (c : Config (AgentState L K))
    (hdrain : clockCounterSumAt (L := L) (K := K) p c = 0)
    (a : AgentState L K) (ha : a ∈ c) (haclock : a.role = .clock)
    (haphase : a.phase.val = p) :
    a.counter.val = 0 := by
  classical
  -- clockCounterSumAt p c = (c.map (wtAt p)).sum = 0; every summand ≥ 0, so wtAt p a = 0.
  rw [clockCounterSumAt_eq_sum_wtAt] at hdrain
  have hmem : wtAt (L := L) (K := K) p a ∈ c.map (wtAt (L := L) (K := K) p) :=
    Multiset.mem_map_of_mem _ ha
  have hzero : wtAt (L := L) (K := K) p a = 0 := by
    by_contra hne
    have hpos : 0 < wtAt (L := L) (K := K) p a := Nat.pos_of_ne_zero hne
    have : 0 < (c.map (wtAt (L := L) (K := K) p)).sum :=
      lt_of_lt_of_le hpos (Multiset.single_le_sum (fun _ _ => Nat.zero_le _) _ hmem)
    omega
  -- wtAt p a = counter (clock at phase p), so counter = 0.
  unfold wtAt at hzero
  rw [if_pos ⟨haclock, haphase⟩] at hzero
  exact hzero

/-- **The un-seeded all-clock characterisation.**  In the all-clock regime `AllClockGEp p`
with `geCount (p+1) c = 0` (no agent yet at phase `≥ p+1`), every agent in `c` is a clock at
phase EXACTLY `p`. -/
theorem unseeded_imp_phase_eq (p : ℕ) (c : Config (AgentState L K))
    (hInv : AllClockGEp (L := L) (K := K) p c)
    (hunseed : geCount (L := L) (K := K) (p + 1) c = 0)
    (a : AgentState L K) (ha : a ∈ c) :
    a.role = .clock ∧ a.phase.val = p := by
  classical
  obtain ⟨haclock, hage⟩ := hInv a ha
  refine ⟨haclock, ?_⟩
  -- geCount (p+1) c = 0 ⇒ countP (geP (p+1)) c = 0 ⇒ a is not geP (p+1), i.e. phase < p+1.
  have hnot : ¬ geP (L := L) (K := K) (p + 1) a := by
    intro hge
    have : 0 < Multiset.countP (fun b => geP (L := L) (K := K) (p + 1) b) c :=
      Multiset.countP_pos.mpr ⟨a, ha, hge⟩
    unfold geCount at hunseed
    omega
  simp only [geP] at hnot
  omega

/-! ## Part 1 — the per-pair seed advance

A distinct clock-clock pair at phase `p` (counter `0`) raises `geCount (p+1)` from `0` to
`≥ 1`: the counter-0 advance (`Transition_timed_clock_counter_zero_advances`) puts one of the
two outputs at phase `≥ p+1`, so the produced pair carries at least one `geP (p+1)` agent. -/

/-- **`countP (geP (p+1))` of the produced pair is `≥ 1`** when a distinct clock-clock pair at
phase `p` (counter `0`) is updated: the per-pair counter-0 advance lands one output at phase
`≥ p+1`. -/
theorem geP_pair_seed_advances (p : ℕ) (hp : p ∈ ({0, 1, 5, 6, 7, 8} : Finset ℕ))
    (s t : AgentState L K)
    (hs_phase : s.phase.val = p) (ht_phase : t.phase.val = p)
    (hs_clock : s.role = .clock) (ht_clock : t.role = .clock)
    (hs_ctr : s.counter.val = 0) (ht_ctr : t.counter.val = 0) :
    1 ≤ Multiset.countP (fun a => geP (L := L) (K := K) (p + 1) a)
        ({(Transition L K s t).1, (Transition L K s t).2}
          : Multiset (AgentState L K)) := by
  have hadv := Transition_timed_clock_counter_zero_advances (L := L) (K := K) p hp s t
    hs_phase ht_phase hs_clock ht_clock (Or.inl hs_ctr)
  rw [countP_geP_pair]
  rcases hadv with h1 | h2
  · -- output .1 at phase ≥ p+1.
    have : geP (L := L) (K := K) (p + 1) (Transition L K s t).1 := h1
    rw [if_pos this]; omega
  · have : geP (L := L) (K := K) (p + 1) (Transition L K s t).2 := h2
    rw [if_pos this]; split_ifs <;> omega

/-- **The per-pair seed advance on the GLOBAL count.**  A scheduled distinct clock-clock pair
at phase `p` (counter `0`) from an un-seeded state (`geCount (p+1) c = 0`) raises the global
`geCount (p+1)` to `≥ 1`.  The un-seeded hypothesis is essential: with `geCount (p+1) c = 0`,
the removed pair `{s,t}` carries `0` informed agents (`countP (geP (p+1)) {s,t} = 0`), so the
produced pair's `≥ 1` informed agent is a NET gain.  Mirrors
`SeamEpidemics.geCount_stepOrSelf_advance` with the counter-0 advance replacing the mixed-pair
advance. -/
theorem geCount_stepOrSelf_seed_advance (p : ℕ)
    (hp : p ∈ ({0, 1, 5, 6, 7, 8} : Finset ℕ)) (c : Config (AgentState L K))
    (s t : AgentState L K) (happ : Protocol.Applicable c s t)
    (hunseed : geCount (L := L) (K := K) (p + 1) c = 0)
    (hs_phase : s.phase.val = p) (ht_phase : t.phase.val = p)
    (hs_clock : s.role = .clock) (ht_clock : t.role = .clock)
    (hs_ctr : s.counter.val = 0) (ht_ctr : t.counter.val = 0) :
    1 ≤ geCount (L := L) (K := K) (p + 1)
          (Protocol.stepOrSelf (NonuniformMajority L K) c s t) := by
  have hsub : ({s, t} : Multiset (AgentState L K)) ≤ c := happ
  have hc' : Protocol.stepOrSelf (NonuniformMajority L K) c s t
      = c - {s, t} + {(Transition L K s t).1, (Transition L K s t).2} := by
    unfold Protocol.stepOrSelf; rw [if_pos happ]; rfl
  unfold geCount
  rw [hc', Multiset.countP_add]
  have hpair_ge : 1 ≤ Multiset.countP (fun a => geP (L := L) (K := K) (p + 1) a)
      ({(Transition L K s t).1, (Transition L K s t).2} : Multiset (AgentState L K)) :=
    geP_pair_seed_advances (L := L) (K := K) p hp s t hs_phase ht_phase hs_clock ht_clock
      hs_ctr ht_ctr
  -- 1 ≤ (anything) + countP{pair} since 1 ≤ countP{pair}.
  omega

/-! ## Part 2 — the seed advance probability (the full clock×clock rectangle)

The drained un-seeded state has EVERY agent a clock at phase exactly `p` with counter `0`.
The seed advance fires on ANY applicable distinct pair (`geCount_stepOrSelf_seed_advance`),
so the per-step kernel mass on `{1 ≤ geCount (p+1)}` is bounded below by the FULL clock-pair
rectangle mass `n(n−1)/(n(n−1))`.  We route this through `SeamEpidemics.advance_prob_of_rect`
with the rectangle `R` = all present states squared (every present state qualifies). -/

/-- **The seed advance probability (`≥ (n−1)/(n(n−1)) = 1/n`-flavoured, via the full
rectangle).**  From a drained (`clockCounterSumAt p c = 0`), un-seeded (`geCount (p+1) c = 0`)
all-clock state `AllClockGEpCard p n` with `n ≥ 2`, one step raises `geCount (p+1)` to `≥ 1`
with probability `≥ (n·(n−1)) / (n(n−1))`.  Every present state is a clock at phase `p` with
counter `0`, so every applicable ordered pair advances; the present-square rectangle aggregates
to `n(n−1)` interaction count out of `n(n−1)` ordered pairs. -/
theorem seed_advance_prob (p : ℕ) (hp : p ∈ ({0, 1, 5, 6, 7, 8} : Finset ℕ)) (n : ℕ)
    (hn : 2 ≤ n) (c : Config (AgentState L K))
    (hInv : AllClockGEpCard (L := L) (K := K) p n c)
    (hdrain : clockCounterSumAt (L := L) (K := K) p c = 0)
    (hunseed : geCount (L := L) (K := K) (p + 1) c = 0) :
    ENNReal.ofReal (((n * (n - 1) : ℕ) : ℝ) / ((n : ℝ) * ((n : ℝ) - 1))) ≤
      ((NonuniformMajority L K).stepDistOrSelf c).toMeasure
        {c' | geCount (L := L) (K := K) (p + 1) c + 1
                ≤ geCount (L := L) (K := K) (p + 1) c'} := by
  classical
  obtain ⟨hAllClock, hcardn⟩ := hInv
  -- The rectangle: full present-state square.
  set R : Finset (AgentState L K × AgentState L K) := Finset.univ ×ˢ Finset.univ with hRdef
  -- Per-pair: a present distinct pair (both clock-at-p-counter-0) seed-advances.
  -- interactionCount sum over the full square = card · (card - 1) = n(n-1).
  have hsquare : (∑ pr ∈ R, c.interactionCount pr.1 pr.2) = c.card * (c.card - 1) := by
    -- mirror sum_interactionCount_posPhaseP_square with F = univ (∑ count over univ = card).
    have hpoint : ∀ pr ∈ R,
        c.interactionCount pr.1 pr.2 + (if pr.1 = pr.2 then c.count pr.1 else 0)
          = c.count pr.1 * c.count pr.2 := by
      rintro ⟨a, b⟩ _
      unfold Config.interactionCount
      by_cases h : a = b
      · subst h; rw [if_pos rfl, if_pos rfl]
        have hle : c.count a ≤ c.count a * c.count a := by nlinarith [Nat.zero_le (c.count a)]
        rw [Nat.mul_sub_one, Nat.sub_add_cancel hle]
      · rw [if_neg h, if_neg h, Nat.add_zero]
    have hNcard : (∑ a ∈ (Finset.univ : Finset (AgentState L K)), c.count a) = c.card := by
      simp only [Config.count]
      rw [← Multiset.sum_count_eq_card (s := Finset.univ) (m := c)
        (fun a _ => Finset.mem_univ a)]
    have hsq : (∑ pr ∈ R, c.count pr.1 * c.count pr.2)
        = (∑ a ∈ (Finset.univ : Finset (AgentState L K)), c.count a)
          * (∑ b ∈ (Finset.univ : Finset (AgentState L K)), c.count b) := by
      rw [hRdef, Finset.sum_product, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro a _; rw [Finset.mul_sum]
    have hdiag : (∑ pr ∈ R, (if pr.1 = pr.2 then c.count pr.1 else 0))
        = (∑ a ∈ (Finset.univ : Finset (AgentState L K)), c.count a) := by
      rw [hRdef, Finset.sum_product]
      have : ∀ a ∈ (Finset.univ : Finset (AgentState L K)),
          (∑ b ∈ (Finset.univ : Finset (AgentState L K)), (if a = b then c.count a else 0))
            = c.count a := by
        intro a ha
        rw [Finset.sum_ite_eq Finset.univ a (fun _ => c.count a), if_pos (Finset.mem_univ a)]
      rw [Finset.sum_congr rfl this]
    have hadd : (∑ pr ∈ R, c.interactionCount pr.1 pr.2) + c.card = c.card * c.card := by
      have hcollect : (∑ pr ∈ R, c.interactionCount pr.1 pr.2)
          + (∑ pr ∈ R, (if pr.1 = pr.2 then c.count pr.1 else 0))
          = ∑ pr ∈ R, c.count pr.1 * c.count pr.2 := by
        rw [← Finset.sum_add_distrib]; exact Finset.sum_congr rfl hpoint
      rw [hdiag, hsq, hNcard] at hcollect; exact hcollect
    rw [Nat.mul_sub_one]; omega
  -- N = n(n-1) ≤ ∑ interactionCount over R.
  have hcount : (n * (n - 1) : ℕ) ≤ ∑ pr ∈ R, c.interactionCount pr.1 pr.2 := by
    rw [hsquare, hcardn]
  -- per-pair advance hypothesis for advance_prob_of_rect.
  refine advance_prob_of_rect p n hn c hcardn R (n * (n - 1)) ?_ hcount
  rintro ⟨a, b⟩ _hp h1 h2 _hsame
  -- a, b are present (count ≥ 1); both are clock-at-p-counter-0 (drained un-seeded all-clock).
  have hamem : a ∈ c := Multiset.one_le_count_iff_mem.mp h1
  have hbmem : b ∈ c := Multiset.one_le_count_iff_mem.mp h2
  obtain ⟨ha_clock, ha_phase⟩ :=
    unseeded_imp_phase_eq (L := L) (K := K) p c hAllClock hunseed a hamem
  obtain ⟨hb_clock, hb_phase⟩ :=
    unseeded_imp_phase_eq (L := L) (K := K) p c hAllClock hunseed b hbmem
  have ha_ctr : a.counter.val = 0 :=
    drained_imp_counter_zero (L := L) (K := K) p c hdrain a hamem ha_clock ha_phase
  have hb_ctr : b.counter.val = 0 :=
    drained_imp_counter_zero (L := L) (K := K) p c hdrain b hbmem hb_clock hb_phase
  -- applicable: distinct present states OR diagonal with count ≥ 2.
  have happ : Protocol.Applicable c a b := by
    by_cases hab : a = b
    · subst hab
      have hcnt2 : 2 ≤ c.count a := _hsame rfl
      show ({a, a} : Multiset (AgentState L K)) ≤ c
      rw [show ({a, a} : Multiset (AgentState L K)) = a ::ₘ a ::ₘ 0 from rfl, Multiset.le_iff_count]
      intro x
      rw [Multiset.count_cons, Multiset.count_cons, Multiset.count_zero]
      by_cases hxa : x = a
      · subst hxa; simp only [if_pos rfl]
        have : c.count a = Multiset.count a c := rfl
        omega
      · simp only [if_neg hxa]; omega
    · exact pair_le_of_mem_ne hamem hbmem hab
  -- the seed advance: geCount(p+1) c + 1 = 0 + 1 = 1 ≤ geCount(p+1)(step).
  rw [hunseed]
  exact geCount_stepOrSelf_seed_advance (L := L) (K := K) p hp c a b happ hunseed
    ha_phase hb_phase ha_clock hb_clock ha_ctr hb_ctr

end SeedRungs
end ExactMajority
