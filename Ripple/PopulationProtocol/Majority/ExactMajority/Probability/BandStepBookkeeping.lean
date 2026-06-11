/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Band step bookkeeping — the config-level `countP` delta for the per-pair eliminator ledger

`SpendLedgerLift.lean` reduces the residual-#3 chain to a SINGLE deterministic atom: the per-step band
closure `hBand` of `SpendLedgerLift.phase7Surviving_step_of_band`.  `SurvivalAccounting.lean` PROVES
the per-pair core (`cancelSplit_elimAbove_survives_or_charged`: an above-`i` eliminator leaves
`elimAbove σ i` under one `cancelSplit` ONLY in the same-level branch, which forces its partner to be
a colliding σ-minority near level `i`).  This file delivers the CONFIG-level aggregation of that
per-pair fact — the `Multiset.countP` delta over the two-removed/two-added agents of one `StepRel`
step — append-only (no existing file edited).

### The honest config-level identity

For a both-Main applicable step (under `Phase7AllMain` ⟹ `Transition = cancelSplit`),
`c' = c − {r₁,r₂} + {p₁,p₂}` with `{p₁,p₂} = cancelSplit r₁ r₂`.  Writing
`A i c := Multiset.countP (elimAbovePred σ i) c` (the eliminator observable, defeq the consumer
`(elimAbove σ i).sum c.count` via `SpendLedgerLift.elimAbove_sum_eq_countP`), the standard multiset
identities `Multiset.countP_add` / `Multiset.countP_sub` give

> `A i c' = A i c − countP_elim {r₁,r₂} + countP_elim {p₁,p₂}`.

The per-pair ledger (in BOTH components — we prove the `.2` analogue here) gives, pointwise on the
removed pair, `countP_elim {r₁,r₂} ≤ countP_elim {p₁,p₂} + (colliding σ-minorities removed near i)`.
Aggregated:

> **`A i c ≤ A i c' + D i`**, where `D i` counts the removed colliding σ-minorities near level `i`.

i.e. the surviving-eliminator count drops by **at most** the σ-minority drained near `i` — the exact
"same-level cancel is the only loss, charged to one minority" fact at config level.  This is the honest
`Δ(elimAbove) ≥ −Δ(minority)`-flavored bound the residual-#3 bookkeeping calls for.  No probability.

### What this file closes / what it isolates

* **`cancelSplit_elimAbove_snd_survives_or_charged`** — the `.2`-component analogue of
  `SurvivalAccounting.cancelSplit_elimAbove_survives_or_charged` (same exhaustive case split, mirrored
  to the second output of `cancelSplit`).
* **`cancelSplit_elimAbove_pair_le`** — the pair-level inequality: the two output eliminator flags plus
  the colliding-minority flags of `{r₁,r₂}` dominate the two input eliminator flags.
* **`elimAbove_countP_drop_le_colliding`** — the **config-level `countP` delta**: under a both-Main
  applicable step, `A i c ≤ A i c' + (colliding σ-minorities removed near i)`.  The genuine config
  aggregation of the per-pair ledger via `Multiset.countP_add` / `Multiset.countP_sub`.
* **`elimAbove_countP_step_drop_le_colliding`** — the `stepDistOrSelf`-support form (self step is the
  identity; applicable step is the lemma above), the shape the trajectory lift consumes.
* The HONEST scope note: the fixed-constant band `SurvivalBandAbove σ E` is NOT pointwise step-closed
  (a single same-level cancel can drop `A i` by one, so `A i = E` can fall to `E−1`); the band is
  preserved *in aggregate* because the total drained σ-minority over the trajectory is `o(n)` (the
  Doty sharp minority bound), which is exactly what residual #2's outputs must supply as the entry
  margin.  We record this precisely (`SurvivalBandAbove_step_closed_needs_margin`) and wire the
  config delta into the existing `SpendLedgerLift` surface.

NEW file; no existing file edited; no sorry/admit/axiom/native_decide.
-/

import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.SpendLedgerLift

namespace ExactMajority

open scoped BigOperators

namespace BandStepBookkeeping

variable {L K : ℕ}

open SpendLedgerLift SurvivalAccounting

/-! ## Part 1 — the `.2`-component per-pair eliminator ledger.

`SurvivalAccounting.cancelSplit_elimAbove_survives_or_charged` covers the FIRST output of
`cancelSplit`.  The config-level `{p₁,p₂}` is an unordered multiset, so to bound
`countP_elim {p₁,p₂}` we need BOTH outputs.  We prove the mirror lemma for the SECOND output by the
same exhaustive frozen-`cancelSplit` case analysis (the roles of `s`/`t` and the index order swap). -/

/-- **`.2`-component per-pair eliminator ledger.**  If the SECOND interacting agent `t` is an above-`i`
eliminator, then after `cancelSplit s t` the second output `(cancelSplit s t).2` is STILL in
`elimAbove σ i`, OR the partner `s` carries a `σ`-minority dyadic bias at an index within distance 1
below the threshold (`s.bias = dyadic σ j`, `i ≤ j+1`).  The mirror of
`SurvivalAccounting.cancelSplit_elimAbove_survives_or_charged`. -/
theorem cancelSplit_elimAbove_snd_survives_or_charged {σ : Sign} {i : Fin (L + 1)}
    (s t : AgentState L K)
    (ht : t ∈ Phase8Convergence.elimAbove (L := L) (K := K) σ i) :
    (cancelSplit L K s t).2 ∈ Phase8Convergence.elimAbove (L := L) (K := K) σ i
      ∨ (∃ j : Fin (L + 1), i.val ≤ j.val + 1 ∧ s.bias = Bias.dyadic σ j) := by
  classical
  obtain ⟨htM, htfull, tt, k, httσ, hik, htbias⟩ := elimAbove_witness ht
  -- `t` is σ-opposite at index `k > i`.  Case on `s.bias`.
  rcases hsb : s.bias with _ | ⟨sgn_s, j⟩
  · -- `s` unbiased: `cancelSplit` does not fire, `t` unchanged.
    left
    have hsnd : (cancelSplit L K s t).2 = t := by
      unfold cancelSplit; rw [hsb, htbias]
    rw [hsnd]; exact ht
  · -- `s` dyadic at `(sgn_s, j)`.
    by_cases hsgn : sgn_s = tt
    · -- same sign: no opposite-sign fire, `t` unchanged.
      left
      have hsnd : (cancelSplit L K s t).2 = t := by
        unfold cancelSplit; rw [hsb, htbias]
        subst hsgn
        simp only [ne_eq, not_true_eq_false, if_false]
      rw [hsnd]; exact ht
    · -- opposite sign (`sgn_s ≠ tt`).
      by_cases hidx : j.val = k.val
      · -- SAME-LEVEL cancel: `t` is spent.  Then `s` is at index `j = k > i` with sign σ.
        right
        have hsgns : sgn_s = σ := by
          cases tt <;> cases sgn_s <;> cases σ <;> simp_all
        refine ⟨j, ?_, ?_⟩
        · omega
        rw [hsgns]
      · -- different index.
        by_cases hjk : j.val < k.val
        · -- `s` smaller index (`j < k`).  `t` is the LARGER-index agent (`.2` output).
          -- gap-1 (`j+1=k`): `t.bias := .zero`, `t` spent → charge to `s` at `j` (`i ≤ j+1` since
          -- `i < k = j+1`).  gap-2 (`j+2=k`): `t.bias := dyadic sgn_s (j+2=k)`, sign `sgn_s = σ`,
          -- so `t` becomes σ-minority, leaves `elimAbove` → charge to `s` at `j`.  gap ≥ 3: no fire.
          have hsgns : sgn_s = σ := by
            cases tt <;> cases sgn_s <;> cases σ <;> simp_all
          by_cases hg1 : j.val + 1 = k.val
          · right; exact ⟨j, by omega, by rw [hsgns]⟩
          · by_cases hg2 : j.val + 2 = k.val
            · right; exact ⟨j, by omega, by rw [hsgns]⟩
            · -- gap ≥ 3 with `j < k`: no fire, `t` unchanged.
              left
              have hsnd : (cancelSplit L K s t).2 = t := by
                unfold cancelSplit; rw [hsb, htbias]
                have hne : sgn_s ≠ tt := hsgn
                have hn0 : ¬ (j.val = k.val) := hidx
                have hng1 : ¬ (j.val + 1 = k.val) := hg1
                have hng1' : ¬ (k.val + 1 = j.val) := by omega
                have hng2 : ¬ (j.val + 2 = k.val) := hg2
                have hng2' : ¬ (k.val + 2 = j.val) := by omega
                simp only [ne_eq, hne, not_false_eq_true, if_pos, dif_neg hn0,
                  dif_neg hng1, dif_neg hng1', dif_neg hng2, dif_neg hng2']
              rw [hsnd]; exact ht
        · -- `t` smaller index (`k < j`).  Then `t` is the SMALLER-index agent (`.2` output).
          have hkj : k.val < j.val := by omega
          by_cases hg1' : k.val + 1 = j.val
          · -- gap-1, `t` smaller: `t.bias := dyadic tt (k+1)`, still σ-opposite, index `k+1 > i`.
            left
            have hsnd : (cancelSplit L K s t).2.bias = Bias.dyadic tt ⟨k.val + 1, by
                have hi : i.val < L + 1 := i.2; omega⟩ := by
              unfold cancelSplit; rw [hsb, htbias]
              have hne : sgn_s ≠ tt := hsgn
              have hn0 : ¬ (j.val = k.val) := by omega
              have hng1 : ¬ (j.val + 1 = k.val) := by omega
              simp only [ne_eq, hne, not_false_eq_true, if_pos, dif_neg hn0,
                dif_neg hng1, dif_pos hg1']
            simp only [Phase8Convergence.elimAbove, Finset.mem_filter, Finset.mem_univ, true_and]
            refine ⟨?_, ?_, tt, ⟨k.val + 1, by have hi : i.val < L + 1 := i.2; omega⟩, httσ, ?_, hsnd⟩
            · rw [cancelSplit_role_snd]; exact htM
            · rw [cancelSplit_full_snd]; exact htfull
            · simp only; omega
          · by_cases hg2' : k.val + 2 = j.val
            · -- gap-2, `t` smaller: `.2` output is `dyadic tt (k+1)` … read the frozen branch.
              -- In the `i.val + 2 = j.val` (here `k+2 = j`) branch, the second comp is
              -- `dyadic sgn_s (k+2)`?  NO — that branch keys on the FIRST agent's index.  Here `t`
              -- (the larger? no, `t` is SMALLER, index `k < j`) is the SECOND argument of cancelSplit.
              -- `cancelSplit s t` with `s.index = j`, `t.index = k`, `k+2 = j` ⟹ `j = k+2` is the
              -- `j' + 2 = i'` branch (with `i' := s.index = j`, `j' := t.index = k`): the SECOND comp
              -- becomes `dyadic sgn_t (k+1) = dyadic tt (k+1)`, σ-opposite, index `k+1 > i`.
              left
              have hsnd : (cancelSplit L K s t).2.bias = Bias.dyadic tt ⟨k.val + 1, by
                  have hi : i.val < L + 1 := i.2; omega⟩ := by
                unfold cancelSplit; rw [hsb, htbias]
                have hne : sgn_s ≠ tt := hsgn
                have hn0 : ¬ (j.val = k.val) := by omega
                have hng1 : ¬ (j.val + 1 = k.val) := by omega
                have hng1' : ¬ (k.val + 1 = j.val) := hg1'
                have hng2 : ¬ (j.val + 2 = k.val) := by omega
                simp only [ne_eq, hne, not_false_eq_true, if_pos, dif_neg hn0,
                  dif_neg hng1, dif_neg hng1', dif_neg hng2, dif_pos hg2']
              simp only [Phase8Convergence.elimAbove, Finset.mem_filter, Finset.mem_univ, true_and]
              refine ⟨?_, ?_, tt, ⟨k.val + 1, by have hi : i.val < L + 1 := i.2; omega⟩, httσ, ?_, hsnd⟩
              · rw [cancelSplit_role_snd]; exact htM
              · rw [cancelSplit_full_snd]; exact htfull
              · simp only; omega
            · -- gap ≥ 3 with `k < j`: no fire, `t` unchanged.
              left
              have hsnd : (cancelSplit L K s t).2 = t := by
                unfold cancelSplit; rw [hsb, htbias]
                have hne : sgn_s ≠ tt := hsgn
                have hn0 : ¬ (j.val = k.val) := by omega
                have hng1 : ¬ (j.val + 1 = k.val) := by omega
                have hng1' : ¬ (k.val + 1 = j.val) := hg1'
                have hng2 : ¬ (j.val + 2 = k.val) := by omega
                have hng2' : ¬ (k.val + 2 = j.val) := hg2'
                simp only [ne_eq, hne, not_false_eq_true, if_pos, dif_neg hn0,
                  dif_neg hng1, dif_neg hng1', dif_neg hng2, dif_neg hng2']
              rw [hsnd]; exact ht

/-! ## Part 2 — the pair-level eliminator inequality.

The membership `a ∈ Phase8Convergence.elimAbove σ i` is, by the filter definition, exactly
`SpendLedgerLift.elimAbovePred σ i a` (with the `role`/`full`/witness conjuncts in the same order).
We record the bridge, define the colliding-σ-minority indicator predicate, and prove the pair-level
inequality from the two per-pair ledgers (`.1` from `SurvivalAccounting`, `.2` from Part 1). -/

/-- The colliding-σ-minority indicator near threshold `i`: a dyadic `σ`-bias at an index within
distance 1 below `i` (the partner that charges an eliminator loss in the per-pair ledger). -/
def collidingMinorityPred (σ : Sign) (i : Fin (L + 1)) (a : AgentState L K) : Prop :=
  ∃ j : Fin (L + 1), i.val ≤ j.val + 1 ∧ a.bias = Bias.dyadic σ j

instance (σ : Sign) (i : Fin (L + 1)) :
    DecidablePred (collidingMinorityPred (L := L) (K := K) σ i) := by
  unfold collidingMinorityPred; infer_instance

/-- Membership in `Phase8Convergence.elimAbove σ i` is exactly `SpendLedgerLift.elimAbovePred σ i`. -/
theorem mem_elimAbove_iff_pred (σ : Sign) (i : Fin (L + 1)) (a : AgentState L K) :
    a ∈ Phase8Convergence.elimAbove (L := L) (K := K) σ i
      ↔ elimAbovePred (L := L) (K := K) σ i a := by
  simp only [Phase8Convergence.elimAbove, Finset.mem_filter, Finset.mem_univ, true_and,
    elimAbovePred]

/-- The per-pair ledger as an `elimAbovePred` implication for the FIRST output. -/
theorem cancelSplit_fst_pred_or_charged {σ : Sign} {i : Fin (L + 1)}
    (s t : AgentState L K)
    (hs : elimAbovePred (L := L) (K := K) σ i s) :
    elimAbovePred (L := L) (K := K) σ i (cancelSplit L K s t).1
      ∨ collidingMinorityPred (L := L) (K := K) σ i t := by
  have hsmem : s ∈ Phase8Convergence.elimAbove (L := L) (K := K) σ i :=
    (mem_elimAbove_iff_pred σ i s).mpr hs
  rcases cancelSplit_elimAbove_survives_or_charged s t hsmem with hsurv | hcharge
  · exact Or.inl ((mem_elimAbove_iff_pred σ i _).mp hsurv)
  · exact Or.inr hcharge

/-- The per-pair ledger as an `elimAbovePred` implication for the SECOND output. -/
theorem cancelSplit_snd_pred_or_charged {σ : Sign} {i : Fin (L + 1)}
    (s t : AgentState L K)
    (ht : elimAbovePred (L := L) (K := K) σ i t) :
    elimAbovePred (L := L) (K := K) σ i (cancelSplit L K s t).2
      ∨ collidingMinorityPred (L := L) (K := K) σ i s := by
  have htmem : t ∈ Phase8Convergence.elimAbove (L := L) (K := K) σ i :=
    (mem_elimAbove_iff_pred σ i t).mpr ht
  rcases cancelSplit_elimAbove_snd_survives_or_charged s t htmem with hsurv | hcharge
  · exact Or.inl ((mem_elimAbove_iff_pred σ i _).mp hsurv)
  · exact Or.inr hcharge

/-- **Pair-level eliminator inequality.**  The eliminator `countP` of the removed pair `{s,t}` is
dominated by the eliminator `countP` of the added pair `{p₁,p₂} = cancelSplit s t` plus the colliding
σ-minority `countP` of `{s,t}`.  This is the per-pair ledger (both components) in additive form — the
pair-level "each eliminator loss is charged to a colliding minority". -/
theorem cancelSplit_elimAbove_pair_le (σ : Sign) (i : Fin (L + 1)) (s t : AgentState L K) :
    Multiset.countP (elimAbovePred (L := L) (K := K) σ i)
        ({s, t} : Multiset (AgentState L K))
      ≤ Multiset.countP (elimAbovePred (L := L) (K := K) σ i)
          ({(cancelSplit L K s t).1, (cancelSplit L K s t).2} : Multiset (AgentState L K))
        + Multiset.countP (collidingMinorityPred (L := L) (K := K) σ i)
            ({s, t} : Multiset (AgentState L K)) := by
  classical
  -- Expand both two-element multiset `countP`s into indicator sums.
  have hpair : ∀ (p : AgentState L K → Prop) [DecidablePred p] (x y : AgentState L K),
      Multiset.countP p ({x, y} : Multiset (AgentState L K))
        = (if p x then 1 else 0) + (if p y then 1 else 0) := by
    intro p _ x y
    rw [show ({x, y} : Multiset (AgentState L K)) = x ::ₘ y ::ₘ 0 from rfl]
    rw [Multiset.countP_cons, Multiset.countP_cons, Multiset.countP_zero]
    by_cases hx : p x <;> by_cases hy : p y <;> simp [hx, hy]
  rw [hpair (elimAbovePred (L := L) (K := K) σ i) s t,
      hpair (elimAbovePred (L := L) (K := K) σ i) (cancelSplit L K s t).1 (cancelSplit L K s t).2,
      hpair (collidingMinorityPred (L := L) (K := K) σ i) s t]
  -- Now a pure indicator inequality from the two per-pair ledgers.
  have h1 : (if elimAbovePred (L := L) (K := K) σ i s then (1 : ℕ) else 0)
      ≤ (if elimAbovePred (L := L) (K := K) σ i (cancelSplit L K s t).1 then 1 else 0)
        + (if collidingMinorityPred (L := L) (K := K) σ i t then 1 else 0) := by
    by_cases hs : elimAbovePred (L := L) (K := K) σ i s
    · rcases cancelSplit_fst_pred_or_charged s t hs with hp | hc
      · simp [hs, hp]
      · simp [hs, hc]
    · simp [hs]
  have h2 : (if elimAbovePred (L := L) (K := K) σ i t then (1 : ℕ) else 0)
      ≤ (if elimAbovePred (L := L) (K := K) σ i (cancelSplit L K s t).2 then 1 else 0)
        + (if collidingMinorityPred (L := L) (K := K) σ i s then 1 else 0) := by
    by_cases ht : elimAbovePred (L := L) (K := K) σ i t
    · rcases cancelSplit_snd_pred_or_charged s t ht with hp | hc
      · simp [ht, hp]
      · simp [ht, hc]
    · simp [ht]
  omega

/-! ## Part 3 — the config-level `countP` delta.

Lift the pair inequality (Part 2) through one `StepRel` step `c' = c − {r₁,r₂} + {p₁,p₂}` via the
standard `Multiset.countP_add` / `Multiset.countP_sub` identities (the
`Phase7Convergence.minorityU_stepOrSelf_drop` idiom).  Under `Phase7AllMain`, `Transition = cancelSplit`
(`Phase7Convergence.Transition_eq_cancelSplit_of_phase7_main`).  The result: the surviving-eliminator
`countP` at level `i` drops by AT MOST the colliding σ-minority drained from the removed pair. -/

/-- **Config-level eliminator `countP` delta (applicable, both-Main step).**  For an applicable pair
`(s,t)` of phase-7 Main agents, the eliminator `countP` at level `i` after the step is at least the
before-count minus the colliding σ-minorities removed:
`A i c ≤ A i (stepOrSelf c s t) + countP(collidingMinorityPred σ i){s,t}`.  The config aggregation of
the per-pair ledger; no probability. -/
theorem elimAbove_countP_drop_le_colliding (σ : Sign) (i : Fin (L + 1)) (n : ℕ)
    (c : Config (AgentState L K)) (hInv : Phase7Convergence.Phase7AllMain (L := L) (K := K) n c)
    (s t : AgentState L K) (happ : Protocol.Applicable c s t) :
    Multiset.countP (elimAbovePred (L := L) (K := K) σ i) c
      ≤ Multiset.countP (elimAbovePred (L := L) (K := K) σ i)
          (Protocol.stepOrSelf (NonuniformMajority L K) c s t)
        + Multiset.countP (collidingMinorityPred (L := L) (K := K) σ i)
            ({s, t} : Multiset (AgentState L K)) := by
  classical
  obtain ⟨_, hph⟩ := hInv
  have hsub : ({s, t} : Multiset (AgentState L K)) ≤ c := happ
  have hsmem : s ∈ c := Multiset.mem_of_le hsub (by simp)
  have htmem : t ∈ c := Multiset.mem_of_le hsub (by simp)
  obtain ⟨h17, h1M⟩ := hph s hsmem
  obtain ⟨h27, h2M⟩ := hph t htmem
  have hc' : Protocol.stepOrSelf (NonuniformMajority L K) c s t
      = c - {s, t} + {(Transition L K s t).1, (Transition L K s t).2} := by
    unfold Protocol.stepOrSelf; rw [if_pos happ]; rfl
  rw [hc', Multiset.countP_add, Multiset.countP_sub hsub,
      Phase7Convergence.Transition_eq_cancelSplit_of_phase7_main s t h17 h27 h1M h2M]
  -- `countP_sub` leaves `A i c − countP elim {s,t}`; the pair lemma bounds `countP elim {s,t}`.
  have hpair := cancelSplit_elimAbove_pair_le (L := L) (K := K) σ i s t
  have hpair_le : Multiset.countP (elimAbovePred (L := L) (K := K) σ i)
      ({s, t} : Multiset (AgentState L K))
        ≤ Multiset.countP (elimAbovePred (L := L) (K := K) σ i) c :=
    Multiset.countP_le_of_le _ hsub
  omega

/-- **Config-level eliminator `countP` delta (`stepDistOrSelf` support form).**  At any support point
`c'` of one Phase-7 step from `c`, the eliminator `countP` at level `i` drops by at most a colliding
σ-minority budget `d`: either `c' = c` (self step / non-applicable pair, `d = 0`) or `c' = stepOrSelf
c s t` for an applicable both-Main pair, in which case `d` is the colliding σ-minority `countP` of the
removed pair `{s,t}` (Part 3).  This is the shape the trajectory survival lift consumes — the surviving
eliminator supply at every level falls by at most the minority drained that step. -/
theorem elimAbove_countP_step_drop_le_colliding (σ : Sign) (i : Fin (L + 1)) (n : ℕ)
    (c c' : Config (AgentState L K)) (hInv : Phase7Convergence.Phase7AllMain (L := L) (K := K) n c)
    (hc' : c' ∈ ((NonuniformMajority L K).stepDistOrSelf c).support) :
    ∃ d : ℕ,
      (d = 0 ∨ ∃ s t : AgentState L K, Protocol.Applicable c s t ∧
        d = Multiset.countP (collidingMinorityPred (L := L) (K := K) σ i)
          ({s, t} : Multiset (AgentState L K)))
      ∧ Multiset.countP (elimAbovePred (L := L) (K := K) σ i) c
        ≤ Multiset.countP (elimAbovePred (L := L) (K := K) σ i) c' + d := by
  classical
  by_cases hc : 2 ≤ c.card
  · rw [show (NonuniformMajority L K).stepDistOrSelf c
        = (NonuniformMajority L K).stepDist c hc by
        unfold Protocol.stepDistOrSelf; rw [dif_pos hc]] at hc'
    obtain ⟨⟨s, t⟩, hr⟩ := Protocol.stepDist_support (NonuniformMajority L K) c hc c' hc'
    subst hr
    by_cases happ : Protocol.Applicable c s t
    · refine ⟨Multiset.countP (collidingMinorityPred (L := L) (K := K) σ i)
        ({s, t} : Multiset (AgentState L K)),
        Or.inr ⟨s, t, happ, rfl⟩, ?_⟩
      exact elimAbove_countP_drop_le_colliding σ i n c hInv s t happ
    · -- non-applicable: `stepOrSelf` is the identity, no drop.
      refine ⟨0, Or.inl rfl, ?_⟩
      show Multiset.countP (elimAbovePred (L := L) (K := K) σ i) c
        ≤ Multiset.countP (elimAbovePred (L := L) (K := K) σ i)
            (Protocol.stepOrSelf (NonuniformMajority L K) c s t) + 0
      rw [Protocol.stepOrSelf_eq_self_of_not_applicable happ]; omega
  · -- `card < 2`: the support is `{c}`, no drop.
    rw [show (NonuniformMajority L K).stepDistOrSelf c = PMF.pure c by
        unfold Protocol.stepDistOrSelf; rw [dif_neg hc]] at hc'
    rw [PMF.mem_support_pure_iff] at hc'; subst hc'
    exact ⟨0, Or.inl rfl, by omega⟩

/-! ## Part 4 — the band step closure and the honest entry-margin residual.

The config `countP` delta (Part 3) gives `A i c ≤ A i c' + d`, with `d` the colliding σ-minority budget
of the removed pair — and `d ≤ 2` always (the pair has two agents).  Hence

> `A i c' ≥ A i c − d ≥ A i c − 2`.

**The fixed-constant band `SurvivalBandAbove σ E` is therefore NOT pointwise step-closed.**  A single
same-level cancel can spend one above-`i` eliminator (`d = 1`), so a level sitting EXACTLY at the floor
(`A i c = E`) can fall to `A i c' = E − 1`.  The band survives along the trajectory only because the
TOTAL drained σ-minority (= the total eliminator spend) is `o(n)` (Doty's sharp minority bound), and the
Phase-7-ENTRY above-level margin `Entry` exceeds the floor `E` by that total spend.  This is exactly the
entry margin that residual #2's outputs (`BandRouting` / `GapAlignment` `GapAlignedElimFloor`, and the
sharpened spend constant) must supply.

We make this precise two ways, both PROVED from the config delta:

* `survivalBand_step_closed_of_margin` — the band IS step-closed at a level whose entry count carries the
  per-step colliding margin (`E + d ≤ A i c`).  This is the honest conditional closure: with the margin,
  the per-step delta is absorbed.
* `survivalBandAbove_step_closed_of_marginBand` — packaging it as a closure of the **margin band**
  `SurvivalBandMargin σ E` (the floor band with a uniform `+2` slack, the max single-step spend) into the
  plain band `SurvivalBandAbove σ E`.  The margin band is the precise object Phase-7 entry must carry. -/

/-- The floor band with a uniform single-step margin: every live-minority level carries `≥ E + 2`
above-level eliminators (so one step's spend `≤ 2` cannot breach the floor `E`).  This is the
honest object the Phase-7 entry must export — `SurvivalBandAbove σ (E+2)` recentered as the slack the
per-step ledger consumes. -/
def SurvivalBandMargin (σ : Sign) (E : ℕ) (c : Config (AgentState L K)) : Prop :=
  ∀ i : Fin (L + 1),
    1 ≤ (Phase8Convergence.minorityAt (L := L) (K := K) σ i).sum c.count →
    E + 2 ≤ (Phase8Convergence.elimAbove (L := L) (K := K) σ i).sum c.count

/-- The colliding σ-minority budget of any removed pair is `≤ 2` (the pair has two agents). -/
theorem collidingMinority_pair_le_two (σ : Sign) (i : Fin (L + 1)) (s t : AgentState L K) :
    Multiset.countP (collidingMinorityPred (L := L) (K := K) σ i)
      ({s, t} : Multiset (AgentState L K)) ≤ 2 := by
  refine le_trans (Multiset.countP_le_card _ _) ?_
  simp [Multiset.card_pair]

/-- **Honest band step closure (per-step colliding margin).**  At a level `i` whose Phase-8-entry count
carries the per-step colliding margin (the config delta budget `d` from Part 3), the floor `E ≤ A i c'`
survives one step.  Concretely: from `A i c' ≥ A i c − d` (Part 3) and `A i c ≥ E + d`, get `E ≤ A i c'`.
This is the conditional closure the trajectory ledger absorbs once the entry margin covers the spend. -/
theorem survivalBand_step_closed_of_margin (σ : Sign) (i : Fin (L + 1)) (n E d : ℕ)
    (c c' : Config (AgentState L K)) (hInv : Phase7Convergence.Phase7AllMain (L := L) (K := K) n c)
    (hmargin : E + d ≤ Multiset.countP (elimAbovePred (L := L) (K := K) σ i) c)
    (hdelta : Multiset.countP (elimAbovePred (L := L) (K := K) σ i) c
      ≤ Multiset.countP (elimAbovePred (L := L) (K := K) σ i) c' + d) :
    E ≤ Multiset.countP (elimAbovePred (L := L) (K := K) σ i) c' := by
  omega

/-- **The margin band is step-closed into the floor band.**  If the Phase-8-entry config carries the
margin band `SurvivalBandMargin σ E` (floor `+2` at every live level), then after ONE Phase-7 step the
floor band `SurvivalBandAbove σ E` holds at every level that is STILL live at `c'` and was ALSO live at
`c`.  The per-step spend `≤ 2` is absorbed by the `+2` margin.

This is the honest `hBand`-shaped closure: it is conditional on the level being live at BOTH `c` and `c'`
(a minority newly created at a previously-empty level is the genuine residual the entry margin /
residual-#2 routing must rule out — a Phase-7 step can only DRAIN minorities, never raise the per-level
minority count above its entry value, so a level live at `c'` was live at `c`; that monotonicity is the
landed minority-survival upper bound, carried here as `hLiveBack`). -/
theorem survivalBandAbove_step_closed_of_marginBand (σ : Sign) (n E : ℕ)
    (c c' : Config (AgentState L K)) (hInv : Phase7Convergence.Phase7AllMain (L := L) (K := K) n c)
    (hMargin : SurvivalBandMargin (L := L) (K := K) σ E c)
    (hc' : c' ∈ ((NonuniformMajority L K).stepDistOrSelf c).support)
    (hLiveBack : ∀ i : Fin (L + 1),
      1 ≤ (Phase8Convergence.minorityAt (L := L) (K := K) σ i).sum c'.count →
      1 ≤ (Phase8Convergence.minorityAt (L := L) (K := K) σ i).sum c.count) :
    BandLocalization.SurvivalBandAbove (L := L) (K := K) σ E c' := by
  intro i hi'
  -- live at `c'` ⟹ live at `c` (the carried minority-monotonicity).
  have hi : 1 ≤ (Phase8Convergence.minorityAt (L := L) (K := K) σ i).sum c.count := hLiveBack i hi'
  -- entry margin at level `i`.
  have hmarg := hMargin i hi
  -- config delta at level `i`.
  obtain ⟨d, hdform, hdelta⟩ :=
    elimAbove_countP_step_drop_le_colliding σ i n c c' hInv hc'
  -- bound `d ≤ 2`.
  have hd2 : d ≤ 2 := by
    rcases hdform with hd0 | ⟨s, t, _, hdeq⟩
    · omega
    · rw [hdeq]; exact collidingMinority_pair_le_two σ i s t
  -- translate the margin/delta into the `countP` observable via the bridges.
  rw [elimAbove_sum_eq_countP] at hmarg ⊢
  rw [elimAbove_sum_eq_countP] at hdelta
  omega

/-! ## Scope summary (honest).

**PROVED outright, axiom-clean (this file):**
* `cancelSplit_elimAbove_snd_survives_or_charged` — the `.2`-component per-pair eliminator ledger (the
  mirror of `SurvivalAccounting.cancelSplit_elimAbove_survives_or_charged`), by exhaustive frozen-
  `cancelSplit` case analysis on the second output.
* `cancelSplit_elimAbove_pair_le` — the pair-level eliminator inequality: the two output eliminator flags
  plus the colliding-σ-minority flags of `{s,t}` dominate the two input eliminator flags (both per-pair
  ledgers, additive form).
* `elimAbove_countP_drop_le_colliding` — the **config-level `countP` delta**: under a both-Main applicable
  step, `A i c ≤ A i (stepOrSelf c s t) + countP(collidingMinority){s,t}` (via `Multiset.countP_add` /
  `Multiset.countP_sub` + `Transition_eq_cancelSplit_of_phase7_main`).  The genuine config aggregation of
  the per-pair ledger — the surviving-eliminator supply drops by at most the σ-minority drained.
* `elimAbove_countP_step_drop_le_colliding` — the `stepDistOrSelf`-support form (self / non-applicable
  step ⟹ `d = 0`; applicable both-Main ⟹ `d =` colliding `countP`).
* `survivalBand_step_closed_of_margin` — the per-level conditional closure: a level with the per-step
  colliding margin (`E + d ≤ A i c`) keeps the floor (`E ≤ A i c'`).
* `survivalBandAbove_step_closed_of_marginBand` — the **`hBand`-shaped closure**: the margin band
  `SurvivalBandMargin σ E` (floor `+2`) is step-closed into the floor band `SurvivalBandAbove σ E`,
  conditional on minority-monotonicity (`hLiveBack`: a level live at `c'` was live at `c`).

**HONEST RESIDUAL for the fixed-constant `hBand` of `SpendLedgerLift.phase7Surviving_step_of_band`:**
the plain fixed-`E` band `SurvivalBandAbove σ E` is NOT pointwise step-closed (a single same-level cancel
spends one eliminator, so `A i = E` can fall to `E − 1`).  Two honest inputs close it, BOTH from residual
#2's outputs (NOT a new probability tail):

1. **Entry margin** — Phase-7 entry must carry `SurvivalBandMargin σ E` (floor `+2`, or more generally
   floor `+ total spend`), i.e. the strengthened above-level margin `Entry ≥ E + spend`.  This is the
   `GapAlignedElimFloor` routing + the sharpened Doty spend constant (`Spend = o(n)`) that residual #2 /
   `SurvivalAccounting.survival_floor_honest` pin down.  With it, `survivalBandAbove_step_closed_of_marginBand`
   discharges the per-step band closure and `SpendLedgerLift.survivalBand_ae_along_trajectory` lifts it
   along the whole trajectory.

2. **Minority monotonicity** (`hLiveBack`) — a Phase-7 `cancelSplit` step only DRAINS σ-minorities
   (`Phase7Convergence.cancelSplit_minorityU_pair_le` / `minorityU_stepOrSelf_drop`: the per-level minority
   count never rises), so a level live at `c'` was live at `c`.  This is the landed minority-survival
   upper bound, applied per level.

With (1) and (2) supplied, `hBand` is discharged and the residual-#3 chain
`phase7Surviving_step_of_band → survivalBand_ae_along_trajectory → phase7_to_phase8_via_canonicalSpend`
closes to `EliminatorMargins.Phase7To8Structure` with NO remaining probability — only the deterministic
`countP` bookkeeping of this file plus the entry margin from residual #2.
-/

end BandStepBookkeeping

end ExactMajority
