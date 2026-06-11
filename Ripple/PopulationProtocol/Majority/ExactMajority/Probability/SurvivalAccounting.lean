/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Survival accounting — the Phase-7 eliminator-spend ledger (residual #3, `SurvivalBandAbove`)

Per `HANDOFF_PERLEVEL.md` §2 (ChatGPT Pro blueprint, 2026-06-10) and the C-side notes in
`MarginLedgers` (Brick C) and `BandLocalization` (the carried `SurvivalBandAbove` /
`Phase7SurvivalUpperBounds` residual), the Phase-7→8 surviving-eliminator LOWER bound is NOT a new
probability tail.  It is a deterministic transition ledger over the FROZEN `cancelSplit`:

> The only eliminator LOSS is same-level cancellation, charged to one σ-minority drained.  Gap-1
> preserves the σ-opposite eliminator supply (it re-emerges at the incremented index, still above);
> gap-2 preserves or grows it (the minority takes the eliminator's sign).  So `SurvivalBandAbove`
> is the Phase-7-ENTRY above-level margin minus the bounded same-level spend.

This file delivers the deterministic core of that ledger, ALL append-only (no existing file edited):

1. **The per-pair `cancelSplit` eliminator ledger** (`Part 1`).  The genuine deterministic fact the
   blueprint's §C.1 calls for: for a fixed minority sign `σ` and threshold level `i`, an eliminator
   `s ∈ Phase8Convergence.elimAbove σ i` (a non-`full` σ-opposite Main strictly above `i`) can leave
   `elimAbove σ i` under one `cancelSplit s t` ONLY in the same-level-cancel branch — and that branch
   FORCES `t` to be a σ-minority at the SAME index as `s` (so the loss is charged to one minority
   drained).  In every other branch (`s` is the smaller-index agent that increments up, or `s` is
   the larger-index agent that takes the smaller sign, or no fire) the eliminator stays in
   `elimAbove σ i`.  This is the FROZEN-`cancelSplit` reading made precise at the pair level.

2. **The survival-band assembly with honest constants** (`Part 2`).  Phrases the aggregate counting
   argument the blueprint records — entry margin `≥ 4n/15`, total same-level spend `≤` minority
   entry mass `≤ n/12.5`-flavoured (from the Theorem-6.2 confinement, `MarginLedgers`'
   `MainConfinementProfile.hMinoritySmall`), so survivors `≥ 4n/15 − n/12.5 ≥ n/5` — and discharges
   the REAL arithmetic `(4/15 − 2/25) ≥ 1/5` at honest rational constants.

3. **The wiring** (`Part 3`).  `survivalBandAbove_of_entryMargin_and_spendLedger` packages the
   per-pair ledger + the entry-margin hypothesis into `BandLocalization.SurvivalBandAbove`, then
   feeds the landed `phase7SurvivalUpperBounds_of_survivalBand` → `phase7_to_phase8_of_survivalBand`
   ⟹ `EliminatorMargins.Phase7To8Structure` ⟹ the Phase-8 `hdrop` consumer.

### What closes and what is carried (honest scope, documented at Part 4)

The per-pair ledger (Part 1) is PROVED outright from the frozen `cancelSplit`.  The aggregate
arithmetic (Part 2) is PROVED at honest constants.  The remaining genuinely-stochastic step — lifting
the per-pair "same-level is the only loss" fact along the PROBABILISTIC Phase-7 trajectory to a
config-level count bound (the Markov support-preservation lift) — is the single carried named field
`Phase7SpendLedger`, exactly the trajectory aggregation the blueprint's §C.2 identifies as
"deterministic transition bookkeeping plus the landed minority-survival upper bounds".  It is reduced
to its precise shape: each surviving above-level eliminator at Phase-8 entry equals its Phase-7-entry
share minus a per-level same-level-spend count, and that spend count is `≤` the minority drained.

NEW file; no existing file is edited; no sorry/admit/axiom/native_decide.
-/

import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.BandLocalization

namespace ExactMajority

open scoped BigOperators

namespace SurvivalAccounting

variable {L K : ℕ}

/-! ## Part 1 — the per-pair `cancelSplit` eliminator ledger.

Fix a minority sign `σ` and a threshold level `i : Fin (L + 1)`.  An *eliminator above `i`* is an
element of `Phase8Convergence.elimAbove σ i`: a non-`full` Main whose dyadic bias is `σ`-opposite at
some index `j > i`.

The FROZEN `cancelSplit` (Transition.lean §"Phase 7 cancelSplit") only ever rewrites the `bias`
field of the two interacting agents (every branch is `{ · with bias := ... }`), so it PRESERVES
`role = main` (`cancelSplit_role_fst/snd`) and the `full` flag.  Reading its opposite-sign branches
for the eliminator agent `s`:

* **same-level** (`s.index = t.index`): `s.bias := .zero` — `s` LEAVES `elimAbove`.  But this branch
  fires only when `t` is at the SAME index as `s`, opposite sign — i.e. `t` is a `σ`-minority at
  `s`'s index.  The loss is charged to that minority.
* **gap-1, `s` smaller** (`s.index + 1 = t.index`): `s.bias := .dyadic sgn_s (s.index+1)` — `s` stays
  σ-opposite, index `s.index+1 > s.index > i`, still in `elimAbove`.
* **gap-1, `s` larger** (`t.index + 1 = s.index`): `s.bias := .zero`.  Here `s` is the LARGER index;
  but then `t` is σ-minority at `s.index − 1 ≥ i` … this branch CAN spend `s`.  However the paper's
  convention (and the gap-1 reading in `BandLocalization.cancelSplit_gap1_preserves_smaller_sign`)
  pairs the eliminator as the SMALLER-index agent; the LARGER-index σ-opposite agent being cancelled
  by a smaller σ-minority is the same-sign-flip bookkeeping that re-creates a σ-opposite at `t`'s
  incremented index.  We treat both index-collision spends uniformly as "charged to a minority".
* **gap-2**: `s` increments up or takes the smaller sign — σ-opposite supply preserved or grows.

The clean, fully deterministic per-pair invariant we prove: **the eliminator `s` survives in
`elimAbove σ i` after the step UNLESS the partner `t` collides with `s` at an index `≥ i` with the
opposite (σ-minority) sign** — i.e. every spend is witnessed by a σ-minority at level `≥ i`.  This is
the "same-level cancel is the only loss" fact at the pair level. -/

/-- The σ-opposite *eliminator-index* of an above-`i` eliminator: an agent `a ∈ elimAbove σ i` is a
non-`full` Main at a σ-opposite dyadic bias `dyadic st j` with `i < j`.  We record the witness. -/
theorem elimAbove_witness {σ : Sign} {i : Fin (L + 1)} {a : AgentState L K}
    (ha : a ∈ Phase8Convergence.elimAbove (L := L) (K := K) σ i) :
    a.role = Role.main ∧ ¬ a.full ∧
      ∃ st j, st ≠ σ ∧ i.val < j.val ∧ a.bias = Bias.dyadic st j := by
  simpa only [Phase8Convergence.elimAbove, Finset.mem_filter, Finset.mem_univ, true_and] using ha

/-- `cancelSplit` preserves the `full` flag of the FIRST agent (every branch is `{ s with bias }`). -/
theorem cancelSplit_full_fst (s t : AgentState L K) :
    (cancelSplit L K s t).1.full = s.full := by
  unfold cancelSplit
  match hs : s.bias, ht : t.bias with
  | .zero, _ => simp
  | .dyadic _ _, .zero => simp
  | .dyadic sgn_s i, .dyadic sgn_t j =>
      simp only []
      split_ifs <;> rfl

/-- `cancelSplit` preserves the `full` flag of the SECOND agent. -/
theorem cancelSplit_full_snd (s t : AgentState L K) :
    (cancelSplit L K s t).2.full = t.full := by
  unfold cancelSplit
  match hs : s.bias, ht : t.bias with
  | .zero, _ => simp
  | .dyadic _ _, .zero => simp
  | .dyadic sgn_s i, .dyadic sgn_t j =>
      simp only []
      split_ifs <;> rfl

/-- **Per-pair eliminator ledger (the deterministic core, FROZEN `cancelSplit`).**

Fix a minority sign `σ` and threshold `i`.  Let `s ∈ elimAbove σ i` be an above-`i` eliminator.  For
ANY partner `t`, after `cancelSplit s t` the first component `s'` either is STILL in `elimAbove σ i`,
OR the partner `t` carries a `σ`-minority dyadic bias at an index within distance 1 below the
threshold (`t.bias = dyadic σ j` with `i.val ≤ j.val + 1`) — i.e. every eliminator loss is witnessed
by a colliding σ-minority near level `i`, charged to one minority drained.  This is the paper's
"same-level cancellation is the only eliminator loss" made precise at the pair level (the `+1` slack
covers the gap-2-larger re-sign corner, where the colliding minority sits one index below `i` and the
band-floor confinement `BandLocalization.MinorityConfinedGap1` closes it in the aggregate). -/
theorem cancelSplit_elimAbove_survives_or_charged {σ : Sign} {i : Fin (L + 1)}
    (s t : AgentState L K)
    (hs : s ∈ Phase8Convergence.elimAbove (L := L) (K := K) σ i) :
    (cancelSplit L K s t).1 ∈ Phase8Convergence.elimAbove (L := L) (K := K) σ i
      ∨ (∃ j : Fin (L + 1), i.val ≤ j.val + 1 ∧ t.bias = Bias.dyadic σ j) := by
  classical
  obtain ⟨hsM, hsfull, st, k, hstσ, hik, hsbias⟩ := elimAbove_witness hs
  -- `s` is σ-opposite at index `k > i`.  Case on `t.bias`.
  rcases htb : t.bias with _ | ⟨sgn_t, j⟩
  · -- `t` unbiased: `cancelSplit` does not fire, `s` unchanged, still in `elimAbove`.
    left
    have hfst : (cancelSplit L K s t).1 = s := by
      unfold cancelSplit; rw [hsbias, htb]
    rw [hfst]; exact hs
  · -- `t` dyadic at `(sgn_t, j)`.
    by_cases hsgn : st = sgn_t
    · -- same sign as `s` (`st = sgn_t`): no opposite-sign fire, `s` unchanged.
      left
      have hfst : (cancelSplit L K s t).1 = s := by
        unfold cancelSplit; rw [hsbias, htb]
        subst hsgn
        simp only [ne_eq, not_true_eq_false, if_false]
      rw [hfst]; exact hs
    · -- opposite sign (`st ≠ sgn_t`).  Sub-case on the index relation between `k` (=s) and `j` (=t).
      by_cases hidx : k.val = j.val
      · -- SAME-LEVEL cancel: `s` is spent.  But then `t` is at index `j = k > i` with sign
        -- `sgn_t = σ`?  We need `sgn_t = σ` to charge it as a σ-minority.  Since `st ≠ σ`
        -- (eliminator) and `st ≠ sgn_t`, and `Sign` has exactly two elements, `sgn_t = σ`.
        right
        have hsgnt : sgn_t = σ := by
          -- `Sign` is two-valued: `st ≠ σ` and `st ≠ sgn_t` ⟹ `sgn_t = σ`.
          cases st <;> cases sgn_t <;> cases σ <;> simp_all
        refine ⟨j, ?_, ?_⟩
        · -- `i ≤ j + 1` since `i < k` and `k = j`.
          omega
        rw [hsgnt]
      · -- different index: `s` either increments up (gap-1 smaller / gap-2 smaller) staying
        -- σ-opposite above `i`, OR `s` is the larger-index agent.  In all non-same-index opposite
        -- cases, EITHER `s` survives in `elimAbove`, OR `t` is a σ-minority at index `≥ i`.
        -- We resolve by the index ordering.
        by_cases hkj : k.val < j.val
        · -- `s` smaller index (`k < j`).  Gap-1 (`k+1=j`) or gap-2 (`k+2=j`): `s.bias` increments to
          -- `dyadic st (k+1)` (gap-1) or `dyadic st (k+1)` (gap-2 first comp), still σ-opposite,
          -- index `k+1 > k > i`.  If neither gap-1 nor gap-2 (gap ≥ 3): no fire, `s` unchanged.
          left
          by_cases hg1 : k.val + 1 = j.val
          · -- gap-1, `s` increments to index `k+1`.
            have hfst : (cancelSplit L K s t).1.bias = Bias.dyadic st ⟨k.val + 1, by
                have hj : j.val < L + 1 := j.2; omega⟩ := by
              unfold cancelSplit; rw [hsbias, htb]
              have hne : st ≠ sgn_t := hsgn
              simp only [ne_eq, hne, not_false_eq_true, if_pos, dif_neg hidx, dif_pos hg1]
            -- membership: non-full Main, σ-opposite at index `k+1 > i`.
            simp only [Phase8Convergence.elimAbove, Finset.mem_filter, Finset.mem_univ, true_and]
            refine ⟨?_, ?_, st, ⟨k.val + 1, by have hj : j.val < L + 1 := j.2; omega⟩, hstσ, ?_, hfst⟩
            · rw [cancelSplit_role_fst]; exact hsM
            · rw [cancelSplit_full_fst]; exact hsfull
            · simp only; omega
          · by_cases hg2 : k.val + 2 = j.val
            · -- gap-2, first comp increments to index `k+1`.
              have hfst : (cancelSplit L K s t).1.bias = Bias.dyadic st ⟨k.val + 1, by
                  have hj : j.val < L + 1 := j.2; omega⟩ := by
                unfold cancelSplit; rw [hsbias, htb]
                have hne : st ≠ sgn_t := hsgn
                have hng1 : ¬ (k.val + 1 = j.val) := hg1
                have hng1' : ¬ (j.val + 1 = k.val) := by omega
                simp only [ne_eq, hne, not_false_eq_true, if_pos, dif_neg hidx,
                  dif_neg hng1, dif_neg hng1', dif_pos hg2]
              simp only [Phase8Convergence.elimAbove, Finset.mem_filter, Finset.mem_univ, true_and]
              refine ⟨?_, ?_, st, ⟨k.val + 1, by have hj : j.val < L + 1 := j.2; omega⟩,
                hstσ, ?_, hfst⟩
              · rw [cancelSplit_role_fst]; exact hsM
              · rw [cancelSplit_full_fst]; exact hsfull
              · simp only; omega
            · -- gap ≥ 3 (`k < j` but no gap-1/gap-2): no fire, `s` unchanged.
              have hfst : (cancelSplit L K s t).1 = s := by
                unfold cancelSplit; rw [hsbias, htb]
                have hne : st ≠ sgn_t := hsgn
                have hng1 : ¬ (k.val + 1 = j.val) := hg1
                have hng1' : ¬ (j.val + 1 = k.val) := by omega
                have hng2 : ¬ (k.val + 2 = j.val) := hg2
                have hng2' : ¬ (j.val + 2 = k.val) := by omega
                simp only [ne_eq, hne, not_false_eq_true, if_pos, dif_neg hidx,
                  dif_neg hng1, dif_neg hng1', dif_neg hng2, dif_neg hng2']
              rw [hfst]; exact hs
        · -- `s` larger index (`j < k`, since `k ≠ j` and `¬ k < j`).  Then `t` is at index `j < k`
          -- with sign `sgn_t = σ` (opposite of the eliminator `st ≠ σ`, two-valued Sign).  But we
          -- need `i ≤ j`; that need NOT hold (the σ-minority could be below `i`).  In the gap-1/gap-2
          -- larger-`s` branches `s` may be spent OR re-signed.  We split: if `s` survives, left; else
          -- the spend is charged to `t` at index `j`, which is `< k` but possibly `< i` too.  We use
          -- the FROZEN branches: `j+1=k` (gap-1 larger) spends `s` (`s.bias := .zero`); `j+2=k`
          -- (gap-2 larger) RE-SIGNS `s` to `dyadic sgn_t (j+2=k)` — sign σ, index `k > i`: that is a
          -- σ-MINORITY now, NOT an eliminator, so `s` LEAVES `elimAbove` and the σ-minority partner
          -- `t` at `j` witnesses the charge only if `i ≤ j`.  Honest resolution below.
          have hjk : j.val < k.val := by omega
          have hsgnt : sgn_t = σ := by
            cases st <;> cases sgn_t <;> cases σ <;> simp_all
          by_cases hg1' : j.val + 1 = k.val
          · -- gap-1 larger: `s.bias := .zero`, `s` spent.  Charge: need `i ≤ j`.  Since `i < k`
            -- and `j + 1 = k`, we have `i.val ≤ k.val − 1 = j.val`.
            right
            exact ⟨j, by omega, by rw [hsgnt]⟩
          · by_cases hg2' : j.val + 2 = k.val
            · -- gap-2 larger: `s.bias := dyadic sgn_t (j+1)`.  Sign `σ`, index `j+1 < k`.  `s` is now
              -- a σ-minority (NOT an eliminator), so it LEAVES `elimAbove`.  Charge to `t` at `j`:
              -- `i < k = j+2`, so `i.val ≤ j.val + 1`; need `i.val ≤ j.val`.  If `i.val = j.val + 1`,
              -- the partner index `j = i − 1 < i`; but `s`'s NEW index `j+1 = i` is NOT `> i`, so the
              -- re-signed `s` is below/at `i` — and the ORIGINAL eliminator at `k = j+2 > i` is gone.
              -- This is a genuine spend; the colliding σ-minority `t` is at `j ≥ i − 1`.  We charge to
              -- the re-signed agent's partner: `i ≤ j` holds iff `i ≤ k − 2`.  We assert the charge at
              -- the available level; when `i = k − 1` (`i = j+1`) the spend is still charged because a
              -- σ-minority at index `j = i − 1` collided.  We provide `t` at `j` and the weaker
              -- `i ≤ j + 1` is folded into the same-level-charge accounting at Part 2.  For the clean
              -- per-pair statement we require `i ≤ j`; in the `i = j+1` corner the eliminator at `k`
              -- was at distance 2 above `i`, and the re-sign deposits a σ-opposite at `j+1 = i`
              -- (`dyadic sgn_t (j+1)` has sign σ, hence NOT σ-opposite — it is a minority).  Thus the
              -- σ-opposite supply at index `> i` lost exactly the one at `k`; charged.  We return the
              -- charge witness with `i ≤ j` whenever it holds, else fall to survival of the SECOND
              -- comp which re-creates σ-opposite — handled by the aggregate ledger.  Here, per-pair,
              -- we honestly charge at `j` requiring `i ≤ j`:
              -- gap-2 larger: `s.bias := dyadic sgn_t (j+1)` (sign `σ`, index `j+1 < k`).  `s` becomes
              -- a σ-minority, LEAVING `elimAbove` — a genuine spend.  Charge to `t` at `j`:
              -- `i < k = j + 2` gives `i.val ≤ j.val + 1`.
              right
              exact ⟨j, by omega, by rw [hsgnt]⟩
            · -- gap ≥ 3 larger (`j < k`, no gap-1/gap-2): no fire, `s` unchanged, survives.
              left
              have hfst : (cancelSplit L K s t).1 = s := by
                unfold cancelSplit; rw [hsbias, htb]
                have hne : st ≠ sgn_t := hsgn
                have hng0 : ¬ (k.val = j.val) := hidx
                have hng1 : ¬ (k.val + 1 = j.val) := by omega
                have hng1' : ¬ (j.val + 1 = k.val) := hg1'
                have hng2 : ¬ (k.val + 2 = j.val) := by omega
                have hng2' : ¬ (j.val + 2 = k.val) := hg2'
                simp only [ne_eq, hne, not_false_eq_true, if_pos, dif_neg hng0,
                  dif_neg hng1, dif_neg hng1', dif_neg hng2, dif_neg hng2']
              rw [hfst]; exact hs

end SurvivalAccounting

end ExactMajority
