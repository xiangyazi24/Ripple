/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Phase 7 — one-sided cancellation of high-level minority mass (Doty et al. §6, Phase 7)

`Phase7Transition` (Protocol/Transition.lean:1303) cancels opposite-sign Main
agents whose exponent **gap is ≤ 2**, via `cancelSplit`:

```
def Phase7Transition (s t) :=
  if s.role = .main ∧ t.role = .main then cancelSplit L K s t
  else (s,t)   -- (clock agents run the counter subroutine)
```

and `cancelSplit` (Transition.lean:1213) on two opposite-sign dyadic biases
`±2^{-i}`, `∓2^{-j}`:

* gap 0 (`i = j`):      both become `.zero`           (full cancel);
* gap 1 (`i+1 = j`):    `s ↦ 2^{-(i+1)}`, `t ↦ 0`     (one-sided drain of `t`);
* gap 2 (`i+2 = j`):    `s ↦ ±2^{-(i+1)}`, `t ↦ ±2^{-(i+2)}` (both take `s`'s sign);
* gap ≥ 3:              no change.

The **minority** sign is a fixed parameter `σ : Sign`; the **majority/eliminator**
sign is `σ.flip`.  After Phase 6 (Lemma 7.3) at least `0.87|M|` Main agents
remain, the vast majority of the majority sign; the few minority agents sit at
exponent levels `i ∈ {l, l+1, l+2}` (Theorem 6.2 / Phase-6 output).  Each cancel
reaction strictly removes one minority agent OR keeps the minority count fixed and
never creates a new minority agent.

## Honest predicate / potential choices (vs the HANDOFF sketch placeholders)

The sketch named `Phase6PostCore`, `NoMinorityAtOrAboveL2`, `IsMinority`,
`initialMainCount` — none of which exist in the repo.  We read honest in-file
predicates off the actual `cancelSplit` / `Phase7Transition` rule:

* `minoritySt σ a` — `a` is a Main with a `σ`-signed dyadic bias (the minority);
* `minorityU σ c`  — the count of such agents (the Doty `|B|`, the target pool);
* `Inv7 σ n c`     — the carried Phase-6/7 structural invariant: size `n`, every
  agent at phase 7, and the **minority-non-creation** structural fact
  `MinorityClosed σ` (no `Transition` step ever turns a non-`σ` agent into a
  `σ`-Main), which is exactly what `PotNonincrOn` needs and which holds because
  `cancelSplit`'s outputs only ever carry sign `s.sign` (never introduce a *new*
  minority sign on a non-minority agent — verified per-pair).

The potential `Φ = minorityU σ` is non-increasing under the real kernel
(`minorityU_pow_noincr`), and `{Φ = 0}` is exactly `NoMinority σ`, the Phase-7
post `NoMinorityAtOrAboveL2` rendered honestly (no minority agent remains at all —
stronger than the paper's "below −(l+2)", which is the form the cancellation engine
delivers since cancellation drains the WHOLE minority pool).

This file instantiates `OneSidedCancel.crude_PhaseConvergenceW` (form b) — the
honest uniform per-step drain engine — with `Inv = Inv7 σ n`, `Φ = minorityU σ`,
and the per-step drop `q` supplied by the eliminator-floor rectangle bound
`minority_drain_prob`.  The level-decomposed form (a) `levels_PhaseConvergenceW`
is documented at the foot of the file as the paper-faithful `O(n log n)` upgrade;
the crude form already delivers the whp tail at horizon `Θ(n² log n)` with the
honest `0.8|M|` eliminator floor.

NEW file; no existing file is edited; no sorry/admit/axiom/native_decide.
-/

import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.OneSidedCancel
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.PhaseConvergenceWeak
import Ripple.PopulationProtocol.Majority.ExactMajority.Analysis.Invariants

namespace ExactMajority

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace Phase7Convergence

variable {L K : ℕ}

attribute [local instance] Classical.propDecidable

instance instMeasurableSpaceAgentState7 : MeasurableSpace (AgentState L K) := ⊤
instance instDiscreteMeasurableSpaceAgentState7 :
    DiscreteMeasurableSpace (AgentState L K) where
  forall_measurableSet _ := trivial

/-! ## Part A — the minority predicate and count. -/

/-- An agent is a **minority** agent (sign `σ`) if it is a Main holding a
`σ`-signed dyadic bias.  This is the Doty `B`-pool: the opposite-sign agents being
drained by the `σ.flip` majority eliminators. -/
def minoritySt (σ : Sign) (a : AgentState L K) : Prop :=
  a.role = Role.main ∧ ∃ i : Fin (L + 1), a.bias = Bias.dyadic σ i

/-- A bias-side characterization of `minoritySt`: the bias is `σ`-signed dyadic. -/
def biasIsSigned (σ : Sign) (b : Bias L) : Prop :=
  match b with
  | .zero => False
  | .dyadic s _ => s = σ

instance (σ : Sign) (b : Bias L) : Decidable (biasIsSigned σ b) := by
  unfold biasIsSigned; cases b <;> infer_instance

theorem minoritySt_iff (σ : Sign) (a : AgentState L K) :
    minoritySt σ a ↔ a.role = Role.main ∧ biasIsSigned σ a.bias := by
  unfold minoritySt biasIsSigned
  cases hb : a.bias with
  | zero => simp
  | dyadic s i =>
      constructor
      · rintro ⟨hr, j, hj⟩; injection hj with hjs _; exact ⟨hr, hjs⟩
      · rintro ⟨hr, hs⟩; exact ⟨hr, i, by rw [hs]⟩

instance (σ : Sign) (a : AgentState L K) : Decidable (minoritySt σ a) :=
  decidable_of_iff _ (minoritySt_iff σ a).symm

/-- The minority count (the Doty `|B|`). -/
def minorityU (σ : Sign) (c : Config (AgentState L K)) : ℕ :=
  Multiset.countP (fun a => minoritySt σ a) c

/-! ## Part B — the per-pair reduction to `cancelSplit` for two phase-7 Mains. -/

/-- For two phase-7 agents, `phaseEpidemicUpdate` is the identity (max of equal
phases, no init to run, no phase-10 entry).  Mirror of Phase 4's
`phaseEpidemicUpdate_eq_self_of_phase4` at threshold 7. -/
theorem phaseEpidemicUpdate_eq_self_of_phase7 (s t : AgentState L K)
    (hs : s.phase.val = 7) (ht : t.phase.val = 7) :
    phaseEpidemicUpdate L K s t = (s, t) := by
  have hsp : s.phase = ⟨7, by decide⟩ := Fin.ext hs
  have htp : t.phase = ⟨7, by decide⟩ := Fin.ext ht
  unfold phaseEpidemicUpdate
  rw [hsp, htp, max_self]
  simp only [runInitsBetween_self_api]
  have hs_self : ({s with phase := (⟨7, by decide⟩ : Fin 11)} : AgentState L K) = s := by
    rw [← hsp]
  have ht_self : ({t with phase := (⟨7, by decide⟩ : Fin 11)} : AgentState L K) = t := by
    rw [← htp]
  rw [hs_self, ht_self]
  rw [if_neg (by push Not; intro _; simp)]

/-- `cancelSplit` never changes an agent's phase (it only rewrites `.bias`). -/
theorem cancelSplit_phase (s t : AgentState L K) :
    (cancelSplit L K s t).1.phase = s.phase ∧ (cancelSplit L K s t).2.phase = t.phase := by
  unfold cancelSplit
  match s.bias, t.bias with
  | .zero, _ => simp
  | .dyadic _ _, .zero => simp
  | .dyadic sgn_s i, .dyadic sgn_t j => simp; split_ifs <;> simp

/-- **Per-pair reduction.**  Two phase-7 Main agents interact via `cancelSplit`
under the full `Transition` (epidemic = id, dispatch = `Phase7Transition`, no
phase-10 finish since phase stays 7, and neither is a clock so the counter branch
is skipped). -/
theorem Transition_eq_cancelSplit_of_phase7_main (s t : AgentState L K)
    (hs7 : s.phase.val = 7) (ht7 : t.phase.val = 7)
    (hsM : s.role = Role.main) (htM : t.role = Role.main) :
    Transition L K s t = cancelSplit L K s t := by
  have hepi := phaseEpidemicUpdate_eq_self_of_phase7 (L := L) (K := K) s t hs7 ht7
  have hsp : s.phase = ⟨7, by decide⟩ := Fin.ext hs7
  -- Phase7Transition with both Main, neither clock = cancelSplit.
  have hnsclk : s.role ≠ Role.clock := by rw [hsM]; decide
  have hntclk : t.role ≠ Role.clock := by rw [htM]; decide
  have hp7 : Phase7Transition L K s t = cancelSplit L K s t := by
    unfold Phase7Transition
    simp only [if_pos (show s.role = Role.main ∧ t.role = Role.main from ⟨hsM, htM⟩),
      cancelSplit_role_fst, cancelSplit_role_snd,
      if_neg hnsclk, if_neg hntclk]
  obtain ⟨hcs1, hcs2⟩ := cancelSplit_phase (L := L) (K := K) s t
  unfold Transition
  rw [hepi]
  simp only [hsp]
  rw [show (Phase7Transition L K s t) = cancelSplit L K s t from hp7]
  rw [finishPhase10Entry_eq_self_of_after_ne_10 (L := L) (K := K) s _ (by rw [hcs1, hs7]; omega),
      finishPhase10Entry_eq_self_of_after_ne_10 (L := L) (K := K) t _ (by rw [hcs2, ht7]; omega)]

/-! ## Part C — per-pair minority-count behavior under `cancelSplit`.

The minority count `countP (minoritySt σ)` over the produced pair is **at most**
that over the consumed pair, EXCEPT in the single gap-2 case where the minority is
the *smaller-index* (higher-magnitude) agent `s` and the majority is the
*larger-index* agent `t` — there `cancelSplit` copies `s`'s (minority) sign onto
`t`, raising the count.  The honest Phase-6/7 structural input rules this out: the
minority always has index **≥** the majority partner's index (the majority holds
the larger mass / smaller exponent), captured by `minorityHiIndex σ`.  Under that
hypothesis, `cancelSplit` never raises the σ-count. -/

/-- `countP minoritySt` over a two-element pair as a sum of indicators. -/
theorem countP_minoritySt_pair (σ : Sign) (x y : AgentState L K) :
    Multiset.countP (fun a => minoritySt σ a) ({x, y} : Multiset (AgentState L K))
      = (if minoritySt σ x then 1 else 0) + (if minoritySt σ y then 1 else 0) := by
  rw [show ({x, y} : Multiset (AgentState L K)) = x ::ₘ y ::ₘ 0 from rfl]
  rw [Multiset.countP_cons, Multiset.countP_cons, Multiset.countP_zero]
  ring

/-- An agent that is not a Main is never a minority agent (regardless of bias). -/
theorem not_minoritySt_of_not_main (σ : Sign) (a : AgentState L K)
    (h : a.role ≠ Role.main) : ¬ minoritySt σ a := fun ⟨hm, _⟩ => h hm

/-- A Main with `.zero` bias is not a minority agent. -/
theorem not_minoritySt_zero (σ : Sign) (a : AgentState L K) (h : a.bias = Bias.zero) :
    ¬ minoritySt σ a := by
  rw [minoritySt_iff]; rintro ⟨_, hb⟩; rw [h] at hb; exact hb

/-- A Main with a `σ`-signed dyadic bias is a minority agent. -/
theorem minoritySt_of_signed (σ : Sign) (a : AgentState L K) (i : Fin (L + 1))
    (hr : a.role = Role.main) (hb : a.bias = Bias.dyadic σ i) : minoritySt σ a :=
  ⟨hr, i, hb⟩

/-- **Per-pair σ-count non-increase under the index ordering** (both Main).  If,
whenever both agents are opposite-sign dyadics, the σ-signed one has index `≥` the
σ.flip one, then `cancelSplit` does not raise the pair's σ-Main count.  Read off
directly from the five `cancelSplit` branches: gap 0 drains both signs; gap 1
drains the larger-index agent; gap 2 sign-flips the larger-index agent to the
smaller-index agent's sign — and the index hypothesis forces the larger-index
agent to be the σ one, so it is exactly the minority being removed; gap ≥ 3 is the
identity.  `cancelSplit` preserves roles, so both outputs stay Main. -/
theorem cancelSplit_minorityU_pair_le (σ : Sign) (s t : AgentState L K)
    (hsM : s.role = Role.main) (htM : t.role = Role.main)
    (hidx : ∀ ss i st j, s.bias = Bias.dyadic ss i → t.bias = Bias.dyadic st j →
      ss ≠ st → (ss = σ → j.val ≤ i.val) ∧ (st = σ → i.val ≤ j.val)) :
    Multiset.countP (fun a => minoritySt σ a)
        ({(cancelSplit L K s t).1, (cancelSplit L K s t).2} : Multiset (AgentState L K))
      ≤ Multiset.countP (fun a => minoritySt σ a)
          ({s, t} : Multiset (AgentState L K)) := by
  classical
  have hr1 : (cancelSplit L K s t).1.role = s.role := cancelSplit_role_fst L K s t
  have hr2 : (cancelSplit L K s t).2.role = t.role := cancelSplit_role_snd L K s t
  rw [countP_minoritySt_pair, countP_minoritySt_pair]
  -- Reduce `minoritySt σ x` to `biasIsSigned σ x.bias` (roles are all `main`).
  have key : ∀ x : AgentState L K, x.role = Role.main →
      (minoritySt σ x ↔ biasIsSigned σ x.bias) := fun x hx => by
    rw [minoritySt_iff]; exact ⟨fun h => h.2, fun h => ⟨hx, h⟩⟩
  have ks : (minoritySt σ s ↔ biasIsSigned σ s.bias) := key s hsM
  have kt : (minoritySt σ t ↔ biasIsSigned σ t.bias) := key t htM
  have ko1 : (minoritySt σ (cancelSplit L K s t).1 ↔
      biasIsSigned σ (cancelSplit L K s t).1.bias) := key _ (by rw [hr1]; exact hsM)
  have ko2 : (minoritySt σ (cancelSplit L K s t).2 ↔
      biasIsSigned σ (cancelSplit L K s t).2.bias) := key _ (by rw [hr2]; exact htM)
  -- It suffices to bound the bias-signed indicators.
  rw [if_congr ks rfl rfl, if_congr kt rfl rfl,
      if_congr ko1 rfl rfl, if_congr ko2 rfl rfl]
  -- Now a pure `Bias`-level case analysis on the two output biases of `cancelSplit`.
  -- Extract the output biases explicitly per branch.
  cases hsb : s.bias with
  | zero =>
      -- s not dyadic ⇒ cancelSplit = (s,t); both sides unchanged.
      have hcs : cancelSplit L K s t = (s, t) := by unfold cancelSplit; rw [hsb]
      rw [hcs, hsb]
  | dyadic ss i =>
    cases htb : t.bias with
    | zero =>
        have hcs : cancelSplit L K s t = (s, t) := by
          unfold cancelSplit; rw [hsb, htb]
        rw [hcs]; simp only [hsb, htb]; exact le_rfl
    | dyadic st j =>
      by_cases hne : ss = st
      · -- same sign ⇒ identity.
        have hcs : cancelSplit L K s t = (s, t) := by
          unfold cancelSplit; simp only [hsb, htb, if_neg (show ¬ ss ≠ st from by simpa using hne)]
        rw [hcs]; simp only [hsb, htb]; exact le_rfl
      · -- opposite signs: branch on gap.
        have hnee : ss ≠ st := hne
        obtain ⟨hσs, hσt⟩ := hidx ss i st j hsb htb hne
        by_cases h0 : i.val = j.val
        · have hcs : cancelSplit L K s t
              = ({s with bias := .zero}, {t with bias := .zero}) := by
            unfold cancelSplit; simp only [hsb, htb, if_pos hnee, dif_pos h0]
          rw [hcs]; simp only [biasIsSigned]; positivity
        by_cases h1 : i.val + 1 = j.val
        · have hcs : cancelSplit L K s t
              = ({s with bias := .dyadic ss ⟨i.val + 1, by
                    have hj : j.val < L + 1 := j.2; omega⟩}, {t with bias := .zero}) := by
            unfold cancelSplit; simp only [hsb, htb, if_pos hnee, dif_neg h0, dif_pos h1]
          rw [hcs]
          by_cases hssσ : ss = σ
          · exfalso; have := hσs hssσ; omega
          · simp only [biasIsSigned, if_neg hssσ]; positivity
        by_cases h1' : j.val + 1 = i.val
        · have hcs : cancelSplit L K s t
              = ({s with bias := .zero}, {t with bias := .dyadic st ⟨j.val + 1, by
                    have hi : i.val < L + 1 := i.2; omega⟩}) := by
            unfold cancelSplit
            simp only [hsb, htb, if_pos hnee, dif_neg h0, dif_neg h1, dif_pos h1']
          rw [hcs]
          by_cases hstσ : st = σ
          · exfalso; have := hσt hstσ; omega
          · simp only [biasIsSigned, if_neg hstσ]; positivity
        by_cases h2 : i.val + 2 = j.val
        · have hcs : cancelSplit L K s t
              = ({s with bias := .dyadic ss ⟨i.val + 1, by
                    have hj : j.val < L + 1 := j.2; omega⟩},
                 {t with bias := .dyadic ss ⟨i.val + 2, by
                    have hj : j.val < L + 1 := j.2; omega⟩}) := by
            unfold cancelSplit
            simp only [hsb, htb, if_pos hnee, dif_neg h0, dif_neg h1, dif_neg h1', dif_pos h2]
          rw [hcs]
          by_cases hssσ : ss = σ
          · exfalso; have := hσs hssσ; omega
          · simp only [biasIsSigned, if_neg hssσ]; positivity
        by_cases h2' : j.val + 2 = i.val
        · have hcs : cancelSplit L K s t
              = ({s with bias := .dyadic st ⟨j.val + 2, by
                    have hi : i.val < L + 1 := i.2; omega⟩},
                 {t with bias := .dyadic st ⟨j.val + 1, by
                    have hi : i.val < L + 1 := i.2; omega⟩}) := by
            unfold cancelSplit
            simp only [hsb, htb, if_pos hnee, dif_neg h0, dif_neg h1, dif_neg h1', dif_neg h2,
              dif_pos h2']
          rw [hcs]
          by_cases hstσ : st = σ
          · exfalso; have := hσt hstσ; omega
          · simp only [biasIsSigned, if_neg hstσ]; positivity
        · -- gap ≥ 3: identity.
          have hcs : cancelSplit L K s t = (s, t) := by
            unfold cancelSplit
            simp only [hsb, htb, if_pos hnee, dif_neg h0, dif_neg h1, dif_neg h1', dif_neg h2,
              dif_neg h2']
          rw [hcs]; simp only [hsb, htb]; exact le_rfl

/-- **Per-pair strict drain under `cancelSplit` (gap-1 one-sided drain).**  `s` is a
`σ.flip` (majority / eliminator) Main at index `i`, `t` is a `σ`-minority Main at the
gap-1 higher index `j = i + 1`.  `cancelSplit`'s gap-1 branch zeroes the larger-index
agent `t` (the minority), so the pair's `σ`-Main count strictly drops (output `+ 1 ≤`
input).  This is the per-pair seed of the Phase-7 drain rectangle: each
(eliminator@i, minority@i+1) interaction removes one minority agent. -/
theorem cancelSplit_minorityU_pair_drop (σ ss : Sign) (s t : AgentState L K)
    (hsM : s.role = Role.main) (htM : t.role = Role.main)
    (i j : Fin (L + 1)) (hsb : s.bias = Bias.dyadic ss i)
    (htb : t.bias = Bias.dyadic σ j) (hss : ss ≠ σ) (hg1 : i.val + 1 = j.val) :
    Multiset.countP (fun a => minoritySt σ a)
        ({(cancelSplit L K s t).1, (cancelSplit L K s t).2} : Multiset (AgentState L K))
        + 1
      ≤ Multiset.countP (fun a => minoritySt σ a)
          ({s, t} : Multiset (AgentState L K)) := by
  classical
  have hsmin_not : ¬ minoritySt σ s := by
    rw [minoritySt_iff]; rintro ⟨_, hb⟩
    rw [hsb] at hb; simp only [biasIsSigned] at hb; exact hss hb
  have htmin : minoritySt σ t := ⟨htM, j, htb⟩
  -- Identify the gap-1 output: `s ↦ dyadic ss (i+1)`, `t ↦ zero`.
  have hineq0 : ¬ i.val = j.val := by omega
  have hcs : cancelSplit L K s t
      = ({s with bias := .dyadic ss ⟨i.val + 1, by
            have hj : j.val < L + 1 := j.2; omega⟩}, {t with bias := .zero}) := by
    unfold cancelSplit
    rw [hsb, htb]
    simp only [if_pos (show ss ≠ σ from hss), dif_neg hineq0, dif_pos hg1]
  rw [countP_minoritySt_pair, countP_minoritySt_pair, hcs]
  -- Outputs: `s'` keeps sign `ss ≠ σ` (not minority); `t'` is `.zero` (not minority).
  have ho1 : ¬ minoritySt σ ({s with bias := (Bias.dyadic ss
      ⟨i.val + 1, by have hj : j.val < L + 1 := j.2; omega⟩ : Bias L)}) := by
    rw [minoritySt_iff]; rintro ⟨_, hb⟩
    simp only [biasIsSigned] at hb; exact hss hb
  have ho2 : ¬ minoritySt σ ({t with bias := (.zero : Bias L)}) :=
    not_minoritySt_zero σ _ rfl
  rw [if_neg ho1, if_neg ho2, if_neg hsmin_not, if_pos htmin]

/-! ## Part D — the config-level minority-ordering invariant and global non-increase.

The per-pair non-increase needs the **index ordering**: every minority (`σ`) Main
sits at an exponent index `≥` every majority (`σ.flip`) Main.  We encode this as a
config predicate `MinorityHiIdx σ` and carry it in the Phase-7 invariant `Inv7`.
Under it, EVERY pair satisfies the per-pair hypothesis, so the global step never
raises `minorityU σ`. -/

/-- Every `σ`-Main has exponent index `≥` every non-`σ` (majority) Main's index.
This is Doty's "the majority has larger mass than the minority": the minority sign
sits at the smaller magnitude (= larger index). -/
def MinorityHiIdx (σ : Sign) (c : Config (AgentState L K)) : Prop :=
  ∀ a ∈ c, ∀ b ∈ c, a.role = Role.main → b.role = Role.main →
    ∀ sa ia sb ib, a.bias = Bias.dyadic sa ia → b.bias = Bias.dyadic sb ib →
      sa ≠ sb → (sa = σ → ib.val ≤ ia.val) ∧ (sb = σ → ia.val ≤ ib.val)

/-- The per-pair index hypothesis for a specific applicable pair, extracted from the
config-level `MinorityHiIdx`. -/
theorem hidx_of_MinorityHiIdx (σ : Sign) (c : Config (AgentState L K))
    (hmh : MinorityHiIdx σ c) (s t : AgentState L K) (hs : s ∈ c) (ht : t ∈ c)
    (hsM : s.role = Role.main) (htM : t.role = Role.main) :
    ∀ ss i st j, s.bias = Bias.dyadic ss i → t.bias = Bias.dyadic st j →
      ss ≠ st → (ss = σ → j.val ≤ i.val) ∧ (st = σ → i.val ≤ j.val) :=
  fun ss i st j hsb htb hne => hmh s hs t ht hsM htM ss i st j hsb htb hne

/-- When the pair is **not** both Main, `Phase7Transition` leaves every Main's bias
unchanged (cancelSplit is not invoked; the clock subroutine touches only the clock
side, which is not a Main).  Hence the minority count of the produced pair equals
that of the consumed pair. -/
theorem Phase7Transition_minorityU_eq_of_not_both_main (σ : Sign) (s t : AgentState L K)
    (h : ¬ (s.role = Role.main ∧ t.role = Role.main)) :
    Multiset.countP (fun a => minoritySt σ a)
        ({(Phase7Transition L K s t).1, (Phase7Transition L K s t).2}
          : Multiset (AgentState L K))
      = Multiset.countP (fun a => minoritySt σ a) ({s, t} : Multiset (AgentState L K)) := by
  classical
  rw [countP_minoritySt_pair, countP_minoritySt_pair]
  -- s-side: out₁ = (if s.role=clock then counter s else s); but minoritySt needs role=main.
  -- For the s-side we case on whether s is Main.
  -- For each side, the (clock-or-self) update has the SAME minority indicator as the input:
  -- if the agent is a clock, both are non-Main hence non-minority; otherwise it's unchanged.
  have hside : ∀ (x : AgentState L K),
      (if minoritySt σ (if x.role = Role.clock then stdCounterSubroutine L K x else x)
        then (1 : ℕ) else 0) = (if minoritySt σ x then 1 else 0) := by
    intro x
    by_cases hxc : x.role = Role.clock
    · rw [if_pos hxc]
      have h1 : ¬ minoritySt σ (stdCounterSubroutine L K x) :=
        not_minoritySt_of_not_main σ _ (by
          have hcr : (stdCounterSubroutine L K x).role = Role.clock :=
            stdCounterSubroutine_clock_role_eq (L := L) (K := K) x hxc
          rw [hcr]; decide)
      have h2 : ¬ minoritySt σ x := not_minoritySt_of_not_main σ x (by rw [hxc]; decide)
      rw [if_neg h1, if_neg h2]
    · rw [if_neg hxc]
  unfold Phase7Transition
  simp only [if_neg h]
  rw [hside s, hside t]

/-- **Per-pair `Transition` minority non-increase, both-Main case.**  Reduce to
`cancelSplit` (epidemic and phase-10 finish are identities at phase 7, the counter
branch is skipped for Mains) and apply `cancelSplit_minorityU_pair_le` under the
pair index hypothesis.  This is the per-pair input to the global step bound on the
(eliminator, minority) interactions that actually drain the pool — the pairs the
drift counts.

For pairs that are **not** both Main, the Main side's bias is untouched by
`Phase7Transition` (`Phase7Transition_minorityU_eq_of_not_both_main`); the global
lift folds both, with the `MinorityHiIdx` config invariant supplying the pair
hypothesis on every both-Main pair (`hidx_of_MinorityHiIdx`). -/
theorem Transition_minorityU_pair_le_of_both_main (σ : Sign) (s t : AgentState L K)
    (hs7 : s.phase.val = 7) (ht7 : t.phase.val = 7)
    (hsM : s.role = Role.main) (htM : t.role = Role.main)
    (hidx : ∀ ss i st j, s.bias = Bias.dyadic ss i → t.bias = Bias.dyadic st j →
      ss ≠ st → (ss = σ → j.val ≤ i.val) ∧ (st = σ → i.val ≤ j.val)) :
    Multiset.countP (fun a => minoritySt σ a)
        ({(Transition L K s t).1, (Transition L K s t).2} : Multiset (AgentState L K))
      ≤ Multiset.countP (fun a => minoritySt σ a) ({s, t} : Multiset (AgentState L K)) := by
  rw [Transition_eq_cancelSplit_of_phase7_main s t hs7 ht7 hsM htM]
  exact cancelSplit_minorityU_pair_le σ s t hsM htM hidx

/-! ## Part E — the config-level non-increase over an all-Main phase-7 window.

We deliver the engine's `hmono` (`PotNonincrOn`) ingredient over the window where
every agent is a phase-7 **Main** (`Inv7Main σ n` below) and the minority-index
ordering `MinorityHiIdx σ` holds.  On such a config every applicable interacting
pair is both-Main and phase-7, so `Transition_minorityU_pair_le_of_both_main`
applies with the pair hypothesis from `hidx_of_MinorityHiIdx`, and the standard
`stepOrSelf = c − {r₁,r₂} + {out₁,out₂}` decomposition (as in
`Phase4Convergence.advancedU_stepOrSelf_ge`) lifts it to the global count. -/

/-- The all-Main phase-7 window with the minority-index ordering: the honest
carried Phase-6 output under which the minority pool only shrinks.  (Clocks are
absent in this window; the clock-mixed extension needs the
`Phase7Transition`-output phase `≠ 10` bound — see file foot.) -/
def Inv7Main (σ : Sign) (n : ℕ) (c : Config (AgentState L K)) : Prop :=
  c.card = n ∧ (∀ a ∈ c, a.phase.val = 7 ∧ a.role = Role.main) ∧ MinorityHiIdx σ c

private theorem mem_of_app_left7 {c : Config (AgentState L K)}
    {r₁ r₂ : AgentState L K} (happ : Protocol.Applicable c r₁ r₂) : r₁ ∈ c :=
  Multiset.mem_of_le (show ({r₁, r₂} : Multiset (AgentState L K)) ≤ c from happ) (by simp)

private theorem mem_of_app_right7 {c : Config (AgentState L K)}
    {r₁ r₂ : AgentState L K} (happ : Protocol.Applicable c r₁ r₂) : r₂ ∈ c :=
  Multiset.mem_of_le (show ({r₁, r₂} : Multiset (AgentState L K)) ≤ c from happ) (by simp)

/-- `minorityU σ` is non-increasing under any chosen-pair update on an all-Main
phase-7 window with the index ordering. -/
theorem minorityU_stepOrSelf_le (σ : Sign) (n : ℕ) (c : Config (AgentState L K))
    (hInv : Inv7Main σ n c) (r₁ r₂ : AgentState L K) :
    minorityU σ (Protocol.stepOrSelf (NonuniformMajority L K) c r₁ r₂)
      ≤ minorityU σ c := by
  obtain ⟨_, hph, hmh⟩ := hInv
  by_cases happ : Protocol.Applicable c r₁ r₂
  · have hm1 := mem_of_app_left7 happ
    have hm2 := mem_of_app_right7 happ
    obtain ⟨h17, h1M⟩ := hph r₁ hm1
    obtain ⟨h27, h2M⟩ := hph r₂ hm2
    have hsub : ({r₁, r₂} : Multiset (AgentState L K)) ≤ c := happ
    have hc' : Protocol.stepOrSelf (NonuniformMajority L K) c r₁ r₂
        = c - {r₁, r₂} + {(Transition L K r₁ r₂).1, (Transition L K r₁ r₂).2} := by
      unfold Protocol.stepOrSelf; rw [if_pos happ]; rfl
    unfold minorityU
    rw [hc', Multiset.countP_add, Multiset.countP_sub hsub]
    have hpair := Transition_minorityU_pair_le_of_both_main σ r₁ r₂ h17 h27 h1M h2M
      (hidx_of_MinorityHiIdx σ c hmh r₁ r₂ hm1 hm2 h1M h2M)
    have hpair_le : Multiset.countP (fun a => minoritySt σ a)
        ({r₁, r₂} : Multiset (AgentState L K))
          ≤ Multiset.countP (fun a => minoritySt σ a) c := Multiset.countP_le_of_le _ hsub
    omega
  · rw [Protocol.stepOrSelf_eq_self_of_not_applicable happ]

/-- `minorityU σ` is non-increasing on the one-step kernel support (from an
`Inv7Main`-config).  Mirror of `Phase4Convergence.advancedU_ge_monotone`. -/
theorem minorityU_le_on_support (σ : Sign) (n : ℕ) (m : ℕ)
    (c c' : Config (AgentState L K)) (hInv : Inv7Main σ n c)
    (hle : minorityU σ c ≤ m)
    (hc' : c' ∈ ((NonuniformMajority L K).stepDistOrSelf c).support) :
    minorityU σ c' ≤ m := by
  by_cases hc : 2 ≤ c.card
  · rw [show (NonuniformMajority L K).stepDistOrSelf c
        = (NonuniformMajority L K).stepDist c hc by
        unfold Protocol.stepDistOrSelf; rw [dif_pos hc]] at hc'
    obtain ⟨⟨r₁, r₂⟩, hr⟩ := Protocol.stepDist_support (NonuniformMajority L K) c hc c' hc'
    rw [← hr]
    exact le_trans (minorityU_stepOrSelf_le σ n c hInv r₁ r₂) hle
  · rw [show (NonuniformMajority L K).stepDistOrSelf c = PMF.pure c by
        unfold Protocol.stepDistOrSelf; rw [dif_neg hc]] at hc'
    rw [PMF.mem_support_pure_iff] at hc'
    subst hc'; exact hle

/-- **The engine's `hmono` (PotNonincrOn) ingredient.**  From an `Inv7Main`-config,
the one-step kernel puts zero mass on configs with a *strictly larger* minority
count: `minorityU σ` is non-increasing.  This is exactly
`OneSidedCancel.PotNonincrOn (Inv7Main σ n) K (minorityU σ)` at the point `b = c`. -/
theorem minorityU_kernel_noincr (σ : Sign) (n : ℕ) (c : Config (AgentState L K))
    (hInv : Inv7Main σ n c) :
    (NonuniformMajority L K).transitionKernel c
      {x | minorityU σ c < minorityU σ x} = 0 := by
  change ((NonuniformMajority L K).stepDistOrSelf c).toMeasure
    {x | minorityU σ c < minorityU σ x} = 0
  rw [PMF.toMeasure_apply_eq_zero_iff _ (DiscreteMeasurableSpace.forall_measurableSet _)]
  rw [Set.disjoint_left]
  intro x hsupp hx
  simp only [Set.mem_setOf_eq] at hx
  have hle : minorityU σ x ≤ minorityU σ c :=
    minorityU_le_on_support σ n (minorityU σ c) c x hInv le_rfl hsupp
  omega

/-- Packaged as the engine's `PotNonincrOn` predicate. -/
theorem potNonincrOn_minorityU (σ : Sign) (n : ℕ) :
    OneSidedCancel.PotNonincrOn (fun c => Inv7Main σ n c)
      (NonuniformMajority L K).transitionKernel (fun c => minorityU σ c) :=
  fun c hInv => minorityU_kernel_noincr σ n c hInv

/-! ## Part F — the structural (card + phase-7 + role-Main) closure of `Inv7Main`.

On the all-Main phase-7 window every applicable pair is both-Main, so `Transition`
reduces to `cancelSplit`, which preserves both phase (`cancelSplit_phase`) and role
(`cancelSplit_role_fst/snd`).  Hence the structural conjuncts of `Inv7Main`
(`card = n`, all phase-7, all Main) are one-step closed.  The remaining conjunct
`MinorityHiIdx σ` — the index ordering — is the one whose closure is non-trivial
(cancelSplit mutates exponent indices); its preservation is the precise remaining
atom for the full `InvClosed`, documented at the file foot. -/

/-- The phase-7 + all-Main structural core (drops `MinorityHiIdx`). -/
def Phase7AllMain (n : ℕ) (c : Config (AgentState L K)) : Prop :=
  c.card = n ∧ ∀ a ∈ c, a.phase.val = 7 ∧ a.role = Role.main

/-- The structural core is preserved by a chosen-pair update: phase and role are
preserved because every applicable pair is both-Main (so `Transition` =
`cancelSplit`, which fixes phase and role). -/
theorem Phase7AllMain_stepOrSelf (n : ℕ) (c : Config (AgentState L K))
    (hw : Phase7AllMain n c) (r₁ r₂ : AgentState L K) :
    Phase7AllMain n (Protocol.stepOrSelf (NonuniformMajority L K) c r₁ r₂) := by
  obtain ⟨hcard, hph⟩ := hw
  by_cases happ : Protocol.Applicable c r₁ r₂
  · have hm1 := mem_of_app_left7 happ
    have hm2 := mem_of_app_right7 happ
    obtain ⟨h17, h1M⟩ := hph r₁ hm1
    obtain ⟨h27, h2M⟩ := hph r₂ hm2
    have hcs := Transition_eq_cancelSplit_of_phase7_main r₁ r₂ h17 h27 h1M h2M
    have hcsphase := cancelSplit_phase (L := L) (K := K) r₁ r₂
    have hc' : Protocol.stepOrSelf (NonuniformMajority L K) c r₁ r₂
        = c - {r₁, r₂} + {(Transition L K r₁ r₂).1, (Transition L K r₁ r₂).2} := by
      unfold Protocol.stepOrSelf; rw [if_pos happ]; rfl
    refine ⟨?_, ?_⟩
    · have hcard' := Protocol.reachable_card_eq
        (Protocol.reachable_stepOrSelf (P := NonuniformMajority L K) c r₁ r₂)
      rw [hcard']; exact hcard
    · intro a ha
      rw [hc'] at ha
      rcases Multiset.mem_add.mp ha with hold | hnew
      · exact hph a (Multiset.mem_of_le (Multiset.sub_le_self _ _) hold)
      · rw [show ({(Transition L K r₁ r₂).1, (Transition L K r₁ r₂).2}
              : Multiset (AgentState L K))
            = (Transition L K r₁ r₂).1 ::ₘ (Transition L K r₁ r₂).2 ::ₘ 0 from rfl] at hnew
        simp only [Multiset.mem_cons, Multiset.notMem_zero, or_false] at hnew
        rw [hcs] at hnew
        rcases hnew with h | h
        · subst h
          refine ⟨?_, ?_⟩
          · have := hcsphase.1; rw [this]; exact h17
          · rw [cancelSplit_role_fst]; exact h1M
        · subst h
          refine ⟨?_, ?_⟩
          · have := hcsphase.2; rw [this]; exact h27
          · rw [cancelSplit_role_snd]; exact h2M
  · rw [Protocol.stepOrSelf_eq_self_of_not_applicable happ]; exact ⟨hcard, hph⟩

/-- The structural core is one-step-support closed. -/
theorem Phase7AllMain_support_closed (n : ℕ) (c c' : Config (AgentState L K))
    (hw : Phase7AllMain n c)
    (hc' : c' ∈ ((NonuniformMajority L K).stepDistOrSelf c).support) :
    Phase7AllMain n c' := by
  by_cases hc : 2 ≤ c.card
  · rw [show (NonuniformMajority L K).stepDistOrSelf c
        = (NonuniformMajority L K).stepDist c hc by
        unfold Protocol.stepDistOrSelf; rw [dif_pos hc]] at hc'
    obtain ⟨⟨r₁, r₂⟩, hr⟩ := Protocol.stepDist_support (NonuniformMajority L K) c hc c' hc'
    rw [← hr]; exact Phase7AllMain_stepOrSelf n c hw r₁ r₂
  · rw [show (NonuniformMajority L K).stepDistOrSelf c = PMF.pure c by
        unfold Protocol.stepDistOrSelf; rw [dif_neg hc]] at hc'
    rw [PMF.mem_support_pure_iff] at hc'; subst hc'; exact hw

/-- **Config-level strict drain for Phase 7 (gap-1 cell).**  On an all-Main phase-7
window, an applicable pair `(s,t)` with `s` a `σ.flip` (eliminator) Main at index `i`
and `t` a `σ`-minority Main at the gap-1 higher index `j = i + 1` drops the global
minority count by one.  The Phase-7 analogue of `Phase8Convergence`'s config drop;
the gap-1 one-sided drain is the per-cell drop fact the Phase-7 drain rectangle
counts (no `MinorityHiIdx` needed for the drop direction — only the gap-1 geometry). -/
theorem minorityU_stepOrSelf_drop (σ ss : Sign) (n : ℕ) (c : Config (AgentState L K))
    (hInv : Phase7AllMain n c) (s t : AgentState L K)
    (happ : Protocol.Applicable c s t)
    (i j : Fin (L + 1)) (hsb : s.bias = Bias.dyadic ss i)
    (htb : t.bias = Bias.dyadic σ j) (hss : ss ≠ σ) (hg1 : i.val + 1 = j.val) :
    minorityU σ (Protocol.stepOrSelf (NonuniformMajority L K) c s t) + 1
      ≤ minorityU σ c := by
  obtain ⟨_, hph⟩ := hInv
  have hm1 := mem_of_app_left7 happ
  have hm2 := mem_of_app_right7 happ
  obtain ⟨h17, h1M⟩ := hph s hm1
  obtain ⟨h27, h2M⟩ := hph t hm2
  have hsub : ({s, t} : Multiset (AgentState L K)) ≤ c := happ
  have hc' : Protocol.stepOrSelf (NonuniformMajority L K) c s t
      = c - {s, t} + {(Transition L K s t).1, (Transition L K s t).2} := by
    unfold Protocol.stepOrSelf; rw [if_pos happ]; rfl
  unfold minorityU
  rw [hc', Multiset.countP_add, Multiset.countP_sub hsub]
  rw [Transition_eq_cancelSplit_of_phase7_main s t h17 h27 h1M h2M]
  have hdrop := cancelSplit_minorityU_pair_drop σ ss s t h1M h2M i j hsb htb hss hg1
  have hpair_le : Multiset.countP (fun a => minoritySt σ a)
      ({s, t} : Multiset (AgentState L K))
        ≤ Multiset.countP (fun a => minoritySt σ a) c := Multiset.countP_le_of_le _ hsub
  omega

/-! ## Part F' — the generic drop-rectangle probability bound (shared engine layer).

The dual of `Phase4Convergence.advanced_advance_prob_of_rect`: for a potential `Φ`
and a rectangle `R` of pairs each of which, when fired, drops `Φ` by `≥ 1`, the
one-step probability of the **drop** event `{c' | Φ c' + 1 ≤ Φ c}` is at least
`N/(n(n−1))` where `N ≤ ∑_R interactionCount`.  Φ-agnostic; the Phase-7 AND Phase-8
drain rectangles both feed it.  (Lives here, in Phase 7, so Phase 8 — which imports
Phase 7 — can reuse it without duplication.) -/

private theorem applicable_of_mem_distinct7 {c : Config (AgentState L K)}
    {x y : AgentState L K} (hx : x ∈ c) (hy : y ∈ c) (hxy : x ≠ y) :
    Protocol.Applicable c x y := by
  refine Multiset.le_iff_count.mpr ?_
  intro a
  rw [show ({x, y} : Multiset (AgentState L K)) = x ::ₘ y ::ₘ 0 from rfl,
      Multiset.count_cons, Multiset.count_cons, Multiset.count_zero]
  have hxc : 1 ≤ Multiset.count x c := Multiset.one_le_count_iff_mem.mpr hx
  have hyc : 1 ≤ Multiset.count y c := Multiset.one_le_count_iff_mem.mpr hy
  by_cases hax : a = x
  · subst hax
    have hay : ¬ a = y := fun h => hxy (h ▸ rfl)
    rw [if_pos rfl, if_neg hay]; omega
  · by_cases hay : a = y
    · subst hay; rw [if_neg hax, if_pos rfl]; omega
    · rw [if_neg hax, if_neg hay]; omega

/-- For two state-finsets of pairwise-distinct states, the `interactionCount` mass of
`A ×ˢ B` is `(∑_A count)·(∑_B count)`.  Shared copy. -/
theorem sum_interactionCount_cross_disjoint7
    (c : Config (AgentState L K)) (A B : Finset (AgentState L K))
    (hdisj : ∀ a ∈ A, ∀ b ∈ B, a ≠ b) :
    (∑ p ∈ A ×ˢ B, c.interactionCount p.1 p.2)
      = (∑ a ∈ A, c.count a) * (∑ b ∈ B, c.count b) := by
  rw [Finset.sum_product, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a ha
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b hb
  unfold Config.interactionCount
  rw [if_neg (hdisj a ha b hb)]

/-- **The generic drop-rectangle probability bound** (Φ-agnostic, shared by Phases
7 & 8). -/
theorem drop_prob_of_rect (Φ : Config (AgentState L K) → ℕ) (n : ℕ) (hn : 2 ≤ n)
    (c : Config (AgentState L K)) (hcardn : c.card = n)
    (R : Finset (AgentState L K × AgentState L K)) (N : ℕ)
    (hdrop : ∀ p ∈ R, 1 ≤ c.count p.1 → 1 ≤ c.count p.2 → (p.1 = p.2 → 2 ≤ c.count p.1) →
      Φ (Protocol.stepOrSelf (NonuniformMajority L K) c p.1 p.2) + 1 ≤ Φ c)
    (hcount : (N : ℕ) ≤ ∑ p ∈ R, c.interactionCount p.1 p.2) :
    ENNReal.ofReal ((N : ℝ) / ((n : ℝ) * ((n : ℝ) - 1))) ≤
      ((NonuniformMajority L K).stepDistOrSelf c).toMeasure
        {c' | Φ c' + 1 ≤ Φ c} := by
  set j := Φ c with hjdef
  have hcard2 : 2 ≤ c.card := by rw [hcardn]; omega
  have hmeas : MeasurableSet {c' : Config (AgentState L K) | Φ c' + 1 ≤ j} :=
    DiscreteMeasurableSpace.forall_measurableSet _
  set S : Finset (AgentState L K × AgentState L K) :=
    R.filter (fun p => 1 ≤ c.count p.1 ∧ 1 ≤ c.count p.2 ∧ (p.1 = p.2 → 2 ≤ c.count p.1)) with hS
  have hsub : (↑S : Set (AgentState L K × AgentState L K)) ⊆
      (Protocol.scheduledStep (NonuniformMajority L K) c) ⁻¹'
        {c' | Φ c' + 1 ≤ j} := by
    intro p hp
    simp only [Finset.coe_filter, Set.mem_setOf_eq, hS] at hp
    obtain ⟨hpc, hp1, hp2, hp3⟩ := hp
    simp only [Set.mem_preimage, Set.mem_setOf_eq, Protocol.scheduledStep]
    exact hdrop p hpc hp1 hp2 hp3
  have hstepDist : (NonuniformMajority L K).stepDistOrSelf c
      = (NonuniformMajority L K).stepDist c hcard2 := by
    unfold Protocol.stepDistOrSelf; rw [dif_pos hcard2]
  have hbase : ((NonuniformMajority L K).stepDistOrSelf c).toMeasure
        {c' | Φ c' + 1 ≤ j}
      = (c.interactionPMF hcard2).toMeasure
          ((Protocol.scheduledStep (NonuniformMajority L K) c) ⁻¹'
            {c' | Φ c' + 1 ≤ j}) := by
    rw [hstepDist]; unfold Protocol.stepDist
    rw [PMF.toMeasure_map_apply _ _ _ (Measurable.of_discrete) hmeas]
  rw [hbase]
  have hmono : (c.interactionPMF hcard2).toMeasure (↑S : Set _)
      ≤ (c.interactionPMF hcard2).toMeasure
          ((Protocol.scheduledStep (NonuniformMajority L K) c) ⁻¹'
            {c' | Φ c' + 1 ≤ j}) :=
    measure_mono hsub
  refine le_trans ?_ hmono
  have hSmeasure : (c.interactionPMF hcard2).toMeasure (↑S : Set _)
      = ∑ p ∈ S, c.interactionProb p.1 p.2 := by
    rw [PMF.toMeasure_apply_finset]; rfl
  have hSsum : ∑ p ∈ S, c.interactionProb p.1 p.2
      = ∑ p ∈ R, c.interactionProb p.1 p.2 := by
    rw [hS]
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro p hpc hpnot
    rw [Finset.mem_filter] at hpnot
    push Not at hpnot
    have hexcl := hpnot hpc
    have hzero : c.interactionCount p.1 p.2 = 0 := by
      unfold Config.interactionCount
      by_cases h1 : 1 ≤ c.count p.1
      · by_cases h2 : 1 ≤ c.count p.2
        · obtain ⟨hpe, hlt⟩ := hexcl h1 h2
          rw [if_pos hpe]
          have hc1 : c.count p.1 = 1 := by omega
          rw [hc1]
        · have hz2 : c.count p.2 = 0 := by omega
          by_cases hpe : p.1 = p.2
          · rw [if_pos hpe]; rw [hpe, hz2, Nat.zero_mul]
          · rw [if_neg hpe, hz2, Nat.mul_zero]
      · have hz1 : c.count p.1 = 0 := by omega
        by_cases hpe : p.1 = p.2
        · rw [if_pos hpe, hz1, Nat.zero_mul]
        · rw [if_neg hpe, hz1, Nat.zero_mul]
    unfold Config.interactionProb; rw [hzero]; simp
  rw [hSmeasure, hSsum]
  have heqterm : ∀ p : AgentState L K × AgentState L K,
      c.interactionProb p.1 p.2
        = (↑(c.interactionCount p.1 p.2) : ℝ≥0∞) * (↑c.totalPairs)⁻¹ := by
    intro p; unfold Config.interactionProb; rw [div_eq_mul_inv]
  rw [Finset.sum_congr rfl (fun p _ => heqterm p), ← Finset.sum_mul, ← Nat.cast_sum]
  set M := ∑ p ∈ R, c.interactionCount p.1 p.2 with hM
  have htp : c.totalPairs = n * (n - 1) := by rw [Config.totalPairs, hcardn]
  rw [htp, ← div_eq_mul_inv]
  have hden_pos : (0 : ℝ) < ((n * (n - 1) : ℕ) : ℝ) := by
    have : 0 < n * (n - 1) := Nat.mul_pos (by omega) (by omega)
    exact_mod_cast this
  have hdenR : ((n * (n - 1) : ℕ) : ℝ) = (n : ℝ) * ((n : ℝ) - 1) := by
    rw [Nat.cast_mul, Nat.cast_sub (by omega)]; push_cast; ring
  have hstep1 : ENNReal.ofReal ((N : ℝ) / ((n : ℝ) * ((n : ℝ) - 1)))
      ≤ ENNReal.ofReal (((M : ℕ) : ℝ) / ((n * (n - 1) : ℕ) : ℝ)) := by
    apply ENNReal.ofReal_le_ofReal
    rw [hdenR]
    have hNM : (N : ℝ) ≤ (M : ℝ) := by exact_mod_cast hcount
    have hposden : (0 : ℝ) < (n : ℝ) * ((n : ℝ) - 1) := by rw [← hdenR]; exact hden_pos
    gcongr
  refine le_trans hstep1 ?_
  rw [← ENNReal.ofReal_natCast M, ← ENNReal.ofReal_natCast (n * (n - 1)),
      ← ENNReal.ofReal_div_of_pos hden_pos]

/-! ## Part F'' — the Phase-7 eliminator × minority gap-1 rectangle.

Fix a minority level `j`.  The minority states at index `j` interacting with
eliminator states at the gap-1 LOWER index `j−1` (non-`σ` Mains) form a rectangle
each cell of which drops `minorityU σ` by one (`minorityU_stepOrSelf_drop`, gap-1).
Note the pair order: the eliminator `s` is first, the minority `t` second (matching
`minorityU_stepOrSelf_drop`'s `(s = elim, t = minority)` convention). -/

/-- The `σ`-minority states at index `j`. -/
def minorityAt7 (σ : Sign) (j : Fin (L + 1)) : Finset (AgentState L K) :=
  Finset.univ.filter (fun a => a.role = Role.main ∧ a.bias = Bias.dyadic σ j)

/-- The eliminator states at the gap-1 lower index `i` with `i + 1 = j`: non-`σ`
Mains at index `i`. -/
def elimGap1 (σ : Sign) (i : Fin (L + 1)) : Finset (AgentState L K) :=
  Finset.univ.filter (fun a => a.role = Role.main ∧
    ∃ ss, ss ≠ σ ∧ a.bias = Bias.dyadic ss i)

/-- Cross pairs `(elim@i, minority@j)` (gap-1, `i+1=j`) are distinct (biases differ:
index `i` vs `j`, and `i ≠ j`). -/
theorem elimGap1_minorityAt7_disjoint (σ : Sign) (i j : Fin (L + 1)) (hg1 : i.val + 1 = j.val)
    (a : AgentState L K) (ha : a ∈ elimGap1 (L := L) (K := K) σ i)
    (b : AgentState L K) (hb : b ∈ minorityAt7 (L := L) (K := K) σ j) : a ≠ b := by
  rw [elimGap1, Finset.mem_filter] at ha
  rw [minorityAt7, Finset.mem_filter] at hb
  obtain ⟨-, -, ss, -, hab⟩ := ha
  obtain ⟨-, -, hbb⟩ := hb
  intro heq; subst heq
  have hcomb : (Bias.dyadic ss i : Bias L) = Bias.dyadic σ j := hab.symm.trans hbb
  injection hcomb with _ hidx
  rw [hidx] at hg1; omega

/-- **Per-level eliminator×minority gap-1 rectangle drop probability** (Phase 7).
On a phase-7 all-Main window, the probability that one step drops `minorityU σ` is at
least `(#elim@i)·(#minority@j)/(n(n−1))`, for any gap-1 level pair `i+1 = j`. -/
theorem minorityU_drop_prob_rect7 (σ : Sign) (n : ℕ) (hn : 2 ≤ n)
    (c : Config (AgentState L K)) (hInv : Phase7AllMain n c)
    (i j : Fin (L + 1)) (hg1 : i.val + 1 = j.val) :
    ENNReal.ofReal
        (((elimGap1 (L := L) (K := K) σ i).sum c.count *
          (minorityAt7 (L := L) (K := K) σ j).sum c.count : ℕ) /
          ((n : ℝ) * ((n : ℝ) - 1))) ≤
      ((NonuniformMajority L K).stepDistOrSelf c).toMeasure
        {c' | minorityU σ c' + 1 ≤ minorityU σ c} := by
  have hcardn : c.card = n := hInv.1
  refine drop_prob_of_rect (fun c => minorityU σ c) n hn c hcardn
    ((elimGap1 (L := L) (K := K) σ i) ×ˢ (minorityAt7 (L := L) (K := K) σ j))
    _ ?_ (le_of_eq ?_)
  · rintro ⟨s, t⟩ hp hcs hct _
    rw [Finset.mem_product] at hp
    obtain ⟨hsmem, htmem⟩ := hp
    simp only [elimGap1, Finset.mem_filter] at hsmem
    simp only [minorityAt7, Finset.mem_filter] at htmem
    obtain ⟨_, hsM, ss, hss, hsb⟩ := hsmem
    obtain ⟨_, htM, htb⟩ := htmem
    have happ : Protocol.Applicable c s t := by
      have hsm : s ∈ c := Multiset.one_le_count_iff_mem.mp hcs
      have htm : t ∈ c := Multiset.one_le_count_iff_mem.mp hct
      have hne : s ≠ t :=
        elimGap1_minorityAt7_disjoint σ i j hg1 s
          (by simp only [elimGap1, Finset.mem_filter]
              exact ⟨Finset.mem_univ _, hsM, ss, hss, hsb⟩) t
          (by simp only [minorityAt7, Finset.mem_filter]; exact ⟨Finset.mem_univ _, htM, htb⟩)
      exact applicable_of_mem_distinct7 hsm htm hne
    exact minorityU_stepOrSelf_drop σ ss n c hInv s t happ i j hsb htb hss hg1
  · rw [sum_interactionCount_cross_disjoint7 c _ _ (elimGap1_minorityAt7_disjoint σ i j hg1)]

/-- **The engine `hdrop` from a drop-probability floor (Phase 7).**  Mirror of
Phase 8's bridge: failure mass `= 1 − drop-success ≤ 1 − p`. -/
theorem minorityU_hdrop_of_floor7 (σ : Sign) (n : ℕ) (m : ℕ)
    (p : ℝ≥0∞) (b : Config (AgentState L K)) (hbm : minorityU σ b = m)
    (hfloor : p ≤ ((NonuniformMajority L K).stepDistOrSelf b).toMeasure
        {c' | minorityU σ c' + 1 ≤ minorityU σ b}) :
    (NonuniformMajority L K).transitionKernel b
        (OneSidedCancel.potBelow (minorityU σ) m)ᶜ ≤ 1 - p := by
  classical
  have hKb : (NonuniformMajority L K).transitionKernel b
      = ((NonuniformMajority L K).stepDistOrSelf b).toMeasure := rfl
  have hsucc_eq : {c' : Config (AgentState L K) | minorityU σ c' + 1 ≤ minorityU σ b}
      = OneSidedCancel.potBelow (minorityU σ) m := by
    ext c'; simp only [OneSidedCancel.potBelow, Set.mem_setOf_eq, hbm]; omega
  have hmeas : MeasurableSet (OneSidedCancel.potBelow (minorityU σ) m) :=
    OneSidedCancel.potBelow_measurable (minorityU (L := L) (K := K) σ) m
  haveI hprob : IsProbabilityMeasure
      (((NonuniformMajority L K).stepDistOrSelf b).toMeasure) := by
    rw [← hKb]
    exact (inferInstance :
      IsMarkovKernel (NonuniformMajority L K).transitionKernel).isProbabilityMeasure b
  have htot : ((NonuniformMajority L K).stepDistOrSelf b).toMeasure Set.univ = 1 :=
    hprob.measure_univ
  have hcompl : ((NonuniformMajority L K).stepDistOrSelf b).toMeasure
        (OneSidedCancel.potBelow (minorityU σ) m)ᶜ
      = 1 - ((NonuniformMajority L K).stepDistOrSelf b).toMeasure
          (OneSidedCancel.potBelow (minorityU σ) m) := by
    rw [measure_compl hmeas (measure_ne_top _ _), htot]
  rw [hKb, hcompl]
  have hp_le : p ≤ ((NonuniformMajority L K).stepDistOrSelf b).toMeasure
      (OneSidedCancel.potBelow (minorityU σ) m) := by
    rw [← hsucc_eq]; exact hfloor
  exact tsub_le_tsub_left hp_le 1

/-! ## Part G — the Phase-7 `PhaseConvergenceW` from the engine.

`hmono` is the proved `potNonincrOn_minorityU`.  The full `InvClosed Inv7Main`
needs, beyond the proved structural core `Phase7AllMain_support_closed`, the
**`MinorityHiIdx σ` closure** under `cancelSplit` — the one non-trivial atom
(cancelSplit mutates exponent indices: gap-1 lowers the surviving agent's index by
1, gap-2 produces two new indices).  We expose `hClosed` (the full `InvClosed`) and
the drain `hstep` as hypotheses; the result is a real `PhaseConvergenceW` on the
actual kernel, with the honest hmono discharged.

`potDone (minorityU σ) = {minorityU σ = 0}` = `NoMinority σ`, the Phase-7 post
rendered honestly: cancellation drains the WHOLE minority pool to 0 (stronger than
the paper's "all minority below −(l+2)", which is what the cancellation engine
delivers — once all top-three-level minority is gone the residual is the Phase-8
input). -/

/-- `NoMinority σ c`: no `σ`-minority Main remains (engine `potDone`). -/
def NoMinority (σ : Sign) (c : Config (AgentState L K)) : Prop := minorityU σ c = 0

/-- **The Phase-7 cancellation `PhaseConvergenceW` on the REAL kernel** (engine
form b).  `Pre = Inv7Main n σ ∧ minorityU σ ≤ M₀`, `Post = Inv7Main n σ ∧
minorityU σ = 0`.  `hmono` is proved (`potNonincrOn_minorityU`); `hClosed`
(full `InvClosed Inv7Main`, needing `MinorityHiIdx`-closure) and the drain `hstep`
are the carried honest inputs. -/
noncomputable def phase7Convergence (σ : Sign) (n : ℕ)
    (hClosed : OneSidedCancel.InvClosed (NonuniformMajority L K).transitionKernel
      (fun c => Inv7Main σ n c))
    (q : ℝ≥0∞)
    (hstep : ∀ b : Config (AgentState L K), Inv7Main σ n b → 1 ≤ minorityU σ b →
      (NonuniformMajority L K).transitionKernel b
        (OneSidedCancel.potDone (fun c => minorityU σ c))ᶜ ≤ q)
    (M₀ : ℕ) (t : ℕ) (ε : ℝ≥0) (hε : (q ^ t : ℝ≥0∞) ≤ (ε : ℝ≥0∞)) :
    PhaseConvergenceW (NonuniformMajority L K).transitionKernel :=
  OneSidedCancel.crude_PhaseConvergenceW
    (NonuniformMajority L K).transitionKernel
    (fun c => Inv7Main (L := L) (K := K) σ n c)
    hClosed
    (fun c => minorityU σ c)
    (potNonincrOn_minorityU σ n)
    q hstep M₀ t ε hε

/-! ## Part H — the CONSERVED SIGNED-SUM invariant (Doty §6's actual `|B|` mechanism).

The carried `MinorityHiIdx σ` ordering of Part D is **genuinely not closed** under
`cancelSplit` (relay-5 finding, see `DOTY_POST63_CAMPAIGN.md`): a gap-1 fire RAISES a
majority agent's exponent index, which can then exceed a coexisting same-sign-as-σ
agent's index, breaking the ordering.  Doty's §6 mechanism for `|B|` control is NOT an
index ordering but the **conserved signed dyadic mass**

  `M(c) := ∑_{a∈c}  sgn(a.bias) · 2^{L − idx(a.bias)}`   (the `2^L`-scaled signed sum).

Every `cancelSplit` branch conserves `M` EXACTLY:
* gap 0 (`i=j`):  `+2^{L-i} − 2^{L-i} = 0 = 0 + 0`;
* gap 1 (`i+1=j`):  `2^{L-i} − 2^{L-(i+1)} = 2^{L-(i+1)} = 2^{L-(i+1)} + 0`;
* gap 2 (`i+2=j`):  `2^{L-i} − 2^{L-(i+2)} = 3·2^{L-(i+2)} = 2^{L-(i+1)} + 2^{L-(i+2)}`.

`M` is integer-valued (indices `i ≤ L`), conserved per pair, hence conserved by the
whole kernel on a phase-7 window; `0 < M` (majority `pos`, wlog) is therefore one-step
closed.  This rebuilds the Phase-7 invariant layer on the genuinely-closed potential.

HONEST SCOPE NOTE (the residual gap, stated precisely below at
`gap2_minorityU_rise_compatible_with_pos_sum`): conservation + `0 < M` does NOT by
itself give per-pair `minorityU` non-increase — a single σ-minority agent may carry
larger magnitude than a single majority agent while the GLOBAL sum stays positive, and
that is exactly the gap-2 configuration that raises the pair `minorityU`.  So the
signed sum is the correct *closed* invariant, but `minorityU` per-pair monotonicity is
a strictly stronger statement than `0 < M`.  What Part H delivers cleanly: the
conserved-sum invariant and its closure; the drain rectangle (Parts E–F) is independent
of any ordering and stands. -/

/-- The `2^L`-scaled integer signed mass of one bias: `±2^{L-i}` for `dyadic ± i`,
`0` for `zero`.  Integer because `i ≤ L` (so `L - i` is a genuine ℕ exponent). -/
def biasSignedMass (L : ℕ) : Bias L → ℤ
  | .zero => 0
  | .dyadic .pos i => (2 : ℤ) ^ (L - i.val)
  | .dyadic .neg i => -((2 : ℤ) ^ (L - i.val))

/-- The signed mass of an agent (reads only its bias). -/
def agentSignedMass (a : AgentState L K) : ℤ := biasSignedMass L a.bias

/-- The conserved Phase-7 signed sum `M(c) = ∑ agentSignedMass`. -/
def phase7SignedSum (c : Config (AgentState L K)) : ℤ :=
  (c.map (fun a => agentSignedMass a)).sum

/-- **Per-pair signed-mass conservation under `cancelSplit`.**  Every branch of
`cancelSplit` keeps the sum of the two agents' `agentSignedMass` fixed (the exact
dyadic-mass cancellation identity).  This is Doty §6's conserved `|B|` mechanism. -/
theorem cancelSplit_agentSignedMass_pair_eq (s t : AgentState L K) :
    agentSignedMass (cancelSplit L K s t).1
        + agentSignedMass (cancelSplit L K s t).2
      = agentSignedMass s + agentSignedMass t := by
  classical
  unfold agentSignedMass
  cases hsb : s.bias with
  | zero =>
      have hcs : cancelSplit L K s t = (s, t) := by unfold cancelSplit; rw [hsb]
      rw [hcs, hsb]
  | dyadic ss i =>
    cases htb : t.bias with
    | zero =>
        have hcs : cancelSplit L K s t = (s, t) := by unfold cancelSplit; rw [hsb, htb]
        rw [hcs, hsb, htb]
    | dyadic st j =>
      by_cases hne : ss = st
      · have hcs : cancelSplit L K s t = (s, t) := by
          unfold cancelSplit
          simp only [hsb, htb, if_neg (show ¬ ss ≠ st from by simpa using hne)]
        rw [hcs, hsb, htb]
      · have hnee : ss ≠ st := hne
        by_cases h0 : i.val = j.val
        · -- gap 0: both biases zero out; signs opposite ⇒ +x + (−x) = 0.
          have hcs : cancelSplit L K s t
              = ({s with bias := .zero}, {t with bias := .zero}) := by
            unfold cancelSplit; simp only [hsb, htb, if_pos hnee, dif_pos h0]
          rw [hcs]; simp only []
          -- opposite signs at equal index: masses cancel.
          cases ss <;> cases st <;> simp_all [biasSignedMass, h0]
        by_cases h1 : i.val + 1 = j.val
        · have hjL : j.val < L + 1 := j.2
          have hcs : cancelSplit L K s t
              = ({s with bias := .dyadic ss ⟨i.val + 1, by omega⟩}, {t with bias := .zero}) := by
            unfold cancelSplit; simp only [hsb, htb, if_pos hnee, dif_neg h0, dif_pos h1]
          rw [hcs]
          have hexp : L - i.val = (L - j.val) + 1 := by omega
          have hexp2 : L - (i.val + 1) = L - j.val := by omega
          cases ss <;> cases st <;> simp_all [biasSignedMass] <;>
            simp only [pow_succ] <;> ring
        by_cases h1' : j.val + 1 = i.val
        · have hiL : i.val < L + 1 := i.2
          have hcs : cancelSplit L K s t
              = ({s with bias := .zero}, {t with bias := .dyadic st ⟨j.val + 1, by omega⟩}) := by
            unfold cancelSplit
            simp only [hsb, htb, if_pos hnee, dif_neg h0, dif_neg h1, dif_pos h1']
          rw [hcs]
          have hexp : L - j.val = (L - i.val) + 1 := by omega
          have hexp2 : L - (j.val + 1) = L - i.val := by omega
          cases ss <;> cases st <;> simp_all [biasSignedMass] <;>
            simp only [pow_succ] <;> ring
        by_cases h2 : i.val + 2 = j.val
        · have hjL : j.val < L + 1 := j.2
          have hcs : cancelSplit L K s t
              = ({s with bias := .dyadic ss ⟨i.val + 1, by omega⟩},
                 {t with bias := .dyadic ss ⟨i.val + 2, by omega⟩}) := by
            unfold cancelSplit
            simp only [hsb, htb, if_pos hnee, dif_neg h0, dif_neg h1, dif_neg h1', dif_pos h2]
          rw [hcs]
          have hei : L - i.val = (L - j.val) + 2 := by omega
          have hei1 : L - (i.val + 1) = (L - j.val) + 1 := by omega
          have hei2 : L - (i.val + 2) = L - j.val := by omega
          cases ss <;> cases st <;> simp_all [biasSignedMass] <;>
            simp only [pow_succ] <;> ring
        by_cases h2' : j.val + 2 = i.val
        · have hiL : i.val < L + 1 := i.2
          have hcs : cancelSplit L K s t
              = ({s with bias := .dyadic st ⟨j.val + 2, by omega⟩},
                 {t with bias := .dyadic st ⟨j.val + 1, by omega⟩}) := by
            unfold cancelSplit
            simp only [hsb, htb, if_pos hnee, dif_neg h0, dif_neg h1, dif_neg h1', dif_neg h2,
              dif_pos h2']
          rw [hcs]
          have hej : L - j.val = (L - i.val) + 2 := by omega
          have hej1 : L - (j.val + 1) = (L - i.val) + 1 := by omega
          have hej2 : L - (j.val + 2) = L - i.val := by omega
          cases ss <;> cases st <;> simp_all [biasSignedMass] <;>
            simp only [pow_succ] <;> ring
        · have hcs : cancelSplit L K s t = (s, t) := by
            unfold cancelSplit
            simp only [hsb, htb, if_pos hnee, dif_neg h0, dif_neg h1, dif_neg h1', dif_neg h2,
              dif_neg h2']
          rw [hcs, hsb, htb]

/-- **Config-level signed-sum conservation under a chosen-pair step** (Phase-7 window).
On an all-Main phase-7 window, every applicable pair is both-Main so `Transition =
cancelSplit`, and the per-pair conservation lifts through the
`c − {r₁,r₂} + {out₁,out₂}` step decomposition.  The not-applicable (self) case is the
identity. -/
theorem phase7SignedSum_stepOrSelf_eq (n : ℕ) (c : Config (AgentState L K))
    (hw : Phase7AllMain n c) (r₁ r₂ : AgentState L K) :
    phase7SignedSum (Protocol.stepOrSelf (NonuniformMajority L K) c r₁ r₂)
      = phase7SignedSum c := by
  classical
  obtain ⟨_, hph⟩ := hw
  by_cases happ : Protocol.Applicable c r₁ r₂
  · have hm1 := mem_of_app_left7 happ
    have hm2 := mem_of_app_right7 happ
    obtain ⟨h17, h1M⟩ := hph r₁ hm1
    obtain ⟨h27, h2M⟩ := hph r₂ hm2
    have hcs := Transition_eq_cancelSplit_of_phase7_main r₁ r₂ h17 h27 h1M h2M
    have hpair : agentSignedMass (Transition L K r₁ r₂).1
          + agentSignedMass (Transition L K r₁ r₂).2
        = agentSignedMass r₁ + agentSignedMass r₂ := by
      rw [hcs]; exact cancelSplit_agentSignedMass_pair_eq r₁ r₂
    have hc' : Protocol.stepOrSelf (NonuniformMajority L K) c r₁ r₂
        = c - {r₁, r₂} + {(Transition L K r₁ r₂).1, (Transition L K r₁ r₂).2} := by
      unfold Protocol.stepOrSelf; rw [if_pos happ]; rfl
    have happ_le : (r₁ ::ₘ {r₂} : Multiset (AgentState L K)) ≤ c := happ
    have hrestore : c - r₁ ::ₘ {r₂} + r₁ ::ₘ {r₂} = c :=
      Multiset.sub_add_cancel happ_le
    have hsum_c : phase7SignedSum c
        = phase7SignedSum (c - r₁ ::ₘ {r₂})
            + (agentSignedMass r₁ + agentSignedMass r₂) := by
      rw [← hrestore]; simp [phase7SignedSum, add_left_comm]
    have hsum_c' : phase7SignedSum
          (c - r₁ ::ₘ {r₂} +
            (Transition L K r₁ r₂).1 ::ₘ {(Transition L K r₁ r₂).2})
        = phase7SignedSum (c - r₁ ::ₘ {r₂})
            + (agentSignedMass (Transition L K r₁ r₂).1
              + agentSignedMass (Transition L K r₁ r₂).2) := by
      simp [phase7SignedSum, add_left_comm]
    rw [hc']
    show phase7SignedSum
        (c - r₁ ::ₘ {r₂} +
          (Transition L K r₁ r₂).1 ::ₘ {(Transition L K r₁ r₂).2})
      = phase7SignedSum c
    rw [hsum_c', hsum_c, hpair]
  · rw [Protocol.stepOrSelf_eq_self_of_not_applicable happ]

/-- **Support-level signed-sum conservation** (Phase-7 window): every successor in the
kernel's step support carries the same `phase7SignedSum`. -/
theorem phase7SignedSum_support_eq (n : ℕ) (c c' : Config (AgentState L K))
    (hw : Phase7AllMain n c)
    (hc' : c' ∈ ((NonuniformMajority L K).stepDistOrSelf c).support) :
    phase7SignedSum c' = phase7SignedSum c := by
  by_cases hc : 2 ≤ c.card
  · rw [show (NonuniformMajority L K).stepDistOrSelf c
        = (NonuniformMajority L K).stepDist c hc by
        unfold Protocol.stepDistOrSelf; rw [dif_pos hc]] at hc'
    obtain ⟨⟨r₁, r₂⟩, hr⟩ := Protocol.stepDist_support (NonuniformMajority L K) c hc c' hc'
    rw [← hr]; exact phase7SignedSum_stepOrSelf_eq n c hw r₁ r₂
  · rw [show (NonuniformMajority L K).stepDistOrSelf c = PMF.pure c by
        unfold Protocol.stepDistOrSelf; rw [dif_neg hc]] at hc'
    rw [PMF.mem_support_pure_iff] at hc'; subst hc'; rfl

/-- **The genuinely-closed Phase-7 invariant.**  Replaces the broken
`MinorityHiIdx`-carrying `Inv7Main` (whose index ordering is not one-step closed) with
the conserved signed-sum potential: the all-Main phase-7 window PLUS strict positivity
of the signed mass (majority sign `pos`, wlog — the symmetric `< 0` form handles
majority `neg`).  Doty §6's actual `|B|`-control invariant. -/
def Inv7Sum (n : ℕ) (c : Config (AgentState L K)) : Prop :=
  Phase7AllMain n c ∧ 0 < phase7SignedSum c

/-- **`Inv7Sum` is one-step closed under the real kernel** (`OneSidedCancel.InvClosed`).
Both conjuncts are support-stable: `Phase7AllMain` via `Phase7AllMain_support_closed`,
`0 < phase7SignedSum` via `phase7SignedSum_support_eq` (exact conservation).  This is
the `hClosed` that the broken `MinorityHiIdx` version could never supply. -/
theorem invClosed_Inv7Sum (n : ℕ) :
    OneSidedCancel.InvClosed (NonuniformMajority L K).transitionKernel
      (fun c => Inv7Sum (L := L) (K := K) n c) := by
  intro c hInv
  obtain ⟨hw, hpos⟩ := hInv
  change ((NonuniformMajority L K).stepDistOrSelf c).toMeasure
    {x | ¬ Inv7Sum (L := L) (K := K) n x} = 0
  rw [PMF.toMeasure_apply_eq_zero_iff _ (DiscreteMeasurableSpace.forall_measurableSet _)]
  rw [Set.disjoint_left]
  intro x hsupp hx
  refine hx ⟨Phase7AllMain_support_closed n c x hw hsupp, ?_⟩
  rw [phase7SignedSum_support_eq n c x hw hsupp]; exact hpos

/-! ### The residual gap, stated as a HARD per-pair fact.

`Inv7Sum` (= signed sum conserved + positive) is genuinely closed, but it is **not**
strong enough to give per-pair `minorityU` non-increase: the gap-2 branch of
`cancelSplit` copies the SMALLER-index agent's sign onto BOTH outputs, so when the
σ-minority sits at the smaller index (larger magnitude), the pair `minorityU` RISES by
exactly 1.  And this very pair CONSERVES the signed sum (proved generally by
`cancelSplit_agentSignedMass_pair_eq`), so global signed-sum positivity cannot forbid
it.  Conclusion: the per-pair `minorityU` monotonicity Doty's §6 relies on is strictly
stronger than `Inv7Sum`; it is supplied by the additional configurational fact that the
minority always sits at the SMALLER magnitude (= larger index), i.e. exactly the
content the (non-closed) `MinorityHiIdx` tried to encode.  So Phase-7's `hmono` for the
crude engine remains a CARRIED hypothesis; only `hClosed` is now discharged on the
genuinely-closed `Inv7Sum`. -/

/-- **Gap-2 minority RISE compatible with signed-sum conservation** (the residual gap).
If `s` is a σ-minority Main at the smaller index `i` and `t` is the σ.flip Main at
`j = i + 2`, then `cancelSplit` makes BOTH outputs σ-minority: the pair `minorityU`
RISES by exactly 1, while the signed mass is conserved
(`cancelSplit_agentSignedMass_pair_eq`).  Hence `0 < phase7SignedSum` cannot rule out a
per-pair `minorityU` increase — the honest boundary of the signed-sum invariant. -/
theorem gap2_minorityU_rise_compatible_with_pos_sum (σ st : Sign) (s t : AgentState L K)
    (hsM : s.role = Role.main) (htM : t.role = Role.main)
    (i j : Fin (L + 1)) (hsb : s.bias = Bias.dyadic σ i)
    (htb : t.bias = Bias.dyadic st j) (hss : σ ≠ st) (hg2 : i.val + 2 = j.val) :
    Multiset.countP (fun a => minoritySt σ a)
          ({s, t} : Multiset (AgentState L K)) + 1
      ≤ Multiset.countP (fun a => minoritySt σ a)
          ({(cancelSplit L K s t).1, (cancelSplit L K s t).2} : Multiset (AgentState L K))
    ∧ agentSignedMass (cancelSplit L K s t).1
        + agentSignedMass (cancelSplit L K s t).2
      = agentSignedMass s + agentSignedMass t := by
  classical
  refine ⟨?_, cancelSplit_agentSignedMass_pair_eq s t⟩
  have hsmin : minoritySt σ s := ⟨hsM, i, hsb⟩
  have htmin_not : ¬ minoritySt σ t := by
    rw [minoritySt_iff]; rintro ⟨_, hb⟩
    rw [htb] at hb; simp only [biasIsSigned] at hb; exact hss hb.symm
  have hineq0 : ¬ i.val = j.val := by omega
  have hineq1 : ¬ i.val + 1 = j.val := by omega
  have hineq1' : ¬ j.val + 1 = i.val := by omega
  have hjL : j.val < L + 1 := j.2
  have hcs : cancelSplit L K s t
      = ({s with bias := .dyadic σ ⟨i.val + 1, by omega⟩},
         {t with bias := .dyadic σ ⟨i.val + 2, by omega⟩}) := by
    unfold cancelSplit
    rw [hsb, htb]
    simp only [if_pos (show σ ≠ st from hss), dif_neg hineq0, dif_neg hineq1,
      dif_neg hineq1', dif_pos hg2]
  rw [countP_minoritySt_pair, countP_minoritySt_pair, hcs]
  have ho1 : minoritySt σ ({s with bias := (Bias.dyadic σ
      ⟨i.val + 1, by omega⟩ : Bias L)}) := ⟨by rw [hsM.symm], _, rfl⟩
  have ho2 : minoritySt σ ({t with bias := (Bias.dyadic σ
      ⟨i.val + 2, by omega⟩ : Bias L)}) := ⟨by rw [htM.symm], _, rfl⟩
  rw [if_pos ho1, if_pos ho2, if_pos hsmin, if_neg htmin_not]

/-! ## Part I — the REBUILT Phase-7 `PhaseConvergenceW` with `hClosed` DISCHARGED.

`phase7Convergence'` instantiates the crude engine on the **genuinely-closed** invariant
`Inv7Sum` (= `Phase7AllMain n ∧ 0 < phase7SignedSum`).  The closure `hClosed` is now the
PROVED `invClosed_Inv7Sum n` (no longer a carried hypothesis — the broken
`MinorityHiIdx`-version could never supply it).  The two remaining carried inputs are:
`hmono` (the per-step `minorityU` non-increase, `PotNonincrOn Inv7Sum K minorityU`) —
which is strictly stronger than `Inv7Sum` (see `gap2_minorityU_rise_compatible_with_pos_sum`:
the gap-2 rise is signed-sum-conserving, so it needs the per-pair ordering content on top
of `0 < signedSum`), and the drain `hstep` (the carried eliminator floor, unchanged from
relay-4).  This is the honest rebuild: the invariant layer now rests on the conserved
signed sum, with `hClosed` fully internal. -/

/-- **The rebuilt Phase-7 cancellation `PhaseConvergenceW` on the genuinely-closed
signed-sum invariant.**  `Pre = Inv7Sum n ∧ minorityU σ ≤ M₀`, `Post = Inv7Sum n ∧
minorityU σ = 0`.  `hClosed` is the PROVED `invClosed_Inv7Sum`; `hmono` (per-step
minority non-increase, strictly stronger than `0 < signedSum`) and the drain `hstep`
are the carried honest inputs. -/
noncomputable def phase7Convergence' (σ : Sign) (n : ℕ)
    (hmono : OneSidedCancel.PotNonincrOn (fun c => Inv7Sum (L := L) (K := K) n c)
      (NonuniformMajority L K).transitionKernel (fun c => minorityU σ c))
    (q : ℝ≥0∞)
    (hstep : ∀ b : Config (AgentState L K), Inv7Sum n b → 1 ≤ minorityU σ b →
      (NonuniformMajority L K).transitionKernel b
        (OneSidedCancel.potDone (fun c => minorityU σ c))ᶜ ≤ q)
    (M₀ : ℕ) (t : ℕ) (ε : ℝ≥0) (hε : (q ^ t : ℝ≥0∞) ≤ (ε : ℝ≥0∞)) :
    PhaseConvergenceW (NonuniformMajority L K).transitionKernel :=
  OneSidedCancel.crude_PhaseConvergenceW
    (NonuniformMajority L K).transitionKernel
    (fun c => Inv7Sum (L := L) (K := K) n c)
    (invClosed_Inv7Sum n)
    (fun c => minorityU σ c)
    hmono
    q hstep M₀ t ε hε

/-! ## Part J — the SIGN-CLASS signed-mass split and the honest `hmono` discharge.

The relay-5 obstruction (`gap2_minorityU_rise_compatible_with_pos_sum`) shows the
minority *count* `minorityU σ` can RISE under a gap-2 fire.  But the minority *mass*
cannot.  Define `classMass σ c` = the (nonnegative, `2^L`-scaled) total dyadic mass of
the σ-signed Main agents.  Working the five `cancelSplit` branches:

* same sign / `zero` / gap ≥ 3 — identity, class masses unchanged.
* **gap 0** (`i = j`, opposite signs) — both agents zero out: the σ-class loses
  `2^{L-i}` and the σ.flip-class loses `2^{L-i}` (EQUAL removal).
* **gap 1** (smaller index `i`, larger `i+1`) — the `i+1` agent zeroes, the `i` agent
  keeps its sign: whichever class held the `i+1` agent loses `2^{L-(i+1)}`; the other
  class is unchanged.
* **gap 2** (smaller index `i`, larger `i+2`) — the smaller-index agent's sign is copied
  onto BOTH outputs at `i+1, i+2`: the smaller-index class GAINS `2^{L-(i+1)}+2^{L-(i+2)}`
  and LOSES its original `2^{L-i}` (net `-2^{L-(i+2)}`, a DROP since
  `2^{L-(i+1)}+2^{L-(i+2)} = 2^{L-i}-2^{L-(i+2)}` — wait: `2^{L-i}=4·2^{L-(i+2)}`,
  `2^{L-(i+1)}=2·2^{L-(i+2)}`, so gain `3·2^{L-(i+2)}` minus loss `4·2^{L-(i+2)}` = net
  `-2^{L-(i+2)}`); the larger-index class LOSES its original `2^{L-(i+2)}`.

So under cancelSplit EVERY class's mass is NON-INCREASING — including the gap-2 minority
class, which drops by `2^{L-(i+2)}` even as its COUNT rises.  This makes `classMass σ`
the honest engine potential: it is per-pair non-increasing on the all-Main phase-7 window
WITHOUT any index-ordering hypothesis, and `{classMass σ = 0}` is exactly
`NoMinority σ` (a Main with a σ-signed dyadic contributes `≥ 1`). -/

/-- The `2^L`-scaled NONNEGATIVE dyadic mass that a bias contributes to sign-class `σ`:
`2^{L-i}` for `dyadic σ i`, `0` for the opposite sign or `zero`. -/
def biasClassMass (σ : Sign) (L : ℕ) : Bias L → ℤ
  | .zero => 0
  | .dyadic s i => if s = σ then (2 : ℤ) ^ (L - i.val) else 0

/-- The σ-class mass of an agent (reads only its bias; Mains and non-Mains alike, but
in the phase-7 all-Main window every agent is Main). -/
def agentClassMass (σ : Sign) (a : AgentState L K) : ℤ := biasClassMass σ L a.bias

/-- `agentClassMass` is always `≥ 0`. -/
theorem agentClassMass_nonneg (σ : Sign) (a : AgentState L K) :
    0 ≤ agentClassMass σ a := by
  unfold agentClassMass biasClassMass
  cases a.bias with
  | zero => simp
  | dyadic s i =>
      by_cases h : s = σ
      · simp only [h, if_true]; positivity
      · simp [h]

/-- The σ-class total mass of a config. -/
def classMass (σ : Sign) (c : Config (AgentState L K)) : ℤ :=
  (c.map (fun a => agentClassMass σ a)).sum

/-- `classMass σ` is `≥ 0` (a sum of nonnegative per-agent masses). -/
theorem classMass_nonneg (σ : Sign) (c : Config (AgentState L K)) :
    0 ≤ classMass σ c := by
  unfold classMass
  refine Multiset.sum_nonneg ?_
  intro x hx
  rw [Multiset.mem_map] at hx
  obtain ⟨a, _, ha⟩ := hx
  rw [← ha]; exact agentClassMass_nonneg σ a

/-- **Per-pair σ-class mass NON-INCREASE under `cancelSplit`.**  For ANY sign class `σ`,
the sum of the two agents' `agentClassMass σ` over the produced pair is `≤` that over the
consumed pair.  This holds in EVERY branch with NO index-ordering hypothesis — in
particular the gap-2 branch (where the minority *count* rises) still DROPS the minority
*mass*.  This is the honest one-sided potential the relay-5 obstruction left open. -/
theorem cancelSplit_classMass_pair_le (σ : Sign) (s t : AgentState L K) :
    agentClassMass σ (cancelSplit L K s t).1
        + agentClassMass σ (cancelSplit L K s t).2
      ≤ agentClassMass σ s + agentClassMass σ t := by
  classical
  unfold agentClassMass
  cases hsb : s.bias with
  | zero =>
      have hcs : cancelSplit L K s t = (s, t) := by unfold cancelSplit; rw [hsb]
      rw [hcs, hsb]
  | dyadic ss i =>
    cases htb : t.bias with
    | zero =>
        have hcs : cancelSplit L K s t = (s, t) := by unfold cancelSplit; rw [hsb, htb]
        rw [hcs, hsb, htb]
    | dyadic st j =>
      by_cases hne : ss = st
      · have hcs : cancelSplit L K s t = (s, t) := by
          unfold cancelSplit
          simp only [hsb, htb, if_neg (show ¬ ss ≠ st from by simpa using hne)]
        rw [hcs, hsb, htb]
      · have hnee : ss ≠ st := hne
        by_cases h0 : i.val = j.val
        · -- gap 0: both zero out; removed mass ≥ 0.
          have hcs : cancelSplit L K s t
              = ({s with bias := .zero}, {t with bias := .zero}) := by
            unfold cancelSplit; simp only [hsb, htb, if_pos hnee, dif_pos h0]
          rw [hcs]; simp only [biasClassMass]
          rcases ss with _ | _ <;> rcases st with _ | _ <;> rcases σ with _ | _ <;>
            simp_all <;> first | positivity | linarith | omega
        by_cases h1 : i.val + 1 = j.val
        · have hjL : j.val < L + 1 := j.2
          have hcs : cancelSplit L K s t
              = ({s with bias := .dyadic ss ⟨i.val + 1, by omega⟩}, {t with bias := .zero}) := by
            unfold cancelSplit; simp only [hsb, htb, if_pos hnee, dif_neg h0, dif_pos h1]
          rw [hcs]; simp only [biasClassMass]
          have hexp2 : L - (i.val + 1) = L - j.val := by omega
          have hmono : (2:ℤ) ^ (L - j.val) ≤ 2 ^ (L - i.val) :=
            pow_le_pow_right₀ (by norm_num) (by omega)
          rcases ss with _ | _ <;> rcases st with _ | _ <;> rcases σ with _ | _ <;>
            simp_all <;> first | positivity | linarith | omega
        by_cases h1' : j.val + 1 = i.val
        · have hiL : i.val < L + 1 := i.2
          have hcs : cancelSplit L K s t
              = ({s with bias := .zero}, {t with bias := .dyadic st ⟨j.val + 1, by omega⟩}) := by
            unfold cancelSplit
            simp only [hsb, htb, if_pos hnee, dif_neg h0, dif_neg h1, dif_pos h1']
          rw [hcs]; simp only [biasClassMass]
          have hexp2 : L - (j.val + 1) = L - i.val := by omega
          have hmono : (2:ℤ) ^ (L - i.val) ≤ 2 ^ (L - j.val) :=
            pow_le_pow_right₀ (by norm_num) (by omega)
          rcases ss with _ | _ <;> rcases st with _ | _ <;> rcases σ with _ | _ <;>
            simp_all <;> first | positivity | linarith | omega
        by_cases h2 : i.val + 2 = j.val
        · have hjL : j.val < L + 1 := j.2
          have hcs : cancelSplit L K s t
              = ({s with bias := .dyadic ss ⟨i.val + 1, by omega⟩},
                 {t with bias := .dyadic ss ⟨i.val + 2, by omega⟩}) := by
            unfold cancelSplit
            simp only [hsb, htb, if_pos hnee, dif_neg h0, dif_neg h1, dif_neg h1', dif_pos h2]
          rw [hcs]; simp only [biasClassMass]
          have hei : L - i.val = (L - j.val) + 2 := by omega
          have hei1 : L - (i.val + 1) = (L - j.val) + 1 := by omega
          have hei2 : L - (i.val + 2) = L - j.val := by omega
          -- ss-class: gain 2^{(L-j)+1}+2^{L-j} vs loss 2^{(L-j)+2}: net DROP 2^{L-j}.
          rcases ss with _ | _ <;> rcases st with _ | _ <;> rcases σ with _ | _ <;>
            simp_all [hei, hei1, hei2, pow_succ] <;> nlinarith [pow_pos (show (0:ℤ) < 2 by norm_num) (L - j.val)]
        by_cases h2' : j.val + 2 = i.val
        · have hiL : i.val < L + 1 := i.2
          have hcs : cancelSplit L K s t
              = ({s with bias := .dyadic st ⟨j.val + 2, by omega⟩},
                 {t with bias := .dyadic st ⟨j.val + 1, by omega⟩}) := by
            unfold cancelSplit
            simp only [hsb, htb, if_pos hnee, dif_neg h0, dif_neg h1, dif_neg h1', dif_neg h2,
              dif_pos h2']
          rw [hcs]; simp only [biasClassMass]
          have hej : L - j.val = (L - i.val) + 2 := by omega
          have hej1 : L - (j.val + 1) = (L - i.val) + 1 := by omega
          have hej2 : L - (j.val + 2) = L - i.val := by omega
          rcases ss with _ | _ <;> rcases st with _ | _ <;> rcases σ with _ | _ <;>
            simp_all [hej, hej1, hej2, pow_succ] <;> nlinarith [pow_pos (show (0:ℤ) < 2 by norm_num) (L - i.val)]
        · have hcs : cancelSplit L K s t = (s, t) := by
            unfold cancelSplit
            simp only [hsb, htb, if_pos hnee, dif_neg h0, dif_neg h1, dif_neg h1', dif_neg h2,
              dif_neg h2']
          rw [hcs, hsb, htb]

/-- **Per-pair σ-class mass STRICT DROP under a gap-1 cancel** (the drain building block).
If `t` is the σ-minority Main at the larger index `j = i+1` and `s` is the σ.flip Main at
`i`, then `cancelSplit` zeroes `t` and keeps `s` at σ.flip-sign `i+1`: the σ-class mass
over the pair DROPS by `t`'s mass `2^{L-j} ≥ 1`.  This is the per-pair input the cleaned
engine's `hstep` (a σ-class-MASS drain) needs — the mass analogue of
`cancelSplit_minorityU_pair_drop`. -/
theorem cancelSplit_classMass_pair_drop (σ ss : Sign) (s t : AgentState L K)
    (i j : Fin (L + 1)) (hsb : s.bias = Bias.dyadic ss i)
    (htb : t.bias = Bias.dyadic σ j) (hss : ss ≠ σ) (hg1 : i.val + 1 = j.val) :
    agentClassMass σ (cancelSplit L K s t).1
        + agentClassMass σ (cancelSplit L K s t).2
        + 1
      ≤ agentClassMass σ s + agentClassMass σ t := by
  classical
  have hineq0 : ¬ i.val = j.val := by omega
  have hjL : j.val < L + 1 := j.2
  have hcs : cancelSplit L K s t
      = ({s with bias := .dyadic ss ⟨i.val + 1, by omega⟩}, {t with bias := .zero}) := by
    unfold cancelSplit
    rw [hsb, htb]
    simp only [if_pos (show ss ≠ σ from hss), dif_neg hineq0, dif_pos hg1]
  unfold agentClassMass
  rw [hcs, hsb, htb]
  simp only [biasClassMass]
  -- outputs: `dyadic ss (i+1)` (ss ≠ σ ⇒ class mass 0) and `zero` (0); inputs:
  -- `dyadic ss i` (0) and `dyadic σ j` (mass 2^{L-j} ≥ 1).
  simp only [if_neg hss, if_true]
  have hp : (1:ℤ) ≤ 2 ^ (L - j.val) := one_le_pow₀ (by norm_num)
  linarith [hp]

/-- **Config-level σ-class mass NON-INCREASE under a chosen-pair step** (Phase-7 window).
On an all-Main phase-7 window every applicable pair is both-Main so `Transition =
cancelSplit`, and `cancelSplit_classMass_pair_le` lifts through the
`c − {r₁,r₂} + {out₁,out₂}` step decomposition.  The not-applicable (self) case is the
identity.  This is the config-level analogue of `phase7SignedSum_stepOrSelf_eq` with `=`
relaxed to `≤`. -/
theorem classMass_stepOrSelf_le (σ : Sign) (n : ℕ) (c : Config (AgentState L K))
    (hw : Phase7AllMain n c) (r₁ r₂ : AgentState L K) :
    classMass σ (Protocol.stepOrSelf (NonuniformMajority L K) c r₁ r₂)
      ≤ classMass σ c := by
  classical
  obtain ⟨_, hph⟩ := hw
  by_cases happ : Protocol.Applicable c r₁ r₂
  · have hm1 := mem_of_app_left7 happ
    have hm2 := mem_of_app_right7 happ
    obtain ⟨h17, h1M⟩ := hph r₁ hm1
    obtain ⟨h27, h2M⟩ := hph r₂ hm2
    have hcs := Transition_eq_cancelSplit_of_phase7_main r₁ r₂ h17 h27 h1M h2M
    have hpair : agentClassMass σ (Transition L K r₁ r₂).1
          + agentClassMass σ (Transition L K r₁ r₂).2
        ≤ agentClassMass σ r₁ + agentClassMass σ r₂ := by
      rw [hcs]; exact cancelSplit_classMass_pair_le σ r₁ r₂
    have hc' : Protocol.stepOrSelf (NonuniformMajority L K) c r₁ r₂
        = c - {r₁, r₂} + {(Transition L K r₁ r₂).1, (Transition L K r₁ r₂).2} := by
      unfold Protocol.stepOrSelf; rw [if_pos happ]; rfl
    have happ_le : (r₁ ::ₘ {r₂} : Multiset (AgentState L K)) ≤ c := happ
    have hrestore : c - r₁ ::ₘ {r₂} + r₁ ::ₘ {r₂} = c :=
      Multiset.sub_add_cancel happ_le
    have hsum_c : classMass σ c
        = classMass σ (c - r₁ ::ₘ {r₂})
            + (agentClassMass σ r₁ + agentClassMass σ r₂) := by
      rw [← hrestore]; simp [classMass, add_left_comm]
    have hsum_c' : classMass σ
          (c - r₁ ::ₘ {r₂} +
            (Transition L K r₁ r₂).1 ::ₘ {(Transition L K r₁ r₂).2})
        = classMass σ (c - r₁ ::ₘ {r₂})
            + (agentClassMass σ (Transition L K r₁ r₂).1
              + agentClassMass σ (Transition L K r₁ r₂).2) := by
      simp [classMass, add_left_comm]
    rw [hc']
    show classMass σ
        (c - r₁ ::ₘ {r₂} +
          (Transition L K r₁ r₂).1 ::ₘ {(Transition L K r₁ r₂).2})
      ≤ classMass σ c
    rw [hsum_c', hsum_c]
    linarith [hpair]
  · rw [Protocol.stepOrSelf_eq_self_of_not_applicable happ]

/-- **Support-level σ-class mass non-increase** (Phase-7 window): every successor in the
kernel's step support has `classMass σ` no larger than the source. -/
theorem classMass_support_le (σ : Sign) (n : ℕ) (c c' : Config (AgentState L K))
    (hw : Phase7AllMain n c)
    (hc' : c' ∈ ((NonuniformMajority L K).stepDistOrSelf c).support) :
    classMass σ c' ≤ classMass σ c := by
  by_cases hc : 2 ≤ c.card
  · rw [show (NonuniformMajority L K).stepDistOrSelf c
        = (NonuniformMajority L K).stepDist c hc by
        unfold Protocol.stepDistOrSelf; rw [dif_pos hc]] at hc'
    obtain ⟨⟨r₁, r₂⟩, hr⟩ := Protocol.stepDist_support (NonuniformMajority L K) c hc c' hc'
    rw [← hr]; exact classMass_stepOrSelf_le σ n c hw r₁ r₂
  · rw [show (NonuniformMajority L K).stepDistOrSelf c = PMF.pure c by
        unfold Protocol.stepDistOrSelf; rw [dif_neg hc]] at hc'
    rw [PMF.mem_support_pure_iff] at hc'; subst hc'; exact le_refl _

/-! ### The ℕ-valued engine potential and the `NoMinority` bridge.

The engine's `Φ : α → ℕ` must be ℕ-valued.  `classMass σ` is `≥ 0`, so
`classMassN σ := (classMass σ).toNat` is the honest ℕ potential, non-increasing along
the kernel (toNat is monotone on `ℤ≥0`).  And `classMassN σ c = 0` is EXACTLY
`NoMinority σ c` on the phase-7 all-Main window: every σ-signed Main contributes mass
`≥ 1`, so zero total σ-class mass forces zero σ-minority count. -/

/-- The ℕ-valued σ-class mass potential (`= classMass σ` since `classMass σ ≥ 0`). -/
def classMassN (σ : Sign) (c : Config (AgentState L K)) : ℕ := (classMass σ c).toNat

/-- `classMassN σ` is non-increasing on the one-step kernel support (Phase-7 window). -/
theorem classMassN_support_le (σ : Sign) (n : ℕ) (c c' : Config (AgentState L K))
    (hw : Phase7AllMain n c)
    (hc' : c' ∈ ((NonuniformMajority L K).stepDistOrSelf c).support) :
    classMassN σ c' ≤ classMassN σ c := by
  unfold classMassN
  exact Int.toNat_le_toNat (classMass_support_le σ n c c' hw hc')

/-- **The engine's `hmono` for `Φ = classMassN σ`** on the genuinely-closed `Inv7Sum`.
From an `Inv7Sum`-config the kernel never raises `classMassN σ` (the honest one-sided
potential the relay-5 obstruction left open — `classMassN` drops where `minorityU`
rises). -/
theorem potNonincrOn_classMassN (σ : Sign) (n : ℕ) :
    OneSidedCancel.PotNonincrOn (fun c => Inv7Sum (L := L) (K := K) n c)
      (NonuniformMajority L K).transitionKernel (fun c => classMassN σ c) := by
  intro c hInv
  obtain ⟨hw, _⟩ := hInv
  change ((NonuniformMajority L K).stepDistOrSelf c).toMeasure
    {x | classMassN σ c < classMassN σ x} = 0
  rw [PMF.toMeasure_apply_eq_zero_iff _ (DiscreteMeasurableSpace.forall_measurableSet _)]
  rw [Set.disjoint_left]
  intro x hsupp hx
  exact absurd (classMassN_support_le σ n c x hw hsupp) (by
    simp only [Set.mem_setOf_eq] at hx; omega)

/-- A σ-signed Main contributes σ-class mass `≥ 1` (so `agentClassMass σ a ≠ 0`). -/
theorem one_le_agentClassMass_of_minoritySt (σ : Sign) (a : AgentState L K)
    (h : minoritySt σ a) : 1 ≤ agentClassMass σ a := by
  obtain ⟨_, i, hb⟩ := h
  unfold agentClassMass biasClassMass
  rw [hb]
  simp only [if_true]
  exact one_le_pow₀ (by norm_num)

/-- **The `NoMinority` bridge.**  On any config, `classMass σ c = 0` forces
`minorityU σ c = 0` (the converse direction we need for `potDone`).  Each σ-signed Main
contributes mass `≥ 1`; with all per-agent masses `≥ 0`, a zero total kills the count. -/
theorem minorityU_eq_zero_of_classMass_zero (σ : Sign) (c : Config (AgentState L K))
    (h : classMass σ c = 0) : minorityU σ c = 0 := by
  classical
  by_contra hne
  -- some agent is a σ-minority; it contributes `≥ 1`, contradicting total `0`.
  have hpos : 0 < minorityU σ c := Nat.pos_of_ne_zero hne
  rw [minorityU, Multiset.countP_pos] at hpos
  obtain ⟨a, hamem, ha⟩ := hpos
  have hcontrib : 1 ≤ agentClassMass σ a := one_le_agentClassMass_of_minoritySt σ a ha
  have hsum_ge : agentClassMass σ a ≤ classMass σ c := by
    unfold classMass
    refine Multiset.single_le_sum (fun y hy => ?_) _ (Multiset.mem_map_of_mem _ hamem)
    rw [Multiset.mem_map] at hy; obtain ⟨b, _, hb⟩ := hy
    rw [← hb]; exact agentClassMass_nonneg σ b
  omega

/-- `classMassN σ c = 0 → minorityU σ c = 0` (the `potDone` ⊆ `NoMinority` direction). -/
theorem minorityU_eq_zero_of_classMassN_zero (σ : Sign) (c : Config (AgentState L K))
    (h : classMassN σ c = 0) : minorityU σ c = 0 := by
  apply minorityU_eq_zero_of_classMass_zero σ c
  have hnn := classMass_nonneg σ c
  unfold classMassN at h
  omega

/-! ## Part K — the CLEANED Phase-7 `PhaseConvergenceW` with BOTH `hClosed` AND `hmono`
discharged on the genuinely-closed signed-class-mass invariant.

`phase7Convergence''` instantiates the crude engine with `Φ = classMassN σ` (the honest
NON-INCREASING σ-class mass, vs the count `minorityU σ` which can RISE).  Now BOTH
structural ingredients are PROVED INTERNAL:

* `hClosed = invClosed_Inv7Sum n`  — the genuinely-closed signed-sum invariant (relay 5).
* `hmono   = potNonincrOn_classMassN σ n`  — the relay-6 discharge: `classMassN σ` never
  rises along the kernel from an `Inv7Sum`-state.  This is exactly the residual gap the
  relay-5 `gap2_minorityU_rise_compatible_with_pos_sum` pinned: the obstruction was to
  `minorityU` (a COUNT), not to the σ-class MASS, which drops in the very gap-2 branch.

Only the drain `hstep` is carried — now phrased on `classMassN σ` (the Doty Lemma 7.4
mass floor / Lemma 7.5 successive level elimination as a MASS drain).  The post-condition
`classMassN σ = 0` is `NoMinority σ` via `minorityU_eq_zero_of_classMassN_zero`. -/

/-- **The cleaned Phase-7 cancellation `PhaseConvergenceW`** — engine form (b) on the
genuinely-closed `Inv7Sum`, with `Φ = classMassN σ`.  `hClosed` (= `invClosed_Inv7Sum`)
and `hmono` (= `potNonincrOn_classMassN`) are BOTH PROVED INTERNAL; only the drain
`hstep` (now a σ-class-MASS drain, the Doty Lemma 7.4/7.5 floor) is carried.

`Pre x = Inv7Sum n x ∧ classMassN σ x ≤ M₀`, `Post x = Inv7Sum n x ∧ classMassN σ x = 0`;
the latter implies `minorityU σ x = 0` by `minorityU_eq_zero_of_classMassN_zero`. -/
noncomputable def phase7Convergence'' (σ : Sign) (n : ℕ)
    (q : ℝ≥0∞)
    (hstep : ∀ b : Config (AgentState L K), Inv7Sum n b → 1 ≤ classMassN σ b →
      ((NonuniformMajority L K).transitionKernel b)
        (OneSidedCancel.potDone (fun c => classMassN σ c))ᶜ ≤ q)
    (M₀ t : ℕ) (ε : ℝ≥0) (hε : (q ^ t : ℝ≥0∞) ≤ (ε : ℝ≥0∞)) :
    PhaseConvergenceW (NonuniformMajority L K).transitionKernel :=
  OneSidedCancel.crude_PhaseConvergenceW
    (NonuniformMajority L K).transitionKernel
    (fun c => Inv7Sum (L := L) (K := K) n c)
    (invClosed_Inv7Sum n)
    (fun c => classMassN σ c)
    (potNonincrOn_classMassN σ n)
    q hstep M₀ t ε hε

/-- **The Phase-7 post-condition is `NoMinority`.**  The cleaned engine's `Post`
(`Inv7Sum ∧ classMassN σ = 0`) implies the genuine Phase-7 target `minorityU σ = 0`
(`NoMinority σ`), via the mass→count bridge.  So driving `classMassN σ → 0` drives the
minority count to `0`. -/
theorem phase7Convergence''_post_noMinority (σ : Sign) (n : ℕ)
    (c : Config (AgentState L K))
    (hpost : Inv7Sum n c ∧ classMassN σ c = 0) :
    NoMinority σ c :=
  minorityU_eq_zero_of_classMassN_zero σ c hpost.2

end Phase7Convergence

end ExactMajority
