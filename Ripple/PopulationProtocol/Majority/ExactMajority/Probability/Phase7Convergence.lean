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

/-- **Per-pair `Transition` minority non-increase.**  Combines the two cases: both
Main (reduce to `cancelSplit`, apply `cancelSplit_minorityU_pair_le` under the pair
index hypothesis) and not both Main (`Phase7Transition` leaves Mains untouched).
The full `Transition` reduces to `Phase7Transition` whenever both are phase-7 (the
epidemic and phase-10 finish are identities at phase 7). -/
theorem Transition_minorityU_pair_le (σ : Sign) (s t : AgentState L K)
    (hs7 : s.phase.val = 7) (ht7 : t.phase.val = 7)
    (hidx : ∀ ss i st j, s.bias = Bias.dyadic ss i → t.bias = Bias.dyadic st j →
      ss ≠ st → (ss = σ → j.val ≤ i.val) ∧ (st = σ → i.val ≤ j.val)) :
    Multiset.countP (fun a => minoritySt σ a)
        ({(Transition L K s t).1, (Transition L K s t).2} : Multiset (AgentState L K))
      ≤ Multiset.countP (fun a => minoritySt σ a) ({s, t} : Multiset (AgentState L K)) := by
  by_cases hboth : s.role = Role.main ∧ t.role = Role.main
  · obtain ⟨hsM, htM⟩ := hboth
    rw [Transition_eq_cancelSplit_of_phase7_main s t hs7 ht7 hsM htM]
    exact cancelSplit_minorityU_pair_le σ s t hsM htM hidx
  · -- not both Main: `Transition` reduces to `Phase7Transition` (epidemic/finish = id).
    have hepi := phaseEpidemicUpdate_eq_self_of_phase7 (L := L) (K := K) s t hs7 ht7
    have hsp : s.phase = ⟨7, by decide⟩ := Fin.ext hs7
    -- Phase7Transition preserves phase 7 ⇒ finishPhase10Entry = id.
    have hp7nd := Phase7Transition_phase_nondec (L := L) (K := K) s t
    have hge1 := (Phase7Transition_phase_nondec (L := L) (K := K) s t).1
    have hge2 := (Phase7Transition_phase_nondec (L := L) (K := K) s t).2
    -- phase of outputs is ≥ 7; and we need ≠ 10 for finishPhase10Entry to be id.
    -- Phase7Transition only runs cancelSplit (phase-preserving) or the clock counter.
    have hTr : Transition L K s t = Phase7Transition L K s t := by
      unfold Transition
      rw [hepi]; simp only [hsp]
      rw [finishPhase10Entry_eq_self_of_after_ne_10 (L := L) (K := K) s _
            (Phase7Transition_after_ne_10_fst s t hs7 ht7),
          finishPhase10Entry_eq_self_of_after_ne_10 (L := L) (K := K) t _
            (Phase7Transition_after_ne_10_snd s t hs7 ht7)]
    rw [hTr]
    exact le_of_eq (Phase7Transition_minorityU_eq_of_not_both_main σ s t hboth)

end Phase7Convergence

end ExactMajority
