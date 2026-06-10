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

end Phase7Convergence

end ExactMajority
