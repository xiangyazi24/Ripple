/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# EarlyDripMarked — the marked kernel for Doty's early-drip set `D` (§6 brick 3.3)

Doty's early-drip set `D_{≥T+1}(t)` (paper lines 1807–1812) is PATH-DEPENDENT: agents that moved
above minute `T` via a drip while the pre-bulk gate held (`c_{≥T} < n^{-0.45}`), plus agents brought
above minute `T` via an epidemic (sync) reaction with an agent already in `D`.  To make it an
ordinary endpoint statistic of a Markov chain we AUGMENT the state with a per-agent Boolean taint
mark (ChatGPT consult route 1a):

* `MarkedAgent L K := AgentState L K × Bool` — the agent state plus its taint mark;
* `markFor` — Doty's marking rule, applied positionally to the pair outputs:
  - an output below minute `T+1` is unmarked (`D` only contains agents above `T`);
  - an agent already above `T` keeps its mark (membership in `D` is decided at crossing time);
  - a DRIP crossing (same-minute pair) is marked iff the pre-bulk gate held (`g = true`) — the
    "early drip";
  - a SYNC crossing inherits the leader's mark — the "epidemic with another early drip agent";
* `markedK T θn` — the marked kernel: the SAME uniform-ordered-pair scheduler (over marked states),
  the same underlying `Transition`, plus the mark update; the gate `g` is computed from the ERASED
  configuration (`rBeyond T < θn`), making the kernel config-dependent (legal for a kernel, not a
  population protocol — exactly why `D` could not be a protocol statistic).

## The projection theorem (the formal bridge)

`markedK_pow_erase`:  `(markedK^t) mc₀ (erase⁻¹ A) = (K^t) (erase mc₀) A` — the marked chain
projects EXACTLY onto the real `NonuniformMajority` chain under `eraseConfig = Multiset.map
Prod.fst`.  Hence every high-probability statement proven in the marked world about events that
depend only on the erased configuration transfers verbatim to the real chain.  The proof:
1. the SCHEDULER projects (`interactionPMF_map_proj`): pushing the marked uniform-pair law through
   the state projection gives the real uniform-pair law — the fiber identity
   `Σ_{b₁,b₂} interactionCount (s₁,b₁) (s₂,b₂) = interactionCount s₁ s₂` (the diagonal
   `count·(count−1)` works out because ordered pairs of DISTINCT AGENTS partition exactly along
   the marks);
2. the STEP projects (`erase_markedStep`): erasing the marked pair update is the real pair update
   (the mark only rides along);
3. Chapman–Kolmogorov induction (the `real_le_killed` template).

The taint-count analysis (`taintedCount`, its drift, the within-gate identity
`taintedCount = rBeyond (T+1) ∘ erase`) is brick 3.4, in a separate development.

Reference: Doty et al. (arXiv:2106.10201v2) lines 1807–1819; `DOTY_LEMMA63_DOCTRINE.md` brick 3.3;
the ChatGPT brick-3 consult (route 1a, archived in the doctrine).
-/

import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.ClockRealKernel
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.HourCoupling
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.ClimbTail

namespace ExactMajority

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace EarlyDripMarked

open ClockRealKernel

variable {L K : ℕ}

/-! ## Part 0 — the marked state and the erasure. -/

/-- The marked agent: the real agent state plus the Doty taint mark. -/
abbrev MarkedAgent (L K : ℕ) := AgentState L K × Bool

/-- Erase the marks: project a marked configuration onto the real one. -/
def eraseConfig (mc : Config (MarkedAgent L K)) : Config (AgentState L K) :=
  mc.map Prod.fst

@[simp] theorem eraseConfig_card (mc : Config (MarkedAgent L K)) :
    (eraseConfig (L := L) (K := K) mc).card = mc.card :=
  Multiset.card_map _ _

/-- The count of a real state under erasure is the sum of the two marked counts of its fiber. -/
theorem count_eraseConfig (mc : Config (MarkedAgent L K)) (s : AgentState L K) :
    (eraseConfig (L := L) (K := K) mc).count s
      = mc.count (s, true) + mc.count (s, false) := by
  classical
  show Multiset.count s (eraseConfig (L := L) (K := K) mc)
    = Multiset.count ((s, true) : MarkedAgent L K) mc
      + Multiset.count ((s, false) : MarkedAgent L K) mc
  induction mc using Multiset.induction_on with
  | empty => simp [eraseConfig]
  | cons m mc ih =>
      rcases m with ⟨a, b⟩
      simp only [eraseConfig, Multiset.map_cons] at ih ⊢
      rw [Multiset.count_cons, Multiset.count_cons, Multiset.count_cons, ih]
      by_cases ha : s = a
      · subst ha
        cases b <;> simp <;> omega
      · have h1 : ¬ (((s, true) : MarkedAgent L K) = (a, b)) := by
          intro h; exact ha (congrArg Prod.fst h)
        have h2 : ¬ (((s, false) : MarkedAgent L K) = (a, b)) := by
          intro h; exact ha (congrArg Prod.fst h)
        simp [ha, h1, h2]

/-! ## Part 1 — the marking rule, the marked step, and the marked kernel. -/

/-- **Doty's marking rule**, positionally: the new mark of the output `o` produced from the input
`own` (with pair partner `partner`), at level `T`, with pre-bulk gate value `g`:
* below `T+1` — unmarked (`D` lives above `T`);
* already above `T` — keep the own mark;
* crossed via DRIP (same-minute pair) — marked iff the gate held (`g`): the early drip;
* crossed via SYNC — inherit the partner's (the leader's) mark: epidemic propagation. -/
def markFor (T : ℕ) (g : Bool) (own partner : MarkedAgent L K)
    (o : AgentState L K) : Bool :=
  if o.minute.val < T + 1 then false
  else if T + 1 ≤ own.1.minute.val then own.2
  else if own.1.minute = partner.1.minute then g
  else partner.2

/-- The marked pair update: the real `Transition` on the erased states, with the positional mark
rule. -/
def markedOut (T : ℕ) (g : Bool) (m₁ m₂ : MarkedAgent L K) :
    MarkedAgent L K × MarkedAgent L K :=
  (((Transition L K m₁.1 m₂.1).1,
      markFor (L := L) (K := K) T g m₁ m₂ (Transition L K m₁.1 m₂.1).1),
   ((Transition L K m₁.1 m₂.1).2,
      markFor (L := L) (K := K) T g m₂ m₁ (Transition L K m₁.1 m₂.1).2))

@[simp] theorem markedOut_fst_state (T : ℕ) (g : Bool) (m₁ m₂ : MarkedAgent L K) :
    (markedOut (L := L) (K := K) T g m₁ m₂).1.1 = (Transition L K m₁.1 m₂.1).1 := rfl

@[simp] theorem markedOut_snd_state (T : ℕ) (g : Bool) (m₁ m₂ : MarkedAgent L K) :
    (markedOut (L := L) (K := K) T g m₁ m₂).2.1 = (Transition L K m₁.1 m₂.1).2 := rfl

/-- The pre-bulk gate, computed from the erased configuration: the bulk has not arrived at level
`T` (`rBeyond T < θn`). -/
def preBulkGate (T θn : ℕ) (mc : Config (MarkedAgent L K)) : Bool :=
  decide (rBeyond (L := L) (K := K) T (eraseConfig (L := L) (K := K) mc) < θn)

/-- The marked scheduled step: replace the scheduled pair by its marked update (when the pair is
present), with the gate evaluated at the CURRENT configuration. -/
def markedStep (T θn : ℕ) (mc : Config (MarkedAgent L K))
    (pr : MarkedAgent L K × MarkedAgent L K) : Config (MarkedAgent L K) :=
  if ({pr.1, pr.2} : Multiset (MarkedAgent L K)) ≤ mc then
    mc - {pr.1, pr.2}
      + {(markedOut (L := L) (K := K) T (preBulkGate (L := L) (K := K) T θn mc) pr.1 pr.2).1,
         (markedOut (L := L) (K := K) T (preBulkGate (L := L) (K := K) T θn mc) pr.1 pr.2).2}
  else mc

/-- The marked one-step distribution: the SAME uniform-ordered-pair scheduler (over marked
states), mapped through the marked step; point mass on degenerate populations. -/
noncomputable def markedPMF (T θn : ℕ) (mc : Config (MarkedAgent L K)) :
    PMF (Config (MarkedAgent L K)) :=
  if h : 2 ≤ mc.card then
    PMF.map (markedStep (L := L) (K := K) T θn mc) (mc.interactionPMF h)
  else PMF.pure mc

/-- The marked transition kernel. -/
noncomputable def markedK (T θn : ℕ) :
    Kernel (Config (MarkedAgent L K)) (Config (MarkedAgent L K)) where
  toFun mc := (markedPMF (L := L) (K := K) T θn mc).toMeasure
  measurable' := Measurable.of_discrete

instance (T θn : ℕ) : IsMarkovKernel (markedK (L := L) (K := K) T θn) where
  isProbabilityMeasure mc := by
    show IsProbabilityMeasure (markedPMF (L := L) (K := K) T θn mc).toMeasure
    infer_instance

/-! ## Part 2 — the scheduler projection (the fiber identity). -/

/-- The diagonal pair-count identity in `ℕ`:
`x(x−1) + xy + yx + y(y−1) = (x+y)(x+y−1)` (truncated subtraction safe). -/
private theorem diag_pair_identity (x y : ℕ) :
    x * (x - 1) + x * y + (y * x + y * (y - 1)) = (x + y) * (x + y - 1) := by
  cases x with
  | zero => cases y with
    | zero => rfl
    | succ m => simp [Nat.succ_sub_one]
  | succ n => cases y with
    | zero => simp [Nat.succ_sub_one]
    | succ m =>
        simp only [Nat.succ_sub_one, show n + 1 + (m + 1) - 1 = n + m + 1 from by omega]
        ring

/-- The fiber identity of the marked interaction counts: ordered pairs of distinct agents
partition exactly along the marks. -/
theorem sum_fiber_interactionCount (mc : Config (MarkedAgent L K))
    (s₁ s₂ : AgentState L K) :
    (∑ b₁ : Bool, ∑ b₂ : Bool, mc.interactionCount ((s₁, b₁)) ((s₂, b₂)))
      = (eraseConfig (L := L) (K := K) mc).interactionCount s₁ s₂ := by
  classical
  have hc₁ := count_eraseConfig (L := L) (K := K) mc s₁
  have hc₂ := count_eraseConfig (L := L) (K := K) mc s₂
  by_cases hs : s₁ = s₂
  · subst hs
    unfold Config.interactionCount
    rw [if_pos rfl]
    rw [Fintype.sum_bool, Fintype.sum_bool, Fintype.sum_bool]
    rw [if_pos rfl, if_pos rfl,
      if_neg (by simp : ¬ (((s₁, true) : MarkedAgent L K) = (s₁, false))),
      if_neg (by simp : ¬ (((s₁, false) : MarkedAgent L K) = (s₁, true)))]
    rw [hc₁]
    exact diag_pair_identity (mc.count (s₁, true)) (mc.count (s₁, false))
  · have hne : ∀ b₁ b₂ : Bool, ¬ (((s₁, b₁) : MarkedAgent L K) = (s₂, b₂)) := by
      intro b₁ b₂ h
      exact hs (congrArg Prod.fst h)
    unfold Config.interactionCount
    rw [if_neg hs]
    rw [Fintype.sum_bool, Fintype.sum_bool, Fintype.sum_bool]
    rw [if_neg (hne true true), if_neg (hne true false),
      if_neg (hne false true), if_neg (hne false false), hc₁, hc₂]
    ring

/-- The delta-collapse of a fiber sum over marked states:
`Σ_m [s = m.1]·f m = f (s,true) + f (s,false)`. -/
private theorem sum_collapse_fiber (f : MarkedAgent L K → ℝ≥0∞) (s : AgentState L K) :
    (∑ m : MarkedAgent L K, if s = m.1 then f m else 0)
      = f (s, true) + f (s, false) := by
  classical
  rw [Fintype.sum_prod_type]
  have hinner : ∀ a : AgentState L K,
      (∑ b : Bool, if s = (a, b).1 then f (a, b) else 0)
        = if s = a then (f (a, true) + f (a, false)) else 0 := by
    intro a
    by_cases ha : s = a
    · simp [ha]
    · simp [ha]
  rw [Finset.sum_congr rfl (fun a _ => hinner a),
    Finset.sum_ite_eq Finset.univ s (fun a => f (a, true) + f (a, false)),
    if_pos (Finset.mem_univ s)]

/-- **The scheduler projects.**  Pushing the marked uniform-ordered-pair law through the state
projection yields the real uniform-ordered-pair law of the erased configuration. -/
theorem interactionPMF_map_proj (mc : Config (MarkedAgent L K)) (h : 2 ≤ mc.card)
    (h' : 2 ≤ (eraseConfig (L := L) (K := K) mc).card) :
    (mc.interactionPMF h).map
        (fun pr : MarkedAgent L K × MarkedAgent L K => (pr.1.1, pr.2.1))
      = (eraseConfig (L := L) (K := K) mc).interactionPMF h' := by
  classical
  apply PMF.ext
  rintro ⟨s₁, s₂⟩
  rw [PMF.map_apply]
  rw [tsum_eq_sum (s := (Finset.univ : Finset (MarkedAgent L K × MarkedAgent L K)))
    (fun pr hpr => absurd (Finset.mem_univ pr) hpr)]
  have hPMFval' : ((eraseConfig (L := L) (K := K) mc).interactionPMF h') (s₁, s₂)
      = (eraseConfig (L := L) (K := K) mc).interactionProb s₁ s₂ := rfl
  rw [hPMFval']
  -- collapse the pair sum onto the fiber {((s₁,b₁),(s₂,b₂))}.
  rw [Fintype.sum_prod_type]
  trans (∑ m₁ : MarkedAgent L K, if s₁ = m₁.1 then
      (∑ m₂ : MarkedAgent L K, if s₂ = m₂.1 then mc.interactionProb m₁ m₂ else 0)
    else 0)
  · apply Finset.sum_congr rfl
    intro m₁ _
    by_cases h₁ : s₁ = m₁.1
    · rw [if_pos h₁]
      apply Finset.sum_congr rfl
      intro m₂ _
      by_cases h₂ : s₂ = m₂.1
      · rw [if_pos h₂, if_pos (show ((s₁, s₂) : AgentState L K × AgentState L K)
          = ((m₁, m₂).1.1, (m₁, m₂).2.1) from by rw [← h₁, ← h₂])]
        rfl
      · rw [if_neg h₂, if_neg (show ¬ ((s₁, s₂) : AgentState L K × AgentState L K)
          = ((m₁, m₂).1.1, (m₁, m₂).2.1) from by
            intro hc; exact h₂ (congrArg Prod.snd hc))]
    · rw [if_neg h₁]
      apply Finset.sum_eq_zero
      intro m₂ _
      rw [if_neg (show ¬ ((s₁, s₂) : AgentState L K × AgentState L K)
        = ((m₁, m₂).1.1, (m₁, m₂).2.1) from by
          intro hc; exact h₁ (congrArg Prod.fst hc))]
  · rw [sum_collapse_fiber (L := L) (K := K)
      (fun m₁ => ∑ m₂ : MarkedAgent L K, if s₂ = m₂.1 then mc.interactionProb m₁ m₂ else 0) s₁]
    rw [sum_collapse_fiber (L := L) (K := K)
      (fun m₂ => mc.interactionProb (s₁, true) m₂) s₂,
      sum_collapse_fiber (L := L) (K := K)
      (fun m₂ => mc.interactionProb (s₁, false) m₂) s₂]
    -- now everything is interactionCount/totalPairs with the same denominator.
    unfold Config.interactionProb
    have htp : (eraseConfig (L := L) (K := K) mc).totalPairs = mc.totalPairs := by
      unfold Config.totalPairs
      rw [eraseConfig_card]
    rw [htp]
    rw [ENNReal.div_add_div_same, ENNReal.div_add_div_same, ENNReal.div_add_div_same]
    congr 1
    have hfib := sum_fiber_interactionCount (L := L) (K := K) mc s₁ s₂
    rw [Fintype.sum_bool, Fintype.sum_bool, Fintype.sum_bool] at hfib
    exact_mod_cast congrArg (Nat.cast : ℕ → ℝ≥0∞) hfib

/-! ## Part 3 — the step projection. -/

/-- A `PMF.map` congruence on the support (Mathlib has no `PMF.map_congr`; local helper). -/
private theorem pmf_map_congr {α β : Type*} (p : PMF α) (f g : α → β)
    (h : ∀ a ∈ p.support, f a = g a) : p.map f = p.map g := by
  classical
  apply PMF.ext
  intro b
  rw [PMF.map_apply, PMF.map_apply]
  apply tsum_congr
  intro a
  by_cases ha : a ∈ p.support
  · rw [h a ha]
  · have hz : p a = 0 := by rwa [PMF.mem_support_iff, not_not] at ha
    rw [hz]
    simp

/-- A scheduler-support pair is present in the configuration (`interactionCount > 0` forces the
pair multiset below `mc`). -/
theorem support_pair_le (mc : Config (MarkedAgent L K)) (h : 2 ≤ mc.card)
    (pr : MarkedAgent L K × MarkedAgent L K)
    (hpr : pr ∈ (mc.interactionPMF h).support) :
    ({pr.1, pr.2} : Multiset (MarkedAgent L K)) ≤ mc := by
  classical
  have hprob : mc.interactionProb pr.1 pr.2 ≠ 0 := hpr
  have hcount : mc.interactionCount pr.1 pr.2 ≠ 0 := by
    intro hc
    apply hprob
    unfold Config.interactionProb
    rw [hc]
    simp
  rw [Multiset.le_iff_count]
  intro m
  have hcnt : Multiset.count m ({pr.1, pr.2} : Multiset (MarkedAgent L K))
      = (if m = pr.1 then 1 else 0) + (if m = pr.2 then 1 else 0) := by
    rw [show ({pr.1, pr.2} : Multiset (MarkedAgent L K)) = pr.1 ::ₘ {pr.2} from rfl,
      Multiset.count_cons, Multiset.count_singleton]
    ring
  rw [hcnt]
  show _ ≤ Multiset.count m mc
  by_cases h12 : pr.1 = pr.2
  · -- diagonal: interactionCount = c(c−1) ≠ 0 forces c ≥ 2.
    unfold Config.interactionCount at hcount
    rw [if_pos h12] at hcount
    have hc2 : 2 ≤ Multiset.count pr.1 mc := by
      show 2 ≤ mc.count pr.1
      by_contra hlt
      have h01 : mc.count pr.1 = 0 ∨ mc.count pr.1 = 1 := by omega
      rcases h01 with h0 | h0 <;> rw [h0] at hcount <;> simp at hcount
    by_cases hm : m = pr.1
    · rw [if_pos hm, if_pos (hm.trans h12), hm]
      omega
    · rw [if_neg hm, if_neg (fun hc => hm (hc.trans h12.symm))]
      simp
  · -- off-diagonal: both counts ≥ 1.
    unfold Config.interactionCount at hcount
    rw [if_neg h12] at hcount
    have hc1 : 1 ≤ Multiset.count pr.1 mc := by
      show 1 ≤ mc.count pr.1
      by_contra hlt
      have h0 : mc.count pr.1 = 0 := by omega
      rw [h0] at hcount
      simp at hcount
    have hc2 : 1 ≤ Multiset.count pr.2 mc := by
      show 1 ≤ mc.count pr.2
      by_contra hlt
      have h0 : mc.count pr.2 = 0 := by omega
      rw [h0] at hcount
      simp at hcount
    by_cases hm1 : m = pr.1
    · rw [if_pos hm1, if_neg (fun hc => h12 (hm1.symm.trans hc)), hm1]
      omega
    · by_cases hm2 : m = pr.2
      · rw [if_neg hm1, if_pos hm2, hm2]
        omega
      · rw [if_neg hm1, if_neg hm2]
        simp

/-- **The step projects**: erasing the marked pair update gives the real scheduled step on the
erased configuration and erased pair (the marks only ride along). -/
theorem erase_markedStep (T θn : ℕ) (mc : Config (MarkedAgent L K))
    (pr : MarkedAgent L K × MarkedAgent L K)
    (happ : ({pr.1, pr.2} : Multiset (MarkedAgent L K)) ≤ mc) :
    eraseConfig (L := L) (K := K) (markedStep (L := L) (K := K) T θn mc pr)
      = Protocol.scheduledStep (NonuniformMajority L K)
          (eraseConfig (L := L) (K := K) mc) (pr.1.1, pr.2.1) := by
  classical
  obtain ⟨rest, hrest⟩ : ∃ rest, mc = rest + {pr.1, pr.2} :=
    ⟨mc - {pr.1, pr.2}, (tsub_add_cancel_of_le happ).symm⟩
  have hmap_pair : Multiset.map Prod.fst ({pr.1, pr.2} : Multiset (MarkedAgent L K))
      = ({pr.1.1, pr.2.1} : Multiset (AgentState L K)) := by
    rw [show ({pr.1, pr.2} : Multiset (MarkedAgent L K)) = pr.1 ::ₘ {pr.2} from rfl,
      Multiset.map_cons, Multiset.map_singleton]
    rfl
  have herase : eraseConfig (L := L) (K := K) mc
      = Multiset.map Prod.fst rest + ({pr.1.1, pr.2.1} : Multiset (AgentState L K)) := by
    rw [show eraseConfig (L := L) (K := K) mc = Multiset.map Prod.fst mc from rfl,
      hrest, Multiset.map_add, hmap_pair]
  have happ' : Protocol.Applicable (eraseConfig (L := L) (K := K) mc) pr.1.1 pr.2.1 := by
    show ({pr.1.1, pr.2.1} : Multiset (AgentState L K))
      ≤ eraseConfig (L := L) (K := K) mc
    rw [herase]
    exact Multiset.le_add_left _ _
  -- the real side, in rest-decomposed form.
  have hreal : Protocol.scheduledStep (NonuniformMajority L K)
      (eraseConfig (L := L) (K := K) mc) (pr.1.1, pr.2.1)
      = Multiset.map Prod.fst rest
          + {(Transition L K pr.1.1 pr.2.1).1, (Transition L K pr.1.1 pr.2.1).2} := by
    unfold Protocol.scheduledStep Protocol.stepOrSelf
    rw [if_pos happ']
    have hδ : (NonuniformMajority L K).δ pr.1.1 pr.2.1 = Transition L K pr.1.1 pr.2.1 := rfl
    rw [show ((pr.1.1, pr.2.1) : AgentState L K × AgentState L K).1 = pr.1.1 from rfl,
      show ((pr.1.1, pr.2.1) : AgentState L K × AgentState L K).2 = pr.2.1 from rfl, hδ]
    rw [herase, add_tsub_cancel_right]
  -- the marked side, erased.
  have hmarked : markedStep (L := L) (K := K) T θn mc pr
      = rest + {(markedOut (L := L) (K := K) T
            (preBulkGate (L := L) (K := K) T θn mc) pr.1 pr.2).1,
          (markedOut (L := L) (K := K) T
            (preBulkGate (L := L) (K := K) T θn mc) pr.1 pr.2).2} := by
    unfold markedStep
    rw [if_pos happ, hrest, add_tsub_cancel_right]
  rw [hmarked, hreal]
  show Multiset.map Prod.fst _ = _
  rw [Multiset.map_add]
  congr 1

/-! ## Part 4 — the kernel projection and its powers. -/

/-- **The one-step projection**: the erased marked kernel IS the real kernel of the erased
configuration. -/
theorem markedK_map_erase (T θn : ℕ) (mc : Config (MarkedAgent L K)) :
    Measure.map (eraseConfig (L := L) (K := K)) (markedK (L := L) (K := K) T θn mc)
      = (NonuniformMajority L K).transitionKernel (eraseConfig (L := L) (K := K) mc) := by
  classical
  have herase_meas : Measurable (eraseConfig (L := L) (K := K)) := Measurable.of_discrete
  show Measure.map (eraseConfig (L := L) (K := K))
      (markedPMF (L := L) (K := K) T θn mc).toMeasure
    = ((NonuniformMajority L K).stepDistOrSelf
        (eraseConfig (L := L) (K := K) mc)).toMeasure
  rw [show Measure.map (eraseConfig (L := L) (K := K))
      (markedPMF (L := L) (K := K) T θn mc).toMeasure
    = ((markedPMF (L := L) (K := K) T θn mc).map
        (eraseConfig (L := L) (K := K))).toMeasure from
    PMF.toMeasure_map _ _ herase_meas]
  congr 1
  -- the PMF-level projection.
  unfold markedPMF Protocol.stepDistOrSelf
  by_cases h : 2 ≤ mc.card
  · have h' : 2 ≤ (eraseConfig (L := L) (K := K) mc).card := by
      rw [eraseConfig_card]; exact h
    rw [dif_pos h, dif_pos h']
    unfold Protocol.stepDist
    rw [PMF.map_comp]
    rw [← interactionPMF_map_proj (L := L) (K := K) mc h h', PMF.map_comp]
    apply pmf_map_congr
    intro pr hpr
    show eraseConfig (L := L) (K := K) (markedStep (L := L) (K := K) T θn mc pr)
      = Protocol.scheduledStep (NonuniformMajority L K)
          (eraseConfig (L := L) (K := K) mc) (pr.1.1, pr.2.1)
    exact erase_markedStep (L := L) (K := K) T θn mc pr
      (support_pair_le (L := L) (K := K) mc h pr hpr)
  · have h' : ¬ 2 ≤ (eraseConfig (L := L) (K := K) mc).card := by
      rw [eraseConfig_card]; exact h
    rw [dif_neg h, dif_neg h']
    show (PMF.pure mc).map (eraseConfig (L := L) (K := K))
      = PMF.pure (eraseConfig (L := L) (K := K) mc)
    rw [← PMF.bind_pure_comp, PMF.pure_bind]
    rfl

/-- **The powered projection (the formal bridge).**  The marked chain projects exactly onto the
real chain at every horizon: for any event `A` of the REAL configuration,

  `(markedK^t) mc₀ (erase⁻¹ A) = (K^t) (erase mc₀) A`.

Every marked-world high-probability statement about erased events transfers verbatim. -/
theorem markedK_pow_erase (T θn : ℕ) (t : ℕ) (mc₀ : Config (MarkedAgent L K))
    (A : Set (Config (AgentState L K))) :
    ((markedK (L := L) (K := K) T θn) ^ t) mc₀
        (eraseConfig (L := L) (K := K) ⁻¹' A)
      = ((NonuniformMajority L K).transitionKernel ^ t)
          (eraseConfig (L := L) (K := K) mc₀) A := by
  classical
  have herase_meas : Measurable (eraseConfig (L := L) (K := K)) := Measurable.of_discrete
  have hA_meas : MeasurableSet A := DiscreteMeasurableSpace.forall_measurableSet _
  induction t generalizing mc₀ with
  | zero =>
      rw [pow_zero, pow_zero]
      change (Kernel.id mc₀) (eraseConfig (L := L) (K := K) ⁻¹' A)
        = (Kernel.id (eraseConfig (L := L) (K := K) mc₀)) A
      rw [Kernel.id_apply, Kernel.id_apply,
        Measure.dirac_apply' _ (DiscreteMeasurableSpace.forall_measurableSet _),
        Measure.dirac_apply' _ hA_meas]
      simp [Set.indicator_apply, Set.mem_preimage]
  | succ t ih =>
      rw [show t + 1 = 1 + t from by ring,
        Kernel.pow_add_apply_eq_lintegral _ 1 t mc₀
          (DiscreteMeasurableSpace.forall_measurableSet _),
        Kernel.pow_add_apply_eq_lintegral _ 1 t (eraseConfig (L := L) (K := K) mc₀) hA_meas,
        pow_one, pow_one]
      calc ∫⁻ mc', ((markedK (L := L) (K := K) T θn) ^ t) mc'
            (eraseConfig (L := L) (K := K) ⁻¹' A)
            ∂(markedK (L := L) (K := K) T θn mc₀)
          = ∫⁻ mc', ((NonuniformMajority L K).transitionKernel ^ t)
              (eraseConfig (L := L) (K := K) mc') A
              ∂(markedK (L := L) (K := K) T θn mc₀) := by
            apply lintegral_congr_ae
            filter_upwards with mc'
            exact ih mc'
        _ = ∫⁻ c', ((NonuniformMajority L K).transitionKernel ^ t) c' A
              ∂(Measure.map (eraseConfig (L := L) (K := K))
                (markedK (L := L) (K := K) T θn mc₀)) := by
            rw [lintegral_map (Measurable.of_discrete) herase_meas]
        _ = ∫⁻ c', ((NonuniformMajority L K).transitionKernel ^ t) c' A
              ∂((NonuniformMajority L K).transitionKernel
                (eraseConfig (L := L) (K := K) mc₀)) := by
            rw [markedK_map_erase (L := L) (K := K) T θn mc₀]

/-! ## Part 5 — the taint count, the mark invariant, and the within-gate purity.

The taint count `taintedCount` is Doty's `|D|`.  Two deterministic facts make it usable:
* the DECOMPOSITION: above-`T` clocks split exactly into tainted + clean
  (`aboveCount = taintedCount + cleanAbove`, given the mark invariant);
* the WITHIN-GATE PURITY: while the pre-bulk gate holds, `cleanAbove` stays `0` — every above-`T`
  agent is tainted (the paper's base case "for `c_{≥i} < n^{-0.45}` the statement holds by
  definition of `d`").  This is DETERMINISTIC on the one-step support: a clean above-`T` output
  would need a clean above-`T` ancestor (branches 2/4 of the mark rule), a closed gate (branch 3),
  or a sub-`T` minute (branch 1) — all excluded. -/

/-- Doty's `|D|`: the number of tainted agents. -/
def taintedCount (mc : Config (MarkedAgent L K)) : ℕ :=
  Multiset.countP (fun m => m.2 = true) mc

/-- The number of agents above level `T` (raw minute count, role-free). -/
def aboveCount (T : ℕ) (mc : Config (MarkedAgent L K)) : ℕ :=
  Multiset.countP (fun m : MarkedAgent L K => T + 1 ≤ m.1.minute.val) mc

/-- The number of CLEAN agents above level `T`. -/
def cleanAbove (T : ℕ) (mc : Config (MarkedAgent L K)) : ℕ :=
  Multiset.countP (fun m : MarkedAgent L K => T + 1 ≤ m.1.minute.val ∧ m.2 = false) mc

/-- **The mark invariant**: tainted agents live above level `T`. -/
def MarkInv (T : ℕ) (mc : Config (MarkedAgent L K)) : Prop :=
  ∀ m ∈ mc, m.2 = true → T + 1 ≤ m.1.minute.val

/-- The mark rule only marks above-`T` outputs. -/
theorem markFor_true_above (T : ℕ) (g : Bool) (own partner : MarkedAgent L K)
    (o : AgentState L K) (h : markFor (L := L) (K := K) T g own partner o = true) :
    T + 1 ≤ o.minute.val := by
  unfold markFor at h
  split_ifs at h with h1
  all_goals first
    | omega
    | exact absurd h (by simp)

/-- **The mark invariant is preserved** on the one-step support (unconditionally — the mark rule
guards it by construction). -/
theorem markInv_step (T θn : ℕ) (mc mc' : Config (MarkedAgent L K))
    (hinv : MarkInv (L := L) (K := K) T mc)
    (hsupp : mc' ∈ (markedPMF (L := L) (K := K) T θn mc).support) :
    MarkInv (L := L) (K := K) T mc' := by
  classical
  unfold markedPMF at hsupp
  by_cases h : 2 ≤ mc.card
  · rw [dif_pos h] at hsupp
    rw [PMF.support_map] at hsupp
    obtain ⟨pr, _, hpr⟩ := hsupp
    subst hpr
    unfold markedStep
    by_cases happ : ({pr.1, pr.2} : Multiset (MarkedAgent L K)) ≤ mc
    · rw [if_pos happ]
      intro m hm hmark
      rw [Multiset.mem_add] at hm
      rcases hm with hm | hm
      · exact hinv m (Multiset.mem_of_le (tsub_le_self (a := mc)) hm) hmark
      · rw [show ({(markedOut (L := L) (K := K) T
            (preBulkGate (L := L) (K := K) T θn mc) pr.1 pr.2).1,
            (markedOut (L := L) (K := K) T
              (preBulkGate (L := L) (K := K) T θn mc) pr.1 pr.2).2}
            : Multiset (MarkedAgent L K))
          = (markedOut (L := L) (K := K) T
              (preBulkGate (L := L) (K := K) T θn mc) pr.1 pr.2).1 ::ₘ
            {(markedOut (L := L) (K := K) T
              (preBulkGate (L := L) (K := K) T θn mc) pr.1 pr.2).2} from rfl] at hm
        rcases Multiset.mem_cons.mp hm with hm | hm
        · rw [hm] at hmark ⊢
          exact markFor_true_above (L := L) (K := K) T _ pr.1 pr.2 _ hmark
        · rw [Multiset.mem_singleton.mp hm] at hmark ⊢
          exact markFor_true_above (L := L) (K := K) T _ pr.2 pr.1 _ hmark
    · rw [if_neg happ]
      exact hinv
  · rw [dif_neg h, PMF.support_pure] at hsupp
    rw [Set.mem_singleton_iff.mp hsupp]
    exact hinv

/-- **The decomposition**: under the mark invariant, the above-`T` agents split exactly into
tainted + clean: `aboveCount = taintedCount + cleanAbove`. -/
theorem aboveCount_eq_tainted_add_clean (T : ℕ) (mc : Config (MarkedAgent L K))
    (hinv : MarkInv (L := L) (K := K) T mc) :
    aboveCount (L := L) (K := K) T mc
      = taintedCount (L := L) (K := K) mc + cleanAbove (L := L) (K := K) T mc := by
  classical
  unfold aboveCount taintedCount cleanAbove
  induction mc using Multiset.induction_on with
  | empty => simp
  | cons m mc ih =>
      have hinv' : MarkInv (L := L) (K := K) T mc := by
        intro x hx hxm
        exact hinv x (Multiset.mem_cons_of_mem hx) hxm
      have hm := hinv m (Multiset.mem_cons_self m mc)
      rw [Multiset.countP_cons, Multiset.countP_cons, Multiset.countP_cons, ih hinv']
      rcases hb : m.2 with _ | _
      · -- clean agent: contributes to above iff clean-above.
        simp only [hb]
        by_cases habove : T + 1 ≤ m.1.minute.val
        · simp [habove]
          omega
        · simp [habove]
      · -- tainted agent: above by the invariant; contributes to above + tainted, not clean.
        have habove : T + 1 ≤ m.1.minute.val := hm hb
        simp only [hb]
        simp [habove]
        omega

/-- The above-`T` clock count of the erased configuration is the marked above-count, on the
`AllClockP3` window (all agents are clocks). -/
theorem rBeyond_erase_eq_aboveCount (T : ℕ) (mc : Config (MarkedAgent L K))
    (hw : AllClockP3 (L := L) (K := K) (eraseConfig (L := L) (K := K) mc)) :
    rBeyond (L := L) (K := K) (T + 1) (eraseConfig (L := L) (K := K) mc)
      = aboveCount (L := L) (K := K) T mc := by
  classical
  unfold rBeyond eraseConfig aboveCount
  rw [Multiset.countP_map, Multiset.countP_eq_card_filter]
  congr 1
  apply Multiset.filter_congr
  intro m hm
  have hrole := hw m.1 (by
    unfold eraseConfig
    exact Multiset.mem_map_of_mem Prod.fst hm)
  unfold clockBeyondP
  constructor
  · rintro ⟨_, hmin⟩
    exact hmin
  · intro hmin
    exact ⟨hrole.1, hmin⟩

/-- The Phase-3 SYNC characterization: a clock-clock pair at DIFFERENT minutes synchronizes both
outputs to the max minute. -/
theorem transition_p3_sync_minute (s t : AgentState L K)
    (hsc : s.role = .clock) (htc : t.role = .clock)
    (hs3 : s.phase.val = 3) (ht3 : t.phase.val = 3)
    (hne : s.minute ≠ t.minute) :
    (Transition L K s t).1.minute = max s.minute t.minute ∧
      (Transition L K s t).2.minute = max s.minute t.minute := by
  classical
  have hout := HourCoupling.phase3_clock_out_phase_le_four (L := L) (K := K) s t hsc htc hs3 ht3
  have heq := HourCoupling.transition_eq_phase3 (L := L) (K := K) s t hs3 ht3
    (by rcases hout.1 with h | h <;> omega)
    (by rcases hout.2 with h | h <;> omega)
  rw [heq]
  have hP3 : Phase3Transition L K s t =
      ({ s with minute := max s.minute t.minute },
        { t with minute := max s.minute t.minute }) := by
    unfold Phase3Transition
    simp only [hsc, htc, and_self, if_true, if_neg hne, ne_eq, hne,
      not_false_eq_true, reduceCtorEq, false_and, and_false, if_false]
  rw [hP3]
  exact ⟨rfl, rfl⟩

/-- **The within-gate purity is absorbing** (deterministic, on the one-step support): on the
`AllClockP3` window, while the pre-bulk gate holds and there is no clean agent above `T`, one step
cannot create one — a clean above-`T` output would need a clean above-`T` ancestor (mark-rule
branches 2/4), a closed gate (branch 3), or a sub-`T+1` minute (branch 1). -/
theorem cleanAbove_zero_step (T θn : ℕ) (mc mc' : Config (MarkedAgent L K))
    (hw : AllClockP3 (L := L) (K := K) (eraseConfig (L := L) (K := K) mc))
    (hgate : preBulkGate (L := L) (K := K) T θn mc = true)
    (hclean : cleanAbove (L := L) (K := K) T mc = 0)
    (hsupp : mc' ∈ (markedPMF (L := L) (K := K) T θn mc).support) :
    cleanAbove (L := L) (K := K) T mc' = 0 := by
  classical
  have hnotclean : ∀ m ∈ mc, ¬ (T + 1 ≤ m.1.minute.val ∧ m.2 = false) := by
    intro m hm hcontra
    have : 0 < cleanAbove (L := L) (K := K) T mc :=
      Multiset.countP_pos.mpr ⟨m, hm, hcontra⟩
    omega
  unfold markedPMF at hsupp
  by_cases h : 2 ≤ mc.card
  · rw [dif_pos h] at hsupp
    rw [PMF.support_map] at hsupp
    obtain ⟨pr, _, hpr⟩ := hsupp
    subst hpr
    unfold markedStep
    by_cases happ : ({pr.1, pr.2} : Multiset (MarkedAgent L K)) ≤ mc
    · rw [if_pos happ]
      unfold cleanAbove
      rw [Multiset.countP_eq_zero]
      intro m hm hcontra
      rw [Multiset.mem_add] at hm
      rcases hm with hm | hm
      · exact hnotclean m (Multiset.mem_of_le (tsub_le_self (a := mc)) hm) hcontra
      · -- m is one of the two outputs; analyse the mark rule.
        have hmem1 : pr.1 ∈ mc := Multiset.mem_of_le happ (Multiset.mem_cons_self _ _)
        have hmem2 : pr.2 ∈ mc := Multiset.mem_of_le happ
          (Multiset.mem_cons_of_mem (Multiset.mem_singleton_self _))
        have h1cp := hw pr.1.1 (Multiset.mem_map_of_mem Prod.fst hmem1)
        have h2cp := hw pr.2.1 (Multiset.mem_map_of_mem Prod.fst hmem2)
        -- the generic per-output argument, symmetric in the positions.
        have key : ∀ own partner : MarkedAgent L K, own ∈ mc → partner ∈ mc →
            own.1.role = .clock → partner.1.role = .clock →
            own.1.phase.val = 3 → partner.1.phase.val = 3 →
            ∀ o : AgentState L K,
              (own.1.minute ≠ partner.1.minute →
                o.minute = max own.1.minute partner.1.minute) →
              T + 1 ≤ o.minute.val →
              markFor (L := L) (K := K) T
                (preBulkGate (L := L) (K := K) T θn mc) own partner o = false → False := by
          intro own partner hownm hpartm _ _ _ _ o hsync habove hmark
          unfold markFor at hmark
          split_ifs at hmark with hb1 hb2 hb3
          · omega
          · -- branch 2: own above with mark false → own was clean above.
            exact hnotclean own hownm ⟨hb2, hmark⟩
          · -- branch 3: the gate value is `true`, contradiction with mark false.
            rw [hgate] at hmark
            exact absurd hmark (by simp)
          · -- branch 4: sync crossing — the partner is the above-`T` leader, clean: contradiction.
            have hmax := hsync hb3
            have hpartner_above : T + 1 ≤ partner.1.minute.val := by
              rcases le_total own.1.minute partner.1.minute with hle | hle
              · rw [max_eq_right hle] at hmax
                rw [hmax] at habove
                exact habove
              · rw [max_eq_left hle] at hmax
                rw [hmax] at habove
                omega
            exact hnotclean partner hpartm ⟨hpartner_above, hmark⟩
        rw [show ({(markedOut (L := L) (K := K) T
            (preBulkGate (L := L) (K := K) T θn mc) pr.1 pr.2).1,
            (markedOut (L := L) (K := K) T
              (preBulkGate (L := L) (K := K) T θn mc) pr.1 pr.2).2}
            : Multiset (MarkedAgent L K))
          = (markedOut (L := L) (K := K) T
              (preBulkGate (L := L) (K := K) T θn mc) pr.1 pr.2).1 ::ₘ
            {(markedOut (L := L) (K := K) T
              (preBulkGate (L := L) (K := K) T θn mc) pr.1 pr.2).2} from rfl] at hm
        rcases Multiset.mem_cons.mp hm with hm | hm
        · -- position 1: own = pr.1, o = (Transition pr.1.1 pr.2.1).1.
          refine key pr.1 pr.2 hmem1 hmem2 h1cp.1 h2cp.1 h1cp.2 h2cp.2
            (Transition L K pr.1.1 pr.2.1).1 ?_ ?_ ?_
          · intro hne
            exact (transition_p3_sync_minute (L := L) (K := K) pr.1.1 pr.2.1
              h1cp.1 h2cp.1 h1cp.2 h2cp.2 hne).1
          · rw [hm] at hcontra
            exact hcontra.1
          · rw [hm] at hcontra
            exact hcontra.2
        · -- position 2: own = pr.2, o = (Transition pr.1.1 pr.2.1).2.
          rw [Multiset.mem_singleton.mp hm] at hcontra
          refine key pr.2 pr.1 hmem2 hmem1 h2cp.1 h1cp.1 h2cp.2 h1cp.2
            (Transition L K pr.1.1 pr.2.1).2 ?_ hcontra.1 hcontra.2
          intro hne
          rw [max_comm pr.2.1.minute pr.1.1.minute]
          exact (transition_p3_sync_minute (L := L) (K := K) pr.1.1 pr.2.1
            h1cp.1 h2cp.1 h1cp.2 h2cp.2 (fun hc => hne hc.symm)).2
    · rw [if_neg happ]
      exact hclean
  · rw [dif_neg h, PMF.support_pure] at hsupp
    rw [Set.mem_singleton_iff.mp hsupp]
    exact hclean

/-! ## Part 6 — the taint-count rise structure: at most one new mark per step.

A marked output is either INHERITED (its agent was already above `T` and marked) or a CROSSING
(its agent moved from below `T+1` to above).  At most one position of a pair can cross — so the
taint count rises by at most one per step.  This feeds the MGF engine (brick 1 / `mgf_one_step`). -/

/-- A marked output is inherited or a crossing (the mark rule self-guards: the crossing branches
require `own < T+1 ≤ o`). -/
theorem markFor_true_cases (T : ℕ) (g : Bool) (own partner : MarkedAgent L K)
    (o : AgentState L K) (h : markFor (L := L) (K := K) T g own partner o = true) :
    (T + 1 ≤ own.1.minute.val ∧ own.2 = true) ∨
      (own.1.minute.val < T + 1 ∧ T + 1 ≤ o.minute.val) := by
  unfold markFor at h
  split_ifs at h with h1 h2 h3
  · exact Or.inl ⟨h2, h⟩
  · exact Or.inr ⟨by omega, by omega⟩
  · exact Or.inr ⟨by omega, by omega⟩

/-- **At most one position of a Phase-3 clock pair can cross above `T`** in one step: a drip moves
only the first position, a sync caps both outputs at the max input minute (below `T+1` when both
inputs are), and the synced-at-cap counter moves no minute. -/
theorem at_most_one_crossing (T : ℕ) (s t : AgentState L K)
    (hsc : s.role = .clock) (htc : t.role = .clock)
    (hs3 : s.phase.val = 3) (ht3 : t.phase.val = 3) :
    ¬ ((s.minute.val < T + 1 ∧ T + 1 ≤ (Transition L K s t).1.minute.val) ∧
        (t.minute.val < T + 1 ∧ T + 1 ≤ (Transition L K s t).2.minute.val)) := by
  classical
  rintro ⟨⟨hs_lo, hs_hi⟩, ⟨ht_lo, ht_hi⟩⟩
  have hout := HourCoupling.phase3_clock_out_phase_le_four (L := L) (K := K) s t hsc htc hs3 ht3
  have heq := HourCoupling.transition_eq_phase3 (L := L) (K := K) s t hs3 ht3
    (by rcases hout.1 with h | h <;> omega)
    (by rcases hout.2 with h | h <;> omega)
  rw [heq] at hs_hi ht_hi
  by_cases hmin : s.minute = t.minute
  · by_cases hcap : s.minute.val < K * (L + 1)
    · -- DRIP: the second output is `t` unchanged — it cannot cross.
      have hcap_t : t.minute.val < K * (L + 1) := by simpa [hmin] using hcap
      have hP3 : Phase3Transition L K s t =
          ({ s with minute := ⟨s.minute.val + 1, by omega⟩ }, t) := by
        unfold Phase3Transition
        simp only [hsc, htc, and_self, if_true, hmin, ne_eq, not_true_eq_false,
          if_false, hcap, hcap_t, ↓reduceDIte, reduceCtorEq, false_and, and_false, true_and,
          if_false]
      rw [hP3] at ht_hi
      simp at ht_hi
      omega
    · -- COUNTER: minutes unchanged — the first output cannot cross.
      have hsc' := stdCounterSubroutine_clock_minute (L := L) (K := K) s hsc (by omega)
      have htc' := stdCounterSubroutine_clock_minute (L := L) (K := K) t htc (by omega)
      have hcap_t : ¬ t.minute.val < K * (L + 1) := by simpa [hmin] using hcap
      have hP3 : Phase3Transition L K s t =
          (stdCounterSubroutine L K s, stdCounterSubroutine L K t) := by
        unfold Phase3Transition
        simp only [hsc, htc, and_self, if_true, hmin, ne_eq, not_true_eq_false,
          if_false, hcap, hcap_t, dif_neg, not_false_eq_true]
        simp only [hsc'.1, htc'.1, reduceCtorEq, false_and, if_false, and_false]
      rw [hP3] at hs_hi
      simp only at hs_hi
      rw [hsc'.2] at hs_hi
      omega
  · -- SYNC: both outputs at the max input minute, below `T+1` when both inputs are.
    have hsync := transition_p3_sync_minute (L := L) (K := K) s t hsc htc hs3 ht3 hmin
    rw [heq] at hsync
    rw [hsync.1] at hs_hi
    have hmax : (max s.minute t.minute).val ≤ max s.minute.val t.minute.val := by
      rcases le_total s.minute t.minute with h | h
      · rw [max_eq_right h]; exact le_max_right _ _
      · rw [max_eq_left h]; exact le_max_left _ _
    omega

/-- **The taint count rises by at most one per step** on the `AllClockP3` window with the mark
invariant: each marked output is inherited (from a marked input occupying the same position) or a
crossing, and at most one position crosses. -/
theorem taintedCount_le_succ_on_support (T θn : ℕ) (mc mc' : Config (MarkedAgent L K))
    (hw : AllClockP3 (L := L) (K := K) (eraseConfig (L := L) (K := K) mc))
    (hsupp : mc' ∈ (markedPMF (L := L) (K := K) T θn mc).support) :
    taintedCount (L := L) (K := K) mc' ≤ taintedCount (L := L) (K := K) mc + 1 := by
  classical
  unfold markedPMF at hsupp
  by_cases h : 2 ≤ mc.card
  · rw [dif_pos h] at hsupp
    rw [PMF.support_map] at hsupp
    obtain ⟨pr, _, hpr⟩ := hsupp
    subst hpr
    unfold markedStep
    by_cases happ : ({pr.1, pr.2} : Multiset (MarkedAgent L K)) ≤ mc
    · rw [if_pos happ]
      have hmem1 : pr.1 ∈ mc := Multiset.mem_of_le happ (Multiset.mem_cons_self _ _)
      have hmem2 : pr.2 ∈ mc := Multiset.mem_of_le happ
        (Multiset.mem_cons_of_mem (Multiset.mem_singleton_self _))
      have h1cp := hw pr.1.1 (Multiset.mem_map_of_mem Prod.fst hmem1)
      have h2cp := hw pr.2.1 (Multiset.mem_map_of_mem Prod.fst hmem2)
      unfold taintedCount
      rw [Multiset.countP_add, Multiset.countP_sub happ]
      have hpair_le : Multiset.countP (fun m : MarkedAgent L K => m.2 = true)
          ({pr.1, pr.2} : Multiset (MarkedAgent L K))
            ≤ Multiset.countP (fun m : MarkedAgent L K => m.2 = true) mc :=
        Multiset.countP_le_of_le _ happ
      -- the two-element countP evaluations.
      have hcountP2 : ∀ x y : MarkedAgent L K,
          Multiset.countP (fun m : MarkedAgent L K => m.2 = true)
              ({x, y} : Multiset (MarkedAgent L K))
            = (if x.2 = true then 1 else 0) + (if y.2 = true then 1 else 0) := by
        intro x y
        rw [show ({x, y} : Multiset (MarkedAgent L K)) = x ::ₘ y ::ₘ 0 from rfl]
        rw [Multiset.countP_cons, Multiset.countP_cons, Multiset.countP_zero]
        ring
      set g := preBulkGate (L := L) (K := K) T θn mc with hg
      set o₁ := (markedOut (L := L) (K := K) T g pr.1 pr.2).1 with ho₁
      set o₂ := (markedOut (L := L) (K := K) T g pr.1 pr.2).2 with ho₂
      have houts : Multiset.countP (fun m : MarkedAgent L K => m.2 = true)
            ({o₁, o₂} : Multiset (MarkedAgent L K))
          ≤ Multiset.countP (fun m : MarkedAgent L K => m.2 = true)
              ({pr.1, pr.2} : Multiset (MarkedAgent L K)) + 1 := by
        rw [hcountP2, hcountP2]
        -- each marked output is inherited or a crossing; at most one crossing.
        have hmark₁ : o₁.2 = markFor (L := L) (K := K) T g pr.1 pr.2
            (Transition L K pr.1.1 pr.2.1).1 := rfl
        have hmark₂ : o₂.2 = markFor (L := L) (K := K) T g pr.2 pr.1
            (Transition L K pr.1.1 pr.2.1).2 := rfl
        have hcase₁ : o₁.2 = true →
            (T + 1 ≤ pr.1.1.minute.val ∧ pr.1.2 = true) ∨
              (pr.1.1.minute.val < T + 1 ∧
                T + 1 ≤ (Transition L K pr.1.1 pr.2.1).1.minute.val) := by
          intro hm
          rw [hmark₁] at hm
          exact markFor_true_cases (L := L) (K := K) T g pr.1 pr.2 _ hm
        have hcase₂ : o₂.2 = true →
            (T + 1 ≤ pr.2.1.minute.val ∧ pr.2.2 = true) ∨
              (pr.2.1.minute.val < T + 1 ∧
                T + 1 ≤ (Transition L K pr.1.1 pr.2.1).2.minute.val) := by
          intro hm
          rw [hmark₂] at hm
          exact markFor_true_cases (L := L) (K := K) T g pr.2 pr.1 _ hm
        have hone := at_most_one_crossing (L := L) (K := K) T pr.1.1 pr.2.1
          h1cp.1 h2cp.1 h1cp.2 h2cp.2
        by_cases hm₁ : o₁.2 = true <;> by_cases hm₂ : o₂.2 = true
        · -- both outputs marked: not both crossings; an inherited one is matched by its input.
          rcases hcase₁ hm₁ with ⟨_, hin₁⟩ | hcr₁
          · simp [hm₁, hm₂, hin₁] <;> split_ifs <;> omega
          · rcases hcase₂ hm₂ with ⟨_, hin₂⟩ | hcr₂
            · simp [hm₁, hm₂, hin₂] <;> split_ifs <;> omega
            · exact absurd ⟨hcr₁, hcr₂⟩ hone
        · rcases hcase₁ hm₁ with ⟨_, hin₁⟩ | _
          · simp [hm₁, hm₂, hin₁] <;> split_ifs <;> omega
          · simp [hm₁, hm₂] <;> split_ifs <;> omega
        · rcases hcase₂ hm₂ with ⟨_, hin₂⟩ | _
          · simp [hm₁, hm₂, hin₂] <;> split_ifs <;> omega
          · simp [hm₁, hm₂] <;> split_ifs <;> omega
        · simp [hm₁, hm₂] <;> split_ifs <;> omega
      omega
    · rw [if_neg happ]
      omega
  · rw [dif_neg h, PMF.support_pure] at hsupp
    rw [Set.mem_singleton_iff.mp hsupp]
    omega

/-! ## Part 7 — the one-step taint-rise probability: drip-seed plus epidemic-from-tainted.

The taint count rises only by a CROSSING mark, which the mark rule grants in exactly two ways:
* branch 3 (drip seed): the scheduled pair sits at the SAME minute `T` (the crossing drip `T → T+1`)
  — probability at most `(count@T / n)²` (the same-block scheduler bound);
* branch 4 (epidemic): the partner is TAINTED — probability at most `2·taintedCount/n` (the
  marked-member scheduler bound).

So `P[rise] ≤ (count@T/n)² + 2·taintedCount/n` — the seed rate plus the branching rate, exactly the
two-phase structure of Doty's `d`-analysis (brick 3.4c). -/

/-- The block interaction-count sum: ordered pairs inside a state block `S` number exactly
`X·(X−1)`, `X = Σ_{m∈S} count m`. -/
private theorem sum_block_interactionCount (c : Config (MarkedAgent L K))
    (S : Finset (MarkedAgent L K)) :
    (∑ m₁ ∈ S, ∑ m₂ ∈ S, c.interactionCount m₁ m₂)
      = (∑ m ∈ S, c.count m) * ((∑ m ∈ S, c.count m) - 1) := by
  classical
  set X := ∑ m ∈ S, c.count m with hX
  have hrow : ∀ m₁ ∈ S, (∑ m₂ ∈ S, c.interactionCount m₁ m₂) = c.count m₁ * (X - 1) := by
    intro m₁ hm₁
    have hc₁X : c.count m₁ ≤ X := Finset.single_le_sum (fun m _ => Nat.zero_le _) hm₁
    rw [← Finset.add_sum_erase S _ hm₁]
    have hdiag : c.interactionCount m₁ m₁ = c.count m₁ * (c.count m₁ - 1) := by
      unfold Config.interactionCount
      rw [if_pos rfl]
    have hoff : (∑ m₂ ∈ S.erase m₁, c.interactionCount m₁ m₂)
        = c.count m₁ * (X - c.count m₁) := by
      have hsum0 : c.count m₁ + (∑ m₂ ∈ S.erase m₁, c.count m₂) = X := by
        rw [hX]
        exact Finset.add_sum_erase S (fun m => c.count m) hm₁
      have hsum : (∑ m₂ ∈ S.erase m₁, c.count m₂) = X - c.count m₁ := by omega
      rw [← hsum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro m₂ hm₂
      unfold Config.interactionCount
      rw [if_neg (fun hc => (Finset.mem_erase.mp hm₂).1 hc.symm)]
    rw [hdiag, hoff]
    -- c₁(c₁−1) + c₁(X−c₁) = c₁(X−1), ℕ-safe (c₁ ≤ X).
    cases hc₁ : c.count m₁ with
    | zero => simp
    | succ k =>
        have h1X : 1 ≤ X := by omega
        zify [show 1 ≤ k + 1 from by omega, show k + 1 ≤ X from by omega, h1X]
        ring
  rw [Finset.sum_congr rfl hrow, ← Finset.sum_mul]

/-- The total count over the whole state space is the population size. -/
private theorem sum_count_univ_marked (c : Config (MarkedAgent L K)) :
    (∑ m : MarkedAgent L K, c.count m) = c.card :=
  Multiset.sum_count_eq_card (s := (Finset.univ : Finset (MarkedAgent L K)))
    (fun a _ => Finset.mem_univ a)

set_option maxHeartbeats 1000000 in
/-- `countP` as the block count sum. -/
private theorem sum_count_filter_eq_countP (p : MarkedAgent L K → Prop) [DecidablePred p]
    (c : Config (MarkedAgent L K)) :
    (∑ m ∈ Finset.univ.filter p, c.count m) = Multiset.countP p c := by
  classical
  calc (∑ m ∈ Finset.univ.filter p, c.count m)
      = ∑ m : MarkedAgent L K, if p m then c.count m else 0 :=
        Finset.sum_filter _ _
    _ = ∑ m : MarkedAgent L K, (c.filter p).count m := by
        apply Finset.sum_congr rfl
        intro m _
        show _ = Multiset.count m (c.filter p)
        rw [Multiset.count_filter]
        rfl
    _ = (c.filter p).card :=
        Multiset.sum_count_eq_card (fun a _ => Finset.mem_univ a)
    _ = Multiset.countP p c := (Multiset.countP_eq_card_filter _ _).symm

/-- A finite-type PMF `toMeasure` value as the indicator sum over the event. -/
private theorem toMeasure_le_sum_event (p : PMF (MarkedAgent L K × MarkedAgent L K))
    (E : Finset (MarkedAgent L K × MarkedAgent L K)) (Eset : Set (MarkedAgent L K × MarkedAgent L K))
    (hsub : Eset ⊆ ↑E) :
    p.toMeasure Eset ≤ ∑ pr ∈ E, p pr := by
  calc p.toMeasure Eset ≤ p.toMeasure ↑E := by
        apply measure_mono hsub
    _ = ∑ pr ∈ E, p pr := by
        rw [PMF.toMeasure_apply_finset]

/-- **The same-block pair bound**: the scheduler picks an ordered pair with BOTH states in a block
`S` with probability at most `(X/n)²`, `X` the block count. -/
theorem pair_block_prob_le_sq (c : Config (MarkedAgent L K)) (h : 2 ≤ c.card)
    (S : Finset (MarkedAgent L K)) :
    (c.interactionPMF h).toMeasure {pr | pr.1 ∈ S ∧ pr.2 ∈ S}
      ≤ ENNReal.ofReal ((((∑ m ∈ S, c.count m : ℕ) : ℝ) / (c.card : ℝ)) ^ 2) := by
  classical
  set X := ∑ m ∈ S, c.count m with hX
  have hXn : X ≤ c.card := by
    calc X ≤ ∑ m : MarkedAgent L K, c.count m :=
          Finset.sum_le_sum_of_subset (Finset.subset_univ S)
      _ = c.card := sum_count_univ_marked c
  have hsub : {pr : MarkedAgent L K × MarkedAgent L K | pr.1 ∈ S ∧ pr.2 ∈ S}
      ⊆ ↑(S ×ˢ S) := by
    rintro pr ⟨h1, h2⟩
    rw [Finset.coe_product]
    exact ⟨h1, h2⟩
  refine le_trans (toMeasure_le_sum_event (c.interactionPMF h) (S ×ˢ S) _ hsub) ?_
  -- Σ over the block of interactionProb = X(X−1)/tp ≤ (X/n)².
  have hval : (∑ pr ∈ S ×ˢ S, (c.interactionPMF h) pr)
      = ((X * (X - 1) : ℕ) : ℝ≥0∞) / ((c.totalPairs : ℕ) : ℝ≥0∞) := by
    rw [Finset.sum_product]
    calc (∑ m₁ ∈ S, ∑ m₂ ∈ S, (c.interactionPMF h) (m₁, m₂))
        = ∑ m₁ ∈ S, ∑ m₂ ∈ S,
            ((c.interactionCount m₁ m₂ : ℕ) : ℝ≥0∞) * ((c.totalPairs : ℕ) : ℝ≥0∞)⁻¹ := by
          apply Finset.sum_congr rfl
          intro m₁ _
          apply Finset.sum_congr rfl
          intro m₂ _
          show c.interactionProb m₁ m₂ = _
          unfold Config.interactionProb
          rw [div_eq_mul_inv]
      _ = (∑ m₁ ∈ S, ∑ m₂ ∈ S, ((c.interactionCount m₁ m₂ : ℕ) : ℝ≥0∞))
            * ((c.totalPairs : ℕ) : ℝ≥0∞)⁻¹ := by
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro m₁ _
          rw [Finset.sum_mul]
      _ = ((X * (X - 1) : ℕ) : ℝ≥0∞) * ((c.totalPairs : ℕ) : ℝ≥0∞)⁻¹ := by
          congr 1
          calc (∑ m₁ ∈ S, ∑ m₂ ∈ S, ((c.interactionCount m₁ m₂ : ℕ) : ℝ≥0∞))
              = ∑ m₁ ∈ S, ((∑ m₂ ∈ S, c.interactionCount m₁ m₂ : ℕ) : ℝ≥0∞) :=
                Finset.sum_congr rfl (fun m₁ _ => (Nat.cast_sum _ _).symm)
            _ = ((∑ m₁ ∈ S, ∑ m₂ ∈ S, c.interactionCount m₁ m₂ : ℕ) : ℝ≥0∞) :=
                (Nat.cast_sum _ _).symm
            _ = ((X * (X - 1) : ℕ) : ℝ≥0∞) := by
                rw [sum_block_interactionCount c S]
      _ = ((X * (X - 1) : ℕ) : ℝ≥0∞) / ((c.totalPairs : ℕ) : ℝ≥0∞) :=
          (div_eq_mul_inv _ _).symm
  rw [hval]
  -- X(X−1)/(n(n−1)) ≤ (X/n)² over ℝ (X ≤ n, n ≥ 2).
  have hn1 : (1 : ℕ) ≤ c.card - 1 := by omega
  have htp : c.totalPairs = c.card * (c.card - 1) := rfl
  rw [htp]
  rw [show ((X * (X - 1) : ℕ) : ℝ≥0∞) = ENNReal.ofReal ((X * (X - 1) : ℕ) : ℝ) from
    (ENNReal.ofReal_natCast _).symm,
    show ((c.card * (c.card - 1) : ℕ) : ℝ≥0∞)
      = ENNReal.ofReal ((c.card * (c.card - 1) : ℕ) : ℝ) from (ENNReal.ofReal_natCast _).symm]
  rw [← ENNReal.ofReal_div_of_pos (by
    have : 0 < c.card * (c.card - 1) := by
      apply Nat.mul_pos <;> omega
    exact_mod_cast this)]
  apply ENNReal.ofReal_le_ofReal
  have hcard : (2 : ℝ) ≤ (c.card : ℝ) := by exact_mod_cast h
  have hXr : ((X : ℕ) : ℝ) ≤ (c.card : ℝ) := by exact_mod_cast hXn
  by_cases hX0 : X = 0
  · rw [hX0]
    simp
  · have h1X : 1 ≤ X := by omega
    have hdenom : (0 : ℝ) < ((c.card * (c.card - 1) : ℕ) : ℝ) := by
      have : 0 < c.card * (c.card - 1) := by
        apply Nat.mul_pos <;> omega
      exact_mod_cast this
    have hXnn : (0 : ℝ) ≤ ((X : ℕ) : ℝ) := by positivity
    have hnnn : (0 : ℝ) ≤ (c.card : ℝ) := by positivity
    rw [div_pow, div_le_div_iff₀ hdenom (by positivity)]
    push_cast [Nat.cast_sub (show 1 ≤ c.card from by omega), Nat.cast_sub h1X]
    nlinarith [mul_nonneg (mul_nonneg hXnn hnnn) (sub_nonneg.mpr hXr)]

/-- The column interaction-count sum: `Σ_{m₁} icount m₁ m₂ = count m₂ · (n−1)` (the mirror of
`sum_interactionCount_right`). -/
private theorem sum_interactionCount_left (c : Config (MarkedAgent L K))
    (m₂ : MarkedAgent L K) :
    (∑ m₁ : MarkedAgent L K, c.interactionCount m₁ m₂) = c.count m₂ * (c.card - 1) := by
  classical
  have hc₂n : c.count m₂ ≤ c.card := Multiset.count_le_card m₂ c
  rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ m₂)]
  have hdiag : c.interactionCount m₂ m₂ = c.count m₂ * (c.count m₂ - 1) := by
    unfold Config.interactionCount
    rw [if_pos rfl]
  have hoff : (∑ m₁ ∈ Finset.univ.erase m₂, c.interactionCount m₁ m₂)
      = (c.card - c.count m₂) * c.count m₂ := by
    have hsum0 : c.count m₂ + (∑ m₁ ∈ Finset.univ.erase m₂, c.count m₁) = c.card := by
      rw [show (∑ m₁ ∈ Finset.univ.erase m₂, c.count m₁)
          = c.card - c.count m₂ from ?_]
      · omega
      · have h := Finset.add_sum_erase Finset.univ (fun m => c.count m) (Finset.mem_univ m₂)
        have h2 : c.count m₂ + (∑ m₁ ∈ Finset.univ.erase m₂, c.count m₁)
            = ∑ m : MarkedAgent L K, c.count m := h
        rw [sum_count_univ_marked c] at h2
        omega
    have hsum : (∑ m₁ ∈ Finset.univ.erase m₂, c.count m₁) = c.card - c.count m₂ := by omega
    rw [← hsum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro m₁ hm₁
    unfold Config.interactionCount
    rw [if_neg ((Finset.mem_erase.mp hm₁).1)]
  rw [hdiag, hoff]
  cases hc₂ : c.count m₂ with
  | zero => simp
  | succ k =>
      have h1n : 1 ≤ c.card := by omega
      zify [show 1 ≤ k + 1 from by omega, show k + 1 ≤ c.card from by omega, h1n]
      ring

/-- **The first-member block bound**: the scheduler picks an ordered pair whose FIRST state lies in
`S` with probability at most `X/n`. -/
theorem fst_block_prob_le (c : Config (MarkedAgent L K)) (h : 2 ≤ c.card)
    (S : Finset (MarkedAgent L K)) :
    (c.interactionPMF h).toMeasure {pr | pr.1 ∈ S}
      ≤ ENNReal.ofReal ((((∑ m ∈ S, c.count m : ℕ) : ℝ) / (c.card : ℝ))) := by
  classical
  set X := ∑ m ∈ S, c.count m with hX
  have hsub : {pr : MarkedAgent L K × MarkedAgent L K | pr.1 ∈ S}
      ⊆ ↑(S ×ˢ (Finset.univ : Finset (MarkedAgent L K))) := by
    intro pr h1
    rw [Finset.coe_product]
    exact ⟨h1, Finset.mem_coe.mpr (Finset.mem_univ _)⟩
  refine le_trans (toMeasure_le_sum_event (c.interactionPMF h) _ _ hsub) ?_
  have hval : (∑ pr ∈ S ×ˢ (Finset.univ : Finset (MarkedAgent L K)),
      (c.interactionPMF h) pr)
      = ((X * (c.card - 1) : ℕ) : ℝ≥0∞) / ((c.totalPairs : ℕ) : ℝ≥0∞) := by
    rw [Finset.sum_product]
    calc (∑ m₁ ∈ S, ∑ m₂ : MarkedAgent L K, (c.interactionPMF h) (m₁, m₂))
        = ∑ m₁ ∈ S, ∑ m₂ : MarkedAgent L K,
            ((c.interactionCount m₁ m₂ : ℕ) : ℝ≥0∞) * ((c.totalPairs : ℕ) : ℝ≥0∞)⁻¹ := by
          apply Finset.sum_congr rfl
          intro m₁ _
          apply Finset.sum_congr rfl
          intro m₂ _
          show c.interactionProb m₁ m₂ = _
          unfold Config.interactionProb
          rw [div_eq_mul_inv]
      _ = (∑ m₁ ∈ S, ∑ m₂ : MarkedAgent L K,
            ((c.interactionCount m₁ m₂ : ℕ) : ℝ≥0∞)) * ((c.totalPairs : ℕ) : ℝ≥0∞)⁻¹ := by
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro m₁ _
          rw [Finset.sum_mul]
      _ = ((X * (c.card - 1) : ℕ) : ℝ≥0∞) * ((c.totalPairs : ℕ) : ℝ≥0∞)⁻¹ := by
          congr 1
          calc (∑ m₁ ∈ S, ∑ m₂ : MarkedAgent L K,
              ((c.interactionCount m₁ m₂ : ℕ) : ℝ≥0∞))
              = ∑ m₁ ∈ S, ((∑ m₂ : MarkedAgent L K, c.interactionCount m₁ m₂ : ℕ) : ℝ≥0∞) :=
                Finset.sum_congr rfl (fun m₁ _ => (Nat.cast_sum _ _).symm)
            _ = ((∑ m₁ ∈ S, ∑ m₂ : MarkedAgent L K, c.interactionCount m₁ m₂ : ℕ) : ℝ≥0∞) :=
                (Nat.cast_sum _ _).symm
            _ = ((X * (c.card - 1) : ℕ) : ℝ≥0∞) := by
                congr 1
                calc (∑ m₁ ∈ S, ∑ m₂ : MarkedAgent L K, c.interactionCount m₁ m₂)
                    = ∑ m₁ ∈ S, c.count m₁ * (c.card - 1) :=
                      Finset.sum_congr rfl
                        (fun m₁ _ => Config.sum_interactionCount_right c m₁)
                  _ = X * (c.card - 1) := by rw [← Finset.sum_mul]
      _ = ((X * (c.card - 1) : ℕ) : ℝ≥0∞) / ((c.totalPairs : ℕ) : ℝ≥0∞) :=
          (div_eq_mul_inv _ _).symm
  rw [hval]
  have htp : c.totalPairs = c.card * (c.card - 1) := rfl
  rw [htp,
    show ((X * (c.card - 1) : ℕ) : ℝ≥0∞)
      = ENNReal.ofReal ((X * (c.card - 1) : ℕ) : ℝ) from (ENNReal.ofReal_natCast _).symm,
    show ((c.card * (c.card - 1) : ℕ) : ℝ≥0∞)
      = ENNReal.ofReal ((c.card * (c.card - 1) : ℕ) : ℝ) from (ENNReal.ofReal_natCast _).symm]
  rw [← ENNReal.ofReal_div_of_pos (by
    have : 0 < c.card * (c.card - 1) := by
      apply Nat.mul_pos <;> omega
    exact_mod_cast this)]
  apply ENNReal.ofReal_le_ofReal
  -- X(n−1)/(n(n−1)) = X/n exactly.
  have hn1 : (0 : ℝ) < ((c.card - 1 : ℕ) : ℝ) := by
    have : 0 < c.card - 1 := by omega
    exact_mod_cast this
  have hn : (0 : ℝ) < (c.card : ℝ) := by
    have : 0 < c.card := by omega
    exact_mod_cast this
  push_cast
  rw [div_le_div_iff₀ (by positivity) hn]
  ring_nf
  nlinarith [hn1, hn]

/-- **The second-member block bound**: same for the SECOND state of the pair (via the column
sum). -/
theorem snd_block_prob_le (c : Config (MarkedAgent L K)) (h : 2 ≤ c.card)
    (S : Finset (MarkedAgent L K)) :
    (c.interactionPMF h).toMeasure {pr | pr.2 ∈ S}
      ≤ ENNReal.ofReal ((((∑ m ∈ S, c.count m : ℕ) : ℝ) / (c.card : ℝ))) := by
  classical
  set X := ∑ m ∈ S, c.count m with hX
  have hsub : {pr : MarkedAgent L K × MarkedAgent L K | pr.2 ∈ S}
      ⊆ ↑((Finset.univ : Finset (MarkedAgent L K)) ×ˢ S) := by
    intro pr h2
    rw [Finset.coe_product]
    exact ⟨Finset.mem_coe.mpr (Finset.mem_univ _), h2⟩
  refine le_trans (toMeasure_le_sum_event (c.interactionPMF h) _ _ hsub) ?_
  have hval : (∑ pr ∈ (Finset.univ : Finset (MarkedAgent L K)) ×ˢ S,
      (c.interactionPMF h) pr)
      = ((X * (c.card - 1) : ℕ) : ℝ≥0∞) / ((c.totalPairs : ℕ) : ℝ≥0∞) := by
    rw [Finset.sum_product_right]
    calc (∑ m₂ ∈ S, ∑ m₁ : MarkedAgent L K, (c.interactionPMF h) (m₁, m₂))
        = ∑ m₂ ∈ S, ∑ m₁ : MarkedAgent L K,
            ((c.interactionCount m₁ m₂ : ℕ) : ℝ≥0∞) * ((c.totalPairs : ℕ) : ℝ≥0∞)⁻¹ := by
          apply Finset.sum_congr rfl
          intro m₂ _
          apply Finset.sum_congr rfl
          intro m₁ _
          show c.interactionProb m₁ m₂ = _
          unfold Config.interactionProb
          rw [div_eq_mul_inv]
      _ = (∑ m₂ ∈ S, ∑ m₁ : MarkedAgent L K,
            ((c.interactionCount m₁ m₂ : ℕ) : ℝ≥0∞)) * ((c.totalPairs : ℕ) : ℝ≥0∞)⁻¹ := by
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro m₂ _
          rw [Finset.sum_mul]
      _ = ((X * (c.card - 1) : ℕ) : ℝ≥0∞) * ((c.totalPairs : ℕ) : ℝ≥0∞)⁻¹ := by
          congr 1
          calc (∑ m₂ ∈ S, ∑ m₁ : MarkedAgent L K,
              ((c.interactionCount m₁ m₂ : ℕ) : ℝ≥0∞))
              = ∑ m₂ ∈ S, ((∑ m₁ : MarkedAgent L K, c.interactionCount m₁ m₂ : ℕ) : ℝ≥0∞) :=
                Finset.sum_congr rfl (fun m₂ _ => (Nat.cast_sum _ _).symm)
            _ = ((∑ m₂ ∈ S, ∑ m₁ : MarkedAgent L K, c.interactionCount m₁ m₂ : ℕ) : ℝ≥0∞) :=
                (Nat.cast_sum _ _).symm
            _ = ((X * (c.card - 1) : ℕ) : ℝ≥0∞) := by
                congr 1
                calc (∑ m₂ ∈ S, ∑ m₁ : MarkedAgent L K, c.interactionCount m₁ m₂)
                    = ∑ m₂ ∈ S, c.count m₂ * (c.card - 1) :=
                      Finset.sum_congr rfl
                        (fun m₂ _ => sum_interactionCount_left (L := L) (K := K) c m₂)
                  _ = X * (c.card - 1) := by rw [← Finset.sum_mul]
      _ = ((X * (c.card - 1) : ℕ) : ℝ≥0∞) / ((c.totalPairs : ℕ) : ℝ≥0∞) :=
          (div_eq_mul_inv _ _).symm
  rw [hval]
  have htp : c.totalPairs = c.card * (c.card - 1) := rfl
  rw [htp,
    show ((X * (c.card - 1) : ℕ) : ℝ≥0∞)
      = ENNReal.ofReal ((X * (c.card - 1) : ℕ) : ℝ) from (ENNReal.ofReal_natCast _).symm,
    show ((c.card * (c.card - 1) : ℕ) : ℝ≥0∞)
      = ENNReal.ofReal ((c.card * (c.card - 1) : ℕ) : ℝ) from (ENNReal.ofReal_natCast _).symm]
  rw [← ENNReal.ofReal_div_of_pos (by
    have : 0 < c.card * (c.card - 1) := by
      apply Nat.mul_pos <;> omega
    exact_mod_cast this)]
  apply ENNReal.ofReal_le_ofReal
  have hn1 : (0 : ℝ) < ((c.card - 1 : ℕ) : ℝ) := by
    have : 0 < c.card - 1 := by omega
    exact_mod_cast this
  have hn : (0 : ℝ) < (c.card : ℝ) := by
    have : 0 < c.card := by omega
    exact_mod_cast this
  push_cast
  rw [div_le_div_iff₀ (by positivity) hn]
  ring_nf
  nlinarith [hn1, hn]

/-- The marked kernel's one-step measure pulls back to the scheduler pair law. -/
theorem markedK_apply_pair (T θn : ℕ) (mc : Config (MarkedAgent L K)) (h : 2 ≤ mc.card)
    (A : Set (Config (MarkedAgent L K))) (hA : MeasurableSet A) :
    markedK (L := L) (K := K) T θn mc A
      = (mc.interactionPMF h).toMeasure (markedStep (L := L) (K := K) T θn mc ⁻¹' A) := by
  show (markedPMF (L := L) (K := K) T θn mc).toMeasure A = _
  unfold markedPMF
  rw [dif_pos h]
  exact PMF.toMeasure_map_apply _ _ _ (Measurable.of_discrete) hA

/-- The sharp mark-rule case split: a marked output is inherited, a gated drip seed (same-minute
pair), or an epidemic from a tainted partner. -/
theorem markFor_true_crossing_cases (T : ℕ) (g : Bool) (own partner : MarkedAgent L K)
    (o : AgentState L K) (h : markFor (L := L) (K := K) T g own partner o = true) :
    (T + 1 ≤ own.1.minute.val ∧ own.2 = true) ∨
      (own.1.minute.val < T + 1 ∧ T + 1 ≤ o.minute.val ∧
        ((own.1.minute = partner.1.minute ∧ g = true) ∨ partner.2 = true)) := by
  unfold markFor at h
  split_ifs at h with h1 h2 h3
  · exact Or.inl ⟨h2, h⟩
  · exact Or.inr ⟨by omega, by omega, Or.inl ⟨h3, h⟩⟩
  · exact Or.inr ⟨by omega, by omega, Or.inr h⟩

/-- **The taint-rise event is contained in the two scheduler events**: a same-minute-`T` pair (the
gated drip seed) or a pair with a tainted member (the epidemic).  Outside both, one marked step
cannot raise the taint count. -/
theorem tainted_rise_subset (T θn : ℕ) (mc : Config (MarkedAgent L K))
    (hw : AllClockP3 (L := L) (K := K) (eraseConfig (L := L) (K := K) mc)) :
    (markedStep (L := L) (K := K) T θn mc) ⁻¹'
        {mc' | taintedCount (L := L) (K := K) mc < taintedCount (L := L) (K := K) mc'} ⊆
      {pr : MarkedAgent L K × MarkedAgent L K |
          pr.1.1.minute.val = T ∧ pr.2.1.minute.val = T} ∪
        {pr : MarkedAgent L K × MarkedAgent L K | pr.1.2 = true ∨ pr.2.2 = true} := by
  classical
  intro pr hpr
  rw [Set.mem_preimage, Set.mem_setOf_eq] at hpr
  by_contra hnot
  rw [Set.mem_union, Set.mem_setOf_eq, Set.mem_setOf_eq] at hnot
  push Not at hnot
  obtain ⟨hnotT, hm₁false, hm₂false⟩ := hnot
  -- the step cannot raise the count: refute hpr.
  unfold markedStep at hpr
  by_cases happ : ({pr.1, pr.2} : Multiset (MarkedAgent L K)) ≤ mc
  · rw [if_pos happ] at hpr
    have hmem1 : pr.1 ∈ mc := Multiset.mem_of_le happ (Multiset.mem_cons_self _ _)
    have hmem2 : pr.2 ∈ mc := Multiset.mem_of_le happ
      (Multiset.mem_cons_of_mem (Multiset.mem_singleton_self _))
    have h1cp := hw pr.1.1 (Multiset.mem_map_of_mem Prod.fst hmem1)
    have h2cp := hw pr.2.1 (Multiset.mem_map_of_mem Prod.fst hmem2)
    have hminute := ClimbTail.transition_p3_minute_le_succ_max (L := L) (K := K)
      pr.1.1 pr.2.1 h1cp.1 h2cp.1 h1cp.2 h2cp.2
    set g := preBulkGate (L := L) (K := K) T θn mc with hg
    set o₁ := (markedOut (L := L) (K := K) T g pr.1 pr.2).1 with ho₁
    set o₂ := (markedOut (L := L) (K := K) T g pr.1 pr.2).2 with ho₂
    have hmark₁ : o₁.2 = markFor (L := L) (K := K) T g pr.1 pr.2
        (Transition L K pr.1.1 pr.2.1).1 := rfl
    have hmark₂ : o₂.2 = markFor (L := L) (K := K) T g pr.2 pr.1
        (Transition L K pr.1.1 pr.2.1).2 := rfl
    have hno₁ : ¬ (o₁.2 = true) := by
      intro hm
      rw [hmark₁] at hm
      rcases markFor_true_crossing_cases (L := L) (K := K) T g pr.1 pr.2 _ hm with
        ⟨_, hin⟩ | ⟨hlo, hhi, hvia⟩
      · exact hm₁false hin
      · rcases hvia with ⟨hsame, _⟩ | hpart
        · -- gated drip seed: both pair minutes are exactly T.
          have hsame' : pr.1.1.minute.val = pr.2.1.minute.val := by rw [hsame]
          have hmax : max pr.1.1.minute.val pr.2.1.minute.val = pr.1.1.minute.val := by
            rw [← hsame']
            exact max_self _
          have h1T : pr.1.1.minute.val = T := by
            have := hminute.1
            rw [hmax] at this
            omega
          exact hnotT h1T (by omega)
        · exact hm₂false hpart
    have hno₂ : ¬ (o₂.2 = true) := by
      intro hm
      rw [hmark₂] at hm
      rcases markFor_true_crossing_cases (L := L) (K := K) T g pr.2 pr.1 _ hm with
        ⟨_, hin⟩ | ⟨hlo, hhi, hvia⟩
      · exact hm₂false hin
      · rcases hvia with ⟨hsame, _⟩ | hpart
        · have hsame' : pr.2.1.minute.val = pr.1.1.minute.val := by rw [hsame]
          have hmax : max pr.1.1.minute.val pr.2.1.minute.val = pr.2.1.minute.val := by
            rw [hsame']
            exact max_self _
          have h2T : pr.2.1.minute.val = T := by
            have := hminute.2
            rw [hmax] at this
            omega
          exact hnotT (by omega) h2T
        · exact hm₁false hpart
    have houts : Multiset.countP (fun m : MarkedAgent L K => m.2 = true)
        ({o₁, o₂} : Multiset (MarkedAgent L K)) = 0 := by
      rw [Multiset.countP_eq_zero]
      intro m hm
      rw [show ({o₁, o₂} : Multiset (MarkedAgent L K)) = o₁ ::ₘ {o₂} from rfl] at hm
      rcases Multiset.mem_cons.mp hm with hm | hm
      · rw [hm]; exact hno₁
      · rw [Multiset.mem_singleton.mp hm]; exact hno₂
    have hle : taintedCount (L := L) (K := K)
        (mc - {pr.1, pr.2} + ({o₁, o₂} : Multiset (MarkedAgent L K)))
        ≤ taintedCount (L := L) (K := K) mc := by
      unfold taintedCount
      rw [Multiset.countP_add, houts, add_zero]
      exact Multiset.countP_le_of_le _ (tsub_le_self (a := mc))
    omega
  · rw [if_neg happ] at hpr
    omega

/-- **The one-step taint-rise probability bound** (brick 3.4b capstone): on the `AllClockP3`
window,

  `P[taintedCount rises] ≤ (count@T / n)² + 2·taintedCount/n`

— the gated drip-seed rate (squared minute-`T` fraction) plus the epidemic-from-tainted rate (the
branching term).  This is the exact two-phase rate structure of Doty's `d`-analysis (brick 3.4c). -/
theorem tainted_rise_prob_le (T θn : ℕ) (mc : Config (MarkedAgent L K)) (h : 2 ≤ mc.card)
    (hw : AllClockP3 (L := L) (K := K) (eraseConfig (L := L) (K := K) mc)) :
    markedK (L := L) (K := K) T θn mc
        {mc' | taintedCount (L := L) (K := K) mc < taintedCount (L := L) (K := K) mc'} ≤
      ENNReal.ofReal
        (((Multiset.countP (fun m : MarkedAgent L K => m.1.minute.val = T) mc : ℝ)
          / (mc.card : ℝ)) ^ 2)
      + ENNReal.ofReal
          (2 * ((taintedCount (L := L) (K := K) mc : ℝ) / (mc.card : ℝ))) := by
  classical
  rw [markedK_apply_pair (L := L) (K := K) T θn mc h _
    (DiscreteMeasurableSpace.forall_measurableSet _)]
  refine le_trans (measure_mono (tainted_rise_subset (L := L) (K := K) T θn mc hw)) ?_
  refine le_trans (measure_union_le _ _) ?_
  set ST : Finset (MarkedAgent L K) :=
    Finset.univ.filter (fun m : MarkedAgent L K => m.1.minute.val = T) with hST
  set SM : Finset (MarkedAgent L K) :=
    Finset.univ.filter (fun m : MarkedAgent L K => m.2 = true) with hSM
  have hXT : (∑ m ∈ ST, mc.count m)
      = Multiset.countP (fun m : MarkedAgent L K => m.1.minute.val = T) mc := by
    rw [hST]
    exact sum_count_filter_eq_countP _ mc
  have hXM : (∑ m ∈ SM, mc.count m) = taintedCount (L := L) (K := K) mc := by
    rw [hSM]
    exact sum_count_filter_eq_countP _ mc
  have hbound1 : (mc.interactionPMF h).toMeasure
      {pr : MarkedAgent L K × MarkedAgent L K |
        pr.1.1.minute.val = T ∧ pr.2.1.minute.val = T} ≤
      ENNReal.ofReal
        (((Multiset.countP (fun m : MarkedAgent L K => m.1.minute.val = T) mc : ℝ)
          / (mc.card : ℝ)) ^ 2) := by
    have hset : {pr : MarkedAgent L K × MarkedAgent L K |
        pr.1.1.minute.val = T ∧ pr.2.1.minute.val = T}
        = {pr : MarkedAgent L K × MarkedAgent L K | pr.1 ∈ ST ∧ pr.2 ∈ ST} := by
      ext pr
      simp [hST]
    rw [hset, ← hXT]
    exact pair_block_prob_le_sq (L := L) (K := K) mc h ST
  have hbound2 : (mc.interactionPMF h).toMeasure
      {pr : MarkedAgent L K × MarkedAgent L K | pr.1.2 = true ∨ pr.2.2 = true} ≤
      ENNReal.ofReal
        (2 * ((taintedCount (L := L) (K := K) mc : ℝ) / (mc.card : ℝ))) := by
    have hsub : {pr : MarkedAgent L K × MarkedAgent L K | pr.1.2 = true ∨ pr.2.2 = true}
        ⊆ {pr : MarkedAgent L K × MarkedAgent L K | pr.1 ∈ SM}
          ∪ {pr : MarkedAgent L K × MarkedAgent L K | pr.2 ∈ SM} := by
      rintro pr (hp | hp)
      · exact Or.inl (by simp [hSM, hp])
      · exact Or.inr (by simp [hSM, hp])
    refine le_trans (measure_mono hsub) (le_trans (measure_union_le _ _) ?_)
    have h1 := fst_block_prob_le (L := L) (K := K) mc h SM
    have h2 := snd_block_prob_le (L := L) (K := K) mc h SM
    rw [hXM] at h1 h2
    refine le_trans (add_le_add h1 h2) ?_
    rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    ring_nf
    exact le_refl _
  exact add_le_add hbound1 hbound2

/-! ## Part 8 — the gate-closed rise bound and the marked a.e. helper (brick 3.4c-ii inputs).

With the pre-bulk gate CLOSED the mark rule grants NO drip marks (branch 3 returns `g = false`),
so the taint can only rise via the epidemic from a tainted member: `P[rise] ≤ 2·taintedCount/n`,
with no drip-seed term at all.  Together with `tainted_rise_prob_le` this gives the uniform rate
`q(mc) ≤ (θn/n)² + 2·taintedCount/n` over the whole hour window — the input to the time-dependent
potential drift (the step-indexed engine instantiation). -/

/-- Almost-every one-step successor of the marked kernel satisfies any support-closed property. -/
theorem ae_markedStep (T θn : ℕ) (mc : Config (MarkedAgent L K))
    (P : Config (MarkedAgent L K) → Prop)
    (h : ∀ mc', mc' ∈ (markedPMF (L := L) (K := K) T θn mc).support → P mc') :
    ∀ᵐ mc' ∂(markedK (L := L) (K := K) T θn mc), P mc' := by
  change ∀ᵐ mc' ∂(markedPMF (L := L) (K := K) T θn mc).toMeasure, P mc'
  rw [ae_iff, PMF.toMeasure_apply_eq_zero_iff _
    (DiscreteMeasurableSpace.forall_measurableSet _), Set.disjoint_left]
  intro mc' hsupp hbad
  exact hbad (h mc' hsupp)

/-- **With the gate closed, the taint rises only via a tainted member** (branch 3 of the mark rule
returns `false`; no minute analysis needed). -/
theorem tainted_rise_subset_gate_false (T θn : ℕ) (mc : Config (MarkedAgent L K))
    (hg : preBulkGate (L := L) (K := K) T θn mc = false) :
    (markedStep (L := L) (K := K) T θn mc) ⁻¹'
        {mc' | taintedCount (L := L) (K := K) mc < taintedCount (L := L) (K := K) mc'} ⊆
      {pr : MarkedAgent L K × MarkedAgent L K | pr.1.2 = true ∨ pr.2.2 = true} := by
  classical
  intro pr hpr
  rw [Set.mem_preimage, Set.mem_setOf_eq] at hpr
  by_contra hnot
  rw [Set.mem_setOf_eq] at hnot
  push Not at hnot
  obtain ⟨hm1, hm2⟩ := hnot
  unfold markedStep at hpr
  by_cases happ : ({pr.1, pr.2} : Multiset (MarkedAgent L K)) ≤ mc
  · rw [if_pos happ] at hpr
    set g := preBulkGate (L := L) (K := K) T θn mc with hgdef
    set o₁ := (markedOut (L := L) (K := K) T g pr.1 pr.2).1 with ho₁
    set o₂ := (markedOut (L := L) (K := K) T g pr.1 pr.2).2 with ho₂
    have hmark₁ : o₁.2 = markFor (L := L) (K := K) T g pr.1 pr.2
        (Transition L K pr.1.1 pr.2.1).1 := rfl
    have hmark₂ : o₂.2 = markFor (L := L) (K := K) T g pr.2 pr.1
        (Transition L K pr.1.1 pr.2.1).2 := rfl
    have hgfalse : g = false := by rw [hgdef]; exact hg
    have hno₁ : ¬ (o₁.2 = true) := by
      intro hm
      rw [hmark₁] at hm
      rcases markFor_true_crossing_cases (L := L) (K := K) T g pr.1 pr.2 _ hm with
        ⟨_, hin⟩ | ⟨_, _, hvia⟩
      · exact hm1 hin
      · rcases hvia with ⟨_, hgt⟩ | hpart
        · rw [hgfalse] at hgt
          exact absurd hgt (by simp)
        · exact hm2 hpart
    have hno₂ : ¬ (o₂.2 = true) := by
      intro hm
      rw [hmark₂] at hm
      rcases markFor_true_crossing_cases (L := L) (K := K) T g pr.2 pr.1 _ hm with
        ⟨_, hin⟩ | ⟨_, _, hvia⟩
      · exact hm2 hin
      · rcases hvia with ⟨_, hgt⟩ | hpart
        · rw [hgfalse] at hgt
          exact absurd hgt (by simp)
        · exact hm1 hpart
    have houts : Multiset.countP (fun m : MarkedAgent L K => m.2 = true)
        ({o₁, o₂} : Multiset (MarkedAgent L K)) = 0 := by
      rw [Multiset.countP_eq_zero]
      intro m hm
      rw [show ({o₁, o₂} : Multiset (MarkedAgent L K)) = o₁ ::ₘ {o₂} from rfl] at hm
      rcases Multiset.mem_cons.mp hm with hm | hm
      · rw [hm]; exact hno₁
      · rw [Multiset.mem_singleton.mp hm]; exact hno₂
    have hle : taintedCount (L := L) (K := K)
        (mc - {pr.1, pr.2} + ({o₁, o₂} : Multiset (MarkedAgent L K)))
        ≤ taintedCount (L := L) (K := K) mc := by
      unfold taintedCount
      rw [Multiset.countP_add, houts, add_zero]
      exact Multiset.countP_le_of_le _ (tsub_le_self (a := mc))
    omega
  · rw [if_neg happ] at hpr
    omega

/-- **The gate-closed taint-rise probability**: `P[rise] ≤ 2·taintedCount/n` (no drip-seed term). -/
theorem tainted_rise_prob_le_of_gate_false (T θn : ℕ) (mc : Config (MarkedAgent L K))
    (h : 2 ≤ mc.card)
    (hg : preBulkGate (L := L) (K := K) T θn mc = false) :
    markedK (L := L) (K := K) T θn mc
        {mc' | taintedCount (L := L) (K := K) mc < taintedCount (L := L) (K := K) mc'} ≤
      ENNReal.ofReal
        (2 * ((taintedCount (L := L) (K := K) mc : ℝ) / (mc.card : ℝ))) := by
  classical
  rw [markedK_apply_pair (L := L) (K := K) T θn mc h _
    (DiscreteMeasurableSpace.forall_measurableSet _)]
  refine le_trans (measure_mono (tainted_rise_subset_gate_false (L := L) (K := K) T θn mc hg)) ?_
  set SM : Finset (MarkedAgent L K) :=
    Finset.univ.filter (fun m : MarkedAgent L K => m.2 = true) with hSM
  have hXM : (∑ m ∈ SM, mc.count m) = taintedCount (L := L) (K := K) mc := by
    rw [hSM]
    exact sum_count_filter_eq_countP _ mc
  have hsub2 : {pr : MarkedAgent L K × MarkedAgent L K | pr.1.2 = true ∨ pr.2.2 = true}
      ⊆ {pr : MarkedAgent L K × MarkedAgent L K | pr.1 ∈ SM}
        ∪ {pr : MarkedAgent L K × MarkedAgent L K | pr.2 ∈ SM} := by
    rintro pr (hp | hp)
    · exact Or.inl (by simp [hSM, hp])
    · exact Or.inr (by simp [hSM, hp])
  refine le_trans (measure_mono hsub2) (le_trans (measure_union_le _ _) ?_)
  have h1 := fst_block_prob_le (L := L) (K := K) mc h SM
  have h2 := snd_block_prob_le (L := L) (K := K) mc h SM
  rw [hXM] at h1 h2
  refine le_trans (add_le_add h1 h2) ?_
  rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  ring_nf
  exact le_refl _

/-! ## Part 9 — the time-dependent taint potential, its gated drift, and the marked taint tail. -/

/-- The hour-window gate for the taint analysis: fixed population, all agents Phase-3 clocks.
(The pre-bulk gate is NOT here — the mark rule itself stops the drip seeds once the bulk arrives,
so the rate `q ≤ (θn/n)² + 2·tainted/n` holds across the whole hour window.) -/
def taintedGate (n : ℕ) : Set (Config (MarkedAgent L K)) :=
  {mc | mc.card = n ∧ AllClockP3 (L := L) (K := K) (eraseConfig (L := L) (K := K) mc)}

/-- The time-dependent exponential taint potential `Φ_j = exp(s_j·taintedCount + b_j)`. -/
noncomputable def taintedPot (s b : ℕ → ℝ) (j : ℕ) (mc : Config (MarkedAgent L K)) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (s j * (taintedCount (L := L) (K := K) mc : ℝ) + b j))

/-- The minute-`T` count is at most the level-`T` tail of the erased configuration, on the
`AllClockP3` window. -/
theorem countT_le_rBeyond_erase (T : ℕ) (mc : Config (MarkedAgent L K))
    (hw : AllClockP3 (L := L) (K := K) (eraseConfig (L := L) (K := K) mc)) :
    Multiset.countP (fun m : MarkedAgent L K => m.1.minute.val = T) mc
      ≤ rBeyond (L := L) (K := K) T (eraseConfig (L := L) (K := K) mc) := by
  classical
  unfold rBeyond eraseConfig
  rw [Multiset.countP_map]
  rw [Multiset.countP_eq_card_filter]
  apply Multiset.card_le_card
  rw [Multiset.le_iff_count]
  intro m
  rw [Multiset.count_filter, Multiset.count_filter]
  by_cases hm : m ∈ mc
  · have hrole := hw m.1 (by
      unfold eraseConfig
      exact Multiset.mem_map_of_mem Prod.fst hm)
    by_cases hT : m.1.minute.val = T
    · rw [if_pos hT, if_pos (show clockBeyondP (L := L) (K := K) T m.1 from
        ⟨hrole.1, by omega⟩)]
    · rw [if_neg hT]
      simp
  · have hz : Multiset.count m mc = 0 := Multiset.count_eq_zero_of_notMem hm
    rw [hz]
    split_ifs <;> simp

/-- **The gated drift of the time-dependent taint potential** (brick 3.4c-ii core).  On the hour
window, with the slope recursion absorbing the branching (`s_{j+1} + 2(e^{s_{j+1}}−1)/n ≤ s_j`)
and the intercept recursion absorbing the drip-seed immigration
(`b_{j+1} + (θn/n)²(e^{s_{j+1}}−1) ≤ b_j`), the potential family is a one-step supermartingale:
`∫ Φ_{j+1} d(markedK mc) ≤ Φ_j mc`. -/
theorem taintedPot_drift (T θn n : ℕ) (hn : 2 ≤ n) (s b : ℕ → ℝ)
    (hs1 : ∀ j, 0 ≤ s (j + 1))
    (hslope : ∀ j, s (j + 1) + 2 * (Real.exp (s (j + 1)) - 1) / (n : ℝ) ≤ s j)
    (hicept : ∀ j, b (j + 1) + ((θn : ℝ) / (n : ℝ)) ^ 2 * (Real.exp (s (j + 1)) - 1) ≤ b j) :
    ∀ (j : ℕ), ∀ mc ∈ taintedGate (L := L) (K := K) n,
      ∫⁻ mc', taintedPot (L := L) (K := K) s b (j + 1) mc'
          ∂(markedK (L := L) (K := K) T θn mc) ≤
        taintedPot (L := L) (K := K) s b j mc := by
  classical
  rintro j mc ⟨hcard, hw⟩
  have hcard2 : 2 ≤ mc.card := by omega
  haveI : IsProbabilityMeasure (markedK (L := L) (K := K) T θn mc) :=
    (inferInstance : IsMarkovKernel (markedK (L := L) (K := K) T θn)).isProbabilityMeasure mc
  set N := taintedCount (L := L) (K := K) mc with hN
  set q : ℝ := ((θn : ℝ) / (n : ℝ)) ^ 2 + 2 * ((N : ℝ) / (n : ℝ)) with hq
  have hq0 : 0 ≤ q := by rw [hq]; positivity
  -- the uniform rise rate over the window.
  have hprob : markedK (L := L) (K := K) T θn mc
      {mc' | N < taintedCount (L := L) (K := K) mc'} ≤ ENNReal.ofReal q := by
    by_cases hg : preBulkGate (L := L) (K := K) T θn mc = true
    · refine le_trans (tainted_rise_prob_le (L := L) (K := K) T θn mc hcard2 hw) ?_
      have hcntT : Multiset.countP (fun m : MarkedAgent L K => m.1.minute.val = T) mc ≤ θn := by
        have h1 := countT_le_rBeyond_erase (L := L) (K := K) T mc hw
        have h2 : rBeyond (L := L) (K := K) T (eraseConfig (L := L) (K := K) mc) < θn :=
          of_decide_eq_true hg
        omega
      have hbound : ((Multiset.countP (fun m : MarkedAgent L K => m.1.minute.val = T) mc : ℝ)
          / (mc.card : ℝ)) ^ 2 ≤ ((θn : ℝ) / (n : ℝ)) ^ 2 := by
        rw [hcard]
        apply pow_le_pow_left₀ (by positivity)
        have hc : (Multiset.countP (fun m : MarkedAgent L K => m.1.minute.val = T) mc : ℝ)
            ≤ (θn : ℝ) := by exact_mod_cast hcntT
        gcongr
      calc ENNReal.ofReal
            (((Multiset.countP (fun m : MarkedAgent L K => m.1.minute.val = T) mc : ℝ)
              / (mc.card : ℝ)) ^ 2)
            + ENNReal.ofReal (2 * ((N : ℝ) / (mc.card : ℝ)))
          ≤ ENNReal.ofReal (((θn : ℝ) / (n : ℝ)) ^ 2)
            + ENNReal.ofReal (2 * ((N : ℝ) / (n : ℝ))) :=
            add_le_add (ENNReal.ofReal_le_ofReal hbound)
              (ENNReal.ofReal_le_ofReal (by rw [hcard]))
        _ = ENNReal.ofReal q := by
            rw [hq, ENNReal.ofReal_add (by positivity) (by positivity)]
    · have hg' : preBulkGate (L := L) (K := K) T θn mc = false := by
        rcases Bool.eq_false_or_eq_true (preBulkGate (L := L) (K := K) T θn mc) with h | h
        · exact absurd h hg
        · exact h
      refine le_trans
        (tainted_rise_prob_le_of_gate_false (L := L) (K := K) T θn mc hcard2 hg') ?_
      apply ENNReal.ofReal_le_ofReal
      rw [hq, hcard]
      have hsq : (0 : ℝ) ≤ ((θn : ℝ) / (n : ℝ)) ^ 2 := by positivity
      linarith
  -- the a.e. one-step increment bound.
  have hstep_ae : ∀ᵐ mc' ∂(markedK (L := L) (K := K) T θn mc),
      taintedCount (L := L) (K := K) mc' ≤ N + 1 :=
    ae_markedStep (L := L) (K := K) T θn mc _ (fun mc' hsupp =>
      taintedCount_le_succ_on_support (L := L) (K := K) T θn mc mc' hw hsupp)
  -- the generic MGF contraction at this state's rate.
  have hmgf := ClimbTail.mgf_one_step (markedK (L := L) (K := K) T θn mc) (s (j + 1)) (hs1 j)
    (taintedCount (L := L) (K := K)) N hstep_ae q hq0 hprob
  -- pull the intercept constant out, combine, close with the real-exponential inequality.
  have hsplit : ∀ mc', taintedPot (L := L) (K := K) s b (j + 1) mc'
      = ENNReal.ofReal (Real.exp (b (j + 1)))
        * ENNReal.ofReal
            (Real.exp (s (j + 1) * (taintedCount (L := L) (K := K) mc' : ℝ))) := by
    intro mc'
    unfold taintedPot
    rw [← ENNReal.ofReal_mul (by positivity), ← Real.exp_add]
    ring_nf
  calc ∫⁻ mc', taintedPot (L := L) (K := K) s b (j + 1) mc'
        ∂(markedK (L := L) (K := K) T θn mc)
      = ENNReal.ofReal (Real.exp (b (j + 1)))
          * ∫⁻ mc', ENNReal.ofReal
              (Real.exp (s (j + 1) * (taintedCount (L := L) (K := K) mc' : ℝ)))
            ∂(markedK (L := L) (K := K) T θn mc) := by
        rw [← MeasureTheory.lintegral_const_mul _ (Measurable.of_discrete)]
        exact lintegral_congr_ae (Filter.Eventually.of_forall (fun mc' => hsplit mc'))
    _ ≤ ENNReal.ofReal (Real.exp (b (j + 1)))
          * ENNReal.ofReal ((1 + q * (Real.exp (s (j + 1)) - 1))
              * Real.exp (s (j + 1) * (N : ℝ))) := by gcongr
    _ ≤ taintedPot (L := L) (K := K) s b j mc := by
        unfold taintedPot
        rw [← ENNReal.ofReal_mul (by positivity)]
        apply ENNReal.ofReal_le_ofReal
        have hexp1 : (1 : ℝ) ≤ Real.exp (s (j + 1)) := Real.one_le_exp (hs1 j)
        have h1e : 1 + q * (Real.exp (s (j + 1)) - 1)
            ≤ Real.exp (q * (Real.exp (s (j + 1)) - 1)) := by
          have h := Real.add_one_le_exp (q * (Real.exp (s (j + 1)) - 1))
          linarith
        calc Real.exp (b (j + 1)) * ((1 + q * (Real.exp (s (j + 1)) - 1))
              * Real.exp (s (j + 1) * (N : ℝ)))
            ≤ Real.exp (b (j + 1)) * (Real.exp (q * (Real.exp (s (j + 1)) - 1))
                * Real.exp (s (j + 1) * (N : ℝ))) := by
              apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
              apply mul_le_mul_of_nonneg_right h1e (Real.exp_pos _).le
          _ = Real.exp (b (j + 1) + q * (Real.exp (s (j + 1)) - 1)
                + s (j + 1) * (N : ℝ)) := by
              rw [← Real.exp_add, ← Real.exp_add]
              ring_nf
          _ ≤ Real.exp (s j * (N : ℝ) + b j) := by
              apply Real.exp_le_exp.mpr
              have hNnn : (0 : ℝ) ≤ (N : ℝ) := by positivity
              have hsl := hslope j
              have hic := hicept j
              have hslN : (s (j + 1) + 2 * (Real.exp (s (j + 1)) - 1) / (n : ℝ)) * (N : ℝ)
                  ≤ s j * (N : ℝ) :=
                mul_le_mul_of_nonneg_right hsl hNnn
              have hslN' : s (j + 1) * (N : ℝ)
                  + 2 * (Real.exp (s (j + 1)) - 1) / (n : ℝ) * (N : ℝ)
                  ≤ s j * (N : ℝ) := by
                calc s (j + 1) * (N : ℝ)
                    + 2 * (Real.exp (s (j + 1)) - 1) / (n : ℝ) * (N : ℝ)
                    = (s (j + 1) + 2 * (Real.exp (s (j + 1)) - 1) / (n : ℝ)) * (N : ℝ) := by
                      ring
                  _ ≤ s j * (N : ℝ) := hslN
              rw [hq, show (((θn : ℝ) / (n : ℝ)) ^ 2 + 2 * ((N : ℝ) / (n : ℝ)))
                  * (Real.exp (s (j + 1)) - 1)
                  = ((θn : ℝ) / (n : ℝ)) ^ 2 * (Real.exp (s (j + 1)) - 1)
                    + 2 * (Real.exp (s (j + 1)) - 1) / (n : ℝ) * (N : ℝ) from by ring]
              linarith [hslN', hic]

/-- **The marked taint tail** (brick 3.4c-ii capstone).  Over `t` steps of the marked kernel from
`mc₀`, the probability that the taint count reaches `a` is at most the hour-window escape mass plus
`Φ_0(mc₀)/exp(s_t·a + b_t)` — the time-dependent-MGF tail.  At the paper scales this is the
`d = O(n^{-0.85})` bound of Doty Theorem 6.5's second claim. -/
theorem tainted_marked_tail (T θn n : ℕ) (hn : 2 ≤ n) (s b : ℕ → ℝ)
    (hs1 : ∀ j, 0 ≤ s (j + 1))
    (hslope : ∀ j, s (j + 1) + 2 * (Real.exp (s (j + 1)) - 1) / (n : ℝ) ≤ s j)
    (hicept : ∀ j, b (j + 1) + ((θn : ℝ) / (n : ℝ)) ^ 2 * (Real.exp (s (j + 1)) - 1) ≤ b j)
    (t : ℕ) (hst : 0 ≤ s t) (mc₀ : Config (MarkedAgent L K)) (a : ℕ) :
    ((markedK (L := L) (K := K) T θn) ^ t) mc₀
        {mc | a ≤ taintedCount (L := L) (K := K) mc} ≤
      (GatedDrift.killK (markedK (L := L) (K := K) T θn)
          (taintedGate (L := L) (K := K) n) ^ t) (some mc₀) {none} +
        taintedPot (L := L) (K := K) s b 0 mc₀
          / ENNReal.ofReal (Real.exp (s t * (a : ℝ) + b t)) := by
  have hsub : {mc : Config (MarkedAgent L K) | a ≤ taintedCount (L := L) (K := K) mc}
      ⊆ {mc | ENNReal.ofReal (Real.exp (s t * (a : ℝ) + b t))
          ≤ taintedPot (L := L) (K := K) s b t mc} := by
    intro mc hmc
    rw [Set.mem_setOf_eq] at hmc ⊢
    unfold taintedPot
    apply ENNReal.ofReal_le_ofReal
    apply Real.exp_le_exp.mpr
    have hcast : (a : ℝ) ≤ (taintedCount (L := L) (K := K) mc : ℝ) := by exact_mod_cast hmc
    nlinarith [hst, hcast]
  refine le_trans (measure_mono hsub) ?_
  exact GatedDrift.stepIndexed_gated_tail (G := taintedGate (L := L) (K := K) n)
    (taintedPot (L := L) (K := K) s b)
    (taintedPot_drift (L := L) (K := K) T θn n hn s b hs1 hslope hicept)
    t mc₀ (ENNReal.ofReal (Real.exp (s t * (a : ℝ) + b t)))
    (by simp [Real.exp_pos]) ENNReal.ofReal_ne_top

/-! ## Part 10 — the explicit slope/intercept sequences (brick 3.4c-iii).

The recursions are satisfied by the geometric slope `s_j = σ·ρ^{t−j}` (`ρ = 1 + 4/n`) and the
linear intercept `b_j = β·(t−j)` (`β = 2σρ^t·(θn/n)²`), as long as the START slope stays small
(`σρ^t ≤ 1/2`, so that `e^x − 1 ≤ 2x` applies).  Packaged: from an all-clean start the taint tail
is `exp(2σρ^t·(θn/n)²·t − σ·a)` — at the paper scales (`θn/n = n^{-0.45}`, `t = O(n log log n)`,
`σ = Θ(1)`, `a = n^{0.15}`) this is `exp(O(n^{0.1} log log n) − Θ(1)·n^{0.15}) = n^{-ω(1)}`. -/

/-- `e^x − 1 ≤ 2x` on `[0, 1/2]`. -/
theorem exp_sub_one_le_two_mul {x : ℝ} (h0 : 0 ≤ x) (h2 : x ≤ 1 / 2) :
    Real.exp x - 1 ≤ 2 * x := by
  have hb := Real.exp_bound_div_one_sub_of_interval h0 (by linarith : x < 1)
  have h1x : (0 : ℝ) < 1 - x := by linarith
  have hdiv : 1 / (1 - x) ≤ 1 + 2 * x := by
    rw [div_le_iff₀ h1x]
    nlinarith
  linarith

/-- **The marked taint tail at the explicit sequences.**  With the geometric slope and linear
intercept, from any start `mc₀`:

  `P[taintedCount ≥ a at t] ≤ hour-escape + exp(σρ^t·N₀ + 2σρ^t(θn/n)²·t − σ·a)`,

`ρ = 1 + 4/n`, provided `σρ^t ≤ 1/2`.  (From the all-clean start `N₀ = 0`.) -/
theorem tainted_marked_tail_explicit (T θn n : ℕ) (hn : 2 ≤ n)
    (σ : ℝ) (hσ : 0 < σ) (t : ℕ)
    (hsmall : σ * (1 + 4 / (n : ℝ)) ^ t ≤ 1 / 2)
    (mc₀ : Config (MarkedAgent L K)) (a : ℕ) :
    ((markedK (L := L) (K := K) T θn) ^ t) mc₀
        {mc | a ≤ taintedCount (L := L) (K := K) mc} ≤
      (GatedDrift.killK (markedK (L := L) (K := K) T θn)
          (taintedGate (L := L) (K := K) n) ^ t) (some mc₀) {none} +
        ENNReal.ofReal
          (Real.exp (σ * (1 + 4 / (n : ℝ)) ^ t * (taintedCount (L := L) (K := K) mc₀ : ℝ)
            + 2 * σ * (1 + 4 / (n : ℝ)) ^ t * ((θn : ℝ) / (n : ℝ)) ^ 2 * (t : ℝ)
            - σ * (a : ℝ))) := by
  classical
  have hnpos : (0 : ℝ) < (n : ℝ) := by
    have : 0 < n := by omega
    exact_mod_cast this
  set ρ : ℝ := 1 + 4 / (n : ℝ) with hρ
  have hρ1 : (1 : ℝ) ≤ ρ := by
    rw [hρ]
    have h4 : (0 : ℝ) ≤ 4 / (n : ℝ) := by positivity
    linarith
  have hρpos : (0 : ℝ) < ρ := by linarith
  have hρ0 : ρ ≠ 0 := by linarith
  set β : ℝ := 2 * σ * ρ ^ t * ((θn : ℝ) / (n : ℝ)) ^ 2 with hβ
  set s : ℕ → ℝ := fun j => σ * ρ ^ ((t : ℤ) - (j : ℤ)) with hs
  set b : ℕ → ℝ := fun j => β * (((t : ℤ) - (j : ℤ) : ℤ) : ℝ) with hb
  have hs_pos : ∀ j, 0 < s j := by
    intro j
    rw [hs]
    positivity
  have hs_le : ∀ j, s j ≤ 1 / 2 := by
    intro j
    rw [hs]
    calc σ * ρ ^ ((t : ℤ) - (j : ℤ)) ≤ σ * ρ ^ (t : ℤ) := by
          apply mul_le_mul_of_nonneg_left _ hσ.le
          apply zpow_le_zpow_right₀ hρ1
          omega
      _ = σ * ρ ^ t := by rw [zpow_natCast]
      _ ≤ 1 / 2 := hsmall
  have hs1 : ∀ j, 0 ≤ s (j + 1) := fun j => (hs_pos (j + 1)).le
  have hslope : ∀ j, s (j + 1) + 2 * (Real.exp (s (j + 1)) - 1) / (n : ℝ) ≤ s j := by
    intro j
    have hexp := exp_sub_one_le_two_mul (hs_pos (j + 1)).le (hs_le (j + 1))
    have hstep : s (j + 1) * ρ = s j := by
      rw [hs]
      show σ * ρ ^ ((t : ℤ) - ((j : ℕ) + 1 : ℕ)) * ρ = σ * ρ ^ ((t : ℤ) - (j : ℤ))
      rw [mul_assoc, ← zpow_add_one₀ hρ0]
      congr 1
      push_cast
      ring_nf
    have hd : 2 * (Real.exp (s (j + 1)) - 1) / (n : ℝ) ≤ 2 * (2 * s (j + 1)) / (n : ℝ) := by
      apply div_le_div_of_nonneg_right (by linarith) hnpos.le
    calc s (j + 1) + 2 * (Real.exp (s (j + 1)) - 1) / (n : ℝ)
        ≤ s (j + 1) + 2 * (2 * s (j + 1)) / (n : ℝ) := by linarith
      _ = s (j + 1) * ρ := by
          rw [hρ]
          field_simp
          ring
      _ = s j := hstep
  have hicept : ∀ j, b (j + 1) + ((θn : ℝ) / (n : ℝ)) ^ 2 * (Real.exp (s (j + 1)) - 1)
      ≤ b j := by
    intro j
    have hexp := exp_sub_one_le_two_mul (hs_pos (j + 1)).le (hs_le (j + 1))
    have hsmax : s (j + 1) ≤ σ * ρ ^ t := by
      rw [hs]
      calc σ * ρ ^ ((t : ℤ) - (((j : ℕ) + 1 : ℕ) : ℤ)) ≤ σ * ρ ^ (t : ℤ) := by
            apply mul_le_mul_of_nonneg_left _ hσ.le
            apply zpow_le_zpow_right₀ hρ1
            push_cast
            omega
        _ = σ * ρ ^ t := by rw [zpow_natCast]
    have hbdiff : b j - b (j + 1) = β := by
      rw [hb]
      push_cast
      ring
    have hθnn : (0 : ℝ) ≤ ((θn : ℝ) / (n : ℝ)) ^ 2 := by positivity
    have hkey : ((θn : ℝ) / (n : ℝ)) ^ 2 * (Real.exp (s (j + 1)) - 1) ≤ β := by
      calc ((θn : ℝ) / (n : ℝ)) ^ 2 * (Real.exp (s (j + 1)) - 1)
          ≤ ((θn : ℝ) / (n : ℝ)) ^ 2 * (2 * s (j + 1)) :=
            mul_le_mul_of_nonneg_left (by linarith) hθnn
        _ ≤ ((θn : ℝ) / (n : ℝ)) ^ 2 * (2 * (σ * ρ ^ t)) := by
            apply mul_le_mul_of_nonneg_left _ hθnn
            linarith
        _ = β := by rw [hβ]; ring
    linarith
  have htail := tainted_marked_tail (L := L) (K := K) T θn n hn s b hs1 hslope hicept
    t (hs_pos t).le mc₀ a
  refine le_trans htail ?_
  gcongr
  have hs0 : s 0 = σ * ρ ^ t := by
    rw [hs]
    show σ * ρ ^ ((t : ℤ) - ((0 : ℕ) : ℤ)) = σ * ρ ^ t
    rw [show (t : ℤ) - ((0 : ℕ) : ℤ) = (t : ℤ) from by push_cast; ring, zpow_natCast]
  have hb0 : b 0 = β * (t : ℝ) := by
    rw [hb]
    push_cast
    ring
  have hst : s t = σ := by
    rw [hs]
    show σ * ρ ^ ((t : ℤ) - ((t : ℕ) : ℤ)) = σ
    rw [sub_self, zpow_zero, mul_one]
  have hbt : b t = 0 := by
    rw [hb]
    push_cast
    ring
  unfold taintedPot
  rw [hs0, hb0, hst, hbt]
  rw [← ENNReal.ofReal_div_of_pos (Real.exp_pos _), ← Real.exp_sub]
  apply ENNReal.ofReal_le_ofReal
  apply Real.exp_le_exp.mpr
  rw [hβ]
  ring_nf
  exact le_refl _

/-! ## Part 11 — the clean-count rise structure (brick 3.5a).

`cleanAbove` (Doty's `y = c_{≥T+1} − d`) mirrors `taintedCount` with the COMPLEMENTARY gate: a
clean above-`T` output is inherited (a clean above-`T` input), a POST-gate drip seed (the mark rule
gives `g = false` once the bulk arrives — clean), or a sync from a clean above-`T` leader.  Hence

  `P[cleanAbove rises] ≤ (count@T/n)² + 2·cleanAbove/n`

— the same affine rate shape, so the whole time-dependent-potential machinery applies verbatim
(the Lemma 6.3 window recurrence instantiates it per window). -/

/-- The mark-rule case split for a CLEAN above-`T` output: inherited clean, a same-minute drip
crossing, or a sync from a clean partner. -/
theorem markFor_false_above_cases (T : ℕ) (g : Bool) (own partner : MarkedAgent L K)
    (o : AgentState L K) (habove : T + 1 ≤ o.minute.val)
    (h : markFor (L := L) (K := K) T g own partner o = false) :
    (T + 1 ≤ own.1.minute.val ∧ own.2 = false) ∨
      (own.1.minute.val < T + 1 ∧
        (own.1.minute = partner.1.minute ∨ partner.2 = false)) := by
  unfold markFor at h
  split_ifs at h with h1 h2 h3
  · omega
  · exact Or.inl ⟨h2, h⟩
  · exact Or.inr ⟨by omega, Or.inl h3⟩
  · exact Or.inr ⟨by omega, Or.inr h⟩

/-- **The clean-rise event is contained in the two scheduler events**: a same-minute-`T` pair (the
post-gate drip seed) or a pair with a clean above-`T` member. -/
theorem cleanAbove_rise_subset (T θn : ℕ) (mc : Config (MarkedAgent L K))
    (hw : AllClockP3 (L := L) (K := K) (eraseConfig (L := L) (K := K) mc)) :
    (markedStep (L := L) (K := K) T θn mc) ⁻¹'
        {mc' | cleanAbove (L := L) (K := K) T mc < cleanAbove (L := L) (K := K) T mc'} ⊆
      {pr : MarkedAgent L K × MarkedAgent L K |
          pr.1.1.minute.val = T ∧ pr.2.1.minute.val = T} ∪
        {pr : MarkedAgent L K × MarkedAgent L K |
          (T + 1 ≤ pr.1.1.minute.val ∧ pr.1.2 = false) ∨
            (T + 1 ≤ pr.2.1.minute.val ∧ pr.2.2 = false)} := by
  classical
  intro pr hpr
  rw [Set.mem_preimage, Set.mem_setOf_eq] at hpr
  by_contra hnot
  rw [Set.mem_union, Set.mem_setOf_eq, Set.mem_setOf_eq] at hnot
  push Not at hnot
  obtain ⟨hnotT, hclean₁, hclean₂⟩ := hnot
  unfold markedStep at hpr
  by_cases happ : ({pr.1, pr.2} : Multiset (MarkedAgent L K)) ≤ mc
  · rw [if_pos happ] at hpr
    have hmem1 : pr.1 ∈ mc := Multiset.mem_of_le happ (Multiset.mem_cons_self _ _)
    have hmem2 : pr.2 ∈ mc := Multiset.mem_of_le happ
      (Multiset.mem_cons_of_mem (Multiset.mem_singleton_self _))
    have h1cp := hw pr.1.1 (Multiset.mem_map_of_mem Prod.fst hmem1)
    have h2cp := hw pr.2.1 (Multiset.mem_map_of_mem Prod.fst hmem2)
    have hminute := ClimbTail.transition_p3_minute_le_succ_max (L := L) (K := K)
      pr.1.1 pr.2.1 h1cp.1 h2cp.1 h1cp.2 h2cp.2
    set g := preBulkGate (L := L) (K := K) T θn mc with hg
    set o₁ := (markedOut (L := L) (K := K) T g pr.1 pr.2).1 with ho₁
    set o₂ := (markedOut (L := L) (K := K) T g pr.1 pr.2).2 with ho₂
    have hmark₁ : o₁.2 = markFor (L := L) (K := K) T g pr.1 pr.2
        (Transition L K pr.1.1 pr.2.1).1 := rfl
    have hmark₂ : o₂.2 = markFor (L := L) (K := K) T g pr.2 pr.1
        (Transition L K pr.1.1 pr.2.1).2 := rfl
    have hstate₁ : o₁.1 = (Transition L K pr.1.1 pr.2.1).1 := rfl
    have hstate₂ : o₂.1 = (Transition L K pr.1.1 pr.2.1).2 := rfl
    -- the generic per-output refutation: no output can be clean above `T`.
    have key : ∀ (own partner : MarkedAgent L K),
        own.1.role = .clock → partner.1.role = .clock →
        own.1.phase.val = 3 → partner.1.phase.val = 3 →
        ∀ o : AgentState L K,
          (own.1.minute ≠ partner.1.minute →
            o.minute = max own.1.minute partner.1.minute) →
          o.minute.val ≤ max own.1.minute.val partner.1.minute.val + 1 →
          ¬ (T + 1 ≤ own.1.minute.val ∧ own.2 = false) →
          ¬ (T + 1 ≤ partner.1.minute.val ∧ partner.2 = false) →
          ¬ (own.1.minute.val = T ∧ partner.1.minute.val = T) →
          T + 1 ≤ o.minute.val →
          markFor (L := L) (K := K) T g own partner o = false → False := by
      intro own partner _ _ _ _ o hsync hle hcl_own hcl_part hnT habove hmark
      rcases markFor_false_above_cases (L := L) (K := K) T g own partner o habove hmark with
        ⟨hab, hcl⟩ | ⟨hlo, hvia⟩
      · exact hcl_own ⟨hab, hcl⟩
      · rcases hvia with hsame | hpartclean
        · have hsame' : own.1.minute.val = partner.1.minute.val := by rw [hsame]
          have hmax : max own.1.minute.val partner.1.minute.val = own.1.minute.val := by
            rw [← hsame']
            exact max_self _
          rw [hmax] at hle
          exact hnT ⟨by omega, by omega⟩
        · by_cases hsame : own.1.minute = partner.1.minute
          · have hsame' : own.1.minute.val = partner.1.minute.val := by rw [hsame]
            have hmax : max own.1.minute.val partner.1.minute.val = own.1.minute.val := by
              rw [← hsame']
              exact max_self _
            rw [hmax] at hle
            exact hnT ⟨by omega, by omega⟩
          · have hmaxeq := hsync hsame
            have hpartner_above : T + 1 ≤ partner.1.minute.val := by
              rcases le_total own.1.minute partner.1.minute with hle' | hle'
              · rw [max_eq_right hle'] at hmaxeq
                rw [hmaxeq] at habove
                exact habove
              · rw [max_eq_left hle'] at hmaxeq
                rw [hmaxeq] at habove
                omega
            exact hcl_part ⟨hpartner_above, hpartclean⟩
    have hnT₁ : ¬ (pr.1.1.minute.val = T ∧ pr.2.1.minute.val = T) := fun hc =>
      hnotT hc.1 hc.2
    have hnT₂ : ¬ (pr.2.1.minute.val = T ∧ pr.1.1.minute.val = T) := fun hc =>
      hnotT hc.2 hc.1
    have hno₁ : ¬ (T + 1 ≤ o₁.1.minute.val ∧ o₁.2 = false) := by
      rintro ⟨hab, hmk⟩
      rw [hstate₁] at hab
      rw [hmark₁] at hmk
      exact key pr.1 pr.2 h1cp.1 h2cp.1 h1cp.2 h2cp.2 _
        (fun hne => (transition_p3_sync_minute (L := L) (K := K) pr.1.1 pr.2.1
          h1cp.1 h2cp.1 h1cp.2 h2cp.2 hne).1)
        hminute.1 (fun hc => hclean₁ hc.1 hc.2) (fun hc => hclean₂ hc.1 hc.2) hnT₁ hab hmk
    have hno₂ : ¬ (T + 1 ≤ o₂.1.minute.val ∧ o₂.2 = false) := by
      rintro ⟨hab, hmk⟩
      rw [hstate₂] at hab
      rw [hmark₂] at hmk
      refine key pr.2 pr.1 h2cp.1 h1cp.1 h2cp.2 h1cp.2 _ ?_ ?_ (fun hc => hclean₂ hc.1 hc.2) (fun hc => hclean₁ hc.1 hc.2) hnT₂ hab hmk
      · intro hne
        rw [max_comm pr.2.1.minute pr.1.1.minute]
        exact (transition_p3_sync_minute (L := L) (K := K) pr.1.1 pr.2.1
          h1cp.1 h2cp.1 h1cp.2 h2cp.2 (fun hc => hne hc.symm)).2
      · rw [max_comm]
        exact hminute.2
    have houts : Multiset.countP
        (fun m : MarkedAgent L K => T + 1 ≤ m.1.minute.val ∧ m.2 = false)
        ({o₁, o₂} : Multiset (MarkedAgent L K)) = 0 := by
      rw [Multiset.countP_eq_zero]
      intro m hm
      rw [show ({o₁, o₂} : Multiset (MarkedAgent L K)) = o₁ ::ₘ {o₂} from rfl] at hm
      rcases Multiset.mem_cons.mp hm with hm | hm
      · rw [hm]; exact hno₁
      · rw [Multiset.mem_singleton.mp hm]; exact hno₂
    have hle : cleanAbove (L := L) (K := K) T
        (mc - {pr.1, pr.2} + ({o₁, o₂} : Multiset (MarkedAgent L K)))
        ≤ cleanAbove (L := L) (K := K) T mc := by
      unfold cleanAbove
      rw [Multiset.countP_add, houts, add_zero]
      exact Multiset.countP_le_of_le _ (tsub_le_self (a := mc))
    omega
  · rw [if_neg happ] at hpr
    omega

/-- **The one-step clean-rise probability bound** (brick 3.5a capstone):

  `P[cleanAbove rises] ≤ (count@T/n)² + 2·cleanAbove/n`

— the post-gate drip-seed rate plus the clean-epidemic rate: the exact `y`-dynamics of Doty
Lemma 6.3. -/
theorem cleanAbove_rise_prob_le (T θn : ℕ) (mc : Config (MarkedAgent L K)) (h : 2 ≤ mc.card)
    (hw : AllClockP3 (L := L) (K := K) (eraseConfig (L := L) (K := K) mc)) :
    markedK (L := L) (K := K) T θn mc
        {mc' | cleanAbove (L := L) (K := K) T mc < cleanAbove (L := L) (K := K) T mc'} ≤
      ENNReal.ofReal
        (((Multiset.countP (fun m : MarkedAgent L K => m.1.minute.val = T) mc : ℝ)
          / (mc.card : ℝ)) ^ 2)
      + ENNReal.ofReal
          (2 * ((cleanAbove (L := L) (K := K) T mc : ℝ) / (mc.card : ℝ))) := by
  classical
  rw [markedK_apply_pair (L := L) (K := K) T θn mc h _
    (DiscreteMeasurableSpace.forall_measurableSet _)]
  refine le_trans (measure_mono (cleanAbove_rise_subset (L := L) (K := K) T θn mc hw)) ?_
  refine le_trans (measure_union_le _ _) ?_
  set ST : Finset (MarkedAgent L K) :=
    Finset.univ.filter (fun m : MarkedAgent L K => m.1.minute.val = T) with hST
  set SC : Finset (MarkedAgent L K) :=
    Finset.univ.filter
      (fun m : MarkedAgent L K => T + 1 ≤ m.1.minute.val ∧ m.2 = false) with hSC
  have hXT : (∑ m ∈ ST, mc.count m)
      = Multiset.countP (fun m : MarkedAgent L K => m.1.minute.val = T) mc := by
    rw [hST]
    exact sum_count_filter_eq_countP _ mc
  have hXC : (∑ m ∈ SC, mc.count m) = cleanAbove (L := L) (K := K) T mc := by
    rw [hSC]
    exact sum_count_filter_eq_countP _ mc
  have hbound1 : (mc.interactionPMF h).toMeasure
      {pr : MarkedAgent L K × MarkedAgent L K |
        pr.1.1.minute.val = T ∧ pr.2.1.minute.val = T} ≤
      ENNReal.ofReal
        (((Multiset.countP (fun m : MarkedAgent L K => m.1.minute.val = T) mc : ℝ)
          / (mc.card : ℝ)) ^ 2) := by
    have hset : {pr : MarkedAgent L K × MarkedAgent L K |
        pr.1.1.minute.val = T ∧ pr.2.1.minute.val = T}
        = {pr : MarkedAgent L K × MarkedAgent L K | pr.1 ∈ ST ∧ pr.2 ∈ ST} := by
      ext pr
      simp [hST]
    rw [hset, ← hXT]
    exact pair_block_prob_le_sq (L := L) (K := K) mc h ST
  have hbound2 : (mc.interactionPMF h).toMeasure
      {pr : MarkedAgent L K × MarkedAgent L K |
        (T + 1 ≤ pr.1.1.minute.val ∧ pr.1.2 = false) ∨
          (T + 1 ≤ pr.2.1.minute.val ∧ pr.2.2 = false)} ≤
      ENNReal.ofReal
        (2 * ((cleanAbove (L := L) (K := K) T mc : ℝ) / (mc.card : ℝ))) := by
    have hsub : {pr : MarkedAgent L K × MarkedAgent L K |
        (T + 1 ≤ pr.1.1.minute.val ∧ pr.1.2 = false) ∨
          (T + 1 ≤ pr.2.1.minute.val ∧ pr.2.2 = false)}
        ⊆ {pr : MarkedAgent L K × MarkedAgent L K | pr.1 ∈ SC}
          ∪ {pr : MarkedAgent L K × MarkedAgent L K | pr.2 ∈ SC} := by
      rintro pr (hp | hp)
      · exact Or.inl (by rw [hSC]; simp only [Set.mem_setOf_eq, Finset.mem_filter, Finset.mem_univ, true_and]; exact hp)
      · exact Or.inr (by rw [hSC]; simp only [Set.mem_setOf_eq, Finset.mem_filter, Finset.mem_univ, true_and]; exact hp)
    refine le_trans (measure_mono hsub) (le_trans (measure_union_le _ _) ?_)
    have h1 := fst_block_prob_le (L := L) (K := K) mc h SC
    have h2 := snd_block_prob_le (L := L) (K := K) mc h SC
    rw [hXC] at h1 h2
    refine le_trans (add_le_add h1 h2) ?_
    rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    ring_nf
    exact le_refl _
  exact add_le_add hbound1 hbound2

/-! ## Part 12 — the parameterized exponential bound and the clean `≤ 1` step (brick 3.5b inputs).

The Lemma 6.3 window induction needs the branching factor per window to be `e^{(2+O(ε))w}`, so the
crude `e^x − 1 ≤ 2x` (which doubles the rate) must be replaced by the parameterized
`e^x − 1 ≤ (1+ε)x` for `x ≤ ε/(1+ε)`. -/

/-- `e^x − 1 ≤ (1+ε)x` for `0 ≤ x ≤ ε/(1+ε)` (sharpens `exp_sub_one_le_two_mul`, which is the
case `ε = 1`). -/
theorem exp_sub_one_le_mul {x ε : ℝ} (h0 : 0 ≤ x) (hε : 0 < ε) (hx : x ≤ ε / (1 + ε)) :
    Real.exp x - 1 ≤ (1 + ε) * x := by
  have h1ε : (0 : ℝ) < 1 + ε := by linarith
  have hx1 : x < 1 := by
    have : ε / (1 + ε) < 1 := by
      rw [div_lt_one h1ε]
      linarith
    linarith
  have hb := Real.exp_bound_div_one_sub_of_interval h0 hx1
  have h1x : (0 : ℝ) < 1 - x := by linarith
  -- 1/(1−x) ≤ 1 + (1+ε)x ⟸ x ≤ ε/(1+ε) (cross-multiplied: (1+(1+ε)x)(1−x) ≥ 1).
  have hdiv : 1 / (1 - x) ≤ 1 + (1 + ε) * x := by
    rw [div_le_iff₀ h1x]
    have hxε : x * (1 + ε) ≤ ε := by
      rw [le_div_iff₀ h1ε] at hx
      exact hx
    nlinarith [h0, hxε]
  linarith

/-- **The clean count rises by at most one per step** (mirror of
`taintedCount_le_succ_on_support` via the clean case split). -/
theorem cleanAbove_le_succ_on_support (T θn : ℕ) (mc mc' : Config (MarkedAgent L K))
    (hw : AllClockP3 (L := L) (K := K) (eraseConfig (L := L) (K := K) mc))
    (hsupp : mc' ∈ (markedPMF (L := L) (K := K) T θn mc).support) :
    cleanAbove (L := L) (K := K) T mc' ≤ cleanAbove (L := L) (K := K) T mc + 1 := by
  classical
  unfold markedPMF at hsupp
  by_cases h : 2 ≤ mc.card
  · rw [dif_pos h] at hsupp
    rw [PMF.support_map] at hsupp
    obtain ⟨pr, _, hpr⟩ := hsupp
    subst hpr
    unfold markedStep
    by_cases happ : ({pr.1, pr.2} : Multiset (MarkedAgent L K)) ≤ mc
    · rw [if_pos happ]
      have hmem1 : pr.1 ∈ mc := Multiset.mem_of_le happ (Multiset.mem_cons_self _ _)
      have hmem2 : pr.2 ∈ mc := Multiset.mem_of_le happ
        (Multiset.mem_cons_of_mem (Multiset.mem_singleton_self _))
      have h1cp := hw pr.1.1 (Multiset.mem_map_of_mem Prod.fst hmem1)
      have h2cp := hw pr.2.1 (Multiset.mem_map_of_mem Prod.fst hmem2)
      unfold cleanAbove
      rw [Multiset.countP_add, Multiset.countP_sub happ]
      have hpair_le : Multiset.countP
          (fun m : MarkedAgent L K => T + 1 ≤ m.1.minute.val ∧ m.2 = false)
          ({pr.1, pr.2} : Multiset (MarkedAgent L K))
            ≤ Multiset.countP
              (fun m : MarkedAgent L K => T + 1 ≤ m.1.minute.val ∧ m.2 = false) mc :=
        Multiset.countP_le_of_le _ happ
      have hcountP2 : ∀ x y : MarkedAgent L K,
          Multiset.countP (fun m : MarkedAgent L K => T + 1 ≤ m.1.minute.val ∧ m.2 = false)
              ({x, y} : Multiset (MarkedAgent L K))
            = (if T + 1 ≤ x.1.minute.val ∧ x.2 = false then 1 else 0)
              + (if T + 1 ≤ y.1.minute.val ∧ y.2 = false then 1 else 0) := by
        intro x y
        rw [show ({x, y} : Multiset (MarkedAgent L K)) = x ::ₘ y ::ₘ 0 from rfl]
        rw [Multiset.countP_cons, Multiset.countP_cons, Multiset.countP_zero]
        ring
      set g := preBulkGate (L := L) (K := K) T θn mc with hg
      set o₁ := (markedOut (L := L) (K := K) T g pr.1 pr.2).1 with ho₁
      set o₂ := (markedOut (L := L) (K := K) T g pr.1 pr.2).2 with ho₂
      have houts : Multiset.countP
            (fun m : MarkedAgent L K => T + 1 ≤ m.1.minute.val ∧ m.2 = false)
            ({o₁, o₂} : Multiset (MarkedAgent L K))
          ≤ Multiset.countP
              (fun m : MarkedAgent L K => T + 1 ≤ m.1.minute.val ∧ m.2 = false)
              ({pr.1, pr.2} : Multiset (MarkedAgent L K)) + 1 := by
        rw [hcountP2, hcountP2]
        have hmark₁ : o₁.2 = markFor (L := L) (K := K) T g pr.1 pr.2
            (Transition L K pr.1.1 pr.2.1).1 := rfl
        have hmark₂ : o₂.2 = markFor (L := L) (K := K) T g pr.2 pr.1
            (Transition L K pr.1.1 pr.2.1).2 := rfl
        have hstate₁ : o₁.1 = (Transition L K pr.1.1 pr.2.1).1 := rfl
        have hstate₂ : o₂.1 = (Transition L K pr.1.1 pr.2.1).2 := rfl
        have hone := at_most_one_crossing (L := L) (K := K) T pr.1.1 pr.2.1
          h1cp.1 h2cp.1 h1cp.2 h2cp.2
        -- each clean-above output is inherited-clean or a crossing; at most one crossing.
        have hcase₁ : (T + 1 ≤ o₁.1.minute.val ∧ o₁.2 = false) →
            (T + 1 ≤ pr.1.1.minute.val ∧ pr.1.2 = false) ∨
              (pr.1.1.minute.val < T + 1 ∧
                T + 1 ≤ (Transition L K pr.1.1 pr.2.1).1.minute.val) := by
          rintro ⟨hab, hmk⟩
          rw [hstate₁] at hab
          rw [hmark₁] at hmk
          rcases markFor_false_above_cases (L := L) (K := K) T g pr.1 pr.2 _ hab hmk with
            ⟨h1, h2⟩ | ⟨hlo, _⟩
          · exact Or.inl ⟨h1, h2⟩
          · exact Or.inr ⟨hlo, hab⟩
        have hcase₂ : (T + 1 ≤ o₂.1.minute.val ∧ o₂.2 = false) →
            (T + 1 ≤ pr.2.1.minute.val ∧ pr.2.2 = false) ∨
              (pr.2.1.minute.val < T + 1 ∧
                T + 1 ≤ (Transition L K pr.1.1 pr.2.1).2.minute.val) := by
          rintro ⟨hab, hmk⟩
          rw [hstate₂] at hab
          rw [hmark₂] at hmk
          rcases markFor_false_above_cases (L := L) (K := K) T g pr.2 pr.1 _ hab hmk with
            ⟨h1, h2⟩ | ⟨hlo, _⟩
          · exact Or.inl ⟨h1, h2⟩
          · exact Or.inr ⟨hlo, hab⟩
        by_cases hm₁ : T + 1 ≤ o₁.1.minute.val ∧ o₁.2 = false <;>
          by_cases hm₂ : T + 1 ≤ o₂.1.minute.val ∧ o₂.2 = false
        · rcases hcase₁ hm₁ with hin₁ | hcr₁
          · rw [if_pos hm₁, if_pos hm₂, if_pos hin₁]
            split_ifs <;> omega
          · rcases hcase₂ hm₂ with hin₂ | hcr₂
            · rw [if_pos hm₁, if_pos hm₂, if_pos hin₂]
              split_ifs <;> omega
            · exact absurd ⟨hcr₁, hcr₂⟩ hone
        · rw [if_pos hm₁, if_neg hm₂]
          split_ifs <;> omega
        · rw [if_neg hm₁, if_pos hm₂]
          split_ifs <;> omega
        · rw [if_neg hm₁, if_neg hm₂]
          split_ifs <;> omega
      omega
    · rw [if_neg happ]
      omega
  · rw [dif_neg h, PMF.support_pure] at hsupp
    rw [Set.mem_singleton_iff.mp hsupp]
    omega

/-! ## Part 13 — the GENERIC affine-rate counter drift (refactor serving both counters).

Both `taintedCount` (rate `(θn/n)² + 2N/n` on the hour window) and `cleanAbove` (rate
`(X₁/n)² + 2N/n` on the bulk-capped window) are `+1`-increment counters with an AFFINE rise rate
`A + 2N/n`.  The time-dependent potential drift only uses that shape — so we prove it once,
generically over the kernel, the counter, the gate, and the constant `A`. -/

/-- **The generic affine-rate potential drift.**  For any Markov kernel, counter `N`, gate `G`,
and constant `A ≥ 0`: if on the gate the counter rises by at most one (a.e.) with probability at
most `A + 2·N/n`, and the sequences satisfy the slope/intercept recursions, then
`Φ_j = exp(s_j·N + b_j)` is a one-step supermartingale on `G`. -/
theorem affinePot_drift {α : Type*} [MeasurableSpace α] [DiscreteMeasurableSpace α]
    (Kk : Kernel α α) [IsMarkovKernel Kk] (N : α → ℕ) (G : Set α)
    (A : ℝ) (hA : 0 ≤ A) (n : ℕ) (hn : 2 ≤ n)
    (hrate : ∀ mc ∈ G, Kk mc {mc' | N mc < N mc'}
      ≤ ENNReal.ofReal (A + 2 * ((N mc : ℝ) / (n : ℝ))))
    (hstep : ∀ mc ∈ G, ∀ᵐ mc' ∂(Kk mc), N mc' ≤ N mc + 1)
    (s b : ℕ → ℝ)
    (hs1 : ∀ j, 0 ≤ s (j + 1))
    (hslope : ∀ j, s (j + 1) + 2 * (Real.exp (s (j + 1)) - 1) / (n : ℝ) ≤ s j)
    (hicept : ∀ j, b (j + 1) + A * (Real.exp (s (j + 1)) - 1) ≤ b j) :
    ∀ (j : ℕ), ∀ mc ∈ G,
      ∫⁻ mc', ENNReal.ofReal (Real.exp (s (j + 1) * (N mc' : ℝ) + b (j + 1))) ∂(Kk mc) ≤
        ENNReal.ofReal (Real.exp (s j * (N mc : ℝ) + b j)) := by
  classical
  intro j mc hmc
  haveI : IsProbabilityMeasure (Kk mc) :=
    (inferInstance : IsMarkovKernel Kk).isProbabilityMeasure mc
  set q : ℝ := A + 2 * ((N mc : ℝ) / (n : ℝ)) with hq
  have hq0 : 0 ≤ q := by rw [hq]; positivity
  have hmgf := ClimbTail.mgf_one_step (Kk mc) (s (j + 1)) (hs1 j)
    N (N mc) (hstep mc hmc) q hq0 (hrate mc hmc)
  have hsplit : ∀ mc', ENNReal.ofReal (Real.exp (s (j + 1) * (N mc' : ℝ) + b (j + 1)))
      = ENNReal.ofReal (Real.exp (b (j + 1)))
        * ENNReal.ofReal (Real.exp (s (j + 1) * (N mc' : ℝ))) := by
    intro mc'
    rw [← ENNReal.ofReal_mul (by positivity), ← Real.exp_add]
    ring_nf
  calc ∫⁻ mc', ENNReal.ofReal (Real.exp (s (j + 1) * (N mc' : ℝ) + b (j + 1))) ∂(Kk mc)
      = ENNReal.ofReal (Real.exp (b (j + 1)))
          * ∫⁻ mc', ENNReal.ofReal (Real.exp (s (j + 1) * (N mc' : ℝ))) ∂(Kk mc) := by
        rw [← MeasureTheory.lintegral_const_mul _ (Measurable.of_discrete)]
        exact lintegral_congr_ae (Filter.Eventually.of_forall (fun mc' => hsplit mc'))
    _ ≤ ENNReal.ofReal (Real.exp (b (j + 1)))
          * ENNReal.ofReal ((1 + q * (Real.exp (s (j + 1)) - 1))
              * Real.exp (s (j + 1) * (N mc : ℝ))) := by gcongr
    _ ≤ ENNReal.ofReal (Real.exp (s j * (N mc : ℝ) + b j)) := by
        rw [← ENNReal.ofReal_mul (by positivity)]
        apply ENNReal.ofReal_le_ofReal
        have hexp1 : (1 : ℝ) ≤ Real.exp (s (j + 1)) := Real.one_le_exp (hs1 j)
        have h1e : 1 + q * (Real.exp (s (j + 1)) - 1)
            ≤ Real.exp (q * (Real.exp (s (j + 1)) - 1)) := by
          have h := Real.add_one_le_exp (q * (Real.exp (s (j + 1)) - 1))
          linarith
        have hNnn : (0 : ℝ) ≤ (N mc : ℝ) := by positivity
        have hsl := hslope j
        have hic := hicept j
        have hslN' : s (j + 1) * (N mc : ℝ)
            + 2 * (Real.exp (s (j + 1)) - 1) / (n : ℝ) * (N mc : ℝ)
            ≤ s j * (N mc : ℝ) := by
          calc s (j + 1) * (N mc : ℝ)
              + 2 * (Real.exp (s (j + 1)) - 1) / (n : ℝ) * (N mc : ℝ)
              = (s (j + 1) + 2 * (Real.exp (s (j + 1)) - 1) / (n : ℝ)) * (N mc : ℝ) := by
                ring
            _ ≤ s j * (N mc : ℝ) := mul_le_mul_of_nonneg_right hsl hNnn
        calc Real.exp (b (j + 1)) * ((1 + q * (Real.exp (s (j + 1)) - 1))
              * Real.exp (s (j + 1) * (N mc : ℝ)))
            ≤ Real.exp (b (j + 1)) * (Real.exp (q * (Real.exp (s (j + 1)) - 1))
                * Real.exp (s (j + 1) * (N mc : ℝ))) := by
              apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
              apply mul_le_mul_of_nonneg_right h1e (Real.exp_pos _).le
          _ = Real.exp (b (j + 1) + q * (Real.exp (s (j + 1)) - 1)
                + s (j + 1) * (N mc : ℝ)) := by
              rw [← Real.exp_add, ← Real.exp_add]
              ring_nf
          _ ≤ Real.exp (s j * (N mc : ℝ) + b j) := by
              apply Real.exp_le_exp.mpr
              rw [hq, show (A + 2 * ((N mc : ℝ) / (n : ℝ)))
                  * (Real.exp (s (j + 1)) - 1)
                  = A * (Real.exp (s (j + 1)) - 1)
                    + 2 * (Real.exp (s (j + 1)) - 1) / (n : ℝ) * (N mc : ℝ) from by
                ring]
              linarith [hslN', hic]

/-- The bulk-capped window gate for the clean-count analysis: fixed population, the hour window,
and the level-`T` feeder capped at `X₁` (the window's end value of `x·n`; leaving it = the window
ended, benign). -/
def cleanGate (T n X₁ : ℕ) : Set (Config (MarkedAgent L K)) :=
  {mc | mc.card = n ∧ AllClockP3 (L := L) (K := K) (eraseConfig (L := L) (K := K) mc) ∧
    rBeyond (L := L) (K := K) T (eraseConfig (L := L) (K := K) mc) ≤ X₁}

/-- **The clean-count potential drift on the bulk-capped window** (instance of the generic
affine-rate drift at `A = (X₁/n)²`). -/
theorem cleanPot_drift (T θn n X₁ : ℕ) (hn : 2 ≤ n) (s b : ℕ → ℝ)
    (hs1 : ∀ j, 0 ≤ s (j + 1))
    (hslope : ∀ j, s (j + 1) + 2 * (Real.exp (s (j + 1)) - 1) / (n : ℝ) ≤ s j)
    (hicept : ∀ j, b (j + 1) + ((X₁ : ℝ) / (n : ℝ)) ^ 2 * (Real.exp (s (j + 1)) - 1) ≤ b j) :
    ∀ (j : ℕ), ∀ mc ∈ cleanGate (L := L) (K := K) T n X₁,
      ∫⁻ mc', ENNReal.ofReal
          (Real.exp (s (j + 1) * (cleanAbove (L := L) (K := K) T mc' : ℝ) + b (j + 1)))
          ∂(markedK (L := L) (K := K) T θn mc) ≤
        ENNReal.ofReal
          (Real.exp (s j * (cleanAbove (L := L) (K := K) T mc : ℝ) + b j)) := by
  apply affinePot_drift (markedK (L := L) (K := K) T θn)
    (cleanAbove (L := L) (K := K) T) (cleanGate (L := L) (K := K) T n X₁)
    (((X₁ : ℝ) / (n : ℝ)) ^ 2) (by positivity) n hn
  · -- the rate on the gate.
    rintro mc ⟨hcard, hw, hcap⟩
    have hcard2 : 2 ≤ mc.card := by omega
    refine le_trans (cleanAbove_rise_prob_le (L := L) (K := K) T θn mc hcard2 hw) ?_
    have hcntT : Multiset.countP (fun m : MarkedAgent L K => m.1.minute.val = T) mc ≤ X₁ :=
      le_trans (countT_le_rBeyond_erase (L := L) (K := K) T mc hw) hcap
    have hbound : ((Multiset.countP (fun m : MarkedAgent L K => m.1.minute.val = T) mc : ℝ)
        / (mc.card : ℝ)) ^ 2 ≤ ((X₁ : ℝ) / (n : ℝ)) ^ 2 := by
      rw [hcard]
      apply pow_le_pow_left₀ (by positivity)
      have hc : (Multiset.countP (fun m : MarkedAgent L K => m.1.minute.val = T) mc : ℝ)
          ≤ (X₁ : ℝ) := by exact_mod_cast hcntT
      gcongr
    calc ENNReal.ofReal
          (((Multiset.countP (fun m : MarkedAgent L K => m.1.minute.val = T) mc : ℝ)
            / (mc.card : ℝ)) ^ 2)
          + ENNReal.ofReal (2 * ((cleanAbove (L := L) (K := K) T mc : ℝ) / (mc.card : ℝ)))
        ≤ ENNReal.ofReal (((X₁ : ℝ) / (n : ℝ)) ^ 2)
          + ENNReal.ofReal (2 * ((cleanAbove (L := L) (K := K) T mc : ℝ) / (n : ℝ))) :=
          add_le_add (ENNReal.ofReal_le_ofReal hbound)
            (ENNReal.ofReal_le_ofReal (by rw [hcard]))
      _ = ENNReal.ofReal (((X₁ : ℝ) / (n : ℝ)) ^ 2
            + 2 * ((cleanAbove (L := L) (K := K) T mc : ℝ) / (n : ℝ))) := by
          rw [ENNReal.ofReal_add (by positivity) (by positivity)]
  · -- the a.e. step bound on the gate.
    rintro mc ⟨_, hw, _⟩
    exact ae_markedStep (L := L) (K := K) T θn mc _ (fun mc' hsupp =>
      cleanAbove_le_succ_on_support (L := L) (K := K) T θn mc mc' hw hsupp)
  · exact hs1
  · exact hslope
  · exact hicept

/-- **The clean-count tail over a window** (via the step-indexed engine): the probability that the
clean count reaches `Y` within `w` steps is at most the window escape mass (the feeder grew past
`X₁` or the hour closed — both benign window boundaries) plus `exp(s_0·y₀ + b_0 − s_w·Y − b_w)`. -/
theorem clean_marked_tail (T θn n X₁ : ℕ) (hn : 2 ≤ n) (s b : ℕ → ℝ)
    (hs1 : ∀ j, 0 ≤ s (j + 1))
    (hslope : ∀ j, s (j + 1) + 2 * (Real.exp (s (j + 1)) - 1) / (n : ℝ) ≤ s j)
    (hicept : ∀ j, b (j + 1) + ((X₁ : ℝ) / (n : ℝ)) ^ 2 * (Real.exp (s (j + 1)) - 1) ≤ b j)
    (w : ℕ) (hsw : 0 ≤ s w) (mc₀ : Config (MarkedAgent L K)) (Y : ℕ) :
    ((markedK (L := L) (K := K) T θn) ^ w) mc₀
        {mc | Y ≤ cleanAbove (L := L) (K := K) T mc} ≤
      (GatedDrift.killK (markedK (L := L) (K := K) T θn)
          (cleanGate (L := L) (K := K) T n X₁) ^ w) (some mc₀) {none} +
        ENNReal.ofReal
            (Real.exp (s 0 * (cleanAbove (L := L) (K := K) T mc₀ : ℝ) + b 0))
          / ENNReal.ofReal (Real.exp (s w * (Y : ℝ) + b w)) := by
  have hsub : {mc : Config (MarkedAgent L K) | Y ≤ cleanAbove (L := L) (K := K) T mc}
      ⊆ {mc | ENNReal.ofReal (Real.exp (s w * (Y : ℝ) + b w))
          ≤ ENNReal.ofReal
              (Real.exp (s w * (cleanAbove (L := L) (K := K) T mc : ℝ) + b w))} := by
    intro mc hmc
    rw [Set.mem_setOf_eq] at hmc ⊢
    apply ENNReal.ofReal_le_ofReal
    apply Real.exp_le_exp.mpr
    have hcast : (Y : ℝ) ≤ (cleanAbove (L := L) (K := K) T mc : ℝ) := by exact_mod_cast hmc
    nlinarith [hsw, hcast]
  refine le_trans (measure_mono hsub) ?_
  exact GatedDrift.stepIndexed_gated_tail (G := cleanGate (L := L) (K := K) T n X₁)
    (fun j mc => ENNReal.ofReal
      (Real.exp (s j * (cleanAbove (L := L) (K := K) T mc : ℝ) + b j)))
    (cleanPot_drift (L := L) (K := K) T θn n X₁ hn s b hs1 hslope hicept)
    w mc₀ (ENNReal.ofReal (Real.exp (s w * (Y : ℝ) + b w)))
    (by simp [Real.exp_pos]) ENNReal.ofReal_ne_top

/-! ## Part 14 — the LOWER one-step MGF for monotone counters (brick 3.5c input).

The window induction also needs the feeder `x = rBeyond T ∘ erase` to have GROWN by a definite
factor over the window — an epidemic LOWER bound.  For a MONOTONE `+1`-increment counter with rise
probability AT LEAST `r`, the decreasing exponential `exp(−s·N)` contracts by `1 − r(1−e^{−s})` —
the mirror of `mgf_one_step` (monotonicity replaces the `≤ +1` step bound). -/

/-- **The lower one-step MGF**: for a monotone counter with rise probability at least `r`,
`∫ exp(−s·N) dμ ≤ (1 − r(1−e^{−s}))·exp(−s·n₀)`. -/
theorem mgf_one_step_lower {α : Type*} [MeasurableSpace α] [DiscreteMeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] (s : ℝ) (hs : 0 ≤ s)
    (N : α → ℕ) (n₀ : ℕ)
    (hmono : ∀ᵐ y ∂μ, n₀ ≤ N y)
    (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1)
    (hprob : ENNReal.ofReal r ≤ μ {y | n₀ < N y}) :
    ∫⁻ y, ENNReal.ofReal (Real.exp (-(s * (N y : ℝ)))) ∂μ ≤
      ENNReal.ofReal ((1 - r * (1 - Real.exp (-s))) * Real.exp (-(s * (n₀ : ℝ)))) := by
  classical
  set D : Set α := {y | n₀ < N y} with hD
  have hD_meas : MeasurableSet D := DiscreteMeasurableSpace.forall_measurableSet _
  have hes : Real.exp (-s) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hes0 : 0 < Real.exp (-s) := Real.exp_pos _
  -- pointwise: on D the value is ≤ e^{−s}·e^{−s n₀}; off D (with monotonicity) it is ≤ e^{−s n₀}.
  have hpt : ∀ᵐ y ∂μ,
      ENNReal.ofReal (Real.exp (-(s * (N y : ℝ)))) ≤
        (if y ∈ D then ENNReal.ofReal (Real.exp (-s) * Real.exp (-(s * (n₀ : ℝ))))
          else ENNReal.ofReal (Real.exp (-(s * (n₀ : ℝ))))) := by
    filter_upwards [hmono] with y hy
    by_cases hyD : y ∈ D
    · simp only [hyD, if_true]
      apply ENNReal.ofReal_le_ofReal
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have hlt : n₀ < N y := hyD
      have hcast : (n₀ : ℝ) + 1 ≤ (N y : ℝ) := by exact_mod_cast hlt
      nlinarith [hs, hcast]
    · simp only [hyD, if_false]
      apply ENNReal.ofReal_le_ofReal
      apply Real.exp_le_exp.mpr
      have hcast : (n₀ : ℝ) ≤ (N y : ℝ) := by exact_mod_cast hy
      nlinarith [hs, hcast]
  calc ∫⁻ y, ENNReal.ofReal (Real.exp (-(s * (N y : ℝ)))) ∂μ
      ≤ ∫⁻ y, (if y ∈ D then ENNReal.ofReal (Real.exp (-s) * Real.exp (-(s * (n₀ : ℝ))))
          else ENNReal.ofReal (Real.exp (-(s * (n₀ : ℝ))))) ∂μ := lintegral_mono_ae hpt
    _ = ENNReal.ofReal (Real.exp (-s) * Real.exp (-(s * (n₀ : ℝ)))) * μ D
        + ENNReal.ofReal (Real.exp (-(s * (n₀ : ℝ)))) * μ Dᶜ := by
        rw [← lintegral_add_compl _ hD_meas]
        congr 1
        · rw [setLIntegral_congr_fun hD_meas
              (g := fun _ => ENNReal.ofReal (Real.exp (-s) * Real.exp (-(s * (n₀ : ℝ)))))
              (fun y hy => by simp only [hy, if_true])]
          rw [lintegral_const, Measure.restrict_apply_univ]
        · rw [setLIntegral_congr_fun hD_meas.compl
              (g := fun _ => ENNReal.ofReal (Real.exp (-(s * (n₀ : ℝ)))))
              (fun y hy => by simp only [Set.mem_compl_iff] at hy; simp only [hy, if_false])]
          rw [lintegral_const, Measure.restrict_apply_univ]
    _ ≤ ENNReal.ofReal ((1 - r * (1 - Real.exp (-s))) * Real.exp (-(s * (n₀ : ℝ)))) := by
        have hΦnn : (0 : ℝ) ≤ Real.exp (-(s * (n₀ : ℝ))) := (Real.exp_pos _).le
        have hμD_le_one : μ D ≤ 1 := by
          calc μ D ≤ μ Set.univ := measure_mono (Set.subset_univ _)
            _ = 1 := measure_univ
        have hμD_ne_top : μ D ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top hμD_le_one
        set pr := (μ D).toReal with hpr
        have hpr_nonneg : 0 ≤ pr := ENNReal.toReal_nonneg
        have hpr_le_one : pr ≤ 1 := by
          rw [hpr, show (1:ℝ) = (1 : ℝ≥0∞).toReal from ENNReal.toReal_one.symm]
          exact ENNReal.toReal_mono ENNReal.one_ne_top hμD_le_one
        have hr_le_pr : r ≤ pr := by
          rw [hpr]
          calc r = (ENNReal.ofReal r).toReal := (ENNReal.toReal_ofReal hr0).symm
            _ ≤ (μ D).toReal := ENNReal.toReal_mono hμD_ne_top hprob
        have hμD_eq : μ D = ENNReal.ofReal pr := (ENNReal.ofReal_toReal hμD_ne_top).symm
        have hμDc_eq : μ Dᶜ = ENNReal.ofReal (1 - pr) := by
          have hcompl := measure_compl hD_meas hμD_ne_top
          rw [show μ Set.univ = 1 from measure_univ] at hcompl
          rw [hcompl, hμD_eq,
            show (1 : ℝ≥0∞) = ENNReal.ofReal 1 from ENNReal.ofReal_one.symm,
            ← ENNReal.ofReal_sub 1 hpr_nonneg]
        rw [hμD_eq, hμDc_eq,
          ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul hΦnn,
          ← ENNReal.ofReal_add
            (mul_nonneg (by positivity) hpr_nonneg)
            (mul_nonneg hΦnn (by linarith))]
        apply ENNReal.ofReal_le_ofReal
        have hfac : Real.exp (-s) * Real.exp (-(s * (n₀ : ℝ))) * pr
              + Real.exp (-(s * (n₀ : ℝ))) * (1 - pr)
            = Real.exp (-(s * (n₀ : ℝ))) * (1 - pr * (1 - Real.exp (-s))) := by ring
        rw [hfac]
        have hbound : 1 - pr * (1 - Real.exp (-s)) ≤ 1 - r * (1 - Real.exp (-s)) := by
          have h1e : 0 ≤ 1 - Real.exp (-s) := by linarith
          nlinarith [mul_le_mul_of_nonneg_right hr_le_pr h1e]
        calc Real.exp (-(s * (n₀ : ℝ))) * (1 - pr * (1 - Real.exp (-s)))
            ≤ Real.exp (-(s * (n₀ : ℝ))) * (1 - r * (1 - Real.exp (-s))) :=
              mul_le_mul_of_nonneg_left hbound hΦnn
          _ = (1 - r * (1 - Real.exp (-s))) * Real.exp (-(s * (n₀ : ℝ))) := by ring

end EarlyDripMarked

end ExactMajority
