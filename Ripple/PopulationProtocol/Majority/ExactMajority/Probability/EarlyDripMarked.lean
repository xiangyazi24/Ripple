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

end EarlyDripMarked

end ExactMajority
