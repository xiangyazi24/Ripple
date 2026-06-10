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
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.ClockFrontProfile

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

/-! ## Part 15 — the sync rise mechanism (brick 3.5c-ii, deterministic half).

The feeder `x·n = rBeyond T ∘ erase` RISES whenever the scheduler picks a mixed (above-`T`,
below-`T`) pair — the sync pulls the laggard up.  This is the deterministic half; the scheduler
block lower bound (`P[mixed pair] = 2X(n−X)/(n(n−1))` exactly) composes it into the epidemic lower
rate feeding `mgf_one_step_lower`. -/

/-- The general-threshold bridge: on the `AllClockP3` window, the marked count at minute `≥ R` is
the erased clock tail. -/
theorem countGE_eq_rBeyond_erase (R : ℕ) (mc : Config (MarkedAgent L K))
    (hw : AllClockP3 (L := L) (K := K) (eraseConfig (L := L) (K := K) mc)) :
    Multiset.countP (fun m : MarkedAgent L K => R ≤ m.1.minute.val) mc
      = rBeyond (L := L) (K := K) R (eraseConfig (L := L) (K := K) mc) := by
  classical
  unfold rBeyond eraseConfig
  rw [Multiset.countP_map, Multiset.countP_eq_card_filter]
  congr 1
  apply Multiset.filter_congr
  intro m hm
  have hrole := hw m.1 (by
    unfold eraseConfig
    exact Multiset.mem_map_of_mem Prod.fst hm)
  unfold clockBeyondP
  constructor
  · intro hmin
    exact ⟨hrole.1, hmin⟩
  · rintro ⟨_, hmin⟩
    exact hmin

/-- **A mixed (above, below) pair raises the erased tail**: the sync pulls the laggard up to the
max minute, turning one above-`T` clock into two. -/
theorem mixed_pair_raises (T θn : ℕ) (mc : Config (MarkedAgent L K))
    (hw : AllClockP3 (L := L) (K := K) (eraseConfig (L := L) (K := K) mc))
    (pr : MarkedAgent L K × MarkedAgent L K)
    (happ : ({pr.1, pr.2} : Multiset (MarkedAgent L K)) ≤ mc)
    (hmix : (T ≤ pr.1.1.minute.val ∧ pr.2.1.minute.val < T) ∨
      (T ≤ pr.2.1.minute.val ∧ pr.1.1.minute.val < T)) :
    rBeyond (L := L) (K := K) T (eraseConfig (L := L) (K := K) mc)
      < rBeyond (L := L) (K := K) T
          (eraseConfig (L := L) (K := K) (markedStep (L := L) (K := K) T θn mc pr)) := by
  classical
  have hmem1 : pr.1 ∈ mc := Multiset.mem_of_le happ (Multiset.mem_cons_self _ _)
  have hmem2 : pr.2 ∈ mc := Multiset.mem_of_le happ
    (Multiset.mem_cons_of_mem (Multiset.mem_singleton_self _))
  have h1cp := hw pr.1.1 (Multiset.mem_map_of_mem Prod.fst hmem1)
  have h2cp := hw pr.2.1 (Multiset.mem_map_of_mem Prod.fst hmem2)
  have hne : pr.1.1.minute ≠ pr.2.1.minute := by
    intro hc
    have hv : pr.1.1.minute.val = pr.2.1.minute.val := congrArg Fin.val hc
    rcases hmix with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega
  have hsync := transition_p3_sync_minute (L := L) (K := K) pr.1.1 pr.2.1
    h1cp.1 h2cp.1 h1cp.2 h2cp.2 hne
  have hroles := Transition_clock_pair (L := L) (K := K) pr.1.1 pr.2.1
    h1cp.1 h2cp.1 (by omega) (by omega)
  have hmaxT : T ≤ (max pr.1.1.minute pr.2.1.minute).val := by
    rcases le_total pr.1.1.minute pr.2.1.minute with hle | hle
    · rw [max_eq_right hle]
      rcases hmix with ⟨h1, _⟩ | ⟨h1, _⟩
      · have : pr.1.1.minute.val ≤ pr.2.1.minute.val := hle
        omega
      · exact h1
    · rw [max_eq_left hle]
      rcases hmix with ⟨h1, _⟩ | ⟨h1, _⟩
      · exact h1
      · have : pr.2.1.minute.val ≤ pr.1.1.minute.val := hle
        omega
  -- the erased step in rest-decomposed form.
  rw [erase_markedStep (L := L) (K := K) T θn mc pr happ]
  have hmap_pair : Multiset.map Prod.fst ({pr.1, pr.2} : Multiset (MarkedAgent L K))
      = ({pr.1.1, pr.2.1} : Multiset (AgentState L K)) := by
    rw [show ({pr.1, pr.2} : Multiset (MarkedAgent L K)) = pr.1 ::ₘ {pr.2} from rfl,
      Multiset.map_cons, Multiset.map_singleton]
    rfl
  have hsub' : ({pr.1.1, pr.2.1} : Multiset (AgentState L K))
      ≤ eraseConfig (L := L) (K := K) mc := by
    rw [← hmap_pair]
    exact Multiset.map_le_map happ
  have hstep_eq : Protocol.scheduledStep (NonuniformMajority L K)
      (eraseConfig (L := L) (K := K) mc) (pr.1.1, pr.2.1)
      = eraseConfig (L := L) (K := K) mc - {pr.1.1, pr.2.1}
          + {(Transition L K pr.1.1 pr.2.1).1, (Transition L K pr.1.1 pr.2.1).2} := by
    unfold Protocol.scheduledStep Protocol.stepOrSelf
    rw [if_pos (show Protocol.Applicable (eraseConfig (L := L) (K := K) mc) pr.1.1 pr.2.1
      from hsub')]
    rfl
  rw [hstep_eq]
  unfold rBeyond
  rw [Multiset.countP_add, Multiset.countP_sub hsub']
  -- the two-element counts: consumed pair has exactly one above-`T` clock; produced pair has two.
  have hpair_le : Multiset.countP (fun a => clockBeyondP (L := L) (K := K) T a)
      ({pr.1.1, pr.2.1} : Multiset (AgentState L K))
        ≤ Multiset.countP (fun a => clockBeyondP (L := L) (K := K) T a)
          (eraseConfig (L := L) (K := K) mc) :=
    Multiset.countP_le_of_le _ hsub'
  have hcons : Multiset.countP (fun a => clockBeyondP (L := L) (K := K) T a)
      ({pr.1.1, pr.2.1} : Multiset (AgentState L K)) = 1 := by
    rw [countP_pair (L := L) (K := K) T pr.1.1 pr.2.1]
    rcases hmix with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [if_pos ⟨h1cp.1, h1⟩, if_neg
        (fun hc : clockBeyondP (L := L) (K := K) T pr.2.1 => absurd hc.2 (by omega))]
    · rw [if_neg
        (fun hc : clockBeyondP (L := L) (K := K) T pr.1.1 => absurd hc.2 (by omega)),
        if_pos ⟨h2cp.1, h1⟩]
  have hprod : Multiset.countP (fun a => clockBeyondP (L := L) (K := K) T a)
      ({(Transition L K pr.1.1 pr.2.1).1, (Transition L K pr.1.1 pr.2.1).2}
        : Multiset (AgentState L K)) = 2 := by
    rw [countP_pair (L := L) (K := K) T _ _]
    rw [if_pos ⟨hroles.1, by rw [hsync.1]; exact hmaxT⟩,
      if_pos ⟨hroles.2.1, by rw [hsync.2]; exact hmaxT⟩]
  rw [hcons, hprod]
  omega

/-- **The sync rise probability LOWER bound** (brick 3.5c-ii, probabilistic half): the scheduler
picks a mixed (above-`T`, below-`T`) ordered pair with probability exactly
`2·X·(n−X)/(n·(n−1))`, and every such pick raises the erased tail:

  `ofReal(2·X·(n−X)/(n(n−1))) ≤ P[rBeyond T ∘ erase rises]`. -/
theorem sync_rise_prob_ge (T θn : ℕ) (mc : Config (MarkedAgent L K)) (h : 2 ≤ mc.card)
    (hw : AllClockP3 (L := L) (K := K) (eraseConfig (L := L) (K := K) mc)) :
    ENNReal.ofReal
        (2 * ((rBeyond (L := L) (K := K) T (eraseConfig (L := L) (K := K) mc) : ℝ)
            * ((mc.card : ℝ)
              - (rBeyond (L := L) (K := K) T (eraseConfig (L := L) (K := K) mc) : ℝ)))
          / ((mc.card : ℝ) * ((mc.card : ℝ) - 1)))
      ≤ markedK (L := L) (K := K) T θn mc
          {mc' | rBeyond (L := L) (K := K) T (eraseConfig (L := L) (K := K) mc)
            < rBeyond (L := L) (K := K) T (eraseConfig (L := L) (K := K) mc')} := by
  classical
  set X := rBeyond (L := L) (K := K) T (eraseConfig (L := L) (K := K) mc) with hX
  set n := mc.card with hn
  rw [markedK_apply_pair (L := L) (K := K) T θn mc h _
    (DiscreteMeasurableSpace.forall_measurableSet _)]
  set SGE : Finset (MarkedAgent L K) :=
    Finset.univ.filter (fun m : MarkedAgent L K => T ≤ m.1.minute.val) with hSGE
  set SLT : Finset (MarkedAgent L K) :=
    Finset.univ.filter (fun m : MarkedAgent L K => m.1.minute.val < T) with hSLT
  -- the block counts: Σ_{SGE} count = X, Σ_{SLT} count = n − X.
  have hXge : (∑ m ∈ SGE, mc.count m) = X := by
    rw [hSGE, sum_count_filter_eq_countP _ mc, hX]
    exact countGE_eq_rBeyond_erase (L := L) (K := K) T mc hw
  have hXln : (∑ m ∈ SGE, mc.count m) + (∑ m ∈ SLT, mc.count m) = n := by
    rw [hSGE, hSLT, sum_count_filter_eq_countP _ mc, sum_count_filter_eq_countP _ mc, hn]
    rw [show Multiset.countP (fun m : MarkedAgent L K => m.1.minute.val < T) mc
      = Multiset.countP (fun m : MarkedAgent L K => ¬ T ≤ m.1.minute.val) mc from by
      rw [Multiset.countP_eq_card_filter, Multiset.countP_eq_card_filter]
      congr 1
      apply Multiset.filter_congr
      intro m _
      omega]
    rw [Multiset.countP_eq_card_filter, Multiset.countP_eq_card_filter,
      ← Multiset.card_add, Multiset.filter_add_not]
  have hXlt : (∑ m ∈ SLT, mc.count m) = n - X := by omega
  have hXn : X ≤ n := by omega
  -- the mixed block as two disjoint product finsets.
  set B : Finset (MarkedAgent L K × MarkedAgent L K) :=
    (SGE ×ˢ SLT) ∪ (SLT ×ˢ SGE) with hB
  -- every positive-probability block pair lands in the rise set.
  have hland : ∀ pr ∈ B, (mc.interactionPMF h) pr ≠ 0 →
      pr ∈ (markedStep (L := L) (K := K) T θn mc) ⁻¹'
        {mc' | X < rBeyond (L := L) (K := K) T (eraseConfig (L := L) (K := K) mc')} := by
    intro pr hprB hpos
    have hple := support_pair_le (L := L) (K := K) mc h pr hpos
    have hmix : (T ≤ pr.1.1.minute.val ∧ pr.2.1.minute.val < T) ∨
        (T ≤ pr.2.1.minute.val ∧ pr.1.1.minute.val < T) := by
      rw [hB, Finset.mem_union] at hprB
      rcases hprB with hpr | hpr
      · rw [Finset.mem_product, hSGE, hSLT] at hpr
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hpr
        exact Or.inl hpr
      · rw [Finset.mem_product, hSGE, hSLT] at hpr
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hpr
        exact Or.inr ⟨hpr.2, hpr.1⟩
    rw [Set.mem_preimage, Set.mem_setOf_eq, hX]
    exact mixed_pair_raises (L := L) (K := K) T θn mc hw pr hple hmix
  -- the measure of the preimage dominates the block sum.
  have hsum_le : (∑ pr ∈ B, (mc.interactionPMF h) pr)
      ≤ (mc.interactionPMF h).toMeasure
        ((markedStep (L := L) (K := K) T θn mc) ⁻¹'
          {mc' | X < rBeyond (L := L) (K := K) T (eraseConfig (L := L) (K := K) mc')}) := by
    set E := (markedStep (L := L) (K := K) T θn mc) ⁻¹'
      {mc' | X < rBeyond (L := L) (K := K) T (eraseConfig (L := L) (K := K) mc')} with hE
    calc (∑ pr ∈ B, (mc.interactionPMF h) pr)
        = ∑ pr ∈ B.filter (· ∈ E), (mc.interactionPMF h) pr := by
          symm
          apply Finset.sum_filter_of_ne
          intro pr hpr hne
          exact hland pr hpr hne
      _ = (mc.interactionPMF h).toMeasure ↑(B.filter (· ∈ E)) :=
          (PMF.toMeasure_apply_finset _ _).symm
      _ ≤ (mc.interactionPMF h).toMeasure E := by
          apply measure_mono
          intro pr hpr
          rw [Finset.coe_filter, Set.mem_setOf_eq] at hpr
          exact hpr.2
  refine le_trans ?_ hsum_le
  -- the block sum is exactly 2X(n−X)/(n(n−1)).
  have hdisj : Disjoint (SGE ×ˢ SLT) (SLT ×ˢ SGE) := by
    rw [Finset.disjoint_left]
    rintro ⟨m₁, m₂⟩ hp hq
    rw [Finset.mem_product, hSGE, hSLT] at hp hq
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp hq
    omega
  rw [hB, Finset.sum_union hdisj]
  -- each off-diagonal product block sums to X(n−X)/tp resp. (n−X)X/tp.
  have hoff : ∀ (S₁ S₂ : Finset (MarkedAgent L K)),
      (∀ m₁ ∈ S₁, ∀ m₂ ∈ S₂, m₁ ≠ m₂) →
      (∑ pr ∈ S₁ ×ˢ S₂, (mc.interactionPMF h) pr)
        = (((∑ m ∈ S₁, mc.count m) * (∑ m ∈ S₂, mc.count m) : ℕ) : ℝ≥0∞)
            / ((mc.totalPairs : ℕ) : ℝ≥0∞) := by
    intro S₁ S₂ hne
    rw [Finset.sum_product]
    calc (∑ m₁ ∈ S₁, ∑ m₂ ∈ S₂, (mc.interactionPMF h) (m₁, m₂))
        = ∑ m₁ ∈ S₁, ∑ m₂ ∈ S₂,
            ((mc.interactionCount m₁ m₂ : ℕ) : ℝ≥0∞) * ((mc.totalPairs : ℕ) : ℝ≥0∞)⁻¹ := by
          apply Finset.sum_congr rfl
          intro m₁ _
          apply Finset.sum_congr rfl
          intro m₂ _
          show mc.interactionProb m₁ m₂ = _
          unfold Config.interactionProb
          rw [div_eq_mul_inv]
      _ = (∑ m₁ ∈ S₁, ∑ m₂ ∈ S₂, ((mc.interactionCount m₁ m₂ : ℕ) : ℝ≥0∞))
            * ((mc.totalPairs : ℕ) : ℝ≥0∞)⁻¹ := by
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro m₁ _
          rw [Finset.sum_mul]
      _ = (((∑ m ∈ S₁, mc.count m) * (∑ m ∈ S₂, mc.count m) : ℕ) : ℝ≥0∞)
            * ((mc.totalPairs : ℕ) : ℝ≥0∞)⁻¹ := by
          congr 1
          calc (∑ m₁ ∈ S₁, ∑ m₂ ∈ S₂, ((mc.interactionCount m₁ m₂ : ℕ) : ℝ≥0∞))
              = ∑ m₁ ∈ S₁, ((∑ m₂ ∈ S₂, mc.interactionCount m₁ m₂ : ℕ) : ℝ≥0∞) :=
                Finset.sum_congr rfl (fun m₁ _ => (Nat.cast_sum _ _).symm)
            _ = ((∑ m₁ ∈ S₁, ∑ m₂ ∈ S₂, mc.interactionCount m₁ m₂ : ℕ) : ℝ≥0∞) :=
                (Nat.cast_sum _ _).symm
            _ = (((∑ m ∈ S₁, mc.count m) * (∑ m ∈ S₂, mc.count m) : ℕ) : ℝ≥0∞) := by
                congr 1
                calc (∑ m₁ ∈ S₁, ∑ m₂ ∈ S₂, mc.interactionCount m₁ m₂)
                    = ∑ m₁ ∈ S₁, mc.count m₁ * (∑ m₂ ∈ S₂, mc.count m₂) := by
                      apply Finset.sum_congr rfl
                      intro m₁ hm₁
                      rw [Finset.mul_sum]
                      apply Finset.sum_congr rfl
                      intro m₂ hm₂
                      unfold Config.interactionCount
                      rw [if_neg (hne m₁ hm₁ m₂ hm₂)]
                  _ = (∑ m ∈ S₁, mc.count m) * (∑ m ∈ S₂, mc.count m) := by
                      rw [← Finset.sum_mul]
      _ = (((∑ m ∈ S₁, mc.count m) * (∑ m ∈ S₂, mc.count m) : ℕ) : ℝ≥0∞)
            / ((mc.totalPairs : ℕ) : ℝ≥0∞) := (div_eq_mul_inv _ _).symm
  have hne₁ : ∀ m₁ ∈ SGE, ∀ m₂ ∈ SLT, m₁ ≠ m₂ := by
    intro m₁ hm₁ m₂ hm₂ hc
    rw [hSGE] at hm₁
    rw [hSLT] at hm₂
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hm₁ hm₂
    rw [hc] at hm₁
    omega
  have hne₂ : ∀ m₁ ∈ SLT, ∀ m₂ ∈ SGE, m₁ ≠ m₂ := by
    intro m₁ hm₁ m₂ hm₂ hc
    rw [hSLT] at hm₁
    rw [hSGE] at hm₂
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hm₁ hm₂
    rw [hc] at hm₁
    omega
  rw [hoff SGE SLT hne₁, hoff SLT SGE hne₂, hXge, hXlt]
  -- combine and compare to the real-valued form.
  rw [ENNReal.div_add_div_same, ← Nat.cast_add]
  have htp : mc.totalPairs = n * (n - 1) := by rw [hn]; rfl
  rw [htp]
  rw [show ((X * (n - X) + (n - X) * X : ℕ) : ℝ≥0∞)
      = ENNReal.ofReal ((X * (n - X) + (n - X) * X : ℕ) : ℝ) from
      (ENNReal.ofReal_natCast _).symm,
    show ((n * (n - 1) : ℕ) : ℝ≥0∞) = ENNReal.ofReal ((n * (n - 1) : ℕ) : ℝ) from
      (ENNReal.ofReal_natCast _).symm]
  rw [← ENNReal.ofReal_div_of_pos (by
    have : 0 < n * (n - 1) := by
      apply Nat.mul_pos <;> omega
    exact_mod_cast this)]
  apply ENNReal.ofReal_le_ofReal
  have h2n : (2 : ℕ) ≤ n := by omega
  push_cast [Nat.cast_sub hXn, Nat.cast_sub (show 1 ≤ n from by omega)]
  apply le_of_eq
  ring

/-! ## Part 16 — the erased tail is monotone along the marked chain, and the lower-exp bound. -/

/-- The erased tail never decreases on the marked one-step support (the marks ride along; the
underlying clock minutes are monotone). -/
theorem rBeyond_erase_monotone (T θn R : ℕ) (mc mc' : Config (MarkedAgent L K))
    (hw : AllClockP3 (L := L) (K := K) (eraseConfig (L := L) (K := K) mc))
    (hsupp : mc' ∈ (markedPMF (L := L) (K := K) T θn mc).support) :
    rBeyond (L := L) (K := K) R (eraseConfig (L := L) (K := K) mc)
      ≤ rBeyond (L := L) (K := K) R (eraseConfig (L := L) (K := K) mc') := by
  classical
  unfold markedPMF at hsupp
  by_cases h : 2 ≤ mc.card
  · rw [dif_pos h] at hsupp
    rw [PMF.support_map] at hsupp
    obtain ⟨pr, _, hpr⟩ := hsupp
    subst hpr
    by_cases happ : ({pr.1, pr.2} : Multiset (MarkedAgent L K)) ≤ mc
    · rw [erase_markedStep (L := L) (K := K) T θn mc pr happ]
      unfold Protocol.scheduledStep
      exact rBeyond_stepOrSelf_ge (L := L) (K := K) R
        (eraseConfig (L := L) (K := K) mc) hw pr.1.1 pr.2.1
    · unfold markedStep
      rw [if_neg happ]
  · rw [dif_neg h, PMF.support_pure] at hsupp
    rw [Set.mem_singleton_iff.mp hsupp]

/-- `(1 - s)*s <= 1 - e^{-s}` for `s >= 0` (the lower-tail rate keeps a `(1-s)` fraction of `s`;
via `e^{-s} <= 1/(1+s)`). -/
theorem one_sub_exp_neg_ge {s : ℝ} (hs : 0 ≤ s) :
    (1 - s) * s ≤ 1 - Real.exp (-s) := by
  have hpos : (0 : ℝ) < 1 + s := by linarith
  have h1 : Real.exp (-s) ≤ 1 / (1 + s) := by
    rw [le_div_iff₀ hpos]
    calc Real.exp (-s) * (1 + s) ≤ Real.exp (-s) * Real.exp s := by
          apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
          linarith [Real.add_one_le_exp s]
      _ = 1 := by rw [← Real.exp_add]; simp
  have h2 : 1 / (1 + s) ≤ 1 - (1 - s) * s := by
    rw [div_le_iff₀ hpos]
    nlinarith [sq_nonneg s, mul_nonneg hs (sq_nonneg s)]
  linarith

/-! ## Part 17 — the feeder GROWTH lower tail (brick 3.5c-iv).

The decreasing potential `Φ_j = exp(−s_j·X)` (X = the erased tail) is a supermartingale on the
sub-bulk gate `{10X ≤ n}`: the sync rise rate is at least `1.8·X/n` there, and the INCREASING
slope sequence absorbs the X-proportional rate.  The step-indexed engine then bounds the LOWER
tail `P[X_w ≤ a] ≤ escape + exp(−s_0·X₀ + s_w·a)` — the "feeder grew by a definite factor per
window" input of the Lemma 6.3 induction. -/

/-- The sub-bulk growth gate: fixed population, the hour window, the feeder below `n/10`
(escape = the feeder passed `n/10` — even better growth, benign). -/
def growthGate (T n : ℕ) : Set (Config (MarkedAgent L K)) :=
  {mc | mc.card = n ∧ AllClockP3 (L := L) (K := K) (eraseConfig (L := L) (K := K) mc) ∧
    10 * rBeyond (L := L) (K := K) T (eraseConfig (L := L) (K := K) mc) ≤ n}

/-- On the growth gate the rise rate is at least `1.8·X/n` (and at most `0.18 ≤ 1`). -/
theorem growth_rate_ge (T θn n : ℕ) (hn : 2 ≤ n) (mc : Config (MarkedAgent L K))
    (hmc : mc ∈ growthGate (L := L) (K := K) T n) :
    ENNReal.ofReal (1.8 * ((rBeyond (L := L) (K := K) T
        (eraseConfig (L := L) (K := K) mc) : ℝ) / (n : ℝ)))
      ≤ markedK (L := L) (K := K) T θn mc
          {mc' | rBeyond (L := L) (K := K) T (eraseConfig (L := L) (K := K) mc)
            < rBeyond (L := L) (K := K) T (eraseConfig (L := L) (K := K) mc')} := by
  obtain ⟨hcard, hw, hgate⟩ := hmc
  have hcard2 : 2 ≤ mc.card := by omega
  refine le_trans ?_ (sync_rise_prob_ge (L := L) (K := K) T θn mc hcard2 hw)
  apply ENNReal.ofReal_le_ofReal
  set X := rBeyond (L := L) (K := K) T (eraseConfig (L := L) (K := K) mc) with hX
  have hXn : 10 * X ≤ n := hgate
  have hnpos : (0 : ℝ) < (mc.card : ℝ) := by
    have : 0 < mc.card := by omega
    exact_mod_cast (by omega : 0 < mc.card)
  rw [hcard] at hnpos ⊢
  -- 1.8·X/n ≤ 2X(n−X)/(n(n−1)) ⟸ 1.8(n−1) ≤ 2(n−X) ⟸ 10X ≤ n.
  by_cases hX0 : X = 0
  · rw [hX0]
    simp
  · have hX1 : (1 : ℕ) ≤ X := by omega
    have hXr : (0 : ℝ) < (X : ℝ) := by exact_mod_cast (by omega : 0 < X)
    have hXnr : 10 * (X : ℝ) ≤ (n : ℝ) := by exact_mod_cast hXn
    have hn1 : (0 : ℝ) < (n : ℝ) - 1 := by
      have : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      linarith
    have hnpos' : (0 : ℝ) < (n : ℝ) := by linarith
    rw [show 1.8 * ((X : ℝ) / (n : ℝ)) = (1.8 * (X : ℝ)) / (n : ℝ) from by ring,
      div_le_div_iff₀ hnpos' (by positivity)]
    have hred : 1.8 * ((n : ℝ) - 1) ≤ 2 * ((n : ℝ) - (X : ℝ)) := by nlinarith [hXnr]
    nlinarith [mul_le_mul_of_nonneg_left hred (mul_nonneg hXr.le hnpos'.le)]

/-- **The growth-potential drift** on the sub-bulk gate: with the INCREASING slope recursion
`s_j ≤ s_{j+1} + 1.8(1−e^{−s_{j+1}})/n`, the decreasing exponential `exp(−s_j·X)` is a one-step
supermartingale. -/
theorem growthPot_drift (T θn n : ℕ) (hn : 2 ≤ n) (s : ℕ → ℝ)
    (hs1 : ∀ j, 0 ≤ s (j + 1))
    (hslope : ∀ j, s j ≤ s (j + 1)
      + 1.8 * (1 - Real.exp (-(s (j + 1)))) / (n : ℝ)) :
    ∀ (j : ℕ), ∀ mc ∈ growthGate (L := L) (K := K) T n,
      ∫⁻ mc', ENNReal.ofReal (Real.exp (-(s (j + 1)
          * (rBeyond (L := L) (K := K) T (eraseConfig (L := L) (K := K) mc') : ℝ))))
          ∂(markedK (L := L) (K := K) T θn mc) ≤
        ENNReal.ofReal (Real.exp (-(s j
          * (rBeyond (L := L) (K := K) T (eraseConfig (L := L) (K := K) mc) : ℝ)))) := by
  classical
  intro j mc hmc
  obtain ⟨hcard, hw, hgate⟩ := hmc
  haveI : IsProbabilityMeasure (markedK (L := L) (K := K) T θn mc) :=
    (inferInstance : IsMarkovKernel (markedK (L := L) (K := K) T θn)).isProbabilityMeasure mc
  set X := rBeyond (L := L) (K := K) T (eraseConfig (L := L) (K := K) mc) with hX
  set r : ℝ := 1.8 * ((X : ℝ) / (n : ℝ)) with hr
  have hnpos : (0 : ℝ) < (n : ℝ) := by
    exact_mod_cast (by omega : 0 < n)
  have hr0 : 0 ≤ r := by rw [hr]; positivity
  have hr1 : r ≤ 1 := by
    rw [hr]
    have hXn : 10 * X ≤ n := hgate
    have hXnr : 10 * (X : ℝ) ≤ (n : ℝ) := by exact_mod_cast hXn
    have hdiv : (X : ℝ) / (n : ℝ) ≤ 1 / 10 := by
      rw [div_le_div_iff₀ hnpos (by norm_num)]
      linarith
    nlinarith [hdiv]
  have hmono : ∀ᵐ mc' ∂(markedK (L := L) (K := K) T θn mc),
      X ≤ rBeyond (L := L) (K := K) T (eraseConfig (L := L) (K := K) mc') :=
    ae_markedStep (L := L) (K := K) T θn mc _ (fun mc' hsupp =>
      rBeyond_erase_monotone (L := L) (K := K) T θn T mc mc' hw hsupp)
  have hprob := growth_rate_ge (L := L) (K := K) T θn n hn mc ⟨hcard, hw, hgate⟩
  have hlow := mgf_one_step_lower (markedK (L := L) (K := K) T θn mc) (s (j + 1)) (hs1 j)
    (fun mc' => rBeyond (L := L) (K := K) T (eraseConfig (L := L) (K := K) mc')) X
    hmono r hr0 hr1 (by rw [hr]; exact hprob)
  refine le_trans hlow ?_
  apply ENNReal.ofReal_le_ofReal
  -- (1 − r(1−e^{−s'}))·e^{−s'X} ≤ e^{−r(1−e^{−s'})}·e^{−s'X} ≤ e^{−s_j X}.
  have hes : 0 ≤ 1 - Real.exp (-(s (j + 1))) := by
    have := Real.exp_le_one_iff.mpr (by linarith [hs1 j] : -(s (j + 1)) ≤ 0)
    linarith
  have h1e : 1 - r * (1 - Real.exp (-(s (j + 1))))
      ≤ Real.exp (-(r * (1 - Real.exp (-(s (j + 1)))))) := by
    have h := Real.add_one_le_exp (-(r * (1 - Real.exp (-(s (j + 1))))))
    linarith
  calc (1 - r * (1 - Real.exp (-(s (j + 1))))) * Real.exp (-(s (j + 1) * (X : ℝ)))
      ≤ Real.exp (-(r * (1 - Real.exp (-(s (j + 1))))))
          * Real.exp (-(s (j + 1) * (X : ℝ))) :=
        mul_le_mul_of_nonneg_right h1e (Real.exp_pos _).le
    _ = Real.exp (-(r * (1 - Real.exp (-(s (j + 1))))) - s (j + 1) * (X : ℝ)) := by
        rw [← Real.exp_add]
        ring_nf
    _ ≤ Real.exp (-(s j * (X : ℝ))) := by
        apply Real.exp_le_exp.mpr
        have hXnn : (0 : ℝ) ≤ (X : ℝ) := by positivity
        have hsl := hslope j
        have hslX : s j * (X : ℝ) ≤ (s (j + 1)
            + 1.8 * (1 - Real.exp (-(s (j + 1)))) / (n : ℝ)) * (X : ℝ) :=
          mul_le_mul_of_nonneg_right hsl hXnn
        rw [hr]
        have hbridge : 1.8 * ((X : ℝ) / (n : ℝ)) * (1 - Real.exp (-(s (j + 1))))
            = 1.8 * (1 - Real.exp (-(s (j + 1)))) / (n : ℝ) * (X : ℝ) := by ring
        have hslX' : s j * (X : ℝ) ≤ s (j + 1) * (X : ℝ)
            + 1.8 * (1 - Real.exp (-(s (j + 1)))) / (n : ℝ) * (X : ℝ) := by
          calc s j * (X : ℝ) ≤ (s (j + 1)
              + 1.8 * (1 - Real.exp (-(s (j + 1)))) / (n : ℝ)) * (X : ℝ) := hslX
            _ = s (j + 1) * (X : ℝ)
                + 1.8 * (1 - Real.exp (-(s (j + 1)))) / (n : ℝ) * (X : ℝ) := by ring
        linarith [hbridge, hslX']

/-- **The feeder growth lower tail** (brick 3.5c-iv capstone): over `w` steps from `mc₀`,

  `P[X_w ≤ a] ≤ sub-bulk escape + exp(−s_0·X₀ + s_w·a)`

— with the geometric increasing slopes this reads `P[X grew by less than the window factor] ≤
escape + exp(−Θ(X₀))`, the x-growth input of the Lemma 6.3 window induction. -/
theorem growth_marked_tail (T θn n : ℕ) (hn : 2 ≤ n) (s : ℕ → ℝ)
    (hs1 : ∀ j, 0 ≤ s (j + 1))
    (hslope : ∀ j, s j ≤ s (j + 1)
      + 1.8 * (1 - Real.exp (-(s (j + 1)))) / (n : ℝ))
    (w : ℕ) (hsw : 0 ≤ s w) (mc₀ : Config (MarkedAgent L K)) (a : ℕ) :
    ((markedK (L := L) (K := K) T θn) ^ w) mc₀
        {mc | rBeyond (L := L) (K := K) T (eraseConfig (L := L) (K := K) mc) ≤ a} ≤
      (GatedDrift.killK (markedK (L := L) (K := K) T θn)
          (growthGate (L := L) (K := K) T n) ^ w) (some mc₀) {none} +
        ENNReal.ofReal (Real.exp (-(s 0
            * (rBeyond (L := L) (K := K) T (eraseConfig (L := L) (K := K) mc₀) : ℝ))))
          / ENNReal.ofReal (Real.exp (-(s w * (a : ℝ)))) := by
  have hsub : {mc : Config (MarkedAgent L K) |
      rBeyond (L := L) (K := K) T (eraseConfig (L := L) (K := K) mc) ≤ a}
      ⊆ {mc | ENNReal.ofReal (Real.exp (-(s w * (a : ℝ))))
          ≤ ENNReal.ofReal (Real.exp (-(s w
            * (rBeyond (L := L) (K := K) T (eraseConfig (L := L) (K := K) mc) : ℝ))))} := by
    intro mc hmc
    rw [Set.mem_setOf_eq] at hmc ⊢
    apply ENNReal.ofReal_le_ofReal
    apply Real.exp_le_exp.mpr
    have hcast : (rBeyond (L := L) (K := K) T (eraseConfig (L := L) (K := K) mc) : ℝ)
        ≤ (a : ℝ) := by exact_mod_cast hmc
    nlinarith [hsw, hcast]
  refine le_trans (measure_mono hsub) ?_
  exact GatedDrift.stepIndexed_gated_tail (G := growthGate (L := L) (K := K) T n)
    (fun j mc => ENNReal.ofReal (Real.exp (-(s j
      * (rBeyond (L := L) (K := K) T (eraseConfig (L := L) (K := K) mc) : ℝ)))))
    (growthPot_drift (L := L) (K := K) T θn n hn s hs1 hslope)
    w mc₀ (ENNReal.ofReal (Real.exp (-(s w * (a : ℝ)))))
    (by simp [Real.exp_pos]) ENNReal.ofReal_ne_top

/-! ## Part 18 — the per-window clean tail at the explicit ε-sequences (brick 3.5d input).

The window induction needs the branching factor per window to be `ρ^w` with `ρ = 1 + 2(1+ε)/n`
(`ρ^{wn-steps} ≈ e^{2(1+ε)·w-parallel}` — the paper-faithful epidemic factor), which requires the
sharp bound `e^x − 1 ≤ (1+ε)x` (valid while every slope stays `≤ ε/(1+ε)`). -/

/-- **The per-window clean tail, explicit sequences**: with the geometric slope at ratio
`ρ = 1 + 2(1+ε)/n` and the matching linear intercept,

  `P[cleanAbove ≥ Y at w] ≤ window-escape + exp(σρ^w·Y₀ + (X₁/n)²(1+ε)σρ^w·w − σ·Y)`

provided `σρ^w ≤ ε/(1+ε)`. -/
theorem clean_marked_tail_explicit (T θn n X₁ : ℕ) (hn : 2 ≤ n)
    (σ ε : ℝ) (hσ : 0 < σ) (hε : 0 < ε) (w : ℕ)
    (hsmall : σ * (1 + 2 * (1 + ε) / (n : ℝ)) ^ w ≤ ε / (1 + ε))
    (mc₀ : Config (MarkedAgent L K)) (Y : ℕ) :
    ((markedK (L := L) (K := K) T θn) ^ w) mc₀
        {mc | Y ≤ cleanAbove (L := L) (K := K) T mc} ≤
      (GatedDrift.killK (markedK (L := L) (K := K) T θn)
          (cleanGate (L := L) (K := K) T n X₁) ^ w) (some mc₀) {none} +
        ENNReal.ofReal
          (Real.exp (σ * (1 + 2 * (1 + ε) / (n : ℝ)) ^ w
              * (cleanAbove (L := L) (K := K) T mc₀ : ℝ)
            + ((X₁ : ℝ) / (n : ℝ)) ^ 2 * (1 + ε) * σ
                * (1 + 2 * (1 + ε) / (n : ℝ)) ^ w * (w : ℝ)
            - σ * (Y : ℝ))) := by
  classical
  have hnpos : (0 : ℝ) < (n : ℝ) := by
    exact_mod_cast (by omega : 0 < n)
  have h1ε : (0 : ℝ) < 1 + ε := by linarith
  set ρ : ℝ := 1 + 2 * (1 + ε) / (n : ℝ) with hρ
  have hρ1 : (1 : ℝ) ≤ ρ := by
    rw [hρ]
    have h0 : (0 : ℝ) ≤ 2 * (1 + ε) / (n : ℝ) := by positivity
    linarith
  have hρpos : (0 : ℝ) < ρ := by linarith
  have hρ0 : ρ ≠ 0 := by linarith
  set A : ℝ := ((X₁ : ℝ) / (n : ℝ)) ^ 2 with hA
  have hAnn : 0 ≤ A := by rw [hA]; positivity
  set β : ℝ := A * (1 + ε) * σ * ρ ^ w with hβ
  set s : ℕ → ℝ := fun j => σ * ρ ^ ((w : ℤ) - (j : ℤ)) with hs
  set b : ℕ → ℝ := fun j => β * (((w : ℤ) - (j : ℤ) : ℤ) : ℝ) with hb
  have hs_pos : ∀ j, 0 < s j := by
    intro j
    rw [hs]
    positivity
  have hs_le : ∀ j, s j ≤ ε / (1 + ε) := by
    intro j
    rw [hs]
    calc σ * ρ ^ ((w : ℤ) - (j : ℤ)) ≤ σ * ρ ^ (w : ℤ) := by
          apply mul_le_mul_of_nonneg_left _ hσ.le
          apply zpow_le_zpow_right₀ hρ1
          omega
      _ = σ * ρ ^ w := by rw [zpow_natCast]
      _ ≤ ε / (1 + ε) := hsmall
  have hs1 : ∀ j, 0 ≤ s (j + 1) := fun j => (hs_pos (j + 1)).le
  have hexpb : ∀ j, Real.exp (s (j + 1)) - 1 ≤ (1 + ε) * s (j + 1) := fun j =>
    exp_sub_one_le_mul (hs_pos (j + 1)).le hε (hs_le (j + 1))
  have hslope : ∀ j, s (j + 1) + 2 * (Real.exp (s (j + 1)) - 1) / (n : ℝ) ≤ s j := by
    intro j
    have hstep : s (j + 1) * ρ = s j := by
      rw [hs]
      show σ * ρ ^ ((w : ℤ) - ((j : ℕ) + 1 : ℕ)) * ρ = σ * ρ ^ ((w : ℤ) - (j : ℤ))
      rw [mul_assoc, ← zpow_add_one₀ hρ0]
      congr 1
      push_cast
      ring_nf
    have hd : 2 * (Real.exp (s (j + 1)) - 1) / (n : ℝ)
        ≤ 2 * ((1 + ε) * s (j + 1)) / (n : ℝ) := by
      apply div_le_div_of_nonneg_right (by linarith [hexpb j]) hnpos.le
    calc s (j + 1) + 2 * (Real.exp (s (j + 1)) - 1) / (n : ℝ)
        ≤ s (j + 1) + 2 * ((1 + ε) * s (j + 1)) / (n : ℝ) := by linarith
      _ = s (j + 1) * ρ := by
          rw [hρ]
          field_simp
      _ = s j := hstep
  have hicept : ∀ j, b (j + 1)
      + ((X₁ : ℝ) / (n : ℝ)) ^ 2 * (Real.exp (s (j + 1)) - 1) ≤ b j := by
    intro j
    have hsmax : s (j + 1) ≤ σ * ρ ^ w := by
      rw [hs]
      calc σ * ρ ^ ((w : ℤ) - (((j : ℕ) + 1 : ℕ) : ℤ)) ≤ σ * ρ ^ (w : ℤ) := by
            apply mul_le_mul_of_nonneg_left _ hσ.le
            apply zpow_le_zpow_right₀ hρ1
            push_cast
            omega
        _ = σ * ρ ^ w := by rw [zpow_natCast]
    have hbdiff : b j - b (j + 1) = β := by
      rw [hb]
      push_cast
      ring
    have hkey : A * (Real.exp (s (j + 1)) - 1) ≤ β := by
      calc A * (Real.exp (s (j + 1)) - 1)
          ≤ A * ((1 + ε) * s (j + 1)) := mul_le_mul_of_nonneg_left (hexpb j) hAnn
        _ ≤ A * ((1 + ε) * (σ * ρ ^ w)) := by
            apply mul_le_mul_of_nonneg_left _ hAnn
            apply mul_le_mul_of_nonneg_left hsmax (by linarith)
        _ = β := by rw [hβ]; ring
    rw [← hA]
    linarith
  have htail := clean_marked_tail (L := L) (K := K) T θn n X₁ hn s b hs1 hslope
    hicept w (hs_pos w).le mc₀ Y
  refine le_trans htail ?_
  gcongr
  have hs0 : s 0 = σ * ρ ^ w := by
    rw [hs]
    show σ * ρ ^ ((w : ℤ) - ((0 : ℕ) : ℤ)) = σ * ρ ^ w
    rw [show (w : ℤ) - ((0 : ℕ) : ℤ) = (w : ℤ) from by push_cast; ring, zpow_natCast]
  have hb0 : b 0 = β * (w : ℝ) := by
    rw [hb]
    push_cast
    ring
  have hsw : s w = σ := by
    rw [hs]
    show σ * ρ ^ ((w : ℤ) - ((w : ℕ) : ℤ)) = σ
    rw [sub_self, zpow_zero, mul_one]
  have hbw : b w = 0 := by
    rw [hb]
    push_cast
    ring
  rw [hs0, hb0, hsw, hbw]
  rw [← ENNReal.ofReal_div_of_pos (Real.exp_pos _), ← Real.exp_sub]
  apply ENNReal.ofReal_le_ofReal
  apply Real.exp_le_exp.mpr
  rw [hβ, hA]
  ring_nf
  exact le_refl _

/-- **The feeder growth lower tail, constant slope** (sufficient for the window induction): the
slope recursion is trivially satisfied by the constant sequence, giving

  `P[X_w ≤ a] ≤ sub-bulk escape + exp(−σ·(X₀ − a))`

— exponentially small in the missing growth `X₀ − a`; in the Lemma 6.3 window the feeder count
`X₀ ≥ θn` makes this `n^{-ω(1)}` for any constant growth-deficit fraction. -/
theorem growth_marked_tail_const (T θn n : ℕ) (hn : 2 ≤ n)
    (σ : ℝ) (hσ : 0 ≤ σ) (w : ℕ)
    (mc₀ : Config (MarkedAgent L K)) (a : ℕ) :
    ((markedK (L := L) (K := K) T θn) ^ w) mc₀
        {mc | rBeyond (L := L) (K := K) T (eraseConfig (L := L) (K := K) mc) ≤ a} ≤
      (GatedDrift.killK (markedK (L := L) (K := K) T θn)
          (growthGate (L := L) (K := K) T n) ^ w) (some mc₀) {none} +
        ENNReal.ofReal
          (Real.exp (-(σ
              * (rBeyond (L := L) (K := K) T (eraseConfig (L := L) (K := K) mc₀) : ℝ))
            + σ * (a : ℝ))) := by
  have hslope : ∀ j : ℕ, (fun _ : ℕ => σ) j ≤ (fun _ : ℕ => σ) (j + 1)
      + 1.8 * (1 - Real.exp (-((fun _ : ℕ => σ) (j + 1)))) / (n : ℝ) := by
    intro j
    have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
    have hes : Real.exp (-σ) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    have h0 : (0 : ℝ) ≤ 1.8 * (1 - Real.exp (-σ)) / (n : ℝ) := by
      apply div_nonneg _ hnpos.le
      nlinarith
    simpa using (by linarith : σ ≤ σ + 1.8 * (1 - Real.exp (-σ)) / (n : ℝ))
  have h := growth_marked_tail (L := L) (K := K) T θn n hn (fun _ => σ)
    (fun _ => hσ) hslope w hσ mc₀ a
  refine le_trans h ?_
  gcongr
  rw [← ENNReal.ofReal_div_of_pos (Real.exp_pos _), ← Real.exp_sub]
  apply ENNReal.ofReal_le_ofReal
  apply Real.exp_le_exp.mpr
  ring_nf
  exact le_refl _

/-! ## Part 19 — the per-window step (brick 3.5d-i).

The window induction's bad event `{Y_w > c·X_w²/n}` carries a RANDOM threshold.  The deterministic
split: for any growth target `a`, on `{X_w > a}` the random threshold dominates the deterministic
one, so

  `{Y_w > c·X_w²/n} ⊆ {X_w ≤ a} ∪ {Yt ≤ Y_w}`   (for `Yt ≤ c·a²/n + 1`),

and the per-window failure is bounded by the growth lower tail at `a` plus the clean upper tail at
`Yt` (plus the two benign window escapes). -/

/-- The deterministic-threshold split of the per-window bad event. -/
theorem window_bad_subset (T : ℕ) (n : ℕ) (cc : ℝ) (hcc : 0 ≤ cc) (a Yt : ℕ)
    (hYt : (Yt : ℝ) ≤ cc * (a : ℝ) ^ 2 / (n : ℝ) + 1) :
    {mc : Config (MarkedAgent L K) |
        cc * (rBeyond (L := L) (K := K) T (eraseConfig (L := L) (K := K) mc) : ℝ) ^ 2
            / (n : ℝ)
          < (cleanAbove (L := L) (K := K) T mc : ℝ)} ⊆
      {mc : Config (MarkedAgent L K) |
          rBeyond (L := L) (K := K) T (eraseConfig (L := L) (K := K) mc) ≤ a} ∪
        {mc : Config (MarkedAgent L K) | Yt ≤ cleanAbove (L := L) (K := K) T mc} := by
  intro mc hmc
  rw [Set.mem_setOf_eq] at hmc
  by_cases hX : rBeyond (L := L) (K := K) T (eraseConfig (L := L) (K := K) mc) ≤ a
  · exact Or.inl hX
  · right
    rw [Set.mem_setOf_eq]
    have hXa : (a : ℝ) ≤ (rBeyond (L := L) (K := K) T
        (eraseConfig (L := L) (K := K) mc) : ℝ) := by
      have : a ≤ rBeyond (L := L) (K := K) T (eraseConfig (L := L) (K := K) mc) := by omega
      exact_mod_cast this
    have hsq : cc * (a : ℝ) ^ 2 / (n : ℝ)
        ≤ cc * (rBeyond (L := L) (K := K) T
            (eraseConfig (L := L) (K := K) mc) : ℝ) ^ 2 / (n : ℝ) := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      apply mul_le_mul_of_nonneg_left _ hcc
      apply pow_le_pow_left₀ (by positivity) hXa
    have hY : cc * (a : ℝ) ^ 2 / (n : ℝ)
        < (cleanAbove (L := L) (K := K) T mc : ℝ) := lt_of_le_of_lt hsq hmc
    -- ℕ-valued Y exceeding a real `< Y` bound: Y ≥ ⌊bound⌋+1 ≥ Yt.
    have hcast : (Yt : ℝ) < (cleanAbove (L := L) (K := K) T mc : ℝ) + 1 := by
      calc (Yt : ℝ) ≤ cc * (a : ℝ) ^ 2 / (n : ℝ) + 1 := hYt
        _ < (cleanAbove (L := L) (K := K) T mc : ℝ) + 1 := by linarith
    have : Yt < cleanAbove (L := L) (K := K) T mc + 1 := by exact_mod_cast hcast
    omega

/-- **The per-window step** (brick 3.5d-i capstone): the per-window failure probability is at most
the growth lower tail at the target `a`, the clean upper tail at `Yt`, and the two benign window
escapes:

  `P[Y_w > c·X_w²/n] ≤ growth-escape + e^{−σg(X₀−a)} + clean-escape + e^{σρ^w Y₀ + βw − σYt}`. -/
theorem per_window_step (T θn n X₁ : ℕ) (hn : 2 ≤ n)
    (cc : ℝ) (hcc : 0 ≤ cc) (σg σ ε : ℝ) (hσg : 0 ≤ σg) (hσ : 0 < σ) (hε : 0 < ε)
    (w : ℕ) (hsmall : σ * (1 + 2 * (1 + ε) / (n : ℝ)) ^ w ≤ ε / (1 + ε))
    (mc₀ : Config (MarkedAgent L K)) (a Yt : ℕ)
    (hYt : (Yt : ℝ) ≤ cc * (a : ℝ) ^ 2 / (n : ℝ) + 1) :
    ((markedK (L := L) (K := K) T θn) ^ w) mc₀
        {mc | cc * (rBeyond (L := L) (K := K) T
              (eraseConfig (L := L) (K := K) mc) : ℝ) ^ 2 / (n : ℝ)
            < (cleanAbove (L := L) (K := K) T mc : ℝ)} ≤
      ((GatedDrift.killK (markedK (L := L) (K := K) T θn)
          (growthGate (L := L) (K := K) T n) ^ w) (some mc₀) {none} +
        ENNReal.ofReal (Real.exp (-(σg
            * (rBeyond (L := L) (K := K) T (eraseConfig (L := L) (K := K) mc₀) : ℝ))
          + σg * (a : ℝ)))) +
      ((GatedDrift.killK (markedK (L := L) (K := K) T θn)
          (cleanGate (L := L) (K := K) T n X₁) ^ w) (some mc₀) {none} +
        ENNReal.ofReal
          (Real.exp (σ * (1 + 2 * (1 + ε) / (n : ℝ)) ^ w
              * (cleanAbove (L := L) (K := K) T mc₀ : ℝ)
            + ((X₁ : ℝ) / (n : ℝ)) ^ 2 * (1 + ε) * σ
                * (1 + 2 * (1 + ε) / (n : ℝ)) ^ w * (w : ℝ)
            - σ * (Yt : ℝ)))) := by
  refine le_trans (measure_mono
    (window_bad_subset (L := L) (K := K) T n cc hcc a Yt hYt)) ?_
  refine le_trans (measure_union_le _ _) ?_
  exact add_le_add
    (growth_marked_tail_const (L := L) (K := K) T θn n hn σg hσg w mc₀ a)
    (clean_marked_tail_explicit (L := L) (K := K) T θn n X₁ hn σ ε hσ hε w hsmall mc₀ Yt)

/-! ## Part 20 — the checkpoint composition (brick 3.5d-ii).

The window induction chains the per-window failure over checkpoints via the Markov property: an
invariant with a uniform one-step (= one-window) failure bound `δ` from invariant states fails by
horizon `t` with probability at most `t·δ`.  Generic over the kernel — applied with the window
kernel `markedK^w`, so the horizon counts WINDOWS. -/

/-- **The invariant union bound**: if from every invariant state one kernel step breaks the
invariant with probability at most `δ`, then from an invariant start the invariant is broken at
time `t` with probability at most `t·δ`. -/
theorem invariant_union_bound {α : Type*} [MeasurableSpace α] [DiscreteMeasurableSpace α]
    (Kk : Kernel α α) [IsMarkovKernel Kk] (Inv : α → Prop) (δ : ℝ≥0∞)
    (hstep : ∀ x, Inv x → Kk x {y | ¬ Inv y} ≤ δ)
    (t : ℕ) (x₀ : α) (h0 : Inv x₀) :
    (Kk ^ t) x₀ {y | ¬ Inv y} ≤ (t : ℝ≥0∞) * δ := by
  classical
  have hmeas : MeasurableSet {y : α | ¬ Inv y} :=
    DiscreteMeasurableSpace.forall_measurableSet _
  induction t generalizing x₀ with
  | zero =>
      simp only [Nat.cast_zero, zero_mul, pow_zero]
      change (Kernel.id x₀) {y | ¬ Inv y} ≤ 0
      rw [Kernel.id_apply, Measure.dirac_apply' _ hmeas]
      simp [Set.indicator_of_notMem (show x₀ ∉ {y : α | ¬ Inv y} from fun hc => hc h0)]
  | succ t ih =>
      have hCK : (Kk ^ (t + 1)) x₀ {y | ¬ Inv y}
          = ∫⁻ b, (Kk ^ t) b {y | ¬ Inv y} ∂(Kk x₀) := by
        rw [show t + 1 = 1 + t from by ring,
          Kernel.pow_add_apply_eq_lintegral Kk 1 t x₀ hmeas, pow_one]
      rw [hCK]
      set E0 : Set α := {b | Inv b} with hE0
      have hE0_meas : MeasurableSet E0 := DiscreteMeasurableSpace.forall_measurableSet _
      rw [← lintegral_add_compl _ hE0_meas]
      have hbound0 : (∫⁻ b in E0, (Kk ^ t) b {y | ¬ Inv y} ∂(Kk x₀))
          ≤ (t : ℝ≥0∞) * δ := by
        calc (∫⁻ b in E0, (Kk ^ t) b {y | ¬ Inv y} ∂(Kk x₀))
            ≤ ∫⁻ _ in E0, (t : ℝ≥0∞) * δ ∂(Kk x₀) := by
              apply lintegral_mono_ae
              filter_upwards [ae_restrict_mem hE0_meas] with b hb
              exact ih b hb
          _ ≤ (t : ℝ≥0∞) * δ := by
              rw [lintegral_const, Measure.restrict_apply_univ]
              haveI : IsProbabilityMeasure (Kk x₀) :=
                (inferInstance : IsMarkovKernel Kk).isProbabilityMeasure x₀
              calc (t : ℝ≥0∞) * δ * (Kk x₀) E0
                  ≤ (t : ℝ≥0∞) * δ * 1 := by
                    gcongr
                    calc (Kk x₀) E0 ≤ (Kk x₀) Set.univ := measure_mono (Set.subset_univ _)
                      _ = 1 := measure_univ
                _ = (t : ℝ≥0∞) * δ := mul_one _
      have hE0c : E0ᶜ = {y : α | ¬ Inv y} := by
        ext b
        simp [hE0]
      have hbound1 : (∫⁻ b in E0ᶜ, (Kk ^ t) b {y | ¬ Inv y} ∂(Kk x₀)) ≤ δ := by
        haveI : ∀ s : ℕ, IsMarkovKernel (Kk ^ s) := by
          intro s
          induction s with
          | zero =>
              rw [pow_zero]
              exact inferInstanceAs (IsMarkovKernel (Kernel.id : Kernel α α))
          | succ s ihs =>
              rw [pow_succ]
              exact inferInstanceAs (IsMarkovKernel ((Kk ^ s) ∘ₖ Kk))
        calc (∫⁻ b in E0ᶜ, (Kk ^ t) b {y | ¬ Inv y} ∂(Kk x₀))
            ≤ ∫⁻ _ in E0ᶜ, (1 : ℝ≥0∞) ∂(Kk x₀) := by
              apply lintegral_mono_ae
              filter_upwards with b
              haveI : IsProbabilityMeasure ((Kk ^ t) b) :=
                (inferInstance : IsMarkovKernel (Kk ^ t)).isProbabilityMeasure b
              calc (Kk ^ t) b {y | ¬ Inv y}
                  ≤ (Kk ^ t) b Set.univ := measure_mono (Set.subset_univ _)
                _ = 1 := measure_univ
          _ = (Kk x₀) E0ᶜ := by rw [lintegral_const, Measure.restrict_apply_univ, one_mul]
          _ = (Kk x₀) {y | ¬ Inv y} := by rw [hE0c]
          _ ≤ δ := hstep x₀ h0
      calc (∫⁻ b in E0, (Kk ^ t) b {y | ¬ Inv y} ∂(Kk x₀))
            + (∫⁻ b in E0ᶜ, (Kk ^ t) b {y | ¬ Inv y} ∂(Kk x₀))
          ≤ (t : ℝ≥0∞) * δ + δ := add_le_add hbound0 hbound1
        _ = ((t + 1 : ℕ) : ℝ≥0∞) * δ := by
            rw [Nat.cast_add, Nat.cast_one, add_mul, one_mul]

/-- **The checkpoint composition**: the invariant union bound at the WINDOW kernel `Kk^w` — an
invariant with per-window failure `δ` from invariant states fails by `KK` windows with probability
at most `KK·δ`. -/
theorem checkpoint_composition {α : Type*} [MeasurableSpace α] [DiscreteMeasurableSpace α]
    (Kk : Kernel α α) [IsMarkovKernel Kk] (Inv : α → Prop) (w : ℕ) (δ : ℝ≥0∞)
    (hwindow : ∀ x, Inv x → (Kk ^ w) x {y | ¬ Inv y} ≤ δ)
    (KK : ℕ) (x₀ : α) (h0 : Inv x₀) :
    (Kk ^ (w * KK)) x₀ {y | ¬ Inv y} ≤ (KK : ℝ≥0∞) * δ := by
  haveI : ∀ s : ℕ, IsMarkovKernel (Kk ^ s) := by
    intro s
    induction s with
    | zero =>
        rw [pow_zero]
        exact inferInstanceAs (IsMarkovKernel (Kernel.id : Kernel α α))
    | succ s ihs =>
        rw [pow_succ]
        exact inferInstanceAs (IsMarkovKernel ((Kk ^ s) ∘ₖ Kk))
  rw [pow_mul]
  exact invariant_union_bound (Kk ^ w) Inv δ hwindow KK x₀ h0

/-! ## Part 21 — the stayed-in-gate coupling (brick 3.5d-iii a).

For a gate of the form `{M ≤ X₁}` with `M` MONOTONE along the chain, a trajectory whose ENDPOINT
satisfies `M ≤ X₁` never left the gate — so the real probability of `{bad ∧ M_end ≤ X₁}` is
bounded by the KILLED chain's alive-bad mass alone, with NO escape term.  This is what lets the
dyadic end-value slices of the window analysis use per-slice gate caps without paying an escape
mass per slice. -/

/-- Monotone quantities stay monotone through kernel powers (a.e.). -/
theorem ae_monotone_pow {α : Type*} [MeasurableSpace α] [DiscreteMeasurableSpace α]
    (Kk : Kernel α α) [IsMarkovKernel Kk] (M : α → ℕ)
    (hmono : ∀ x, ∀ᵐ y ∂(Kk x), M x ≤ M y)
    (t : ℕ) (x : α) :
    ∀ᵐ z ∂((Kk ^ t) x), M x ≤ M z := by
  classical
  induction t generalizing x with
  | zero =>
      simp only [pow_zero]
      change ∀ᵐ z ∂(Kernel.id x), M x ≤ M z
      rw [Kernel.id_apply,
        MeasureTheory.ae_dirac_iff (DiscreteMeasurableSpace.forall_measurableSet _)]
  | succ t ih =>
      rw [MeasureTheory.ae_iff]
      have hbad_meas : MeasurableSet {z : α | ¬ M x ≤ M z} :=
        DiscreteMeasurableSpace.forall_measurableSet _
      rw [show t + 1 = 1 + t from by ring,
        Kernel.pow_add_apply_eq_lintegral Kk 1 t x hbad_meas, pow_one,
        MeasureTheory.lintegral_eq_zero_iff (Kernel.measurable_coe _ hbad_meas)]
      filter_upwards [hmono x] with y hy
      have hsub : {z : α | ¬ M x ≤ M z} ⊆ {z : α | ¬ M y ≤ M z} := by
        intro z hz
        rw [Set.mem_setOf_eq] at hz ⊢
        omega
      have hzero : ((Kk ^ t) y) {z : α | ¬ M y ≤ M z} = 0 := by
        have h := ih y
        rwa [MeasureTheory.ae_iff] at h
      exact le_antisymm (le_trans (measure_mono hsub) hzero.le) zero_le'

/-- **The stayed-in-gate coupling**: with the gate `G = {M ≤ X₁}` and `M` monotone, the real
probability of ending bad WITH `M ≤ X₁` is bounded by the killed chain's alive-bad mass — no
escape term (a trajectory ending inside the gate never left it). -/
theorem real_le_killed_of_monotone {α : Type*} [MeasurableSpace α] [DiscreteMeasurableSpace α]
    [Inhabited α] (Kk : Kernel α α) [IsMarkovKernel Kk] (M : α → ℕ) (X₁ : ℕ)
    (hmono : ∀ x, ∀ᵐ y ∂(Kk x), M x ≤ M y)
    (bad : α → Prop) (t : ℕ) (x : α) :
    (Kk ^ t) x {y | bad y ∧ M y ≤ X₁} ≤
      (GatedDrift.killK Kk {x' | M x' ≤ X₁} ^ t) (some x)
        {o | ∃ y, o = some y ∧ bad y ∧ M y ≤ X₁} := by
  classical
  letI : MeasurableSpace (Option α) := GatedDrift.instOptionMS
  letI : DiscreteMeasurableSpace (Option α) := GatedDrift.instOptionDMS
  set G : Set α := {x' | M x' ≤ X₁} with hG
  induction t generalizing x with
  | zero =>
      rw [pow_zero, pow_zero]
      change (Measure.dirac x) {y | bad y ∧ M y ≤ X₁}
        ≤ (Measure.dirac (some x)) {o | ∃ y, o = some y ∧ bad y ∧ M y ≤ X₁}
      rw [Measure.dirac_apply' _ (DiscreteMeasurableSpace.forall_measurableSet _),
        Measure.dirac_apply' _ (DiscreteMeasurableSpace.forall_measurableSet _)]
      by_cases hb : bad x ∧ M x ≤ X₁
      · simp [Set.indicator_of_mem (show x ∈ {y | bad y ∧ M y ≤ X₁} from hb),
          Set.indicator_of_mem (show (some x) ∈
            {o : Option α | ∃ y, o = some y ∧ bad y ∧ M y ≤ X₁} from ⟨x, rfl, hb⟩)]
      · simp [Set.indicator_of_notMem (show x ∉ {y | bad y ∧ M y ≤ X₁} from hb)]
  | succ t ih =>
      have hmeasL : MeasurableSet {y : α | bad y ∧ M y ≤ X₁} :=
        DiscreteMeasurableSpace.forall_measurableSet _
      have hmeasR : MeasurableSet {o : Option α | ∃ y, o = some y ∧ bad y ∧ M y ≤ X₁} :=
        DiscreteMeasurableSpace.forall_measurableSet _
      rw [show t + 1 = 1 + t from by ring,
        Kernel.pow_add_apply_eq_lintegral Kk 1 t x hmeasL, pow_one,
        Kernel.pow_add_apply_eq_lintegral _ 1 t (some x) hmeasR, pow_one]
      by_cases hx : x ∈ G
      · rw [GatedDrift.killK_some_gated (K := Kk) (G := G) x hx,
          MeasureTheory.lintegral_map (Measurable.of_discrete) (Measurable.of_discrete)]
        exact lintegral_mono (fun y => ih y)
      · -- off the gate: M x > X₁, and monotonicity kills the LHS event entirely.
        have hMx : X₁ < M x := by
          rw [hG, Set.mem_setOf_eq, not_le] at hx
          exact hx
        have hzero : ∫⁻ y, (Kk ^ t) y {y' | bad y' ∧ M y' ≤ X₁} ∂(Kk x) = 0 := by
          rw [MeasureTheory.lintegral_eq_zero_iff
            (Kernel.measurable_coe _ hmeasL)]
          filter_upwards [hmono x] with y hy
          have h := ae_monotone_pow Kk M hmono t y
          rw [MeasureTheory.ae_iff] at h
          have hsub : {y' : α | bad y' ∧ M y' ≤ X₁} ⊆ {z : α | ¬ M y ≤ M z} := by
            intro z hz
            rw [Set.mem_setOf_eq] at hz ⊢
            omega
          exact le_antisymm (le_trans (measure_mono hsub) h.le) zero_le'
        rw [hzero]
        exact zero_le'

/-! ## Part 22 — the relative absorbing-exit coupling (brick 3.5d-iii b, the general device).

Generalizes `real_le_killed_of_monotone`: for a gate `G` whose complement is ABSORBING along the
chain — relative to a chain-invariant region `R` — every endpoint-in-`G` event is bounded by the
killed chain's alive mass with NO escape term.  The §6 slice gates ({hour window} ∩ {X ≤ X₁}) have
absorbing complements relative to the `AllClockGE3` window: phases never decrease (the hour-exit is
permanent) and the erased tail never decreases (the cap-exit is permanent). -/

/-- Leaving the gate is permanent (a.e., relative to the invariant region), through kernel
powers. -/
theorem ae_notG_pow {α : Type*} [MeasurableSpace α] [DiscreteMeasurableSpace α]
    (Kk : Kernel α α) [IsMarkovKernel Kk] (R G : Set α)
    (hRstep : ∀ x ∈ R, ∀ᵐ y ∂(Kk x), y ∈ R)
    (habs : ∀ x ∈ R, x ∉ G → ∀ᵐ y ∂(Kk x), y ∉ G)
    (t : ℕ) (x : α) (hxR : x ∈ R) (hxG : x ∉ G) :
    ∀ᵐ z ∂((Kk ^ t) x), z ∉ G := by
  classical
  induction t generalizing x with
  | zero =>
      simp only [pow_zero]
      change ∀ᵐ z ∂(Kernel.id x), z ∉ G
      rw [Kernel.id_apply,
        MeasureTheory.ae_dirac_iff (DiscreteMeasurableSpace.forall_measurableSet _)]
      exact hxG
  | succ t ih =>
      rw [MeasureTheory.ae_iff]
      have hbad_meas : MeasurableSet {z : α | ¬ z ∉ G} :=
        DiscreteMeasurableSpace.forall_measurableSet _
      rw [show t + 1 = 1 + t from by ring,
        Kernel.pow_add_apply_eq_lintegral Kk 1 t x hbad_meas, pow_one,
        MeasureTheory.lintegral_eq_zero_iff (Kernel.measurable_coe _ hbad_meas)]
      filter_upwards [hRstep x hxR, habs x hxR hxG] with y hyR hyG
      have h := ih y hyR hyG
      rwa [MeasureTheory.ae_iff] at h

/-- **The relative absorbing-exit coupling**: if the gate's complement is absorbing (relative to a
chain-invariant region containing the start), then any endpoint event INSIDE the gate is bounded by
the killed chain's alive-bad mass — no escape term. -/
theorem real_le_killed_of_absorbing {α : Type*} [MeasurableSpace α] [DiscreteMeasurableSpace α]
    [Inhabited α] (Kk : Kernel α α) [IsMarkovKernel Kk] (R G : Set α)
    (hRstep : ∀ x ∈ R, ∀ᵐ y ∂(Kk x), y ∈ R)
    (habs : ∀ x ∈ R, x ∉ G → ∀ᵐ y ∂(Kk x), y ∉ G)
    (bad : α → Prop) (hbadG : ∀ y, bad y → y ∈ G)
    (t : ℕ) (x : α) (hxR : x ∈ R) :
    (Kk ^ t) x {y | bad y} ≤
      (GatedDrift.killK Kk G ^ t) (some x) {o | ∃ y, o = some y ∧ bad y} := by
  classical
  letI : MeasurableSpace (Option α) := GatedDrift.instOptionMS
  letI : DiscreteMeasurableSpace (Option α) := GatedDrift.instOptionDMS
  induction t generalizing x with
  | zero =>
      rw [pow_zero, pow_zero]
      change (Measure.dirac x) {y | bad y}
        ≤ (Measure.dirac (some x)) {o | ∃ y, o = some y ∧ bad y}
      rw [Measure.dirac_apply' _ (DiscreteMeasurableSpace.forall_measurableSet _),
        Measure.dirac_apply' _ (DiscreteMeasurableSpace.forall_measurableSet _)]
      by_cases hb : bad x
      · simp [Set.indicator_of_mem (show x ∈ {y | bad y} from hb),
          Set.indicator_of_mem (show (some x) ∈
            {o : Option α | ∃ y, o = some y ∧ bad y} from ⟨x, rfl, hb⟩)]
      · simp [Set.indicator_of_notMem (show x ∉ {y | bad y} from hb)]
  | succ t ih =>
      have hmeasL : MeasurableSet {y : α | bad y} :=
        DiscreteMeasurableSpace.forall_measurableSet _
      have hmeasR : MeasurableSet {o : Option α | ∃ y, o = some y ∧ bad y} :=
        DiscreteMeasurableSpace.forall_measurableSet _
      rw [show t + 1 = 1 + t from by ring,
        Kernel.pow_add_apply_eq_lintegral Kk 1 t x hmeasL, pow_one,
        Kernel.pow_add_apply_eq_lintegral _ 1 t (some x) hmeasR, pow_one]
      by_cases hx : x ∈ G
      · rw [GatedDrift.killK_some_gated (K := Kk) (G := G) x hx,
          MeasureTheory.lintegral_map (Measurable.of_discrete) (Measurable.of_discrete)]
        apply lintegral_mono_ae
        filter_upwards [hRstep x hxR] with y hyR
        exact ih y hyR
      · -- off the gate: the complement is absorbing, so no endpoint can be bad (bad ⊆ G).
        have hzero : ∫⁻ y, (Kk ^ t) y {y' | bad y'} ∂(Kk x) = 0 := by
          rw [MeasureTheory.lintegral_eq_zero_iff (Kernel.measurable_coe _ hmeasL)]
          filter_upwards [hRstep x hxR, habs x hxR hx] with y hyR hyG
          have h := ae_notG_pow Kk R G hRstep habs t y hyR hyG
          rw [MeasureTheory.ae_iff] at h
          have hsub : {y' : α | bad y'} ⊆ {z : α | ¬ z ∉ G} := by
            intro z hz
            rw [Set.mem_setOf_eq] at hz ⊢
            exact fun hc => hc (hbadG z hz)
          exact le_antisymm (le_trans (measure_mono hsub) h.le) zero_le'
        rw [hzero]
        exact zero_le'

/-! ## Part 23 — the standalone step-indexed KILLED tail (the alive-mass bound the slices consume).

`stepIndexed_gated_tail` couples to the real chain and carries the escape; the dyadic slices use
`real_le_killed_of_absorbing` for the coupling instead, so they need the killed alive-mass tail by
itself. -/

/-- The step-indexed killed tail: under the gated drift, the killed chain's alive mass at
`{θ ≤ Φ_t}` is at most `Φ_0(x)/θ`. -/
theorem stepIndexed_killed_tail {α : Type*} [MeasurableSpace α] [DiscreteMeasurableSpace α]
    [Inhabited α] (Kk : Kernel α α) [IsMarkovKernel Kk] (G : Set α)
    (Φ : ℕ → α → ℝ≥0∞)
    (hdrift_G : ∀ (j : ℕ), ∀ x ∈ G, ∫⁻ y, Φ (j + 1) y ∂(Kk x) ≤ Φ j x)
    (t : ℕ) (x : α) (θ : ℝ≥0∞) (hθ0 : θ ≠ 0) (hθtop : θ ≠ ∞) :
    (GatedDrift.killK Kk G ^ t) (some x)
        {o | θ ≤ GatedDrift.killΦ (Φ t) o} ≤ Φ 0 x / θ := by
  classical
  letI : MeasurableSpace (Option α) := GatedDrift.instOptionMS
  letI : DiscreteMeasurableSpace (Option α) := GatedDrift.instOptionDMS
  have hkill_drift : ∀ (j : ℕ) (o : Option α),
      ∫⁻ p, GatedDrift.killΦ (Φ (j + 1)) p ∂(GatedDrift.killK Kk G o)
        ≤ GatedDrift.killΦ (Φ j) o := by
    intro j o
    rcases o with _ | x'
    · rw [GatedDrift.killK_none,
        MeasureTheory.lintegral_dirac' _ (GatedDrift.killΦ_measurable _)]
      simp
    · by_cases hx : x' ∈ G
      · rw [GatedDrift.killK_some_gated x' hx,
          MeasureTheory.lintegral_map (GatedDrift.killΦ_measurable _)
            (Measurable.of_discrete)]
        simp only [GatedDrift.killΦ_some]
        exact hdrift_G j x' hx
      · have hdead : GatedDrift.killK Kk G (some x')
            = Measure.dirac (none : Option α) := by
          unfold GatedDrift.killK
          rw [Kernel.piecewise_apply,
            if_neg (fun h => hx ((GatedDrift.some_mem_image_iff x').1 h)),
            Kernel.const_apply]
        rw [hdead, MeasureTheory.lintegral_dirac' _ (GatedDrift.killΦ_measurable _)]
        simp
  have hdecay := GatedDrift.lintegral_stepIndexed_decay (GatedDrift.killK Kk G) t
    (fun j => GatedDrift.killΦ (Φ j)) (fun j => GatedDrift.killΦ_measurable _)
    hkill_drift (some x)
  simp only [GatedDrift.killΦ_some] at hdecay
  have hMarkov : θ * (GatedDrift.killK Kk G ^ t) (some x)
      {o | θ ≤ GatedDrift.killΦ (Φ t) o} ≤ Φ 0 x :=
    le_trans (mul_meas_ge_le_lintegral₀
      (hf := (GatedDrift.killΦ_measurable _).aemeasurable) (ε := θ)) hdecay
  calc (GatedDrift.killK Kk G ^ t) (some x) {o | θ ≤ GatedDrift.killΦ (Φ t) o}
      = (θ⁻¹ * θ) * (GatedDrift.killK Kk G ^ t) (some x)
          {o | θ ≤ GatedDrift.killΦ (Φ t) o} := by
        simp [ENNReal.inv_mul_cancel hθ0 hθtop]
    _ = θ⁻¹ * (θ * (GatedDrift.killK Kk G ^ t) (some x)
          {o | θ ≤ GatedDrift.killΦ (Φ t) o}) := by
        simp [mul_assoc]
    _ ≤ θ⁻¹ * Φ 0 x := by gcongr
    _ = Φ 0 x / θ := by rw [mul_comm]; rfl

/-! ## Part 24 — the absorbing inputs for the slice gates (brick 3.5d-iii d).

The slice gate `{AllClockP3 ∘ erase ∧ X ≤ X₁}` has an absorbing complement RELATIVE to the
`AllClockGE3` region: within the region, leaving `AllClockP3` means some agent reached phase 4
(permanent — phases never decrease), and `X = rBeyond T ∘ erase` never decreases (clock minutes
are monotone at phases ≥ 3).  These are the `hRstep`/`habs` inputs of
`real_le_killed_of_absorbing`. -/

/-- Any chosen-pair real update preserves `AllClockGE3` (per-pair form of
`AllClockGE3_absorbing`). -/
theorem allClockGE3_stepOrSelf (c : Config (AgentState L K))
    (hw : AllClockGE3 (L := L) (K := K) c) (r₁ r₂ : AgentState L K) :
    AllClockGE3 (L := L) (K := K)
      (Protocol.stepOrSelf (NonuniformMajority L K) c r₁ r₂) := by
  classical
  by_cases happ : Protocol.Applicable c r₁ r₂
  · have hc2 : 2 ≤ c.card := by
      have hle : ({r₁, r₂} : Multiset (AgentState L K)).card ≤ c.card :=
        Multiset.card_le_card happ
      simpa using hle
    have hsupp : Protocol.stepOrSelf (NonuniformMajority L K) c r₁ r₂
        ∈ ((NonuniformMajority L K).stepDistOrSelf c).support := by
      rw [show (NonuniformMajority L K).stepDistOrSelf c
          = (NonuniformMajority L K).stepDist c hc2 by
        unfold Protocol.stepDistOrSelf; rw [dif_pos hc2]]
      unfold Protocol.stepDist
      rw [PMF.support_map]
      refine ⟨(r₁, r₂), ?_, rfl⟩
      show c.interactionProb r₁ r₂ ≠ 0
      have hcount : c.interactionCount r₁ r₂ ≠ 0 := by
        unfold Config.interactionCount
        by_cases h12 : r₁ = r₂
        · rw [if_pos h12]
          subst h12
          have h2 : 2 ≤ c.count r₁ := by
            have h := Multiset.le_iff_count.mp happ r₁
            have hpair : Multiset.count r₁ ({r₁, r₁} : Multiset (AgentState L K)) = 2 := by
              rw [show ({r₁, r₁} : Multiset (AgentState L K)) = r₁ ::ₘ {r₁} from rfl,
                Multiset.count_cons_self, Multiset.count_singleton, if_pos rfl]
            rw [hpair] at h
            exact h
          have hpos : 0 < c.count r₁ * (c.count r₁ - 1) :=
            Nat.mul_pos (by omega) (by omega)
          omega
        · rw [if_neg h12]
          have h1 : 1 ≤ c.count r₁ := by
            have hm : r₁ ∈ c := mem_of_applicable_left happ
            exact Multiset.one_le_count_iff_mem.mpr hm
          have h2 : 1 ≤ c.count r₂ := by
            have hm : r₂ ∈ c := mem_of_applicable_right happ
            exact Multiset.one_le_count_iff_mem.mpr hm
          have hpos : 0 < c.count r₁ * c.count r₂ := Nat.mul_pos (by omega) (by omega)
          omega
      unfold Config.interactionProb
      intro hzero
      rw [ENNReal.div_eq_zero_iff] at hzero
      rcases hzero with h | h
      · exact hcount (by exact_mod_cast h)
      · exact (Config.totalPairs_ne_top c) h
    exact AllClockGE3_absorbing (L := L) (K := K) c _ hw hsupp
  · rw [Protocol.stepOrSelf_eq_self_of_not_applicable happ]
    exact hw

/-- The `AllClockGE3` window (of the erased configuration) is invariant along the marked chain. -/
theorem allClockGE3_erase_step (T θn : ℕ) (mc mc' : Config (MarkedAgent L K))
    (hw : AllClockGE3 (L := L) (K := K) (eraseConfig (L := L) (K := K) mc))
    (hsupp : mc' ∈ (markedPMF (L := L) (K := K) T θn mc).support) :
    AllClockGE3 (L := L) (K := K) (eraseConfig (L := L) (K := K) mc') := by
  classical
  unfold markedPMF at hsupp
  by_cases h : 2 ≤ mc.card
  · rw [dif_pos h] at hsupp
    rw [PMF.support_map] at hsupp
    obtain ⟨pr, _, hpr⟩ := hsupp
    subst hpr
    by_cases happ : ({pr.1, pr.2} : Multiset (MarkedAgent L K)) ≤ mc
    · rw [erase_markedStep (L := L) (K := K) T θn mc pr happ]
      exact allClockGE3_stepOrSelf (L := L) (K := K) _ hw pr.1.1 pr.2.1
    · unfold markedStep
      rw [if_neg happ]
      exact hw
  · rw [dif_neg h, PMF.support_pure] at hsupp
    rw [Set.mem_singleton_iff.mp hsupp]
    exact hw

/-- A phase-4 witness is permanent along the marked chain (phases never decrease). -/
theorem phase4_witness_absorbing (T θn : ℕ) (mc mc' : Config (MarkedAgent L K))
    (hP4 : ∃ m ∈ mc, 4 ≤ m.1.phase.val)
    (hsupp : mc' ∈ (markedPMF (L := L) (K := K) T θn mc).support) :
    ∃ m ∈ mc', 4 ≤ m.1.phase.val := by
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
      obtain ⟨m, hm, hm4⟩ := hP4
      set g := preBulkGate (L := L) (K := K) T θn mc with hg
      set o₁ := (markedOut (L := L) (K := K) T g pr.1 pr.2).1 with ho₁
      set o₂ := (markedOut (L := L) (K := K) T g pr.1 pr.2).2 with ho₂
      have hphase := HabsDischarge.Transition_phase_nondec_local (L := L) (K := K) pr.1.1 pr.2.1
      -- count the phase-4 witnesses: either m survives in mc − pair, or its slot's output works.
      by_cases hmem : m ∈ mc - {pr.1, pr.2}
      · exact ⟨m, Multiset.mem_add.mpr (Or.inl hmem), hm4⟩
      · -- m was consumed: it is r₁ or r₂ up to multiplicity; the corresponding output has
        -- phase ≥ m's phase ≥ 4.  Use a counting argument: the consumed pair contains a
        -- phase-≥4 member, so one of the OUTPUTS has phase ≥ 4.
        have hpos : 0 < Multiset.countP
            (fun x : MarkedAgent L K => 4 ≤ x.1.phase.val) mc :=
          Multiset.countP_pos.mpr ⟨m, hm, hm4⟩
        have hsplit : Multiset.countP (fun x : MarkedAgent L K => 4 ≤ x.1.phase.val) mc
            = Multiset.countP (fun x : MarkedAgent L K => 4 ≤ x.1.phase.val)
                (mc - {pr.1, pr.2})
              + Multiset.countP (fun x : MarkedAgent L K => 4 ≤ x.1.phase.val)
                ({pr.1, pr.2} : Multiset (MarkedAgent L K)) := by
          rw [← Multiset.countP_add, tsub_add_cancel_of_le happ]
        have hrest0 : Multiset.countP (fun x : MarkedAgent L K => 4 ≤ x.1.phase.val)
            (mc - {pr.1, pr.2}) = 0 ∨ ∃ m' ∈ mc - {pr.1, pr.2}, 4 ≤ m'.1.phase.val := by
          by_cases h0 : Multiset.countP
              (fun x : MarkedAgent L K => 4 ≤ x.1.phase.val) (mc - {pr.1, pr.2}) = 0
          · exact Or.inl h0
          · right
            have : 0 < Multiset.countP
                (fun x : MarkedAgent L K => 4 ≤ x.1.phase.val) (mc - {pr.1, pr.2}) := by
              omega
            exact Multiset.countP_pos.mp this
        rcases hrest0 with h0 | ⟨m', hm', hm'4⟩
        · -- the witness sits in the pair: some pr-member has phase ≥ 4; its output follows.
          have hpair_pos : 0 < Multiset.countP
              (fun x : MarkedAgent L K => 4 ≤ x.1.phase.val)
              ({pr.1, pr.2} : Multiset (MarkedAgent L K)) := by
            omega
          have hpair : 4 ≤ pr.1.1.phase.val ∨ 4 ≤ pr.2.1.phase.val := by
            obtain ⟨x, hx, hx4⟩ := Multiset.countP_pos.mp hpair_pos
            rw [show ({pr.1, pr.2} : Multiset (MarkedAgent L K))
              = pr.1 ::ₘ {pr.2} from rfl] at hx
            rcases Multiset.mem_cons.mp hx with hx | hx
            · exact Or.inl (hx ▸ hx4)
            · exact Or.inr ((Multiset.mem_singleton.mp hx) ▸ hx4)
          rcases hpair with h4 | h4
          · refine ⟨o₁, Multiset.mem_add.mpr (Or.inr ?_), ?_⟩
            · rw [show ({o₁, o₂} : Multiset (MarkedAgent L K)) = o₁ ::ₘ {o₂} from rfl]
              exact Multiset.mem_cons_self _ _
            · have : pr.1.1.phase.val ≤ o₁.1.phase.val := hphase.1
              omega
          · refine ⟨o₂, Multiset.mem_add.mpr (Or.inr ?_), ?_⟩
            · rw [show ({o₁, o₂} : Multiset (MarkedAgent L K)) = o₁ ::ₘ {o₂} from rfl]
              exact Multiset.mem_cons_of_mem (Multiset.mem_singleton_self _)
            · have : pr.2.1.phase.val ≤ o₂.1.phase.val := hphase.2
              omega
        · exact ⟨m', Multiset.mem_add.mpr (Or.inl hm'), hm'4⟩
    · rw [if_neg happ]
      exact hP4
  · rw [dif_neg h, PMF.support_pure] at hsupp
    rw [Set.mem_singleton_iff.mp hsupp]
    exact hP4

/-- The erased tail is monotone along the marked chain on the `AllClockGE3` window (the phases-≥3
generalization of `rBeyond_erase_monotone`). -/
theorem rBeyond_erase_monotone_ge3 (T θn R : ℕ) (mc mc' : Config (MarkedAgent L K))
    (hw : AllClockGE3 (L := L) (K := K) (eraseConfig (L := L) (K := K) mc))
    (hsupp : mc' ∈ (markedPMF (L := L) (K := K) T θn mc).support) :
    rBeyond (L := L) (K := K) R (eraseConfig (L := L) (K := K) mc)
      ≤ rBeyond (L := L) (K := K) R (eraseConfig (L := L) (K := K) mc') := by
  classical
  unfold markedPMF at hsupp
  by_cases h : 2 ≤ mc.card
  · rw [dif_pos h] at hsupp
    rw [PMF.support_map] at hsupp
    obtain ⟨pr, _, hpr⟩ := hsupp
    subst hpr
    by_cases happ : ({pr.1, pr.2} : Multiset (MarkedAgent L K)) ≤ mc
    · rw [erase_markedStep (L := L) (K := K) T θn mc pr happ]
      unfold Protocol.scheduledStep
      exact rBeyondGE3_stepOrSelf_ge (L := L) (K := K) R
        (eraseConfig (L := L) (K := K) mc) hw pr.1.1 pr.2.1
    · unfold markedStep
      rw [if_neg happ]
  · rw [dif_neg h, PMF.support_pure] at hsupp
    rw [Set.mem_singleton_iff.mp hsupp]

/-- **The slice gate has an absorbing complement** relative to the `AllClockGE3` region: within
the region, `¬(AllClockP3 ∧ X ≤ X₁)` means a phase-4 witness (permanent) or `X > X₁`
(permanent). -/
theorem slice_gate_absorbing (T θn n X₁ : ℕ)
    (mc : Config (MarkedAgent L K))
    (hR : mc.card = n ∧ AllClockGE3 (L := L) (K := K) (eraseConfig (L := L) (K := K) mc))
    (hG : mc ∉ cleanGate (L := L) (K := K) T n X₁) :
    ∀ mc' ∈ (markedPMF (L := L) (K := K) T θn mc).support,
      mc' ∉ cleanGate (L := L) (K := K) T n X₁ := by
  classical
  obtain ⟨hcard, hge3⟩ := hR
  intro mc' hsupp
  -- the three failure modes of the gate, within the region.
  have hcard' : mc'.card = n := by
    rw [← hcard]
    -- card is preserved: the erased card is, and erasure preserves card.
    have h1 := eraseConfig_card (L := L) (K := K) mc
    have h2 := eraseConfig_card (L := L) (K := K) mc'
    unfold markedPMF at hsupp
    by_cases h : 2 ≤ mc.card
    · rw [dif_pos h] at hsupp
      rw [PMF.support_map] at hsupp
      obtain ⟨pr, _, hpr⟩ := hsupp
      subst hpr
      by_cases happ : ({pr.1, pr.2} : Multiset (MarkedAgent L K)) ≤ mc
      · have herase := erase_markedStep (L := L) (K := K) T θn mc pr happ
        have hreal : (eraseConfig (L := L) (K := K)
            (markedStep (L := L) (K := K) T θn mc pr)).card
            = (eraseConfig (L := L) (K := K) mc).card := by
          rw [herase]
          exact Protocol.reachable_card_eq (Protocol.reachable_stepOrSelf (P := NonuniformMajority L K) _ pr.1.1 pr.2.1)
        omega
      · unfold markedStep
        rw [if_neg happ]
    · rw [dif_neg h, PMF.support_pure] at hsupp
      rw [Set.mem_singleton_iff.mp hsupp]
  -- ¬gate within the region: phase-4 witness or X > X₁.
  have hsplit : (∃ m ∈ mc, 4 ≤ m.1.phase.val) ∨
      X₁ < rBeyond (L := L) (K := K) T (eraseConfig (L := L) (K := K) mc) := by
    by_contra hcon
    push Not at hcon
    obtain ⟨hno4, hX⟩ := hcon
    apply hG
    refine ⟨hcard, ?_, by omega⟩
    -- AllClockP3 of the erased config: roles from GE3, phases = 3 from GE3 + no phase-4 witness.
    intro a ha
    unfold eraseConfig at ha
    obtain ⟨m, hm, hma⟩ := Multiset.mem_map.mp ha
    have hge := hge3 a ha
    have h4 := hno4 m hm
    refine ⟨hge.1, ?_⟩
    have h3 : 3 ≤ a.phase.val := hge.2
    have : a.phase.val ≤ 3 := by
      rw [← hma]
      omega
    omega
  rcases hsplit with h4 | hX
  · -- phase-4 witness persists; the successor cannot be AllClockP3.
    have h4' := phase4_witness_absorbing (L := L) (K := K) T θn mc mc' h4 hsupp
    rintro ⟨_, hP3, _⟩
    obtain ⟨m, hm, hm4⟩ := h4'
    have := hP3 m.1 (by
      unfold eraseConfig
      exact Multiset.mem_map_of_mem Prod.fst hm)
    omega
  · -- X > X₁ persists.
    have hmono := rBeyond_erase_monotone_ge3 (L := L) (K := K) T θn T mc mc' hge3 hsupp
    rintro ⟨_, _, hX'⟩
    omega

/-! ## Part 25 — the SLICE clean tail (brick 3.5d-iii capstone): zero escape.

Assembling the coupling (`real_le_killed_of_absorbing` with the slice gate's absorbing complement)
with the killed alive-mass tail (`stepIndexed_killed_tail` + `cleanPot_drift`) gives the per-slice
clean tail with NO escape term: endpoints inside the slice gate never left it. -/

/-- **The slice clean tail, explicit sequences, zero escape**: from a start in the `AllClockGE3`
region, the probability of ending with `Yt ≤ cleanAbove` INSIDE the slice gate is at most
`exp(σρ^w·Y₀ + (X₁/n)²(1+ε)σρ^w·w − σ·Yt)` — no escape mass. -/
theorem slice_clean_tail_explicit (T θn n X₁ : ℕ) (hn : 2 ≤ n)
    (σ ε : ℝ) (hσ : 0 < σ) (hε : 0 < ε) (w : ℕ)
    (hsmall : σ * (1 + 2 * (1 + ε) / (n : ℝ)) ^ w ≤ ε / (1 + ε))
    (mc₀ : Config (MarkedAgent L K))
    (hR : mc₀.card = n ∧ AllClockGE3 (L := L) (K := K) (eraseConfig (L := L) (K := K) mc₀))
    (Yt : ℕ) :
    ((markedK (L := L) (K := K) T θn) ^ w) mc₀
        {mc | Yt ≤ cleanAbove (L := L) (K := K) T mc ∧
          mc ∈ cleanGate (L := L) (K := K) T n X₁} ≤
      ENNReal.ofReal
        (Real.exp (σ * (1 + 2 * (1 + ε) / (n : ℝ)) ^ w
            * (cleanAbove (L := L) (K := K) T mc₀ : ℝ)
          + ((X₁ : ℝ) / (n : ℝ)) ^ 2 * (1 + ε) * σ
              * (1 + 2 * (1 + ε) / (n : ℝ)) ^ w * (w : ℝ)
          - σ * (Yt : ℝ))) := by
  classical
  letI : MeasurableSpace (Option (Config (MarkedAgent L K))) := GatedDrift.instOptionMS
  letI : DiscreteMeasurableSpace (Option (Config (MarkedAgent L K))) :=
    GatedDrift.instOptionDMS
  have hnpos : (0 : ℝ) < (n : ℝ) := by
    exact_mod_cast (by omega : 0 < n)
  have h1ε : (0 : ℝ) < 1 + ε := by linarith
  set ρ : ℝ := 1 + 2 * (1 + ε) / (n : ℝ) with hρ
  have hρ1 : (1 : ℝ) ≤ ρ := by
    rw [hρ]
    have h0 : (0 : ℝ) ≤ 2 * (1 + ε) / (n : ℝ) := by positivity
    linarith
  have hρpos : (0 : ℝ) < ρ := by linarith
  have hρ0 : ρ ≠ 0 := by linarith
  set A : ℝ := ((X₁ : ℝ) / (n : ℝ)) ^ 2 with hA
  have hAnn : 0 ≤ A := by rw [hA]; positivity
  set β : ℝ := A * (1 + ε) * σ * ρ ^ w with hβ
  set s : ℕ → ℝ := fun j => σ * ρ ^ ((w : ℤ) - (j : ℤ)) with hs
  set b : ℕ → ℝ := fun j => β * (((w : ℤ) - (j : ℤ) : ℤ) : ℝ) with hb
  have hs_pos : ∀ j, 0 < s j := by
    intro j
    rw [hs]
    positivity
  have hs_le : ∀ j, s j ≤ ε / (1 + ε) := by
    intro j
    rw [hs]
    calc σ * ρ ^ ((w : ℤ) - (j : ℤ)) ≤ σ * ρ ^ (w : ℤ) := by
          apply mul_le_mul_of_nonneg_left _ hσ.le
          apply zpow_le_zpow_right₀ hρ1
          omega
      _ = σ * ρ ^ w := by rw [zpow_natCast]
      _ ≤ ε / (1 + ε) := hsmall
  have hs1 : ∀ j, 0 ≤ s (j + 1) := fun j => (hs_pos (j + 1)).le
  have hexpb : ∀ j, Real.exp (s (j + 1)) - 1 ≤ (1 + ε) * s (j + 1) := fun j =>
    exp_sub_one_le_mul (hs_pos (j + 1)).le hε (hs_le (j + 1))
  have hslope : ∀ j, s (j + 1) + 2 * (Real.exp (s (j + 1)) - 1) / (n : ℝ) ≤ s j := by
    intro j
    have hstep : s (j + 1) * ρ = s j := by
      rw [hs]
      show σ * ρ ^ ((w : ℤ) - ((j : ℕ) + 1 : ℕ)) * ρ = σ * ρ ^ ((w : ℤ) - (j : ℤ))
      rw [mul_assoc, ← zpow_add_one₀ hρ0]
      congr 1
      push_cast
      ring_nf
    have hd : 2 * (Real.exp (s (j + 1)) - 1) / (n : ℝ)
        ≤ 2 * ((1 + ε) * s (j + 1)) / (n : ℝ) := by
      apply div_le_div_of_nonneg_right (by linarith [hexpb j]) hnpos.le
    calc s (j + 1) + 2 * (Real.exp (s (j + 1)) - 1) / (n : ℝ)
        ≤ s (j + 1) + 2 * ((1 + ε) * s (j + 1)) / (n : ℝ) := by linarith
      _ = s (j + 1) * ρ := by
          rw [hρ]
          field_simp
      _ = s j := hstep
  have hicept : ∀ j, b (j + 1)
      + ((X₁ : ℝ) / (n : ℝ)) ^ 2 * (Real.exp (s (j + 1)) - 1) ≤ b j := by
    intro j
    have hsmax : s (j + 1) ≤ σ * ρ ^ w := by
      rw [hs]
      calc σ * ρ ^ ((w : ℤ) - (((j : ℕ) + 1 : ℕ) : ℤ)) ≤ σ * ρ ^ (w : ℤ) := by
            apply mul_le_mul_of_nonneg_left _ hσ.le
            apply zpow_le_zpow_right₀ hρ1
            push_cast
            omega
        _ = σ * ρ ^ w := by rw [zpow_natCast]
    have hbdiff : b j - b (j + 1) = β := by
      rw [hb]
      push_cast
      ring
    have hkey : A * (Real.exp (s (j + 1)) - 1) ≤ β := by
      calc A * (Real.exp (s (j + 1)) - 1)
          ≤ A * ((1 + ε) * s (j + 1)) := mul_le_mul_of_nonneg_left (hexpb j) hAnn
        _ ≤ A * ((1 + ε) * (σ * ρ ^ w)) := by
            apply mul_le_mul_of_nonneg_left _ hAnn
            apply mul_le_mul_of_nonneg_left hsmax (by linarith)
        _ = β := by rw [hβ]; ring
    rw [← hA]
    linarith
  -- the zero-escape coupling at the slice gate.
  have hcoupling := real_le_killed_of_absorbing
    (markedK (L := L) (K := K) T θn)
    {mc : Config (MarkedAgent L K) |
      mc.card = n ∧ AllClockGE3 (L := L) (K := K) (eraseConfig (L := L) (K := K) mc)}
    (cleanGate (L := L) (K := K) T n X₁)
    (fun mc hmc => ae_markedStep (L := L) (K := K) T θn mc _ (fun mc' hsupp =>
      ⟨by
        obtain ⟨hcard, hge3⟩ := hmc
        have h1 := eraseConfig_card (L := L) (K := K) mc
        have h2 := eraseConfig_card (L := L) (K := K) mc'
        revert hsupp
        unfold markedPMF
        by_cases h : 2 ≤ mc.card
        · rw [dif_pos h]
          intro hsupp
          rw [PMF.support_map] at hsupp
          obtain ⟨pr, _, hpr⟩ := hsupp
          subst hpr
          by_cases happ : ({pr.1, pr.2} : Multiset (MarkedAgent L K)) ≤ mc
          · have herase := erase_markedStep (L := L) (K := K) T θn mc pr happ
            have hreal : (eraseConfig (L := L) (K := K)
                (markedStep (L := L) (K := K) T θn mc pr)).card
                = (eraseConfig (L := L) (K := K) mc).card := by
              rw [herase]
              exact Protocol.reachable_card_eq
                (Protocol.reachable_stepOrSelf (P := NonuniformMajority L K) _ pr.1.1 pr.2.1)
            omega
          · unfold markedStep
            rw [if_neg happ]
            omega
        · rw [dif_neg h]
          intro hsupp
          rw [PMF.support_pure] at hsupp
          rw [Set.mem_singleton_iff.mp hsupp]
          omega,
       allClockGE3_erase_step (L := L) (K := K) T θn mc mc' hmc.2 hsupp⟩))
    (fun mc hmc hG => ae_markedStep (L := L) (K := K) T θn mc _ (fun mc' hsupp =>
      slice_gate_absorbing (L := L) (K := K) T θn n X₁ mc hmc hG mc' hsupp))
    (fun mc => Yt ≤ cleanAbove (L := L) (K := K) T mc ∧
      mc ∈ cleanGate (L := L) (K := K) T n X₁)
    (fun mc hmc => hmc.2) w mc₀ hR
  refine le_trans hcoupling ?_
  -- include into the potential super-level set and run the killed tail.
  have hsub : {o : Option (Config (MarkedAgent L K)) |
      ∃ mc, o = some mc ∧ Yt ≤ cleanAbove (L := L) (K := K) T mc ∧
        mc ∈ cleanGate (L := L) (K := K) T n X₁} ⊆
      {o | ENNReal.ofReal (Real.exp (s w * (Yt : ℝ) + b w))
        ≤ GatedDrift.killΦ (fun mc => ENNReal.ofReal
            (Real.exp (s w * (cleanAbove (L := L) (K := K) T mc : ℝ) + b w))) o} := by
    rintro o ⟨mc, rfl, hY, _⟩
    rw [Set.mem_setOf_eq, GatedDrift.killΦ_some]
    apply ENNReal.ofReal_le_ofReal
    apply Real.exp_le_exp.mpr
    have hcast : (Yt : ℝ) ≤ (cleanAbove (L := L) (K := K) T mc : ℝ) := by
      exact_mod_cast hY
    nlinarith [(hs_pos w).le, hcast]
  refine le_trans (measure_mono hsub) ?_
  have htail := stepIndexed_killed_tail (markedK (L := L) (K := K) T θn)
    (cleanGate (L := L) (K := K) T n X₁)
    (fun j mc => ENNReal.ofReal
      (Real.exp (s j * (cleanAbove (L := L) (K := K) T mc : ℝ) + b j)))
    (cleanPot_drift (L := L) (K := K) T θn n X₁ hn s b hs1 hslope hicept)
    w mc₀ (ENNReal.ofReal (Real.exp (s w * (Yt : ℝ) + b w)))
    (by simp [Real.exp_pos]) ENNReal.ofReal_ne_top
  refine le_trans htail ?_
  dsimp only
  have hs0 : s 0 = σ * ρ ^ w := by
    rw [hs]
    show σ * ρ ^ ((w : ℤ) - ((0 : ℕ) : ℤ)) = σ * ρ ^ w
    rw [show (w : ℤ) - ((0 : ℕ) : ℤ) = (w : ℤ) from by push_cast; ring, zpow_natCast]
  have hb0 : b 0 = β * (w : ℝ) := by
    rw [hb]
    push_cast
    ring
  have hsw : s w = σ := by
    rw [hs]
    show σ * ρ ^ ((w : ℤ) - ((w : ℕ) : ℤ)) = σ
    rw [sub_self, zpow_zero, mul_one]
  have hbw : b w = 0 := by
    rw [hb]
    push_cast
    ring
  rw [hs0, hb0, hsw, hbw]
  rw [← ENNReal.ofReal_div_of_pos (Real.exp_pos _), ← Real.exp_sub]
  apply ENNReal.ofReal_le_ofReal
  apply Real.exp_le_exp.mpr
  rw [hβ, hA]
  ring_nf
  exact le_refl _

/-! ## Part 26 — the ladder decomposition (brick 3.5d-iv, set level).

The per-window bad event with its RANDOM threshold `cc·X_w²/n` splits along any monotone ladder
`a 0 < a 1 < … < a M`: either the feeder failed to clear the floor (`X ≤ a 0` — the growth tail),
or the endpoint sits in some rung `(a m, a (m+1)]` where the deterministic threshold
`Yt m ≈ cc·(a m)²/n` is exceeded INSIDE the rung's slice gate (`X ≤ a (m+1)`) — the zero-escape
slice tail. -/

/-- Locate the rung: a monotone ladder with `a 0 < X ≤ a M` has a rung `(a m, a (m+1)]`
containing `X`. -/
theorem ladder_locate (a : ℕ → ℕ) (M : ℕ) (X : ℕ)
    (hlo : a 0 < X) (hhi : X ≤ a M) :
    ∃ m < M, a m < X ∧ X ≤ a (m + 1) := by
  induction M with
  | zero => omega
  | succ M ih =>
      by_cases hM : X ≤ a M
      · obtain ⟨m, hm, h1, h2⟩ := ih hM
        exact ⟨m, by omega, h1, h2⟩
      · exact ⟨M, by omega, by omega, hhi⟩

/-- **The ladder decomposition of the per-window bad event.** -/
theorem ladder_bad_subset (T n : ℕ) (cc : ℝ) (hcc : 0 ≤ cc)
    (a : ℕ → ℕ) (M : ℕ) (Yt : ℕ → ℕ)
    (hYt : ∀ m < M, (Yt m : ℝ) ≤ cc * (a m : ℝ) ^ 2 / (n : ℝ) + 1) :
    {mc : Config (MarkedAgent L K) |
        (cc * (rBeyond (L := L) (K := K) T (eraseConfig (L := L) (K := K) mc) : ℝ) ^ 2
            / (n : ℝ)
          < (cleanAbove (L := L) (K := K) T mc : ℝ)) ∧
        rBeyond (L := L) (K := K) T (eraseConfig (L := L) (K := K) mc) ≤ a M ∧
        mc.card = n ∧ AllClockP3 (L := L) (K := K) (eraseConfig (L := L) (K := K) mc)} ⊆
      {mc : Config (MarkedAgent L K) |
          rBeyond (L := L) (K := K) T (eraseConfig (L := L) (K := K) mc) ≤ a 0} ∪
        ⋃ m ∈ Finset.range M,
          {mc : Config (MarkedAgent L K) |
            Yt m ≤ cleanAbove (L := L) (K := K) T mc ∧
              mc ∈ cleanGate (L := L) (K := K) T n (a (m + 1))} := by
  rintro mc ⟨hbad, hXtop, hcard, hP3⟩
  set X := rBeyond (L := L) (K := K) T (eraseConfig (L := L) (K := K) mc) with hX
  by_cases hfloor : X ≤ a 0
  · exact Or.inl hfloor
  · right
    obtain ⟨m, hmM, hlo, hhi⟩ := ladder_locate a M X (by omega) hXtop
    rw [Set.mem_iUnion]
    refine ⟨m, ?_⟩
    rw [Set.mem_iUnion]
    refine ⟨Finset.mem_range.mpr hmM, ?_⟩
    refine ⟨?_, hcard, hP3, hhi⟩
    -- Y > cc·X²/n ≥ cc·(a m)²/n, and Yt m ≤ cc·(a m)²/n + 1: the ℕ threshold is met.
    have ham : ((a m : ℕ) : ℝ) ≤ (X : ℝ) := by
      have : a m ≤ X := by omega
      exact_mod_cast this
    have hsq : cc * (a m : ℝ) ^ 2 / (n : ℝ)
        ≤ cc * (X : ℝ) ^ 2 / (n : ℝ) := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      apply mul_le_mul_of_nonneg_left _ hcc
      apply pow_le_pow_left₀ (by positivity) ham
    have hY : cc * (a m : ℝ) ^ 2 / (n : ℝ)
        < (cleanAbove (L := L) (K := K) T mc : ℝ) := lt_of_le_of_lt hsq hbad
    have hcast : ((Yt m : ℕ) : ℝ) < (cleanAbove (L := L) (K := K) T mc : ℝ) + 1 := by
      calc ((Yt m : ℕ) : ℝ) ≤ cc * (a m : ℝ) ^ 2 / (n : ℝ) + 1 := hYt m hmM
        _ < (cleanAbove (L := L) (K := K) T mc : ℝ) + 1 := by linarith
    have : Yt m < cleanAbove (L := L) (K := K) T mc + 1 := by exact_mod_cast hcast
    omega

/-! ## Part 27 — the zero-escape growth slice (brick 3.5d-iv b).

The growth gate's complement is absorbing relative to the `AllClockGE3` region by the same
argument as the clean slice gate (`10X ≤ n` exits are monotone-permanent; hour exits are
phase-permanent), so the growth lower tail also sheds its escape term when the bad endpoint
carries the gate membership. -/

/-- The growth gate's complement is absorbing relative to the `AllClockGE3` region. -/
theorem growth_gate_absorbing (T θn n : ℕ)
    (mc : Config (MarkedAgent L K))
    (hR : mc.card = n ∧ AllClockGE3 (L := L) (K := K) (eraseConfig (L := L) (K := K) mc))
    (hG : mc ∉ growthGate (L := L) (K := K) T n) :
    ∀ mc' ∈ (markedPMF (L := L) (K := K) T θn mc).support,
      mc' ∉ growthGate (L := L) (K := K) T n := by
  classical
  obtain ⟨hcard, hge3⟩ := hR
  intro mc' hsupp
  have hcard' : mc'.card = n := by
    rw [← hcard]
    have h1 := eraseConfig_card (L := L) (K := K) mc
    have h2 := eraseConfig_card (L := L) (K := K) mc'
    revert hsupp
    unfold markedPMF
    by_cases h : 2 ≤ mc.card
    · rw [dif_pos h]
      intro hsupp
      rw [PMF.support_map] at hsupp
      obtain ⟨pr, _, hpr⟩ := hsupp
      subst hpr
      by_cases happ : ({pr.1, pr.2} : Multiset (MarkedAgent L K)) ≤ mc
      · have herase := erase_markedStep (L := L) (K := K) T θn mc pr happ
        have hreal : (eraseConfig (L := L) (K := K)
            (markedStep (L := L) (K := K) T θn mc pr)).card
            = (eraseConfig (L := L) (K := K) mc).card := by
          rw [herase]
          exact Protocol.reachable_card_eq
            (Protocol.reachable_stepOrSelf (P := NonuniformMajority L K) _ pr.1.1 pr.2.1)
        omega
      · unfold markedStep
        rw [if_neg happ]
    · rw [dif_neg h]
      intro hsupp
      rw [PMF.support_pure] at hsupp
      rw [Set.mem_singleton_iff.mp hsupp]
  have hsplit : (∃ m ∈ mc, 4 ≤ m.1.phase.val) ∨
      n < 10 * rBeyond (L := L) (K := K) T (eraseConfig (L := L) (K := K) mc) := by
    by_contra hcon
    push Not at hcon
    obtain ⟨hno4, hX⟩ := hcon
    apply hG
    refine ⟨hcard, ?_, by omega⟩
    intro a ha
    unfold eraseConfig at ha
    obtain ⟨m, hm, hma⟩ := Multiset.mem_map.mp ha
    have hge := hge3 a ha
    have h4 := hno4 m hm
    refine ⟨hge.1, ?_⟩
    have h3 : 3 ≤ a.phase.val := hge.2
    have : a.phase.val ≤ 3 := by
      rw [← hma]
      omega
    omega
  rcases hsplit with h4 | hX
  · have h4' := phase4_witness_absorbing (L := L) (K := K) T θn mc mc' h4 hsupp
    rintro ⟨_, hP3, _⟩
    obtain ⟨m, hm, hm4⟩ := h4'
    have := hP3 m.1 (by
      unfold eraseConfig
      exact Multiset.mem_map_of_mem Prod.fst hm)
    omega
  · have hmono := rBeyond_erase_monotone_ge3 (L := L) (K := K) T θn T mc mc' hge3 hsupp
    rintro ⟨_, _, hX'⟩
    omega

/-- **The zero-escape growth slice tail**: from a start in the `AllClockGE3` region, the
probability of ending with the feeder still at or below `a` INSIDE the growth gate is at most
`exp(−σ(X₀ − a))` — no escape mass. -/
theorem slice_growth_tail (T θn n : ℕ) (hn : 2 ≤ n)
    (σ : ℝ) (hσ : 0 ≤ σ) (w : ℕ)
    (mc₀ : Config (MarkedAgent L K))
    (hR : mc₀.card = n ∧ AllClockGE3 (L := L) (K := K) (eraseConfig (L := L) (K := K) mc₀))
    (a : ℕ) :
    ((markedK (L := L) (K := K) T θn) ^ w) mc₀
        {mc | rBeyond (L := L) (K := K) T (eraseConfig (L := L) (K := K) mc) ≤ a ∧
          mc ∈ growthGate (L := L) (K := K) T n} ≤
      ENNReal.ofReal
        (Real.exp (-(σ
            * (rBeyond (L := L) (K := K) T (eraseConfig (L := L) (K := K) mc₀) : ℝ))
          + σ * (a : ℝ))) := by
  classical
  letI : MeasurableSpace (Option (Config (MarkedAgent L K))) := GatedDrift.instOptionMS
  letI : DiscreteMeasurableSpace (Option (Config (MarkedAgent L K))) :=
    GatedDrift.instOptionDMS
  have hcoupling := real_le_killed_of_absorbing
    (markedK (L := L) (K := K) T θn)
    {mc : Config (MarkedAgent L K) |
      mc.card = n ∧ AllClockGE3 (L := L) (K := K) (eraseConfig (L := L) (K := K) mc)}
    (growthGate (L := L) (K := K) T n)
    (fun mc hmc => ae_markedStep (L := L) (K := K) T θn mc _ (fun mc' hsupp =>
      ⟨by
        obtain ⟨hcard, hge3⟩ := hmc
        have h1 := eraseConfig_card (L := L) (K := K) mc
        have h2 := eraseConfig_card (L := L) (K := K) mc'
        revert hsupp
        unfold markedPMF
        by_cases h : 2 ≤ mc.card
        · rw [dif_pos h]
          intro hsupp
          rw [PMF.support_map] at hsupp
          obtain ⟨pr, _, hpr⟩ := hsupp
          subst hpr
          by_cases happ : ({pr.1, pr.2} : Multiset (MarkedAgent L K)) ≤ mc
          · have herase := erase_markedStep (L := L) (K := K) T θn mc pr happ
            have hreal : (eraseConfig (L := L) (K := K)
                (markedStep (L := L) (K := K) T θn mc pr)).card
                = (eraseConfig (L := L) (K := K) mc).card := by
              rw [herase]
              exact Protocol.reachable_card_eq
                (Protocol.reachable_stepOrSelf (P := NonuniformMajority L K) _ pr.1.1 pr.2.1)
            omega
          · unfold markedStep
            rw [if_neg happ]
            omega
        · rw [dif_neg h]
          intro hsupp
          rw [PMF.support_pure] at hsupp
          rw [Set.mem_singleton_iff.mp hsupp]
          omega,
       allClockGE3_erase_step (L := L) (K := K) T θn mc mc' hmc.2 hsupp⟩))
    (fun mc hmc hG => ae_markedStep (L := L) (K := K) T θn mc _ (fun mc' hsupp =>
      growth_gate_absorbing (L := L) (K := K) T θn n mc hmc hG mc' hsupp))
    (fun mc => rBeyond (L := L) (K := K) T (eraseConfig (L := L) (K := K) mc) ≤ a ∧
      mc ∈ growthGate (L := L) (K := K) T n)
    (fun mc hmc => hmc.2) w mc₀ hR
  refine le_trans hcoupling ?_
  have hsub : {o : Option (Config (MarkedAgent L K)) |
      ∃ mc, o = some mc ∧
        rBeyond (L := L) (K := K) T (eraseConfig (L := L) (K := K) mc) ≤ a ∧
        mc ∈ growthGate (L := L) (K := K) T n} ⊆
      {o | ENNReal.ofReal (Real.exp (-(σ * (a : ℝ))))
        ≤ GatedDrift.killΦ (fun mc => ENNReal.ofReal
            (Real.exp (-(σ * (rBeyond (L := L) (K := K) T
              (eraseConfig (L := L) (K := K) mc) : ℝ))))) o} := by
    rintro o ⟨mc, rfl, hXa, _⟩
    rw [Set.mem_setOf_eq, GatedDrift.killΦ_some]
    apply ENNReal.ofReal_le_ofReal
    apply Real.exp_le_exp.mpr
    have hcast : (rBeyond (L := L) (K := K) T (eraseConfig (L := L) (K := K) mc) : ℝ)
        ≤ (a : ℝ) := by exact_mod_cast hXa
    nlinarith [hσ, hcast]
  refine le_trans (measure_mono hsub) ?_
  have hdrift := growthPot_drift (L := L) (K := K) T θn n hn (fun _ => σ)
    (fun _ => hσ)
    (fun j => by
      have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
      have hes : Real.exp (-σ) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
      have h0 : (0 : ℝ) ≤ 1.8 * (1 - Real.exp (-σ)) / (n : ℝ) := by
        apply div_nonneg _ hnpos.le
        nlinarith
      simpa using (by linarith : σ ≤ σ + 1.8 * (1 - Real.exp (-σ)) / (n : ℝ)))
  have htail := stepIndexed_killed_tail (markedK (L := L) (K := K) T θn)
    (growthGate (L := L) (K := K) T n)
    (fun _ mc => ENNReal.ofReal (Real.exp (-(σ * (rBeyond (L := L) (K := K) T
      (eraseConfig (L := L) (K := K) mc) : ℝ)))))
    hdrift w mc₀ (ENNReal.ofReal (Real.exp (-(σ * (a : ℝ)))))
    (by simp [Real.exp_pos]) ENNReal.ofReal_ne_top
  refine le_trans htail ?_
  dsimp only
  rw [← ENNReal.ofReal_div_of_pos (Real.exp_pos _), ← Real.exp_sub]
  apply ENNReal.ofReal_le_ofReal
  apply Real.exp_le_exp.mpr
  ring_nf
  exact le_refl _

/-! ## Part 27b — the UPWARD growth slice tail (brick 3.5e, the 11th-shape fix).

`slice_growth_tail` (constant slope) certifies only anti-SHRINK: `P[X_w ≤ a]` small for `a < X₀`.
The Lemma 6.3 recurrence needs the OPPOSITE: `P[X_w ≤ g·X₀]` small for a growth factor `g > 1`
(the paper's `x(t−0.1) < 0.84·x(t)` ↦ `x(end) ≥ x(start)/0.84`).  The contraction factor
`exp(−1.8(X/n)(1−e^{−s}))` produced inside `growthPot_drift` is RETAINED by using the INCREASING
(backward) slope `s_j = σ + (w−j)·c`, `c = 1.8(1−e^{−σ})/n`: the drift recursion
`s_j ≤ s_{j+1} + 1.8(1−e^{−s_{j+1}})/n` holds because `s_{j+1} ≥ σ` makes `1−e^{−s_{j+1}} ≥ 1−e^{−σ}`.
The tail exponent is then `−s_0·X₀ + s_w·a = −(σ+w·c)X₀ + σ·a`, and at `a = g·X₀` with
`w·c = 1.8(1−e^{−σ})·(w/n)` this is `−X₀·[σ(g−1) + 1.8(1−e^{−σ})(w/n) − σ(g−1) … ]`; explicitly
`= σ·a − (σ+w·c)·X₀`, which at the doctrine scales (σ = 1/10, w/n = wp = 0.015, g = 41/40) is
`≤ −X₀·δ` with `δ ≈ 7e−5 > 0`. -/

/-- **The zero-escape UPWARD growth slice tail**: with the increasing slope `s j = σ + (w−j)·c`,
`c = 1.8(1−e^{−σ})/n`, the probability of ending with the feeder still `≤ a` is at most
`exp(−(σ + w·c)·X₀ + σ·a)` — small even for `a > X₀` (upward growth), no escape mass. -/
theorem slice_growth_tail_up (T θn n : ℕ) (hn : 2 ≤ n)
    (σ : ℝ) (hσ : 0 < σ) (w : ℕ)
    (mc₀ : Config (MarkedAgent L K))
    (hR : mc₀.card = n ∧ AllClockGE3 (L := L) (K := K) (eraseConfig (L := L) (K := K) mc₀))
    (a : ℕ) :
    ((markedK (L := L) (K := K) T θn) ^ w) mc₀
        {mc | rBeyond (L := L) (K := K) T (eraseConfig (L := L) (K := K) mc) ≤ a ∧
          mc ∈ growthGate (L := L) (K := K) T n} ≤
      ENNReal.ofReal
        (Real.exp (-((σ + (w : ℝ) * (1.8 * (1 - Real.exp (-σ)) / (n : ℝ)))
            * (rBeyond (L := L) (K := K) T (eraseConfig (L := L) (K := K) mc₀) : ℝ))
          + σ * (a : ℝ))) := by
  classical
  letI : MeasurableSpace (Option (Config (MarkedAgent L K))) := GatedDrift.instOptionMS
  letI : DiscreteMeasurableSpace (Option (Config (MarkedAgent L K))) :=
    GatedDrift.instOptionDMS
  -- the increasing backward slope, clamped at σ past the horizon via ℕ-truncated subtraction.
  set c : ℝ := 1.8 * (1 - Real.exp (-σ)) / (n : ℝ) with hc
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hes : Real.exp (-σ) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hc0 : 0 ≤ c := by rw [hc]; apply div_nonneg _ hnpos.le; nlinarith
  set s : ℕ → ℝ := fun j => σ + ((w - j : ℕ) : ℝ) * c with hs
  have hs1 : ∀ j, 0 ≤ s (j + 1) := by
    intro j
    rw [hs]
    have : (0 : ℝ) ≤ ((w - (j + 1) : ℕ) : ℝ) * c := mul_nonneg (by positivity) hc0
    simp only
    linarith [hσ.le]
  -- the drift recursion: c ≤ 1.8(1−e^{−s_{j+1}})/n because s_{j+1} ≥ σ.
  have hslope : ∀ j, s j ≤ s (j + 1)
      + 1.8 * (1 - Real.exp (-(s (j + 1)))) / (n : ℝ) := by
    intro j
    have hsj1_ge : σ ≤ s (j + 1) := by
      rw [hs]; simp only
      have : (0 : ℝ) ≤ ((w - (j + 1) : ℕ) : ℝ) * c := mul_nonneg (by positivity) hc0
      linarith
    -- 1−e^{−s_{j+1}} ≥ 1−e^{−σ}, so the RHS rate ≥ c.
    have hrate_ge : c ≤ 1.8 * (1 - Real.exp (-(s (j + 1)))) / (n : ℝ) := by
      rw [hc]
      have h1 : Real.exp (-(s (j + 1))) ≤ Real.exp (-σ) :=
        Real.exp_le_exp.mpr (by linarith)
      have hnum : 1.8 * (1 - Real.exp (-σ)) ≤ 1.8 * (1 - Real.exp (-(s (j + 1)))) := by
        nlinarith [h1]
      gcongr
    -- s j − s(j+1) = (w−j) − (w−(j+1)) (ℕ-trunc) times c ≤ c.
    have hdiff : s j - s (j + 1) ≤ c := by
      rw [hs]; simp only
      have hle : ((w - j : ℕ) : ℝ) ≤ ((w - (j + 1) : ℕ) : ℝ) + 1 := by
        have : w - j ≤ (w - (j + 1)) + 1 := by omega
        exact_mod_cast this
      nlinarith [hc0, hle]
    linarith [hdiff, hrate_ge]
  have hsw : s w = σ := by rw [hs]; simp
  have hsw0 : 0 ≤ s w := by rw [hsw]; linarith
  -- the zero-escape coupling (same region/gate as slice_growth_tail).
  have hcoupling := real_le_killed_of_absorbing
    (markedK (L := L) (K := K) T θn)
    {mc : Config (MarkedAgent L K) |
      mc.card = n ∧ AllClockGE3 (L := L) (K := K) (eraseConfig (L := L) (K := K) mc)}
    (growthGate (L := L) (K := K) T n)
    (fun mc hmc => ae_markedStep (L := L) (K := K) T θn mc _ (fun mc' hsupp =>
      ⟨by
        obtain ⟨hcard, hge3⟩ := hmc
        have h1 := eraseConfig_card (L := L) (K := K) mc
        have h2 := eraseConfig_card (L := L) (K := K) mc'
        revert hsupp
        unfold markedPMF
        by_cases h : 2 ≤ mc.card
        · rw [dif_pos h]
          intro hsupp
          rw [PMF.support_map] at hsupp
          obtain ⟨pr, _, hpr⟩ := hsupp
          subst hpr
          by_cases happ : ({pr.1, pr.2} : Multiset (MarkedAgent L K)) ≤ mc
          · have herase := erase_markedStep (L := L) (K := K) T θn mc pr happ
            have hreal : (eraseConfig (L := L) (K := K)
                (markedStep (L := L) (K := K) T θn mc pr)).card
                = (eraseConfig (L := L) (K := K) mc).card := by
              rw [herase]
              exact Protocol.reachable_card_eq
                (Protocol.reachable_stepOrSelf (P := NonuniformMajority L K) _ pr.1.1 pr.2.1)
            omega
          · unfold markedStep
            rw [if_neg happ]
            omega
        · rw [dif_neg h]
          intro hsupp
          rw [PMF.support_pure] at hsupp
          rw [Set.mem_singleton_iff.mp hsupp]
          omega,
       allClockGE3_erase_step (L := L) (K := K) T θn mc mc' hmc.2 hsupp⟩))
    (fun mc hmc hG => ae_markedStep (L := L) (K := K) T θn mc _ (fun mc' hsupp =>
      growth_gate_absorbing (L := L) (K := K) T θn n mc hmc hG mc' hsupp))
    (fun mc => rBeyond (L := L) (K := K) T (eraseConfig (L := L) (K := K) mc) ≤ a ∧
      mc ∈ growthGate (L := L) (K := K) T n)
    (fun mc hmc => hmc.2) w mc₀ hR
  refine le_trans hcoupling ?_
  have hsub : {o : Option (Config (MarkedAgent L K)) |
      ∃ mc, o = some mc ∧
        rBeyond (L := L) (K := K) T (eraseConfig (L := L) (K := K) mc) ≤ a ∧
        mc ∈ growthGate (L := L) (K := K) T n} ⊆
      {o | ENNReal.ofReal (Real.exp (-(s w * (a : ℝ))))
        ≤ GatedDrift.killΦ (fun mc => ENNReal.ofReal
            (Real.exp (-(s w * (rBeyond (L := L) (K := K) T
              (eraseConfig (L := L) (K := K) mc) : ℝ))))) o} := by
    rintro o ⟨mc, rfl, hXa, _⟩
    rw [Set.mem_setOf_eq, GatedDrift.killΦ_some]
    apply ENNReal.ofReal_le_ofReal
    apply Real.exp_le_exp.mpr
    have hcast : (rBeyond (L := L) (K := K) T (eraseConfig (L := L) (K := K) mc) : ℝ)
        ≤ (a : ℝ) := by exact_mod_cast hXa
    nlinarith [hsw0, hcast]
  refine le_trans (measure_mono hsub) ?_
  have hdrift := growthPot_drift (L := L) (K := K) T θn n hn s hs1 hslope
  have htail := stepIndexed_killed_tail (markedK (L := L) (K := K) T θn)
    (growthGate (L := L) (K := K) T n)
    (fun j mc => ENNReal.ofReal (Real.exp (-(s j * (rBeyond (L := L) (K := K) T
      (eraseConfig (L := L) (K := K) mc) : ℝ)))))
    hdrift w mc₀ (ENNReal.ofReal (Real.exp (-(s w * (a : ℝ)))))
    (by simp [Real.exp_pos]) ENNReal.ofReal_ne_top
  refine le_trans htail ?_
  dsimp only
  rw [← ENNReal.ofReal_div_of_pos (Real.exp_pos _), ← Real.exp_sub]
  apply ENNReal.ofReal_le_ofReal
  apply Real.exp_le_exp.mpr
  -- s 0 = σ + w·c; goal: −(s 0)·X₀ + s w · a ≤ −(σ + w·c)·X₀ + σ·a, with equality.
  have hs0 : s 0 = σ + (w : ℝ) * c := by rw [hs]; simp
  rw [hs0, hsw]
  ring_nf
  exact le_refl _

/-- **The per-window ladder bound**: for any monotone ladder `a` with `10·a 0 ≤ n` and matching
clean thresholds `Yt`,

  `P[cc·X_w²/n < Y_w ∧ X_w ≤ a M ∧ in-hour] ≤ e^{−σg(X₀ − a 0)} + Σ_m e^{slice-m exponent}`. -/
theorem per_window_ladder (T θn n : ℕ) (hn : 2 ≤ n)
    (cc : ℝ) (hcc : 0 ≤ cc) (σg σ ε : ℝ) (hσg : 0 ≤ σg) (hσ : 0 < σ) (hε : 0 < ε)
    (w : ℕ) (hsmall : σ * (1 + 2 * (1 + ε) / (n : ℝ)) ^ w ≤ ε / (1 + ε))
    (mc₀ : Config (MarkedAgent L K))
    (hR : mc₀.card = n ∧ AllClockGE3 (L := L) (K := K) (eraseConfig (L := L) (K := K) mc₀))
    (a : ℕ → ℕ) (M : ℕ) (ha0 : 10 * a 0 ≤ n) (Yt : ℕ → ℕ)
    (hYt : ∀ m < M, (Yt m : ℝ) ≤ cc * (a m : ℝ) ^ 2 / (n : ℝ) + 1) :
    ((markedK (L := L) (K := K) T θn) ^ w) mc₀
        {mc | (cc * (rBeyond (L := L) (K := K) T
              (eraseConfig (L := L) (K := K) mc) : ℝ) ^ 2 / (n : ℝ)
            < (cleanAbove (L := L) (K := K) T mc : ℝ)) ∧
          rBeyond (L := L) (K := K) T (eraseConfig (L := L) (K := K) mc) ≤ a M ∧
          mc.card = n ∧ AllClockP3 (L := L) (K := K) (eraseConfig (L := L) (K := K) mc)} ≤
      ENNReal.ofReal
        (Real.exp (-(σg * (rBeyond (L := L) (K := K) T
            (eraseConfig (L := L) (K := K) mc₀) : ℝ)) + σg * (a 0 : ℝ))) +
      ∑ m ∈ Finset.range M, ENNReal.ofReal
        (Real.exp (σ * (1 + 2 * (1 + ε) / (n : ℝ)) ^ w
            * (cleanAbove (L := L) (K := K) T mc₀ : ℝ)
          + ((a (m + 1) : ℝ) / (n : ℝ)) ^ 2 * (1 + ε) * σ
              * (1 + 2 * (1 + ε) / (n : ℝ)) ^ w * (w : ℝ)
          - σ * (Yt m : ℝ))) := by
  classical
  set src : Set (Config (MarkedAgent L K)) :=
    {mc | (cc * (rBeyond (L := L) (K := K) T
          (eraseConfig (L := L) (K := K) mc) : ℝ) ^ 2 / (n : ℝ)
        < (cleanAbove (L := L) (K := K) T mc : ℝ)) ∧
      rBeyond (L := L) (K := K) T (eraseConfig (L := L) (K := K) mc) ≤ a M ∧
      mc.card = n ∧ AllClockP3 (L := L) (K := K) (eraseConfig (L := L) (K := K) mc)}
    with hsrc
  -- the refined split: keep the hour/card info in the floor branch.
  have hsplit : src ⊆
      {mc : Config (MarkedAgent L K) |
          rBeyond (L := L) (K := K) T (eraseConfig (L := L) (K := K) mc) ≤ a 0 ∧
            mc ∈ growthGate (L := L) (K := K) T n} ∪
        ⋃ m ∈ Finset.range M,
          {mc : Config (MarkedAgent L K) |
            Yt m ≤ cleanAbove (L := L) (K := K) T mc ∧
              mc ∈ cleanGate (L := L) (K := K) T n (a (m + 1))} := by
    intro mc hmc
    have hsub := ladder_bad_subset (L := L) (K := K) T n cc hcc a M Yt hYt hmc
    rcases hsub with hfloor | hrungs
    · left
      obtain ⟨_, _, hcard, hP3⟩ := hmc
      refine ⟨hfloor, hcard, hP3, ?_⟩
      rw [Set.mem_setOf_eq] at hfloor
      omega
    · exact Or.inr hrungs
  refine le_trans (measure_mono hsplit) ?_
  refine le_trans (measure_union_le _ _) ?_
  refine add_le_add ?_ ?_
  · exact slice_growth_tail (L := L) (K := K) T θn n hn σg hσg w mc₀ hR (a 0)
  · refine le_trans (measure_biUnion_finset_le _ _) ?_
    apply Finset.sum_le_sum
    intro m _
    exact slice_clean_tail_explicit (L := L) (K := K) T θn n (a (m + 1)) hn σ ε hσ hε w
      hsmall mc₀ hR (Yt m)

/-- **The per-window ladder bound, UPWARD floor** (brick 3.5e): identical to `per_window_ladder`
but the floor branch uses the UPWARD growth tail `slice_growth_tail_up`, so the floor exponent is
`−(σg + w·cg)·X₀ + σg·a0` (`cg = 1.8(1−e^{−σg})/n`) — small even for the growth floor `a0 = g·X₀`,
`g > 1`.  This is the version the recurrence actually consumes. -/
theorem per_window_ladder_up (T θn n : ℕ) (hn : 2 ≤ n)
    (cc : ℝ) (hcc : 0 ≤ cc) (σg σ ε : ℝ) (hσg : 0 < σg) (hσ : 0 < σ) (hε : 0 < ε)
    (w : ℕ) (hsmall : σ * (1 + 2 * (1 + ε) / (n : ℝ)) ^ w ≤ ε / (1 + ε))
    (mc₀ : Config (MarkedAgent L K))
    (hR : mc₀.card = n ∧ AllClockGE3 (L := L) (K := K) (eraseConfig (L := L) (K := K) mc₀))
    (a : ℕ → ℕ) (M : ℕ) (ha0 : 10 * a 0 ≤ n) (Yt : ℕ → ℕ)
    (hYt : ∀ m < M, (Yt m : ℝ) ≤ cc * (a m : ℝ) ^ 2 / (n : ℝ) + 1) :
    ((markedK (L := L) (K := K) T θn) ^ w) mc₀
        {mc | (cc * (rBeyond (L := L) (K := K) T
              (eraseConfig (L := L) (K := K) mc) : ℝ) ^ 2 / (n : ℝ)
            < (cleanAbove (L := L) (K := K) T mc : ℝ)) ∧
          rBeyond (L := L) (K := K) T (eraseConfig (L := L) (K := K) mc) ≤ a M ∧
          mc.card = n ∧ AllClockP3 (L := L) (K := K) (eraseConfig (L := L) (K := K) mc)} ≤
      ENNReal.ofReal
        (Real.exp (-((σg + (w : ℝ) * (1.8 * (1 - Real.exp (-σg)) / (n : ℝ)))
            * (rBeyond (L := L) (K := K) T
              (eraseConfig (L := L) (K := K) mc₀) : ℝ))
          + σg * (a 0 : ℝ))) +
      ∑ m ∈ Finset.range M, ENNReal.ofReal
        (Real.exp (σ * (1 + 2 * (1 + ε) / (n : ℝ)) ^ w
            * (cleanAbove (L := L) (K := K) T mc₀ : ℝ)
          + ((a (m + 1) : ℝ) / (n : ℝ)) ^ 2 * (1 + ε) * σ
              * (1 + 2 * (1 + ε) / (n : ℝ)) ^ w * (w : ℝ)
          - σ * (Yt m : ℝ))) := by
  classical
  set src : Set (Config (MarkedAgent L K)) :=
    {mc | (cc * (rBeyond (L := L) (K := K) T
          (eraseConfig (L := L) (K := K) mc) : ℝ) ^ 2 / (n : ℝ)
        < (cleanAbove (L := L) (K := K) T mc : ℝ)) ∧
      rBeyond (L := L) (K := K) T (eraseConfig (L := L) (K := K) mc) ≤ a M ∧
      mc.card = n ∧ AllClockP3 (L := L) (K := K) (eraseConfig (L := L) (K := K) mc)}
    with hsrc
  have hsplit : src ⊆
      {mc : Config (MarkedAgent L K) |
          rBeyond (L := L) (K := K) T (eraseConfig (L := L) (K := K) mc) ≤ a 0 ∧
            mc ∈ growthGate (L := L) (K := K) T n} ∪
        ⋃ m ∈ Finset.range M,
          {mc : Config (MarkedAgent L K) |
            Yt m ≤ cleanAbove (L := L) (K := K) T mc ∧
              mc ∈ cleanGate (L := L) (K := K) T n (a (m + 1))} := by
    intro mc hmc
    have hsub := ladder_bad_subset (L := L) (K := K) T n cc hcc a M Yt hYt hmc
    rcases hsub with hfloor | hrungs
    · left
      obtain ⟨_, _, hcard, hP3⟩ := hmc
      refine ⟨hfloor, hcard, hP3, ?_⟩
      rw [Set.mem_setOf_eq] at hfloor
      omega
    · exact Or.inr hrungs
  refine le_trans (measure_mono hsplit) ?_
  refine le_trans (measure_union_le _ _) ?_
  refine add_le_add ?_ ?_
  · exact slice_growth_tail_up (L := L) (K := K) T θn n hn σg hσg w mc₀ hR (a 0)
  · refine le_trans (measure_biUnion_finset_le _ _) ?_
    apply Finset.sum_le_sum
    intro m _
    exact slice_clean_tail_explicit (L := L) (K := K) T θn n (a (m + 1)) hn σ ε hσ hε w
      hsmall mc₀ hR (Yt m)

/-! ## Part 29 — the locked window constants (brick 3.5e step 1, the norm_num closing gate).

The two binding inequalities of the per-window recurrence at the LOCKED constants
(wp = 3/200, cc = 9/10, ε = 1/200, g = 5123/5000 ≈ 1.0246, G = 201/200 = 1.005, sg = 1/10),
both verified with `norm_num` over exact rationals using the Lean-provable bounds
`exp(u) ≤ 1/(1−u)` (slice) and `1−e^{−sg} ≥ sg − sg²/2` (growth). -/

/-- **The slice closing inequality** `A < B` with `A = cc·RWb`, `B = g²(cc − G²(1+ε)·RWb·wp)`,
`RWb = 1/(1−u)`, `u = 2(1+ε)wp` — the single inequality from which every ladder slice bracket
`A − G^{2m}·B < 0` follows (`G^{2m} ≥ 1`, `B > 0`).  Margin ≈ 3.6e-4. -/
theorem window_constants_slice :
    let wp : ℝ := 3/200
    let cc : ℝ := 9/10
    let ε : ℝ := 1/200
    let g : ℝ := 5123/5000
    let G : ℝ := 201/200
    let u : ℝ := 2 * (1 + ε) * wp
    let RWb : ℝ := 1 / (1 - u)
    cc * RWb < g^2 * (cc - G^2 * (1 + ε) * RWb * wp) ∧
      (0 : ℝ) < g^2 * (cc - G^2 * (1 + ε) * RWb * wp) := by
  norm_num

/-- **The growth closing inequality** `δ > 0`, `δ = 1.8(sg − sg²/2)·wp − sg(g−1)` — the floor-tail
exponent slope, using `1−e^{−sg} ≥ sg − sg²/2`.  Margin ≈ 1.05e-4. -/
theorem window_constants_growth :
    let wp : ℝ := 3/200
    let g : ℝ := 5123/5000
    let sg : ℝ := 1/10
    (0 : ℝ) < 18/10 * (sg - sg^2/2) * wp - sg * (g - 1) := by
  norm_num

/-- **The floor-exponent bound**: the upward-growth floor exponent of `per_window_ladder_up`,
`−(sg + w·cg)·X₀ + sg·a0` with `cg = 1.8(1−e^{−sg})/n` and `a0 ≤ g·X₀ + 1`, is at most
`−δ·X₀ + sg` whenever the per-step growth margin `δ ≤ w·cg − sg·(g−1)` holds.  This isolates the
`exp(−Ω(X₀))` floor decay; the margin hypothesis is discharged from `window_constants_growth`. -/
theorem floor_exp_le (n : ℕ) (sg g δ : ℝ) (hsg : 0 ≤ sg)
    (w : ℕ) (X₀ : ℕ) (a0 : ℕ) (ha0 : (a0 : ℝ) ≤ g * (X₀ : ℝ) + 1)
    (hδ : δ ≤ (w : ℝ) * (1.8 * (1 - Real.exp (-sg)) / (n : ℝ)) - sg * (g - 1)) :
    -((sg + (w : ℝ) * (1.8 * (1 - Real.exp (-sg)) / (n : ℝ))) * (X₀ : ℝ)) + sg * (a0 : ℝ)
      ≤ -(δ * (X₀ : ℝ)) + sg := by
  set cg : ℝ := 1.8 * (1 - Real.exp (-sg)) / (n : ℝ) with hcg
  have hX0 : (0 : ℝ) ≤ (X₀ : ℝ) := by positivity
  have h1 : sg * (a0 : ℝ) ≤ sg * (g * (X₀ : ℝ) + 1) :=
    mul_le_mul_of_nonneg_left ha0 hsg
  have hmargin : δ ≤ (w : ℝ) * cg - sg * (g - 1) := by rw [hcg]; exact hδ
  nlinarith [mul_le_mul_of_nonneg_right hmargin hX0, h1, hX0]

/-- **The slice-exponent bound**: the rung-`m` clean exponent of `per_window_ladder_up`,
`σ·RW·Y₀ + (a_{m+1}/n)²(1+ε)·σ·RW·w − σ·Yt`, is at most `σ·(X₀²/n)·(A − Gm·B)` where
`A = cc·RWb`, `B = g²(cc − G²(1+ε)RWb·wp)`, `Gm = G^{2m}` — given the structural inputs
(invariant `Y₀ ≤ cc·X₀²/n`, `RW ≤ RWb`, the drip cap, the threshold lower bound).  `Gm ≥ 1` and
`A < B` (`window_constants_slice`) then make every rung `≤ σ(X₀²/n)(A − B) < 0`. -/
theorem slice_exp_le (Q σ ε RW RWb cc g G wp Y₀ drip Gm Yt : ℝ)
    (hσ : 0 ≤ σ) (hQ : 0 ≤ Q) (hRW0 : 0 ≤ RW) (hccnn : 0 ≤ cc) (hε0 : 0 ≤ ε)
    (hY : Y₀ ≤ cc * Q) (hRW : RW ≤ RWb) (hRWb0 : 0 ≤ RWb)
    (hdrip : drip * (1 + ε) * RW ≤ Gm * G ^ 2 * g ^ 2 * (1 + ε) * RWb * wp * Q)
    (hdrip0 : 0 ≤ drip)
    (hYt : cc * Gm * g ^ 2 * Q ≤ Yt) :
    σ * RW * Y₀ + drip * (1 + ε) * σ * RW - σ * Yt
      ≤ σ * (Q * (cc * RWb - Gm * (g ^ 2 * (cc - G ^ 2 * (1 + ε) * RWb * wp)))) := by
  -- RW·Y₀ ≤ RWb·cc·Q ; drip(1+ε)RW ≤ Gm·G²·g²(1+ε)RWb·wp·Q ; Yt ≥ cc·Gm·g²·Q.
  have hb1 : RW * Y₀ ≤ RWb * (cc * Q) := by
    calc RW * Y₀ ≤ RW * (cc * Q) := mul_le_mul_of_nonneg_left hY hRW0
      _ ≤ RWb * (cc * Q) := mul_le_mul_of_nonneg_right hRW
          (mul_nonneg hccnn hQ)
  have hkey : RW * Y₀ + drip * (1 + ε) * RW - Yt
      ≤ Q * (cc * RWb - Gm * (g ^ 2 * (cc - G ^ 2 * (1 + ε) * RWb * wp))) := by
    nlinarith [hb1, hdrip, hYt]
  calc σ * RW * Y₀ + drip * (1 + ε) * σ * RW - σ * Yt
      = σ * (RW * Y₀ + drip * (1 + ε) * RW - Yt) := by ring
    _ ≤ σ * (Q * (cc * RWb - Gm * (g ^ 2 * (cc - G ^ 2 * (1 + ε) * RWb * wp)))) :=
        mul_le_mul_of_nonneg_left hkey hσ

/-- **The uniform slice-sum bound**: a finite sum of `M` real-exponential slice terms, each with
exponent `≤ σ·Q·(A − Gm_m·B)`, is bounded by `M · exp(σ·Q·(A − B))` once `Gm_m ≥ 1` and `B ≥ 0`
(so `A − Gm_m·B ≤ A − B`).  At the locked constants `A − B < 0`, so the uniform term is a genuine
`exp(−Ω(σ·Q))` decay times the rung count `M = O(log n)`. -/
theorem slice_sum_le (M : ℕ) (σ Q A B : ℝ) (Gm : ℕ → ℝ) (e : ℕ → ℝ)
    (hσQ : 0 ≤ σ * Q) (hB : 0 ≤ B) (hGm : ∀ m, 1 ≤ Gm m)
    (he : ∀ m < M, e m ≤ σ * (Q * (A - Gm m * B))) :
    ∑ m ∈ Finset.range M, ENNReal.ofReal (Real.exp (e m))
      ≤ (M : ℝ≥0∞) * ENNReal.ofReal (Real.exp (σ * (Q * (A - B)))) := by
  classical
  have hbound : ∀ m ∈ Finset.range M, ENNReal.ofReal (Real.exp (e m))
      ≤ ENNReal.ofReal (Real.exp (σ * (Q * (A - B)))) := by
    intro m hm
    rw [Finset.mem_range] at hm
    apply ENNReal.ofReal_le_ofReal
    apply Real.exp_le_exp.mpr
    refine le_trans (he m hm) ?_
    -- σQ(A − Gm·B) ≤ σQ(A − B) since Gm ≥ 1, B ≥ 0 ⟹ Gm·B ≥ B.
    have hGmB : B ≤ Gm m * B := by nlinarith [hGm m, hB]
    nlinarith [hσQ, hGmB]
  calc ∑ m ∈ Finset.range M, ENNReal.ofReal (Real.exp (e m))
      ≤ ∑ _m ∈ Finset.range M, ENNReal.ofReal (Real.exp (σ * (Q * (A - B)))) :=
        Finset.sum_le_sum hbound
    _ = (M : ℝ≥0∞) * ENNReal.ofReal (Real.exp (σ * (Q * (A - B)))) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

/-! ## Part 30 — the UNIFORM per-window δ (brick 3.5e step 1 capstone).

Assemble: `per_window_ladder_up`'s pure-exponential RHS, bounded by the floor decay
`exp(−δg·X₀ + sg)` (via `floor_exp_le`) plus the uniform slice sum `M·exp(σ·Q·(A−B))` (via
`slice_exp_le` per rung + `slice_sum_le`).  This is the deterministic δ consumed by
`checkpoint_composition` in step 2 — a function of `X₀ = rBeyond T (erase mc₀)` and `Y₀ =
cleanAbove T mc₀` only, of size `exp(−Ω(n^{0.1}))` at the paper scales (`X₀ ≥ θn ≥ n^{0.55}`,
`Q = X₀²/n ≥ n^{0.1}`, `A − B < 0`, `δg > 0`). -/

/-- **The uniform per-window δ**: from `per_window_ladder_up` plus the floor/slice exponent bounds,
the per-window Lemma-6.3 failure from an invariant start `mc₀` is at most
`exp(−δg·X₀ + sg) + M·exp(σ·Q·(A − B))`, with `δg > 0` and `A − B < 0` at the locked constants —
a deterministic δ in `(X₀, Y₀)`.  All per-rung structural facts (`RW ≤ RWb`, the drip caps, the
threshold lower bounds, `G^{2m} ≥ 1`) are taken as hypotheses to be discharged at the scale
plug-in. -/
theorem per_window_delta (T θn n : ℕ) (hn : 2 ≤ n)
    (cc σg σ ε : ℝ) (hcc : 0 ≤ cc) (hσg : 0 < σg) (hσ : 0 < σ) (hε : 0 < ε)
    (w : ℕ) (hsmall : σ * (1 + 2 * (1 + ε) / (n : ℝ)) ^ w ≤ ε / (1 + ε))
    (mc₀ : Config (MarkedAgent L K))
    (hR : mc₀.card = n ∧ AllClockGE3 (L := L) (K := K) (eraseConfig (L := L) (K := K) mc₀))
    (a : ℕ → ℕ) (M : ℕ) (ha0 : 10 * a 0 ≤ n) (Yt : ℕ → ℕ)
    (hYt : ∀ m < M, (Yt m : ℝ) ≤ cc * (a m : ℝ) ^ 2 / (n : ℝ) + 1)
    -- the deterministic δ parameters and the discharging facts:
    (δg g G RWb : ℝ) (Gm : ℕ → ℝ)
    (hGm1 : ∀ m, 1 ≤ Gm m) (hRWb0 : 0 ≤ RWb)
    (hQ0 : 0 ≤ (rBeyond (L := L) (K := K) T (eraseConfig (L := L) (K := K) mc₀) : ℝ) ^ 2 / (n : ℝ))
    (hB0 : 0 ≤ g ^ 2 * (cc - G ^ 2 * (1 + ε) * RWb * (3 / 200)))
    (hfloor : -((σg + (w : ℝ) * (1.8 * (1 - Real.exp (-σg)) / (n : ℝ)))
          * (rBeyond (L := L) (K := K) T (eraseConfig (L := L) (K := K) mc₀) : ℝ))
        + σg * (a 0 : ℝ) ≤ -(δg
          * (rBeyond (L := L) (K := K) T (eraseConfig (L := L) (K := K) mc₀) : ℝ)) + σg)
    (hslice : ∀ m < M,
      σ * (1 + 2 * (1 + ε) / (n : ℝ)) ^ w
            * (cleanAbove (L := L) (K := K) T mc₀ : ℝ)
          + ((a (m + 1) : ℝ) / (n : ℝ)) ^ 2 * (1 + ε) * σ
              * (1 + 2 * (1 + ε) / (n : ℝ)) ^ w * (w : ℝ)
          - σ * (Yt m : ℝ)
        ≤ σ * (((rBeyond (L := L) (K := K) T
              (eraseConfig (L := L) (K := K) mc₀) : ℝ) ^ 2 / (n : ℝ))
            * (cc * RWb - Gm m * (g ^ 2 * (cc - G ^ 2 * (1 + ε) * RWb * (3 / 200)))))) :
    ((markedK (L := L) (K := K) T θn) ^ w) mc₀
        {mc | (cc * (rBeyond (L := L) (K := K) T
              (eraseConfig (L := L) (K := K) mc) : ℝ) ^ 2 / (n : ℝ)
            < (cleanAbove (L := L) (K := K) T mc : ℝ)) ∧
          rBeyond (L := L) (K := K) T (eraseConfig (L := L) (K := K) mc) ≤ a M ∧
          mc.card = n ∧ AllClockP3 (L := L) (K := K) (eraseConfig (L := L) (K := K) mc)} ≤
      ENNReal.ofReal (Real.exp (-(δg
          * (rBeyond (L := L) (K := K) T (eraseConfig (L := L) (K := K) mc₀) : ℝ)) + σg))
      + (M : ℝ≥0∞) * ENNReal.ofReal (Real.exp (σ
          * (((rBeyond (L := L) (K := K) T (eraseConfig (L := L) (K := K) mc₀) : ℝ) ^ 2
                / (n : ℝ))
              * (cc * RWb - g ^ 2 * (cc - G ^ 2 * (1 + ε) * RWb * (3 / 200)))))) := by
  classical
  refine le_trans (per_window_ladder_up (L := L) (K := K) T θn n hn cc hcc σg σ ε hσg hσ hε
    w hsmall mc₀ hR a M ha0 Yt hYt) ?_
  refine add_le_add ?_ ?_
  · exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr hfloor)
  · -- the slice sum, via slice_sum_le with e m the per_window_ladder_up slice exponent.
    refine le_trans ?_ (le_refl _)
    refine slice_sum_le M σ
      ((rBeyond (L := L) (K := K) T (eraseConfig (L := L) (K := K) mc₀) : ℝ) ^ 2 / (n : ℝ))
      (cc * RWb) (g ^ 2 * (cc - G ^ 2 * (1 + ε) * RWb * (3 / 200))) Gm
      (fun m => σ * (1 + 2 * (1 + ε) / (n : ℝ)) ^ w
            * (cleanAbove (L := L) (K := K) T mc₀ : ℝ)
          + ((a (m + 1) : ℝ) / (n : ℝ)) ^ 2 * (1 + ε) * σ
              * (1 + 2 * (1 + ε) / (n : ℝ)) ^ w * (w : ℝ)
          - σ * (Yt m : ℝ))
      (mul_nonneg hσ.le hQ0) hB0 hGm1 (fun m hm => hslice m hm)

/-! ## Part 31 — the recurrence invariant and the per-window failure bound (brick 3.5e step 2).

`recInv` is Lemma 6.3's induction invariant at level `T`: inside the hour region (full population,
phases ≥ 3), WHILE the level is in the recurrence window (`AllClockP3 ∧ 10X ≤ n`), the feeder has
reached the gate floor (`θn ≤ X`) and the clean tail obeys the recurrence (`Y ≤ cc·X²/n`).  The
window-exit disjuncts (phase 4 reached, or `10X > n`) are PERMANENT (phase monotone, `X` monotone),
so a window that starts exited never re-enters — failure only happens through the per-window bad
event, which is exactly `per_window_delta`'s. -/

/-- The hour region: full population, all clocks at phases ≥ 3 (forward-invariant a.e.). -/
def hourRegion (n : ℕ) : Set (Config (MarkedAgent L K)) :=
  {mc | mc.card = n ∧ AllClockGE3 (L := L) (K := K) (eraseConfig (L := L) (K := K) mc)}

/-- The hour region is preserved by one marked step (a.e.). -/
theorem hourRegion_ae_step (T θn n : ℕ) (mc : Config (MarkedAgent L K))
    (hmc : mc ∈ hourRegion (L := L) (K := K) n) :
    ∀ᵐ mc' ∂(markedK (L := L) (K := K) T θn mc),
      mc' ∈ hourRegion (L := L) (K := K) n := by
  classical
  obtain ⟨hcard, hge3⟩ := hmc
  refine ae_markedStep (L := L) (K := K) T θn mc _ (fun mc' hsupp => ⟨?_, ?_⟩)
  · have h1 := eraseConfig_card (L := L) (K := K) mc
    have h2 := eraseConfig_card (L := L) (K := K) mc'
    revert hsupp
    unfold markedPMF
    by_cases h : 2 ≤ mc.card
    · rw [dif_pos h]
      intro hsupp
      rw [PMF.support_map] at hsupp
      obtain ⟨pr, _, hpr⟩ := hsupp
      subst hpr
      by_cases happ : ({pr.1, pr.2} : Multiset (MarkedAgent L K)) ≤ mc
      · have herase := erase_markedStep (L := L) (K := K) T θn mc pr happ
        have hreal : (eraseConfig (L := L) (K := K)
            (markedStep (L := L) (K := K) T θn mc pr)).card
            = (eraseConfig (L := L) (K := K) mc).card := by
          rw [herase]
          exact Protocol.reachable_card_eq
            (Protocol.reachable_stepOrSelf (P := NonuniformMajority L K) _ pr.1.1 pr.2.1)
        omega
      · unfold markedStep
        rw [if_neg happ]
        omega
    · rw [dif_neg h]
      intro hsupp
      rw [PMF.support_pure] at hsupp
      rw [Set.mem_singleton_iff.mp hsupp]
      omega
  · exact allClockGE3_erase_step (L := L) (K := K) T θn mc mc' hge3 hsupp

/-- Leaving the `AllClockP3` hour window is permanent (one step, a.e., within the region): within
`AllClockGE3`, `¬AllClockP3` means a phase-4 witness, and witnesses persist. -/
theorem notP3_ae_step (T θn n : ℕ) (mc : Config (MarkedAgent L K))
    (hmc : mc ∈ hourRegion (L := L) (K := K) n)
    (hP3 : ¬ AllClockP3 (L := L) (K := K) (eraseConfig (L := L) (K := K) mc)) :
    ∀ᵐ mc' ∂(markedK (L := L) (K := K) T θn mc),
      ¬ AllClockP3 (L := L) (K := K) (eraseConfig (L := L) (K := K) mc') := by
  classical
  obtain ⟨hcard, hge3⟩ := hmc
  have h4 : ∃ m ∈ mc, 4 ≤ m.1.phase.val := by
    by_contra hcon
    push Not at hcon
    apply hP3
    intro a ha
    unfold eraseConfig at ha
    obtain ⟨m, hm, hma⟩ := Multiset.mem_map.mp ha
    have hge := hge3 a ha
    have hno4 := hcon m hm
    refine ⟨hge.1, ?_⟩
    have h3 : 3 ≤ a.phase.val := hge.2
    have : a.phase.val ≤ 3 := by
      rw [← hma]
      omega
    omega
  refine ae_markedStep (L := L) (K := K) T θn mc _ (fun mc' hsupp => ?_)
  have h4' := phase4_witness_absorbing (L := L) (K := K) T θn mc mc' h4 hsupp
  intro hP3'
  obtain ⟨m, hm, hm4⟩ := h4'
  have := hP3' m.1 (by
    unfold eraseConfig
    exact Multiset.mem_map_of_mem Prod.fst hm)
  omega

/-- **The Lemma 6.3 recurrence invariant at level `T`**: inside the hour region, while the level is
in the recurrence window (`AllClockP3 ∧ 10X ≤ n`), the feeder is past the floor and the clean tail
obeys the recurrence. -/
def recInv (T θn n : ℕ) (cc : ℝ) (mc : Config (MarkedAgent L K)) : Prop :=
  mc.card = n ∧ AllClockGE3 (L := L) (K := K) (eraseConfig (L := L) (K := K) mc) ∧
    (AllClockP3 (L := L) (K := K) (eraseConfig (L := L) (K := K) mc) →
      10 * rBeyond (L := L) (K := K) T (eraseConfig (L := L) (K := K) mc) ≤ n →
      (θn ≤ rBeyond (L := L) (K := K) T (eraseConfig (L := L) (K := K) mc) ∧
        (cleanAbove (L := L) (K := K) T mc : ℝ) ≤
          cc * (rBeyond (L := L) (K := K) T
            (eraseConfig (L := L) (K := K) mc) : ℝ) ^ 2 / (n : ℝ)))

/-- **The per-window failure bound for the recurrence invariant**: from any `recInv` start, the
probability that `recInv` fails after `w` steps is at most the recurrence-window bad-event bound
`δ` (supplied, in the live case, by `per_window_delta`); the window-exit and region-exit failure
modes are NULL (monotone/absorbing).  This is `checkpoint_composition`'s `hwindow` input. -/
theorem window_failure_le (T θn n : ℕ) (cc : ℝ) (w : ℕ) (aM : ℕ) (haM : n ≤ 10 * aM)
    (δ : ℝ≥0∞) (mc₀ : Config (MarkedAgent L K))
    (hInv : recInv (L := L) (K := K) T θn n cc mc₀)
    (hB : AllClockP3 (L := L) (K := K) (eraseConfig (L := L) (K := K) mc₀) →
      10 * rBeyond (L := L) (K := K) T (eraseConfig (L := L) (K := K) mc₀) ≤ n →
      ((markedK (L := L) (K := K) T θn) ^ w) mc₀
          {mc | (cc * (rBeyond (L := L) (K := K) T
                (eraseConfig (L := L) (K := K) mc) : ℝ) ^ 2 / (n : ℝ)
              < (cleanAbove (L := L) (K := K) T mc : ℝ)) ∧
            rBeyond (L := L) (K := K) T (eraseConfig (L := L) (K := K) mc) ≤ aM ∧
            mc.card = n ∧ AllClockP3 (L := L) (K := K) (eraseConfig (L := L) (K := K) mc)}
        ≤ δ) :
    ((markedK (L := L) (K := K) T θn) ^ w) mc₀
        {mc | ¬ recInv (L := L) (K := K) T θn n cc mc} ≤ δ := by
  classical
  obtain ⟨hcard, hge3, himpl⟩ := hInv
  have hR : mc₀ ∈ hourRegion (L := L) (K := K) n := ⟨hcard, hge3⟩
  -- region preservation at w steps (null region-exit).
  have hRstep : ∀ mc ∈ hourRegion (L := L) (K := K) n,
      ∀ᵐ mc' ∂(markedK (L := L) (K := K) T θn mc),
        mc' ∈ hourRegion (L := L) (K := K) n :=
    fun mc hmc => hourRegion_ae_step (L := L) (K := K) T θn n mc hmc
  have hnull_region : ((markedK (L := L) (K := K) T θn) ^ w) mc₀
      {mc | mc ∉ hourRegion (L := L) (K := K) n} = 0 := by
    have h := ae_notG_pow (markedK (L := L) (K := K) T θn)
      (hourRegion (L := L) (K := K) n) (hourRegion (L := L) (K := K) n)ᶜ
      hRstep
      (fun mc hmc _ => by
        filter_upwards [hRstep mc hmc] with mc' hmc'
        exact fun hc => hc hmc')
      w mc₀ hR (fun hc => hc hR)
    rw [MeasureTheory.ae_iff] at h
    have hset : {z : Config (MarkedAgent L K) | ¬ z ∉ (hourRegion (L := L) (K := K) n)ᶜ}
        = {mc | mc ∉ hourRegion (L := L) (K := K) n} := by
      ext z
      simp [Set.mem_compl_iff, not_not]
    rwa [hset] at h
  by_cases hP3₀ : AllClockP3 (L := L) (K := K) (eraseConfig (L := L) (K := K) mc₀)
  · by_cases hX₀ : 10 * rBeyond (L := L) (K := K) T (eraseConfig (L := L) (K := K) mc₀) ≤ n
    · -- the live case: the recurrence window is open at the start.
      obtain ⟨hθ, hY⟩ := himpl hP3₀ hX₀
      -- X never drops below θn (null floor-exit).
      have hnull_theta : ((markedK (L := L) (K := K) T θn) ^ w) mc₀
          {mc | rBeyond (L := L) (K := K) T (eraseConfig (L := L) (K := K) mc) < θn} = 0 := by
        have h := ae_notG_pow (markedK (L := L) (K := K) T θn)
          (hourRegion (L := L) (K := K) n)
          {mc | rBeyond (L := L) (K := K) T (eraseConfig (L := L) (K := K) mc) < θn}
          hRstep
          (fun mc hmc hG => by
            refine ae_markedStep (L := L) (K := K) T θn mc _ (fun mc' hsupp => ?_)
            have hmono := rBeyond_erase_monotone_ge3 (L := L) (K := K) T θn T mc mc'
              hmc.2 hsupp
            rw [Set.mem_setOf_eq] at hG ⊢
            omega)
          w mc₀ hR (by
            rw [Set.mem_setOf_eq]
            omega)
        rw [MeasureTheory.ae_iff] at h
        have hset : {z : Config (MarkedAgent L K) |
            ¬ z ∉ {mc | rBeyond (L := L) (K := K) T (eraseConfig (L := L) (K := K) mc) < θn}}
            = {mc | rBeyond (L := L) (K := K) T (eraseConfig (L := L) (K := K) mc) < θn} := by
          ext z
          simp
        rwa [hset] at h
      -- split the failure into the two null modes and the bad event.
      have hsub : {mc | ¬ recInv (L := L) (K := K) T θn n cc mc} ⊆
          {mc | mc ∉ hourRegion (L := L) (K := K) n} ∪
          ({mc | rBeyond (L := L) (K := K) T (eraseConfig (L := L) (K := K) mc) < θn} ∪
          {mc | (cc * (rBeyond (L := L) (K := K) T
                (eraseConfig (L := L) (K := K) mc) : ℝ) ^ 2 / (n : ℝ)
              < (cleanAbove (L := L) (K := K) T mc : ℝ)) ∧
            rBeyond (L := L) (K := K) T (eraseConfig (L := L) (K := K) mc) ≤ aM ∧
            mc.card = n ∧
            AllClockP3 (L := L) (K := K) (eraseConfig (L := L) (K := K) mc)}) := by
        intro mc hmc
        rw [Set.mem_setOf_eq] at hmc
        by_cases hreg : mc ∈ hourRegion (L := L) (K := K) n
        · right
          by_cases hθ' : rBeyond (L := L) (K := K) T (eraseConfig (L := L) (K := K) mc) < θn
          · exact Or.inl hθ'
          · right
            -- in-region, floor held: the failure must be the recurrence break in the window.
            unfold recInv at hmc
            push Not at hmc
            obtain ⟨hregc, hregg⟩ := hreg
            obtain ⟨hP3', hXw, hbreak⟩ := hmc hregc hregg
            have hbreak' : cc * (rBeyond (L := L) (K := K) T
                (eraseConfig (L := L) (K := K) mc) : ℝ) ^ 2 / (n : ℝ)
                < (cleanAbove (L := L) (K := K) T mc : ℝ) := hbreak (by omega)
            exact ⟨hbreak', by omega, hregc, hP3'⟩
        · exact Or.inl hreg
      refine le_trans (measure_mono hsub) ?_
      refine le_trans (measure_union_le _ _) ?_
      rw [hnull_region, zero_add]
      refine le_trans (measure_union_le _ _) ?_
      rw [hnull_theta, zero_add]
      exact hB hP3₀ hX₀
    · -- the bulk has arrived at the start: `10X > n` is permanent, the window never reopens.
      have hnull_X : ((markedK (L := L) (K := K) T θn) ^ w) mc₀
          {mc | 10 * rBeyond (L := L) (K := K) T (eraseConfig (L := L) (K := K) mc) ≤ n}
          = 0 := by
        have h := ae_notG_pow (markedK (L := L) (K := K) T θn)
          (hourRegion (L := L) (K := K) n)
          {mc | 10 * rBeyond (L := L) (K := K) T (eraseConfig (L := L) (K := K) mc) ≤ n}
          hRstep
          (fun mc hmc hG => by
            refine ae_markedStep (L := L) (K := K) T θn mc _ (fun mc' hsupp => ?_)
            have hmono := rBeyond_erase_monotone_ge3 (L := L) (K := K) T θn T mc mc'
              hmc.2 hsupp
            rw [Set.mem_setOf_eq] at hG ⊢
            omega)
          w mc₀ hR (by
            rw [Set.mem_setOf_eq]
            omega)
        rw [MeasureTheory.ae_iff] at h
        have hset : {z : Config (MarkedAgent L K) |
            ¬ z ∉ {mc | 10 * rBeyond (L := L) (K := K) T
                (eraseConfig (L := L) (K := K) mc) ≤ n}}
            = {mc | 10 * rBeyond (L := L) (K := K) T
                (eraseConfig (L := L) (K := K) mc) ≤ n} := by
          ext z
          simp
        rwa [hset] at h
      have hsub : {mc | ¬ recInv (L := L) (K := K) T θn n cc mc} ⊆
          {mc | mc ∉ hourRegion (L := L) (K := K) n} ∪
          {mc | 10 * rBeyond (L := L) (K := K) T (eraseConfig (L := L) (K := K) mc) ≤ n} := by
        intro mc hmc
        rw [Set.mem_setOf_eq] at hmc
        by_cases hreg : mc ∈ hourRegion (L := L) (K := K) n
        · right
          unfold recInv at hmc
          push Not at hmc
          obtain ⟨hregc, hregg⟩ := hreg
          obtain ⟨_, hXw, _⟩ := hmc hregc hregg
          exact hXw
        · exact Or.inl hreg
      refine le_trans (measure_mono hsub) ?_
      refine le_trans (measure_union_le _ _) ?_
      rw [hnull_region, hnull_X, zero_add]
      exact zero_le'
  · -- the hour window is already over at the start: `¬P3` is permanent.
    have hnull_P3 : ((markedK (L := L) (K := K) T θn) ^ w) mc₀
        {mc | AllClockP3 (L := L) (K := K) (eraseConfig (L := L) (K := K) mc)} = 0 := by
      have h := ae_notG_pow (markedK (L := L) (K := K) T θn)
        (hourRegion (L := L) (K := K) n)
        {mc | AllClockP3 (L := L) (K := K) (eraseConfig (L := L) (K := K) mc)}
        hRstep
        (fun mc hmc hG => by
          have := notP3_ae_step (L := L) (K := K) T θn n mc hmc (by
            rw [Set.mem_setOf_eq] at hG
            exact hG)
          filter_upwards [this] with mc' hmc'
          exact hmc')
        w mc₀ hR (by
          rw [Set.mem_setOf_eq]
          exact hP3₀)
      rw [MeasureTheory.ae_iff] at h
      have hset : {z : Config (MarkedAgent L K) |
          ¬ z ∉ {mc | AllClockP3 (L := L) (K := K) (eraseConfig (L := L) (K := K) mc)}}
          = {mc | AllClockP3 (L := L) (K := K) (eraseConfig (L := L) (K := K) mc)} := by
        ext z
        simp
      rwa [hset] at h
    have hsub : {mc | ¬ recInv (L := L) (K := K) T θn n cc mc} ⊆
        {mc | mc ∉ hourRegion (L := L) (K := K) n} ∪
        {mc | AllClockP3 (L := L) (K := K) (eraseConfig (L := L) (K := K) mc)} := by
      intro mc hmc
      rw [Set.mem_setOf_eq] at hmc
      by_cases hreg : mc ∈ hourRegion (L := L) (K := K) n
      · right
        unfold recInv at hmc
        push Not at hmc
        obtain ⟨hregc, hregg⟩ := hreg
        obtain ⟨hP3', _, _⟩ := hmc hregc hregg
        exact hP3'
      · exact Or.inl hreg
    refine le_trans (measure_mono hsub) ?_
    refine le_trans (measure_union_le _ _) ?_
    rw [hnull_region, hnull_P3, zero_add]
    exact zero_le'

/-- **The recurrence checkpoint composition** (brick 3.5e step 2 capstone): with a uniform
per-window recurrence-bad bound `δ` over invariant window-open starts, the invariant fails by
checkpoint `K·w` with probability at most `K·δ`. -/
theorem recurrence_checkpoint (T θn n : ℕ) (cc : ℝ) (w aM : ℕ) (haM : n ≤ 10 * aM)
    (δ : ℝ≥0∞)
    (hB : ∀ mc₀, recInv (L := L) (K := K) T θn n cc mc₀ →
      AllClockP3 (L := L) (K := K) (eraseConfig (L := L) (K := K) mc₀) →
      10 * rBeyond (L := L) (K := K) T (eraseConfig (L := L) (K := K) mc₀) ≤ n →
      ((markedK (L := L) (K := K) T θn) ^ w) mc₀
          {mc | (cc * (rBeyond (L := L) (K := K) T
                (eraseConfig (L := L) (K := K) mc) : ℝ) ^ 2 / (n : ℝ)
              < (cleanAbove (L := L) (K := K) T mc : ℝ)) ∧
            rBeyond (L := L) (K := K) T (eraseConfig (L := L) (K := K) mc) ≤ aM ∧
            mc.card = n ∧ AllClockP3 (L := L) (K := K) (eraseConfig (L := L) (K := K) mc)}
        ≤ δ)
    (KK : ℕ) (mc₀ : Config (MarkedAgent L K))
    (h0 : recInv (L := L) (K := K) T θn n cc mc₀) :
    ((markedK (L := L) (K := K) T θn) ^ (w * KK)) mc₀
        {mc | ¬ recInv (L := L) (K := K) T θn n cc mc} ≤ (KK : ℝ≥0∞) * δ :=
  checkpoint_composition (markedK (L := L) (K := K) T θn)
    (recInv (L := L) (K := K) T θn n cc) w δ
    (fun mc hmc => window_failure_le (L := L) (K := K) T θn n cc w aM haM δ mc hmc
      (fun hP3 hX => hB mc hmc hP3 hX))
    KK mc₀ h0

/-! ## Part 32 — the per-level recurrence (STEP 3): combine the recurrence invariant
(`cleanAbove ≤ cc·X²/n`) with the taint tail (`taintedCount ≤ tt`) through the decomposition
`rBeyond(T+1)∘erase = taintedCount + cleanAbove`. -/

/-- **A region is a.s.-preserved through kernel powers** (generic stay-in-region): if `R` is a.s.
absorbing one-step, then from a start in `R` the chain stays in `R` a.s. for every horizon. -/
theorem region_ae_pow {α : Type*} [MeasurableSpace α] [DiscreteMeasurableSpace α]
    (Kk : Kernel α α) [IsMarkovKernel Kk] (R : Set α)
    (hRstep : ∀ x ∈ R, ∀ᵐ y ∂(Kk x), y ∈ R)
    (t : ℕ) (x : α) (hxR : x ∈ R) :
    ∀ᵐ z ∂((Kk ^ t) x), z ∈ R := by
  classical
  induction t generalizing x with
  | zero =>
      simp only [pow_zero]
      change ∀ᵐ z ∂(Kernel.id x), z ∈ R
      rw [Kernel.id_apply,
        MeasureTheory.ae_dirac_iff (DiscreteMeasurableSpace.forall_measurableSet _)]
      exact hxR
  | succ t ih =>
      rw [MeasureTheory.ae_iff]
      have hbad_meas : MeasurableSet {z : α | ¬ z ∈ R} :=
        DiscreteMeasurableSpace.forall_measurableSet _
      rw [show t + 1 = 1 + t from by ring,
        Kernel.pow_add_apply_eq_lintegral Kk 1 t x hbad_meas, pow_one,
        MeasureTheory.lintegral_eq_zero_iff (Kernel.measurable_coe _ hbad_meas)]
      filter_upwards [hRstep x hxR] with y hyR
      have h := ih y hyR
      rwa [MeasureTheory.ae_iff] at h

/-- **MarkInv is a.s.-preserved one-step** (lift of `markInv_step` to the kernel). -/
theorem markInv_ae_step (T θn : ℕ) (mc : Config (MarkedAgent L K))
    (hinv : MarkInv (L := L) (K := K) T mc) :
    ∀ᵐ mc' ∂(markedK (L := L) (K := K) T θn mc), MarkInv (L := L) (K := K) T mc' :=
  ae_markedStep (L := L) (K := K) T θn mc _
    (fun mc' hsupp => markInv_step (L := L) (K := K) T θn mc mc' hinv hsupp)

/-- **MarkInv stays through kernel powers** from a MarkInv start. -/
theorem markInv_ae_pow (T θn : ℕ) (t : ℕ) (mc₀ : Config (MarkedAgent L K))
    (hinv : MarkInv (L := L) (K := K) T mc₀) :
    ∀ᵐ mc ∂((markedK (L := L) (K := K) T θn) ^ t) mc₀, MarkInv (L := L) (K := K) T mc :=
  region_ae_pow (markedK (L := L) (K := K) T θn) {mc | MarkInv (L := L) (K := K) T mc}
    (fun x hx => markInv_ae_step (L := L) (K := K) T θn x hx) t mc₀ hinv

/-- **The deterministic recurrence combine** (count form): at a checkpoint config under the mark
invariant in the P3 window, with the clean part obeying the recurrence and the taint bounded by
`tt`, the erased front: `rBeyond(T+1)∘erase ≤ cc·X²/n + tt`. -/
theorem recurrence_combine (T n : ℕ) (cc : ℝ) (tt : ℕ) (mc : Config (MarkedAgent L K))
    (hcard : mc.card = n)
    (hP3 : AllClockP3 (L := L) (K := K) (eraseConfig (L := L) (K := K) mc))
    (hinv : MarkInv (L := L) (K := K) T mc)
    (hrec : (cleanAbove (L := L) (K := K) T mc : ℝ)
      ≤ cc * (rBeyond (L := L) (K := K) T (eraseConfig (L := L) (K := K) mc) : ℝ) ^ 2 / (n : ℝ))
    (htaint : taintedCount (L := L) (K := K) mc ≤ tt) :
    (rBeyond (L := L) (K := K) (T + 1) (eraseConfig (L := L) (K := K) mc) : ℝ)
      ≤ cc * (rBeyond (L := L) (K := K) T (eraseConfig (L := L) (K := K) mc) : ℝ) ^ 2 / (n : ℝ)
        + (tt : ℝ) := by
  have hdecomp : rBeyond (L := L) (K := K) (T + 1) (eraseConfig (L := L) (K := K) mc)
      = taintedCount (L := L) (K := K) mc + cleanAbove (L := L) (K := K) T mc := by
    rw [rBeyond_erase_eq_aboveCount (L := L) (K := K) T mc hP3,
      aboveCount_eq_tainted_add_clean (L := L) (K := K) T mc hinv]
  rw [hdecomp]
  push_cast
  have htaint' : (taintedCount (L := L) (K := K) mc : ℝ) ≤ (tt : ℝ) := by exact_mod_cast htaint
  linarith

/-- **The count-form per-level recurrence**: under the recurrence-combine hypotheses plus the
negligibility `cc·X²/n + tt ≤ X²/n` (the `d`-term small at window scales), the erased front squares
in count form: `rBeyond(T+1)·n ≤ X²` (i.e. `frac(T+1) ≤ (frac T)²` on `card = n`). -/
theorem front_squares_count (T n : ℕ) (hn : 0 < n) (cc : ℝ) (tt : ℕ)
    (mc : Config (MarkedAgent L K))
    (hcard : mc.card = n)
    (hP3 : AllClockP3 (L := L) (K := K) (eraseConfig (L := L) (K := K) mc))
    (hinv : MarkInv (L := L) (K := K) T mc)
    (hrec : (cleanAbove (L := L) (K := K) T mc : ℝ)
      ≤ cc * (rBeyond (L := L) (K := K) T (eraseConfig (L := L) (K := K) mc) : ℝ) ^ 2 / (n : ℝ))
    (htaint : taintedCount (L := L) (K := K) mc ≤ tt)
    (hneg : cc * (rBeyond (L := L) (K := K) T (eraseConfig (L := L) (K := K) mc) : ℝ) ^ 2 / (n : ℝ)
        + (tt : ℝ)
      ≤ (rBeyond (L := L) (K := K) T (eraseConfig (L := L) (K := K) mc) : ℝ) ^ 2 / (n : ℝ)) :
    (rBeyond (L := L) (K := K) (T + 1) (eraseConfig (L := L) (K := K) mc) : ℝ) * (n : ℝ)
      ≤ (rBeyond (L := L) (K := K) T (eraseConfig (L := L) (K := K) mc) : ℝ) ^ 2 := by
  have hnℝ : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hcomb := recurrence_combine (L := L) (K := K) T n cc tt mc hcard hP3 hinv hrec htaint
  have hX1 : (rBeyond (L := L) (K := K) (T + 1) (eraseConfig (L := L) (K := K) mc) : ℝ)
      ≤ (rBeyond (L := L) (K := K) T (eraseConfig (L := L) (K := K) mc) : ℝ) ^ 2 / (n : ℝ) :=
    le_trans hcomb hneg
  rw [le_div_iff₀ hnℝ] at hX1
  linarith

/-! ## Part 33 — the probabilistic per-level recurrence (STEP 3 capstone): the front squares whp
at a checkpoint.  The bad event (in the recurrence window, the front does NOT square) is covered by
`{¬recInv} ∪ {taintedCount ≥ tt+1} ∪ {¬MarkInv}` — the recurrence-checkpoint failure, the taint
tail, and the (null, from a clean start) mark-invariant failure. -/

/-- **The deterministic bad-event cover**: if at config `mc` we are in the recurrence window
(`card = n ∧ P3 ∧ 10X ≤ n`), the negligibility holds, yet the front does NOT square, then `recInv`
fails, or the taint exceeds `tt`, or the mark invariant fails. -/
theorem front_bad_subset (T θn n : ℕ) (hn : 0 < n) (cc : ℝ) (tt : ℕ)
    (mc : Config (MarkedAgent L K))
    (hwin : mc.card = n ∧ AllClockP3 (L := L) (K := K) (eraseConfig (L := L) (K := K) mc) ∧
      10 * rBeyond (L := L) (K := K) T (eraseConfig (L := L) (K := K) mc) ≤ n ∧
      cc * (rBeyond (L := L) (K := K) T (eraseConfig (L := L) (K := K) mc) : ℝ) ^ 2 / (n : ℝ)
          + (tt : ℝ)
        ≤ (rBeyond (L := L) (K := K) T (eraseConfig (L := L) (K := K) mc) : ℝ) ^ 2 / (n : ℝ))
    (hns : ¬ ((rBeyond (L := L) (K := K) (T + 1) (eraseConfig (L := L) (K := K) mc) : ℝ) * (n : ℝ)
      ≤ (rBeyond (L := L) (K := K) T (eraseConfig (L := L) (K := K) mc) : ℝ) ^ 2)) :
    ¬ recInv (L := L) (K := K) T θn n cc mc ∨ tt + 1 ≤ taintedCount (L := L) (K := K) mc ∨
      ¬ MarkInv (L := L) (K := K) T mc := by
  classical
  obtain ⟨hcard, hP3, hX, hneg⟩ := hwin
  by_contra hcon
  push Not at hcon
  obtain ⟨hrec, htaint, hinv⟩ := hcon
  -- recInv + window ⟹ clean ≤ cc·X²/n.
  obtain ⟨_, _, himpl⟩ := hrec
  obtain ⟨_, hclean⟩ := himpl hP3 hX
  have htaint' : taintedCount (L := L) (K := K) mc ≤ tt := by omega
  exact hns (front_squares_count (L := L) (K := K) T n hn cc tt mc hcard hP3 hinv
    hclean htaint' hneg)

/-- **STEP 3 capstone — the per-level recurrence whp at a checkpoint.**  From a `recInv` ∧ `MarkInv`
start, at horizon `t = w·KK`, the probability that the level is in the recurrence window yet the
front fails to square is at most the recurrence-checkpoint failure `KK·δ` plus the taint tail.  The
mark-invariant failure mode is null (a.s.-preserved from the start). -/
theorem front_squares_whp (T θn n : ℕ) (hn : 2 ≤ n) (cc : ℝ) (w aM : ℕ) (haM : n ≤ 10 * aM)
    (δ : ℝ≥0∞)
    (hB : ∀ mc₀, recInv (L := L) (K := K) T θn n cc mc₀ →
      AllClockP3 (L := L) (K := K) (eraseConfig (L := L) (K := K) mc₀) →
      10 * rBeyond (L := L) (K := K) T (eraseConfig (L := L) (K := K) mc₀) ≤ n →
      ((markedK (L := L) (K := K) T θn) ^ w) mc₀
          {mc | (cc * (rBeyond (L := L) (K := K) T
                (eraseConfig (L := L) (K := K) mc) : ℝ) ^ 2 / (n : ℝ)
              < (cleanAbove (L := L) (K := K) T mc : ℝ)) ∧
            rBeyond (L := L) (K := K) T (eraseConfig (L := L) (K := K) mc) ≤ aM ∧
            mc.card = n ∧ AllClockP3 (L := L) (K := K) (eraseConfig (L := L) (K := K) mc)}
        ≤ δ)
    (σ : ℝ) (hσ : 0 < σ) (KK : ℕ)
    (hsmall : σ * (1 + 4 / (n : ℝ)) ^ (w * KK) ≤ 1 / 2)
    (tt : ℕ)
    (mc₀ : Config (MarkedAgent L K))
    (h0 : recInv (L := L) (K := K) T θn n cc mc₀)
    (hmark : MarkInv (L := L) (K := K) T mc₀) :
    ((markedK (L := L) (K := K) T θn) ^ (w * KK)) mc₀
        {mc | (mc.card = n ∧
            AllClockP3 (L := L) (K := K) (eraseConfig (L := L) (K := K) mc) ∧
            10 * rBeyond (L := L) (K := K) T (eraseConfig (L := L) (K := K) mc) ≤ n ∧
            cc * (rBeyond (L := L) (K := K) T (eraseConfig (L := L) (K := K) mc) : ℝ) ^ 2 / (n : ℝ)
                + (tt : ℝ)
              ≤ (rBeyond (L := L) (K := K) T (eraseConfig (L := L) (K := K) mc) : ℝ) ^ 2 / (n : ℝ))
          ∧ ¬ ((rBeyond (L := L) (K := K) (T + 1) (eraseConfig (L := L) (K := K) mc) : ℝ) * (n : ℝ)
            ≤ (rBeyond (L := L) (K := K) T (eraseConfig (L := L) (K := K) mc) : ℝ) ^ 2)}
      ≤ (KK : ℝ≥0∞) * δ
        + ((GatedDrift.killK (markedK (L := L) (K := K) T θn)
            (taintedGate (L := L) (K := K) n) ^ (w * KK)) (some mc₀) {none}
          + ENNReal.ofReal
            (Real.exp (σ * (1 + 4 / (n : ℝ)) ^ (w * KK)
                * (taintedCount (L := L) (K := K) mc₀ : ℝ)
              + 2 * σ * (1 + 4 / (n : ℝ)) ^ (w * KK) * ((θn : ℝ) / (n : ℝ)) ^ 2 * ((w * KK : ℕ) : ℝ)
              - σ * ((tt + 1 : ℕ) : ℝ)))) := by
  classical
  -- the bad event is covered by {¬recInv} ∪ {taint ≥ tt+1} ∪ {¬MarkInv}.
  set bad : Set (Config (MarkedAgent L K)) :=
    {mc | (mc.card = n ∧
        AllClockP3 (L := L) (K := K) (eraseConfig (L := L) (K := K) mc) ∧
        10 * rBeyond (L := L) (K := K) T (eraseConfig (L := L) (K := K) mc) ≤ n ∧
        cc * (rBeyond (L := L) (K := K) T (eraseConfig (L := L) (K := K) mc) : ℝ) ^ 2 / (n : ℝ)
            + (tt : ℝ)
          ≤ (rBeyond (L := L) (K := K) T (eraseConfig (L := L) (K := K) mc) : ℝ) ^ 2 / (n : ℝ))
      ∧ ¬ ((rBeyond (L := L) (K := K) (T + 1) (eraseConfig (L := L) (K := K) mc) : ℝ) * (n : ℝ)
        ≤ (rBeyond (L := L) (K := K) T (eraseConfig (L := L) (K := K) mc) : ℝ) ^ 2)}
    with hbad
  have hsub : bad ⊆ {mc | ¬ recInv (L := L) (K := K) T θn n cc mc} ∪
      ({mc | tt + 1 ≤ taintedCount (L := L) (K := K) mc} ∪
        {mc | ¬ MarkInv (L := L) (K := K) T mc}) := by
    intro mc hmc
    rw [hbad, Set.mem_setOf_eq] at hmc
    obtain ⟨hwin, hns⟩ := hmc
    rcases front_bad_subset (L := L) (K := K) T θn n (by omega) cc tt mc hwin hns with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  refine le_trans (measure_mono hsub) ?_
  refine le_trans (measure_union_le _ _) ?_
  refine add_le_add ?_ ?_
  · -- the recurrence-checkpoint failure ≤ KK·δ.
    exact recurrence_checkpoint (L := L) (K := K) T θn n cc w aM haM δ hB KK mc₀ h0
  · refine le_trans (measure_union_le _ _) ?_
    -- the MarkInv-failure mass is 0 (null), so the union ≤ taint tail + 0.
    have hmarknull : ((markedK (L := L) (K := K) T θn) ^ (w * KK)) mc₀
        {mc | ¬ MarkInv (L := L) (K := K) T mc} = 0 := by
      have h := markInv_ae_pow (L := L) (K := K) T θn (w * KK) mc₀ hmark
      rwa [MeasureTheory.ae_iff] at h
    rw [hmarknull, add_zero]
    exact tainted_marked_tail_explicit (L := L) (K := K) T θn n hn σ hσ (w * KK)
      hsmall mc₀ (tt + 1)

/-! ## Part 34 — the real-kernel transfer and the level union (STEP 4).

`front_squares_whp` bounds a MARKED-world probability whose EVENT depends only on the erased config
(`card`, `AllClockP3`, `rBeyond` are all functions of `erase mc`).  So the bad event is exactly the
`erase`-preimage of a real-config set, and `markedK_pow_erase` transfers it to the REAL kernel
verbatim.  Then a union over the levels `T < capMinute` yields the run-long windowed recurrence
failure on the real kernel. -/

/-- The real-config per-level bad set (in the recurrence window, the front fails to square). -/
def realFrontBad (T n : ℕ) (cc : ℝ) (tt : ℕ) : Set (Config (AgentState L K)) :=
  {c | (c.card = n ∧ AllClockP3 (L := L) (K := K) c ∧
      10 * rBeyond (L := L) (K := K) T c ≤ n ∧
      cc * (rBeyond (L := L) (K := K) T c : ℝ) ^ 2 / (n : ℝ) + (tt : ℝ)
        ≤ (rBeyond (L := L) (K := K) T c : ℝ) ^ 2 / (n : ℝ))
    ∧ ¬ ((rBeyond (L := L) (K := K) (T + 1) c : ℝ) * (n : ℝ)
      ≤ (rBeyond (L := L) (K := K) T c : ℝ) ^ 2)}

/-- The marked bad event of `front_squares_whp` is the `erase`-preimage of `realFrontBad`. -/
theorem markedFrontBad_eq_preimage (T n : ℕ) (cc : ℝ) (tt : ℕ) :
    {mc : Config (MarkedAgent L K) | (mc.card = n ∧
        AllClockP3 (L := L) (K := K) (eraseConfig (L := L) (K := K) mc) ∧
        10 * rBeyond (L := L) (K := K) T (eraseConfig (L := L) (K := K) mc) ≤ n ∧
        cc * (rBeyond (L := L) (K := K) T (eraseConfig (L := L) (K := K) mc) : ℝ) ^ 2 / (n : ℝ)
            + (tt : ℝ)
          ≤ (rBeyond (L := L) (K := K) T (eraseConfig (L := L) (K := K) mc) : ℝ) ^ 2 / (n : ℝ))
      ∧ ¬ ((rBeyond (L := L) (K := K) (T + 1) (eraseConfig (L := L) (K := K) mc) : ℝ) * (n : ℝ)
        ≤ (rBeyond (L := L) (K := K) T (eraseConfig (L := L) (K := K) mc) : ℝ) ^ 2)}
      = eraseConfig (L := L) (K := K) ⁻¹' realFrontBad (L := L) (K := K) T n cc tt := by
  ext mc
  simp only [realFrontBad, Set.mem_preimage, Set.mem_setOf_eq, eraseConfig_card]

/-- **STEP 4 — the real-kernel per-level transfer.**  The real kernel's probability of the per-level
recurrence failure (in the window) is bounded by `KK·δ` plus the (marked-world) hour-escape and
taint tail.  Via `markedK_pow_erase`, the bound on the marked world transfers verbatim, since the
event is erase-measurable. -/
theorem real_front_squares_whp (T θn n : ℕ) (hn : 2 ≤ n) (cc : ℝ) (w aM : ℕ) (haM : n ≤ 10 * aM)
    (δ : ℝ≥0∞)
    (hB : ∀ mc₀, recInv (L := L) (K := K) T θn n cc mc₀ →
      AllClockP3 (L := L) (K := K) (eraseConfig (L := L) (K := K) mc₀) →
      10 * rBeyond (L := L) (K := K) T (eraseConfig (L := L) (K := K) mc₀) ≤ n →
      ((markedK (L := L) (K := K) T θn) ^ w) mc₀
          {mc | (cc * (rBeyond (L := L) (K := K) T
                (eraseConfig (L := L) (K := K) mc) : ℝ) ^ 2 / (n : ℝ)
              < (cleanAbove (L := L) (K := K) T mc : ℝ)) ∧
            rBeyond (L := L) (K := K) T (eraseConfig (L := L) (K := K) mc) ≤ aM ∧
            mc.card = n ∧ AllClockP3 (L := L) (K := K) (eraseConfig (L := L) (K := K) mc)}
        ≤ δ)
    (σ : ℝ) (hσ : 0 < σ) (KK : ℕ)
    (hsmall : σ * (1 + 4 / (n : ℝ)) ^ (w * KK) ≤ 1 / 2)
    (tt : ℕ)
    (mc₀ : Config (MarkedAgent L K))
    (h0 : recInv (L := L) (K := K) T θn n cc mc₀)
    (hmark : MarkInv (L := L) (K := K) T mc₀) :
    ((NonuniformMajority L K).transitionKernel ^ (w * KK))
        (eraseConfig (L := L) (K := K) mc₀)
        (realFrontBad (L := L) (K := K) T n cc tt)
      ≤ (KK : ℝ≥0∞) * δ
        + ((GatedDrift.killK (markedK (L := L) (K := K) T θn)
            (taintedGate (L := L) (K := K) n) ^ (w * KK)) (some mc₀) {none}
          + ENNReal.ofReal
            (Real.exp (σ * (1 + 4 / (n : ℝ)) ^ (w * KK)
                * (taintedCount (L := L) (K := K) mc₀ : ℝ)
              + 2 * σ * (1 + 4 / (n : ℝ)) ^ (w * KK) * ((θn : ℝ) / (n : ℝ)) ^ 2 * ((w * KK : ℕ) : ℝ)
              - σ * ((tt + 1 : ℕ) : ℝ)))) := by
  rw [← markedK_pow_erase (L := L) (K := K) T θn (w * KK) mc₀
    (realFrontBad (L := L) (K := K) T n cc tt),
    ← markedFrontBad_eq_preimage (L := L) (K := K) T n cc tt]
  exact front_squares_whp (L := L) (K := K) T θn n hn cc w aM haM δ hB σ hσ KK hsmall tt
    mc₀ h0 hmark

/-! ## Part 35 — the level union (STEP 4 continued): union the per-level real-kernel failure over
`T < capMinute`.  The complement of the union is the windowed recurrence holding at every level in
the window, run-long. -/

/-- **The union over levels** of the real per-level recurrence failure.  With a start that is
`recInv T` ∧ `MarkInv T` for every level `T` (e.g. the all-clean, all-window-open initial config),
and the per-level checkpoint inputs, the real-kernel probability that SOME level `< Tcap` is in its
recurrence window yet fails to square is at most the sum of the per-level bounds. -/
theorem real_front_union (θn n : ℕ) (hn : 2 ≤ n) (cc : ℝ) (w : ℕ)
    (aM : ℕ → ℕ) (haM : ∀ T, n ≤ 10 * aM T)
    (δ : ℕ → ℝ≥0∞)
    (hB : ∀ T, ∀ mc₀, recInv (L := L) (K := K) T θn n cc mc₀ →
      AllClockP3 (L := L) (K := K) (eraseConfig (L := L) (K := K) mc₀) →
      10 * rBeyond (L := L) (K := K) T (eraseConfig (L := L) (K := K) mc₀) ≤ n →
      ((markedK (L := L) (K := K) T θn) ^ w) mc₀
          {mc | (cc * (rBeyond (L := L) (K := K) T
                (eraseConfig (L := L) (K := K) mc) : ℝ) ^ 2 / (n : ℝ)
              < (cleanAbove (L := L) (K := K) T mc : ℝ)) ∧
            rBeyond (L := L) (K := K) T (eraseConfig (L := L) (K := K) mc) ≤ aM T ∧
            mc.card = n ∧ AllClockP3 (L := L) (K := K) (eraseConfig (L := L) (K := K) mc)}
        ≤ δ T)
    (σ : ℝ) (hσ : 0 < σ) (KK : ℕ)
    (hsmall : σ * (1 + 4 / (n : ℝ)) ^ (w * KK) ≤ 1 / 2)
    (tt : ℕ) (Tcap : ℕ)
    (mc₀ : Config (MarkedAgent L K))
    (h0 : ∀ T < Tcap, recInv (L := L) (K := K) T θn n cc mc₀)
    (hmark : ∀ T < Tcap, MarkInv (L := L) (K := K) T mc₀) :
    ∀ T₀, T₀ = w * KK →
    ((NonuniformMajority L K).transitionKernel ^ T₀) (eraseConfig (L := L) (K := K) mc₀)
        (⋃ T ∈ Finset.range Tcap, realFrontBad (L := L) (K := K) T n cc tt)
      ≤ ∑ T ∈ Finset.range Tcap,
          ((KK : ℝ≥0∞) * δ T
            + ((GatedDrift.killK (markedK (L := L) (K := K) T θn)
                (taintedGate (L := L) (K := K) n) ^ (w * KK)) (some mc₀) {none}
              + ENNReal.ofReal
                (Real.exp (σ * (1 + 4 / (n : ℝ)) ^ (w * KK)
                    * (taintedCount (L := L) (K := K) mc₀ : ℝ)
                  + 2 * σ * (1 + 4 / (n : ℝ)) ^ (w * KK) * ((θn : ℝ) / (n : ℝ)) ^ 2
                      * ((w * KK : ℕ) : ℝ)
                  - σ * ((tt + 1 : ℕ) : ℝ))))) := by
  intro T₀ hT₀
  subst hT₀
  refine le_trans (measure_biUnion_finset_le _ _) ?_
  apply Finset.sum_le_sum
  intro T hT
  rw [Finset.mem_range] at hT
  exact real_front_squares_whp (L := L) (K := K) T θn n hn cc w (aM T) (haM T) (δ T)
    (hB T) σ hσ KK hsmall tt mc₀ (h0 T hT) (hmark T hT)

/-! ## Part 36 — the `WindowedFrontProfile` bridge (STEP 4 deliverable): the complement of the
level union is the windowed recurrence (Doty Thm 6.5's windowed shape) on the real config. -/

open ClockFrontProfile in
/-- **The deterministic bridge**: if a real config `c` has full population, all clocks at phase 3,
and avoids `realFrontBad T` for every level `T < Tcap` where `Tcap` exceeds the cap minute, and the
negligibility `cc·X²/n + tt ≤ X²/n` holds whenever the floor `θ ≤ frac T` is met, then `c` satisfies
`WindowedFrontProfile θ` (the front squares on the recurrence window `[θ, 1/10]`).  The floor `θ`
must be positive so the trivial levels (`frac = 0` past the cap) are out of the window. -/
theorem windowedFrontProfile_of_not_bad (n Tcap : ℕ) (hn : 0 < n) (cc : ℝ) (tt : ℕ) (θ : ℝ)
    (hθpos : 0 < θ)
    (c : Config (AgentState L K)) (hcard : c.card = n)
    (hP3 : AllClockP3 (L := L) (K := K) c)
    (hcap : ClockFrontShape.capMinute (L := L) (K := K) < Tcap)
    (hneg : ∀ T, θ ≤ ClockFrontProfile.frac (L := L) (K := K) T c →
      cc * (rBeyond (L := L) (K := K) T c : ℝ) ^ 2 / (n : ℝ) + (tt : ℝ)
        ≤ (rBeyond (L := L) (K := K) T c : ℝ) ^ 2 / (n : ℝ))
    (hnotbad : ∀ T < Tcap, c ∉ realFrontBad (L := L) (K := K) T n cc tt) :
    WindowedFrontProfile (L := L) (K := K) θ c := by
  have hnℝ : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hcardℝ : (0 : ℝ) < (c.card : ℝ) := by rw [hcard]; exact hnℝ
  intro T hθT hupper
  -- `frac T ≤ 1/10` ⟺ `10·rBeyond T ≤ card = n`.
  have hwin10 : 10 * rBeyond (L := L) (K := K) T c ≤ n := by
    unfold ClockFrontProfile.frac at hupper
    rw [div_le_iff₀ hcardℝ] at hupper
    have : (rBeyond (L := L) (K := K) T c : ℝ) * 10 ≤ (c.card : ℝ) := by linarith
    rw [hcard] at this
    have h10 : (10 * rBeyond (L := L) (K := K) T c : ℝ) ≤ (n : ℝ) := by push_cast; linarith
    exact_mod_cast h10
  -- T must be < Tcap: else frac T = 0 < θ contradicts hθT.
  have hTlt : T < Tcap := by
    by_contra hge
    push Not at hge
    by_cases hTcapeq : T ≤ ClockFrontShape.capMinute (L := L) (K := K)
    · omega
    · push Not at hTcapeq
      have hz := ClimbTail.rBeyond_eq_zero_of_cap_lt (L := L) (K := K) T hTcapeq c
      have : ClockFrontProfile.frac (L := L) (K := K) T c = 0 := by
        unfold ClockFrontProfile.frac; rw [hz]; simp
      rw [this] at hθT; linarith
  -- the level is in the window and (by hnotbad) avoids realFrontBad ⟹ the front squares.
  have hnb := hnotbad T hTlt
  rw [realFrontBad, Set.mem_setOf_eq] at hnb
  push Not at hnb
  have hneg' := hneg T hθT
  have hsq := hnb ⟨hcard, hP3, hwin10, hneg'⟩
  -- `rBeyond(T+1)·n ≤ X²` ⟹ `frac(T+1) ≤ (frac T)²`, both sides over `card = n`.
  have hX1nn : (0 : ℝ) ≤ (rBeyond (L := L) (K := K) (T + 1) c : ℝ) := by positivity
  have hkey : (rBeyond (L := L) (K := K) (T + 1) c : ℝ) / (c.card : ℝ)
      ≤ ((rBeyond (L := L) (K := K) T c : ℝ) / (c.card : ℝ)) ^ 2 := by
    rw [div_pow, div_le_div_iff₀ hcardℝ (by positivity)]
    have hcsq : (c.card : ℝ) ^ 2 = (n : ℝ) * (c.card : ℝ) := by rw [hcard]; ring
    rw [hcsq]
    nlinarith [hsq, hcardℝ, hnℝ, hX1nn]
  exact hkey

/-! ## Part 37 — the whp `WindowedFrontProfile` (STEP 4 capstone): assemble `real_front_union`
(union probability ≤ per-level sum) with `windowedFrontProfile_of_not_bad` (the union complement ⟹
the windowed recurrence).  The final statement bounds, on the REAL kernel, the probability that the
end config is in the hour region with the negligibility holding yet FAILS the windowed recurrence,
by the sum of the per-level tails. -/

open ClockFrontProfile in
/-- **STEP 4 CAPSTONE — whp WindowedFrontProfile on the real kernel.**  From an all-levels-clean,
all-window-open start (the per-level `recInv`/`MarkInv` hypotheses) and the per-level checkpoint
inputs, the real-kernel probability that the end config is a full-population all-phase-3 clock config
on which the negligibility holds at every floor-met level yet the windowed front recurrence
`WindowedFrontProfile θ` FAILS, is at most the sum of the per-level recurrence tails.  (The region
and negligibility are carried as properties of the END config; their own whp control is the bulk
epidemic / scale plug-in, supplied separately.) -/
theorem windowedFrontProfile_whp (θn n : ℕ) (hn : 2 ≤ n) (cc : ℝ) (w : ℕ) (θ : ℝ) (hθpos : 0 < θ)
    (aM : ℕ → ℕ) (haM : ∀ T, n ≤ 10 * aM T)
    (δ : ℕ → ℝ≥0∞)
    (hB : ∀ T, ∀ mc₀, recInv (L := L) (K := K) T θn n cc mc₀ →
      AllClockP3 (L := L) (K := K) (eraseConfig (L := L) (K := K) mc₀) →
      10 * rBeyond (L := L) (K := K) T (eraseConfig (L := L) (K := K) mc₀) ≤ n →
      ((markedK (L := L) (K := K) T θn) ^ w) mc₀
          {mc | (cc * (rBeyond (L := L) (K := K) T
                (eraseConfig (L := L) (K := K) mc) : ℝ) ^ 2 / (n : ℝ)
              < (cleanAbove (L := L) (K := K) T mc : ℝ)) ∧
            rBeyond (L := L) (K := K) T (eraseConfig (L := L) (K := K) mc) ≤ aM T ∧
            mc.card = n ∧ AllClockP3 (L := L) (K := K) (eraseConfig (L := L) (K := K) mc)}
        ≤ δ T)
    (σ : ℝ) (hσ : 0 < σ) (KK : ℕ)
    (hsmall : σ * (1 + 4 / (n : ℝ)) ^ (w * KK) ≤ 1 / 2)
    (tt : ℕ) (Tcap : ℕ) (hcap : ClockFrontShape.capMinute (L := L) (K := K) < Tcap)
    (mc₀ : Config (MarkedAgent L K))
    (h0 : ∀ T < Tcap, recInv (L := L) (K := K) T θn n cc mc₀)
    (hmark : ∀ T < Tcap, MarkInv (L := L) (K := K) T mc₀) :
    ((NonuniformMajority L K).transitionKernel ^ (w * KK)) (eraseConfig (L := L) (K := K) mc₀)
        {c | (c.card = n ∧ AllClockP3 (L := L) (K := K) c ∧
            (∀ T, θ ≤ ClockFrontProfile.frac (L := L) (K := K) T c →
              cc * (rBeyond (L := L) (K := K) T c : ℝ) ^ 2 / (n : ℝ) + (tt : ℝ)
                ≤ (rBeyond (L := L) (K := K) T c : ℝ) ^ 2 / (n : ℝ)))
          ∧ ¬ WindowedFrontProfile (L := L) (K := K) θ c}
      ≤ ∑ T ∈ Finset.range Tcap,
          ((KK : ℝ≥0∞) * δ T
            + ((GatedDrift.killK (markedK (L := L) (K := K) T θn)
                (taintedGate (L := L) (K := K) n) ^ (w * KK)) (some mc₀) {none}
              + ENNReal.ofReal
                (Real.exp (σ * (1 + 4 / (n : ℝ)) ^ (w * KK)
                    * (taintedCount (L := L) (K := K) mc₀ : ℝ)
                  + 2 * σ * (1 + 4 / (n : ℝ)) ^ (w * KK) * ((θn : ℝ) / (n : ℝ)) ^ 2
                      * ((w * KK : ℕ) : ℝ)
                  - σ * ((tt + 1 : ℕ) : ℝ))))) := by
  classical
  -- the failure event ⊆ the level union (via the deterministic bridge contrapositive).
  have hsub : {c : Config (AgentState L K) | (c.card = n ∧ AllClockP3 (L := L) (K := K) c ∧
        (∀ T, θ ≤ ClockFrontProfile.frac (L := L) (K := K) T c →
          cc * (rBeyond (L := L) (K := K) T c : ℝ) ^ 2 / (n : ℝ) + (tt : ℝ)
            ≤ (rBeyond (L := L) (K := K) T c : ℝ) ^ 2 / (n : ℝ)))
      ∧ ¬ WindowedFrontProfile (L := L) (K := K) θ c}
      ⊆ ⋃ T ∈ Finset.range Tcap, realFrontBad (L := L) (K := K) T n cc tt := by
    intro c hc
    obtain ⟨⟨hcard, hP3, hnegc⟩, hwfp⟩ := hc
    -- if c avoided every realFrontBad, the bridge gives WindowedFrontProfile — contradiction.
    by_contra hcon
    apply hwfp
    refine windowedFrontProfile_of_not_bad (L := L) (K := K) n Tcap (by omega) cc tt θ hθpos
      c hcard hP3 hcap hnegc ?_
    intro T hT hbad
    apply hcon
    rw [Set.mem_iUnion₂]
    exact ⟨T, Finset.mem_range.mpr hT, hbad⟩
  refine le_trans (measure_mono hsub) ?_
  exact real_front_union (L := L) (K := K) θn n hn cc w aM haM δ hB σ hσ KK hsmall tt Tcap
    mc₀ h0 hmark (w * KK) rfl

/-! ## Part 38 — the initial-config start hypotheses (STEP 3, item 3): the all-clean,
all-window-open start satisfies `MarkInv` and `recInv` at every level.

The Doty start is the all-clean marked configuration (every agent's mark `= false`), with the
clocks not yet in the recurrence window.  `MarkInv` is then vacuous (no tainted agent), and `recInv`
holds either at the floor (`θn ≤ X` with the recurrence) or — the genuine start — because the
recurrence window `P3 ∧ 10X ≤ n` is not yet open.  These structural dischargers supply the
per-level `h0`/`hmark` inputs of `windowedFrontProfile_whp` for any concrete start config. -/

/-- **The mark invariant holds at any all-clean config**: if every agent's mark is `false`, there
are no tainted agents, so `MarkInv T` holds vacuously at every level `T`. -/
theorem markInv_of_clean (T : ℕ) (mc : Config (MarkedAgent L K))
    (hclean : ∀ m ∈ mc, m.2 = false) :
    MarkInv (L := L) (K := K) T mc := by
  intro m hm htrue
  have := hclean m hm
  simp [this] at htrue

/-- **`taintedCount = 0` at an all-clean config.** -/
theorem taintedCount_of_clean (mc : Config (MarkedAgent L K))
    (hclean : ∀ m ∈ mc, m.2 = false) :
    taintedCount (L := L) (K := K) mc = 0 := by
  unfold taintedCount
  rw [Multiset.countP_eq_zero]
  intro m hm
  rw [hclean m hm]
  simp

/-- **`recInv` at a window-closed start** (the genuine Doty start): inside the hour region, if the
recurrence window is not open — either the config is not all-phase-3 or the feeder already passed
`n/10` — then `recInv T` holds vacuously (the recurrence claim is conditioned on the open window). -/
theorem recInv_of_window_closed (T θn n : ℕ) (cc : ℝ) (mc : Config (MarkedAgent L K))
    (hcard : mc.card = n)
    (hge3 : AllClockGE3 (L := L) (K := K) (eraseConfig (L := L) (K := K) mc))
    (hclosed : ¬ AllClockP3 (L := L) (K := K) (eraseConfig (L := L) (K := K) mc) ∨
      ¬ (10 * rBeyond (L := L) (K := K) T (eraseConfig (L := L) (K := K) mc) ≤ n)) :
    recInv (L := L) (K := K) T θn n cc mc := by
  refine ⟨hcard, hge3, ?_⟩
  intro hP3 hX
  rcases hclosed with h | h
  · exact absurd hP3 h
  · exact absurd hX h

/-- **`recInv` at the floor**: inside the hour region, if the feeder is past the floor (`θn ≤ X`)
and the clean tail obeys the recurrence, `recInv T` holds. -/
theorem recInv_of_floor (T θn n : ℕ) (cc : ℝ) (mc : Config (MarkedAgent L K))
    (hcard : mc.card = n)
    (hge3 : AllClockGE3 (L := L) (K := K) (eraseConfig (L := L) (K := K) mc))
    (hθ : θn ≤ rBeyond (L := L) (K := K) T (eraseConfig (L := L) (K := K) mc))
    (hrec : (cleanAbove (L := L) (K := K) T mc : ℝ) ≤
      cc * (rBeyond (L := L) (K := K) T (eraseConfig (L := L) (K := K) mc) : ℝ) ^ 2 / (n : ℝ)) :
    recInv (L := L) (K := K) T θn n cc mc := by
  exact ⟨hcard, hge3, fun _ _ => ⟨hθ, hrec⟩⟩

/-! ## Part 39 — the negligibility step (item 2): `cc·X²/n + tt ≤ X²/n` at window scales.

The `d`-term `tt` (the tainted tail, `n^{0.15}` whp) is negligible against the recurrence slack
`(1−cc)·X²/n`: with `cc < 1` and the feeder past the floor (`θn ≤ X`), the slack is at least
`(1−cc)·(θn)²/n`, which dominates `tt` once the scale hypothesis `tt·n ≤ (1−cc)·(θn)²` holds.
At the paper scales (`θ = n^{-0.4}`, `tt = n^{0.15}`, `cc = 9/10`): `(1−cc)(θn)² = n^{1.2}/10 ≫
n^{1.15} = tt·n`.  Pure scale arithmetic; the multiplicative scale fact is carried as a hypothesis. -/

/-- **The negligibility inequality** (generic, real-valued): from `0 ≤ cc ≤ 1`, `0 < n`, the feeder
floor `θn ≤ X`, and the scale fact `tt·n ≤ (1−cc)·(θn)²`, the `d`-term is absorbed:
`cc·X²/n + tt ≤ X²/n`.  This is exactly `windowedFrontProfile_of_not_bad`'s `hneg` per level. -/
theorem negligibility_le (n : ℕ) (hn : 0 < n) (cc : ℝ) (hcc1 : cc ≤ 1)
    (θn : ℕ) (X : ℕ) (tt : ℕ) (hθ : θn ≤ X)
    (hscale : (tt : ℝ) * (n : ℝ) ≤ (1 - cc) * (θn : ℝ) ^ 2) :
    cc * (X : ℝ) ^ 2 / (n : ℝ) + (tt : ℝ) ≤ (X : ℝ) ^ 2 / (n : ℝ) := by
  have hnℝ : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hθX : (θn : ℝ) ≤ (X : ℝ) := by exact_mod_cast hθ
  have hθ0 : (0 : ℝ) ≤ (θn : ℝ) := by positivity
  -- (1−cc)·(θn)² ≤ (1−cc)·X²  (monotone in the squared feeder).
  have hsq : (θn : ℝ) ^ 2 ≤ (X : ℝ) ^ 2 := by nlinarith [hθX, hθ0]
  have hslack : (tt : ℝ) * (n : ℝ) ≤ (1 - cc) * (X : ℝ) ^ 2 := by
    refine le_trans hscale ?_
    have h1cc : (0 : ℝ) ≤ 1 - cc := by linarith
    exact mul_le_mul_of_nonneg_left hsq h1cc
  -- divide by n: tt ≤ (1−cc)·X²/n, i.e. cc·X²/n + tt ≤ X²/n.
  rw [div_add' _ _ _ (ne_of_gt hnℝ), div_le_div_iff_of_pos_right hnℝ]
  nlinarith [hslack]

/-! ## Part 40 — the tail-sum smallness packaging (item 4): the `windowedFrontProfile_whp` RHS
collapses to `Tcap · (uniform per-level tail)`.

`windowedFrontProfile_whp`'s RHS is `Σ_{T<Tcap} (KK·δ T + escape_T + tail_T)`.  Under the locked-
constant margins each summand is bounded by a single deterministic value (`δ T ≤ dB`, the hour-escape
`≤ eB`, the taint tail `≤ tB`, all uniform in `T`), so the whole sum collapses to
`Tcap · (KK·dB + eB + tB)`.  With `Tcap = O(log n)`, `KK = O(n loglog n)`, `dB = exp(−Ω(n^{0.1}))`,
`eB` = bulk-not-arrived, `tB = exp(−n^{0.15−o(1)})`, the package stays `n^{−ω(1)}`.  Pure ENNReal
monotone summation — the per-level smallness is the locked-margin input, not re-derived here. -/

/-- **The per-level uniform bound on the `windowedFrontProfile_whp` summand.**  Given uniform bounds
on the three pieces of the `T`-th term, the term is at most `KK·dB + (eB + tB)`. -/
theorem front_tail_term_le (KK : ℕ) (δT eT tT dB eB tB : ℝ≥0∞)
    (hδ : δT ≤ dB) (he : eT ≤ eB) (ht : tT ≤ tB) :
    (KK : ℝ≥0∞) * δT + (eT + tT) ≤ (KK : ℝ≥0∞) * dB + (eB + tB) := by
  exact add_le_add (mul_le_mul_left' hδ _) (add_le_add he ht)

/-- **The tail-sum packaging** (item 4): a finite sum of `Tcap` per-level terms, each of the
`windowedFrontProfile_whp` shape and uniformly bounded by `KK·dB + eB + tB`, collapses to
`Tcap · (KK·dB + eB + tB)` — a single exponential/polynomial smallness form. -/
theorem front_tail_sum_le (KK Tcap : ℕ) (δ esc tail : ℕ → ℝ≥0∞) (dB eB tB : ℝ≥0∞)
    (hδ : ∀ T < Tcap, δ T ≤ dB) (he : ∀ T < Tcap, esc T ≤ eB) (ht : ∀ T < Tcap, tail T ≤ tB) :
    ∑ T ∈ Finset.range Tcap, ((KK : ℝ≥0∞) * δ T + (esc T + tail T))
      ≤ (Tcap : ℝ≥0∞) * ((KK : ℝ≥0∞) * dB + (eB + tB)) := by
  classical
  calc ∑ T ∈ Finset.range Tcap, ((KK : ℝ≥0∞) * δ T + (esc T + tail T))
      ≤ ∑ _T ∈ Finset.range Tcap, ((KK : ℝ≥0∞) * dB + (eB + tB)) := by
        apply Finset.sum_le_sum
        intro T hT
        rw [Finset.mem_range] at hT
        exact front_tail_term_le KK (δ T) (esc T) (tail T) dB eB tB
          (hδ T hT) (he T hT) (ht T hT)
    _ = (Tcap : ℝ≥0∞) * ((KK : ℝ≥0∞) * dB + (eB + tB)) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

open ClockFrontProfile in
/-- **STEP 4 packaged — whp `WindowedFrontProfile` with a single-form tail.**  Compose
`windowedFrontProfile_whp` with the tail-sum packaging: from uniform per-level bounds `δ T ≤ dB`,
hour-escape `≤ eB`, taint-tail `≤ tB` (the locked-margin smallness inputs), the real-kernel
probability that the end config is in the hour region with the negligibility yet FAILS the windowed
front recurrence is at most the single term `Tcap · (KK·dB + eB + tB)` — an explicit
exponential/polynomial form (each factor `n^{−ω(1)}` at the paper scales). -/
theorem windowedFrontProfile_whp_packaged
    (θn n : ℕ) (hn : 2 ≤ n) (cc : ℝ) (w : ℕ) (θ : ℝ) (hθpos : 0 < θ)
    (aM : ℕ → ℕ) (haM : ∀ T, n ≤ 10 * aM T)
    (δ : ℕ → ℝ≥0∞)
    (hB : ∀ T, ∀ mc₀, recInv (L := L) (K := K) T θn n cc mc₀ →
      AllClockP3 (L := L) (K := K) (eraseConfig (L := L) (K := K) mc₀) →
      10 * rBeyond (L := L) (K := K) T (eraseConfig (L := L) (K := K) mc₀) ≤ n →
      ((markedK (L := L) (K := K) T θn) ^ w) mc₀
          {mc | (cc * (rBeyond (L := L) (K := K) T
                (eraseConfig (L := L) (K := K) mc) : ℝ) ^ 2 / (n : ℝ)
              < (cleanAbove (L := L) (K := K) T mc : ℝ)) ∧
            rBeyond (L := L) (K := K) T (eraseConfig (L := L) (K := K) mc) ≤ aM T ∧
            mc.card = n ∧ AllClockP3 (L := L) (K := K) (eraseConfig (L := L) (K := K) mc)}
        ≤ δ T)
    (σ : ℝ) (hσ : 0 < σ) (KK : ℕ)
    (hsmall : σ * (1 + 4 / (n : ℝ)) ^ (w * KK) ≤ 1 / 2)
    (tt : ℕ) (Tcap : ℕ) (hcap : ClockFrontShape.capMinute (L := L) (K := K) < Tcap)
    (mc₀ : Config (MarkedAgent L K))
    (h0 : ∀ T < Tcap, recInv (L := L) (K := K) T θn n cc mc₀)
    (hmark : ∀ T < Tcap, MarkInv (L := L) (K := K) T mc₀)
    -- the locked-margin uniform smallness inputs (item 4):
    (dB eB tB : ℝ≥0∞)
    (hdB : ∀ T < Tcap, δ T ≤ dB)
    (heB : ∀ T < Tcap,
      (GatedDrift.killK (markedK (L := L) (K := K) T θn)
          (taintedGate (L := L) (K := K) n) ^ (w * KK)) (some mc₀) {none} ≤ eB)
    (htB : ∀ T < Tcap,
      ENNReal.ofReal
        (Real.exp (σ * (1 + 4 / (n : ℝ)) ^ (w * KK)
            * (taintedCount (L := L) (K := K) mc₀ : ℝ)
          + 2 * σ * (1 + 4 / (n : ℝ)) ^ (w * KK) * ((θn : ℝ) / (n : ℝ)) ^ 2
              * ((w * KK : ℕ) : ℝ)
          - σ * ((tt + 1 : ℕ) : ℝ))) ≤ tB) :
    ((NonuniformMajority L K).transitionKernel ^ (w * KK)) (eraseConfig (L := L) (K := K) mc₀)
        {c | (c.card = n ∧ AllClockP3 (L := L) (K := K) c ∧
            (∀ T, θ ≤ ClockFrontProfile.frac (L := L) (K := K) T c →
              cc * (rBeyond (L := L) (K := K) T c : ℝ) ^ 2 / (n : ℝ) + (tt : ℝ)
                ≤ (rBeyond (L := L) (K := K) T c : ℝ) ^ 2 / (n : ℝ)))
          ∧ ¬ WindowedFrontProfile (L := L) (K := K) θ c}
      ≤ (Tcap : ℝ≥0∞) * ((KK : ℝ≥0∞) * dB + (eB + tB)) := by
  refine le_trans (windowedFrontProfile_whp (L := L) (K := K) θn n hn cc w θ hθpos aM haM δ hB
    σ hσ KK hsmall tt Tcap hcap mc₀ h0 hmark) ?_
  exact front_tail_sum_le KK Tcap δ
    (fun T => (GatedDrift.killK (markedK (L := L) (K := K) T θn)
        (taintedGate (L := L) (K := K) n) ^ (w * KK)) (some mc₀) {none})
    (fun T => ENNReal.ofReal
      (Real.exp (σ * (1 + 4 / (n : ℝ)) ^ (w * KK)
          * (taintedCount (L := L) (K := K) mc₀ : ℝ)
        + 2 * σ * (1 + 4 / (n : ℝ)) ^ (w * KK) * ((θn : ℝ) / (n : ℝ)) ^ 2
            * ((w * KK : ℕ) : ℝ)
        - σ * ((tt + 1 : ℕ) : ℝ))))
    dB eB tB hdB heB htB

/-! ## Part 41 — the glue wiring (item 5): `GoodFrontWidth` whp from `WindowedFrontProfile` whp
(item 4) and `ClimbBound` whp.

`goodFrontWidth_of_windowed_profile_and_climb` (ClockFrontProfile) is the DETERMINISTIC reduction
`GoodFrontWidth (W₁+W₂) ⟸ WindowedFrontProfile θ ∧ ClimbBound θ W₂` on a full-population all-phase-3
config with floor `θ ≥ 1/card`.  So the failure event for `GoodFrontWidth` is covered by the union
of the two failure events.  We bound it by the `windowedFrontProfile_whp_packaged` tail (item 4) plus
the `ClimbBound`-failure mass; the latter is bounded from `ClimbTail.climb_real_tail` (a union over
levels `k ≤ capMinute`), carried here as the `hclimb` input so the WindowedFrontProfile-side wiring is
complete and the ClimbBound-side residual is exactly localized. -/

open ClockFrontProfile in
/-- **The deterministic GoodFrontWidth bad-event cover.**  On a full-population all-phase-3 config
with floor `θ ≥ 1/card`, if `GoodFrontWidth (W₁+W₂)` fails (`W₁ = frontWidthBound card`), then either
`WindowedFrontProfile θ` fails or `ClimbBound θ W₂` fails. -/
theorem goodFrontWidth_bad_subset (θ : ℝ) (W₂ : ℕ) (c : Config (AgentState L K))
    (hcard : 2 ≤ c.card) (hall : AllClockP3 (L := L) (K := K) c)
    (hθ : 1 / (c.card : ℝ) ≤ θ)
    (hbad : ¬ GoodFrontWidth (L := L) (K := K)
      (FrontTail.frontWidthBound c.card + W₂) c) :
    ¬ WindowedFrontProfile (L := L) (K := K) θ c ∨
      ¬ ClimbBound (L := L) (K := K) θ W₂ c := by
  by_contra hcon
  push Not at hcon
  obtain ⟨hwp, hcb⟩ := hcon
  exact hbad (goodFrontWidth_of_windowed_profile_and_climb (L := L) (K := K) θ W₂ c hcard hall hθ
    hwp hcb)

open ClockFrontProfile in
/-- **STEP 5 — `GoodFrontWidth` whp (the glue capstone).**  On the real kernel, the probability that
the end config is a full-population all-phase-3 clock config (with the negligibility, the floor
`θ ≥ 1/n`) yet FAILS the moving-frame width invariant `GoodFrontWidth (W₁+W₂)` is at most the
`WindowedFrontProfile` tail (item 4's packaging) plus the `ClimbBound`-failure mass `climbB`.  This
wires the whole windowed-front engine (items 1–4) into the clock consumers' shape; the `ClimbBound`
mass `climbB` is the `ClimbTail.climb_real_tail` deliverable (the level-union of the gated climb
tail), carried here as `hclimb`. -/
theorem goodFrontWidth_whp (n : ℕ) (hn : 2 ≤ n) (cc : ℝ) (θ : ℝ) (hθn : 1 / (n : ℝ) ≤ θ)
    (tt : ℕ) (W₂ : ℕ) (t : ℕ) (mc₀ : Config (MarkedAgent L K))
    (wfpB climbB : ℝ≥0∞)
    (hwfp : ((NonuniformMajority L K).transitionKernel ^ t) (eraseConfig (L := L) (K := K) mc₀)
        {c | (c.card = n ∧ AllClockP3 (L := L) (K := K) c ∧
            (∀ T, θ ≤ ClockFrontProfile.frac (L := L) (K := K) T c →
              cc * (rBeyond (L := L) (K := K) T c : ℝ) ^ 2 / (n : ℝ) + (tt : ℝ)
                ≤ (rBeyond (L := L) (K := K) T c : ℝ) ^ 2 / (n : ℝ)))
          ∧ ¬ WindowedFrontProfile (L := L) (K := K) θ c} ≤ wfpB)
    (hclimb : ((NonuniformMajority L K).transitionKernel ^ t) (eraseConfig (L := L) (K := K) mc₀)
        {c | (c.card = n ∧ AllClockP3 (L := L) (K := K) c)
          ∧ ¬ ClimbBound (L := L) (K := K) θ W₂ c} ≤ climbB) :
    ((NonuniformMajority L K).transitionKernel ^ t) (eraseConfig (L := L) (K := K) mc₀)
        {c | (c.card = n ∧ AllClockP3 (L := L) (K := K) c ∧
            (∀ T, θ ≤ ClockFrontProfile.frac (L := L) (K := K) T c →
              cc * (rBeyond (L := L) (K := K) T c : ℝ) ^ 2 / (n : ℝ) + (tt : ℝ)
                ≤ (rBeyond (L := L) (K := K) T c : ℝ) ^ 2 / (n : ℝ)))
          ∧ ¬ GoodFrontWidth (L := L) (K := K)
              (FrontTail.frontWidthBound n + W₂) c}
      ≤ wfpB + climbB := by
  classical
  set wfpSet : Set (Config (AgentState L K)) :=
    {c | (c.card = n ∧ AllClockP3 (L := L) (K := K) c ∧
        (∀ T, θ ≤ ClockFrontProfile.frac (L := L) (K := K) T c →
          cc * (rBeyond (L := L) (K := K) T c : ℝ) ^ 2 / (n : ℝ) + (tt : ℝ)
            ≤ (rBeyond (L := L) (K := K) T c : ℝ) ^ 2 / (n : ℝ)))
      ∧ ¬ WindowedFrontProfile (L := L) (K := K) θ c} with hwfpSet
  set climbSet : Set (Config (AgentState L K)) :=
    {c | (c.card = n ∧ AllClockP3 (L := L) (K := K) c)
      ∧ ¬ ClimbBound (L := L) (K := K) θ W₂ c} with hclimbSet
  have hsub : {c : Config (AgentState L K) |
      (c.card = n ∧ AllClockP3 (L := L) (K := K) c ∧
        (∀ T, θ ≤ ClockFrontProfile.frac (L := L) (K := K) T c →
          cc * (rBeyond (L := L) (K := K) T c : ℝ) ^ 2 / (n : ℝ) + (tt : ℝ)
            ≤ (rBeyond (L := L) (K := K) T c : ℝ) ^ 2 / (n : ℝ)))
      ∧ ¬ GoodFrontWidth (L := L) (K := K)
          (FrontTail.frontWidthBound n + W₂) c}
      ⊆ wfpSet ∪ climbSet := by
    intro c hc
    obtain ⟨⟨hcard, hP3, hnegc⟩, hgfw⟩ := hc
    have hcard2 : 2 ≤ c.card := by rw [hcard]; omega
    have hθc : 1 / (c.card : ℝ) ≤ θ := by rw [hcard]; exact hθn
    have hgfw' : ¬ GoodFrontWidth (L := L) (K := K)
        (FrontTail.frontWidthBound c.card + W₂) c := by
      rwa [hcard]
    rcases goodFrontWidth_bad_subset (L := L) (K := K) θ W₂ c hcard2 hP3 hθc hgfw' with h | h
    · exact Or.inl ⟨⟨hcard, hP3, hnegc⟩, h⟩
    · exact Or.inr ⟨⟨hcard, hP3⟩, h⟩
  refine le_trans (measure_mono hsub) ?_
  refine le_trans (measure_union_le _ _) ?_
  exact add_le_add hwfp hclimb

/-! ## Part 42 — the `ClimbBound`-whp union (item 5, ClimbBound side): the climb-failure mass via
`ClimbTail.climb_real_tail`.

`ClimbBound θ W₂ c` fails iff some level `k` is sub-floor (`frac k < θ`) yet carries a clock `W₂`
above (`0 < rBeyond(k+W₂)`).  A clock that far above forces `k ≤ capMinute`
(`climbN_ge_of_beyond_pos`), so the failure event is a finite union over `k ≤ capMinute` of exactly
`climb_real_tail`'s bad event (at `card = n`, `frac k < θ ↔ rBeyond k < θn` for `θ = θn/n`).  Each
term is the gated climb tail; the union is bounded by the per-level sum. -/

open ClockFrontProfile in
/-- **The `ClimbBound`-failure deterministic cover.**  On a full-population config (`card = n`) with
`θ = θn/n`, if `ClimbBound θ W₂` fails then some `k ≤ capMinute` witnesses the climb bad event
`rBeyond k < θn ∧ 0 < rBeyond(k+W₂)`. -/
theorem climbBound_bad_subset (n θn W₂ : ℕ) (hn : 0 < n) (hW₂ : 2 ≤ W₂) (θ : ℝ)
    (hθ : θ = (θn : ℝ) / (n : ℝ)) (c : Config (AgentState L K)) (hcard : c.card = n)
    (hbad : ¬ ClimbBound (L := L) (K := K) θ W₂ c) :
    ∃ k ∈ Finset.range (ClockFrontShape.capMinute (L := L) (K := K) + 1),
      rBeyond (L := L) (K := K) k c < θn ∧ 0 < rBeyond (L := L) (K := K) (k + W₂) c := by
  classical
  have hnℝ : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  unfold ClimbBound at hbad
  push Not at hbad
  obtain ⟨k, hfrac, hbeyond⟩ := hbad
  have hbeyond' : 0 < rBeyond (L := L) (K := K) (k + W₂) c := Nat.pos_of_ne_zero hbeyond
  -- frac k < θ ⟹ rBeyond k < θn (at card = n, θ = θn/n).
  have hrk : rBeyond (L := L) (K := K) k c < θn := by
    unfold ClockFrontProfile.frac at hfrac
    rw [hθ, hcard, div_lt_div_iff_of_pos_right hnℝ] at hfrac
    exact_mod_cast hfrac
  -- the clock W₂ above forces k + W₂ ≤ capMinute, hence k ≤ capMinute.
  have hkcap : k ≤ ClockFrontShape.capMinute (L := L) (K := K) := by
    by_contra hc
    push Not at hc
    rw [ClimbTail.rBeyond_eq_zero_of_cap_lt (L := L) (K := K) (k + W₂) (by omega) c] at hbeyond'
    omega
  exact ⟨k, Finset.mem_range.mpr (by omega), hrk, hbeyond'⟩

open ClockFrontProfile in
/-- **STEP 5 (ClimbBound side) — the `ClimbBound`-failure mass via the gated climb tail.**  On the
real kernel, the probability that the end config is a full-population all-phase-3 config yet FAILS
`ClimbBound θ W₂` (`θ = θn/n`) is at most the sum over levels `k ≤ capMinute` of
`ClimbTail.climb_real_tail`'s gated-tail bound (escape + the contraction tail).  This is the precise
`climbB` input of `goodFrontWidth_whp` — completing item 5. -/
theorem climbBound_whp (n θn W₂ : ℕ) (hn : 0 < n) (hW₂ : 2 ≤ W₂) (θ : ℝ)
    (hθ : θ = (θn : ℝ) / (n : ℝ)) (B' : ℕ) (s : ℝ) (hs : 0 ≤ s) (t : ℕ)
    (c₀ : Config (AgentState L K)) :
    ((NonuniformMajority L K).transitionKernel ^ t) c₀
        {c | (c.card = n ∧ AllClockP3 (L := L) (K := K) c)
          ∧ ¬ ClimbBound (L := L) (K := K) θ W₂ c}
      ≤ ∑ k ∈ Finset.range (ClockFrontShape.capMinute (L := L) (K := K) + 1),
          ((GatedDrift.killK ((NonuniformMajority L K).transitionKernel)
              (ClimbTail.climbGate (L := L) (K := K) n k B' θn) ^ t) (some c₀) {none} +
            (ENNReal.ofReal (1 + ((B' : ℝ) / (n : ℝ)) ^ 2 * (Real.exp s - 1))) ^ t *
              ClimbTail.climbPot (L := L) (K := K) k θn s c₀ /
              ENNReal.ofReal (Real.exp (s * ((W₂ : ℝ) - 1)))) := by
  classical
  have hsub : {c : Config (AgentState L K) |
      (c.card = n ∧ AllClockP3 (L := L) (K := K) c)
        ∧ ¬ ClimbBound (L := L) (K := K) θ W₂ c}
      ⊆ ⋃ k ∈ Finset.range (ClockFrontShape.capMinute (L := L) (K := K) + 1),
          {c | rBeyond (L := L) (K := K) k c < θn ∧
            0 < rBeyond (L := L) (K := K) (k + W₂) c} := by
    intro c hc
    obtain ⟨⟨hcard, _hP3⟩, hbad⟩ := hc
    obtain ⟨k, hk, hev⟩ := climbBound_bad_subset (L := L) (K := K) n θn W₂ hn hW₂ θ hθ c hcard hbad
    rw [Set.mem_iUnion₂]
    exact ⟨k, hk, hev⟩
  refine le_trans (measure_mono hsub) ?_
  refine le_trans (measure_biUnion_finset_le _ _) ?_
  apply Finset.sum_le_sum
  intro k _
  exact ClimbTail.climb_real_tail (L := L) (K := K) n k B' θn W₂ hW₂ s hs t c₀

/-! ## Part 43 — the `hB` discharge bricks (item 1): the geometric ladder + the floor/slice
exponent dischargers at the locked constants.

`per_window_delta` already abstracts the probabilistic content into the real inequalities `hfloor`
(floor exponent) and `hslice` (per-rung clean exponent); these are discharged from the proven helpers
`floor_exp_le`/`slice_exp_le` and the `window_constants_*` `norm_num` gates.  The two binding margins
(growth `δg > 0`, slice `A − B < 0`) are the locked-constant facts.  The remaining `n`-dependent
input is the window-length margin (`w = ⌊3n/200⌋`), carried as the scale hypotheses `hδg`/`hslc`.

Constants: `wp = 3/200`, `cc = 9/10`, `ε = 1/200`, `g = 5123/5000`, `G = 201/200`, `sg = 1/10`. -/

/-- **The locked growth `δg`**: a positive growth-floor slope at the locked constants `sg = 1/10`,
`g = 5123/5000`.  `δg = 171/1000·wp − sg(g−1)` with `wp = 3/200` (using `1−e^{−sg} ≥ sg − sg²/2`
for the `9.5e-2` factor); equals `≈ 1.05e-4 > 0` (`window_constants_growth`). -/
noncomputable def δgLocked : ℝ := (171/1000) * (3/200) - (1/10) * (5123/5000 - 1)

theorem δgLocked_pos : 0 < δgLocked := by
  unfold δgLocked; norm_num

/-- **The floor discharger**: at the locked growth constants, the floor exponent of
`per_window_delta` is `≤ −δgLocked·X₀ + sg`, provided the window-length scale margin
`δgLocked ≤ w·cg − sg(g−1)` holds (`cg = 1.8(1−e^{−sg})/n`; discharged from `w = ⌊3n/200⌋` at the
plug-in).  This supplies `per_window_delta`'s `hfloor` with `δg := δgLocked`. -/
theorem floor_discharge (n : ℕ) (w : ℕ) (X₀ : ℕ) (a0 : ℕ)
    (ha0 : (a0 : ℝ) ≤ (5123/5000) * (X₀ : ℝ) + 1)
    (hwmargin : δgLocked
      ≤ (w : ℝ) * (1.8 * (1 - Real.exp (-(1/10 : ℝ))) / (n : ℝ)) - (1/10) * (5123/5000 - 1)) :
    -(((1/10 : ℝ) + (w : ℝ) * (1.8 * (1 - Real.exp (-(1/10 : ℝ))) / (n : ℝ))) * (X₀ : ℝ))
        + (1/10 : ℝ) * (a0 : ℝ)
      ≤ -(δgLocked * (X₀ : ℝ)) + (1/10 : ℝ) :=
  floor_exp_le n (1/10) (5123/5000) δgLocked (by norm_num) w X₀ a0 ha0 hwmargin

/-- **The slice discharger**: at the locked constants, the rung-`m` clean exponent of
`per_window_delta` is `≤ σ·Q·(A − Gm·B)` with `A = cc·RWb`, `B = g²(cc − G²(1+ε)RWb·wp) > 0`, given
the per-rung structural inputs (`Y₀ ≤ cc·Q`, `RW ≤ RWb`, the drip cap, the threshold lower bound).
Combined with `window_constants_slice` (`A < B`) this yields the negative slice bracket. -/
theorem slice_discharge (Q σ RW RWb Gm Y₀ drip Yt : ℝ)
    (hσ : 0 ≤ σ) (hQ : 0 ≤ Q) (hRW0 : 0 ≤ RW)
    (hY : Y₀ ≤ (9/10 : ℝ) * Q) (hRW : RW ≤ RWb) (hRWb0 : 0 ≤ RWb)
    (hdrip : drip * (1 + (1/200 : ℝ)) * RW
      ≤ Gm * (201/200 : ℝ) ^ 2 * (5123/5000 : ℝ) ^ 2 * (1 + (1/200 : ℝ)) * RWb * (3/200) * Q)
    (hdrip0 : 0 ≤ drip)
    (hYt : (9/10 : ℝ) * Gm * (5123/5000 : ℝ) ^ 2 * Q ≤ Yt) :
    σ * RW * Y₀ + drip * (1 + (1/200 : ℝ)) * σ * RW - σ * Yt
      ≤ σ * (Q * ((9/10 : ℝ) * RWb - Gm
          * ((5123/5000 : ℝ) ^ 2 * ((9/10 : ℝ) - (201/200 : ℝ) ^ 2 * (1 + (1/200 : ℝ)) * RWb
              * (3/200))))) :=
  slice_exp_le Q σ (1/200) RW RWb (9/10) (5123/5000) (201/200) (3/200) Y₀ drip Gm Yt
    hσ hQ hRW0 (by norm_num) (by norm_num) hY hRW hRWb0 hdrip hdrip0 hYt

end EarlyDripMarked

end ExactMajority
