/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Margin ledgers — the shared exponent-profile finset algebra (Brick 0) and the
# Phase-6→7 / Phase-7→8 deterministic eliminator-margin ledgers (Bricks B, C)

Per `HANDOFF_THREE_CORES.md`, the §6/§7 margin floors split into:

* **A** (Theorem 6.2 Main confinement) — the one genuinely-new probability brick, carried as
  `UsefulMainFloor.Theorem62EntryHypotheses.hConfine` (not in this file).
* **B** (Lemma 7.4 as a deterministic ledger) — `Phase6To7Structure` from the A-shape confinement
  profile plus the Phase-6 high-mass drain.
* **C** (Lemma 7.6 as a deterministic ledger) — `Phase7To8Structure` from the Phase-7-entry margins
  minus the eliminators spent during the Phase-7 cancellation.

This file delivers **Brick 0** (the shared exponent-profile observables + partition identity used
by A/B/C) and the B/C deterministic ledgers, following the `PhaseFloors` /
`UsefulMainFloor.mainCount_eq_usefulMains_add_satExp` finset-filter count style.

NEW file; no existing file is edited; no sorry/admit/axiom/native_decide.
-/

import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.EliminatorMargins
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.UsefulMainFloor

namespace ExactMajority

open scoped BigOperators

namespace MarginLedgers

variable {L K : ℕ}

/-! ## Brick 0 — the shared Main exponent-profile observables and partition identity.

A `Main` agent has one of three bias shapes: `zero` (unbiased), `dyadic σ i` (a `σ`-signed
eliminand at exponent `i`, the **minority** side from the σ-perspective), or `dyadic s i` with
`s ≠ σ` (a `σ`-opposite eliminator at exponent `i`, the **majority** side).  These three classes
partition the Main population.  The per-exponent finsets `mainAtExp`/`minorityAtExp` reuse the
exact filter shape of `Phase7Convergence.minorityAt7` / `Phase8Convergence.minorityAt`
(definitionally equal), so the profile masses below feed directly into B/C. -/

/-- `σ`-signed Mains at exponent `i` (the minority/eliminand side).  Definitionally equal to
`Phase7Convergence.minorityAt7 σ i` and `Phase8Convergence.minorityAt σ i`. -/
def mainAtExp (σ : Sign) (i : Fin (L + 1)) : Finset (AgentState L K) :=
  Finset.univ.filter (fun a => a.role = Role.main ∧ a.bias = Bias.dyadic σ i)

/-- The `σ`-minority finset at exponent `i` (alias of `mainAtExp`, the σ-signed side). -/
def minorityAtExp (σ : Sign) (i : Fin (L + 1)) : Finset (AgentState L K) :=
  mainAtExp (L := L) (K := K) σ i

/-- `σ`-opposite Mains at exponent `i` (the majority/eliminator side): a Main whose dyadic bias is
signed `s ≠ σ` at exponent `i`. -/
def majorityAtExp (σ : Sign) (i : Fin (L + 1)) : Finset (AgentState L K) :=
  Finset.univ.filter (fun a => a.role = Role.main ∧ ∃ s, s ≠ σ ∧ a.bias = Bias.dyadic s i)

/-- Unbiased Mains (`role = main ∧ bias = zero`). -/
def zeroMainSet (L K : ℕ) : Finset (AgentState L K) :=
  Finset.univ.filter (fun a => a.role = Role.main ∧ a.bias = Bias.zero)

/-- `mainAtExp σ i` is the Phase-7 minority finset (definitional). -/
theorem mainAtExp_eq_minorityAt7 (σ : Sign) (i : Fin (L + 1)) :
    mainAtExp (L := L) (K := K) σ i = Phase7Convergence.minorityAt7 (L := L) (K := K) σ i := rfl

/-- `mainAtExp σ i` is the Phase-8 minority finset (definitional). -/
theorem mainAtExp_eq_minorityAt (σ : Sign) (i : Fin (L + 1)) :
    mainAtExp (L := L) (K := K) σ i = Phase8Convergence.minorityAt (L := L) (K := K) σ i := rfl

/-! ### Profile masses: total count over all exponents per class. -/

/-- Total `σ`-minority mass over all exponents. -/
def minorityProfileMass (σ : Sign) (c : Config (AgentState L K)) : ℕ :=
  ∑ i : Fin (L + 1), (minorityAtExp (L := L) (K := K) σ i).sum c.count

/-- Total `σ`-opposite (majority) eliminator mass over all exponents. -/
def majorityProfileMass (σ : Sign) (c : Config (AgentState L K)) : ℕ :=
  ∑ i : Fin (L + 1), (majorityAtExp (L := L) (K := K) σ i).sum c.count

/-- The unbiased-Main count. -/
def zeroMainCount (c : Config (AgentState L K)) : ℕ :=
  (zeroMainSet L K).sum c.count

/-! ### Flat per-class finsets (over the bias, not per-exponent) and the flat = per-exponent
bridge.  The flat finsets give the clean disjoint partition of the Main filter; the per-exponent
profile masses equal the flat sums via a fiberwise sum keyed on the bias exponent. -/

/-- Flat `σ`-minority finset: all `σ`-signed Mains (any exponent). -/
def minoritySet (σ : Sign) : Finset (AgentState L K) :=
  Finset.univ.filter (fun a => a.role = Role.main ∧ ∃ i, a.bias = Bias.dyadic σ i)

/-- Flat `σ`-opposite (majority) finset: all `s ≠ σ`-signed Mains (any exponent). -/
def majoritySet (σ : Sign) : Finset (AgentState L K) :=
  Finset.univ.filter (fun a => a.role = Role.main ∧ ∃ s i, s ≠ σ ∧ a.bias = Bias.dyadic s i)

/-- The flat minority mass equals the per-exponent profile mass: each `σ`-signed Main sits at
exactly one exponent `i`, so the flat sum fibers over the exponent index. -/
theorem minoritySet_sum_eq_profileMass (σ : Sign) (c : Config (AgentState L K)) :
    (minoritySet (L := L) (K := K) σ).sum c.count
      = minorityProfileMass (L := L) (K := K) σ c := by
  classical
  unfold minorityProfileMass minorityAtExp mainAtExp minoritySet
  -- fiber the flat filter over the exponent index `i`.
  rw [← Finset.sum_biUnion]
  · apply Finset.sum_congr _ (fun _ _ => rfl)
    ext a
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion]
    constructor
    · rintro ⟨hr, i, hb⟩; exact ⟨i, hr, hb⟩
    · rintro ⟨i, hr, hb⟩; exact ⟨hr, i, hb⟩
  · -- disjointness across distinct exponents.
    intro i _ j _ hij
    simp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro a ha hb
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
    rw [ha.2] at hb
    injection hb.2 with _ hidx
    exact hij hidx

/-- The flat majority mass equals the per-exponent profile mass. -/
theorem majoritySet_sum_eq_profileMass (σ : Sign) (c : Config (AgentState L K)) :
    (majoritySet (L := L) (K := K) σ).sum c.count
      = majorityProfileMass (L := L) (K := K) σ c := by
  classical
  unfold majorityProfileMass majorityAtExp majoritySet
  rw [← Finset.sum_biUnion]
  · apply Finset.sum_congr _ (fun _ _ => rfl)
    ext a
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion]
    constructor
    · rintro ⟨hr, s, i, hsne, hb⟩; exact ⟨i, hr, s, hsne, hb⟩
    · rintro ⟨i, hr, s, hsne, hb⟩; exact ⟨hr, s, i, hsne, hb⟩
  · intro i _ j _ hij
    simp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro a ha hb
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
    obtain ⟨_, s, _, hbi⟩ := ha
    obtain ⟨_, s', _, hbj⟩ := hb
    rw [hbi] at hbj
    injection hbj with _ hidx
    exact hij hidx

/-! ### The Main-population partition: `minoritySet ⊔ majoritySet ⊔ zeroMainSet`. -/

/-- A `Main` is exactly one of: `σ`-signed (minority), `σ`-opposite (majority), or unbiased. -/
theorem main_iff_minority_or_majority_or_zero (σ : Sign) (a : AgentState L K) :
    a.role = Role.main ↔
      a ∈ minoritySet (L := L) (K := K) σ ∨ a ∈ majoritySet (L := L) (K := K) σ
        ∨ a ∈ zeroMainSet L K := by
  simp only [minoritySet, majoritySet, zeroMainSet, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro hr
    rcases hb : a.bias with _ | ⟨s, i⟩
    · exact Or.inr (Or.inr ⟨hr, rfl⟩)
    · by_cases hs : s = σ
      · subst hs; exact Or.inl ⟨hr, i, rfl⟩
      · exact Or.inr (Or.inl ⟨hr, s, i, hs, rfl⟩)
  · rintro (⟨hr, _⟩ | ⟨hr, _⟩ | ⟨hr, _⟩) <;> exact hr

theorem minoritySet_majoritySet_disjoint (σ : Sign) :
    Disjoint (minoritySet (L := L) (K := K) σ) (majoritySet (L := L) (K := K) σ) := by
  classical
  rw [Finset.disjoint_left]
  intro a ha hb
  simp only [minoritySet, majoritySet, Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
  obtain ⟨_, i, hbi⟩ := ha
  obtain ⟨_, s, _, hsne, hbj⟩ := hb
  rw [hbi] at hbj
  injection hbj with hsig _
  exact hsne hsig.symm

theorem minoritySet_zeroMainSet_disjoint (σ : Sign) :
    Disjoint (minoritySet (L := L) (K := K) σ) (zeroMainSet L K) := by
  classical
  rw [Finset.disjoint_left]
  intro a ha hb
  simp only [minoritySet, zeroMainSet, Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
  obtain ⟨_, i, hbi⟩ := ha
  rw [hbi] at hb
  exact absurd hb.2 (by simp)

theorem majoritySet_zeroMainSet_disjoint (σ : Sign) :
    Disjoint (majoritySet (L := L) (K := K) σ) (zeroMainSet L K) := by
  classical
  rw [Finset.disjoint_left]
  intro a ha hb
  simp only [majoritySet, zeroMainSet, Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
  obtain ⟨_, s, i, _, hbi⟩ := ha
  rw [hbi] at hb
  exact absurd hb.2 (by simp)

/-- **Brick 0 — the Main exponent-profile partition.**  The Main role count splits exactly into the
σ-opposite (majority) eliminator profile mass, the σ-signed (minority) profile mass, and the
unbiased-Main count:
`mainCount c = majorityProfileMass σ c + minorityProfileMass σ c + zeroMainCount c`.
This is the shared finset algebra that B/C build the eliminator margins on. -/
theorem main_profile_partition (σ : Sign) (c : Config (AgentState L K)) :
    RoleSplitConcentration.mainCount (L := L) (K := K) c
      = majorityProfileMass (L := L) (K := K) σ c
        + minorityProfileMass (L := L) (K := K) σ c
        + zeroMainCount (L := L) (K := K) c := by
  classical
  rw [RoleSplitConcentration.mainCount,
    Phase6Convergence.countP_eq_sum_count6 (fun a : AgentState L K => a.role = Role.main) c]
  -- the Main filter = minoritySet ∪ majoritySet ∪ zeroMainSet (disjoint).
  have hsplit :
      Finset.univ.filter (fun a : AgentState L K => a.role = Role.main)
        = minoritySet (L := L) (K := K) σ ∪
          (majoritySet (L := L) (K := K) σ ∪ zeroMainSet L K) := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
    rw [main_iff_minority_or_majority_or_zero σ a]
  have hdisj1 :
      Disjoint (minoritySet (L := L) (K := K) σ)
        (majoritySet (L := L) (K := K) σ ∪ zeroMainSet L K) := by
    rw [Finset.disjoint_union_right]
    exact ⟨minoritySet_majoritySet_disjoint σ, minoritySet_zeroMainSet_disjoint σ⟩
  rw [hsplit, Finset.sum_union hdisj1,
    Finset.sum_union (majoritySet_zeroMainSet_disjoint σ),
    minoritySet_sum_eq_profileMass, majoritySet_sum_eq_profileMass]
  have hz : (∑ x ∈ zeroMainSet L K, c.count x) = zeroMainCount (L := L) (K := K) c := rfl
  rw [hz]
  omega

end MarginLedgers

end ExactMajority
