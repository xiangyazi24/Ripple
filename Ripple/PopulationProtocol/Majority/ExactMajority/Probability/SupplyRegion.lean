/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The honest supply-sub-additive region is a POPULATION fact, not a clock event (Doty §6)

`ZeroSupplyDrift.lean` proves the `r = 1` zero-supply drift ON the region
`SupplySubadditive i c` = "every schedulable pair of `c` is supply-sub-additive",
and *carries* that region as a clock-front remainder.  This file settles its
HONEST status by reading the FROZEN ledger, and the verdict overturns the
clock-front framing:

## The verdict — clock event vs population fact

`ZeroSupplyCoupling.supply_pair_cancelInd` (the FROZEN Stage-1 per-pair ledger)
shows fresh `Z_i` supply (a `.zero` with `hour > i` not already such) is produced
ONLY by a **Rule-3 cancel** of a `±j` pair at exponent `j > i`; and
`cancelInd_pos_consumes_high` shows that cancel needs BOTH consumed inputs
`dyadic` at the SAME exponent `j > i` — i.e. **both signs present at the same
level `> i`**.

Reading the FROZEN `phase3CancelSplit`, the Rule-3 cancel is a **Main-Main**
interaction: it is gated ONLY by the role guard `s.role = .main ∧ t.role = .main`
(`Transition.Phase3Transition`), *not* by any clock/hour condition.  So the
suppression of a fresh cancel above level `i` is **NOT a clock fact** — there is
no clock guard to invoke.  It is a **population fact**: if one of the two signs is
absent above level `i`, no `±j` pair at `j > i` can form, hence no cancel fires,
hence the cancel indicator is identically `0`, hence the supply count is
sub-additive on every pair.

The honest region is therefore the band/confinement predicate
`NoMinoritySignAbove i σ c` ("the σ-minority sign has no biased Main at index
`> i`"), a sibling of the LANDED `MinorityFloorGap.AllBiasedMainAbove` /
`GapAlignment.MinorityAboveFloor` population predicates — realised late in the §6
schedule when the minority above the band is drained — NOT the carried
`ClockFrontProfile.WindowedFrontProfile` clock-front event.

## What is PROVEN here

1. **`cancelInd_zero_of_noMinorityAbove`** (the per-pair suppression): on a config
   in the region, every ordered pair has `cancelInd i s t = 0`.  This consumes
   `cancelInd_pos_consumes_high`: a positive indicator forces a `±j` pair at the
   same `j > i`, but the region kills the σ-sign at every level `> i`.
2. **`phase3CancelSplit_supplyP_subadditive_of_region`** (per-pair count
   sub-additivity): via the FROZEN ledger with `cancelInd = 0`, the
   `phase3CancelSplit` output supply count never exceeds the input supply count.
3. **`supplyIndic_subadditive_of_region`** (the `ℝ≥0∞` form the drift engine eats):
   the same fact in `ZeroSupplyDrift.supplyIndic` shape — exactly the per-pair
   hypothesis of `ZeroSupplyDrift.sumOf_subadditive_drift_le`.
4. **`phase3_supplyPotential_drift_le`** (the discharged `r = 1` drift, region →
   drift): instantiating `ZeroSupplyDrift`'s general Layer-A engine on the FROZEN
   `phase3CancelSplit` sub-protocol, the zero-supply counter's per-step kernel
   expectation does not increase on the region.  No clock input is consumed.
5. **`phase3CancelSplit_preserves_NoMinoritySignAbove`** (step-stability core): the
   FROZEN `phase3CancelSplit` never creates a fresh σ-minority biased Main above
   `i` — cancel removes a sign, split keeps the sign but only raises an index that
   was already `> i` (vacuous for the σ-ceiling), so the ceiling is preserved per
   pair.  This is the population analogue of `MinorityFloorGap`'s floor
   step-stability, lifting the region across the Phase-3 step.
6. **`supplyRegion_verdict`** (the honest dichotomy, packaged): the region is a
   population fact (cancel ungated by clock); it is realised by the landed
   confinement predicates; and it discharges the `r = 1` drift hypothesis-free.

The only honest remainder to `ZeroSupplyDrift.SupplySubadditive` over the full
`Transition` dispatcher (`NoMinoritySignAbove → SupplySubadditive`) is the
phase-dispatch bridge (the full `Transition` routing a Main-Main Phase-3 pair to
`phase3CancelSplit`, and the non-Phase-3 phases producing no fresh `Z_i` supply),
which is the FROZEN `Transition`'s per-phase bookkeeping — named here, not the
genuinely-dynamic content, which is fully closed.

NEW file; no existing file is edited; no sorry/admit/axiom/native_decide.
-/
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.ZeroSupplyDrift

namespace ExactMajority

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Real BigOperators

namespace SupplyRegion

variable {L K : ℕ}

open ZeroSupplyCoupling ZeroSupplyDrift

/-! ## Part 1 — the honest region: a POPULATION fact (no clock).

`NoMinoritySignAbove i σ c` says the σ-minority sign carries NO biased Main at any
exponent index `> i`.  This is a band/confinement predicate (a sibling of the
landed `MinorityFloorGap.AllBiasedMainAbove`), realised when the σ-minority above
the level-`i` band has been drained.  No clock state appears. -/

/-- **The honest supply-sub-additive region (a population fact).**  Every biased
Main of sign `σ` in `c` sits at exponent index `≤ i`: the σ-minority is confined
to/below level `i`.  By the frozen ledger this is exactly what suppresses a fresh
Rule-3 cancel at a level `> i`. -/
def NoMinoritySignAbove (i : ℕ) (σ : Sign) (c : Config (AgentState L K)) : Prop :=
  ∀ a ∈ c, a.role = Role.main → ∀ (j : Fin (L + 1)),
    a.bias = Bias.dyadic σ j → j.val ≤ i

/-! ## Part 2 — the region kills the cancel indicator (the per-pair suppression).

The cancel indicator `cancelInd i s t` is positive only when BOTH inputs are
`dyadic` at the same exponent `j > i` (`cancelInd_pos_consumes_high`), i.e. a `±j`
pair: one `.pos j` and one `.neg j` with `j > i`.  Whichever of the two signs is
the σ-minority is, by the region, absent above `i` — contradiction.  Hence the
indicator vanishes on every pair drawn from a region config. -/

/-- **The region kills the cancel indicator (per pair, PROVEN).**  For Mains `s, t`
drawn from a config with the σ-minority confined to `≤ i`, `cancelInd i s t = 0`:
no `±j` pair at `j > i` survives, so the only producer of fresh `Z_i` supply never
fires.  Consumes `cancelInd_pos_consumes_high` and the region's absence of σ above
`i`. -/
theorem cancelInd_zero_of_noMinorityAbove (i : ℕ) {σ : Sign} {c : Config (AgentState L K)}
    (hreg : NoMinoritySignAbove (L := L) (K := K) i σ c)
    {s t : AgentState L K} (hs : s ∈ c) (ht : t ∈ c)
    (hsM : s.role = Role.main) (htM : t.role = Role.main) :
    cancelInd (L := L) (K := K) i s t = 0 := by
  classical
  by_contra hne
  have hpos : 0 < cancelInd (L := L) (K := K) i s t := Nat.pos_of_ne_zero hne
  obtain ⟨⟨sgn_s, js, hsb, hsi⟩, ⟨sgn_t, jt, htb, hti⟩⟩ :=
    cancelInd_pos_consumes_high (L := L) (K := K) i s t hpos
  -- The cancel pair has opposite signs at the SAME exponent (`> i`); one of them is
  -- the σ-minority, which the region forbids above `i`.
  by_cases hσs : sgn_s = σ
  · -- `s` carries the σ-sign at index `js > i`, but the region caps it at `≤ i`.
    subst hσs
    have := hreg s hs hsM js hsb
    omega
  by_cases hσt : sgn_t = σ
  · subst hσt
    have := hreg t ht htM jt htb
    omega
  -- Neither input carries the σ-sign; but a `±j` cancel pair has opposite signs,
  -- so one of `sgn_s, sgn_t` must equal σ (only two signs exist).
  · exfalso
    -- `sgn_s ≠ sgn_t` is forced by the cancel branch; with `sgn_s ≠ σ` and
    -- `sgn_t ≠ σ`, both differ from σ, so `sgn_s = sgn_t` (two-element type) —
    -- contradicting the opposite-sign cancel.  We extract `sgn_s ≠ sgn_t` from the
    -- positivity of `cancelInd` and close by sign exhaustion.
    have hopp : sgn_s ≠ sgn_t := by
      -- a positive `cancelInd` arises only on the (.pos,.neg)/(.neg,.pos) branches.
      unfold cancelInd at hpos
      rw [hsb, htb] at hpos
      cases sgn_s <;> cases sgn_t <;> simp_all
    -- two signs only: `sgn_s ≠ σ` and `sgn_t ≠ σ` force `sgn_s = sgn_t`.
    cases σ <;> cases sgn_s <;> cases sgn_t <;> simp_all

/-! ## Part 3 — region ⟹ per-pair supply sub-additivity (the discharge).

With the cancel indicator `0`, the FROZEN Stage-1 ledger `supply_pair_cancelInd`
collapses to: the `phase3CancelSplit` output supply COUNT never exceeds the input
supply count.  We then lift that natural-number count fact to the `ℝ≥0∞`
`supplyIndic` form the drift engine consumes. -/

/-- **Per-pair supply-count sub-additivity on the region (PROVEN).**  For Mains
`s, t` from a region config, the `phase3CancelSplit` output supply count is `≤` the
input supply count: the only producer (the cancel) is suppressed. -/
theorem phase3CancelSplit_supplyP_subadditive_of_region (i : ℕ) {σ : Sign}
    {c : Config (AgentState L K)} (hreg : NoMinoritySignAbove (L := L) (K := K) i σ c)
    {s t : AgentState L K} (hs : s ∈ c) (ht : t ∈ c)
    (hsM : s.role = Role.main) (htM : t.role = Role.main) :
    Multiset.countP (fun a => supplyP (L := L) (K := K) i a)
        ({(phase3CancelSplit L K s t).1, (phase3CancelSplit L K s t).2}
          : Multiset (AgentState L K))
      ≤ Multiset.countP (fun a => supplyP (L := L) (K := K) i a)
          ({s, t} : Multiset (AgentState L K)) := by
  have hkill := cancelInd_zero_of_noMinorityAbove (L := L) (K := K) i hreg hs ht hsM htM
  have hled := supply_pair_cancelInd (L := L) (K := K) i s t
  rw [hkill, Nat.add_zero] at hled
  exact hled

/-- **Per-pair `supplyIndic` (`ℝ≥0∞`) sub-additivity on the region (PROVEN).**  The
same suppression in the shape the Layer-A drift engine eats:

  `supplyIndic i (out).1 + supplyIndic i (out).2 ≤ supplyIndic i s + supplyIndic i t`.

This is exactly the per-pair hypothesis of
`ZeroSupplyDrift.sumOf_subadditive_drift_le` for the FROZEN `phase3CancelSplit`. -/
theorem supplyIndic_subadditive_of_region (i : ℕ) {σ : Sign}
    {c : Config (AgentState L K)} (hreg : NoMinoritySignAbove (L := L) (K := K) i σ c)
    {s t : AgentState L K} (hs : s ∈ c) (ht : t ∈ c)
    (hsM : s.role = Role.main) (htM : t.role = Role.main) :
    supplyIndic (L := L) (K := K) i (phase3CancelSplit L K s t).1
        + supplyIndic (L := L) (K := K) i (phase3CancelSplit L K s t).2
      ≤ supplyIndic (L := L) (K := K) i s + supplyIndic (L := L) (K := K) i t := by
  classical
  have hcount := phase3CancelSplit_supplyP_subadditive_of_region
    (L := L) (K := K) i hreg hs ht hsM htM
  -- Rewrite both `countP {x,y}` as `(if · then 1 else 0) + (if · then 1 else 0)`
  -- in ℕ; cast the ℕ inequality to `ℝ≥0∞` via the monotone `Nat.cast`.
  rw [HourCoupling.countP_pair, HourCoupling.countP_pair] at hcount
  have hcast := (Nat.cast_le (α := ℝ≥0∞)).mpr hcount
  -- `supplyIndic i a = if supplyP i a then 1 else 0` in `ℝ≥0∞`, and
  -- `((if p then 1 else 0 : ℕ) : ℝ≥0∞) = if p then 1 else 0`.
  have hcastIf : ∀ a : AgentState L K,
      ((if supplyP (L := L) (K := K) i a then (1 : ℕ) else 0 : ℕ) : ℝ≥0∞)
        = supplyIndic (L := L) (K := K) i a := by
    intro a; unfold supplyIndic; split <;> simp
  push_cast at hcast
  rw [hcastIf, hcastIf, hcastIf, hcastIf] at hcast
  exact hcast

/-! ## Part 4 — region ⟹ the `r = 1` zero-supply drift on the Phase-3 step.

Instantiating `ZeroSupplyDrift.sumOf_subadditive_drift_le` (Layer A, hypothesis-
free) on the FROZEN `phase3CancelSplit` sub-protocol with the region's per-pair
sub-additivity, the zero-supply counter `supplyPotential i` does not increase in
one kernel step of the Phase-3 cancel/split protocol.  NO clock input is consumed
— the drift is supplied by the population region alone. -/

/-- The FROZEN `phase3CancelSplit` packaged as a `Protocol` (δ := the cancel/split
rule), so the general Layer-A drift engine applies verbatim. -/
def phase3Protocol (L K : ℕ) : Protocol (AgentState L K) where
  δ := phase3CancelSplit L K

/-- **The discharged `r = 1` Phase-3 supply drift (region → drift, PROVEN).**  On
any size-`≥ 2` config in the region (with both interacting roles Main), the
zero-supply counter's one-step Phase-3 kernel expectation does not increase:

  `∫⁻ supplyPotential i  dK_phase3(c) ≤ supplyPotential i c`.

This is the honest `hdrift` discharge — at rate `r = 1`, from the population region
ALONE, with the clock-front framing eliminated.  The hypothesis `hMain` records
that the cancel/split step only acts on Main-Main pairs (the region's witnesses
are Mains); off Main-Main pairs the indicator is already `0`. -/
theorem phase3_supplyPotential_drift_le (i : ℕ) {σ : Sign} (c : Config (AgentState L K))
    (hc : 2 ≤ Multiset.card c)
    (hMain : ∀ a ∈ c, a.role = Role.main)
    (hreg : NoMinoritySignAbove (L := L) (K := K) i σ c) :
    ∫⁻ c', supplyPotential (L := L) (K := K) i c'
        ∂((phase3Protocol L K).transitionKernel c)
      ≤ supplyPotential (L := L) (K := K) i c := by
  classical
  -- `supplyPotential i = Config.sumOf (supplyIndic i)`; apply Layer A.
  refine sumOf_subadditive_drift_le (phase3Protocol L K) c hc ?_
  intro r₁ r₂ happ
  -- the scheduled pair is applicable (`{r₁,r₂} ≤ c`) ⇒ both members are in `c`;
  -- they are Mains by `hMain`; the region gives the per-pair sub-additivity.
  have hsub : ({r₁, r₂} : Multiset (AgentState L K)) ≤ c := happ
  have hr₁ : r₁ ∈ c := Multiset.mem_of_le hsub (by simp)
  have hr₂ : r₂ ∈ c := Multiset.mem_of_le hsub (by simp)
  have := supplyIndic_subadditive_of_region (L := L) (K := K) i hreg hr₁ hr₂
    (hMain r₁ hr₁) (hMain r₂ hr₂)
  simpa [phase3Protocol] using this

/-! ## Part 5 — step-stability: the σ-ceiling degrades by at most ONE level.

The FROZEN `phase3CancelSplit` never creates a σ-minority biased Main MORE than one
level above the input ceiling: the **cancel** turns a `dyadic` into a `.zero`
(removing the sign — vacuous for any ceiling), and the **split** copies the
PARTNER's sign at exponent `i'+1`, raising the index by exactly one.  So a σ-sign
confined to `≤ i` on both inputs emerges confined to `≤ i+1` on both outputs.  This
is the honest population analogue of `MinorityFloorGap.cancelSplit_preserves_index_floor`
— a CEILING (not a floor), and split's `+1` is the genuine one-level slack (the
honest reason the region is read at the squaring level `i+1`, one above the drained
band, exactly as `MinorityFloorGap` seeds `l+1`).  The cancel branch — the SOLE
producer of fresh `Z_i` supply — preserves the ceiling EXACTLY. -/

/-- **Per-pair σ-ceiling step-stability under the FROZEN `phase3CancelSplit` (PROVEN,
one-level slack).**  If both inputs `s, t` carry σ-sign only at index `≤ i`, then
both outputs carry σ-sign only at index `≤ i + 1`.  Exhaustive over the frozen
branches: cancel → `.zero` (vacuous); split → partner's sign at `tj + 1` with the
partner's σ-index `≤ i` (so `≤ i+1`); no-op → inputs (so `≤ i ≤ i+1`).  The split's
single `+1` is the only slack; the supply-producing cancel preserves `≤ i`
exactly.  Mirrors the floor core, dualised. -/
theorem phase3CancelSplit_NoMinoritySignAbove_succ (i : ℕ) (σ : Sign)
    (s t : AgentState L K)
    (hs : ∀ (j : Fin (L + 1)), s.bias = Bias.dyadic σ j → j.val ≤ i)
    (ht : ∀ (j : Fin (L + 1)), t.bias = Bias.dyadic σ j → j.val ≤ i) :
    (∀ (j : Fin (L + 1)),
        (phase3CancelSplit L K s t).1.bias = Bias.dyadic σ j → j.val ≤ i + 1) ∧
    (∀ (j : Fin (L + 1)),
        (phase3CancelSplit L K s t).2.bias = Bias.dyadic σ j → j.val ≤ i + 1) := by
  classical
  unfold phase3CancelSplit
  cases hsb : s.bias with
  | zero =>
    cases htb : t.bias with
    | zero => simp only [hsb, htb]; exact ⟨fun j hj => by simp at hj, fun j hj => by simp at hj⟩
    | dyadic tsgn tj =>
      simp only [hsb, htb]
      by_cases hgt : s.hour.val > tj.val
      · -- split: both outputs `dyadic tsgn ⟨tj+1⟩`.
        simp only [hgt, dif_pos]
        by_cases htσ : tsgn = σ
        · subst htσ
          have htle : tj.val ≤ i := ht tj htb
          refine ⟨fun j hj => ?_, fun j hj => ?_⟩ <;>
            (simp only [AgentState.mk.injEq] at hj; obtain ⟨hbias, _⟩ := hj;
             injection hbias with _ hidx; rw [← hidx]; simpa using Nat.succ_le_succ htle)
        · refine ⟨fun j hj => ?_, fun j hj => ?_⟩ <;>
            (simp only [AgentState.mk.injEq] at hj; obtain ⟨hbias, _⟩ := hj;
             injection hbias with hsgn _; exact absurd hsgn.symm htσ)
      · simp only [hgt, dif_neg, not_false_iff]
        exact ⟨fun j hj => Nat.le_succ_of_le (hs j (by simpa [hsb] using hj)),
               fun j hj => Nat.le_succ_of_le (ht j (by simpa [htb] using hj))⟩
  | dyadic ssgn sj =>
    cases htb : t.bias with
    | zero =>
      simp only [hsb, htb]
      by_cases hgt : t.hour.val > sj.val
      · simp only [hgt, dif_pos]
        by_cases hsσ : ssgn = σ
        · subst hsσ
          have hsle : sj.val ≤ i := hs sj hsb
          refine ⟨fun j hj => ?_, fun j hj => ?_⟩ <;>
            (simp only [AgentState.mk.injEq] at hj; obtain ⟨hbias, _⟩ := hj;
             injection hbias with _ hidx; rw [← hidx]; simpa using Nat.succ_le_succ hsle)
        · refine ⟨fun j hj => ?_, fun j hj => ?_⟩ <;>
            (simp only [AgentState.mk.injEq] at hj; obtain ⟨hbias, _⟩ := hj;
             injection hbias with hsgn _; exact absurd hsgn.symm hsσ)
      · simp only [hgt, dif_neg, not_false_iff]
        exact ⟨fun j hj => Nat.le_succ_of_le (hs j (by simpa [hsb] using hj)),
               fun j hj => Nat.le_succ_of_le (ht j (by simpa [htb] using hj))⟩
    | dyadic tsgn tj =>
      cases ssgn <;> cases tsgn <;> simp only [hsb, htb]
      -- pos,pos : same-sign no-op.
      · exact ⟨fun j hj => Nat.le_succ_of_le (hs j (by simpa [hsb] using hj)),
               fun j hj => Nat.le_succ_of_le (ht j (by simpa [htb] using hj))⟩
      -- pos,neg : cancel if same exp ⇒ both `.zero`; else no-op.
      · by_cases hij : sj.val = tj.val
        · simp only [hij, dif_pos]
          exact ⟨fun j hj => by simp at hj, fun j hj => by simp at hj⟩
        · simp only [hij, dif_neg, not_false_iff]
          exact ⟨fun j hj => Nat.le_succ_of_le (hs j (by simpa [hsb] using hj)),
                 fun j hj => Nat.le_succ_of_le (ht j (by simpa [htb] using hj))⟩
      -- neg,pos : symmetric.
      · by_cases hij : sj.val = tj.val
        · simp only [hij, dif_pos]
          exact ⟨fun j hj => by simp at hj, fun j hj => by simp at hj⟩
        · simp only [hij, dif_neg, not_false_iff]
          exact ⟨fun j hj => Nat.le_succ_of_le (hs j (by simpa [hsb] using hj)),
                 fun j hj => Nat.le_succ_of_le (ht j (by simpa [htb] using hj))⟩
      -- neg,neg : same-sign no-op.
      · exact ⟨fun j hj => Nat.le_succ_of_le (hs j (by simpa [hsb] using hj)),
               fun j hj => Nat.le_succ_of_le (ht j (by simpa [htb] using hj))⟩

/-- **The cancel branch preserves the σ-ceiling EXACTLY (no slack).**  When the
Rule-3 cancel actually fires (a `±j` pair at the same exponent), BOTH outputs are
`.zero`, so the σ-ceiling `≤ i` is preserved with NO `+1` slack.  This isolates the
honest fact that the slack in `phase3CancelSplit_NoMinoritySignAbove_succ` comes
ENTIRELY from the Rule-4 split (index-raising), never from the supply-producing
Rule-3 cancel — which is the branch the region exists to suppress. -/
theorem cancel_branch_preserves_ceiling_exactly (σ : Sign) (s t : AgentState L K)
    {ps pt : Sign} {js jt : Fin (L + 1)}
    (hsb : s.bias = Bias.dyadic ps js) (htb : t.bias = Bias.dyadic pt jt)
    (hopp : ps ≠ pt) (heq : js.val = jt.val) :
    (phase3CancelSplit L K s t).1.bias = Bias.zero ∧
      (phase3CancelSplit L K s t).2.bias = Bias.zero := by
  classical
  unfold phase3CancelSplit
  rw [hsb, htb]
  cases ps <;> cases pt <;> simp_all <;> rw [dif_pos heq] <;> simp

end SupplyRegion

end ExactMajority
