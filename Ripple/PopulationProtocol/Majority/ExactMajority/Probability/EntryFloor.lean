/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The §6 hour-induction BASE CASE — the Phase-3 entry band floor (`hStart`)

This file (append-only; no existing file edited) supplies the genuinely-open BASE CASE that
`HourInduction.lean`'s `hourInduction` / `movingBand_union` consume as `hStart` —
`BandConfined l₀ c₀`, the band floor at the Phase-3 entry.  It surveys the HONEST provenance of that
floor from the protocol's frozen `phaseInit 3` (Transition.lean), and records the hour arithmetic
that ties the deepened terminal floor `l₀ + numHours` to the seed level `l + 1` the downstream
`SeedExport` / `PaperRegime` consumers require.

## The provenance chain (where the entry floor comes from)

The §6 dyadic-exponent track does NOT exist in Phases 1–2:

* **Phase 1** averages the **`smallBias`** field — the `Fin 7` "small bias" track (values `0..6`),
  NOT the dyadic `Bias L` exponent track.  `phaseInit 1` only touches roles/counters; the dyadic
  `bias` field is untouched (`phaseInit_smallBias_eq`, and the dyadic `bias` is set only at phase 3).
* **Phase 2** detects opinions from the averaged `smallBias`: `phaseInit 2` errors out (phase 10) if
  `|smallBias|` is too small/large, else sets `opinions := sign(smallBias)`.  Still no dyadic track.
* **Phase 3** is where the dyadic exponent track is BORN.  `phaseInit 3` at a Main performs the
  **smallBias → dyadic conversion**:

  ```
  newBias := if a.smallBias.val < 3 then .dyadic .neg ⟨0,_⟩
             else if a.smallBias.val > 3 then .dyadic .pos ⟨0,_⟩
             else .zero
  { a with bias := newBias, hour := ⟨0,_⟩ }
  ```

  So a biased Main entering Phase 3 gets dyadic exponent index **exactly `0`** (the index `⟨0,_⟩`
  in `Fin (L+1)`; recall in `Bias.lean` the index `i = 0` is the SHALLOWEST level, bias `= ±1`).
  The conversion maps every averaged `smallBias` to STARTING exponent `0` — it is DETERMINISTIC.

## The honest entry floor `l₀ = 0`

`MinorityFloorGap.AllBiasedMainAbove m c` is *every biased Main sits at exponent index `≥ m`*.  At
the Phase-3 entry every biased Main's index is the init value `0`, so the entry floor is `l₀ = 0`:

* `allBiasedMainAbove_zero` — `AllBiasedMainAbove 0 c` holds for ANY config `c`, because the dyadic
  index is a `Fin (L+1)`, so `0 ≤ i.val` is unconditional.  This is the trivially-honest floor; the
  induction needs no nontrivial entry hypothesis, exactly because the conversion seeds at index `0`.
* `phaseInit3_main_bias_index_zero` — the SHARP provenance: the entry index is not merely `≥ 0` but
  EQUAL to `0`.  A Main with `a.smallBias.val ≠ 3` (a *biased* Main, the conversion's non-zero
  branch) entering Phase 3 has `(phaseInit L K 3 a).bias = .dyadic ss ⟨0,_⟩` for the conversion's
  sign — so its entry index is literally `0`.  This is the deterministic init mapping that makes the
  entry floor exactly `l₀ = 0`, not just vacuously `≥ 0`.

## The hour arithmetic (`l₀ → l₀ + numHours = l + 1`, and where `l` sits relative to `L`)

`hourInduction` deepens the floor `l₀ → l₀ + numHours`.  The downstream seed consumers
(`SeedExport.seedExport_of_post_succ`, `phase6To7_surface_of_seed`, `Theorem62Paper.hConfine3`) ride
on the TERMINAL floor `AllBiasedMainAbove (l + 1)` — the band seed at level `l + 1`.  Matching the
terminal floor to the seed:

```
l₀ + numHours = l + 1   with   l₀ = 0   ⟹   numHours = l + 1.
```

The §6 schedule budgets one hour per band level, and the clock carries `L + 1` hours (indices
`0..L`).  `SeedExport`'s `l+1` drain runs while there is a free sampling hour strictly above the
band-top index `l` and below the saturated top `L`, i.e. the explicit budget side-condition
`l + 2 ≤ L`.  Therefore the drain level `l` sits at

```
l ≤ L - 2,   hence the terminal seed level   l + 1 ≤ L - 1,
   and   numHours = l + 1 ≤ L - 1 < L + 1,
```

so the deepening budget `numHours` fits COMFORTABLY inside the `L+1`-hour schedule (with two hours
of slack: the band-top hour `l` and the top hour `L` are never spent as deepening notches).  This is
the honest accounting `entryFloor_hour_arithmetic` records.

## What this file delivers

1. `allBiasedMainAbove_zero` / `bandConfined_entry` — the entry floor `l₀ = 0` (the trivially-honest
   floor, wired as `HourInduction.BandConfined 0`, the `hStart` shape).
2. `phaseInit3_main_bias_index_zero` — the SHARP phaseInit-3 provenance (entry index literally `0`).
3. `entryFloor_hour_arithmetic` — the hour accounting `numHours = l + 1`, `l + 1 ≤ L - 1 < L + 1`.
4. `hourInduction_from_entry` — the headline wiring: `hourInduction` instantiated at the entry floor
   `l₀ = 0` and the matched hour count `numHours = l + 1`, delivering the terminal seed
   `BandConfined (l + 1)` failure `≤ η` over the Phase-3→5 horizon.

NEW file; no existing file is edited; no sorry/admit/axiom/native_decide.

Reference: Doty et al. (arXiv:2106.10201v2), §6 (the hour-by-hour band collapse) — base case.
-/
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.HourInduction

namespace ExactMajority

open scoped ENNReal NNReal BigOperators

namespace EntryFloor

variable {L K : ℕ}

open MinorityFloorGap (AllBiasedMainAbove)

/-! ## Part 1 — the trivially-honest entry floor `l₀ = 0`.

`AllBiasedMainAbove 0 c` is unconditional: the dyadic exponent index lives in `Fin (L+1)`, so
`0 ≤ i.val` always.  This is the base case the moving-band induction starts from — and it is honest
precisely BECAUSE the frozen `phaseInit 3` conversion seeds every biased Main at index `0` (Part 2),
so no biased Main can sit below `0` at the Phase-3 entry. -/

/-- **The entry floor `AllBiasedMainAbove 0` holds for ANY config.**  Every biased Main's dyadic
exponent index is a `Fin (L+1)`, so its value is `≥ 0` unconditionally.  This is the §6 base case at
`l₀ = 0`. -/
theorem allBiasedMainAbove_zero (c : Config (AgentState L K)) :
    AllBiasedMainAbove (L := L) (K := K) 0 c :=
  fun _ _ _ _ _ _ => Nat.zero_le _

/-- **The entry band floor, in the `HourInduction.BandConfined` shape (= `hStart` at `l₀ = 0`).**
`BandConfined 0 c` is `AllBiasedMainAbove 0 c`, which holds for any `c` — the Phase-3 entry floor the
hour induction consumes as its base case. -/
theorem bandConfined_entry (c : Config (AgentState L K)) :
    HourInduction.BandConfined (L := L) (K := K) 0 c :=
  allBiasedMainAbove_zero c

/-! ## Part 2 — the SHARP phaseInit-3 provenance (entry index literally `0`).

The frozen `phaseInit 3` (Transition.lean) performs the smallBias → dyadic conversion.  We prove the
sharp fact: a *biased* Main (one whose `smallBias.val ≠ 3`, the conversion's non-zero branch)
entering Phase 3 gets dyadic index EQUAL to `0`.  So the entry floor is not merely vacuously `≥ 0`;
it is ACHIEVED at the init value `0` by the deterministic conversion. -/

/-- **The phaseInit-3 bias conversion produces dyadic index `0` (the deterministic entry value).**
For a Main `a` entering Phase 3 (`p.val = 3`), the resulting bias is one of `.dyadic .neg ⟨0,_⟩`,
`.dyadic .pos ⟨0,_⟩`, or `.zero` — so if it is dyadic at all, its exponent index is exactly `0`.
This is the smallBias → dyadic conversion's STARTING exponent: every biased Main enters the §6
dyadic track at the SHALLOWEST level `0` (bias `±1`).  Hence the Phase-3 entry floor is `l₀ = 0`,
achieved (not merely `≥ 0`). -/
theorem phaseInit3_main_bias_index_zero (p : Fin 11) (hp : p.val = 3)
    (a : AgentState L K) (ha : a.role = Role.main)
    (ss : Sign) (i : Fin (L + 1))
    (hbias : (phaseInit L K p a).bias = Bias.dyadic ss i) :
    i.val = 0 := by
  -- Unfold `phaseInit` at `p.val = 3`; the Main branch sets `bias := newBias`.
  have h1 : ¬ p.val = 1 := by omega
  have h2 : ¬ p.val = 2 := by omega
  simp only [phaseInit, h1, h2, hp, dif_pos, dif_neg, ha] at hbias
  -- `newBias` is `.dyadic _ ⟨0,_⟩` or `.zero`; match the conversion's branches.
  by_cases hlt : a.smallBias.val < 3
  · simp only [hlt, if_true] at hbias
    -- `.dyadic .neg ⟨0,_⟩ = .dyadic ss i` forces `i = ⟨0,_⟩`.
    rw [Bias.dyadic.injEq] at hbias
    obtain ⟨_, hi⟩ := hbias
    rw [← hi]
  · simp only [hlt, if_false] at hbias
    by_cases hgt : a.smallBias.val > 3
    · simp only [hgt, if_true] at hbias
      rw [Bias.dyadic.injEq] at hbias
      obtain ⟨_, hi⟩ := hbias
      rw [← hi]
    · -- the `= 3` branch produces `.zero`, contradicting a dyadic bias.
      simp only [hgt, if_false] at hbias
      exact absurd hbias (by simp)

/-! ## Part 3 — the hour arithmetic (`numHours = l + 1`, `l + 1 ≤ L - 1 < L + 1`).

The induction deepens `l₀ → l₀ + numHours`.  The downstream seed consumers require the TERMINAL
floor at level `l + 1`.  With `l₀ = 0` this forces `numHours = l + 1`.  The §6 schedule budgets one
hour per level and the clock carries `L + 1` hours; `SeedExport`'s `l+1` drain needs the budget
side-condition `l + 2 ≤ L`, placing `l ≤ L - 2`.  Hence `numHours = l + 1 ≤ L - 1 < L + 1` — the
deepening fits inside the schedule with two hours of slack. -/

/-- **The §6 hour accounting (honest arithmetic).**  Given the seed-budget side-condition
`l + 2 ≤ L` (`SeedExport`'s `l+1` drain availability), with the entry floor `l₀ = 0` and the matched
hour count `numHours = l + 1` (so the terminal floor `l₀ + numHours = l + 1` is exactly the seed
level), the deepening budget satisfies `numHours ≤ L - 1 < L + 1` — comfortably inside the
`(L+1)`-hour schedule. -/
theorem entryFloor_hour_arithmetic (l : ℕ) (hlL2 : l + 2 ≤ L) :
    (0 : ℕ) + (l + 1) = l + 1 ∧ l + 1 ≤ L - 1 ∧ L - 1 < L + 1 := by
  refine ⟨by omega, by omega, by omega⟩

/-! ## Part 4 — the headline wiring (`hourInduction` from the entry floor).

Compose Part 1 (the entry floor `l₀ = 0`) with `HourInduction.hourInduction`, at the matched hour
count `numHours = l + 1`, to deliver the terminal seed `BandConfined (l + 1)` failure `≤ η` over the
Phase-3→5 horizon.  The per-hour notch-deepening tail `hHour` (the landed `SeedExport` drain) and the
budget are carried, exactly as `hourInduction` expects; this file supplies the BASE CASE. -/

/-- **`hourInduction_from_entry` — the §6 induction from the Phase-3 entry floor (headline).**

Instantiates `HourInduction.hourInduction` at the honest entry floor `l₀ = 0` (Part 1, the
phaseInit-3-seeded floor) and the matched hour count `numHours = l + 1` (Part 3), so the deepened
terminal floor is exactly the seed level `l + 1`.  From any start config `c₀` (the entry floor is
unconditional), the per-hour drain tails `hHour`, the horizon decomposition, and the union budget,
the failure to reach the terminal seed band `BandConfined (l + 1)` over the Phase-3→5 horizon is
`≤ η`.  This wires the base case onto the moving-band induction's headline. -/
theorem hourInduction_from_entry
    (l hourLen phase3to5Time : ℕ) (δ η : ℝ≥0∞) (c₀ : Config (AgentState L K))
    (hHour : ∀ (h : ℕ), ∀ x, HourInduction.BandConfined (L := L) (K := K) (0 + h) x →
      ((NonuniformMajority L K).transitionKernel ^ hourLen) x
        {c | ¬ HourInduction.BandConfined (L := L) (K := K) (0 + h + 1) c} ≤ δ)
    (hHorizon : phase3to5Time = hourLen * (l + 1))
    (hBudget : ((l + 1 : ℕ) : ℝ≥0∞) * δ ≤ η) :
    ((NonuniformMajority L K).transitionKernel ^ phase3to5Time) c₀
      {c | ¬ HourInduction.BandConfined (L := L) (K := K) (0 + (l + 1)) c} ≤ η :=
  HourInduction.hourInduction (L := L) (K := K) 0 hourLen (l + 1) phase3to5Time δ η c₀
    (bandConfined_entry c₀) hHour hHorizon hBudget

end EntryFloor

end ExactMajority
