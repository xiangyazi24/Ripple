# HANDOFF: per-level localization B/C (family3 letter, task 4d2eff92, 2026-06-10)

Source: ChatGPT Pro, 14,375 B via network. Verbatim below.

---

## STATUS (2026-06-10, agent: BandLocalization.lean landed, EXIT_0, axiom-clean)

New file `Probability/BandLocalization.lean` (append-only; no existing file edited). Single-file
`lake env lean … BandLocalization.lean` EXIT_0; `#print axioms` on all 5 headlines ⊆
[propext, Classical.choice, Quot.sound]; no sorry/admit/axiom/native_decide.

Faithful to the blueprint's short verdict (B/C are band-position, NOT counting; global 4n/15 budget
already proved in `MarginLedgers.majorityProfileMass_floor`).

**Band-position structure defined (honest Props, documented provenance):**
- `MajorityBandAtGap1 σ E c` — every gap-1 predecessor level `i = j−1` of a live minority level `j`
  carries `≥ E` σ-opposite eliminators (`= MarginLedgers.majorityAtExp σ i = Phase7Convergence.elimGap1 σ i`, defeq).
- `MinorityConfinedGap1 σ c` — every live minority level `j` has a gap-1 predecessor index in range
  (`j.val ≥ 1`), the band-floor confinement.
- `Phase6BandPositionFacts σ E c` — bundle of the two; definitionally assembles into `Phase6HighMassDrained`.
- `SurvivalBandAbove σ E c` (C-side) — surviving above-level eliminator LOWER bound after the bounded
  Phase-7 same-level spend; defeq to `Phase7SurvivalUpperBounds`.

**Localizations closed deterministically:**
- B: `phase6HighMassDrained_of_bandPosition` (band ⟹ `Phase6HighMassDrained`) and
  `phase6_to_phase7_of_bandPosition` (wired through the landed adapter ⟹ `Phase6To7Structure`).
- C: `cancelSplit_gap1_preserves_smaller_sign` — the FROZEN `cancelSplit` gap-1 reading proven directly
  (smaller-index eliminator re-emerges at incremented index, same sign → gap-1 preserves σ-opposite
  supply; per the blueprint's §2 verdict, gap-2 is NOT an obstruction, only same-level cancellation
  spends). `phase7SurvivalUpperBounds_of_survivalBand` + `phase7_to_phase8_of_survivalBand` (wired
  through the landed adapter ⟹ `Phase7To8Structure`).

**Named residual — what Phase 6/7's convergence proof must additionally export:**
- Phase-6 Post must export `Phase6BandPositionFacts σ E c`: (1) `MinorityConfinedGap1` (the drain
  separates the two bands by one step, no live minority at bottom index 0); (2) `MajorityBandAtGap1`
  (the per-level ROUTING — `doSplit` magnitude-halving deposits eliminators at the partner band one
  index below each minority; the GLOBAL 4n/15 budget is already proved, only routing is missing).
- Phase-7 Post must export `SurvivalBandAbove σ E c` (the surviving above-level eliminator LOWER
  bound; the landed `lemma_7_5/7_6` are minority-survival UPPER bounds only).

---

[intro]
I’ll inspect the newly landed ledgers and margin structures first, then cross-check the paper §7 wording so the localization claim is not inferred from comments alone.

[answer]
## Short verdict

For **B**, the missing fact is not “there are many majority eliminators globally”; `MarginLedgers.majorityProfileMass_floor` already proves that. The remaining localization is a **band-position / Phase-6 Post export**: the majority mass must be located at the specific gap-1 predecessor level of each live minority level. This is exactly the carried field

```lean
MarginLedgers.Phase6HighMassDrained
```

not a new global concentration theorem.

For **C**, the paper’s accounting is essentially “spent eliminators ≤ eliminated minorities,” but Lean still needs a **per-level dynamic ledger**, not just one global subtraction. The good news: gap-2 does **not** create an obstruction; under the frozen `cancelSplit`, gap-2 preserves or increases the σ-opposite eliminator supply. The only genuine eliminator loss is same-level cancellation. So C is deterministic transition bookkeeping once B and the Phase-7 survival bounds are present; it is not a new probability tail.

---

## 1. B: what the paper’s localization really is

The branch’s ledger already separates the two parts correctly.

### Already proved: global majority-eliminator supply

`MarginLedgers` defines the exponent profile split:

```lean
def minorityProfileMass (σ : Sign) (c : Config (AgentState L K)) : ℕ :=
  ∑ i : Fin (L + 1), (minorityAtExp σ i).sum c.count

def majorityProfileMass (σ : Sign) (c : Config (AgentState L K)) : ℕ :=
  ∑ i : Fin (L + 1), (majorityAtExp σ i).sum c.count
```

and proves the exact Main partition

```lean
mainCount c = majorityProfileMass σ c + minorityProfileMass σ c + zeroMainCount c
```

via `main_profile_partition`. fileciteturn84file0L74-L84MainConfinementProfile` packages the Theorem-6.2-shaped assumptions: `n/3 ≤ mainCount`, `0.92·mainCount ≤ majorityProfileMass + minorityProfileMass`, and `minorityProfileMass ≤ 0.12·mainCount`. fileciteturn85file0L58-L73 From these, the file proves

```lean
theorem majorityProfileMass_floor ...
  (4 : ℝ) * (n : ℝ) / 15 ≤ (majorityProfileMass σ c : ℝ)
```

i.e. the global ≥ `4n/15` majority-eliminator budget. fileciteturn85file0L is not implied by that global budget. The file states it exactly:

```lean
def Phase6HighMassDrained (σ : Sign) (E : ℕ) (c : Config (AgentState L K)) : Prop :=
  ∀ j : Fin (L + 1),
    1 ≤ (Phase7Convergence.minorityAt7 σ j).sum c.count →
    ∃ i : Fin (L + 1),
      i.val + 1 = j.val ∧
      E ≤ (Phase7Convergence.elimGap1 σ i).sum c.count
```

fileciteturn for every live minority level `j`, there is a gap-1 predecessor `i = j−1`, and that predecessor level has at least `E` eliminators.

That is a **band-position fact**: Phase 6 must force the live minority band and the majority eliminator band to be aligned one index apart. A global sum `majorityProfileMass ≥ 4n/15` alone cannot prove it; all the mass could sit at a useless exponent. `MarginLedgers` explicitly says the global mass “could in principle sit at a non-partner level,” and the missing field is the Phase-6 high-mass-drain confinement that routes it to the partner level. fileciteturn`Phase6Convergence.lean` gives the faithful split semantics. `doSplit` takes a biased Main at index `j` and, when fueled by an appropriate Reserve, produces two Mains at index `j+1`; i.e. it halves the magnitude / increases the Lean index. fileciteturn top-of-band progress: a high Main at `j = l−1` splits to index `l`, no longer high. fileciteturn91file0L185-L204 saying “for every live minority level `j`, the majority mass is at `j−1`.” Therefore Phase 6 should export exactly this:

```lean
/-- Phase-6 Post field needed by Lemma 7.4 localization. -/
def Phase6HighMassDrained (σ : Sign) (E : ℕ) (c : Config (AgentState L K)) : Prop :=
  ∀ j : Fin (L + 1),
    1 ≤ (Phase7Convergence.minorityAt7 (L := L) (K := K) σ j).sum c.count →
    ∃ i : Fin (L + 1),
      i.val + 1 = j.val ∧
      E ≤ (Phase7Convergence.elimGap1 (L := L) (K := K) σ i).sum c.count
```

which is already the definition in `MarginLedgers`. fileciteturn85file0L81-L87

Then the adapter is already proved:

```lean
theorem phase6_to_phase7_eliminator_margin_of_confinement
    ...
    (hA : MainConfinementProfile σ n c)
    (h6 : Phase6Convergence.Phase6Win n c)
    (hPost6 : Phase6HighMassDrained σ E c)
    (hE : (E : ℝ) ≤ 4 * n / 15) :
    EliminatorMargins.Phase6To7Structure σ E c
```

It uses the global budget only as consistency, then returns `hPost6` for each live minority level. fileciteturn85file0Lcondition bookkeeping from the Phase-6 high-mass drain, not new probability.

---

## 2. C: spent-eliminator accounting from Phase 7 to Phase 8

### What the frozen transition says

The `cancelSplit` rule has exactly the three relevant opposite-sign cases:

```lean
-- same exponent
i = j      → both zero

-- gap 1
i + 1 = j  → smaller-index agent increments, other zero

-- gap 2
i + 2 = j  → smaller-index agent increments,
             larger-index agent takes smaller-index sign
```

filecite as the minority sign and σ.flip as the majority/eliminator sign:

* **same-level cancel** spends one eliminator and removes one minority;
* **gap-1** removes the minority but preserves the eliminator sign, moving it up one level;
* **gap-2** converts the minority into the eliminator sign, so σ-opposite supply is preserved or grows.

`MarginLedgers` records this exact reading: same-level is the only eliminator loss, gap-1 preserves the eliminator, and gap-2 preserves or grows σ-opposite supply. fileciteturn global subtraction?

Almost, but not quite in the form Lean needs.

The paper-level intuition is:

```text
surviving eliminators ≥ initial eliminators − spent eliminators
spent eliminators ≤ minority eliminated
remaining demand ≤ remaining minority
```

and with constants:

```text
4n/15 − O(0.08|M|) ≥ n/5
```

But the Phase-8 consumer needs a **per-level** statement:

```lean
∀ i,
  minorityAt σ i ≥ 1 →
  E ≤ elimAbove σ i
```

not merely a global count of remaining eliminators. That is why `MarginLedgers` defines:

```lean
def Phase7SurvivalUpperBounds (σ : Sign) (E : ℕ) (c : Config (AgentState L K)) : Prop :=
  ∀ i : Fin (L + 1),
    1 ≤ (Phase8Convergence.minorityAt σ i).sum c.count →
    E ≤ (Phase8Convergence.elimAbove σ i).sum c.count
```

fileciteturn86file02. Gap-2 helps. The remaining work is a **per-level spend ledger**: for each threshold `i`, prove that the above-level eliminator supply at Phase-8 entry is the Phase-7-entry above/gap supply minus only same-level spends, and those spends are bounded by minority eliminations. This is deterministic transition bookkeeping plus the landed minority-survival upper bounds; not a new stochastic engine.

`MarginLedgers` is explicit that the landed `lemma_7_5/7_6` facts are minority-survival upper bounds, not eliminator lower bounds, so the lower-bound survival field is still carried as `Phase7SurvivalUpperBounds`. fileciteturn85file0L163hStart : EliminatorMargins.Phase6To7Structure σ E c_start)
    (h7win : Phase7Convergence.Phase7AllMain n c)
    (hSurvive : Phase7SurvivalUpperBounds σ E c)
    (hE : (E : ℝ) ≤ n / 5) :
    EliminatorMargins.Phase7To8Structure σ E c
```

and it simply returns `hSurvive` for each live Phase-8 minority level. fileciteturn86file0L18-L43

---

## 3. Target Lean statements for B

### B.1 Minimal target: export the Post field from Phase 6

This is the most direct target:

```lean
/-- Phase 6 exports the Lemma-7.4 per-level localization. -/
theorem phase6_highMassDrained_of_phase6Post
    {L K n E : ℕ} {σ : Sign} {c : Config (AgentState L K)}
    (hA : MarginLedgers.MainConfinementProfile (L := L) (K := K) σ n c)
    (h6 : Phase6Convergence.Phase6Win (L := L) (K := K) n c)
    -- whatever the landed Phase-6 Post currently says, e.g. `highMass l = 0`
    -- plus the band-position facts from the Phase-6 proof:
    (hBand : Phase6BandPositionFacts (L := L) (K := K) σ E c)
    (hE : (E : ℝ) ≤ (4 : ℝ) * (n : ℝ) / 15) :
    MarginLedgers.Phase6HighMassDrained (L := L) (K := K) σ E c := by
  -- show every live minority level j has predecessor i=j-1
  -- and the σ-opposite mass at i is ≥ E.
  sorry
```

The honest missing piece is `Phase6BandPositionFacts`. It should not be vague; the exact useful form is simply the final field itself:

```lean
/-- The Phase-6 band-position fact needed for Lemma 7.4. -/
def Phase6BandPositionFacts (σ : Sign) (E : ℕ) (c : Config (AgentState L K)) : Prop :=
  ∀ j : Fin (L + 1),
    1 ≤ (Phase7Convergence.minorityAt7 (L := L) (K := K) σ j).sum c.count →
    ∃ i : Fin (L + 1),
      i.val + 1 = j.val ∧
      E ≤ (Phase7Convergence.elimGap1 (L := L) (K := K) σ i).sum c.count
```

which is definitionally the same as `Phase6HighMassDrained`. The proof should live near Phase 6’s convergence/Post, not in `PhaseFloors`.

### B.2 Existing consumer adapter

Once `Phase6HighMassDrained` is available, the following is already landed:

```lean
theorem phase6_to_phase7_eliminator_margin_of_confinement
    ...
    (hPost6 : Phase6HighMassDrained σ E c)
    ...
    EliminatorMargins.Phase6To7Structure σ E c
```

fileciteturn85file0L119drop engine:

```lean
theorem lemma7_4_phase7_elimGap1_floor
    ...
    (hPhase6Post : Phase6To7Structure σ E c)
    (hminor : 1 ≤ Phase7Convergence.classMassN σ c)
    ...
    ∃ i j,
      i.val + 1 = j.val ∧
      1 ≤ minorityAt7 σ j ∧
      E ≤ elimGap1 σ i
```

fileciteturn88file0L22-L41 Target Lean statements for C

### C.1 Per-rule spend ledger

The first missing deterministic lemma should be local, over `cancelSplit`:

```lean
/--
Phase-7 per-pair eliminator-spend ledger.

For a fixed minority sign `σ` and threshold level `i`, the above-level σ-opposite
eliminator count can decrease only in same-level cancellation, and each such decrease
is charged to one σ-minority disappearance. Gap-1 preserves σ-opposite supply; gap-2
preserves or grows it.
-/
theorem cancelSplit_elimAbove_spend_le_minority_drop
    {L K : ℕ} (σ : Sign) (i : Fin (L + 1))
    (s t : AgentState L K)
    (hsM : s.role = Role.main) (htM : t.role = Role.main) :
    -- schematic: the exact RHS should be a pair-level minority-drop/spend counter
    pairElimAboveLoss σ i (cancelSplit L K s t) s t
      ≤ pairMinorityDrop σ i (cancelSplit L K s t) s t := by
  -- cases on s.bias, t.bias
  -- use the frozen cancelSplit branches:
  -- same-level: loss=1, minorityDrop=1
  -- gap-1: loss=0, minorityDrop=1
  -- gap-2: loss=0 or negative, minorityDrop/nonincrease sufficient
  -- identity/same-sign/zero: loss=0
  sorry
```

I would avoid defining this in terms of subtraction of finset sums at first; define small pair-level indicator functions for “σ-opposite above i and not full” and “σ-minority at/above i,” then prove the inequality by exhaustive cases.

### C.2 Config-level Phase-7 survival ledger

Then lift it through `Phase7Transition`:

```lean
/--
Config-level Phase-7 eliminator survival: along a Phase7AllMain trajectory,
above-level eliminator supply at threshold i is initial supply minus at most
the number of minorities eliminated at/near i.
-/
theorem phase7_elimAbove_survival_of_spend_ledger
    {L K n E : ℕ} {σ : Sign}
    {c_start c_end : Config (AgentState L K)}
    (hStart : EliminatorMargins.Phase6To7Structure (L := L) (K := K) σ E c_start)
    (hReach7 :
      Phase7ReachableWithinWindow (L := L) (K := K) n c_start c_end)
    (hSurvivalUpper :
      Phase7MinoritySurvivalUpperBounds (L := L) (K := K) σ n c_start c_end)
    (hE : (E : ℝ) ≤ (1 : ℝ) * (n : ℝ) / 5) :
    MarginLedgers.Phase7SurvivalUpperBounds (L := L) (K := K) σ E c_end := by
  -- per level i:
  --   use hStart on the Phase-7-entry minority/margin band,
  --   subtract same-level spends bounded by minority eliminated,
  --   use hSurvivalUpper to bound remaining demand.
  sorry
```

The exact existing end field is:

```lean
def Phase7SurvivalUpperBounds (σ : Sign) (E : ℕ) (c : Config (AgentState L K)) : Prop :=
  ∀ i,
    1 ≤ (Phase8Convergence.minorityAt σ i).sum c.count →
    E ≤ (Phase8Convergence.elimAbove σ i).sum c.count
```

fileciteturnvivalUpperBounds` is proved, the existing adapter gives:

```lean
theorem phase7_to_phase8_eliminator_margin_of_phase7
    ...
    (hSurvive : Phase7SurvivalUpperBounds σ E c)
    ...
    EliminatorMargins.Phase7To8Structure σ E c
```

fileciteturn86file0L27-L43

Then `lemma7_6_phase8_elimAbove_floor` consumes `Phase7To8Structure`:

```lean
theorem lemma7_6_phase8_elimAbove_floor
    ...
    (hPhase7Post : Phase7To8Structure σ E c)
    (hmin : 1 ≤ minorityAt σ i)
    ...
    E ≤ elimAbove σ i
```

fileciteturn88file0L43-L56

And `phase8_hdrop_wired

---

## 5. New probability versus deterministic bookkeeping

### B: no new probability, but Phase-6 Post must export a stronger deterministic/band-position fact

The probability for Phase 6 is the high-mass drain itself. Once the Phase-6 drain has succeeded, the localization should be a deterministic statement about where the remaining minority and majority profiles sit. The current code does not export that as a Post, so `Phase6HighMassDrained` remains carried. fileciteturn ledger

The stochastic part of Phase 7 is already the drain/survival upper bound. What is missing is the lower-bound side for eliminators after accounting for spends. Gap-2 is not an obstruction because it preserves or grows the σ-opposite supply; same-level cancellation is the only loss. This is exactly why the target field should be `Phase7SurvivalUpperBounds`, not another tail estimate. fileciteturn85file0L142-L168

---

## Recommended implementation order

1. **Prove/export B as a Phase-6 Post field.**  
   This is the current bottleneck for Phase 7. The exact field already exists: `MarginLedgers.Phase6HighMassDrained`.

2. **Prove local `cancelSplit` spend lemmas.**  
   Work pair-level first, directly from the frozen `cancelSplit` cases. Use `cancelSplit` semantics from `Transition.lean`: same-level, gap-1, gap-2. fileciteturn92file0L ledger with the landed minority survival upper-bound theorem shape to prove `Phase7SurvivalUpperBounds`.

4. **Use existing adapters.**  
   Do not reopen `PhaseFloors`: the hdrop consumers are already wired through `EliminatorMargins` and `MarginLedgers`.

---

## UPDATE (2026-06-10, agent: BandRouting.lean landed — residual #2 part (1) CLOSED, EXIT_0, axiom-clean)

New file `Probability/BandRouting.lean` (append-only; no existing file edited). Single-file
`lake env lean … BandRouting.lean` EXIT_0; `#print axioms` on all 7 headlines ⊆
[propext, Classical.choice, Quot.sound]; no sorry/admit/axiom/native_decide.

This file EXPORTS `BandLocalization.Phase6BandPositionFacts` from the LANDED Phase-6 Post instead of
assuming it. Survey verdict: the landed Phase-6 convergence (`Phase6Convergence.phase6Convergence'`)
has `Post = (highMass l c = 0)`, read by `Phase6Convergence.phase6Post_iff` as **every biased Main
has exponent index ≥ l** (the band FLOOR). That is enough to PROVE half of the residual:

**Stage 1 — `MinorityConfinedGap1` GENUINELY PROVEN (no carried assumption).**
- `exists_minority_witness`: a live minority level `j` (`1 ≤ (minorityAt7 σ j).sum c.count`) yields an
  actual biased-Main witness `a ∈ c`, `a.bias = dyadic σ j` (positive finset count-sum ⟹ member).
- `minorityConfinedGap1_of_post (hl : 1 ≤ l) (hPost : highMass l c = 0)`: the witness has index `≥ l ≥ 1`,
  so `j.val ≥ 1` and the gap-1 predecessor `j − 1` exists. **Closes part (1) of `Phase6BandPositionFacts`
  from the landed drain Post + `1 ≤ l` only.**

**Stage 2 — the genuine routing residual + honest per-level constant.**
- `GapAlignedElimFloor σ E c` (defeq `BandLocalization.MajorityBandAtGap1`): the ONE carried routing
  field — `≥ E` σ-opposite eliminators AT each live minority's predecessor `j − 1`. Honest obstruction:
  the band floor `highMass l = 0` does NOT pin a SPECIFIC partner level; the global budget
  `majorityProfileMass ≥ 4n/15` (PROVED, `MarginLedgers.majorityProfileMass_floor`) could sit anywhere
  in the band. This is the irreducible per-level routing the `doSplit` magnitude-halving achieves.
- `exists_band_level_floor` + `exists_band_level_floor_4n45`: the honest DETERMINISTIC content the
  global budget DOES give once Theorem-6.2 confines the majority mass to a 3-level band finset `S`
  (`MajoritySupportedOn`, `S.card ≤ 3`): by pigeonhole SOME band level carries `≥ 4n/45`. This pins
  the per-level constant (`4n/45 = (4n/15)/3`) but does NOT give the per-PARTNER-level placement
  (that remains `GapAlignedElimFloor`). `majorityAtExp = elimGap1` and
  `majorityProfileMass = ∑ elimGap1` are defeq (verified), so the pigeonhole consumes the landed floor.

**Stage 3 — assembly + wiring.**
- `phase6BandPositionFacts_of_post (hl) (hPost) (hRoute)`: `Phase6BandPositionFacts` from the Phase-6
  Post (part 1 proven) + the routing field (part 2 carried).
- `phase6_to_phase7_of_post`: end-to-end through `BandLocalization.phase6_to_phase7_of_bandPosition`
  to `EliminatorMargins.Phase6To7Structure` — band FLOOR discharged from the drain Post, GLOBAL budget
  from `hA`, only per-level routing `hRoute` carried.

**Net for residual #2:** part (1) `MinorityConfinedGap1` fully closed (was assumed, now proven from
the landed Phase-6 Post); part (2) `MajorityBandAtGap1` reduced to the single named per-level routing
field `GapAlignedElimFloor` with its constant pinned at `4n/45` by the band pigeonhole. The honest
remaining brick is the Phase-6 `doSplit`-routing-to-partner-level invariant (the per-level placement,
not the per-level count) — the precise thing the convergence proof must additionally maintain.
