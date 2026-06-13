/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Package B2 — HONEST Phase-7/8 eliminator-margin witnesses for `WorkInputsV51`

This file is append-only (it edits NO existing file) and REDOES the V51 witness fields
`hwit7` / `hwit8` HONESTLY, removing the globally-false all-Main bridges that the audited
`PkgBAtoms` package carried.

## The defect being repaired

`PkgBAtoms.hwit7_of_phase6To7Structure_honest` and `PkgBAtoms.hwit8_of_phase7To8Structure_honest`
produced the V51 witness fields through the bridges

    Phase7Honest n b → Phase7AllMain n b        and        Phase8Honest n b → Phase8AllMain n b

(`PkgBAtoms:48` / `PkgBAtoms:72`).  Those bridges are GLOBALLY FALSE: `HonestWindows`
(`incompat_allMain_with_chain_roles`, source-verified) shows the all-Main windows are
UNSATISFIABLE on every reachable post-role-split full-population config — the chain permanently
keeps `clockCount ≥ n/5 > 0` clocks coexisting with the mains.  So the all-Main hypothesis can
never be discharged on the chain; it was a packaging shortcut, not a real input.

## The honest redo — what actually carries the margins

The eliminator margins are about counts of MAIN-role agents at specific bias levels.  The two
landed structural Posts

    EliminatorMargins.Phase6To7Structure σ E7   (gap-1 eliminator ≥ E7 at each live minority level)
    EliminatorMargins.Phase7To8Structure σ E8   (above-level survival ≥ E8 at each live minority level)

are the honest §6/§7 chain outputs (the precise named eliminator-count remainder).  They are
predicates on a config that read ONLY the Main sub-population finsets (`minorityAt7`,
`elimGap1`, `minorityAt`, `elimAbove`).  They are carried verbatim — the point of this file is to
remove the all-Main bridge, NOT to re-prove §7.

The deterministic minority-witness extractors are ALREADY window-free:

* `EliminatorMargins.exists_minorityAt_of_minorityU_pos`  — `minorityU σ b ≥ 1 → ∃ i, minorityAt σ i ≥ 1`;
* `EliminatorMargins.exists_minorityAt7_of_minorityU_pos` — `minorityU σ b ≥ 1 → ∃ j, minorityAt7 σ j ≥ 1`.

Both extract the Main role from `minoritySt` itself (`minoritySt σ a = (a.role = main ∧ …)`), so
NO role window is needed.  This is the count-budget resolution: the Main role travels INSIDE the
minority potential `minorityU`, not in a separate all-Main window.  Non-Main agents coexisting in
`b` are irrelevant to these per-level Main counts (the finsets are Main-filtered), so the margin
floors hold whether or not non-Main agents coexist — exactly as long as the count budget is honest
(`mainCount ≤ n`, which the chain carries together with `mainCount ≥ n/3`).

## The slot-7 mass↔Main-minority carry (the ONE honest §6/§7 input that replaces the bridge)

The V51 `hwit7` field is keyed off the σ-class MASS potential `classMassN σ b ≥ 1`, whereas the
window-free extractor consumes the Main minority COUNT `minorityU σ b ≥ 1`.  `classMassN` reads
only `bias` (`agentClassMass` ignores `role`, `Phase7Convergence:1251`), so positive class mass
could in principle be carried by a non-Main σ-dyadic agent.  The honest §6/§7 chain fact that the
surviving σ-class mass on the phase-7 window is Main-carried is supplied as the NAMED structural
carry

    hMainMass7 : Phase7Honest n b → classMassN σ b ≥ 1 → minorityU σ b ≥ 1

(the precise remainder, named not faked — it is the honest replacement for the all-Main bridge,
and unlike that bridge it IS satisfiable on the chain).  The audited package buried exactly this
content inside the unsatisfiable `Phase7AllMain` window; here it is exposed as a chain-honest
hypothesis.  The slot-8 field is keyed directly off `minorityU σ b ≥ 1`, so it needs no such carry.

## Fields produced

* `hwit7` (`WorkInputsV51.hwit7`, `FinalAssemblyV51:135`) — via `hwit7_honest`;
* `hwit8` (`WorkInputsV51.hwit8`, `FinalAssemblyV51:152`) — via `hwit8_honest`.

The budget fields `hpt7` / `hpt8` are NOT touched: the audit found their arithmetic
(`PkgBAtoms.hpt7_budget_alpha` / `hpt8_budget_recut`) clean, and they never referenced an all-Main
window.

No `Phase7AllMain` / `Phase8AllMain` bridge appears below (grep-verifiable absent).
Single-file `lake env lean` build; `#print axioms ⊆ {propext, Classical.choice, Quot.sound}`.
-/

import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.EliminatorMargins
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.HonestWindows

namespace ExactMajority
namespace PkgB2HonestMargin

open scoped ENNReal NNReal BigOperators

variable {L K : ℕ}

/-! ## Slot 7 witness field (`WorkInputsV51.hwit7`), HONEST.

The all-Main bridge of `PkgBAtoms.hwit7_of_phase6To7Structure_honest` is replaced by the
chain-honest mass↔Main-minority carry `hMainMass7`.  The minority LEVEL is then produced by the
window-free extractor `EliminatorMargins.exists_minorityAt7_of_minorityU_pos`, and the gap-1
eliminator floor is supplied by the carried §6 Post `Phase6To7Structure`. -/

/-- Produces the EXACT `WorkInputsV51.hwit7` field shape, honestly, on `Phase7Honest`.

Field produced: `WorkInputsV51.hwit7`
  (`FinalAssemblyV51:135–139`: `Phase7Honest n b → classMassN σ b ≥ 1 → ∃ i j, i+1 = j ∧
  1 ≤ minorityAt7 σ j .sum count ∧ E7 ≤ elimGap1 σ i .sum count`).

Honest hypotheses (NO `Phase7AllMain` bridge):
* `hMainMass7` — the §6/§7 chain carry `classMassN σ ≥ 1 → minorityU σ ≥ 1` on the honest window
  (the surviving σ-class mass is Main-carried);
* `hStruct7` — the carried §6 Post `Phase6To7Structure σ E7` on the honest window. -/
theorem hwit7_honest {n E7 : ℕ} {σ : Sign}
    (hMainMass7 : ∀ b : Config (AgentState L K),
      HonestWindows.Phase7Honest (L := L) (K := K) n b →
      Phase7Convergence.classMassN σ b ≥ 1 →
      Phase7Convergence.minorityU (L := L) (K := K) σ b ≥ 1)
    (hStruct7 : ∀ b : Config (AgentState L K),
      HonestWindows.Phase7Honest (L := L) (K := K) n b →
      EliminatorMargins.Phase6To7Structure (L := L) (K := K) σ E7 b) :
    ∀ b : Config (AgentState L K), HonestWindows.Phase7Honest (L := L) (K := K) n b →
      Phase7Convergence.classMassN σ b ≥ 1 →
      ∃ i j : Fin (L + 1), i.val + 1 = j.val ∧
        1 ≤ (Phase7Convergence.minorityAt7 (L := L) (K := K) σ j).sum b.count ∧
        E7 ≤ (Phase7Convergence.elimGap1 (L := L) (K := K) σ i).sum b.count := by
  intro b hb7 hmass
  -- The honest mass→Main-minority carry turns positive class MASS into a positive Main minority
  -- COUNT; the window-free extractor then exposes a minority LEVEL `j`.
  have hminorU : Phase7Convergence.minorityU (L := L) (K := K) σ b ≥ 1 := hMainMass7 b hb7 hmass
  obtain ⟨j, hj⟩ := EliminatorMargins.exists_minorityAt7_of_minorityU_pos σ b hminorU
  -- The carried §6 Post supplies the gap-1 partner level `i = j − 1` with `≥ E7` eliminators.
  obtain ⟨i, hg1, helim⟩ := hStruct7 b hb7 j hj
  exact ⟨i, j, hg1, hj, helim⟩

/-! ## Slot 8 witness field (`WorkInputsV51.hwit8`), HONEST.

No mass carry is needed: the V51 `hwit8` field is keyed directly off the Main minority COUNT
`minorityU σ b ≥ 1`.  The minority LEVEL is produced by the window-free extractor
`EliminatorMargins.exists_minorityAt_of_minorityU_pos`, and the above-level eliminator floor is
supplied by the carried §7 Post `Phase7To8Structure`.  No all-Main bridge — and unlike the audited
package, even the carried §7 Post is taken on the honest window. -/

/-- Produces the EXACT `WorkInputsV51.hwit8` field shape, honestly, on `Phase8Honest`.

Field produced: `WorkInputsV51.hwit8`
  (`FinalAssemblyV51:152–156`: `Phase8Honest n b → minorityU σ b ≥ 1 → ∃ i,
  1 ≤ minorityAt σ i .sum count ∧ E8 ≤ elimAbove σ i .sum count`).

Honest hypothesis (NO `Phase8AllMain` bridge):
* `hStruct8` — the carried §7 Post `Phase7To8Structure σ E8` on the honest window. -/
theorem hwit8_honest {n E8 : ℕ} {σ : Sign}
    (hStruct8 : ∀ b : Config (AgentState L K),
      HonestWindows.Phase8Honest (L := L) (K := K) n b →
      EliminatorMargins.Phase7To8Structure (L := L) (K := K) σ E8 b) :
    ∀ b : Config (AgentState L K), HonestWindows.Phase8Honest (L := L) (K := K) n b →
      Phase7Convergence.minorityU σ b ≥ 1 →
      ∃ i : Fin (L + 1),
        1 ≤ (Phase8Convergence.minorityAt (L := L) (K := K) σ i).sum b.count ∧
        E8 ≤ (Phase8Convergence.elimAbove (L := L) (K := K) σ i).sum b.count := by
  intro b hb8 hminor
  -- Window-free extractor: the Main role travels inside `minorityU` (via `minoritySt`).
  obtain ⟨i, hmini⟩ := EliminatorMargins.exists_minorityAt_of_minorityU_pos σ b hminor
  -- The carried §7 Post supplies the `≥ E8` above-level eliminators at that level.
  exact ⟨i, hmini, hStruct8 b hb8 i hmini⟩

/-! ## The honest survival constant.  Re-stated here so the slot-8 honest re-cut `14n/75` is
visible alongside the witnesses (the documented survival floor, not `n/5`).  This is the same
clean fact `PkgBAtoms.fourteen_seventyfive_le_one_fifth` carried; re-proved locally so this file is
self-contained for the slot-8 margin constant. -/

/-- The honest slot-8 survival constant `14n/75` is below the landed consumer's `n/5`
side-condition. -/
theorem honest_E8_le_one_fifth (n : ℕ) :
    (14 : ℝ) * (n : ℝ) / 75 ≤ (1 : ℝ) * (n : ℝ) / 5 := by
  have hn0 : (0 : ℝ) ≤ n := by exact_mod_cast Nat.zero_le n
  nlinarith

#print axioms hwit7_honest
#print axioms hwit8_honest
#print axioms honest_E8_le_one_fifth

end PkgB2HonestMargin
end ExactMajority
