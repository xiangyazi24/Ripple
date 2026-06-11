
---

## DoublingEdges.lean — hour-gated top edge + occupancy verdict (2026-06-10)

The §6 "doubling chain passes through every level, band is 3 levels" positional content of
`BandEdges.lean` (`MajorityTopEdge`, `MinorityTopEdge`, `TwoLevelOccupancy`) is now discharged to the
honest FROZEN-rule mechanism, splitting deterministic from probabilistic content.

**Hour-gated TOP edge (the headline, FULLY PROVEN).** The doubling/split move `phase3CancelSplit`
raises a level ONLY under the guard `partner.hour.val > i.val`, so the raised level `i+1 ≤
partner.hour.val` — the top edge IS the hour ceiling. `phase3CancelSplit_preserves_top_edge`: inputs
`≤ top` + all `hour.val ≤ top` ⟹ outputs `≤ top`. This is the exact mirror of the landed FLOOR
`MinorityFloorGap.cancelSplit_preserves_index_floor`, proven exhaustively over the frozen branches.
The snapshot consumer predicate is `AllBiasedMainBelow top c` (front at the band top — the within-hour
clock-front fact); from the SINGLE ceiling, `majorityTopEdge_of_hourCeiling` +
`minorityTopEdge_of_hourCeiling` produce BOTH carried top-band readouts.

**Occupancy verdict: CONDITIONAL.** `TwoLevelOccupancy` is a simultaneous-population SNAPSHOT, hence a
probabilistic timing fact — NOT a deterministic ledger. The deterministic chain content is the no-jump
SOURCE `raise_traces_to_predecessor` (mass at `i+1` traces to `i`, never skips). The snapshot is
delivered conditionally via the named event `PredecessorLevelsCoPopulated` (both levels populated at
the routing instant). This is the honest line between what the FROZEN rules give for free (the top
edge) and what needs a within-hour concentration argument (the occupancy).

**Wired:** `phase6_to_phase7_of_doubling_edges` / `phase6To7_surface_of_doubling_edges` feed
`BandEdges.phase6_to_phase7_of_seed_edges`, producing `EliminatorMargins.Phase6To7Structure σ E c`
from the seed + the one hour ceiling + the co-population event. Carried residual reduced to: hour
ceiling (deterministic clock-front front-position) + co-population timing event (probabilistic).

**Audit.** 7/7 theorems axiom-clean ⊆ [propext, Classical.choice, Quot.sound]; 0
sorry/admit/axiom/native_decide; lake env lean clean (uisai2 shm, v4.30.0 + mathlib c5ea00351c28).
