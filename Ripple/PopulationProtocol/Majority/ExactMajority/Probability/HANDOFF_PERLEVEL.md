
---

## DoublingEdges.lean — the hour-gated TOP edge + the occupancy verdict (2026-06-10)

`BandEdges` carried three positional residuals (`MajorityTopEdge`, `MinorityTopEdge`,
`TwoLevelOccupancy`). `DoublingEdges.lean` discharges them to the extent the FROZEN rules honestly
allow, splitting the deterministic per-rule content from the probabilistic timing content.

**Hour-gated TOP edge (deterministic, FULLY PROVEN — mirror of the landed FLOOR).**
The §6 doubling/split move `phase3CancelSplit` (Rule 4) raises `i → i+1` ONLY under the guard
`partner.hour.val > i.val`, so the raised level `i+1 ≤ partner.hour.val`. Hence the per-rule TOP-edge
ledger `phase3CancelSplit_preserves_top_edge`: **if every biased input sits at level `≤ top` AND every
input `hour.val ≤ top`, every biased output sits at level `≤ top`** — no agent is ever raised above the
hour ceiling. This is the honest hour-gated top edge, the exact mirror of
`MinorityFloorGap.cancelSplit_preserves_index_floor` (the FLOOR), proven exhaustively over the frozen
branches (cancel/no-op preserve; split raises under the hour guard).

The SNAPSHOT predicate the routing consumer needs is `AllBiasedMainBelow top c` (every biased Main in
`c` at index `≤ top` — the within-hour clock-front content: front sits at the band top). It discharges
BOTH carried readouts from a SINGLE ceiling: `majorityTopEdge_of_hourCeiling` ⟹
`BandEdges.MajorityTopEdge σ top c`, `minorityTopEdge_of_hourCeiling` ⟹ `BandEdges.MinorityTopEdge σ
top c`. So with `top = l+2` the 3-level majority band `{l ≤ i ≤ l+2}` AND the minority confinement
`{l+1, l+2}` both follow from the one hour ceiling.

**Occupancy verdict (HONEST: conditional on a named timing event).** `TwoLevelOccupancy` is a SNAPSHOT
fact (both predecessor levels `{l, l+1}` carry `≥ E` at the SAME config) — a probabilistic timing
statement, NOT a deterministic ledger. The deterministic content the chain provides is the no-jump
SOURCE: `raise_traces_to_predecessor` (corollary of `phase3CancelSplit_no_jump`) — mass at `i+1` either
was already at `i+1` or came from `i = (i+1)−1`; the chain never skips a level. Converting that to the
snapshot needs a within-hour timing event (both levels populated SIMULTANEOUSLY at the routing
instant). So the honest occupancy is delivered CONDITIONALLY via the named event
`PredecessorLevelsCoPopulated σ E l c` (defeq `BandEdges.TwoLevelOccupancy`), and
`twoLevelOccupancy_of_coPopulated` makes the conditional explicit.

**Wired:** `phase6_to_phase7_of_doubling_edges` — from the `l+1` seed + `hA` + `h6` + the single hour
ceiling `AllBiasedMainBelow (l+2)` + the co-population event, the carried `MinorityTopEdge` is PRODUCED
from the hour ceiling and `TwoLevelOccupancy` from the timing event, feeding
`BandEdges.phase6_to_phase7_of_seed_edges` ⟹ `EliminatorMargins.Phase6To7Structure σ E c`.
`phase6To7_surface_of_doubling_edges` additionally exports `MajorityTopEdge σ (l+2) c` +
`MinorityTopEdge σ (l+2) c` (both from the same ceiling). The carried residual is now reduced to: the
hour ceiling `AllBiasedMainBelow (l+2)` (deterministic, the clock-front front-position fact) + the
co-population timing event (probabilistic). The hour-gated top edge mechanism is FULLY PROVEN off the
FROZEN split guard.

**Audit.** All 7 `DoublingEdges` theorems `#print axioms` ⊆ `[propext, Classical.choice, Quot.sound]`
(the two non-classical: `phase3CancelSplit_preserves_top_edge`, `raise_traces_to_predecessor` use only
`[propext, Quot.sound]`); 0 sorry/admit/axiom/native_decide; single-file `lake env lean` clean
(uisai2 /dev/shm, v4.30.0 + mathlib c5ea00351c28 bucket).
