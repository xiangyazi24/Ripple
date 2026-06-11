
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

---

## PaperRegime.lean — ChatGPT paper-faithfulness audit verdicts (2026-06-11)

New append-only file `Probability/PaperRegime.lean` answers the ChatGPT faithfulness audit
(`/tmp/gpt_faithfulness.out`, 2026-06-09).  Each auditor claim was VERIFIED against the actual
source BEFORE acting; the actual source wins over the auditor's reconstruction (the auditor could
not fetch `DotyParams.lean` / this doc, so several "HIGH" flags were unverified suspicions).

| # | Auditor claim | Source verdict (file:line) | Action taken |
|---|---|---|---|
| 1 | Thm 6.2 object: paper's `0.92|M'|` is MAJORITY-sign Mains at THREE exact levels `{l,l+1,l+2}`; Lean's `hConfine` is broad (both-sign, index `<L`). HIGH divergence. | **PARTIAL-RIGHT.** `UsefulMainFloor.lean:197` `hConfine = 0.92·|M| ≤ usefulMains.sum` is genuinely broad (both-sign, all index `<L`). BUT the file already documents `M' ⊆ usefulMains` (`UsefulMainFloor.lean:182,196`), and `MarginLedgers.lean:255` already carries the sign-aware `MainConfinementProfile` (`majorityProfileMass σ` / `minorityProfileMass σ`). The MISSING piece was only the **3-level restriction** `{l,l+1,l+2}`. | Defined the paper-faithful object `PaperRegime.majorityConfined3 σ l c` (majority-sign Mains at the three exact levels) + `Theorem62Paper` structure (confinement + mass-above `≤0.06|M|` + minority-small `≤0.12|M|`). PROVED the projection chain: `majorityConfined3 ≤ usefulMains` (`majorityConfined3_le_usefulMains`, needs `l+2<L`) ⟹ `theorem62Paper_implies_broad_floor` (faithful ⟹ broad `hConfine`); and `majorityConfined3 ≤ majorityProfileMass` ⟹ `mainConfinementProfile_of_paper` (faithful ⟹ the sign-aware eliminator-ledger A-shape that drives `majorityProfileMass_floor`/`4n/45`). `hConfine` re-stated honestly as the Phase-5 sampling projection of the faithful object. |
| 2 | `K=45`: paper proof needs `k=45` minutes/hour at `p=1`; Lean polymorphic in arbitrary `K`. HIGH (stronger-than-paper ⟹ probably false unless width lemmas carry `45≤K`). | **RIGHT (diagnosis), but no bug.** Confirmed: `ClockFrontShape.capMinute = K*(L+1)` and ALL §6 width/seam lemmas are polymorphic in `K` (`DotyParams.lean` threads `{L K : ℕ}` with NO `K`-lower-bound hypothesis; the headline `DotyTimeHeadline.lean:324` is polymorphic in `{L K n}`). Polymorphism over `K` means the lemmas HOLD for the paper's `K=45` (it is an instance) — not false; it is an unstated regime tie. | Added the named predicate `PaperRegime.DotyRegime n L K` collecting the regime ties in ONE inspectable place: `hLlog : L = Nat.clog 2 n`, `hK : 45 ≤ K`, `hN : N₀ ≤ n`. Documented as THE regime hypothesis to thread into the concrete headline. Accessors `DotyRegime.{L_eq_clog,K_ge_45,N₀_le,two_le_n}`. |
| 3 | `wp=3/200`: HIGH if it is a transition probability (the clock drip rate). | **WRONG.** The FROZEN protocol transition is DETERMINISTIC per pair (`Transition.lean`: every `PhaseNTransition : AgentState → AgentState → AgentState × AgentState`; no `Prob`/`PMF`/`p`-rate anywhere in `Protocol/`). The only randomness is uniform pair selection. `wp` enters ONLY as the analysis step-count `DotyParams.w n = ⌊3n/200⌋` (`DotyParams.lean:44`) and the MGF window-rung ratio `uW = 2(1+ε)·wp = 603/20000` (`DotyParams.lean:454`). It is an ANALYSIS constant, not a drip rate. Paper's "drip probability `p=1`" = the deterministic frozen rule. | Documented in `PaperRegime.lean` Part 5; closed with the proven identity `wp_is_analysis_constant : DotyParams.uW = 2·(1+1/200)·(3/200)` exhibiting `wp` purely as an MGF quantity. |
| 4 | `L = ⌈log₂ n⌉` carried only in comments, not as a hypothesis. Medium. | **RIGHT.** `AgentState` carries `L` as a bare parameter (comments say `L=⌈log₂n⌉`); the headline does not tie it. | Included as `DotyRegime.hLlog : L = Nat.clog 2 n` (`Nat.clog 2 n = ⌈log₂ n⌉`). |

**Build/audit.** `Probability/PaperRegime.lean` — single-file `lake env lean` clean + `lake build`
target EXIT 0 (3417 jobs, uisai2 /dev/shm, v4.30.0 @ mathlib c5ea0035). All exported theorems
`#print axioms ⊆ [propext, Classical.choice, Quot.sound]`; 0 sorry/admit/axiom/native_decide;
lint-clean (no longLine in this file). Append-only; no existing file edited.

**Scope note (honest).** `PaperRegime.lean` is a *surface*/*definitions* file: it states the
paper-faithful object and PROVES the deterministic projections (faithful ⟹ broad floor; faithful ⟹
sign-aware A-shape; the regime predicate; the wp identity). It does NOT discharge the probabilistic
CONTENT of Theorem 6.2 (`hConfine3`/`hMassAbove`/`hMinoritySmall` remain carried whp facts inside
`Theorem62Paper`, exactly as `hConfine` was carried in `UsefulMainFloor`) — that bias-ledger
collapse is the same genuinely-new probabilistic residual flagged in `UsefulMainFloor.lean`'s header.
What changed: the carried object is now the paper-faithful majority-sign 3-level one, the broad floor
is a PROVEN consequence of it, and the regime ties are collected in one named predicate.
