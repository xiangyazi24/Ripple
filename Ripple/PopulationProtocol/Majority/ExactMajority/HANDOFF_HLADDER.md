# HANDOFF: hLadder reachable-relative E4 (family letter, task d9ac167d, 2026-06-10)

Source: ChatGPT Pro, 14,192 B via network. Verbatim below.

---

[intro]
I’ll inspect the new expected-time/recovery files first, then check the transition rules that matter for “clock preservation” and “eventual phase-10 backup.”

A key obstruction is already visible: the current `hLadder` theorem is universal over `StableDoneᶜ`, not reachability-filtered. An “all-backup from arbitrary state” proof would need to handle configurations with no clocks or no enabled phase-advance path, which the protocol does not guarantee.

[answer]
## Bottom line

The **all-backup route is not honest** for the current faithful protocol. It would require a deterministic statement like “every not-stable configuration eventually reaches Phase 10 or stabilizes first,” but that is false without additional regime hypotheses. A configuration can have no clocks, or fewer than two clocks, or be in a non-backup phase with no enabled counter progress. The protocol does not contain a global “force Phase 10 from anywhere” rule. Phase 10 spreads once it exists, but existence of one Phase-10 agent is not guaranteed from an arbitrary reachable/non-stable state by deterministic progress alone.

So the correct `hLadder` remains the paper-faithful one:

```lean
∀ b ∈ StableDoneᶜ, LadderData L K init b Brecover
```

or, better, a reachable/invariant-relative version of this. It must classify a not-done state into either a timed clock ladder with floors, or a Phase-10 backup ladder. The timed branches are still needed.

---

## 1. What deterministic facts are actually available?

### Available, deterministic

**Cardinality preservation.** The recovery files repeatedly use fixed-card invariants, and `AllClockGEpCard` is explicitly `AllClockGEp p c ∧ c.card = n`. Its support closure combines role/phase preservation with `stepDistOrSelf_support_card_eq`. fileciteturn74Fin 11`.** This is built into `AgentState.phase`; all phase motion is by `advancePhase`, `phaseInit`, or the phase epidemic. The dispatcher uses `max s.phase t.phase` and then runs inits over the interval. fileciteturn82file0 For the post-role-split all-clock regime, `RecoveryBridges` packages this as `AllClockGEpCard` support closure and all-time preservation for `3 ≤ p`. fileciteturn66file0L171-L202 -10 epidemic entry is real.** If an interaction’s epidemic/init stage sends either participant to phase 10, both participants are put on the backup track in that same interaction; lower-phase participants are reinitialized by `enterPhase10`. fileciteturn83file0 floor for arbitrary reachable states.** `RecoveryBridges` is explicit: `AllClockGEpCard` is a post-role-split regime, not a property of arbitrary reachable not-done states, which may still contain main/reserve roles or be mid-seam. fileciteturn66file0L171-L183Phase-10 presence does not automatically mean `S1` or `Tie1plus`.** It gives a path toward the backup regime by epidemic, but the Phase-10 expected-time branches need a classified Phase-10 start shape, namely the majority/tie backup predicates. `DotyExpectedTime` records these as `phase10Majority` and `phase10Tie`, with expected-time witnesses. filecite without a clock-clock supply.** The E3 progress mechanism is explicitly based on clock-clock meetings, with rate `mC(mC−1)/(n(n−1))`; if `mC < 2`, this rate is zero. fileciteturn70file0. The timed branches are not redundant.

`RecoveryClass` has four branches:

```lean
| bigClockTimed
| tinyClockTimed
| phase10Majority
| phase10Tie
```

Each constructor currently carries a witness

```lean
expectedHitting K b (StableDone L K init) ≤ B
```

fileciteturn69file0L184  k : ℕ
  S : ℕ → Set (Config (AgentState L K))
  hlink : ∀ i, i < k → ∀ y ∈ S i,
    expectedHitting K y (S (i + 1)) ≤ β i
  hb : b ∈ S 0
  hsum : ∑ j ∈ Finset.range k, β j ≤ Brecover
```

fileciteturn68file0The timed branches are exactly where E3 applies:

```lean
timed_phase_progress_real_tinyClock
timed_phase_progress_real_bigClock
```

The tiny-clock branch gives `≤ counterMax * n²`; the big-clock branch gives `≤ counterMax * 11*n`. Both require `AllClockGEpCard p n`, a counter-sum cap, and the floor hypothesis `mC ≤ posClockCount p b`; big-clock additionally needs `n/5 ≤ mC`. fileciteturn74file0L these timed links by a deterministic bound to Phase 10, but no such bound exists for arbitrary not-done configurations.

---

## 3. Why “all-backup from arbitrary c” fails

The proposed proof idea is:

> every not-stable state eventually enters Phase 10 via counter timeout, because some counter keeps decrementing.

The transition semantics do not support this.

Counters decrement only through clock-driven rules. For the E3 timed progress theorem, the drop rate is based on ordered pairs of **positive-counter phase-`p` clocks**; the proof aggregates over `presentPosPairs`. file relevant clocks has no uniform counter-drain rate. A state with no clocks has no counter-drain route at all. Phase-10 error entry exists, but only when protocol guards trigger it; it is not a universal fallback transition.

Thus the deterministic lemma

```lean
expectedHitting K c Phase10Regime ≤ D
```

for every arbitrary `c ∈ StableDoneᶜ` is not true in this formalization without extra assumptions.

A weaker true target would be:

```lean
theorem expected_to_phase10_or_progress_from_timed_regime
    {L K n p mC counterMax : ℕ}
    (hp : p ∈ ({5,6,7,8} : Finset ℕ)) (hp3 : 3 ≤ p)
    (hmC : 2 ≤ mC) (hmCn : mC ≤ n) (hn : 2 ≤ n)
    (hfloor : ∀ b, ConditionalPhaseProgress.AllClockGEpCard
        (L := L) (K := K) p n b →
        mC ≤ ConditionalPhaseProgress.posClockCount (L := L) (K := K) p b)
    (c : Config (AgentState L K))
    (hInv : ConditionalPhaseProgress.AllClockGEpCard (L := L) (K := K) p n c)
    (hcap :
      ConditionalPhaseProgress.clockCounterSumAt (L := L) (K := K) p c ≤ counterMax * mC) :
    expectedHitting (NonuniformMajority L K).transitionKernel c
      (ConditionalPhaseProgress.Engine.potBelow
        (ConditionalPhaseProgress.clockCounterSumAt (L := L) (K := K) p) 1)
      ≤ ((counterMax : ℕ) : ℝ≥0∞) * ((n * n : ℕ) : ℝ≥0∞) :=
  ConditionalPhaseProgress.timed_phase_progress_real_tinyClock ...
```

which is already essentially landed. filecite design

The current final theorem consumes:

```lean
(hLadder : ∀ b ∈ (StableDone L K init)ᶜ,
  LadderData L K init b (Brecover : ℝ≥0∞))
```

and then derives the uniform recovery cap through `doty_recovery_bound_via_ladder`. fileciteturn but too strong semantically unless the ladder classifier covers all synthetic `AgentState` configurations, not just reachable ones. The more honest theorem surface is reachable-relative:

```lean
def ReachableFrom (L K : ℕ) (init c : Config (AgentState L K)) : Prop :=
  (NonuniformMajority L K).Reachable init c
```

Then add an invariant-relative recovery theorem:

```lean
theorem doty_recovery_bound_via_ladder_on_reachable
    {L K n : ℕ}
    (init : Config (AgentState L K)) (Brecover : ℝ≥0∞)
    (hDone : MeasurableSet (StableDone L K init))
    (hAbs : ∀ x ∈ StableDone L K init,
      (NonuniformMajority L K).transitionKernel x (StableDone L K init)ᶜ = 0)
    (hReachClosed :
      ∀ b, ReachableFrom L K init b →
        (NonuniformMajority L K).transitionKernel b
          {x | ¬ ReachableFrom L K init x} = 0)
    (hLadder :
      ∀ b,
        ReachableFrom L K init b →
        b ∈ (StableDone L K init)ᶜ →
        LadderData L K init b Brecover) :
    ∀ b,
      ReachableFrom L K init b →
      b ∈ (StableDone L K init)ᶜ →
      expectedHitting (NonuniformMajority L K).transitionKernel b
        (StableDone L K init) ≤ Brecover := by
  intro b hbReach hbBad
  exact (recoveryClass_of_ladderData (n := n) init b Brecover hDone hAbs
    (hLadder b hbReach hbBad)).expectedHitting_le
```

To plug this into E4’s block restart, also add a reachable-relative version of the split-geometric recovery theorem, or carry the invariant `ReachableFrom init` in the block restart. The generic shape should mirror `expectedHitting_seqcomp_on`, already landed for invariant-relative ladders. fileciteturn66file Kernel α α) [IsMarkovKernel K]
    (J : α → Prop)
    (hJClosed : ∀ b, J b → K b {x | ¬ J x} = 0)
    (c₀ : α) (hJ0 : J c₀)
    {Done : Set α} (hDone : MeasurableSet Done)
    (hAbs : ∀ x ∈ Done, K x Doneᶜ = 0)
    (Tgood sRecover : ℕ)
    (δgood B : ℝ≥0∞)
    (hBfin : B ≠ ⊤)
    (hspos : 0 < sRecover)
    (hs : B * 2 ≤ (sRecover : ℝ≥0∞))
    (hδ : (K ^ Tgood) c₀ Doneᶜ ≤ δgood)
    (hRecover : ∀ b, J b → b ∈ Doneᶜ → expectedHitting K b Done ≤ B) :
    expectedHitting K c₀ Done
      ≤ (Tgood : ℝ≥0∞) + δgood * sRecover * (1 - (1 / 2 : ℝ≥0∞))⁻¹ := by
  -- same proof as `expected_time_from_whp_and_recovery`,
  -- but use invariant-relative bad-block bound:
  -- from b with J b, Markov half-tail applies;
  -- support closure keeps restarts inside J.
  sorry
```

This avoids demanding ladders for unreachable garbage states.

---

## 5. What a ladder should look like

### Timed-phase ladder branch

For a state already in a timed clock regime:

```lean
ConditionalPhaseProgress.AllClockGEpCard p n b
```

with `p ∈ {5,6,7,8}`, `3 ≤ p`, and floor

```lean
mC ≤ ConditionalPhaseProgress.posClockCount p b
```

define:

```lean
S 0 = {c | ConditionalPhaseProgress.AllClockGEpCard p n c ∧
           c = b or same phase-rung condition}
S 1 = ConditionalPhaseProgress.Engine.potBelow
        (ConditionalPhaseProgress.clockCounterSumAt p) 1
...
S k = StableDone L K init
```

The first link uses:

```lean
ConditionalPhaseProgress.timed_phase_progress_real_bigClock
```

or

```lean
ConditionalPhaseProgress.timed_phase_progress_real_tinyClock
```

depending on whether the floor is `n/5 ≤ mC` or only `2 ≤ mC`. The big-clock cap is `counterMax * 11*n`; the tiny-clock cap is `counterMax * n²`. fileciteturn74file0L### Phase-10 branch

For a state in the all-phase-10 backup regime, classify into either:

```lean
S1 n
Tie1plus n
```

or the repo’s actual Phase-10 predicates, and use the Phase-10 expected stabilization caps. `DotyExpectedTime` records the expected bounds as:

* majority case: `≤ 3*n²*(1 + 2 log n)`;
* tie case: `≤ 2*n²*(1 + 2 log n)`.

fileciteTime file also explains that these are interaction-count bounds and that the backup has cancel/coupon stages. fileciteturnp-floor alternative versus all-backup

### All-backup route

Lean cost looks tempting, but the central deterministic statement is false or at least far stronger than the protocol semantics:

```lean
∀ c ∈ StableDoneᶜ, expectedHitting K c Phase10Regime ≤ O(n * counterMax * (L+1))
```

This fails for arbitrary configurations without enough clocks and without an error-trigger guard. It also does not match the current E3 engines, which need `AllClockGEpCard` and clock floors.

### Paper-faithful whp-floor route

This is the honest route:

1. On the good role-split event, Lemma 5.2 gives enough clocks.
2. Clock roles are preserved after the post-role-split regime; `AllClockGEpCard` is support-closed. file; the expectation cost is multiplied by small bad-event mass in the E4 tail-sum split.

This matches `RecoveryBridges`’ Stage-4 note: the genuine residual is the phase-regime classification plus the per-phase clock floors; the engines above it are discharged. fileciteturn68file0L47-L82

### Recommendation

Use the **reachable-relative paper-faithful ladder**.

Do not collapse to all-backup. Instead, change the final E4 surface from a universal `StableDoneᶜ` ladder to a reachable/invariant-relative ladder, then prove `hLadder` by cases:

```lean
theorem reachable_hLadder
    {L K n Brecover : ℕ}
    (init b : Config (AgentState L K))
    (hReach : (NonuniformMajority L K).Reachable init b)
    (hBad : b ∈ (StableDone L K init)ᶜ)
    -- role-split/clock-floor data, phase-regime classifier:
    (hClass : ReachablePhaseRegimeClassification L K n init b)
    (hFloors : ReachableClockFloors L K n b) :
    LadderData L K init b (Brecover : ℝ≥0∞) := by
  -- cases on hClass:
  -- 1. big-clock timed phase: build ladder using timed_phase_progress_real_bigClock.
  -- 2. tiny-clock timed phase: build ladder using timed_phase_progress_real_tinyClock.
  -- 3. phase10 majority: use Phase10ExpectedTime majority cap.
  -- 4. phase10 tie: use Phase10ExpectedTime tie cap.
  sorry
```

The two missing protocol predicates should be made explicit:

```lean
structure ReachablePhaseRegimeClassification
    (L K n : ℕ) (init b : Config (AgentState L K)) : Prop where
  card_n : b.card = n
  branch :
    TimedBigClockRegime L K n b ∨
    TimedTinyClockRegime L K n b ∨
    Phase10MajorityRegime L K n init b ∨
    Phase10TieRegime L K n init b

structure ReachableClockFloors
    (L K n : ℕ) (b : Config (AgentState L K)) : Prop where
  big :
    ∀ p, TimedBigClockRegime L K n b →
      ∃ mC, n / 5 ≤ mC ∧ mC ≤ n ∧
        ∀ y, ConditionalPhaseProgress.AllClockGEpCard (L := L) (K := K) p n y →
          mC ≤ ConditionalPhaseProgress.posClockCount (L := L) (K := K) p y
  tiny :
    ∀ p, TimedTinyClockRegime L K n b →
      ∃ mC, 2 ≤ mC ∧ mC ≤ n ∧
        ∀ y, ConditionalPhaseProgress.AllClockGEpCard (L := L) (K := K) p n y →
          mC ≤ ConditionalPhaseProgress.posClockCount (L := L) (K := K) p y
```

This is the exact formal version of the paper’s recovery logic: good clock floors feed fast timed ladders; bad/tiny regimes feed slow recovery; Phase 10 handles actual backup states.

---

## 7. Answer to the key question

**No, the Lean `RecoveryClass` should not drop timed branches.** The all-backup route is not supported by the transition semantics. The right simplification is different: make `hLadder` reachable-relative and explicit, so it does not pretend to classify arbitrary impossible states.

The remaining protocol work is exactly:

1. `ReachablePhaseRegimeClassification`: reachable not-done states fall into timed clock regime or Phase-10 backup regime.
2. `ReachableClockFloors`: good role-split floors propagate into the timed regimes; bad floors are charged to tiny/backup recovery.
3. A reachable-relative E4 recovery theorem so `hLadder` only has to classify states that can actually occur from `init`.

Everything else—seqcomp, ladder telescope, clock-role preservation after role split, and E3/E2 expected-time caps—is already in place.

---

## STATUS — LANDED (2026-06-10): `Probability/ReachableLadder.lean`

All four deliverables implemented in the new append-only file
`Probability/ReachableLadder.lean` (no existing file edited). Single-file
`lake env lean … ReachableLadder.lean` EXIT_0; all seven headlines `#print axioms`
⊆ `[propext, Classical.choice, Quot.sound]`; no sorry/admit/axiom/native_decide.

**Reachability notion used.** The repo's own kernel reachability predicate
`Protocol.Reachable` (= `Relation.ReflTransGen StepRel`, `Basic/PopulationProtocol.lean:89`),
named `ReachableFrom L K init c := (NonuniformMajority L K).Reachable init c`. The
closure fact `hReachClosed` is the THEOREM `reachableFrom_kernel_closed`: from the landed
bridge `stepDistOrSelf_support_reachable` (every one-step support point is deterministically
reachable) + `ReflTransGen.trans`, fed through the generic kernel-power support-preservation
template at `t = 1`. So `hReachClosed` is no longer a hypothesis — it is discharged.

1. **`ReachableFrom`, `reachableFrom_step_closed`, `reachableFrom_kernel_closed`** — the
   reachability predicate + its one-step support/kernel closure.
2. **`expected_time_from_whp_and_recovery_on`** — the `J`-invariant-relative split-geometric
   E1 composition, mirroring `expectedHitting_seqcomp_on`'s `_on` pattern. Built from new
   `_on` block atoms (`bad_block_geometric_from_on`, `tail_le_block_on`,
   `expectedHitting_split_geometric_on`, `block_half_from_recovery_expected_on`) assembled
   from the landed `ExpectedHitting` `_on` engine; `J`'s one-step closure keeps restarts
   inside `J`, so the Markov half-tail only needs the `J`-relative recovery cap.
3. **`doty_recovery_bound_via_ladder_on_reachable`** (verbatim §4 shape) + the
   **`reachable_hLadder`** §6 skeleton: the 4-way classifier
   `ReachablePhaseRegimeClassification` (a `Type`-valued inductive with the four §6 regime
   constructors, each carrying its per-state `LadderData` keyed by the regime witness) and
   the floor data `ReachableClockFloors`. `reachable_hLadder` extracts the carried ladder
   per branch (the engine each branch uses is documented per constructor).
4. **`doty_expected_time_reachable`** — the final E4 theorem, conclusion identical to
   `doty_expected_time_via_ladder` (`E[T] ≤ (21·C0 + 4·Cbad)·n·(L+1)`), but the recovery
   half runs `expected_time_from_whp_and_recovery_on` with `J := ReachableFrom L K init`
   on the reachable not-done states, whose per-state caps are the reachable ladder telescope
   (`doty_recovery_bound_via_ladder_on_reachable`). Consumes the two honest residuals
   instead of the universal `hLadder`.

**What the two residuals demand (precisely).**
- `ReachablePhaseRegimeClassification L K n init b Brecover`: a deterministic 4-way
  classification of every *reachable not-done* `b` into bigClock-timed / tinyClock-timed /
  phase-10-majority / phase-10-tie, **with the per-state `LadderData` to `StableDone`** for
  that regime. The ladder's first link is the named E3/E2 cap
  (`timed_phase_progress_real_{big,tiny}Clock`, `phase10_expected_stabilization{,_tie}_O_nsq_log`);
  the remaining links chain through the phase progress sets via the landed
  seqcomp/telescope. Discharge = the phase-regime classification of reachable configs +
  the ladder-spine construction (future work).
- `ReachableClockFloors L K n init b Brecover`: the Lemma-5.2 clock-floor propagation per
  timed branch (`n/5 ≤ mC` big, `2 ≤ mC` tiny), each propagating to every `AllClockGEpCard`
  invariant state via `posClockCount`. Discharge = Lemma 5.2 floor propagation (future work).

Everything above these two residuals — the reachability layer, the `_on` split-geometric,
the seqcomp/telescope transfer (`RecoveryBridges`), the whp composition — is discharged.

---

## STATUS — LANDED (2026-06-10): `Probability/RegimeClassification.lean` (residual #4 attack)

Append-only new file `Probability/RegimeClassification.lean` (no existing file edited).
Attacks the TWO honest residuals left by `ReachableLadder.lean` — the regime classification
and the clock floors — by REPLACING the opaque carried-`LadderData` field of the four
`ReachableLadder` regime structures with explicit ladder-SPINE constructions. Single-file
`lake env lean … RegimeClassification.lean` EXIT_0; all twelve headlines `#print axioms`
⊆ `[propext, Classical.choice, Quot.sound]` (the two `floorProp_*` even drop
`Classical.choice`); no sorry/admit/axiom/native_decide.

**(a) Regime content, ladder-free.** `TimedBigClockData`, `TimedTinyClockData`,
`Phase10MajorityData`, `Phase10TieData` — the regime CONTENT (phase membership +
`AllClockGEpCard` invariant + Lemma-5.2 floor + counter cap, resp. `S1`/`Tie1plus`) WITHOUT
the carried ladder. The ladder is now a CONCLUSION, not an input.

**(b) Per-regime ladder spines (the substance).** `ladderData_of_two_rung` (the 2-rung
spine builder: `Dom → Prog → StableDone`) + the four instantiations
`ladderData_of_{bigClock,tinyClock,phase10Majority,phase10Tie}`. Each BUILDS the
`LadderData` to `StableDone` from the landed E3/E2 cap as the FIRST link
(`timed_phase_progress_real_{big,tiny}Clock` ≤ `counterMax·11n` / `counterMax·n²`;
`phase10_expected_stabilization{,_tie}_O_nsq_log` ≤ `3n²(1+2log n)` / `2n²(1+2log n)`) and the
`RecoveryBridges` telescope (`expectedHitting_telescope_from_start`) to assemble. The SINGLE
isolated residual per regime is the final-rung bridge `progressSet (potBelow Φ 1) ⟹
StableDone` (`βbridge`) — supplied as an explicit hypothesis; everything else is discharged.

**(c) Floor propagation.** `clockRole_preserved_all_time` (re-export of
`RecoveryBridges.allClockGEpCard_pow_preserved`: the FROZEN-transition "clocks never
destroyed at phase ≥ 3" all-time kernel fact) + `floorProp_{big,tiny}Clock` (the Lemma-5.2
floor as the genuinely-true UNIFORM-over-`AllClockGEpCard`-invariant-states fact, for the
regime's OWN phase). **Honest non-claim:** `ReachableLadder.ReachableClockFloors`'s `big`/`tiny`
fields quantify a FREE outer phase `p` (`∀ p, …Regime → ∃ mC, … ∀ y, AllClockGEpCard p n y → …`),
while a single regime carries a floor only for its OWN `h.p`; no clock floor holds at every
phase simultaneously, so that structure is NOT fake-discharged. The genuinely-true content is
the per-regime `floorProp_*`, which is exactly what the timed E3 engines consume via `hfloor`.

**(d) Checkpoint-conditional classifier.**
`regimeClassification_{bigClock,tinyClock,phase10Majority,phase10Tie}` assemble the
`ReachablePhaseRegimeClassification` from the ladder-free `*Data` + the per-regime bridge
(the carried `ladder` field now BUILT via (b)). **Honest scope:** the remaining `hClassify`
residual of `doty_expected_time_reachable` is exactly "for every reachable not-done `b`,
EXHIBIT one of the four `*Data` witnesses + its bridge". This is honest for states reachable
from a GOOD role-split checkpoint (the whp `RoleSplitGood` event, `clockCount_linear_of_RoleSplitGood`
→ `n/5 ≤ |Clock|`); the UNCONDITIONAL classifier (arbitrary reachable states) is OUT OF SCOPE
and honestly so — pre-role-split states hold main/reserve roles (no `AllClockGEpCard` invariant,
no floor) and a FAILED role split has no deterministic `2 ≤ mC`. The unconditional version is a
whp statement conditioned on the checkpoint event, documented as such in the file's closing note.

**Net narrowing of the E4 surface:** the regime ladders are no longer opaque carried fields —
they are theorems modulo (i) the per-regime final-rung bridge `potBelow Φ 1 ⟹ StableDone`
and (ii) the deterministic floor VALUE `mC` (Lemma 5.2). Those two are the honest, named,
genuinely-protocol residuals; the spine, the telescope wiring, the clock-role preservation,
and the classifier assembly are discharged.

---

## STATUS — LANDED (2026-06-10): `Probability/StableBridges.lean` (tip #4a — final-rung bridges)

Append-only new file (no existing file edited). Discharges the single explicit residual `hbridge`
(`progressSet (potBelow Φ 1) ⟹ StableDone`) of `RegimeClassification.lean`'s four `ladderData_of_*`
builders, for the two regimes where it is honestly true, and re-shapes the spine for the two where it
is FALSE. Single-file `lake env lean … StableBridges.lean` EXIT_0; 12 headlines `#print axioms` ⊆
`[propext, Classical.choice, Quot.sound]`; no sorry/admit/axiom/native_decide.

**Zero-state survey (the heart of the task).** `potBelow Φ 1 = {Φ = 0}`:
- `wrongACount = 0` (Phase-10 majority) ⟺ all output `A` ⟹ (with `AllPhase10` + `0 < initialGap init`)
  `phase10MajorityWitness` ⟹ `StableDone`. **The real stability bridge** (not the clock potential).
- `wrongTCount = 0` (Phase-10 tie) ⟺ all output `T` ⟹ (with `AllPhase10` + `initialGap init = 0`)
  `phase10MajorityWitness` (T-disjunct) ⟹ `StableDone`.
- `clockCounterSumAt p = 0` (timed) means clocks all hit counter `0` ⟹ phase **ADVANCE**, NOT
  stability. Direct `⟹ StableDone` is FALSE; honest target is next-phase entry (`AllClockGEpCard (p+1) n`),
  ladder continues `p → ⋯ → 10 → stable`.

**Closed (Phase-10):** `phase10Majority_drained_mem_stableDone`, `phase10Tie_drained_mem_stableDone`
(membership bridges), `phase10Majority_link_intersected`, `phase10Tie_link_intersected` (E2 first link
routed to the `S1`/`Tie1plus`-intersected drain target via the InvClosed slice argument),
`phase10Majority_bridge_expectedHitting`, `phase10Tie_bridge_expectedHitting` (bridge = 0 via
`expectedHitting_eq_zero_of_mem`), `ladderData_of_phase10Majority_bridged`,
`ladderData_of_phase10Tie_bridged` (re-shaped spines, bridge DISCHARGED, no `hbridge` hypothesis).

**Re-shaped (timed):** `timed_phase_chain_target` / `timed_chain_target_is_next_phase` name the honest
next-phase rung target; the false direct timed bridge is deliberately NOT fake-discharged. The per-step
phase-advance transition feeding the re-shaped chain is the named Stage-4 timed residual.
