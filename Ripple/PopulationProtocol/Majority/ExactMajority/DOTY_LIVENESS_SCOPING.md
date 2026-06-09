# Doty Theorem 3.1 — Liveness Scoping Report

Read-only scoping pass, 2026-06-06. No edits, no git, no build mutation.
Author task: produce the attack plan to discharge the open obligation in
`stable_majority_correct`.

---

## 0. HEADLINE FINDING (re-frames the whole campaign)

**The open `sorry` is NOT the §4 probabilistic argument.** The doctrine
(`DOTY_LIVENESS_DOCTRINE.md`) assumes sorry #2 = "minority elimination /
clock concentration w.h.p." That premise is **wrong against the current
code**. Evidence:

1. There is exactly **one** active `sorry` in the entire `ExactMajority`
   subtree: `Analysis/DeterministicChain.lean:9130`, the `· sorry)` closing
   the `by_cases hn : 16 ≤ init.card` — i.e. the **`init.card ≤ 15` branch**
   of `stable_majority_correct` (DeterministicChain.lean:9102–9130).

2. `Protocol.StablyComputes` (Basic/PopulationProtocol.lean:245–251) is the
   **purely existential** Doty §2.2 notion:
   `∀ init valid, ∀ c reachable, ∃ o reachable from c, output = verdict ∧ IsStable o`.
   No measure, no probability. Under the standard fair-scheduler reading,
   w.p.-1 stable computation ⟺ this reachability statement. So
   `stable_majority_correct` is a **deterministic reachability theorem**.

3. The §4 probabilistic machinery (clock concentration Θ(log n), minority
   elimination by hour ⌈log₂(1/g)⌉ w.h.p.) is needed only for the **expected
   O(log n) time** part of Theorem 3.1, which `MainTheorem.lean:123–152`
   explicitly does **not** export ("No Lean theorem is exported here yet: the
   current development does not have a typed random schedule and stopping-time
   API"). It is orthogonal to the open `sorry`.

4. The `16`/`8`/`2^L` constants are deterministic counting thresholds for
   **role allocation** (creating 2 clock agents from MCR agents), not
   concentration bounds.

**Consequence:** the faithful `stable_majority_correct` (L = ⌈log₂ n⌉, i.e.
`hsize : init.card < 2^L`) can be closed **without any new probability**, by
extending the deterministic role-allocation / checkpoint argument down to
small populations. This is strictly easier and entirely self-contained.

The deterministic descent driver
`synchronized_checkpoint_deterministic_liveness`
(DeterministicChain.lean:8016) is **already fully proven, 0 sorry**, by strong
induction on the phase deficit `10 - maxPhase c`. The Phase-4 tie callback
`phase4_tie_callback_of_size` (9065) already threads the `card < 2^L`
hypothesis and works for **all** `2 ≤ card`. So the only gap is the bridge
**"arbitrary reachable c (card ≤ 15) → synchronized checkpoint with 2
clocks."**

---

## 1. The exact remaining obligation (precise statement)

The `16 ≤`-branch of `stable_majority_correct` is discharged by
`reachable_to_checkpoint` (DeterministicChain.lean:8970) + the proven driver.
`reachable_to_checkpoint` produces, from any reachable `c`, a synchronized
`mid` with `1 ≤ maxPhase mid` and an applicable clock pair, **requiring
`16 ≤ init.card`** (via `phase0_creates_two_clocks_general` → `…_aux` →
`phase0_potential_bound`).

The open `sorry` must prove, for `init.card ≤ 15`:

> `∀ init, validInitial init, init.card < 2^L (already in scope as hsize_init),
>  ∀ c reachable from init,`
> `∃ final reachable from c, majorityStableEndpoint init final.`

`validInitial` (MainTheorem.lean:101) forces **every initial agent to be role
`.mcr`, phase 0**. So `init.card = MCR_count`, `CR = Clock = 0` initially.

### Role-creation arithmetic (Phase0Transition, Transition.lean:356–404)

- **Rule 1** MCR+MCR → Main + CR. Net per step: `MCR −2, CR +1`.
- **Rule 4** CR+CR → Clock + Reserve. Net: `CR −2, Clock +1`.
- Two clocks ⇒ need 4 CR ⇒ need 4 Rule-1 steps ⇒ need **8 MCR**.

Hence `phase0_creates_two_clocks` (PhaseProgress.lean:531) requires exactly
`8 ≤ card`. The `16` in `reachable_to_checkpoint` is looser only because it
must tolerate role "waste" through Rule 2/3 (assignment) interactions on an
arbitrary reachable `c` (not the clean all-MCR `init`).

### Two genuinely distinct sub-regimes inside `card ≤ 15`

- **Regime A: `8 ≤ card ≤ 15`.** Two clocks ARE deterministically reachable.
  The gap is purely that `reachable_to_checkpoint`'s waste-margin is set at
  16; the underlying ability exists (cf. the proven `validInitial_to_checkpoint`
  at `8 ≤ card`, DeterministicChain.lean:7961). This is a **bookkeeping /
  bound-tightening** task.

- **Regime B: `card ≤ 7`.** Two clocks **cannot** be created (not enough MCR
  fuel). The protocol cannot synchronize a clock-driven phase clock. This is
  the genuinely-new piece. Here either (i) Doty's protocol still stabilizes by
  a **degenerate / clock-free** route that must be analyzed directly, or (ii)
  the faithful statement needs `n` "sufficiently large" (paper line 251 says
  exactly "n sufficiently large"), so `card ≤ 7` is **outside the paper's
  claimed regime** and the honest faithful theorem carries a small-`n`
  hypothesis. See §3.

### Dependency DAG (new lemmas)

```
                       stable_majority_correct  (close sorry @9130)
                                  │
                 ┌────────────────┴─────────────────┐
        [Regime A: 8≤card≤15]              [Regime B: card≤7]
                 │                                   │
   (L1) reachable_to_checkpoint_8          (decide between B-route i / ii)
        : relax 16→8 for arbitrary             │
          reachable c                  ┌────────┴─────────┐
                 │                  (B-i) small-pop      (B-ii) add
   (L2) phase0_potential_bound_8     direct stabilization  n-large hyp
        : potential bound @ card≥8     analysis            to faithful stmt
          (currently states ≥card,      │                  (honest, paper-
          proof needs the 16 only    (L3) card≤7 finite     faithful at
          inside _aux case split)      reachability:        "n suff. large")
                 │                      ∃ majorityStable
   (L_drv) reuse (proven):              Endpoint reachable
     synchronized_checkpoint_           for each card∈{2..7}
     deterministic_liveness  ──────────────┘
     phase4_tie_callback_of_size
     full_deterministic_liveness_from_initial
```

`L_drv` nodes are **already proven** (0 sorry) and reused verbatim. The only
new work is `L1/L2` (Regime A, easy) and the Regime-B decision + `L3`.

---

## 2. Per-lemma reuse assessment

| Node | What it is | Reusable Ripple machinery? | Verdict |
|------|------------|----------------------------|---------|
| `L_drv` descent driver | `synchronized_checkpoint_deterministic_liveness` (DC:8016), strong-induction on `10−maxPhase` | **Already proven, 0 sorry.** Used verbatim by the `16≤` branch. | REUSE AS-IS |
| `L_drv` phase-4 callback | `phase4_tie_callback_of_size` (DC:9065): card<2^L ⇒ initialGap=0 ⇒ tie endpoint; needs only `2≤card` | Already proven. Threads `hsize_init` correctly for all card. | REUSE AS-IS |
| `L_drv` 8-bound entry | `validInitial_to_checkpoint` (DC:7961, `8≤card`), `full_deterministic_liveness_from_initial` (DC:8233, `8≤card`) | Already proven for `init` (not arbitrary `c`). | REUSE / ADAPT |
| `L1` checkpoint @ ≥8 from arbitrary `c` | relax `reachable_to_checkpoint`'s `16` to `8` | Adapt `reachable_to_checkpoint` (DC:8970) + `phase0_creates_two_clocks_general` (DC:8952). The reachable-c version goes through `phase0_reach_two_clocks_aux` (DC:8889) whose CR<2∧Clock<2 branch needs `MCR≥2`, derived from potential ≥ card with card≥? | NEW (adaptation) — medium |
| `L2` potential bound @ ≥8 | `phase0_potential_bound` (DC:8769) currently `hn:16≤card`; statement is `MCR+3(CR+2Clk) ≥ card`, proof `omega` from `phase0_adjusted_potential_invariant` (no 16 needed in the invariant itself) | The **invariant** `phase0_adjusted_potential_invariant` has NO card hypothesis. The `16` is only consumed downstream in `_aux`'s arithmetic `MCR ≥ 16−9 = 7`. At card≥8 the same case analysis gives `MCR ≥ 8−9 < 0` — **the naive bound breaks**; need a sharper case split (track Reserve/Main waste). | NEW — the real Regime-A subtlety |
| `L3` finite card≤7 reachability | enumerate stabilization for card∈{2,…,7} | No direct reuse. Possibly `decide`/`Finset`-exhaustion over reachable configs, OR a clock-free stabilization argument. | NEW — see §3 |
| §4 clock concentration | drip+epidemic clock Θ(log n) w.h.p. | SSEM `JansonGeometric.lean` (0 sorry, exists), `Epidemic.lean`, `EpidemicTime.lean`, `Supermartingale.lean`; PopProto `GeometricDrift` | **NOT NEEDED for the open sorry.** Needed only for unexported time bound. |
| §4 minority elimination | count→0 by hour ⌈log₂(1/g)⌉ w.h.p. | SSEM hitting-time toolkit; PopProto geometric-decay | **NOT NEEDED for the open sorry.** Time bound only. |

### Honest note on the doctrine's "reusable machinery"

The SSEM `Probability/` toolkit (DriftHittingTime, ExpectedTime, PhaseRace,
RandomScheduler, SchedulerBridge, SelectionCount) and the **per-protocol**
`ExactMajority/Probability/` files (JansonGeometric 1898 lines/0 sorry,
Epidemic, EpidemicTime, Supermartingale, SupermartingaleHitting,
PhaseConvergence, JansonHitting, …) are real and largely proven. But per the
UNDERSTANDING.md (stale, 2026-05-23) note they were **built for the
time-complexity / convergence-rate program and were never wired into the
correctness theorem** — because the correctness theorem never needed them.
They remain the asset for the (separate) expected-O(log n)-time theorem.

---

## 3. The single hardest genuinely-new piece

It is **NOT** clock concentration. It is **Regime B (`card ≤ 7`)** — the
populations that cannot build a phase clock — plus the sharper potential
case-split in **Regime A** (`L2`).

### 3a. Regime A `L2` (the real but bounded difficulty)

Tightening `phase0_potential_bound` / `phase0_reach_two_clocks_aux` from `16`
to `8`. The blocker: the proven `_aux` (DC:8889) in the `CR<2 ∧ Clock<2`
branch derives `MCR ≥ 2` from `MCR + 3(CR+2Clk) ≥ 16` with `CR≤1, Clock≤1`
(⇒ `MCR ≥ 7`). At threshold 8 this gives `MCR ≥ 8−9 < 0` — vacuous. So the
adjusted-potential invariant `phiTotal ≥ card + surplusTotal`
(`phase0_adjusted_potential_invariant`, DC:~7945) must be exploited more
carefully: the surplus term tracks Main/Reserve "waste", and a population that
started all-MCR with `card ≥ 8` provably has enough fuel to reach 4 CR. The
correct argument is the **`init`-side** one already proven in
`phase0_creates_two_clocks` (PhaseProgress.lean:531, `8≤card`, exploits
all-MCR ⇒ `MCR=card`, `CR=0`, clean). The task is to route the `card ≤ 15`
branch through the **`init`-anchored** chain
(`validInitial_to_checkpoint` + `full_deterministic_liveness_from_initial`,
both `8≤card`) rather than the arbitrary-`c`
`reachable_to_checkpoint` (`16≤card`). Because the `sorry` branch has `init`
in scope and `c` reachable from `init`, one can checkpoint **from `init`**
(reaching `mid`), and since `final` need only be reachable **from `c`**, use
confluence: `init ⇒ c` and `init ⇒ mid ⇒ final`; need `c ⇒ (something) ⇒
final`. This needs a **diamond/confluence** step that the `16`-branch sidesteps
by checkpointing from `c` directly. So `L1` is genuinely needed: checkpoint
from arbitrary reachable `c` at `8 ≤ card`.

### 3b. Regime B `card ≤ 7` (genuinely new, but small)

No 2 clocks ⇒ no phase clock ⇒ the descent driver's precondition
(`∃ applicable clock pair`) is unreachable. Two honest options:

- **(B-i) Direct finite analysis.** For each `card ∈ {2,…,7}`, the state space
  is finite and the reachable set from any all-MCR `init` is a concrete finite
  graph. One can prove `∃ majorityStableEndpoint reachable` by a structural /
  `decide`-style exhaustion, OR show the protocol degenerates to a
  Phase-2/Phase-4 consensus without ever needing a clock (Rule 1 alone
  produces Main agents carrying the bias; the bias averaging in Phase 1 may
  still converge). This requires reading the no-clock dynamics carefully —
  genuinely new, but bounded (≤7 agents, finite).

- **(B-ii) Faithful-with-n-large.** Paper line 251 states the theorem for
  "n sufficiently large." The faithful theorem may legitimately carry a
  `8 ≤ init.card` (or `card ≥ n₀`) hypothesis. This is **not** a weakening of
  the paper — it is the paper's own "n sufficiently large." If Xiang accepts
  this as faithful, Regime B vanishes and the whole `sorry` reduces to
  Regime A.

**Recommendation:** confirm with Xiang whether "faithful L=⌈log₂n⌉, n large"
permits a `card ≥ 8` (or `≥ 16`) hypothesis. The paper's "n sufficiently
large" strongly suggests YES, which collapses the hardest piece. If NO, do
(B-i) by finite exhaustion — still no probability.

Neither option needs SSEM hitting-time or PopProto geometric-drift.

---

## 4. Difficulty / round estimate & first executable avenue

**Difficulty:** Medium, NOT a multi-round probabilistic campaign. There is no
martingale, no concentration, no measure-theoretic content in the open goal.

**Recommended FIRST executable lemma** (smallest self-contained, highest
leverage):

> **`reachable_to_checkpoint_8`**: same statement as `reachable_to_checkpoint`
> (DC:8970) but with `hn : 8 ≤ init.card`.

Reuse plan: it already case-splits (DC:8982) on
`reachable_clockCount_ge_two_or_all_phase_zero`. The non-all-phase-0 branches
need no card bound. The all-phase-0 branch calls
`phase0_creates_two_clocks_general` (`16≤`) — replace with an `8≤` version
`phase0_creates_two_clocks_general_8`, whose proof must redo the
`phase0_reach_two_clocks_aux` arithmetic with the **surplus-aware** invariant
(§3a) instead of the crude `MCR + 3(CR+2Clk) ≥ 16`. Concretely: prove that a
config reachable from an all-MCR `init` with `card ≥ 8`, still all phase 0,
has `MCR + 3·CR + 6·Clock ≥ 8` AND enough structure to reach `Clock ≥ 2`
(the `init`-side proof `phase0_creates_two_clocks` already does this at the
all-MCR root; the surplus invariant transports it along Rule-2/3 waste).

Once `reachable_to_checkpoint_8` exists, the `sorry` branch becomes: split
`8 ≤ init.card` (use it; mirror the `16≤` branch verbatim) vs `init.card ≤ 7`
(Regime B). That isolates the only genuinely-new content to ≤7-agent
populations.

**Round estimate:**
- R1: `reachable_to_checkpoint_8` (+ its `_general_8` helper). Closes
  `8 ≤ card ≤ 15`. 1–2 rounds; the hard sub-step is the surplus-aware
  potential bound, which is real Lean arithmetic but finite and `omega`-shaped.
- R2: Regime B decision. If (B-ii) accepted → done in minutes (add hypothesis,
  rewire `stable_majority_correct` to require `8 ≤ card`, document as the
  paper's "n large"). If (B-i) → 2–4 rounds of finite no-clock analysis.

---

## 5. Mathlib / Ripple probability primitives: present vs absent?

**No hard-stop.** The open `sorry` needs **zero** probability primitives —
it is deterministic reachability over a finite-multiset transition relation,
all within `Relation.ReflTransGen` + `Multiset` + `omega` arithmetic, which
are present and heavily used in the existing 0-sorry chain.

For the (separate, unexported) §4 **time-complexity** theorem, the audit is:
- **Present in Ripple:** geometric tail concentration (`JansonGeometric.lean`,
  0 sorry), epidemic concentration (`Epidemic.lean`, `EpidemicTime.lean`),
  multiplicative-drift supermartingale (`Supermartingale.lean`), uniform random
  scheduler (`Scheduler.lean`, SSEM `RandomScheduler.lean`), expected
  hitting-time toolkit (SSEM `ExpectedTime.lean`,
  `expectedHittingTime_le_window_mul_inv`, drift→hitting bridges,
  Freedman/tail bounds), scheduler bridge (`SchedulerBridge.lean`).
- **Present in Mathlib:** `PMF`, `MeasureTheory`, martingales
  (`MeasureTheory.Martingale`), `ProbabilityTheory` hitting times,
  `ENNReal`/`NNReal` tsum machinery.
- **The genuine gap for the time theorem** (acknowledged in MainTheorem.lean):
  a **typed random schedule + stopping-time API for THIS protocol** wiring the
  above into the 11-phase kernel. That is the multi-round probabilistic
  campaign the doctrine describes — but it is the *time* theorem, not the
  open correctness `sorry`.

---

## TL;DR for the campaign

1. Open `sorry` = `init.card ≤ 15` deterministic-reachability branch of
   `stable_majority_correct` (DC:9130). NOT the §4 probability.
2. The descent driver + Phase-4 callback are already proven and thread
   `card < 2^L` for all `card ≥ 2`. Faithful statement is intact.
3. First move: prove `reachable_to_checkpoint_8` (relax 16→8 via a
   surplus-aware Phase-0 potential bound), reusing the all-MCR-rooted
   `phase0_creates_two_clocks` (`8≤card`, already proven). Closes `8..15`.
4. Residual `card ≤ 7`: ask Xiang whether the paper's "n sufficiently large"
   permits a `card ≥ 8` hypothesis (collapses it); else finite no-clock
   exhaustion. Either way, no probability.
5. No Mathlib/Ripple probability primitive is missing for the correctness
   goal. The probability stack matters only for the separate, unexported
   O(log n) time theorem.
