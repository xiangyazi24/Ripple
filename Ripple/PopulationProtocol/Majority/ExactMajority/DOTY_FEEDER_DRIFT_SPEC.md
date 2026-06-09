# Doty time-half — feeder-count one-step DRIFT bound (the real probabilistic handle on `hwin_all`)

Directive: 脚踏实地，绝对不退缩，不 over-claim, 不空转. Produce a GENUINE new proven lemma — do not
re-wrap an existing residual under a new name.

## Where this sits (the EXACT remaining hypothesis)
`FrontSyncConc.clock_real_unconditional` proves the real-kernel O(log n) clock's FrontSync maintenance
over the horizon — its ONLY remaining hypothesis is
`hwin_all : ∀ c, FrontSync c → c.card = n → FrontFeederWindow n B c`, where
`FrontFeederWindow n B c := c.card = n ∧ AllClockP3 c ∧ frontMinuteCount (capMinute−1) c ≤ B`
(file `FrontSyncConc.lean:341`; `frontMinuteCount` in `ClockFrontShape.lean:518`; `capMinute = K*(L+1)`).
So the whole clock rests on: **the cap−1 feeder count `frontMinuteCount(capMinute−1) c` stays ≤ B**
(`B = O(log log n)`) at every reachable FrontSync config.

## The genuine mechanism (think first, then prove)
`frontMinuteCount(capMinute−1) c` = number of agents that are Phase-3 clocks at minute EXACTLY `capMinute−1`
(the cap−1 feeder; the leading edge while FrontSync = "cap empty" holds). Its one-step change under the real
kernel `NonuniformMajority L K`:
- INCREASES by 1 when a clock ENTERS minute `capMinute−1`: either (a) DRIP — two clocks both at `capMinute−2`
  interact and one increments to `capMinute−1`; or (b) SYNC/epidemic — a clock at minute `< capMinute−1`
  meets a clock at minute `≥ capMinute−1` and jumps (takes the max) to `≥ capMinute−1`.
- DECREASES by 1 when a clock LEAVES `capMinute−1` upward to `capMinute` — but that is EXACTLY the FrontSync
  breach (a clock reaches the cap). On the FrontSync-good event (cap empty, maintained whp by
  `clock_real_unconditional`), this out-flux is the rare breach already accounted for.

So on the FrontSync window the feeder is fed from the `capMinute−2` "source". The drift is bounded by the
mass at/below `capMinute−2` that can cross into `capMinute−1` — i.e. by the SOURCE counts at the levels just
below, via the SAME pair-counting that `HourCouplingV2` uses for the hour-drag/epidemic drift.

## Task — NEW file `Probability/FeederDrift.lean` ONLY
Prove the **feeder one-step drift bound** by REUSING the proven pair-counting machinery in
`HourCouplingV2.lean`:
- `HourCouplingV2.integral_transitionKernel_eq_sum` (line 98): for any real observable `f`,
  `∫ f d(K c) = ∑_{(s,t)} interactionProb(s,t) · f(stepOrSelf c s t)` on `2 ≤ card`.
- the per-pair crossing indicators + the disjoint-cross sum lemmas
  (`sum_interactionCount_indicator` line 504, `sum_interactionCount_dragInd = 2·mainBelowCount·cAbove`
  line 535, `sum_interactionCount_epiInd = 2·cAbove·clockBelowCount` line 586) — define the ANALOGOUS
  feeder-entry indicator `feederInInd (s t : AgentState L K) : ℕ` = 1 iff the pair `(s,t)` (under
  `stepOrSelf`) moves an agent INTO minute `capMinute−1` from below, and sum it the same way.

Deliverables (state precisely, prove genuinely):
1. `feeder_drift_le`: on `AllClockP3 c`, `FrontSync c`, `2 ≤ card`, the one-step expected feeder count
   `∫ (frontMinuteCount (capMinute−1) ·) d(K c)` is `≤ frontMinuteCount(capMinute−1) c + (drift)` where
   `(drift)` is the pair-sum of `feederInInd`, bounded by the SOURCE count
   `frontMinuteCount(capMinute−2) c` (drip) plus the sync mass `∝ rBeyond(capMinute−1) c · clockBelowCount`.
   Give the SHARP bound the pair-counting yields (the analog of the `2·X·Y / (card·(card−1))` forms in
   `HourCouplingV2`). PROVE it via `integral_transitionKernel_eq_sum` + the feeder indicator pair-sum.
2. If a clean bounded-difference form falls out (`|frontMinuteCount(capMinute−1) c' − frontMinuteCount(...) c| ≤ 1`
   on the support — at most one agent moves per interaction), state `feeder_step_bddDiff` (this is the
   bounded-difference hypothesis `AzumaKernel.azuma_tail` needs).
3. HONEST status: state whether the drift is a SUPERMARTINGALE (≤ 0 net) — note that under FrontSync the
   feeder is FED with no upward out-flux, so the NET drift is `≥ 0` (the feeder GROWS), hence `hwin_all`
   (≤ B at EVERY FrontSync config) is NOT a fixed invariant: it holds only while the SOURCE
   `frontMinuteCount(capMinute−2)` (equivalently the bulk leading edge) is below the top band. Report this
   precisely: the genuine discharge of `hwin_all` is a COUPLED feeder-count ⊗ bulk-position bound (the source
   stays sparse until the bulk arrives, at which point Hour L completes). Do NOT assert hwin_all; deliver the
   drift bound + the precise coupled residual.

## Why this is real progress (not churn)
The drift bound is a STANDALONE proven lemma — the first probabilistic handle on the feeder count itself
(the analog of `HourCouplingV2.hour_coupling_v2`'s drift). It makes the feeder dynamics explicit and is the
prerequisite for any supermartingale/Azuma discharge of `hwin_all`. Even if the full discharge needs the
bulk-position coupling, the drift bound is bankable and advances the actual remaining hypothesis.

## BUILD ROUTING
Iterate SINGLE-FILE: `cd /Users/huangx/.openclaw/workspace/projects/Ripple` then
`nice -n 15 env LEAN_NUM_THREADS=2 ~/.elan/bin/lake env lean Ripple/PopulationProtocol/Majority/ExactMajority/Probability/FeederDrift.lean`
(single-file check, ALLOWED locally). Do NOT run bare `lake build` locally (the hook blocks it — heavy builds
go to uisai1 via `scripts/remote-build.sh`). One full module build at the very end if needed (remote).

## HARD RULES (绝对不退缩, 不 over-claim, 不空转)
NEW file `FeederDrift.lean` ONLY; do NOT edit or weaken any existing file/lemma. The drift bound MUST be
genuinely proven via the pair-counting (reuse `HourCouplingV2`/`ClockRealMixed` lemmas), NEVER asserted. Do
NOT add a false hyp — 9+ false-shapes were caught this campaign; do not add a 10th. No
sorry/admit/new axiom/native_decide. Verify `#print axioms` of your main lemma (temp importer via
`lake env lean`, then delete) is `[propext, Classical.choice, Quot.sound]`. Do NOT git. Final message: the
drift bound statement (genuinely proven via pair-counting?), the bounded-difference form (yes/no), the HONEST
net-drift sign + the precise coupled residual for `hwin_all`, the single-file build verdict, `#print axioms`.
If a pair-counting API genuinely doesn't exist to continue, prove the maximal clean prefix and STOP at the
EXACT missing lemma name — do not fake.
