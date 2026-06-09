# Doty time-half — Avenue C5: Thm 6.8 (two-sided per-minute) + Thm 6.9 (hour bounds) + all_hours_O_log_n

Directive: 挨个做，绝对不退缩. Next piece in the consult-confirmed DAG after C3 (upper) + C4 (lower).
C5 ASSEMBLES the two-sided clock timing theorem on the standalone clock kernel `clockProto L₀`:
combine C3's per-minute UPPER (`clock_step_upper` / `clock_faithful_O_log_n_upper`) with C4's per-minute
LOWER (`clock_step_lower` / `clock_step_lower_strict`) into the per-minute two-sided bound (Thm 6.8), sum
over k=45 minutes/hour (Thm 6.9), and conclude the clock reaches its final hour `L = ⌈log₂ n⌉`
(= `L₀ = k·L` minutes) in O(log n) parallel time at the kernel level (`all_hours_O_log_n`).

Repo: ~/.openclaw/workspace/projects/Ripple (local, NO .git). Build: `nice -n 15 env LEAN_NUM_THREADS=2
~/.elan/bin/lake build <Module>`. Toolchain leanprover/lean4:v4.30.0.

## SCOPE BOUNDARY (be faithful, do NOT inflate)
C5 completes the CLOCK's OWN two-sided O(log n) timing (Doty Thm 6.8/6.9) on `clockProto L₀`. It does
**NOT** claim the full majority-protocol expected-time headline: bridging `clockProto` to the main kernel
`NonuniformMajority L K` (the hour-sync coupling, Doty Lemma 6.10's supermartingale Φ(t)=m_{>h}−1.1·c_{>h})
is a SEPARATE later piece. State C5's results on `clockProto` only. If a step would require the cross-protocol
product, STOP and report the exact gap — do NOT fabricate a bridge.

## Reuse (all proven, in Probability/, namespaces ExactMajority.ClockFaithful / ExactMajority.FrontShape)
- C3 `ClockFaithful.lean`:
  - `clock_step_upper (n T) (hT : T+1 ≤ L₀) (hn : 20 ≤ n) (tseed tbulk εseed εbulk) (hεs hεb) (c₀) (hc₀ : seedFloorInv n T c₀) : (clockProto L₀).transitionKernel^(tseed+tbulk) c₀ {c | ¬(c.card=n ∧ CrossedB n (T+1) c)} ≤ εseed+εbulk`  — the per-minute UPPER.
  - `clock_faithful_O_log_n_upper (n m) (hm : m>0) (hML : m ≤ L₀) (hn) (tseed tbulk εseed εbulk) (hεs hεb) (c₀) (hx₀ : seedFloorInv n 0 c₀) : (clockProto L₀).transitionKernel^(∑_{i:Fin m}(tseed+tbulk)) c₀ {y | ¬(y.card=n ∧ CrossedB n m y)} ≤ ∑_{i:Fin m}(εseed+εbulk)`  — composed over m minutes.
  - defs: `CrossedB n i c := hi n ≤ beyond i c`, `seedFloorInv n T c := c.card=n ∧ CrossedB n T c`, `lo n = ⌊n/10⌋`, `hi n = ⌊9n/10⌋`, `beyond i c` = count at minute ≥ i. `variable {L₀ : ℕ}`.
- C4 `FrontShapeInduction.lean`:
  - `clock_step_lower (n) (hn : 100 ≤ n) (c i) (hcard : c.card=n) (_hcrossed_i : lo n ≤ beyond i c) (hsmall : beyond (i+1) c ≤ n/100) : ¬ CrossedB n (i+1) c`  — the per-minute LOWER (non-crossing).
  - `clock_step_lower_strict (... same hyps ...) : beyond (i+1) c < hi n`  — strict gap form.
  - `front_shape_all`, `next_minute_small`, `frontShape_couples_earlyDrip` etc. (front-shape supplies `hsmall`).

## Task (NEW file Probability/ClockHourBounds.lean only — do NOT edit existing files)
1. `clock_minute_bounds` (Thm 6.8): package the two-sided per-minute statement. UPPER = `clock_step_upper`
   (time `tseed+tbulk` suffices for minute T→T+1 whp). LOWER = `clock_step_lower_strict` (at the moment
   minute T reaches `lo n`, minute T+1 is not yet crossed when its front is `≤ n/100` — supplied by C4's
   front-shape `next_minute_small`). State both sides; the lower is the kernel-level strict non-crossing
   (the discrete shadow of the paper's `≥ 0.45` parallel-time gap — keep the same honest framing as C4).
2. `clock_hour_bounds` (Thm 6.9): define an hour as k=45 consecutive minutes (`hourStart h := h*k`,
   `hourEnd h := h*k + k`). Sum the per-minute UPPER over k minutes: reaching minute `(h+1)*k` from minute
   `h*k` costs `k*(tseed+tbulk)` interactions with failure `≤ k*(εseed+εbulk)`. This is the per-hour upper
   (Thm 6.9 upper). For the lower, carry the per-minute strict gap (clock advances at least one step per
   minute → hour h+1 not reached too early). Scale note: the paper's 1/c² (c = clock-agent fraction) lives
   in the per-step rate, already inside `tseed/tbulk`; keep the count form (no need to reintroduce 1/c²
   unless a hyp forces it). p=1, k=45 for the deterministic variant.
3. `all_hours_O_log_n`: instantiate `clock_faithful_O_log_n_upper` with `m = L₀` (= k·⌈log₂ n⌉) and prove
   `L₀ ≤ k * (Nat.log 2 n + 1)` (or the project's existing `L = ⌈log₂ n⌉` defn — check how L₀ relates to n;
   if L₀ is a free variable, state the bound CONDITIONAL on `hL₀ : L₀ ≤ k*(Nat.log 2 n + 1)` and note that
   the protocol instantiates L₀ = k·⌈log₂ n⌉). Conclude: total interactions `∑_{i:Fin L₀}(tseed+tbulk) =
   L₀*(tseed+tbulk) ≤ k*(Nat.log 2 n + 1)*(tseed+tbulk)` = O(n·log n) (parallel time O(log n)), with kernel
   failure `≤ L₀*(εseed+εbulk)` ≤ 1/poly when εseed+εbulk ≤ 1/(n·L₀). This is the clock reaching its final
   hour in O(log n) parallel time — Doty's clock timing theorem, two-sided.

## HARD RULES (automode, NO effort cap; 绝对不退缩)
NEW file `Probability/ClockHourBounds.lean` only; do NOT edit existing files (reuse C3/C4). No
sorry/admit/new axiom/native_decide. Iterate `lake build` until clean. The bounds must be GENUINE
consequences of C3+C4 (the lower from C4's front-shape non-crossing, NOT re-assumed). If `all_hours_O_log_n`
genuinely needs `L₀ = k·⌈log₂ n⌉` and L₀ is a free variable in the clock model, state it as an explicit
hypothesis `hL₀` and document that the protocol supplies it — do NOT fabricate a definitional equality that
isn't there. Do NOT git. Final message: the three theorem statements, build verdict, `#print axioms` (must be
`[propext, Classical.choice, Quot.sound]`, no sorryAx/ofReduceBool), and an HONEST status: what is proven
kernel-level (two-sided clock timing on clockProto) and the explicit remaining gap (clock→main hour-sync
coupling, Lemma 6.10 — NOT in scope for C5).
