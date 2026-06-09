# Doty time-half — Avenue D-lynch: clock-minute advance drift ON THE REAL NonuniformMajority kernel

Directive: 挨个做，绝对不退缩. The LINCHPIN of the D-frontier (DOTY_COUPLING_SCOPING.md). C3/C4/C5 proved the
ABSTRACT `clockProto (Fin(L₀+1))`. The REAL protocol's clock is the `AgentState.minute` field inside
`NonuniformMajority L K`. They are NOT connected. D-lynch builds the clock-minute advance DIRECTLY on the real
kernel — the FAITHFUL link (no lumpability isomorphism, no assumed time-change; the C2 lesson). This is the
exact C3 `seedPot_contracts_on_floor` pattern transplanted to `NonuniformMajority`, reusing the ALREADY-PROVEN
per-pair minute descent lemmas.

Repo: ~/.openclaw/workspace/projects/Ripple (local, NO .git). Build: `nice -n 15 env LEAN_NUM_THREADS=2
~/.elan/bin/lake build <Module>`. Single-file check: `nice -n 15 env LEAN_NUM_THREADS=2 ~/.elan/bin/lake env
lean <file>`. Toolchain leanprover/lean4:v4.30.0.

## Reuse (all proven — open the files for EXACT signatures, do not paraphrase)
- F (the kernel-GENERIC builder) `Probability/WindowConcentration.lean`:
  `windowDrift_PhaseConvergence (P : Protocol Λ) (Φ : Config Λ → ℝ≥0∞) (hΦ) (Q) (hQ_abs) (r) (hdrift : ∀ c, Q c
  → ∫⁻ c', Φ c' ∂(P.transitionKernel c) ≤ r * Φ c) (Pre Post) (hPost_abs) (θ hθ hθ_top) (hlink : ∀ c, ¬Post c
  → θ ≤ Φ c) (hPre_Q) (Φ₀ hPre_bound) (t ε) (hε : r^t * Φ₀ / θ ≤ ε) : PhaseConvergence P.transitionKernel`.
  This applies DIRECTLY to `P := NonuniformMajority L K` (it is a `Protocol (AgentState L K)`, Fintype +
  DecidableEq). Also `measure_ge_thresh_on_absorbing`, `lintegral_decay_on_absorbing`, `windowDrift_tail`.
- Per-pair minute descent (REAL kernel) `Analysis/PhaseProgress.lean`:
  `phase3MinutePotential (s t : AgentState L K) : ℕ := 2*(K*(L+1) − max s.minute.val t.minute.val) + (if
  s.minute=t.minute then 0 else 1)` (private — you may need to re-expose or define your own config-level
  potential), `Transition_phase3_clock_minute_sync_decreases` (unequal minutes → sync up, strict pair-potential
  drop), `Transition_phase3_clock_minute_drip_decreases` (equal minutes below threshold → drip, strict drop),
  `phase3_minute_sync_of_applicable_two_clocks`. These are the proven combinatorial core.
- C3 `Probability/ClockFaithful.lean`: `seedPot_contracts_on_floor` / `clock_drip_seed_advance_prob` — the
  TEMPLATE for turning a per-pair advance into a config-level expected contraction (on clockProto; mirror its
  structure on the real kernel).
- Protocol scaffolding `Probability/NonuniformMarkovChain.lean` (nonuniformTransitionKernel, support lemmas),
  `Protocol/Transition.lean` (Phase 3 Rule 1 = the clock drip+epidemic, lines ~734-748).

## Task (NEW file Probability/ClockRealKernel.lean only — do NOT edit existing files)
Scope = the ATOMIC linchpin piece (single clock-minute advance drift), NOT all hours / NOT Lemma 6.10.
1. Define a CONFIG-level clock-minute potential `clockMinuteDeficit (T) (c : Config (AgentState L K)) : ℕ` =
   number of Clock agents (role=.clock, phase=3) with `minute.val < T` (the agents not yet beyond minute T),
   or a deficit sum — choose the form that makes the drift cleanest. Provide the ℝ≥0∞ / exponential-window
   version `Φ` needed by `windowDrift_PhaseConvergence`, with measurability `hΦ` (DiscreteMeasurableSpace).
2. Define the absorbing window `Q` (e.g. `c.card = n ∧ all non-clock structure stable enough that clock-clock
   pairs keep dripping`) and prove `hQ_abs` (Q preserved on the kernel support). Keep Q minimal but TRUE.
3. **The drift `hdrift : ∀ c, Q c → ∫⁻ c', Φ c' ∂((NonuniformMajority L K).transitionKernel c) ≤ r * Φ c`** —
   THE HARD CORE. A uniformly-random ordered pair is selected; when it is a clock-clock pair with the right
   minute relation, `Transition_phase3_clock_minute_{sync,drip}_decreases` gives a strict potential drop; all
   other pairs leave the clock-minute marginal unchanged (or non-increasing). The expected contraction factor
   `r = 1 − Θ((#clock-pairs)/(#all-pairs))` is where Doty's `1/c²` (c = clock fraction) appears NATURALLY —
   derive it by pair-counting, do NOT assume it. Mirror `seedPot_contracts_on_floor`'s structure.
4. Package: `clock_real_advance : PhaseConvergence (NonuniformMajority L K).transitionKernel` via
   `windowDrift_PhaseConvergence` with Pre = "Q ∧ deficit ≤ Φ₀", Post = "all clock agents at minute ≥ T",
   t = the interaction count, ε = the failure. State t/n in terms of n and c (the clock fraction) — this is the
   real-kernel analog of C3's per-minute advance.

## HARD RULES (automode, NO effort cap; 绝对不退缩)
NEW file `Probability/ClockRealKernel.lean` only; do NOT edit existing files. The drift MUST be a genuine
consequence of the per-pair descent lemmas + pair-counting — the `1/c²` factor DERIVED, never assumed as a
hypothesis or axiom. No sorry/admit/new axiom/native_decide. Iterate build until clean. If `phase3MinutePotential`
being `private` blocks reuse, define your own config-level potential from scratch (do NOT un-private the
existing one by editing PhaseProgress). If a genuine sub-lemma is missing (e.g. a pair-counting / expected-value
identity not in Mathlib or the repo), build it honestly in your file or STOP and report the EXACT atom with the
failing tactic chain — do NOT leave the drift as an abstract hypothesis (the C2 flaw). Do NOT git. Do NOT run a
full `lake build` while iterating (lean-check your file; the deps C3/C4/C5/F/PhaseProgress are already built).
Final message: the potential def, Q, the drift statement, the PhaseConvergence statement, build verdict,
`#print axioms` (must be `[propext, Classical.choice, Quot.sound]`, no sorryAx/ofReduceBool), how the `1/c²`
is DERIVED from pair-counting (not assumed), and HONEST status (drift proven on real kernel, or exact blocker).
