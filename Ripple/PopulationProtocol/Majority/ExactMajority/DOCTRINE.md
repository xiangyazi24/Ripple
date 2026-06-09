# DOCTRINE — Doty Thm 3.1 time half, autonomous run

## Goal (one sentence)
Complete the time half of Doty et al. Theorem 3.1 — O(log n) parallel stabilization time whp /
expected — to GENUINE 0-sorry, faithful, UNCONDITIONAL Lean, OR drive each layer to a real terminal
condition (unconditional theorem or documented exact blocker). No over-claim — every result labeled
proven-vs-assumed (the accountability lesson from blog 027).

## State at run start
- Correctness half: DONE (`stable_majority_correct`, 0-sorry). Not in scope here.
- Layer 1 (abstract clock O(log n) two-sided): DONE — C3/C4/C5 (`clockProto`), 0-sorry, axioms clean.
- Layer 2 (clock advance on REAL NonuniformMajority kernel): all-clocks done (D-lynch/2);
  mixed-regime c² in flight (D-lynch-3); two structural invariants undischarged.
- Layer 3 (clock drives Main, Lemma 6.10): not started.
- Layer 4 (11 phase instances → A1 → expected-time): not started.

## Avenues (ranked; each a complete attack, terminal condition = unconditional theorem or exact blocker)
(a) **D-lynch-3 mixed-regime advance** (in flight): genuine c² from full-denominator pair-counting,
    structural invariants carried as labeled hyps. Terminal: 0-sorry conditional PhaseConvergence with
    c² derived + invariants explicit.
(b) **Discharge clock-count Θ(n)**: Phase-0 population-split creates a constant fraction of clocks. Only
    `phase0_creates_two_clocks` (≥2) exists. Build the Θ(n) lower-bound invariant. Terminal: `γn ≤
    clockCount` on reachable configs, or documented blocker.
(c) **Discharge phase-3 window (habs)**: "clock at minute < cap ⟹ phase exactly 3" + one-step closure —
    a reachability/synchronization invariant (clocks hit cap together → enter phase 4 together). The
    real-kernel analog of C4/C5 front-shape. Terminal: window one-step-closed unconditionally, or blocker.
(d) **Compose real-kernel advance over minutes/hours**: the NonuniformMajority analog of C5
    `all_hours_O_log_n` — clock reaches hour L in O(log n) parallel, using (a)+(b)+(c). Terminal:
    unconditional O(log n) real-kernel clock timing.
(e) **Lemma 6.10 hour-coupling**: Φ(t)=m_{>h}−1.1·c_{>h} supermartingale (via `Supermartingale` Thm 4.2)
    ⟹ Main `hour` tracks Clock `minute`, split reactions gated. Terminal: hour-sync theorem.
(f) **Timed + untimed phase instances → A1**: build the 11 `PhaseConvergence (NonuniformMajority)`
    instances (untimed via framework F; timed via (d)+(e)), feed into `doty_time_headline`. Terminal:
    `doty_time_headline` instantiated with REAL phases (discharge its abstract phase hypotheses).
(g) **Expected-time wrapper**: whp O(log n) path (f) + rare backup (phase3TieConvergence / Phase-10,
    negligible, finite via `stable_majority_correct`) ⟹ E[parallel time] = O(log n). Terminal: the
    headline expected-time theorem, 0-sorry, axioms clean.

## Fallbacks
- One-step framework can't prove a reachability invariant ((b),(c)) → develop it as a separate
  induction over reachable configs (PopProtoCommon reachability API), don't fake it.
- Missing Mathlib/repo atom → build it honestly in-file or STOP and document the exact atom + failing
  tactic chain. No axiom escape, no native_decide, no assumed-contraction.

## Discipline (hard rules for this run)
- Every committed result tagged: unconditional / conditional-on-X (X listed) / partial. Never inflate.
- Independent `#print axioms` on every milestone — must be {propext, Classical.choice, Quot.sound}.
- Hard problems single-line (one coherent agent), not parallel-fired. Commit per avenue.
- Telegram only at: avenue complete, all avenues exhausted, or genuine hard block. No tactical check-ins,
  no time estimates, no choice questions.
- GitHub (full Ripple) stays frozen until whole-repo verified-clean. Sturm/Number line untouched.
