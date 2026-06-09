# Doty time-half — Avenue (d'): compose clock_real_step over minutes → GENUINE O(log n) real-kernel clock

Directive: 挨个做，绝对不退缩，不 over-claim. (a'')'s `clock_real_step` is the faithful per-minute O(1)-parallel
clock advance (level T crossed → level T+1 bulk-crossed, = C3 clock_step_upper on the real kernel). (d') composes
it over L₀ = K·(L+1) minutes → the clock reaches its final level in O(log n) PARALLEL time (genuinely O(1) per
minute × O(log n) minutes — NOT the Θ(log²n) the superseded full-crossing (d) gave). Replaces the mislabeled
clock_real_O_log_n.

## The chaining is DEFINITIONAL now (the bulk fix makes it clean)
`clock_real_step` Pre = `Q_mix n mC T ∧ 9*mC/10 ≤ rBeyond T`, Post = `Q_mix n mC T ∧ bulkHi mC ≤ rBeyond (T+1)`
with `bulkHi mC = 9*mC/10`. So Post(T) = `Q_mix n mC T ∧ 9*mC/10 ≤ rBeyond (T+1)`. The next minute's phase Pre is
`Q_mix n mC (T+1) ∧ 9*mC/10 ≤ rBeyond (T+1)`. The `9*mC/10 ≤ rBeyond (T+1)` part is identical; the `Q_mix n mC T
→ Q_mix n mC (T+1)` part is a small genuine implication (the window predicate is level-indexed — prove it like
(d)'s Q_mix_succ_of_post, or note Q_mix's clock-phase-3/card/clockCount parts are T-independent and only the
"floor level" differs — verify the exact Q_mix def). Discharge it honestly; do NOT assume.

## Task (NEW file Probability/ClockRealFaithfulHours.lean only)
1. `minuteStepPhase n mC (habs...) T : PhaseConvergence (NonuniformMajority L K).transitionKernel` — Pre =
   `Q_mix n mC T ∧ 9*mC/10 ≤ rBeyond T`, Post = `Q_mix n mC (T) ∧ bulkHi mC ≤ rBeyond (T+1)` (the clock_real_step
   shape), t = tseed+tbulk, ε = εseed+εbulk, convergence = `clock_real_step`, post_absorbing from habs_mix
   (Q_mix closure) + hmono_mix_discharged (9mC/10 ≤ rBeyond(T+1) preserved since rBeyond non-decreasing).
2. `clock_real_faithful_all_minutes` : compose `minuteStepPhase` over `Fin L₀` via `compose_n_phases` with the
   (genuine, proven) cross-minute chaining → after `L₀·(tseed+tbulk)` interactions, P[¬ level L₀ bulk-crossed]
   ≤ `L₀·(εseed+εbulk)`. MIRROR (d)'s clock_real_all_minutes / C5's clock_faithful_O_log_n_upper structure.
3. `clock_real_faithful_O_log_n` : instantiate L₀ = K·(L+1). With per-minute t = O(n/c²) (O(1) parallel) and
   ε = exp(−Θ(mC)), total interactions = K(L+1)·t = O(n·log n / c²) ⟹ parallel O(log n) for constant clock
   fraction; failure ≤ K(L+1)·ε = 1/poly. THE GENUINE O(log n) real-kernel clock (O(1)/minute, faithful
   decomposition), conditional ONLY on habs_mix ∀-minute (deterministic window closure). Document the O(log n)
   parallel reading and that it is now the CORRECT scale (contrast: the superseded clock_real_O_log_n was
   full-crossing = Θ(log²n)).

## HARD RULES (automode, 绝对不退缩, 不 over-claim)
NEW file ClockRealFaithfulHours.lean only; do NOT edit existing files, do NOT weaken proven lemmas. Use
`clock_real_step` as the GENUINE per-minute input (never re-assume per-minute convergence). The cross-minute
chaining `Q_mix n mC T → Q_mix n mC (T+1)` part must be genuinely PROVEN (or shown definitional) — do NOT assume
it. Carry ONLY habs_mix ∀-minute (the single deterministic hyp). No sorry/admit/new axiom/native_decide. Iterate
`lake build Ripple.PopulationProtocol.Majority.ExactMajority.Probability.ClockRealFaithfulHours` until clean. Do
NOT git. Final message: minuteStepPhase + clock_real_faithful_all_minutes + clock_real_faithful_O_log_n
signatures verbatim, the cross-minute chaining proof (genuine?), build verdict, #print axioms (must be [propext,
Classical.choice, Quot.sound]), HONEST status: genuine O(1)/minute composition → O(log n) (correct scale)?
chaining genuine not assumed? only habs_mix carried? Be precise, do not over-claim. If rate-limited, report WIP.
