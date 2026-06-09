# Doty time-half — Avenue (d): compose real-kernel mixed advance over minutes → O(log n) clock on NonuniformMajority

Directive: 挨个做，绝对不退缩，不 over-claim. Avenue (a) gave the per-minute mixed-regime clock advance on the
REAL `NonuniformMajority` kernel (`clock_real_advance_mixed`, genuine c², 0-sorry, conditional on 3 labeled
structural hyps). Avenue (d) COMPOSES it over the L₀ = K·(L+1) minutes into the real-kernel analog of C5's
`all_hours_O_log_n`: the protocol's clock reaches its final hour in O(log n) parallel time, on the real kernel.

## Reuse (open for exact signatures)
- `Probability/ClockRealMixed.lean` (avenue a): `clock_real_advance_mixed (n mC T) (hn hmC hT) (γ hγ hγ1)
  (habs_mix) (hmono_mix) (hfrontier_mix) (t ε) (hε) : PhaseConvergence (NonuniformMajority L K).transitionKernel`
  with Pre = `Q_mix n mC T` (includes `rBeyond T c = mC`), Post = `rShell ∧ rFinished` (`rBeyond (T+1) c = mC`).
  Also `Q_mix`, `clockCount`, `rBeyond`, `rSeedPot`.
- `Probability/ClockHourBounds.lean` (C5): the COMPOSITION TEMPLATE — `clock_faithful_O_log_n_upper` /
  `clock_hour_bounds` / `all_hours_O_log_n` compose per-minute phases via `compose_n_phases` over `Fin m` with
  the DEFINITIONAL cross-minute chaining (minute T Post = minute T+1 Pre). MIRROR this structure exactly.
- `Probability/PhaseConvergence.lean`: `compose_n_phases`, `PhaseConvergence`.

## The chaining (definitional, like C5)
minute T `clock_real_advance_mixed` has Post `rBeyond (T+1) c = mC`; minute T+1's Pre `Q_mix n mC (T+1)`
includes `rBeyond (T+1) c = mC`. So `phases T |>.Post → phases (T+1) |>.Pre` is the definitional identity
(the rest of `Q_mix` — card = n, phase-3 window, clockCount = mC — is carried by the structural hyps). Mirror
C5's `h_chain := fun i hi x hx => hx`.

## Task (NEW file Probability/ClockRealHours.lean only — do NOT edit existing files)
1. Define the per-minute phase family `mixedMinutePhases n mC (hyps...) : Fin L₀ → PhaseConvergence
   (NonuniformMajority L K).transitionKernel`, each = `clock_real_advance_mixed` at minute T = i.val, fed the
   per-minute structural hyps (carry them as `∀ T, habs_mix/hmono_mix/hfrontier_mix at T` inputs to the family).
2. `clock_real_all_minutes` : compose over `Fin L₀` via `compose_n_phases` (definitional chaining) → after
   `∑_{i:Fin L₀} t` interactions, P[¬ all clocks crossed minute L₀] ≤ `∑_{i:Fin L₀} ε`. MIRROR C5's
   `clock_faithful_O_log_n_upper` proof structure.
3. `clock_real_O_log_n` : instantiate with `L₀ = K·(L+1)` and per-minute t = O(n/c²), ε = 1/poly, giving total
   interactions `L₀ · t = O(n·log n / c²)` (parallel time O(log n) for constant clock fraction c) with kernel
   failure ≤ 1/poly. The real-kernel analog of `all_hours_O_log_n`. Document the O(log n) parallel-time reading
   (interactions/n) and that it is conditional on the carried structural hyps (∀ minute) — labeled, deferred.

## HARD RULES (automode, NO effort cap; 绝对不退缩; 不 over-claim)
NEW file `Probability/ClockRealHours.lean` only; do NOT edit existing files, do NOT weaken any proven lemma. No
sorry/admit/new axiom/native_decide. The carried structural hyps from avenue (a) propagate through composition
as EXPLICIT labeled hypotheses (∀ minute T) — do NOT discharge them here (separate avenues), do NOT hide them,
do NOT assume the per-minute convergence (use `clock_real_advance_mixed` as the genuine per-minute input).
Iterate build until clean. If the composition needs a sum/arithmetic lemma not present, build it. Do NOT git.
Build: `nice -n 15 env LEAN_NUM_THREADS=2 ~/.elan/bin/lake build
Ripple.PopulationProtocol.Majority.ExactMajority.Probability.ClockRealHours`. Final message: the
`clock_real_all_minutes` + `clock_real_O_log_n` signatures verbatim (showing carried hyps), build verdict,
`#print axioms` (must be [propext, Classical.choice, Quot.sound]), and HONEST status: is the composition genuine
(real per-minute input, definitional chaining), what hyps are carried through, and the O(log n) parallel-time
reading. Be precise, do not over-claim. If rate-limited, report on-disk WIP.
