# Doty time-half — generalize front-narrowness to ALL front levels → discharge hfeeder_all → close clock

Directive: 挨个做，绝对不退缩，不 over-claim. `FrontNarrowConc.feeder_narrow_concentration` PROVES the feeder
level (cap−1) stays empty whp (level-union over the proven squaring). The residual `hfeeder_all` (within-envelope
at cap−2) is the SAME front-narrowness one level down: cap−2 is also beyond `frontWidthBound n = O(log log n)`, so
`env(cap−2) < 1/n` (front_shape_collapse) ⟹ within-envelope at cap−2 ⟺ rBeyond(cap−2)=0. Generalize the proven
one-level concentration to ALL front levels `j ≥ frontWidthBound` → the whole front is empty whp → discharge
`hfeeder_all` → unconditional clock whp.

## The design (generalize, do not re-derive)
- The PROVEN per-step slip `FrontNarrowConc.rNarrow_breach_le_envCap` / `feeder_narrow_concentration` is stated
  for the feeder level. Re-instantiate / generalize it to an arbitrary front level `j` with `frontWidthBound n ≤
  j < cap`: `(K^H) c₀ {1 ≤ rBeyond j} ≤ H·ofReal(env j)` (same level-union, level `j` instead of cap−1).
- Union over the front levels `j ∈ [frontWidthBound n, cap)`: `P[∃ j in front, rBeyond j ≥ 1] ≤ Σ_j H·env j ≤
  H · Σ_j env j < 1/poly` (the doubly-exp envelope sum, `front_shape_collapse`'s `env j < 1/n` for
  `j ≥ frontWidthBound`). So WHP the ENTIRE front (all levels ≥ frontWidthBound) is empty.
- Whole-front-empty ⟹ `RWithinEnvelope f₀ (cap−2)` (since rBeyond(cap−2)=0 ≤ n·env(cap−2)) and feeder-empty ⟹
  exactly `hfeeder_all`'s conclusion. Discharge `hfeeder_all` from this whole-front concentration (it becomes a
  theorem about the reachable/whp trajectory, not a false ∀c — the whp form).

## Task
1. NEW file `Probability/FrontAllLevels.lean` (or extend FrontNarrowConc if cleaner — but prefer NEW file):
   prove `frontAll_empty_concentration` = `(K^H) c₀ {¬ (∀ j ∈ [frontWidthBound, cap), rBeyond j = 0)} ≤ 1/poly`,
   by the level-union over all front levels (generalize feeder_narrow_concentration; reuse rBeyond_seed_le_rBeyondSq
   + envelope + frontSync_union_horizon + the doubly-exp sum).
2. Discharge the carried `hfeeder_all` (the within-envelope at cap−2 from whole-front-empty) — feed it into
   `FrontNarrowConc.clock_frontSync_via_narrow` (or rewire) so the clock FrontSync-breach bound carries NO
   `hfeeder_all` (only the standard ε/t budget + the true `hcollapse` env<1/n which is arithmetic).
3. Deliver `clock_real_O_log_n_unconditional_whp` : the real-kernel O(log n) clock with FrontSync/habs DISCHARGED
   whp, carrying NO undischarged structural hypothesis (only ε/t + arithmetic collapse). 0-sorry, axioms clean.

## HARD RULES (automode, 绝对不退缩, 不 over-claim)
The whole-front concentration MUST be genuinely proven (level-union over the PROVEN squaring + doubly-exp sum),
NEVER assumed. Do NOT add a false/undischargeable hyp — EIGHT shapes were caught this session; do NOT add a 9th.
You MAY edit FrontNarrowConc.lean / ClockEnvMaint.lean to rewire (sole writer); do NOT weaken proven lemmas; do
NOT touch other files. No sorry/admit/new axiom/native_decide. If discharging hfeeder_all genuinely needs a fact
beyond the whole-front concentration (e.g. AllClockP3 maintenance), prove it or STOP and name the EXACT residual.
Iterate `lake build` until the touched tree is clean. Do NOT git. Final message: the whole-front concentration
(genuine?), whether hfeeder_all is DISCHARGED and the clock is NOW unconditional whp (final theorem VERBATIM +
confirm NO undischarged structural hyp), or the exact remaining residual, build verdict, #print axioms (must be
[propext, Classical.choice, Quot.sound]), HONEST status. If rate-limited, report on-disk WIP + compiling modules.
