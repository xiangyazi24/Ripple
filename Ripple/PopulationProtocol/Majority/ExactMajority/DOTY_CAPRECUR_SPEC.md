# Doty time-half — discharge CapRelRecurrence (cap-relative probabilistic front concentration)

Directive: 挨个做，绝对不退缩，不 over-claim. The cap-relative front-shape (ClockCapRelFront.lean) rests on two
residuals: `CapRelWithinEnvelope` (bulk-top fraction ≤ ρ₀<1, the genuine bulk condition) and `CapRelRecurrence`
(the per-level within-envelope maintenance). `CapRelRecurrence`, if a DETERMINISTIC ∀c per-level squaring, is the
wrong (false) form — the one-step squaring `rBeyond_seed_le_rBeyondSq` is PROBABILISTIC. Discharge
`CapRelRecurrence` PROBABILISTICALLY via a cap-relative level-union (the correctly-indexed analog of the proven
`FrontSyncConc.feeder_narrow_concentration`), leaving the clock on ONLY `CapRelWithinEnvelope`.

## The design
The front levels cap-W..cap (W=frontWidthBound n) are near-empty (above the bulk-top). The PROVEN per-level
empty-seed squaring `rBeyond_seed_le_rBeyondSq` bounds seeding each from below. Level-union over the W front
levels (à la `frontSync_union_horizon`/`feeder_narrow_concentration`, at cap-relative levels cap-j, j=1..W) of
the per-step seed probs (each ≤ env(j), doubly-exp) gives: whp the front fraction stays within the cap-relative
envelope, i.e. `CapRelRecurrence` holds whp — GIVEN the bulk-top fraction `CapRelWithinEnvelope` (the seed at the
bulk-top cap-W is bounded by ρ₀). So the recurrence is discharged probabilistically, bottoming out at ONLY
`CapRelWithinEnvelope`.

## Task (NEW file Probability/ClockCapRecur.lean only)
1. `capRel_recurrence_concentration`: prove `CapRelRecurrence` holds whp via the level-union over the front
   levels, GIVEN `CapRelWithinEnvelope` (bulk-top fraction ≤ ρ₀). Reuse `rBeyond_seed_le_rBeyondSq` + the
   doubly-exp envelope + the union machinery. GENUINE, not assumed.
2. Wire into `ClockCapRelFront.capRel_frontSync_concentration` so the clock FrontSync-whp rests on ONLY
   `CapRelWithinEnvelope` (the single genuine bulk/synchronization condition, TRUE while the clock runs — the
   bulk is at minutes below cap-W). Deliver `clock_frontSync_via_capRel` carrying only it.
3. HONEST: report whether the clock now rests on the SINGLE bulk-top fraction condition, or if discharging
   CapRelRecurrence needs a per-level fact beyond the empty-seed squaring (the m→m+1 at occupied front levels) —
   if so, prove the maximal clean prefix and STOP at the exact named residual.

## BUILD ROUTING (important)
Per infra: heavy `lake build` on the 24GB mini is constrained. PREFER `lake env lean <file>` (single-file check,
fast, allowed) for iterating. For a full module build use `scripts/remote-build.sh Ripple` (runs on uisai1) OR a
single local `lake build Ripple.PopulationProtocol.Majority.ExactMajority.Probability.ClockCapRecur` ONLY if you
confirm mini memory is free (memory_pressure shows >50% free) and run it ALONE (no concurrent builds). Do single-
file `lake env lean` checks while developing; one full build at the end.

## HARD RULES (automode, 绝对不退缩, 不 over-claim)
NEW file ClockCapRecur.lean only (you MAY edit ClockCapRelFront.lean to rewire if needed — sole writer); do NOT
weaken proven lemmas; do NOT touch other files. The concentration MUST be genuinely proven (level-union over the
PROVEN squaring + doubly-exp envelope), NEVER assumed. Do NOT add a false/undischargeable hyp — NINE issues
caught this session; do NOT add a 10th. The carried residual MUST be the genuine cap-relative bulk-top fraction
(TRUE while running), NOT the false absolute-low/deterministic forms. No sorry/admit/new axiom/native_decide.
Do NOT git. Final message: the recurrence concentration (genuine level-union?); whether the clock now rests on
the SINGLE bulk-top fraction or a smaller named residual; build verdict; #print axioms (must be [propext,
Classical.choice, Quot.sound]); HONEST status. If rate-limited, report on-disk WIP.
