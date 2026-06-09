# Doty time-half — discharge rEnvelope_maintained (transfer abstract front_shape_all → real) = COMPLETE the clock

Directive: 挨个做，绝对不退缩，不 over-claim. The real-kernel clock is reduced to ONE residual:
`rEnvelope_maintained` (ClockFrontWidth.lean) = the random front-fraction stays within the doubly-exp envelope
`f₀^(2^i)` along the trajectory = Doty Theorem 6.5 front-shape on the real kernel. The ABSTRACT version is a
COMPLETE theorem (`FrontShapeInduction.front_shape_all` / `frontShape_step` / `front_shape_collapse`), and the
real per-level squaring `ClockFrontWidth.rBeyond_seed_le_rBeyondSq` is PROVEN. Transfer the abstract induction
to the real count to DISCHARGE `rEnvelope_maintained` → the clock becomes unconditional whp.

## Why this should CLOSE (not reduce again)
The abstract `front_shape_all` fully proves the front-shape envelope maintenance for the abstract clock via:
`frontShape_step` (within-envelope at i ⟹ within-envelope at i+1, using the one-step squaring) iterated, plus
`front_shape_collapse`/`front_emptied_real` (the doubly-exp `f₀^(2^i) < 1/n` collapse). The REAL analog has the
SAME structure: `rBeyond_seed_le_rBeyondSq` is the real one-step squaring; `rFront_emptied_of_envelope` (already
proven in ClockFrontWidth) is the real collapse. So `rEnvelope_maintained` = re-run the abstract induction on the
real `rBeyond` count. The abstract theorem is closed, so the transfer closes.

## Reuse
- `FrontShapeInduction.lean`: `front_shape_all`, `frontShape_step`, `front_shape_collapse`, `front_width_at`,
  `front_emptied_real`, `envelope`/`envelope_step`/`FrontWithinEnvelope` (the abstract complete front-shape).
- `ClockFrontWidth.lean`: `rBeyond_seed_le_rBeyondSq` (real squaring, PROVEN), `rFront_emptied_of_envelope` (real
  collapse, PROVEN), `RWithinEnvelope`, `rFrontFrac`, `rEnvelope_maintained` (the Prop to discharge),
  `frontWidth_concentration`, `frontSync_concentration_of_capWindow`, `clock_unconditional_of_envelope`.
- `FrontSyncConc.frontSync_union_horizon`, `AzumaKernel.azuma_tail` (the union/concentration machinery).

## Task (NEW file Probability/ClockEnvMaint.lean only)
1. Transfer the abstract envelope-maintenance induction to the real count: prove that along the kernel dynamics,
   `RWithinEnvelope f₀ i` is maintained whp (the union over levels/steps of the squaring `rBeyond_seed_le_rBeyondSq`
   keeps the front within `f₀^(2^i)`), mirroring `frontShape_step` + `front_shape_all`. Use `rFront_emptied_of_
   envelope` for the collapse beyond O(log log n).
2. Prove `rEnvelope_maintained n Bcap` (the exact Prop in ClockFrontWidth).
3. Wire: `rEnvelope_maintained` + `clock_unconditional_of_envelope` (ClockFrontWidth) ⟹ the real-kernel
   `clock_real_faithful_O_log_n` with FrontSync/habs DISCHARGED whp ⟹ `clock_real_O_log_n_unconditional` :
   the O(log n) real-kernel clock carrying NO undischarged structural hypothesis (only the standard ε/t budget).

## HARD RULES (automode, 绝对不退缩, 不 over-claim)
NEW file ClockEnvMaint.lean only; do NOT edit existing files, do NOT weaken proven lemmas. The transfer MUST be
genuinely proven (re-run the abstract induction on the real count via the PROVEN real squaring), NOT assumed. Do
NOT add a false/undischargeable hyp — SIX were caught this session; do not add a 7th. If the transfer genuinely
needs an abstract-lemma generalization that doesn't apply to the real count, prove the maximal clean prefix and
STOP at the EXACT remaining sub-lemma (name it precisely). No sorry/admit/new axiom/native_decide. Iterate `lake
build Ripple.PopulationProtocol.Majority.ExactMajority.Probability.ClockEnvMaint` until clean. Do NOT git. Final
message: the envelope-maintenance transfer (genuinely proven?), whether `rEnvelope_maintained` is DISCHARGED and
the clock is NOW UNCONDITIONAL whp (give clock_real_O_log_n_unconditional statement), or reduced to a smaller
named sub-lemma, build verdict, #print axioms (must be [propext, Classical.choice, Quot.sound]), HONEST status.
If rate-limited, report on-disk WIP.
