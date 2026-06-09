# Doty time-half — real-kernel front-width concentration (the genuine final clock gap)

Directive: 挨个做，绝对不退缩，不 over-claim. FrontSyncConc reduced the clock to `hwin_all` (feeder ≤ B for
FrontSync configs). That is FALSE as a ∀c/deterministic bound (clocks can bunch at cap−1). The GENUINE statement
is PROBABILISTIC: the leading front stays O(log log n) wide WHP, by the doubly-exponential squaring — i.e. the
real-kernel transfer of `FrontShapeInduction.frontWidth_loglog`. Build that concentration; it discharges
`hwin_all` in its correct (probabilistic, over-the-dynamics) form and completes the clock.

## The content (doubly-exp front tail on the real kernel)
The per-minute seed of a new leading front level squares (PROVEN: `ClockFrontShape.real_front_advance_squares`:
seed prob ≤ (front-feeder/n)²). Iterating the squaring over leading levels gives a doubly-exponential decay, so
the front beyond width `B = O(log log n)` is empty WHP. This is exactly the abstract `frontWidth_loglog`
mechanism (FrontShapeInduction.lean / FrontTailKernel.lean) — transfer it to the real-kernel feeder count
`frontMinuteCount`.

## Reuse
- `ClockFrontShape.real_front_advance_squares` / `_cap` (the PROVEN per-level squaring on the real kernel).
- `FrontShapeInduction.lean`: `frontShape_step`, `front_width_at`, `frontWidth_loglog`, `front_emptied_real`,
  `envelope`/`envelope_step` (the doubly-exp envelope `f₀^(2^i)` and the O(log log n) width arithmetic).
- `FrontTailKernel.lean`: `frontTail_kernel_one_step_le_beyondSq`, the doubly-exp arithmetic.
- `FrontSyncConc.frontSync_union_horizon` (the kernel union-bound machinery) and/or `AzumaKernel.azuma_tail`.

## Task (NEW file Probability/ClockFrontWidth.lean only)
1. Define the real-kernel front-width event `FrontWidthWHP B c` and the leading-level seed recurrence (the front
   beyond level `T` is empty unless seeded, seed prob ≤ square — `real_front_advance_squares`).
2. Prove the doubly-exponential decay: iterating the squaring over leading levels, the probability that the front
   extends beyond width `B = O(log log n)` is ≤ 1/poly (the kernel-level transfer of `frontWidth_loglog`). Use the
   `envelope f₀^(2^i)` doubly-exp arithmetic + the union machinery.
3. Conclude `frontWidth_concentration` : `(K^t) c₀ {¬ FrontFeederWindow n B}` ≤ 1/poly for `B = O(log log n)` —
   i.e. WHP the feeder ≤ B throughout. This is the correct (probabilistic) form of `hwin_all`.
4. Wire: feed it (in the over-the-dynamics form the union bounds consume) to discharge
   `FrontSyncConc.frontSync_concentration_remaining_proven`'s `hwin_all` along the trajectory ⟹ FrontSync holds
   whp ⟹ (with the existing `habs_mix_full` wiring) the clock invariant holds whp ⟹ the real-kernel O(log n)
   clock is UNCONDITIONAL whp (carrying only the standard ε/t budget).

## HARD RULES (automode, 绝对不退缩, 不 over-claim)
NEW file ClockFrontWidth.lean only; do NOT edit existing files, do NOT weaken proven lemmas. The doubly-exp decay
MUST be genuinely proven (iterate the PROVEN squaring + the doubly-exp envelope arithmetic), NOT assumed. Do NOT
add a false/undischargeable hyp — SIX such were caught this session; do not add a 7th. THIS IS GENUINELY HARD
(the doubly-exp front-tail concentration on the real kernel). If a step needs a transfer that doesn't go through
cleanly, prove the maximal clean prefix and STOP at the EXACT remaining sub-lemma (name it precisely). No
sorry/admit/new axiom/native_decide. Iterate `lake build
Ripple.PopulationProtocol.Majority.ExactMajority.Probability.ClockFrontWidth` until clean. Do NOT git. Final
message: the front-width event + recurrence, the doubly-exp decay proof (genuine?), whether `hwin_all`/the clock
is NOW unconditional (whp) or reduced to a smaller named sub-lemma, build verdict, #print axioms (must be
[propext, Classical.choice, Quot.sound]), HONEST status. If rate-limited, report on-disk WIP.
