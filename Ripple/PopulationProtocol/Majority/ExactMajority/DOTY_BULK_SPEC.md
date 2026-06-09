# Doty time-half — Avenue (a'): real-kernel BULK clock crossing 0.1mC→0.9mC (faithful O(1)/minute, = C3)

Directive: 挨个做，绝对不退缩，不 over-claim. Course-correction: (a)/(d) targeted FULL crossing
(rBeyond(T+1)=mC) ⟹ Θ(log²n) + needed the false-near-completion hfrontier. The FAITHFUL decomposition (C3's):
each minute only needs **0.9-BULK crossing** of the cumulative tail, via the constant-fraction epidemic, where
the front is WIDE throughout (c² genuinely uniform, hfrontier genuinely TRUE in [0.1,0.9]mC). This gives O(1)
parallel per minute ⟹ O(log n) total. Mirror C3 `clock_step_upper` (seed + epidemic) on the REAL kernel.

## The faithful target (the bulk window, where hfrontier is genuinely true)
On the minute-marginal: "infected" = clocks at minute ≥ T+1 (count `rBeyond(T+1)`), "susceptible" = clocks at
minute = T (count `mC − rBeyond(T+1)`, since all mC clocks are at minute ≥ T in the level-T floor). Advance of
`rBeyond(T+1)`:
- EPIDEMIC/sync: an infected (minute ≥T+1) meets a susceptible (minute T) → sync pulls susceptible up to ≥T+1
  (`rEpidemic_pair_advances` in ClockRealAdvance.lean). Ordered-pair mass = rBeyond(T+1)·(mC−rBeyond(T+1)) /
  (n(n−1)). In the window rBeyond(T+1) ∈ [0.1mC, 0.9mC], BOTH factors ≥ 0.1mC ⟹ advance prob ≥
  0.01·(mC/n)² = Θ(c²), GENUINELY UNIFORM (front wide both sides — hfrontier TRUE here, no false assumption).
- This is the S1 `ConstantDensityEpidemic` pattern (0.1→0.9 in O(1) parallel, ln 9 ≈ 2.2), on the real kernel.

## Task (NEW file Probability/ClockRealBulk.lean only)
1. `clock_real_advance_bulk` : a `PhaseConvergence (NonuniformMajority L K).transitionKernel` with
   Pre = `Q_mix-like floor ∧ ⌊mC/10⌋ ≤ rBeyond(T+1)` (already at 0.1mC infected),
   Post = `⌊9·mC/10⌋ ≤ rBeyond(T+1)` (0.9mC infected), t = O(n/c²) interactions (= O(1) parallel for constant c),
   ε = exp(−Θ(mC)) — the constant-fraction epidemic crossing. Build via `windowDrift_PhaseConvergence` with the
   epidemic potential (susceptible count, exponential window) and the SYNC advance probability above.
2. The contraction r = 1 − 0.01·(mC/n)²·(1−e^{−s}) (or the S1 form) is DERIVED in the [0.1,0.9] window from
   interactionCount/totalPairs — here the (mC−m)·m product floor `≥ 0.01·mC²` is GENUINELY TRUE (both factors
   ≥ 0.1mC), NOT a carried false hypothesis. Prove that floor as a lemma (not assume it).
3. Reuse: rEpidemic_pair_advances / rDripDistinct_pair_advances (ClockRealAdvance.lean), rBeyond,
   hmono_mix_discharged (ClockMonoDischarge.lean), the S1 ConstantDensityEpidemic.lean patterns
   (windowPot_contracts_on_floor, constantDensity_epidemic_O1_parallel — MIRROR these), windowDrift framework.

## HARD RULES (automode, 绝对不退缩, 不 over-claim)
NEW file ClockRealBulk.lean only; do NOT edit existing files, do NOT weaken proven lemmas. No
sorry/admit/new axiom/native_decide. The bulk-window product floor (m·(mC−m) ≥ 0.01·mC² on [0.1mC,0.9mC]) MUST
be PROVEN (it is genuinely true here — this is the whole point of switching to bulk), NOT carried as a
hypothesis. Target Post is 0.9-crossing, NOT full crossing. Iterate `lake build
Ripple.PopulationProtocol.Majority.ExactMajority.Probability.ClockRealBulk` until clean. Do NOT git. Final
message: clock_real_advance_bulk signature verbatim, the proven product-floor lemma, build verdict, #print
axioms (must be [propext, Classical.choice, Quot.sound]), HONEST status: is the c² contraction GENUINELY proven
in the bulk window (product floor proven, not assumed)? what (if anything) is still carried? This replaces the
full-crossing (a) with the faithful bulk crossing. If rate-limited, report on-disk WIP.
