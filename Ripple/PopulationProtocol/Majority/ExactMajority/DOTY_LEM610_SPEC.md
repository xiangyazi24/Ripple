# Doty time-half — Avenue (e): Lemma 6.10 clock→Main hour-coupling (Main doesn't run ahead of the clock)

Directive: 挨个做，绝对不退缩，不 over-claim. Lemma 6.10 is the clock→Main coupling: the small fraction of
too-fast Clock agents cannot drag too many Main/O agents above hour h. It is what lets the clock's O(log n)
timing drive the timed phases in sync. Φ(t) = m_{>h}(t) − 1.1·c_{>h}(t) is a SUPERMARTINGALE (additive).

## Definitions (on the real NonuniformMajority config)
- `mAbove h c` = `Multiset.countP (fun a => a.role = .main ∧ h < a.hour.val) c` (Main agents at hour > h).
- `cAbove h c` = `Multiset.countP (fun a => a.role = .clock ∧ (h+1)*K ≤ a.minute.val) c` (Clock agents whose
  clock-hour ⌊minute/K⌋ > h, i.e., minute ≥ (h+1)·K).
- `Φ h c = mAbove h c − 1.1 · cAbove h c` (as ℝ; can be negative — ADDITIVE supermartingale, not multiplicative).

## The drift (the heart)
The ONLY way `mAbove h` increases is the hour-drag (Phase3Transition Rule 2): an unbiased Main meets a Clock
with `⌊minute/K⌋ > h` (i.e. that Clock is counted in `cAbove h`), setting Main.hour ← min(L, ⌊minute/K⌋) > h.
So `mAbove h` can rise only when `cAbove h > 0`, and each rise consumes a (Main-below-h, Clock-above-h) pair.
The `1.1·cAbove h` slack makes `E[Φ(t+1) | F_t] ≤ Φ(t)` (supermartingale): the expected `mAbove` increase per
step is bounded by the available clock-above mass, dominated by the 1.1 factor. Prove
`∀ c, ∫⁻ ... ≤ ...` in the appropriate (additive) form.

## INFRA CHECK FIRST (do this before the main proof)
The repo has MULTIPLICATIVE `Supermartingale.geometric_drift_tail` and `Concentration.chernoff_two_sided_hoeffding`.
Lemma 6.10 needs an ADDITIVE supermartingale tail (Azuma-style: bounded-difference supermartingale ⟹ tail).
STEP 1: determine whether `chernoff_two_sided_hoeffding` (or any existing lemma) applies to a
dependent/martingale-difference sequence, OR only to independent sums. If it suffices, use it. If NOT, BUILD the
minimal additive-supermartingale tail lemma needed (Azuma–Hoeffding for a supermartingale with bounded
per-step differences) as a clean infra lemma in your file — state it generally, prove it (or, if it requires a
Mathlib martingale API genuinely absent, STOP and report the EXACT missing Mathlib lemma). Report which path
you took.

## Task (NEW file Probability/HourCoupling.lean only)
1. `mAbove`, `cAbove`, `Φ` definitions + measurability.
2. The hour-drag drift lemma: `mAbove h` rises only via a Main×(Clock-above-h) pair (from Rule 2) — prove the
   per-step bound that makes `Φ h` a supermartingale. Reuse the per-pair transition facts; the hour-drag is
   Phase3Transition Rule 2 (Main.hour ← min(L, ⌊minute/K⌋)).
3. `hour_coupling` (Lemma 6.10): the kernel-level tail — `Pr[mAbove h ≥ (something) · cAbove h + slack]` is small
   (whp Main does not exceed ~1.1× the clock-above mass) — via the additive supermartingale tail from the infra
   check. State it as a kernel-power tail bound, mirroring how geometric_drift_tail is stated.

## HARD RULES (automode, 绝对不退缩, 不 over-claim)
NEW file HourCoupling.lean only; do NOT edit existing files, do NOT weaken proven lemmas. The supermartingale
drift MUST be genuinely proven from the hour-drag mechanism (Rule 2) — never assumed. No sorry/admit/new
axiom/native_decide. If the additive tail genuinely needs a Mathlib martingale API that is absent, STOP and
report the EXACT missing lemma (do NOT fake it with the multiplicative form if it doesn't apply). Iterate `lake
build Ripple.PopulationProtocol.Majority.ExactMajority.Probability.HourCoupling` until clean. Do NOT git. Final
message: the infra-check outcome (existing lemma sufficed / built additive tail / blocked on exact Mathlib gap),
mAbove/cAbove/Φ defs, the supermartingale drift lemma, the hour_coupling statement, build verdict, #print axioms
(must be [propext, Classical.choice, Quot.sound]), HONEST status: drift genuinely proven? what carried? Be
precise, do not over-claim. If rate-limited, report on-disk WIP.
