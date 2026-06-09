# Doty time-half — Avenue C3: FAITHFUL clock O(log n) via profile-inductive ClockGoodAt package

Directive: 绝对不退缩，要论文的命题不缩水. C2 (ClockOLogN.lean) is 0-sorry but CONDITIONAL/UNFAITHFUL: it
assumes the front-cap `B` (hwin) and cross-minute chaining (h_chain) rather than maintaining the profile
invariant inductively. Pro-ChatGPT audit (and the paper §6) say the faithful structure is a minute-indexed
profile-inductive package, NOT three independent same-minute regimes. C3 builds the faithful version.

## The faithful architecture (pro-ChatGPT, against Doty §6: Lemmas 6.3-6.6, Thms 6.5/6.8/6.9, footnote 9)
Per-minute composition + union bound IS faithful, BUT the per-minute "good event" is a COUPLED inductive
package, and the early-drip smallness DEPENDS on the front width (which comes from the front-tail induction):

    ClockGoodAt i :=  MinuteUpper i ∧ FrontShape i ∧ FrontWidth i ∧ EarlyDripSmall i ∧ MinuteLower i

with the central profile invariant (Theorem 6.5):
    n^{-0.4} ≤ c≥i(t) ≤ 0.1  ⟹  c≥(i+1)(t) < p · c≥i(t)²
and Lemma 6.3 (local, the 0.1-time-increment): c≥(i+1)(t) ≤ 0.9p·c≥i(t)² + d≥(i+1)(t).
Then: Pr[∀ i<N, ClockGoodAt i] ≥ 1 − Σ_{i<N} failProb i  (conditional high-prob + union over minutes, NO
independence assumed); minute_time_sum: GoodClockPrefix N → t01 N − t01 0 ≤ N·U (Lemma 6.4 per-minute upper
2.11+½ln(1/p)); N=Θ(log n) ⟹ t01 N = O(log n).

## Reuse (all proven, in Probability/)
- S2b FrontTailKernel.lean: frontTail_kernel_one_step_le_beyondSq (the c≥i+1 seed ≤ (beyond T/n)² ONE-STEP, on
  real chain) + the doubly-exp arithmetic FrontTail.frontTail_doubly_exp / frontWidth_loglog — these give
  FrontShape + FrontWidth.
- S3 EarlyDripBound.lean: earlyDrip_kernel_bound (d≥ ≤ t·(B/n)², O(n^−0.85)) — EarlyDripSmall, COUPLED to the
  front width B (B = frontWidth-derived cap, NOT a free parameter — this coupling is the faithfulness fix).
- S1 ConstantDensityEpidemic.lean + C2 clock_beyond_advance_prob: the bulk crossing 0.1→0.9 (MinuteUpper bulk).
- Framework WindowConcentration.lean: windowDrift/windowGrowth for the kernel-level wrapping.
- C2 ClockOLogN.lean: clock_beyond_advance_prob + bulkPhase REUSABLE (the bulk-transport keystone is fine).

## Task (NEW file Probability/ClockFaithful.lean)
1. Define `ClockGoodAt i` as the conjunction package above on the real clock count c≥i = beyond i / card.
2. The minute-induction step `clockGood_step : GoodPrefix i → (FrontShape ∧ FrontWidth ∧ EarlyDripSmall)(i)` —
   DERIVE the front cap at minute i+1 from the profile invariant c≥i+1 ≲ p·c≥i² (S2b one-step + Lemma 6.3
   local), and DERIVE early-drip smallness from the front width (S3 with B := the inductively-maintained front
   cap, NOT assumed). This is the coupling C2 lacked.
3. `good_clock_prefix_whp : Pr[∀ i<N, ClockGoodAt i] ≥ 1 − N·n^{−A}` — union over minutes of the package
   failure (conditional high-prob, no independence).
4. `clock_faithful_O_log_n` : GoodClockPrefix (Θ(log n)) → kernel-level (K^T) c₀ {¬synchronized} ≤ 1/poly with
   T/n = O(log n) — DISCHARGING C2's hwin + h_chain via the maintained invariant. This replaces C2's conditional
   clock_composed_O_log_n with the faithful one.

## HARD RULES (automode, NO effort cap; 绝对不退缩)
NEW file ClockFaithful.lean only; do NOT edit existing files (reuse S1/S2b/S3/framework/C2). The point is to
DISCHARGE the assumed hypotheses (front cap, chaining) via the profile induction — do NOT re-assume them. No
sorry/admit/new axiom/native_decide. Iterate lake build until clean. The hard genuine content: the minute-index
induction maintaining c≥i+1 ≲ p·c≥i² with early-drip coupled to front-width (Thm 6.5 + Lemma 6.3). If a step
genuinely needs a sub-lemma not yet built, build it honestly or STOP and report the exact gap — do NOT leave the
invariant as an abstract hypothesis (that's C2's flaw you're fixing). Do NOT git. Final message: ClockGoodAt +
the induction + clock_faithful_O_log_n statements, how the profile invariant is MAINTAINED (not assumed), how
front-cap + chaining are DISCHARGED, build verdict, #print axioms, honest status (faithful clock O(log n) proven
kernel-level, or blocked on exact sub-lemma). NOTE: launch only after BOTH ChatGPT consults (pro+extended) agree
on this architecture — the orchestrator gates this.
## REFINEMENT (both consults agree; extended-consult correction — FOLLOW THIS DAG)
BOTH ChatGPT pro+extended converge: per-minute/per-hour compose+union is faithful IFF each per-minute event is
Theorem-6.8-strength (coupled), not 3 independent regimes. KEY extended correction: Lemma 6.4 (the O(1)-per-minute
UPPER time bound = the SOURCE of O(log n)) does NOT use front/early-drip — proof is: once c≥i ≥ 0.1, drips create a
seed c≥i+1 > 0.0045p within 0.5 parallel time, then epidemic growth (S1!) brings c≥i+1 to 0.1. Front-shape (Thm 6.5)
+ early-drip are for the LOWER bound + "not too far ahead" + hour-sync, NOT the upper time bound.

Faithful dependency DAG (build in this order):
- `clock_step_upper` (Lemma 6.4): t01(i+1) − t01(i) ≤ T_up  — SEED (drip in 0.5) + EPIDEMIC (S1 bulk 0.0045p→0.1).
  THIS is the O(log n) source. Mostly S1 + a seed-creation lemma. Does NOT need S2b/S3.
- `front_with_early_shape` (Lemma 6.3 + Thm 6.5, minute induction): n^−0.4 ≤ c≥i ≤ 0.1 ⟹ c≥i+1 < p·c≥i²;
  early-drip d≥i+1 = O(n^−0.85) proved INSIDE (after front width O(log log n)). Uses S2b + S3, COUPLED.
- `clock_step_lower` (Lemmas 6.6/6.7, from front shape): T_low ≤ t01(i+1) − t01(i).
- `clock_minute_bounds` (Thm 6.8): T_low ≤ Δi ≤ T_up.
- `clock_hour_bounds` (Thm 6.9): sum over k=45 minutes/hour; start/end_h; scale 1/c².
- `all_hours_O_log_n`: union over h < L (or i < kL), L=Θ(log n) ⟹ O(log n) whp.
- expected-time: whp O(log n) path + rare slow backup (negligible) ⟹ E[time] = O(log n).

PRIORITY: clock_step_upper FIRST (it is the headline O(log n) source, S1-driven, most tractable). Then the
front-shape coupled induction for lower+sync. Naming: Lemma 6.3 = continuous-time shape (c≥i+1 ≤ 0.9p·c≥i² + d≥i+1);
d≥i+1=O(n^−0.85) is inside Thm 6.5. p=1, k=45 for the deterministic variant.
