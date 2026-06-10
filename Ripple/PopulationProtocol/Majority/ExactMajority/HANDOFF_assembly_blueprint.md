(saved from family2 letter, full version — the assembly design of record, SUPERSEDING the
self-derived "averaged composition" section: the cost-valued weak composition is the same
mathematical content in cleaner Lean shape. Key deltas vs the self-derived design:
- PhaseConvergenceWC: convergence ∀ x, Pre x → (K^t) x {¬Post} ≤ ε + cost x  (cost-valued, not averaged)
- composeW_n_phases_cost_constTime: integrates per-leg costs over the prefix law (hcost inputs escB i)
- legEscCost + legEscCost_integral_le_global: the exact local→global reconciliation
- Side gates settled: deterministic skeleton (card/crossedT T≥1/allPhaseGE3/clockSize =
  habs_mix_deterministic_skeleton) vs whp gates (noPhaseAbove3, allClocksCounterPos) folded into
  HabsSide ⊆ S; the single named one-step obligation = hstepEsc (ClockPhase3_remaining_synchronization
  shape); GoodFrontWidth/bulk-below/FrontSync conjuncts fed by the landed bridges
- Endpoint clock_real_faithful_O_log_n_W + parallel-time wrapper + retire list (ClockRealFaithfulHours
  4 strong consumers + ClockRealHours 3 full-crossing consumers; KEEP the drift lemmas/Q_mix_succ_of_post/
  deterministic skeletons/WidthPrefix/bridges))
---- FULL LETTER BELOW ----

# The cost-valued weak composition (the recommended layer 2)

## New structure (next to PhaseConvergenceWeak.lean)

```lean
structure PhaseConvergenceWC {Ω} [MeasurableSpace Ω] [DiscreteMeasurableSpace Ω] (K : Kernel Ω Ω) where
  Pre : Ω → Prop
  Post : Ω → Prop
  t : ℕ
  ε : ℝ≥0∞
  cost : Ω → ℝ≥0∞
  convergence : ∀ x, Pre x → (K ^ t) x {y | ¬ Post y} ≤ ε + cost x
```

## Constant-time cost composition

```lean
theorem composeW_n_phases_cost_constTime
    {m : ℕ} (hm : 0 < m) (M : ℕ)
    (phases : Fin m → PhaseConvergenceWC K)
    (ht : ∀ i, (phases i).t = M)
    (h_chain : ∀ (i : Fin m) (hi : i.val + 1 < m), ∀ x, (phases i).Post x → (phases ⟨i.val+1, hi⟩).Pre x)
    (x₀ : Ω) (hx₀ : (phases ⟨0, hm⟩).Pre x₀)
    (escB : Fin m → ℝ≥0∞)
    (hcost : ∀ i : Fin m, ∫⁻ x, (phases i).cost x ∂((K ^ (i.val * M)) x₀) ≤ escB i) :
    (K ^ (m * M)) x₀ {y | ¬ (phases ⟨m-1, by omega⟩).Post y} ≤
      (∑ i : Fin m, (phases i).ε) + ∑ i : Fin m, escB i
-- proof: same induction as composeW_n_phases; on the successful-prefix branch each phase
-- contributes ε_i + cost_i(x); integrate cost over the prefix law, use hcost.
```

## Per-leg cost + the local→global reconciliation

```lean
def legEscCost (T M : ℕ) (S : Set (Config (AgentState L K))) (q : ℝ≥0∞) (c) : ℝ≥0∞ :=
  (M : ℝ≥0∞) * q + ∑ τ ∈ Finset.range M, ((NonuniformMajority L K).transitionKernel ^ τ) c Sᶜ

lemma legEscCost_integral_le_global ... :
    ∫⁻ c, legEscCost T M (S i) (q i) c ∂((κ ^ (i.val * M)) c₀)
      ≤ (M : ℝ≥0∞) * q i + ∑ τ : Fin M, sideB i τ
-- proof given in full in the letter: lintegral_add_left (fun_prop), lintegral_const +
-- measure_univ for the q part; lintegral_finset_sum + Kernel.pow_add_apply_eq_lintegral
-- collapse (K^{i·M+τ}) for the side part, bounded by hside_global.
```

## Cost-valued minute phase (replaces uniform-εesc clock_real_step_gatedW)

```lean
clock_real_step_gatedWC (n mC T ...) (S : Set Config) (q : ℝ≥0∞)
    (hstepEsc : ∀ c, c ∈ {Q_mix n mC T} → c ∈ S → κ c {Q_mix n mC T}ᶜ ≤ q)
    (hεs hεb ...) : PhaseConvergenceWC κ where
  Pre := Q_mix ∧ 0.9-floor at T;  Post := Q_mix ∧ bulkHi ≤ rBeyond (T+1)
  t := tseed + tbulk;  ε := εseed + εbulk
  cost := legEscCost T (tseed+tbulk) S q
  convergence := -- real bad ≤ killed none + killed alive-bad (real_le_killed_now);
                 -- alive-bad ≤ εseed+εbulk (killed phases); none ≤ M·q + ∑_{τ<M} (K^τ)c₀ Sᶜ
                 -- (kill_now_escape_le_prefix_union INLINED, not a uniform εesc)
```

## Minute family + all-minutes (proof body in letter — chain via Q_mix_succ_of_post verbatim)

faithfulMinutePhasesWC (S q hstepEsc per leg) : Fin L₀ → PhaseConvergenceWC κ
clock_real_faithful_all_minutes_W: inputs sideB : ∀ i, Fin M → ℝ≥0∞ +
  hside_global : ∀ i τ, (κ ^ (i·M+τ)) c₀ (S i)ᶜ ≤ sideB i τ  ← THE WidthPrefix/DotyParams feed point
  conclusion ≤ ∑(εseed+εbulk) + ∑_i (M·q i + ∑_τ sideB i τ)

# Side gates audit (settled)

DETERMINISTIC (do NOT budget; use inside hstepEsc): HabsDischarge.qmix_card_closed;
qmix_crossedT_closed (T ≥ 1; T=0 excluded — chain handles all T+1 starts);
allPhaseGE3_closed; qmix_clockSize_closed (under allPhaseGE3);
packaged: habs_mix_deterministic_skeleton (card ∧ clockSize ∧ crossedT ∧ allPhaseGE3 closure).

WHP (into S i, charged via sideB): noPhaseAbove3, allClocksCounterPos, and the SINGLE remaining
named obligation = hstepEsc itself (the ClockPhase3_remaining_synchronization shape — do NOT
reintroduce as global deterministic habs_mix_all). Suggested side shape:
  HabsSide W i c := allPhaseGE3 ∧ noPhaseAbove3 ∧ allClocksCounterPos ∧ GoodFrontWidth W c
  (+ bulk-below 10·rBeyond(capMinute−W) < card ∧ FrontSync as needed by the hstepEsc proof).
GoodFrontWidth failure → sideB via WidthPrefix.goodFrontWidth_whp_at; FrontSync / cap-feeder
conversions via ClockFrontSyncFromWidth bridges.

# Endpoint + wrapper + retire list

clock_real_faithful_O_log_n_W: minutes := K*(L+1); start from eraseConfig mc₀ (the marked-chain
origin — hside_global is stated there, matching WidthPrefix); hypothesis list = N₀ ≤ n + hεs/hεb +
S/q/hstepEsc + sideB/hside_global + start Q_mix∧floor. Parallel-time wrapper mirrors
ClockOLogN.clock_O_log_n with uniform M (proof given in letter: div_le_iff₀ + gcongr).

RETIRE (assembly consumers): ClockRealFaithfulHours.{minuteStepPhase, faithfulMinutePhases,
clock_real_faithful_all_minutes, clock_real_faithful_O_log_n}; ClockRealHours.{mixedMinutePhases,
clock_real_all_minutes, clock_real_O_log_n}.
KEEP (load-bearing): rSeedPot_contracts_seed/bulk, Q_mix_succ_of_post, HabsDischarge.*_closed
skeletons, WidthPrefix.goodFrontWidth_whp_at, ClockFrontSyncFromWidth bridges.
