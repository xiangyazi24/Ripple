# Doty time-half — rFrontNarrow_concentration (genuine Thm 6.5) + refactor → CLOSE the clock whp

Directive: 挨个做，绝对不退缩，不 over-claim. The clock's irreducible residual is `rFrontNarrow_concentration`
(ClockEnvMaint.lean, ClockFrontWidth uses a WRONG deterministic-∀c `rEnvelope_maintained`). Prove the TRUE
probabilistic front-narrowness via a LEVEL-UNION over the PROVEN per-level squaring, then refactor the chain to
use it → unconditional clock whp. Editing the chain files IS authorized here (the refactor needs it).

## The genuine concentration (level-union over the squaring) — the design
The PROVEN `ClockFrontWidth.rBeyond_seed_le_rBeyondSq`: if level `T+1` is empty, one step seeds it with prob
≤ (rBeyond T c / n)². Define the doubly-exp envelope `env i = f₀^(2^i)` (`FrontTailKernel.envelope`). The
front-narrowness:
- "Within-envelope at level i" := `rBeyond i c ≤ ⌊n · env i⌋`. Conditioned on within-envelope at level i, the
  seed prob for level i+1 is ≤ (env i)² = env (i+1) (`envelope_step`). So the envelope is a SUPERMARTINGALE-style
  envelope maintained level-to-level with per-level slip prob ≤ env(i+1).
- BAD event = "some level i in (B, capLevel] exceeds env i for the FIRST time" (level i-1 within, level i not).
  `P[BAD] ≤ Σ_{i>B} (slip prob at i) ≤ Σ_{i>B} env i = Σ_{i>B} f₀^(2^i)`. The doubly-exp sum: with
  `B = frontWidthBound n = O(log log n)`, `env B < 1/n²`, so `Σ_{i>B} env i < 1/poly`.
- Hence `P[front extends beyond B] ≤ 1/poly` = `rFrontNarrow_concentration`. Use the kernel-power / union
  machinery (`FrontSyncConc.frontSync_union_horizon` pattern, or a fresh finite level-union via
  `Finset.sum` over levels) — over LEVELS i, not horizon minutes. Reuse the abstract
  `FrontTail.front_emptied_at_width` / `frontWidth_loglog` doubly-exp arithmetic for the sum bound.

## Task
1. NEW file `Probability/FrontNarrowConc.lean`: prove `rFrontNarrow_concentration f₀ n H ε` (the EXACT Prop in
   ClockEnvMaint.lean / the probabilistic front-narrowness) at `ε = 1/poly` via the level-union above. The
   per-level slip uses `rBeyond_seed_le_rBeyondSq`; the doubly-exp sum uses the envelope arithmetic. GENUINE,
   no false hyp.
2. REFACTOR (authorized — you are sole writer of these for this task): in `ClockFrontWidth.lean`, change
   `rEnvelope_maintained` from the deterministic-∀c form to consume the probabilistic `rFrontNarrow_concentration`
   (or add the probabilistic theorem and rewire `frontSync_concentration_of_capWindow` / `clock_unconditional_of_
   envelope` to it). In `ClockEnvMaint.lean`, discharge the conditional wiring using the now-proven concentration.
3. Deliver `clock_real_O_log_n_unconditional` (or equivalently `clock_real_faithful_O_log_n` with FrontSync/habs
   DISCHARGED whp) — the real-kernel O(log n) clock carrying NO undischarged structural hypothesis (only the
   standard ε/t budget), 0-sorry, axioms clean.

## HARD RULES (automode, 绝对不退缩, 不 over-claim)
The concentration MUST be genuinely proven (level-union over the PROVEN squaring + doubly-exp envelope sum),
NEVER assumed. Do NOT add a false/undischargeable hyp — SEVEN were caught this session; do NOT add an 8th. You
MAY edit ClockFrontWidth.lean / ClockEnvMaint.lean / FrontSyncConc.lean for the refactor (sole writer), but do
NOT weaken any PROVEN lemma elsewhere and do NOT touch other files. No sorry/admit/new axiom/native_decide. If
the level-union genuinely needs a Mathlib/infra atom that's absent, build the minimal piece or STOP and report
the EXACT gap. Iterate `lake build` (each touched module, then the whole ExactMajority.Probability tree) until
clean. Do NOT git. Final message: the rFrontNarrow_concentration proof (level-union genuine?), the refactor done,
whether the clock is NOW UNCONDITIONAL whp (give the final theorem statement VERBATIM + confirm it has NO
undischarged structural hyp) or the exact remaining gap, build verdict, #print axioms (must be [propext,
Classical.choice, Quot.sound]), HONEST status. If rate-limited, report on-disk WIP + which modules compile.
