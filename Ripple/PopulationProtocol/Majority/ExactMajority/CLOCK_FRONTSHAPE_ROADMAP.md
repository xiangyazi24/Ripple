# Clock front-shape formalization roadmap (C-A) — from Doty §6, via ChatGPT cross-check (2026-06-13)

This is the formalization skeleton for the DEEPEST remaining residual of `doty_theorem_3_1`:
the real-kernel front-WIDTH / FrontSync maintenance (`ClockFrontWidth.hcap_all` /
`FrontSyncConc.hwin_all` / `rEnvelope_maintained`). Mapped to Doty et al. (arXiv:2106.10201v2) §6.

## The key correction (why the naive within-envelope maintenance is FALSE)

The clean recurrence `c_{≥i+1} ≤ p·c_{≥i}²` does NOT hold pointwise at tiny tail masses: a single
lucky drip makes `c_{≥i+1} = 1/n` even when `c_{≥i}² ≪ 1/n`. Doty's Lemma 6.3 carries an
**early-drip ghost term** `d_{≥i+1}`:

    Lemma 6.3:   c_{≥i+1}(t) ≤ 0.9·p·c_{≥i}(t)² + d_{≥i+1}(t),   valid for  n^{−0.45} ≤ c_{≥i} ≤ 0.1.

The early-drip carve-out is ESSENTIAL — it is the reason a bare deterministic envelope-maintenance
(what I initially considered) is unsound. Formalize the transfer as a **cumulative-tail theorem with
an early-drip ghost term**, NOT a raw per-level profile.

## The proof skeleton (Lemma 6.3 local window argument)

Fix a constant time window τ = 1/10. Let x = X_i, y = X_{i+1} − D_{i+1}.
1. Epidemic growth lower bound:  x(t−τ) ≤ a·x(t)   (epidemic hitting-time, Doty Lemma 4.5).
2. Immigration upper bound (Chernoff): non-early-drip immigrants in [t−τ,t] ≤ b·p·x(t)².
3. Epidemic amplification (Janson, Thm 4.3 / Cor 4.4):  y(t) ≤ γ·(y(t−τ)+Imm).
Close with constants satisfying  γ(K·a² + b) < K.  Lean-friendly rationals (τ=1/10):

    a = 167/200,  b = 101/1000,  γ = 123/100,  K = 9/10
    ⟹  (123/100)·( (9/10)(167/200)² + 101/1000 ) < 9/10   ✓   (avoids paper's decimals)

Early-drip negligibility (second induction):  D_{i+1}(t^{0.1}_{≥i}) = O(n^{−0.85}).
Drips while X_i < n^{−0.45} occur with prob ≤ p·n^{−0.9} per interaction; epidemic cannot amplify
to n^{−0.85} in only O(log log n) parallel time (would need Ω(log n)). Then for X_i ≥ n^{−0.4},
D_{i+1} ≪ X_i², so Lemma 6.3 upgrades to the clean **Theorem 6.5**:

    n^{−0.4} ≤ c_{≥i} ≤ 0.1   ⟹   c_{≥i+1} < p·c_{≥i}²    (w.v.h.p.)

## Front-width O(log log n) (Theorem 6.5's internal claim)

T = t^+_{≥i} (first arrival at minute i). With k = i − log log n: if c_{≥k}(T) < n^{−0.4}, the IH
gives c_{≥k+1} ≤ p·c_{≥k}² < n^{−0.8}, so a drip above k+1 has prob ≤ n^{−1.6}/interaction; getting
log log n such drips in O(log log n) time is n^{−ω(1)} — contradiction. So c_{≥k}(T) ≥ n^{−0.4}.
Iterate back another log log n levels (square-root growth): c_{≥i−2 log log n}(T) ≥ 0.1.
Hence front width ≤ 2⌈log₂ log n⌉ + O(1). This matches our deterministic `FrontTailDecay.frontWidth_loglog`
(`frontWidthBound n = Nat.clog 2 (Nat.clog 2 n + 1)`), which consumes the clean recurrence above threshold.

## The Lean-friendly transfer target

    Pr[ ∀ i,t.  n^{−0.4} ≤ X_i(t) ≤ 0.1  ⟹  X_{i+1}(t) ≤ p·X_i(t)² ]  ≥  1 − n^{−ω(1)}.

Then `frontWidth_loglog` applies to a_r = X_{b+r}(t), b = largest level with X_b ≥ 0.1, stopping at
X < n^{−0.4}. ONE sparse-pioneer / no-long-early-drip lemma is still needed for the sub-n^{−0.4} regime.
Protocol thinning: only fraction c=|C|/n are Clock; thin clock-clock interactions by c² (Thm 6.9 scaling).

## The LEANER bypass for Theorem 3.1 (recommended for the overall headline)

The majority part needs only an **hour-level** `ClockHourGood` event, NOT the full per-minute profile:
- ∀h.  end_h − start_h ≥ α            (hour has positive constant length)         — Thm 6.9
- ∀h.  start_{h+1} − start_h ≤ β       (consecutive hours start within const time) — Thm 6.9
- ∀h,t≤end_h.  m_{>h}(t) ≤ η           (fast clocks pull few Mains ahead)          — Lemma 6.10

Thm 6.9 (p=1, k minutes/hour, fraction c): length ≥ (1/c²)(0.45k−3.1), start gap ≤ (1/c²)(2.11k+2.2);
k=45 ⟹ all L=Θ(log n) hours finish in O(log n). The lower-bound proof needs only the TWO-level tail
`c_{≥(h+1)k} ≤ (0.1²)² = 10^{−4}` from Thm 6.5 (weaker than the full envelope, enough for O(log n)).

**Lemma 6.10 IS a clean Azuma supermartingale** (the one genuinely clean piece): with
Φ(t) = m_{>h}(t) − 1.1·c_{>h}(t), clock updates raise Φ but clock-clock epidemic lowers it faster in
expectation ⟹ m_{>h} ≤ 0.0012 until end_h. Ripple already has `DiscreteFreedman`/`bernstein_optimal`
(`Ripple/Probability/`) — the Azuma tool for this.

Minimal clock-side obligation for `ClockHourGood`:
    c_{≥r+2}(t^{0.1}_{≥r}) ≤ 10^{−4}   for hour-boundary minutes r=(h+1)k−2,  + const hitting-time bounds.

## Lemma 6.10 — the Azuma/Freedman recipe (ChatGPT-derived 2026-06-13, ready to formalize)

Potential (ROLE-normalized, not whole-population): with m_{>h}=M_{>h}/|M|, c_{>h}=C_{>h}/|C|,
    Φ(t) = m_{>h}(t) − 1.1·c_{>h}(t).
(Whole-pop form: Φ = (M_{>h}/n)/m₀ − 1.1·(C_{>h}/n)/c₀, m₀=|M|/n, c₀=|C|/n. Using bare M_{>h}/n − 1.1 C_{>h}/n is NOT the supermartingale.)

Two driving reactions (per interaction, paper normalization):
| reaction | prob | ΔΦ |
| Clock pulls Main  C_{>h},M_{≤h} → C_{>h},M_{>h} | 2c·c_{>h}·m(1−m_{>h}) | +1/|M| |
| Clock epidemic    C_{>h},C_{≤h} → C_{>h},C_{>h} | 2c²·c_{>h}(1−c_{>h}) | −1.1/|C| |
(Reaction 1 = Phase-3 Line 9, unbiased Main sets hour from Clock; reaction 2 = clock max-minute epidemic Line 3.
Clock drips crossing h and Main-split consuming O-agents only DECREASE Φ — ignored, they help.)

One-step drift:  E[ΔΦ|F_t] ≤ (2c·c_{>h}/n)·((1−m_{>h}) − 1.1(1−c_{>h})).
Until end_h, c_{>h} ≤ 0.001 ⟹ bracket ≤ 1 − 1.1·0.999 = −0.0989 < 0 ⟹ stopped process is a supermartingale.

FREEDMAN PARAMETERS (the Lean plug-in for Ripple `discrete_freedman`):
    b = 11/(2n),   V_N ≤ (121/4)·(T+1)/n      (role sizes m₀≥1/3, c₀≥1/5 from RoleSplitGood)
    (centered-difference martingale form: b_centered = 11/n, same V_N.)
With δ = 0.0001: Pr[sup Φ ≥ δ] ≤ exp(−δ²/(2(V_N + bδ/3))) = exp(−Ω(n/T)); T=O(1) per hour ⟹ exp(−Ω(n)).
Initial: at Phase-3 init, minutes/hours = 0 ⟹ m_{>h}(0)=c_{>h}(0)=0 ⟹ Φ(0)=0 (use Phase-3 init as zero-time, NOT start_h).
Conclusion: ∀t≤end_h, m_{>h}(t) ≤ Φ + 1.1·0.001 ≤ 0.0012.
Robust formal: stop at τ = min{t : c_{>h}>0.001 ∨ Φ>0.0001 ∨ t>T_max}; prove drift before τ; Freedman on stopped process to T_max (from Thm 6.9 clock-good).

Ripple tools confirmed present: `Ripple/Probability/DiscreteFreedman.discrete_freedman`, `BennettLemma.bernstein_optimal`;
ExactMajority has `AzumaKernel.lean`, `SupermartingaleHitting.lean`, `MGFHorizon.lean`, `HourCouplingV2.lean`.

KERNEL-DRIFT TRANSLATION (ChatGPT-confirmed 2026-06-13): Doty's per-interaction drift IS exactly the
one-step kernel drift ∫Φ dK(c) − Φ(c) — NO parallel-time scaling. Ordered-pair kernel (denominator
n(n−1), factor 2 both orientations: #(C_{>h},M_{≤h})_ord = 2 C_{>h} M_{≤h}):
    ∫Φ dK(c) − Φ(c) ≤ (2 C_{>h}/(n(n−1)))·(M_{≤h}/|M| − 1.1 C_{≤h}/|C|)
                     = (2c·c_{>h}/(n−1))·((1−m_{>h}) − 1.1(1−c_{>h}))   ≤ 0 when c_{>h} ≤ 0.001.
This is the `hdrift` for `AzumaKernel.expSupermartingale_drift`, on the good event {c_{>h} ≤ 0.001} (gated/stopped).
Increment b = max(1/|M|, 1.1/|C|) = 11/(2n) (|M|≥n/3, |C|≥n/5). [Epidemic sets two clocks to max-minute;
check whether it can push 2 past h at once — if so increment doubles for the c_{>h} term; |M|-term stays 1/|M|.]

STOPPED-KERNEL CONSTRUCTION for the gated Azuma (ChatGPT-confirmed 2026-06-13) — the implementation blueprint:
  Do NOT gate Φ to 0 off the good event (destroys the boundary crossing signal). Use a STOPPED KERNEL.
  Active predicate:  A(c) := (c_{>h}(c) ≤ 0.001) ∧ (Φ(c) < δ),  δ := 0.0001.
  Stopped kernel:    K*(c,·) := K(c,·) if A(c) else δ_c (point mass — self-loop/freeze).
  Three kernel lemmas to write (then Azuma):
    drift_active  :  A(c) → ∫Φ dK(c) ≤ Φ(c)        [the exact ordered-pair drift, ≤0 on the good event]
    drift_stopped :  ∀c, ∫Φ dK*(c) ≤ Φ(c)          [active: = drift_active; inactive: ∫Φ dδ_c = Φ(c)]
    diff_stopped  :  y ∈ supp(K* c) → |Φ(y)−Φ(c)| ≤ 11/(2n)   [active = K-step; inactive = 0]
  Tail transfer (coupling): couple X_j, X_j* until τ = inf{j : ¬G(X_j) ∨ Φ(X_j) ≥ δ}; before τ they agree;
    {sup_{j≤N, j≤τ_G} Φ(X_j) ≥ δ} ⊆ {Φ(X_N*) ≥ δ}. Azuma on K* to N=⌈n·T_max⌉ (T_max = end_h from Thm 6.9).
  Conclusion: Pr[Φ(X_N*) ≥ 0.0001] ≤ exp(−Ω(n)); on the no-early-stop event, m_{>h}(t) ≤ Φ + 1.1·0.001 ≤ 0.0012.
  Engine: AzumaKernel.expSupermartingale_drift / azuma_tail consume exactly (drift_stopped, diff_stopped).

  ⚠ M_{>h} DEFINITION SUBTLETY (directly resolves the phase-6 reserve-split finding below): M_{>h} should NOT
  literally count all Main with hour > h. A cancel at exponent −j creates two O-agents at hour j; reserve-split
  creates new Main. Lemma 6.10 bounds the Main PULLED AHEAD by fast clocks; their split/cancel DESCENDANTS are
  bounded SEPARATELY by Lemma 6.11 (factor 2). So define M_{>h} = "pulled-ahead-by-clock" count, NOT raw hour>h.

ROLE-PRESERVATION INFRA STATUS (toward mainCount conservation = fixed |M|,|C| denominators):
  LANDED (RolePreservation.lean, axiom-clean): advancePhase/phaseInit(≥2)/advancePhaseWithInit/
  stdCounterSubroutine role-eqs; phase3CancelSplit + Phase3Transition first/second role-eqs.

  ⚠ DESIGN FINDING (2026-06-13): mainCount is NOT conserved across all phases ≥ 3. At Phase 6
  (Reserve-split) `doSplit` converts Reserve→Main (`{r with role := .main}`), so |M| GROWS. Clocks
  NEVER split, so clockCount/|C| IS conserved at all phases ≥ 3 (this is why ClockCapReachable is sound).
  ⟹ a GENERAL phase-≥3 role-eq is FALSE (phase 6); grinding Phase4-10 toward mainCount conservation
  chases a false target.

  RESOLVED (ChatGPT window answer 2026-06-13): Lemma 6.10 is a PHASE-3-ONLY lemma (window t ∈ [0, end_h],
  time 0 = Phase-3 entry); it does NOT span Phase 6. So M_0 := #Main, C_0 := #Clock are FIXED parameters
  CAPTURED AT PHASE-3 ENTRY (not state-dependent denominators); freeze the process on leaving the Phase-3
  window. ⟹ mainCount conservation is UNNECESSARY; the Phase4-10 role-eq grind is SKIPPED (pause was correct).
  RolePreservation foundational+Phase3 lemmas remain reusable. Phase-6 reserve→Main growth is handled
  separately by Doty's §7 (Lemma 7.2+), NOT by extending Lemma 6.10.

  THE POTENTIAL (fixed-n, M_0/C_0 entry constants — the Lean recommendation, Ψ = m_0·Φ_Doty):
      Ψ_h(x) = M_{>h}(x)/n − (11/10)·(M_0/C_0)·C_{>h}(x)/n
    where M_{>h} = #{Phase-3-entry Main with hour > h}, C_{>h} = #{Clock with hour > h}.
    ⚠ clock-coeff is (11/10)(M_0/C_0), NOT (11/10)/c_0 (too strong, loses factor 1/m_0).
  DRIFT:  E[ΔΨ_h|x] ≤ (2 c_0 c_{>h} m_0/(n−1))·((1−m_{>h}) − (11/10)(1−c_{>h})) ≤ −0.0989·(…) < 0 on c_{>h} ≤ 0.001.
  INCREMENT b = 11/(2n) (M_0 ≤ n, C_0 ≥ n/5). Active_h(x) := (Phase-3 window) ∧ (C_{>h} ≤ 0.001 C_0) ∧ (Ψ_h < 10⁻⁴ m_0).
  K* = K on Active else δ_x; drift_stopped + diff_stopped → Azuma → Pr[Ψ_h ≥ 10⁻⁴ m_0] ≤ exp(−Ω(n)).
  TAIL: δ_Ψ = 10⁻⁴ m_0; on the event ⟹ M_{>h}/M_0 ≤ 0.0012 (Lemma 6.10). [Stopped-kernel construction above.]

ROLE-PRESERVATION INFRA STATUS (clock side only now — mainCount conservation NOT needed, see RESOLVED above):

## ⚑ MAJOR FINDING + FIX (2026-06-13): Lemma 6.10 was VACUOUS; fixed via stopped kernel

DISCOVERY: `HourCouplingV2` ALREADY implements Lemma 6.10 — potential `Phi = mAbove/M − 1.1·cAbove/C`,
the GENUINE per-pair drift `hour_drift` (`∫Φ dK ≤ Φ` on the window, via drag/epidemic pair-counting),
the unconditional increment `hour_bdd`, and the Azuma application `hour_coupling_v2`. (My naming search
"mainBeyondHour"/"m_>h" missed it — it uses `mAbove`/`cAbove`/`Phi`. My `Lemma610Potential.lean` Ψ is a
redundant alternative; the general `countP_stepDistOrSelf_diff_le` there is still a clean reusable lemma.)

BUT `hour_coupling_v2` (and its re-export `HourComposition.main_not_ahead_of_clock`) carry
`hreg : ∀ c, Regime M C h c` — the window + fixed counts hold at EVERY config. This is UNSATISFIABLE
(empty config has clockCount 0 ≠ C), so BOTH are VACUOUS — the §3.3 trap (`#print axioms` can't see it).
Refutation-checked: `Lemma610StoppedAzuma.regime_not_universal`.

FIX (LANDED, axiom-clean — `Lemma610StoppedAzuma.lean`): the STOPPED kernel
`K* := Kernel.piecewise {Regime} K Kernel.id` (run K on the regime, self-loop off it). Then:
  `drift_stopped : ∀ x, ∫Φ dK*(x) ≤ Φ x`  — UNCONDITIONAL (regime → hour_drift; off → ∫Φ dδ_x = Φ x).
  `diff_stopped  : ∀ x, ∀ᵐ y ∂K*(x), |Φy−Φx| ≤ c0`  — (regime → hour_bdd; off → 0).
  `lemma610_stopped` — the HONEST non-vacuous Azuma tail for K*, NO false global window:
    `(K*^t) c₀ {Φ ≥ Φ c₀ + lam} ≤ exp(−lam²/(2 t c0²))`,  c0 = 2/M + 2(11/10)/C.
The vacuous `hour_coupling_v2` is a near-leaf (docs only, not deeply consumed) — future §6 consumers
must use `lemma610_stopped`, not the vacuous version.

REMAINING for a complete drop-in Lemma 6.10: (i) the stopped→unstopped tail transfer (coupling: K and K*
agree until first regime-exit, so {sup Φ ≥ δ before exit} ⊆ {Φ(X_N*) ≥ δ}); (ii) read off Φ(c₀)=0 +
δ=10⁻⁴m_0 ⟹ m_{>h} ≤ 0.0012; (iii) wire into the §6 clock assembly. The regime actually holding along
the trajectory whp is the BROADER synchronization analysis (the front-shape / hour-good chain), not a
standalone gap.

## Formalization plan (priority order)
1. **Lemma 6.10 (Azuma, clean)** via Ripple `DiscreteFreedman`/`bernstein_optimal` — the m_{>h} ≤ η bound.
2. **Thm 6.9 hitting-time bounds** (hour length/gap) — epidemic Lemma 4.5 + Janson Cor 4.4.
3. **Two-level tail** `c_{≥r+2} ≤ 10^{−4}` (the minimal Thm 6.5 consequence) — Lemma 6.3 + early-drip ghost.
4. **`ClockHourGood`** assembled from 1–3, then the majority dynamics consume it (bypasses per-minute profile).
5. (Full faithfulness) the complete Thm 6.5 envelope + sparse-pioneer lemma — for the standalone clock theorem.

Reusable Ripple machinery to lean on: `DiscreteFreedman.discrete_freedman`, `bernstein_optimal`
(Azuma/Freedman); `EhrenfestUrn.bernstein_tail_bound` (binomial Chebyshev); the proven
`ClockFrontShape.real_front_advance_squares_cap` + `ClockFrontWidth.front_breach_le_capSq`
(per-level squaring already on the real kernel); `FrontTailDecay.frontWidth_loglog` (deterministic envelope).
