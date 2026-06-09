# Doty time-half — Lemma 6.10 (GENUINE redo): supermartingale drift + azuma_tail

Directive: 挨个做，绝对不退缩，不 over-claim. The first 6.10 attempt used a wrong exp-transform (false hfloor).
The paper's Lemma 6.10 (ref/Doty-2021-exact-majority.txt lines 2146–2180) IS a genuine bounded-difference
supermartingale, and the NEW `AzumaKernel.azuma_tail` is exactly the tool. Redo it correctly.

## The paper's exact argument (lines 2146–2180 — follow it)
Φ(t) = m_{>h}(t) − 1.1·c_{>h}(t), where m_{>h} = |{Main : hour>h}|/|M|, c_{>h} = |{Clock : hour>h}|/|C| (FRACTIONS).
- Drag reaction `Ch,Mj→Ch,Mh` (h>j) increases Φ by 1/|M| (one Main joins m_{>h}); prob ∝ 2c·c_{>h}·m(1−m_{>h}).
- Clock-epidemic `Ch,Cj→Ch,Ch` (h>j) decreases Φ by 1.1/|C| (one Clock joins c_{>h}); prob ∝ 2c²·c_{>h}(1−c_{>h}).
- E[ΔΦ] = (2c·c_{>h}/n)·[(1−m_{>h}) − 1.1(1−c_{>h})]. On the window `c_{>h} ≤ 1/11` (⊇ [0,end_h] since
  c_{>h}≤0.001 there), `1.1(1−c_{>h}) ≥ 1 ≥ 1−m_{>h}` ⟹ bracket ≤ 0 ⟹ E[ΔΦ] ≤ 0. SUPERMARTINGALE. (Both rates
  share the c_{>h} factor — a drag needs a clock-above partner — this is why my earlier "drag without
  clock-crossing" worry was wrong.)
- Bounded difference |ΔΦ| ≤ max(1/|M|, 1.1/|C|) = O(1/n). Azuma (Theorem 4.2 = `azuma_tail`) ⟹
  `m_{>h}(t) ≤ 1.2·c_{>h}(end_h)` whp for t ≤ end_h.

## Reuse
- `AzumaKernel.azuma_tail` (NEW): `(K^t) x {Φx+λ ≤ Φy} ≤ exp(−λ²/(2tc²))` for supermartingale drift
  (∫Φ∂K≤Φ) + bounded a.e. difference (|Φy−Φx|≤c). THIS is the concentration tool — use it (note: it wants the
  supermartingale form ∫Φ∂K ≤ Φ globally on the relevant region; restrict to the window or use −Φ orientation
  as needed; azuma_exp_tail is also available).
- The PARTIAL `HourCoupling.lean` mechanism lemmas (REUSE, they're genuine): `mAbove_pair_drag` (mAbove rises
  ONLY via Rule-2 drag against a clockAbove agent), `cAbove_support_ge` (cAbove monotone),
  `phase3CancelSplit_id_of_unbiased` (Rules 3/4 inert), `mAbove_stepOrSelf_le`, `cAbove_stepOrSelf_ge`. These
  bound which reactions change Φ.
- The c²/pair-counting patterns (`ClockRealMixed.sum_interactionCount_*`, interactionCount/totalPairs) for the
  drag-pair and epidemic-pair counts.

## Task (NEW file Probability/HourCouplingV2.lean only — supersede the partial's headline)
1. Φ (fraction form `m_{>h} − 1.1·c_{>h}`, or a scaled integer form that azuma_tail can consume) + measurability.
2. **The GENUINE drift** `hour_drift : ∀ c, (c on the window c_{>h} ≤ 1/11) → ∫ Φ ∂(K c) ≤ Φ c` — computed from
   ALL reaction types: drag pairs contribute +1/|M| each (bounded via mAbove_pair_drag — ONLY Rule-2 drag raises
   mAbove), clock-epidemic pairs −1.1/|C| each, all others ≤0 or 0 to Φ; the pair-counting + the bracket
   inequality `(1−m_{>h}) − 1.1(1−c_{>h}) ≤ 0` on the window give E[ΔΦ] ≤ 0. This is the heart — derive it, do
   NOT assume (no frozen-cAbove hfloor!).
3. **Bounded difference** `hour_bdd : ∀ x, ∀ᵐ y ∂(K x), |Φ y − Φ x| ≤ C/n` (a single interaction changes one
   agent's hour ⟹ ΔΦ ≤ max(1/|M|,1.1/|C|)).
4. `hour_coupling_v2` : apply `azuma_tail` to get `(K^t) c₀ {m_{>h} > 1.2·c_{>h}(end_h)} ≤ 1/poly` (the genuine
   Lemma 6.10), on the window/until end_h.

## HARD RULES (automode, 绝对不退缩, 不 over-claim)
NEW file HourCouplingV2.lean only; do NOT edit existing files, do NOT weaken proven lemmas. The drift MUST be
genuinely derived from the drag/epidemic pair-counting + the bracket inequality (the paper's computation), NEVER
the frozen-cAbove false hfloor. Use the REAL azuma_tail. No sorry/admit/new axiom/native_decide. If the drift
genuinely needs a window hypothesis (c_{>h} ≤ 1/11, true until end_h), carry it as an EXPLICIT labeled window
(it is TRUE, = the synchronous-hour regime) — that is faithful, not a false hyp. Iterate `lake build
Ripple.PopulationProtocol.Majority.ExactMajority.Probability.HourCouplingV2` until clean. Do NOT git. Final
message: Φ def, the genuine drift lemma statement (showing it's derived from pair-counting + bracket, not frozen
cAbove), the bounded-difference lemma, hour_coupling_v2 statement VERBATIM, build verdict, #print axioms (must be
[propext, Classical.choice, Quot.sound]), HONEST status: drift genuinely derived (not the old false hfloor)?
azuma_tail used? what window/hyp carried (should be only the true c_{>h}≤1/11 synchronous-hour window)? Be
precise. If rate-limited, report on-disk WIP.
