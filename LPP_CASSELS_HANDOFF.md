# LPP/CasselsClassical — Session Handoff (2026-05-16)

## What This File Is

`Ripple/LPP/CasselsClassical.lean` formalizes Cassels-1960 "On the
equation a^x−b^y=1, II" in Lean 4 / Mathlib v4.29.  **45 kernel-clean
declarations, 0 sorry / 0 axiom, build 1443 jobs.**

## Proven (all kernel-clean):

| Block | Key declarations | What |
|---|---|---|
| Lemma 1 (±) | `cassels_lemma_1_sub/add`, `*_gcd_eq` | gcd((c^p±1)/(c±1), c±1) ∈ {1,p} |
| Cor of Lemma 1 (±) | `cassels_cor_lemma_1_sub/add` | p^j∣(c±1) ⟹ quot ≡ p mod p^{j+1} |
| Size inequalities | `cassels_size_ineq`, `cassels_size_ineq_plus` | (u^q−1)^p < (u^p−1)^q etc. |
| Lemma 2 (±) | `cassels_lemma_2_plus/minus` | a^p=b^q±1 ⟹ q∣(b±1) |
| Exact gcd (±) | `cassels_gcd_add/sub_eq_q` | q∣(b±1) ⟹ gcd = q exactly |
| q∣a (±) | `cassels_q_dvd_a_plus/minus` | q∣a from the equation |
| v_q(quot)=1 (±) | `cassels_vq_altQuot/posQuot_eq_one` | exact valuation |
| p∣(v_q+1) (±) | `cassels_p_dvd_vq_succ_plus/minus` | via padicValInt mul + pow |
| Cor 1 split (±) | `cassels_cor1_split_plus/minus` | b±1 = q^{v_q}·u^p |
| Cor 2 a-factor (±) | `cassels_cor2_a_factor_plus/minus` | a = q^k·u·w |
| Reductio subst | `cassels_reductio_subst` | p∤(a−1) ⟹ a−1=z^q |
| **B2.2 linchpin** | `cassels_B22` | v_ℓ(r!) ≤ v_ℓ(∏(p−iq)) for ℓ∤q |
| B2.2 payload | `cassels_factorial_dvd`, `cassels_qpow_prod_factorial_dvd` | r! ∣ q^{v_q(r!)}·∏(p−iq) |
| Binomial defs | `gbinomQ`, `casselsR/Sigma/Nu`, `gbinomQ_nat_div` | C(p/q,r) identity |

## Key Architectural Finding

Cassels' theorem proves **divisibility** (`p|y ∧ q|x`), NOT non-existence.
`cassels_runge_gap_core` (CasselsElementary:1551) wants `False` — that's
Catalan/Mihăilescu-strength. **Fork A/B/C** for gap_core wiring: Xiang's
research decision, documented in CHECKPOINT cont.22.

## What's Next (from ChatGPT's PIECE 2/3 design, pasted by Xiang)

1. **`casselsTruncQ` + clearing lemma** — `∑_{r≤R} gbinomQ(p/q,r)·z^{q(R-r)}`;
   `q^{R+ν}`-clearing is integer (consumes `cassels_factorial_dvd` per-term).

2. **`truncR_over_rpow`** — THE Mathlib gap: generalized binomial truncation
   with signed remainder for `Real.rpow`. Route: Taylor integral remainder
   for `(1+t)^α`, iterated deriv `= (∏_{i<n}(α-i))·(1+t)^{α-n}`.

3. **`cassels_binomial_contradiction`** — integer I, 0<I<1, contradiction.
   For p<q (gap_core): R=1, ν=0, σ=q−p, I = q·z^q + p − q·z^{q-p}·b.

4. Full `cassels_divisibility_theorem` combining Lemma 2 + reductio.

5. (f) gap_core wiring — fork-blocked on Xiang's A/B/C decision.

## Imports

```
Mathlib.Algebra.Ring.GeomSum, Data.Int.ModEq, Data.Int.GCD,
Data.Nat.Prime.Basic, Algebra.GCDMonoid.Basic/Nat,
RingTheory.Int.Basic, Tactic.Ring/Linarith/FieldSimp,
NumberTheory.Padics.PadicVal.Basic, Data.ZMod.Basic
```

## ChatGPT Bridge

- Dedicated `life` channel (tmux window = life) tested OK for short queries
- Long heavy questions → connection-fails (bridge limit)
- ChatGPT's full PIECE 1/2/3 design was pasted by Xiang directly into session
- PIECE 1 matches proven `cassels_B22`; PIECE 2/3 inform next steps above

## References

- `ref/Cassels-1960-On-the-equation-ax-by-1-II.pdf`
- `ref/Ribenboim-Catalans-Conjecture.pdf` (B2.1-B2.4, pp.204-212)
- ChatGPT design: saved context in CHECKPOINT cont.22h-22i + Xiang's paste
