# Doty time-half — INFRA: martingale Azuma-Hoeffding tail (the genuine unblock for Lemma 6.10)

Directive: 挨个做，绝对不退缩，不 over-claim. Lemma 6.10 needs an ADDITIVE bounded-difference supermartingale
tail (Azuma). The naive `exp(sΦ)` is NOT a supermartingale (Jensen wrong way; the 4th false-hyp shortcut). The
genuine object is the Azuma exponential supermartingale `exp(s·Φ(t) − (s²c²/2)·t)`, whose tail gives the
concentration. Build this infra (kernel-power form, matching `geometric_drift_tail`), reusing Mathlib's
Hoeffding's lemma.

## What Mathlib provides (verified)
`Mathlib/Probability/Moments/SubGaussian.lean`: `ProbabilityTheory.HasSubgaussianMGF` and
`hasSubgaussianMGF_of_mem_Icc` (Hoeffding's lemma: `Y ∈ [a,b] ⟹ E[exp(s(Y−EY))] ≤ exp(s²(b−a)²/8)`). The repo's
`Concentration.lean` uses the INDEPENDENT sum bound. The CONDITIONAL/martingale variant is what 6.10 needs —
check `SubGaussian.lean` for a conditional (`Kernel`/`condExp`) `HasSubgaussianMGF` and a martingale/partial-sum
tail; if present, USE it; if not, BUILD the minimal kernel-step version below.

## Target (NEW file Probability/AzumaKernel.lean)
A kernel-power Azuma tail mirroring `Supermartingale.geometric_drift_tail`, for a real potential `Φ : α → ℝ` on
a Markov kernel `K : Kernel α α`:
- HYP1 (supermartingale drift): `∀ x, ∫ y, Φ y ∂(K x) ≤ Φ x` (additive, E[Φ']≤Φ).
- HYP2 (bounded per-step difference): `∀ x, ∀ y ∈ (K x).support, |Φ y − Φ x| ≤ c`.
- CONCLUSION: `(K^t) x {y | Φ x + λ ≤ Φ y} ≤ exp(−λ² / (2·t·c²))` (upper Azuma tail), and/or the exponential
  form `(K^t) x {y | θ ≤ exp(s·Φ y)} ≤ exp(s·Φ x + (s²c²/2)·t) / θ`.
Strategy: per-step `E[exp(s(Φ' − Φ))|x] ≤ exp(s²c²/2)` from Hoeffding's lemma (`hasSubgaussianMGF_of_mem_Icc`
applied to `Φ' − Φ ∈ [−c, c]` with conditional mean ≤ 0) ⟹ `Ψ_t = exp(s·Φ − (s²c²/2)·t)` is a MULTIPLICATIVE
(r=1) supermartingale ⟹ feed to `geometric_drift_tail_kernel` (r=1) ⟹ tail ⟹ optimize `s = λ/(t c²)`.

## HARD RULES (automode, 绝对不退缩, 不 over-claim)
NEW file AzumaKernel.lean only; do NOT edit existing files. This is PURE PROBABILITY infra (no protocol
dependency) — keep it general (any `α`, `K`, `Φ`). The per-step MGF bound MUST be genuinely derived from
Hoeffding's lemma (Mathlib `hasSubgaussianMGF_of_mem_Icc` or equivalent), NOT assumed. No sorry/admit/new
axiom/native_decide. If a needed Mathlib lemma (conditional MGF, exp-supermartingale telescoping) is genuinely
absent, build the minimal piece OR STOP and report the EXACT missing Mathlib API. Iterate `lake build
Ripple.PopulationProtocol.Majority.ExactMajority.Probability.AzumaKernel` until clean. Do NOT git. Final message:
whether Mathlib's conditional sub-Gaussian sufficed or you built the step-MGF bound; the Azuma tail theorem
statement VERBATIM; build verdict; #print axioms (must be [propext, Classical.choice, Quot.sound]); HONEST
status: per-step MGF genuinely derived from Hoeffding (not assumed)? tail proven? If blocked on an exact Mathlib
gap, name it precisely. If rate-limited, report on-disk WIP.
