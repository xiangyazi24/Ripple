# HANDOFF: RoleSplitWindows via top-split (family3 letter, task 59da8aae, 2026-06-10)

Source: ChatGPT Pro (family3 channel, GitHub connector on xiangyazi24/Ripple
opus-wip). Auto-capture truncated at 181 B; full text manually pasted by Xiang.
This file is the verbatim-faithful blueprint record.

## Bottom line (ChatGPT's verdict)

Do NOT formalize `RoleSplitWindows` as "Chernoff on the number of R1 fires."
That is not what the paper's proof needs, and is not stable under the Lean
encoding where R4 can fire concurrently. Minimal route:

1. Formalize the **Lemma 5.1 top-split balance**: `Main` vs "ever-produced
   RoleCR mass" is `n/2 ± δn` whp.
2. Reuse existing Stage-2 CR-drain/Janson machinery to convert most RoleCR
   mass into balanced `Clock`/`Reserve`.
3. Deterministic lemma: `TopSplitWindow δ` + `CRDrainWindow δ` +
   `ClockReserveBalanced` + conservation ⟹ `RoleSplitWindows η`, δ = η/4.

Constants: final η = 1/25, internal δ = 1/100. Satisfies
`clockCount_linear_of_RoleSplitGood` (expects η ≤ 1/25, gives clockCount ≥ n/5).

## What Lemma 5.2 actually bounds

Paper Lemma 5.2: whp 1 − O(1/n²), by end of Phase 0: no RoleMCR; Main count
n/2(1±ε); Clock and Reserve each ≥ n/4(1−ε). The top-level split is Lemma 5.1
with U = RoleMCR, M = Main, S = RoleCR; only AFTER that does it analyze the
RoleCR→Clock/Reserve split (U,U → R,C plus U → R at phase end). By Lemma 5.1,
after 12.5 ln n time, produced RoleCR count s satisfies n/3 ≤ s ≤ 2n/3 w.p. 1
and s = n/2(1±ε₀) whp; second-level split yields Clock,Reserve ≥ n/4(1−4ε₀) whp.

The Chernoff part is NOT "#R1 near its mean." The key balance process is
|m − s| (m = #Main, s = #RoleCR in top split). The invariant `sf + 2st = mf + 2mt`
implies: when s > m then sf > mf, so the next reaction changing s − m is more
likely to decrease it; |m−s| is stochastically dominated by a sum of independent
coin flips → Chernoff gives |m−s| ≤ εn.

Honest event probabilities, top split:
- R1: MCR+MCR, raw ordered ≈ u(u−1)/(n(n−1))
- R2/R3 combined: MCR+assignable, one-oriented lower bound u·assignable/(n(n−1))
  (full two-oriented paper rate ≈ 2u·assignable/(n(n−1)))

Repo already proves (reuse these): `phase0_mcrCount_decrease_prob_oneSided`,
`phase0_mcrCount_decrease_prob_combined`, `phase0_mcrCount_decrease_prob_floor`.

Conditional R1 probability among the single-oriented good rectangle:
p_R1(u,A) = (u−1)/(u−1+A), A = assignableCount = sf+mf — NOT uniformly bounded
away from 0 over the whole run. Early (u ≥ 2n/3) the paper bounds the top
reaction ≥ 1/2 among non-null; later it uses the assignable-floor rate, not R1.

## Target Lean surface

### A. New defs

```lean
/-- Total mass descended from the top-level S = RoleCR split. -/
def topCRMass (c : Config (AgentState L K)) : ℕ :=
  crCount c + clockCount c + reserveCount c

def TopSplitWindow (δ : ℝ) (n : ℕ) (c : Config (AgentState L K)) : Prop :=
  |(mainCount c : ℝ) - (topCRMass c : ℝ)| ≤ δ * n

def CRDrainWindow (δ : ℝ) (c : Config (AgentState L K)) : Prop :=
  (crCount c : ℝ) ≤ δ * (topCRMass c : ℝ)
```

topCRMass (not crCount alone) because R4 moves RoleCR into Clock+Reserve
without changing the top-level Main-vs-S balance (ΔX = 0 for R1 and R4).

### B. Deterministic conversion (pure algebra, no probability)

```lean
theorem RoleSplitWindows_of_topSplit_crDrain
    {η δ : ℝ} {n : ℕ} {c : Config (AgentState L K)}
    (hη0 : 0 ≤ η) (hη1 : η ≤ 1) (hδ : δ = η / 4)
    (hcard : Multiset.card c = n)
    (hmcr0 : roleMCRCount c = 0)
    (hbal : ClockReserveBalanced c)
    (htop : TopSplitWindow δ n c)
    (hdrain : CRDrainWindow δ c) :
    RoleSplitWindows η n c
```

Arithmetic: conservation + hmcr0 ⟹ mainCount + topCRMass = n; htop ⟹
mainCount ∈ [(1−δ)n/2, (1+δ)n/2] (δ ≤ η gives Main window); hbal ⟹
topCRMass = crCount + 2·clockCount; hdrain ⟹ clockCount = reserveCount
≥ (1−δ)·topCRMass/2 ≥ (1−δ)²n/4 ≥ (1−η)n/4 (with δ=η/4: (1−1/100)²/4 =
0.9801/4 > 0.96/4 = (1−1/25)/4). Uses existing `roleCount_conservation`,
`balanced_conservation`.

### C. Probabilistic top-split tail (the real residual)

```lean
theorem topSplitWindow_whp
    {δ : ℝ} (hδ : 0 < δ) {n : ℕ} (hn : 2 ≤ n)
    {c₀ : Config (AgentState L K)} (hinit : Phase0Initial n c₀) (tTop : ℕ) :
    ((NonuniformMajority L K).transitionKernel ^ tTop) c₀
      {c | ¬ TopSplitWindow δ n c} ≤ ENNReal.ofReal (((n:ℝ)^2)⁻¹)
```

Proof via inward-drift for X c = mainCount c − topCRMass c (NOT R1-count
concentration). One-step sign-drift from the paper invariant sf+2st = mf+2mt.

### D. Abstract sign-drift Chernoff brick (fits existing engines)

```lean
theorem signDrift_abs_chernoff
    (K : Kernel α α) [IsMarkovKernel K] (X : α → ℤ) (G : Set α)
    (T : ℕ) (x₀ : α) (a : ℝ)
    (hX0 : X x₀ = 0)
    (hjump : ∀ x ∈ G, ∀ y ∈ (K x).support, |((X y:ℝ) - (X x:ℝ))| ≤ 1)
    (h_inward : <if X>0 downward prob ≥ upward; if X<0 upward ≥ downward>)
    (hgate_tail : (killK K G ^ T) (some x₀) {none} ≤ ofReal ((n:ℝ)²)⁻¹) :
    (K ^ T) x₀ {x | a ≤ |(X x : ℝ)|} ≤
      gate_escape + ENNReal.ofReal (2 * Real.exp (-(a*a)/(2*T)))
```

Use `stepIndexed_gated_tail` with Φ_j x = exp(s·|X x| + correction_j). If the
window is genuinely support-closed use `windowDrift_tail`; otherwise the
killed-kernel version.

### E. Final assembly

```lean
theorem roleSplitWindows_whp
    {n : ℕ} (hn : 100 ≤ n) {c₀} (hinit : Phase0Initial n c₀) (tRole : ℕ) :
    (K' ^ tRole) c₀ {c | ¬ RoleSplitWindows (1/25 : ℝ) n c}
      ≤ ENNReal.ofReal (3 * ((n:ℝ)^2)⁻¹)
```

Union bound: (1) topSplitWindow_whp δ=1/100; (2) existing
`phase0_roleSplit_whp_two_stage` (Stage-1/1.5/2 composition, Post =
`RoleSplitStage2Good` = mcr=0 ∧ crCount ≤ 1); (3) deterministic conversion B.
Insertion point: `phase0_roleSplit_whp_assembled_stage2` already takes
(hstage2, hbal, hwin) — `roleSplitWindows_whp` is the last clean named input.

## Status

- [ ] A+B (defs + deterministic conversion) — pure algebra, dispatch first
- [ ] D (abstract sign-drift brick) — needs the one-step inward-drift
      computation from the protocol invariant sf+2st = mf+2mt
- [ ] C (instantiate for X = mainCount − topCRMass)
- [ ] E (union-bound assembly)
