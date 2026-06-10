I’ll try direct file fetch by GitHub URL rather than repo lookup, since the repository-name lookup was being misrouted. If that still fails, I’ll give a branch-honest answer: no fabricated code quotes, only a concrete patch skeleton and the identifiers you supplied.

I cannot quote real opus-wip code: the GitHub connector available in this chat resolves xiangyazi24/Ripple to a different private repo, and direct fetch of Phase1Convergence.lean on opus-wip returns 404. So below is the concrete calibration patch, not a verified branch quote.

Most important: make one generic lemma, then instantiate only the α-floor.

lemma rect_pow_le_budget
    {n M₀ m T : ℕ} {α q : ℝ}
    (hn : 2 ≤ n) (hm : 1 ≤ m) (hM₀ : (M₀ : ℝ) ≤ n)
    (hα0 : 0 < α) (hα1 : α ≤ 1)
    (hq0 : 0 ≤ q)
    (hq : q ≤ 1 - α * (m : ℝ) / n)
    (hT : (3 / α) * ((n : ℝ) / (m : ℝ)) * Real.log n ≤ T) :
    q ^ T ≤ 1 / ((M₀ : ℝ) * (n : ℝ)^2) := by
  -- route:
  -- q ≤ 1-u ≤ exp(-u), u = α*m/n
  -- q^T ≤ exp(-u*T)
  -- hT gives u*T ≥ 3 log n
  -- exp(-u*T) ≤ exp(-3 log n) = n⁻³
  -- n⁻³ ≤ 1/(M₀*n²), since M₀ ≤ n
  sorry


Mathlib route: use Real.one_add_le_exp (-u) for 1 - u ≤ exp (-u), pow_le_pow_left₀, Real.exp_le_exp, Real.exp_log, Real.rpow_natCast, Real.rpow_neg, plus field_simp, ring_nf, nlinarith, positivity.

Per phase constants:

Phase 1, extremeU:

q₁ m = 1 - (mainCount * m : ℝ) / (n * (n - 1))
mainCount ≥ n/3        -- from RoleSplitWindows / Lemma 5.2
q₁ m ≤ 1 - (1/3) * m/n
α₁ = 1/3
tWin₁ m = ⌈9 * n * log n / m⌉


Phase 5, unsampledReserveU:

q₅ m = 1 - (biasedMainCount * m : ℝ) / (n * (n - 1))
biasedMainCount ≥ 0.92 * mainCount ≥ 0.92 * n/3 = 23*n/75
q₅ m ≤ 1 - (23/75) * m/n
α₅ = 23/75
tWin₅ m = ⌈(225/23) * n * log n / m⌉


Phase 6, highMass, per level:

q₆ m = 1 - (reserveClassCount * m : ℝ) / (n * (n - 1))
reserveClassCount ≥ ρ₆ * n   -- from ReserveSampleGood K₀
q₆ m ≤ 1 - ρ₆ * m/n
α₆ = ρ₆
tWin₆ m = ⌈(3/ρ₆) * n * log n / m⌉


If ReserveSampleGood K₀ only gives reserveClassCount ≥ n/(10*K₀), then use:

α₆ = 1 / (10*K₀)
tWin₆ m = ⌈30 * K₀ * n * log n / m⌉


Phase 7, classMassN, per level:

q₇ m = 1 - (elimGap1Count * m : ℝ) / (n * (n - 1))
elimGap1Count ≥ 0.8 * mainCount ≥ 0.8 * n/3 = 4*n/15
q₇ m ≤ 1 - (4/15) * m/n
α₇ = 4/15
tWin₇ m = ⌈(45/4) * n * log n / m⌉


This is the crude mechanized replacement for the paper’s sharper 6.41/6.45/6.51 ln n windows.

Phase 8, minorityU:

q₈ m = 1 - (nonFullMajorityCount * m : ℝ) / (n * (n - 1))
nonFullMajorityCount ≥ (0.8 - 0.2) * mainCount ≥ 0.6 * n/3 = n/5
q₈ m ≤ 1 - (1/5) * m/n
α₈ = 1/5
tWin₈ m = ⌈15 * n * log n / m⌉


If your Phase 8 post actually exports nonFullMajorityCount ≥ 0.8 * mainCount, improve to:

α₈ = 4/15
tWin₈ m = ⌈(45/4) * n * log n / m⌉


Sum discharge:

lemma rect_sum_le_phase_budget
    {n M₀ : ℕ} {q tWin : ℕ → ℝ} -- or q : ℕ → ℝ, tWin : ℕ → ℕ
    (hM₀ : (M₀ : ℝ) ≤ n)
    (hpt : ∀ m ∈ Finset.Icc 1 M₀,
      q m ^ tWin m ≤ 1 / ((M₀ : ℝ) * (n : ℝ)^2)) :
    (∑ m in Finset.Icc 1 M₀, q m ^ tWin m) ≤ 1 / (n : ℝ)^2 := by
  -- sum_le_sum hpt
  -- card_Icc 1 M₀ ≤ M₀
  -- cancel M₀
  sorry


Threading gaps I would check first:

Phase 1: Phase1Convergence.Post must import/export RoleSplitWindows.mainCount ≥ n/3.

Phase 5: needs Theorem 6.2 post exporting biasedMainCount ≥ 0.92 * mainCount.

Phase 6: biggest likely gap: ReserveSampling.Post / ReserveSampleGood K₀ must expose an actual numeric reserveClassCount ≥ ρ₆*n.

Phase 7: needs Phase 6/structural post exporting elimGap1Count ≥ 0.8 * mainCount.

Phase 8: needs Phase 7 post exporting the non-full-majority floor; check whether it is 0.6*mainCount or 0.8*mainCount.

The public arXiv record confirms the exact-majority paper and its v2 date; I did not use it as a source for branch-local Lean names. 
arxiv.org
