/-
# Doty Thm 3.1 — Phase B, steps 1–2: the concrete parameters and the carried-scale dischargers.

This file fixes, ONCE, the concrete parameters of the §6 windowed-front engine
(`EarlyDripMarked.windowedFrontProfile_whp_packaged` / `goodFrontWidth_whp` / `climbBound_whp` /
`hB_discharge`) at the paper scales, and discharges the carried scale hypotheses at those parameters.

The locked constants (from `DOTY_LEMMA63_DOCTRINE.md`): wp = 3/200, cc = 9/10, ε = 1/200,
g = 5123/5000, G = 201/200, sg = σg = 1/10.

The paper scales: θ = n^{−0.4} (so the pre-bulk feeder threshold `θn = ⌊n^{3/5}⌋`), the taint
threshold `tt = ⌊n^{3/20}⌋`, the per-window step count `w = ⌊3n/200⌋`.

NOTE (the finite-n negligibility crossover): the negligibility inequality `tt·n ≤ (1−cc)·θn²`
(item 2) is ASYMPTOTIC — at `θn = n^{3/5}`, `tt = n^{3/20}`, `cc = 9/10` it reads
`n^{1.15} ≤ n^{1.2}/10`, which needs `n^{0.05} ≥ 10`, i.e. `n ≳ 10^{20}`.  This is a genuine
finite-n constant gap, not an error: the doctrine's `≫` is asymptotic.  The dischargers below carry
the scale fact as an explicit hypothesis (`negligibility_le` already does), and `neg_params` proves
it at the genuine crossover `N₀`.
-/

import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.EarlyDripMarked

namespace ExactMajority

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace DotyParams

open ClockRealKernel EarlyDripMarked

variable {L K : ℕ}

/-! ## Part 1 — the concrete parameter definitions. -/

/-- The pre-bulk feeder threshold count at the paper scale `n^{3/5}` (so `θ = θn/n = n^{−2/5}`). -/
noncomputable def θn (n : ℕ) : ℕ := ⌊(n : ℝ) ^ ((3 : ℝ) / 5)⌋₊

/-- The taint threshold count at the paper scale `n^{3/20}`. -/
noncomputable def tt (n : ℕ) : ℕ := ⌊(n : ℝ) ^ ((3 : ℝ) / 20)⌋₊

/-- The per-window step count `w = ⌊3n/200⌋` (= `wp·n`, `wp = 3/200` parallel time). -/
def w (n : ℕ) : ℕ := 3 * n / 200

/-- The clock-floor scale `N₀`.  Raised well past the negligibility crossover (`≈10^{20}`) so every
binding inequality holds with comfortable margins; recorded in the doctrine.  The exponent `40` is
chosen a multiple of `20` so the rpow powers `N₀^{3/5} = 10^{24}` and `N₀^{3/20} = 10^{6}` are clean
integer powers. -/
def N₀ : ℕ := 10 ^ 40

/-! ## Part 2 — basic rpow/floor facts about `θn` and `tt`.

All `Real.rpow` reasoning is confined here; downstream sees only `ℕ`/simple-`ℝ` facts. -/

/-- `(θn n : ℝ) ≤ n^{3/5}` (floor below its argument). -/
theorem θn_le (n : ℕ) (hn : 1 ≤ n) : (θn n : ℝ) ≤ (n : ℝ) ^ ((3 : ℝ) / 5) := by
  have hpos : (0 : ℝ) ≤ (n : ℝ) ^ ((3 : ℝ) / 5) := by positivity
  exact Nat.floor_le hpos

/-- `n^{3/5} < θn n + 1` (the floor is within 1 of its argument). -/
theorem lt_θn_succ (n : ℕ) : (n : ℝ) ^ ((3 : ℝ) / 5) < (θn n : ℝ) + 1 :=
  Nat.lt_floor_add_one _

/-- `n^{3/5} − 1 ≤ θn n` (the floor's lower bound). -/
theorem sub_one_le_θn (n : ℕ) : (n : ℝ) ^ ((3 : ℝ) / 5) - 1 ≤ (θn n : ℝ) := by
  have := lt_θn_succ n
  linarith

/-- `(tt n : ℝ) ≤ n^{3/20}`. -/
theorem tt_le (n : ℕ) : (tt n : ℝ) ≤ (n : ℝ) ^ ((3 : ℝ) / 20) := by
  have hpos : (0 : ℝ) ≤ (n : ℝ) ^ ((3 : ℝ) / 20) := by positivity
  exact Nat.floor_le hpos

/-- `N₀ = 10^40` as a real is `(10:ℝ)^(40:ℕ)`. -/
theorem N₀_cast : (N₀ : ℝ) = (10 : ℝ) ^ (40 : ℕ) := by unfold N₀; push_cast; ring

/-- `(10^40)^{3/5} = 10^24` as reals. -/
theorem rpow_N₀_three_fifths : ((10 : ℝ) ^ (40 : ℕ)) ^ ((3 : ℝ) / 5) = (10 : ℝ) ^ (24 : ℕ) := by
  rw [← Real.rpow_natCast (10 : ℝ) 40, ← Real.rpow_natCast (10 : ℝ) 24,
      ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 10)]
  norm_num

/-- `(10^40)^{3/20} = 10^6` as reals. -/
theorem rpow_N₀_three_twentieths :
    ((10 : ℝ) ^ (40 : ℕ)) ^ ((3 : ℝ) / 20) = (10 : ℝ) ^ (6 : ℕ) := by
  rw [← Real.rpow_natCast (10 : ℝ) 40, ← Real.rpow_natCast (10 : ℝ) 6,
      ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 10)]
  norm_num

/-- For `n ≥ N₀`, `n^{3/5} ≥ 10^24`. -/
theorem rpow_three_fifths_ge (n : ℕ) (hn : N₀ ≤ n) :
    (10 : ℝ) ^ (24 : ℕ) ≤ (n : ℝ) ^ ((3 : ℝ) / 5) := by
  have hNℝ : ((10 : ℝ) ^ (40 : ℕ)) ≤ (n : ℝ) := by
    have : (N₀ : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    rwa [N₀_cast] at this
  calc (10 : ℝ) ^ (24 : ℕ) = ((10 : ℝ) ^ (40 : ℕ)) ^ ((3 : ℝ) / 5) := rpow_N₀_three_fifths.symm
    _ ≤ (n : ℝ) ^ ((3 : ℝ) / 5) :=
        Real.rpow_le_rpow (by positivity) hNℝ (by norm_num)

/-- For `n ≥ N₀`, `θn n ≥ 30000` (in fact `θn n ≥ 10^24 − 1`). -/
theorem θn_ge_30000 (n : ℕ) (hn : N₀ ≤ n) : 30000 ≤ θn n := by
  have hlo : (10 : ℝ) ^ (24 : ℕ) ≤ (n : ℝ) ^ ((3 : ℝ) / 5) := rpow_three_fifths_ge n hn
  have h2 : (10 : ℝ) ^ (24 : ℕ) - 1 ≤ (θn n : ℝ) := le_trans (by linarith) (sub_one_le_θn n)
  have : (30000 : ℝ) ≤ (θn n : ℝ) := by
    refine le_trans ?_ h2; norm_num
  exact_mod_cast this

/-- `0 < n` for `n ≥ N₀`. -/
theorem N₀_pos (n : ℕ) (hn : N₀ ≤ n) : 0 < n := by
  have : 0 < N₀ := by unfold N₀; positivity
  omega

/-- `2 ≤ n` for `n ≥ N₀`. -/
theorem two_le (n : ℕ) (hn : N₀ ≤ n) : 2 ≤ n := by
  have : (2 : ℕ) ≤ N₀ := by unfold N₀; norm_num
  omega

/-- `0 < θn n` for `n ≥ N₀`. -/
theorem θn_pos (n : ℕ) (hn : N₀ ≤ n) : 0 < θn n := by
  have := θn_ge_30000 n hn; omega

/-- `θn n ≤ n` for `n ≥ N₀` (the feeder count never exceeds the population). -/
theorem θn_le_n (n : ℕ) (hn : N₀ ≤ n) : θn n ≤ n := by
  have h1 : (θn n : ℝ) ≤ (n : ℝ) ^ ((3 : ℝ) / 5) := θn_le n (by have := N₀_pos n hn; omega)
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by
    have := N₀_pos n hn; exact_mod_cast (by omega : 1 ≤ n)
  have h2 : (n : ℝ) ^ ((3 : ℝ) / 5) ≤ (n : ℝ) ^ (1 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hn1 (by norm_num)
  rw [Real.rpow_one] at h2
  have : (θn n : ℝ) ≤ (n : ℝ) := le_trans h1 h2
  exact_mod_cast this

/-! ## Part 3 — the front threshold fraction `θ := θn/n` and its floor `1/n ≤ θ`. -/

/-- The front threshold fraction `θ = θn/n = n^{−2/5}`. -/
noncomputable def θ (n : ℕ) : ℝ := (θn n : ℝ) / (n : ℝ)

/-- `0 < θ n` for `n ≥ N₀`. -/
theorem θ_pos (n : ℕ) (hn : N₀ ≤ n) : 0 < θ n := by
  unfold θ
  have h1 : (0 : ℝ) < (θn n : ℝ) := by exact_mod_cast θn_pos n hn
  have h2 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast N₀_pos n hn
  positivity

/-- `1/n ≤ θ n` for `n ≥ N₀` (the front floor needed by `goodFrontWidth_whp`). -/
theorem one_div_le_θ (n : ℕ) (hn : N₀ ≤ n) : 1 / (n : ℝ) ≤ θ n := by
  unfold θ
  have h2 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast N₀_pos n hn
  rw [div_le_div_iff_of_pos_right h2]
  have : 1 ≤ θn n := θn_pos n hn
  exact_mod_cast this

/-! ## Part 4 — the negligibility scale fact `tt·n ≤ (1−cc)·θn²` at `cc = 9/10`, `n ≥ N₀`.

`(1−cc)·θn² = θn²/10`.  At `θn ≥ n^{3/5}−1`, `tt ≤ n^{3/20}`: `tt·n ≤ n^{23/20}` and
`θn²/10 ≥ (n^{3/5}−1)²/10`.  At `n ≥ 10^{40}` the gap is comfortable (`n^{3/20}·n ≤ (n^{3/5}−1)²/10`
since `n^{6/5}/n^{23/20} = n^{1/20} ≥ 10^2 ≫ 10`). -/

/-- The negligibility scale inequality `tt·n ≤ (1−9/10)·θn²` at `n ≥ N₀`. -/
theorem tt_scale (n : ℕ) (hn : N₀ ≤ n) :
    (tt n : ℝ) * (n : ℝ) ≤ (1 - (9/10 : ℝ)) * (θn n : ℝ) ^ 2 := by
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast N₀_pos n hn
  -- tt ≤ n^{3/20}.
  have httle : (tt n : ℝ) ≤ (n : ℝ) ^ ((3 : ℝ) / 20) := tt_le n
  have htt0 : (0 : ℝ) ≤ (tt n : ℝ) := by positivity
  -- θn ≥ n^{3/5} − 1 ≥ 10^{24} − 1 (so θn ≥ (9/10)·n^{3/5} comfortably).
  have hθlo : (n : ℝ) ^ ((3 : ℝ) / 5) - 1 ≤ (θn n : ℝ) := sub_one_le_θn n
  have hrpge : (10 : ℝ) ^ (24 : ℕ) ≤ (n : ℝ) ^ ((3 : ℝ) / 5) := rpow_three_fifths_ge n hn
  -- so θn ≥ n^{3/5} − 1 ≥ (1 − 10^{-24})·n^{3/5} ≥ (9/10)·n^{3/5}.
  have hθlo2 : (9/10 : ℝ) * (n : ℝ) ^ ((3 : ℝ) / 5) ≤ (θn n : ℝ) := by
    refine le_trans ?_ hθlo
    nlinarith [hrpge]
  have hθ0 : (0 : ℝ) ≤ (θn n : ℝ) := by positivity
  -- θn² ≥ (9/10)²·n^{6/5}.
  have hθsq : (81/100 : ℝ) * ((n : ℝ) ^ ((3 : ℝ) / 5)) ^ 2 ≤ (θn n : ℝ) ^ 2 := by
    have hrp0 : (0 : ℝ) ≤ (n : ℝ) ^ ((3 : ℝ) / 5) := by positivity
    nlinarith [hθlo2, hrp0, hθ0]
  -- (n^{3/5})² = n^{6/5}; tt·n ≤ n^{3/20}·n = n^{23/20}.
  have hsq_eq : ((n : ℝ) ^ ((3 : ℝ) / 5)) ^ 2 = (n : ℝ) ^ ((6 : ℝ) / 5) := by
    rw [← Real.rpow_natCast ((n : ℝ) ^ ((3 : ℝ) / 5)) 2, ← Real.rpow_mul (le_of_lt hnpos)]
    norm_num
  have httn_eq : (n : ℝ) ^ ((3 : ℝ) / 20) * (n : ℝ) = (n : ℝ) ^ ((23 : ℝ) / 20) := by
    have : (n : ℝ) ^ ((3 : ℝ) / 20) * (n : ℝ) ^ (1 : ℝ) = (n : ℝ) ^ ((23 : ℝ) / 20) := by
      rw [← Real.rpow_add hnpos]; norm_num
    rwa [Real.rpow_one] at this
  -- the binding scale gap n^{23/20} ≤ (81/1000)·n^{6/5}, i.e. (810/1000)·n^{1/20} ≥ 1 — huge at N₀.
  have hgap : (n : ℝ) ^ ((23 : ℝ) / 20) ≤ (81/1000 : ℝ) * (n : ℝ) ^ ((6 : ℝ) / 5) := by
    have hfac : (n : ℝ) ^ ((6 : ℝ) / 5) = (n : ℝ) ^ ((23 : ℝ) / 20) * (n : ℝ) ^ ((1 : ℝ) / 20) := by
      rw [← Real.rpow_add hnpos]; norm_num
    rw [hfac]
    have hn120 : (10 : ℝ) ^ (2 : ℕ) ≤ (n : ℝ) ^ ((1 : ℝ) / 20) := by
      have hNℝ : ((10 : ℝ) ^ (40 : ℕ)) ≤ (n : ℝ) := by
        have : (N₀ : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
        rwa [N₀_cast] at this
      have : ((10 : ℝ) ^ (40 : ℕ)) ^ ((1 : ℝ) / 20) ≤ (n : ℝ) ^ ((1 : ℝ) / 20) :=
        Real.rpow_le_rpow (by positivity) hNℝ (by norm_num)
      refine le_trans ?_ this
      rw [← Real.rpow_natCast (10 : ℝ) 40, ← Real.rpow_natCast (10 : ℝ) 2,
        ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 10)]
      norm_num
    have hrp23 : (0 : ℝ) ≤ (n : ℝ) ^ ((23 : ℝ) / 20) := by positivity
    nlinarith [hn120, hrp23]
  -- chain: tt·n ≤ n^{23/20} ≤ (81/1000)n^{6/5} = (1/10)·(81/100)n^{6/5} ≤ (1/10)·θn².
  calc (tt n : ℝ) * (n : ℝ) ≤ (n : ℝ) ^ ((3 : ℝ) / 20) * (n : ℝ) := by
        apply mul_le_mul_of_nonneg_right httle (le_of_lt hnpos)
    _ = (n : ℝ) ^ ((23 : ℝ) / 20) := httn_eq
    _ ≤ (81/1000 : ℝ) * (n : ℝ) ^ ((6 : ℝ) / 5) := hgap
    _ = (1 - (9/10 : ℝ)) * ((81/100 : ℝ) * ((n : ℝ) ^ ((3 : ℝ) / 5)) ^ 2) := by
        rw [hsq_eq]; ring
    _ ≤ (1 - (9/10 : ℝ)) * (θn n : ℝ) ^ 2 := by
        apply mul_le_mul_of_nonneg_left hθsq (by norm_num)

end DotyParams

end ExactMajority
