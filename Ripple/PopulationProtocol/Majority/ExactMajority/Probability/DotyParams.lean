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

/-- The number of recurrence windows over the per-hour horizon.  Free at the steps-1–2 level (the
O(log n) clock coupling is the downstream Phase-B step 3–4 work); chosen here to cover the per-minute
clock run `capMinute = K(L+1)` with one window per minute. -/
def KK (L K : ℕ) : ℕ := ClockFrontShape.capMinute (L := L) (K := K) + 1

/-- The global MGF scale `σ`, chosen so that the smallness gate `σ·(1+4/n)^{w·KK} ≤ 1/2` holds with
EQUALITY — the tightest value (any smaller `σ` also works).  This couples `σ` and `KK` together as
the doctrine requires. -/
noncomputable def σ (L K n : ℕ) : ℝ :=
  (1/2) * (1 + 4 / (n : ℝ)) ^ (-(((w n * KK L K : ℕ) : ℤ)))

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

/-! ## Part 5 — the `σ`/`KK` smallness gate `hsmall : σ·(1+4/n)^{w·KK} ≤ 1/2`. -/

/-- `0 < 1 + 4/n` for `n ≥ N₀`. -/
theorem base_pos (n : ℕ) (hn : N₀ ≤ n) : (0 : ℝ) < 1 + 4 / (n : ℝ) := by
  have h2 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast N₀_pos n hn
  positivity

/-- `0 < σ` for `n ≥ N₀`. -/
theorem σ_pos (n : ℕ) (hn : N₀ ≤ n) : 0 < σ (L := L) (K := K) n := by
  unfold σ
  have hb := base_pos n hn
  positivity

/-- The smallness gate holds with equality: `σ·(1+4/n)^{w·KK} = 1/2 ≤ 1/2`. -/
theorem hsmall_eq (n : ℕ) (hn : N₀ ≤ n) :
    σ (L := L) (K := K) n * (1 + 4 / (n : ℝ)) ^ (w n * KK L K) ≤ 1 / 2 := by
  unfold σ
  have hb := base_pos n hn
  have hb0 : (1 + 4 / (n : ℝ)) ≠ 0 := ne_of_gt hb
  rw [mul_assoc]
  rw [show ((1 + 4 / (n : ℝ)) ^ (-(((w n * KK L K : ℕ) : ℤ)))) * (1 + 4 / (n : ℝ)) ^ (w n * KK L K)
      = (1 + 4 / (n : ℝ)) ^ (-(((w n * KK L K : ℕ) : ℤ))) * (1 + 4 / (n : ℝ)) ^ (((w n * KK L K : ℕ) : ℤ)) by
        rw [zpow_natCast]]
  rw [← zpow_add₀ hb0]
  simp

/-! ## Part 6 — `neg_params`: the negligibility predicate holds for ALL `n`-card configs.

The negligibility conjunct in `windowedFrontProfile_whp_packaged`'s event is a CONDITIONING; here we
show it holds AUTOMATICALLY on every `n`-card config (`n ≥ N₀`), so the concrete corollary can drop it
from the event.  At a level `T` with `θ ≤ frac T c` (i.e. the feeder is past the floor `θn`), the
`d`-term `tt` is absorbed by the `(1−cc)X²/n` recurrence slack via `negligibility_le` + `tt_scale`. -/

/-- **`neg_params`** — for every `n`-card config (`n ≥ N₀`), the per-level negligibility
`cc·X²/n + tt ≤ X²/n` holds at every level `T` whose fraction is past the floor `θ`.  This is the
exact negligibility conjunct of `windowedFrontProfile_whp_packaged` at `cc = 9/10`, `θ = θn/n`,
`tt = tt n`, and it holds for ALL such configs (so the corollary drops it from the event). -/
theorem neg_params (n : ℕ) (hn : N₀ ≤ n) (c : Config (AgentState L K)) (hcard : c.card = n) :
    ∀ T, θ n ≤ ClockFrontProfile.frac (L := L) (K := K) T c →
      (9/10 : ℝ) * (rBeyond (L := L) (K := K) T c : ℝ) ^ 2 / (n : ℝ) + (tt n : ℝ)
        ≤ (rBeyond (L := L) (K := K) T c : ℝ) ^ 2 / (n : ℝ) := by
  intro T hfrac
  have hnpos : 0 < n := N₀_pos n hn
  have hnℝ : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hnpos
  -- frac T c = rBeyond T c / card = rBeyond T c / n; θ = θn/n; so θ ≤ frac ⟹ θn ≤ rBeyond T c.
  have hθX : θn n ≤ rBeyond (L := L) (K := K) T c := by
    unfold ClockFrontProfile.frac θ at hfrac
    rw [hcard] at hfrac
    rw [div_le_div_iff_of_pos_right hnℝ] at hfrac
    exact_mod_cast hfrac
  exact negligibility_le n hnpos (9/10) (by norm_num) (θn n)
    (rBeyond (L := L) (K := K) T c) (tt n) hθX (tt_scale n hn)

/-! ## Part 7 — the all-clean Doty start dischargers (`h0`/`hmark` inputs).

The Doty start is the all-clean marked configuration (every agent mark `= false`) in the hour region
(`card = n`, all clocks at phase ≥ 3) with the recurrence window NOT yet open at any level (some
clock still at phase 3, i.e. `¬AllClockP3`).  At such a start, `MarkInv T` is vacuous (no taint) and
`recInv T` holds via `recInv_of_window_closed` for every `T`.  These supply the per-level `h0`/`hmark`
inputs of `windowedFrontProfile_whp_packaged`. -/

/-- **`hmark_params`** — the all-clean start satisfies `MarkInv` at every level. -/
theorem hmark_params (mc₀ : Config (MarkedAgent L K)) (hclean : ∀ m ∈ mc₀, m.2 = false) :
    ∀ T, MarkInv (L := L) (K := K) T mc₀ :=
  fun T => markInv_of_clean (L := L) (K := K) T mc₀ hclean

/-- **`h0_params`** — the all-clean, window-closed start (in-region, but the recurrence window not yet
open: `¬AllClockP3`) satisfies `recInv T θn n cc` at every level `T`, for any `cc`.  This is the
genuine Doty start (every clock still ≤ phase 3). -/
theorem h0_params (n : ℕ) (cc : ℝ) (mc₀ : Config (MarkedAgent L K))
    (hcard : mc₀.card = n)
    (hge3 : AllClockGE3 (L := L) (K := K) (eraseConfig (L := L) (K := K) mc₀))
    (hnotP3 : ¬ AllClockP3 (L := L) (K := K) (eraseConfig (L := L) (K := K) mc₀)) :
    ∀ T, recInv (L := L) (K := K) T (θn n) n cc mc₀ :=
  fun T => recInv_of_window_closed (L := L) (K := K) T (θn n) n cc mc₀ hcard hge3 (Or.inl hnotP3)

/-! ## Part 8 — the ladder cap `aM` and its `n ≤ 10·aM` fact. -/

/-- The ladder cap `aM := n/10 + 1` (so `10·aM ≥ n`, the `recurrence_checkpoint` cap honest). -/
def aM (n : ℕ) : ℕ := n / 10 + 1

/-- `n ≤ 10·aM n`. -/
theorem n_le_ten_aM (n : ℕ) : n ≤ 10 * aM n := by
  unfold aM; omega

/-! ## Part 9 — the assembled concrete corollary `windowedFrontProfile_whp_concrete`.

Specializes `windowedFrontProfile_whp_packaged` at the concrete parameters (`θn n`, `w n`, `θ n`,
`aM n`, `KK`, `σ`, `tt n`).  The smallness gate `hsmall` is discharged (`hsmall_eq`); the negligibility
conjunct is dropped from the event (it holds automatically via `neg_params`, so the event sets are
equal); the per-level start hypotheses `h0`/`hmark` come from the all-clean window-closed start.

GENUINELY-REMAINING inputs, carried as NAMED hypotheses (these are the two pieces still open in the
campaign — documented in the doctrine):
- `hB` — the per-window recurrence bad-event bound (item 1, the two-regime ceiling ladder; the
  doctrine's last big arithmetic; `hB_discharge` supplies its shape but carries ceiling/scale facts).
- `hdB`/`heB`/`htB` — the uniform per-level tail bounds.  `htB` is the explicit taint tail
  (`tainted_marked_tail_explicit`'s shape); `heB` is the hour-escape mass (the bulk-arrival epidemic,
  benign but not yet bounded as a Lean term — the doctrine's flagged residual).  `hdB` = `δ T ≤ dB`. -/

open ClockFrontProfile in
/-- **`windowedFrontProfile_whp_concrete`** — `windowedFrontProfile_whp_packaged` specialized at the
concrete parameters, with `hsmall` discharged, the negligibility conjunct removed from the event (it
holds automatically), and the all-clean window-closed start supplying `h0`/`hmark`.  The per-window
bound `hB` and the uniform tail bounds `hdB`/`heB`/`htB` are carried as named hypotheses (the campaign's
two open residuals). -/
theorem windowedFrontProfile_whp_concrete (n : ℕ) (hn : N₀ ≤ n)
    (mc₀ : Config (MarkedAgent L K))
    (hcard : mc₀.card = n)
    (hge3 : AllClockGE3 (L := L) (K := K) (eraseConfig (L := L) (K := K) mc₀))
    (hnotP3 : ¬ AllClockP3 (L := L) (K := K) (eraseConfig (L := L) (K := K) mc₀))
    (hclean : ∀ m ∈ mc₀, m.2 = false)
    (Tcap : ℕ) (hcap : ClockFrontShape.capMinute (L := L) (K := K) < Tcap)
    (δ : ℕ → ℝ≥0∞)
    (hB : ∀ T, ∀ mc, recInv (L := L) (K := K) T (θn n) n (9/10) mc →
      AllClockP3 (L := L) (K := K) (eraseConfig (L := L) (K := K) mc) →
      10 * rBeyond (L := L) (K := K) T (eraseConfig (L := L) (K := K) mc) ≤ n →
      ((markedK (L := L) (K := K) T (θn n)) ^ (w n)) mc
          {mc' | ((9/10 : ℝ) * (rBeyond (L := L) (K := K) T
                (eraseConfig (L := L) (K := K) mc') : ℝ) ^ 2 / (n : ℝ)
              < (cleanAbove (L := L) (K := K) T mc' : ℝ)) ∧
            rBeyond (L := L) (K := K) T (eraseConfig (L := L) (K := K) mc') ≤ aM n ∧
            mc'.card = n ∧ AllClockP3 (L := L) (K := K) (eraseConfig (L := L) (K := K) mc')}
        ≤ δ T)
    (dB eB tB : ℝ≥0∞)
    (hdB : ∀ T < Tcap, δ T ≤ dB)
    (heB : ∀ T < Tcap,
      (GatedDrift.killK (markedK (L := L) (K := K) T (θn n))
          (taintedGate (L := L) (K := K) n) ^ (w n * KK L K)) (some mc₀) {none} ≤ eB)
    (htB : ∀ T < Tcap,
      ENNReal.ofReal
        (Real.exp (σ (L := L) (K := K) n * (1 + 4 / (n : ℝ)) ^ (w n * KK L K)
            * (taintedCount (L := L) (K := K) mc₀ : ℝ)
          + 2 * σ (L := L) (K := K) n * (1 + 4 / (n : ℝ)) ^ (w n * KK L K)
              * ((θn n : ℝ) / (n : ℝ)) ^ 2 * ((w n * KK L K : ℕ) : ℝ)
          - σ (L := L) (K := K) n * ((tt n + 1 : ℕ) : ℝ))) ≤ tB) :
    ((NonuniformMajority L K).transitionKernel ^ (w n * KK L K))
        (eraseConfig (L := L) (K := K) mc₀)
        {c | (c.card = n ∧ AllClockP3 (L := L) (K := K) c)
          ∧ ¬ WindowedFrontProfile (L := L) (K := K) (θ n) c}
      ≤ (Tcap : ℝ≥0∞) * ((KK L K : ℝ≥0∞) * dB + (eB + tB)) := by
  classical
  -- the no-neg event equals the with-neg event (neg holds automatically on card=n configs).
  have hset : {c : Config (AgentState L K) | (c.card = n ∧ AllClockP3 (L := L) (K := K) c)
        ∧ ¬ WindowedFrontProfile (L := L) (K := K) (θ n) c}
      ⊆ {c | (c.card = n ∧ AllClockP3 (L := L) (K := K) c ∧
          (∀ T, θ n ≤ ClockFrontProfile.frac (L := L) (K := K) T c →
            (9/10 : ℝ) * (rBeyond (L := L) (K := K) T c : ℝ) ^ 2 / (n : ℝ) + (tt n : ℝ)
              ≤ (rBeyond (L := L) (K := K) T c : ℝ) ^ 2 / (n : ℝ)))
        ∧ ¬ WindowedFrontProfile (L := L) (K := K) (θ n) c} := by
    intro c hc
    obtain ⟨⟨hcardc, hP3⟩, hwfp⟩ := hc
    exact ⟨⟨hcardc, hP3, neg_params n hn c hcardc⟩, hwfp⟩
  refine le_trans (measure_mono hset) ?_
  exact windowedFrontProfile_whp_packaged (L := L) (K := K) (θn n) n (two_le n hn) (9/10) (w n)
    (θ n) (θ_pos n hn) (fun _ => aM n) (fun _ => n_le_ten_aM n) δ hB
    (σ (L := L) (K := K) n) (σ_pos n hn) (KK L K) (hsmall_eq (L := L) (K := K) n hn)
    (tt n) Tcap hcap mc₀
    (fun T _ => h0_params n (9/10) mc₀ hcard hge3 hnotP3 T)
    (fun T _ => hmark_params mc₀ hclean T)
    dB eB tB hdB heB htB

/-! ## Part 10 — `climbBound_whp_concrete`: the climb-failure mass at the concrete `θ = θn/n`.

`climbBound_whp` is already self-contained (it produces the level-sum of `ClimbTail.climb_real_tail`'s
gated tails, no carried scale hypotheses), so the concrete version is a direct specialization at
`θ n = θn n / n`.  The climb window `W₂`, the per-level gate bound `B'`, and the MGF slope `s` and
horizon `t` are free parameters (the paper scales `B' = n^{0.2}`, `s = Θ(log n)`, `W₂ = Θ(loglog n)`
are plugged when the climb tail is shown `n^{−ω(1)}` downstream). -/

open ClockFrontProfile in
theorem climbBound_whp_concrete (n W₂ : ℕ) (hn : N₀ ≤ n) (hW₂ : 2 ≤ W₂)
    (B' : ℕ) (s : ℝ) (hs : 0 ≤ s) (t : ℕ) (c₀ : Config (AgentState L K)) :
    ((NonuniformMajority L K).transitionKernel ^ t) c₀
        {c | (c.card = n ∧ AllClockP3 (L := L) (K := K) c)
          ∧ ¬ ClimbBound (L := L) (K := K) (θ n) W₂ c}
      ≤ ∑ k ∈ Finset.range (ClockFrontShape.capMinute (L := L) (K := K) + 1),
          ((GatedDrift.killK ((NonuniformMajority L K).transitionKernel)
              (ClimbTail.climbGate (L := L) (K := K) n k B' (θn n)) ^ t) (some c₀) {none} +
            (ENNReal.ofReal (1 + ((B' : ℝ) / (n : ℝ)) ^ 2 * (Real.exp s - 1))) ^ t *
              ClimbTail.climbPot (L := L) (K := K) k (θn n) s c₀ /
              ENNReal.ofReal (Real.exp (s * ((W₂ : ℝ) - 1)))) :=
  climbBound_whp (L := L) (K := K) n (θn n) W₂ (N₀_pos n hn) hW₂ (θ n) rfl B' s hs t c₀

/-! ## Part 11 — `goodFrontWidth_whp_concrete`: the moving-frame width invariant whp.

`goodFrontWidth_whp` is the deterministic glue `GoodFrontWidth (W₁+W₂) ⟸ WindowedFrontProfile ∧
ClimbBound` lifted to the real kernel.  Its two inputs are the WindowedFrontProfile tail
(`windowedFrontProfile_whp_concrete`'s packaging — carried here as `hwfp`) and the ClimbBound mass
(`climbBound_whp_concrete` — carried as `hclimb`).  At the concrete floor `1/n ≤ θ n` (Part 3), the
glue gives `GoodFrontWidth (frontWidthBound n + W₂)` whp.  This is the exact clock-consumer shape that
retires the false `hwin_all` (the downstream rewire, Phase-B step 3–4). -/

open ClockFrontProfile in
theorem goodFrontWidth_whp_concrete (n : ℕ) (hn : N₀ ≤ n) (W₂ : ℕ) (t : ℕ)
    (mc₀ : Config (MarkedAgent L K)) (wfpB climbB : ℝ≥0∞)
    (hwfp : ((NonuniformMajority L K).transitionKernel ^ t) (eraseConfig (L := L) (K := K) mc₀)
        {c | (c.card = n ∧ AllClockP3 (L := L) (K := K) c ∧
            (∀ T, θ n ≤ ClockFrontProfile.frac (L := L) (K := K) T c →
              (9/10 : ℝ) * (rBeyond (L := L) (K := K) T c : ℝ) ^ 2 / (n : ℝ) + (tt n : ℝ)
                ≤ (rBeyond (L := L) (K := K) T c : ℝ) ^ 2 / (n : ℝ)))
          ∧ ¬ WindowedFrontProfile (L := L) (K := K) (θ n) c} ≤ wfpB)
    (hclimb : ((NonuniformMajority L K).transitionKernel ^ t) (eraseConfig (L := L) (K := K) mc₀)
        {c | (c.card = n ∧ AllClockP3 (L := L) (K := K) c)
          ∧ ¬ ClimbBound (L := L) (K := K) (θ n) W₂ c} ≤ climbB) :
    ((NonuniformMajority L K).transitionKernel ^ t) (eraseConfig (L := L) (K := K) mc₀)
        {c | (c.card = n ∧ AllClockP3 (L := L) (K := K) c ∧
            (∀ T, θ n ≤ ClockFrontProfile.frac (L := L) (K := K) T c →
              (9/10 : ℝ) * (rBeyond (L := L) (K := K) T c : ℝ) ^ 2 / (n : ℝ) + (tt n : ℝ)
                ≤ (rBeyond (L := L) (K := K) T c : ℝ) ^ 2 / (n : ℝ)))
          ∧ ¬ GoodFrontWidth (L := L) (K := K)
              (FrontTail.frontWidthBound n + W₂) c}
      ≤ wfpB + climbB :=
  goodFrontWidth_whp (L := L) (K := K) n (two_le n hn) (9/10) (θ n) (one_div_le_θ n hn)
    (tt n) W₂ t mc₀ wfpB climbB hwfp hclimb

end DotyParams

end ExactMajority
