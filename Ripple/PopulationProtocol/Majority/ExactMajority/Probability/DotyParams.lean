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

/-! ## Part 12 — shared `hB` infrastructure: the window MGF scale `σw`, the smallness gate
`hsmallW`, and the `RW ≤ RWb` bound at the locked rationals.

The per-window engine `per_window_delta` runs at a window MGF scale `σw` (distinct from the global
gate scale `σ` of Part 5, which couples to `KK`).  `per_window_delta` needs `hsmall :
σw·(1+2(1+ε)/n)^w ≤ ε/(1+ε)` with `ε = 1/200`, and `slice_discharge` needs `RW ≤ RWb` with
`RWb = 1/(1−u)`, `u = 2(1+ε)·wp = 603/20000` (the exact `window_constants_slice` constant).  We fix
`σw := 1/250` and bound `RW = (1+2(1+ε)/n)^w ≤ exp(u) ≤ 1/(1−u) = RWb` via `w·y ≤ u`
(`y = 2(1+ε)/n`, `w = ⌊3n/200⌋`). -/

/-- The locked window-rung ratio `u := 2·(1+1/200)·(3/200) = 603/20000` (the `RWb = 1/(1−u)`
denominator of `window_constants_slice`). -/
noncomputable def uW : ℝ := 603 / 20000

/-- The locked recurrence-window MGF bound `RWb := 1/(1−u)` (`window_constants_slice`'s constant). -/
noncomputable def RWb : ℝ := 1 / (1 - uW)

/-- The window MGF scale `σw := 1/250` (small enough for `hsmallW`). -/
noncomputable def σw : ℝ := 1 / 250

theorem σw_pos : (0 : ℝ) < σw := by unfold σw; norm_num

/-- `0 < 1 + 2·(1+1/200)/n` for `n ≥ N₀`. -/
theorem baseW_pos (n : ℕ) (hn : N₀ ≤ n) : (0 : ℝ) < 1 + 2 * (1 + (1/200 : ℝ)) / (n : ℝ) := by
  have h2 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast N₀_pos n hn
  positivity

/-- `(w n : ℝ) · (2·(1+1/200)/n) ≤ u = 603/20000` (the rung-ratio bound; `w = ⌊3n/200⌋`). -/
theorem w_y_le_uW (n : ℕ) (hn : N₀ ≤ n) :
    (w n : ℝ) * (2 * (1 + (1/200 : ℝ)) / (n : ℝ)) ≤ uW := by
  have hnpos : 0 < n := N₀_pos n hn
  have hnℝ : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hnpos
  -- w n = 3*n/200 ≤ 3n/200 (Nat floor), so (w n : ℝ) ≤ 3*(n:ℝ)/200.
  have hwle : (w n : ℝ) ≤ 3 * (n : ℝ) / 200 := by
    unfold w
    rw [le_div_iff₀ (by norm_num : (0:ℝ) < 200)]
    have hmul : (3 * n / 200 : ℕ) * 200 ≤ 3 * n := Nat.div_mul_le_self (3 * n) 200
    calc ((3 * n / 200 : ℕ) : ℝ) * 200 = (((3 * n / 200 : ℕ) * 200 : ℕ) : ℝ) := by push_cast; ring
      _ ≤ ((3 * n : ℕ) : ℝ) := by exact_mod_cast hmul
      _ = 3 * (n : ℝ) := by push_cast; ring
  -- (w n)·(2(1+1/200)/n) ≤ (3n/200)·(201/100/n) = 3·201/20000 = 603/20000.
  have hy0 : (0 : ℝ) ≤ 2 * (1 + (1/200 : ℝ)) / (n : ℝ) := by positivity
  calc (w n : ℝ) * (2 * (1 + (1/200 : ℝ)) / (n : ℝ))
      ≤ (3 * (n : ℝ) / 200) * (2 * (1 + (1/200 : ℝ)) / (n : ℝ)) :=
        mul_le_mul_of_nonneg_right hwle hy0
    _ = uW := by unfold uW; field_simp; ring

/-- `RW := (1+2(1+1/200)/n)^w ≤ 1/(1−u) = RWb` for `n ≥ N₀` (the `slice_discharge` MGF bound).
Chain: `(1+y)^w ≤ exp(y)^w = exp(w·y) ≤ exp(u) ≤ 1/(1−u)` (last step via
`exp_bound_div_one_sub_of_interval`, `u = 603/20000 < 1`). -/
theorem RW_le_RWb (n : ℕ) (hn : N₀ ≤ n) :
    (1 + 2 * (1 + (1/200 : ℝ)) / (n : ℝ)) ^ (w n) ≤ RWb := by
  set y : ℝ := 2 * (1 + (1/200 : ℝ)) / (n : ℝ) with hy
  have hy0 : (0 : ℝ) ≤ y := by rw [hy]; have := baseW_pos n hn; positivity
  -- (1+y)^w ≤ exp(y)^w
  have h1 : (1 + y) ^ (w n) ≤ (Real.exp y) ^ (w n) := by
    have hcomm : (1 + y) = (y + 1) := by ring
    rw [hcomm]
    exact pow_le_pow_left₀ (by linarith) (Real.add_one_le_exp y) (w n)
  -- exp(y)^w = exp(w·y)
  have h2 : (Real.exp y) ^ (w n) = Real.exp ((w n : ℝ) * y) := by
    rw [← Real.exp_nat_mul]
  -- w·y ≤ u
  have h3 : (w n : ℝ) * y ≤ uW := w_y_le_uW n hn
  -- exp(w·y) ≤ exp(u)
  have h4 : Real.exp ((w n : ℝ) * y) ≤ Real.exp uW := Real.exp_le_exp.mpr h3
  -- exp(u) ≤ 1/(1−u)
  have hu0 : (0 : ℝ) ≤ uW := by unfold uW; norm_num
  have hu1 : uW < 1 := by unfold uW; norm_num
  have h5 : Real.exp uW ≤ 1 / (1 - uW) := Real.exp_bound_div_one_sub_of_interval hu0 hu1
  calc (1 + y) ^ (w n) ≤ (Real.exp y) ^ (w n) := h1
    _ = Real.exp ((w n : ℝ) * y) := h2
    _ ≤ Real.exp uW := h4
    _ ≤ 1 / (1 - uW) := h5
    _ = RWb := rfl

/-! ## Part 13 — `hB_params`: the two-regime ceiling-ladder discharge of the carried `hB` hypothesis.

The concrete corollary `windowedFrontProfile_whp_concrete` carries `hB` (the per-window recurrence
bad-event bound) as a named hypothesis.  Here we discharge it at the concrete parameters, splitting
each invariant window-open start `mc₀` on the feeder regime `X₀ := rBeyond T (erase mc₀)`:
- REGIME 1 (`θn ≤ X₀`, `41·X₀ ≤ 4n`): the full geometric ceiling ladder `a m = ⌈G^m·⌈g·X₀⌉⌉`,
  `M` rungs up to `aM`, via `per_window_delta` with `floor_discharge`/`slice_discharge`.
- REGIME 2 (`4n < 41·X₀`, `10·X₀ ≤ n`): the band is thinner than one growth factor, so `M = 0`,
  a single floor rung `a 0 = aM`; the bad bound is the bare upward-growth floor exponent of
  `per_window_ladder_up`, bounded `≤ −6·n/10⁶ < 0` by `X₀ > 4n/41`, `a0 = aM ≤ n/10+1`.

The uniform `δ T := regime1Val + regime2Val` (constant in `T`) bounds both branches.  `σ := σw =
1/250` (so `hsmall` holds via `RW_le_RWb`).  This is the campaign's "last big arithmetic". -/

/-- The provable rational lower bound `47/500 ≤ 1 − e^{−1/10}` (needed for the regime-2 margin; the
crude `1−e^{−s} ≥ (1−s)s = 9/100` is too weak — regime 2 needs `> 0.0926`).  Via `Real.exp_bound`
at `n = 3` (cubic Taylor remainder `≤ 1/4000`). -/
theorem one_sub_exp_neg_tenth : (47/500 : ℝ) ≤ 1 - Real.exp (-(1/10 : ℝ)) := by
  have hb := Real.exp_bound (x := -(1/10 : ℝ)) (by rw [abs_neg, abs_of_nonneg] <;> norm_num)
    (n := 3) (by norm_num)
  have hsum : ∑ m ∈ Finset.range 3, (-(1/10 : ℝ)) ^ m / m.factorial = 1 - 1/10 + 1/200 := by
    simp [Finset.sum_range_succ, Nat.factorial]; norm_num
  rw [hsum] at hb
  have hrem : |(-(1/10 : ℝ))| ^ 3 * ((3:ℕ).succ / ((3:ℕ).factorial * 3)) ≤ 1/4000 := by
    rw [abs_neg, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 1/10)]
    norm_num [Nat.factorial]
  have hupper : Real.exp (-(1/10:ℝ)) ≤ (1 - 1/10 + 1/200) + 1/4000 := by
    have := abs_le.1 hb
    nlinarith [this.2, hrem]
  linarith

/-- The window MGF scale `σw = 1/250` satisfies the `per_window_delta` smallness gate
`σw·(1+2(1+1/200)/n)^w ≤ (1/200)/(1+1/200)` for `n ≥ N₀` (via `RW_le_RWb`, `RWb ≤ 250/201`). -/
theorem σw_hsmall (n : ℕ) (hn : N₀ ≤ n) :
    σw * (1 + 2 * (1 + (1/200 : ℝ)) / (n : ℝ)) ^ (w n) ≤ (1/200 : ℝ) / (1 + (1/200 : ℝ)) := by
  have hRW : (1 + 2 * (1 + (1/200 : ℝ)) / (n : ℝ)) ^ (w n) ≤ RWb := RW_le_RWb n hn
  have hRWb : RWb ≤ 250/201 := by unfold RWb uW; norm_num
  have hRWle : (1 + 2 * (1 + (1/200 : ℝ)) / (n : ℝ)) ^ (w n) ≤ 250/201 := le_trans hRW hRWb
  have hRW0 : (0 : ℝ) ≤ (1 + 2 * (1 + (1/200 : ℝ)) / (n : ℝ)) ^ (w n) := by
    have := baseW_pos n hn; positivity
  calc σw * (1 + 2 * (1 + (1/200 : ℝ)) / (n : ℝ)) ^ (w n)
      ≤ σw * (250/201) := by
        apply mul_le_mul_of_nonneg_left hRWle; unfold σw; norm_num
    _ ≤ (1/200 : ℝ) / (1 + (1/200 : ℝ)) := by unfold σw; norm_num

/-! ### Part 13a — the geometric-ladder reach `(201/200)^M·θn ≥ aM n`.

The ladder rung `a m = ⌈G^m·⌈g·X₀⌉⌉` (`G = 201/200`) must reach the cap `aM n = n/10+1` at the
saturation index.  The key growth fact is the EXPONENTIAL lower bound `(201/200)^{10000} ≥ 10^{15}`
(via `((201/200)^{200})^{50} ≥ 2^{50} ≥ 10^{15}`), which gives `(201/200)^{10000}·θn ≥ 10^{15}·10^{24}
= 10^{39} = n/10 ≥ aM n − 1`; the `2^{50} = 1.126·10^{15}` slack covers the `+1`. -/

/-- `(201/200)^{200} ≥ 2` (the doubling block; `(1.005)^{200} ≈ 2.71`). -/
theorem G_pow_200_ge_two : (2 : ℝ) ≤ (201/200 : ℝ) ^ 200 := by norm_num

/-- `(201/200)^{10000} ≥ 10^{15}` (the ladder-reach growth: `((201/200)^{200})^{50} ≥ 2^{50}`). -/
theorem G_pow_10000_ge : (10 : ℝ) ^ (15 : ℕ) ≤ (201/200 : ℝ) ^ (10000 : ℕ) := by
  have hchain : ((201/200 : ℝ) ^ 200) ^ 50 = (201/200 : ℝ) ^ (10000 : ℕ) := by rw [← pow_mul]
  have h2 : (2 : ℝ) ^ 50 ≤ ((201/200 : ℝ) ^ 200) ^ 50 :=
    pow_le_pow_left₀ (by norm_num) G_pow_200_ge_two 50
  calc (10 : ℝ) ^ (15 : ℕ) ≤ (2 : ℝ) ^ 50 := by norm_num
    _ ≤ ((201/200 : ℝ) ^ 200) ^ 50 := h2
    _ = (201/200 : ℝ) ^ (10000 : ℕ) := hchain

/-- **Bernoulli reach** `(201/200)^n ≥ 1 + n/200`.  The `M := n`-dependent ladder reach: the
geometric factor `G^M` with `M = n` beats the bare additive `1 + n/200` for free (no `G_pow_10000`
fixed-`M` saturation needed — the doctrine's n-dependent reach). -/
theorem G_pow_n_bernoulli (n : ℕ) : (1 : ℝ) + (n : ℝ) / 200 ≤ (201/200 : ℝ) ^ n := by
  have h := one_add_mul_le_pow (a := (1/200 : ℝ)) (by norm_num) n
  have he : (1 : ℝ) + 1/200 = 201/200 := by norm_num
  rw [he] at h
  calc (1 : ℝ) + (n : ℝ) / 200 = 1 + (n : ℝ) * (1/200) := by ring
    _ ≤ (201/200 : ℝ) ^ n := h

/-- **The n-dependent ladder reach** `(201/200)^n · θn ≥ aM n` for `n ≥ N₀`.  Via Bernoulli
`(201/200)^n ≥ 1 + n/200` and `(1 + n/200)·θn ≥ (n/200)·(10²⁴−1) ≥ n/10 + 1 = aM n`
(`θn ≥ 10²⁴−1`).  This is the reach used by `measure_mono` (cap `aMn ⊆` ladder-cap `a M`) so NO
exact `a M = aM n` saturation is needed. -/
theorem G_pow_n_reach (n : ℕ) (hn : N₀ ≤ n) :
    (aM n : ℝ) ≤ (201/200 : ℝ) ^ n * (θn n : ℝ) := by
  have hθlo : (10 : ℝ) ^ (24 : ℕ) - 1 ≤ (θn n : ℝ) :=
    le_trans (by linarith [rpow_three_fifths_ge n hn]) (sub_one_le_θn n)
  have hθ1 : (1 : ℝ) ≤ (θn n : ℝ) := by
    have : (30000 : ℝ) ≤ (θn n : ℝ) := by exact_mod_cast θn_ge_30000 n hn
    linarith
  have hbern : (1 : ℝ) + (n : ℝ) / 200 ≤ (201/200 : ℝ) ^ n := G_pow_n_bernoulli n
  have hnℝ : (1 : ℝ) ≤ (n : ℝ) := by
    have := N₀_pos n hn; exact_mod_cast (by omega : 1 ≤ n)
  -- aM n = n/10 + 1 ≤ (1 + n/200)·θn ≤ (201/200)^n·θn.
  have haMle : (aM n : ℝ) ≤ (n : ℝ) / 10 + 1 := by
    have heq : (aM n : ℕ) = n / 10 + 1 := rfl
    have hdiv : (10 : ℝ) * ((n / 10 : ℕ) : ℝ) ≤ (n : ℝ) := by
      have := Nat.div_mul_le_self n 10
      have : (10 * (n / 10) : ℕ) ≤ n := by omega
      calc (10 : ℝ) * ((n / 10 : ℕ) : ℝ) = ((10 * (n / 10) : ℕ) : ℝ) := by push_cast; ring
        _ ≤ (n : ℝ) := by exact_mod_cast this
    rw [heq]; push_cast; linarith [hdiv]
  have hθpos : (0 : ℝ) ≤ (θn n : ℝ) := by linarith
  have hstep1 : (n : ℝ) / 10 + 1 ≤ (1 + (n : ℝ) / 200) * (θn n : ℝ) := by
    have hmul : (1 + (n : ℝ) / 200) * (θn n : ℝ)
        ≥ (1 + (n : ℝ) / 200) * ((10 : ℝ) ^ (24 : ℕ) - 1) := by
      apply mul_le_mul_of_nonneg_left hθlo
      positivity
    nlinarith [hmul, hnℝ]
  have hstep2 : (1 + (n : ℝ) / 200) * (θn n : ℝ) ≤ (201/200 : ℝ) ^ n * (θn n : ℝ) :=
    mul_le_mul_of_nonneg_right hbern hθpos
  linarith [haMle, hstep1, hstep2]

/-- **The per-rung ceiling-inflation cap** (the core drip-cap arithmetic): if a ladder rung satisfies
`a_succ ≤ Gp·a0 + 1` with `a0 ≤ g·X₀ + 1`, `1 ≤ Gp`, `1 ≤ g`, and the feeder is large
(`30000 ≤ g·X₀`, comfortably met by `X₀ ≥ θn ≥ 30000`), then `(a_succ)² ≤ κ·Gp²·g²·X₀²` for
`κ = 1 + 1/10000`.  The κ slack (`√κ ≈ 1+5e-5`) absorbs the two `+1` ceiling roundings
(`a_succ ≤ Gp·g·X₀·(1 + 2/(g·X₀)) ≤ Gp·g·X₀·(1+2/30000)`, and `(1+2/30000)² < κ`). -/
theorem rung_sq_cap (a_succ a0 Gp g X₀ : ℝ)
    (hGp : 1 ≤ Gp) (hg : 1 ≤ g) (hX₀ : 30000 ≤ g * X₀)
    (ha0 : a0 ≤ g * X₀ + 1) (hsucc : a_succ ≤ Gp * a0 + 1)
    (hasucc0 : 0 ≤ a_succ) :
    a_succ ^ 2 ≤ (1 + 1/10000 : ℝ) * Gp ^ 2 * g ^ 2 * X₀ ^ 2 := by
  have hX₀0 : (0 : ℝ) < X₀ := by nlinarith [hg, hX₀]
  have hgX0 : (0 : ℝ) < g * X₀ := by linarith
  -- a_succ ≤ Gp·(g·X₀+1)+1 = Gp·g·X₀ + Gp + 1 ≤ Gp·g·X₀ + 2·Gp = Gp·g·X₀·(1 + 2/(g·X₀)).
  have hub : a_succ ≤ Gp * (g * X₀) * (1 + 2 / (g * X₀)) := by
    have h1 : a_succ ≤ Gp * (g * X₀ + 1) + 1 := by
      refine le_trans hsucc ?_
      have := mul_le_mul_of_nonneg_left ha0 (by linarith : (0:ℝ) ≤ Gp)
      linarith
    have h2 : Gp * (g * X₀ + 1) + 1 ≤ Gp * (g * X₀) + 2 * Gp := by nlinarith [hGp]
    have h3 : Gp * (g * X₀) + 2 * Gp = Gp * (g * X₀) * (1 + 2 / (g * X₀)) := by
      field_simp; ring
    linarith [h1, h2, h3.symm.le, h3.le]
  -- (1 + 2/(g·X₀))² ≤ (1 + 2/30000)² ≤ 1 + 1/10000 = κ.
  have hfrac : 2 / (g * X₀) ≤ 2 / 30000 := by
    apply div_le_div_of_nonneg_left (by norm_num) (by norm_num) hX₀
  have hinfl : (1 + 2 / (g * X₀)) ^ 2 ≤ (1 + 1/10000 : ℝ) := by
    have hbase : (0:ℝ) ≤ 2 / (g * X₀) := by positivity
    nlinarith [hfrac, hbase]
  -- square the upper bound.
  have hub0 : (0:ℝ) ≤ Gp * (g * X₀) * (1 + 2 / (g * X₀)) := by positivity
  have hsq : a_succ ^ 2 ≤ (Gp * (g * X₀) * (1 + 2 / (g * X₀))) ^ 2 := by
    nlinarith [hub, hasucc0, hub0]
  calc a_succ ^ 2 ≤ (Gp * (g * X₀) * (1 + 2 / (g * X₀))) ^ 2 := hsq
    _ = Gp ^ 2 * g ^ 2 * X₀ ^ 2 * (1 + 2 / (g * X₀)) ^ 2 := by ring
    _ ≤ Gp ^ 2 * g ^ 2 * X₀ ^ 2 * (1 + 1/10000 : ℝ) := by
        apply mul_le_mul_of_nonneg_left hinfl; positivity
    _ = (1 + 1/10000 : ℝ) * Gp ^ 2 * g ^ 2 * X₀ ^ 2 := by ring

/-! ### Part 13b — the INFLATED slice discharger (the fix for the ceiling-ladder drip↔threshold gap).

`EarlyDripMarked.slice_exp_le`/`slice_discharge` couple the drip cap and the threshold through the
rigid factor `G²` with ZERO rounding slack, so the geometric ceiling ladder `a_m = ⌈G^m·a0⌉` (where
`a_{m+1}/a_m ⪈ G` by the ⌈⌉) opens an irreducible ≈1.1e-8 gap (drip needs `Gm ≳ 1`, threshold allows
`Gm ≲ 1`, empty window for ~6988/7001 rungs; verified exact-fraction this session).

The fix: a κ-INFLATED slice bound with κ in the DRIP slot only (threshold stays bare `Gm`), so the
two decouple.  κ = 1+1/10000 covers the ⌈⌉ inflation `(1+1/(g·θn))² ≤ 1+2e-24` (θn ≥ 10^24) with vast
margin, and the conclusion bracket `cc·RWb − Gm·g²(cc − κ·G²(1+ε)RWb·wp)` is STILL negative
(`A − B' = −3.63e-4 < 0`, only 2e-6 worse than the un-inflated −3.65e-4). -/

/-- **The inflated slice-exponent bound**: as `EarlyDripMarked.slice_exp_le` but with a κ factor in
the drip cap (`drip·(1+ε)·RW ≤ Gm·κ·G²·g²·(1+ε)·RWb·wp·Q`) and the threshold kept bare
(`cc·Gm·g²·Q ≤ Yt`).  The κ decouples the drip and threshold rungs, absorbing the ceiling ladder's
`a_{m+1}/a_m ⪈ G` inflation; the conclusion bracket carries κ on the inner `G²` term only. -/
theorem slice_exp_le_inflated (Q σ ε RW RWb cc g G wp Y₀ drip Gm κ Yt : ℝ)
    (hσ : 0 ≤ σ) (hQ : 0 ≤ Q) (hRW0 : 0 ≤ RW) (hccnn : 0 ≤ cc)
    (hY : Y₀ ≤ cc * Q) (hRW : RW ≤ RWb)
    (hdrip : drip * (1 + ε) * RW ≤ Gm * κ * G ^ 2 * g ^ 2 * (1 + ε) * RWb * wp * Q)
    (hYt : cc * Gm * g ^ 2 * Q ≤ Yt) :
    σ * RW * Y₀ + drip * (1 + ε) * σ * RW - σ * Yt
      ≤ σ * (Q * (cc * RWb - Gm * (g ^ 2 * (cc - κ * G ^ 2 * (1 + ε) * RWb * wp)))) := by
  have hb1 : RW * Y₀ ≤ RWb * (cc * Q) := by
    calc RW * Y₀ ≤ RW * (cc * Q) := mul_le_mul_of_nonneg_left hY hRW0
      _ ≤ RWb * (cc * Q) := mul_le_mul_of_nonneg_right hRW (mul_nonneg hccnn hQ)
  have hkey : RW * Y₀ + drip * (1 + ε) * RW - Yt
      ≤ Q * (cc * RWb - Gm * (g ^ 2 * (cc - κ * G ^ 2 * (1 + ε) * RWb * wp))) := by
    nlinarith [hb1, hdrip, hYt]
  calc σ * RW * Y₀ + drip * (1 + ε) * σ * RW - σ * Yt
      = σ * (RW * Y₀ + drip * (1 + ε) * RW - Yt) := by ring
    _ ≤ σ * (Q * (cc * RWb - Gm * (g ^ 2 * (cc - κ * G ^ 2 * (1 + ε) * RWb * wp)))) :=
        mul_le_mul_of_nonneg_left hkey hσ

/-- **The inflated slice closing inequality** `A < B'` with `A = cc·RWb`,
`B' = g²(cc − κ·G²(1+ε)·RWb·wp)`, `κ = 1+1/10000` — the κ-decoupled analogue of
`EarlyDripMarked.window_constants_slice`.  Margin ≈ 3.63e-4 (only 2e-6 below the un-inflated gate),
so every ladder slice bracket `A − G^{2m}·B' < 0` still follows (`G^{2m} ≥ 1`, `B' > 0`). -/
theorem window_constants_slice_inflated :
    let wp : ℝ := 3/200
    let cc : ℝ := 9/10
    let ε : ℝ := 1/200
    let g : ℝ := 5123/5000
    let G : ℝ := 201/200
    let κ : ℝ := 1 + 1/10000
    let u : ℝ := 2 * (1 + ε) * wp
    let RWb : ℝ := 1 / (1 - u)
    cc * RWb < g^2 * (cc - κ * G^2 * (1 + ε) * RWb * wp) ∧
      (0 : ℝ) < g^2 * (cc - κ * G^2 * (1 + ε) * RWb * wp) := by
  norm_num

end DotyParams

end ExactMajority
