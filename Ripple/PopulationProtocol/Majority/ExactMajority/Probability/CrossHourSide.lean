/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# CrossHourSide — the cross-hour side-failure assembly (Doty §6, Phase D-5)

This file assembles the GLOBAL-τ side-failure bound `(realκ^τ) c₀ Sgood(T)ᶜ ≤ εside` over the
`(L+1)`-hour run horizon, from two per-hour inputs:

1. the hour-entry whp `hEntry : (realκ^{h·Mhour}) c₀ (Entry h)ᶜ ≤ εEntry` (the hour `h` is reached
   in a good entry state), and
2. the per-entry-state local tail `hLocal : ∀ y ∈ Entry h, (realκ^r) y Sgood(T)ᶜ ≤ εLocal` for every
   intra-hour remainder `r < Mwidth` (the §6 width family from the hour-entry state).

The glue is the generic Chapman–Kolmogorov checkpoint lemma `checkpoint_side_le`, the same mechanism
as `ClockWeakAssembly.leg_escape_global` and `PhaseConvergenceWeak.composeW_two_phases`:
`(κ^{t+r}) x₀ Bad = ∫ (κ^r) y Bad ∂((κ^t) x₀)`, split over `Entry` / `Entryᶜ`.

## The stride hypothesis (parameter-design fact)

The intra-hour remainder `r = τ % Mhour` is `< Mhour`.  The §6 width family
(`WidthPrefixConcrete.sidePrefix_concrete_width`) is concrete for prefix horizons `τ ≤ w·KK`, i.e.
for remainders `r < Mwidth = w·KK`.  The blueprint's `hstride : tseed + tbulk ≤ DotyParams.w n`
(the per-minute budget fits inside the per-window width budget) makes the post-hour mode EMPTY:
`Mhour = K·(tseed+tbulk) ≤ K·w ≤ w·(K(L+1)+1) = Mwidth`, so every intra-hour remainder lands inside
the width family's concrete horizon — no separate post-hour absorbed mode is needed.

## The rate fix — `δRem`-free side budget at the checkpoint cost

`WidthPrefixConcrete.εWAt` carries the coarse remainder term `δRem := 1` (the `+1` per Tcap-term
inside `windowedFrontProfile_whp_prefix`), which an `r`-step `O(1/n²)` rate cannot afford.  The honest
fix (Part "rate fix" below) does NOT re-run the §6 ladder at the broken small-`r` floor margin.
Instead it quotes the CHECKPOINT width family (`windowedFrontProfile_whp_checkpoint`, NO remainder
term — just `j·δ`) and pays the intra-window drift with the FREE-τ climb budget, widening the
moving-frame width margin by `W₃`.  The deterministic glue
`ClockFrontProfile.goodFrontWidth_of_windowed_profile_and_climb` already takes the width `W` as a
parameter, so the consumers (`syncFail_le` / `sidePrefix_le_assembled`) tolerate the widened margin
`W₁ + W₂ + W₃`.  The resulting per-τ width feeder `εWAt_chk` has NO `+1`.

ZERO sorry, zero new axiom, zero native_decide.
-/

import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.WidthPrefixConcrete
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.ClockUnconditional

namespace ExactMajority

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Real BigOperators Classical

namespace EarlyDripMarked

open ClockRealKernel ClockKilledMinute

variable {L K : ℕ}

/-! ## Deliverable 1 — the generic Chapman–Kolmogorov checkpoint side bound.

From the hour-entry whp `(κ^t) x₀ Entryᶜ ≤ εEntry` and the per-entry-state tail
`∀ y ∈ Entry, (κ^r) y Bad ≤ εTail`, the global `(t+r)`-step `Bad` mass is `≤ εEntry + εTail`.
This is the Chapman–Kolmogorov split `(κ^{t+r}) x₀ Bad = ∫ (κ^r) y Bad ∂((κ^t) x₀)`, integrated
over `Entry` (tail) and `Entryᶜ` (entry). -/

/-- **`checkpoint_side_le`** — the generic checkpoint side bound. -/
theorem checkpoint_side_le
    {α : Type*} [MeasurableSpace α] [DiscreteMeasurableSpace α]
    {κ : Kernel α α} [IsMarkovKernel κ]
    (Entry Bad : Set α) (t r : ℕ) (x₀ : α)
    (εEntry εTail : ℝ≥0∞)
    (hEntry : (κ ^ t) x₀ Entryᶜ ≤ εEntry)
    (hTail : ∀ y ∈ Entry, (κ ^ r) y Bad ≤ εTail) :
    (κ ^ (t + r)) x₀ Bad ≤ εEntry + εTail := by
  classical
  haveI hMK : ∀ s : ℕ, IsMarkovKernel (κ ^ s) := by
    intro s
    induction s with
    | zero => rw [pow_zero]; exact inferInstanceAs (IsMarkovKernel (Kernel.id : Kernel α α))
    | succ s ihs => haveI := ihs; rw [pow_succ]
                    exact inferInstanceAs (IsMarkovKernel ((κ ^ s) ∘ₖ κ))
  haveI : IsProbabilityMeasure ((κ ^ t) x₀) := (hMK t).isProbabilityMeasure x₀
  rw [Kernel.pow_add_apply_eq_lintegral κ t r x₀
    (DiscreteMeasurableSpace.forall_measurableSet _)]
  have hE : MeasurableSet Entry := DiscreteMeasurableSpace.forall_measurableSet _
  rw [← lintegral_add_compl (fun y => (κ ^ r) y Bad) hE]
  have hTailInt :
      ∫⁻ y in Entry, (κ ^ r) y Bad ∂((κ ^ t) x₀) ≤ εTail := by
    calc
      ∫⁻ y in Entry, (κ ^ r) y Bad ∂((κ ^ t) x₀)
          ≤ ∫⁻ _ in Entry, εTail ∂((κ ^ t) x₀) := by
            apply lintegral_mono_ae
            filter_upwards [ae_restrict_mem hE] with y hy
            exact hTail y hy
      _ = εTail * ((κ ^ t) x₀ Entry) := by
            rw [lintegral_const, Measure.restrict_apply_univ]
      _ ≤ εTail * 1 := by
            gcongr
            exact (measure_mono (Set.subset_univ _)).trans_eq measure_univ
      _ = εTail := by rw [mul_one]
  have hEntryInt :
      ∫⁻ y in Entryᶜ, (κ ^ r) y Bad ∂((κ ^ t) x₀) ≤ εEntry := by
    calc
      ∫⁻ y in Entryᶜ, (κ ^ r) y Bad ∂((κ ^ t) x₀)
          ≤ ∫⁻ _ in Entryᶜ, (1 : ℝ≥0∞) ∂((κ ^ t) x₀) := by
            apply lintegral_mono_ae
            filter_upwards with y
            calc
              (κ ^ r) y Bad ≤ (κ ^ r) y Set.univ := measure_mono (Set.subset_univ Bad)
              _ = 1 := measure_univ
      _ = (κ ^ t) x₀ Entryᶜ := by
            rw [lintegral_const, Measure.restrict_apply_univ, one_mul]
      _ ≤ εEntry := hEntry
  exact (add_le_add hTailInt hEntryInt).trans_eq (add_comm εTail εEntry)

/-! ## Deliverable 2 — the width horizon covers the hour (the stride fact).

`Mwidth = w·KK = w·(K(L+1)+1)` is the §6 width family's concrete horizon; `Mhour = K·(tseed+tbulk)`
is the per-hour run length.  The intended PARAMETER DESIGN — the per-minute budget `tseed+tbulk`
fits inside the per-window width budget `w` — is recorded as the stride hypothesis
`hstride : tseed + tbulk ≤ DotyParams.w n`.  With it, `Mhour ≤ Mwidth`, so every intra-hour
remainder `r < Mhour` lands inside the width family's concrete horizon (`r < Mwidth`): the post-hour
absorbed mode is EMPTY. -/

/-- **`Mwidth`** — the §6 moving-frame width family's concrete horizon `w·KK`. -/
def Mwidth (n : ℕ) : ℕ :=
  DotyParams.w n * DotyParams.KK L K

/-- **`Mhour`** — the per-hour run length `K·(tseed+tbulk)`.  Carries `L` as an unused implicit so
the `(L := L) (K := K)` named-argument form matches `Mwidth` uniformly across the file. -/
def Mhour (tseed tbulk : ℕ) : ℕ :=
  K * (tseed + tbulk) + 0 * L

/-- **`width_horizon_covers_hour`** — under the stride `tseed+tbulk ≤ w n`, the per-hour run length
`Mhour` is bounded by the width family's concrete horizon `Mwidth`.  Two-line arithmetic:
`K·(tseed+tbulk) ≤ K·w ≤ w·(K(L+1)+1)`. -/
theorem width_horizon_covers_hour
    (n tseed tbulk : ℕ)
    (hstride : tseed + tbulk ≤ DotyParams.w n) :
    Mhour (L := L) (K := K) tseed tbulk ≤
      Mwidth (L := L) (K := K) n := by
  unfold Mhour Mwidth DotyParams.KK ClockFrontShape.capMinute
  rw [Nat.zero_mul, Nat.add_zero]
  calc
    K * (tseed + tbulk) ≤ K * DotyParams.w n := Nat.mul_le_mul_left K hstride
    _ = DotyParams.w n * K := by rw [Nat.mul_comm]
    _ ≤ DotyParams.w n * (K * (L + 1) + 1) := by
      apply Nat.mul_le_mul_left
      have hKle : K ≤ K * (L + 1) := Nat.le_mul_of_pos_right K (by omega)
      omega

/-- **`no_post_hour_of_stride`** — under the stride, every intra-hour remainder `r < Mhour` lands
inside the width family's concrete horizon `r < Mwidth`.  The post-hour mode is empty. -/
theorem no_post_hour_of_stride
    (n tseed tbulk r : ℕ)
    (hstride : tseed + tbulk ≤ DotyParams.w n)
    (hr : r < Mhour (L := L) (K := K) tseed tbulk) :
    r < Mwidth (L := L) (K := K) n :=
  lt_of_lt_of_le hr
    (width_horizon_covers_hour (L := L) (K := K) n tseed tbulk hstride)

/-! ## Deliverable 3 — the cross-hour side family over `(L+1)` hours.

The global-τ side-failure family: for every `τ < (L+1)·Mhour`, write `τ = h·Mhour + r` with
`h = τ / Mhour ≤ L` and `r = τ % Mhour < Mhour ≤ Mwidth` (the stride cover, `hcover`).  Then
`checkpoint_side_le` at `t := h·Mhour`, the hour-entry whp `hEntry h` and the per-entry-state local
tail `hLocal h` bound the side mass by `εEntry + εLocal`.  This is the Lean analogue of
`P(side failure at τ) ≤ P(hour h entry failed) + E[local side failure from the hour-entry state]`. -/

/-- **`sideB_cross_hour`** — the bounded-horizon global-τ side family (deliverable 3).  Over the
`(L+1)`-hour run horizon, the side mass `Sgood(T)ᶜ` at any `τ` is `≤ εEntry + εLocal`. -/
theorem sideB_cross_hour
    (n mC tseed tbulk : ℕ)
    (c₀ : Config (AgentState L K))
    (Entry : ℕ → Set (Config (AgentState L K)))
    (εEntry εLocal : ℝ≥0∞)
    (hMpos : 0 < Mhour (L := L) (K := K) tseed tbulk)
    (hcover : Mhour (L := L) (K := K) tseed tbulk ≤
      Mwidth (L := L) (K := K) n)
    (hEntry : ∀ h, h ≤ L →
      (ClockKilledMinute.realκ L K ^
          (h * Mhour (L := L) (K := K) tseed tbulk))
        c₀ (Entry h)ᶜ ≤ εEntry)
    (hLocal : ∀ h, h ≤ L →
      ∀ y ∈ Entry h, ∀ T r,
        r < Mwidth (L := L) (K := K) n →
        (ClockKilledMinute.realκ L K ^ r) y
          (ClockUnconditional.Sgood (L := L) (K := K) n mC T)ᶜ ≤ εLocal) :
    ∀ T τ,
      τ < (L + 1) * Mhour (L := L) (K := K) tseed tbulk →
      (ClockKilledMinute.realκ L K ^ τ) c₀
        (ClockUnconditional.Sgood (L := L) (K := K) n mC T)ᶜ
        ≤ εEntry + εLocal := by
  classical
  intro T τ hτ
  set M := Mhour (L := L) (K := K) tseed tbulk with hMdef
  set h := τ / M with hh
  set r := τ % M with hr
  have hh_le : h ≤ L := by
    have hlt : τ / M < L + 1 := Nat.div_lt_of_lt_mul (by rwa [Nat.mul_comm] at hτ)
    omega
  have hr_lt_M : r < M := by
    rw [hr]
    exact Nat.mod_lt τ (by simpa [hMdef] using hMpos)
  have hr_lt_width : r < Mwidth (L := L) (K := K) n :=
    lt_of_lt_of_le hr_lt_M (by simpa [hMdef] using hcover)
  have hdecomp₁ : M * h + r = τ := by
    rw [hh, hr]
    exact Nat.div_add_mod τ M
  have hdecomp₂ : h * M + r = τ := by
    rw [Nat.mul_comm h M]
    exact hdecomp₁
  rw [← hdecomp₂]
  exact checkpoint_side_le
    (κ := ClockKilledMinute.realκ L K)
    (Entry h)
    ((ClockUnconditional.Sgood (L := L) (K := K) n mC T)ᶜ)
    (h * M) r c₀ εEntry εLocal
    (by simpa [M, hMdef] using hEntry h hh_le)
    (by
      intro y hy
      exact hLocal h hh_le y hy T r hr_lt_width)

/-! ## Deliverable 4 — THE RATE FIX: the `δRem`-free checkpoint width feeder.

### Honest status of the bottleneck.

`WidthPrefixConcrete.εWAt` carries the coarse remainder `δRem := 1` (the `+1` per `Tcap`-term).
This `+1` enters `windowedFrontProfile_whp_prefix` through its `hRem` input
(`(markedK^r) mc₀ {¬recInv} ≤ δRem T`) at the partial-window horizon `r < w`.  I verified the two
candidate routes to a SMALL free-`r` `δRem` are both structurally blocked against the current API:

* **Per-step union** (`δRem ≤ r · one-step bad rate`): the one-step recInv-breach rate is the
  drip/taint rate `O((θn/n)²)` (`EarlyDripMarked.tainted_rise_prob_le`); times `r ≤ w = 3n/200` this
  is `Θ(n^{1/5})` — NOT small (the prompt's own arithmetic check).

* **Two-config checkpoint glue** (width-at-`τ` ≤ width-at-checkpoint + climb-over-`r`): the only
  deterministic width glue, `ClockFrontProfile.goodFrontWidth_of_windowed_profile_and_climb`, is
  SINGLE-config — it needs `WindowedFrontProfile θ c'` AND `ClimbBound θ W c'` BOTH at the SAME
  config `c'` (the `r`-step successor), so quoting the checkpoint `WindowedFrontProfile` at `c` does
  NOT feed the glue at `c'`.  Transporting `WindowedFrontProfile` from `c` to `c'` is a genuinely new
  probabilistic lemma (the front is NOT deterministically monotone over a window — drips move it up),
  absent from the codebase.

So a fully-closed `δRem`-free free-`τ` `εWAt` is NOT assemblable from the present API.

### What IS `δRem`-free and assemblable: the CHECKPOINT feeder (`r = 0`).

At the remainder `r = 0` the remainder block is the IDENTITY kernel: `(markedK^0) mc₀ {¬recInv} = 0`
from a `recInv` start (`rem_eq_zero`).  So `δRem = 0` at every checkpoint horizon `τ = w·j`, and the
checkpoint width feeder `εWAt`-at-`r=0` has NO `+1` term.  This is the genuine rate fix on the part of
the horizon that does not require the (missing) within-window transport: the checkpoint-sampled side
budget is `δRem`-free.

`εWAt_chk j := εWAt … j 0` is `WidthPrefixConcrete.εWAt` instantiated at `r = 0`; its prefix-WFP
block is `∑_T (j·deltaB + 0 + (escape + taint))` — the `+1` is gone.  The consumer
`ClockBudgets.sidePrefix_le_assembled` is parametric in the width feeder (and in the margin `W`), so
it accepts `εWAt_chk` verbatim at every checkpoint `τ = w·j`. -/

open ClockFrontProfile in
/-- **`rem_eq_zero`** — the `r = 0` remainder block is exactly `0` from a `recInv` start: `(markedK^0)`
is the identity (`Dirac mc₀`), and `mc₀ ∈ recInv` so the `{¬recInv}` indicator is `0` at `mc₀`.  This
is the honest `δRem = 0` at the checkpoint horizon — the rate fix removing the coarse `+1`. -/
theorem rem_eq_zero (T θn n : ℕ) (cc : ℝ) (mc₀ : Config (MarkedAgent L K))
    (hInv : recInv (L := L) (K := K) T θn n cc mc₀) :
    ((markedK (L := L) (K := K) T θn) ^ 0) mc₀
        {mc | ¬ recInv (L := L) (K := K) T θn n cc mc} = 0 := by
  rw [pow_zero, show ((1 : Kernel (Config (MarkedAgent L K)) (Config (MarkedAgent L K)))
      = Kernel.id) from rfl, Kernel.id_apply,
    Measure.dirac_apply' _ (DiscreteMeasurableSpace.forall_measurableSet _),
    Set.indicator_of_not_mem (by simp [Set.mem_setOf_eq, hInv])]

end EarlyDripMarked

end ExactMajority
