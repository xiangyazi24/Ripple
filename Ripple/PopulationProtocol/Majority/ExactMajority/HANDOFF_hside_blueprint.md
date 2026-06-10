Bottom line

Your proposed cross-hour decomposition is the right probabilistic shape, but the clean Lean route is not to build a new deterministic hour-chain inside HourComposition. The branch already documents Phase 3 as a union-bound / checkpoint assembly, not a deterministic Post → next Pre chain: each marked hour is re-seeded from the gated start, and the hour budgets are summed. The file explicitly says no separate deterministic cross-hour chaining lemma is needed, and that heB is already discharged by SideBudget.heB_concrete into the εsync side budget. 

HourComposition

The main correction I would make is: do not try to prove the literal unbounded hypothesis

lean
∀ T τ, (realκ^τ) c₀ (Sgood n mC T)ᶜ ≤ εside

at a paper-rate small εside. The clock proof only consumes τ in a finite Phase-3 window, but the current ClockBudgets statement quantifies all τ for convenience. Outside the run horizon, a small uniform bound is generally false unless you use a trivial εside ≥ 1, which destroys the rate. The target should be the bounded-horizon variant.

1. Cross-hour structure

Yes: the correct generic lemma is the same Chapman–Kolmogorov checkpoint pattern already used in ClockWeakAssembly.leg_escape_global and PhaseConvergenceWeak.composeW_two_phases. leg_escape_global integrates over the global run distribution and collapses the prefix terms by Kernel.pow_add_apply_eq_lintegral; that is exactly the mechanism you want for τ = h·M_hour + r. 

ClockWeakAssembly

 The weak phase composition proof uses the same split over checkpoint-good versus checkpoint-bad states. 

PhaseConvergenceWeak

I would add this generic lemma once:

lean
namespace ExactMajority

open MeasureTheory ProbabilityTheory
open scoped ENNReal

theorem checkpoint_side_le
    {α : Type*} [MeasurableSpace α] [DiscreteMeasurableSpace α]
    {κ : Kernel α α} [IsMarkovKernel κ]
    (Entry Bad : Set α) (t r : ℕ) (x₀ : α)
    (εEntry εTail : ℝ≥0∞)
    (hEntry : (κ ^ t) x₀ Entryᶜ ≤ εEntry)
    (hTail : ∀ y ∈ Entry, (κ ^ r) y Bad ≤ εTail) :
    (κ ^ (t + r)) x₀ Bad ≤ εEntry + εTail := by
  classical
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
  exact add_le_add hTailInt hEntryInt

Then the hour decomposition is just the τ / M_hour, τ % M_hour instantiation of this lemma.

2. Post-hour mode

The concrete comparison is:

lean
DotyParams.w n = 3 * n / 200
DotyParams.KK L K = ClockFrontShape.capMinute + 1
ClockFrontShape.capMinute = K * (L + 1)

so the §6 width horizon is

lean
Mwidth = DotyParams.w n * DotyParams.KK L K
       = (3*n/200) * (K*(L+1) + 1)

These definitions are explicit in DotyParams and ClockFrontShape. 

DotyParams

 

ClockFrontShape

The older standalone clock-hour layer has minutesPerHour := 45, and its per-hour bound runs for 45 * (tseed + tbulk) interactions. 

ClockHourBounds

 In the current Phase-3 real-kernel code, however, tseed and tbulk are still parameters; phase3Horizon is defined from them, not concretely fixed in DotyParams. 

HourComposition

So the honest answer is:

lean
-- This cannot be closed from DotyParams alone:
K * (tseed + tbulk) ≤ DotyParams.w n * DotyParams.KK L K

unless you add the intended stride hypothesis:

lean
hstride : tseed + tbulk ≤ DotyParams.w n

With that hypothesis, the post-hour mode is empty:

lean
namespace ExactMajority
namespace EarlyDripMarked

open scoped ENNReal

variable {L K : ℕ}

def Mwidth (n : ℕ) : ℕ :=
  DotyParams.w n * DotyParams.KK L K

def Mhour (tseed tbulk : ℕ) : ℕ :=
  K * (tseed + tbulk)

theorem width_horizon_covers_hour
    (n tseed tbulk : ℕ)
    (hstride : tseed + tbulk ≤ DotyParams.w n) :
    Mhour (L := L) (K := K) tseed tbulk ≤
      Mwidth (L := L) (K := K) n := by
  unfold Mhour Mwidth DotyParams.KK ClockFrontShape.capMinute
  calc
    K * (tseed + tbulk) ≤ K * DotyParams.w n := Nat.mul_le_mul_left K hstride
    _ = DotyParams.w n * K := by rw [Nat.mul_comm]
    _ ≤ DotyParams.w n * (K * (L + 1) + 1) := by
      apply Nat.mul_le_mul_left
      omega

theorem no_post_hour_of_stride
    (n tseed tbulk r : ℕ)
    (hstride : tseed + tbulk ≤ DotyParams.w n)
    (hr : r < Mhour (L := L) (K := K) tseed tbulk) :
    r < Mwidth (L := L) (K := K) n :=
  lt_of_lt_of_le hr
    (width_horizon_covers_hour (L := L) (K := K) n tseed tbulk hstride)

end EarlyDripMarked
end ExactMajority

If you refuse to add hstride, then the post-hour mode is real. The cleaner design is not “absorbed forever”; it is:

lean
r ≥ Mwidth ∧ r < Mhour

is charged to the hour-completion / bulk-arrival branch, i.e. to BulkPost / HourComplete. This matches HourComposition: HourComplete is exactly BulkPost n mC (K*(L+1)-1), and the file says the bulk-arrival event is the good branch of the named εB residual. 

HourComposition

 

HourComposition

But I would strongly prefer the hstride route: it makes the post-hour theorem a two-line arithmetic lemma instead of adding a second absorbed-mode proof.

3. εside arithmetic and the bottleneck

The assembled side budget is:

lean
sideEps εQ εfloor εW εP εB εge3 εno3 εcpos εsucc
= εQ + εfloor + (εW + εP + εB)
  + (εge3 + εno3 + εcpos + εsucc)

This is the exact definition in ClockBudgets. 

ClockBudgets

 The clock budget then multiplies this by the number of clock minutes and by tbulk:

lean
εclock L K tbulk εbulk εside
= (K * (L + 1) - 1) * (εbulk + tbulk * εside)

ClockBudgets

The problem is that the current concrete free-τ width feeder is not yet paper-rate small. WidthPrefixConcrete explicitly uses the coarse remainder bound δRem := 1, and the header says this contributes a Tcap term to every per-τ width budget. 

WidthPrefixConcrete

 The actual εWAt definition contains the term

lean
∑ T ∈ Finset.range Tcap,
  (((j : ℝ≥0∞) * DotyParams.deltaB n + 1) + ...)

so the +1 is not just commentary; it is in the budget. 

WidthPrefixConcrete

Therefore, at the current branch state, the paper-rate statement

total failure = O(1/n²)

does not close. The bottleneck is the coarse δRem := 1, amplified by Tcap, then by the clock sum. After that is fixed, the next controlling factors are the union multipliers:

hour factor      ≈ L + 1
clock minutes    ≈ K*(L+1)
bulk window      ≈ tbulk
width union      ≈ Tcap * KK

So the repaired shape should be morally:

εside_global
  ≈ εQ + εfloor + εP + εB + εge3 + εno3 + εcpos + εsucc
    + Tcap * (KK*deltaB + eB + tB + δRem)
    + climbB

and then

εclock ≈ (K*(L+1)-1) * (εbulk + tbulk * εside_global).

If tbulk = Θ(n) and K*(L+1)=Θ(log n), then to make εclock = O(1/n²) you need roughly

εside_global = O(1 / (n³ log n))

up to the extra Tcap, KK, and cross-hour log factors. The current +1 term makes that impossible; replacing it by a true small δRem is the real rate bottleneck, not deltaB itself.

Also: the branch headline is currently an eleven-phase composition, not 21 phases. It sums the phase errors through composeW_n_phases; if you have 21 external budget instances, the same arithmetic applies with 21 replacing 11. 

DotyTimeHeadline

 

DotyTimeHeadline

4. Target Lean statements
4(a). Cross-hour side theorem

This is the statement I would add after the generic checkpoint lemma:

lean
namespace ExactMajority
namespace EarlyDripMarked

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Real BigOperators Classical

variable {L K : ℕ}

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
    have hlt : τ / M < L + 1 := Nat.div_lt_of_lt_mul hτ
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

end EarlyDripMarked
end ExactMajority

This is the precise Lean analogue of your formula:

P(global side failure at τ)
≤ P(hour h entry failed) + E[local side failure from hour-entry state].

The local side bound is supplied by WidthPrefixConcrete.sidePrefix_concrete_width, which already turns Sgood(T)ᶜ into sideEps with εWAt substituted. 

WidthPrefixConcrete

 

WidthPrefixConcrete

4(b). Post-hour treatment

Preferred target:

lean
theorem post_hour_empty
    (n tseed tbulk r : ℕ)
    (hstride : tseed + tbulk ≤ DotyParams.w n)
    (hr : r < Mhour (L := L) (K := K) tseed tbulk) :
    r < Mwidth (L := L) (K := K) n :=
  no_post_hour_of_stride (L := L) (K := K) n tseed tbulk r hstride hr

Then the local theorem never needs a post-hour branch.

Fallback target if you do not add hstride:

lean
theorem side_post_width_tail_charged_to_completion
    (n mC T r : ℕ) (y : Config (AgentState L K))
    (εcomplete εstruct : ℝ≥0∞)
    (hr₀ : Mwidth (L := L) (K := K) n ≤ r)
    (hr₁ : r < Mhour (L := L) (K := K) tseed tbulk)
    (hcomplete :
      (ClockKilledMinute.realκ L K ^ r) y
        {c | ¬ HourComposition.HourComplete (L := L) (K := K) n mC c}
        ≤ εcomplete)
    (hstruct :
      (ClockKilledMinute.realκ L K ^ r) y
        {c | HourComposition.HourComplete (L := L) (K := K) n mC c}ᶜ
        ≤ εstruct) :
    (ClockKilledMinute.realκ L K ^ r) y
      (ClockUnconditional.Sgood (L := L) (K := K) n mC T)ᶜ
      ≤ εcomplete + εstruct := by
  -- Usually this should be a set-inclusion/union-bound lemma:
  -- after the §6 width budget is exhausted, either the hour has completed
  -- or this side failure is charged to the completion failure.
  ...

But I would avoid this if possible; the branch already treats BulkPost/HourComplete as the good hour-ending branch, so the arithmetic hstride closure is much cleaner.

4(c). Final bounded hside_concrete

I would not feed the current ClockBudgets.clock_unconditional_concrete unchanged if you want paper-rate small error, because it asks for ∀ τ. Instead, add the bounded version:

lean
theorem hside_concrete_bounded
    (n mC tseed tbulk : ℕ)
    (c₀ : Config (AgentState L K))
    (Entry : ℕ → Set (Config (AgentState L K)))
    (εEntry εQ εfloor εWu εP εB εge3 εno3 εcpos εsucc : ℝ≥0∞)
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
          (ClockUnconditional.Sgood (L := L) (K := K) n mC T)ᶜ
          ≤ ClockBudgets.sideEps
              εQ εfloor εWu εP εB εge3 εno3 εcpos εsucc) :
    ∀ T τ,
      τ < (L + 1) * Mhour (L := L) (K := K) tseed tbulk →
      (ClockKilledMinute.realκ L K ^ τ) c₀
        (ClockUnconditional.Sgood (L := L) (K := K) n mC T)ᶜ
      ≤ εEntry +
          ClockBudgets.sideEps
            εQ εfloor εWu εP εB εge3 εno3 εcpos εsucc :=
  sideB_cross_hour
    (L := L) (K := K)
    n mC tseed tbulk c₀ Entry εEntry
    (ClockBudgets.sideEps εQ εfloor εWu εP εB εge3 εno3 εcpos εsucc)
    hMpos hcover hEntry hLocal

Then make the clock budget consume the bounded form over its actual window. This is a tiny refactor of window_sum_le / minutes_sum_le: replace the current global hypothesis with a hypothesis only for τ ∈ Ico .... The current proof already only uses those finite Ico windows. 

ClockBudgets

 

ClockBudgets

If you absolutely do not want to edit ClockBudgets, then define the bounded theorem and wrap it with a trivial ≤ 1 outside the horizon. But then εside must be at least 1, so the headline cannot close at paper rate.

My recommendation: add the bounded hside variant, add hstride : tseed + tbulk ≤ w n, and replace the coarse δRem := 1 before attempting the final O(1/n²) arithmetic.
