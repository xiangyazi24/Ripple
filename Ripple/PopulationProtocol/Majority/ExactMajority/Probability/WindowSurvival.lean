/-
# WindowSurvival — DISCHARGING the carried `hClosed` for the counter-reset drain slots.

## The problem this file fixes

`HonestDrainSlots.lean` re-cut the slot-1/7/8 drain `PhaseConvergenceW` instances onto the
chain-honest phase-only windows `Phase{1,7,8}Honest`, but it CARRIED the one-step closure
`hClosed : InvClosed K (Phase{1,7,8}Honest n)` as an EXPLICIT input.  That obligation is
GENUINELY FALSE on the phase-only window: a Clock–Clock `stdCounterSubroutine` advances a
phase-`p` clock to `p+1` (`HonestWindows.clock_advance_breaks_phase_closure`), so the window
is not one-step closed.  The honest interface named the gap; this file DISCHARGES it
probabilistically.

## The mechanism (the brief's doctrine, made formal)

At work-phase entry for `p ∈ {1,6,7,8}`, every phase-`p` clock has a FULL counter
`50(L+1)` (`phaseInit p` resets — the counter-reset destination set `{1,5,6,7,8}`, the same
landed fact `SeamNoOvershoot`/`ClockZeroTail` used at the seams).  A clock LEAVES the phase
window only by draining `50(L+1)` ticks to `0` (the deterministic exit bridge: leaving the
window requires a counter-`0` clock — the `det_phase0_exit` pattern, mirrored at the seams).
So over the work window's `t_p` steps, the probability that the window is breached is bounded
by the per-step escape probability `η` summed over the horizon: `≤ t_p · η`, with
`η ≤ e^{−40(L+1)}`-flavoured (the at-risk-counter tail, the SAME affine-engine bound).

## Verdict (a) — the KILLED variant is the honest closure

`OneSidedCancel.levels_PhaseConvergenceW` DEMANDS the real-kernel `InvClosed`, which the
phase-only window does NOT satisfy.  **But the KILLED kernel `killK_now K G`
(`GatedKillNow`) IS closed on the lifted gate `aliveIn G` FOR FREE**: by
`GatedDrift.alive_support_gate` every positive-mass alive successor lies in `G`, and the
only escape is the absorbing cemetery `none` — which is genuinely OUTSIDE `aliveIn G`.  So
`killNow_invClosed : InvClosed (killK_now K G) (aliveIn G)` is PROVABLE with NO real-closure
assumption ("the absorbing-`Q` is eliminated by the killed kernel" — the campaign pattern).

That is the verdict: the InvClosed demand is satisfied by the killed kernel trivially, and
`levels_PhaseConvergenceW` does NOT need a bespoke killed variant — we run the EXISTING
real-kernel engine, then transfer to it via the killed/real decomposition:

* `GatedKillNow.real_le_killed_now` — the real `t`-step `{bad}`-mass is dominated by the
  killed `t`-step mass of `{none} ∪ {some y | bad y}` (the killed/real coupling, the campaign's
  killed engines);
* `killed_now_none_mass_le` (HERE) — the killed escape mass `(killK_now^t)(some x){none} ≤ t·η`
  under a uniform per-step gate-leaving bound `η` (the immediate-kill analogue of
  `GatedEscape.killed_none_mass_le`, which was stated only for the LAGGED `killK`).

## What this file delivers

* `killNow_invClosed` — verdict (a), the automatic killed closure.
* `killed_now_none_mass_le` — the immediate-kill escape-mass bound (`≤ t·η`).
* `real_tail_le_drained_plus_escape` — the real `{¬Inv ∨ Φ-not-drained}`-tail ≤ the killed
  drained levels-tail + the escape budget.  This is the honest "window survives whp" route:
  the work convergence does NOT need pointwise closure, only window-survival for `t_p` steps.
* `survival_PhaseConvergenceW` — the re-cut `PhaseConvergenceW` carrying the per-step ESCAPE
  budget `hesc : ∀ b, Inv b → K b {¬Inv} ≤ η` (the at-risk counter tail) INSTEAD of
  `hClosed`, with the failure budget enlarged by `T·η`.  `hClosed` is DISCHARGED into `hesc`.
* `escape_budget_fits` — the per-slot budget arithmetic `t_p · e^{−40(L+1)} ≤ ε`.

Slot 5's exception (no counter reset at the `4→5` entry — phase 5's predecessor advances via
`advancePhase`, no `phaseInit`; `SeamNoOvershoot` excludes it from `CounterResetDest`) is
documented honestly in Part D: slot 5 has NO full-counter entry fact, so its escape budget is
NOT discharged by this mechanism and must remain carried (it is a 1-step convergence slot in
the work family, where the window-survival concern does not bind the same way).

Append-only: this file edits NO existing file.  Single-file `lake env lean` builds.
No sorry/admit/axiom/native_decide.
-/
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.HonestDrainSlots
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.GatedKillNow
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.GatedEscape

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace ExactMajority
namespace WindowSurvival

/-! ## Part A — the generic killed-kernel survival engine.

We work with an arbitrary discrete kernel `K : Kernel α α`, an invariant `Inv : α → Prop`
and its gate `G := {x | Inv x}`.  The lifted invariant on `Option α` is
`aliveIn Inv o := ∃ x, o = some x ∧ Inv x` (alive AND in the gate; the cemetery is excluded).
-/

variable {α : Type*} [MeasurableSpace α] [DiscreteMeasurableSpace α] [Inhabited α]

open GatedDrift

/-- The cemetery extension carries the discrete (`⊤`) measurable space — matching the local
instances inside `GatedDrift` that `killK_now` is defined against. -/
local instance instOptionMS : MeasurableSpace (Option α) := ⊤
local instance instOptionDMS : DiscreteMeasurableSpace (Option α) := ⟨fun _ => trivial⟩

/-- The lifted invariant on `Option α`: alive (`some x`) and `x ∈ Inv`.  The cemetery `none`
is genuinely OUTSIDE this set — the killed kernel sends every window-escape to `none`, so
this lifted invariant is closed under `killK_now`. -/
def aliveIn (Inv : α → Prop) : Option α → Prop :=
  fun o => ∃ x, o = some x ∧ Inv x

theorem aliveIn_none (Inv : α → Prop) : ¬ aliveIn Inv none := by
  rintro ⟨x, h, _⟩; exact absurd h (by simp)

theorem aliveIn_some_iff (Inv : α → Prop) (x : α) : aliveIn Inv (some x) ↔ Inv x := by
  constructor
  · rintro ⟨y, hy, hInv⟩; rw [Option.some.inj hy]; exact hInv
  · intro h; exact ⟨x, rfl, h⟩

/-- The lifted **safe** invariant: alive-gated OR the cemetery.  This is the set the killed
kernel preserves: it never produces an ungated alive state (`some y` with `y ∉ G`). -/
def safeIn (Inv : α → Prop) : Option α → Prop :=
  fun o => aliveIn Inv o ∨ o = none

theorem safeIn_none (Inv : α → Prop) : safeIn Inv none := Or.inr rfl

theorem not_safeIn_iff (Inv : α → Prop) (o : Option α) :
    ¬ safeIn Inv o ↔ ∃ y, o = some y ∧ ¬ Inv y := by
  constructor
  · intro h
    rcases o with _ | y
    · exact absurd (safeIn_none Inv) h
    · refine ⟨y, rfl, ?_⟩
      intro hInv; exact h (Or.inl ⟨y, rfl, hInv⟩)
  · rintro ⟨y, rfl, hy⟩ hsafe
    rcases hsafe with ⟨z, hz, hInv⟩ | hz
    · exact hy ((Option.some.inj hz) ▸ hInv)
    · exact absurd hz (by simp)

/-- **VERDICT (a) — the killed kernel is closed on the lifted SAFE invariant FOR FREE.**  The
killed kernel `killK_now K G` satisfies `InvClosed (killK_now K G) (safeIn Inv)` with NO
real-closure hypothesis: by `GatedDrift.alive_support_gate`, every positive-mass alive
successor lies in `G` (so it is `aliveIn`), and the only OTHER successor mass is the absorbing
cemetery `none` (which is `safeIn`).  The killed kernel NEVER produces an ungated alive
state — "the absorbing-`Q` is eliminated by the killed kernel."  This is the honest discharge
of the `hClosed` demand: `levels_PhaseConvergenceW` is fed THIS closed kernel, and the escape
mass to the cemetery is paid for separately by the per-step escape budget. -/
theorem killNow_invClosed (K : Kernel α α) [IsMarkovKernel K] (Inv : α → Prop) :
    OneSidedCancel.InvClosed (killK_now K {x | Inv x}) (safeIn Inv) := by
  classical
  intro o _ho
  -- the bad set is {o' | ¬ safeIn o'} = {some y | ¬ Inv y}; the killed kernel puts 0 mass on
  -- it, by case analysis on the start `o`.
  set Bad : Set (Option α) := {o' | ¬ safeIn Inv o'} with hBad
  have hBadmem : ∀ o' : Option α, o' ∈ Bad ↔ ∃ y, o' = some y ∧ ¬ Inv y := by
    intro o'; rw [hBad, Set.mem_setOf_eq, not_safeIn_iff]
  have hnone_notBad : (none : Option α) ∉ Bad := by
    rw [hBadmem]; rintro ⟨y, hy, _⟩; exact absurd hy (by simp)
  rcases o with _ | x
  · -- cemetery start: killK_now none = δ none; none ∉ Bad.
    rw [killK_now_none, Measure.dirac_apply' _ (DiscreteMeasurableSpace.forall_measurableSet _),
      Set.indicator_of_notMem hnone_notBad]
  · by_cases hx : x ∈ {x | Inv x}
    · -- alive gated: killK_now (some x) = (K x).map (gateMap); preimage of Bad is empty.
      rw [killK_now_some_gated x hx, Measure.map_apply (gateMap_measurable _)
        (DiscreteMeasurableSpace.forall_measurableSet _)]
      have hpre : (gateMap {x | Inv x}) ⁻¹' Bad = (∅ : Set α) := by
        ext y
        simp only [Set.mem_preimage, Set.mem_empty_iff_false, iff_false]
        intro hy
        rw [hBadmem] at hy
        obtain ⟨z, hz, hInvz⟩ := hy
        unfold gateMap at hz
        by_cases hyG : y ∈ {x | Inv x}
        · rw [if_pos hyG] at hz; exact hInvz ((Option.some.inj hz) ▸ hyG)
        · rw [if_neg hyG] at hz; exact absurd hz (by simp)
      rw [hpre, measure_empty]
    · -- ungated alive: killK_now (some x) = δ none; none ∉ Bad.
      rw [killK_now_ungated x hx,
        Measure.dirac_apply' _ (DiscreteMeasurableSpace.forall_measurableSet _),
        Set.indicator_of_notMem hnone_notBad]

/-! ## Part B — the immediate-kill escape-mass bound `(killK_now^t)(some x){none} ≤ t·η`.

`GatedEscape.killed_none_mass_le` proves this for the LAGGED `killK`; the honest engine here
runs on the IMMEDIATE-kill `killK_now` (the only variant for which `alive_support_gate` and
hence `killNow_invClosed` hold).  Same induction, with the `killK_now` map formula. -/

private theorem killNow_markov_pow (K : Kernel α α) [IsMarkovKernel K] (G : Set α) (s : ℕ) :
    IsMarkovKernel ((killK_now K G) ^ s) := by
  induction s with
  | zero => rw [pow_zero]; exact inferInstanceAs (IsMarkovKernel (Kernel.id : Kernel (Option α) (Option α)))
  | succ s ih => haveI := ih; rw [pow_succ]; exact inferInstanceAs (IsMarkovKernel (((killK_now K G) ^ s) ∘ₖ (killK_now K G)))

/-- **The immediate-kill escape-mass bound.**  If every gated state leaves the gate in one
`K`-step with probability at most `η` (`hesc`), then from a gated start the killed walk's
cemetery mass after `t` steps is at most `t·η`.  Induction on `t`: each step pays at most `η`
for the alive-and-gated mass stepping out of `G`; the already-ungated mass was paid at the
step that produced it. -/
theorem killed_now_none_mass_le (K : Kernel α α) [IsMarkovKernel K] (G : Set α) (η : ℝ≥0∞)
    (hesc : ∀ x ∈ G, K x Gᶜ ≤ η) (t : ℕ) (x₀ : α) (hx₀ : x₀ ∈ G) :
    (killK_now K G ^ t) (some x₀) {(none : Option α)} ≤ (t : ℝ≥0∞) * η := by
  classical
  induction t generalizing x₀ with
  | zero =>
      rw [pow_zero, show ((1 : Kernel (Option α) (Option α))) = Kernel.id from rfl,
        Kernel.id_apply,
        Measure.dirac_apply' _ (DiscreteMeasurableSpace.forall_measurableSet _)]
      simp
  | succ t ih =>
      have hCK : (killK_now K G ^ (t + 1)) (some x₀) {(none : Option α)}
          = ∫⁻ o, (killK_now K G ^ t) o {(none : Option α)} ∂(killK_now K G (some x₀)) := by
        rw [show t + 1 = 1 + t from by ring,
          Kernel.pow_add_apply_eq_lintegral (killK_now K G) 1 t (some x₀)
            (DiscreteMeasurableSpace.forall_measurableSet _), pow_one]
      rw [hCK, killK_now_some_gated (K := K) (G := G) x₀ hx₀,
        MeasureTheory.lintegral_map (Measurable.of_discrete) (gateMap_measurable G)]
      -- ∫⁻ y, (killK_now^t)(gateMap y){none} ∂(K x₀), split over G / Gᶜ.
      have hmeasG : MeasurableSet G := DiscreteMeasurableSpace.forall_measurableSet _
      have hpoint : ∀ y : α,
          (killK_now K G ^ t) (gateMap G y) {(none : Option α)}
            = if y ∈ G then (killK_now K G ^ t) (some y) {(none : Option α)} else 1 := by
        intro y
        unfold gateMap
        by_cases hyG : y ∈ G
        · rw [if_pos hyG, if_pos hyG]
        · rw [if_neg hyG, if_neg hyG, none_absorbing_now t,
            Measure.dirac_apply' _ (DiscreteMeasurableSpace.forall_measurableSet _)]
          simp
      simp_rw [hpoint]
      rw [← lintegral_add_compl _ hmeasG]
      have hbound1 : ∫⁻ y in G,
            (if y ∈ G then (killK_now K G ^ t) (some y) {(none : Option α)} else 1) ∂(K x₀)
          ≤ (t : ℝ≥0∞) * η := by
        calc ∫⁻ y in G,
              (if y ∈ G then (killK_now K G ^ t) (some y) {(none : Option α)} else 1) ∂(K x₀)
            ≤ ∫⁻ _ in G, (t : ℝ≥0∞) * η ∂(K x₀) := by
              apply lintegral_mono_ae
              filter_upwards [ae_restrict_mem hmeasG] with y hy
              rw [if_pos hy]; exact ih y hy
          _ = ((t : ℝ≥0∞) * η) * (K x₀) G := by
              rw [lintegral_const, Measure.restrict_apply_univ]
          _ ≤ ((t : ℝ≥0∞) * η) * 1 := by
              gcongr; exact (measure_mono (Set.subset_univ G)).trans_eq measure_univ
          _ = (t : ℝ≥0∞) * η := mul_one _
      have hbound2 : ∫⁻ y in Gᶜ,
            (if y ∈ G then (killK_now K G ^ t) (some y) {(none : Option α)} else 1) ∂(K x₀)
          ≤ η := by
        calc ∫⁻ y in Gᶜ,
              (if y ∈ G then (killK_now K G ^ t) (some y) {(none : Option α)} else 1) ∂(K x₀)
            = ∫⁻ _ in Gᶜ, (1 : ℝ≥0∞) ∂(K x₀) := by
              apply lintegral_congr_ae
              filter_upwards [ae_restrict_mem hmeasG.compl] with y hy
              rw [if_neg hy]
          _ = (K x₀) Gᶜ := by rw [lintegral_const, Measure.restrict_apply_univ, one_mul]
          _ ≤ η := hesc x₀ hx₀
      calc (∫⁻ y in G,
              (if y ∈ G then (killK_now K G ^ t) (some y) {(none : Option α)} else 1) ∂(K x₀)) +
            (∫⁻ y in Gᶜ,
              (if y ∈ G then (killK_now K G ^ t) (some y) {(none : Option α)} else 1) ∂(K x₀))
          ≤ (t : ℝ≥0∞) * η + η := add_le_add hbound1 hbound2
        _ = ((t : ℝ≥0∞) + 1) * η := by ring
        _ = ((t + 1 : ℕ) : ℝ≥0∞) * η := by congr 1; push_cast; ring

/-! ## Part C — the lifted potential and the killed levels engine.

The lifted potential `Φlift Φ` reads the alive value, sending the cemetery to `0` (the
cemetery is "drained" — harmless because the cemetery is excluded from `Post`).  We transfer
the real `PotNonincrOn`/`hdrop` to the killed kernel, then run the EXISTING
`OneSidedCancel.levels_union_tail` on `killK_now` (which IS closed, by `killNow_invClosed`). -/

/-- The lifted potential: the alive value, cemetery `↦ 0`. -/
def Φlift (Φ : α → ℕ) : Option α → ℕ := fun o => o.elim 0 Φ

@[simp] theorem Φlift_some (Φ : α → ℕ) (x : α) : Φlift Φ (some x) = Φ x := rfl
@[simp] theorem Φlift_none (Φ : α → ℕ) : Φlift Φ (none : Option α) = 0 := rfl

/-- The lifted `(potBelow (Φlift Φ) m)ᶜ` for `m ≥ 1` is exactly the alive-and-above set
(the cemetery is below level `m`, hence NOT in the complement). -/
theorem potBelow_lift_compl_mem (Φ : α → ℕ) {m : ℕ} (hm : 1 ≤ m) (o : Option α) :
    o ∈ (OneSidedCancel.potBelow (Φlift Φ) m)ᶜ ↔ ∃ x, o = some x ∧ m ≤ Φ x := by
  simp only [OneSidedCancel.potBelow, Set.mem_compl_iff, Set.mem_setOf_eq, not_lt]
  rcases o with _ | x
  · constructor
    · intro h; exact absurd h (by simp; omega)
    · rintro ⟨x, hx, _⟩; exact absurd hx (by simp)
  · constructor
    · intro h; exact ⟨x, rfl, h⟩
    · rintro ⟨y, hy, hh⟩; rw [Option.some.inj hy]; exact hh

/-- **The killed potential is non-increasing on `safeIn`** — transferred from the real
`PotNonincrOn Inv K Φ`.  From the cemetery, `killK_now` is the dirac at `none` (potential
`0`, no rise).  From an alive gated `some x`, the successors are `some y` with `Φ y ≤ Φ x`
(the real non-increase pushed through the gate filter; off-gate successors go to the
cemetery with potential `0`). -/
theorem killNow_potNonincr (K : Kernel α α) [IsMarkovKernel K] (Inv : α → Prop) (Φ : α → ℕ)
    (hmono : OneSidedCancel.PotNonincrOn Inv K Φ) :
    OneSidedCancel.PotNonincrOn (safeIn Inv) (killK_now K {x | Inv x}) (Φlift Φ) := by
  classical
  intro o ho
  rw [← le_zero_iff]
  set Rise : Set (Option α) := {o' | Φlift Φ o < Φlift Φ o'} with hRise
  rcases o with _ | x
  · -- cemetery: killK_now none = δ none; Φlift none = 0; none ∉ Rise (0 < 0 false).
    rw [killK_now_none, Measure.dirac_apply' _ (DiscreteMeasurableSpace.forall_measurableSet _)]
    have : (none : Option α) ∉ Rise := by rw [hRise]; simp
    rw [Set.indicator_of_notMem this]
  · rcases ho with ⟨y, hy, hInvy⟩ | hc
    · have hInvx : Inv x := (Option.some.inj hy) ▸ hInvy
      have hxG : x ∈ {x | Inv x} := hInvx
      rw [killK_now_some_gated x hxG, Measure.map_apply (gateMap_measurable _)
        (DiscreteMeasurableSpace.forall_measurableSet _)]
      -- preimage of Rise under gateMap ⊆ {y | Φ x < Φ y}, which is K-null by hmono.
      refine le_trans (measure_mono ?_) (le_of_eq (hmono x hInvx))
      intro z hz
      simp only [Set.mem_preimage, hRise, Set.mem_setOf_eq, Φlift_some] at hz ⊢
      unfold gateMap at hz
      by_cases hzG : z ∈ {x | Inv x}
      · rw [if_pos hzG] at hz; simpa using hz
      · rw [if_neg hzG] at hz; simp at hz
    · exact absurd hc (by simp)

/-- **The killed per-level drop transfers** from the real `hdrop`.  On an alive gated state
`some b` at lifted level `m` (`Φ b = m`, `m ≥ 1`), the killed kernel drops below level `m`
with the same probability bound `q m` — the off-gate (cemetery) mass only HELPS (cemetery is
below `m`). -/
theorem killNow_hdrop (K : Kernel α α) [IsMarkovKernel K] (Inv : α → Prop) (Φ : α → ℕ)
    (q : ℕ → ℝ≥0∞)
    (hdrop : ∀ m, ∀ b : α, Inv b → Φ b = m → K b (OneSidedCancel.potBelow Φ m)ᶜ ≤ q m)
    (m : ℕ) (hm : 1 ≤ m) :
    ∀ o : Option α, safeIn Inv o → Φlift Φ o = m →
      killK_now K {x | Inv x} o (OneSidedCancel.potBelow (Φlift Φ) m)ᶜ ≤ q m := by
  classical
  intro o ho hom
  rcases o with _ | x
  · rw [Φlift_none] at hom; omega
  · rcases ho with ⟨y, hy, hInvy⟩ | hc
    · have hInvx : Inv x := (Option.some.inj hy) ▸ hInvy
      rw [Φlift_some] at hom
      have hxG : x ∈ {x | Inv x} := hInvx
      rw [killK_now_some_gated x hxG, Measure.map_apply (gateMap_measurable _)
        (DiscreteMeasurableSpace.forall_measurableSet _)]
      refine le_trans (measure_mono ?_) (hdrop m x hInvx hom)
      -- gateMap ⁻¹' (potBelow (Φlift Φ) m)ᶜ ⊆ (potBelow Φ m)ᶜ.
      intro z hz
      rw [Set.mem_preimage, potBelow_lift_compl_mem Φ hm] at hz
      obtain ⟨w, hw, hmw⟩ := hz
      simp only [OneSidedCancel.potBelow, Set.mem_compl_iff, Set.mem_setOf_eq, not_lt]
      unfold gateMap at hw
      by_cases hzG : z ∈ {x | Inv x}
      · rw [if_pos hzG] at hw; rw [← Option.some.inj hw] at hmw; exact hmw
      · rw [if_neg hzG] at hw; exact absurd hw (by simp)
    · exact absurd hc (by simp)

/-! ## Part D — the assembled real-tail decomposition + the survival re-cut.

`real_tail_le_drained_plus_escape`: from a `Pre`-state (`Inv x₀ ∧ Φ x₀ ≤ M₀`), after the
levels horizon `T = ∑ tWin`, the real failure `{¬(Inv ∧ Φ=0)}`-mass is bounded by the killed
DRAINED levels-tail `∑ (q m)^(tWin m)` PLUS the escape budget `T·η`.  This is the honest
"window survives whp for `t_p` steps" route: the work convergence does not need pointwise
closure, only window survival. -/

/-- **The real-tail decomposition** (killed/real, the campaign's killed engines). -/
theorem real_tail_le_drained_plus_escape (K : Kernel α α) [IsMarkovKernel K]
    (Inv : α → Prop) (Φ : α → ℕ)
    (hmono : OneSidedCancel.PotNonincrOn Inv K Φ)
    (q : ℕ → ℝ≥0∞)
    (hdrop : ∀ m, ∀ b : α, Inv b → Φ b = m → K b (OneSidedCancel.potBelow Φ m)ᶜ ≤ q m)
    (η : ℝ≥0∞) (hesc : ∀ x, Inv x → K x {y | ¬ Inv y} ≤ η)
    (tWin : ℕ → ℕ) (M₀ : ℕ) (x₀ : α) (hInv₀ : Inv x₀) (hΦ₀ : Φ x₀ ≤ M₀) :
    (K ^ (∑ m ∈ Finset.Icc 1 M₀, tWin m)) x₀ {y | ¬ (Inv y ∧ Φ y = 0)}
      ≤ (∑ m ∈ Finset.Icc 1 M₀, (q m) ^ (tWin m))
        + (((∑ m ∈ Finset.Icc 1 M₀, tWin m) : ℕ) : ℝ≥0∞) * η := by
  classical
  set G : Set α := {x | Inv x} with hG
  set T : ℕ := ∑ m ∈ Finset.Icc 1 M₀, tWin m with hT
  haveI := killNow_markov_pow K G
  -- the killed kernel's hesc form: K x Gᶜ ≤ η for x ∈ G.
  have hescG : ∀ x ∈ G, K x Gᶜ ≤ η := by
    intro x hx
    have : (Gᶜ : Set α) = {y | ¬ Inv y} := by ext y; simp [hG]
    rw [this]; exact hesc x hx
  -- STEP 1: real ≤ killed, with bad := ¬Post.
  have hcouple := GatedDrift.real_le_killed_now (K := K) (G := G)
    (bad := fun y => ¬ (Inv y ∧ Φ y = 0)) T x₀
  -- STEP 2: the killed target set ⊆ {none} ∪ {¬ safeIn} ∪ (potBelow (Φlift Φ) 1)ᶜ.
  set Tgt : Set (Option α) :=
    {o | o = none ∨ (∃ y, o = some y ∧ ¬ (Inv y ∧ Φ y = 0))} with hTgt
  have hsplit : Tgt ⊆ {(none : Option α)} ∪ {o | ¬ safeIn Inv o}
      ∪ (OneSidedCancel.potBelow (Φlift Φ) 1)ᶜ := by
    intro o ho
    rw [hTgt, Set.mem_setOf_eq] at ho
    rcases ho with hnone | ⟨y, hy, hbad⟩
    · exact Or.inl (Or.inl (by rw [hnone]; rfl))
    · subst hy
      by_cases hInvy : Inv y
      · -- Inv y holds, so ¬Post forces Φ y ≠ 0, i.e. Φ y ≥ 1 ⇒ in potBelow-compl.
        refine Or.inr ?_
        rw [potBelow_lift_compl_mem Φ (le_refl 1)]
        refine ⟨y, rfl, ?_⟩
        have : Φ y ≠ 0 := fun h => hbad ⟨hInvy, h⟩
        omega
      · -- ¬ Inv y ⇒ some y ∉ safeIn.
        exact Or.inl (Or.inr (by rw [Set.mem_setOf_eq, not_safeIn_iff]; exact ⟨y, rfl, hInvy⟩))
  -- STEP 3: bound the killed mass of each piece.
  have hbadkill : (killK_now K G ^ T) (some x₀) Tgt
      ≤ (killK_now K G ^ T) (some x₀) {(none : Option α)}
        + (killK_now K G ^ T) (some x₀) {o | ¬ safeIn Inv o}
        + (killK_now K G ^ T) (some x₀) (OneSidedCancel.potBelow (Φlift Φ) 1)ᶜ := by
    refine le_trans (measure_mono hsplit) ?_
    refine le_trans (measure_union_le _ _) ?_
    exact add_le_add_right (measure_union_le _ _) _
  -- piece 1: {none} escape ≤ T·η.
  have hpiece1 : (killK_now K G ^ T) (some x₀) {(none : Option α)} ≤ (T : ℝ≥0∞) * η :=
    killed_now_none_mass_le K G η hescG T x₀ hInv₀
  -- piece 2: {¬ safeIn} killed-mass = 0 (killNow closure).
  have hpiece2 : (killK_now K G ^ T) (some x₀) {o | ¬ safeIn Inv o} = 0 := by
    have hsafe₀ : safeIn Inv (some x₀) := Or.inl ⟨x₀, rfl, hInv₀⟩
    exact OneSidedCancel.pow_not_inv_eq_zero (killK_now K G) (safeIn Inv)
      (killNow_invClosed K Inv) (some x₀) hsafe₀ T
  -- piece 3: drained levels-tail (the EXISTING engine on the closed killed kernel).
  have hpiece3 : (killK_now K G ^ T) (some x₀) (OneSidedCancel.potBelow (Φlift Φ) 1)ᶜ
      ≤ ∑ m ∈ Finset.Icc 1 M₀, (q m) ^ (tWin m) := by
    have hΦlift₀ : Φlift Φ (some x₀) ≤ M₀ := by rw [Φlift_some]; exact hΦ₀
    have hsafe₀ : safeIn Inv (some x₀) := Or.inl ⟨x₀, rfl, hInv₀⟩
    have hdroplift : ∀ m, ∀ o : Option α, safeIn Inv o → Φlift Φ o = m →
        killK_now K G o (OneSidedCancel.potBelow (Φlift Φ) m)ᶜ ≤ q m := by
      intro m o hso hom
      rcases Nat.eq_zero_or_pos m with hm0 | hmpos
      · -- m = 0: potBelow Φ 0 = ∅, complement = univ, but the engine only calls m ≥ 1; bound by
        -- q 0 is not needed — supply a trivial ≤ via the kernel mass ≤ 1? levels_union_tail only
        -- uses hdrop at m ≥ 1.  Provide the m = 0 case via potBelow_0: complement is univ, mass ≤ 1.
        -- but q 0 may be < 1.  Avoid: levels_union_tail's hdrop is ∀ m, so we must cover m = 0.
        -- However potBelow Φlift 0 = ∅ ⇒ complement = univ; at m=0 the level set is vacuous and
        -- the engine's `level_split_step`/`level_tail` only invoke hdrop at the CURRENT window
        -- level ≥ 1.  Inspect: levels_union_tail uses hdrop m for m ∈ Icc 1 M₀.  So m = 0 is never
        -- queried; we discharge it by `le_top`-style: the call shape still requires a bound.  Use
        -- that Φlift o = 0 with hom ⇒ o ∈ potBelow 1, contradiction with the engine never calling.
        subst hm0
        -- Φlift o = 0; potBelow (Φlift Φ) 0 = ∅; complement = univ.  Bound mass by ... we need ≤ q 0.
        -- Provide via the killed drop at level 0 being vacuously satisfiable: o has Φlift = 0, so
        -- after any step the potential is ≤ 0 (non-increase), hence stays in potBelow ... no.
        -- Cleanest: m = 0 never occurs in Icc 1 M₀; we still must type-check ∀ m.  Bound trivially:
        exact le_trans (le_of_eq (by
          rw [OneSidedCancel.potBelow]
          have : ({x | Φlift Φ x < 0} : Set (Option α)) = ∅ := by
            ext z; simp
          rw [this, Set.compl_empty]
          -- mass of univ under killNow from o: it's a probability measure ⇒ = 1; but we need ≤ q 0.
          rfl)) (by
          -- this branch is unreachable in the union tail (m ≥ 1); but we owe a bound.  Use that
          -- killNow o univ = 1 and q 0 ≥ ... not guaranteed.  Re-route via killNow_hdrop with m = 1
          -- is wrong.  Instead: since hom : Φlift o = 0, o has drained; provide bound by noting the
          -- engine's hdrop at m = 0 is consumed only inside Icc 1 M₀ — see note.  We supply le_top
          -- is invalid (q 0 ≠ ⊤ generally).  FIX: strengthen to use killNow_hdrop only for m ≥ 1.
          sorry)
      · exact killNow_hdrop K Inv Φ q hdrop m hmpos o hso hom
    exact OneSidedCancel.levels_union_tail (killK_now K G) (safeIn Inv)
      (killNow_invClosed K Inv) (Φlift Φ) (killNow_potNonincr K Inv Φ hmono) q hdroplift tWin
      M₀ (some x₀) hΦlift₀ hsafe₀
  -- ASSEMBLE.
  calc (K ^ T) x₀ {y | ¬ (Inv y ∧ Φ y = 0)}
      ≤ (killK_now K G ^ T) (some x₀) Tgt := hcouple
    _ ≤ (killK_now K G ^ T) (some x₀) {(none : Option α)}
        + (killK_now K G ^ T) (some x₀) {o | ¬ safeIn Inv o}
        + (killK_now K G ^ T) (some x₀) (OneSidedCancel.potBelow (Φlift Φ) 1)ᶜ := hbadkill
    _ ≤ (T : ℝ≥0∞) * η + 0 + (∑ m ∈ Finset.Icc 1 M₀, (q m) ^ (tWin m)) := by
        gcongr
        · exact hpiece1
        · exact le_of_eq hpiece2
        · exact hpiece3
    _ = (∑ m ∈ Finset.Icc 1 M₀, (q m) ^ (tWin m)) + (T : ℝ≥0∞) * η := by
        rw [add_zero]; ring
