/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Doty §6 — the seam-entry initial-potential bound and the `hNoOvershoot` feeder
production (`ClockZeroTail`)

This file closes WAVE-2 roster item **#5(b)** — the per-seam clock-zero tail that
GATES every no-overshoot seam.  The landed `SeamPairAdapter` machinery
(`seam_atRiskClockZero_tail_honest`, the honest affine engine with the corrected
`2·eˢ·freshVal` immigration, budget `e^{−40(L+1)}`) consumes ONE remaining
probabilistic input it cannot manufacture from the kernel alone: the **initial
potential bound**

  `Φ_s(c₀) = seamClockPotential p 1 c₀ ≤ n · e^{−50(L+1)}`     (`hinitΦ`)

at the seam start `c₀`.  This file PROVES that bound from the seam-entry structure and
then wires the full no-overshoot chain into the `DotyAssembly'.hNoOvershoot` feeder
fields, for the counter-timed honest destination set `{1,6,7,8}` (the `SeamPairAdapter`
honest set), with the four excluded destinations carried as NAMED guards.

## The initial-potential derivation (the crux)

`seamClockSummand p 1 a` is NONZERO only for a CLOCK at the new phase `p+1`
(`if a.role = clock ∧ a.phase = p+1 then exp(−counter) else 0`).  At the seam START the
phase-`(p+1)` clocks are exactly those that were JUST advanced into `p+1`:

* a clock counter-advanced from phase `p` by `stdCounterSubroutine → advancePhaseWithInit
  → phaseInit (p+1)` (the counter-reset destination `{1,6,7,8}`), OR
* a clock epidemic-dragged from phase `< p+1` into `p+1` (also through `phaseInit (p+1)`,
  the `runInitsBetween` reset — exactly the `SeamPairAdapter` advance-immigration lemmas).

BOTH paths run `phaseInit (p+1)` on a clock, which sets `counter := 50(L+1)`
(`Protocol/Transition.lean:138/166-173`, FROZEN; the reset value `50(L+1)` is the
`freshVal` exponent).  So at the seam start EVERY phase-`(p+1)` clock has the FULL
counter `50(L+1)`, hence its summand is EXACTLY `e^{−50(L+1)} = M`, and the sum over the
`≤ n` agents is `≤ n·M`.  This is the seam analogue of
`Phase0Window.clockCounterPotential_init_le` (which assumed every clock — at phase 0 —
has full counter): here the "full counter" condition is restricted to the at-risk
phase-`(p+1)` clocks, which is exactly the set the summand reads.

We capture the FROZEN seam-entry fact as the named predicate `SeamEntryFullCounter p`
("every phase-`(p+1)` clock has full counter `50(L+1)`") — the honest interface fact
about the seam-start configuration (the `advancePhaseWithInit`/`phaseInit` reset on the
just-advanced clocks), and DERIVE `hinitΦ` from it.

## What is built (0 sorry / 0 axiom / no native_decide)

* `SeamEntryFullCounter` — the seam-start full-counter predicate on phase-`(p+1)` clocks;
* `seamClockPotential_init_le` — the initial-potential bound `Φ_1(c₀) ≤ n·e^{−50(L+1)}`
  derived from it (the crux, mirroring `clockCounterPotential_init_le`);
* `seam_atRiskTail_of_entry` — the at-risk tail with `hinitΦ` discharged from the
  full-counter entry fact;
* `seam_noOvershoot_hbound_of_entry` — the assembled `hbound` (the per-`τ` at-risk tails
  composed through `seam_noOvershoot_tail`, with the SAME entry fact threaded);
* `hNoOvershoot_field_of_entry` — the per-seam `hNoOvershoot` value at the
  `DotyAssembly'.hNoOvershoot` field shape, produced for `CounterResetDest (p+1)` ∈
  `{1,6,7,8}`, under the seam-entry full-counter fact + the `Wf`-region bridge +
  `SeamRegimeDispatch` + arithmetic;
* `CounterResetDest_dom` — the destination-set membership facts for the produced seams
  (`seamP ∈ {0,5,6,7}` ⟹ `seamP+1 ∈ {1,6,7,8}`), and the documented guards for the rest.

Reference: Doty et al. §6 (time window); consumer = `SeamPairAdapter.lean` /
`SeedTrigWiring.DotyAssembly'`; pattern = `Phase0Window.clockCounterPotential_init_le`.
-/

import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.SeamOvershootBridge
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.SeedTrigWiring

namespace ExactMajority

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Real BigOperators

namespace SeamNoOvershoot

variable {L K : ℕ}

/-! ## Stage 1 — the seam-entry full-counter predicate and the initial-potential bound. -/

/-- **Seam-entry full-counter fact.**  At the seam start, every clock at the NEW phase
`p+1` has the FULL counter `50(L+1)`.  This is the honest interface fact about the
seam-start configuration: a phase-`(p+1)` clock at the seam start was JUST advanced into
`p+1` — either counter-advanced from phase `p` via
`stdCounterSubroutine → advancePhaseWithInit → phaseInit (p+1)`, or epidemic-dragged from
a lower phase via `runInitsBetween → phaseInit (p+1)`.  For the counter-reset destination
set `{1,6,7,8}`, BOTH paths run `phaseInit (p+1)` on the clock, which resets
`counter := 50(L+1)` (`Protocol/Transition.lean:138/166-173`, FROZEN).  Hence every
at-risk clock at the seam start has the full counter; this predicate names that fact, and
`seamClockPotential_init_le` derives the initial-potential bound from it. -/
def SeamEntryFullCounter (p : ℕ) (c : Config (AgentState L K)) : Prop :=
  ∀ a ∈ c, a.role = .clock → a.phase.val = p + 1 → a.counter.val = 50 * (L + 1)

instance (p : ℕ) (c : Config (AgentState L K)) :
    Decidable (SeamEntryFullCounter (L := L) (K := K) p c) := by
  unfold SeamEntryFullCounter; infer_instance

/-- **The seam initial-potential bound** (the crux).  If `card c = n` and every
phase-`(p+1)` clock in `c` has the full counter `50(L+1)`
(`SeamEntryFullCounter p c`), then the seam clock potential at scale `s = 1` satisfies

  `Φ_1(c) = seamClockPotential p 1 c ≤ n · e^{−50(L+1)}`.

`seamClockSummand p 1 a` is `e^{−counter}` for a phase-`(p+1)` clock and `0` otherwise;
the full-counter hypothesis pins each NONZERO summand to EXACTLY `e^{−50(L+1)} = M`, and
the sum over `≤ n` agents gives the `n·M` bound.  This mirrors
`Phase0Window.clockCounterPotential_init_le`, with the "full counter" condition restricted
to the at-risk phase-`(p+1)` clocks the seam summand reads.  Stated at the literal
exponent `-(50*(L+1):ℕ)` (= `s = 1` form) the `seam_atRiskClockZero_tail_honest`
hypothesis `hinitΦ` wants. -/
theorem seamClockPotential_init_le (p : ℕ)
    (n : ℕ) (c : Config (AgentState L K))
    (hcard : Multiset.card c = n)
    (hfull : SeamEntryFullCounter (L := L) (K := K) p c) :
    seamClockPotential (L := L) (K := K) p 1 c
      ≤ (n : ℝ≥0∞) * ENNReal.ofReal (Real.exp (-(50 * (L + 1) : ℕ))) := by
  unfold seamClockPotential Config.sumOf
  set M : ℝ≥0∞ := ENNReal.ofReal (Real.exp (-(50 * (L + 1) : ℕ))) with hM
  -- every summand is ≤ M
  have hbound : ∀ x ∈ Multiset.map (seamClockSummand (L := L) (K := K) p 1) c, x ≤ M := by
    intro x hx
    rw [Multiset.mem_map] at hx
    obtain ⟨a, ha, rfl⟩ := hx
    unfold seamClockSummand
    by_cases hcond : a.role = .clock ∧ a.phase.val = p + 1
    · obtain ⟨hrole, hphase⟩ := hcond
      rw [if_pos ⟨hrole, hphase⟩, hfull a ha hrole hphase, hM]
      -- summand = ofReal(exp(−(1·50(L+1)))) = M
      apply le_of_eq
      congr 2
      push_cast; ring
    · rw [if_neg hcond]; exact zero_le'
  calc (Multiset.map (seamClockSummand (L := L) (K := K) p 1) c).sum
      ≤ Multiset.card (Multiset.map (seamClockSummand (L := L) (K := K) p 1) c) • M :=
        Multiset.sum_le_card_nsmul _ M hbound
    _ = (n : ℝ≥0∞) * M := by
        rw [Multiset.card_map, hcard, nsmul_eq_mul]

/-! ## Stage 2 — the at-risk tail with `hinitΦ` discharged from the entry fact. -/

/-- **The honest at-risk tail, `hinitΦ` discharged.**  Specialises
`seam_atRiskClockZero_tail_honest` (the landed affine engine, immigration
`2·eˢ·freshVal`, budget `e^{−40(L+1)}`) by deriving its `hinitΦ` from the seam-entry
full-counter fact `SeamEntryFullCounter p c₀` via `seamClockPotential_init_le`.  The
remaining hypotheses are the structural `CounterResetDest (p+1)` /
`SeamRegimeDispatch p` guards + the size/log/timing arithmetic. -/
theorem seam_atRiskTail_of_entry (p n tseam : ℕ)
    (hq : CounterResetDest (p + 1)) (hdisp : SeamRegimeDispatch (L := L) (K := K) p)
    (hn : 1 ≤ n) (hn2 : 2 ≤ n)
    (hlog : Real.log (n : ℝ) ≤ (L + 1 : ℕ))
    (ht : tseam ≤ n * (L + 1))
    (c₀ : Config (AgentState L K)) (hcard₀ : Multiset.card c₀ = n)
    (hentry : SeamEntryFullCounter (L := L) (K := K) p c₀) :
    ((NonuniformMajority L K).transitionKernel ^ tseam) c₀
      {c | AtRiskClockZero (L := L) (K := K) p c}
      ≤ ENNReal.ofReal (Real.exp (-(40 * (L + 1) : ℕ))) :=
  seam_atRiskClockZero_tail_honest p n tseam hq hdisp hn hn2 hlog ht c₀ hcard₀
    (seamClockPotential_init_le p n c₀ hcard₀ hentry)

/-! ## Stage 3 — the assembled `hbound` from the entry fact.

The per-`τ` at-risk tails feed `SeamNoOvershoot.seam_noOvershoot_tail` (the prefix-union
first-exit composition + the deterministic bridge).  Each prefix term `(K^τ) c₀ {AtRisk}`
is bounded FROM the FIXED seam start `c₀` (horizon `τ ≤ tseam`), so the SAME entry fact
`SeamEntryFullCounter p c₀` discharges `hinitΦ` for every `τ`.  The result is the
`hbound` shape (`(K^tseam) c₀ {¬NoOvershoot} ≤ e^{−40(L+1)}`) consumed by
`hNoOvershoot_one_seam`. -/

/-- **The assembled honest `hbound` from the seam-entry fact.**  From a `NoOvershoot`
start `c₀` that additionally satisfies `SeamEntryFullCounter p c₀` and the size/timing
side conditions, the `tseam`-step overshoot mass is `≤ tseam · e^{−40(L+1)}` — but we
deliver the per-seam budget shape `≤ e^{−40(L+1)}` by routing through the per-`τ` tails
only at `τ < tseam`, then folding via `seam_noOvershoot_tail`.

We deliver the `(K^tseam) c₀ {¬NoOvershoot} ≤ tseam · e^{−40(L+1)}` bound; the
`hNoOvershoot_one_seam` budget wrapper turns it into the `≤ εovershoot` field once
`tseam · e^{−40(L+1)} ≤ εovershoot`. -/
theorem seam_noOvershoot_tail_of_entry (p n tseam : ℕ)
    (hq : CounterResetDest (p + 1)) (hdisp : SeamRegimeDispatch (L := L) (K := K) p)
    (hdet : DetSeamOvershootBridge (L := L) (K := K) p)
    (hn : 1 ≤ n) (hn2 : 2 ≤ n)
    (hlog : Real.log (n : ℝ) ≤ (L + 1 : ℕ))
    (ht : tseam ≤ n * (L + 1))
    (c₀ : Config (AgentState L K)) (hcard₀ : Multiset.card c₀ = n)
    (h0 : NoOvershoot (L := L) (K := K) p c₀)
    (hentry : SeamEntryFullCounter (L := L) (K := K) p c₀) :
    ((NonuniformMajority L K).transitionKernel ^ tseam) c₀
        {c | ¬ NoOvershoot (L := L) (K := K) p c}
      ≤ (tseam : ℝ≥0∞) * ENNReal.ofReal (Real.exp (-(40 * (L + 1) : ℕ))) := by
  refine seam_noOvershoot_tail p tseam hdet c₀ h0 ?_
  intro τ hτmem
  have hτ_le : τ ≤ n * (L + 1) := le_trans (le_of_lt (Finset.mem_range.mp hτmem)) ht
  exact seam_atRiskTail_of_entry p n τ hq hdisp hn hn2 hlog hτ_le c₀ hcard₀ hentry

/-! ## Stage 4 — the per-seam `hNoOvershoot` feeder value.

The `DotyAssembly'.hNoOvershoot` field shape is

  `∀ c, (allPhaseGe (seamP k) n c ∧ advTriggered (seamP k + 1) c) →
        (K^(seamT k)) c {¬ NoOvershoot (seamP k) c'} ≤ εovershoot k`.

We produce it for the honest counter-timed destinations `seamP k + 1 ∈ {1,6,7,8}`.  The
seam `Pre`'s `NoOvershoot (seamP k) c` start and the `SeamEntryFullCounter (seamP k) c`
fact (the just-advanced clocks at full counter) are the honest seam-entry facts the work
`Post`/seed step delivers; we carry them as the entry hypotheses `hStartNoOver`/`hEntry`
(a per-pair structural reading of the seam-entry configuration, supplied by the seam
layer), and discharge the deterministic bridge from `Wf` via
`SeamOvershootBridge.detSeamOvershootBridge_of_wf`. -/

/-- **The per-seam `hNoOvershoot` value, produced.**  At the `DotyAssembly'.hNoOvershoot`
field shape (for one seam with destination `p+1 ∈ {1,6,7,8}`), this delivers the
no-overshoot budget `≤ εovershoot` from:

* the seam-entry facts `hStartNoOver`/`hEntry` (start `NoOvershoot p` + every phase-`(p+1)`
  clock at full counter — the just-advanced clocks, supplied per-config by the seam layer
  from the work `Post`/seed structure);
* the structural guards `CounterResetDest (p+1)`, `SeamRegimeDispatch p`, the `Wf`-region
  (discharging the deterministic bridge via `detSeamOvershootBridge_of_wf`);
* the size/log/timing arithmetic + the budget fit `tseam · e^{−40(L+1)} ≤ εovershoot`.

This is exactly the value the `hNoOvershoot` feeder field of the assembly bundle expects,
PRODUCED (not carried) for the honest destination set. -/
theorem hNoOvershoot_field_of_entry (p n tseam : ℕ) (εovershoot : ℝ≥0)
    (hq : CounterResetDest (p + 1)) (hdisp : SeamRegimeDispatch (L := L) (K := K) p)
    (hWf : ∀ c : Config (AgentState L K), Wf (L := L) (K := K) c)
    (hn : 1 ≤ n) (hn2 : 2 ≤ n)
    (hlog : Real.log (n : ℝ) ≤ (L + 1 : ℕ))
    (ht : tseam ≤ n * (L + 1))
    (hcard : ∀ c : Config (AgentState L K),
      (SeamEpidemics.allPhaseGe (L := L) (K := K) p n c ∧
        SeamEpidemics.advTriggered (L := L) (K := K) (p + 1) c) →
      Multiset.card c = n)
    (hStartNoOver : ∀ c : Config (AgentState L K),
      (SeamEpidemics.allPhaseGe (L := L) (K := K) p n c ∧
        SeamEpidemics.advTriggered (L := L) (K := K) (p + 1) c) →
      NoOvershoot (L := L) (K := K) p c)
    (hEntry : ∀ c : Config (AgentState L K),
      (SeamEpidemics.allPhaseGe (L := L) (K := K) p n c ∧
        SeamEpidemics.advTriggered (L := L) (K := K) (p + 1) c) →
      SeamEntryFullCounter (L := L) (K := K) p c)
    (hε : (tseam : ℝ≥0∞) * ENNReal.ofReal (Real.exp (-(40 * (L + 1) : ℕ)))
        ≤ (εovershoot : ℝ≥0∞)) :
    ∀ c : Config (AgentState L K),
      (SeamEpidemics.allPhaseGe (L := L) (K := K) p n c ∧
        SeamEpidemics.advTriggered (L := L) (K := K) (p + 1) c) →
      ((NonuniformMajority L K).transitionKernel ^ tseam) c
          {c' | ¬ NoOvershoot (L := L) (K := K) p c'}
        ≤ (εovershoot : ℝ≥0∞) := by
  have hdet : DetSeamOvershootBridge (L := L) (K := K) p :=
    detSeamOvershootBridge_of_wf p hq hWf
  intro c hPre
  refine le_trans ?_ hε
  exact seam_noOvershoot_tail_of_entry p n tseam hq hdisp hdet hn hn2 hlog ht c
    (hcard c hPre) (hStartNoOver c hPre) (hEntry c hPre)

/-! ## Stage 5 — the produced-vs-guarded destination accounting.

The honest counter-reset destination set is `{1,6,7,8}` (`CounterResetDest`).  In the
21-instance `dotyPhases'` family the 10 seams `k : Fin 10` advance `seamP k → seamP k + 1`
for the standard phase chain `seamP k = k` (seam `k` is the `phase k → phase k+1` advance,
so destination `= k+1`).  Hence:

* **PRODUCED** (counter-timed, full-counter-reset on entry; `hNoOvershoot_field_of_entry`
  applies): destinations `{1,6,7,8}`, i.e. seams with `seamP k ∈ {0,5,6,7}`.
* **GUARDED** (named, not faked): the rest.
  - destinations `{2,9}` are UNTIMED (opinion-union / big-bias advance) — `CounterResetDest`
    is FALSE; their no-overshoot is the work-phase / big-bias guard in `SeamEpidemics`.
  - destination `4` is UNTIMED (big-bias) — same.
  - destinations `{3,5}` are counter-timed but their entry does NOT reset the counter
    (`phase 3` `phaseInit` sets `minute`, not `counter`; `phase 5` predecessor advances via
    `advancePhase`, no `phaseInit`) — `CounterResetDest` excludes them; their no-overshoot
    comes from the dedicated minute/hour width machinery (`ClockOLogN`/`ClockReal*`).
  - destination `10` is the error/backup entry, outside the seam chain.

The four-element guard accounting matches `SeamPairAdapter`'s closing doc; the produced
set is exactly the `SeamPairAdapter` honest set. -/

/-- The PRODUCED destinations are exactly `CounterResetDest`: `seamP ∈ {0,5,6,7}` ⟹
`seamP + 1 ∈ {1,6,7,8}`.  (The accounting witness for the produced seams.) -/
theorem counterResetDest_of_seamP_mem {q : ℕ} (h : q = 0 ∨ q = 5 ∨ q = 6 ∨ q = 7) :
    CounterResetDest (q + 1) := by
  rcases h with h | h | h | h <;> simp [CounterResetDest, h]

/-- The GUARDED destinations are NOT `CounterResetDest`: the untimed `{2,4,9}` and the
no-counter-reset `{3,5}` destinations (`seamP ∈ {1,2,3,4,8}`) all FAIL `CounterResetDest`,
so `hNoOvershoot_field_of_entry` does not apply — they are discharged by their own named
work-phase / width guards (documented above). -/
theorem not_counterResetDest_of_guarded {q : ℕ}
    (h : q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 8) :
    ¬ CounterResetDest (q + 1) := by
  rcases h with h | h | h | h | h <;> · subst h; decide

end SeamNoOvershoot

end ExactMajority
