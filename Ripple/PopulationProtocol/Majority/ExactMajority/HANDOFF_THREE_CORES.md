# HANDOFF: three cores A/B/C (family2 letter, task ac794b96, 2026-06-10)

Source: ChatGPT Pro (family2, Ripple connector). 15,421 B. Verbatim below.

---

## STATUS (2026-06-10) — Brick A remainder attacked in `Probability/ProfileSquaringRate.lean`

The single named remainder of Brick A — `MainExponentConfinement.MainProfileSquaredBound` (the
real-valued windowed squaring on `mainFrac`, carried as the `hSquaring` field of
`MainProfileHourHypotheses`) — is now DISCHARGED *modulo* ONE genuinely-dynamic carried coupling,
in NEW append-only file `Probability/ProfileSquaringRate.lean`. No existing file edited. Single-file
`lake env lean` EXIT_0 (uisai2 v4.30.0); all headlines `#print axioms ⊆ [propext, Classical.choice,
Quot.sound]`; no sorry/admit/axiom/native_decide. One commit `61a90ce2`, pushed to `main` + mirrored.

* **Stage 1 — the HONEST per-step rate (PROVEN, the genuine quantitative attack).**
  `split_rectangle_mass` / `honest_per_step_source`: ONE interaction raises `mainProfileAbove (i+1)`
  only via a split on the rectangle of pairs `(.zero with hour>i) × (.main dyadic exactly i)`. Via
  the LANDED `RoleSplitConcentration.sum_iCount_rectangle_disjoint`, the split-eligible rectangle
  mass factorises as `zeroSupplyCount i · mainExactCount i = Z_i · M_i`. **The honest one-step rate
  is therefore `c_{=i}·Z_i/n²` — a PRODUCT, demonstrably NOT the naive `c_{≥i}²`.** This is the
  honest derivation the prompt demanded: the naive squared form is FALSE at the single-step level.
* **Stage 2 — the hour-level squaring recovery (carried coupling).**
  The square `c_{≥i+1} ≤ c_{≥i}²` is an HOUR-level fact: the `.zero`-supply `Z_i` doublable to level
  `i+1` is itself produced, within the hour, by Rule-3 cancellations of `±i` pairs (which emit two
  `.zero` agents with `hour = i`), so `Z_i` is dynamically bounded by the level-`≥i` mass and the
  product `Z_i · M_i ≲ µ_{≥i}²`. This zero-supply ↔ high-mass coupling is carried as ONE precise
  named field `IntegerProfileSquaring` (the integer `µ_{≥i+1}·|M| ≤ µ_{≥i}²`), the Main-profile
  counterpart of the clock side's `ClockFrontProfile.GoodFrontProfile` — exactly the same honesty
  shape (a TRUE dynamic recurrence carried, not faked).
* **Stage 3 — the reduction + wiring (PROVEN).**
  `mainProfileSquaredBound_of_coupling` DERIVES `MainProfileSquaredBound` from `IntegerProfileSquaring`
  by pure division algebra (in-range: divide by `mainCount²`; boundary `i+1=L+1`: `mainFrac = 0 ≤ □²`).
  `mainHourHypotheses_of_coupling` builds `MainProfileHourHypotheses` discharging `hSquaring`, so
  `theorem6_2_main_confinement_whp`'s per-hour input is hypothesis-free except the landed clock facts
  + the carried `IntegerProfileSquaring` coupling + arithmetic.

**Closed vs carried (honest).** The honest per-step rate (Stage 1) is fully CLOSED — the genuine new
content, and it proves the naive `c²` form is NOT the single-step rate. The reduction (Stage 3) is
fully CLOSED. The single remaining residual is `IntegerProfileSquaring` — the integer hour-boundary
squaring `µ_{≥i+1}·|M| ≤ µ_{≥i}²`, the genuinely-dynamic zero-supply ↔ high-mass coupling that the
landed §6 clock Posts do not export for the Main exponent profile. It is the Main-profile twin of
the clock's already-named `GoodFrontProfile` residual: the next thing to discharge probabilistically
(the §6 hour dynamics establishing `Z_i ≲ µ_{≥i}`).

---

## STATUS (2026-06-10) — Brick A landed in `Probability/MainExponentConfinement.lean`

Brick A (Theorem 6.2 Main biased-exponent profile confinement, the LAST big probability brick of
the whp half) DELIVERED in NEW append-only file `Probability/MainExponentConfinement.lean`. No
existing file edited. Single-file `lake env lean` EXIT_0; all headlines `#print axioms` ⊆
`[propext, Classical.choice, Quot.sound]`; no sorry/admit/axiom/native_decide. Two commits (Stage 1
ledger `02f00244`, Stage 2+3 union+wire `f01e3081`), pushed to `main` + mirrored to
`xiangyazi24/Ripple opus-wip`.

* **Stage 1 — per-rule profile ledger (PROVEN, the honest squaring core).**
  `phase3CancelSplit_no_jump`: exhaustive case analysis of the FROZEN `phase3CancelSplit` rules
  shows an output at exponent `k = m+1` is sourced ONLY from an input already at exponent `k`
  (cancel/no-op preserve exponents) or exponent `m = k-1` (the split/doubling rule). This is the
  deterministic squaring witness — "advancing to level `i+1` consumes an agent already at level
  `i`" — that grounds the paper's `c_{≥i+1} ≤ p·c_{≥i}²` rate. Plus `phase3CancelSplit_output_exp_ledger`
  (bias-sum conservation) and the `mainProfileAbove`/`mainBiasedAt` observables on Brick 0 finsets.
* **Stage 2 — single-hour squaring brick (PROVEN by instantiating LANDED engines).**
  `mainProfile_collapse` instantiates the LANDED `FrontTail.windowed_floor_crossing`
  doubly-exponential descent on the Main above-cap fraction `mainFrac` (collapse below any floor
  `θ ≥ 1/n` within `frontWidthBound n = O(log log n)` hours), fed the carried per-hour squaring
  rate. `main_profile_hour_squaring` instantiates the LANDED `WindowConcentration.windowDrift_tail`
  for the per-hour probabilistic tail `(Kᵗ) c₀ {¬Post} ≤ rᵗ·Φ(c₀)/θ`.
* **Stage 3 — all-hours union + consumer wiring (PROVEN union SHAPE).**
  `theorem6_2_main_confinement_whp`: the headline producing the `hConfine` event bound `≤ η` from
  the per-hour tails. `theorem62_entry_of_confinement` constructs
  `UsefulMainFloor.Theorem62EntryHypotheses` from the confinement readout + Phase-5 window + role
  floor — verified end-to-end to feed `UsefulMainFloor.theorem6_2_usefulMains_floor` → the consumer
  floor `P ≤ #usefulMains` UNCHANGED.

**Closed vs carried (honest).** The deterministic per-rule squaring ledger (Stage 1) and both
abstract-engine instantiations (Stage 2) are CLOSED. The all-hours union (Stage 3) is the honest
union SHAPE: the per-hour squaring tail is consumed as the explicit hypothesis `hHourTail` (the
Stage-2 brick named), and the union is discharged from the per-hour budget. The hour-clock
synchronisation is consumed as `MainProfileHourHypotheses` (bundling the landed
`ClockFrontProfile.WindowedFrontProfile`), NOT re-proved. The genuinely-dynamic Main-profile
per-hour drift RATE — the `c_{≥i+1} ≤ p·c_{≥i}²` the landed clock Posts do not export for the Main
exponent profile — is carried as ONE precise named field `MainProfileSquaredBound` (the Main-profile
counterpart of the clock `WindowedFrontProfile`), after the Stage-1 ledger attack establishes its
mechanism. The confinement readout `0.92·|M| ≤ #usefulMains` is the carried `MainProfileConfinedToUseful`
field, definitionally the `hConfine` event. So `hConfine` is now derivable from
`MainProfileConfinedToUseful` via `theorem62_entry_of_confinement` (the carried field is the precise
named remainder, the collapse readout, not a faked bound).

---

## STATUS (2026-06-10) — Brick 0 + B + C landed in `Probability/MarginLedgers.lean`

New file `Probability/MarginLedgers.lean` (append-only, no existing file edited). Single-file
`lake env lean` EXIT_0; every headline `#print axioms ⊆ [propext, Classical.choice, Quot.sound]`;
no sorry/admit/axiom/native_decide.

* **Brick 0 (DONE, fully closed)** — shared Main exponent-profile finset algebra.
  `mainAtExp`/`majorityAtExp`/`minorityAtExp` observables (`mainAtExp = Phase7.minorityAt7 =
  Phase8.minorityAt`, definitional), profile masses, and `main_profile_partition`:
  `mainCount c = majorityProfileMass σ c + minorityProfileMass σ c + zeroMainCount c`.
  Flat ↔ per-exponent bridge proved fiberwise over the bias exponent. Follows `PhaseFloors`
  finset-filter style. NO carried field.
* **Brick B (DONE, ledger closed; ONE carried per-level field)** —
  `phase6_to_phase7_eliminator_margin_of_confinement`. From `MainConfinementProfile` (A-shape:
  `hUseful` 0.92 confinement, `hMinoritySmall` 0.12, `hMainFloor` n/3) + `Phase6Win` + carried
  `Phase6HighMassDrained`, derives `EliminatorMargins.Phase6To7Structure σ E c` for `E ≤ 4n/15`.
  The GLOBAL majority-eliminator budget `majorityProfileMass ≥ 4n/15` is PROVED
  (`majorityProfileMass_floor`: 0.92−0.12 = 0.8, 0.8·(n/3) = 4n/15 — the partition residue ledger).
  Per-level gap-1 localization carried as `Phase6HighMassDrained` (the eliminator LOWER bound the
  survival-UPPER Posts omit).
* **Brick C (DONE, ledger closed; ONE carried per-level field)** —
  `phase7_to_phase8_eliminator_margin_of_phase7`. From B's `Phase6To7Structure` at Phase-7 entry
  (`c_start`) + `Phase7AllMain` window + carried `Phase7SurvivalUpperBounds`, derives
  `EliminatorMargins.Phase7To8Structure σ E c` for `E ≤ n/5`. REAL transition-ledger attack on the
  FROZEN `cancelSplit`: same-level cancel is the only eliminator loss (gap-1 increments/preserves
  the eliminator, gap-2 preserves/grows the σ-opposite supply); landed `lemma_7_5/7_6` are
  survival-UPPER bounds not eliminator LOWER bounds, so the surviving above-level count is a genuine
  dynamic fact — carried as ONE precise named field after the attack.

Both B/C outputs are the EXACT `EliminatorMargins.Phase6To7Structure` / `Phase7To8Structure`
consumer shapes (`#check`-verified); the downstream adapters (`lemma7_4_phase7_elimGap1_floor`,
`lemma7_6_phase8_elimAbove_floor`, `phase7/8_hdrop_wired`) consume them unchanged. Constants
verified: 0.92, 0.12, 0.8, 4n/15 = 0.8·n/3, n/5. Brick A (Theorem 6.2 Main confinement, the one big
probability brick) remains carried in `UsefulMainFloor.Theorem62EntryHypotheses.hConfine` — out of
scope for this file.

---

I’ll read the three new floor files and the invariant/Post files enough to separate “new probability” from deterministic ledger work. Then I’ll give a brick order and Lean target signatures without claiming unlanded exports exist.

The new files are explicit: A/B/C are deliberately carried as named fields, not hidden in Posts. UsefulMainFloor carries hConfine; EliminatorMargins carries Phase6To7Structure/Phase7To8Structure; PhaseFloors confirms 5/7/8 provenance is not landed. I’ll now separate what can be deterministic from what needs a new probabilistic brick.

Bottom line

The new floor-wiring files correctly isolate the remaining probability. I would not try to derive A/B/C from the existing Phase-3/4/6/7/8 Posts: the landed code explicitly audits that those Posts do not export the needed count-lower bounds. The right plan is:

Build the Main exponent-profile confinement theorem for A first.

Then try to derive B/C deterministically from A plus Phase-6/7 transition ledgers, but do not assume this is already landed.

Keep B/C as named fields until the deterministic margin derivations are actually proved.

The new files say this plainly: UsefulMainFloor carries hConfine; EliminatorMargins carries Phase6To7Structure and Phase7To8Structure; PhaseFloors says phases 5/7/8 are still missing their lower-bound provenance, while Phase 6 alone is fully wired from a landed Phase-5 Post. 

UsefulMainFloor

 

EliminatorMargins

 

PhaseFloors

1. A: Theorem 6.2 mechanism and Lean route

The paper mechanism is not just clock-front width. The clock front is only the scheduler/synchronization backbone. The actual Theorem 6.2 content is a Main bias-exponent profile collapse.

The UsefulMainFloor audit summarizes the intended paper route: Theorem 6.2 uses Theorem 6.5’s repeated-squaring style bound on the biased-Main exponent profile, plus mass-above and minority-mass bounds, unioned over O(log n) hours. Its header records the critical profile facts as the missing content: a squaring recurrence of the form roughly “mass at exponent ≥ i+1 after an hour is bounded by a constant times the square of mass at exponent ≥ i,” together with bounds like µ(>−l) and minority mass being small. 

UsefulMainFloor

The Lean consumer wants only this final field:

lean
hConfine :
  (0.92 : ℝ) * (RoleSplitConcentration.mainCount (L := L) (K := K) c : ℝ)
    ≤ (((Phase5Convergence.usefulMains (L := L) (K := K)).sum c.count : ℕ) : ℝ)

inside:

lean
structure Theorem62EntryHypotheses (n : ℕ) (c : Config (AgentState L K)) : Prop where
  hPhase5 : ReserveSampling.Phase5AllWin (L := L) (K := K) n c
  hMainFloor : (n : ℝ) / 3 ≤
    (RoleSplitConcentration.mainCount (L := L) (K := K) c : ℝ)
  hConfine : ...

and the arithmetic from hConfine to the Phase-5 floor is already proved:

lean
theorem theorem6_2_usefulMains_floor ...
    (hT62 : Theorem62EntryHypotheses n c) (P : ℕ)
    (hP : (P : ℝ) ≤ (23 : ℝ) * (n : ℝ) / 75) :
    P ≤ (Phase5Convergence.usefulMains (L := L) (K := K)).sum c.count

UsefulMainFloor

Minimal Main-side ledger for A

Do not extend the clock-front files. Add a new Main-side profile file, e.g.

lean
Probability/MainExponentConfinement.lean

with these bricks.

First define Main exponent-profile observables, distinct from clock minute front:

lean
namespace MainExponentConfinement

def mainDyadicAt (σ : Sign) (i : Fin (L + 1)) : Finset (AgentState L K) :=
  Finset.univ.filter
    (fun a => a.role = Role.main ∧ a.bias = Bias.dyadic σ i)

def mainDyadicBelowCap : Finset (AgentState L K) :=
  Phase5Convergence.usefulMains (L := L) (K := K)

def mainProfileAbove (σ : Sign) (i : Fin (L + 1)) (c : Config (AgentState L K)) : ℕ :=
  ∑ j : Fin (L + 1), if i.val ≤ j.val then
    (mainDyadicAt (L := L) (K := K) σ j).sum c.count else 0

Then prove the per-rule profile ledger for Phase 3/4 Main bias operations. This is the new deterministic core:

lean
theorem phase3_mainProfile_step_ledger
    (σ : Sign) (i : Fin (L + 1))
    (c c' : Config (AgentState L K))
    (hstep : (NonuniformMajority L K).StepRel c c')
    (hphase : Phase3MainWindow n c) :
    mainProfileAbove (L := L) (K := K) σ i c'
      ≤ MainProfileStepBound σ i c

Then the probabilistic hour-level squaring brick:

lean
structure MainProfileHourHypotheses (n : ℕ) (T : ℕ)
    (c : Config (AgentState L K)) : Prop where
  hClockWindow : ClockFrontProfile.WindowedFrontProfile ... c
  hMainWindow  : Phase3MainWindow (L := L) (K := K) n c
  hProfileMass : MainProfileMassInvariant (L := L) (K := K) n c

theorem main_profile_hour_squaring
    (n T : ℕ) (σ : Sign) (i : Fin (L + 1))
    (ε : ℝ≥0∞)
    (c₀ : Config (AgentState L K))
    (hH : MainProfileHourHypotheses (L := L) (K := K) n T c₀) :
    ((NonuniformMajority L K).transitionKernel ^ hourLen) c₀
      {c | ¬ MainProfileSquaredBound (L := L) (K := K) n σ i T c}
      ≤ ε

This is where you reuse the landed engines, not the landed clock statements. The best fit is the same finite-window drift/union technology already used elsewhere: WindowConcentration for one-step MGF/potential drift, or the killed/step-indexed gated engine if the profile drift is only on a side gate. The clock §6 files provide side conditions, not the Main-profile conclusion.

Finally package the all-hours union:

lean
theorem theorem6_2_main_confinement_whp
    (n : ℕ) (η : ℝ≥0∞)
    (c₀ : Config (AgentState L K))
    (hEntry : Phase3GoodEntry (L := L) (K := K) n c₀)
    (hHours :
      ∀ T < L + 1, MainProfileHourHypotheses (L := L) (K := K) n T c₀)
    (hSquaring :
      ∀ T < L + 1, MainProfileHourSquaringBudget ... ≤ η / (L + 1)) :
    ((NonuniformMajority L K).transitionKernel ^ phase3to5Time) c₀
      {c | ¬
        ((0.92 : ℝ) *
          (RoleSplitConcentration.mainCount (L := L) (K := K) c : ℝ)
          ≤ (((Phase5Convergence.usefulMains (L := L) (K := K)).sum c.count : ℕ) : ℝ))}
      ≤ η

Then wire it into the existing consumer by filling Theorem62EntryHypotheses.hConfine.

2. B/C: deterministic consequence of A, or new probability?
What is already proved

EliminatorMargins is explicit: the minority-witness half is deterministic and already proved, but the eliminator lower bound is carried.

For Phase 7, the carried field is:

lean
def Phase6To7Structure (σ : Sign) (E : ℕ) (c : Config (AgentState L K)) : Prop :=
  ∀ j : Fin (L + 1),
    1 ≤ (Phase7Convergence.minorityAt7 σ j).sum c.count →
    ∃ i : Fin (L + 1),
      i.val + 1 = j.val ∧
      E ≤ (Phase7Convergence.elimGap1 σ i).sum c.count

For Phase 8:

lean
def Phase7To8Structure (σ : Sign) (E : ℕ) (c : Config (AgentState L K)) : Prop :=
  ∀ i : Fin (L + 1),
    1 ≤ (Phase8Convergence.minorityAt σ i).sum c.count →
    E ≤ (Phase8Convergence.elimAbove σ i).sum c.count

and the adapters simply consume those fields. 

EliminatorMargins

The file also states why landed Posts do not suffice: Invariants.lemma_7_5/7_6 are survival upper bounds, not eliminator-count lower bounds. 

EliminatorMargins

B: likely deterministic after A + Phase 6, but not from current Posts alone

Conceptually, B should be a deterministic consequence of:

A’s confinement: most majority Mains are useful and concentrated in a narrow exponent band.

Phase 6 high-mass drain: high-exponent biased agents have been split downward.

Bias/mass conservation and minority upper bound: remaining minority at level j forces a large majority supply at j−1.

The definition of elimGap1 σ i.

But this deterministic implication is not currently in the landed Phase6Convergence.Post. The Phase 6 file’s status note says it has the highU predicate and per-rule doSplit behavior, and that the full Lemma-7.2 progress instance is follow-up; it does not export an eliminator-margin lower bound. 

Phase6Convergence

So B should be attacked as a new deterministic ledger theorem, but until it is proved, keep Phase6To7Structure as the named field.

Target deterministic theorem:

lean
structure MainConfinementProfile (σ : Sign) (n : ℕ)
    (c : Config (AgentState L K)) : Prop where
  hUseful :
    (0.92 : ℝ) *
      (RoleSplitConcentration.mainCount (L := L) (K := K) c : ℝ)
      ≤ (((Phase5Convergence.usefulMains (L := L) (K := K)).sum c.count : ℕ) : ℝ)
  hMinoritySmall :
    MinorityProfileMass (L := L) (K := K) σ c ≤ ...
  hMajorityBand :
    MajorityBandMass (L := L) (K := K) σ.flip c ≥ ...

theorem phase6_to_phase7_eliminator_margin_of_confinement
    {n E : ℕ} {σ : Sign} {c : Config (AgentState L K)}
    (hA : MainConfinementProfile (L := L) (K := K) σ n c)
    (h6 : Phase6Convergence.Phase6Win (L := L) (K := K) n c)
    (hPost6 : Phase6HighMassDrained (L := L) (K := K) σ c)
    (hE : (E : ℝ) ≤ (4 : ℝ) * (n : ℝ) / 15) :
    EliminatorMargins.Phase6To7Structure (L := L) (K := K) σ E c

The proof should be a partition ledger:

useful majority Mains
= gap-1 eliminators
  + same-level/nonpartner majority
  + too-high/too-low residue
  + minority residue

Then use A plus Phase-6 high-mass-drain upper bounds to show the residues are at most about 0.12|M|, leaving ≥ 0.8|M| in the gap-1 partner bucket. The exact constants must be chosen to match the consumer’s E ≤ 4n/15, because 0.8 * n/3 = 4n/15.

Once this theorem is proved, it fills:

lean
hPhase6Post : Phase6To7Structure σ E c

and the existing adapter:

lean
lemma7_4_phase7_elimGap1_floor

finishes the Phase-7 hdrop. 

EliminatorMargins

C: likely deterministic after B + Phase 7 survival, but not currently landed

Phase 8’s header explains the intended invariant: absorbConsume consumes minority using non-full majority eliminators above the minority level; full eliminates one-time capacity, and the carried invariant is that surviving non-full majority eliminators remain above the minority count. 

Phase8Convergence

So C should be a deterministic consequence of:

B’s Phase-7 starting eliminator margins.

Phase-7 cancellation dynamics: it drains minority without exhausting too many eliminators.

Landed survival upper bounds from lemma_7_5/7_6, if they indeed cap minority survivors or consumed eliminators.

The Phase-7 Post.

But again, current files do not export the lower bound. EliminatorMargins intentionally carries:

lean
Phase7To8Structure σ E c

as the exact missing remainder. 

EliminatorMargins

Target deterministic theorem:

lean
theorem phase7_to_phase8_eliminator_margin_of_phase7
    {n E : ℕ} {σ : Sign} {c : Config (AgentState L K)}
    (hStart : EliminatorMargins.Phase6To7Structure (L := L) (K := K) σ E c_start)
    (h7win : Phase7Convergence.Phase7AllMain (L := L) (K := K) n c)
    (h7post : Phase7Convergence.Phase7PostStructure (L := L) (K := K) σ c)
    (hSurviveUpper :
      Phase7SurvivalUpperBounds (L := L) (K := K) σ E c)
    (hE : (E : ℝ) ≤ (1 : ℝ) * (n : ℝ) / 5) :
    EliminatorMargins.Phase7To8Structure (L := L) (K := K) σ E c

Partition ledger:

initial gap-1 / above eliminators
− eliminators spent or marked full during Phase 7
− eliminators lost to cancellation side effects
≥ remaining minority-at-level demand + margin

If the landed lemma_7_5/7_6 only gives minority upper bounds and not “spent eliminator” accounting, then C still needs a new deterministic transition ledger, not new probability. The probability is already in the Phase-7 drain convergence; the margin preservation is structural but unproved.

Once C is proved, the existing adapter:

lean
lemma7_6_phase8_elimAbove_floor

and then

lean
phase8_hdrop_wired_from_lemma7_6

complete the Phase-8 consumer. 

EliminatorMargins

 

EliminatorMargins

3. Recommended brick order
Brick 0: shared Main/exponent finset algebra

Do this before any probability.

lean
def mainAtExp (σ : Sign) (i : Fin (L + 1)) : Finset (AgentState L K) := ...
def majorityAtExp (σ : Sign) (i : Fin (L + 1)) : Finset (AgentState L K) := ...
def minorityAtExp (σ : Sign) (i : Fin (L + 1)) : Finset (AgentState L K) := ...

theorem main_profile_partition
    (σ : Sign) (c : Config (AgentState L K)) :
    RoleSplitConcentration.mainCount c =
      majorityProfileMass σ c + minorityProfileMass σ c + zeroMainCount c := ...

This infrastructure is shared by A/B/C.

Brick 1: A, probabilistic Main confinement

This is the only large new probability brick.

lean
theorem theorem6_2_main_confinement_whp
    (n : ℕ) (c₀ : Config (AgentState L K))
    (ε : ℝ≥0∞)
    (hEntry : Phase3EntryGood (L := L) (K := K) n c₀)
    (hClockWidth : ClockWidthFeeders (L := L) (K := K) n c₀)
    (hMainProfileDrift : MainProfileSquaringFeeders (L := L) (K := K) n c₀) :
    ((NonuniformMajority L K).transitionKernel ^ phase3to5Time) c₀
      {c | ¬
        ((0.92 : ℝ) *
          (RoleSplitConcentration.mainCount (L := L) (K := K) c : ℝ)
          ≤ (((Phase5Convergence.usefulMains (L := L) (K := K)).sum c.count : ℕ) : ℝ))}
      ≤ ε

Then a deterministic constructor:

lean
theorem theorem62_entry_of_confinement
    {n : ℕ} {c : Config (AgentState L K)}
    (hPhase5 : ReserveSampling.Phase5AllWin (L := L) (K := K) n c)
    (hRole : RoleSplitGood (L := L) (K := K) η n c)
    (hη : η ≤ 1 / 25)
    (hConfine : ... ) :
    UsefulMainFloor.Theorem62EntryHypotheses (L := L) (K := K) n c

using mainCount_lower_of_RoleSplitGood.

Brick 2: B deterministic margin from A + Phase 6

Prove or fail explicitly. This should be next because C probably depends on B.

lean
theorem phase6_to_phase7_structure_of_main_confinement
    {n E : ℕ} {σ : Sign} {c : Config (AgentState L K)}
    (hT62 : UsefulMainFloor.Theorem62EntryHypotheses (L := L) (K := K) n c)
    (h6post : Phase6PostProfile (L := L) (K := K) σ n c)
    (hE : (E : ℝ) ≤ (4 : ℝ) * (n : ℝ) / 15) :
    EliminatorMargins.Phase6To7Structure (L := L) (K := K) σ E c

If this cannot be proved from landed Phase-6 Post, refine Phase6PostProfile to the exact additional deterministic profile facts needed. Do not call it probability unless it is a new tail event.

Brick 3: C deterministic margin from B + Phase 7
lean
theorem phase7_to_phase8_structure_of_phase7_margin
    {n E : ℕ} {σ : Sign} {c : Config (AgentState L K)}
    (hB : EliminatorMargins.Phase6To7Structure (L := L) (K := K) σ E c_before)
    (h7post : Phase7PostProfile (L := L) (K := K) σ n c_before c)
    (hSurv : Phase7SurvivalUpperBounds (L := L) (K := K) σ E c)
    (hE : (E : ℝ) ≤ (1 : ℝ) * (n : ℝ) / 5) :
    EliminatorMargins.Phase7To8Structure (L := L) (K := K) σ E c

Again, if hSurv is not enough because it is only a minority upper bound, add the deterministic “spent eliminator” ledger.

Brick 4: Replace carried fields with derived fields

Once Bricks 1–3 are proved, replace:

lean
Theorem62EntryHypotheses.hConfine
Phase6To7Structure
Phase7To8Structure

by constructors from the proved facts, while leaving the consumer theorems unchanged. That is the lowest-risk path because UsefulMainFloor and EliminatorMargins already provide the adapters into PhaseFloors.

4. What not to do

Do not try to extract A from ClockFrontProfile alone. The UsefulMainFloor audit is correct: clock width says clocks stay synchronized; it does not count Main dyadic exponents. 

UsefulMainFloor

Do not claim B/C follow from lemma_7_5/7_6 unless a lower-bound eliminator ledger is proved. The new files explicitly say the landed lemmas are survival upper bounds, not eliminator lower bounds. 

EliminatorMargins

Do not edit consumers first. They are already wired: phase5_hdrop_wired_from_theorem6_2, phase7_hdrop_wired_from_lemma7_4, and phase8_hdrop_wired_from_lemma7_6 are the correct stable interfaces. 

UsefulMainFloor

 

EliminatorMargins
