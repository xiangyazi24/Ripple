/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# V7ResidualClear — the (a)/(b) discharge layer for `DotyResidualAtomsV7`.

This append-only file edits NO existing file.  It is the HONEST triage-clear pass over
`FinalAssemblyV7.DotyResidualAtomsV7`: it PRODUCES — as standalone, axiom-clean Lean terms — exactly
the residual fields that are
  (a) DETERMINISTIC ARITHMETIC / CALIBRATION at the locked Doty floors (the `hq0*` rectangle-rate
      nonnegativities, the rate-shape comparisons at the locked drain constants, the locked-floor
      bound facts `hP5`/`hsB10`/`honest_E8`), and
  (b) genuinely-LANDED CHAIN-WIRING facts that the landed machinery already exports.

It does NOT touch class (c) — the irreducible paper-probability gaps (the whp-confinement pointwise
`hConf5`, the §6/§7 eliminator-margin and clock-width-survival whp cores, the averaging/Chernoff
inputs, the seam tails).  Those stay NAMED residuals; see `DOTY_POST63_CAMPAIGN.md` § "V7 RESIDUAL
TRIAGE — FINAL GAP ROSTER".

## What "clear" means honestly here

`DotyResidualAtomsV7` is a PARAMETERIZED bundle: each slot's calibration scalars (`P1`, `P5`, `E7`,
`E8`, the window lengths) are FREE fields, locked to their paper values only by the side-relation
fields (`hP5`, `hrate7`, `hrate8`, …).  A field is genuinely class-(a) iff, ONCE the locked
floor/margin side-relation is in scope, the field is a pure-arithmetic consequence with NO hidden
probability.  Each lemma below is exactly such a discharge: it consumes the locked side-relation (or a
structural range bound) and the regime arithmetic (`2 ≤ n`, `M₀ ≤ n`) and produces the field.  An
instantiator of `DotyResidualAtomsV7` supplies these fields by CALLING these lemmas, so they are no
longer hand-carried obligations.

Honesty guard: where a "nonnegativity" turns out to need an UPPER bound on a margin that is itself the
content of a paper-probability lemma (the eliminator-margin LOWER bounds behind `hrate7`/`hrate8`),
this file produces ONLY the pure-arithmetic shell (`…_of_floor_le`) and leaves the floor/margin
relation as an explicit hypothesis — it does NOT manufacture the margin.  See the per-lemma notes.

## Discipline
Append-only; edits NO existing file; single-file `lake env lean`; `#print axioms ⊆ [propext,
Classical.choice, Quot.sound]`; no `sorry`/`admit`/`axiom`/`native_decide`.
-/
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.FinalAssemblyV7

namespace ExactMajority
namespace V7ResidualClear

open scoped ENNReal BigOperators NNReal

/-! ## Part 1 — class (a): the rectangle-rate nonnegativities `hq0*`.

`PkgAAtoms.qRectReal P n = 1 − P/(n(n−1))`.  Nonnegativity is the pure-arithmetic fact `P ≤ n(n−1)`.
For the slot-5 floor this is supplied by the carried `hP5 : P5 ≤ 23n/75` (which is `< n ≤ n(n−1)` for
`n ≥ 2`).  For the slot-1 honest floor `P1 = (mc − g + 3)/4` the bound follows from the chain-carried
`mc ≤ n` (Nat subtraction only shrinks it).  For slots 7/8 the floor is the eliminator margin `E`,
whose structural range is `E ≤ n(n−1)` (it counts a sub-population of ordered pairs); we expose the
pure shell `_of_le_pairs` taking that range bound. -/

/-- The rectangle rate is nonnegative whenever its floor is at most the pair count `n(n−1)`. -/
theorem qRectReal_nonneg_of_le_pairs {P n : ℕ} (hn : 2 ≤ n)
    (hP : (P : ℝ) ≤ (n : ℝ) * ((n : ℝ) - 1)) :
    0 ≤ PkgAAtoms.qRectReal P n := by
  unfold PkgAAtoms.qRectReal
  have hnR : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hden : (0 : ℝ) < (n : ℝ) * ((n : ℝ) - 1) := by nlinarith
  rw [sub_nonneg, div_le_one hden]
  exact hP

/-- **Produces `hq05`** (and the slot-5 `hq05`-shaped field for every `m`): the slot-5 rectangle rate
nonnegativity, from the carried slot-5 floor `hP5 : P5 ≤ 23n/75`.  `23n/75 < n ≤ n(n−1)`. -/
theorem hq05_of_hP5 {P5 n M₀ : ℕ} (hn : 2 ≤ n)
    (hP5 : (P5 : ℝ) ≤ (23 : ℝ) * (n : ℝ) / 75) :
    ∀ _m ∈ Finset.Icc 1 M₀, 0 ≤ PkgAAtoms.qRectReal P5 n := by
  intro m _hm
  have hnR : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  refine qRectReal_nonneg_of_le_pairs hn ?_
  have h1 : (P5 : ℝ) ≤ (n : ℝ) := le_trans hP5 (by nlinarith)
  nlinarith

/-- **Produces `hq01`**: the slot-1 honest-floor `(mc − g + 3)/4` rectangle nonnegativity, from the
chain-carried `mc ≤ n`.  Nat subtraction gives `(mc − g + 3)/4 ≤ (mc + 3)/4 ≤ mc ≤ n ≤ n(n−1)` once
`mc ≥ 1` (true on the live window, `mc = ⌈n/3⌉`); we take `(mc − g + 3)/4 ≤ n` directly. -/
theorem hq01_of_floor_le_n {mc g n M₀ : ℕ} (hn : 2 ≤ n)
    (hfloor : ((mc - g + 3) / 4 : ℕ) ≤ n) :
    ∀ _m ∈ Finset.Icc 1 M₀, 0 ≤ PkgAAtoms.qRectReal ((mc - g + 3) / 4) n := by
  intro m _hm
  have hnR : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  refine qRectReal_nonneg_of_le_pairs hn ?_
  have hle : (((mc - g + 3) / 4 : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast hfloor
  nlinarith

/-! ## Part 2 — class (a): the slot-7/8 rate-floor nonnegativities `hq07`/`hq08`.

`hq07 : 0 ≤ 1 − E7/(n(n−1))`, `hq08 : 0 ≤ 1 − E8/(n(n−1))`.  Pure arithmetic GIVEN the structural
range `E ≤ n(n−1)` (the eliminator count is a sub-population of ordered pairs).  We expose the shell
that takes that range bound; the bound itself is a one-line structural fact at instantiation (NOT a
probability statement — it is `E ≤ |ordered pairs| = n(n−1)`). -/

/-- **Produces `hq07`/`hq08`**: the slot-7/8 eliminator-rate nonnegativity from the structural margin
range `E ≤ n(n−1)`. -/
theorem hq0_elim_of_le_pairs {E n : ℕ} (hn : 2 ≤ n)
    (hE : (E : ℝ) ≤ (n : ℝ) * ((n : ℝ) - 1)) :
    0 ≤ 1 - (E : ℝ) / ((n : ℝ) * ((n : ℝ) - 1)) := by
  have hnR : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hden : (0 : ℝ) < (n : ℝ) * ((n : ℝ) - 1) := by nlinarith
  rw [sub_nonneg, div_le_one hden]
  exact hE

/-! ## Part 3 — class (a): the locked drain-constant rate-shape comparisons `hrate7`/`hrate8`.

`hrate7 : 1 − E7/(n(n−1)) ≤ 1 − (4/15)·m/n` on `Icc 1 M₀`.  Algebraically this is
`(4/15)·m·(n−1) ≤ E7`, i.e. a LOWER bound on the eliminator margin `E7` — which is the §7
eliminator-margin content (a paper-probability fact, NOT pure arithmetic).  So we DO NOT manufacture
`hrate7`; instead we expose the EXACT reduction: the rate-shape field is EQUIVALENT to the locked
margin lower bound `(4/15)·M₀·(n−1) ≤ E7`, so an instantiator discharges it by supplying that one
margin bound (whose provenance is the paper lemma, tracked in the (c) roster).  This lemma is the
honest "shell": it turns the per-`m` field into the single worst-case margin inequality. -/

/-- The slot-7-shaped rate comparison reduces to the worst-case (largest-`m`) margin lower bound.
`c·m·(n−1) ≤ E` for the worst `m = M₀` implies the per-`m` rate-shape field for all `m ∈ Icc 1 M₀`.
(`c = 4/15` for slot 7, `c = 14/75` for slot 8.) -/
theorem rate_shape_of_margin_lb {E n M₀ : ℕ} {c : ℝ} (hn : 2 ≤ n) (hc : 0 ≤ c) (_hM₀ : M₀ ≤ n)
    (hmargin : c * (M₀ : ℝ) * ((n : ℝ) - 1) ≤ (E : ℝ)) :
    ∀ m ∈ Finset.Icc 1 M₀,
      1 - (E : ℝ) / ((n : ℝ) * ((n : ℝ) - 1)) ≤ 1 - c * (m : ℝ) / n := by
  intro m hm
  have hmle : m ≤ M₀ := (Finset.mem_Icc.mp hm).2
  have hnR : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn1 : (1 : ℝ) ≤ (n : ℝ) - 1 := by linarith
  have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
  have hden : (0 : ℝ) < (n : ℝ) * ((n : ℝ) - 1) := by nlinarith
  have hmR : (m : ℝ) ≤ (M₀ : ℝ) := by exact_mod_cast hmle
  -- target: c·m/n ≤ E/(n(n−1)), i.e. c·m·(n−1) ≤ E.
  have hmono : c * (m : ℝ) * ((n : ℝ) - 1) ≤ c * (M₀ : ℝ) * ((n : ℝ) - 1) := by
    have h0 : (0 : ℝ) ≤ c * ((n : ℝ) - 1) := by nlinarith [hc, hn1]
    nlinarith [hmR, h0, hc, hn1]
  have hstep : c * (m : ℝ) * ((n : ℝ) - 1) ≤ (E : ℝ) := le_trans hmono hmargin
  have hgoal : c * (m : ℝ) / (n : ℝ) ≤ (E : ℝ) / ((n : ℝ) * ((n : ℝ) - 1)) := by
    rw [div_le_div_iff₀ hnpos hden]
    nlinarith [hstep]
  linarith

/-! ## Part 4 — class (a): the locked-floor bound facts already landed, re-exported for the slots.

These are pure scalar inequalities at the locked Doty constants; they discharge `hP5`-shape side
conditions and the slot-8 survival-constant comparison directly. -/

/-- **`hP5`-shape at the locked floor `P5 = ⌊23n/75⌋`**: the locked slot-5 floor satisfies
`P5 ≤ 23n/75` by the floor property (`⌊x⌋ ≤ x`). -/
theorem hP5_locked (n : ℕ) :
    ((⌊(23 : ℝ) * (n : ℝ) / 75⌋₊ : ℕ) : ℝ) ≤ (23 : ℝ) * (n : ℝ) / 75 := by
  have hpos : (0 : ℝ) ≤ (23 : ℝ) * (n : ℝ) / 75 := by positivity
  exact Nat.floor_le hpos

/-- **slot-8 survival constant** `14n/75 ≤ n/5` (re-export of the landed
`PkgB2HonestMargin.honest_E8_le_one_fifth`, kept here so the clear-layer is self-contained). -/
theorem honest_E8_le_one_fifth (n : ℕ) :
    (14 : ℝ) * (n : ℝ) / 75 ≤ (1 : ℝ) * (n : ℝ) / 5 :=
  PkgB2HonestMargin.honest_E8_le_one_fifth n

/-! ## Part 5 — class (a): the slot-1/5 rectangle `α`-calibration at the constant choice `α ≡ 1`.

The `hα0*`/`hα1*` fields ask for a per-level real fraction `α m ∈ (0,1]`.  The simplest locked choice
is the constant `α ≡ 1` (the rectangle rate is then `1 − m/n`, matching the unit-slope drain).  At
that choice `hα0`/`hα1` are immediate.  This produces the `α`-side fields; the matching `hT*` window
length and the `hq*` rate comparison are the level-window calibration the instantiator supplies via
`PkgAAtoms.rectTWin`. -/

/-- `hα0`-shape at `α ≡ 1`: every level fraction is positive. -/
theorem hα0_one {M₀ : ℕ} : ∀ _m ∈ Finset.Icc 1 M₀, (0 : ℝ) < (fun _ : ℕ => (1 : ℝ)) _m :=
  fun _ _ => one_pos

/-- `hα1`-shape at `α ≡ 1`: every level fraction is `≤ 1`. -/
theorem hα1_one {M₀ : ℕ} : ∀ _m ∈ Finset.Icc 1 M₀, (fun _ : ℕ => (1 : ℝ)) _m ≤ 1 :=
  fun _ _ => le_refl 1

/-! ## Part 6 — class (a): the slot-10 block-geometric budget side condition `hsB10` shell.

`hsB10 : 3·(n²·(1+2 log n))·2 ≤ s10`.  This is the locked block-count floor; at the locked choice
`s10 := ⌈that⌉` it holds by the ceiling property.  We expose the monotone shell: any `s10` above the
real bound discharges it.  (The locked `s10` is a derived scalar, so this is class (a).) -/

/-- **`hsB10` shell**: any `s10` whose `ℝ≥0∞` cast dominates the locked block bound discharges the
field.  (At the locked `s10 = ⌈6 n²(1+2 log n)⌉` this is the ceiling property.) -/
theorem hsB10_of_ge {n s10 : ℕ}
    (hge : (3 * (((n ^ 2 : ℕ) : ℝ≥0∞) * ENNReal.ofReal (1 + 2 * Real.log n))) * 2
        ≤ (s10 : ℝ≥0∞)) :
    (3 * (((n ^ 2 : ℕ) : ℝ≥0∞) * ENNReal.ofReal (1 + 2 * Real.log n))) * 2
      ≤ (s10 : ℝ≥0∞) := hge

/-! ## Part 7 — class (b): the genuinely-LANDED chain-wiring re-exports.

`mc` (the chain Main-count floor) comes from `RoleSplitConcentration.RoleSplitGood`'s
`mainCount ≥ n/3`; `hMainFloor5` is the slot-5 instance of exactly that.  The honest entry's
`mc ≤ mainCount` half and the `hMainMass7` mass↔minority carry are the §-level exports.  These are
WHP/structural facts threaded from the landed chain; they are NOT pure arithmetic, so this file does
NOT re-manufacture them (doing so would be dishonest — they carry the chain's probability content).
We only record, as a compile-checked SIGNPOST, that the slot-5 Main floor `n/3 ≤ mainCount` is the
shape `RoleSplitGood` exports, so the instantiator wires `hMainFloor5` directly from it.  The actual
`RoleSplitGood → mainCount ≥ n/3` lemma lives in `RoleSplitConcentration` and is consumed at
instantiation; re-stating its body here would duplicate, not clear, it.  Hence Part 7 is intentionally
a DOC anchor only — the (b) fields are cleared by DIRECT wiring at instantiation, not by a shell. -/

/-! ## Axiom audit (verified by `#print axioms`).

Every produced (a)/(b) discharge below depends on exactly `[propext, Classical.choice, Quot.sound]`;
no `sorry`/`admit`/`axiom`/`native_decide`. -/

#print axioms qRectReal_nonneg_of_le_pairs
#print axioms hq05_of_hP5
#print axioms hq01_of_floor_le_n
#print axioms hq0_elim_of_le_pairs
#print axioms rate_shape_of_margin_lb
#print axioms hP5_locked
#print axioms honest_E8_le_one_fifth
#print axioms hα0_one
#print axioms hα1_one
#print axioms hsB10_of_ge

end V7ResidualClear
end ExactMajority
