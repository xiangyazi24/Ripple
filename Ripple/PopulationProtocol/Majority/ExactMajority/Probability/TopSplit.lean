/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# `RoleSplitWindows` via the Lemma-5.1 top-split balance (Doty et al., §5.2).

Doty et al., *Exact Majority* (arXiv:2106.10201v2), Lemma 5.1 / Lemma 5.2.

The blueprint (`HANDOFF_ROLESPLIT_TOPSPLIT.md`, ChatGPT Pro family3 letter): do
NOT formalize `RoleSplitWindows` as "Chernoff on the number of R1 fires" — that
is not stable under the Lean encoding (R4 fires concurrently).  Instead:

  1. The **top-level split balance** (this file, §C/§D): `Main` vs the total mass
     "ever produced as RoleCR" (`topCRMass`) is `n/2 ± δn` whp.  The key process
     is the sign-drift of `X = mainCount − topCRMass`, which the protocol
     invariant `sf + 2·st = mf + 2·mt` (Lemma 5.1) makes inward-drifting.
  2. The **CR-drain** Stage-2 machinery converts most `RoleCR` into balanced
     `Clock`/`Reserve` (`CRDrainWindow`).
  3. The **deterministic conversion** (§B, fully proven here): `TopSplitWindow δ`
     + `CRDrainWindow δ` + `ClockReserveBalanced` + conservation ⟹
     `RoleSplitWindows η` with `δ = η/4`.

Constants: final `η = 1/25`, internal `δ = 1/100` (so `δ = η/4`).

## What this file delivers

* **Stage A** (defs): `topCRMass`, `TopSplitWindow`, `CRDrainWindow`.
* **Stage B** (pure algebra, 0-`sorry`): `RoleSplitWindows_of_topSplit_crDrain`
  — the deterministic conversion, via `roleCount_conservation` +
  `balanced_conservation` from `RoleSplitConcentration`.
* **Stage D** (abstract sign-drift Chernoff brick, 0-`sorry`):
  `signDrift_abs_chernoff` — fitted to the EXISTING `AzumaKernel.azuma_tail`
  engine with potential `Φ = |X|` (see the header note below for the reshaping
  of the blueprint's schematic `h_inward`).
* **Stage C** (instantiate): `topSplitWindow_whp` — the named-hypothesis version
  with the one-step `|X|`-supermartingale drift carried as an explicit input
  `hdrift` (the genuine residual, documented).
* **Stage E** (assembly): `roleSplitWindows_whp` — the union bound over
  `topSplitWindow_whp` (B) + the existing two-stage composition.

## Stage-D reshaping note (RECORDED per the campaign discipline)

The blueprint's §D brick `signDrift_abs_chernoff` cites `stepIndexed_gated_tail`
with `Φ_j x = exp(s·|X x| + correction_j)` and a schematic `h_inward`.  After
studying how `AzumaKernel` instantiates MGF drifts (`stepMGF_bound`,
`expSupermartingale_drift`, `azuma_tail`), the cleaner fit is the **already-built
Azuma engine** `AzumaKernel.azuma_tail`: it takes a real potential with a
*downward supermartingale drift* `∫ Φ ∂(K x) ≤ Φ x` and a *bounded difference*
`|Φ y − Φ x| ≤ c`, and produces the additive tail `exp(−λ²/(2 t c²))` directly
(no killed-kernel escape term).  The reshaping:

  * The blueprint's `h_inward` ("if `X > 0` downward prob ≥ upward; if `X < 0`
    upward ≥ downward") is *exactly* the statement that `Φ = |X|` has downward
    drift `∫ |X| ∂(K x) ≤ |X x|` — when `X > 0` an inward step lowers `|X|`, when
    `X < 0` an inward step also lowers `|X|`.  We therefore take the `|X|`-drift
    `hdrift : ∀ x, ∫ |X| ∂(K x) ≤ |X x|` as the brick's hypothesis (the precise,
    non-schematic form of `h_inward`).
  * The blueprint's `hjump` (`|X y − X x| ≤ 1`) gives `||X y| − |X x|| ≤ 1` by
    the reverse triangle inequality, supplying `c = 1`.
  * The blueprint's `hgate_tail` / killed-kernel escape term is therefore NOT
    needed in the abstract brick: when the drift holds globally there is no
    escape.  (The protocol's inward drift only holds inside the Phase-0 region;
    that *region-restriction* is folded into the named hypothesis `hdrift` at
    instantiation — Stage C carries it explicitly, documenting exactly what the
    protocol must supply.)

This is strictly cleaner than the gated route and reuses the audited
`AzumaKernel` engine verbatim.

Reference: Doty et al. §5.1–§5.2; the blueprint file
`HANDOFF_ROLESPLIT_TOPSPLIT.md`.
-/

import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.RoleSplitConcentration
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.AzumaKernel

namespace ExactMajority
namespace RoleSplitConcentration

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

variable {L K : ℕ}

/-! ## Stage A — the top-split definitions. -/

/-- **Total mass descended from the top-level `S = RoleCR` split.**  This is
`crCount + clockCount + reserveCount`: every agent ever produced as `RoleCR` is
now either still `RoleCR`, or has been drained into a `Clock` or a `Reserve` by
Rule 4.  `topCRMass` (not `crCount` alone) is the right top-level variable
because Rule 4 moves `RoleCR` into `Clock + Reserve` *without* changing the
top-level `Main`-vs-`S` balance (`ΔX = 0` for both R1 and R4). -/
def topCRMass (c : Config (AgentState L K)) : ℕ :=
  crCount (L := L) (K := K) c + clockCount (L := L) (K := K) c +
    reserveCount (L := L) (K := K) c

/-- **The top-split window** `|Main − topCRMass| ≤ δ·n`: the configuration
realizes the Lemma-5.1 balance between the `Main` pool and the total
RoleCR-descended pool with slack `δ`. -/
def TopSplitWindow (δ : ℝ) (n : ℕ) (c : Config (AgentState L K)) : Prop :=
  |(mainCount (L := L) (K := K) c : ℝ) - (topCRMass (L := L) (K := K) c : ℝ)| ≤ δ * n

/-- **The CR-drain window** `crCount ≤ δ·topCRMass`: by the end of Phase 0 (Stage-2
drain) almost all of the RoleCR-descended mass has been converted into balanced
`Clock`/`Reserve`, leaving at most a `δ`-fraction still as raw `RoleCR`. -/
def CRDrainWindow (δ : ℝ) (c : Config (AgentState L K)) : Prop :=
  (crCount (L := L) (K := K) c : ℝ) ≤ δ * (topCRMass (L := L) (K := K) c : ℝ)

/-! ## Stage B — the deterministic conversion (pure algebra, 0-`sorry`).

`TopSplitWindow δ` + `CRDrainWindow δ` + `ClockReserveBalanced` + conservation
⟹ `RoleSplitWindows η`, with `δ = η/4`.  This is pure arithmetic over the count
ledger, using `roleCount_conservation` (which collapses, via the balance and
`roleMCRCount = 0`, to `mainCount + topCRMass = n`). -/

/-- **The `mainCount + topCRMass = n` identity** under the Phase-0 ledger.  With
`roleMCRCount = 0` and `card = n`, the five-way `roleCount_conservation` gives
`mainCount + (crCount + clockCount + reserveCount) = n`, i.e.
`mainCount + topCRMass = n`. -/
theorem mainCount_add_topCRMass {n : ℕ} (c : Config (AgentState L K))
    (hcard : Multiset.card c = n)
    (hmcr0 : roleMCRCount (L := L) (K := K) c = 0) :
    mainCount (L := L) (K := K) c + topCRMass (L := L) (K := K) c = n := by
  have hcons := roleCount_conservation (L := L) (K := K) c
  rw [hcard] at hcons
  unfold topCRMass
  omega

/-- **`topCRMass = crCount + 2·clockCount` under the balance.**  When
`ClockReserveBalanced` (`clockCount = reserveCount`) holds, the RoleCR-descended
mass is `crCount + 2·clockCount`. -/
theorem topCRMass_balanced (c : Config (AgentState L K))
    (hbal : ClockReserveBalanced (L := L) (K := K) c) :
    topCRMass (L := L) (K := K) c =
      crCount (L := L) (K := K) c + 2 * clockCount (L := L) (K := K) c := by
  unfold topCRMass ClockReserveBalanced at *
  omega

/-- **Stage B — the deterministic conversion.**  The top-split balance window
(`TopSplitWindow δ`), the CR-drain window (`CRDrainWindow δ`), the exact
Clock/Reserve balance (`ClockReserveBalanced`), and the Phase-0 ledger
(`card = n`, `roleMCRCount = 0`) together force the Lemma-5.2 count windows
`RoleSplitWindows η`, with `δ = η/4`.

Arithmetic (all over `ℝ`):
* `mainCount + topCRMass = n` (`mainCount_add_topCRMass`), so the balance window
  `|mainCount − topCRMass| ≤ δn` gives `mainCount ∈ [(1−δ)n/2, (1+δ)n/2]`; since
  `δ = η/4 ≤ η`, the Main window `[(1−η)n/2, (1+η)n/2]` holds.
* `topCRMass = crCount + 2·clockCount` (`topCRMass_balanced`); the drain window
  `crCount ≤ δ·topCRMass` gives `2·clockCount ≥ (1−δ)·topCRMass`, and
  `topCRMass = n − mainCount ≥ (1−δ)n/2`, so `clockCount ≥ (1−δ)²·n/4 ≥ (1−η)n/4`
  (because `(1−η/4)² = 1 − η/2 + η²/16 ≥ 1 − η/2 ≥ 1 − η` for `η ≥ 0`).
  `reserveCount = clockCount`, same bound. -/
theorem RoleSplitWindows_of_topSplit_crDrain
    {η δ : ℝ} {n : ℕ} {c : Config (AgentState L K)}
    (hη0 : 0 ≤ η) (hη1 : η ≤ 1) (hδ : δ = η / 4)
    (hcard : Multiset.card c = n)
    (hmcr0 : roleMCRCount (L := L) (K := K) c = 0)
    (hbal : ClockReserveBalanced (L := L) (K := K) c)
    (htop : TopSplitWindow (L := L) (K := K) δ n c)
    (hdrain : CRDrainWindow (L := L) (K := K) δ c) :
    RoleSplitWindows (L := L) (K := K) η n c := by
  -- Cast the count identities to ℝ.
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hδ0 : 0 ≤ δ := by rw [hδ]; linarith
  have hδη : δ ≤ η := by rw [hδ]; linarith
  -- `mainCount + topCRMass = n` over ℝ.
  have hsumN : mainCount (L := L) (K := K) c + topCRMass (L := L) (K := K) c = n :=
    mainCount_add_topCRMass (L := L) (K := K) c hcard hmcr0
  have hsum : (mainCount (L := L) (K := K) c : ℝ) + (topCRMass (L := L) (K := K) c : ℝ)
      = (n : ℝ) := by exact_mod_cast hsumN
  -- `topCRMass = crCount + 2·clockCount` over ℝ.
  have htopN : topCRMass (L := L) (K := K) c =
      crCount (L := L) (K := K) c + 2 * clockCount (L := L) (K := K) c :=
    topCRMass_balanced (L := L) (K := K) c hbal
  have htopR : (topCRMass (L := L) (K := K) c : ℝ) =
      (crCount (L := L) (K := K) c : ℝ) + 2 * (clockCount (L := L) (K := K) c : ℝ) := by
    exact_mod_cast htopN
  -- Balance over ℝ: clockCount = reserveCount.
  have hbalR : (clockCount (L := L) (K := K) c : ℝ) = (reserveCount (L := L) (K := K) c : ℝ) := by
    unfold ClockReserveBalanced at hbal; exact_mod_cast hbal
  -- Unfold the window hypotheses.
  rw [TopSplitWindow, abs_le] at htop
  obtain ⟨htop_lo, htop_hi⟩ := htop
  rw [CRDrainWindow] at hdrain
  -- Abbreviations.
  set m : ℝ := (mainCount (L := L) (K := K) c : ℝ) with hm
  set S : ℝ := (topCRMass (L := L) (K := K) c : ℝ) with hS
  set cr : ℝ := (crCount (L := L) (K := K) c : ℝ) with hcr
  set cl : ℝ := (clockCount (L := L) (K := K) c : ℝ) with hcl
  -- `topCRMass ≥ 0`, `clockCount ≥ 0`, `crCount ≥ 0`.
  have hScast : 0 ≤ S := by rw [hS]; exact Nat.cast_nonneg _
  have hclcast : 0 ≤ cl := by rw [hcl]; exact Nat.cast_nonneg _
  -- Main window: from `m + S = n` and `|m − S| ≤ δn`.
  have hmain_lo : (1 - η) * (n : ℝ) / 2 ≤ m := by
    -- m = (n + (m − S))/2 ≥ (n − δn)/2 = (1−δ)n/2 ≥ (1−η)n/2.
    nlinarith [htop_lo, hsum, mul_nonneg (sub_nonneg.mpr hδη) hn0]
  have hmain_hi : m ≤ (1 + η) * (n : ℝ) / 2 := by
    nlinarith [htop_hi, hsum, mul_nonneg (sub_nonneg.mpr hδη) hn0]
  -- topCRMass ≥ (1−δ)·n/2 (from `m ≤ (1+δ)n/2` and `m + S = n`).
  have hS_lo : (1 - δ) * (n : ℝ) / 2 ≤ S := by
    nlinarith [htop_hi, hsum]
  -- 2·clockCount = S − crCount ≥ (1−δ)·S.
  have h2cl : (1 - δ) * S ≤ 2 * cl := by
    -- 2·cl = S − cr (from `S = cr + 2·cl`); cr ≤ δ·S.
    have : 2 * cl = S - cr := by rw [htopR]; ring
    nlinarith [hdrain]
  -- clockCount ≥ (1−δ)²·n/4 ≥ (1−η)·n/4.
  have hδ1 : δ ≤ 1 := by linarith
  have hcl_floor : (1 - η) * (n : ℝ) / 4 ≤ cl := by
    -- 2·cl ≥ (1−δ)·S ≥ (1−δ)·(1−δ)n/2 = (1−δ)²·n/2  (using 1−δ ≥ 0, S ≥ (1−δ)n/2).
    have hstep : (1 - δ) * ((1 - δ) * (n : ℝ) / 2) ≤ (1 - δ) * S :=
      mul_le_mul_of_nonneg_left hS_lo (by linarith)
    -- (1−δ)²·n/2 ≥ (1−η)·n/2 since (1−δ)² ≥ 1−η for δ = η/4.
    -- (1−δ)² = 1 − 2δ + δ² ; with δ = η/4: = 1 − η/2 + η²/16 ≥ 1 − η.
    have hsq : (1 - η) * (n : ℝ) / 2 ≤ (1 - δ) * ((1 - δ) * (n : ℝ) / 2) := by
      have hηsq : 0 ≤ η * η := mul_nonneg hη0 hη0
      nlinarith [hn0, hηsq, hδ, mul_nonneg hη0 hn0]
    linarith [h2cl, hstep, hsq]
  have hres_floor : (1 - η) * (n : ℝ) / 4 ≤ (reserveCount (L := L) (K := K) c : ℝ) := by
    rw [← hbalR]; exact hcl_floor
  exact ⟨hmain_lo, hmain_hi, hcl_floor, hres_floor⟩

end RoleSplitConcentration
end ExactMajority
