# Frobenius Framework Inventory

_Last updated 2026-04-29 after C3/C4.  Authoritative for the F5 split route
as of commit `6d760a1b`; subordinate to root `STRATEGY.md`._

## Top-level picture

Per `STRATEGY.md`, the Frobenius / regular-singular local theory is the
long-term strategic route for holonomic period constants.  For the Apéry
series route, the present Lean state is:

| Step | Apéry-specific status | Generic status |
|------|-----------------------|----------------|
| 1. Formal substitution | Closed in `Substitution.lean` and used by `AperyGeneratingFunction.lean` | partial |
| 2. Indicial polynomial | Closed for Apéry conifold roots `{0, 1/2, 1}` | not done |
| 3. Local Frobenius branches | Ratio-bound family closed in `AperyGeneratingFunction.lean` | not done |
| 4. Integer-gap/log cases | not needed for this Apéry conifold use | not done |
| 5. F4/F5 application | F5 split and downstream glue in `F5Bridge.lean`; analytic C-tier still open | n/a |

The canonical closed ζ(3) route remains `AperyFermi.lean`.  The Apéry series
route is now a transparent conditional route, not an end-to-end theorem.

## File-by-file status

### Substitution.lean

Apéry-specific Taylor shift and formal substitution into the Apéry ODE.
Sorry-free; still not generic regular-singular infrastructure.

### Indicial.lean / AperyConifoldIndicial.lean

Indicial wrapper plus concrete Apéry conifold root calculation.  The roots
are proved to be `0`, `1/2`, and `1`.

### CompanionMatrix.lean, Falling.lean, RegularDisk.lean, PoincaréPerron.lean

Supporting Frobenius algebra, disk-convergence, and recurrence asymptotic
infrastructure.  No current F5 blocker here.

### AperyGeneratingFunction.lean

Large analytic-side file.  Current relevant closed facts:

| Item | Lines | Status |
|------|-------|--------|
| `aperyFrobenius_half_ratio_bound` | 20692 | closed |
| `aperyFrobenius_half_coeff_growth_bound` | 20766 | closed |
| `aperyFrobenius_half_tendsto_at_zero` | 20874 | closed |
| `aperyAlphaInf_z1_identity` | 21509 | closed |
| `aperyAlphaInf_z1_double_root` | 21539 | closed |
| `aperyBirkhoffResidualHalf_recurrence` | 21771 | closed |
| `aperyBirkhoffResidualZero_recurrence` | 21966 | closed |
| `aperyBetaInf_z1_birkhoff_L` | 22186 | closed |
| `aperyConifold_birkhoff_ansatz_preserved` | 22224 | closed |
| `aperyBirkhoffResidualOne_recurrence` | 22280 | closed |
| `aperyFrobenius_one_ratio_bound` | 22305 | closed |
| `aperyFrobenius_one_coeff_growth_bound` | 22393 | closed |
| `aperyFrobenius_one_tendsto_at_zero` | 22422 | closed |
| `aperyFrobenius_zero_ratio_bound` | 22485 | closed |
| `aperyFrobenius_zero_coeff_growth_bound` | 22572 | closed |
| `aperyFrobenius_zero_tendsto_at_zero` | 22601 | closed |

This file is the intended source for C-tier step a/b, but `F5Bridge.lean`
does not currently import it.

### AperyInstance.lean

Connection-coefficient structural API for conifold branches.  See
`UNDERSTANDING.md` for the older branch-basis and Cramer-rule scaffolding.

### F5Bridge.lean

Current F5 architecture file.  Head comment at lines 5-21 states the split:
Frobenius/series-level estimate plus trajectory-level PIVP tracking.  It uses
the second-derivative ratio `B''(z)/A''(z)` matching the implemented PIVP.

| Item | Lines | Status |
|------|-------|--------|
| local replicas `aperyF5A`, `aperyF5B`, `aperyF5GFASecondReal`, `aperyF5GFBSecondReal` | 46, 365, 380, 385 | closed defs |
| `aperyF5GFASecondReal_summable`, `aperyF5GFBSecondReal_summable` | 391, 640 | closed |
| `aperyF5GFASecondReal_pos` | 448 | closed |
| `aperyF5GFASecondReal_continuousOn`, `aperyF5GFBSecondReal_continuousOn` | 474, 722 | closed |
| `aperyF5AnalyticRatio_continuousOn`, `_error_bdd_on_Icc` | 877, 889 | closed |
| `AperyFrobeniusRatioBound` | 919 | local conifold Prop |
| `AperyFrobeniusRatioBoundGlobalized` | 930 | full-disk Prop |
| `AperyFrobeniusRatioPreconifoldBound_from_series_continuity` | 951 | closed |
| C3 step a coefficient-control theorem | 1026 | `sorry` |
| C3 step b Birkhoff sharp-asymptotic theorem | 1034 | `sorry` |
| C3 step c connection-coefficient theorem | 1042 | `sorry` |
| C3 step d numerator-transfer theorem | 1049 | `sorry` |
| C3 step e numerator-to-ratio theorem | 1058 | closed |
| `aperyFrobeniusRatioBound_from_ratio_family_and_birkhoff` | 1079 | closed composition of a-e |
| `aperyFrobeniusRatioBoundGlobalized_of_local_and_preconifold` | 1090 | closed |
| `aperyFrobeniusRatioBoundGlobalized_scaffold` | 1172 | closed composition |
| `AperyPIVPRatioTracking` | 1193 | remaining PIVP-tracking hypothesis Prop |
| `aperyConifoldThreeHalvesBound_of_global_split` | 1207 | closed |
| `AperyFrobeniusRatioBoundAlong` | 1279 | trajectory-local Prop |
| `aperyConifoldThreeHalvesBound_of_along_split` | 1293 | closed |
| compact/F6 local-to-global trajectory lemmas | 1331-1526 | closed |
| `aperyConifoldThreeHalvesBound_of_split` | 1552 | closed |

### ApreyBounded.lean

`AperyConifoldThreeHalvesBound` is the downstream F5 hypothesis at lines
350-357.  Its exponential upgrade is closed in
`apery_three_halves_bound_exponential` at lines 362-430.  F5Bridge supplies
closed implications from split hypotheses back to this Prop.

## Open sorries

_(updated post-C7/C8: namespace fix + step_a/step_b substantive Props closed)_

| Sorry | File | Difficulty | Notes |
|-------|------|------------|-------|
| `aperyRatioBound_step_a_ratio_family_coefficient_control` | ~~F5Bridge.lean:1026~~ | ✅ CLOSED (C7) | Substantive Prop using AperyGenFunc lemmas |
| `aperyRatioBound_step_b_birkhoff_residual_sharp_asymptotics` | ~~F5Bridge.lean:1034~~ | ✅ CLOSED (C8) | Substantive Prop using BirkhoffResidual + AlphaInf lemmas |
| `aperyRatioBound_step_c_connection_coefficients` | `F5Bridge.lean:~1042` | 1-3 weeks | Need new connection-coefficient lemma; AperyInstance has structural API but no closed identification of A/B branch coefficients |
| `aperyRatioBound_step_d_series_to_differentiated_numerator` | `F5Bridge.lean:~1049` | several days after step_c | Transfer to numerator estimate; depends on substantive step_c output |
| `chudnovsky_one_over_pi` | `Chudnovsky1989.lean:169` | 1-3 months | Separate π identity project |
| `theorem_main` | `Ramanujan1914.lean:179` | 1-3 months | Separate π identity project |

Apéry F5 Lean code has exactly two active F5Bridge sorries, both real
mathematical content (connection coefficients + numerator transfer).
B-side continuity, summability, positivity, compact transient, and
local/global glue are closed. Steps a/b now have substantive Props
referencing the closed AperyGeneratingFunction infrastructure.

## Hypothesis-pushed Props

| Prop | Defined in | Role |
|------|------------|------|
| `AperyFrobeniusRatioBound` | `F5Bridge.lean:919` | local analytic `3/2` conifold estimate |
| `AperyFrobeniusRatioBoundGlobalized` | `F5Bridge.lean:930` | full disk version, derived from local + preconifold bound |
| `AperyFrobeniusRatioBoundAlong` | `F5Bridge.lean:1279` | local estimate restricted to a trajectory |
| `AperyPIVPRatioTracking` | `F5Bridge.lean:1193` | PIVP `ρ` coordinate tracks `B''/A''` |
| `AperyConifoldThreeHalvesBound` | `ApreyBounded.lean:350` | downstream F5 hypothesis implied by F5Bridge split |

## Suggested attack order

1. **C step a:** replace `AperyFrobeniusRatioFamilyCoefficientControl` with
   the weakest concrete statement needed from
   `aperyFrobenius_{zero,half,one}_{ratio_bound,coeff_growth_bound,tendsto_at_zero}`.
2. **C step b:** formalize the Birkhoff sharp asymptotic using
   `aperyBirkhoffResidual{Zero,Half,One}_recurrence` and
   `aperyConifold_birkhoff_ansatz_preserved`.
3. **C step c:** connect ordinary `A,B` to the conifold Frobenius branch basis.
   This is the most mathematical/transcendental part.
4. **C step d:** package the previous outputs into the differentiated numerator
   bound `AperyF5DifferentiatedNumeratorThreeHalvesBound`.
5. **PIVP tracking:** discharge `AperyPIVPRatioTracking` if the goal is to
   remove all F5 hypotheses from the PIVP theorem.
6. Generic Frobenius graduation: only after F5 architecture stabilizes.

## Numerical backing

| Hypothesis | Numerical experiment | Status |
|------------|----------------------|--------|
| F5 / `3/2` asymptotic | `experiments/apery_8var_pivp.py` | slope about 1.502 in commit `1ff239c3` |

## Recent progress log

| Commit | Tier | Description |
|--------|------|-------------|
| `b1373944` | A2 | sequence-level `aperyB/aperyA -> ζ(3)` Tendsto |
| `1ff239c3` | numerics | 8-var PIVP validates the `3/2` conifold rate |
| `cb581cd3` | B1 | split F5 into Frobenius series + PIVP tracking pieces |
| `817a5a92` | B2 | downstream theorem wired through F5Bridge |
| `d3fac32f` | B3 | localized F5 sorry to analyticity infrastructure |
| `97014071` | B4 | decomposed analyticity into named sub-lemmas |
| `2b45bbff` | B5 | closed trajectory compactness sub-sorry |
| `2aa24834` | B6 | closed A-side positivity/summability infra |
| `6bd62423` | B7 | closed A'' continuity |
| `7fd4a026` | B8 | closed B'' summability/continuity except final bound |
| `3278140d` | B9 | closed final F5Bridge B-side bound |
| `9559df75` | C1 | scaffolded globalized ratio-bound split and fixed AGF build break |
| `d5d6a95d` | C2 | closed preconifold compactness/continuity branch |
| `6d760a1b` | C3 | decomposed hard Birkhoff step into 5 named substeps; step e closed |
