# F5 Bridge Architecture Design

_Created 2026-04-29 after C3.  This note is for future dispatchers working on
the Apéry F5 conifold estimate._

## Why split

The original downstream F5 hypothesis,
`AperyConifoldThreeHalvesBound`, is defined in `ApreyBounded.lean:350`.
It says that along an 8-variable Apéry PIVP solution,

```text
|rho(t) - zeta(3)| <= K * |z1 - z(t)| * sqrt |z1 - z(t)|.
```

This single Prop bundles several different concerns:

1. Frobenius series asymptotics at the conifold.
2. PIVP coordinate tracking.
3. Compact transient handling before the trajectory enters the local
   Frobenius window.

`F5Bridge.lean` separates these layers.  Its head comment at
`F5Bridge.lean:5-21` records the intended split and clarifies that the PIVP
uses the implemented second-derivative analytic ratio `B''(z)/A''(z)`, not
the undifferentiated ratio `B(z)/A(z)`.

The purpose of the split is not to hide analysis.  It makes each analytic
claim a separately named target and keeps the downstream PIVP theorem honest:
closed glue stays closed, hard conifold/connection-coefficient content remains
visible.

## Main objects

### Downstream F5 hypothesis

`AperyConifoldThreeHalvesBound` is in `ApreyBounded.lean:350-357`.
It is trajectory-level:

```text
forall t >= 0,
  |sol.trajectory t iR - zeta(3)|
    <= K32 * |z1 - sol.trajectory t iZ| * sqrt |z1 - sol.trajectory t iZ|.
```

`apery_three_halves_bound_exponential` at `ApreyBounded.lean:362-430`
then combines this with scalar exponential convergence of `z(t)` to obtain
exponential convergence of `rho(t)` to `zeta(3)`.

### Analytic ratio

`F5Bridge.lean` locally defines the differentiated generating functions:

| Name | Line | Meaning |
|------|------|---------|
| `aperyF5GFASecondReal` | 380 | real series for `A''(z)` |
| `aperyF5GFBSecondReal` | 385 | real series for `B''(z)` |
| `aperyF5AnalyticRatio` | 440 | `B''(z) / A''(z)` |

The local `aperyF5*` copies exist because `ApreyBounded.lean` and
`AperySequences.lean` currently collide on exported names such as
`Ripple.Number.aperyQ`; see `F5Bridge.lean:38-42`.

### Three ratio-bound Props

`F5Bridge.lean` distinguishes three scopes of the same analytic estimate:

| Prop | Line | Scope |
|------|------|-------|
| `AperyFrobeniusRatioBound` | 919 | local conifold window, for `z` near `z1` |
| `AperyFrobeniusRatioBoundGlobalized` | 930 | all `0 < z < z1` |
| `AperyFrobeniusRatioBoundAlong` | 1279 | only points `z(t)` on one PIVP trajectory |

The distinction matters:

- The local Prop is the natural Frobenius/Birkhoff theorem.
- The globalized Prop is convenient for pure triangle-inequality downstream
  glue, but it requires a compactness bound away from the conifold.
- The along-trajectory Prop is weaker than globalized and is enough for
  `AperyConifoldThreeHalvesBound`; it uses scalar F6 to enter the local window
  and compactness only on the finite pre-entry trajectory segment.

### PIVP tracking Prop

`AperyPIVPRatioTracking` is defined at `F5Bridge.lean:1193-1201`.  It says
that the PIVP coordinate `rho(t)` follows the analytic ratio `B''/A''` in the
same `3/2` scale.  This is logically separate from the Frobenius asymptotic of
the analytic ratio itself.

## Layer 1: pure analytic side

This layer proves facts about `A''`, `B''`, and their ratio as real functions
on the conifold disk.

Closed facts in `F5Bridge.lean`:

| Fact | Lines | Content |
|------|-------|---------|
| `aperyF5A_le_pow_conifold` | 333 | crude `a_n <= R^n` growth |
| `aperyF5ConifoldZ1_eq_inv_R` | 345 | `z1 = 1 / (17 + 12 sqrt 2)` |
| `aperyF5GFASecondReal_summable` | 391 | summability of `A''` inside disk |
| `aperyF5GFASecondReal_pos` | 448 | `A''(z) > 0` for `0 < z < z1` |
| `aperyF5GFASecondReal_continuousOn` | 474 | continuity of `A''` on `(0,z1)` |
| `aperyF5B_abs_le_aperyF5A` | 604 | crude `|b_n| <= (2n+1) a_n` |
| `aperyF5GFBSecondReal_summable` | 640 | summability of `B''` inside disk |
| `aperyF5GFBSecondReal_continuousOn` | 722 | continuity of `B''` on `(0,z1)` |
| `aperyF5GFASecondReal_continuousOn_Icc_zero` | 775 | `A''` continuity on `[0,b]` |
| `aperyF5GFBSecondReal_continuousOn_Icc_zero` | 805 | `B''` continuity on `[0,b]` |
| `aperyF5GFASecondReal_pos_nonneg` | 839 | `A''(z) > 0` also at `z=0` |
| `aperyF5AnalyticRatio_continuousOn_Icc_zero` | 866 | ratio continuity on `[0,b]` |
| `aperyF5AnalyticRatio_continuousOn` | 877 | ratio continuity on `(0,z1)` |
| `aperyF5AnalyticRatio_error_bdd_on_Icc` | 889 | compact bound on ratio error |

The closed preconifold theorem
`aperyFrobeniusRatioPreconifoldBound_from_series_continuity` at
`F5Bridge.lean:951` turns these ordinary continuity facts into a uniform
bound away from the conifold endpoint.

## Layer 2: PIVP tracking side

This layer relates the analytic ratio to the PIVP state.

The remaining high-level hypothesis is:

```lean
def AperyPIVPRatioTracking
    (init : Fin 8 -> Q)
    (sol : PIVP.Solution (apery8VarPolyPIVP init).toPIVP) : Prop
```

at `F5Bridge.lean:1193`.  It states:

```text
|rho(t) - analyticRatio(z(t))|
  <= K_track * |z1 - z(t)| * sqrt |z1 - z(t)|.
```

Once this Prop and a Frobenius ratio bound are supplied, the downstream
triangle-inequality bridge is closed:

| Theorem | Lines | Inputs |
|---------|-------|--------|
| `aperyConifoldThreeHalvesBound_of_global_split` | 1207 | globalized Frobenius + tracking + disk invariant |
| `aperyConifoldThreeHalvesBound_of_along_split` | 1293 | along-trajectory Frobenius + tracking |
| `aperyConifoldThreeHalvesBound_of_split` | 1552 | local Frobenius + tracking + F6/compactness |

The tracking Prop is not the same as the connection-coefficient problem.  The
connection-coefficient problem identifies analytic generating functions near
the conifold.  Tracking is about the implemented 8-variable ODE coordinates
following that analytic ratio along a solution.

## Layer 3: compact transient and globalization

The local Frobenius estimate only applies once `z(t)` is close to `z1`.
F5Bridge already closes the local-to-global trajectory mechanics:

| Theorem | Lines | Role |
|---------|-------|------|
| `aperyFrobeniusRatioBoundGlobalized_of_local_and_preconifold` | 1090 | local + preconifold bound -> full disk |
| `aperyFrobeniusRatioBoundGlobalized_scaffold` | 1172 | globalized scaffold from local C-tier theorem + preconifold theorem |
| `aperyFrobeniusRatioBound_of_globalized` | 1179 | full disk -> local |
| `aperyF5_z_coordinate_continuousOn_Icc` | 1331 | z-coordinate continuity on compact time intervals |
| `aperyF5_exp_decay_eventually_below` | 1348 | exponential envelope enters any positive window |
| `aperyF5Trajectory_prewindow_Icc_bounds` | 1379 | compact prewindow z-image lies in `[a,b] subset (0,z1)` |
| `aperyF5Trajectory_local_F6_compact_along_bound` | 1420 | local Frobenius + F6 + compact prewindow -> along bound |
| `aperyFrobeniusRatioBound_along_of_local_F6_compact` | 1526 | wrapper for the previous theorem |

Mathematically, the proof splits time into two regions:

1. Tail: scalar F6 makes `z1 - z(t)` smaller than the local `delta`, so the
   local Frobenius estimate applies directly.
2. Transient: compactness of `z([0,T0])` gives a positive distance from `z1`,
   and continuity bounds the analytic ratio error by a finite constant.  The
   positive distance converts this constant into the same `3/2` scale.

No hard Frobenius analysis remains in this layer.

## Layer 4: Birkhoff sub-step decomposition

C3 decomposes the hard local conifold theorem into five named substeps.
The top theorem `aperyFrobeniusRatioBound_from_ratio_family_and_birkhoff` at
`F5Bridge.lean:1079` is now closed composition, not a black-box `sorry`.

### Step a: coefficient control from ratio-bound family

Lean target:

```lean
theorem aperyRatioBound_step_a_ratio_family_coefficient_control :
    AperyFrobeniusRatioFamilyCoefficientControl
```

Location: `F5Bridge.lean:1026`.  Status: `sorry`.

Current interface is intentionally weak:

```lean
def AperyFrobeniusRatioFamilyCoefficientControl : Prop :=
  exists C : R, 0 < C
```

The first real task is to replace this placeholder with the weakest useful
concrete statement.  Source lemmas in `AperyGeneratingFunction.lean` include:

| Lemma | Line |
|-------|------|
| `aperyFrobenius_half_ratio_bound` | 20692 |
| `aperyFrobenius_half_coeff_growth_bound` | 20766 |
| `aperyFrobenius_half_tendsto_at_zero` | 20874 |
| `aperyFrobenius_one_ratio_bound` | 22305 |
| `aperyFrobenius_one_coeff_growth_bound` | 22393 |
| `aperyFrobenius_one_tendsto_at_zero` | 22422 |
| `aperyFrobenius_zero_ratio_bound` | 22485 |
| `aperyFrobenius_zero_coeff_growth_bound` | 22572 |
| `aperyFrobenius_zero_tendsto_at_zero` | 22601 |

Estimated difficulty: 1-3 days if the interface is chosen conservatively.

### Step b: Birkhoff residual sharp asymptotics

Lean target:

```lean
theorem aperyRatioBound_step_b_birkhoff_residual_sharp_asymptotics
    (_hcoef : AperyFrobeniusRatioFamilyCoefficientControl) :
    AperyFrobeniusBirkhoffResidualSharpAsymptotics
```

Location: `F5Bridge.lean:1034`.  Status: `sorry`.

Relevant existing source lemmas:

| Lemma | Line |
|-------|------|
| `aperyAlphaInf_z1_identity` | 21509 |
| `aperyAlphaInf_z1_double_root` | 21539 |
| `aperyBirkhoffResidualHalf_recurrence` | 21771 |
| `aperyBirkhoffResidualZero_recurrence` | 21966 |
| `aperyBetaInf_z1_birkhoff_L` | 22186 |
| `aperyConifold_birkhoff_ansatz_preserved` | 22224 |
| `aperyBirkhoffResidualOne_recurrence` | 22280 |

Mathematical content: prove that each conifold Frobenius branch has a sharp
enough expansion near `z1` after subtracting the preserved Birkhoff ansatz.
The hard point is cancellation in the dominant double-root sector; naive
triangle bounds are too weak.

Estimated difficulty: 1-2 weeks.

### Step c: connection coefficients

Lean target:

```lean
theorem aperyRatioBound_step_c_connection_coefficients
    (_hbirk : AperyFrobeniusBirkhoffResidualSharpAsymptotics) :
    AperyFrobeniusConnectionCoefficientIdentification
```

Location: `F5Bridge.lean:1042`.  Status: `sorry`.

Mathematical content: identify the ordinary Apéry generating functions `A`
and `B` as linear combinations of the three local conifold branches.  The
key cancellation is in the numerator `B - zeta(3) A`, and after
differentiating in `F5Bridge` it becomes `B'' - zeta(3) A''`.

This is the most delicate part because the connection coefficients are not
expected to be algebraic.  `UNDERSTANDING.md` records older branch-basis and
Cramer-rule scaffolding in `AperyInstance.lean`, including the predicate
`IsAperyConnectionCoeffsOn` and finite-witness uniqueness APIs.

Estimated difficulty: 1-3 weeks for architecture, potentially longer for a
fully unconditional proof.

### Step d: series-to-numerator transfer

Lean target:

```lean
theorem aperyRatioBound_step_d_series_to_differentiated_numerator
    (_hcoef : AperyFrobeniusRatioFamilyCoefficientControl)
    (_hbirk : AperyFrobeniusBirkhoffResidualSharpAsymptotics)
    (_hconn : AperyFrobeniusConnectionCoefficientIdentification) :
    AperyF5DifferentiatedNumeratorThreeHalvesBound
```

Location: `F5Bridge.lean:1049`.  Status: `sorry`.

Mathematical content: combine coefficient growth, branch asymptotics, and
connection coefficients to prove the numerator estimate

```text
|B''(z) - zeta(3) A''(z)|
  <= K * |z1-z| * sqrt |z1-z| * A''(z).
```

The target Prop is `AperyF5DifferentiatedNumeratorThreeHalvesBound` at
`F5Bridge.lean:1014`.

Estimated difficulty: several days after steps a-c are concrete.

### Step e: numerator-to-ratio algebra

Lean target:

```lean
theorem aperyRatioBound_step_e_ratio_bound_of_numerator
    (hnum : AperyF5DifferentiatedNumeratorThreeHalvesBound) :
    AperyFrobeniusRatioBound
```

Location: `F5Bridge.lean:1058`.  Status: closed.

This is pure algebra: divide by `A''(z)`, using positivity from
`aperyF5GFASecondReal_pos` at `F5Bridge.lean:448`.

Estimated difficulty: done.

## Dependencies

### Dependency chain

```text
AperyGeneratingFunction ratio_bound family
  -> C step a: coefficient control
  -> C step b: Birkhoff residual sharp asymptotics
  -> C step c: connection coefficients
  -> C step d: differentiated numerator bound
  -> C step e: local AperyFrobeniusRatioBound
  -> local + preconifold continuity: AperyFrobeniusRatioBoundGlobalized
  -> globalized/along Frobenius + AperyPIVPRatioTracking
  -> AperyConifoldThreeHalvesBound
  -> ApreyBounded exponential convergence theorem
```

### Table view

| Output | Depends on | Status |
|--------|------------|--------|
| `AperyFrobeniusRatioPreconifoldBound` | `A''/B''` continuity and `A'' > 0` | closed |
| `AperyFrobeniusRatioBound` | C steps a-e | open via a-d |
| `AperyFrobeniusRatioBoundGlobalized` | local bound + preconifold bound | closed composition |
| `AperyFrobeniusRatioBoundAlong` | local bound + scalar F6 + compact transient | closed composition |
| `AperyConifoldThreeHalvesBound` | along/globalized Frobenius + PIVP tracking | closed composition |
| Exponential convergence of `rho(t)` | `AperyConifoldThreeHalvesBound` + scalar F6 | closed in `ApreyBounded.lean` |

## Open problems by layer

### Analytic side

Open: C steps a-d.

Closed: summability, continuity, positivity, compact preconifold bounds,
globalized/along glue.

### PIVP side

Open: `AperyPIVPRatioTracking`.

This should be attacked only after deciding whether tracking is meant to be
proved from the actual 8-variable ODE equations or treated as a separate
connection/implementation theorem.  The present split makes either choice
explicit.

### Generic Frobenius framework

Open: generic regular-singular local theory.  This is larger than F5 and
should not block the Apéry-specific C-tier dispatch unless the dispatcher is
explicitly assigned generic infrastructure.

## Recommended dispatch order

1. **Normalize the C-step interfaces.**  Replace the dummy `exists C, C>0`
   Props by concrete, minimal statements.  Start with step a because the
   closed ratio-bound family already exists.
2. **Import or bridge `AperyGeneratingFunction.lean` carefully.**  The current
   F5Bridge file does not import it.  If importing causes name or build issues,
   create a small intermediate bridge file rather than moving large code.
3. **Close step a.**  It should be mostly translation from existing
   `ratio_bound`, `coeff_growth_bound`, and `tendsto_at_zero` theorems.
4. **Work step b in scratch first.**  The Birkhoff cancellation is the first
   genuinely hard estimate.  Keep the final interface narrow.
5. **Only then work step c.**  Connection coefficients are likely the longest
   path.  Use the `AperyInstance.lean` APIs recorded in `UNDERSTANDING.md`.
6. **Close step d mechanically after a-c.**  This is expected to be assembly,
   differentiation bookkeeping, and comparison to `A''`.
7. **Return to `AperyPIVPRatioTracking`.**  This is required for the full PIVP
   F5 theorem after the analytic local estimate is available.

## What not to do

- Do not reintroduce a monolithic F5 `sorry`; keep substeps named.
- Do not use axioms for C-tier estimates.
- Do not claim the Apéry series route is fully formalized while
  `AperyPIVPRatioTracking` or C steps remain hypotheses/sorries.
- Do not conflate `B/A` with the implemented `B''/A''` ratio.
- Do not spend generic-framework time inside an Apéry-specific dispatch unless
  the task explicitly asks for that infrastructure.
