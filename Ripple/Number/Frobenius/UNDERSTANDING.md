# Ripple/Number/Frobenius — UNDERSTANDING

Snapshot of the structural state of the Apéry conifold Frobenius layer as of 2026-04-25.

## Conventions (forward-only from 2026-04-27)

Entries added or edited from 2026-04-27 onward carry trailing tags:

`· author · class · YYYY-MM-DD`

- **Author:** `by Xiang` (direction decision — locked) / `by Zinan`
  (my working assumption — revisable).
- **Class:** `stable` (no expiry) / `active` (re-audit every 30 days,
  open-problem state) / `working` (re-audit every 7 days, hypothesis).
- **Date:** last date the entry was verified correct, not first written.

Pre-2026-04-27 entries are not retroactively tagged — touch-then-tag.

A nightly auditor (`scripts/memory/understanding_stale_audit.py`)
flags `active`/`working` entries past their freshness window and
surfaces them in the morning Telegram report.

See also: `## Abandoned avenues` at the bottom — record approaches
tried and dropped so future-me / downstream agents don't re-attempt
the same dead-ends.

## Goal (narrowed by Xiang on 2026-04-25)

Connection coefficient extraction: express the analytic-at-`z=0`
generating function `f_apery` (sum-of-cubes for ζ(3)) as
`f_apery(z) = a₀·Y₀(z−z₁) + a_½·Y_½(z−z₁) + a₁·Y_1(z−z₁)`
on a left neighbourhood of the conifold `z₁ = 17 − 12√2`, where
`{Y_ρ}_{ρ ∈ {0,1/2,1}}` are the three local Frobenius branches.

The triple `(a₀, a_½, a₁)` is **transcendental** (involves `π²`,
ζ-values). Mathlib has no machinery for this. Tonight's job is the
*structural plumbing* so that when `(a₀, a_½, a₁)` is eventually
specified, the chain to "value at corridor right endpoint" is automatic.

## Key objects (in `AperyInstance.lean`)

- `yAperyZero c₀ t` — ρ=0 branch `V₀(c₀, t)`.
- `yAperyHalf c_half t` — ρ=1/2 branch `√(-t) · V_{1/2}(c_half, t)`,
  real-valued on `t < 0`.
- `yApery c₁ t` — ρ=1 branch `t · V_1(c₁, t)`.
- `aperyBranchTriple c₀ c_half c₁ t` — the three-branch superposition.
- `aperyConifoldExpExtension ε init_v t` — exp transport of the
  first-order y₂ corridor ODE on `[z₁−1, −ε]` from right endpoint
  data `init_v` (specific to ρ=1 reduction).
- `aperyConifoldBoundaryConnection ε` — `K(ε) := exp(∫_{−ε}^{z₁−1} φ)`.
- `aperyApéryBoundaryFunctional ε c₀` — packaged ρ=1 boundary value.
- `aperyBranchAmplitude_one ε` — `A_one(ε) := 2V'(1,−ε) − ε·V''(1,−ε)`.

## What is built (structural side, ρ=1 chain)

1. ρ=1 `y₂ := 2V' + t·V''` corridor reduction:
   - First-order ODE `Y' = (Q_sh / P_sh) · Y` on `(z₁−1, 0)`.
   - Closed-form transport `K(ε)`.
   - Picard uniqueness on each side of zero.
2. `aperyApéryBoundaryFunctional ε c₀ = c₀ · A_one(ε) · K(ε)`
   (factorisation theorem).
3. `A_one(0) = 2 · c₁(unit seed)` — limit of amplitude as corridor
   shrinks to the conifold equals `2 ×` first nontrivial Frobenius
   coefficient.
4. Vanishing/sign characterisations (use `K(ε) > 0`).

## What is built (algebraic skeleton, three branches)

1. `aperyBranchTriple` is ℝ-linear in seed triple (smul + add + zero
   simp lemmas). Single-component reductions
   `aperyBranchTriple_only_{zero,half,one}_branch`.
2. Branch values at `t = 0`:
   - `yAperyZero_at_zero c₀ = c₀`.
   - `yAperyHalf_at_zero = 0` (from `√0 = 0`).
   - `yApery_at_zero = 0` (from explicit `t` factor).
   - `aperyBranchTriple_at_zero c₀ c_half c₁ = c₀`.
3. Desingularised forms (off-conifold):
   - `yApery_div_t (ht : t ≠ 0)`: divides out `t` to recover `V_1`.
   - `yAperyHalf_div_sqrt (ht : t < 0)`: divides out `√(-t)` to
     recover `V_{1/2}`.
   - `aperyBranchTriple_singular_div_sqrt`: after subtracting V₀,
     `(triple − V₀)/√(-t) = V_{1/2}(c_half) − √(-t)·V_1(c₁)`.
   - `aperyBranchTriple_singular_div_t`: parallel for c₁ extraction.
4. `aperyBranchTriple_eq_decomp`: explicit
   `triple = V₀ + √(-t)·V_{1/2} + t·V_1`.
5. `aperyBranchTriple_zero_at_zero_implies_c₀`: regular-component
   independence.

## Connection-coefficient interface (added 2026-04-25 evening, session 50q+)

`AperyInstance.lean` now exposes a structural API:

- `IsAperyConnectionCoeffsOn (a₀ a_half a₁ : ℝ) (f : ℝ → ℝ) (I : Set ℝ) : Prop`
  — predicate: `f(z₁ + t) = aperyBranchTriple a₀ a_half a₁ t` on `I`.
- Constructors: `.zero`, `.of_pure_{regular,half,one}`,
  `.of_shifted_eqOn`, `.canonical` (free instance),
  `.exists_of_triple` (existence corollary).
- Operators: `.smul`, `.neg`, `.mono`, `.union`, `.inter_left/right`,
  `.empty`, `.congr` (function congruence on z₁+I).
- Reductions: `.zero_iff`, `.singleton_zero_iff`,
  `.iff_shifted_eqOn` (full iff form).
- Extractors: `.regular_seed` (`a₀ = f(z₁)` when `0 ∈ I`),
  `.right_endpoint` (linear functional in seeds).
- Uniqueness: `.regular_unique` (a₀ alone), `.singular_difference`
  (algebraic constraint), `.unique_of_two_witnesses` (full triple
  uniqueness given two `−ε` witnesses with nondegenerate 2×2 det),
  `.unique_of_positive_witnesses` (bracket-form variant).
- Cramer extractors: `.a_half_cramer`, `.a_one_cramer` (Δ-multiplied
  identities), `.a_half_eq_div`, `.a_one_eq_div` (closed-form ratios),
  `.a_half_from_f`, `.a_one_from_f` (a₀-free, purely f-functional).
- Δ structure: `aperyBranchSingularDet_factor` (explicit
  `√ε₁·√ε₂·bracket` factorisation),
  `aperyBranchSingularDet_ne_zero_iff` (Δ≠0 ↔ bracket≠0 for ε>0),
  `aperyBranchSingularDet_antisymm`, `_at_diag`, `_ne_zero_imp_ne`,
  `_at_zero_left/right`.

The full uniqueness theorem is conditional on
`Δ(ε₁, ε₂) := A_½(ε₁) · V_1(ε₂) − A_½(ε₂) · V_1(ε₁) ≠ 0`. Leading-order
asymptotics (as `ε → 0`) give `Δ(ε₁, ε₂) ≈ √(ε₁·ε₂)·(√ε₁ − √ε₂)`,
nonzero for `ε₁ ≠ ε₂ > 0`, but the rigorous proof requires Frobenius
series continuity at `t = 0` (deferred — gap A).

## Gap-A discharge chain (added 2026-04-25 late session, 50r+)

Layered scaffolding pushing the gap-A obligation into the canonical
Frobenius analytic data:

- `bracket_ne_zero_skeleton` — abstract perturbation control (pure ℝ).
- `aperyBranchSingularBracket_decomp` — ring identity isolating the
  principal `V_half_0·V_one_0·(√ε₁−√ε₂)` term from perturbation.
- `aperyBranchSingularBracket_ne_zero_of_perturbation` — bracket ≠ 0
  given a domination hypothesis `h_dom`.
- `aperyBranchSingularDet_ne_zero_of_perturbation` — Δ ≠ 0 directly.
- `IsAperyConnectionCoeffsOn.unique_of_perturbation` — predicate-level
  triple uniqueness from `h_dom`.
- `aperyBranchSingular_h_dom_of_uniform_bound` — replaces `h_dom` by
  a uniform off-diagonal bound `M` and a quantitative ε comparison.
- `abs_mul_sub_mul_le` — `|ab − cd| ≤ |a|·|b−d| + |d|·|a−c|`.
- `aperyBranchSingular_offdiag_bound` — produces `M = B_half·ν +
  |V_one_0|·μ` from individual Lipschitz inputs (`B_half` uniform on
  `V_½`, `μ` continuity modulus of `V_½`, `ν` continuity modulus of
  `V_1`).
- `IsAperyConnectionCoeffsOn.unique_of_lipschitz` — single end-to-end
  user-facing API: `(B_half, μ, ν, ε comparison)` → triple uniqueness.

Production discharge requires only Mathlib's analytic-continuation
machinery on the apery polynomial Frobenius series (supplying
`B_half, μ, ν`); the rest is pure real algebra.

## Existence side (added same session)

- `aperyTriple_interpolates_three_points` — given any `f` and Δ ≠ 0,
  Cramer's rule constructs an explicit triple matching `f` at
  `{z₁, z₁−ε₁, z₁−ε₂}`. `a₀ := f(z₁)`; `a_half, a₁` from 2×2 solve.
- `IsAperyConnectionCoeffsOn.exists_on_three_points` — predicate-level
  lift: triple exists with predicate holding on `{0, −ε₁, −ε₂}`.

Together with the uniqueness theorems this gives "exists-and-unique"
on the 3-point set via real algebra alone — no analytic continuation
needed for the finite-witness case.

## |Δ| two-sided control (added 2026-04-25 even later, 50s+)

Quantitative bounds beyond `Δ ≠ 0`, useful for stability/asymptotic
analysis where signed determinant must be quantified.

- `aperyBranchSingularDet_abs_lower_bound` — `|Δ| ≥ √ε₁·√ε₂·(|principal|−perturbation)`
  via factor + reverse triangle inequality on `bracket = principal + perturbation`.
- `aperyBranchSingularDet_abs_pos_of_perturbation_lt` — strict `0 < |Δ|`
  when `ε_i > 0` and `(√ε₁·|δ₁| + √ε₂·|δ₂|) < |principal|`.
- `aperyBranchSingularDet_abs_pos_of_lipschitz` — Lipschitz wrapper:
  `(B_half, μ, ν) + ε_i>0 + (√ε₁+√ε₂)·M < |principal|` ⇒ `0 < |Δ|`,
  parallel to `unique_of_lipschitz` but quantitative.
- `aperyBranchSingularDet_principal_abs_pos` — `|principal| > 0` from
  `V_h₀, V_1₀ ≠ 0` and `ε₁ ≠ ε₂` (≥ 0). Discharges the size comparison
  hypothesis for any concrete distinct-ε regime.
- `aperyBranchSingularDet_abs_eq_sqrt_prod_mul_bracket` — direct
  `|Δ| = √ε₁·√ε₂·|bracket|` form of the factor.
- `aperyBranchSingularBracket_abs_le_uniform` — triangle-inequality
  `|bracket| ≤ (√ε₁+√ε₂)·B_half·B_one` from uniform sup bounds.
- `aperyBranchSingularDet_abs_le_uniform` — pairs the two:
  `|Δ| ≤ √ε₁·√ε₂·(√ε₁+√ε₂)·B_half·B_one`.
- `aperyBranchSingularDet_abs_lower_bound_fraction` — fractional
  `|Δ| ≥ c·√ε₁·√ε₂·|principal|` from perturbation ≤ `(1−c)·|principal|`.
- `aperyBranchSingularDet_abs_lower_bound_half` — `c = 1/2`
  specialization: standard halve-the-principal stability margin.

## Three-point f-functional bundle (added 2026-04-25 even later, 50t+)

End-user atoms exposing the predicate as a three-point evaluation
problem. Plays directly with `Cramer` extractors and `triple_from_f`.

- `IsAperyConnectionCoeffsOn.eval_three_points` — packages
  `f(z₁), f(z₁−ε₁), f(z₁−ε₂)` from the predicate.
- `IsAperyConnectionCoeffsOn.eval_three_points_amp` — same but unfolds
  RHS via `aperyBranchTriple_at_neg_eps` to expose the linear system
  `a₀·V₀_amp + a_h·A_h + a₁·V_1`.
- `IsAperyConnectionCoeffsOn.triple_from_f` — bundles
  `regular_seed`/`a_half_from_f`/`a_one_from_f` into a single triple
  determination from `f` at the three points.
- `IsAperyConnectionCoeffsOn.triple_eq_of_three_point_agreement` — two
  witnesses, three-point agreement ⇒ triples agree.
- `IsAperyConnectionCoeffsOn.triple_zero_of_three_point_vanish` — `f`
  vanishes at the three points ⇒ triple is zero.
- `IsAperyConnectionCoeffsOn.triple_zero_iff_three_point_vanish` — iff
  form combining the two directions.

## Stability bounds on `|a_half|`, `|a₁|` (added 2026-04-25 even later, 50u+)

Quantitative `|a_*| ≤ (numerator-bound) / |Δ|` formulas. Plug any
`|Δ|` lower bound (from the two-sided control section) to convert into
a fully concrete bound.

- `IsAperyConnectionCoeffsOn.a_half_abs_eq_div` — exact equality
  `|a_h| = |numer| / |Δ|` from `a_half_eq_div` + `abs_div`.
- `IsAperyConnectionCoeffsOn.a_one_abs_eq_div` — companion for `|a₁|`.
- `abs_mul_sub_mul_triangle` — pure ℝ workhorse `|a·b−c·d| ≤
  |a|·|b|+|c|·|d|`.
- `aperyConnection_a_half_numerator_abs_le` /
  `aperyConnection_a_one_numerator_abs_le` — explicit triangle bound on
  each numerator (no predicate hypothesis).
- `IsAperyConnectionCoeffsOn.a_half_abs_le_div` /
  `IsAperyConnectionCoeffsOn.a_one_abs_le_div` — end-to-end:
  `|a_*| ≤ (triangle numerator bound) / |Δ|`. Combines the equality
  with the numerator triangle bound.

## What is *not* built (gaps)

A. **Limit machinery.** `lim_{t→0⁻}` of the desingularised forms
   should yield `(c_half, c₁)` directly, but requires
   `frobeniusValue_continuousOn` instantiated for the apery
   conifold polynomial — heavy hypotheses (M₀, B, polynomial coeff
   bounds) need explicit discharge for the apery instance.
B. **ρ=0 corridor transport.** The y₂ trick is specific to ρ=1
   (cancels the leading `t` factor). For ρ=0 the branch is `V_0`
   directly; need a separate analytic-continuation route from
   `t = z₁−1` to `t = 0` since `|z₁−1| > convergence radius` of
   the Frobenius disk around `z₁`. Likely needs corridor patching:
   chain of overlapping disks from `z₁` along `[0, z₁]` toward
   `z = 1` (i.e. `t = z₁−1`).
C. **ρ=1/2 corridor transport.** Same as ρ=0 in principle, plus
   the `√(-t)` branch handling.
D. **Connection coefficient values.** The actual numerical values
   `(a₀, a_½, a₁)` for the ζ(3) sum-of-cubes generating function —
   transcendental, needs π²/ζ machinery.
E. **Three-branch linear independence.** Currently only c₀
   independence is proved. c_half, c₁ independence requires either
   limit machinery (gap A) or evaluation at multiple distinguished
   points combined with non-vanishing of the Frobenius series.

## Gap E — CLOSED (2026-04-28, modulo coefficient growth sorry's)

`aperyFrobenius_branches_linearly_independent` — the three Frobenius
branches `yAperyZero, yAperyHalf, yApery` are linearly independent
on `(0, z₁)`. Proved by instantiating `frobenius_three_branch_linear_independence`
(the reusable abstract theorem for O(1), O(√t), O(t) functions).

The proof chain:
1. `frobenius_three_branch_linear_independence` (general theorem, 128 lines)
2. Six Tendsto results at ε → 0⁺ for each branch and ratio
3. One-line instantiation at the Apéry conifold

Conditional on 3 `sorry` (not axiom) for coefficient growth bounds.
These can be discharged via either:
- Generic `frobeniusCoeff_abs_mul_pow_summable_general` (tiny-disk summability, ~200 lines of √2 arithmetic)
- Or eigenvalue decomposition from `taylorShift(P) = t·(z₁-t)²·(t+24√2)` (proved)
· by Zinan · stable · 2026-04-28

## Gap B status — effectively resolved (2026-04-27)

**Gap B's original motivation was to build a chain of overlapping disks
to extend `aperyGFAReal` from `[0, 1/64)` to `[0, z₁)`.** With Gap F
closed (`aₙ ≤ (17+12√2)ⁿ`), `aperyGFAReal` converges unconditionally
on `[0, z₁)`, so `F = aperyGFAReal` is itself the extension. Both
`HasAperyAnalyticExtension` and `HasCorridorAperyAnalyticExtension` are
now unconditionally true without any chain construction.

The chain infrastructure (AperyAnalyticDiskAt, chainGlue, ofGFAChain,
etc.) remains useful for other purposes (e.g., analytic continuation
*beyond* `z₁` if needed), but is no longer required for the main
`[0, z₁)` corridor.
· by Zinan · stable · 2026-04-27

## Working strategy

Build invariant: 0 sorry / 0 axiom in all new lemmas.

## Recent commits (this session)

- `66b9a68` aperyBranchTriple superposition
- `dc018c2` yAperyZero_y2_smul_c₀
- `9242b18` aperyApéryBoundaryFunctional packaging
- `57ae40e` factorisation `c₀ · A · K`
- `cd10244` amplitude_at_zero
- `cb77085` vanishing/sign characterisations
- `306f868` aperyBranchTriple_at_zero
- `25b42ba` branch-at-zero atoms
- `9c54a4d` desingularised ρ=1, ρ=1/2 forms
- `9018516` decomposition with explicit prefactors
- `6f96e9c` single-branch reductions + split
- `b64681e` singular-pair desingularised forms

## `aperyConnectionResidual` (added 2026-04-25 morning)

Definition: `aperyConnectionResidual f ε := f(z₁ − ε) − f(z₁)·A_0(ε)`.
This is the part of `f(z₁ − ε)` not absorbed by the regular Frobenius
branch. When `(a₀, a_half, a₁)` represents `f`:

  `residual(ε) = a_half · A_½(ε) + a₁ · V_1(ε)`

So the singular pair is the only thing residual sees. Atoms:

- `aperyConnectionResidual_zero` — ε=0 ⇒ residual = 0 (`@[simp]`).
- `aperyConnectionResidual_eq` — residual = `a_half · A_½(ε) + a₁ · V_1(ε)`
  via `right_endpoint` + `regular_seed`.
- `aperyConnectionResidual_abs_le` — `|residual| ≤ |a_half|·|A_½| + |a₁|·|V_1|`.
- `a_*_abs_le_div_residual` — stability bounds rephrased via residual.
- Linearity: `_add`, `_sub`, `_smul`, `_const` (constant gives `c·(1 − A_0(ε))`).

This packaging is a clean ℝ-linear functional on candidate `f`. Downstream
analytic-continuation work needs only to bound `|residual(ε)|` to bound
the singular coefficients.

## f-only stability batch (added 2026-04-25 morning)

- `a_zero_abs_eq_from_f` — `|a₀| = |f(z₁)|`.
- `a_half_abs_le_div_from_f` / `a_one_abs_le_div_from_f` — stability
  bounds with `a₀` substituted by `f(z₁)`.

## Has-level toolkit (added 2026-04-25 late evening, autonomous batch)

`HasAperyConnectionCoeffsOn f I := ∃ a₀ a_half a₁, IsAperyConnectionCoeffsOn …`
— the existential closure. New atoms wrap each Is-level lemma at the
existential level so downstream code never has to reach inside:

- Constructors: `.of_pure_regular`, `.of_pure_half`, `.of_pure_one`,
  `.of_three_pure` (sum of three single-branch components).
- Set algebra: `.inter_left`, `.inter_right`, `.congr` (lift from Is).
- Reductions: `.eq_iff_three_point_agreement`,
  `.eq_zero_iff_three_point_vanish` (Is-level three-point reductions
  lifted to Has).
- Iff form: `.iff_exists_eqOn` — Has = `∃ triple, EqOn (shift f) (triple)`.
- Uniqueness: `.existsUnique_witness` — under `0 ∈ I` and `Δ ≠ 0`, the
  triple is unique (lifts `unique_of_two_witnesses`).
- Closure: `.smul_iff` — `c ≠ 0 ⇒ Has(c·f) ↔ Has(f)`.
- Extractor: `.forall_regular_seed_eq` — every witnessing triple has
  `a₀ = f(z₁)` (regular-seed agreement at existential level).

## `aperyGFAReal` analytic toolkit on `[0, 1/64)` and `[0, 1/34)` (added 2026-04-25, improved 2026-04-27)

**Improved convergence radius (2026-04-27):** `aₙ ≤ 34ⁿ` from the
three-term recurrence + algebra `(2n+1)(17n²+17n+5) ≤ 34(n+1)³`. This
gives unconditional convergence on `|z| < 1/34 ≈ 0.0294`, nearly matching
the true radius `z₁ = 17−12√2 ≈ 0.02943`. The numerical sandwich is now
`1/34 < z₁ < 1/32`, so the conifold is just barely outside the
unconditional disk. All three standard probes (z₁/2, 2z₁/3, 3z₁/4) are
in the unconditional disk `[0, 1/34)`. The full `[0, 1/34)` toolkit
(ge_one, positivity, strict_mono, injOn) is built.
· by Zinan · stable · 2026-04-27

Original crude radius `1/64` from `aₙ ≤ (n+1)·64ⁿ`. True radius is
`z₁ ≈ 0.0294`; sharp asymptotic `aₙ ∼ z₁⁻ⁿ/n^{3/2}` is gap F (now
nearly closed by the `aₙ ≤ 34ⁿ` bound — remaining gap is `[1/34, z₁)`).

- `aperyGFAPartial_le_aperyGFAReal` — partials bound the tsum from below.
- `aperyGFAReal_ge_one_plus_5z` — affine lower bound from `a₀=1, a₁=5`.
- `aperyGFAReal_ge_quadratic_partial` — `1 + 5z + 73z² ≤ GF(z)` from
  `a₂ = 73`. Uses `change` (not `rw [show …]`) for partial-sum unfold.
- `aperyGFAReal_gt_one_of_pos` — strict `1 < GF(z)` for `0 < z < 1/64`.
- `aperyGFAReal_inv_lt_one_of_pos`, `aperyGFAReal_inv_pos_of_pos` —
  reciprocal bounds on the same interval.
- `aperyGFAReal_strict_mono_on_nonneg` — strict monotone via splitting
  partial(N=2) (linear part `5(z₂−z₁) > 0`) and tail tsum monotonicity.
- `aperyGFAReal_injOn_nonneg` — `Set.InjOn` on `[0, 1/64)` from strict
  mono.
- `aperyGFAReal_image_Ico_subset_Ici_one` — image lands in `[1, ∞)`.
- `aperyGFAReal_le_inv_sq_of_mem` — upper bound `GF(z) ≤ 1/(1−64z)²`
  via `aₙ ≤ (n+1)·64ⁿ` plus
  `tsum_choose_mul_geometric_of_norm_lt_one`.
- `aperyGFAReal_div_form` — `(GF(z)−1)/z = ∑ a_{n+1}·zⁿ` for `z ≠ 0`,
  `|z| < 1/64`. Uses `field_simp` to discharge division.

## Pure-shift residual layer (added 2026-04-25 night, autonomous batch)

Atoms expressing the connection residual on *literal* shifted Frobenius
functions, no predicate needed. These compose the residual functional
into the closed-form Cramer extraction.

- `aperyConnectionResidual_pure_regular_shift` — for
  `f x := yAperyZero a₀ (x − z₁)`, residual ≡ 0. Regular branch is
  fully absorbed by `f(z₁) · A_0(ε)`.
- `aperyConnectionResidual_pure_half_shift` — for
  `f x := yAperyHalf a_half (x − z₁)`, residual = `a_half · A_½(ε)`.
- `aperyConnectionResidual_pure_one_shift` — for
  `f x := yApery a₁ (x − z₁)`, residual = `a₁ · V_1(ε)`.
- `aperyConnectionResidual_pure_triple_shift` — for the full triple
  `aperyBranchTriple a₀ a_half a₁ (x − z₁)`, residual =
  `a_half · A_½(ε) + a₁ · V_1(ε)`. Direct from the three pure-branch
  atoms via residual additivity.
- `aperyConnectionResidual_eq_sub_yAperyZero` — semantic recast:
  residual `f` ε = `f(z₁ − ε) − yAperyZero(f(z₁), −ε)` = "deviation
  of `f` from the unique regular Frobenius branch matching its
  `t = 0` value".
- `aperyConnectionResidual_abs_le_sup` — sup-norm envelope:
  `|f(z₁ ± ε)| ≤ M ⇒ |residual| ≤ M·(1 + |A_0(ε)|)`. Useful when only
  L∞ control of `f` near the conifold is available.

## Cramer extraction at the residual level (added same session)

Pure ℝ-algebra atoms — no predicate, no analytic content. The
counterpart of the predicate-side `unique_of_two_witnesses`/`a_*_cramer`
expressed directly on residual data.

- `aperyConnection_singular_pair_zero_of_residual_zero` — if
  `a_h·A_½(εᵢ) + a₁·V_1(εᵢ) = 0` for `i = 1, 2` and `Δ ≠ 0`, then
  `a_h = a₁ = 0`. (Special r=0 case of solve.)
- `aperyConnection_singular_pair_solve` — Cramer's rule on arbitrary
  residual RHS `(r₁, r₂)`: returns explicit closed-form quotients for
  `a_h` and `a₁`.
- `aperyConnection_triple_recover` — end-to-end composite: combines
  `pure_triple_shift` (residual computation) with `singular_pair_solve`
  (Cramer) so that for the literal `aperyBranchTriple` function, the
  full triple `(a₀, a_h, a₁)` is recovered as closed-form
  ratios of residual values, with `a₀ = f(z₁)` directly.

The chain `(a₀, a_h, a₁) → f → (a₀, a_h, a₁)` is now closed by real
algebra alone for the literal triple function. The remaining work is
to lift this to abstract `f` for which a triple representation exists
— which is exactly the Has-level uniqueness theorem (already in place
via `unique_of_lipschitz`).

## `aperyGFAReal` analytic toolkit — late evening additions

Beyond what was logged in the earlier UNDERSTANDING update:

- `aperyGFAReal_ge_quadratic_partial` — `1 + 5z + 73z² ≤ GF(z)`.
- `aperyGFAReal_ge_cubic_partial` — `1 + 5z + 73z² + 1445z³ ≤ GF(z)`.
- `aperyGFAReal_ge_quartic_partial` — `1 + 5z + 73z² + 1445z³ + 33001z⁴ ≤ GF(z)`.
- `aperyGFAReal_gt_quadratic_partial_of_pos` — strict `<` for `z > 0`.
- `aperyGFAReal_gt_cubic_partial_of_pos` — strict `<` for `z > 0`.
- `aperyGFAReal_div_diff_ge_five` — `(GF(z)−1)/z ≥ 5` for `0 < z`.
- `aperyGFAReal_div_diff_gt_linear` — `(GF(z)−1)/z > 5 + 73z` for `0 < z`.
- `aperyGFAReal_le_two_of_small` — `GF(z) ≤ 2` on `[0, 1/256]`
  (constant envelope on subdisk).
- `aperyGFAReal_sub_partial_pos` — every truncation-tail strictly
  positive for `z > 0`.
- `aperyGFAReal_inv_strict_anti_on_Ico` — `1/GF` strictly decreasing.
- `aperyGFAReal_{,strict}MonotoneOn_Ico` — Mathlib-style packaging.

## Algebraic seed-equivalence layer (added 2026-04-25 late night)

A clean ladder of injectivity/vanishing atoms for `aperyBranchTriple`,
all gated on the standard non-degenerate singular bracket
`Δ(ε₁,ε₂) ≠ 0` and proved purely by lifting via
`IsAperyConnectionCoeffsOn.of_pure_triple_shift` plus
`triple_eq_of_two_witnesses` (no analytic content).

- `aperyBranchTriple_decomp` — definitional unfold:
  `aperyBranchTriple a₀ a_h a₁ t = yAperyZero a₀ t + yAperyHalf a_h t + yApery a₁ t`.
- `aperyBranchTriple_shift_eq_sum` — pointwise rewrite to literal
  three-summand form with `t = x − z₁`.
- `aperyBranchTriple_seeds_eq_of_three_witnesses` — three-point
  agreement ⇒ seed-triple equality.
- `aperyBranchTriple_seeds_zero_of_three_point_vanish` — special
  `(b₀, b_h, b₁) = 0` case: three-point vanishing ⇒ all seeds zero.
- `aperyBranchTriple_seeds_zero_iff_three_point_vanish` — iff form
  of the vanishing test.
- `aperyBranchTriple_seeds_eq_iff_three_point_agreement` — iff form
  of the agreement test.
- `aperyBranchTriple_funeq_iff_seeds_eq` — strongest packaging:
  `(∀ t, aperyBranchTriple a t = aperyBranchTriple b t) ↔ a = b`.

## Pure-triple shift constructor & cumulative shifts (same session)

- `IsAperyConnectionCoeffsOn.of_pure_triple_shift` — the literal
  shifted triple `fun x ↦ aperyBranchTriple b₀ b_h b₁ (x − z₁)`
  carries `(b₀, b_h, b₁)` on every set.
- `IsAperyConnectionCoeffsOn.{add,sub}_aperyBranchTriple_shift` —
  cumulative ±-shift atoms: adding/subtracting the literal shifted
  triple shifts seeds coordinate-wise.
- `HasAperyConnectionCoeffsOn.{add,sub}_aperyBranchTriple_shift` —
  Has-level mirrors.
- `HasAperyConnectionCoeffsOn.{yAperyZero,yAperyHalf,yApery,aperyBranchTriple}_shift` —
  unconditional existence atoms: each of the four shifted Frobenius
  forms is representable on every set.
- `HasAperyConnectionCoeffsOn.three_branch_shift_sum` — Has-level
  existence for the explicit three-summand form (alias of
  `aperyBranchTriple_shift` via `_decomp`).
- `aperyConnectionResidual_{smul,neg}_pure_triple_shift` — residual
  under scalar transforms of the literal shifted triple; closed-form
  in `(a_h · A_½(ε) + a₁ · V_1(ε))`.

## Branch ±-shift hexad (added 2026-04-25 late night, autonomous batch)

Twelve atoms covering the full algebra of how each Frobenius branch
plugs into the residual/predicate machinery via pointwise ±:

**Residual layer (six):**
- `aperyConnectionResidual_{add,sub}_yAperyZero_shift` — residual is
  *invariant* under ±yAperyZero c (regular branch absorbed).
- `aperyConnectionResidual_{add,sub}_yAperyHalf_shift` — residual
  shifts by ±b·A_½(ε).
- `aperyConnectionResidual_{add,sub}_yApery_shift` — residual shifts
  by ±c·V_1(ε).

**Predicate `IsAperyConnectionCoeffsOn` layer (six):**
- `IsAperyConnectionCoeffsOn.{add,sub}_yAperyZero_shift` — only
  `a₀ ↦ a₀ ± c`.
- `IsAperyConnectionCoeffsOn.{add,sub}_yAperyHalf_shift` — only
  `a_half ↦ a_half ± b`.
- `IsAperyConnectionCoeffsOn.{add,sub}_yApery_shift` — only
  `a₁ ↦ a₁ ± c`.

**Existential `HasAperyConnectionCoeffsOn` layer (six):**
identical signature without explicit triple, by destructuring +
applying the Is-level shift. Closes representability under each
elementary branch operation.

The proofs at every layer are pure algebra (residual ⇒ `unfold + ring`;
predicate ⇒ `add` with a pure-branch witness then `simpa`; Has ⇒
destruct the triple and repackage).

## Named extraction interface (added 2026-04-25 even later night, autonomous batch)

After the algebraic / branch-shift / Finset-summation infrastructure
for `IsAperyConnectionCoeffsOn`, `HasAperyConnectionCoeffsOn`, and the
residual was complete, the next layer abstracts Cramer recovery into
three named, *non-conditional* `noncomputable def`s on functions:

- `aperyExtractRegular f := f Number.aperyConifoldZ1Poly`
- `aperyExtractHalf f ε₁ ε₂ := (R(f)(ε₁)·V_1(ε₂) − R(f)(ε₂)·V_1(ε₁)) / Δ`
- `aperyExtractOne   f ε₁ ε₂ := (−R(f)(ε₁)·A_½(ε₂) + R(f)(ε₂)·A_½(ε₁)) / Δ`

where `R = aperyConnectionResidual` and `Δ` is the Cramer determinant.

**Promotion lemmas:**
- `HasAperyConnectionCoeffsOn.is_extract` — under representability +
  three witness points + non-degenerate Δ, the extract values form a
  valid `IsAperyConnectionCoeffsOn` witness.
- `IsAperyConnectionCoeffsOn.eq_extract` — any concrete witness's three
  components equal the corresponding extract values (uniqueness).

**Linearity (15 atoms = 3 components × 5 operations):**
`aperyExtract{Regular,Half,One}_{zero,add,smul,neg,sub}`. Regular is
function-application linear (proofs are `rfl`); Half and One chain
through residual linearity + `ring`.

**Pure-branch values (9 atoms = 3 components × 3 pure branches):**
`aperyExtract{R,H,O}_pure_{regular,half,one}_shift`. Diagonal entries
recover the seed (Half→Half and One→One require Δ ≠ 0); off-diagonal
entries vanish unconditionally (`0 / Δ = 0` in ℝ).

**Pure-triple values (3 atoms):**
`aperyExtract{R,H,O}_pure_triple_shift`. On the canonical
`fun x => aperyBranchTriple a₀ a_half a₁ (x − z₁)`, extract returns
exactly `(a₀, a_half, a₁)`. Proven via `IsAperyConnectionCoeffsOn.canonical`
+ `eq_extract`.

**Branch-shift hexads (24 atoms):**
`aperyExtract{R,H,O}_{add,sub}_y{AperyZero,AperyHalf,Apery}_shift`
(18) + `aperyExtract{R,H,O}_{add,sub}_aperyBranchTriple_shift` (6).
Each `simp`-friendly: extract over `f ± shifted-branch` reduces to
extract f shifted by the corresponding seed. Diagonal entries that
move on the shifted seed need Δ ≠ 0; off-diagonal are unconditional.

**Finset additivity (3 atoms):**
`aperyExtract{Regular,Half,One}_finset_sum`. Each component
distributes over `∑ i ∈ s, f i z`. Same induction pattern as the
residual / Is / Has Finset_sum atoms.

The named interface is the working abstraction layer between abstract
representability (`HasAperyConnectionCoeffsOn`) and concrete coefficient
algebra. Downstream code should write equations in `aperyExtract*`
rather than the underlying Cramer expressions.

**Congruence atoms (6 atoms = 3 components × 2 forms):**
`aperyExtract{R,H,O}_congr` — extract depends only on `f` at `z₁`
(Regular) or at `{z₁, z₁ − ε₁, z₁ − ε₂}` (Half/One). Plus
`aperyExtract{R,H,O}_congr_eqOn` — `Set.EqOn` packaging: agreement on
any set `S` containing the relevant points yields equal extracts.
Useful for swapping `f` ↔ `g` along proven equalities without unfolding.

**Single-component projections (3 atoms):**
`IsAperyConnectionCoeffsOn.{regular,half,one}_eq_extract` — split
`eq_extract` projections; named one-sided versions handy when only one
component is needed.

**Has-level uniqueness via extract (1 atom):**
`HasAperyConnectionCoeffsOn.witness_eq_via_extract` — under non-degenerate
Δ, any two `IsAperyConnectionCoeffsOn` triples on the same `f, I` are
componentwise equal (proof goes via `extract`).

**Has-level existsUnique extract (1 atom):**
`HasAperyConnectionCoeffsOn.existsUnique_extract` — under representability
+ Δ ≠ 0, the extract triple is the unique `(a₀, a_half, a₁)` satisfying
`IsAperyConnectionCoeffsOn` *and* equal to the extract values.

**Has-level shifted reconstruction (1 atom):**
`HasAperyConnectionCoeffsOn.shifted_eq_extract` — `Set.EqOn` form:
`f (z₁ + t) = aperyBranchTriple (extractR f) (extractH f ε₁ ε₂) (extractO f ε₁ ε₂) t`
on `I`. Closes the loop: extract not only matches witnesses but
*reconstructs* `f` on the corridor right-endpoint.

## Cramer determinant `aperyConnectionDet` (added same autonomous batch)

The denominator of `aperyExtract{Half,One}` is now packaged as
`aperyConnectionDet ε₁ ε₂ := A_½(ε₁) · V_1(ε₂) − A_½(ε₂) · V_1(ε₁)` so
downstream proofs write `Δ ≠ 0` instead of the expanded inequality.

**Algebraic atoms (5):**
- `aperyConnectionDet_def` — unfold lemma to expanded form
- `aperyConnectionDet_ne_zero_iff` — `Iff.rfl` bridge to expanded `≠ 0`
- `aperyConnectionDet_swap` — antisymmetry: `Δ(ε₂, ε₁) = −Δ(ε₁, ε₂)`
- `aperyConnectionDet_self` — diagonal vanish: `Δ(ε, ε) = 0`
- `aperyConnectionDet_zero_left` / `_zero_right` — Δ vanishes when
  either probe is zero

**Sign / probe constraint (1 atom):**
- `aperyConnectionDet_ne_zero_probes_nonzero` — `Δ(ε₁, ε₂) ≠ 0` forces
  `ε₁ ≠ 0`, `ε₂ ≠ 0`, and `ε₁ ≠ ε₂`.

**Extract via Det (4 atoms):**
- `aperyExtractHalf_eq_div_det`, `aperyExtractOne_eq_div_det` —
  reformulation lemmas using named Δ.
- `aperyExtractHalf_swap`, `aperyExtractOne_swap` — extract values are
  invariant under probe-pair swap (sign cancellation between numerator
  and denominator).

**Det-form Has wrappers (3 atoms):**
`HasAperyConnectionCoeffsOn.is_extract_det`,
`IsAperyConnectionCoeffsOn.eq_extract_det`,
`HasAperyConnectionCoeffsOn.shifted_eq_extract_det` — restatements
accepting `hdet : aperyConnectionDet ε₁ ε₂ ≠ 0`.

**Probe-pair invariance (2 atoms — the structural payoff):**
`HasAperyConnectionCoeffsOn.extract{Half,One}_probe_invariant`. Under
`Has f I` plus two non-degenerate probe pairs `(ε₁, ε₂)` and
`(ε₁', ε₂')`, the extract values agree:
`extractH f ε₁ ε₂ = extractH f ε₁' ε₂'` (and similarly for
`extractOne`). This is the intrinsic statement: the extract of `f` is
not a function of probe choice — it's the genuine connection
coefficient. Probes only certify non-degeneracy.

## Gap F — CLOSED (2026-04-27)

**`aₙ ≤ (17+12√2)ⁿ`** proved via two-level ratio-bound induction using
the three-term recurrence + characteristic equation `R² = 34R − 1`.
Convergence radius is now exactly `z₁ = 1/(17+12√2) = 17−12√2`.
`aperyGFAReal_summable_conifold` gives summability on `|z| < z₁`.
· by Zinan · stable · 2026-04-27

Intermediate results also proved:
- `aₙ ≤ 34ⁿ` (simpler, from dropping subtracted term)
- `ContinuousOn aperyGFAReal [0, b]` for `b < 1/34` (unconditional)
- Full `[0, 1/34)` toolkit (ge_one, pos, strict_mono, injOn, image, sInf/sSup)
- `1/34 < z₁ < 1/32` sandwich

The *interface* downstream of Gap F has been abstracted so dependent
code can proceed unconditionally on the bridge. Three Prop-level
abstractions:

1. `AperyGFASummableOnFullDisk` — minimal hypothesis: summability of
   `aₙ z^n` for every `|z| < z₁`. Consumer:
   `aperyGFAReal_summable_of_bridge`.

2. `AperyAnalyticExtension` (structure) — bundles a function `F : ℝ → ℝ`
   that agrees with `aperyGFAReal` on the unconditional disk
   `[0, 1/64)` and is `ContinuousOn [0, z₁)`. `HasAperyAnalyticExtension`
   is its Prop-level existence wrapper.

3. `AperyConnectionData` (structure, extends `AperyAnalyticExtension`) —
   adds a corridor `corridor : Set ℝ` containing `0`, plus a witness
   `has_conn : HasAperyConnectionCoeffsOn F corridor`. This is the full
   bridge: from here, the entire extract toolkit applies. Named
   projections `extract{Regular,Half,One}` plus the two probe-pair
   invariance lifts complete the API.

Once the analytic asymptotic is supplied, `HasAperyConnectionData` can
be discharged and all extract-based theorems become unconditional.
Until then, downstream proofs accept `(d : AperyConnectionData)` as
input and write coefficient identities in `d.extract*` form.

### ConnectionData layer atoms (lives in `AperyGeneratingFunction.lean`)

Beyond the structure itself, the following atoms make `(d : AperyConnectionData)`
a complete working interface:

- `d.hasConnectionCoeffs` — extract the underlying `Has` predicate.
- `d.extract{Regular,Half,One}` — the three named coefficients.
- `d.extract{Half,One}_probe_invariant` — extract values are intrinsic
  (probe-pair independent under non-degenerate Δ).
- `d.shifted_eq_extract` — corridor reconstruction theorem: on the
  corridor, `F (z₁ + t) = aperyBranchTriple (extractR) (extractH)
  (extractO) t`.
- `d.extractRegular_eq` — `extractRegular = F z₁` by `rfl`.
- `d.F_eq_GFA_on_small` — small-disk pinning to `aperyGFAReal`.
- `d.F_unique_on_small` — pairwise small-disk uniqueness.
- `d.F_shift_eq_GFA` — shift form of the small-disk pinning.
- `d.GFA_eq_branchTriple_on_overlap` — main empirical constraint: on
  shifts `t` in `corridor` such that `z₁ + t ∈ [0, 1/64)`,
  `aperyGFAReal (z₁ + t) = aperyBranchTriple (extract triple) t`.
  This is the *checkable* identity downstream code can hit numerically.

### Candidate verification + overlap set form (added 2026-04-25 night, autonomous batch)

These atoms close the "guess and verify" pattern: a downstream solver
proposes `(a₀, a_½, a₁)` matching `d.F` on `corridor`; the framework
forces it to coincide with `d.extract*`.

- `d.candidate_eq_extract` — positive verification: if a triple
  `(a₀, a_half, a₁)` satisfies the corridor equality
  `F (z₁ + t) = aperyBranchTriple a₀ a_half a₁ t` for `t ∈ corridor`,
  then `a₀ = extractRegular`, `a_half = extractHalf ε₁ ε₂`,
  `a₁ = extractOne ε₁ ε₂` (under any non-degenerate probe pair).
- `d.candidate_unique` — corollary via two `candidate_eq_extract`
  calls + transitivity: any two corridor-matching candidate triples
  coincide. The `corridor + Δ ≠ 0` data pins the triple uniquely.
- `d.overlapShifts` — the shift set `{t : t ∈ corridor ∧ z₁ + t ∈ [0,1/64)}`
  named explicitly so downstream lemmas can reason about its structure.
- `d.mem_overlapShifts` — `Iff.rfl` unfold giving membership characterization.
- `d.GFA_eqOn_overlapShifts` — `Set.EqOn` packaging of
  `GFA_eq_branchTriple_on_overlap`: on `overlapShifts`, the GFA shift
  agrees with the extract-triple branch sum. Lets downstream code use
  `Set.EqOn` lemmas (mono, congruence, restriction) directly.

### Sub-corridor restriction + GFA on overlap as connection data (added 2026-04-25 late night, autonomous batch)

The next layer makes corridor restriction first-class and lifts the
overlap identity into the predicate algebra.

- `d.restrictCorridor (hJ : J ⊆ d.corridor) (h0 : 0 ∈ J)` — sub-corridor
  constructor: same `AnalyticExtension`, smaller corridor `J`. Useful
  when a downstream solver only cares about `J`. (Note: cannot use
  `J = overlapShifts` since `0 ∉ overlapShifts` because `z₁ > 1/64`.)
- `d.restrictCorridor_F`, `_corridor`, `_extractRegular`, `_extractHalf`,
  `_extractOne` — five `simp` projections, all `rfl`. Restrict preserves
  the entire extract API.
- `d.overlapShifts_subset_corridor` — the obvious subset relation, used
  with `mono` lemmas downstream.
- `d.GFA_isAperyConnectionCoeffsOn_overlapShifts` — extract triple
  represents `aperyGFAReal` (not `d.F`) in `IsAperyConnectionCoeffsOn`
  sense on `overlapShifts`. The `IsAperyConnectionCoeffsOn` predicate
  is purely pointwise so it is well-defined even though `0 ∉ overlapShifts`.
- `d.GFA_hasAperyConnectionCoeffsOn_overlapShifts` — Has-form, lifting
  the Is-form via existential intro.

### Constructor + boundary identities (added same batch)

- `d.F_at_z1` — `simp` `rfl` lemma: `d.F z₁ = d.extractRegular`.
- `d.F_at_z1_eq_branchTriple_at_zero` — connects `d.F z₁` to
  `aperyBranchTriple extractRegular a_half a₁ 0` for *any* `a_half`,
  `a₁` via `aperyBranchTriple_at_zero` (only the regular branch
  survives at `t = 0`).
- `AperyConnectionData.of_witness ext I h0 h` — explicit constructor:
  takes an `AperyAnalyticExtension`, a corridor `I` containing `0`,
  and a `HasAperyConnectionCoeffsOn ext.F I` witness. Returns the
  bundled `AperyConnectionData`. Two `simp` projections (`_F`,
  `_corridor`) for unfold-on-use.

### Overlap conversion + geometry (added 2026-04-25 late night, autonomous batch)

These atoms make the overlap layer a complete sub-API:

- `d.candidate_GFA_iff_F_on_overlapShifts` — GFA-side ↔ F-side
  candidate `Set.EqOn` interconversion on `overlapShifts`. Justified by
  `F_shift_eq_GFA` (small-disk pinning). Lets downstream code freely
  convert between the two function references on the overlap region.
- `d.F_eqOn_extractTriple_on_overlapShifts` — `shifted_eq_extract`
  restricted via `Set.EqOn.mono` to `overlapShifts ⊆ corridor`.
- `d.mem_overlapShifts_iff_bounds` — explicit unfolding:
  `t ∈ overlapShifts ↔ t ∈ corridor ∧ -z₁ ≤ t ∧ t < 1/64 - z₁`.
  Useful when the disk-membership predicate is harder to manipulate
  than the linear inequalities.
- `d.overlapShifts_subset_neg_shifts` — direct corollary: every
  overlap shift satisfies `t < 1/64 - z₁` (which is `< 0` since
  `z₁ > 1/64`).
- `d.overlapShifts_eq_Ico` — when `[-z₁, 1/64 - z₁) ⊆ corridor`,
  `overlapShifts = [-z₁, 1/64 - z₁)` exactly. Lets the overlap region
  be treated as an explicit interval for integration / summation.
- `d.overlapShifts_eq_empty_of_bound_empty` — abstract degenerate
  form: if the bound interval is empty, so is `overlapShifts`. (Not
  hit numerically, but a defensive sanity-check atom.)

### Has-form lifts + three-point verification (added 2026-04-25 late night, autonomous batch)

These atoms close the Prop-layer / data-layer round-trip and replace
corridor-wide candidate matching with three-point matching.

- `HasAperyConnectionData.toHasAperyAnalyticExtension` — Prop-layer
  projection along `extends`: connection-data Nonempty → analytic-
  extension Nonempty. Pattern-match unfold.
- `HasAperyConnectionData.choose` — `Classical.choice` extractor:
  noncomputable `AperyConnectionData` from a `Nonempty` witness.
- `AperyConnectionData.toHasAperyConnectionData`,
  `AperyAnalyticExtension.toHasAperyAnalyticExtension` — concrete →
  Nonempty wrappers. Together with `choose`, make the Prop layer fully
  interconvertible with the data layer.
- `AperyConnectionData.of_witness_{extractRegular, extractHalf,
  extractOne}` — three `simp` `rfl` projections that unfold extracts
  through the `of_witness` constructor.
- `d.candidate_eq_extract_of_three_points` — three-point candidate
  verification: instead of `Set.EqOn` over corridor, just three
  pointwise equalities `d.F (z₁ + tᵢ) = aperyBranchTriple a₀ a_h a₁ tᵢ`
  at `tᵢ ∈ {0, -ε₁, -ε₂}`. Closes by `IsAperyConnectionCoeffsOn` on
  the three-point set + `eq_extract` (which only needs the predicate
  at the three points, not corridor-wide).
- `d.candidate_eq_extract_via_GFA_three_points` — GFA-side variant:
  the two probe-shift hypotheses are stated against `aperyGFAReal`
  (with `z₁ - εᵢ ∈ [0, 1/64)` to enable `F_shift_eq_GFA`). The `t = 0`
  hypothesis stays `d.F`-side since `z₁ ∉ [0, 1/64)`. Most ergonomic
  shape for downstream code that knows `aperyGFAReal` numerically.

### Component selectors (added 2026-04-25 late night, autonomous batch)

Both three-point verification lemmas have three single-component
selectors so downstream code can avoid destructuring the triple
conjunction when it only needs one extract value.

- `d.candidate_eq_extract{Regular, Half, One}_of_three_points` — F-side
  selectors (each picks one of the conjuncts of
  `candidate_eq_extract_of_three_points`).
- `d.candidate_eq_extract{Regular, Half, One}_via_GFA_three_points` —
  GFA-side selectors (each picks one of the conjuncts of
  `candidate_eq_extract_via_GFA_three_points`).

### Probe-swap symmetry, extensionality, ConnectionData equalities (added 2026-04-26 dawn, autonomous batch — iterations 112–117)

- `d.extractHalf_swap`, `d.extractOne_swap` — lift of
  `aperyExtract{Half,One}_swap` to ConnectionData. Both unconditional:
  swapping `(ε₁, ε₂)` negates numerator and denominator, ratio
  preserved.
- `AperyAnalyticExtension.ext` — extensionality: equal `F`-fields
  force structure equality (the two `Prop` fields collapse by proof
  irrelevance, via `cases hF; rfl` after destructuring).
- `AperyConnectionData.ext_iff_extension_corridor` — equal
  ext-projection and equal corridor force structure equality. Workhorse
  for downstream equalities.
- `d.restrictCorridor_self`, `d.restrictCorridor_trans` — restriction
  to the same corridor returns `d`; nested restrictions collapse to a
  single restriction along the composed inclusion.
- `d.of_witness_self`, `of_witness_toAperyAnalyticExtension` — round-
  trip identities for the `of_witness` constructor.
- `d.is_extract_triple` — under non-degenerate Δ, the Cramer-extracted
  triple is a genuine `IsAperyConnectionCoeffsOn` witness on the
  *entire* corridor (not just the three probes). Bridge via
  `shifted_eq_extract` + `of_shifted_eqOn`.
- `d.has_extract_triple`, `d.has_extract_triple_mono` — Has-form +
  descent to sub-corridor.
- `d.F_shift_eq_extract_at` — pointwise reconstruction at a single
  corridor shift.
- `d.is_extract_triple_mono` — Is-form descent to any J ⊆ corridor
  (probes still in the full corridor).
- `d.extractTriple_restrictCorridor_eq` — extract triple (3-tuple) is
  invariant under `restrictCorridor` (rfl).
- `d.restrictCorridor_overlapShifts` (simp), `_overlapShifts_subset`,
  `GFA_isAperyConnectionCoeffsOn_overlapShifts_restrict` (Is),
  `GFA_hasAperyConnectionCoeffsOn_overlapShifts_restrict` (Has) —
  overlap geometry × GFA-on-overlap descend through `restrictCorridor`.

### Disk-shift generalization, ext-layer minimal data (added 2026-04-26 — iterations 118–120)

- `d.candidate_GFA_iff_F_on_disk_shifts` — generalization of
  `candidate_GFA_iff_F_on_overlapShifts` to any set `S` whose every
  shift lands in the disk; sub-corridor variant becomes a one-line
  specialization (`_restrict`).
- `AperyAnalyticExtension.toMinimalConnectionData` — every analytic
  extension upgrades unconditionally to ConnectionData with trivial
  corridor `{0}` (uses `HasAperyConnectionCoeffsOn.singleton_zero`).
  Three projection simp lemmas (corridor, F, ext).
- `ext.hasAperyConnectionData`, `HasAperyAnalyticExtension.toHasAperyConnectionData`
  — Has-level lifts; the two Prop wrappers collapse via the minimal
  lift.
- `ext.F_eq_GFA_on_small`, `ext.F_unique_on_small` — agrees_on_small
  as pointwise lemma; two ext agree on the unconditional disk.
- `ext.toMinimalConnectionData_extractRegular` (simp) — minimal data's
  regular extract = ext.F z₁ (rfl).
- `ext.toMinimalConnectionData_congr` — F-equality lifts to minimal-
  data equality.

### connectionResidual layer + right-endpoint reconstruction (added 2026-04-26 — iterations 121–126)

- `d.connectionResidual ε := aperyConnectionResidual d.F ε` — thin
  wrapper. With `_def` unfold, `_zero` (simp at ε=0), and `_via_GFA`
  (replace d.F by GFA when probe lands in disk).
- `d.extractHalf_eq_residual_form`, `_extractOne_eq_residual_form` —
  Cramer formulas in named-residual form (rfl). With
  `_eq_zero_of_residual_zero` corollaries: both probes' residuals
  vanish ⇒ singular extract is zero.
- `d.connectionResidual_eq_singular_part` — under hdet and -ε ∈
  corridor, residual = extractHalf·A_½(ε) + extractOne·V_1(ε). The
  *meaning* of the residual: it isolates the singular branches' value.
  Plus zero-of-singular-zero corollary.
- `d.F_right_endpoint` — F(z₁ - ε) = extractRegular·A_0(ε) +
  extractHalf·A_½(ε) + extractOne·V_1(ε). Lift of right_endpoint to
  ConnectionData.
- `d.connectionResidual_eq_zero_iff` — diagnostic: residual = 0 ⇔ F at
  -ε is purely regular (sub_eq_zero on the def).
- `d.GFA_right_endpoint`, `d.GFA_residual_eq_singular_part` —
  GFA-side reconstructions on disk-overlap. Bridge between numerical
  GFA values and connection-coefficient extract triple.
- `extractRegular_congr`, `extractHalf_congr`, `extractOne_congr`,
  `connectionResidual_congr` — all four quantities depend only on `F`;
  equal F-fields force equal extracts and residual.
- `d.det_ne_zero_probes_nonzero` — wrapper: hdet ≠ 0 ⇒ probes pairwise
  nonzero.

### connectionCoefficients triple + canonical layer (added 2026-04-26 — iterations 127–170)

`connectionCoefficients` packages the three extracts as a triple
`(a₀, a_½, a₁)`. Defined at three layers: data, ext, canonical.

**Data + ext layer triple API:**
- `(d|ext).connectionCoefficients ε₁ ε₂ : ℝ × ℝ × ℝ` — triple of
  named extracts. Three component-projection simp lemmas at each layer.
- `connectionCoefficients_congr` (data, ext) — F-equality ⇒ triple
  equality.
- `connectionCoefficients_swap` — invariant under probe swap; lifted
  through `extractHalf_swap` / `extractOne_swap`.
- `connectionCoefficients_diagonal` (raw, data, ext, canonical) —
  coincident probes collapse to `(a₀, 0, 0)` (with `a₀ = F z₁` /
  `extractRegular` / seed).
- `extract{Half,One}_self` (raw, data, ext) — `_diagonal` factor
  through these per-extract zero lemmas. Numerator ring-reduces to 0
  on coincident probes; `0 / Δ(ε,ε)` = 0 via `zero_div`.
- `connectionCoefficients_unique` (data) — corridor reconstruction +
  candidate uniqueness lifted to triple form.

**ext × data uniqueness via decomposition** (sub/inversion):
- `IsAperyConnectionCoeffsOn.sub_{regular,half,one}` — each branch
  subtraction is closed under the predicate (algebraic decomposition
  at the value level).
- `IsAperyConnectionCoeffsOn.sub_all` — all three together gives
  `IsAperyConnectionCoeffsOn 0 0 0` for the residual.
- `IsAperyConnectionCoeffsOn.eq_zero_of_pure_zero` — the residual
  with all-zero seeds is identically 0 on the corridor (value form).
- `IsAperyConnectionCoeffsOn.f_decomposes` — value-level forward
  identity: f decomposes as the explicit branch sum at the seed
  triple, on the corridor.
- `IsAperyConnectionCoeffsOn.of_F_decomposes` — inversion direction:
  explicit branch decomposition ⇒ predicate.

**Decomposition + GFA bridges:**
- `AperyAnalyticExtension.F_decomposes_via_coefficients_on` — F
  decomposes as the branch triple at `(extractR, extractH, extractO)`
  on the corridor.
- `AperyAnalyticExtension.GFA_decomposes_via_coefficients_on_disk` —
  same in GFA form on disk overlap (via `F_eq_GFA_on_small`).
- `AperyAnalyticExtension.connectionDataOfDecomposition` — explicit
  decomposition data → `AperyConnectionData` builder.
- `AperyAnalyticExtension.connectionCoefficients_eq_of_F_eq_on_corridor` —
  cross-ext invariance: same F on corridor ⇒ same triple at any
  probe pair.
- `connectionCoefficients_eq_of_F_eq_at_z1_on_disk` — same triple
  follows from agreement at z₁ alone (via canonical-disk form), under
  probe-disk hypotheses.
- `connectionCoefficients_eq_iff_F_eq_at_z1_on_disk` — iff form.

**Canonical layer:** parameterised purely by seed `c₀` and the probe
pair, ext-independent.
- `aperyCanonicalExtract{Half,One} c₀ ε₁ ε₂ : ℝ` — pure formula in
  `c₀` and explicit GFA values at the probes (no ext).
- `aperyCanonicalConnectionCoefficients c₀ ε₁ ε₂` — triple form.
- `extract{Half,One}_eq_canonical_on_disk` (ext) — ext-layer extracts
  factor through canonical at `c₀ = ext.F z₁` when both probes hit
  disk.
- `connectionCoefficients_eq_canonical_on_disk` — triple form.
- `connectionCoefficients_eq_canonical_iff_F_at_z1` — iff:
  `ext.connectionCoefficients = canonical c₀ ε₁ ε₂ ↔ ext.F z₁ = c₀`.
- `aperyCanonicalConnectionCoefficients_eq_iff` (simp) — canonical
  triples agree iff seeds agree (fst projection).
- Canonical swap + diagonal lemmas mirror the ext layer.

**Headline canonical statement (iter 170):**
- `AperyAnalyticExtension.GFA_decomposes_canonical_on_disk` — when
  all three (probes ε₁, ε₂ and corridor point t) hit the disk,
  `aperyGFAReal (z₁ + t)` decomposes as the branch triple at
  `(c₀, aperyCanonicalExtractHalf c₀ ε₁ ε₂, aperyCanonicalExtractOne
  c₀ ε₁ ε₂)` with `c₀ = ext.F z₁`. RHS contains no ext — only `c₀`
  and explicit GFA values at probes (through canonical extracts).
  The cleanest "knobless" right-endpoint identity.

The Frobenius-side connection-coefficient interface is now complete
across four layers with full bidirectional API. The remaining open
piece is the analytic Gap F (sharp `aₙ ∼ z₁⁻ⁿ/n^{3/2}`) lifting
`aperyGFAReal` past `1/64` to the full disk `|z| < z₁`, which would
discharge `HasAperyAnalyticExtension` and turn all extract-based
theorems unconditional.

### Cramer self-consistency + data-layer canonical mirror (iters 172–175)

After the iter 170 ext-layer headline, mirror atoms at the data layer
plus self-consistency at canonical probes:

- `aperyGFAReal_eq_canonical_rhs_at_probe1` (iter 172) — Cramer
  consistency: at probe ε₁, the canonical RHS evaluated at the canonical
  extracts equals the GFA value at z₁ - ε₁. Pure algebra (`field_simp
  [hdet]` + `ring` keeping `aperyConnectionDet` symbolic during
  field_simp).
- `AperyAnalyticExtension.GFA_right_endpoint_canonical_on_disk` (iter
  173) — t = -ε specialization of iter 170 with explicit
  `A_0/A_½/V_1` amplitude factorization via the three `_at_neg_eps`
  rewrites.
- `AperyConnectionData.{extractHalf,extractOne}_via_GFA_on_disk` +
  `_eq_canonical_on_disk` + `connectionCoefficients_eq_canonical_on_disk`
  (iter 174) — full data-layer mirror of the ext-layer canonical
  bridges. Closes the four-layer mirror.
- `AperyConnectionData.GFA_decomposes_canonical_on_disk` +
  `GFA_right_endpoint_canonical_on_disk` (iter 175) — data-layer
  headline + endpoint, paralleling iter 170/173.

### Right-endpoint via data + uniqueness chain (iters 176–184)

Closing the algebraic side of Gap E (three-branch linear independence):

- `AperyConnectionData.GFA_right_endpoint_via_data` (iter 176) — most
  natural right-endpoint form: uses `d.extractHalf, d.extractOne`
  directly (no canonical layer). Only ε needs disk; ε₁/ε₂ only need
  corridor + nonzero connection det.
- `aperyBranchTriple_canonical_swap` (iter 176) — RHS of canonical
  decomposition is invariant under (ε₁, ε₂) swap.
- `aperyBranch_linearly_independent_at_two_probes` (iter 177) — pure
  2×2 Cramer fact: `α·A_½(ε) + β·V_1(ε) = 0` at two probes with
  `aperyConnectionDet ≠ 0` forces `α = β = 0`.
- `aperyBranchAmplitudes_unique_at_two_probes` (iter 178) — uniqueness
  of `(c_h, c_1)` from combination value at two probes.
- `aperyBranchTriple_endpoint_unique` (iter 178) — full triple
  uniqueness when c₀ shared: c₀ cancels, two-dimensional Cramer
  applies.
- `AperyConnectionData.extracts_unique_from_right_endpoint` (iter 179)
  + ext-layer mirror (iter 180) — any pair `(c_h, c_1)` compatible
  with `d.extractRegular` and the GFA at two disk probes must equal
  Cramer extracts.
- `apery3Det ε₁ ε₂ ε₃` (iter 181) — 3×3 Cramer det along the A_0
  column, isolates simultaneous linear dependence of A_0, A_½, V_1.
- `aperyBranch_linearly_independent_at_three_probes` (iter 181) —
  3-probe linear independence: each `α_X · apery3Det = cofactor
  combination of the three equations` (verified by `ring`); h_i = 0
  forces `α_X · apery3Det = 0`.
- `aperyBranchTriple_unique_at_three_probes` (iter 182) — three-
  dimensional analogue of iter 178 endpoint uniqueness; c₀ no longer
  free.
- `AperyConnectionData.triple_unique_from_three_disk_probes` (iter 183)
  + ext-layer mirror (iter 184) — closes c₀ uniqueness on the data
  layer too: any candidate triple matching GFA at three disk probes
  must equal `(d.extractRegular, d.extractHalf ε₁ ε₂, d.extractOne
  ε₁ ε₂)`.

Gap E status after iter 184: algebraic side fully closed across four
layers. Open: a concrete witness `apery3Det ε₁ ε₂ ε₃ ≠ 0` for some
explicit probes, which depends on the analytic form of A_0, A_½, V_1
as Frobenius series.

### apery3Det algebraic toolkit + 3-probe canonical packaging (iters 186–195)

Following the uniqueness chain, expand the `apery3Det` symbol into a
usable algebraic gadget and package the 3-probe canonical recovery
into a clean ℝ × ℝ × ℝ interface mirroring the existing 2-probe
canonical layer.

- **Symmetries (iter 186):** `apery3Det_swap12 / swap13 / swap23`
  (antisymmetry under any single transposition, by `unfold + ring`),
  `apery3Det_self12 / self13 / self23` (`@[simp]`, vanishes when two
  probes coincide), `apery3Det_cycle` (cyclic shift identity).
- **Conifold-collapse cases (iter 187):** `apery3Det_first_zero /
  second_zero / third_zero` (`@[simp]`) — when any probe equals zero,
  the 3×3 det collapses to the 2×2 `aperyConnectionDet` of the other
  two probes (the A_0 column kills the corresponding row, leaving the
  A_½/V_1 minor). Reduces 3-probe analysis to 2-probe at the apex.
- **Alternative cofactor expansions (iter 188):**
  `apery3Det_expand_half_column` and `apery3Det_expand_one_column` —
  same value as the def (which expands along A_0), but expanded along
  A_½ and V_1 columns respectively. Useful when proofs need the
  factor-out structure to involve A_½ or V_1 instead of A_0.
- **`aperyCanonicalExtractRegular3` (iter 189) + ext mirror (iter 190):**
  pure GFA-only formula recovering c₀ via Cramer along the A_0 column
  when 3-probe det is nonzero. The data-layer bridge derives
  `d.extractRegular · apery3Det = (cofactor combination of three
  right-endpoint identities)` by `unfold + ring`, then closes via
  `field_simp [h3det] + linarith [hkey]`. Ext mirror is a one-line
  `of_witness` delegation.
- **`aperyCanonicalExtractHalf3` (iter 191) and `aperyCanonicalExtractOne3`
  (iter 192) + ext mirrors (iter 193):** half3 / one3 are defined as
  `aperyCanonicalExtractHalf (aperyCanonicalExtractRegular3 ε₁ ε₂ ε₃) ε₁ ε₂`
  (and similarly for one) — composing the 3-probe `c₀` recovery with
  the existing 2-probe canonical c_h / c_1 formula. Each data-layer
  bridge `unfolds` the def then chains the 2-probe canonical bridge
  with the 3-probe regular bridge. Ext mirrors via `of_witness`.
- **Triple3 packaging (iter 194 data, iter 195 ext):**
  `aperyCanonicalTriple3 ε₁ ε₂ ε₃ : ℝ × ℝ × ℝ` bundles
  `(extractRegular3, extractHalf3, extractOne3)`.
  `AperyConnectionData.canonicalTriple3_eq_on_disk` proves the data-
  layer triple `(d.extractRegular, d.extractHalf ε₁ ε₂, d.extractOne
  ε₁ ε₂) = aperyCanonicalTriple3 ε₁ ε₂ ε₃` via `Prod.ext` + the three
  individual extract bridges. Ext mirror: one-line `of_witness`.

Status after iter 195: the canonical-extracts API is now a complete
3 (extracts) × 2 (layers: data / ext) × 2 (forms: 2-probe canonical
seed-parameterized / 3-probe canonical seedless) matrix, plus the
packaged `triple3` form. All bridges require: corridor membership for
the probes, disk membership of the conifold-shifted points, and
nonvanishing of `aperyConnectionDet` (2-probe) or `apery3Det` (3-
probe). Gap E remains open on the analytic side: producing a
witness `apery3Det ε₁ ε₂ ε₃ ≠ 0` requires the Frobenius-series form
of A_0, A_½, V_1.

### Seedless GFA decompositions + Gap E foundations (iters 197–211)

Building on the 3-probe canonical interface, push the chain through to
ready-made GFA decomposition statements that take the right-endpoint
identity all the way to "GFA value = canonical-extracts triple
evaluated at branch superposition" without exposing any seed
parameter.

- **`GFA_right_endpoint_via_canonical3_on_disk` (iter 197 data, iter 198
  ext):** Given three valid disk probes, GFA at the right endpoint
  rewrites as `extractRegular3 · A_0 + extractHalf3 · A_½ +
  extractOne3 · V_1`. Proof = chain `GFA_right_endpoint_via_data` with
  the three `extract_eq_canonical3_on_disk` rewrites.
- **`GFA_decomposes_canonical3_on_disk` (iter 199 data, iter 200 ext):**
  Same statement at *arbitrary corridor t* (not just right endpoint);
  the conclusion is `aperyGFAReal (z₁ + t) = aperyBranchTriple
  extractRegular3 extractHalf3 extractOne3 t`. Proof needs
  `rfl` after the rewrites because half3/one3 don't auto-unfold.
- **Probe-distinctness from `apery3Det ≠ 0` (iter 201):**
  `apery3Det_ne_zero_probes_distinct` — pairwise distinctness of three
  probes follows from non-vanishing 3-det by `subst + simp` in each
  collision case.
- **Numerical sandwich for `z₁` (iters 202, 204):**
  `aperyConifoldZ1Poly_gt_one_div_64` and `_lt_one_div_32` —
  `z₁ ∈ (1/64, 1/32)` proved via rational rigorous bounds on `√2`
  (`543/384 < √2 < 1087/768`) discharged by `nlinarith` from
  `(√2)² = 2`. Sandwich confirms `z₁ ∉ Set.Ico 0 (1/64)` (so the
  conifold is just outside the disk) and `z₁ < 1/32` (so multiples
  like `z₁/2`, `2z₁/3`, `3z₁/4` are all in the disk-admissible range).
- **Disk membership ↔ ε range translation (iter 203):**
  `disk_membership_iff_eps_in_range` — `z₁ + (-ε) ∈ Set.Ico 0 (1/64)
  ↔ ε ∈ Set.Ioc (z₁ - 1/64) z₁`. Trivial linarith both directions;
  serves as the bridge between the disk-side and corridor-side
  hypothesis languages.
- **Three concrete admissible probes (iters 205–209):**
  `half_z1_in_disk_eps_range` etc. for ε = z₁/2, 2z₁/3, 3z₁/4. Each
  proven from the numerical sandwich (z₁ < 1/32 ⟹ z₁/2 < 1/64 ⟹
  z₁ - z₁/2 = z₁/2 > z₁ - 1/64 since 1/64 < z₁/2). Bundled
  `..._disk_hypothesis` lemmas restate as direct
  `Set.Ico 0 (1/64)` membership of the conifold-shifted probe, ready
  to feed into the GFA-decomposition bridges. Pairwise distinctness
  `standard_three_probes_distinct` since `z₁/2 ≠ 2z₁/3 ≠ 3z₁/4` for
  `z₁ > 0`.
- **Standard-probes wrapper (iter 210 data, iter 211 ext):**
  `GFA_decomposes_canonical3_standard_probes` — same conclusion as
  `GFA_decomposes_canonical3_on_disk` but with the three disk
  hypotheses baked-in. Caller now needs only corridor memberships of
  the three standard probes plus the two non-vanishing det
  hypotheses.

Status after iter 211: every layer above the analytic det
non-vanishing question is closed. The standing open atom is
`apery3Det (z₁/2) (2z₁/3) (3z₁/4) ≠ 0` (and the corresponding
2-probe `aperyConnectionDet (z₁/2) (2z₁/3) ≠ 0`). These require the
Frobenius series structure: at small `ε`, leading orders are
`A_0 ≈ 1`, `A_½ ≈ √ε`, `V_1 ≈ -ε`, so the 3×3 matrix is
asymptotically Vandermonde-like in `(1, √ε, ε)`. For the standard
probes (ε of size `≈ z₁ ≈ 0.029`), the leading-order argument is no
longer free; one needs explicit truncation bounds on the regular
Frobenius series remainder.

### HalfCore/OneCore + factored-form Vandermonde toolkit (iters 213–220)

Build the algebraic infrastructure for attacking the analytic det
non-vanishing target by exposing the leading-order Vandermonde
structure.

- **`aperyBranchHalfCore` / `aperyBranchOneCore` (iter 213):** Strip
  the `√ε` and `(−ε)` prefactors from `aperyBranchAmplitude_half` and
  `aperyBranchValue_one` respectively. Both are `frobeniusValue (...)
  ρ 1 (−ε)` for ρ ∈ {1/2, 1}. `_at_zero = 1` for both (m=0 series
  term equals seed `c₀ = 1`). `_factored` lemmas: `A_½ = √ε · HalfCore`
  and `V_1 = (−ε) · OneCore`, both by `rfl`.
- **`aperyConnectionDet_factored` (iter 214):** For `0 ≤ ε₁`,
  `0 ≤ ε₂`, factor out `√ε₁·√ε₂` from the 2×2 connection det:
  `Δ = √ε₁·√ε₂ · (√ε₁·H₂·O₁ − √ε₂·H₁·O₂)`. Proof via `linear_combination`
  with `Real.mul_self_sqrt` injecting `√εᵢ² = εᵢ`. The bracket exposes
  the Vandermonde-like structure that limits to `√ε₁ − √ε₂` at unit
  cores.
- **`apery3Det_factored` (iter 215):** Apply 2-probe factored form to
  each of the three cofactor minors in `apery3Det`. Each cofactor term
  has its own `√ε_a·√ε_b` prefactor; the three terms don't share a
  common `√ε₁·√ε₂·√ε₃` factor. Proof closes by `rw` chain alone.
- **`aperyConnectionDet_ne_zero_iff_bracket` (iter 216):** For
  `0 < εᵢ`, `Δ ≠ 0` reduces to bracket non-vanishing (the
  `√ε₁·√ε₂` prefactor is positive). Operational form for downstream
  hypothesis discharge.
- **`apery3Det_unit_cores_eq_neg_vandermonde` (iter 217):** Polynomial
  identity at the leading-order ideal limit: when all `Z_i = H_i =
  O_i = 1`, `apery3Det = −(√ε₂−√ε₁)(√ε₃−√ε₁)(√ε₃−√ε₂)`. Closes by `rw
  + ring`. Hypotheses literally hold only at `ε = 0`, but the
  polynomial identity is a useful structural milestone.
- **`vandermonde_sqrt_ne_zero` (iter 218):** Standard Vandermonde
  non-vanishing in sqrt coords: nonneg pairwise-distinct ε_i ⟹
  `(√ε₂−√ε₁)(√ε₃−√ε₁)(√ε₃−√ε₂) ≠ 0`. Three `mul_ne_zero` calls each
  using `Real.sqrt_inj` injectivity on nonneg reals.
- **`apery3Det_unit_cores_ne_zero` (iter 219):** Composes 217 + 218 to
  give: under positive distinct probes and unit cores,
  `apery3Det ≠ 0`. The ideal-limit reference for the genuine analytic
  target.
- **`aperyConnectionDet_unit_cores_{eq,ne_zero}` (iter 220):** 2-probe
  siblings of 217/219. At unit cores `Δ = √ε₁·√ε₂·(√ε₁−√ε₂)`; for
  positive distinct probes `Δ ≠ 0`.

Status after iter 220: the algebraic / Vandermonde / ideal-limit
infrastructure is complete. The remaining gap is genuine analysis:
to apply the unit-core lemmas at the standard probes, one would need
`HalfCore (z₁/2) = 1` etc., which is **not** literally true (those
core values are nontrivial transcendental numbers). The actual non-
vanishing argument needs either:
1. Series remainder bounds: `|HalfCore − 1| < ε` for `|ε|` small
   enough, plus continuity from analyticity of `frobeniusValue` on
   the convergence disk;
2. Direct numerical computation of partial sums with rigorous
   truncation error bounds at the specific probes.

Both routes go through Gap A in the original taxonomy (limit
machinery / continuity instantiation for the apery conifold
polynomial). That gap is non-trivial — explicit `M₀`, `B`,
polynomial coefficient bounds for the Frobenius recurrence at the
apery instance.

## Session 2026-04-26 / 2026-04-27: A4 + A5 closure

### A4 — connection coefficients, right-side Y₀+Y₁ basis (task #13)

Tonight built the full connection-coefficient theory across four
layers (predicate / data / ext / GFA) for the Apéry conifold:

- **Seed identification:**
  - `IsAperyConnectionCoeffsOn.value_at_z1`: a₀ = f(z₁) (transcendental anchor).
  - `IsAperyConnectionCoeffsOn.eq_extract`: full triple via Cramer at 2 probes.
  - `seeds_unique`: seeds match across corridors sharing 3 probe points.
  - `value_via_extracts`: pointwise transport via the extract triple.
- **Bundled identifications:**
  - `seed_triple_eq_extracts` (data + ext layers).
  - `is_extract_triple` (data + ext): canonical predicate at standard extracts.
- **Branch decomposition forms:**
  - `eq_branches_sum`: the explicit yAperyZero + yAperyHalf + yApery sum.
  - 6 single/dual basis forms: `eq_yZero_plus_yOne_of_no_half`,
    `eq_yZero_plus_yHalf_of_no_one`, `eq_yZero_of_only_regular`,
    `eq_yOne_of_only_one`, `eq_yHalf_of_only_half`.
- **Right-side basis** (key A4 answer):
  - `eq_yZero_plus_yOne_on_right`: for `t ≥ 0` in corridor, the half
    branch automatically drops (√(-t) = 0); value = `yAperyZero a₀ t +
    yApery a₁ t`. Lifted to data / ext / GFA layers.
  - Capstones: `right_value_independent_of_half`,
    `right_value_eq_of_seeds_match` — half seed plays no role at the
    right corridor endpoint, so forward continuation needs only
    `(a₀, a₁)`.
- **Left-side Y_½ extraction:**
  - `yHalf_isolated`: `f(z₁+t) − Y₀ − Y₁ = yAperyHalf a_half t` (pure algebra).
  - `frobeniusValue_half_via_sqrt_neg_t`: for `t < 0`, divide by
    `√(-t) > 0` to recover the underlying `frobeniusValue` at indicial
    root 1/2. Lifted to data / ext / GFA layers.
- **GFA closed-form extracts:**
  - `aperyExtractHalf_via_GFA`, `aperyExtractOne_via_GFA`: closed
    forms expanding both probes via raw GFA residuals, modulo `F(z₁)`
    (the transcendental anchor).

### A5 — corridor patching toolkit (task #14)

Generic patching infrastructure for combining Has-witnesses across
overlapping corridors:

- **Set-level:** `mono`, `union` (binary), `iUnion` (indexed),
  `biUnion_finset`, `inter_left/right`, `empty`, `congr_set`.
- **Three-probe merge:**
  - `IsAperyConnectionCoeffsOn.merge_via_three_probes` (predicate):
    two witnesses with possibly different seeds patch into a single
    witness on `I₁ ∪ I₂` if they share `{0, -ε₁, -ε₂}` with non-
    degenerate Cramer determinant. Combines `seeds_unique` + `union`.
  - `AperyConnectionData.has_conn_union_via_three_probes` (data layer
    lift): given an external `Has`-witness on `J` overlapping
    `d.corridor` at three probes, the `Has`-property extends to
    `d.corridor ∪ J` at canonical extracts.
  - `AperyAnalyticExtension.has_conn_union_via_three_probes` (ext-
    layer convenience wrapper).
- **`extendCorridor` constructor:** `AperyConnectionData.extendCorridor`
  builds a new data object on `d.corridor ∪ J`, preserving `F` and
  the underlying analytic extension. Seven simp/utility lemmas:
  `_F` (rfl), `_corridor` (= union), `_extractRegular/Half/One` (rfl
  preserved), `_corridor_subset`, `_J_subset`.
- **Capstones on extended data:** the right-side Y₀+Y₁ basis and the
  left-side Y_½ isolation/`frobeniusValue` extraction all transparently
  lift through `extendCorridor` (since extracts are rfl-preserved).
- **Chain induction:** `has_conn_on_iUnion_of_three_probes` — given
  an indexed family of Has-witnesses each containing the global probe
  triple, the Has-property extends to `d.corridor ∪ ⋃ i, J i` at
  canonical extracts.

### Operational meaning

A4 says: at the right corridor endpoint, only `(a₀, a₁)` matter — the
half-branch contribution is invisible. A5 says: any external
Has-witness on a set sharing three probe points with the existing
corridor can be patched in, automatically inheriting the canonical
extracts. Together these enable forward analytic continuation
*within the Frobenius disk around z₁* without losing track of the
seeds anchored at z₁.

The remaining hard step (gap B in earlier taxonomy) — pushing beyond
the Frobenius disk via a chain centered at moving points — still
requires defining a "Frobenius disk at point z*" object; the current
`IsAperyConnectionCoeffsOn` predicate is intrinsically z₁-anchored.

(Note 2026-04-27: gap B is now under active construction —
`AperyAnalyticDisk`, `AperyAnalyticDiskAt`, `AperyLocalAnalyticExtension`,
`chainGlue`, `ofGFAChain` — see commits 5cddf3e4 onward. The
"intrinsically z₁-anchored" obstruction is being resolved via
`AperyAnalyticDiskAt` (analytic-at moving center) + `chainGlue`
(piecewise glued analytic function across overlapping disks).
· by Zinan · active · 2026-04-27)

## Session 2026-04-28: Poincaré-Perron + CompanionMatrix + Jordan 分解

工作链：Frobenius coefficient growth bound 的 3 个 sorry → 转 Poincaré-Perron 通用框架 → 五个 helper 全部证完 → Jordan 分量化简 → 发现 zSubdom 设计错误。

### PoincaréPerron.lean — 五个 helper 全证完

`a5b08b08`–`f90db355` 之间的 commit 链：

- `perturbed_geometric_decay`：`|aₘ₊₁| ≤ |λ|·|aₘ| + εₘ` with `Σεₘ < ∞`, `|λ| < 1` ⇒ `|aₘ| → 0`。
- `summable_of_perturbed_contraction`：扰动 contraction 下序列差和 summable。
- `bounded_of_summable_diffs`：序列差 summable ⇒ 序列 bounded。
- `rescaled_bound_of_firstDiff_bound`：bounded first-difference ⇒ rescaled growth ≤ linear。
- `growth_bound_of_rescaled_bound`：rescaled ≤ linear ⇒ 原序列 ≤ linear · |ev₁|^m。

PoincaréPerron.lean:269 还有一个 sorry，是 cast cleanup（不影响主架构）。
· by Zinan · stable · 2026-04-28

### CompanionMatrix.lean — Jordan 接口 OK，scalar 分解出 BUG

Commit `0ad8b67b`：CompanionMatrix.lean 文件创建，定义 `ConvergentThreeStep` 结构。
Commit `42c4de68`：`poincare_perron_of_jordan_components` 定理（已完整证明）—— 给出
"3 component bounds → growth bound" 的接口。

Commit `70be12f7` + `f48dbfe1`：scalar Jordan 分解尝试。定义
```
zSubdom c ev₁ ev₂ m := (c m − ev₁ · c (m−1)) / (ev₂ − ev₁)
wSubdom c ev₁ ev₂ m := zSubdom c ev₁ ev₂ m / ev₂ ^ m
```
和对应 `zSubdom_recurrence` lemma。

**Const-coeff sanity check 失败（2026-04-28 night, by Zinan）：**

设 `α(m) ≡ lim_a, β(m) ≡ lim_b, γ(m) ≡ lim_c`，由 char_poly
`x³ − lim_a·x² − lim_b·x − lim_c = (x−ev₁)²·(x−ev₂)` 展开得：
- `lim_a = 2·ev₁ + ev₂`
- `lim_b = −(2·ev₁·ev₂ + ev₁²)`
- `lim_c = ev₁² · ev₂`

代入 `c(m+1) = lim_a·c(m) + lim_b·c(m−1) + lim_c·c(m−2)`，化简
`z₃(m+1) − ev₂·z₃(m)`：
```
(ev₂ − ev₁) · [z₃(m+1) − ev₂·z₃(m)]
  = c(m+1) − (ev₁+ev₂)·c(m) + ev₁·ev₂·c(m−1)
  = ev₁ · [c(m) − (ev₁+ev₂)·c(m−1) + ev₁·ev₂·c(m−2)]
  = ev₁ · (ev₂ − ev₁) · [z₃(m) − ev₂·z₃(m−1)]
```

所以 const-coeff 下 `z₃(m+1) = ev₂·z₃(m) + ev₁·(z₃(m) − ev₂·z₃(m−1))`，**不是**
单步 `z₃(m+1) = ev₂·z₃(m)`。原因：`ev₁` 是 double root，单次差分 `c − ev₁·prev`
只杀掉一阶 ev₁ 分量，残留 `B·ev₁^m`。

下游影响：在 `c(m) = (A + B·m)·ev₁^m + C·ev₂^m` 下，
`z₃(m) = B·ev₁^m/(ev₂−ev₁) + C·ev₂^(m−1)`，
`wSubdom = z₃/ev₂^m = (B/(ev₂−ev₁))·(ev₁/ev₂)^m + C/ev₂ → ∞`。

所以 `f48dbfe1` 提交的 `zSubdom_recurrence` 陈述漏了一项；即使把那个 sorry 填了，下游 `w₃ bounded` 也证不出来。

### Decision (2026-04-28 night, by Zinan)：用 (D−ev₁)² 二阶差分

正确的 ev₂ 提取算子是 `(shift − ev₁)²`：对 `(A+B·m)·ev₁^m + C·ev₂^m`，
```
c(m) − 2·ev₁·c(m−1) + ev₁²·c(m−2)
  = ev₁^m · [(A+Bm) − 2(A+B(m−1)) + (A+B(m−2))]
    + ev₂^(m−2) · C · (ev₂² − 2·ev₁·ev₂ + ev₁²)
  = 0 + C · (ev₂ − ev₁)² · ev₂^(m−2)
```

所以新定义
```
zSubdom c ev₁ ev₂ m := (c m − 2·ev₁·c(m−1) + ev₁²·c(m−2)) / (ev₂ − ev₁)²
```
能彻底打掉 `ev₁` 双重根分量，提取 pure ev₂。
`wSubdom = zSubdom / ev₂^m` 真正 bounded，
`poincare_perron_of_jordan_components` 接口（`hdecomp` 用 `|ev₂|^m`）保持不变。

正在执行 Avenue (B)（见 projects/Ripple/DOCTRINE.md）。
· by Zinan · working · 2026-04-28

### Lesson learned（2026-04-28 by Zinan, stable）

写完一个 lemma 立即用 const-coeff 闭式解 sanity check。`zSubdom_recurrence` 应该在
落盘前先验证 `c(m) = ev₁^m`、`c(m) = m·ev₁^m`、`c(m) = ev₂^m` 三种情形 RHS 是否
等于 LHS——这样就不会把错误陈述提交进 git。

### Avenue (B) update（2026-04-28 18:30 by Zinan, stable）

`zSubdom` 已重写为 `(c m − 2·ev₁·c(m−1) + ev₁²·c(m−2))/(ev₂−ev₁)²` (二阶差分 (D−ev₁)²)，
建立了三个 lemma + 1-step recurrence form：
```
zSubdom(m+1) = ev₂·zSubdom(m) + perturbation/(ev₂−ev₁)²
```
where `perturbation = (α(m)−α∞)·c(m) + (β(m)−β∞)·c(m−1) + (γ(m)−γ∞)·c(m−2)`.

`lake build`: 0 error, CompanionMatrix.lean 仅剩 1 sorry (`poincare_perron_growth_bound`
on line 92).

**但下游 `wSubdom = zSubdom/ev₂^m` bounded 仍证不出来**（bootstrap obstruction）：
即使 `|c(k)| ≤ C·(k+1)·|ev₁|^k` 假设成立，`|ε(m)/ev₂^(m+1)|` 在因子 `(|ev₁|/|ev₂|)^m` 下
发散，不 summable。原因：variable-coeff 下 `zSubdom` 不再是纯 ev₂^(m−2)，多出
`O(rate·ev₁^m/m)` 的尾巴。

**结论：** `poincare_perron_growth_bound` 需要 Birkhoff 渐近基构造或离散
Lyapunov 函数，是多日工作量。今晚收尾，sorry 保留 + 添加 Birkhoff approach 注释。
· by Zinan · stable · 2026-04-28

## Abandoned avenues

_Approaches tried and dropped. Each entry: what · why dropped ·
revisit-if. Recording these prevents future-me or downstream agents
from re-attempting the same dead-ends._

- **One-shift zSubdom `(c − ev₁·prev)/(ev₂−ev₁)` for double-root case**
  · 单次差分留下 `B·ev₁^m` 残留，下游 `wSubdom = z/ev₂^m` 必爆 ·
  revisit-if: 如果 ev₁ 退化成 simple root（等价于 `ev₁ ≠ ev₂`，三个特征值都简单），
  这条路恢复有效，因为没有广义本征空间。
  · by Zinan · stable · 2026-04-28

## 2026-04-29 session: Birkhoff 两项 asymptotic 数学结构 + bootstrap handoff

### Session 累计成果

33 closures + 1 forward-ref bug fix + 47 commits this session.

**完整代数前置层 EXHAUSTIVELY done (in `AperyGeneratingFunction.lean`):**

- 24 sub-lemmas (3 ρ-cases × 8): 3step_recurrence, denom_explicit,
  w_{m,m-1,m-2}_explicit, 3step_closed_form, w_m_simplified, alpha/beta/gamma_explicit_form
- 9 explicit recurrence coefficient defs (ρ-cases × {α, β, γ}):
  `aperyAlpha{One,Half,Zero}`, `aperyBeta{One,Half,Zero}`, `aperyGamma{One,Half,Zero}`
- 3 limit constants noncomputable defs:
  `aperyAlphaInf := K'/(2K)`, `aperyBetaInf := B/K`, `aperyGammaInf := 1/K`
- 6 char poly identities (raw + α∞/β∞/γ∞ form):
  - `aperyConifold_charPoly_dominantEv_identity`: K'·z/2 + B·z² + z³ = K
  - `aperyAlphaInf_z1_identity`: α∞·z + β∞·z² + γ∞·z³ = 1
  - `aperyConifold_charPoly_dominantEv_double_root`: K'·z + B·z² = 3K
  - `aperyAlphaInf_z1_double_root`: 2α∞·z + β∞·z² = 3
  - `aperyConifold_charPoly_thirdRoot_identity`: K = -24√2·z²
  - `aperyConifold_charPoly_vieta_sum_identity`: 12√2·K' = K(1151+816√2)
- `aperyConifold_birkhoff_L_cancellation`: B·z² + 2z³ = -K
- `aperyBetaInf_z1_birkhoff_L`: β∞·z² + 2γ∞·z³ = -1 (α∞ form)
- 5 exact-difference formulas:
  `aperyAlpha{One,Half,Zero}_sub_alphaInf`, `aperyBetaOne_sub_betaInf`, `aperyGammaOne_sub_gammaInf`
- **Divided 3-step recurrence form for ρ=1**:
  `aperyFrobenius_one_explicit_recurrence`: c(m+1) = α(m)·c(m) + β(m)·c(m-1) + γ(m)·c(m-2)
  via piecewise mul_denom sub-lemmas + hK_ne' normalization
  (`Real.sqrt 2 * 13848 → 13848 * Real.sqrt 2`)
- **Birkhoff infrastructure**:
  - `aperyBirkhoffResidualOne (K∞ L∞ : ℝ) (m : ℕ): R(m) := c(m) - (K∞·m + L∞)·z⁻ᵐ` (def)
  - `aperyBirkhoffForcingOne (K∞ L∞ : ℝ) (m : ℕ)`: perturbation Δ(m) (def)
  - `aperyFrobenius_one_birkhoff_decomposition`: c(m) = leading + R(m)
  - `aperyConifold_birkhoff_ansatz_preserved`: limit recurrence preserves K∞·m + L∞ exactly
    (linear_combination certificate: `(K∞·m + L∞)·h_eigen - K∞·h_L_α`)

### Birkhoff 数学发现 (核心)

**正确的 ratio_bound bootstrap invariant** 不是 dual K_low/K_high bound (推不出 (1+1/m) factor),
而是 SHARP 两项 asymptotic:
```
c(m) = (K∞·m + L∞)·z⁻ᵐ + R(m)  其中 |R(m)| ≤ M·ρ⁻ᵐ, ρ > z
```

关键: K∞ 和 L∞ 项 cancellation 的代数证书 = 已证的两个 char poly identity:
- K∞ 项 cancellation = `aperyAlphaInf_z1_identity` (eigenvalue at 1/z)
- L∞ 项 cancellation = `aperyAlphaInf_z1_double_root` 等价于 `aperyBetaInf_z1_birkhoff_L`
  (双根 derivative 消)

两个 char poly identity 共同 perfectly preserve 两项 ansatz (无残差 — 已证 via
`aperyConifold_birkhoff_ansatz_preserved`). R(m) 满足 SAME recurrence as c(m) 但
leading 两项已 cancel, dominant 项变成 subdominant eigenvalue -1/(24√2)
(|−1/(24√2)| ≈ 0.0295, 比 dominant |1/z₁| ≈ 33.97 小约 1000 倍).

**数值预测:** R(m) decay 速率 ≈ 0.0295^m → 0, c(m) ≈ K∞·m·z⁻ᵐ + bounded R.
Then c(m+1)/c(m) ≈ z⁻¹·(K∞·(m+1) + L∞)/(K∞·m + L∞) ≈ (1/z)·(1 + 1/m). ✓

### 下次 session 接手清单 (优先级降序)

1. **R recurrence 闭合** (`aperyBirkhoffResidualOne_recurrence`):
   `R(m+1) = α(m)·R(m) + β(m)·R(m-1) + γ(m)·R(m-2) + Δ(m)`

   **当前阻碍**: ring tactic 在 multi-power-z atoms (z⁻ᵐ, z⁻⁽ᵐ⁻¹⁾, z⁻⁽ᵐ⁻²⁾, z⁻⁽ᵐ⁺¹⁾)
   + nat-subtraction casts (↑(m-1), ↑(m-2), ↑(m+1)) 上挂. 已尝试 push_cast /
   hmcast0/1/2 / linear_combination h_div, 部分进展 (m-1, m-2 cast 解决了,
   还差 m+1).

   **建议路径**: 加 `hmcast0 : ((m+1 : ℕ) : ℝ) = (m : ℝ) + 1` using `push_cast; ring`,
   配合已有 hmcast1/2, 然后 `linear_combination h_div`. (我 session 末尝试到这一步,
   没 build 验证 — 用户切换 session 中断.) 见 git stash 或 commit `8cf96831`
   附近的状态.

2. **R bootstrap (subdominant decay rate)**:
   选 K∞, L∞ 让 R 在 [M₀, M₀+2] 满足初值匹配, 然后 induction 维护
   `|R(m)| ≤ M·(1/(24√2))^m`. 用 R recurrence 上一步 + perturbation 控制
   (Δ(m) ≤ z⁻ᵐ/m 用 sub_alphaInf 等).

3. **ratio_bound 闭合**: 用 Birkhoff sharp asymptotic 推 c(m+1)/c(m) → 1/z,
   matches (1/z)·(1+1/m). 直接代数.

4. **ρ=1/2 + ρ=0 平行**: 当前 explicit_recurrence 只 ρ=1 有. 写 parallel
   `aperyFrobenius_{half,zero}_explicit_recurrence` (相同 piecewise mul_denom
   pattern), 然后重复 1-3.

### Lean tactic notes (避坑)

- **ring 在 multi-c × poly(m, √2) 上能力上限**: 用 piecewise sub-lemma matching
  (3 个 mul_denom lemma 各自单 c-atom 的 ring) 然后 mul_right_cancel₀ + ring 收尾.
- **field_simp 不识别 (19584 - √2*13848) ≠ 0**: 需要 hK_ne' 显式 rewrite
  `Real.sqrt 2 * 13848 → 13848 * Real.sqrt 2` 让形式匹配 hypothesis.
- **Apéry identity 2·Q' = 3·P''**: rewrite `(5187 - 3672√2) → 3·(3458-2448√2)/2`
  在 closed_form 中, 为 alpha simplification 关键.
- **char poly identities certificate 套路**: `linear_combination ((coef)·√2 + const) * hs`
  where `hs : (Real.sqrt 2)^2 = 2`.

### Build 状态

`lake build` 0 errors, 3 sorries (ratio_bound family 不变).

· by Zinan · active · 2026-04-29
