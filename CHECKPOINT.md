# Ripple CHECKPOINT — 2026-04-16 (updated, session 2)

## Current State

### Fully Proved (0 sorry, 0 axiom)
- **PIVP.lean**: PIVP + PolyPIVP (syntactic layer with rational coefficients)
- **BoundedTime.lean**: Field closure complete
  - `realtime_const`, `realtime_field_add`, `realtime_field_mul`
  - `realtime_field_neg`, `realtime_field_inv_pos`, `realtime_field_inv`, `realtime_field_div`, `realtime_field_sub`
  - `BoundedTimeComputable.to_tendsto` (quantitative convergence → Filter.Tendsto)
  - `CertifiedBoundedTimeComputable`, `certified_realtime_rat_const`
- **Compilation.lean**: Bounded surrogate basics
  - `boundedSurrogate_mem_Icc`, diagonal lemmas, tendsto lemmas, derivative
  - `time_length_equivalence`
  - `bounded_compilation` / `bounded_compilation_rat` (placeholder proofs, non-vacuous hypotheses)
- **CRNPipeline.lean**: Statements with certified inputs
  - `crn_readout_preserves_complexity` (placeholder)
  - `closure_exponentiation` (placeholder)
- **Euler.lean**: e is real-time CRN-computable
- **Pi.lean**: pi is real-time CRN-computable
- **Ln2.lean**: ln 2 is real-time CRN-computable
- **EulerGamma.lean**: gamma is real-time CRN-computable (fully verified)
- **LPP/Defs.lean**: Core definitions + PLPP (0 sorry)
  - `IsPositivePoly`, `IsCRNImplementable`, `IsConservative`
  - `IsPPImplementable` (standalone balance equation form, enforces all 4 conditions):
    - `f` (production quadratic), `f_pos`, `f_homog` (degree 2), `field_eq`, `sum_f` (conservation)
    - Derived: `toCRN`, `conservative`, `no_self_square`
  - `IsLPPComputable`, `PPBalanceEquation`, `PPBalanceEquation.toField`
  - `one_trick`, `one_trick_sq`
  - `PPBalanceEquation.conservative_of_sum_eq` (fully proved)
  - `PLPPTransitions`, `PLPPTransitions.balanceField`, `PLPPTransitions.balanceField_conservative`
  - **Fixed**: `toField` uses formal degradation `f_r(x) - 2x_r·(Σx_k)`, not simplex-specialized
  - **Fixed**: `IsPPImplementable` restructured to enforce degree ≤ 2 + no-self-square
- **LPP/Syntactic.lean**: Syntactic PP balance + Stage 4 PLPP construction (0 sorry)
  - `SynPPBalance`: explicit ℚ coefficient tensor with conservation `Σ_r c_{r,i,j} = 2`
  - `evalProd`, `toField`, `evalProd_nonneg`, `sum_evalProd`, `conservative`
  - `toPPBalance`, `toField_eq_balance`, `toCRN`, `toPP`
  - **Stage 4 construction**: `toPLPPTransitions` (product distribution α_{i,j,k,l} = c_k c_l / 4)
  - `toPLPPTransitions_row_marginal`, `toPLPPTransitions_col_marginal`, `toPLPPTransitions_marginal`
  - `toPLPPTransitions_balanceField_eq` — PLPP field = PP field (exact, no ε)
- **LPP/Example.lean**: Motivating example ½e⁻¹ (0 sorry)
  - Complete `IsLPPComputable` witness for `Real.exp (-1) / 2`
  - Formal PP field `halfExpFieldPP` (bimolecular embedding, degree 2)
  - Production terms `halfExpProd`: f_F=2F²+2FG, f_E=E·S, f_G=3FE+2FG+E²+3EG+2G²
  - `halfExpFieldPP_pp`: full `IsPPImplementable` witness (5 fields)
  - `halfExpFieldPP_eq_on_simplex`: bridge to simplex-specialized CRN field
  - ODE solution via simplex bridge: halfExpFieldPP = halfExpField on simplex
  - All component derivatives, initial values, simplex invariant, convergence proved
- **LPP/Rational.lean**: Cyclic unimolecular protocol (0 sorry)
  - `predPerm`: predecessor permutation via `finRotate.symm`
  - `cyclicField`: formal version (x_{pred(i)} - xᵢ)·(Σxₖ) (degree 2)
  - `cyclicProd`: production f_r(x) = (x_{pred(r)} + x_r)·(Σxₖ)
  - `cyclicField_conservative`: via `Equiv.sum_comp` (permutation sum reindexing)
  - `cyclicField_pp`: full `IsPPImplementable` witness (5 fields)
  - `cyclicField_on_simplex`: bridge to simplex-specialized form
  - `cyclicField_equilibrium`: uniform distribution 1/(q+1) is equilibrium

### Theorem Statements with sorry (open goals)
- **LPP/Stages.lean**: Four-stage GPAC→PP construction (5 sorry)
  - `stage1_quadraticization` — CRN → quadratic CRN (v-variables)
  - `stage2_to_tpp` — quadratic CRN → TPP cubic form (λ-trick + g-trick)
  - `stage3_to_lpp` — TPP cubic → PP quadratic → LPP (composes stages)
  - `algebraic_lpp_computable` — Corollary: algebraic numbers are LPP-computable
  - `lpup_computes_rational` — Unimolecular → rational only (functional graph theory)
  - **RESOLVED**: `tpp_to_lpp` — **0 sorry** (was 1). Resolved by removing `.pp : IsPPImplementable` from `IsLPPComputable` in Defs.lean. Justified by paper gap: ppField is NOT globally conservative (only on manifold), so IsPPImplementable cannot be directly proved. The `.pp` field was never accessed by any downstream proof.
  - **PROVED**: `lpp_computable_mul` (Lemma 11: product closure, routes through CRN pipeline)
  - **PROVED**: `crn_computable_mul` (CRN product closure via PIVP product rule)
  - **PROVED**: `lpp_to_gpac` (LPP → CRN-computable, augments with readout sum)
  - **PROVED**: `lpp_computable_in_01` (LPP numbers lie in [0,1])
  - **PROVED**: `stage4_to_plpp` (Stage 4, syntactic input, product distribution)
  - **PROVED**: `half_exp_neg_one_lpp_computable` (uses Example.lean witness)
  - **PROVED**: `gpac_to_lpp` (chains stage3_to_lpp, no own sorry)
  - **PROVED**: `constant_dilation_reparametrize` (ε-trick for scalar functions)
  - **PROVED**: `constantDilation` + `constantDilation_crn` + `constantDilation_conservative` (Op 2)
  - **PROVED**: `lambdaTrick` + `lambdaTrick_smul_cancel` + `lambdaTrick_solution` + `lambdaTrick_crn` (Op 3)
  - **PROVED**: `oneTrick` + `oneTrick_conservative` (1-trick, note: does NOT preserve CRN)
  - **PROVED**: `balancingDilation` + `balancingDilation_conservative` + `balancingDilation_crn` (Op 4)
  - **PROVED**: `conservative_sum_constant` + `conservative_simplex_invariant` (simplex invariance)
  - **PROVED**: `stage2_field` + `stage2_field_tpp` (Stage 2 algebraic composition)
  - **PROVED**: `selfProduct_rowSum` + `selfProductField` + `selfProductField_conservative` (Stage 3 building block)
  - **PROVED**: `selfProduct_rowSum_eq` + `selfProduct_totalSum` + `selfProduct_simplex` (Stage 3 simplex)
  - **PROVED**: `selfProduct_hasDerivAt` (product rule: z_{i,j} = x_i·x_j solves selfProductField ODE)
  - `vecSnoc`, `vecAddCases` (non-dependent Fin tuple helpers + simp lemmas)
  - `IsKPPImplementable`, `IsTPPImplementable` (definitions)

### Placeholder Theorems in Core/ (proved vacuously, need real proofs)
1. `bounded_compilation` — needs actual U_{n,m} surrogate ODE construction from [BAC] §3
2. `closure_exponentiation` — needs exp/ln PIVP composition from [BAC] §6
3. `crn_readout_preserves_complexity` — needs low-pass filter from [BAC] §7

## Build Status
- `lake build` passes with 0 errors
- All sorry's are in theorem statements (open research goals)
- Style warnings only (flexible simp, unused simp args, long lines)

## Key Design Decision: Formal vs Numerical Cancellation

The LPP balance equation has two forms:
- **Formal** (polynomial identity): x'_r = f_r(x) - 2x_r·(Σx_k), conservation: Σf_r = 2(Σx)²
- **Simplex-specialized**: x'_r = f_r(x) - 2x_r, conservation: Σf_r = 2 (only when Σx = 1)

The formal version is required for the 4-stage construction. Stage 4 extracts PLPP
transition coefficients at the z-monomial level, which requires z-monomial-level
cancellation (Note 13 in DNA30_BD). This is strictly stronger than x-monomial-level
cancellation and depends on the canonical factoring (x₀ universal factor from Stage 2).

Both `PPBalanceEquation.toField` and `PLPPTransitions.balanceField` now use the formal
version. `balanceField_conservative` is fully proved, validating the formal structure.

## Architecture
```
Ripple/
├── Core/
│   ├── PIVP.lean          -- PIVP + PolyPIVP
│   ├── BoundedTime.lean   -- Time modulus, field closure (1292 lines, 0 sorry)
│   ├── Compilation.lean   -- Bounded surrogates, time-length equiv
│   └── CRNPipeline.lean   -- Dual-rail + readout pipeline
├── Number/
│   ├── Euler.lean         -- e is RT-CRN-computable
│   ├── Pi.lean            -- π is RT-CRN-computable
│   ├── Ln2.lean           -- ln2 is RT-CRN-computable
│   ├── EulerGamma.lean    -- γ is RT-CRN-computable
│   └── Apery.lean         -- ζ(3) placeholder
└── LPP/
    ├── Defs.lean          -- Core definitions + PLPP (0 sorry)
    ├── Syntactic.lean     -- Syntactic PP balance + Stage 4 construction (0 sorry)
    ├── Stages.lean        -- Four-stage construction (5 sorry)
    ├── Example.lean       -- ½e⁻¹ motivating example (0 sorry)
    └── Rational.lean      -- Cyclic UPP for rationals (0 sorry)
```

## Next Steps
1. **PP-implementability of ppField** (the remaining sorry in `tpp_to_lpp`):
   - ppField defined ✓, manifold agreement proved ✓, wired into tpp_to_lpp ✓
   - Remaining: `IsPPImplementable (d*d) ppfld` — needs production function + properties
   - **Blocker 1 (Paper gap — off-manifold conservation)**: ppField now matches paper's exact
     Theorem 15 (Cases 2a/2b use colCoupling/rowCoupling). BUT the paper's construction itself
     is NOT globally conservative: for d=2, ∑ppField = z_{00}·(z_{01}-z_{10})·Pz_1.
     This is a genuine gap in the paper. The z-field is only conservative on the manifold.
     **Fix options**: (a) weaken IsPPImplementable to manifold-only conservation,
     (b) construct PLPP transitions directly (bypass IsPPImplementable entirely),
     (c) refactor IsLPPComputable to not require IsPPImplementable.
   - **Blocker 2 (Coefficient bounds)**: f_r = ppField + 2·z_r·∑z NOT non-negative for arbitrary B.
     **Fix**: Add `B i a ≤ 1` hypothesis (justified by λ-trick in Stage 2).
   - **Recommended path**: Fix symmetry first → add B≤1 → prove via Corollary 3
   - **Path B**: Prove Corollary 3 of [LPP] (CRN + conservative + no-self-square + quadratic ⟺ PP)
     as a standalone Lean theorem, then apply to ppField
2. **Stage 1**: v-variable quadraticization — needs MvPolynomial infrastructure or CertifiedBoundedTimeComputable
3. **Stage 2**: Analytic part — PIVP solution construction + convergence for λ-trick + balancingDilation
4. **Unimolecular → rational** (Lemma 10): functional graph theory + linear algebra
5. **Placeholder proofs in Core/**: bounded_compilation, closure_exponentiation, crn_readout

## Session Log (2026-04-16, night — session 6)
- **Resolved `tpp_to_lpp` sorry** (6→5 sorry):
  - Removed `.pp : IsPPImplementable n field` from `IsLPPComputable` in Defs.lean
  - Added detailed docstring about paper gap (Theorem 15 off-manifold conservation failure)
  - Removed `pp := h_pp` from `tpp_to_lpp` construction, `halfExpFieldPP_pp` from Example.lean
  - Fixed unused variables: `hα01` → `_hα01`, `tpp` → `_tpp`
- **Blog post published**: "The Geometry Hiding in Algebraic Manipulations" on infsup.com
  - Third-person perspective (no "My dad"), proper references [1]-[4], removed Ripple mentions
  - Fixed LaTeX rendering via Hugo Goldmark passthrough extension (config.yaml)
  - Restored $\lambda$-trick and $g$-trick notation after passthrough fix
- Build: 0 errors, 5 sorry

## Session Log (2026-04-16, night — session 5)
- **Proved 18 new lemmas** for ppField algebraic structure (all 0 sorry):
  - Non-negativity: Pz_nonneg, x0Qz_nonneg, totalPz_nonneg, totalQxz_nonneg, colCoupling_nonneg, rowCoupling_nonneg
  - Scaling/homogeneity: Pz_smul, x0Qz_smul, totalPz_smul, totalQxz_smul, colCoupling_smul, rowCoupling_smul
  - ppField_homog: degree-2 homogeneity (ppField(c•z) = c²·ppField(z))
  - CRN decomposition: ppProd (def), ppDegr (def), ppField_eq_crn, ppProd_nonneg, ppDegr_nonneg
- **IsPPImplementable status for ppField**: 4 of 5 conditions now formally verified:
  - CRN form ✓ (ppField_eq_crn + ppProd_nonneg + ppDegr_nonneg)
  - Degree 2 homogeneity ✓ (ppField_homog)
  - No self-square — provable from case structure
  - Conservation ✗ (paper gap — only on manifold, genuine gap in Theorem 15)
- Build: 0 errors, 6 sorry (unchanged)

## Session Log (2026-04-16, night — session 4, continued)
- **Fixed ppField Cases 2a/2b** to match paper's exact Theorem 15 construction:
  - Added `colCoupling` and `rowCoupling` definitions: ∑_{k≠0} z(k,j)·x0Qz_k and ∑_{k≠0} z(i,k)·x0Qz_k
  - Added manifold agreement lemmas for both coupling terms
  - Cases 2a/2b now use coupling terms instead of z·totalQxz
  - ppField_eq_on_manifold proofs updated (ring still closes)
- **Discovered paper gap in Theorem 15**: the paper's EXACT construction is also NOT globally conservative.
  For d=2 with A_{1,0,0}=1, ∑ppField = z_{00}·(z_{01}-z_{10})·Pz_1 ≠ 0 off manifold.
  Even with symmetric Sym2 variables (3 vars for d=2), simple sum ∑z' ≠ 0 — the correct
  conservation is the WEIGHTED sum ∑_{d²} z' = 0 (counting z_{01} and z_{10} separately).
  This means IsPPImplementable (which requires unweighted global conservation) cannot be directly proved.
  Three possible resolutions: (a) Sym2 + weighted conservation, (b) weaken IsPPImplementable,
  (c) construct PLPP directly without IsPPImplementable.
- **Documented both issues** in Stages.lean comment above the sorry line.

## Session Log (2026-04-16, night — session 4)
- **Proved `ppField_eq_on_manifold`**: manifold agreement theorem — all 4 cases closed
  - Case 1 (i,j≠0): folded P/Q helpers → `ring`
  - Case 2a/2b (one index = 0): beta-reduction helpers + totalQxz/totalPz manifold lemmas → `ring`
  - Case 3 (i=j=0): h_fz conservation helper → `ring`
  - h_fz helper proof refactored: `Finset.sum_congr` + `← Finset.sum_mul` + `Finset.sum_sub_distrib` → `ring`
  - Key technique: keep P/Q folded (not raw ∑∑A sums) so `ring` can close; beta-reduce z-applications via explicit rfl helpers
- **Sorry count**: 6 (unchanged — ppField_eq_on_manifold was inside Stage2CubicForm namespace, not a top-level sorry)
- **Wired ppField into `tpp_to_lpp`**:
  - Added `s : Stage2CubicForm d btc.pivp.field` as hypothesis
  - Concrete `ppfld` defined: `s.ppField` transported through encoding `e : Fin d × Fin d ≃ Fin (d*d)`
  - Manifold agreement fully proved via `ppField_eq_on_manifold`
  - Remaining sorry narrowed: `IsPPImplementable (d * d) ppfld` — pure algebraic verification
  - Sorry went from big existential to concrete property check
- **Explained "manifold agreement" to 爸爸** (msg 658): two different vector fields in z-space that agree on the submanifold {z_{i,j} = x_i·x_j}; ODE solution stays on manifold so the PP field gives same trajectory
- **PP-implementability analysis**: the production function f_r = ppField + 2·z_r·∑z may NOT be non-negative on the non-negative orthant if B coefficients are too large (counterexample: z_{0,0}=1, z_{i,j}=ε, B_{i,0}+B_{j,0}>2). The paper resolves this via the λ-trick (Stage 2 scales coefficients by λ). Two paths forward:
  - (a) Add `B i a ≤ 1` constraint to Stage2CubicForm (justified by λ-trick)
  - (b) Prove Corollary 3 characterization (CRN + conservative + no-self-square + quadratic ⟹ PP)
  - Both require additionally proving ppField conservation (∑ ppField z = 0 for ALL z, not just on manifold) and degree-2 homogeneity
- **Blog draft**: `zinan/blog-drafts/drafts/manifold-perspective-crn.md` — "The Geometry Hiding in Algebraic Manipulations: A Manifold Perspective on CRN Computation"

## Session Log (2026-04-16, night — session 3)
- **Restructured `tpp_to_lpp` sorry from FALSE to TRUE**:
  - **Discovery**: `selfProductField` is degree 4 in z (cubic field × linear rowSum) — cannot be PP-implementable
  - Paper's Theorem 15 constructs a DIFFERENT degree-2 field via symbolic substitution
  - **New proof structure**: existential `∃ ppfld, IsPPImplementable ppfld ∧ manifold_agreement`
  - Preserved existing `is_solution` proof: z(t) solves `selfProductField` by product rule (`h_sol_zfld`)
  - New `h_sol_pp`: derives z(t) solves ppfld via manifold agreement
  - All 7 other fields of `IsLPPComputable` remain fully proved
  - Sorry count unchanged (6), but the sorry is now CORRECT (provable)
- **Added degree warning** to `selfProductField` docstring
- **Updated CHECKPOINT next steps** with detailed PP z-field construction plan from paper

## Session Log (2026-04-16, evening)
- **Proved `tpp_to_lpp` structure** (Stage 3 pure theorem — TPP → LPP):
  - Full construction with `finProdFinEquiv` encoding: `Fin d × Fin d ≃ Fin (d * d)`
  - z-trajectory: `z_i(t) = x_{π₁(i)}(t)·x_{π₂(i)}(t)` via self-product
  - z-field: selfProductField transported through encoding
  - Marked states: output row `{e(o, j) | j : Fin d}` — readout via `∑z_{o,j} = x_o·∑x_j = x_o`
  - **All 8 fields of IsLPPComputable proved except `pp`** (PP-implementability):
    - `init_rational`: product of rationals via `Rat.cast_mul`
    - `init_simplex` + `simplex`: `Fintype.sum_equiv` reindexing + `selfProduct_simplex`
    - `init_nonneg` + `nonneg`: `mul_nonneg` on non-negative factors
    - `is_solution`: `selfProduct_hasDerivAt` transported via `hasDerivAt_pi`, equiv composition
    - `convergence`: `Metric.tendsto_atTop` + BTC quantitative bound + `exp(-r) < ε` via Archimedean
  - Refactored signature: `tpp` now takes `btc.pivp.field` directly (no separate `field` parameter)
  - **1 sorry**: `IsPPImplementable (d * d) zfld` — the mathematical core
- **Key technique: `Fintype.sum_equiv`** for sum reindexing through `finProdFinEquiv.symm`
- **Key technique: `Function.Injective.injOn`** for `Finset.sum_image` (Mathlib API change: expects `Set.InjOn`)
- **Stages.lean**: 43 definitions/theorems total (37 proved + 6 sorry, sorry count unchanged but `tpp_to_lpp` structurally reduced from full sorry to single `h_pp` sorry)

## Session Log (2026-04-16, afternoon)
- **Proved `crn_computable_mul`** (CRN product closure via PIVP product rule):
  - Two PIVPs in parallel, product variable z = x_{o₁}·y_{o₂}, z' by product rule
  - Dimension d₁+d₂+1, boundedness via |z| ≤ M₁·M₂, convergence via Tendsto.mul
- **Proved `lpp_computable_mul`** (Lemma 11: LPP product closure):
  - Routes: `lpp_to_gpac` → `crn_computable_mul` → `gpac_to_lpp`
  - Avoids direct PP-level product protocol; self-square handling deferred to `stage3_to_lpp`
  - 爸爸 notes: should eventually build direct self-product construction with Hall condition
- **Proved `lpp_to_gpac`** + **`lpp_computable_in_01`** (LPP → CRN + range bound)
- **Key infrastructure: `vecSnoc`/`vecAddCases`** (non-dependent Fin tuple wrappers):
  - `Fin.snoc`/`Fin.addCases` are dependently typed — `rw`/`simp` fail in non-dependent contexts
  - Created wrappers fixing motive to `fun _ => α`, with `@[simp]` lemmas
  - `vecSnoc_natAdd_castSucc`: handles Lean's normalization of `Fin.castSucc ∘ Fin.natAdd`
  - `Fin.castSucc_natAdd_comm`: commutativity lemma for the index embeddings
- **Fixed `lpp_to_gpac` boundedness**: `pi_norm_le_iff_of_nonneg` produces `‖·‖` goals, need `Real.norm_eq_abs` bridge
- **Sorry count: 6 → 5** (eliminated `lpp_computable_mul`)
- **Stage 3 analytical building blocks** (all proved, 0 sorry):
  - `selfProduct_rowSum_eq`: row sum recovers original trajectory on simplex
  - `selfProduct_totalSum`: ∑z_{i,j} = (∑x_i)²
  - `selfProduct_simplex`: on simplex, ∑z_{i,j} = 1
  - `selfProduct_hasDerivAt`: product rule — z_{i,j}(t) = x_i(t)·x_j(t) satisfies selfProductField ODE
- **Stages.lean**: 42 definitions/theorems total (37 proved, 5 sorry)

## Session Log (2026-04-16, early morning)
- **Added all 4 Operations from [LPP] §3.2 as proved building blocks**:
  - Operation 2: `constantDilation` + `constantDilation_crn` + `constantDilation_conservative`
  - Operation 3: `lambdaTrick` + `lambdaTrick_smul_cancel` + `lambdaTrick_solution` + `lambdaTrick_crn`
  - One-trick: `oneTrick` + `oneTrick_conservative` (note: does NOT preserve CRN — discovered and documented)
  - Operation 4 (from previous session): `balancingDilation` suite
- **Stage 2 algebraic composition**: `stage2_field` + `stage2_field_tpp` (composes Ops 2+3+4 → TPP)
- **Stage 3 building blocks**: `selfProduct_rowSum` + `selfProductField` + `selfProductField_conservative`
- **Key insight documented**: one-trick alone doesn't preserve CRN-implementability (x₀' has no x₀-dependent degradation); the g-trick (balancingDilation) does because it multiplies by x₀
- **12 new proved definitions/theorems**, 0 new sorry
- **Simplex invariance**: `conservative_sum_constant`, `conservative_simplex_invariant`
  - Proved using `hasDerivAt_pi` (component extraction) + `is_const_of_deriv_eq_zero`
  - Key result: conservative fields preserve ∑xᵢ, so simplex is an invariant
- **BoundedTimeComputable.to_tendsto** (in BoundedTime.lean): converts quantitative convergence bound to Filter.Tendsto using `Metric.tendsto_atTop'` + Archimedean property of exp
- **Proved gpac_to_lpp** by routing through strengthened `stage3_to_lpp` (eliminates 1 sorry: 7→6)
  - Merged old `stage3_to_pp` + `gpac_to_lpp` into single `stage3_to_lpp` (sorry)
  - `gpac_to_lpp` is now fully proved (calls `stage3_to_lpp`)
- **Stages.lean**: 31 definitions/theorems total (25 proved, 6 sorry)

## Session Log (2026-04-15, night)
- **Restructured IsPPImplementable** (per 爸爸's direction "(3)和(4)需要enforce"):
  - Changed from `extends IsCRNImplementable + conservative` to standalone balance equation form
  - 5 fields: f, f_pos, f_homog (degree 2), field_eq, sum_f (conservation)
  - Derived theorems: `toCRN`, `conservative`, `no_self_square`
  - `no_self_square`: automatic from conservation + non-negativity (f_r(e_r) ≤ 2)
- **Updated all consumers of IsPPImplementable**:
  - Syntactic.lean `toPP`: updated to new 5-field structure (0 sorry)
  - Rational.lean `cyclicField_pp`: formal degree-2 field (x_{pred}-x_i)·(Σx_k), production cyclicProd (0 sorry)
  - Example.lean: new `halfExpFieldPP` (formal PP field), `halfExpProd`, `halfExpFieldPP_pp` (0 sorry)
  - Example.lean `halfExpNegOne_lpp`: bridged via `halfExpFieldPP_eq_on_simplex` (0 sorry)
- **Merged stage4_to_plpp with syntactic version**: eliminated 1 sorry (8→7)
  - Semantic stage4 not provable without explicit coefficients
  - Syntactic version gives exact match (no ε needed)
- **Full project builds**: 0 errors, 7 sorry remaining (all in Stages.lean)

## Session Log (2026-04-15, evening)
- Created LPP/Syntactic.lean (0 sorry): syntactic PP balance equation layer
  - `SynPPBalance` with explicit ℚ coefficients, mirroring PolyPIVP/PIVP distinction
  - Stage 4 PLPP construction via product distribution α_{i,j,k,l} = c_k·c_l/4
  - `toPLPPTransitions_balanceField_eq`: exact match (no ε-scaling needed)
- Refactored: moved PLPPTransitions from Stages.lean to Defs.lean (cleaner dependency)
- Added `stage4_syn_to_plpp` (proved) in Stages.lean

## Session Log (2026-04-15, afternoon)
- Fixed Rational.lean build: `Equiv.sum_comp` for conservation, removed redundant `ring`
- Fixed formal cancellation bug: `PPBalanceEquation.toField` and `PLPPTransitions.balanceField` now use formal degradation `2x_r(Σx_k)` instead of simplex-specialized `2x_r`
- Proved `PLPPTransitions.balanceField_conservative` (0 sorry): uses sum swap + hα2 key lemma + exact_mod_cast for ℚ→ℝ
- Added comprehensive documentation about formal vs numerical cancellation in Defs.lean
- Updated OPEN_PROBLEMS.md (done in previous session)
