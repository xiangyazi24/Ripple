# Open Problems in CRN Computable Numbers
## Formalized using the Ripple Framework

### Status Legend
- **PROVED**: Fully verified in Lean (0 sorry, clean axiom trace)
- **STATED**: Statement formalized, proof placeholder / vacuous
- **PARTIAL**: Some components proved
- **OPEN**: Not yet formalized

*Global state (2026-04-19, post-Phase D):* 0 real sorries across the
codebase. One residual axiom `polyCRN_exists_neg_shift` (scoped to
`AddRationalNeg.lean`, eliminated from the top-level axiom trace of
`algebraic_is_certified_crn` and `bounded_crn_is_lpp_computable_unconditional`).

---

## 1. Structural Results

### 1.1 LPPs ⊇ bounded CRNs on [0,1] (DNA28 Theorem 8, ← direction)
**Status: PROVED** (`bounded_crn_is_lpp_computable_unconditional` in
`Ripple/LPP/BoundedLPP.lean`)

Axiom trace: `[propext, Classical.choice, Quot.sound]`. All four DNA28
stages land:
- Stage 1 (v-variable quadraticization): `stage1_vvariable`
- Stage 2 (CRN → TPP cubic + balancing dilation): `stage2_to_lpp_from_room`
- Stage 3 (TPP → PP quadratic self-product): `stage3_to_lpp_crn`
- Stage 4 (PP → PLPP): `stage4_to_plpp`

The Stage 2 slack (DNA28 Remark 14 requires `x_out < 1`) is closed
unconditionally via the saturating-surrogate construction in
`Ripple/LPP/SaturatingSurrogate.lean` (Phase D, commit `0598a7c`).

### 1.2 Product Protocol Closure (DNA28 Lemma 11)
**Status: PROVED** (`lpp_computable_mul` in `Ripple/LPP/Stages.lean` via
`lpp_product` in `Ripple/LPP/Product.lean`)

`z_{i,j} = x_i · y_j` construction over the Cartesian product PIVP.

### 1.3 Unimolecular Protocols Compute Only Rationals (DNA28 Lemma 10)
**Status: PROVED** (`lpup_computes_rational` in `Ripple/LPP/Stages.lean`)

Linear ODE + Cayley-Hamilton + factoring out `x^k` + integration.
Avoids eigenvalue decomposition.

### 1.4 LPP → CRN (easy direction of DNA28 Theorem 8)
**Status: PROVED** (`lpp_to_gpac` in `Ripple/LPP/Stages.lean`)

Augment LPP with readout-sum variable.

---

## 2. Bounded Analog Complexity ([BAC])

### 2.1 Bounded Surrogate Compilation
**Status: STATED** (`bounded_compilation` in `Ripple/Core/Compilation.lean`
uses a placeholder `realtime_const` proof)

Phase D provided the real construction (`saturating_surrogate_cbtc`) that
DNA28 Remark 14 requires. Rewiring `bounded_compilation` to consume a CBTC
(rather than the looser `PIVP.Solution` hypothesis) and emit the saturating
surrogate is the next step.

### 2.2 Exponentiation Closure (BAC Thm 6.1)
**Status: STATED** (`closure_exponentiation` in `Ripple/Core/CRNPipeline.lean`
uses placeholder proof)

Needs: exp/ln are CRN-computable (inherit from `e` via `Euler.lean`) +
PIVP composition preserving bounded-time complexity + identity
`α^β = exp(β·ln α)`.

### 2.3 CRN Readout Complexity Preservation
**Status: STATED** (`crn_readout_preserves_complexity` in
`Ripple/Core/CRNPipeline.lean` returns `C = 0` via `btc' = btc`)

Needs the actual low-pass filter analysis: `δ̇ + α·δ = α·ε(t)` with
two-regime bound on the convolution.

---

## 3. Specific Numbers

### 3.1 ½e⁻¹ is LPP-Computable
**Status: PROVED** (`halfExpNegOne_lpp` in `Ripple/LPP/Example.lean`,
re-exported as `half_exp_neg_one_lpp_computable` in `Stages.lean`)

First transcendental number proved LPP-computable in this framework.

### 3.2 Famous Constants are RT-CRN-Computable
**Status: PROVED** (all 0 sorry, clean axiom trace)
- `e` (`Ripple/Number/Euler.lean`)
- `π` (`Ripple/Number/Pi.lean`)
- `ln 2` (`Ripple/Number/Ln2.lean`)
- `γ` Euler-Mascheroni (`Ripple/Number/EulerGamma.lean`, most complex)

### 3.3 ζ(3) is CRN-Computable
**Status: OPEN** (`Ripple/Number/Apery.lean` placeholder commented out)

The Apéry constant. Research directions from `experiments/FINDINGS.md`:
- ODE: `x²(4+x)F''' + x(10+3x)F'' + (2+x)F' = 1`
- Generates ζ(3) via Apéry's generating function
- Obstacle: singular point at `x = 0` needs regularization for PIVP form
- Deeper obstacle (2026-04 finding): MUM singularity is a *universal*
  structural barrier for the Apéry-style generating function, not Apéry-specific
- Open: first-floor (real-time) vs second-floor characterization

### 3.4 Catalan's Constant is CRN-Computable
**Status: OPEN**

DNA28 Corollary 19: `G = ½∫₀^∞ t/cosh(t) dt` via PIVP
`G' = R(1-V), R' = E-R, E' = -E, V' = (1-V)²·(-2E²)`
with `G(0)=0, R(0)=0, E(0)=1, V(0)=½`. Concrete PIVP awaiting formalization.

---

## 4. Research Questions

### 4.1 Can LPP-computable numbers use a single output variable?
Currently requires marking a *set* of states. Is there a single-output
characterization? (DNA28 §4 open question)

### 4.2 Complexity hierarchy for LPP computation
The GPAC→LPP translation introduces at most linear slowdown (from the
balancing dilation). Is this tight? Can we define LPP-analogues of the
bounded complexity floors?

### 4.3 Scarce-variable population protocols
Protocols with some variables at `O(1)` population (not tending to ∞)
escape Kurtz's theorem. What can they compute? (DNA28 §4)

### 4.4 Black-and-white k-PPs
Two-state k-PPs with restricted products can compute some algebraic
numbers (e.g., `(3-√5)/2`) but not all rationals (e.g., not `1/5`).
Exact characterization is open.

### 4.5 PP → NAP construction: is it general?
**Status: OPEN — dad flagged 2026-04-19, revisit now that Phase D is closed**

`Ripple/LPP/NAP.lean` (703 lines) formalizes the monomial-level
splitting-feasibility combinatorics:
- `nap_splitting_feasibility` — general split criterion (pipeline-bound
  + foreign-pair)
- `pp_to_nap_split` — strict no-self-production case
- `cubed_pp_nap` — protocol-level for cubed PP monomials under strict
  no-self-prod
- `nap_split_comprehensive` — combines (A) strict no-self-prod + (B)
  pipeline-bound + foreign-pair

Informal analysis at the end of `NAP.lean` argues the Stage 3 self-product
PP is covered by `nap_split_comprehensive` case-by-case, but this is a
*comment*, not a formal theorem.

**Open sub-goals**:
- Formalize an `IsNAP` protocol-level predicate
- Theorem: "for any 4-PP π satisfying [strict no-self-prod OR pipeline+foreign],
  cubing(π) is a NAP"
- Theorem (stronger): "for any PP π, cubing(r²-trick(π)) is a NAP" — or
  identify the PP class for which this holds

Dad's 2026-04-19 note: "我们有例子能成功转成, 但是我不确定这是不是一个
general 的办法."

---

## 5. Infrastructure Priorities

1. **Polynomial degree tracking** — Stages 1-3 of the LPP construction
   reason about polynomial degree and homogeneity informally. A syntactic
   layer for degree-bounded polynomials would make a few ad-hoc arguments
   systematic.

2. **Simplex invariance** — Many LPP proofs need the fact that the
   probability simplex `{x ≥ 0, Σx_i = 1}` is invariant under conservative
   systems. Currently re-derived per callsite.

3. **`polyCRN_exists_neg_shift` discharge** — the single remaining live
   axiom (`Ripple/LPP/AddRationalNeg.lean`). Scoped: given CBTC+PCD for β
   and `q < 0` with `β + q ≥ 0`, produce CBTC+PCD for `β + q`. Three
   candidate constructions (dual-rail reduction, second-order annihilation,
   quadratic forcing) each have their own obstacles; none is in Lean yet.

---

*Ripple framework, last audited 2026-04-19 (post-Phase D).*
*Papers: [RTCRN1] Nat.Comput.2018, [RTCRN2] DNA25, [LPP] DNA28, [BAC] DNA32.*
