# Ripple — Strategic Direction

_Last updated 2026-04-21. Authoritative: this supersedes any conflicting guidance in `CODEX_BRIEF.md`, `OPEN_PROBLEMS.md`, or `CHECKPOINT.md`. When in doubt, follow this document._

## Decision (2026-04-21, Xiang)

**The Frobenius / regular-singular local theory is the long-term strategic pillar of Ripple.** All future Ripple work on periods, special constants, and holonomic-series-defined numbers is expected either to use this framework or to contribute to building it.

This decision is permanent until Xiang explicitly overrides it. Do not re-litigate route choice for any specific period number without referring back to this document.

## Immediate state (2026-04-21)

### ζ(3) is formalized as CRN-computable — canonical route: Fermi-Dirac

The canonical Lean witness for "ζ(3) is CRN-computable" is **`Ripple/Number/AperyFermi.lean`**. Five-variable first-floor PIVP encoding the identity

$$\frac{2}{3}\int_0^\infty \frac{x^2}{1+e^x}\,dx = \zeta(3).$$

Status: end-to-end closed, 0 sorry, 0 axiom. All five main theorems (`fermiTrajectory_is_solution`, `fermiTrajectory_bounded`, `fermi_integral_eq_zeta3`, `apery_fermi_is_crn_computable`, `fermi_realtime_modulus`) are fully proved.

**Any downstream Ripple claim that ζ(3) is CRN-computable should cite the Fermi-Dirac theorems, not the Apéry series route.**

### Apéry series route is secondary and *partially open* — waiting on Frobenius framework

`Ripple/Number/ApreyBounded.lean` + `Ripple/Number/AperyConifoldIndicial.lean` encode the 8-variable PIVP modelling Apéry's generating-function proof. Current state:

- F1 (Apéry recurrence), F2 (generating-function ODE): closed
- F3 (indicial equation at the conifold): algebraic core closed in `AperyConifoldIndicial.lean`
- F6 (scalar z-component exponential convergence to the conifold): closed in `ApreyScalarZ.lean`
- F4 (Apéry identity β₁/α₁ = ζ(3)) and F5 (3/2-order conifold asymptotic): **not proved**, packaged as the Prop-level hypothesis `AperyConifoldThreeHalvesBound` in the bridge-theorem signature

The bridge theorem `apery_conifold_frobenius_bridge` is therefore *conditional*: it closes the gap from `AperyConifoldThreeHalvesBound + F6` to the final exponential ζ(3)-convergence. The hypothesis itself has no proof witness in the repository.

**This is not a sorry — the repository compiles clean. But the analytic content of Apéry's theorem is not formalized; it is pushed to the theorem caller.** Do not hide this fact in downstream claims.

## Long-term direction — the Frobenius framework

### Why

Formal local analysis at regular singular points of linear ODEs is the natural language for:

- Periods (ζ-values, multiple zeta values, L-values at integers)
- Special constants defined via holonomic series (Catalan's G with a different encoding, Feigenbaum, Chaitin-Ω-adjacent constructions)
- Any number whose "integral representation" is better expressed through an ODE with regular singular points than through a proper integral

Having this infrastructure in Lean is the prerequisite for scaling Ripple beyond the few numbers where a clever Fermi-Dirac-style integral happens to work.

### What to build (in rough order)

1. **Formal power series substitution into linear ODEs**: given `p(z) y''' + q(z) y'' + r(z) y' + s(z) y = 0` and an ansatz `y(z) = (z₁ - z)^ρ · Σ aₙ (z₁ - z)ⁿ`, define the substitution rigorously and prove the leading-coefficient equation is the indicial polynomial.
2. **Indicial polynomial for regular singular points** (generalizing the concrete `aperyConifoldIndicial`): give a general Lean definition of the indicial polynomial at a regular singular point of an order-k linear ODE.
3. **Frobenius exponent → local solution existence**: for each root of the indicial polynomial (with appropriate integer-gap conditions), prove the corresponding formal series converges in a neighborhood and satisfies the ODE.
4. **Integer-gap / logarithmic cases**: handle the cases where indicial roots differ by an integer and logarithmic terms appear.
5. **Application layer**: F4 (Apéry identity) and F5 (3/2 asymptotic) become clean consequences once (1)–(3) are in place.

Each step is a standalone formalization project. Do not treat this as a single "close the Apéry sorry" task — it is infrastructure.

### How this affects route selection

- **For any new number target**: first ask "does this fit a Fermi-Dirac-style direct integral encoding?" If yes, follow the Fermi pattern (clean, no Frobenius needed). If no (holonomic series / periods / L-values), the work necessarily contributes to the Frobenius framework.
- **Do not build one-off local-analysis hacks**: if you need regular-singular behavior for one number, factor it through the generalized framework being built above. One-off proofs tied to specific ODEs accumulate technical debt.
- **Apéry series route stays open-but-paused**: returning to prove F4 and F5 properly is a milestone of the Frobenius framework, not an independent goal. Close it when the framework reaches step (5).

## Working rules

1. Hypothesis-pushing (turning an unproved analytical fact into an explicit `Prop` argument of a theorem, as codex did with `AperyConifoldThreeHalvesBound`) is allowed *for structural reasons* — it preserves `lake build` cleanliness without hiding the gap. But it must be flagged prominently in any public-facing statement about what Ripple proves.
2. When in doubt between "add an `axiom`" and "push to hypothesis", prefer the hypothesis form — it is strictly more honest about who is responsible for supplying the fact.
3. When Xiang says "just prove X", clarify whether X is the Lean target or the mathematical target. They can diverge when analytical content is hypothesis-pushed.
4. Numerical experiments (in `experiments/`) should back any hypothesis-pushed Prop: if we claim `|ρ − ζ(3)| = O(|z₁ − z|^{3/2})` in a signature, there must be a numerical script confirming the rate. Otherwise the hypothesis is unconstrained.

## Pointers

- Canonical ζ(3) route: `Ripple/Number/AperyFermi.lean`
- Series route (conditional): `Ripple/Number/ApreyBounded.lean`, `Ripple/Number/AperyConifoldIndicial.lean`, `Ripple/Number/ApreyScalarZ.lean`
- Numerical Fermi validation: `experiments/apery_fermi_5var.py`
- Numerical series validation: *not yet written — see `experiments/apery_8var_pivp.py` as the next deliverable*

---

_Revisions require Xiang's sign-off. Codex / Claude should not unilaterally edit strategic claims in this file; surface proposed changes in conversation first._
