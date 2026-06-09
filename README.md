# Ripple — Lean 4 Framework for CRN Computable Numbers

Ripple formalizes the theory of Chemical Reaction Network (CRN)
computable numbers in Lean 4, building on four papers by Xiang Huang
et al.:

- **[RTCRN1]** Real-time computability of real numbers by CRNs (Nat. Comput. 2018)
- **[RTCRN2]** Real-time equivalence of CRNs and analog computers (DNA 25, 2019)
- **[LPP]** Computing real numbers with large-population protocols (DNA 28, 2022)
- **[BAC]** Bounded analog complexity (DNA 32, 2026)

## Status

**0 sorry / 0 axiom decl** across all six pillars (as of 2026-05-08):

| Pillar | Path | What it covers |
|---|---|---|
| Core | `Ripple/Core/` | PIVP / GPAC, bounded time, compilation, ODE-global, init shifts |
| ODE | `Ripple/ODE/` | Scalar barriers |
| DualRail | `Ripple/DualRail/` | Constant annihilation, BTC reduction, scalar cubic/quintic, exp-majorization, subtraction |
| LPP | `Ripple/LPP/` | Large-population protocols, algebraic construction, CF24 |
| Number | `Ripple/Number/` | Apéry constant, π, ln 2, 1/e, Catalan, Frobenius, AttractorIntegralEquivalence |
| Number/Modular | `Ripple/Number/Modular/` | Modular forms, j-invariant, CM-163, Φ₄₁ Sturm, generic level-1 Sturm |

Headline result: the long-standing
`complex_sturm_bound_valence_formula_phi41Level41Cleared` chain
runs unconditionally, which means the Heegner-class CM evaluation
`j(τ₁₆₃) = -640320³` is fully verified through the Φ₄₁ modular
polynomial.

## Build

```bash
export PATH="$HOME/.elan/bin:$PATH"
cd projects/Ripple
lake build         # 3695 jobs, ~30-45 min from scratch
```

The longest single file is `Ripple/Number/Modular/ModularPolynomialSturmCertificate.lean`,
which evaluates a 3529-coefficient recurrence under `native_decide`
(see *Trust footprint* below).

## Architecture

```
Ripple/
├── Core/              — PIVP (GPAC) primitives, time complexity, compilation
├── ODE/               — Lyapunov-style scalar barriers
├── DualRail/          — Dual-rail encoding of polynomial dynamics
├── LPP/               — Large-population protocols (DNA28)
├── Number/            — Specific real numbers (Apéry, π, ...)
│   ├── Frobenius/     — Regular-singular Frobenius theory (long-term pillar)
│   └── Modular/       — Modular forms, Φ₄₁, CM evaluation
└── Tactic/            — (planned) automation for constructing CRN proofs
```

## Trust footprint

Ripple aims to be reproducible from the Lean 4 + Mathlib kernel. There
are no `axiom` declarations. The only trust beyond the Lean kernel is
the `native_decide` tactic, used in finitely many places to discharge
finite-but-large decidable claims that the Lean kernel cannot evaluate
in reasonable time:

| File | Site | What is claimed |
|---|---|---|
| `Number/Modular/ModularPolynomialSturmCertificate.lean` | `phi41Level41RecurrenceCoeffArrayFirstZero_sturmBound` | The first 3529 entries of the level-41 Φ₄₁ cleared q-expansion recurrence array vanish |
| `Number/Modular/ModularPoly41.lean` | `phi41Diag_root` | `evalPhi41Diag(j(τ₁₆₃)) = 0` |
| `Number/Modular/ModularPoly41.lean` | `phi41DiagCofactor_ne_zero` | The cofactor at the root is nonzero |
| `Number/Modular/ModularPoly41.lean` (Forall lemma) | level-41 difference table check | All 83 difference values vanish |

`native_decide` compiles the decision procedure to native code and
trusts that the result matches what the Lean kernel would compute. This
trusts the entire compiler chain (Lean → C → machine code) plus libc /
OS / hardware. It does **not** trust any unverified mathematical
content; it only trusts that the compiled program faithfully represents
the kernel definition of the decidable proposition.

A kernel-only Chinese-Remainder-Theorem (CRT) replacement for the
Φ₄₁ Sturm certificate is documented in
`HANDOFF/crt_route_replace_native_decide.md`. The CRT helpers are
already in place in `ModularPolynomialSturmCertificate.lean`; the
remaining work is generating the per-prime data tables. At the current
Sturm bound (3529), the natural a-priori coefficient bound is ≈10^8590,
requiring ≈468 CRT primes — yielding a Lean source file in the
hundreds of megabytes. A practical kernel-only replacement therefore
requires either (a) a tighter problem-specific coefficient bound, or
(b) a custom reflection evaluator. Both are research-grade engineering
tasks; in the meantime `native_decide` is the practical choice.

## Conventions

- Mathlib style guide.
- `sorry` would mark a genuine open goal — the project has none.
- `axiom` would mark a stated-without-proof theorem — the project has none.
- Use Mathlib's ODE and analysis libraries wherever possible.

## Repository layout

- `Ripple/` — Lean source.
- `scripts/` — Python helpers (Φ₄₁ recurrence checker, CRT certificate generator).
- `experiments/` — research-only Python scripts and findings.
- `HANDOFF/` — task descriptions for asynchronous LLM agent collaboration; `done/` contains completed handoffs.
- `lectures/`, `working_notes/` — research notes (not built).

## Documentation

- `CHECKPOINT.md` — chronological session log of major milestones.
- `WORK_LOG.md` — per-commit one-liners.
- `STRATEGY.md` — long-term direction (Frobenius pillar).
- `DOCTRINE.md` — proof-engineering conventions.
- `OPEN_PROBLEMS.md` — open problems being formalized.
- `RELEASE_NOTES.md` — versioned release summaries.

## References

PDFs of source/reference papers live in `ref/`.  Cite as marked
in-file when adding new theorems whose statement or proof is taken
from a paper.

Catalan-equation / Cassels-descent line (used by `Ripple/LPP/CasselsActualPade.lean` and the planned `CasselsClassical.lean`):

- **[Cassels-1960]** J. W. S. Cassels, *On the equation aˣ−bʸ=1, II*, Proc. Camb. Phil. Soc. **56** (1960), 97–103. File: `ref/Cassels-1960-On-the-equation-ax-by-1-II.pdf`. The original elementary descent: gcd-lemma + binomial-series truncation at `R=[p/q]+1` with explicit integer-clearing `z^{Rq−p}·q^{R+ρ}` (NOT a Padé approximant — this is the architectural correction recorded in `CHECKPOINT.md` cont.18).
- **[Ribenboim-1994]** P. Ribenboim, *Catalan's Conjecture: Are 8 and 9 the Only Consecutive Powers?*, Academic Press, 1994. File: `ref/Ribenboim-Catalans-Conjecture.pdf`. Book-length exposition; Cassels' elementary descent is written out in full with the explicit estimates, and the surrounding Nagell / Selberg / Inkeri / Tijdeman context.

CRN / analog-computation pillar (cited as `[RTCRN1]`, `[RTCRN2]`, `[LPP]`, `[BAC]` at the top of this file).  PDFs for those live in `../Bounded/ref/`.

ζ(3) / Apéry-irrationality pillar (used by `Ripple/Number/`): Apéry 1979, Beukers 1979 / 1987, Nesterenko 1996, van der Poorten 1979, Anderson–Joshi 2024 — files in `ref/`.
