# Ripple — Lean 4 Framework for CRN Computable Numbers

## What This Is

Ripple formalizes the theory of Chemical Reaction Network (CRN) computable numbers in Lean 4, building on four papers by Xiang Huang et al.:

1. **[RTCRN1]** Real-time computability of real numbers by CRNs (Nat. Comput. 2018)
2. **[RTCRN2]** Real-time equivalence of CRNs and analog computers (DNA 25, 2019)
3. **[LPP]** Computing real numbers with large-population protocols (DNA 28, 2022)
4. **[BAC]** Bounded Analog Complexity (DNA 32, 2026)

PDFs of these papers are in `../Bounded/ref/`:
- `RTCRN2-Huang-Klinge-Lathrop.pdf` — [RTCRN2]
- `Huang-Huls.pdf` — [LPP]
- `../Bounded/main.pdf` — [BAC]

## Architecture

```
Ripple/
├── Core/
│   ├── PIVP.lean          -- Polynomial Initial Value Problems (GPAC model)
│   ├── BoundedTime.lean   -- Time modulus, complexity hierarchy
│   ├── Compilation.lean   -- Bounded surrogate compilation
│   └── CRNPipeline.lean   -- Dual-rail + readout, complexity preservation
├── Number/
│   └── Apery.lean         -- ζ(3): first target number
└── Tactic/                -- (future) automation for constructing proofs
```

## The Vision

**Frontend:** An LLM agent takes a target number and searches for integral representations.
**Middle:** Lean 4 formal proof infrastructure — encode integrals as ODEs, verify boundedness, prove convergence rate.
**Backend:** (future) ODE simulator to validate constructions numerically.

## Current Goal

Prove Apéry's constant ζ(3) is CRN-computable in the **first floor** of the bounded complexity hierarchy (real-time, μ(r) = Θ(r)). The existing manual proof is second-floor.

## Build

```bash
export PATH="$HOME/.elan/bin:$PATH"
cd projects/Ripple
lake build
```

## Conventions

- All proofs follow the Mathlib style guide
- `sorry` marks genuine open goals; `axiom` marks theorems stated but proof deferred
- Use Mathlib's ODE and analysis libraries wherever possible
