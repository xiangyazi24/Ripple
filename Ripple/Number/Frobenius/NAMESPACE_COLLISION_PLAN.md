# Namespace Collision Plan: `Ripple.Number.aperyQ`

_Created 2026-04-29.  Scope: analysis only; no Lean code changed._

## Problem

`F5Bridge.lean` imports `Ripple.Number.ApreyBounded`, while the C-tier
Frobenius ratio-bound lemmas live behind
`Ripple.Number.Frobenius.AperyGeneratingFunction`, which imports
`Ripple.Number.AperySequences`.

Trying to import `AperyGeneratingFunction` into `F5Bridge` fails because both
sides export a declaration named `Ripple.Number.aperyQ`:

```text
import Ripple.Number.AperySequences failed, environment already contains
'Ripple.Number.aperyQ' from Ripple.Number.ApreyBounded
```

The two declarations are mathematically related but live in different Lean
types:

| File | Line | Declaration | Type |
|------|------|-------------|------|
| `Ripple/Number/ApreyBounded.lean` | 119 | `aperyQ` | `MvPolynomial (Fin 8) Q` |
| `Ripple/Number/AperySequences.lean` | 2841 | `aperyQ` | `Polynomial Q` |

There is also a sibling collision:

| File | Line | Declaration | Type |
|------|------|-------------|------|
| `Ripple/Number/ApreyBounded.lean` | 114 | `aperyP` | `MvPolynomial (Fin 8) Q` |
| `Ripple/Number/AperySequences.lean` | 2838 | `aperyP` | `Polynomial Q` |

So fixing only `aperyQ` is probably not enough; `aperyP` should be handled in
the same pass.

## Grep Counts

Commands run from `/Users/huangx/.openclaw/workspace/projects/Ripple`:

```bash
rg -n "\baperyQ\b" Ripple/Number/ApreyBounded.lean \
  Ripple/Number/Frobenius/F5Bridge.lean \
  Ripple/Number/ApreyScalarZ.lean \
  Ripple/Number/AperyCertificate.lean

rg -n "\baperyQ\b" Ripple/Number/AperySequences.lean \
  Ripple/Number/Frobenius \
  Ripple/Number/AperyConifoldIndicial.lean

rg -n "\baperyQ\b" Ripple
```

Raw grep counts:

| Version | Files | Raw hits | Notes |
|---------|-------|----------|-------|
| `MvPolynomial (Fin 8) Q` | `ApreyBounded.lean` | 4 | definition, `aperyBigQ`, `#check`, vector field |
| `Polynomial Q` | `AperySequences.lean` | 12 | definition, coefficient lemma/doc, ODE power-series terms |
| textual docs mentioning collision | `F5Bridge.lean`, `F5_DESIGN.md` | 3 | comments/docs only |
| repo total raw hits | `Ripple/**` | 19 | 4 + 12 + 3 |

Detailed `ApreyBounded.lean` hits:

```text
119 noncomputable def aperyQ : MvPolynomial (Fin 8) Q
136 aperyQ + aperyR * X iA + aperyS * X iSA
145 #check (aperyQ : MvPolynomial (Fin 8) Q)
166 | <1, _> => aperyP + aperyQ * alpha + ...
```

Detailed `AperySequences.lean` hits:

```text
2841 noncomputable def aperyQ : Polynomial Q
2888 docstring for explicit coefficient
2890 aperyQ.coeff n = ...
2894 unfold aperyQ
2964, 3009, 3053, 3074 A-series ODE uses
3132, 3177, 3217, 3244 B-series ODE uses
```

Sibling-name raw counts inside `Ripple/Number`:

| Name | Raw hits | Comment |
|------|----------|---------|
| `aperyP` | 24 | collides across the same two files |
| `aperyQ` | 19 | primary observed import failure |
| `aperyR` | 69 | no one-variable collision because sequence side uses `aperyRcoef` |
| `aperyS` | 5 | no one-variable collision because sequence side uses `aperyScoef` |
| `aperyBigQ` | 6 | only PIVP side |
| `aperyRcoef` | 13 | only sequence/ODE side |
| `aperyScoef` | 12 | only sequence/ODE side |

## Option 1: Rename A, the PIVP `MvPolynomial` Side

Rename declarations in `ApreyBounded.lean`:

```text
aperyP    -> apery8VarP
aperyQ    -> apery8VarQ
aperyR    -> apery8VarR
aperyS    -> apery8VarS
aperyBigQ -> apery8VarBigQ
```

Strictly, only `aperyP` and `aperyQ` are needed for the import collision, but
renaming the whole 8-var polynomial family gives a cleaner public API.

Estimated work:

- Small mechanical rename in `ApreyBounded.lean`.
- Update local references in the vector field and proofs.
- Update any downstream explicit references. Current grep suggests these
  names are not used outside `ApreyBounded.lean` except comments/docs.
- Build targets: at least `Ripple.Number.ApreyBounded`,
  `Ripple.Number.Frobenius.F5Bridge`, and `Ripple.Number.Frobenius`.

Risk:

- Low to medium.
- `ApreyBounded.lean` is PIVP-facing and already has `iZ/iR` private names;
  prefixing the polynomial field helpers is semantically natural.
- Biggest risk is proof breakage in the existing `apery_z_component...` proof
  where `aperyP` is unfolded, but this is a direct rename.

Pros:

- Smallest reference surface: `aperyQ` has 4 raw hits on this side.
- Clears the import path for `AperyGeneratingFunction` without touching the
  large sequence/Frobenius files.
- Better naming: the 8-variable polynomial field should not occupy generic
  names like `aperyP` and `aperyQ`.

Cons:

- Changes public names in `ApreyBounded.lean`, though they appear to be helper
  objects rather than stable API.

## Option 2: Rename B, the `Polynomial Q` ODE Side

Rename declarations in `AperySequences.lean`:

```text
aperyP -> aperyOdeP
aperyQ -> aperyOdeQ
```

Possibly also normalize the already distinct names:

```text
aperyRcoef -> aperyOdeR
aperyScoef -> aperyOdeS
```

Estimated work:

- Medium mechanical rename in `AperySequences.lean`.
- Potential follow-on edits in `AperyGeneratingFunction.lean`,
  `AperyInstance.lean`, and any file using the ODE coefficient names through
  imports.
- More expensive builds because this side is connected to the large
  Frobenius stack.

Risk:

- Medium.
- `AperySequences.lean` and `AperyGeneratingFunction.lean` are large and
  proof-heavy.  Even a rename can trigger brittle unfold/simp references.
- The one-variable ODE coefficient names are older and closer to the
  Frobenius infrastructure.

Pros:

- Makes the ODE-coefficient role explicit.
- If done as a family rename (`aperyOdeP/Q/R/S`), the naming becomes more
  uniform than the current `aperyP`, `aperyQ`, `aperyRcoef`, `aperyScoef`.

Cons:

- Larger blast radius than Option 1.
- Touches the more delicate side of the codebase.

## Option 3: Move One Family Into a Sub-Namespace

Move either family into a dedicated namespace without preserving top-level
aliases:

```lean
namespace AperyPIVP
  noncomputable def P : MvPolynomial (Fin 8) Q := ...
  noncomputable def Q : MvPolynomial (Fin 8) Q := ...
end AperyPIVP
```

or:

```lean
namespace AperyODE
  noncomputable def P : Polynomial Q := ...
  noncomputable def Q : Polynomial Q := ...
end AperyODE
```

Estimated work:

- Medium.
- Requires changing all unqualified uses to qualified names or opening the
  namespace locally.
- Must not keep top-level aliases named `aperyP` / `aperyQ`, because those
  aliases would recreate the same collision.

Risk:

- Medium.
- Namespace moves can be clean, but they interact with theorem names,
  generated fully-qualified names, and any downstream code that expects the
  old constants.
- If only one side is moved, choose the PIVP side for the same reason as
  Option 1: smaller surface.

Pros:

- Best long-term organization if more Apéry subsystems are expected.
- Avoids long prefixed names at every use site if local namespaces are opened.

Cons:

- More structural churn than a direct rename.
- More room for accidental API movement.

## Recommendation

Use **Option 1: rename the PIVP `MvPolynomial` side**.

Recommended concrete names:

```text
aperyP    -> apery8VarP
aperyQ    -> apery8VarQ
aperyR    -> apery8VarR
aperyS    -> apery8VarS
aperyBigQ -> apery8VarBigQ
```

Rationale:

1. The PIVP side has the smaller surface area: `aperyQ` has 4 raw hits in
   `ApreyBounded.lean`, versus 12 on the sequence/ODE side.
2. The one-variable ODE side is upstream of the heavy Frobenius files; avoid
   touching it unless necessary.
3. The PIVP names are currently too generic.  `apery8VarQ` says exactly what
   the object is and prevents future confusion with the ODE coefficient `Q`.
4. The fix should also rename `aperyP`, because it is the same kind of
   collision and will likely surface after `aperyQ` is fixed.

After the rename, retry adding:

```lean
import Ripple.Number.Frobenius.AperyGeneratingFunction
```

to `F5Bridge.lean`, then replace the current tiny
`AperyFrobeniusRatioFamilyCoefficientControl` placeholder with a concrete
payload using the closed ratio-bound family.

## Suggested Verification Sequence

1. Rename only the PIVP polynomial family in `ApreyBounded.lean`.
2. Build:

```bash
lake build Ripple.Number.ApreyBounded
```

3. Add the `AperyGeneratingFunction` import to `F5Bridge.lean`.
4. Build:

```bash
lake build Ripple.Number.Frobenius.F5Bridge
```

5. If the import succeeds, make step-a concrete by packaging:

```text
aperyFrobenius_{zero,half,one}_ratio_bound
aperyFrobenius_{zero,half,one}_coeff_growth_bound
aperyFrobenius_{zero,half,one}_tendsto_at_zero
```

6. Build:

```bash
lake build Ripple.Number.Frobenius
```
