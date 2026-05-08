# Handoff: aperyF5B sequence-level bound (codex resume @ 22:09)

_Updated 2026-04-29 21:25 CDT, after B8 (Opus closed summable+continuity)._

## Context

After B8 (commit 7fd4a026), F5Bridge.lean has exactly 1 sorry left:
`aperyF5B_abs_le_aperyF5A` (line 520). Everything else in the F5 split
chain is closed.

The full continuity + summability machinery for B''(z) is in place; it
only needs the bound discharged.

## What to prove

```lean
lemma aperyF5B_abs_le_aperyF5A (n : ℕ) :
    |((aperyF5B n : ℚ) : ℝ)| ≤ ((n : ℝ) + 1) * (aperyF5A n : ℝ)
```

**IMPORTANT (Opus 21:26 finding):** the natural triangle-inequality bound
gives `|b_n| ≤ 2n · a_n` (n ≥ 0) or `≤ (2n+1) · a_n` if you want a single
clean constant covering n=0. The current statement asks for `(n+1)·a_n`,
which is **strictly tighter** than what the triangle-inequality argument
produces (for n ≥ 1, `2n+1 > n+1`).

You have two clean options:

**Option A (recommended):** *Relax the statement* to `≤ (2*n + 1) · a_n` and
propagate the constant through:

- In `aperyF5GFBSecondReal_summable` (current line ~530), replace
  `((n : ℝ) + 3)` with `((2*n + 5 : ℕ) : ℝ)` (= 2(n+2)+1 after the +2 shift).
  The poly×geometric majorant is still summable (degree-1 × geometric).
- In `aperyF5GFBSecondReal_continuousOn` (current line ~600), update the
  same factor in the M-test bound.

**Option B:** keep the (n+1) statement, but tighten the aperyF5C bound to
something like `|aperyF5C(n,k)| ≤ ζ(3) + 1 ≤ 3` (constant!) by:
- bounding `∑_{j=1}^n 1/j^3 ≤ ζ(3) < 2` via tsum
- bounding the alternating sum's absolute value by Leibniz: ≤ |first term|
  ≤ 1/2 (since first nonzero term is `1/(2 · 1 · 1 · 1) = 1/2`)

Option B yields `|b_n| ≤ 3 · a_n` (no n factor), which would let you keep
`(n+1)` since `3 ≤ n+1` for `n ≥ 2` (and base cases n=0, 1 explicit). But
proving `∑ 1/j^3 < 2` in Lean takes effort (needs Mathlib summability
manipulations).

Recommended: Option A.

## Proof plan

### Step 1: bound on aperyF5C(n, k)

Definition (line 49-55):

```lean
noncomputable def aperyF5C (n k : ℕ) : ℚ :=
  (∑ j ∈ range n, (1 : ℚ) / ((j + 1 : ℚ) ^ 3)) +
    ∑ j ∈ range k,
      ((-1 : ℚ) ^ j) /
        (2 * ((j + 1 : ℚ) ^ 3) *
          (Nat.choose n (j + 1) : ℚ) *
          (Nat.choose (n + j + 1) (j + 1) : ℚ))
```

Show: `|aperyF5C n k| ≤ (n : ℚ) + (k : ℚ)`.

Triangle inequality on the two sums. Each summand of the first sum has
absolute value `1/(j+1)^3 ≤ 1` (since j+1 ≥ 1, so (j+1)^3 ≥ 1). Each
summand of the second sum has absolute value bounded by
`1/(2 · 1 · C(n,j+1) · C(n+j+1,j+1))`; if `j+1 ≤ n` both binomials are ≥ 1
so the bound is `≤ 1/2 ≤ 1`; if `j+1 > n` then `C(n,j+1) = 0` and Lean's
division gives `1/0 = 0 ≤ 1`. So each absolute term ≤ 1. Total absolute
value ≤ count of terms = `n + k`.

```lean
private lemma aperyF5C_abs_le (n k : ℕ) :
    |aperyF5C n k| ≤ (n : ℚ) + (k : ℚ) := by
  unfold aperyF5C
  refine (abs_add _ _).trans ?_
  -- Bound each sum's absolute value by count
  ...
```

### Step 2: aperyF5B_abs_le_aperyF5A from Step 1

```lean
lemma aperyF5B_abs_le_aperyF5A (n : ℕ) :
    |((aperyF5B n : ℚ) : ℝ)| ≤ ((n : ℝ) + 1) * (aperyF5A n : ℝ) := by
  unfold aperyF5B
  -- |∑ k C²·C²·aperyF5C(n,k)| ≤ ∑ k C²·C²·|aperyF5C(n,k)|
  --                          ≤ ∑ k C²·C²·(n + k)
  --                          ≤ (2n) · ∑ k C²·C² = (2n) · aperyF5A n
  -- Then bound (2n) by (n+1) · 2 ≤ ... actually (2n + 1) ≤ 2(n+1) for n ≥ 0
  -- For looser bound (n+1)·a_n we need some adjustment, OR change the
  -- statement to ≤ (2n + 1) · aperyF5A n which is honest.
  ...
```

**Note**: The (n+1) bound may be too tight; if so, change the statement to
`≤ (2*n + 1) · aperyF5A n` and propagate. The summable lemma uses
`(n + 3)` which equals `((n+2) + 1)`; if we change to `2*(n+2) + 1 = 2n+5`,
the poly×geometric stays summable (still poly degree-3 × geometric). Adjust
`aperyF5GFBSecondReal_summable` and `_continuousOn` accordingly.

### Estimated lines

50-100 lines. Mostly Finset.abs_sum_le_sum_abs + per-term bounds + sum-of-1
counting. Use `@[push_cast]` lemmas for ℕ → ℚ → ℝ chain.

## Constraints

- Only edit `Frobenius/F5Bridge.lean`
- No new sorry (close the named one)
- `lake build` clean
- Don't commit; I review and commit

## Why this matters

After this, F5 split chain is **fully sorry-free at the Lean level**.

Repo total sorry drops to 2 (Chudnovsky + Ramanujan, both deep ζ-π
identities, unrelated to Apéry).

The two hypothesis-pushed Props (`AperyFrobeniusRatioBound...` and
`AperyPIVPRatioTracking`) remain but are *honest* mathematical hypotheses
about the analytic + ODE-tracking content, not infrastructure gaps.
