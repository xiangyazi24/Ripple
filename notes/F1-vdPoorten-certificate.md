# F1 (aperyA_recurrence) — proof plan from van der Poorten 1979

## Source

Alfred van der Poorten, *A Proof that Euler Missed... Apéry's Proof of the Irrationality of ζ(3)*, Math. Intelligencer 1 (1979), pp. 195–203. Archived at `projects/Bounded/ref/vdPoorten-Apery-1979.pdf`.

The explicit Zeilberger / creative-telescoping certificate is stated on **page 201**, Section 8 ("Some Rather Complicated but Ingenious Explanations").

## The certificate

Define
- `P(n,k) := C(n,k)² · C(n+k,k)²`  (same as our `b_{n,k}` in vdPo's notation; our `aperyA n = Σ_{k=0..n} P(n,k)`).
- `B(n,k) := 4·(2n+1)·( k·(2k+1) − (2n+1)² ) · P(n,k)`.

## Telescoping identity (the "miracle")

For all n ≥ 1, k ≥ 1 (with suitable boundary conventions):

```
B(n,k) − B(n,k−1)
  = (n+1)³ · P(n+1,k) − (34n³ + 51n² + 27n + 5) · P(n,k) + n³ · P(n−1,k)
```

This is a **pure polynomial identity** in (n,k) after clearing the factorials in the binomials. vdPo writes "by virtue of the method of creative telescoping" — it is verifiable by hand (tedious) or automated by `ring` in Lean.

## How F1 follows

Sum both sides over k from 0 to n+1 (say):

- **LHS telescopes:** `Σ_{k=0..n+1} (B(n,k) − B(n,k−1)) = B(n,n+1) − B(n,−1)`.
- **Both boundary terms vanish:**
  - `B(n,−1)` uses `C(n,−1) = 0` (convention: vdPo explicitly says "B_{nk} = 0 for k < 0 or k > n"). In Lean with `ℕ` we express this as the k=0 term handled separately.
  - `B(n,n+1)` uses `C(n, n+1) = 0`.
- **RHS equals** `(n+1)³ · aperyA(n+1) − (34n³+51n²+27n+5) · aperyA(n) + n³ · aperyA(n−1)`.

Hence `(n+1)³ · a_{n+1} = (34n³+51n²+27n+5) · a_n − n³ · a_{n-1}`, which matches our F1 statement (note `(2n+1)(17n²+17n+5) = 34n³+51n²+27n+5`).

## Lean implementation plan

### Stage A — the certificate as integer identity

```lean
def apery_P (n k : ℕ) : ℤ :=
  (Nat.choose n k : ℤ) ^ 2 * (Nat.choose (n + k) k : ℤ) ^ 2

def apery_B (n k : ℕ) : ℤ :=
  4 * (2 * n + 1) * (k * (2 * k + 1) - (2 * n + 1) ^ 2) * apery_P n k
```

**Core identity:**
```lean
lemma apery_telescoping (n k : ℕ) (hk : 1 ≤ k) (hkn : k ≤ n) :
    apery_B n k - apery_B n (k - 1)
    = (n + 1 : ℤ) ^ 3 * apery_P (n + 1) k
      - (34 * n ^ 3 + 51 * n ^ 2 + 27 * n + 5) * apery_P n k
      + (n : ℤ) ^ 3 * apery_P (n - 1) k
```

Proof strategy: express `Nat.choose (n+1) k` in terms of `Nat.choose n k` via `(n+1)/(n+1-k)` (valid for k ≤ n), similarly for `Nat.choose (n+k+1) k` etc. Then multiply both sides by a common denominator (power of `(n+1-k)(n+k)(n-k+1)` etc.) and close by `ring`.

Key ratios (for `0 ≤ k ≤ n`):
- `C(n+1, k)² · C(n+1+k, k)² = C(n,k)² · C(n+k,k)² · (n+k+1)² / (n+1-k)²`
- `C(n-1, k)² · C(n-1+k, k)² = C(n,k)² · C(n+k,k)² · (n-k)² / (n+k)²`
- `C(n, k-1)² · C(n+k-1, k-1)² = C(n,k)² · C(n+k,k)² · k⁴ / ((n-k+1)²(n+k)²)`

### Stage B — boundary cases

For `k = 0`: use `B(n, 0) = 4·(2n+1)·(0 − (2n+1)²)·P(n,0) = −4·(2n+1)³`. And we need `B(n, -1) = 0` — in ℕ interpretation, `apery_B n (0 - 1) = apery_B n 0` (ℕ subtraction clipped), so the "telescoping at k=0" becomes trivial (LHS = 0). Need to split summation to start at k=1.

For `k = n+1`: `C(n, n+1) = 0` so `apery_P n (n+1) = 0`, hence `apery_B n (n+1) = 0`. Similarly `apery_P (n-1) (n+1) = 0`.

Edge case: `apery_P (n+1) (n+1) = C(n+1, n+1)² · C(2n+2, n+1)²` which is NONZERO. So at k = n+1, the telescoping identity still has a nontrivial `(n+1)³ · P(n+1, n+1)` on the RHS. We need to sum over k from 0 to **n+1** (not just n) so this term is captured.

### Stage C — summation

```lean
lemma aperyA_recurrence (n : ℕ) (hn : 1 ≤ n) :
    ((n + 1 : ℤ) ^ 3) * (aperyA (n + 1) : ℤ)
      = (34 * n ^ 3 + 51 * n ^ 2 + 27 * n + 5) * (aperyA n : ℤ)
          - (n : ℤ) ^ 3 * (aperyA (n - 1) : ℤ) := by
  -- 1. Rewrite RHS of F1 as Σ_{k=0..n+1} [(n+1)³ P(n+1,k) − ... + n³ P(n-1,k)]
  --    using aperyA definition (with boundary terms zero where applicable).
  -- 2. Apply apery_telescoping (for k ≥ 1) to rewrite each summand as B_diff.
  -- 3. Use Finset.sum_Ico_sub_bottom or manually telescope.
  -- 4. Both boundary terms zero → result is 0.
  sorry
```

### Challenge

The main technical pain is **Stage A** — the polynomial identity after clearing denominators. This will be a polynomial in (n, k) of total degree ~20. Lean's `ring` should close it if the expression is cast correctly to ℤ.

Before doing Stage A by brute `ring`, it may be cleaner to:
1. Factor `P(n+1,k) = [(n+1+k)/(n+1-k)]² · P(n,k)` etc. over ℚ.
2. Set `r := (n+1-k)² · (n+k)² · (n-k+1)²` (common denominator).
3. Prove `r · (B(n,k) - B(n,k-1)) = r · RHS` as ℤ polynomial identity → `ring`.
4. Cancel `r` (nonzero for 1 ≤ k ≤ n).

## Timeline estimate

- Stage A (pure polynomial identity via factorial expansion + ring): **1-2 days** of Lean work.
- Stage B (boundary handling): **half day**.
- Stage C (summation telescoping): **half day**.

Total: **~3 days** to close F1 properly. F1' (aperyB_recurrence) should follow with an extended certificate (vdPo gives it for b_n as well, with an inhomogeneous correction `6/n³`).
