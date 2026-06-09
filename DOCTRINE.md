# DOCTRINE — Eliminate remaining native_decide in Modular

**Goal:** Close the 3 sorry's in SturmCRTBound.lean (Qrow_bound_big, Qrow_bound_pull, phi41_final_coeff_bound) and eliminate the remaining 5 native_decide calls in the Modular directory.

## Current state
- 11/16 native_decide → decide/norm_num (committed, build passes)
- maj_DeltaTight, maj_Qrow proved (committed)
- phi41SparseCoeffL1 filled (committed)
- Codex (uis-ripple-modular) built SturmQrowCertSupport.lean (324 lines) + 144 certificate data files (76MB), pivoting to exact recurrence certificate approach
- Numerical validation: max |Q_j[n]| = 1045 digits (j=42, n=3528), fits in 10^1090

## Avenues (ranked by promise)

### (a) Exact recurrence certificate — Codex is on this, I assist
Monitor and drive the Codex on uis-ripple-modular. It's building exact Q_j coefficient tables + rfl verification via the derivative recurrence. If it completes, this closes Qrow_bound_big and Qrow_bound_pull directly. I sync, review, fix build errors, and dispatch ChatGPT when math questions arise.
- Terminal success: SturmCRTBound.lean builds with 0 sorry
- Terminal failure: rfl proofs too slow for kernel at large indices. At n=3528 each rfl evaluates an O(n)-term sum in the kernel; chunk_size=8 gives 28K ops per rfl, taking 9+ minutes and 8.5GB RAM per file. With 1935 files per prime × 59 primes, total compile time ~years. CONFIRMED INFEASIBLE for n > ~200. Works for small n (n < 42: trivial zeros, 15s). The kernel reduction speed is the absolute bottleneck — native_decide is ~1000× faster.

### (b) Function-table mod-p CRT for remaining 5 native_decide
Rewrite the 5 Array-based cert functions using ℕ → ℤ function tables. Use many small primes (kernel can evaluate mod-p arithmetic on functions). Generate chunked decide proofs.
- Terminal success: all 5 native_decide replaced with decide/rfl
- Terminal failure: kernel still too slow even with function tables and smallest viable chunks

### (c) Inductive recurrence bound proof
Prove |Q_j[n]| ≤ B(n) inductively via the recurrence, using a pre-computed envelope B stored as a function table. Each induction step: triangle inequality + norm_num per chunk.
- Terminal success: Qrow_bound_big/pull proved analytically
- Terminal failure: per-chunk norm_num too heavy for 3529 × 43 entries

### (d) ChatGPT-assisted Hecke/modular bound
Ask ChatGPT to design a Lean-formalizable Hecke-type bound. Weight 504 forms satisfy |a_n| ≤ C·d(n)·n^{251.5}. If C can be bounded explicitly for E4^{3j}·Δ^{42-j}, this closes both bounds analytically.
- Terminal success: clean analytical proof, no certificate data needed
- Terminal failure: Hecke constant C requires eigenform decomposition (too much Lean infra)

## Hard-block conditions (only these stop the run)
- Lean kernel fundamentally cannot verify ANY chunk-based certificate (all chunk sizes tried, all fail)
- Mathematical error discovered in the stated bounds
- Destructive action needed
- All avenues exhausted with documented terminal verdicts
