/-
  Ripple.Number.AperySequences — the combinatorial Apéry sequences
  `aₙ`, `bₙ` that feed the Frobenius roadmap (F1)–(F5) of
  `Ripple.Number.ApreyBounded.apery_conifold_frobenius_witness`.

  ## What's here

  * `aperyA n := Σ_{k ≤ n} C(n,k)² · C(n+k,k)²`           (integer-valued)
  * `aperyB n := Σ_{k ≤ n} C(n,k)² · C(n+k,k)² · c(n,k)`   (rational-valued)
    where `c(n,k)` is Apéry's harmonic-like correction
    `c(n,k) := Σ_{j=1..n} 1/j³ + Σ_{j=1..k} (-1)^(j-1) / (2 j³ C(n,j) C(n+j,j))`.

  ## What's not here (sorry'd — (F1))

  * `aperyA_recurrence : (n+1)³ · aperyA (n+1)
                        = (2n+1)·(17n²+17n+5) · aperyA n
                          − n³ · aperyA (n−1)`  (n ≥ 1)
  * `aperyB_recurrence : same homogeneous three-term recurrence for `bₙ``

  Both recurrences admit Zeilberger / WZ-style creative-telescoping proofs;
  Mathlib does not yet have the Zeilberger algorithm, so the certificate
  would need to be supplied by hand.  We record the statements as named
  sorries so the Frobenius roadmap can thread them as explicit inputs.

  Base-case values `aperyA 0 = 1`, `aperyA 1 = 5` are closed by `decide`.
-/

import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Rat.Defs
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.IntervalCases
import Ripple.Number.AperyCertificate

namespace Ripple
namespace Number

open Finset

/-! ## Sequence `aₙ` -/

/-- The Apéry integer sequence
    `aₙ := Σ_{k = 0}^{n} C(n,k)² · C(n+k,k)²`.

Values: 1, 5, 73, 1445, 33001, 819005, 21460825, ... (OEIS A005259). -/
def aperyA (n : ℕ) : ℕ :=
  ∑ k ∈ range (n + 1), (Nat.choose n k) ^ 2 * (Nat.choose (n + k) k) ^ 2

@[simp]
lemma aperyA_zero : aperyA 0 = 1 := by
  unfold aperyA; decide

@[simp]
lemma aperyA_one : aperyA 1 = 5 := by
  unfold aperyA; decide

lemma aperyA_two : aperyA 2 = 73 := by
  unfold aperyA; decide

lemma aperyA_three : aperyA 3 = 1445 := by
  unfold aperyA; decide

lemma aperyA_four : aperyA 4 = 33001 := by
  unfold aperyA; decide

lemma aperyA_five : aperyA 5 = 819005 := by
  unfold aperyA; decide

/-- `aₙ` is positive for all `n`.  (Immediate from the `k = 0` term
`C(n,0)² · C(n,0)² = 1 > 0`.) -/
lemma aperyA_pos (n : ℕ) : 0 < aperyA n := by
  unfold aperyA
  -- The `k = 0` summand is `1`.
  have h0 : (Nat.choose n 0) ^ 2 * (Nat.choose (n + 0) 0) ^ 2 = 1 := by
    simp
  refine lt_of_lt_of_le (show 0 < 1 from Nat.zero_lt_one) ?_
  calc (1 : ℕ)
      = (Nat.choose n 0) ^ 2 * (Nat.choose (n + 0) 0) ^ 2 := h0.symm
    _ ≤ ∑ k ∈ range (n + 1),
            (Nat.choose n k) ^ 2 * (Nat.choose (n + k) k) ^ 2 := by
        apply Finset.single_le_sum
          (f := fun k => (Nat.choose n k) ^ 2 * (Nat.choose (n + k) k) ^ 2)
          (s := range (n + 1)) (a := 0)
        · intro i _; exact Nat.zero_le _
        · exact Finset.mem_range.mpr (Nat.succ_pos _)

/- **(F1) — Apéry three-term recurrence for `aₙ`.**
    `(n+1)³ aₙ₊₁ = (2n+1)(17n²+17n+5) aₙ − n³ aₙ₋₁`  for `n ≥ 1`.

Proof via van der Poorten's creative-telescoping certificate
`apery_B n k := 4(2n+1)(k(2k+1) − (2n+1)²) · apery_P n k`, established
axiom-freely in `Ripple.Number.AperyCertificate`.  The telescoping
identity
    `B(n,k) − B(n,k−1) = (n+1)³ P(n+1,k) − (34n³+51n²+27n+5) P(n,k)
                         + n³ P(n−1,k)`
holds for `1 ≤ k ≤ n`.  Summing both sides over `k ∈ {0, …, n+1}` and
handling the two endpoints `k = 0` and `k = n+1` manually yields
`F(n) = ∑ T(n,k) = 0`, i.e. F1. -/

/-! ### Summation helpers for F1 — integer sum form of `aperyA` -/

section AperyRecurrenceProof

open Finset

/-- Integer-cast form of `aperyA n` as a sum of `apery_P`. -/
private lemma aperyA_int_eq_sum (n : ℕ) :
    ((aperyA n : ℕ) : ℤ) = ∑ k ∈ range (n + 1), apery_P n k := by
  unfold aperyA apery_P
  push_cast
  rfl

/-- Extend the summation range beyond `n+1`: the extra terms vanish by
`apery_P_k_gt`. -/
private lemma aperyA_int_extended (n m : ℕ) (hm : n ≤ m) :
    ((aperyA n : ℕ) : ℤ) = ∑ k ∈ range (m + 1), apery_P n k := by
  rw [aperyA_int_eq_sum]
  -- range (m+1) = range (n+1) ∪ Ico (n+1) (m+1), and P(n,k) = 0 for k > n.
  have hsplit : range (m + 1) = range (n + 1) ∪ Ico (n + 1) (m + 1) := by
    ext k
    simp only [mem_range, mem_union, mem_Ico]
    omega
  rw [hsplit]
  have hdisj : Disjoint (range (n + 1)) (Ico (n + 1) (m + 1)) := by
    rw [disjoint_left]
    intro k hk hk'
    simp only [mem_range] at hk
    simp only [mem_Ico] at hk'
    omega
  rw [sum_union hdisj]
  have hzero : ∑ k ∈ Ico (n + 1) (m + 1), apery_P n k = 0 := by
    apply sum_eq_zero
    intro k hk
    simp only [mem_Ico] at hk
    exact apery_P_k_gt n k (by omega)
  rw [hzero, add_zero]

/-- `apery_B n 0 = -4(2n+1)³`. -/
private lemma apery_B_n_zero (n : ℕ) : apery_B n 0 = -4 * (2 * (n : ℤ) + 1) ^ 3 := by
  unfold apery_B
  rw [apery_P_n_zero]
  push_cast
  ring

/-- The telescoping summand evaluated at `k = 0`. -/
private lemma T_at_zero (n : ℕ) :
    (n + 1 : ℤ) ^ 3 * apery_P (n + 1) 0
      - (34 * (n : ℤ) ^ 3 + 51 * n ^ 2 + 27 * n + 5) * apery_P n 0
      + (n : ℤ) ^ 3 * apery_P (n - 1) 0
    = apery_B n 0 := by
  rw [apery_P_n_zero, apery_P_n_zero, apery_P_n_zero, apery_B_n_zero]
  ring

/-! ### The key Pascal-ratio identity for `T_at_top`:
`(n+1) · C(2n+2, n+1) = 2(2n+1) · C(2n, n)`. -/

private lemma choose_two_n_succ_identity (n : ℕ) :
    ((n : ℤ) + 1) * (Nat.choose (2 * n + 2) (n + 1) : ℤ)
      = 2 * (2 * (n : ℤ) + 1) * (Nat.choose (2 * n) n : ℤ) := by
  -- Step 1: C(2n+2, n+1) = C(2n+1, n+1) + C(2n+1, n) by Pascal.
  -- Since (n+1) + n = 2n+1, by symmetry C(2n+1, n+1) = C(2n+1, n).
  -- So C(2n+2, n+1) = 2 · C(2n+1, n).
  have hpascal : Nat.choose (2 * n + 2) (n + 1)
      = Nat.choose (2 * n + 1) n + Nat.choose (2 * n + 1) (n + 1) := by
    -- Nat.choose_succ_succ : (n+1).choose (k+1) = n.choose k + n.choose (k+1)
    exact Nat.choose_succ_succ (2 * n + 1) n
  have hsym : Nat.choose (2 * n + 1) (n + 1) = Nat.choose (2 * n + 1) n := by
    have heq : 2 * n + 1 = (n + 1) + n := by ring
    exact Nat.choose_symm_of_eq_add heq
  have hC2 : Nat.choose (2 * n + 2) (n + 1) = 2 * Nat.choose (2 * n + 1) n := by
    rw [hpascal, hsym]; ring
  -- Step 2: (n+1) · C(2n+1, n) = (2n+1) · C(2n, n).
  -- From Nat.choose_mul_succ_eq (2n) n : C(2n, n)·(2n+1) = C(2n+1, n)·(2n+1-n).
  have hms := Nat.choose_mul_succ_eq (2 * n) n
  have hsub : 2 * n + 1 - n = n + 1 := by omega
  rw [hsub] at hms
  -- hms : C(2n, n) * (2n+1) = C(2n+1, n) * (n+1)
  -- Now combine.
  have hZ : ((Nat.choose (2 * n + 2) (n + 1) : ℕ) : ℤ)
      = 2 * ((Nat.choose (2 * n + 1) n : ℕ) : ℤ) := by exact_mod_cast hC2
  have hZ2 : ((Nat.choose (2 * n) n * (2 * n + 1) : ℕ) : ℤ)
      = ((Nat.choose (2 * n + 1) n * (n + 1) : ℕ) : ℤ) := by exact_mod_cast hms
  push_cast at hZ hZ2
  -- Goal: (n+1) · C(2n+2, n+1) = 2(2n+1) · C(2n, n)
  -- Via hZ: (n+1) · C(2n+2, n+1) = (n+1) · 2 · C(2n+1, n) = 2 · (n+1) · C(2n+1, n)
  -- Via hZ2 (flipped): (n+1) · C(2n+1, n) = C(2n, n) · (2n+1)
  -- So (n+1) · C(2n+2, n+1) = 2 · C(2n, n) · (2n+1)
  calc ((n : ℤ) + 1) * (Nat.choose (2 * n + 2) (n + 1) : ℤ)
      = ((n : ℤ) + 1) * (2 * (Nat.choose (2 * n + 1) n : ℤ)) := by rw [hZ]
    _ = 2 * ((Nat.choose (2 * n + 1) n : ℤ) * ((n : ℤ) + 1)) := by ring
    _ = 2 * ((Nat.choose (2 * n) n : ℤ) * (2 * (n : ℤ) + 1)) := by rw [← hZ2]
    _ = 2 * (2 * (n : ℤ) + 1) * (Nat.choose (2 * n) n : ℤ) := by ring

/-- The telescoping summand evaluated at `k = n+1`. -/
private lemma T_at_top (n : ℕ) (hn : 1 ≤ n) :
    (n + 1 : ℤ) ^ 3 * apery_P (n + 1) (n + 1)
      - (34 * (n : ℤ) ^ 3 + 51 * n ^ 2 + 27 * n + 5) * apery_P n (n + 1)
      + (n : ℤ) ^ 3 * apery_P (n - 1) (n + 1)
    = -apery_B n n := by
  -- Middle and third terms vanish.
  have hmid : apery_P n (n + 1) = 0 := apery_P_k_gt n (n + 1) (Nat.lt_succ_self _)
  have hthird : apery_P (n - 1) (n + 1) = 0 := by
    apply apery_P_k_gt
    omega
  rw [hmid, hthird]
  -- Now LHS = (n+1)³ · P(n+1, n+1).
  -- P(n+1, n+1) = C(n+1, n+1)² · C(2n+2, n+1)² = C(2n+2, n+1)²
  have hPtop : apery_P (n + 1) (n + 1)
      = (Nat.choose (2 * n + 2) (n + 1) : ℤ) ^ 2 := by
    unfold apery_P
    rw [Nat.choose_self]
    have : n + 1 + (n + 1) = 2 * n + 2 := by ring
    rw [this]
    push_cast; ring
  -- apery_B n n: plug k = n. Compute -apery_B n n.
  have hPnn : apery_P n n = (Nat.choose (2 * n) n : ℤ) ^ 2 := by
    unfold apery_P
    rw [Nat.choose_self]
    have : n + n = 2 * n := by ring
    rw [this]
    push_cast; ring
  have hBnn : apery_B n n = -4 * ((n : ℤ) + 1) * (2 * n + 1) ^ 2 *
        (Nat.choose (2 * n) n : ℤ) ^ 2 := by
    unfold apery_B
    rw [hPnn]
    push_cast; ring
  rw [hPtop, hBnn]
  -- Goal: (n+1)³ · C(2n+2, n+1)² - 0 + 0 = -(-4(n+1)(2n+1)² · C(2n,n)²)
  -- From choose_two_n_succ_identity: (n+1)·C(2n+2,n+1) = 2(2n+1)·C(2n,n)
  -- Squaring: (n+1)²·C(2n+2,n+1)² = 4(2n+1)²·C(2n,n)²
  -- Multiplying by (n+1) gives (n+1)³·C(2n+2,n+1)² = 4(n+1)(2n+1)²·C(2n,n)² ✓
  have hkey := choose_two_n_succ_identity n
  have hkey_sq : (((n : ℤ) + 1) * (Nat.choose (2 * n + 2) (n + 1) : ℤ)) ^ 2
      = (2 * (2 * (n : ℤ) + 1) * (Nat.choose (2 * n) n : ℤ)) ^ 2 := by
    rw [hkey]
  -- Goal after simplification: (n+1)³ · C(2n+2, n+1)² = 4(n+1)(2n+1)² · C(2n, n)²
  -- hkey_sq: (n+1)² · C(2n+2, n+1)² = 4(2n+1)² · C(2n, n)²
  -- Multiply both sides of hkey_sq by (n+1).
  have hmul : ((n : ℤ) + 1) * (((n : ℤ) + 1) * (Nat.choose (2 * n + 2) (n + 1) : ℤ)) ^ 2
        = ((n : ℤ) + 1) * (2 * (2 * (n : ℤ) + 1) * (Nat.choose (2 * n) n : ℤ)) ^ 2 := by
    rw [hkey_sq]
  -- Unfold powers and get the goal form.
  linear_combination hmul

/-! ### Main assembly -/

end AperyRecurrenceProof

open Finset in
lemma aperyA_recurrence (n : ℕ) (hn : 1 ≤ n) :
    ((n + 1 : ℤ) ^ 3) * (aperyA (n + 1) : ℤ)
      = (2 * n + 1 : ℤ) * (17 * n ^ 2 + 17 * n + 5) * (aperyA n : ℤ)
          - (n : ℤ) ^ 3 * (aperyA (n - 1) : ℤ) := by
  -- Define the "telescoping summand" T and the LHS-minus-RHS quantity F.
  set T : ℕ → ℤ := fun k =>
    (n + 1 : ℤ) ^ 3 * apery_P (n + 1) k
      - (34 * (n : ℤ) ^ 3 + 51 * n ^ 2 + 27 * n + 5) * apery_P n k
      + (n : ℤ) ^ 3 * apery_P (n - 1) k with hT_def
  -- Replace the target coefficient with its expanded form.
  have hcoef : (2 * (n : ℤ) + 1) * (17 * n ^ 2 + 17 * n + 5)
      = 34 * n ^ 3 + 51 * n ^ 2 + 27 * n + 5 := by ring
  -- It suffices to show the F-sum is zero.
  suffices hF :
      ∑ k ∈ range (n + 2), T k = 0 by
    -- Unpack the sum over T into the three component sums.
    have hsum_expand :
        ∑ k ∈ range (n + 2), T k
          = (n + 1 : ℤ) ^ 3 * (∑ k ∈ range (n + 2), apery_P (n + 1) k)
            - (34 * (n : ℤ) ^ 3 + 51 * n ^ 2 + 27 * n + 5)
              * (∑ k ∈ range (n + 2), apery_P n k)
            + (n : ℤ) ^ 3 * (∑ k ∈ range (n + 2), apery_P (n - 1) k) := by
      simp only [hT_def, Finset.sum_add_distrib, Finset.sum_sub_distrib,
                 ← Finset.mul_sum]
    rw [hsum_expand] at hF
    -- Recognize each sum as the integer cast of the corresponding aperyA value.
    rw [← aperyA_int_extended (n + 1) (n + 1) le_rfl,
        ← aperyA_int_extended n (n + 1) (Nat.le_succ _),
        ← aperyA_int_extended (n - 1) (n + 1) (by omega)] at hF
    rw [hcoef]
    linarith
  -- Now prove ∑_{k ∈ range (n+2)} T k = 0.
  -- Split range (n+2) = {0} ∪ Ico 1 (n+1) ∪ {n+1}.
  -- First peel off k = 0 via sum_range_succ'.
  rw [Finset.sum_range_succ']
  -- sum becomes: ∑ k ∈ range (n+1), T (k+1) + T 0
  -- Peel off the top term k = n from range (n+1) via sum_range_succ.
  rw [Finset.sum_range_succ]
  -- Sum becomes: (∑ k ∈ range n, T (k+1)) + T (n+1) + T 0
  -- The middle sum telescopes: T (k+1) = apery_B n (k+1) - apery_B n k.
  have htele : ∀ k ∈ range n, T (k + 1) = apery_B n (k + 1) - apery_B n k := by
    intro k hk
    simp only [mem_range] at hk
    have hk1 : 1 ≤ k + 1 := Nat.succ_le_succ (Nat.zero_le _)
    have hkn : k + 1 ≤ n := hk
    have hAT := apery_telescoping n (k + 1) hk1 hkn
    -- apery_telescoping: B(n, k+1) - B(n, (k+1)-1) = ... T form
    have hsub : (k + 1) - 1 = k := by omega
    rw [hsub] at hAT
    simp only [hT_def]
    linarith
  rw [Finset.sum_congr rfl htele]
  -- Now: ∑ k ∈ range n, (apery_B n (k+1) - apery_B n k) = apery_B n n - apery_B n 0.
  rw [Finset.sum_range_sub (fun k => apery_B n k)]
  -- Goal: (apery_B n n - apery_B n 0) + T (n+1) + T 0 = 0
  -- Substitute T using its definition.
  have hT0 : T 0 = apery_B n 0 := by simp only [hT_def]; exact T_at_zero n
  have hTtop : T (n + 1) = -apery_B n n := by simp only [hT_def]; exact T_at_top n hn
  rw [hT0, hTtop]
  ring

/-- Sanity check of `aperyA_recurrence` at `n = 1`:
    `2³ · a₂ = 3 · 39 · a₁ − 1³ · a₀`, i.e. `8 · 73 = 585 − 1 = 584`. -/
example :
    ((1 + 1 : ℤ) ^ 3) * (aperyA 2 : ℤ)
      = (2 * 1 + 1 : ℤ) * (17 * 1 ^ 2 + 17 * 1 + 5) * (aperyA 1 : ℤ)
          - (1 : ℤ) ^ 3 * (aperyA 0 : ℤ) := by
  simp [aperyA_zero, aperyA_one, aperyA_two]

/-- Sanity check of `aperyA_recurrence` at `n = 2`:
    `3³ · a₃ = 5 · (17·4 + 17·2 + 5) · a₂ − 2³ · a₁`,
    i.e. `27 · 1445 = 5 · 107 · 73 − 8 · 5 = 39055 − 40 = 39015 = 27 · 1445`. -/
example :
    ((2 + 1 : ℤ) ^ 3) * (aperyA 3 : ℤ)
      = (2 * 2 + 1 : ℤ) * (17 * 2 ^ 2 + 17 * 2 + 5) * (aperyA 2 : ℤ)
          - (2 : ℤ) ^ 3 * (aperyA 1 : ℤ) := by
  simp [aperyA_one, aperyA_two, aperyA_three]

/-- Sanity check of `aperyA_recurrence` at `n = 3`:
    `4³ · a₄ = 7 · (17·9 + 17·3 + 5) · a₃ − 3³ · a₂`,
    i.e. `64 · 33001 = 7 · 209 · 1445 − 27 · 73
                     = 2 114 035 − 1 971 = 2 112 064`. -/
example :
    ((3 + 1 : ℤ) ^ 3) * (aperyA 4 : ℤ)
      = (2 * 3 + 1 : ℤ) * (17 * 3 ^ 2 + 17 * 3 + 5) * (aperyA 3 : ℤ)
          - (3 : ℤ) ^ 3 * (aperyA 2 : ℤ) := by
  simp [aperyA_two, aperyA_three, aperyA_four]

/-- Sanity check at `n = 4`: `5³ · a₅ = 9 · (17·16 + 17·4 + 5) · a₄ − 4³ · a₃`,
    i.e. `125 · 819005 = 9 · 345 · 33001 − 64 · 1445
                       = 102 468 105 − 92 480 = 102 375 625 = 125 · 819005`. -/
example :
    ((4 + 1 : ℤ) ^ 3) * (aperyA 5 : ℤ)
      = (2 * 4 + 1 : ℤ) * (17 * 4 ^ 2 + 17 * 4 + 5) * (aperyA 4 : ℤ)
          - (4 : ℤ) ^ 3 * (aperyA 3 : ℤ) := by
  simp [aperyA_three, aperyA_four, aperyA_five]

/-! ## Sequence `bₙ` (rational, inhomogeneous)

    The companion sequence `bₙ` uses the harmonic-like correction
    `c(n,k) := Σ_{j=1..n} 1/j³ + Σ_{j=1..k} (−1)^(j−1)/(2 j³ C(n,j) C(n+j,j))`.

    Apéry showed `bₙ/aₙ → ζ(3)` at exponential rate.  This file only
    *defines* the sequence and records the recurrence it satisfies —
    the ζ(3)-convergence is (F4)–(F5) of the Frobenius roadmap and is
    developed downstream.
-/

/-- Apéry's correction term
    `c(n, k) := Σ_{j=1..n} 1/j³
              + Σ_{j=1..k} (−1)^(j−1) / (2 j³ C(n,j) C(n+j, j))`. -/
noncomputable def aperyC (n k : ℕ) : ℚ :=
  (∑ j ∈ range n, (1 : ℚ) / ((j + 1 : ℚ) ^ 3)) +
    ∑ j ∈ range k,
      ((-1 : ℚ) ^ j) /
        (2 * ((j + 1 : ℚ) ^ 3) *
          (Nat.choose n (j + 1) : ℚ) * (Nat.choose (n + j + 1) (j + 1) : ℚ))

/-- Apéry's rational sequence
    `bₙ := Σ_{k = 0}^{n} C(n,k)² · C(n+k,k)² · c(n, k)`. -/
noncomputable def aperyB (n : ℕ) : ℚ :=
  ∑ k ∈ range (n + 1),
    (Nat.choose n k : ℚ) ^ 2 * (Nat.choose (n + k) k : ℚ) ^ 2 * aperyC n k

@[simp]
lemma aperyB_zero : aperyB 0 = 0 := by
  unfold aperyB aperyC
  simp

/-! ### Decomposition `bₙ = H₃(n) · aₙ + dₙ`

The correction `c(n,k) = H₃(n) + e(n,k)` splits `bₙ` into a harmonic part
and an "error-series" part `dₙ := Σ_k P(n,k) · e(n,k)`.  The harmonic
part satisfies the Apéry recurrence *with inhomogeneity* `aₙ₊₁ − aₙ₋₁`
(from the shifts `H₃(n+1) − H₃(n) = 1/(n+1)³` and `H₃(n) − H₃(n-1) = 1/n³`),
and the miracle of Apéry's proof is that `dₙ` satisfies the *opposite*
inhomogeneity, so `bₙ` satisfies the homogeneous recurrence.
-/

/-- Harmonic-cubic partial sum `H₃(n) = Σ_{j=1..n} 1/j³`. -/
noncomputable def aperyH3 (n : ℕ) : ℚ :=
  ∑ j ∈ range n, (1 : ℚ) / ((j + 1 : ℚ) ^ 3)

/-- The "error" part of `aperyC`:
    `e(n, k) := Σ_{j=1..k} (−1)^(j−1) / (2 j³ C(n,j) C(n+j, j))`. -/
noncomputable def aperyE (n k : ℕ) : ℚ :=
  ∑ j ∈ range k,
    ((-1 : ℚ) ^ j) /
      (2 * ((j + 1 : ℚ) ^ 3) *
        (Nat.choose n (j + 1) : ℚ) * (Nat.choose (n + j + 1) (j + 1) : ℚ))

lemma aperyC_split (n k : ℕ) : aperyC n k = aperyH3 n + aperyE n k := by
  unfold aperyC aperyH3 aperyE
  rfl

/-- Rational sum version of `aperyA n`, over ℚ instead of ℤ. -/
lemma aperyA_rat_eq (n : ℕ) :
    (aperyA n : ℚ) = ∑ k ∈ range (n + 1),
        (Nat.choose n k : ℚ) ^ 2 * (Nat.choose (n + k) k : ℚ) ^ 2 := by
  unfold aperyA
  push_cast
  rfl

/-- The "error sequence"
    `dₙ := Σ_{k = 0}^{n} C(n,k)² · C(n+k,k)² · e(n, k)`. -/
noncomputable def aperyD (n : ℕ) : ℚ :=
  ∑ k ∈ range (n + 1),
    (Nat.choose n k : ℚ) ^ 2 * (Nat.choose (n + k) k : ℚ) ^ 2 * aperyE n k

/-- **Linearity decomposition.** `bₙ = H₃(n) · aₙ + dₙ`. -/
lemma aperyB_eq_decomp (n : ℕ) :
    aperyB n = aperyH3 n * (aperyA n : ℚ) + aperyD n := by
  unfold aperyB aperyD
  simp_rw [aperyC_split, mul_add]
  rw [Finset.sum_add_distrib]
  congr 1
  -- Goal 1: ∑ k, P(n,k) * H₃(n) = H₃(n) * aperyA n
  · rw [← Finset.sum_mul, aperyA_rat_eq, mul_comm]

/-- Harmonic increment: `H₃(n+1) = H₃(n) + 1/(n+1)³`. -/
lemma aperyH3_succ (n : ℕ) :
    aperyH3 (n + 1) = aperyH3 n + 1 / ((n + 1 : ℚ) ^ 3) := by
  unfold aperyH3
  rw [Finset.sum_range_succ]

/-- Harmonic decrement (for `n ≥ 1`): `H₃(n) = H₃(n-1) + 1/n³`. -/
lemma aperyH3_pred (n : ℕ) (hn : 1 ≤ n) :
    aperyH3 n = aperyH3 (n - 1) + 1 / ((n : ℚ) ^ 3) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have : m + 1 - 1 = m := by omega
  rw [this, aperyH3_succ]
  push_cast; ring

/-- **Harmonic-part recurrence.** The "`H₃ · aₙ` piece" of `F_B` equals
    `aₙ₊₁ - aₙ₋₁`, by combining F1 with the harmonic shifts. -/
lemma aperyHA_recurrence (n : ℕ) (hn : 1 ≤ n) :
    ((n + 1 : ℚ) ^ 3) * (aperyH3 (n + 1) * (aperyA (n + 1) : ℚ))
      - (2 * n + 1 : ℚ) * (17 * n ^ 2 + 17 * n + 5)
          * (aperyH3 n * (aperyA n : ℚ))
      + (n : ℚ) ^ 3 * (aperyH3 (n - 1) * (aperyA (n - 1) : ℚ))
    = (aperyA (n + 1) : ℚ) - (aperyA (n - 1) : ℚ) := by
  -- Substitute harmonic shifts.
  have hSucc : aperyH3 (n + 1) = aperyH3 n + 1 / ((n + 1 : ℚ) ^ 3) :=
    aperyH3_succ n
  have hPred : aperyH3 n = aperyH3 (n - 1) + 1 / ((n : ℚ) ^ 3) :=
    aperyH3_pred n hn
  have hPred' : aperyH3 (n - 1) = aperyH3 n - 1 / ((n : ℚ) ^ 3) := by
    rw [hPred]; ring
  rw [hSucc, hPred']
  -- Use F1 over ℚ, derived from `aperyA_recurrence`.
  have hrec := aperyA_recurrence n hn
  have hrecQ :
      ((n : ℚ) + 1) ^ 3 * (aperyA (n + 1) : ℚ)
        = (2 * (n : ℚ) + 1) * (17 * (n : ℚ) ^ 2 + 17 * n + 5) * (aperyA n : ℚ)
            - (n : ℚ) ^ 3 * (aperyA (n - 1) : ℚ) := by
    have := congrArg ((↑·) : ℤ → ℚ) hrec
    push_cast at this
    linarith
  -- Cancel 1/(n+1)³ against (n+1)³ and 1/n³ against n³.
  have hn1 : ((n : ℚ) + 1) ^ 3 ≠ 0 := by positivity
  have hnn : (n : ℚ) ≠ 0 := by
    have : (1 : ℚ) ≤ (n : ℚ) := by exact_mod_cast hn
    linarith
  have hnn3 : (n : ℚ) ^ 3 ≠ 0 := pow_ne_zero 3 hnn
  field_simp
  -- After field_simp, the goal is a polynomial identity modulo hrecQ.
  linear_combination (aperyH3 n) * hrecQ

/-! ### Scaffolding for the F1' / `aperyD_recurrence` proof

We expose some structural lemmas about `aperyE` and `aperyD` that are
axiom-freely provable.  The main recurrence is then stated, with its
mathematically-substantial core left as a `sorry` pending the full
vdPoorten §8 Zeilberger-style telescoping write-out. -/

/-- Recursive unfolding of `aperyE`:
    `e(n, k+1) = e(n, k) + (-1)^k / (2 (k+1)³ · C(n, k+1) · C(n+k+1, k+1))`. -/
lemma aperyE_succ (n k : ℕ) :
    aperyE n (k + 1) = aperyE n k
      + (-1 : ℚ) ^ k / (2 * ((k + 1 : ℚ) ^ 3) *
          (Nat.choose n (k + 1) : ℚ) * (Nat.choose (n + k + 1) (k + 1) : ℚ)) := by
  unfold aperyE
  rw [Finset.sum_range_succ]

/-- `e(n, 0) = 0`. -/
@[simp]
lemma aperyE_zero (n : ℕ) : aperyE n 0 = 0 := by
  unfold aperyE; simp

/-- Closed form for the k-difference of `aperyE`:
    `e(n, k+1) − e(n, k) = (−1)^k / (2(k+1)³ · C(n, k+1) · C(n+k+1, k+1))`.

    Direct corollary of `aperyE_succ`. -/
lemma aperyE_diff_right_closed (n k : ℕ) :
    aperyE n (k + 1) - aperyE n k
      = (-1 : ℚ) ^ k / (2 * ((k + 1 : ℚ) ^ 3)
          * (Nat.choose n (k + 1) : ℚ) * (Nat.choose (n + k + 1) (k + 1) : ℚ)) := by
  rw [aperyE_succ]; ring

/-- **(vdPoorten's closed-form miracle.)** The n-difference of `aperyE` has a
    simple rational closed form. For `1 ≤ n` and `k ≤ n - 1`:

    `aperyE n k - aperyE (n-1) k + 1/n³
      = (-1)^k · (k!)² · (n-k-1)! / (n² · (n+k)!)`

    Proved by induction on `k` using `aperyE_succ` and explicit factorial
    algebra.  Source: vdPoorten 1979 §8, p. 201, column 1 ("After some massive
    reorganization"). -/
lemma aperyE_diff_pred_closed (n k : ℕ) (hn : 1 ≤ n) (hk : k ≤ n - 1) :
    aperyE n k - aperyE (n - 1) k + 1 / ((n : ℚ) ^ 3)
      = (-1 : ℚ) ^ k * (Nat.factorial k : ℚ) ^ 2 * (Nat.factorial (n - k - 1) : ℚ)
          / ((n : ℚ) ^ 2 * (Nat.factorial (n + k) : ℚ)) := by
  -- Basic positivity facts for `n`.
  have hn_pos : 0 < n := hn
  have hnQ_pos : (0 : ℚ) < (n : ℚ) := by exact_mod_cast hn_pos
  have hnQ_ne : (n : ℚ) ≠ 0 := ne_of_gt hnQ_pos
  induction k with
  | zero =>
      -- Base: both E-terms are 0; reduces to 1/n³ = (n-1)! / (n² · n!).
      have hnfac_pos : 0 < Nat.factorial n := Nat.factorial_pos n
      have hnfacQ_ne : (Nat.factorial n : ℚ) ≠ 0 := by
        exact_mod_cast Nat.factorial_pos n |>.ne'
      -- `n! = n · (n-1)!` (as ℕ) since `n ≥ 1`.
      have hfac_unfold : Nat.factorial n = n * Nat.factorial (n - 1) := by
        obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
        simp [Nat.factorial_succ]
      have hfac_unfoldQ : (Nat.factorial n : ℚ)
          = (n : ℚ) * (Nat.factorial (n - 1) : ℚ) := by
        exact_mod_cast hfac_unfold
      simp only [aperyE_zero, sub_self, zero_add, pow_zero, Nat.factorial_zero,
        Nat.cast_one, one_pow, one_mul, Nat.sub_zero, Nat.add_zero]
      -- Goal: 1 / n³ = (n-1)! / (n² · n!)
      rw [hfac_unfoldQ]
      have hfacnm1_ne : (Nat.factorial (n - 1) : ℚ) ≠ 0 := by
        exact_mod_cast (Nat.factorial_pos _).ne'
      field_simp
  | succ k ih =>
      -- Induction step: `k+1 ≤ n-1`, i.e. `k ≤ n - 2`.
      have hk1 : k ≤ n - 1 := by omega
      have ih' := ih hk1
      -- Useful arithmetic: `k + 1 ≤ n - 1`, `k + 2 ≤ n`, etc.
      have hk_plus : k + 1 ≤ n - 1 := hk
      have hk_plus' : k + 2 ≤ n := by omega
      have hk_leq_n : k + 1 ≤ n := by omega
      have hk_succ_leq : k + 1 ≤ n - 1 := hk
      -- Expand (k+1) in aperyE recursively at n and n-1.
      rw [aperyE_succ n k, aperyE_succ (n - 1) k]
      -- Collect the new increments; the algebraic target splits into:
      --   (diff at k increments) - (closed form difference at k+1 vs k).
      -- First move: factor out the IH, reducing to a factorial identity.
      -- Key positivity facts.
      have hk1Q_pos : (0 : ℚ) < ((k : ℚ) + 1) := by positivity
      have hk1Q_ne : ((k : ℚ) + 1) ≠ 0 := ne_of_gt hk1Q_pos
      have hk1Q_pow3_ne : ((k : ℚ) + 1) ^ 3 ≠ 0 := pow_ne_zero _ hk1Q_ne
      -- Choose values are positive for the indices in range.
      have hCn : 0 < Nat.choose n (k + 1) := Nat.choose_pos hk_leq_n
      have hCnQ_ne : (Nat.choose n (k + 1) : ℚ) ≠ 0 := by exact_mod_cast hCn.ne'
      have hCnk : 0 < Nat.choose (n + k + 1) (k + 1) := by
        apply Nat.choose_pos; omega
      have hCnkQ_ne : (Nat.choose (n + k + 1) (k + 1) : ℚ) ≠ 0 := by
        exact_mod_cast hCnk.ne'
      have hn1_pos : 0 < n - 1 := by omega
      have hCnm : 0 < Nat.choose (n - 1) (k + 1) := by
        apply Nat.choose_pos; omega
      have hCnmQ_ne : (Nat.choose (n - 1) (k + 1) : ℚ) ≠ 0 := by
        exact_mod_cast hCnm.ne'
      have hCmk : 0 < Nat.choose (n - 1 + k + 1) (k + 1) := by
        apply Nat.choose_pos; omega
      have hCmkQ_ne : (Nat.choose (n - 1 + k + 1) (k + 1) : ℚ) ≠ 0 := by
        exact_mod_cast hCmk.ne'
      -- Factorial positivity / nonzero.
      have hfac_nk_ne : (Nat.factorial (n + k) : ℚ) ≠ 0 := by
        exact_mod_cast (Nat.factorial_pos _).ne'
      have hfac_nk1_ne : (Nat.factorial (n + k + 1) : ℚ) ≠ 0 := by
        exact_mod_cast (Nat.factorial_pos _).ne'
      have hfac_k_ne : (Nat.factorial k : ℚ) ≠ 0 := by
        exact_mod_cast (Nat.factorial_pos _).ne'
      have hfac_k1_ne : (Nat.factorial (k + 1) : ℚ) ≠ 0 := by
        exact_mod_cast (Nat.factorial_pos _).ne'
      have hfac_nmk1_ne : (Nat.factorial (n - k - 1) : ℚ) ≠ 0 := by
        exact_mod_cast (Nat.factorial_pos _).ne'
      have hfac_nmk2_ne : (Nat.factorial (n - k - 2) : ℚ) ≠ 0 := by
        exact_mod_cast (Nat.factorial_pos _).ne'
      -- Key binomial-to-factorial identities (as ℚ).
      -- (1) C(n, k+1) · (k+1)! · (n-k-1)! = n!
      have hCn_id : (Nat.choose n (k + 1) : ℚ) * (Nat.factorial (k + 1) : ℚ)
                        * (Nat.factorial (n - (k + 1)) : ℚ)
                      = (Nat.factorial n : ℚ) := by
        have := Nat.choose_mul_factorial_mul_factorial hk_leq_n
        exact_mod_cast this
      -- (2) C(n+k+1, k+1) · (k+1)! · (n+k+1 - (k+1))! = (n+k+1)!
      have hCnk_id : (Nat.choose (n + k + 1) (k + 1) : ℚ)
                        * (Nat.factorial (k + 1) : ℚ)
                        * (Nat.factorial ((n + k + 1) - (k + 1)) : ℚ)
                      = (Nat.factorial (n + k + 1) : ℚ) := by
        have h : k + 1 ≤ n + k + 1 := by omega
        have := Nat.choose_mul_factorial_mul_factorial h
        exact_mod_cast this
      -- (3) C(n-1, k+1) · (k+1)! · (n-1-(k+1))! = (n-1)!
      have hCnm_id : (Nat.choose (n - 1) (k + 1) : ℚ)
                        * (Nat.factorial (k + 1) : ℚ)
                        * (Nat.factorial ((n - 1) - (k + 1)) : ℚ)
                      = (Nat.factorial (n - 1) : ℚ) := by
        have h : k + 1 ≤ n - 1 := hk
        have := Nat.choose_mul_factorial_mul_factorial h
        exact_mod_cast this
      -- (4) C(n-1+k+1, k+1) · (k+1)! · (n-1+k+1-(k+1))! = (n-1+k+1)!
      have hCmk_id : (Nat.choose (n - 1 + k + 1) (k + 1) : ℚ)
                        * (Nat.factorial (k + 1) : ℚ)
                        * (Nat.factorial ((n - 1 + k + 1) - (k + 1)) : ℚ)
                      = (Nat.factorial (n - 1 + k + 1) : ℚ) := by
        have h : k + 1 ≤ n - 1 + k + 1 := by omega
        have := Nat.choose_mul_factorial_mul_factorial h
        exact_mod_cast this
      -- Simplify nat subtractions.
      have hsub1 : n - (k + 1) = n - k - 1 := by omega
      have hsub2 : (n + k + 1) - (k + 1) = n := by omega
      have hsub3 : (n - 1) - (k + 1) = n - k - 2 := by omega
      have hsub4 : (n - 1 + k + 1) - (k + 1) = n - 1 := by omega
      have hsub5 : n - 1 + k + 1 = n + k := by omega
      rw [hsub1] at hCn_id
      rw [hsub2] at hCnk_id
      rw [hsub3] at hCnm_id
      rw [hsub4, hsub5] at hCmk_id
      -- Replace `n - 1 + k + 1` everywhere with `n + k` so the binomial matches `(n+k)`.
      have h_nmk : n - 1 + k + 1 = n + k := by omega
      -- For hCmk the argument was already `(n - 1 + k + 1)`; rewrite to `(n + k)`
      -- in both the choose and the factorial.
      rw [h_nmk] at hCmk hCmkQ_ne
      -- Also rewrite the LHS aperyE arguments for consistency: `(n - 1) + k + 1 = n + k`.
      -- In the goal after `aperyE_succ (n-1) k`, we have `Nat.choose ((n-1) + k + 1) (k+1)`;
      -- it should become `Nat.choose (n + k) (k + 1)`.
      -- We do not need to rewrite in the goal; we'll handle with linear_combination below.
      -- Expand `n!` in terms of `(n-1)!` and similar for `(n+k+1)!` vs `(n+k)!`.
      have hfac_n_unfold : (Nat.factorial n : ℚ)
          = (n : ℚ) * (Nat.factorial (n - 1) : ℚ) := by
        obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
        simp [Nat.factorial_succ]
      have hfac_nk1_unfold : (Nat.factorial (n + k + 1) : ℚ)
          = ((n + k + 1 : ℕ) : ℚ) * (Nat.factorial (n + k) : ℚ) := by
        have : Nat.factorial (n + k + 1) = (n + k + 1) * Nat.factorial (n + k) := by
          rw [Nat.factorial_succ]
        exact_mod_cast this
      -- Unfold `(n - k - 1)! = (n - k - 1) · (n - k - 2)!` using `k+1 ≤ n-1`, so `n-k-1 ≥ 1`.
      have hnk1_pos : 1 ≤ n - k - 1 := by omega
      have hfac_nmk1_unfold : (Nat.factorial (n - k - 1) : ℚ)
          = ((n - k - 1 : ℕ) : ℚ) * (Nat.factorial (n - k - 2) : ℚ) := by
        have h : n - k - 1 = (n - k - 2) + 1 := by omega
        rw [h, Nat.factorial_succ]
        push_cast; ring
      -- Key arithmetic: (n - k - 1 : ℕ) cast to ℚ equals (n : ℚ) - k - 1.
      have hnkQ : ((n - k - 1 : ℕ) : ℚ) = (n : ℚ) - (k : ℚ) - 1 := by
        have : (n - k - 1 : ℕ) + (k + 1) = n := by omega
        have h1 := congrArg (fun m : ℕ => (m : ℚ)) this
        push_cast at h1
        linarith
      have hnk1Q : ((n + k + 1 : ℕ) : ℚ) = (n : ℚ) + k + 1 := by push_cast; ring
      -- Now close the proof. Strategy:
      -- After the two `aperyE_succ` rewrites, the LHS of the goal is:
      --   (e(n,k) + Δ_n) - (e(n-1,k) + Δ_{n-1}) + 1/n³
      -- where Δ_n = (-1)^k / (2(k+1)³ · C(n,k+1) · C(n+k+1,k+1))
      --       Δ_{n-1} = (-1)^k / (2(k+1)³ · C(n-1,k+1) · C(n-1+k+1,k+1))
      -- The RHS is the closed form at (k+1).
      -- Using IH, rearrange: LHS = RHS_ih + (Δ_n - Δ_{n-1}), need = RHS_{k+1}.
      -- So need: Δ_n - Δ_{n-1} = RHS_{k+1} - RHS_ih.
      -- We'll reduce everything to the common denominator via linear_combination.
      --
      -- Push `(n-1) + k + 1 = n + k` in the goal.
      have hsum_rewrite : (n - 1) + k + 1 = n + k := by omega
      rw [hsum_rewrite]
      -- Now the goal involves choose arguments:
      --   C(n, k+1), C(n+k+1, k+1), C(n-1, k+1), C(n+k, k+1).
      -- We have identities relating these to factorials.  Clear the denominators
      -- with field_simp then close by linear_combination of the four identities.
      -- First, rewrite factorial on RHS: `(n + (k+1))! = (n+k+1)!`.
      have h_nkk : n + (k + 1) = n + k + 1 := by ring
      rw [h_nkk]
      -- And `n - (k + 1) - 1 = n - k - 2`.
      have h_nm2 : n - (k + 1) - 1 = n - k - 2 := by omega
      rw [h_nm2]
      -- Multiply through. Clear all fractions.
      -- Strategy: multiply by common denominator and use ring after substituting
      -- the four factorial identities.
      -- Use `linear_combination` with explicit coefficients.
      --
      -- Express Δ_n and Δ_{n-1} rationally using the identities.
      -- Define shorthand (as hypotheses) to tame the expression sizes.
      set A : ℚ := (Nat.factorial k : ℚ) with hA
      set Fn : ℚ := (Nat.factorial n : ℚ) with hFn
      set Fnm : ℚ := (Nat.factorial (n - 1) : ℚ) with hFnm
      set Fnk : ℚ := (Nat.factorial (n + k) : ℚ) with hFnk
      set Fnk1 : ℚ := (Nat.factorial (n + k + 1) : ℚ) with hFnk1
      set Fmk1 : ℚ := (Nat.factorial (n - k - 1) : ℚ) with hFmk1
      set Fmk2 : ℚ := (Nat.factorial (n - k - 2) : ℚ) with hFmk2
      set Fk1 : ℚ := (Nat.factorial (k + 1) : ℚ) with hFk1
      -- Relate Fk1 to A: (k+1)! = (k+1) · k!
      have hFk1_eq : Fk1 = ((k : ℚ) + 1) * A := by
        simp [hFk1, hA, Nat.factorial_succ]
      -- Relate Fn to Fnm: n! = n · (n-1)!
      have hFn_eq : Fn = (n : ℚ) * Fnm := hfac_n_unfold
      -- Relate Fnk1 to Fnk: (n+k+1)! = (n+k+1) · (n+k)!
      have hFnk1_eq : Fnk1 = ((n : ℚ) + k + 1) * Fnk := by
        rw [hfac_nk1_unfold, hnk1Q]
      -- Relate Fmk1 to Fmk2: (n-k-1)! = (n-k-1) · (n-k-2)!
      have hFmk1_eq : Fmk1 = ((n : ℚ) - k - 1) * Fmk2 := by
        rw [hfac_nmk1_unfold, hnkQ]
      -- Rewrite all factorial-ids via set.
      have hCn_id' : (Nat.choose n (k + 1) : ℚ) * Fk1 * Fmk1 = Fn := hCn_id
      have hCnk_id' : (Nat.choose (n + k + 1) (k + 1) : ℚ) * Fk1 * Fn = Fnk1 := hCnk_id
      have hCnm_id' : (Nat.choose (n - 1) (k + 1) : ℚ) * Fk1 * Fmk2 = Fnm := hCnm_id
      have hCmk_id' : (Nat.choose (n + k) (k + 1) : ℚ) * Fk1 * Fnm = Fnk := hCmk_id
      -- Short names for the binomial values (to avoid cast noise).
      set b1 : ℚ := (Nat.choose n (k + 1) : ℚ) with hb1
      set b2 : ℚ := (Nat.choose (n + k + 1) (k + 1) : ℚ) with hb2
      set b3 : ℚ := (Nat.choose (n - 1) (k + 1) : ℚ) with hb3
      set b4 : ℚ := (Nat.choose (n + k) (k + 1) : ℚ) with hb4
      have hb1_ne : b1 ≠ 0 := hCnQ_ne
      have hb2_ne : b2 ≠ 0 := hCnkQ_ne
      have hb3_ne : b3 ≠ 0 := hCnmQ_ne
      have hb4_ne : b4 ≠ 0 := hCmkQ_ne
      have hFn_ne : Fn ≠ 0 := by
        simp [hFn]; exact_mod_cast (Nat.factorial_pos n).ne'
      have hFnm_ne : Fnm ≠ 0 := by
        simp [hFnm]; exact_mod_cast (Nat.factorial_pos _).ne'
      have hFnk_ne : Fnk ≠ 0 := by
        simp [hFnk]; exact_mod_cast (Nat.factorial_pos _).ne'
      have hFnk1_ne : Fnk1 ≠ 0 := by
        simp [hFnk1]; exact_mod_cast (Nat.factorial_pos _).ne'
      have hFmk1_ne : Fmk1 ≠ 0 := by
        simp [hFmk1]; exact_mod_cast (Nat.factorial_pos _).ne'
      have hFmk2_ne : Fmk2 ≠ 0 := by
        simp [hFmk2]; exact_mod_cast (Nat.factorial_pos _).ne'
      have hFk1_ne : Fk1 ≠ 0 := by
        simp [hFk1]; exact_mod_cast (Nat.factorial_pos _).ne'
      have hA_ne : A ≠ 0 := by
        simp [hA]; exact_mod_cast (Nat.factorial_pos _).ne'
      -- From the four binomial-factorial identities, solve for each binomial.
      have hb1_val : b1 = Fn / (Fk1 * Fmk1) := by
        rw [eq_div_iff (mul_ne_zero hFk1_ne hFmk1_ne), ← mul_assoc]; exact hCn_id'
      have hb2_val : b2 = Fnk1 / (Fk1 * Fn) := by
        rw [eq_div_iff (mul_ne_zero hFk1_ne hFn_ne), ← mul_assoc]; exact hCnk_id'
      have hb3_val : b3 = Fnm / (Fk1 * Fmk2) := by
        rw [eq_div_iff (mul_ne_zero hFk1_ne hFmk2_ne), ← mul_assoc]; exact hCnm_id'
      have hb4_val : b4 = Fnk / (Fk1 * Fnm) := by
        rw [eq_div_iff (mul_ne_zero hFk1_ne hFnm_ne), ← mul_assoc]; exact hCmk_id'
      -- Now the goal is a rational function equation in (n, k, and the set
      -- variables).  Substitute binomial values and reduce.
      rw [hb1_val, hb2_val, hb3_val, hb4_val]
      -- Substitute Fk1, Fn, Fnk1, Fmk1 — both in the goal and in the IH.
      rw [hFk1_eq, hFn_eq, hFnk1_eq, hFmk1_eq]
      rw [hFmk1_eq] at ih'
      -- Use `linear_combination` with IH to avoid `field_simp`'s blow-up.
      -- First, introduce shortnames for the two "big" denominators on LHS.
      -- After substitutions, the goal is purely rational in n, k, A, Fnm, Fnk, Fmk2.
      -- Nonzero facts needed for field_simp:
      have hnkp1_ne : ((n : ℚ) + k + 1) ≠ 0 := by
        have : (0 : ℚ) < (n : ℚ) + k + 1 := by positivity
        linarith
      have hnkm1_ne : ((n : ℚ) - k - 1) ≠ 0 := by
        have h1 : (1 : ℚ) ≤ ((n - k - 1 : ℕ) : ℚ) := by exact_mod_cast hnk1_pos
        have h2 : ((n - k - 1 : ℕ) : ℚ) = (n : ℚ) - k - 1 := hnkQ
        linarith
      linear_combination (norm := (field_simp; ring)) ih'
@[simp]
lemma aperyD_zero : aperyD 0 = 0 := by
  unfold aperyD
  simp [Finset.sum_range_succ, Finset.sum_range_zero]

/-- The `k = 0` summand of `aperyD` vanishes, since `e(n, 0) = 0`. -/
lemma aperyD_k0_zero (n : ℕ) :
    (Nat.choose n 0 : ℚ) ^ 2 * (Nat.choose (n + 0) 0 : ℚ) ^ 2 * aperyE n 0 = 0 := by
  simp

/-- `aperyD` expressed as a sum starting at `k = 1` (the `k = 0` term is zero). -/
lemma aperyD_eq_sum_from_one (n : ℕ) :
    aperyD n = ∑ k ∈ Finset.Ico 1 (n + 1),
      (Nat.choose n k : ℚ) ^ 2 * (Nat.choose (n + k) k : ℚ) ^ 2 * aperyE n k := by
  unfold aperyD
  rw [show Finset.range (n + 1) = insert 0 (Finset.Ico 1 (n + 1)) from by
        ext k; simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Ico]; omega]
  rw [Finset.sum_insert (by simp)]
  simp

/-- **Successor form of the closed-form `E`-difference.** For `k ≤ n`:

    `e(n+1,k) − e(n,k) + 1/(n+1)³
      = (−1)^k · k!² · (n−k)! / ((n+1)² · (n+1+k)!)`.

    Direct corollary of `aperyE_diff_pred_closed` applied at `m = n+1`. -/
lemma aperyE_diff_succ_closed (n k : ℕ) (hk : k ≤ n) :
    aperyE (n + 1) k - aperyE n k + 1 / (((n : ℚ) + 1) ^ 3)
      = (-1 : ℚ) ^ k * (Nat.factorial k : ℚ) ^ 2 * (Nat.factorial (n - k) : ℚ)
          / (((n : ℚ) + 1) ^ 2 * (Nat.factorial (n + 1 + k) : ℚ)) := by
  have h := aperyE_diff_pred_closed (n + 1) k (Nat.succ_le_succ (Nat.zero_le _))
    (by omega)
  -- `(n + 1) - 1 = n`, `(n + 1) - k - 1 = n - k`, `((n + 1 : ℕ) : ℚ) = (n : ℚ) + 1`.
  have h1 : n + 1 - 1 = n := by omega
  have h2 : n + 1 - k - 1 = n - k := by omega
  rw [h1, h2] at h
  have h3 : ((n + 1 : ℕ) : ℚ) = (n : ℚ) + 1 := by push_cast; ring
  rw [h3] at h
  exact h

/-! ### Abel-telescoping for the e-weighted T sum

The Zeilberger identity `T(n,k) = B(n,k) − B(n,k−1)` (from
`apery_telescoping`) does NOT give a pointwise identity when summed
against `e(n,k)` to produce `F_D(n) − [a(n−1) − a(n+1)]`.  Instead,
summing by parts (Abel summation) transforms the `T·e` sum into
`−Σ B(n,k) · Δe(n,k)`, where `Δe(n,k) = e(n,k+1) − e(n,k)` has the
closed form from `aperyE_diff_right_closed`.  This is the first
structural step toward `aperyD_recurrence`. -/
lemma aperyD_abel_telescope (n : ℕ) (hn : 1 ≤ n) :
    ∑ k ∈ Finset.range (n + 2),
        (((n + 1 : ℤ) ^ 3 * apery_P (n + 1) k
          - (34 * (n : ℤ) ^ 3 + 51 * n ^ 2 + 27 * n + 5) * apery_P n k
          + (n : ℤ) ^ 3 * apery_P (n - 1) k : ℤ) : ℚ) * aperyE n k
      = - ∑ k ∈ Finset.range (n + 1),
            ((apery_B n k : ℤ) : ℚ) * (aperyE n (k + 1) - aperyE n k) := by
  -- Short name for the T-summand.
  set T : ℕ → ℤ := fun k =>
    (n + 1 : ℤ) ^ 3 * apery_P (n + 1) k
      - (34 * (n : ℤ) ^ 3 + 51 * n ^ 2 + 27 * n + 5) * apery_P n k
      + (n : ℤ) ^ 3 * apery_P (n - 1) k with hT_def
  -- Peel off k = 0 using e(n,0) = 0.
  rw [Finset.sum_range_succ']
  simp only [aperyE_zero, mul_zero, add_zero]
  -- Now the sum is over `range (n+1)`, with shifted index (k+1). Peel off top.
  rw [Finset.sum_range_succ]
  -- T(k+1) for k ∈ range n uses apery_telescoping.
  have htele : ∀ k ∈ Finset.range n,
      ((T (k + 1) : ℤ) : ℚ) * aperyE n (k + 1)
        = ((apery_B n (k + 1) - apery_B n k : ℤ) : ℚ) * aperyE n (k + 1) := by
    intro k hk
    simp only [Finset.mem_range] at hk
    have hk1 : 1 ≤ k + 1 := Nat.succ_le_succ (Nat.zero_le _)
    have hkn : k + 1 ≤ n := hk
    have hAT := apery_telescoping n (k + 1) hk1 hkn
    have hsub : (k + 1) - 1 = k := by omega
    rw [hsub] at hAT
    have hTeq : T (k + 1) = apery_B n (k + 1) - apery_B n k := by
      simp only [hT_def]; linarith
    rw [hTeq]
  rw [Finset.sum_congr rfl htele]
  -- Now goal: (Σ k ∈ range n, (B(n,k+1) − B(n,k)) · e(n,k+1)) + T(n+1) · e(n,n+1)
  --          = −Σ k ∈ range (n+1), B(n,k) · Δe(n,k).
  -- T(n+1) = −B(n,n) (by T_at_top).
  have hTtop : T (n + 1) = - apery_B n n := by
    simp only [hT_def]; exact T_at_top n hn
  have hTtopQ : ((T (n + 1) : ℤ) : ℚ) = ((- apery_B n n : ℤ) : ℚ) := by
    rw [hTtop]
  rw [hTtopQ]
  -- Split out middle sum: (B(n,k+1) − B(n,k)) · e(n,k+1)
  --   = B(n,k+1) · e(n,k+1) − B(n,k) · e(n,k+1)
  have hmid_rw : ∀ k ∈ Finset.range n,
      ((apery_B n (k + 1) - apery_B n k : ℤ) : ℚ) * aperyE n (k + 1)
        = ((apery_B n (k + 1) : ℤ) : ℚ) * aperyE n (k + 1)
          - ((apery_B n k : ℤ) : ℚ) * aperyE n (k + 1) := by
    intro k _; push_cast; ring
  rw [Finset.sum_congr rfl hmid_rw, Finset.sum_sub_distrib]
  -- Reindex: Σ_{k ∈ range n} B(n, k+1) · e(n, k+1) = Σ_{k ∈ range n} B(n, k+1) · e(n, k+1).
  -- Use Finset.sum_range_succ' to shift on the first sum: Σ B(n,k+1) e(n,k+1) is the sum
  -- from k=0..n-1 of the "B·e shifted up". Equivalently this equals (Σ over k=1..n of B(n,k)·e(n,k)).
  -- Strategy: rewrite everything over a common range(n+1) with indices.
  -- Denote f(k) := B(n,k)·e(n,k) over ℚ. Then:
  --   Σ_{k∈range n} B(n,k+1) e(n,k+1) = Σ_{k∈range (n+1)} f(k) − f(0) = f(n) + Σ_{k∈range n} f(k) − f(0).
  -- Hmm let's do it cleanly via sum_range_succ'.
  -- Rewrite LHS sum A: ∑_{k ∈ range n}, B(n,k+1) e(n,k+1).
  -- We claim: ∑_{k ∈ range n}, B(n,k+1) e(n,k+1) = ∑_{k ∈ range (n+1)}, B(n,k) e(n,k).
  -- This is because B(n,0) e(n,0) = 0, and reindex k+1 = k'.
  have hsumA :
      ∑ k ∈ Finset.range n, ((apery_B n (k + 1) : ℤ) : ℚ) * aperyE n (k + 1)
        = ∑ k ∈ Finset.range (n + 1), ((apery_B n k : ℤ) : ℚ) * aperyE n k := by
    rw [Finset.sum_range_succ' (fun k => ((apery_B n k : ℤ) : ℚ) * aperyE n k) n]
    simp [aperyE_zero]
  rw [hsumA]
  -- Goal now:
  --   (∑ k ∈ range (n+1), B(n,k) e(n,k) − ∑ k ∈ range n, B(n,k) e(n,k+1))
  --     + (−B(n,n)) · e(n,n+1)
  --   = −∑ k ∈ range (n+1), B(n,k) · Δe(n,k)
  -- where Δe(n,k) = e(n,k+1) − e(n,k).
  -- Expand RHS: −∑ B(n,k) · Δe(n,k) = ∑ B(n,k) e(n,k) − ∑ B(n,k) e(n,k+1).
  -- So we need:
  --   ∑ range(n+1) B(n,k) e(n,k) − ∑ range(n) B(n,k) e(n,k+1) − B(n,n) e(n,n+1)
  --     = ∑ range(n+1) B(n,k) e(n,k) − ∑ range(n+1) B(n,k) e(n,k+1).
  -- That is: ∑ range(n) B(n,k) e(n,k+1) + B(n,n) e(n,n+1) = ∑ range(n+1) B(n,k) e(n,k+1).
  -- Which is just peeling off k=n on the right via sum_range_succ.
  have : ∑ k ∈ Finset.range (n + 1),
            ((apery_B n k : ℤ) : ℚ) * (aperyE n (k + 1) - aperyE n k)
          = ∑ k ∈ Finset.range (n + 1),
              ((apery_B n k : ℤ) : ℚ) * aperyE n (k + 1)
            - ∑ k ∈ Finset.range (n + 1),
              ((apery_B n k : ℤ) : ℚ) * aperyE n k := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro k _; ring
  rw [this]
  -- Peel off k = n from ∑ range (n+1), B(n,k) e(n,k+1):
  have hRsplit : ∑ k ∈ Finset.range (n + 1),
            ((apery_B n k : ℤ) : ℚ) * aperyE n (k + 1)
        = ∑ k ∈ Finset.range n, ((apery_B n k : ℤ) : ℚ) * aperyE n (k + 1)
          + ((apery_B n n : ℤ) : ℚ) * aperyE n (n + 1) := by
    rw [Finset.sum_range_succ]
  rw [hRsplit]
  push_cast
  ring

/-- **Range-extension for `aperyD`.**

    For `n ≤ m`, the defining sum of `aperyD n` may be extended from
    `range (n+1)` up to `range (m+1)` — the extra summands all vanish
    since `C(n, k) = 0` for `k > n`, hence `P(n, k) = 0` and each
    coefficient in the sum is zero.

    This is the `aperyD` analogue of `aperyA_int_extended`.  It is the
    first structural ingredient of `aperyD_recurrence`: the three
    sequences `aperyD (n-1)`, `aperyD n`, `aperyD (n+1)` use different
    native ranges, and this lemma unifies them onto a single range
    `range (n + 2)` so that the `F_D`-sum may be taken termwise. -/
lemma aperyD_range_extended (n m : ℕ) (hm : n ≤ m) :
    aperyD n = ∑ k ∈ Finset.range (m + 1),
      (Nat.choose n k : ℚ) ^ 2 * (Nat.choose (n + k) k : ℚ) ^ 2 * aperyE n k := by
  unfold aperyD
  -- Split `range (m+1) = range (n+1) ∪ Ico (n+1) (m+1)` and show the second part is zero.
  have hsplit : Finset.range (m + 1)
      = Finset.range (n + 1) ∪ Finset.Ico (n + 1) (m + 1) := by
    ext k
    simp only [Finset.mem_range, Finset.mem_union, Finset.mem_Ico]
    omega
  rw [hsplit]
  have hdisj : Disjoint (Finset.range (n + 1)) (Finset.Ico (n + 1) (m + 1)) := by
    rw [Finset.disjoint_left]
    intro k hk hk'
    simp only [Finset.mem_range] at hk
    simp only [Finset.mem_Ico] at hk'
    omega
  rw [Finset.sum_union hdisj]
  have hzero : ∑ k ∈ Finset.Ico (n + 1) (m + 1),
      (Nat.choose n k : ℚ) ^ 2 * (Nat.choose (n + k) k : ℚ) ^ 2 * aperyE n k = 0 := by
    apply Finset.sum_eq_zero
    intro k hk
    simp only [Finset.mem_Ico] at hk
    have hkn : n < k := by omega
    have hCn : Nat.choose n k = 0 := Nat.choose_eq_zero_of_lt hkn
    rw [hCn]
    push_cast
    ring
  rw [hzero, add_zero]

/-- **Three-sum decomposition of `F_D(n)`.**

    After unifying the summation ranges (via `aperyD_range_extended`),
    the `F_D`-expression rewrites as a sum of T·e over `range (n+2)`
    plus boundary corrections δ₊, δ₋ capturing `e(n±1, k) − e(n, k)`:

    `F_D(n) = Σ T(n,k)·e(n,k)
             + Σ (n+1)³·P(n+1,k)·[e(n+1,k) − e(n,k)]
             − Σ n³·P(n-1,k)·[e(n,k) − e(n-1,k)]`,

    where `T(n,k) := (n+1)³ P(n+1,k) − (34n³+51n²+27n+5) P(n,k)
                      + n³ P(n-1,k)` is the telescoping summand from F1.

    This identity is purely algebraic — it holds by expanding each
    `aperyD` as its unified sum, substituting
    `e(n±1, k) = e(n, k) + (e(n±1, k) − e(n, k))`, and collecting. -/
lemma aperyD_recurrence_three_sum_form (n : ℕ) (hn : 1 ≤ n) :
    ((n + 1 : ℚ) ^ 3) * aperyD (n + 1)
      - (34 * (n : ℚ) ^ 3 + 51 * n ^ 2 + 27 * n + 5) * aperyD n
      + (n : ℚ) ^ 3 * aperyD (n - 1)
    = ∑ k ∈ Finset.range (n + 2),
        (((n + 1 : ℤ) ^ 3 * apery_P (n + 1) k
          - (34 * (n : ℤ) ^ 3 + 51 * n ^ 2 + 27 * n + 5) * apery_P n k
          + (n : ℤ) ^ 3 * apery_P (n - 1) k : ℤ) : ℚ) * aperyE n k
      + ∑ k ∈ Finset.range (n + 2),
          ((n + 1 : ℚ) ^ 3) * ((apery_P (n + 1) k : ℤ) : ℚ)
            * (aperyE (n + 1) k - aperyE n k)
      - ∑ k ∈ Finset.range (n + 2),
          ((n : ℚ) ^ 3) * ((apery_P (n - 1) k : ℤ) : ℚ)
            * (aperyE n k - aperyE (n - 1) k) := by
  -- Unify all three `aperyD` to `range (n + 2)`.
  rw [aperyD_range_extended (n + 1) (n + 1) (le_refl _),
      aperyD_range_extended n (n + 1) (Nat.le_succ _),
      aperyD_range_extended (n - 1) (n + 1) (by omega)]
  -- Cast `apery_P` from ℤ to the rational sum-form.
  have hPeq : ∀ (m : ℕ) (k : ℕ),
      (Nat.choose m k : ℚ) ^ 2 * (Nat.choose (m + k) k : ℚ) ^ 2
        = ((apery_P m k : ℤ) : ℚ) := by
    intro m k
    unfold apery_P
    push_cast
    ring
  -- Rewrite each `(C·C)²` as `apery_P`.
  simp_rw [hPeq]
  -- Distribute constants into the three sums on the LHS (Finset.mul_sum),
  -- distribute the sum_add/sub on the RHS to one big sum, then compare
  -- termwise via `sum_congr`.
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro k _
  push_cast
  ring

/-- **Abel-reduced form of the `F_D` recurrence.**

    Combining `aperyD_recurrence_three_sum_form` (three-sum expansion)
    with `aperyD_abel_telescope` (Abel summation on the T·e sum), the
    `F_D(n)` quantity equals

    `−Σ_{k∈range(n+1)} B(n,k) · Δe(n,k)
        + Σ_{k∈range(n+2)} (n+1)³ P(n+1,k) · δ₊(n,k)
        − Σ_{k∈range(n+2)} n³ P(n-1,k) · δ₋(n,k)`,

    where `Δe(n,k) := e(n,k+1) − e(n,k)`,
    `δ₊(n,k) := e(n+1,k) − e(n,k)`, and
    `δ₋(n,k) := e(n,k) − e(n-1,k)`.

    Proving that this quantity equals `a(n-1) − a(n+1)` is the
    remaining sum-level factorial identity in `aperyD_recurrence`. -/
lemma aperyD_recurrence_abel_form (n : ℕ) (hn : 1 ≤ n) :
    ((n + 1 : ℚ) ^ 3) * aperyD (n + 1)
      - (2 * n + 1 : ℚ) * (17 * n ^ 2 + 17 * n + 5) * aperyD n
      + (n : ℚ) ^ 3 * aperyD (n - 1)
    = - ∑ k ∈ Finset.range (n + 1),
            ((apery_B n k : ℤ) : ℚ) * (aperyE n (k + 1) - aperyE n k)
      + ∑ k ∈ Finset.range (n + 2),
          ((n + 1 : ℚ) ^ 3) * ((apery_P (n + 1) k : ℤ) : ℚ)
            * (aperyE (n + 1) k - aperyE n k)
      - ∑ k ∈ Finset.range (n + 2),
          ((n : ℚ) ^ 3) * ((apery_P (n - 1) k : ℤ) : ℚ)
            * (aperyE n k - aperyE (n - 1) k) := by
  -- Coefficient identity: (2n+1)(17n²+17n+5) = 34n³+51n²+27n+5.
  have hcoef : (2 * (n : ℚ) + 1) * (17 * n ^ 2 + 17 * n + 5)
      = 34 * (n : ℚ) ^ 3 + 51 * n ^ 2 + 27 * n + 5 := by ring
  -- Replace the "(2n+1)(17n²+17n+5)" coefficient with the expanded form
  -- to match `aperyD_recurrence_three_sum_form`.
  have hLHS : ((n + 1 : ℚ) ^ 3) * aperyD (n + 1)
        - (2 * (n : ℚ) + 1) * (17 * n ^ 2 + 17 * n + 5) * aperyD n
        + (n : ℚ) ^ 3 * aperyD (n - 1)
      = ((n + 1 : ℚ) ^ 3) * aperyD (n + 1)
        - (34 * (n : ℚ) ^ 3 + 51 * n ^ 2 + 27 * n + 5) * aperyD n
        + (n : ℚ) ^ 3 * aperyD (n - 1) := by
    rw [hcoef]
  rw [hLHS]
  -- Apply the three-sum decomposition.
  rw [aperyD_recurrence_three_sum_form n hn]
  -- Apply Abel summation on the T·e sum.
  rw [aperyD_abel_telescope n hn]

/-- **Error-sequence recurrence (irreducible core — Zeilberger witness).**

    The error series `dₙ = Σ_k P(n,k) · e(n,k)` satisfies the
    inhomogeneous recurrence
    `(n+1)³ dₙ₊₁ − (2n+1)(17n²+17n+5) dₙ + n³ dₙ₋₁ = aₙ₋₁ − aₙ₊₁`.

    Proof: van der Poorten 1979 §8, pp. 201–203.  Scaffolding in place:

    * `aperyE_diff_pred_closed` (proved, ~250 lines, axiom-free) — gives
      `e(n,k) − e(n−1,k) + 1/n³ = Δ₋(n,k)` closed form.
    * `aperyE_diff_succ_closed` (proved) — `n+1` counterpart.
    * `aperyE_diff_right_closed` (proved) — k-difference closed form.
    * `apery_telescoping` (proved in AperyCertificate) — Zeilberger
      k-telescope for `P` weighted by `B(n,k)`.
    * `aperyD_abel_telescope` (proved) — Abel summation transforms
      `Σ_{k∈range(n+2)} T(n,k) e(n,k) = −Σ_{k∈range(n+1)} B(n,k) Δe(n,k)`.
    * `aperyA_int_extended` — range-extension lemma used in F1.

    **Remaining residual (what the `sorry` below covers):** after
    expanding `F_D(n)` via the three-sum decomposition
    `F_D = Σ T·e + Σ (n+1)³ p(n+1,k) δ₊ − Σ n³ p(n-1,k) δ₋` and
    applying `aperyD_abel_telescope`, the target reduces to

        `Σ_{k∈range(n+2)} [(n+1)³ P(n+1,k) δ₊(n,k) − n³ P(n-1,k) δ₋(n,k)]
                − Σ_{k∈range(n+1)} B(n,k) Δe(n,k)
            = a(n-1) − a(n+1)`.

    Substituting the closed forms for δ₊, δ₋, Δe and reducing using
    `aperyA_int_extended` leaves a purely rational identity in factorials
    / binomial coefficients that does NOT hold pointwise in k — the
    telescope is genuinely sum-level.  Numerical check (via Python) at
    n ∈ {1, 2, 3, 4} confirms the identity holds but per-k residuals are
    nonzero; the identity is recovered only after summation.

    The remaining grind is: unfold closed forms of δ₊, δ₋, Δe, split the
    −1/(n+1)³, −1/n³ pieces from each closed form (these sum to
    ±a(n±1) using `aperyA_int_extended`), boundary-separate k=n+1 in the
    δ₊ sum, then establish the resulting pure-factorial identity
    `Σ k!²(n-k)!·{...}/[(n+1+k)!(n+k+1)!] = ...`.  This is van der
    Poorten's "massive reorganization" (1979, p. 201). -/
lemma aperyD_recurrence (n : ℕ) (hn : 1 ≤ n) :
    ((n + 1 : ℚ) ^ 3) * aperyD (n + 1)
      - (2 * n + 1 : ℚ) * (17 * n ^ 2 + 17 * n + 5) * aperyD n
      + (n : ℚ) ^ 3 * aperyD (n - 1)
    = (aperyA (n - 1) : ℚ) - (aperyA (n + 1) : ℚ) := by
  sorry

/-- Numerical sanity check at `n = 1`:
    `8 d₂ − 117 d₁ + d₀ = a₀ − a₂ = 1 − 73 = −72`,
    i.e. `d₂ = 45/8, d₁ = 1, d₀ = 0` gives `45 − 117 + 0 = −72`. -/
example :
    ((1 + 1 : ℚ) ^ 3) * aperyD (1 + 1)
      - (2 * 1 + 1 : ℚ) * (17 * 1 ^ 2 + 17 * 1 + 5) * aperyD 1
      + (1 : ℚ) ^ 3 * aperyD (1 - 1)
    = (aperyA (1 - 1) : ℚ) - (aperyA (1 + 1) : ℚ) := by
  show _ = ((aperyA 0 : ℕ) : ℚ) - ((aperyA 2 : ℕ) : ℚ)
  rw [aperyA_zero, aperyA_two]
  unfold aperyD aperyE
  simp only [Nat.choose, Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num

/-- Numerical sanity check at `n = 2`. -/
example :
    ((2 + 1 : ℚ) ^ 3) * aperyD (2 + 1)
      - (2 * 2 + 1 : ℚ) * (17 * 2 ^ 2 + 17 * 2 + 5) * aperyD 2
      + (2 : ℚ) ^ 3 * aperyD (2 - 1)
    = (aperyA (2 - 1) : ℚ) - (aperyA (2 + 1) : ℚ) := by
  show _ = ((aperyA 1 : ℕ) : ℚ) - ((aperyA 3 : ℕ) : ℚ)
  rw [aperyA_one, aperyA_three]
  unfold aperyD aperyE
  simp only [Nat.choose, Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num

/-- Numerical sanity check at `n = 3`. -/
example :
    ((3 + 1 : ℚ) ^ 3) * aperyD (3 + 1)
      - (2 * 3 + 1 : ℚ) * (17 * 3 ^ 2 + 17 * 3 + 5) * aperyD 3
      + (3 : ℚ) ^ 3 * aperyD (3 - 1)
    = (aperyA (3 - 1) : ℚ) - (aperyA (3 + 1) : ℚ) := by
  show _ = ((aperyA 2 : ℕ) : ℚ) - ((aperyA 4 : ℕ) : ℚ)
  rw [aperyA_two, aperyA_four]
  unfold aperyD aperyE
  simp only [Nat.choose, Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num

/-- **(F1', rational companion) — Apéry three-term recurrence for `bₙ`.**

    `bₙ` satisfies the *same* homogeneous three-term recurrence as `aₙ`
    (vdPoorten 1979, Thm 2, p. 196).  This is the structural reason why
    `bₙ / aₙ → ζ(3)`: both are solutions of a single linear recurrence,
    so the ratio stabilizes.

    **Proof structure (axiom-free reduction).**  Decompose
    `bₙ = H₃(n) · aₙ + dₙ` (lemma `aperyB_eq_decomp`).  The
    harmonic piece's recurrence inhomogeneity is `aₙ₊₁ − aₙ₋₁`
    (lemma `aperyHA_recurrence`); the error piece's recurrence
    inhomogeneity is `aₙ₋₁ − aₙ₊₁` (lemma `aperyD_recurrence`, which
    is the only residual `sorry` — the Zeilberger witness for the
    correction-term series, vdPoorten 1979 §8).  The two
    inhomogeneities cancel, yielding the homogeneous recurrence. -/
lemma aperyB_recurrence (n : ℕ) (hn : 1 ≤ n) :
    ((n + 1 : ℚ) ^ 3) * aperyB (n + 1)
      = (2 * n + 1 : ℚ) * (17 * n ^ 2 + 17 * n + 5) * aperyB n
          - (n : ℚ) ^ 3 * aperyB (n - 1) := by
  -- Expand `bₙ = H₃(n) · aₙ + dₙ` at all three indices.
  rw [aperyB_eq_decomp (n + 1), aperyB_eq_decomp n, aperyB_eq_decomp (n - 1)]
  -- Combine the harmonic and error recurrences.
  have hHA := aperyHA_recurrence n hn
  have hD := aperyD_recurrence n hn
  linarith

/-- Sanity check: `b₁ = 6`. -/
example : aperyB 1 = 6 := by
  unfold aperyB aperyC
  simp [Finset.sum_range_succ, Finset.sum_range_one]
  norm_num

/-- Sanity check: `b₂ = 351/4`. -/
example : aperyB 2 = 351 / 4 := by
  unfold aperyB aperyC
  simp [Finset.sum_range_succ, Finset.sum_range_one, Nat.choose]
  norm_num

/-! ## Generating functions `A(z)`, `B(z)` (formal power series)

    The Apéry ODE
        `p(z) A''' + q(z) A'' + r(z) A' + s(z) A = 0`
        `p(z) B''' + q(z) B'' + r(z) B' + s(z) B = 0`
    (both *homogeneous* — `A(z)` and `B(z)` are two linearly independent
    solutions of the same third-order operator; the ratio
    `B(z)/A(z) → ζ(3)`) where
        `p(z) = z² − 34 z³ + z⁴`,
        `q(z) = 3 z − 153 z² + 6 z³`,
        `r(z) = 1 − 112 z + 7 z²`,
        `s(z) = −5 + z`
    is the analytic content of (F2) of the Frobenius roadmap.

    At the formal-power-series level (coefficient-wise), the ODE is
    *equivalent* to the three-term recurrences `aperyA_recurrence` /
    `aperyB_recurrence` via standard shift-of-indices algebra.  So (F2)
    reduces to (F1) + (F1') — modulo the translation between coefficient
    recurrences and formal differential equations.

    We record `aperyGFA`, `aperyGFB` as formal series over `ℚ`, together
    with the ODE statement (F2).  The F2 sorry is thus provable *from*
    F1 + F1' + a small amount of `PowerSeries.derivative` algebra. -/

/-- Generating function `A(z) = Σ aₙ zⁿ` as a formal power series over `ℚ`. -/
noncomputable def aperyGFA : PowerSeries ℚ :=
  PowerSeries.mk (fun n => (aperyA n : ℚ))

/-- Generating function `B(z) = Σ bₙ zⁿ` as a formal power series over `ℚ`. -/
noncomputable def aperyGFB : PowerSeries ℚ :=
  PowerSeries.mk aperyB

@[simp]
lemma coeff_aperyGFA (n : ℕ) :
    PowerSeries.coeff (R := ℚ) n aperyGFA = (aperyA n : ℚ) := by
  unfold aperyGFA; simp [PowerSeries.coeff_mk]

@[simp]
lemma coeff_aperyGFB (n : ℕ) :
    PowerSeries.coeff (R := ℚ) n aperyGFB = aperyB n := by
  unfold aperyGFB; simp [PowerSeries.coeff_mk]

/-- Apéry's differential-operator coefficients `p, q, r, s` as rational
polynomials of `z`.  Used both in the formal-power-series ODE (F2) and
in the analytic incarnation at the conifold singularity. -/
noncomputable def aperyP : Polynomial ℚ :=
  Polynomial.monomial 2 1 + Polynomial.monomial 3 (-34) + Polynomial.monomial 4 1

noncomputable def aperyQ : Polynomial ℚ :=
  Polynomial.monomial 1 3 + Polynomial.monomial 2 (-153) + Polynomial.monomial 3 6

noncomputable def aperyRcoef : Polynomial ℚ :=
  Polynomial.monomial 0 1 + Polynomial.monomial 1 (-112) + Polynomial.monomial 2 7

noncomputable def aperyScoef : Polynomial ℚ :=
  Polynomial.monomial 0 (-5) + Polynomial.monomial 1 1

/-- Unified coefficient form of Apéry's recurrence, covering `n = 0`
    (where the `aperyA (n-1)` term has coefficient `0`) and `n ≥ 1`
    (where it reduces to `aperyA_recurrence`). -/
lemma aperyA_ode_coefficient (n : ℕ) :
    ((n + 1 : ℚ) ^ 3) * (aperyA (n + 1) : ℚ)
      - (2 * n + 1 : ℚ) * (17 * n ^ 2 + 17 * n + 5) * (aperyA n : ℚ)
      + (n : ℚ) ^ 3 * (aperyA (n - 1) : ℚ) = 0 := by
  rcases n with _ | m
  · simp [aperyA_zero, aperyA_one]
  · have hrec := aperyA_recurrence (m + 1) (Nat.le_add_left 1 m)
    have hsub : (m + 1 - 1 : ℕ) = m := by omega
    rw [hsub] at hrec
    -- hrec is over ℤ; cast to ℚ
    have hrecQ : ((m : ℚ) + 1 + 1) ^ 3 * (aperyA (m + 1 + 1) : ℚ)
        = (2 * ((m : ℚ) + 1) + 1) *
            (17 * ((m : ℚ) + 1) ^ 2 + 17 * ((m : ℚ) + 1) + 5) *
            (aperyA (m + 1) : ℚ)
          - ((m : ℚ) + 1) ^ 3 * (aperyA m : ℚ) := by
      have := congrArg ((↑·) : ℤ → ℚ) hrec
      push_cast at this
      linarith
    push_cast
    linear_combination hrecQ

/-- Coefficient of a polynomial in `toPowerSeries` form. -/
private lemma coeff_toPS (p : Polynomial ℚ) (n : ℕ) :
    PowerSeries.coeff (R := ℚ) n (p.toPowerSeries) = p.coeff n := by
  simp [Polynomial.coeff_coe]

/-- Explicit coefficient of `aperyP` viewed as a polynomial. -/
private lemma aperyP_coeff_explicit (n : ℕ) :
    aperyP.coeff n =
      (if 2 = n then 1 else 0)
      + (if 3 = n then -34 else 0)
      + (if 4 = n then 1 else 0) := by
  unfold aperyP
  simp only [Polynomial.coeff_add, Polynomial.coeff_monomial]

/-- Explicit coefficient of `aperyQ`. -/
private lemma aperyQ_coeff_explicit (n : ℕ) :
    aperyQ.coeff n =
      (if 1 = n then 3 else 0)
      + (if 2 = n then -153 else 0)
      + (if 3 = n then 6 else 0) := by
  unfold aperyQ
  simp only [Polynomial.coeff_add, Polynomial.coeff_monomial]

/-- Explicit coefficient of `aperyRcoef`. -/
private lemma aperyRcoef_coeff_explicit (n : ℕ) :
    aperyRcoef.coeff n =
      (if 0 = n then 1 else 0)
      + (if 1 = n then -112 else 0)
      + (if 2 = n then 7 else 0) := by
  unfold aperyRcoef
  simp only [Polynomial.coeff_add, Polynomial.coeff_monomial]

/-- Explicit coefficient of `aperyScoef`. -/
private lemma aperyScoef_coeff_explicit (n : ℕ) :
    aperyScoef.coeff n =
      (if 0 = n then -5 else 0)
      + (if 1 = n then 1 else 0) := by
  unfold aperyScoef
  simp only [Polynomial.coeff_add, Polynomial.coeff_monomial]

/-- Helper: the N-th coefficient of `poly.toPowerSeries * PowerSeries.mk f`
    is `∑_{i ∈ range (N+1)} poly.coeff i · f (N - i)`. -/
private lemma coeff_toPS_mul_mk (p : Polynomial ℚ) (f : ℕ → ℚ) (N : ℕ) :
    PowerSeries.coeff (R := ℚ) N (p.toPowerSeries * PowerSeries.mk f)
      = ∑ i ∈ Finset.range (N + 1), p.coeff i * f (N - i) := by
  rw [PowerSeries.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ
        (fun i j => PowerSeries.coeff (R := ℚ) i p.toPowerSeries
                    * PowerSeries.coeff (R := ℚ) j (PowerSeries.mk f)) N]
  simp [Polynomial.coeff_coe, PowerSeries.coeff_mk]

/-- Sum with indicator-if factored out: useful for reducing our convolution sums. -/
private lemma sum_ite_eq_select (N : ℕ) (k : ℕ) (c : ℚ) (g : ℕ → ℚ)
    (hk : k ≤ N) :
    ∑ i ∈ Finset.range (N + 1), (if k = i then c else 0) * g i = c * g k := by
  rw [Finset.sum_eq_single k]
  · simp
  · intro b _ hb; simp [Ne.symm hb]
  · intro h; exact absurd (Finset.mem_range.mpr (by omega)) h

private lemma sum_ite_eq_select_zero (N : ℕ) (k : ℕ) (c : ℚ) (g : ℕ → ℚ)
    (hk : N < k) :
    ∑ i ∈ Finset.range (N + 1), (if k = i then c else 0) * g i = 0 := by
  apply Finset.sum_eq_zero
  intro i hi
  rw [Finset.mem_range] at hi
  have : k ≠ i := by omega
  simp [this]

/-- The N-th coefficient of `aperyP.toPowerSeries * (Σ (a_{n+3}·(n+3)(n+2)(n+1)) zⁿ)`
    is the sum of the three contributing monomials' terms, for N ≥ 4. -/
private lemma aperyP_conv_coeff_ge4 (N : ℕ) (hN : 4 ≤ N) :
    PowerSeries.coeff (R := ℚ) N
        (aperyP.toPowerSeries * (PowerSeries.mk (fun n => (aperyA (n + 3) : ℚ) *
            ((n + 3) * (n + 2) * (n + 1) : ℚ))))
      = 1 * ((aperyA (N - 2 + 3) : ℚ) *
              (((N - 2 : ℕ) + 3) * ((N - 2 : ℕ) + 2) * ((N - 2 : ℕ) + 1) : ℚ))
        + (-34) * ((aperyA (N - 3 + 3) : ℚ) *
              (((N - 3 : ℕ) + 3) * ((N - 3 : ℕ) + 2) * ((N - 3 : ℕ) + 1) : ℚ))
        + 1 * ((aperyA (N - 4 + 3) : ℚ) *
              (((N - 4 : ℕ) + 3) * ((N - 4 : ℕ) + 2) * ((N - 4 : ℕ) + 1) : ℚ)) := by
  rw [coeff_toPS_mul_mk]
  simp_rw [aperyP_coeff_explicit, add_mul]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  rw [sum_ite_eq_select N 2 1 _ (by omega),
      sum_ite_eq_select N 3 (-34) _ (by omega),
      sum_ite_eq_select N 4 1 _ (by omega)]

private lemma aperyQ_conv_coeff_ge3 (N : ℕ) (hN : 3 ≤ N) :
    PowerSeries.coeff (R := ℚ) N
        (aperyQ.toPowerSeries * (PowerSeries.mk (fun n => (aperyA (n + 2) : ℚ) *
            ((n + 2) * (n + 1) : ℚ))))
      = 3 * ((aperyA (N - 1 + 2) : ℚ) *
              (((N - 1 : ℕ) + 2) * ((N - 1 : ℕ) + 1) : ℚ))
        + (-153) * ((aperyA (N - 2 + 2) : ℚ) *
              (((N - 2 : ℕ) + 2) * ((N - 2 : ℕ) + 1) : ℚ))
        + 6 * ((aperyA (N - 3 + 2) : ℚ) *
              (((N - 3 : ℕ) + 2) * ((N - 3 : ℕ) + 1) : ℚ)) := by
  rw [coeff_toPS_mul_mk]
  simp_rw [aperyQ_coeff_explicit, add_mul]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  rw [sum_ite_eq_select N 1 3 _ (by omega),
      sum_ite_eq_select N 2 (-153) _ (by omega),
      sum_ite_eq_select N 3 6 _ (by omega)]

private lemma aperyR_conv_coeff_ge2 (N : ℕ) (hN : 2 ≤ N) :
    PowerSeries.coeff (R := ℚ) N
        (aperyRcoef.toPowerSeries * (PowerSeries.mk (fun n => (aperyA (n + 1) : ℚ) *
            ((n + 1) : ℚ))))
      = 1 * ((aperyA (N - 0 + 1) : ℚ) * (((N - 0 : ℕ) + 1) : ℚ))
        + (-112) * ((aperyA (N - 1 + 1) : ℚ) * (((N - 1 : ℕ) + 1) : ℚ))
        + 7 * ((aperyA (N - 2 + 1) : ℚ) * (((N - 2 : ℕ) + 1) : ℚ)) := by
  rw [coeff_toPS_mul_mk]
  simp_rw [aperyRcoef_coeff_explicit, add_mul]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  rw [sum_ite_eq_select N 0 1 _ (by omega),
      sum_ite_eq_select N 1 (-112) _ (by omega),
      sum_ite_eq_select N 2 7 _ (by omega)]

private lemma aperyS_conv_coeff_ge1 (N : ℕ) (hN : 1 ≤ N) :
    PowerSeries.coeff (R := ℚ) N
        (aperyScoef.toPowerSeries * aperyGFA)
      = (-5) * (aperyA (N - 0) : ℚ) + 1 * (aperyA (N - 1) : ℚ) := by
  unfold aperyGFA
  rw [coeff_toPS_mul_mk]
  simp_rw [aperyScoef_coeff_explicit, add_mul]
  rw [Finset.sum_add_distrib]
  rw [sum_ite_eq_select N 0 (-5) _ (by omega),
      sum_ite_eq_select N 1 1 _ (by omega)]

/-- Helper: for N ≥ 4, the sum of the four convolutions matches the ODE coefficient. -/
private lemma aperyGFA_ode_coeff_ge4 (N : ℕ) (hN : 4 ≤ N) :
    PowerSeries.coeff (R := ℚ) N
      (aperyP.toPowerSeries * (PowerSeries.mk (fun n => (aperyA (n + 3) : ℚ) *
          ((n + 3) * (n + 2) * (n + 1) : ℚ)))
        + aperyQ.toPowerSeries * (PowerSeries.mk (fun n => (aperyA (n + 2) : ℚ) *
          ((n + 2) * (n + 1) : ℚ)))
        + aperyRcoef.toPowerSeries * (PowerSeries.mk (fun n => (aperyA (n + 1) : ℚ) *
          ((n + 1) : ℚ)))
        + aperyScoef.toPowerSeries * aperyGFA) = 0 := by
  rw [map_add, map_add, map_add,
      aperyP_conv_coeff_ge4 N hN,
      aperyQ_conv_coeff_ge3 N (by omega),
      aperyR_conv_coeff_ge2 N (by omega),
      aperyS_conv_coeff_ge1 N (by omega)]
  -- Now need to show the accumulated sum = 0
  -- Rewrite nat subtractions into usable form
  obtain ⟨m, rfl⟩ : ∃ m, N = m + 4 := ⟨N - 4, by omega⟩
  have h1 : m + 4 - 0 = m + 4 := by omega
  have h2 : m + 4 - 1 = m + 3 := by omega
  have h3 : m + 4 - 2 = m + 2 := by omega
  have h4 : m + 4 - 3 = m + 1 := by omega
  have h5 : m + 4 - 4 = m := by omega
  simp only [h1, h2, h3, h4, h5]
  -- Normalize nat index sums: m+2+3 = m+5, m+1+3 = m+4, m+3+2 = m+5, etc.
  have e1 : m + 2 + 3 = m + 5 := by omega
  have e2 : m + 1 + 3 = m + 4 := by omega
  have e3 : m + 3 + 2 = m + 5 := by omega
  have e4 : m + 2 + 2 = m + 4 := by omega
  have e5 : m + 1 + 2 = m + 3 := by omega
  have e6 : m + 4 + 1 = m + 5 := by omega
  have e7 : m + 3 + 1 = m + 4 := by omega
  have e8 : m + 2 + 1 = m + 3 := by omega
  simp only [e1, e2, e3, e4, e5, e6, e7, e8]
  -- Apply the ODE coefficient identity at n = m+4
  have hode := aperyA_ode_coefficient (m + 4)
  have heq1 : m + 4 + 1 = m + 5 := by omega
  have heq2 : m + 4 - 1 = m + 3 := by omega
  rw [heq1, heq2] at hode
  push_cast at hode
  push_cast
  linarith [hode]

/-- Helper: for N ∈ {0, 1, 2, 3}, verify the ODE coefficient identity by
    direct computation using the explicit small values of `aperyA`. -/
private lemma aperyGFA_ode_coeff_small (N : ℕ) (hN : N < 4) :
    PowerSeries.coeff (R := ℚ) N
      (aperyP.toPowerSeries * (PowerSeries.mk (fun n => (aperyA (n + 3) : ℚ) *
          ((n + 3) * (n + 2) * (n + 1) : ℚ)))
        + aperyQ.toPowerSeries * (PowerSeries.mk (fun n => (aperyA (n + 2) : ℚ) *
          ((n + 2) * (n + 1) : ℚ)))
        + aperyRcoef.toPowerSeries * (PowerSeries.mk (fun n => (aperyA (n + 1) : ℚ) *
          ((n + 1) : ℚ)))
        + aperyScoef.toPowerSeries * aperyGFA) = 0 := by
  rw [map_add, map_add, map_add]
  unfold aperyGFA
  simp only [coeff_toPS_mul_mk, PowerSeries.coeff_mk]
  -- For small N, unfold the coefficient sums manually
  interval_cases N <;>
    (simp [Finset.sum_range_succ, aperyP_coeff_explicit, aperyQ_coeff_explicit,
           aperyRcoef_coeff_explicit, aperyScoef_coeff_explicit,
           aperyA_zero, aperyA_one, aperyA_two, aperyA_three, aperyA_four]) <;>
    norm_num

/-- **(F2) — Apéry ODE (homogeneous part) as a formal power series identity.**

    Reduces coefficient-by-coefficient to `aperyA_ode_coefficient`. -/
lemma aperyGFA_satisfies_ode :
    aperyP.toPowerSeries * (PowerSeries.mk (fun n => (aperyA (n + 3) : ℚ) *
        ((n + 3) * (n + 2) * (n + 1) : ℚ)))
      + aperyQ.toPowerSeries * (PowerSeries.mk (fun n => (aperyA (n + 2) : ℚ) *
        ((n + 2) * (n + 1) : ℚ)))
      + aperyRcoef.toPowerSeries * (PowerSeries.mk (fun n => (aperyA (n + 1) : ℚ) *
        ((n + 1) : ℚ)))
      + aperyScoef.toPowerSeries * aperyGFA
    = 0 := by
  apply PowerSeries.ext
  intro N
  rw [map_zero]
  by_cases hN : 4 ≤ N
  · exact aperyGFA_ode_coeff_ge4 N hN
  · exact aperyGFA_ode_coeff_small N (by omega)

end Number
end Ripple
