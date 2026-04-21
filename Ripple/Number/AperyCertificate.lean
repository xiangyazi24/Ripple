/-
  Ripple.Number.AperyCertificate — van der Poorten's Zeilberger
  certificate for the Apéry recurrence.

  Source: Alfred van der Poorten, "A Proof that Euler Missed...
  Apéry's Proof of the Irrationality of ζ(3)", Math. Intelligencer 1
  (1979), pp. 195–203, Section 8. Archived at
  `projects/Bounded/ref/vdPoorten-Apery-1979.pdf`.

  ## Plan

  1. `apery_P n k := C(n,k)² · C(n+k,k)²` — the summand.
  2. `apery_B n k := 4(2n+1)·(k(2k+1) − (2n+1)²) · apery_P n k` — the
     creative-telescoping witness.
  3. `apery_telescoping`: for 1 ≤ k ≤ n,
     `B(n,k) − B(n,k−1) = (n+1)³ P(n+1,k) − (34n³+51n²+27n+5) P(n,k)
                                          + n³ P(n−1,k)`.
     This is a pure polynomial identity in (n,k) after clearing
     factorials. Closable by `ring` on an equivalent form with common
     denominators.
  4. The F1 recurrence follows by summing over k and noting both
     boundary terms vanish.

  This file sets up (1) and (2); (3) is the main technical lemma
  (currently `sorry`), and it is consumed by `AperySequences.lean`'s
  `aperyA_recurrence`.
-/

import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

namespace Ripple
namespace Number

/-- The summand `P(n,k) := C(n,k)² · C(n+k,k)²`, cast to ℤ. -/
def apery_P (n k : ℕ) : ℤ :=
  (Nat.choose n k : ℤ) ^ 2 * (Nat.choose (n + k) k : ℤ) ^ 2

/-- Van der Poorten's creative-telescoping witness
    `B(n,k) := 4·(2n+1)·(k·(2k+1) − (2n+1)²) · P(n,k)`. -/
def apery_B (n k : ℕ) : ℤ :=
  4 * (2 * (n : ℤ) + 1) * ((k : ℤ) * (2 * k + 1) - (2 * n + 1) ^ 2) * apery_P n k

@[simp]
lemma apery_P_zero_k (k : ℕ) (hk : 1 ≤ k) : apery_P 0 k = 0 := by
  unfold apery_P
  have : Nat.choose 0 k = 0 := Nat.choose_eq_zero_of_lt hk
  simp [this]

@[simp]
lemma apery_P_n_zero (n : ℕ) : apery_P n 0 = 1 := by
  unfold apery_P; simp

@[simp]
lemma apery_P_k_gt (n k : ℕ) (h : n < k) : apery_P n k = 0 := by
  unfold apery_P
  have : Nat.choose n k = 0 := Nat.choose_eq_zero_of_lt h
  simp [this]

/-- **Creative-telescoping identity (vdPo 1979 §8, page 201).**

    For `1 ≤ k ≤ n`:
    `B(n,k) − B(n,k−1) = (n+1)³ · P(n+1,k)
                         − (34n³+51n²+27n+5) · P(n,k)
                         + n³ · P(n−1,k)`.

    Proof outline: express each `P(·,k)` as a rational multiple of
    `P(n,k)` via the standard binomial ratios
      `C(n+1,k) = C(n,k) · (n+1)/(n+1−k)`,
      `C(n−1,k) = C(n,k) · (n−k)/n`,
      `C(n+k+1,k) = C(n+k,k) · (n+k+1)/(n+1)`,
      `C(n+k−1,k) = C(n+k,k) · (n+1−k) · (n+1) / ((n+k)(n+1))`  (wait, simpler: via `k-1`),
    and similarly for `P(n,k−1)`. After multiplying by the common
    denominator `(n+1−k)²·(n+k)²·(n−k+1)²`, both sides reduce to
    polynomial equality in `(n,k)` closable by `ring`.

    Transcribing this in Lean requires an auxiliary factorial
    identity for each binomial ratio. -/
/-- Master polynomial identity: after clearing denominators (multiplying by
`(n+1-k)²·(n+k)²`), the creative-telescoping identity reduces to a pure
polynomial identity in ℤ[N,K], closable by `ring`. -/
private lemma master_poly_identity (N K : ℤ) :
    4 * (2 * N + 1) * (K * (2 * K + 1) - (2 * N + 1) ^ 2) * (N + 1 - K) ^ 2 * (N + K) ^ 2
      - 4 * (2 * N + 1) * ((K - 1) * (2 * K - 1) - (2 * N + 1) ^ 2) * K ^ 4
    = (N + 1) ^ 3 * (N + K) ^ 2 * (N + 1 + K) ^ 2
      - (34 * N ^ 3 + 51 * N ^ 2 + 27 * N + 5) * (N + 1 - K) ^ 2 * (N + K) ^ 2
      + N ^ 3 * (N + 1 - K) ^ 2 * (N - K) ^ 2 := by
  ring

/-- Ratio lemma: `(n+1-k)² · P(n+1,k) = (n+1+k)² · P(n,k)`.
Holds whenever `k ≤ n+1`. -/
private lemma R_succ_n (n k : ℕ) (hk : k ≤ n + 1) :
    ((n + 1 : ℤ) - k) ^ 2 * apery_P (n + 1) k
      = ((n : ℤ) + 1 + k) ^ 2 * apery_P n k := by
  -- From `Nat.choose_mul_succ_eq n k`: C(n,k)·(n+1) = C(n+1,k)·(n+1-k).
  -- From `Nat.choose_mul_succ_eq (n+k) k`: C(n+k,k)·(n+k+1) = C(n+k+1,k)·(n+k+1-k) = C(n+k+1,k)·(n+1).
  have h1 : (Nat.choose n k : ℤ) * (n + 1) = (Nat.choose (n + 1) k : ℤ) * ((n + 1 : ℤ) - k) := by
    have h := Nat.choose_mul_succ_eq n k
    have hcast : ((Nat.choose n k * (n + 1) : ℕ) : ℤ) =
        ((Nat.choose (n + 1) k * (n + 1 - k) : ℕ) : ℤ) := by exact_mod_cast h
    have hsub : ((n + 1 - k : ℕ) : ℤ) = (n + 1 : ℤ) - k := by
      exact_mod_cast Int.natCast_sub hk
    push_cast at hcast
    rw [hsub] at *
    linarith
  have h2 : (Nat.choose (n + k) k : ℤ) * (n + k + 1)
      = (Nat.choose (n + k + 1) k : ℤ) * (n + 1) := by
    have h := Nat.choose_mul_succ_eq (n + k) k
    -- h : C(n+k, k)*(n+k+1) = C(n+k+1, k)*(n+k+1-k)
    have hsub : ((n + k + 1 - k : ℕ) : ℤ) = (n + 1 : ℤ) := by
      have : n + k + 1 - k = n + 1 := by omega
      exact_mod_cast this
    have hcast : ((Nat.choose (n + k) k * (n + k + 1) : ℕ) : ℤ) =
        ((Nat.choose (n + k + 1) k * (n + k + 1 - k) : ℕ) : ℤ) := by exact_mod_cast h
    push_cast at hcast
    rw [hsub] at hcast
    linarith
  -- apery_P (n+1) k = C(n+1,k)² · C(n+1+k, k)²
  -- multiply by (n+1-k)² · (n+1)² and use the ratios
  unfold apery_P
  -- Rename (n+1)+k as n+1+k; Nat level n+1+k = n+k+1
  have hnk : (n + 1 + k : ℕ) = n + k + 1 := by omega
  rw [hnk]
  -- Goal: ((n+1:ℤ)-k)^2 * (C(n+1,k):ℤ)^2 * (C(n+k+1,k):ℤ)^2
  --     = ((n:ℤ)+1+k)^2 * (C(n,k):ℤ)^2 * (C(n+k,k):ℤ)^2
  -- Square h1 and h2 and combine.
  have h1sq : ((Nat.choose n k : ℤ) * (n + 1)) ^ 2
      = ((Nat.choose (n + 1) k : ℤ) * ((n + 1 : ℤ) - k)) ^ 2 := by rw [h1]
  have h2sq : ((Nat.choose (n + k) k : ℤ) * (n + k + 1)) ^ 2
      = ((Nat.choose (n + k + 1) k : ℤ) * (n + 1)) ^ 2 := by rw [h2]
  -- We want:  ((n+1)-k)^2 * C(n+1,k)^2 * C(n+k+1,k)^2
  --        = ((n+1)+k)^2 * C(n,k)^2 * C(n+k,k)^2
  -- From h1sq: C(n+1,k)^2 * ((n+1)-k)^2 = C(n,k)^2 * (n+1)^2
  -- From h2sq: C(n+k,k)^2 * (n+k+1)^2 = C(n+k+1,k)^2 * (n+1)^2
  -- So: C(n+1,k)^2 * ((n+1)-k)^2 * C(n+k+1,k)^2 * (n+1)^2
  --   = C(n,k)^2 * (n+1)^2 * C(n+k,k)^2 * (n+k+1)^2
  -- i.e. ((n+1)-k)^2 * C(n+1,k)^2 * C(n+k+1,k)^2 * (n+1)^2
  --    = (n+k+1)^2 * C(n,k)^2 * C(n+k,k)^2 * (n+1)^2
  -- Cancel (n+1)^2 if nonzero. But n+1 ≥ 1 > 0, so (n+1 : ℤ) ≠ 0.
  have hn1 : ((n : ℤ) + 1) ≠ 0 := by positivity
  have hn1sq : ((n : ℤ) + 1) ^ 2 ≠ 0 := pow_ne_zero 2 hn1
  have hcomb :
      ((n + 1 : ℤ) - k) ^ 2 * (Nat.choose (n + 1) k : ℤ) ^ 2
          * (Nat.choose (n + k + 1) k : ℤ) ^ 2 * ((n : ℤ) + 1) ^ 2
      = ((n : ℤ) + k + 1) ^ 2 * (Nat.choose n k : ℤ) ^ 2
          * (Nat.choose (n + k) k : ℤ) ^ 2 * ((n : ℤ) + 1) ^ 2 := by
    have e1 : (Nat.choose (n + 1) k : ℤ) ^ 2 * ((n + 1 : ℤ) - k) ^ 2
        = (Nat.choose n k : ℤ) ^ 2 * ((n : ℤ) + 1) ^ 2 := by
      have := h1sq; ring_nf; ring_nf at this; linarith
    have e2 : (Nat.choose (n + k) k : ℤ) ^ 2 * ((n : ℤ) + k + 1) ^ 2
        = (Nat.choose (n + k + 1) k : ℤ) ^ 2 * ((n : ℤ) + 1) ^ 2 := by
      have := h2sq
      have heq : ((n : ℤ) + k + 1) = (↑(n + k + 1) : ℤ) := by push_cast; ring
      ring_nf
      ring_nf at this
      -- align casts
      have h2' : ((Nat.choose (n + k) k : ℤ)) ^ 2 * ((n : ℤ) + k + 1) ^ 2
          = ((Nat.choose (n + k + 1) k : ℤ)) ^ 2 * ((n : ℤ) + 1) ^ 2 := by
        have := h2sq
        push_cast at this
        nlinarith [this]
      nlinarith [h2']
    nlinarith [e1, e2]
  have := mul_right_cancel₀ hn1sq hcomb
  nlinarith [this]

lemma apery_telescoping (n k : ℕ) (hk : 1 ≤ k) (hkn : k ≤ n) :
    apery_B n k - apery_B n (k - 1)
      = (n + 1 : ℤ) ^ 3 * apery_P (n + 1) k
        - (34 * (n : ℤ) ^ 3 + 51 * n ^ 2 + 27 * n + 5) * apery_P n k
        + (n : ℤ) ^ 3 * apery_P (n - 1) k := by
  sorry

end Number
end Ripple
