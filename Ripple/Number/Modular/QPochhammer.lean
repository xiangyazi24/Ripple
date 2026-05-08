import Mathlib.NumberTheory.ModularForms.DedekindEta
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Elementary q-Pochhammer product bookkeeping

This file contains only finite and definitional product identities.  It is the
algebraic product layer needed before the Jacobi triple-product and singular
modulus evaluations can be connected to Mathlib's Dedekind eta product.
-/

noncomputable section

namespace Ripple
namespace Number
namespace Modular

open Complex
open scoped BigOperators

/-- Finite q-Pochhammer product `(q; q)_N = ∏_{n=1}^N (1 - q^n)`. -/
noncomputable def qPochhammer (q : ℂ) (N : ℕ) : ℂ :=
  ∏ n ∈ Finset.range N, (1 - q ^ (n + 1))

/-- Infinite q-Pochhammer product `(q; q)_∞ = ∏_{n≥1} (1 - q^n)`. -/
noncomputable def qPochhammerInf (q : ℂ) : ℂ :=
  ∏' n : ℕ, (1 - q ^ (n + 1))

lemma qPochhammer_zero (q : ℂ) :
    qPochhammer q 0 = 1 := by
  simp [qPochhammer]

lemma qPochhammer_succ (q : ℂ) (N : ℕ) :
    qPochhammer q (N + 1) =
      qPochhammer q N * (1 - q ^ (N + 1)) := by
  simp [qPochhammer, Finset.prod_range_succ, mul_comm]

lemma qPochhammer_sq_split (q : ℂ) (N : ℕ) :
    qPochhammer (q ^ 2) N =
      qPochhammer q N * ∏ n ∈ Finset.range N, (1 + q ^ (n + 1)) := by
  unfold qPochhammer
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl ?_
  intro n hn
  rw [show (q ^ 2) ^ (n + 1) = (q ^ (n + 1)) ^ 2 by ring]
  ring

lemma qPochhammer_one_add_eq_div (q : ℂ) (N : ℕ)
    (h : qPochhammer q N ≠ 0) :
    (∏ n ∈ Finset.range N, (1 + q ^ (n + 1))) =
      qPochhammer (q ^ 2) N / qPochhammer q N := by
  rw [qPochhammer_sq_split]
  field_simp [h]

lemma qPochhammer_even_odd_split (q : ℂ) (N : ℕ) :
    qPochhammer q (2 * N) =
      qPochhammer (q ^ 2) N *
        ∏ n ∈ Finset.range N, (1 - q ^ (2 * n + 1)) := by
  induction N with
  | zero =>
      simp [qPochhammer]
  | succ N ih =>
      rw [show 2 * (N + 1) = 2 * N + 1 + 1 by omega]
      rw [qPochhammer_succ, qPochhammer_succ]
      rw [show 2 * N + 1 = 2 * N + 1 by rfl]
      rw [ih, qPochhammer_succ, Finset.prod_range_succ]
      rw [show (q ^ 2) ^ (N + 1) = q ^ (2 * N + 2) by
        simpa [Nat.mul_add, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
          (pow_mul q 2 (N + 1)).symm]
      ring

lemma qPochhammer_odd_part_eq_div (q : ℂ) (N : ℕ)
    (h : qPochhammer (q ^ 2) N ≠ 0) :
    (∏ n ∈ Finset.range N, (1 - q ^ (2 * n + 1))) =
      qPochhammer q (2 * N) / qPochhammer (q ^ 2) N := by
  rw [qPochhammer_even_odd_split]
  field_simp [h]

/-- Infinite product version of `(1 - x^2) = (1 - x)(1 + x)`.

The hypotheses are only the multipliability bookkeeping needed to multiply
the two infinite products. -/
lemma qPochhammerInf_sq_split_of_multipliable (q : ℂ)
    (hminus : Multipliable fun n : ℕ => 1 - q ^ (n + 1))
    (hplus : Multipliable fun n : ℕ => 1 + q ^ (n + 1)) :
    qPochhammerInf (q ^ 2) =
      qPochhammerInf q * ∏' n : ℕ, (1 + q ^ (n + 1)) := by
  rw [qPochhammerInf, qPochhammerInf]
  rw [← hminus.tprod_mul hplus]
  apply tprod_congr
  intro n
  rw [show (q ^ 2) ^ (n + 1) = (q ^ (n + 1)) ^ 2 by ring]
  ring

/-- Infinite product version of splitting `(q;q)_∞` into its odd and even
exponents. -/
lemma qPochhammerInf_even_odd_split_of_multipliable (q : ℂ)
    (hodd : Multipliable fun n : ℕ => 1 - q ^ (2 * n + 1))
    (heven : Multipliable fun n : ℕ => 1 - q ^ (2 * n + 1 + 1)) :
    qPochhammerInf q =
      (∏' n : ℕ, (1 - q ^ (2 * n + 1))) *
        qPochhammerInf (q ^ 2) := by
  have hsplit :
      (∏' n : ℕ, (1 - q ^ (2 * n + 1))) *
          (∏' n : ℕ, (1 - q ^ (2 * n + 1 + 1))) =
        ∏' n : ℕ, (1 - q ^ (n + 1)) :=
    tprod_even_mul_odd (f := fun n : ℕ => 1 - q ^ (n + 1)) hodd heven
  rw [qPochhammerInf]
  rw [← hsplit]
  rw [qPochhammerInf]
  congr 1
  apply tprod_congr
  intro n
  rw [show (q ^ 2) ^ (n + 1) = q ^ (2 * n + 2) by
    simpa [Nat.mul_add, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      (pow_mul q 2 (n + 1)).symm]

/-- The infinite-product cancellation used in
`θ₂ θ₃ θ₄ = 2 η^3`: the even `1 + q^n` factors cancel the odd part after
splitting `(q;q)_∞`. -/
lemma qPochhammerInf_plus_mul_odd_eq_one_of_multipliable (q : ℂ)
    (hminus : Multipliable fun n : ℕ => 1 - q ^ (n + 1))
    (hplus : Multipliable fun n : ℕ => 1 + q ^ (n + 1))
    (hodd : Multipliable fun n : ℕ => 1 - q ^ (2 * n + 1))
    (heven : Multipliable fun n : ℕ => 1 - q ^ (2 * n + 1 + 1))
    (hP : qPochhammerInf q ≠ 0) :
    (∏' n : ℕ, (1 + q ^ (n + 1))) *
        (∏' n : ℕ, (1 - q ^ (2 * n + 1))) = 1 := by
  have hs :=
    qPochhammerInf_sq_split_of_multipliable q hminus hplus
  have he :=
    qPochhammerInf_even_odd_split_of_multipliable q hodd heven
  rw [hs] at he
  have hcancel :
      qPochhammerInf q =
        qPochhammerInf q *
          ((∏' n : ℕ, (1 + q ^ (n + 1))) *
            (∏' n : ℕ, (1 - q ^ (2 * n + 1)))) := by
    calc
      qPochhammerInf q =
          (∏' n : ℕ, (1 - q ^ (2 * n + 1))) *
            (qPochhammerInf q * ∏' n : ℕ, (1 + q ^ (n + 1))) := he
      _ = qPochhammerInf q *
          ((∏' n : ℕ, (1 + q ^ (n + 1))) *
            (∏' n : ℕ, (1 - q ^ (2 * n + 1)))) := by ring
  have h1 : qPochhammerInf q * 1 =
      qPochhammerInf q *
        ((∏' n : ℕ, (1 + q ^ (n + 1))) *
          (∏' n : ℕ, (1 - q ^ (2 * n + 1)))) := by
    rw [mul_one]; exact hcancel
  exact (mul_left_cancel₀ hP h1).symm

lemma qPochhammerInf_eq_eta_tprod (z : ℂ) :
    qPochhammerInf (Complex.exp (2 * Real.pi * Complex.I * z)) =
      ∏' n : ℕ, (1 - ModularForm.eta_q n z) := by
  unfold qPochhammerInf
  apply tprod_congr
  intro n
  rw [ModularForm.eta_q_eq_pow]

end Modular
end Number
end Ripple
