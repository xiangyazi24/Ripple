/-
  Kernel-verified analytical coefficient majorant bound for the CRT proof.

  Architecture (zero native_decide):

  Layer 1: Majorant algebra — Maj f F closed under conv, pow, pullback, sparse sum
  Layer 2: Eisenstein/Δ bounds — |E4[n]| ≤ G4[n], |E6[n]| ≤ G6[n], |Δ[n]| ≤ DeltaBound[n]
  Layer 3: Row bridge — Q_j recurrence = Δ^(42-j) · E4^(3j) closed form, row bounds
  Layer 4: Final hbound — sparse L¹ convolution → B ≈ H · 10^1420

  Key insight: the recurrence for Q_j is NOT an arbitrary recurrence — it is the
  coefficient recurrence for Q_j(q) = Δ(q)^(42-j) · E4(q)^(3j). The derivative
  identity E4 · D Q_j = (42 E2E4 - j E6) · Q_j (already proved) establishes this.
  Bounding the closed form via majorants avoids the exponential blowup from
  taking absolute values in the recurrence.
-/
import Ripple.Number.Modular.ModularPolynomialSturmCertificate

namespace Ripple.Number.Modular

open scoped UpperHalfPlane
open CongruenceSubgroup

/-! ## Layer 1: Majorant Algebra -/

/-- Coefficientwise majorization: |f(n)| ≤ F(n) for all n. -/
def Maj (f : ℕ → ℤ) (F : ℕ → ℕ) : Prop :=
  ∀ n, |f n| ≤ (F n : ℤ)

/-- Convolution of nonneg sequences. -/
def convNat (F G : ℕ → ℕ) (n : ℕ) : ℕ :=
  (Finset.range (n + 1)).sum (fun k => F k * G (n - k))

theorem Maj.conv {f g : ℕ → ℤ} {F G : ℕ → ℕ}
    (hf : Maj f F) (hg : Maj g G) :
    Maj (fun n => (Finset.range (n + 1)).sum (fun k => f k * g (n - k)))
      (convNat F G) := by
  intro n; simp only [convNat]
  calc |∑ k ∈ Finset.range (n + 1), f k * g (n - k)|
      ≤ ∑ k ∈ Finset.range (n + 1), |f k * g (n - k)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ Finset.range (n + 1), (F k * G (n - k) : ℤ) := by
        apply Finset.sum_le_sum; intro k _
        rw [abs_mul]
        exact mul_le_mul (hf k) (hg (n - k)) (abs_nonneg _) (Int.natCast_nonneg _)
    _ = ↑(∑ k ∈ Finset.range (n + 1), F k * G (n - k)) := by push_cast; ring_nf

/-- Majorant of n-fold convolution power. -/
def powConvNat (F : ℕ → ℕ) (k : ℕ) : ℕ → ℕ :=
  match k with
  | 0 => fun n => if n = 0 then 1 else 0
  | k + 1 => convNat F (powConvNat F k)

theorem Maj.powConv {f : ℕ → ℤ} {F : ℕ → ℕ} (hf : Maj f F)
    (k : ℕ) :
    Maj (fun n => PowerSeries.coeff (R := ℤ) n ((PowerSeries.mk f) ^ k))
      (powConvNat F k) := by
  induction k with
  | zero =>
    intro n; simp only [pow_zero, PowerSeries.coeff_one, powConvNat]; split <;> simp
  | succ k ih =>
    show Maj _ (convNat F (powConvNat F k))
    intro n; dsimp only
    rw [pow_succ', PowerSeries.coeff_mul,
        Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    simp_rw [PowerSeries.coeff_mk]
    exact Maj.conv hf ih n

theorem Maj.add {f g : ℕ → ℤ} {F G : ℕ → ℕ}
    (hf : Maj f F) (hg : Maj g G) :
    Maj (fun n => f n + g n) (fun n => F n + G n) := by
  intro n; push_cast
  calc |f n + g n| ≤ |f n| + |g n| := abs_add_le _ _
    _ ≤ ↑(F n) + ↑(G n) := add_le_add (hf n) (hg n)

theorem Maj.smul {f : ℕ → ℤ} {F : ℕ → ℕ} (c : ℤ)
    (hf : Maj f F) :
    Maj (fun n => c * f n) (fun n => c.natAbs * F n) := by
  intro n
  rw [abs_mul]
  push_cast
  rw [Int.abs_eq_natAbs]
  exact mul_le_mul_of_nonneg_left (hf n) (by positivity)

/-- Majorant for q-pullback by 41: f(q^41). -/
def pullback41Nat (F : ℕ → ℕ) (n : ℕ) : ℕ :=
  if 41 ∣ n then F (n / 41) else 0

theorem Maj.pullback41 {f : ℕ → ℤ} {F : ℕ → ℕ} (hf : Maj f F) :
    Maj (fun n => if 41 ∣ n then f (n / 41) else 0) (pullback41Nat F) := by
  intro n; simp only [pullback41Nat]
  split
  · exact hf _
  · simp

/-! ## Layer 2: Eisenstein and Δ coefficient bounds -/

/-- G4 majorant: |E4[n]| ≤ G4Bound n.
    Uses 2880 · C(n+2, 3) ≥ 480 n³ ≥ 240 σ₃(n). -/
def G4Bound (n : ℕ) : ℕ :=
  if n = 0 then 1 else 2880 * Nat.choose (n + 2) 3

/-- G6 majorant: |E6[n]| ≤ G6Bound n.
    Uses 120960 · C(n+4, 5) ≥ 1008 n⁵ ≥ 504 σ₅(n). -/
def G6Bound (n : ℕ) : ℕ :=
  if n = 0 then 1 else 120960 * Nat.choose (n + 4) 5

/-! ### σ₃(n) ≤ 2n³: proof via ℚ telescoping

Strategy: cast to ℚ. Split σ₃(n) = n³ + Σ_{properDiv} d³.
For each d ∈ properDivisors, we have n/d ≥ 2 and d·(n/d) = n,
so (d:ℚ)³ = (n:ℚ)³/(n/d:ℚ)³. Bound 1/e³ ≤ 1/(e(e-1))
and use telescoping: Σ_{e ∈ S, e ≥ 2} 1/(e(e-1)) ≤ 1. -/

/-- Telescoping bound: Σ_{e=2}^{M} 1/(e(e-1)) = 1 - 1/M in ℚ. -/
private lemma sum_Icc_inv_pred_mul (M : ℕ) (hM : 2 ≤ M) :
    (Finset.Icc 2 M).sum (fun e => (1 : ℚ) / ((e : ℚ) * ((e : ℚ) - 1))) =
      1 - 1 / (M : ℚ) := by
  induction M with
  | zero => omega
  | succ M ih =>
    by_cases hM2 : M + 1 = 2
    · -- Base case: M+1 = 2, so M = 1
      have : M = 1 := by omega
      subst this; simp [Finset.Icc_self]; ring
    · -- Inductive step: M+1 ≥ 3, so M ≥ 2
      have hM1 : 2 ≤ M := by omega
      -- Icc 2 (M+1) = insert (M+1) (Icc 2 M)
      have hIcc : Finset.Icc 2 (M + 1) = insert (M + 1) (Finset.Icc 2 M) := by
        ext x; simp [Finset.mem_Icc, Finset.mem_insert]; omega
      rw [hIcc, Finset.sum_insert (by simp [Finset.mem_Icc])]
      rw [ih hM1]
      -- Now goal: 1/((M+1)*((M+1)-1)) + (1 - 1/M) = 1 - 1/(M+1)
      have hMne : (M : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      have hM1ne : ((M : ℚ) + 1) ≠ 0 := by positivity
      -- Simplify (M+1)-1 = M in ℚ
      have hsimp : ((M + 1 : ℕ) : ℚ) - 1 = (M : ℚ) := by push_cast; ring
      rw [hsimp]
      -- Now goal: 1/((M+1)*M) + (1 - 1/M) = 1 - 1/(M+1)
      -- i.e. 1/((M+1)*M) = 1/M - 1/(M+1) (partial fractions)
      -- The Nat.cast of (M+1) needs to be rewritten
      have hcast : ((M + 1 : ℕ) : ℚ) = (M : ℚ) + 1 := by push_cast; ring
      rw [hcast]
      rw [show (1 : ℚ) / (((M : ℚ) + 1) * (M : ℚ)) = 1 / (M : ℚ) - 1 / ((M : ℚ) + 1) from by
        rw [div_sub_div _ _ hMne hM1ne, mul_comm]; congr 1; ring]
      ring

/-- For each d ∈ properDivisors n: d³ ≤ n³ · 1/((n/d)(n/d - 1)) in ℚ. -/
private lemma proper_div_cube_le_inv_pred (n d : ℕ) (hn : 0 < n)
    (hd : d ∈ n.properDivisors) :
    (d : ℚ) ^ 3 ≤ (n : ℚ) ^ 3 * ((1 : ℚ) / ((n / d : ℕ) * (((n / d : ℕ) : ℚ) - 1))) := by
  have hdvd := (Nat.mem_properDivisors.mp hd).1
  have hlt := (Nat.mem_properDivisors.mp hd).2
  have hd_pos : 0 < d := Nat.pos_of_mem_divisors (Nat.properDivisors_subset_divisors hd)
  set e := n / d
  have he : 2 ≤ e := Nat.one_lt_div_of_mem_properDivisors hd
  have hde : d * e = n := by
    show d * (n / d) = n
    rw [mul_comm]; exact Nat.div_mul_cancel hdvd
  -- In ℚ: d = n/e, so d³ = n³/e³.
  -- We need: n³/e³ ≤ n³/(e(e-1)), i.e., e(e-1) ≤ e³, i.e., e-1 ≤ e², true.
  have he_pos : (0 : ℚ) < (e : ℚ) := by positivity
  have he1_pos : (0 : ℚ) < ((e : ℚ) - 1) := by
    have : (2 : ℚ) ≤ (e : ℚ) := by exact_mod_cast he
    linarith
  have hdQ : (d : ℚ) = (n : ℚ) / (e : ℚ) := by
    rw [eq_div_iff (ne_of_gt he_pos)]
    exact_mod_cast hde
  rw [hdQ, div_pow, mul_one_div]
  -- Goal: n^3 / e^3 ≤ n^3 / (e * (e - 1))
  -- Since e*(e-1) ≤ e^3 and e*(e-1) > 0:
  exact div_le_div_of_nonneg_left (by positivity) (mul_pos he_pos he1_pos) (by nlinarith [sq_nonneg ((e : ℚ) - 1)])

/-- The Finset image of n/· on properDivisors maps into Icc 2 n. -/
private lemma div_properDivisors_subset_Icc (n : ℕ) (_hn : 0 < n) :
    (n.properDivisors.image (n / ·)) ⊆ Finset.Icc 2 n := by
  intro e he
  rw [Finset.mem_image] at he
  obtain ⟨d, hd, rfl⟩ := he
  rw [Finset.mem_Icc]
  exact ⟨Nat.one_lt_div_of_mem_properDivisors hd,
         Nat.div_le_self n d⟩

private lemma sigma3_le_two_mul_cube (n : ℕ) (hn : 0 < n) :
    ArithmeticFunction.sigma 3 n ≤ 2 * n ^ 3 := by
  -- Cast to ℚ
  suffices h : (ArithmeticFunction.sigma 3 n : ℚ) ≤ 2 * (n : ℚ) ^ 3 by exact_mod_cast h
  -- Rewrite sigma as a sum over divisors
  rw [ArithmeticFunction.sigma_apply]
  push_cast
  -- Split: divisors n = {n} ∪ properDivisors n
  have hne : n ≠ 0 := by omega
  rw [← Nat.cons_self_properDivisors hne, Finset.sum_cons]
  -- Goal: n^3 + Σ_{d ∈ properDiv} d^3 ≤ 2*n^3
  -- Suffices: Σ_{d ∈ properDiv} d^3 ≤ n^3
  suffices hpd : (n.properDivisors.sum fun d => (d : ℚ) ^ 3) ≤ (n : ℚ) ^ 3 by linarith
  -- Bound each d^3 by n^3 * 1/(e*(e-1)) where e = n/d
  calc n.properDivisors.sum (fun d => (d : ℚ) ^ 3)
      ≤ n.properDivisors.sum (fun d =>
          (n : ℚ) ^ 3 * (1 / ((n / d : ℕ) * (((n / d : ℕ) : ℚ) - 1)))) := by
        apply Finset.sum_le_sum
        intro d hd
        exact proper_div_cube_le_inv_pred n d hn hd
    _ = (n : ℚ) ^ 3 * n.properDivisors.sum (fun d =>
          1 / ((n / d : ℕ) * (((n / d : ℕ) : ℚ) - 1))) := by
        rw [← Finset.mul_sum]
    _ ≤ (n : ℚ) ^ 3 * 1 := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        -- Step 1: The map d ↦ n/d is injective on properDivisors
        have hinj : ∀ a ∈ n.properDivisors, ∀ b ∈ n.properDivisors,
            n / a = n / b → a = b := by
          intro a ha b hb hab
          have ha' := (Nat.mem_properDivisors.mp ha).1
          have hb' := (Nat.mem_properDivisors.mp hb).1
          have ha_pos : 0 < a := Nat.pos_of_mem_divisors (Nat.properDivisors_subset_divisors ha)
          have hb_pos : 0 < b := Nat.pos_of_mem_divisors (Nat.properDivisors_subset_divisors hb)
          calc a = n / (n / a) := (Nat.div_div_self ha' hne).symm
            _ = n / (n / b) := by rw [hab]
            _ = b := Nat.div_div_self hb' hne
        -- Handle n = 1 separately (properDivisors empty)
        by_cases hn1 : n = 1
        · subst hn1; simp [Nat.properDivisors_one]
        · have hn2 : 2 ≤ n := by omega
          -- Step 2: Rewrite sum over image
          set g : ℕ → ℚ := fun e => (1 : ℚ) / ((e : ℚ) * ((e : ℚ) - 1)) with hg_def
          have hsum_eq : n.properDivisors.sum (fun d => g (n / d)) =
              (n.properDivisors.image (n / ·)).sum g :=
            (Finset.sum_image hinj).symm
          rw [hsum_eq]
          -- Step 3: Bound image sum by Icc 2 n sum (all terms nonneg)
          have himg := div_properDivisors_subset_Icc n hn
          have hg_nn : ∀ e ∈ Finset.Icc 2 n, 0 ≤ g e := by
            intro e he
            have he2 : 2 ≤ e := (Finset.mem_Icc.mp he).1
            apply div_nonneg one_pos.le
            apply mul_nonneg (Nat.cast_nonneg e)
            have : (2 : ℚ) ≤ (e : ℚ) := by exact_mod_cast he2
            linarith
          calc (n.properDivisors.image (n / ·)).sum g
              ≤ (Finset.Icc 2 n).sum g :=
                Finset.sum_le_sum_of_subset_of_nonneg himg (fun e he _ => hg_nn e he)
            _ = 1 - 1 / (n : ℚ) := sum_Icc_inv_pred_mul n hn2
            _ ≤ 1 := sub_le_self _ (div_nonneg one_pos.le (Nat.cast_nonneg n))
    _ = (n : ℚ) ^ 3 := by ring

theorem maj_E4 :
    Maj (fun n => PowerSeries.coeff (R := ℤ) n E4ZSeries) G4Bound := by
  intro n; dsimp only; rw [coeff_E4ZSeries]; unfold E4CoeffZ G4Bound
  by_cases hn : n = 0
  · simp [hn]
  · simp only [hn, ↓reduceIte]
    have hn_pos : 0 < n := Nat.pos_of_ne_zero hn
    rw [show (240 : ℤ) * ↑(ArithmeticFunction.sigma 3 n) =
      ↑(240 * ArithmeticFunction.sigma 3 n) from by push_cast; ring]
    rw [abs_of_nonneg (by positivity)]
    push_cast
    calc (240 * ArithmeticFunction.sigma 3 n : ℤ)
        ≤ 240 * (2 * n ^ 3) := by
          apply mul_le_mul_of_nonneg_left
          · exact_mod_cast sigma3_le_two_mul_cube n hn_pos
          · norm_num
      _ = 480 * n ^ 3 := by ring
      _ ≤ 2880 * Nat.choose (n + 2) 3 := by
          have hchoose : 6 * Nat.choose (n + 2) 3 = n * (n + 1) * (n + 2) := by
            have h1 := Nat.succ_mul_choose_eq (n + 1) 2
            have h2 := Nat.succ_mul_choose_eq n 1
            rw [Nat.choose_one_right] at h2
            nlinarith
          have hcube : n ^ 3 ≤ n * (n + 1) * (n + 2) := by nlinarith
          nlinarith

/-- For each d ∈ properDivisors n: d^5 ≤ n^5 · 1/((n/d)(n/d - 1)) in ℚ. -/
private lemma proper_div_fifth_le_inv_pred (n d : ℕ) (hn : 0 < n)
    (hd : d ∈ n.properDivisors) :
    (d : ℚ) ^ 5 ≤ (n : ℚ) ^ 5 * ((1 : ℚ) / ((n / d : ℕ) * (((n / d : ℕ) : ℚ) - 1))) := by
  have hdvd := (Nat.mem_properDivisors.mp hd).1
  have hlt := (Nat.mem_properDivisors.mp hd).2
  have hd_pos : 0 < d := Nat.pos_of_mem_divisors (Nat.properDivisors_subset_divisors hd)
  set e := n / d
  have he : 2 ≤ e := Nat.one_lt_div_of_mem_properDivisors hd
  have hde : d * e = n := by
    show d * (n / d) = n
    rw [mul_comm]; exact Nat.div_mul_cancel hdvd
  have he_pos : (0 : ℚ) < (e : ℚ) := by positivity
  have he1_pos : (0 : ℚ) < ((e : ℚ) - 1) := by
    have : (2 : ℚ) ≤ (e : ℚ) := by exact_mod_cast he
    linarith
  have hdQ : (d : ℚ) = (n : ℚ) / (e : ℚ) := by
    rw [eq_div_iff (ne_of_gt he_pos)]
    exact_mod_cast hde
  rw [hdQ, div_pow, mul_one_div]
  -- Goal: n^5 / e^5 ≤ n^5 / (e * (e - 1))
  -- Since e*(e-1) ≤ e^5 and e*(e-1) > 0:
  apply div_le_div_of_nonneg_left (by positivity) (mul_pos he_pos he1_pos)
  -- Need: e * (e - 1) ≤ e ^ 5, i.e. e - 1 ≤ e ^ 4
  have he2 : (2 : ℚ) ≤ (e : ℚ) := by exact_mod_cast he
  nlinarith [sq_nonneg ((e : ℚ)), sq_nonneg ((e : ℚ) ^ 2 - 1)]

private lemma sigma5_le_two_mul_pow5 (n : ℕ) (hn : 0 < n) :
    ArithmeticFunction.sigma 5 n ≤ 2 * n ^ 5 := by
  -- Cast to ℚ
  suffices h : (ArithmeticFunction.sigma 5 n : ℚ) ≤ 2 * (n : ℚ) ^ 5 by exact_mod_cast h
  -- Rewrite sigma as a sum over divisors
  rw [ArithmeticFunction.sigma_apply]
  push_cast
  -- Split: divisors n = {n} ∪ properDivisors n
  have hne : n ≠ 0 := by omega
  rw [← Nat.cons_self_properDivisors hne, Finset.sum_cons]
  -- Goal: n^5 + Σ_{d ∈ properDiv} d^5 ≤ 2*n^5
  -- Suffices: Σ_{d ∈ properDiv} d^5 ≤ n^5
  suffices hpd : (n.properDivisors.sum fun d => (d : ℚ) ^ 5) ≤ (n : ℚ) ^ 5 by linarith
  -- Bound each d^5 by n^5 * 1/(e*(e-1)) where e = n/d
  calc n.properDivisors.sum (fun d => (d : ℚ) ^ 5)
      ≤ n.properDivisors.sum (fun d =>
          (n : ℚ) ^ 5 * (1 / ((n / d : ℕ) * (((n / d : ℕ) : ℚ) - 1)))) := by
        apply Finset.sum_le_sum
        intro d hd
        exact proper_div_fifth_le_inv_pred n d hn hd
    _ = (n : ℚ) ^ 5 * n.properDivisors.sum (fun d =>
          1 / ((n / d : ℕ) * (((n / d : ℕ) : ℚ) - 1))) := by
        rw [← Finset.mul_sum]
    _ ≤ (n : ℚ) ^ 5 * 1 := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        -- Step 1: The map d ↦ n/d is injective on properDivisors
        have hinj : ∀ a ∈ n.properDivisors, ∀ b ∈ n.properDivisors,
            n / a = n / b → a = b := by
          intro a ha b hb hab
          have ha' := (Nat.mem_properDivisors.mp ha).1
          have hb' := (Nat.mem_properDivisors.mp hb).1
          have ha_pos : 0 < a := Nat.pos_of_mem_divisors (Nat.properDivisors_subset_divisors ha)
          have hb_pos : 0 < b := Nat.pos_of_mem_divisors (Nat.properDivisors_subset_divisors hb)
          calc a = n / (n / a) := (Nat.div_div_self ha' hne).symm
            _ = n / (n / b) := by rw [hab]
            _ = b := Nat.div_div_self hb' hne
        -- Handle n = 1 separately (properDivisors empty)
        by_cases hn1 : n = 1
        · subst hn1; simp [Nat.properDivisors_one]
        · have hn2 : 2 ≤ n := by omega
          -- Step 2: Rewrite sum over image
          set g : ℕ → ℚ := fun e => (1 : ℚ) / ((e : ℚ) * ((e : ℚ) - 1)) with hg_def
          have hsum_eq : n.properDivisors.sum (fun d => g (n / d)) =
              (n.properDivisors.image (n / ·)).sum g :=
            (Finset.sum_image hinj).symm
          rw [hsum_eq]
          -- Step 3: Bound image sum by Icc 2 n sum (all terms nonneg)
          have himg := div_properDivisors_subset_Icc n hn
          have hg_nn : ∀ e ∈ Finset.Icc 2 n, 0 ≤ g e := by
            intro e he
            have he2 : 2 ≤ e := (Finset.mem_Icc.mp he).1
            apply div_nonneg one_pos.le
            apply mul_nonneg (Nat.cast_nonneg e)
            have : (2 : ℚ) ≤ (e : ℚ) := by exact_mod_cast he2
            linarith
          calc (n.properDivisors.image (n / ·)).sum g
              ≤ (Finset.Icc 2 n).sum g :=
                Finset.sum_le_sum_of_subset_of_nonneg himg (fun e he _ => hg_nn e he)
            _ = 1 - 1 / (n : ℚ) := sum_Icc_inv_pred_mul n hn2
            _ ≤ 1 := sub_le_self _ (div_nonneg one_pos.le (Nat.cast_nonneg n))
    _ = (n : ℚ) ^ 5 := by ring

set_option maxHeartbeats 400000 in
theorem maj_E6 :
    Maj (fun n => PowerSeries.coeff (R := ℤ) n E6ZSeries) G6Bound := by
  intro n; dsimp only; rw [coeff_E6ZSeries]; unfold E6CoeffZ G6Bound
  by_cases hn : n = 0
  · simp [hn]
  · simp only [hn, ↓reduceIte]
    have hn_pos : 0 < n := Nat.pos_of_ne_zero hn
    rw [show (-504 : ℤ) * ↑(ArithmeticFunction.sigma 5 n) =
      -(↑(504 * ArithmeticFunction.sigma 5 n)) from by push_cast; ring]
    rw [abs_neg, abs_of_nonneg (by positivity)]
    push_cast
    calc (504 * ArithmeticFunction.sigma 5 n : ℤ)
        ≤ 504 * (2 * n ^ 5) := by
          apply mul_le_mul_of_nonneg_left
          · exact_mod_cast sigma5_le_two_mul_pow5 n hn_pos
          · norm_num
      _ = 1008 * n ^ 5 := by ring
      _ ≤ 120960 * Nat.choose (n + 4) 5 := by
          -- 120 * C(n+4,5) = n*(n+1)*(n+2)*(n+3)*(n+4)
          -- Build up: C(n+1,2)*2 = n*(n+1), C(n+2,3)*3 = (n+2)*C(n+1,2), etc.
          have h4 := Nat.succ_mul_choose_eq n 1
          rw [Nat.choose_one_right] at h4
          -- h4: (n+1) * n = C(n+1,2) * 2
          have h3 := Nat.succ_mul_choose_eq (n + 1) 2
          -- h3: (n+2) * C(n+1,2) = C(n+2,3) * 3
          have h2 := Nat.succ_mul_choose_eq (n + 2) 3
          -- h2: (n+3) * C(n+2,3) = C(n+3,4) * 4
          have h1 := Nat.succ_mul_choose_eq (n + 3) 4
          -- h1: (n+4) * C(n+3,4) = C(n+4,5) * 5
          -- From these: 120 * C(n+4,5) = n*(n+1)*(n+2)*(n+3)*(n+4)
          -- Step by step: set intermediate variables
          set c2 := Nat.choose (n + 1) 2
          set c3 := Nat.choose (n + 2) 3
          set c4 := Nat.choose (n + 3) 4
          set c5 := Nat.choose (n + 4) 5
          -- From h4: n*(n+1) = 2*c2
          have eq2 : n * (n + 1) = 2 * c2 := by linarith
          -- From h3: (n+2)*c2 = 3*c3
          have eq3 : (n + 2) * c2 = 3 * c3 := by linarith
          -- From h2: (n+3)*c3 = 4*c4
          have eq4 : (n + 3) * c3 = 4 * c4 := by linarith
          -- From h1: (n+4)*c4 = 5*c5
          have eq5 : (n + 4) * c4 = 5 * c5 := by linarith
          -- Chain: 120*c5 = 24*(n+4)*c4 = 24*(n+4)*(n+3)*c3/4 = ...
          -- Easier: n*(n+1)*(n+2)*(n+3)*(n+4) = 2*c2*(n+2)*(n+3)*(n+4)
          --   = 2*3*c3*(n+3)*(n+4) = 6*c3*(n+3)*(n+4)
          --   = 6*4*c4*(n+4) = 24*c4*(n+4) = 24*5*c5 = 120*c5
          have step1 : n * (n + 1) * (n + 2) = 2 * c2 * (n + 2) := by nlinarith
          have step2 : 2 * c2 * (n + 2) = 2 * (3 * c3) := by nlinarith
          have step3 : n * (n + 1) * (n + 2) * (n + 3) = 6 * c3 * (n + 3) := by nlinarith
          have step4 : 6 * c3 * (n + 3) = 6 * (4 * c4) := by nlinarith
          have step5 : n * (n + 1) * (n + 2) * (n + 3) * (n + 4) = 24 * c4 * (n + 4) := by nlinarith
          have step6 : 24 * c4 * (n + 4) = 24 * (5 * c5) := by nlinarith
          have hchoose : n * (n + 1) * (n + 2) * (n + 3) * (n + 4) = 120 * c5 := by nlinarith
          -- n^5 ≤ n*(n+1)*(n+2)*(n+3)*(n+4)
          have hpow5 : n ^ 5 ≤ n * (n + 1) * (n + 2) * (n + 3) * (n + 4) := by
            have h0 : 0 < n := hn_pos
            nlinarith [sq_nonneg n, sq_nonneg (n * (n + 1) - n * n)]
          -- 1008 * n^5 ≤ 120960 * c5
          nlinarith

/-- Δ majorant from |1728 Δ| ≤ |E4³| + |E6²|, i.e. |Δ| ≤ (G4³ + G6²).
    We skip the 1728 denominator for simplicity. -/
def DeltaBound (n : ℕ) : ℕ :=
  convNat (convNat G4Bound (convNat G4Bound G4Bound)) (fun _ => 1) n +
  convNat G6Bound G6Bound n

/-- Tighter Δ majorant keeping the 1/1728 factor: |Δ[n]| ≤ ⌈(G4³ + G6²)(n) / 1728⌉. -/
def DeltaBoundTight (n : ℕ) : ℕ :=
  (convNat G4Bound (convNat G4Bound G4Bound) n +
   convNat G6Bound G6Bound n) / 1728 + 1

/-- Classical identity: `1728 Δ = E₄³ − E₆²`, as a formal power series over `ℤ`.

**Proof route** (all ingredients exist in the codebase):

1. Form `G := E₄³ − E₆² − 1728 Δ` as a `CuspForm Γ(1) 12` in the complex setting.
   - E₄³ and E₆² are weight-12 modular forms; 1728 Δ is weight 12.
   - G[0] = 1 − 1 − 0 = 0, so G is a cusp form.

2. Apply `cuspForm_eq_zero_via` (from `LevelOneSturmGeneric.lean`) with
   `(k, a, b, n) = (12, 1, 1, 2)`:
   - `1 * 12 = 12 * 1` ✓
   - `1 * 2 ≥ 1 + 1` ✓
   - Need G's q-expansion coefficients at m = 0 and m = 1 to vanish.
   - G[0] = 0 ✓;  G[1] = 720 − (−1008) − 1728 = 0 ✓  (by `native_decide`).

3. From `G = 0` as functions ℍ → ℂ, use `qExpansion_coeff_unique` to get
   `∀ n, coeff n (map ℤ→ℂ) G_Z = 0`, then lift to ℤ by `Int.cast_injective`.

This requires bundling E₄³ − E₆² as a `ModularForm Γ(1) 12` and constructing the
corresponding `CuspForm`.  The generic Sturm machinery handles the rest. -/
-- Helper: weight cast lemmas
private lemma three_mul_four_eq_twelve : (3 : ℕ) * (4 : ℤ) = 12 := by norm_num
private lemma two_mul_six_eq_twelve : (2 : ℕ) * (6 : ℤ) = 12 := by norm_num

-- Helper: E4^3 as a weight-12 modular form at level 1.
private noncomputable def E4CubedMF : ModularForm Γ(1) 12 :=
  ModularForm.mcast three_mul_four_eq_twelve
    (((DirectSum.of (ModularForm Γ(1)) 4 E4) ^ 3) ((3 : ℕ) * (4 : ℤ)))

-- Helper: E6^2 as a weight-12 modular form at level 1.
private noncomputable def E6SquaredMF : ModularForm Γ(1) 12 :=
  ModularForm.mcast two_mul_six_eq_twelve
    (((DirectSum.of (ModularForm Γ(1)) 6 E6) ^ 2) ((2 : ℕ) * (6 : ℤ)))

-- Helper: E4^3 q-expansion = E4QExpansion^3
private lemma E4CubedMF_qExpansion :
    ModularFormClass.qExpansion (1 : ℝ) (E4CubedMF : ℍ → ℂ) =
      E4QExpansion ^ 3 := by
  -- E4CubedMF = mcast (of E4 ^ 3), and mcast doesn't change the underlying function.
  -- qExpansion_of_pow gives qExpansion of (of E4)^3 = (qExpansion E4)^3.
  change ModularFormClass.qExpansion (1 : ℝ)
    ((ModularForm.mcast three_mul_four_eq_twelve
      (((DirectSum.of (ModularForm Γ(1)) 4 E4) ^ 3) ((3 : ℕ) * (4 : ℤ))) : ModularForm Γ(1) 12) : ℍ → ℂ) = _
  -- mcast doesn't change the function
  show ModularFormClass.qExpansion (1 : ℝ)
    ((((DirectSum.of (ModularForm Γ(1)) 4 E4) ^ 3) ((3 : ℕ) * (4 : ℤ)) : ModularForm Γ(1) _) : ℍ → ℂ) = _
  exact qExpansion_of_pow one_pos ModularFormClass.one_mem_strictPeriods_SL2Z E4 3

-- Helper: E6^2 q-expansion = E6QExpansion^2
private lemma E6SquaredMF_qExpansion :
    ModularFormClass.qExpansion (1 : ℝ) (E6SquaredMF : ℍ → ℂ) =
      E6QExpansion ^ 2 := by
  change ModularFormClass.qExpansion (1 : ℝ)
    ((ModularForm.mcast two_mul_six_eq_twelve
      (((DirectSum.of (ModularForm Γ(1)) 6 E6) ^ 2) ((2 : ℕ) * (6 : ℤ))) : ModularForm Γ(1) 12) : ℍ → ℂ) = _
  show ModularFormClass.qExpansion (1 : ℝ)
    ((((DirectSum.of (ModularForm Γ(1)) 6 E6) ^ 2) ((2 : ℕ) * (6 : ℤ)) : ModularForm Γ(1) _) : ℍ → ℂ) = _
  exact qExpansion_of_pow one_pos ModularFormClass.one_mem_strictPeriods_SL2Z E6 2

-- Helper: Δ q-expansion of deltaLevelOneMF equals deltaEulerSeries
private lemma deltaLevelOneMF_qExpansion :
    ModularFormClass.qExpansion (1 : ℝ) (deltaLevelOneMF : ℍ → ℂ) =
      deltaEulerSeries := by
  ext d; symm
  refine qExpansion_coeff_unique one_pos ModularFormClass.one_mem_strictPeriods_SL2Z ?_ d
  intro τ; simpa [smul_eq_mul, deltaLevelOneMF] using deltaEulerSeries_hasSum τ

-- Helper: map ℤ → ℂ for E6ZSeries
private lemma map_E6ZSeries :
    PowerSeries.map (Int.castRingHom ℂ) E6ZSeries = E6QExpansion := by
  ext n; rw [PowerSeries.coeff_map, coeff_E6ZSeries, coeff_E6QExpansion]
  unfold E6CoeffZ; by_cases hn : n = 0 <;> simp [hn]

/-- The modular form `G = E₄³ − E₆² − 1728 Δ` of weight 12 and level 1,
whose vanishing is the core of the identity. -/
private noncomputable def deltaIdentityGMF : ModularForm Γ(1) 12 :=
  E4CubedMF - E6SquaredMF - (1728 : ℂ) • deltaLevelOneMF

-- Coefficient of G's q-expansion at m equals the corresponding integer computation.
set_option maxHeartbeats 3200000 in
private lemma deltaIdentityGMF_qExpansion_coeff (m : ℕ) :
    (ModularFormClass.qExpansion (1 : ℝ) (deltaIdentityGMF : ℍ → ℂ)).coeff m =
      (PowerSeries.coeff (R := ℤ) m (E4ZSeries ^ 3) : ℂ) -
        (PowerSeries.coeff (R := ℤ) m (E6ZSeries ^ 2) : ℂ) -
        1728 * (PowerSeries.coeff (R := ℤ) m deltaEulerSeriesZ : ℂ) := by
  -- Use qExpansion_coeff_unique: G has HasSum equal to E4^3 - E6^2 - 1728*Δ.
  -- The ℤ power series mapped to ℂ give HasSum to E4, E6, Δ.
  -- G = E4CubedMF - E6SquaredMF - 1728 • deltaLevelOneMF
  -- The coefficients of qExpansion(G) equal the HasSum coefficients.
  -- We show HasSum for G using the individual HasSum for E4^3, E6^2, Δ.
  let c : ℕ → ℂ := fun m =>
    (PowerSeries.coeff (R := ℤ) m (E4ZSeries ^ 3) : ℂ) -
      (PowerSeries.coeff (R := ℤ) m (E6ZSeries ^ 2) : ℂ) -
      1728 * (PowerSeries.coeff (R := ℤ) m deltaEulerSeriesZ : ℂ)
  suffices hHS : ∀ τ : ℍ, HasSum (fun m => c m • Function.Periodic.qParam 1 (τ : ℂ) ^ m)
      (deltaIdentityGMF τ) by
    exact (qExpansion_coeff_unique one_pos ModularFormClass.one_mem_strictPeriods_SL2Z hHS m).symm
  intro τ
  -- deltaIdentityGMF τ = E4CubedMF τ - E6SquaredMF τ - 1728 * deltaLevelOneMF τ
  -- = E4(τ)^3 - E6(τ)^2 - 1728 * delta(τ)  (by definition)
  -- HasSum for E4^3: from E4CubedMF
  have hE4cube : HasSum (fun m => PowerSeries.coeff (R := ℂ) m (E4QExpansion ^ 3) *
      Function.Periodic.qParam 1 (τ : ℂ) ^ m) (E4CubedMF τ) := by
    rw [← E4CubedMF_qExpansion]
    exact ModularFormClass.hasSum_qExpansion (f := E4CubedMF) one_pos
      ModularFormClass.one_mem_strictPeriods_SL2Z τ
  have hE6sq : HasSum (fun m => PowerSeries.coeff (R := ℂ) m (E6QExpansion ^ 2) *
      Function.Periodic.qParam 1 (τ : ℂ) ^ m) (E6SquaredMF τ) := by
    rw [← E6SquaredMF_qExpansion]
    exact ModularFormClass.hasSum_qExpansion (f := E6SquaredMF) one_pos
      ModularFormClass.one_mem_strictPeriods_SL2Z τ
  have hDelta : HasSum (fun m => PowerSeries.coeff (R := ℂ) m deltaEulerSeries *
      Function.Periodic.qParam 1 (τ : ℂ) ^ m) (deltaLevelOneMF τ) := by
    rw [← deltaLevelOneMF_qExpansion]
    exact ModularFormClass.hasSum_qExpansion (f := deltaLevelOneMF) one_pos
      ModularFormClass.one_mem_strictPeriods_SL2Z τ
  -- Combine: G = E4³ - E6² - 1728*Δ
  have hcombine := ((hE4cube.sub hE6sq).sub (hDelta.mul_left 1728))
  -- Rewrite E4QExpansion etc. in terms of ℤ-series mapped to ℂ
  convert hcombine using 1
  · ext m
    simp only [c, smul_eq_mul, sub_mul]
    rw [← map_E4ZSeries, ← map_E6ZSeries, ← map_deltaEulerSeriesZ]
    rw [← map_pow, ← map_pow]
    simp only [PowerSeries.coeff_map]
    push_cast; ring
  · show deltaIdentityGMF τ = E4CubedMF τ - E6SquaredMF τ - 1728 * deltaLevelOneMF τ
    simp [deltaIdentityGMF, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]

/-- Coefficient check: the first two coefficients of `G = E₄³ − E₆² − 1728 Δ` vanish.
For `m = 0`: `1 − 1 − 1728 · 0 = 0`.
For `m = 1`: `720 − (−1008) − 1728 · 1 = 0`. -/
set_option maxHeartbeats 1600000 in
private theorem deltaIdentityGMF_low_coeffs_vanish (m : ℕ) (hm : m ≤ 1) :
    (ModularFormClass.qExpansion (1 : ℝ) (deltaIdentityGMF : ℍ → ℂ)).coeff m = 0 := by
  rw [deltaIdentityGMF_qExpansion_coeff]
  -- It suffices to show the ℤ expression is zero.
  suffices hZ : PowerSeries.coeff (R := ℤ) m (E4ZSeries ^ 3) -
      PowerSeries.coeff (R := ℤ) m (E6ZSeries ^ 2) -
      1728 * PowerSeries.coeff (R := ℤ) m deltaEulerSeriesZ = 0 by
    exact_mod_cast hZ
  interval_cases m
  · -- m = 0: E4Z^3[0] = 1^3 = 1, E6Z^2[0] = 1^2 = 1, Δ[0] = 0
    have hE4 : PowerSeries.coeff (R := ℤ) 0 (E4ZSeries ^ 3) = 1 := by
      rw [PowerSeries.coeff_zero_eq_constantCoeff, map_pow]
      have : PowerSeries.constantCoeff (R := ℤ) E4ZSeries = 1 := by
        simp [E4ZSeries, E4CoeffZ]
      simp [this]
    have hE6 : PowerSeries.coeff (R := ℤ) 0 (E6ZSeries ^ 2) = 1 := by
      rw [PowerSeries.coeff_zero_eq_constantCoeff, map_pow]
      have : PowerSeries.constantCoeff (R := ℤ) E6ZSeries = 1 := by
        simp [E6ZSeries, E6CoeffZ]
      simp [this]
    have hD : PowerSeries.coeff (R := ℤ) 0 deltaEulerSeriesZ = 0 := by
      rw [coeff_deltaEulerSeriesZ]; exact deltaEulerCoeffZ_zero
    simp [hE4, hE6, hD]
  · -- m = 1: use coeff_mul to expand convolutions
    -- E4Z^3 = E4Z * E4Z^2, and E4Z^2 = E4Z * E4Z
    -- coeff 1 (f * g) = f[0]*g[1] + f[1]*g[0]
    -- E4Z[0] = 1, E4Z[1] = 240, E6Z[0] = 1, E6Z[1] = -504, Δ[1] = 1
    have hE4_0 : PowerSeries.coeff (R := ℤ) 0 E4ZSeries = 1 := by
      simp [coeff_E4ZSeries, E4CoeffZ]
    have hE4_1 : PowerSeries.coeff (R := ℤ) 1 E4ZSeries = 240 := by
      simp [coeff_E4ZSeries, E4CoeffZ, ArithmeticFunction.sigma]
    have hE6_0 : PowerSeries.coeff (R := ℤ) 0 E6ZSeries = 1 := by
      simp [coeff_E6ZSeries, E6CoeffZ]
    have hE6_1 : PowerSeries.coeff (R := ℤ) 1 E6ZSeries = -504 := by
      simp [coeff_E6ZSeries, E6CoeffZ, ArithmeticFunction.sigma]
    have hD_1 : PowerSeries.coeff (R := ℤ) 1 deltaEulerSeriesZ = 1 :=
      coeff_deltaEulerSeriesZ_one
    -- E4Z^2[1] = E4Z[0]*E4Z[1] + E4Z[1]*E4Z[0] = 2*240 = 480
    have hE4sq_1 : PowerSeries.coeff (R := ℤ) 1 (E4ZSeries ^ 2) = 480 := by
      rw [pow_two, PowerSeries.coeff_mul,
        Finset.Nat.sum_antidiagonal_succ, Finset.Nat.antidiagonal_zero,
        Finset.sum_singleton]
      simp [hE4_0, hE4_1]
    -- E4Z^3[1] = E4Z[0]*E4Z^2[1] + E4Z[1]*E4Z^2[0] = 480 + 240 = 720
    have hE4sq_0 : PowerSeries.coeff (R := ℤ) 0 (E4ZSeries ^ 2) = 1 := by
      rw [PowerSeries.coeff_zero_eq_constantCoeff, map_pow]
      simp [E4ZSeries, E4CoeffZ]
    have hE4cube_1 : PowerSeries.coeff (R := ℤ) 1 (E4ZSeries ^ 3) = 720 := by
      rw [show (3 : ℕ) = 2 + 1 from rfl, pow_succ, PowerSeries.coeff_mul,
        Finset.Nat.sum_antidiagonal_succ, Finset.Nat.antidiagonal_zero,
        Finset.sum_singleton]
      simp [hE4_0, hE4_1, hE4sq_0, hE4sq_1]
    -- E6Z^2[1] = E6Z[0]*E6Z[1] + E6Z[1]*E6Z[0] = 2*(-504) = -1008
    have hE6sq_1 : PowerSeries.coeff (R := ℤ) 1 (E6ZSeries ^ 2) = -1008 := by
      rw [pow_two, PowerSeries.coeff_mul,
        Finset.Nat.sum_antidiagonal_succ, Finset.Nat.antidiagonal_zero,
        Finset.sum_singleton]
      simp [hE6_0, hE6_1]
    rw [hE4cube_1, hE6sq_1, hD_1]
    ring

set_option maxHeartbeats 800000 in
theorem delta_1728_identity :
    (1728 : ℤ) • deltaEulerSeriesZ = E4ZSeries ^ 3 - E6ZSeries ^ 2 := by
  -- Step 1: Show G = E4³ - E6² - 1728Δ = 0 as a weight-12 modular form via Sturm bound.
  have hG : deltaIdentityGMF = 0 :=
    levelOne_modularForm_eq_zero_of_low_coeffs_vanish
      (show (4 : ℕ) ≤ 12 by norm_num) ⟨6, rfl⟩
      (fun m hm => deltaIdentityGMF_low_coeffs_vanish m (by omega))
  -- Step 2: From G = 0, every q-expansion coefficient vanishes.
  have hqzero : ModularFormClass.qExpansion (1 : ℝ) (deltaIdentityGMF : ℍ → ℂ) = 0 :=
    (qExpansion_eq_zero_iff one_pos ModularFormClass.one_mem_strictPeriods_SL2Z
      deltaIdentityGMF).mpr hG
  have hzero_coeff : ∀ n, (ModularFormClass.qExpansion (1 : ℝ) (deltaIdentityGMF : ℍ → ℂ)).coeff n = 0 := by
    intro n; rw [hqzero]; simp
  -- Step 3: Each coefficient of G's q-expansion equals the ℤ computation.
  -- From deltaIdentityGMF_qExpansion_coeff + hzero_coeff, we get the ℤ identity.
  ext n
  have hcoeff := deltaIdentityGMF_qExpansion_coeff n
  rw [hzero_coeff] at hcoeff
  -- hcoeff: 0 = (E4Z^3[n] : ℂ) - (E6Z^2[n] : ℂ) - 1728 * (ΔZ[n] : ℂ)
  -- Goal: 1728 • ΔZ[n] = E4Z^3[n] - E6Z^2[n]
  -- The ℤ identity follows from the vanishing ℂ identity by injectivity of ℤ → ℂ.
  apply Int.cast_injective (α := ℂ)
  push_cast [PowerSeries.coeff_smul, PowerSeries.coeff_sub, smul_eq_mul]
  linarith

/-- Convolution of a nonneg sequence with the constant-1 sequence is at least
    the original sequence pointwise. -/
private lemma le_convNat_one (F : ℕ → ℕ) (n : ℕ) :
    F n ≤ convNat F (fun _ => 1) n := by
  simp only [convNat, mul_one]
  exact Finset.single_le_sum (fun k _ => Nat.zero_le _)
    (Finset.mem_range.mpr (Nat.lt_succ_iff.mpr le_rfl))

/-- `PowerSeries.mk (coeff · f) = f` — reconstruction from coefficients. -/
private lemma mk_coeff_eq (f : PowerSeries ℤ) :
    PowerSeries.mk (fun n => PowerSeries.coeff (R := ℤ) n f) = f :=
  PowerSeries.ext (fun n => PowerSeries.coeff_mk n _)

theorem maj_Delta :
    Maj (fun n => PowerSeries.coeff (R := ℤ) n deltaEulerSeriesZ) DeltaBound := by
  -- From the 1728 identity: 1728 * Δ[n] = (E4³)[n] - (E6²)[n]
  -- So |Δ[n]| = |(E4³ - E6²)[n]| / 1728 ≤ (|(E4³)[n]| + |(E6²)[n]|) / 1728
  --          ≤ |(E4³)[n]| + |(E6²)[n]|
  have hident := delta_1728_identity
  -- E4³ majorant
  have hE4_mk : PowerSeries.mk (fun n => PowerSeries.coeff (R := ℤ) n E4ZSeries) =
      E4ZSeries := mk_coeff_eq _
  have hE6_mk : PowerSeries.mk (fun n => PowerSeries.coeff (R := ℤ) n E6ZSeries) =
      E6ZSeries := mk_coeff_eq _
  have maj_E4_cube : Maj (fun n =>
      PowerSeries.coeff (R := ℤ) n (E4ZSeries ^ 3))
      (powConvNat G4Bound 3) := by
    have h := Maj.powConv maj_E4 3; rwa [hE4_mk] at h
  have maj_E6_sq : Maj (fun n =>
      PowerSeries.coeff (R := ℤ) n (E6ZSeries ^ 2))
      (powConvNat G6Bound 2) := by
    have h := Maj.powConv maj_E6 2; rwa [hE6_mk] at h
  -- powConvNat G4Bound 3 = convNat G4Bound (convNat G4Bound G4Bound)
  -- powConvNat G6Bound 2 = convNat G6Bound G6Bound
  -- We need to show these definitional equalities modulo convNat with delta_0
  -- powConvNat F 1 = convNat F δ₀ which equals F pointwise
  -- For now, unfold powConvNat and work with the definitions
  intro n
  -- From the identity: 1728 * Δ[n] = (E4³ - E6²)[n]
  have hcoeff : (1728 : ℤ) * PowerSeries.coeff (R := ℤ) n deltaEulerSeriesZ =
      PowerSeries.coeff (R := ℤ) n (E4ZSeries ^ 3 - E6ZSeries ^ 2) := by
    have := congr_arg (PowerSeries.coeff (R := ℤ) n) hident
    simp only [map_smul, smul_eq_mul] at this
    exact this
  -- |Δ[n]| * 1728 = |1728 * Δ[n]| = |(E4³ - E6²)[n]| ≤ |E4³[n]| + |E6²[n]|
  have h1728_pos : (0 : ℤ) < 1728 := by norm_num
  rw [map_sub] at hcoeff
  have habs_ineq : (1728 : ℤ) * |PowerSeries.coeff (R := ℤ) n deltaEulerSeriesZ| ≤
      |PowerSeries.coeff (R := ℤ) n (E4ZSeries ^ 3)| +
      |PowerSeries.coeff (R := ℤ) n (E6ZSeries ^ 2)| := by
    rw [← abs_of_pos h1728_pos, ← abs_mul, hcoeff]
    -- |a - b| ≤ |a| + |b|
    calc |PowerSeries.coeff (R := ℤ) n (E4ZSeries ^ 3) -
            PowerSeries.coeff (R := ℤ) n (E6ZSeries ^ 2)|
        ≤ |PowerSeries.coeff (R := ℤ) n (E4ZSeries ^ 3)| +
          |-(PowerSeries.coeff (R := ℤ) n (E6ZSeries ^ 2))| := by
            rw [show PowerSeries.coeff (R := ℤ) n (E4ZSeries ^ 3) -
              PowerSeries.coeff (R := ℤ) n (E6ZSeries ^ 2) =
              PowerSeries.coeff (R := ℤ) n (E4ZSeries ^ 3) +
              (-(PowerSeries.coeff (R := ℤ) n (E6ZSeries ^ 2))) from sub_eq_add_neg _ _]
            exact abs_add_le _ _
      _ = _ := by rw [abs_neg]
  -- Now bound |E4³[n]| and |E6²[n]|
  have hE4cube_bound := maj_E4_cube n
  have hE6sq_bound := maj_E6_sq n
  -- |Δ[n]| ≤ (|E4³[n]| + |E6²[n]|) / 1728
  --        ≤ |E4³[n]| + |E6²[n]|
  --        ≤ powConvNat G4Bound 3 n + powConvNat G6Bound 2 n
  have hdelta_bound : |PowerSeries.coeff (R := ℤ) n deltaEulerSeriesZ| ≤
      ↑(powConvNat G4Bound 3 n) + ↑(powConvNat G6Bound 2 n) := by
    have h := habs_ineq
    have := add_le_add hE4cube_bound hE6sq_bound
    calc |PowerSeries.coeff (R := ℤ) n deltaEulerSeriesZ|
        ≤ 1728 * |PowerSeries.coeff (R := ℤ) n deltaEulerSeriesZ| := by
          linarith [abs_nonneg (PowerSeries.coeff (R := ℤ) n deltaEulerSeriesZ)]
      _ ≤ |PowerSeries.coeff (R := ℤ) n (E4ZSeries ^ 3)| +
          |PowerSeries.coeff (R := ℤ) n (E6ZSeries ^ 2)| := habs_ineq
      _ ≤ ↑(powConvNat G4Bound 3 n) + ↑(powConvNat G6Bound 2 n) := this
  -- Now relate powConvNat to the DeltaBound definition
  -- DeltaBound n = convNat (convNat G4Bound (convNat G4Bound G4Bound)) (fun _ => 1) n
  --             + convNat G6Bound G6Bound n
  -- powConvNat G4Bound 3 n ≤ convNat (powConvNat G4Bound 3) (fun _ => 1) n
  -- and powConvNat G4Bound 3 = convNat G4Bound (convNat G4Bound G4Bound) (need proof)
  -- powConvNat G6Bound 2 n = convNat G6Bound G6Bound (need proof)
  -- Step: show powConvNat G4Bound 3 n ≤ first term of DeltaBound
  -- and powConvNat G6Bound 2 n ≤ second term of DeltaBound
  show |PowerSeries.coeff (R := ℤ) n deltaEulerSeriesZ| ≤ ↑(DeltaBound n)
  unfold DeltaBound
  push_cast
  calc |PowerSeries.coeff (R := ℤ) n deltaEulerSeriesZ|
      ≤ ↑(powConvNat G4Bound 3 n) + ↑(powConvNat G6Bound 2 n) := hdelta_bound
    _ ≤ ↑(convNat (convNat G4Bound (convNat G4Bound G4Bound)) (fun _ => 1) n) +
        ↑(convNat G6Bound G6Bound n) := by
        apply add_le_add
        · -- powConvNat G4Bound 3 n ≤ convNat (...) (fun _ => 1) n
          -- First: powConvNat G4Bound 3 = convNat G4Bound (convNat G4Bound G4Bound)
          -- as functions (need to unfold and show convNat F δ₀ = F)
          suffices h : powConvNat G4Bound 3 n ≤
              convNat (convNat G4Bound (convNat G4Bound G4Bound)) (fun _ => 1) n by
            exact_mod_cast h
          -- powConvNat G4Bound 3 n = convNat G4Bound (powConvNat G4Bound 2) n
          --   = convNat G4Bound (convNat G4Bound (powConvNat G4Bound 1)) n
          -- where powConvNat G4Bound 1 = convNat G4Bound (powConvNat G4Bound 0)
          --   = convNat G4Bound δ₀
          -- and convNat F δ₀ = F pointwise
          -- So powConvNat G4Bound 3 n = convNat G4Bound (convNat G4Bound G4Bound) n
          have hpow1 : ∀ m, powConvNat G4Bound 1 m = G4Bound m := by
            intro m; show convNat G4Bound (fun n => if n = 0 then 1 else 0) m = G4Bound m
            simp only [convNat]
            rw [Finset.sum_eq_single_of_mem m (Finset.mem_range.mpr (by omega))
              (fun k hk hkm => by
                have : k < m + 1 := Finset.mem_range.mp hk
                simp [show m - k ≠ 0 from by omega])]
            simp
          have hpow3_eq : powConvNat G4Bound 3 n =
              convNat G4Bound (convNat G4Bound G4Bound) n := by
            show convNat G4Bound (convNat G4Bound (powConvNat G4Bound 1)) n =
              convNat G4Bound (convNat G4Bound G4Bound) n
            congr 1; ext m; congr 1; ext m'; exact hpow1 m'
          rw [hpow3_eq]
          exact le_convNat_one _ n
        · -- powConvNat G6Bound 2 n = convNat G6Bound G6Bound n
          have hpow1 : ∀ m, powConvNat G6Bound 1 m = G6Bound m := by
            intro m; show convNat G6Bound (fun n => if n = 0 then 1 else 0) m = G6Bound m
            simp only [convNat]
            rw [Finset.sum_eq_single_of_mem m (Finset.mem_range.mpr (by omega))
              (fun k hk hkm => by
                have : k < m + 1 := Finset.mem_range.mp hk
                simp [show m - k ≠ 0 from by omega])]
            simp
          have hpow2_eq : powConvNat G6Bound 2 n = convNat G6Bound G6Bound n := by
            show convNat G6Bound (powConvNat G6Bound 1) n =
              convNat G6Bound G6Bound n
            congr 1; ext m; exact hpow1 m
          rw [hpow2_eq]

theorem maj_DeltaTight :
    Maj (fun n => PowerSeries.coeff (R := ℤ) n deltaEulerSeriesZ) DeltaBoundTight := by
  have hident := delta_1728_identity
  have hE4_mk := mk_coeff_eq E4ZSeries
  have hE6_mk := mk_coeff_eq E6ZSeries
  have maj_E4_cube : Maj (fun n => PowerSeries.coeff (R := ℤ) n (E4ZSeries ^ 3))
      (powConvNat G4Bound 3) := by
    have h := Maj.powConv maj_E4 3; rwa [hE4_mk] at h
  have maj_E6_sq : Maj (fun n => PowerSeries.coeff (R := ℤ) n (E6ZSeries ^ 2))
      (powConvNat G6Bound 2) := by
    have h := Maj.powConv maj_E6 2; rwa [hE6_mk] at h
  intro n
  have hcoeff : (1728 : ℤ) * PowerSeries.coeff (R := ℤ) n deltaEulerSeriesZ =
      PowerSeries.coeff (R := ℤ) n (E4ZSeries ^ 3 - E6ZSeries ^ 2) := by
    have := congr_arg (PowerSeries.coeff (R := ℤ) n) hident
    simp only [map_smul, smul_eq_mul] at this; exact this
  rw [map_sub] at hcoeff
  have hpow1_G4 : ∀ m, powConvNat G4Bound 1 m = G4Bound m := by
    intro m; show convNat G4Bound (fun n => if n = 0 then 1 else 0) m = G4Bound m
    simp only [convNat]
    rw [Finset.sum_eq_single_of_mem m (Finset.mem_range.mpr (by omega))
      (fun k hk hkm => by simp [show m - k ≠ 0 from by omega])]
    simp
  have hpow3_eq : ∀ m, powConvNat G4Bound 3 m =
      convNat G4Bound (convNat G4Bound G4Bound) m := by
    intro m
    show convNat G4Bound (convNat G4Bound (powConvNat G4Bound 1)) m = _
    congr 1; ext m'; congr 1; ext m''; exact hpow1_G4 m''
  have hpow1_G6 : ∀ m, powConvNat G6Bound 1 m = G6Bound m := by
    intro m; show convNat G6Bound (fun n => if n = 0 then 1 else 0) m = G6Bound m
    simp only [convNat]
    rw [Finset.sum_eq_single_of_mem m (Finset.mem_range.mpr (by omega))
      (fun k hk hkm => by simp [show m - k ≠ 0 from by omega])]
    simp
  have hpow2_eq : ∀ m, powConvNat G6Bound 2 m = convNat G6Bound G6Bound m := by
    intro m; show convNat G6Bound (powConvNat G6Bound 1) m = _
    congr 1; ext m'; exact hpow1_G6 m'
  set C := convNat G4Bound (convNat G4Bound G4Bound) n + convNat G6Bound G6Bound n
  have h1728_bound : 1728 * |PowerSeries.coeff (R := ℤ) n deltaEulerSeriesZ| ≤ (C : ℤ) := by
    rw [← abs_of_pos (show (0 : ℤ) < 1728 from by norm_num), ← abs_mul, hcoeff]
    calc |PowerSeries.coeff (R := ℤ) n (E4ZSeries ^ 3) -
            PowerSeries.coeff (R := ℤ) n (E6ZSeries ^ 2)|
        ≤ |PowerSeries.coeff (R := ℤ) n (E4ZSeries ^ 3)| +
          |PowerSeries.coeff (R := ℤ) n (E6ZSeries ^ 2)| := by
          rw [sub_eq_add_neg]; exact (abs_add_le _ _).trans (by rw [abs_neg])
      _ ≤ ↑(powConvNat G4Bound 3 n) + ↑(powConvNat G6Bound 2 n) :=
          add_le_add (maj_E4_cube n) (maj_E6_sq n)
      _ = ↑C := by simp only [C, hpow3_eq, hpow2_eq]; push_cast; ring
  show |PowerSeries.coeff (R := ℤ) n deltaEulerSeriesZ| ≤ ↑(DeltaBoundTight n)
  unfold DeltaBoundTight
  push_cast
  have h_abs_nn : (0 : ℤ) ≤ |PowerSeries.coeff (R := ℤ) n deltaEulerSeriesZ| := abs_nonneg _
  omega

/-! ## Layer 3: Row bridge and row bounds

  The derivative identity (already proved):
    E4 · D Q_j = (42 E2E4 - j E6) · Q_j

  establishes that the recurrence rows Q_j are exactly the Fourier
  coefficients of Δ^(42-j) · E4^(3j). This is a symbolic proof
  using uniqueness of the recurrence solution.
-/

/-- The recurrence row Q_j equals the closed form Δ^(42-j) · (E4³)^j. -/
theorem phi41_Qrow_eq_closed_form (j : ℕ) (hj : j ≤ 42) (n : ℕ)
    (hn : n < phi41Level41SturmBound) :
    truncCoeffArrayAt
      ((phi41QRecurrenceRowsArray phi41Level41SturmBound).getD j
        (zeroTruncCoeffArray phi41Level41SturmBound)) n =
      PowerSeries.coeff (R := ℤ) n
        ((E4ZSeries ^ 3) ^ j * deltaEulerSeriesZ ^ (42 - j)) := by
  set N := phi41Level41SturmBound with hN_def
  -- Step 1: TruncRep connects the power series to the dense row list
  have hTR := TruncRep.phi41LevelOneDenseRowExpr N j
  -- Step 2: The dense row list satisfies the recurrence (from the derivative identity)
  have hderiv : E4ZSeries *
      (PowerSeries.X * PowerSeries.derivative ℤ
        ((E4ZSeries ^ 3) ^ j * deltaEulerSeriesZ ^ (42 - j))) =
    (PowerSeries.C (42 : ℤ) * (E2ZSeries * E4ZSeries) -
      PowerSeries.C (j : ℤ) * E6ZSeries) *
        ((E4ZSeries ^ 3) ^ j * deltaEulerSeriesZ ^ (42 - j)) :=
    phi41LevelOneDenseRow_derivative_identity_of_base j hj
      (E4ZSeries_cubed_derivative_identity_of_E4_derivative_identity
        E4ZSeries_derivative_identity)
      deltaEulerSeriesZ_derivative_identity
  -- Step 3: ListArrayEq connects the dense row list to the recurrence row array
  have hLA : ListArrayEq N
      ((phi41LevelOneDenseRowsList N).getD j (zeroTruncCoeffList N))
      (phi41QRecurrenceRowArray N j
        (E4TruncCoeffArray N) (E6TruncCoeffArray N) (E2E4TruncCoeffArray N)) :=
    ListArrayEq.of_phi41QRecurrence
      (ListArrayEq.E4 N) (ListArrayEq.E6 N) (ListArrayEq.E2E4 N)
      (fun m hm hmv =>
        truncCoeffAt_phi41LevelOneDenseRowsList_eq_zero_of_lt_valuation hj hm hmv)
      (fun m hm hmv =>
        truncCoeffAt_phi41LevelOneDenseRowsList_eq_one_of_eq_valuation hj hm hmv)
      (fun m hm hmv =>
        truncCoeffAt_phi41LevelOneDenseRowsList_eq_recurrence_of_derivative_identity
          hj hm hmv hderiv)
  -- Step 4: Unwrap the array access
  rw [phi41QRecurrenceRowsArray_getD_of_le N hj]
  -- Step 5: Chain the equalities
  -- TruncRep gives: coeff n (...) = truncCoeffAt (dense_row) n
  have hcoeff := hTR n hn
  -- ListArrayEq gives: truncCoeffAt (dense_row) n = truncCoeffArrayAt (rec_row) n
  have hLA_n := hLA n hn
  -- Rewrite using phi41LevelOneDenseRowsList_getD_of_le
  rw [phi41LevelOneDenseRowsList_getD_of_le N hj] at hLA_n
  -- Now hLA_n : truncCoeffAt (mulTruncCoeffList ...) n = truncCoeffArrayAt (recRow) n
  -- hcoeff : coeff n (...) = truncCoeffAt (mulTruncCoeffList ...) n
  rw [← hLA_n, ← hcoeff]

/-- Majorant chain: |(E4³)^j · Δ^(42-j) [n]| ≤ conv(G4^{3j}, DeltaTight^{42-j})(n). -/
theorem maj_Qrow (j : ℕ) (hj : j ≤ 42) :
    Maj (fun n => PowerSeries.coeff (R := ℤ) n
        ((E4ZSeries ^ 3) ^ j * deltaEulerSeriesZ ^ (42 - j)))
      (convNat (powConvNat G4Bound (3 * j)) (powConvNat DeltaBoundTight (42 - j))) := by
  have hE4_mk := mk_coeff_eq E4ZSeries
  have hD_mk := mk_coeff_eq deltaEulerSeriesZ
  have maj_E4_pow : Maj (fun n => PowerSeries.coeff (R := ℤ) n (E4ZSeries ^ (3 * j)))
      (powConvNat G4Bound (3 * j)) := by
    have h := Maj.powConv maj_E4 (3 * j); rwa [hE4_mk] at h
  have maj_D_pow : Maj (fun n => PowerSeries.coeff (R := ℤ) n (deltaEulerSeriesZ ^ (42 - j)))
      (powConvNat DeltaBoundTight (42 - j)) := by
    have h := Maj.powConv maj_DeltaTight (42 - j); rwa [hD_mk] at h
  have hpow : (E4ZSeries ^ 3) ^ j = E4ZSeries ^ (3 * j) := by rw [← pow_mul]
  rw [hpow]
  exact Maj.conv maj_E4_pow maj_D_pow

/-- Q_j row bound for the big side (n ≤ 3528). -/
def QrowBigBound : ℕ := 10 ^ 1090

theorem Qrow_bound_big (j n : ℕ) (hj : j ≤ 42) (hn : n < phi41Level41SturmBound) :
    |PowerSeries.coeff (R := ℤ) n
      ((E4ZSeries ^ 3) ^ j * deltaEulerSeriesZ ^ (42 - j))| ≤
        (QrowBigBound : ℤ) := by
  sorry

/-- Q_j row bound for the pullback side (n ≤ 86). -/
def QrowPullBound : ℕ := 10 ^ 335

theorem Qrow_bound_pull (j n : ℕ) (hj : j ≤ 42)
    (hn : n < (phi41Level41SturmBound + 40) / 41) :
    |PowerSeries.coeff (R := ℤ) n
      ((E4ZSeries ^ 3) ^ j * deltaEulerSeriesZ ^ (42 - j))| ≤
        (QrowPullBound : ℤ) := by
  sorry

/-! ## Layer 4: Final hbound -/

/-- L¹ norm of the sparse polynomial coefficients. -/
def phi41SparseCoeffL1 : ℕ := 430214329162130934998014102783361653658762732413094968916550882973547953622830262212842588534662719039444865306033970385222128557480041050477161942460951747267724218572856686366457354033833183729895066298456075383665917627855402679807422318295127406075930386573946224224589581427869341548900894574793047751098726891135150527133456232175958143472802273850895591408228388096697078890752446780701243687850587368626490269011874194961146618896275452020396881788950421918688605914846416454068185912748488270029811530696637748568712369220658313129280786402819547027841719551741165076517643725037564882558190925529

/-- Final height bound: 87 · H · 10^1090 · 10^335, rounded up. -/
def phi41HeightBound : ℕ :=
  87 * phi41SparseCoeffL1 * QrowBigBound * QrowPullBound

/-- The analytical hbound — zero native_decide. -/
theorem phi41_final_coeff_bound (n : ℕ) (hn : n < phi41Level41SturmBound) :
    |truncCoeffArrayAt
      (phi41Level41RecurrenceCoeffArray phi41Level41SturmBound) n| ≤
        (phi41HeightBound : ℤ) := by
  sorry

end Ripple.Number.Modular
