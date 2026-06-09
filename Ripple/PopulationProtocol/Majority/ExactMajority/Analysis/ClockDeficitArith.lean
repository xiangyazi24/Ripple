import Mathlib.Data.Nat.Basic

namespace ExactMajority
namespace Analysis

/-- Given a clock phase `p` that is strictly less than 3, any strictly greater
phase `q` has a strictly smaller clock deficit.
This is pure arithmetic over `ℕ` showing `3 - min q 3 < 3 - min p 3`. -/
lemma clockDeficit_lt_of_phase_advance (p q : ℕ) (hp : p < 3) (h_lt : p < q) :
    3 - min q 3 < 3 - min p 3 := by
  omega

/-- If two agents update their phases monotonically (p₁ ≤ q₁ and p₂ ≤ q₂),
and at least one strictly advances from a phase < 3, then their combined
clock deficit strictly decreases. -/
lemma pair_deficit_decreases (p1 p2 q1 q2 : ℕ) 
    (h_mono1 : p1 ≤ q1) (h_mono2 : p2 ≤ q2)
    (h_strict : (p1 < 3 ∧ p1 < q1) ∨ (p2 < 3 ∧ p2 < q2)) :
    (3 - min q1 3) + (3 - min q2 3) < (3 - min p1 3) + (3 - min p2 3) := by
  rcases h_strict with ⟨hp1_lt3, hp1_lt⟩ | ⟨hp2_lt3, hp2_lt⟩
  · -- p1 strictly advanced from < 3
    have h1 : 3 - min q1 3 < 3 - min p1 3 := clockDeficit_lt_of_phase_advance p1 q1 hp1_lt3 hp1_lt
    have h2 : 3 - min q2 3 ≤ 3 - min p2 3 := by omega
    omega
  · -- p2 strictly advanced from < 3
    have h1 : 3 - min q1 3 ≤ 3 - min p1 3 := by omega
    have h2 : 3 - min q2 3 < 3 - min p2 3 := clockDeficit_lt_of_phase_advance p2 q2 hp2_lt3 hp2_lt
    omega

end Analysis
end ExactMajority
