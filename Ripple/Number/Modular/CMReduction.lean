import Mathlib.Tactic

/-!
# Elementary CM reduction checks

This file contains finite arithmetic checks for the class-number-one CM
points used by the Ramanujan--Chudnovsky identities.  The analytic bridge
to singular moduli is built elsewhere; these lemmas isolate the exact
reduced-form arithmetic that the CM evaluation will use.
-/

namespace Ripple
namespace Number
namespace Modular

/-- The unique reduced positive definite binary quadratic form of discriminant `-163`
with the convention `0 ≤ b ≤ a ≤ c` is `[1, 1, 41]`.

This is the elementary finite reduction step behind the Heegner discriminant
`-163`; no modular-form evaluation is used here. -/
lemma reduced_discriminant_neg163_unique {a b c : ℤ}
    (ha : 0 < a) (hb_nonneg : 0 ≤ b) (hb_le : b ≤ a) (ha_le_c : a ≤ c)
    (hdisc : b * b - 4 * a * c = -163) :
    a = 1 ∧ b = 1 ∧ c = 41 := by
  have hb2_le_a2 : b * b ≤ a * a := by nlinarith
  have ha2_le_ac : a * a ≤ a * c := by nlinarith
  have h4ac : 4 * a * c = b * b + 163 := by nlinarith
  have ha_bound : a ≤ 7 := by
    have : 3 * a * a ≤ 163 := by nlinarith
    nlinarith [sq_nonneg (a - 8)]
  have ha_cases :
      a = 1 ∨ a = 2 ∨ a = 3 ∨ a = 4 ∨ a = 5 ∨ a = 6 ∨ a = 7 := by
    omega
  rcases ha_cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    interval_cases b <;> omega

/-- The reduced positive definite binary quadratic forms of discriminant `-232`
with the convention `0 ≤ b ≤ a ≤ c` are `[1, 0, 58]` and `[2, 0, 29]`.

The point `i √58` corresponds to the first of these.  The second form is the
other reduced representative that must be handled by the level-2 class invariant
in the Ramanujan `λ(√-58)` evaluation. -/
lemma reduced_discriminant_neg232_cases {a b c : ℤ}
    (ha : 0 < a) (hb_nonneg : 0 ≤ b) (hb_le : b ≤ a) (ha_le_c : a ≤ c)
    (hdisc : b * b - 4 * a * c = -232) :
    (a = 1 ∧ b = 0 ∧ c = 58) ∨ (a = 2 ∧ b = 0 ∧ c = 29) := by
  have hb2_le_a2 : b * b ≤ a * a := by nlinarith
  have ha2_le_ac : a * a ≤ a * c := by nlinarith
  have h4ac : 4 * a * c = b * b + 232 := by nlinarith
  have ha_bound : a ≤ 9 := by
    have : 3 * a * a ≤ 232 := by nlinarith
    nlinarith [sq_nonneg (a - 9)]
  have ha_cases :
      a = 1 ∨ a = 2 ∨ a = 3 ∨ a = 4 ∨ a = 5 ∨ a = 6 ∨ a = 7 ∨ a = 8 ∨ a = 9 := by
    omega
  rcases ha_cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    interval_cases b <;> omega

end Modular
end Number
end Ripple
