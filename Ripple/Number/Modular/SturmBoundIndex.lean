/-
  Bridge between the literal `phi41Level41SturmBound = 3529 = 1008/12 * 42 + 1`
  expression and the proven `[SL₂(ℤ):Γ₀(41)] = 42` index formula.

  This is the small connector that lets downstream Sturm-bound work refer to
  the Γ₀(41) Sturm bound in terms of the abstract group-theoretic index, not
  a magic constant.
-/
import Ripple.Number.Modular.ModularPolynomialQExpansion
import Ripple.Number.Modular.CosetIndex

namespace Ripple
namespace Number
namespace Modular

/-- Restatement of `phi41Level41SturmBound_eq` using the proven Γ₀(41) index
formula in place of the literal `42`. -/
theorem phi41Level41SturmBound_eq_index :
    phi41Level41SturmBound =
      phi41Level41ClearedWeight / 12 * (CongruenceSubgroup.Gamma0 41).index + 1 := by
  have hidx : (CongruenceSubgroup.Gamma0 41).index = 42 :=
    Ripple.CosetIndex.gamma0_index_41
  rw [phi41Level41SturmBound_eq, hidx]

end Modular
end Number
end Ripple
