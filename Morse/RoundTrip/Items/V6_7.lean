import Morse
import RoundTrip.Check
import RoundTrip.Blind.V6_7

namespace RoundTrip.V6_7

/-- The project's statement (universe of `E` instantiated at 0): uniqueness for `x' = A(t)x`
(`A` continuous, `E` any real normed space) on an open interval and on `ℝ`, and global existence
when `A(t)` is skew-adjoint (`E` a complete real inner product space). -/
def A : Prop :=
  type_of% @Morse.linearODE_eqOn.{0} ∧ type_of% @Morse.linearODE_eq.{0} ∧
    type_of% @Morse.exists_skewLinearODE.{0}

theorem A_holds : A := ⟨@Morse.linearODE_eqOn, @Morse.linearODE_eq, @Morse.exists_skewLinearODE⟩

/-! Neither direction is proved: see `V6_7.json`.  A gives existence only for skew-adjoint
coefficients, while B asks for existence for Milnor's (non-skew) coefficients
`-Σᵢ (duⁱ/dt) Γᵏᵢⱼ(u(t))`; B covers only smooth coefficients on `ℝⁿ`, while A's uniqueness is for
continuous coefficients on arbitrary normed spaces. -/

end RoundTrip.V6_7
