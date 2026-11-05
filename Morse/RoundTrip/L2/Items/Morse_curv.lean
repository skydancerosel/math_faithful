import Morse
import RoundTrip.L2.Blind.Morse_curv

/-! Layer-2 check of `Morse.curv` (Milnor's curvature of a connection on left-invariant fields,
`R(X, Y)Z = −D_X D_Y Z + D_Y D_X Z + D_{[X,Y]} Z`) against the blind textbook definition (the same
formula, Milnor's sign). The two definitions are syntactically identical: `agree` is `rfl`. -/

namespace RoundTrip.L2.Morse_curv

/-- **Agreement**, outright (definitional). -/
theorem agree {L : Type*} [LieRing L] [LieAlgebra ℝ L] (D : L →ₗ[ℝ] L →ₗ[ℝ] L) (X Y Z : L) :
    Morse.curv D X Y Z = T D X Y Z := rfl

end RoundTrip.L2.Morse_curv
