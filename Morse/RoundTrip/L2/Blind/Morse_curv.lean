import Morse
/-! Layer-2 blind definition of Morse_curv. Textbook: Milnor, *Morse Theory*, §9, p. 51 (and §21
for Lie groups): the curvature tensor of a connection `D`, in MILNOR'S SIGN CONVENTION
`R(X, Y)Z = −D_X(D_Y Z) + D_Y(D_X Z) + D_{[X,Y]} Z` (minus the usual
`D_X D_Y − D_Y D_X − D_{[X,Y]}`), so that `⟨R(X,Y)X, Y⟩` is the sectional curvature of the plane
of orthonormal `X, Y`; for a bi-invariant metric `D_X Y = ½[X,Y]` gives `R(X,Y)Z = ¼[[X,Y],Z]`.
Choices: evaluated on left-invariant fields, identified with the Lie algebra `L` (bracket `⁅X, Y⁆`
= bracket of the left-invariant fields); `D X Y` is `D_X Y`, which is again left-invariant for a
left-invariant connection, so all three terms are computed in `L`. -/
namespace RoundTrip.L2.Morse_curv

/-- The textbook notion: `R(X, Y)Z = −D_X D_Y Z + D_Y D_X Z + D_{[X,Y]} Z` (Milnor's sign). -/
def T {L : Type*} [LieRing L] [LieAlgebra ℝ L] (D : L →ₗ[ℝ] L →ₗ[ℝ] L) (X Y Z : L) : L :=
  -D X (D Y Z) + D Y (D X Z) + D ⁅X, Y⁆ Z

end RoundTrip.L2.Morse_curv
