import Morse
/-! Layer-2 blind definition of Morse_IsLeviCivita. Textbook: Milnor, *Morse Theory*, §8
(8.4–8.5, the Riemannian / Levi-Civita connection) and §21 (Lie groups): a connection `D` is the
Levi-Civita connection of the metric iff it is symmetric, `D_X Y − D_Y X = [X, Y]`, and
compatible with the metric, `X⟨Y, Z⟩ = ⟨D_X Y, Z⟩ + ⟨Y, D_X Z⟩`, for all vector fields.
Choices: restricted to left-invariant fields, identified with the Lie algebra `L` (bracket
`⁅X, Y⁆`), with the (left-invariant) metric given by the bilinear form `B` on `L`; then `⟨Y, Z⟩`
is the constant function `B Y Z`, so `X⟨Y, Z⟩ = 0` and compatibility reads
`B (D X Y) Z + B Y (D X Z) = 0`. No condition on `B` (symmetry, positivity) is part of the
predicate: `B` being a left-invariant metric is the setting. -/
namespace RoundTrip.L2.Morse_IsLeviCivita

/-- The textbook notion: `D` is symmetric and compatible with the metric `B`. -/
def T {L : Type*} [LieRing L] [LieAlgebra ℝ L] (B : LinearMap.BilinForm ℝ L)
    (D : L →ₗ[ℝ] L →ₗ[ℝ] L) : Prop :=
  (∀ X Y : L, D X Y - D Y X = ⁅X, Y⁆) ∧ (∀ X Y Z : L, B (D X Y) Z + B Y (D X Z) = 0)

end RoundTrip.L2.Morse_IsLeviCivita
