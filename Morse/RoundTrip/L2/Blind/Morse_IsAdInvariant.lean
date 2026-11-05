import Morse
/-! Layer-2 blind definition of Morse_IsAdInvariant. Textbook: Milnor, *Morse Theory*, §21,
Lemma 21.3(a), p. 123: a (left-invariant) metric on a Lie group is bi-invariant iff the inner
product on the Lie algebra satisfies `⟨[X, Y], Z⟩ = ⟨X, [Y, Z]⟩` for all `X, Y, Z ∈ 𝔤` (equivalently
every `ad Y` is skew-adjoint).
Choices: stated for an arbitrary real bilinear form `B` on the real Lie algebra `L` (no symmetry or
positivity required: those are separate properties of an inner product, not part of
ad-invariance). The bracket is the Lie bracket of `L`. -/
namespace RoundTrip.L2.Morse_IsAdInvariant

/-- The textbook notion: `B([X, Y], Z) = B(X, [Y, Z])` for all `X, Y, Z`. -/
def T {L : Type*} [LieRing L] [LieAlgebra ℝ L] (B : LinearMap.BilinForm ℝ L) : Prop :=
  ∀ X Y Z : L, B ⁅X, Y⁆ Z = B X ⁅Y, Z⁆

end RoundTrip.L2.Morse_IsAdInvariant
