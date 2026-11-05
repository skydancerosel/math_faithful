import Morse
/-! Layer-2 blind definition of Morse_IsOrthComplexStructure. Textbook: Milnor, *Morse Theory*,
§24, p. 133 (and §7): a complex structure on a Euclidean space `V` is an orthogonal linear map `J`
with `J² = −1` (multiplication by `i`).
Choices: "orthogonal" = preserves the inner product, `⟨Jx, Jy⟩ = ⟨x, y⟩` (surjectivity is not
added: `J² = −1` makes `J` invertible with inverse `−J`). `J² = −1` is stated pointwise,
`J (J x) = −x`. No finite-dimensionality is assumed. -/
namespace RoundTrip.L2.Morse_IsOrthComplexStructure

/-- The textbook notion: `J` preserves the inner product and `J ∘ J = −id`. -/
def T {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] (J : V →L[ℝ] V) : Prop :=
  (∀ x y : V, inner ℝ (J x) (J y) = inner ℝ x y) ∧ ∀ x : V, J (J x) = -x

end RoundTrip.L2.Morse_IsOrthComplexStructure
