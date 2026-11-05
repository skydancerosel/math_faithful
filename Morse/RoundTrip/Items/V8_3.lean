import Morse
import RoundTrip.Check
import RoundTrip.Blind.«V8_3»

namespace RoundTrip.«V8_3»

/-- The project's statement (universes instantiated at 0): Lemma 11.A for a slice submanifold
`N ⊆ V` with the induced metric (completeness not assumed): for `ω ∈ Ω(N; p, q)` and a piecewise
smooth family `Λ(t) : P →L V` of tangent-valued linear maps with `Λ(0) = Λ(1) = 0`, for some
`ε > 0` Milnor's formula `α(u, t) = exp_{ω(t)}(Λ(t) u)` is a variation on `ball 0 ε ⊆ P` (with a
finite break set), `α(0, t) = ω(t)` and `∂α/∂u (0, t) = Λ(t)` on `[0, 1]`; the one-field case
`exp_{ω(t)}(u W(t))`, `|u| < ε`, with `varField = W` on `[0, 1]`; and the two-field case
`exp_{ω(t)}(u₁ W₁(t) + u₂ W₂(t))` with partial derivatives `W₁`, `W₂` on `[0, 1]`. -/
def A : Prop :=
  type_of% @Morse.exists_variation.{0,0,0,0} ∧
    type_of% @Morse.exists_variation_one.{0,0,0} ∧
    type_of% @Morse.exists_variation_two.{0,0,0}

theorem A_holds : A :=
  ⟨@Morse.exists_variation, @Morse.exists_variation_one, @Morse.exists_variation_two⟩

/-! No direction is proved; see `V8_3.json`. -/

end RoundTrip.«V8_3»
