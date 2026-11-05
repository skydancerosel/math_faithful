import Morse
import RoundTrip.Check
import RoundTrip.Blind.V8_3

namespace RoundTrip.«V8_3»

/-- The project's statement (universes instantiated at 0): Lemma 11.A in the embedded setting.
For `ω ∈ Ω(N; p, q)` and a piecewise smooth family of linear maps `Λ(t) : P → T_{ω(t)}N` with
`Λ(0) = Λ(1) = 0` (any normed parameter space `P`), `α(u, t) = exp_{ω(t)}(Λ(t) u)` is a variation
of `ω` on a ball `‖u‖ < ε` with `∂α/∂u(0, t) = Λ(t)`; the one-field form (`u • W(t)`, `|u| < ε`,
variation field `W`) and the two-field form (`u₁ W₁(t) + u₂ W₂(t)`, partial derivatives
`W₁`, `W₂`). -/
def A : Prop :=
  type_of% @Morse.exists_variation.{0,0,0,0} ∧
    type_of% @Morse.exists_variation_one.{0,0,0} ∧
    type_of% @Morse.exists_variation_two.{0,0,0}

theorem A_holds : A :=
  ⟨@Morse.exists_variation, @Morse.exists_variation_one, @Morse.exists_variation_two⟩

/-! No direction is proved; see `V8_3.json`. -/

end RoundTrip.«V8_3»
