import Morse
/-! Layer-2 blind definition of Morse_IsMorsePatch. Textbook: Milnor, *Morse Theory*, Lemma 2.2
(Morse lemma chart) in its topological use (§3, p. 15): a homeomorphism `φ` from an open
neighbourhood `U` of `p` onto an open subset of `X × Y`, `φ(p) = 0`, with
`f = f(p) − ‖x‖² + ‖y‖²` on `U`, where `φ(u) = (x, y)`.
Choices: `φ` is an `OpenPartialHomeomorph` (open source `U`, open target, homeomorphism between
them); "neighbourhood of `p`" is `p ∈ φ.source`. The identity is required at every point of the
source. `‖·‖` is the given norm of `X`, `Y` (Milnor: `X = ℝ^λ`, `Y = ℝ^{n−λ}` Euclidean, so
`‖x‖² = (u¹)² + ⋯ + (u^λ)²`). No smoothness, no non-degeneracy hypothesis on `f` or `p`
(they are the setting of the Morse lemma, not part of the chart's defining property). -/
namespace RoundTrip.L2.Morse_IsMorsePatch

/-- The textbook notion: `φ` is a (topological) Morse chart of `f` centred at `p`. -/
def T {M : Type*} [TopologicalSpace M] {X : Type*} {Y : Type*} [NormedAddCommGroup X]
    [NormedAddCommGroup Y] (f : M → ℝ) (p : M) (φ : OpenPartialHomeomorph M (X × Y)) : Prop :=
  p ∈ φ.source ∧ φ p = 0 ∧
    ∀ u ∈ φ.source, f u = f p - ‖(φ u).1‖ ^ 2 + ‖(φ u).2‖ ^ 2

end RoundTrip.L2.Morse_IsMorsePatch
