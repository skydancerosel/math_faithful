import Morse
/-! Layer-2 blind definition of Morse_IsSplitMorseChart. Textbook: Milnor, *Morse Theory*, §2,
Lemma 2.2, p. 6 (Morse coordinates): a local coordinate system `(u¹,…,uⁿ)` on a neighbourhood
`U` of `p` with `uⁱ(p) = 0` and `f = f(p) − (u¹)² − ⋯ − (u^λ)² + (u^{λ+1})² + ⋯ + (uⁿ)²`
throughout `U`.
Choices: the coordinates are split as `φ(u) = (x, y) ∈ X × Y` (Milnor: `X = ℝ^λ`, `Y = ℝ^{n−λ}`;
for inner product spaces `‖x‖² = Σ (uⁱ)²` in orthonormal coordinates), so the formula reads
`f = f(p) − ‖x‖² + ‖y‖²`. "Local coordinate system" on the vector space `E` = a `C^∞`
diffeomorphism from the open set `φ.source` onto the open set `φ.target` (`φ` and `φ.symm` are
`C^∞` on source/target); "centred" = `p ∈ φ.source ∧ φ p = 0`. The formula is required at every
point of `φ.source`. Hypotheses of Lemma 2.2 (`f` smooth, `p` a non-degenerate critical point of
index `λ = dim X`) are not part of the definition (they follow from the formula in finite
dimension); no finite-dimensionality is imposed on `X`, `Y`, `E`. -/
namespace RoundTrip.L2.Morse_IsSplitMorseChart

open scoped ContDiff

/-- The textbook notion: `φ` is a smooth Morse coordinate chart for `f` centred at `p`. -/
def T {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {X : Type*} {Y : Type*}
    [NormedAddCommGroup X] [InnerProductSpace ℝ X] [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]
    (f : E → ℝ) (p : E) (φ : OpenPartialHomeomorph E (X × Y)) : Prop :=
  ContDiffOn ℝ ∞ φ φ.source ∧ ContDiffOn ℝ ∞ φ.symm φ.target ∧
    p ∈ φ.source ∧ φ p = 0 ∧
    ∀ u ∈ φ.source, f u = f p - ‖(φ u).1‖ ^ 2 + ‖(φ u).2‖ ^ 2

end RoundTrip.L2.Morse_IsSplitMorseChart
