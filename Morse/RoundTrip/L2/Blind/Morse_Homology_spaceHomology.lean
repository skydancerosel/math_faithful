import Morse
/-! Layer-2 blind definition of Morse_Homology_spaceHomology. Textbook: Milnor, *Morse Theory*,
§5, p. 27, and Hatcher, *Algebraic Topology*, ch. 2.1/3.1: the singular homology
`H_i(X; 𝕜) = H_i(C_*(X; 𝕜))` of the singular chain complex `C_n(X; 𝕜) = ⊕_{σ : Δⁿ → X} 𝕜`
(boundary = alternating sum of faces) of the space `X`, a `𝕜`-vector space.
Choices: Mathlib's singular homology `AlgebraicTopology.singularHomologyFunctor` in the category
`ModuleCat 𝕜`, with coefficient object `𝕜` itself (`ModuleCat.of 𝕜 𝕜`), evaluated at
`TopCat.of X`. No hypotheses needed (defined for every space and every `i : ℕ`). -/
namespace RoundTrip.L2.Morse_Homology_spaceHomology

open CategoryTheory

universe u

/-- The textbook notion: `H_i(X; 𝕜)`, the `i`-th singular homology of `X` with coefficients in
the field `𝕜`. -/
noncomputable def T (𝕜 : Type u) [Field 𝕜] (i : ℕ) (X : Type u) [TopologicalSpace X] :
    ModuleCat.{u} 𝕜 :=
  ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} 𝕜) i).obj
    (ModuleCat.of 𝕜 𝕜)).obj (TopCat.of X)

end RoundTrip.L2.Morse_Homology_spaceHomology
