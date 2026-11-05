import Morse
/-! Layer-2 blind definition of Morse_Homology_bettiNumber. Textbook: Milnor, *Morse Theory*,
§5, p. 28: the `i`-th Betti number `R_i(X) = b_i(X)` is the rank (= dimension over the field
`𝕜`) of the `i`-th singular homology vector space `H_i(X; 𝕜)`.
Choices: `H_i(X; 𝕜)` is Mathlib's singular homology (`AlgebraicTopology.singularHomologyFunctor`
in `ModuleCat 𝕜`, coefficient object `𝕜`), defined here from scratch (not via the project's
homology); the dimension is `Module.finrank`. Encoding: Milnor uses `b_i` only when it is finite
(e.g. compact manifolds); when `H_i(X; 𝕜)` is infinite-dimensional the result type `ℕ` cannot
hold `∞`, and `finrank` gives `0` (junk value). -/
namespace RoundTrip.L2.Morse_Homology_bettiNumber

open CategoryTheory

universe u

/-- `H_i(X; 𝕜)`: singular homology of `X` with coefficients in `𝕜`. -/
noncomputable def singH (𝕜 : Type u) [Field 𝕜] (X : Type u) [TopologicalSpace X] (i : ℕ) :
    ModuleCat.{u} 𝕜 :=
  ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} 𝕜) i).obj
    (ModuleCat.of 𝕜 𝕜)).obj (TopCat.of X)

/-- The textbook notion: the Betti number `b_i(X) = dim_𝕜 H_i(X; 𝕜)` (`0` if infinite). -/
noncomputable def T (𝕜 : Type u) [Field 𝕜] (X : Type u) [TopologicalSpace X] (i : ℕ) : ℕ :=
  Module.finrank 𝕜 (singH 𝕜 X i)

end RoundTrip.L2.Morse_Homology_bettiNumber
