import Morse
/-! Layer-2 blind definition of Morse_Homology_singularChains. Textbook: Hatcher, *Algebraic
Topology*, ch. 2.1 (singular chain complex): `C_n(X; R) = ⊕_{σ : Δⁿ → X} R` (one copy of the
coefficient object `R` for each singular `n`-simplex `σ`), with boundary
`∂σ = Σᵢ (-1)ⁱ σ ∘ dⁱ` (alternating sum of the faces), functorial in `X` by `f_♯ σ = f ∘ σ`.
Choices: coefficients in an object `R` of an abelian category `C` with coproducts (the direct sum
is the coproduct `∐_σ R`); this is exactly Mathlib's `AlgebraicTopology.singularChainComplexFunctor`
(the alternating face map complex of `R[Sing X]`, with `Sing X` the singular simplicial set),
evaluated at `R`. Chain complexes are `ℕ`-graded with the differential lowering degree. -/
namespace RoundTrip.L2.Morse_Homology_singularChains

open CategoryTheory Limits

universe w v u

/-- The textbook notion: the singular chain complex functor `X ↦ C_*(X; R)`. -/
noncomputable def T {C : Type u} [Category.{v} C] [Abelian C] [HasCoproducts.{w} C] (R : C) :
    TopCat.{w} ⥤ ChainComplex C ℕ :=
  (AlgebraicTopology.singularChainComplexFunctor C).obj R

end RoundTrip.L2.Morse_Homology_singularChains
