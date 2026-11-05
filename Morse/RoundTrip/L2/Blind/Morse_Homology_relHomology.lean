import Morse
/-! Layer-2 blind definition of Morse_Homology_relHomology. Textbook: Milnor, *Morse Theory*,
§3/§5, pp. 27-28, and Hatcher, *Algebraic Topology*, ch. 2.1: `H_n(X, A; R)` is the `n`-th
homology of the relative singular chain complex `C_*(X; R) / C_*(A; R)`; functorial in maps of
pairs.
Choices: pairs are Mathlib's `TopPair` (an embedding `A ⟶ X`; `P.fst = X`, `P.snd = A`).
`C_*(-; R)` is Mathlib's `AlgebraicTopology.singularChainComplexFunctor` at the coefficient object
`R`; the quotient complex is the cokernel in `ChainComplex C ℕ` of the (mono) chain map
`C(A) → C(X)` (Mathlib's `Limits.coker` on the arrow), defined here from scratch; `H_n` is
Mathlib's `HomologicalComplex.homologyFunctor` in degree `n`. -/
namespace RoundTrip.L2.Morse_Homology_relHomology

open CategoryTheory Limits

universe w v u

variable {C : Type u} [Category.{v} C] [Abelian C] [HasCoproducts.{w} C]

/-- Singular chains `X ↦ C_*(X; R)`. -/
noncomputable def chains (R : C) : TopCat.{w} ⥤ ChainComplex C ℕ :=
  (AlgebraicTopology.singularChainComplexFunctor C).obj R

/-- Relative singular chains `(X, A) ↦ C_*(X; R) / C_*(A; R)`. -/
noncomputable def relCh (R : C) : TopPair.{w} ⥤ ChainComplex C ℕ :=
  MorphismProperty.Arrow.forget _ _ _ ⋙ (chains R).mapArrow ⋙ Limits.coker _

/-- The textbook notion: `(X, A) ↦ H_n(X, A; R) = H_n(C_*(X; R) / C_*(A; R))`. -/
noncomputable def T (R : C) (n : ℕ) : TopPair.{w} ⥤ C :=
  relCh R ⋙ HomologicalComplex.homologyFunctor C (ComplexShape.down ℕ) n

end RoundTrip.L2.Morse_Homology_relHomology
