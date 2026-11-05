import Morse
/-! Layer-2 blind definition of Morse_Homology_relChains. Textbook: Hatcher, *Algebraic
Topology*, ch. 2.1 (relative groups): for a pair `(X, A)`, `C_n(X, A; R) = C_n(X; R) / C_n(A; R)`,
the quotient of the singular chain complex of `X` by the subcomplex of chains in `A`, with the
induced boundary; a map of pairs `f : (X, A) → (Y, B)` induces `f_♯` on the quotients.
Choices: pairs are Mathlib's `TopPair` (an embedding `A ⟶ X` in `TopCat`; `P.fst = X`,
`P.snd = A`, `P.map : A ⟶ X`). Singular chains `C_*(-; R)` are Mathlib's
`AlgebraicTopology.singularChainComplexFunctor` at the coefficient object `R`. The quotient
`C(X)/C(A)` is the cokernel in `ChainComplex C ℕ` of the chain map `C(A) → C(X)` induced by the
inclusion (a monomorphism, so the cokernel is the textbook quotient, computed degreewise); on
morphisms of pairs the functor is the induced map of cokernels (Mathlib's `Limits.coker` applied
to the arrow `C(A) → C(X)`). -/
namespace RoundTrip.L2.Morse_Homology_relChains

open CategoryTheory Limits

universe w v u

variable {C : Type u} [Category.{v} C] [Abelian C] [HasCoproducts.{w} C]

/-- Singular chains `X ↦ C_*(X; R)`. -/
noncomputable def chains (R : C) : TopCat.{w} ⥤ ChainComplex C ℕ :=
  (AlgebraicTopology.singularChainComplexFunctor C).obj R

/-- The textbook notion: `(X, A) ↦ C_*(X; R) / C_*(A; R)` (cokernel of `C(A) → C(X)`). -/
noncomputable def T (R : C) : TopPair.{w} ⥤ ChainComplex C ℕ :=
  MorphismProperty.Arrow.forget _ _ _ ⋙ (chains R).mapArrow ⋙ Limits.coker _

/-- Sanity check: on objects, `T R` is the cokernel of `C(A) → C(X)`. -/
example (R : C) (P : TopPair.{w}) : (T R).obj P = cokernel ((chains R).map P.map) := rfl

end RoundTrip.L2.Morse_Homology_relChains
