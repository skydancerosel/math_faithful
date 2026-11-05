import Morse
import RoundTrip.L2.Blind.Morse_Homology_relChains
namespace RoundTrip.L2.Morse_Homology_relChains

open CategoryTheory Limits

universe w v u

/-- On objects both are `cokernel (C(A) ⟶ C(X))`; on maps of pairs both are the map
`(coker _).map` of cokernels induced by the square. -/
theorem agree {C : Type u} [Category.{v} C] [Abelian C] [HasCoproducts.{w} C] (R : C) :
    Morse.Homology.relChains.{w} R = T R := rfl

end RoundTrip.L2.Morse_Homology_relChains
