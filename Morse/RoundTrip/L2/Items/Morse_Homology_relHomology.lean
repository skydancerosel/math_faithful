import Morse
import RoundTrip.L2.Blind.Morse_Homology_relHomology
namespace RoundTrip.L2.Morse_Homology_relHomology

open CategoryTheory Limits

universe w v u

/-- Both are `relChains ⋙ homologyFunctor n`, with the same relative chains functor. -/
theorem agree {C : Type u} [Category.{v} C] [Abelian C] [HasCoproducts.{w} C] (R : C) (n : ℕ) :
    Morse.Homology.relHomology.{w} R n = T R n := rfl

end RoundTrip.L2.Morse_Homology_relHomology
