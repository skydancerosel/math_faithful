import Morse
import RoundTrip.L2.Blind.Morse_Homology_singularChains
namespace RoundTrip.L2.Morse_Homology_singularChains

open CategoryTheory Limits

universe w v u

/-- Both are Mathlib's singular chain complex functor at the coefficient object `R`. -/
theorem agree {C : Type u} [Category.{v} C] [Abelian C] [HasCoproducts.{w} C] (R : C) :
    Morse.Homology.singularChains.{w} R = T R := rfl

end RoundTrip.L2.Morse_Homology_singularChains
