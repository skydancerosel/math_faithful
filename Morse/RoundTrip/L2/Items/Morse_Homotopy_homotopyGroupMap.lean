import Morse
import RoundTrip.L2.Blind.Morse_Homotopy_homotopyGroupMap
namespace RoundTrip.L2.Morse_Homotopy_homotopyGroupMap

/-- Both send `[γ]` to `[f ∘ γ]`. -/
theorem agree {N X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (f : C(X, Y)) (x : X) :
    Morse.Homotopy.homotopyGroupMap (N := N) f x = T f x := rfl

end RoundTrip.L2.Morse_Homotopy_homotopyGroupMap
