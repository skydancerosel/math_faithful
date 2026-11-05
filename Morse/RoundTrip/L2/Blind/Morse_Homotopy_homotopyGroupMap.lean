import Morse
/-! Layer-2 blind definition of Morse_Homotopy_homotopyGroupMap. Textbook: Hatcher, *Algebraic
Topology*, ch. 4.1, and Milnor, *Morse Theory*, §17: a based map `f : (X, x) → (Y, f x)` induces
`f_* : π_n(X, x) → π_n(Y, f x)`, `[γ] ↦ [f ∘ γ]`.
Choices: homotopy groups are Mathlib's `HomotopyGroup N X x` (classes of generalized loops
`γ : (I^N, ∂I^N) → (X, x)` up to homotopy rel `∂I^N`); `f ∘ γ` is again such a loop based at
`f x`, and a homotopy rel `∂I^N` is carried to one by composing with `f`. Only the map of
underlying sets is required by the signature (it is a homomorphism for `N` nonempty, not
recorded). No hypothesis on `N` (for `N` empty this is the map on path components). -/
namespace RoundTrip.L2.Morse_Homotopy_homotopyGroupMap

open scoped Topology

/-- `f ∘ γ` for a generalized loop `γ : (I^N, ∂I^N) → (X, x)`. -/
def genLoopMap {N X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (f : C(X, Y)) {x : X}
    (γ : ↥(GenLoop N X x)) : ↥(GenLoop N Y (f x)) :=
  ⟨f.comp γ.1, fun y hy => by simp [GenLoop.boundary γ y hy]⟩

/-- The textbook notion: `f_* : π_N(X, x) → π_N(Y, f x)`, `[γ] ↦ [f ∘ γ]`. -/
def T {N X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (f : C(X, Y)) (x : X) :
    HomotopyGroup N X x → HomotopyGroup N Y (f x) :=
  Quotient.map' (genLoopMap f) (fun _ _ h => ContinuousMap.HomotopicRel.comp_continuousMap h f)

end RoundTrip.L2.Morse_Homotopy_homotopyGroupMap
