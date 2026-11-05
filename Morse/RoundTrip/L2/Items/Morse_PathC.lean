import Morse
import RoundTrip.L2.Blind.Morse_PathC
namespace RoundTrip.L2.Morse_PathC

/-- The project's `PathC` and the textbook `Ω*` are the same type (same underlying set of
`C([0,1], V)`). -/
theorem agree_type {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] (N : Set V) (p q : V) :
    Morse.pathCSet N p q = S N p q ∧ Morse.PathC N p q = T N p q :=
  ⟨rfl, rfl⟩

/-- **Agreement as spaces**: the identity is a homeomorphism (both carry the subspace topology of
the compact-open topology of `C([0,1], V)`). -/
def agree {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    (N : Set V) (p q : V) : Morse.PathC N p q ≃ₜ T N p q :=
  Homeomorph.refl _

/-- The homeomorphism is the identity on the underlying paths. -/
theorem agree_apply {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] (N : Set V) (p q : V) (ω : Morse.PathC N p q) :
    (show ↥(S N p q) from agree N p q ω).1 = ω.1 := rfl

end RoundTrip.L2.Morse_PathC
