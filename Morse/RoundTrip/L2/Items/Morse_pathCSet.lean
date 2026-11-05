import Morse
import RoundTrip.L2.Blind.Morse_pathCSet
namespace RoundTrip.L2.Morse_pathCSet

/-- The project's `pathCSet` is literally the textbook set of continuous paths in `N` from `p` to
`q` (as a subset of `C([0,1], V)`). -/
theorem agree {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    (N : Set V) (p q : V) : Morse.pathCSet N p q = T N p q :=
  rfl

end RoundTrip.L2.Morse_pathCSet
