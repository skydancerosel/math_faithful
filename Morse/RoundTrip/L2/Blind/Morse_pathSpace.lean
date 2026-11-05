import Morse
/-! Layer-2 blind definition of Morse_pathSpace. Textbook: Milnor, *Morse Theory*, §§12-13,
p. 67: `Ω(M; p, q)` is the set of piecewise smooth paths `ω : [0, 1] → M` with `ω(0) = p` and
`ω(1) = q`.
Choices: a path is a map `ω : ℝ → V` of which only the values on `[0, 1]` are constrained (values
off `[0, 1]` are arbitrary, so each textbook path has many representatives in the set).
Piecewise smooth is defined from scratch (as in the layer-2 blind file of
`Morse_IsPiecewiseSmooth`): continuous on `[0, 1]` and `C^∞` (`ContDiffOn`, one-sided
derivatives at the ends) on each closed piece of a subdivision `0 = t₀ < ⋯ < t_k = 1`.
`ω([0, 1]) ⊆ N`. -/
namespace RoundTrip.L2.Morse_pathSpace

open scoped ContDiff
open Set

/-- `c` is piecewise smooth on `[a, b]`. -/
def IsPiecewiseSmooth {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] (c : ℝ → V)
    (a b : ℝ) : Prop :=
  ContinuousOn c (Icc a b) ∧
    ∃ k : ℕ, ∃ t : Fin (k + 1) → ℝ, StrictMono t ∧ t 0 = a ∧ t (Fin.last k) = b ∧
      ∀ i : Fin k, ContDiffOn ℝ ∞ c (Icc (t i.castSucc) (t i.succ))

/-- The textbook notion: `Ω(N; p, q)`. -/
def T {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] (N : Set V) (p q : V) :
    Set (ℝ → V) :=
  {σ | IsPiecewiseSmooth σ 0 1 ∧ MapsTo σ (Icc 0 1) N ∧ σ 0 = p ∧ σ 1 = q}

end RoundTrip.L2.Morse_pathSpace
