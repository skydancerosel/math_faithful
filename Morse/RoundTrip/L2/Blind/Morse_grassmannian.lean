import Morse
/-! Layer-2 blind definition of Morse_grassmannian. Textbook: Milnor, *Morse Theory*, §§23–24,
p. 133: the complex Grassmann manifold `G_m(ℂⁿ)` of `m`-dimensional complex linear subspaces of
`ℂⁿ`.
Choices: realised inside `M_n(ℂ)` (subspace topology) by identifying a subspace `V ⊆ ℂⁿ` with the
orthogonal projection onto it (for the standard Hermitian product of `ℂⁿ = ι → ℂ`): the matrices
`P` with `P* = P`, `P² = P` and `rank P = dim_ℂ (image P) = m`; this is a bijection between
`m`-dimensional subspaces and such `P`. For `m > n` the set is empty. -/
namespace RoundTrip.L2.Morse_grassmannian

open scoped Matrix

/-- The textbook notion: orthogonal projections of `ℂ^ι` onto `m`-dimensional subspaces. -/
def T (ι : Type*) [Fintype ι] [DecidableEq ι] (m : ℕ) : Set (Matrix ι ι ℂ) :=
  {P | Pᴴ = P ∧ P * P = P ∧ P.rank = m}

end RoundTrip.L2.Morse_grassmannian
