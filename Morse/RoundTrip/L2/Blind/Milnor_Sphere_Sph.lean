import Morse
/-! Layer-2 blind definition of Milnor_Sphere_Sph. Textbook: Milnor, *Morse Theory*, §1/§5
(standard): the unit `n`-sphere `Sⁿ = {x ∈ ℝⁿ⁺¹ : |x| = 1}`.
Choices: `ℝⁿ⁺¹` is `EuclideanSpace ℝ (Fin (n + 1))` with its Euclidean norm `|x| = √(Σ xᵢ²)`;
the sphere is the plain subset (no manifold structure). -/
namespace RoundTrip.L2.Milnor_Sphere_Sph

/-- The textbook notion: the unit sphere of Euclidean `(n+1)`-space. -/
def T (n : ℕ) : Set (EuclideanSpace ℝ (Fin (n + 1))) :=
  {x | ‖x‖ = 1}

end RoundTrip.L2.Milnor_Sphere_Sph
