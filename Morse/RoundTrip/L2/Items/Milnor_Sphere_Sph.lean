import Morse
import RoundTrip.L2.Blind.Milnor_Sphere_Sph

/-! Layer-2 check of `Milnor.Sphere.Sph` (the level set `{x | ⟪x, x⟫ - 1 = 0}`) against the blind
textbook definition (the plain set `{x | ‖x‖ = 1}` in `ℝⁿ⁺¹`): equal, by the project's
`Milnor.Sphere.mem_iff_norm`. -/

namespace RoundTrip.L2.Milnor_Sphere_Sph

theorem agree (n : ℕ) : Milnor.Sphere.Sph n = T n :=
  Set.ext fun _ => Milnor.Sphere.mem_iff_norm

end RoundTrip.L2.Milnor_Sphere_Sph
