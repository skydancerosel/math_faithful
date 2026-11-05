import Morse
import RoundTrip.Check
import RoundTrip.Blind.«V7_30′»

namespace RoundTrip.«V7_30′»

/-- The project's statement (universes instantiated at 0 where present; the sphere lemmas are
universe-free): for the round sphere `Sⁿ ⊆ ℝⁿ⁺¹` (`sphSub n`, induced metric) great circles
`t ↦ cos(Lt) p + sin(Lt) u` (`u ⊥ p` unit) are geodesics on `ℝ`; for `n ≥ 1` every unbroken
geodesic in `Ω(Sⁿ; p, q)` agrees on `[0, 1]` with a great circle from `p` (speed `L ≥ 0`), and,
for `q ≠ ±p`, with one of the geodesics `sphGeod p q k`, whose energies strictly increase in `k`;
for a codimension-0 slice submanifold `N` (every `T_qN = V`, e.g. open subsets of `V`), if the
segment `[p, q]` lies in `N` it is a geodesic in `Ω(N; p, q)` and the only one. -/
def A : Prop :=
  type_of% @Morse.isGeodesicOn_greatCircle ∧
    type_of% @Morse.exists_eqOn_greatCircle ∧
    type_of% @Morse.exists_eqOn_sphGeod ∧
    type_of% @Morse.strictMono_energy_sphGeod ∧
    type_of% @Morse.unique_geodesic_of_top.{0,0,0}

theorem A_holds : A :=
  ⟨@Morse.isGeodesicOn_greatCircle, @Morse.exists_eqOn_greatCircle, @Morse.exists_eqOn_sphGeod,
    @Morse.strictMono_energy_sphGeod, @Morse.unique_geodesic_of_top⟩

/-! No direction is proved; see `V7_30′.json`. B is stated for abstract Riemannian manifolds `M`
(any Levi-Civita `CovariantDerivative`) given with a bijective isometric immersion `f` onto `ℝⁿ`,
`Sⁿ`, the cylinder, or a surface of revolution; A is stated for the concrete sets `Sⁿ ⊆ ℝⁿ⁺¹` and
codimension-0 `N ⊆ V` with the induced connection. B has the cylinder, surfaces of revolution,
the converse "every great-circle motion is a geodesic on any interval" and the counts of
minimal/non-minimal geodesics; A has the energy monotonicity of `sphGeod` and uniqueness of the
segment in arbitrary (e.g. non-convex open) codimension-0 `N`. -/

end RoundTrip.«V7_30′»
