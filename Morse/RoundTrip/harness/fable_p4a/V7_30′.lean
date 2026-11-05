import Morse
import RoundTrip.Check
import RoundTrip.Blind.«V7_30′»

namespace RoundTrip.«V7_30′»

/-- The project's statement (universes instantiated at 0 where there are any): on the round
sphere `Sⁿ ⊆ ℝⁿ⁺¹` (a slice submanifold with the induced metric) great circles are geodesics;
for `n ≥ 1` every geodesic `γ ∈ Ω(Sⁿ; p, q)` is a great circle `cos(Lt) p + sin(Lt) u` on `[0, 1]`;
for `q ≠ ±p` it is one of the `sphGeod p q k`, whose energies increase strictly in `k`; and in a
submanifold `N ⊆ V` of codimension `0` a segment lying in `N` is the unique geodesic of
`Ω(N; p, q)`. -/
def A : Prop :=
  type_of% @Morse.isGeodesicOn_greatCircle ∧
    type_of% @Morse.exists_eqOn_greatCircle ∧
    type_of% @Morse.exists_eqOn_sphGeod ∧
    type_of% @Morse.strictMono_energy_sphGeod ∧
    type_of% @Morse.unique_geodesic_of_top.{0,0,0}

theorem A_holds : A :=
  ⟨@Morse.isGeodesicOn_greatCircle, @Morse.exists_eqOn_greatCircle, @Morse.exists_eqOn_sphGeod,
    @Morse.strictMono_energy_sphGeod, @Morse.unique_geodesic_of_top⟩

/-! No direction is proved; see `V7_30′.json`. -/

end RoundTrip.«V7_30′»
