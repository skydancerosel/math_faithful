import Morse
import RoundTrip.Check
import RoundTrip.Blind.V1_10

open scoped ContDiff Manifold Topology

namespace RoundTrip.V1_10

/-- The project's statement, universes instantiated at `0`. -/
def A : Prop :=
  type_of% @Morse.IsNondegenerateCriticalPoint.exists_nhds_isCriticalPoint_eq.{0} ∧
  type_of% @Morse.IsNondegenerateCriticalPointM.exists_nhds_isCriticalPointM_eq.{0, 0}

theorem A_holds : A :=
  ⟨@Morse.IsNondegenerateCriticalPoint.exists_nhds_isCriticalPoint_eq.{0},
   @Morse.IsNondegenerateCriticalPointM.exists_nhds_isCriticalPointM_eq.{0, 0}⟩

theorem A_to_B : A → B := by
  intro hA E _ _ _ M _ _ _ _ f p hf hp
  obtain ⟨U, hU, h⟩ := hA.2 (hf.contMDiffAt.of_le (WithTop.coe_le_coe.2 le_top)) hp
  exact ⟨U, hU, fun q hq hc => (h q hq).1 hc⟩

#rt_check RoundTrip.V1_10.A_to_B [Morse.IsNondegenerateCriticalPoint.exists_nhds_isCriticalPoint_eq,
  Morse.IsNondegenerateCriticalPointM.exists_nhds_isCriticalPointM_eq]

end RoundTrip.V1_10
