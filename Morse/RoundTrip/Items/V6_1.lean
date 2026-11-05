import Morse
import RoundTrip.Check
import RoundTrip.Blind.V6_1

open scoped Manifold

namespace RoundTrip.V6_1

/-- The project's statement (universes instantiated at 0; `tangentSubspace`, `tanProj`, `dN`,
`IsTangentField`, `projField` are definitions): the derivative `dN` of a map on a slice
submanifold `N ⊆ V` along a tangent vector is the ambient derivative of any local extension;
`q ↦ P_q` (orthogonal projection onto `T_qN`) is smooth; `P_q u = u` for `u ∈ T_qN`. -/
def A : Prop :=
  type_of% @Morse.dN_eq_fderiv.{0,0,0,0} ∧ type_of% @Morse.contMDiff_tanProj.{0,0,0} ∧
    type_of% @Morse.projField_apply_of_mem.{0,0,0}

theorem A_holds : A := ⟨@Morse.dN_eq_fderiv, @Morse.contMDiff_tanProj, @Morse.projField_apply_of_mem⟩

/-- Vocabulary check: B's `P_q` (`starProjection` onto `Milnor.Tub.tanN`) is the project's
`tanProj` (both are the orthogonal projection onto the range of `mfd val`). -/
example {K d m : ℕ} {M : Set (Rn (K + 1))}
    (hM : Milnor.IsSliceSubmanifold 𝓘(ℝ, Rn (K + 1)) (Rn (d + 1)) (Rn m) M) (q : M) (v : Rn (K + 1)) :
    (Milnor.Tub.tanN hM q).starProjection v = Morse.tanProj hM q v := rfl

end RoundTrip.V6_1
