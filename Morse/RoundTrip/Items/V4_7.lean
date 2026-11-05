import Morse
import RoundTrip.Check
import RoundTrip.Blind.V4_7

namespace RoundTrip.V4_7

/-- The project's statement: the five listed theorems (`focalMult` is a definition); no universe
parameters. -/
def A : Prop :=
  type_of% @Morse.focalMult_add_smul ∧
  type_of% @Morse.isFocalPoint_add_smul_iff ∧
  type_of% @Morse.focalMult_add_inv_smul ∧
  type_of% @Morse.sum_focalMult_add_smul_le ∧
  type_of% @Morse.map_nullSpace_firstFF_sub_eq_eigenspace

theorem A_holds : A :=
  ⟨@Morse.focalMult_add_smul, @Morse.isFocalPoint_add_smul_iff, @Morse.focalMult_add_inv_smul,
    @Morse.sum_focalMult_add_smul_le, @Morse.map_nullSpace_firstFF_sub_eq_eigenspace⟩

/-! Neither direction is proved; see the `.json` diagnosis. Both sides are Lemma 6.3, but about
different objects:

* A: in the project's own parametrization `xParam hM q` (no normalization `g = 1`), for any
  `v ⊥ T_qM` (not necessarily unit) the multiplicity of `q + t v` as a focal point, with the
  nullity of `dE` computed in the canonical slice structure `isSliceSubmanifold_normalBundle hM hkw`
  on `N`, is `0` for `t = 0` and `dim eigenspace(S_v, 1/t)` otherwise, `S_v` the shape operator on
  `T_qM`; hence the focal points on the line are the `q + K⁻¹ v`, `K ≠ 0` an eigenvalue, and their
  multiplicities over any finite set of `t` add up to at most `k`.
* B: for an arbitrary coordinate patch `x` of `M` with `g(u₀) = 1`, a unit normal `v`, `K_i` the
  eigenvalues of B's matrix `(v · ℓ_ij)` computed in `x`, and the nullity of `dE` computed in an
  arbitrary slice structure `hNN` on `N` with complement `ℝⁿ`.

A ⇒ B needs (1) that `x`'s matrix `(v · ℓ_ij)` (with `g = 1`) represents the project's shape
operator, i.e. that the normal part of `∂²x/∂uⁱ∂uʲ` does not depend on the parametrization
(the project states explicitly that this independence is "not needed and not proved"); and
(2) that the nullity of `dE` does not depend on the slice structure on `N`. Neither is in the
project; both are true. B ⇒ A fails: B says nothing about the project's canonical objects, about
non-unit `v`, about the eigenspace identification `map_nullSpace_firstFF_sub_eq_eigenspace`, or
about `k = 0` / `M ⊆ ℝ⁰`. The vocabulary agreement in one direction (`g = 1` in `xParam`) is
proved in `RoundTrip/Items/V4_6.lean` (`isPrincCurv_principalCurvatures`). -/

end RoundTrip.V4_7
