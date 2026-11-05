import Morse
import RoundTrip.Check
import RoundTrip.Blind.V4_3

open MeasureTheory
open scoped ContDiff Manifold

namespace RoundTrip.V4_3

/-- The project's statement: the two listed theorems, universes instantiated at `0`. -/
def A : Prop :=
  type_of% @Morse.measure_image_inter_critPoints_eq_zero.{0, 0, 0} ∧
  type_of% @Morse.measure_image_critPoints_eq_zero.{0, 0, 0}

theorem A_holds : A :=
  ⟨@Morse.measure_image_inter_critPoints_eq_zero.{0, 0, 0},
    @Morse.measure_image_critPoints_eq_zero.{0, 0, 0}⟩

/-! Neither direction is proved; see the `.json` diagnosis.

* A ⇒ B fails on regularity: A is Sard's theorem for **smooth** (`C^∞`) maps (on an open set `U`)
  into a finite-dimensional **vector space** `F`, any dimensions, any Haar measure. B is Milnor's
  `C¹` statement between manifolds of the same dimension. The manifold target alone is harmless
  (read `f` in a chart of `M₂`, on the open set `f⁻¹(chart)`, with A's `U`-version), but `C¹` is
  not: A has nothing below `C^∞`, and the `C¹` equal-dimension Sard theorem is not in the project.
* B ⇒ A fails on dimensions: B only concerns `dim M₁ = dim M₂`; A covers `dim M > dim F` (the
  genuinely harder case of Sard) and `dim M < dim F`, and manifolds modelled on any `H` with a
  boundaryless model.
-/

end RoundTrip.V4_3
