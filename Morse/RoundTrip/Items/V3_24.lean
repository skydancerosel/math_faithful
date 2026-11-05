import Morse
import RoundTrip.Check
import RoundTrip.Blind.V3_24

open Module Morse Morse.Torus
open scoped ContDiff Manifold

namespace RoundTrip.V3_24

/-- The project's statement: the three listed theorems. -/
def A : Prop :=
  type_of% @Morse.Torus.sublevel_height_eq_empty ∧
  type_of% @Morse.Torus.sublevel_height_eq_univ ∧
  type_of% @Morse.theorem_3_1_torus

theorem A_holds : A :=
  ⟨@Morse.Torus.sublevel_height_eq_empty, @Morse.Torus.sublevel_height_eq_univ,
    @Morse.theorem_3_1_torus⟩

/-- Vocabulary: B's `M^a` is the image in `ℝ³` of the project's sublevel set of `height ∘ val`. -/
theorem sub_eq (R r a : ℝ) :
    sub R r a = Subtype.val '' sublevel (height R r ∘ (Subtype.val : Morse.torus R r → Rn 3)) a := by
  ext x
  constructor
  · rintro ⟨hx, ha⟩
    exact ⟨⟨x, hx⟩, ha, rfl⟩
  · rintro ⟨⟨x, hx⟩, ha, rfl⟩
    exact ⟨hx, ha⟩

/-! Neither direction is proved. The shared clauses (1) and (5) transfer through `sub_eq`, but
B's clauses (2)–(4), that `M^a` is homeomorphic to a closed 2-disk, to `S¹ × [0,1]`, and to the
torus minus an open embedded disk, are not in A (which only has Theorem 3.1 between critical
levels); and A's `theorem_3_1_torus` (a diffeomorphism of `T` carrying `T^a` to `T^b`, a strong
deformation retraction, a homotopy equivalence) is not in B. -/

end RoundTrip.V3_24
