import Morse
import RoundTrip.Check
import RoundTrip.Blind.V2_9

open scoped ContDiff Manifold Topology

namespace RoundTrip.V2_9

/-- The project's statement: Remark 3.3 for a slice submanifold of a finite-dimensional normed
space (strong deformation retraction onto `N^{c-ε} ∪ ⋃ e_p` inside `N`), together with the
general-topology lemma turning disjoint embedded cells into iterated adjunction spaces.
Universes instantiated at `0`. -/
def A : Prop :=
  type_of% @Morse.remark_3_3_submanifold.{0, 0, 0} ∧
  type_of% @Morse.isFiniteCellComplexType_union_cells.{0, 0}

theorem A_holds : A :=
  ⟨@Morse.remark_3_3_submanifold.{0, 0, 0}, @Morse.isFiniteCellComplexType_union_cells.{0, 0}⟩

/-! Neither direction is proved; see `V2_9.json`.
* `A → B`: `A` only treats manifolds given as slice submanifolds of a normed space, while `B`
  quantifies over abstract (Hausdorff, finite-dimensional, but not second-countable) manifolds;
  passing from one to the other needs an embedding theorem (Whitney), which is not available.
* `B → A`: `B` only gives an abstract homotopy equivalence with some iterated adjunction space,
  while `A`'s first conjunct asserts a strong deformation retraction onto an explicit subspace
  made of explicit embedded cells (pairwise disjoint, meeting `N^{c-ε}` in their boundary), and
  its second conjunct is a general-topology lemma about arbitrary Hausdorff spaces that has
  nothing to do with Morse functions. -/

end RoundTrip.V2_9
