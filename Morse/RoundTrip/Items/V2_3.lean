import Morse
import RoundTrip.Check
import RoundTrip.Blind.V2_3

namespace RoundTrip.V2_3

/-- The project's statement: the types of the listed theorems (Theorem 3.1 for `f = F|N`, `N` a
slice submanifold of a finite-dimensional normed space `V`), universes instantiated at `0`. -/
def A : Prop :=
  (type_of% @Morse.theorem_3_1_submanifold.{0, 0, 0}) ∧
  (type_of% @Morse.theorem_3_1_submanifold_of_isCompact.{0, 0, 0}) ∧
  (type_of% @Morse.flow_mem_of_tangent.{0, 0, 0})

theorem A_holds : A :=
  ⟨@Morse.theorem_3_1_submanifold.{0, 0, 0}, @Morse.theorem_3_1_submanifold_of_isCompact.{0, 0, 0},
    @Morse.flow_mem_of_tangent.{0, 0, 0}⟩

/-! Neither direction is proved. `A ⇒ B` fails: `A` covers only functions `F|N` restricted from
the ambient space to a slice submanifold `N ⊆ V`; an abstract manifold `M` would first have to be
embedded (and `f` extended), which is not in `A`. `B ⇒ A` fails: `A` concludes an ambient
diffeomorphism `Φ : N ≃ N` with `Φ '' N^a = N^b` (`B` only gives maps between sublevel sets that
are smooth on them), and `flow_mem_of_tangent` (flows of tangent fields stay in `N`) has no
counterpart in `B`; moreover `B` speaks of `ChartedSpace` manifolds while `N` is a subset with a
slice-chart structure. -/

end RoundTrip.V2_3
