import Morse
import RoundTrip.Check
import RoundTrip.Blind.V3_34

open CategoryTheory Morse Morse.Homology Module Finset
open scoped ContDiff Manifold

namespace RoundTrip.V3_34

/-- The project's statement: the eight listed theorems, universes instantiated at `0`. -/
def A : Prop :=
  type_of% @Morse.exists_separating_seq ∧
  type_of% @Morse.isCriticalPointM_of_forall_ge.{0, 0} ∧
  type_of% @Morse.Homology.sublevel_step_critical.{0, 0, 0, 0} ∧
  type_of% @Morse.Homology.sublevel_step.{0, 0, 0, 0} ∧
  type_of% @Morse.Homology.exists_morse_filtration.{0, 0, 0, 0} ∧
  type_of% @Morse.Homology.exists_cells_filtration.{0, 0, 0, 0} ∧
  type_of% @Morse.Homology.critCount_eq_card.{0, 0, 0} ∧
  type_of% @Morse.Homology.finiteDimensional_spaceHomology.{0, 0, 0, 0}

theorem A_holds : A :=
  ⟨@Morse.exists_separating_seq, @Morse.isCriticalPointM_of_forall_ge.{0, 0},
    @Morse.Homology.sublevel_step_critical.{0, 0, 0, 0}, @Morse.Homology.sublevel_step.{0, 0, 0, 0},
    @Morse.Homology.exists_morse_filtration.{0, 0, 0, 0},
    @Morse.Homology.exists_cells_filtration.{0, 0, 0, 0},
    @Morse.Homology.critCount_eq_card.{0, 0, 0},
    @Morse.Homology.finiteDimensional_spaceHomology.{0, 0, 0, 0}⟩

/-! Neither direction is proved; see the `.json` diagnosis.

* A ⇒ B: A's slab computations (`sublevel_step`, `sublevel_step_critical`) require the two ends
  `a' < a` of a slab to be **regular** values (`F q ≠ a'`, `F q ≠ a` for critical `q`, resp.
  `a' < c < a` with no other critical value in `[a', a]`). B's `MorseFilt` only asks that
  `M^{a_i}` contain exactly the critical points `p_0, …, p_{i-1}`; this allows
  `a_i = f(p_{i-1})`, a critical value. For such a filtration B's claim
  `H_*(M^{a_{i+1}}, M^{a_i}) ≅ F[λ_i]` needs `H_*(M^{c+δ}, M^c) = 0` at a critical level `c`
  (Remark 3.4 on a manifold), which the project proves only for `M = E` a vector space
  (`Morse.isStrongDeformationRetract_sublevel_crit`), not for submanifolds or abstract
  manifolds. With regular ends the Whitney transport (`Glue.exists_ambient_any_dim`-style, with
  `G ∘ Φ = f`) and `sublevel_step` would suffice.
* B ⇒ A: B is vacuous when two critical points share a critical value (no `MorseFilt` exists),
  while A's `sublevel_step` / `exists_morse_filtration` handle any number of critical points on a
  level; B also asserts no existence of a filtration, no finite-dimensionality of `H_*(N)`, and
  has no counterpart of the real-number lemma `exists_separating_seq` or of
  `isCriticalPointM_of_forall_ge`.
-/

end RoundTrip.V3_34
