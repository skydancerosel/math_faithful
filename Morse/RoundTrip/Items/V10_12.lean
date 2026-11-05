import Morse
import RoundTrip.Check
import RoundTrip.Blind.V10_12

open Set Filter Topology
open scoped ContDiff Manifold

namespace RoundTrip.V10_12

/-- The project's statement (universes instantiated at `0`):
* `exists_contDiff_eq_of_locally`: a function on `S ⊆ E` (finite-dimensional) that agrees near
  each point of a compact `K ⊆ S` with a smooth function agrees on `K` with a globally smooth `F`;
* `isFiniteCellComplexType_sublevel_of_isCompact`: Theorem 3.5 for sublevel sets on a slice
  submanifold `N ⊆ V` (model `Z`) of an ambient smooth `F : V → ℝ`: if `{F ≤ a₀} ∩ N` is compact,
  the critical points in it are non-degenerate and `a₀` is NOT a critical value, then `N^{a₀}` has
  the homotopy type (`Morse.IsFiniteCellComplexType`) of an iterated adjunction space — cells
  attached one at a time along arbitrary maps, in order of critical value — with one cell of
  dimension `index p` per critical point `p` below `a₀`;
* `theorem_16_3`, `theorem_16_3_count`: the same for `E'` on `{y ∈ B.nodes | E'(y) ≤ a}`
  (`B : Morse.BrokenSetup`, `a < c` not a critical value, nullity `0` at the geodesics), cells of
  dimension `geodIndex y = formIndex (energyHessian)`, with finiteness and counts. -/
def A : Prop :=
  type_of% @Morse.exists_contDiff_eq_of_locally.{0} ∧
    type_of% @Morse.isFiniteCellComplexType_sublevel_of_isCompact.{0, 0, 0} ∧
    type_of% @Morse.BrokenSetup.theorem_16_3.{0, 0, 0} ∧
    type_of% @Morse.BrokenSetup.theorem_16_3_count.{0, 0, 0}

theorem A_holds : A :=
  ⟨@Morse.exists_contDiff_eq_of_locally, @Morse.isFiniteCellComplexType_sublevel_of_isCompact,
    @Morse.BrokenSetup.theorem_16_3, @Morse.BrokenSetup.theorem_16_3_count⟩

/-! Neither `A → B` nor `B → A` is proved; see `V10_12.json`.

B is Theorem 3.5 on an ABSTRACT smooth Hausdorff manifold (model any finite-dimensional `E`), in
two forms: (1) all sublevel sets compact ⇒ `M` is homotopy equivalent to a Mathlib `CWComplex`
(possibly infinite) with `λ`-cells in bijection with the critical points of index `λ`; (2) the
`c`-version: sublevel sets compact for `a < c` ⇒ for EVERY `a < c` (critical value or not) `{f ≤ a}`
is homotopy equivalent to a finite Mathlib `CWComplex` with cells ↔ critical points in `{f ≤ a}`.

* A ⇒ B fails genuinely: A's conclusion is `Morse.IsFiniteCellComplexType` (iterated adjunction
  spaces with arbitrary attaching maps), and turning it into a CW complex needs cellular
  approximation (not in Mathlib) — the V2_12 obstacle; A only treats slice submanifolds `N ⊆ V`
  and ambient `F` (an abstract `M` and `f` would need an embedding theorem and an extension);
  A needs `a₀` to be a regular value, B's (2) does not; B's (1) (non-compact `M`, infinitely many
  cells: direct limit / Whitehead) has no counterpart in A.
* B ⇒ A fails genuinely: a CW complex does not give A's ordered iterated adjunction (cells in order
  of critical value, not of dimension); A's `exists_contDiff_eq_of_locally` (extension lemma) and
  the `BrokenSetup` specialization `theorem_16_3` (`E'` on `B^a`, with `geodIndex` given by the
  formula-defined `energyHessian`) are not consequences of B.

The embedded special case does not apply: B quantifies over smooth manifolds with a function,
not over Riemannian manifolds. -/

end RoundTrip.V10_12
