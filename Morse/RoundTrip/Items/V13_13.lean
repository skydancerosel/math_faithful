import Morse
import RoundTrip.Check
import RoundTrip.Blind.V13_13

open scoped ContDiff Manifold

namespace RoundTrip.V13_13

/-- The project's statement (universes instantiated at `0`): a finite set of reals has a gap around
each point (`exists_gap_of_finite`); **Lemma D** (`lemma_D`): for a slice submanifold `N ⊆ V` and
`f = F|N`, `F : V → ℝ` smooth, with `N^{a₀}` compact, `a` a regular value of `f` and every critical
point `q` with `a < f(q) ≤ a₀` non-degenerate of index `≥ λ₀`: for `a ≤ b < a₀`, `N^a` pushes maps
from any compact `P` embedded in a real vector space of dimension `< λ₀` out of `N^b` (every map
`P → N^b` is homotopic in `N`, rel the preimage of `N^a`, to a map into `N^a`). -/
def A : Prop :=
  type_of% @Morse.exists_gap_of_finite ∧
  type_of% @Morse.lemma_D.{0,0,0,0,0}

theorem A_holds : A := ⟨@Morse.exists_gap_of_finite, @Morse.lemma_D⟩

/-! Neither direction is proved; see `V13_13.json`.

The two statements have different conclusions. `B` (Milnor's sentence) asserts a *homotopy type*:
there is a relative CW complex `(Y, D)` with no cells of dimension `< λ₀`, `D ≃ g⁻¹(−∞, a]` and
`Y ≃ g⁻¹(−∞, b]` compatibly with the inclusion. `A` asserts the *consequence Milnor draws from it*
("since `r < λ₀`, `h` is homotopic to a map into `g⁻¹(−∞, 2δ]`"): a compression property of the pair
`(N^b, N^a)` for low-dimensional compact `P`, rel the preimage of `N^a`.
* `A ⇒ B` fails genuinely: a compression property does not produce a CW model (that needs
  Theorems 3.1/3.2 assembled into a relative CW complex; the project has `remark_3_3_submanifold`
  and `isFiniteCellComplexType_union_cells` but they are not in `A`); also abstract `M` vs slice
  submanifolds, and `B` allows critical points at level `a` and needs only the slab `g⁻¹[a, b]`
  compact, while `A` needs `a` regular and `N^{a₀}` compact.
* `B ⇒ A` fails genuinely: from a relative CW complex with cells of dimension `≥ λ₀` to the
  compression of maps from arbitrary compact `P ⊆ ℝ^{<λ₀}` rel an arbitrary closed subset needs
  cellular approximation / the push-off lemma (Hatcher 4.10) and the transport along the two
  compatible homotopy equivalences; plus setting (abstract `M` only, `f = F|N` with `F` ambient on
  the project's side). `exists_gap_of_finite` is a trivial real-analysis lemma (true outright). -/

end RoundTrip.V13_13
