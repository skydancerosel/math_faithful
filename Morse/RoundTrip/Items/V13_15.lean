import Morse
import RoundTrip.Check
import RoundTrip.Blind.V13_15

open scoped ContDiff Manifold

namespace RoundTrip.V13_15

/-- The project's statement (universes instantiated at `0`), all inside the finite-dimensional model
`B = Int Ω(t₀, …, t_k)^c` of the path space (`Morse.BrokenSetup`, a slice submanifold `N ⊆ V`):
break points of broken geodesics lie in the closed Riemannian ball `ρ(p, ·) ≤ √c`
(`mem_ball_of_mem_nodes`); the short join of a point with itself is `0` (`joinVec_self`);
**Milnor's deformation of a neighbourhood of the minima** (`exists_pushesInto_nodes`): for an open
`O` with `Nᵐ ∩ O ⊆ nodes` and `d < c`, if `{γ ∈ Ω : E(γ) ≤ d}` is a retract of an open set `Or ⊆ Ω`
containing it (hypothesis), then `M⁰ = {y ∈ Nᵐ ∩ O : E'(y) ≤ d}` has an open neighbourhood `U` in
`Nᵐ ∩ O` from which it pushes maps (from any space `P`). -/
def A : Prop :=
  type_of% @Morse.BrokenSetup.mem_ball_of_mem_nodes.{0,0,0} ∧
  type_of% @Morse.BrokenSetup.joinVec_self.{0,0,0} ∧
  type_of% @Morse.BrokenSetup.exists_pushesInto_nodes.{0,0,0,0}

theorem A_holds : A :=
  ⟨@Morse.BrokenSetup.mem_ball_of_mem_nodes, @Morse.BrokenSetup.joinVec_self,
    @Morse.BrokenSetup.exists_pushesInto_nodes⟩

/-! Neither direction is proved; see `V13_15.json`.

`B` is Milnor's sentence for a general `f : M → ℝ` with minimum `0`, compact sublevel sets and `M⁰`
a topological manifold, on any Riemannian manifold `M`: Hanner's theorem (an open `U ⊇ M⁰` retracts
onto `M⁰`), uniqueness of the minimal geodesic from `x ∈ U` to `r(x)`, and the deformation of `U`
into `M⁰` along these geodesics. `A` is the special case the project needs for Theorem 22.1, in a
different form: the manifold is the break-point manifold `Nᵐ ∩ O` of the broken-geodesic model, the
function is `E'`, the retraction is a *hypothesis* (of `{E ≤ d}` in `Ω`, transported to `Nᵐ ∩ O`),
and the conclusion is only the pushing property of a neighbourhood (no uniqueness of minimal
geodesics, no retraction `r` on `Nᵐ ∩ O`, no explicit deformation in the statement).
* `A ⇒ B` fails genuinely: Hanner's theorem (topological manifold ⇒ neighbourhood retract) is not
  formalized and is not in `A`; `A` is about one specific manifold and function; abstract `M`.
* `B ⇒ A` fails genuinely: `A`'s hypotheses (a retraction of `{E ≤ d}` on an open subset of `Ω`)
  do not make `{E' ≤ d}` a topological manifold, and `E'` on the open `Nᵐ ∩ O` does not have
  compact sublevel sets for all levels (only below `c`), so `B` does not apply; `A`'s two
  auxiliary lemmas are about the project's `BrokenSetup` vocabulary only. -/

end RoundTrip.V13_15
