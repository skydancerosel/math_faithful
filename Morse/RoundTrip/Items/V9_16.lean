import Morse
import RoundTrip.Check
import RoundTrip.Blind.V9_16
import RoundTrip.Bridge

open Set Filter Topology Function Module
open scoped ContDiff Manifold

namespace RoundTrip.V9_16

/-- The project's statement (universes instantiated at `0`), for a slice submanifold `N ⊆ V` with
the induced metric and ANY smooth curve `γ` in `N` on `[0, 1]` (`Morse.IsSmoothCurveIn`, no
geodesic hypothesis), with the analytic mesh `h₀ = Morse.fineMesh hN γ hc > 0` (vocabulary; built
from a bound for `‖P'‖² + ‖R(V, ·)V‖` along `γ`):
* `hessForm_ge` (**positivity near zeros**): if every `t ∈ [0, 1]` has a zero of `X ∈ TΩ_γ` in
  `[t − h₀, t]`, then `∫₀¹ ‖X‖² ≤ hessForm X X` (the formula-defined `½ E_**`);
* `eq_zero_of_short`: a Jacobi field vanishing at `a < b` with `b − a ≤ h₀` is `0`;
* `jacEvalEnds_bijective`: for `a < b` in `[0, 1]`, `b − a ≤ h₀`, `J ↦ (J(a), J(b))` is a bijection
  from the Jacobi fields along `γ` onto `T_{γ(a)}N × T_{γ(b)}N`;
* `exists_isFine`: for `τ > 0` there is a finite set `B ⊆ (0, τ)` cutting `[0, τ]` into pieces of
  length `≤ h₀` (`Morse.IsFine`, vocabulary), with its last point within `h₀ / 2` of `τ`. -/
def A : Prop :=
  type_of% @Morse.hessForm_ge.{0, 0, 0} ∧ type_of% @Morse.eq_zero_of_short.{0, 0, 0} ∧
    type_of% @Morse.jacEvalEnds_bijective.{0, 0, 0} ∧ type_of% @Morse.exists_isFine.{0, 0, 0}

theorem A_holds : A :=
  ⟨@Morse.hessForm_ge, @Morse.eq_zero_of_short, @Morse.jacEvalEnds_bijective,
    @Morse.exists_isFine⟩

/-! Neither `A → B` nor `B → A` is proved; see `V9_16.json`.

The two statements formalize two different notions of "sufficiently fine subdivision".
* B (Milnor's): `FineSub` — every piece `γ|[t_{i-1}, t_i]` lies in a neighbourhood `U` with unique
  minimal geodesics depending smoothly on the end points (`GoodNbhd`) and is itself minimal
  (`IsMinimal`, length against every piecewise smooth path). B claims such subdivisions exist,
  that along each piece Jacobi fields are determined by, and can take any, end values, and that
  each piece has energy `≤` any piecewise smooth path on the same interval with the same ends.
* A (the project's substitute): `IsFine` — pieces of parameter length `≤ h₀`, an analytic constant
  from curvature bounds, for any smooth curve. Along such pieces Jacobi fields are determined by
  and can take any end values (`jacEvalEnds_bijective`, through `eq_zero_of_short`, through the
  estimate `hessForm_ge`, which has no counterpart in B or in Milnor's text).

Neither notion of fineness implies the other: a blind-fine piece can be much longer than `h₀`
(and A then says nothing about it), while an `h₀`-short piece need not be minimal or lie in a
`GoodNbhd`. A ⇒ B (even on `↥N`) would need that the end points of a minimal geodesic segment in
a `GoodNbhd` are not conjugate (Lemma 14.4 / Remark 14.5 with Milnor's `U`, via the smooth inverse
`G` of `exp`), the existence of `GoodNbhd`s on `↥N` (Lemma 10.3 in the blind vocabulary: blind
`IsMinimal`, smooth `G : M × M → TM`), and the energy inequality for minimal segments (Schwarz),
none of which is in A. B ⇒ A fails as B has no estimate for the Hessian and no statement about
`h₀`-short pieces.

## The embedded special case (stated, not proved) -/

/-- B on embedded manifolds: `M = ↥N` (model `ℝⁿ`, induced metric), induced connection. -/
def B_emb : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    (W : Type) [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W] (n : ℕ)
    (N : Set V) (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) (Rn n) W N)
    [ConnectedSpace (Bridge.Sub hN)] (γ : ℝ → Bridge.Sub hN),
    IsGeodesic (Bridge.conn (hN := hN)) γ (Set.Icc 0 1) →
  (∃ (k : ℕ) (t : ℕ → ℝ), FineSub (Bridge.conn (hN := hN)) γ 1 k t) ∧
  ∀ (k : ℕ) (t : ℕ → ℝ), FineSub (Bridge.conn (hN := hN)) γ 1 k t → ∀ i < k,
    (∀ (x : TangentSpace 𝓘(ℝ, Rn n) (γ (t i))) (y : TangentSpace 𝓘(ℝ, Rn n) (γ (t (i + 1)))),
      ∃ J : FA n γ, IsJacobi (Bridge.conn (hN := hN)) γ (Set.Icc (t i) (t (i + 1))) J ∧
        J (t i) = x ∧ J (t (i + 1)) = y) ∧
    (∀ J₁ J₂ : FA n γ, IsJacobi (Bridge.conn (hN := hN)) γ (Set.Icc (t i) (t (i + 1))) J₁ →
      IsJacobi (Bridge.conn (hN := hN)) γ (Set.Icc (t i) (t (i + 1))) J₂ →
      J₁ (t i) = J₂ (t i) → J₁ (t (i + 1)) = J₂ (t (i + 1)) →
      Set.EqOn J₁ J₂ (Set.Icc (t i) (t (i + 1)))) ∧
    (∀ pw : ℝ → Bridge.Sub hN, IsPW (n := n) pw (t i) (t (i + 1)) → pw (t i) = γ (t i) →
      pw (t (i + 1)) = γ (t (i + 1)) →
      energy (n := n) γ (t i) (t (i + 1)) ≤ energy (n := n) pw (t i) (t (i + 1)))

theorem B_to_B_emb : B → B_emb := fun hB _ _ _ _ _ _ _ _ n _ hN _ =>
  hB n (Bridge.Sub hN) (Bridge.conn (hN := hN)) Bridge.conn_isLC

end RoundTrip.V9_16
