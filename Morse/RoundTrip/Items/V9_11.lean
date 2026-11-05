import Morse
import RoundTrip.Check
import RoundTrip.Blind.V9_11
import RoundTrip.Bridge

open Set Filter Topology Function Module
open scoped ContDiff Manifold

namespace RoundTrip.V9_11

/-- The project's statement (universes instantiated at `0`), for a slice submanifold `N ⊆ V` with
the induced metric: (1) for a normal radius `ε` at `q` and `‖v‖ < ε`, the ray `t ↦ exp_q(tv)` is a
smooth curve in `N` on `[0, 1]`; (2) a Jacobi field along it vanishing at `t = 0, 1` vanishes on
`[0, 1]`; (3) `J ↦ (J(0), J(1))` is bijective along it (values determined AND prescribable);
(4) every `p ∈ N` has an open `O ∋ p` and `ε > 0` (Lemma 10.3) such that any `q₁, q₂ ∈ O ∩ N` are
joined by such a ray `exp_{q₁}(tv)`, `‖v‖ < ε` a normal radius at `q₁`, along which (2) holds. -/
def A : Prop :=
  type_of% @Morse.IsNormalRadius.isSmoothCurveIn_ray.{0, 0, 0} ∧
    type_of% @Morse.remark_14_5_of_isNormalRadius.{0, 0, 0} ∧
    type_of% @Morse.remark_14_5_bijective.{0, 0, 0} ∧
    type_of% @Morse.remark_14_5.{0, 0, 0}

theorem A_holds : A :=
  ⟨@Morse.IsNormalRadius.isSmoothCurveIn_ray, @Morse.remark_14_5_of_isNormalRadius,
    @Morse.remark_14_5_bijective, @Morse.remark_14_5⟩

/-! No direction is proved; see `V9_11.json`. Besides the setting (abstract manifolds vs slice
submanifolds), the hypotheses differ: B quantifies over EVERY open `U` with unique minimal
geodesics depending smoothly on the end points (`GoodNbhd`) and EVERY geodesic segment
`γ : [a, b] → U` (no length bound, not necessarily minimal), while A only treats the short rays
`exp_q(tv)` with `‖v‖` below a normal radius at `q` (and the neighbourhoods of Lemma 10.3 in its
existential form (4)). Milnor's argument (the variation through the minimal geodesics of `U`,
Lemma 14.4) only reaches minimal segments.

## The embedded special case (stated, not proved) -/

/-- B on embedded manifolds: `M = ↥N` (model `ℝⁿ`, induced metric), induced connection. -/
def B_emb : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    (W : Type) [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W] (n : ℕ)
    (N : Set V) (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) (Rn n) W N)
    [ConnectedSpace (Bridge.Sub hN)],
  ∀ U : Set (Bridge.Sub hN), GoodNbhd (Bridge.conn (hN := hN)) U →
    ∀ (γ : ℝ → Bridge.Sub hN) (a b : ℝ), a < b → IsGeodesic (Bridge.conn (hN := hN)) γ (Set.Icc a b) →
    (∀ t ∈ Set.Icc a b, γ t ∈ U) →
    ∀ J₁ J₂ : FA n γ, IsJacobi (Bridge.conn (hN := hN)) γ (Set.Icc a b) J₁ →
      IsJacobi (Bridge.conn (hN := hN)) γ (Set.Icc a b) J₂ →
      J₁ a = J₂ a → J₁ b = J₂ b → Set.EqOn J₁ J₂ (Set.Icc a b)

theorem B_to_B_emb : B → B_emb := fun hB _ _ _ _ _ _ _ _ n _ hN _ =>
  hB n (Bridge.Sub hN) (Bridge.conn (hN := hN)) Bridge.conn_isLC

end RoundTrip.V9_11
