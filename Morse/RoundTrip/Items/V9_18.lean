import Morse
import RoundTrip.Check
import RoundTrip.Blind.V9_18
import RoundTrip.Bridge

open Set Filter Topology Function Module
open scoped ContDiff Manifold

namespace RoundTrip.V9_18

/-- The project's statement (universes instantiated at `0`), for a slice submanifold `N ⊆ V` with
the induced metric, ANY smooth curve `γ` in `N` on `[0, 1]` (no geodesic hypothesis), `0 < τ ≤ 1`
and division points `B` with `Morse.IsFine hN γ hc B τ` (pieces of length `≤ h₀`); `E_**` is
`Morse.energyHessian`, the bilinear form on `TΩ_γ` DEFINED as `2 ×` the right side of the second
variation formula:
* `energyHessian_broken_eq`: for `X` a broken Jacobi field along `γ|[0, τ]` and `Y` vanishing
  outside `[0, τ]`, `E_**(X, Y) = −2 Σ_{b ∈ B} ⟨Y(b), P Δ_b X'⟩`;
* `isCompl_broken_nodeZero`: inside the fields along `γ|[0, τ]`, the broken Jacobi fields and the
  fields vanishing at the division points (`T'`) are complementary subspaces;
* `energyHessian_broken_nodeZero`: `E_**(X, Y) = 0` for `X` broken Jacobi and `Y ∈ T'`;
* `energyHessian_nodeZero_pos`: `E_**(Y, Y) > 0` for `0 ≠ Y ∈ T'`. -/
def A : Prop :=
  type_of% @Morse.energyHessian_broken_eq.{0, 0, 0} ∧
    type_of% @Morse.isCompl_broken_nodeZero.{0, 0, 0} ∧
    type_of% @Morse.energyHessian_broken_nodeZero.{0, 0, 0} ∧
    type_of% @Morse.energyHessian_nodeZero_pos.{0, 0, 0}

theorem A_holds : A :=
  ⟨@Morse.energyHessian_broken_eq, @Morse.isCompl_broken_nodeZero,
    @Morse.energyHessian_broken_nodeZero, @Morse.energyHessian_nodeZero_pos⟩

/-! Neither `A → B` nor `B → A` is proved; see `V9_18.json`. Three independent gaps, each of which
already blocks the embedded special case `B_emb` below:
1. **The Hessian.** B's `E_**` is the relation `IsHessT 1 γ W₁ W₂ r`: SOME 2-parameter variation
   with variation fields `W₁, W₂` has `∂²E/∂u₂∂u₁ (0) = r`, with Fréchet derivatives (`mixedD`) and
   a Fréchet-differentiability side condition. A's `E_**` is the formula-defined `energyHessian`.
   Relating them needs Lemma 11.A with that regularity, Theorem 13.1, and the analysis fact, absent
   from the project, that `u ↦ E(α(u))` is jointly `C²` (the obstacle of V8_13, V8_14, V9_5).
2. **Fineness.** B's subdivision is Milnor's `FineSub` (minimal pieces in `GoodNbhd`s), A's is
   `IsFine` (pieces of length `≤ h₀`); neither implies the other (see V9_16/V9_17), and B's
   splitting and positivity rest on the end points of each piece not being conjugate, which A only
   proves for `h₀`-short pieces.
3. **Dictionary.** Blind `InTOmegaT`/`BrokenSet`/`TPrime` (fields `ℝ → TM`, piecewise smooth in the
   manifold sense) vs the project's `pathTangent`/`brokenSpace`/`nodeZero` (fields `ℝ → V`); no such
   dictionary exists yet.
Besides, A is for every `τ ∈ (0, 1]` and every smooth curve, and has the explicit jump formula;
B is for `τ = 1`, geodesics, and asserts existence of the realizing variations.

## The embedded special case (stated, not proved) -/

/-- B on embedded manifolds: `M = ↥N` (model `ℝⁿ`, induced metric), induced connection. -/
def B_emb : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    (W : Type) [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W] (n : ℕ)
    (N : Set V) (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) (Rn n) W N)
    [ConnectedSpace (Bridge.Sub hN)] (γ : ℝ → Bridge.Sub hN),
    IsGeodesic (Bridge.conn (hN := hN)) γ (Set.Icc 0 1) →
  ∀ (k : ℕ) (t : ℕ → ℝ), FineSub (Bridge.conn (hN := hN)) γ 1 k t →
    (∀ W : FA n γ, InTOmegaT (n := n) 1 γ W →
      ∃! p : FA n γ × FA n γ, p.1 ∈ BrokenSet (Bridge.conn (hN := hN)) γ 1 k t ∧
        p.2 ∈ TPrime (n := n) γ 1 k t ∧ W = p.1 + p.2) ∧
    (∀ W₁ ∈ BrokenSet (Bridge.conn (hN := hN)) γ 1 k t, ∀ W₂ ∈ TPrime (n := n) γ 1 k t,
      IsHessT (n := n) 1 γ W₁ W₂ 0 ∧ IsHessT (n := n) 1 γ W₂ W₁ 0) ∧
    (∀ W ∈ TPrime (n := n) γ 1 k t, W ≠ 0 → ∃ r : ℝ, IsHessT (n := n) 1 γ W W r ∧ 0 < r)

theorem B_to_B_emb : B → B_emb := fun hB _ _ _ _ _ _ _ _ n _ hN _ =>
  hB n (Bridge.Sub hN) (Bridge.conn (hN := hN)) Bridge.conn_isLC

end RoundTrip.V9_18
