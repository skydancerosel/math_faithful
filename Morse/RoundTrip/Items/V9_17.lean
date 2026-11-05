import Morse
import RoundTrip.Check
import RoundTrip.Blind.V9_17
import RoundTrip.Bridge

open Set Filter Topology Function Module
open scoped ContDiff Manifold

namespace RoundTrip.V9_17

/-- The project's statement (universes instantiated at `0`), for a slice submanifold `N ⊆ V` with
the induced metric and ANY smooth curve `γ` in `N` on `[0, 1]` (no geodesic hypothesis), `B` a
finite set of division points and `0 < τ ≤ 1` with `Morse.IsFine hN γ hc B τ` (pieces of
parameter length `≤ h₀ = Morse.fineMesh`):
* `exists_isBrokenJacobi`: for any tangent values `x(t) ∈ T_{γ(t)}N` at `t ∈ {0, τ} ∪ B` there is a
  broken Jacobi field (`Morse.IsBrokenJacobi`: on every piece equal to a Jacobi field along `γ`)
  taking them;
* `nodeEval_bijective`: `W ↦ (W(b))_{b ∈ B}` is a linear bijection from `Morse.brokenSpace hc B τ`
  (broken Jacobi fields in `TΩ_γ` vanishing outside `[0, τ]`, Milnor's `TΩ_γ(t₀, …, t_k)` along
  `γ|[0, τ]`) onto `Σ = Morse.nodeSpace hN γ B = ⊕_{b ∈ B} T_{γ(b)}N`.
`Morse.fieldsUpTo`, `Morse.nodeZero` (Milnor's `T'`) are vocabulary. -/
def A : Prop :=
  type_of% @Morse.exists_isBrokenJacobi.{0, 0, 0} ∧ type_of% @Morse.nodeEval_bijective.{0, 0, 0}

theorem A_holds : A := ⟨@Morse.exists_isBrokenJacobi, @Morse.nodeEval_bijective⟩

/-! Neither `A → B` nor `B → A` is proved; see `V9_17.json`.

Both statements say the same thing about broken Jacobi fields (existence and uniqueness with
prescribed values at the division points; the space is `≅ ⊕ T_{γ(t_i)}M`), but for different
notions of a fine subdivision:
* B: Milnor's `FineSub` — pieces minimal and inside neighbourhoods with unique, smoothly varying
  minimal geodesics (`GoodNbhd`); dimension stated as `setDim = (k − 1) n`;
* A: `IsFine` — pieces of parameter length `≤ h₀`, an analytic constant (curvature bounds), for any
  smooth curve; the dimension is given as a linear bijection onto `Σ` (whose dimension
  `|B| · dim N` is a separate project lemma), and existence also for non-zero end values.
What is really used on each piece is that its end points are not conjugate. A proves this for
`h₀`-short pieces (`Morse.eq_zero_of_short`); B for minimal pieces of a `GoodNbhd` (via the smooth
inverse `G` of `exp`, Milnor's Lemma 14.4/Remark 14.5). Neither kind of piece is the other, so even
on `↥N` (`B_emb` below) a proof would need new Riemannian geometry (non-conjugacy of the end points
of a minimal segment in a `GoodNbhd` of `↥N`, in the blind vocabulary), besides a dictionary for
blind piecewise smooth fields (`InTOmegaT`, continuity in `TM`, `IsSmoothAlong` on pieces) and blind
Jacobi fields on sub-intervals `[t_i, t_{i+1}]` (Items/V9_10.lean only covers `[0, 1]`).

## The embedded special case (stated, not proved) -/

/-- B on embedded manifolds: `M = ↥N` (model `ℝⁿ`, induced metric), induced connection. -/
def B_emb : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    (W : Type) [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W] (n : ℕ)
    (N : Set V) (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) (Rn n) W N)
    [ConnectedSpace (Bridge.Sub hN)] (γ : ℝ → Bridge.Sub hN),
    IsGeodesic (Bridge.conn (hN := hN)) γ (Set.Icc 0 1) →
  ∀ τ : ℝ, 0 < τ → τ ≤ 1 → ∀ (k : ℕ) (t : ℕ → ℝ), FineSub (Bridge.conn (hN := hN)) γ τ k t →
    (∀ x : (i : ℕ) → TangentSpace 𝓘(ℝ, Rn n) (γ (t i)), x 0 = 0 → x k = 0 →
      ∃! W : FA n γ, IsBrokenT (Bridge.conn (hN := hN)) γ τ k t W ∧ ∀ i ≤ k, W (t i) = x i) ∧
    setDim (BrokenSet (Bridge.conn (hN := hN)) γ τ k t) = (((k - 1) * n : ℕ) : ℕ∞)

theorem B_to_B_emb : B → B_emb := fun hB _ _ _ _ _ _ _ _ n _ hN _ =>
  hB n (Bridge.Sub hN) (Bridge.conn (hN := hN)) Bridge.conn_isLC

end RoundTrip.V9_17
