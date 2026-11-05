import Morse
import RoundTrip.Check
import RoundTrip.Blind.V9_21
import RoundTrip.Bridge

open Set Filter Topology Function Module
open scoped ContDiff Manifold

namespace RoundTrip.V9_21

/-- The project's statement (universes instantiated at `0`), for a slice submanifold `N ⊆ V` with
the induced metric, ANY smooth curve `γ` in `N` on `[0, 1]` (no geodesic hypothesis) and a finite
set `B` of division points; `Morse.validFor hc B` (vocabulary) is the set of `τ ∈ (0, 1]` for
which `B` is `IsFine` for `[0, τ]` (pieces of length `≤ h₀`), and `Morse.Hform hN γ hc B τ`
(vocabulary) is Milnor's `H_τ`: the formula-defined `energyHessian` on the broken Jacobi fields
along `γ|[0, τ]`, transported to `Σ = Morse.nodeSpace hN γ B = ⊕_{b ∈ B} T_{γ(b)}N` by the
evaluation isomorphism (`0` for `τ ∉ validFor`):
* `formIndex_Hform`: for `τ ∈ validFor`, `formIndex H_τ = λ(τ) = Morse.indexUpTo hN γ hc τ`;
* `finrank_ker_Hform`: for `τ ∈ validFor`, the nullity of `H_τ` is `conjMultiplicity 0 τ`;
* `continuousWithinAt_Hform`: for `τ₀ ∈ validFor` and fixed `x, y ∈ Σ`, `τ ↦ H_τ(x, y)` is
  continuous within `validFor` at `τ₀` (Lemma 15.C);
* `mem_validFor_of_near`: if `B` is fine for `[0, τ]` with its last point `m` within `h₀ / 2` of
  `τ`, every `τ' ∈ (m, τ + h₀ / 2)` with `τ' ≤ 1` is in `validFor`. -/
def A : Prop :=
  type_of% @Morse.formIndex_Hform.{0, 0, 0} ∧ type_of% @Morse.finrank_ker_Hform.{0, 0, 0} ∧
    type_of% @Morse.continuousWithinAt_Hform.{0, 0, 0} ∧
    type_of% @Morse.mem_validFor_of_near.{0, 0, 0}

theorem A_holds : A :=
  ⟨@Morse.formIndex_Hform, @Morse.finrank_ker_Hform, @Morse.continuousWithinAt_Hform,
    @Morse.mem_validFor_of_near⟩

/-! Neither `A → B` nor `B → A` is proved; see `V9_21.json`. The shapes correspond (B's (b)
`λ(τ) = bIndex univ H_τ` ↔ `formIndex_Hform`; B's joint continuity of `(τ, x) ↦ H_τ(x, x)` on
`(t_i, t_{i+1}) × Σ` ↔ the separate continuity of `τ ↦ H_τ(x, y)` within `validFor`, equivalent
for symmetric forms on the finite dimensional `Σ` by polarization / coordinates), but every
ingredient differs:
* `H_τ`: B's `Htau` is the choice function of `HtauRel`, i.e. of the variational `IsHessT τ`
  (Fréchet mixed partial of `E_0^τ ∘ α` for some 2-parameter variation `α`), on broken Jacobi
  fields for the subdivision `t₀ < ⋯ < t_i < τ`; B's (a) asserts that the value exists for all
  `x, y` (Lemma 11.A with the Fréchet regularity). A's `Hform` is the formula-defined
  `energyHessian` (for `E_0^1`, on fields supported in `[0, τ]`). Identifying them needs the
  missing joint `C²` regularity of `u ↦ E_0^τ(α(u))` (obstacle of V8_13, V8_14, V9_5).
* `λ(τ)`: B's `lam` (index of `HessT τ` on the blind `TΩ`) vs A's `indexUpTo` (see V9_20).
* Fineness: B's `FineSub` of `[0, 1]` with `τ ∈ (t_i, t_{i+1})` vs A's `IsFine` of `[0, τ]` and the
  set `validFor`; A's `mem_validFor_of_near` is the project's replacement for B's choice of `τ`
  between two division points.
* `Σ`: B's `Sig γ t i = Π_{j < i} T_{γ(t_{j+1})}M` (product topology) vs A's `nodeSpace` (tangent
  vectors in `V` indexed by `B`).
A has the nullity statement (`finrank_ker_Hform`, used for Assertion (4)) that B lacks.

## The embedded special case (stated, not proved) -/

/-- B on embedded manifolds: `M = ↥N` (model `ℝⁿ`, induced metric), induced connection. -/
def B_emb : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    (W : Type) [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W] (n : ℕ)
    (N : Set V) (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) (Rn n) W N)
    [ConnectedSpace (Bridge.Sub hN)] (γ : ℝ → Bridge.Sub hN),
    IsGeodesic (Bridge.conn (hN := hN)) γ (Set.Icc 0 1) →
  ∀ (k : ℕ) (t : ℕ → ℝ), FineSub (Bridge.conn (hN := hN)) γ 1 k t → ∀ i < k,
    (∀ τ ∈ Set.Ioo (t i) (t (i + 1)), ∀ x y : Sig (n := n) γ t i,
      ∃ r, HtauRel (Bridge.conn (hN := hN)) γ t i τ x y r) ∧
    (∀ τ ∈ Set.Ioo (t i) (t (i + 1)),
      lam (n := n) τ γ = bIndex Set.univ (Htau (Bridge.conn (hN := hN)) γ t i τ)) ∧
    ContinuousOn (fun z : ℝ × Sig (n := n) γ t i =>
        Htau (Bridge.conn (hN := hN)) γ t i z.1 z.2 z.2)
      (Set.Ioo (t i) (t (i + 1)) ×ˢ Set.univ)

theorem B_to_B_emb : B → B_emb := fun hB _ _ _ _ _ _ _ _ n _ hN _ =>
  hB n (Bridge.Sub hN) (Bridge.conn (hN := hN)) Bridge.conn_isLC

end RoundTrip.V9_21
