import Morse
import RoundTrip.Check
import RoundTrip.Blind.V10_11
import RoundTrip.Bridge

open Set Filter Topology
open scoped ContDiff Manifold

namespace RoundTrip.V10_11

/-- The project's statement (universes instantiated at `0`; `Morse.BrokenSetup.chartBrokenEquiv`
is vocabulary — a linear isomorphism `(Fin m → Z) ≃ brokenSpace` built from the slice chart of
`N^m ∩ O` at `y`):
* `hasDerivAt_deriv_line`: for `G` of class `C²` at `z₀`, the second derivative of
  `u ↦ G(z₀ + u z)` at `0` is `hessian G z₀ z z`;
* `hessian_eq_energyHessian`: for `B : Morse.BrokenSetup hN p q c m`, an open `O ⊆ V^m` with
  `N^m ∩ O ⊆ B.nodes`, `F : V^m → ℝ` smooth with `F = E'` on `N^m ∩ O`, and `y ∈ N^m ∩ O` with
  `B.path y` an unbroken geodesic: the Hessian of `F` in the slice chart at `y` is the
  formula-defined `E_**` (`Morse.energyHessian`) on the corresponding broken Jacobi fields;
* `theorem_16_2_index` (Theorem 16.2): in the same situation, `indexM (F ∘ val) y` (index of
  `E'` on the slice submanifold `N^m ∩ O` of `V^m`) `= formIndex (energyHessian)` and
  `nullityM (F ∘ val) y = hessNullity`. -/
def A : Prop :=
  type_of% @Morse.hasDerivAt_deriv_line.{0} ∧
    type_of% @Morse.BrokenSetup.hessian_eq_energyHessian.{0, 0, 0} ∧
    type_of% @Morse.BrokenSetup.theorem_16_2_index.{0, 0, 0}

theorem A_holds : A :=
  ⟨@Morse.hasDerivAt_deriv_line, @Morse.BrokenSetup.hessian_eq_energyHessian,
    @Morse.BrokenSetup.theorem_16_2_index⟩

/-! Neither `A → B` nor `B → A` is proved; see `V10_11.json`. Beyond the setting (abstract
Riemannian manifolds vs slice submanifolds with the induced metric):

* B's right-hand side `lam 1 γ` / nullity is that of `HessT 1 γ`, the choice function of Milnor's
  VARIATIONAL `E_**`; A's is `Morse.energyHessian` (defined by the second variation formula).
  `RoundTrip/EnergyC2.lean` removes the analytic obstacle, but the identification on `↥N` still
  needs a 2-parameter variation dictionary, realizing variations for every pair of `TΩ` (lifted
  from `Morse.exists_variation_two`) and a `TΩ` dictionary (`TOm 1 γ` ⇔ `pathTangent`).
* B's left-hand side `HessPi` is Milnor's Hessian of ANY `F` smooth on `e(B) ⊆ M^{k−1}` (product
  manifold of `M`, 2-parameter maps, `mixedD`), with index/nullity as `bIndex`/`setDim` on the
  whole model space; A's is `indexM`/`nullityM` (Morse.hessianM in slice charts) of `F ∘ val` on
  `N^m ∩ O ⊆ V^m`, with `F` smooth on all of `V^m`. Relating them needs the product manifold
  `(↥N)^{k−1}` ⇔ slice submanifold `N^m ∩ O`, a smooth ambient extension of the blind `F`
  (`Morse.exists_contDiff_eq_of_locally`, item V10_12) and chart-independence of the index.
* B's subdivisions are `Setup16` (ε of Lemma 10.8 only); A's are `BrokenSetup`s (plus normal radii),
  so even on `↥N` A does not reach B's subdivisions (genuine, see V10_10).
* B's second conjunct (the variation field of a variation through broken geodesics is a broken
  Jacobi field, Milnor p. 92 / 14.3) is not in A; A's `hasDerivAt_deriv_line` and the chart
  formula `hessian_eq_energyHessian` are not in B.

## The embedded special case (stated, not proved) -/

/-- B on embedded manifolds: `M = ↥N` (model `ℝⁿ`, induced metric), induced connection. -/
def B_emb : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    (W : Type) [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W] (n : ℕ)
    (N : Set V) (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) (Rn n) W N)
    [ConnectedSpace (Bridge.Sub hN)], MetricComplete n (Bridge.Sub hN) →
  ∀ (p q : Bridge.Sub hN) (c ε : ℝ) (k : ℕ) (t : ℕ → ℝ),
    Setup16 n (Bridge.conn (hN := hN)) p q c ε k t →
    (∀ (F : (Fin (k - 1) → Bridge.Sub hN) → ℝ) (U : Set (Fin (k - 1) → Bridge.Sub hN)),
      IsEprime n (Bridge.conn (hN := hN)) p q c k t F U →
      ∀ γ : ℝ → Bridge.Sub hN, IsGeodPQ n (Bridge.conn (hN := hN)) p q γ → Efun (n := n) γ < c →
        bIndex (Set.univ : Set (Fin (k - 1) → Rn n)) (HessPi n (k - 1) F (evalPts k t γ)) =
          lam (n := n) 1 γ ∧
        setDim (bNullSet (Set.univ : Set (Fin (k - 1) → Rn n))
            (HessPi n (k - 1) F (evalPts k t γ))) =
          setDim (bNullSet (TOm (n := n) 1 γ) (HessT (n := n) 1 γ))) ∧
    (∀ (U : Set (Rn 1)) (α : Rn 1 → ℝ → Bridge.Sub hN), IsOpen U → (0 : Rn 1) ∈ U →
      (∀ u ∈ U, α u ∈ OmegaSub (Bridge.conn (hN := hN)) p q k t ∧ Efun (n := n) (α u) < c) →
      (∀ i < k, ContMDiffOn 𝓘(ℝ, Rn 1 × ℝ) 𝓘(ℝ, Rn n) ∞ (fun x : Rn 1 × ℝ => α x.1 x.2)
        (U ×ˢ Set.Icc (t i) (t (i + 1)))) →
      ∀ i < k, IsJacobi (Bridge.conn (hN := hN)) (α 0) (Set.Icc (t i) (t (i + 1)))
        (varField (n := n) α 0))

theorem B_to_B_emb : B → B_emb := fun hB _ _ _ _ _ _ _ _ n _ hN _ =>
  hB n (Bridge.Sub hN) (Bridge.conn (hN := hN)) Bridge.conn_isLC

end RoundTrip.V10_11
