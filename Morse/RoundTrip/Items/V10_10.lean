import Morse
import RoundTrip.Check
import RoundTrip.Blind.V10_10
import RoundTrip.Bridge

open Set Filter Topology
open scoped ContDiff Manifold

namespace RoundTrip.V10_10

/-- The project's statement (universes instantiated at `0`). For a slice submanifold `N ⊆ V` with
the induced metric and `B : Morse.BrokenSetup hN p q c m` (Milnor's §16 data, with the project's
choice of `δ`: unique short joins AND normal radii `≥ δ` on `S`, `c·(t_{i+1} − t_i) < δ²`), and
break points `y ∈ B.nodes` whose broken geodesic `B.path y` is an unbroken geodesic:
* `IsJacobiField.comp_affine`: Jacobi fields are preserved by affine reparametrization;
* `energy'_nodeVal_le`: `E'(γ(t₁), …, γ(t_m)) ≤ E(γ)` for `γ ∈ Ω`;
* `not_isConjugate_seg`: `γ(tᵢ)`, `γ(t_{i+1})` are not conjugate along `γ`;
* `brokenNodeMap_bijective`: `X ↦ (X(t₁), …, X(t_m))` is a linear bijection from the broken Jacobi
  fields `brokenSpace B.breaks 1` onto `⊕_j T_{y_j}N` (i.e. `TB_γ`);
* `energyHessian_nodeZero_pos`: `E_** > 0` on non-zero fields of `TΩ_γ` vanishing at the `tᵢ`;
* `formIndex_brokenSpace`, `finrank_ker_brokenSpace`: index and nullity of the formula-defined
  `E_**` (`Morse.energyHessian`) on `TΩ_γ` equal those of its restriction to the broken Jacobi
  fields. -/
def A : Prop :=
  type_of% @Morse.IsJacobiField.comp_affine.{0, 0, 0} ∧
    type_of% @Morse.BrokenSetup.energy'_nodeVal_le.{0, 0, 0} ∧
    type_of% @Morse.BrokenSetup.not_isConjugate_seg.{0, 0, 0} ∧
    type_of% @Morse.BrokenSetup.brokenNodeMap_bijective.{0, 0, 0} ∧
    type_of% @Morse.BrokenSetup.energyHessian_nodeZero_pos.{0, 0, 0} ∧
    type_of% @Morse.BrokenSetup.formIndex_brokenSpace.{0, 0, 0} ∧
    type_of% @Morse.BrokenSetup.finrank_ker_brokenSpace.{0, 0, 0}

theorem A_holds : A :=
  ⟨@Morse.IsJacobiField.comp_affine, @Morse.BrokenSetup.energy'_nodeVal_le,
    @Morse.BrokenSetup.not_isConjugate_seg, @Morse.BrokenSetup.brokenNodeMap_bijective,
    @Morse.BrokenSetup.energyHessian_nodeZero_pos, @Morse.BrokenSetup.formIndex_brokenSpace,
    @Morse.BrokenSetup.finrank_ker_brokenSpace⟩

/-! Neither `A → B` nor `B → A` is proved; see `V10_10.json`. Beyond the setting (abstract
Riemannian manifolds vs slice submanifolds with the induced metric):

* B's `E_**` is `HessT 1 γ`, the choice function of Milnor's variational relation (Fréchet mixed
  partial of `E ∘ α` for some 2-parameter variation, junk `0` when no variation realizes a pair);
  A's is the formula-defined `Morse.energyHessian`. `RoundTrip/EnergyC2.lean` now supplies the
  analysis (`u ↦ E(α u)` is `C^∞`, `fderiv_fderiv_apply_energy_eq_energyHessian`), but the
  identification on `↥N` still needs a 2-parameter variation dictionary (blind `IsVarSubT` over
  `Rn 2` into `↥N` ⇔ `Morse.IsVariation`, `varField` ⇔ partial fields, at every `t ∈ ℝ`),
  existence of realizing variations for every pair of `TΩ` (`Morse.exists_variation_two`, lifted),
  and a `TΩ` dictionary (`TOm 1 γ` / `BrokenSet` ⇔ `pathTangent` / `brokenSpace`).
* B's subdivision is Milnor's (`Setup16`: `ε` from Lemma 10.8 — unique short geodesics depending
  smoothly on the end points — and `t_{i+1} − tᵢ < ε²/c`); A's is a `BrokenSetup`, whose `δ`
  also carries normal radii `≥ δ` on `S`. A `Setup16` subdivision need not carry a `BrokenSetup`
  (the project's `δ` may be smaller than `ε`), so A's non-conjugacy and Lemma 15.3/15.4 for the
  segments are not available for B's subdivisions: this is a genuine gap even on `↥N`, independent
  of the Hessian.
* A's lemmas `comp_affine`, `energy'_nodeVal_le`, `energyHessian_nodeZero_pos`,
  `not_isConjugate_seg` are not stated by B.

The linear algebra of B's index/nullity on a subspace (B's `bIndex T H = formIndex (H.restrict T)`,
B's nullity `= rank ker (H.restrict T)`) is proved in `Items/V9_19.lean` (`LinAlg`).

## The embedded special case (stated, not proved) -/

/-- B on embedded manifolds: `M = ↥N` (model `ℝⁿ`, induced metric), induced connection. -/
def B_emb : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    (W : Type) [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W] (n : ℕ)
    (N : Set V) (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) (Rn n) W N)
    [ConnectedSpace (Bridge.Sub hN)], MetricComplete n (Bridge.Sub hN) →
  ∀ (p q : Bridge.Sub hN) (c ε : ℝ) (k : ℕ) (t : ℕ → ℝ),
    Setup16 n (Bridge.conn (hN := hN)) p q c ε k t →
    ∀ γ : ℝ → Bridge.Sub hN, IsGeodPQ n (Bridge.conn (hN := hN)) p q γ → Efun (n := n) γ < c →
      Set.BijOn (fun X : FA n γ => fun j : Fin (k - 1) => (X (t ((j : ℕ) + 1)) : Rn n))
        (BrokenSet (Bridge.conn (hN := hN)) γ 1 k t) Set.univ ∧
      bIndex (BrokenSet (Bridge.conn (hN := hN)) γ 1 k t) (HessT (n := n) 1 γ) =
        bIndex (TOm (n := n) 1 γ) (HessT (n := n) 1 γ) ∧
      setDim (bNullSet (BrokenSet (Bridge.conn (hN := hN)) γ 1 k t) (HessT (n := n) 1 γ)) =
        setDim (bNullSet (TOm (n := n) 1 γ) (HessT (n := n) 1 γ))

theorem B_to_B_emb : B → B_emb := fun hB _ _ _ _ _ _ _ _ n _ hN _ =>
  hB n (Bridge.Sub hN) (Bridge.conn (hN := hN)) Bridge.conn_isLC

end RoundTrip.V10_10
