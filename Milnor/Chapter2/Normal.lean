import Milnor.Chapter2.LevelSet
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional

/-!
Milnor, *Topology from the Differentiable Viewpoint*, §2, Lemma 2 (p. 11), second clause.

# The normal space of a regular level set

> **Lemma 2.** The null space of `dfₓ : TMₓ → TN_y` is precisely equal to the tangent space
> `TM'ₓ ⊆ TMₓ` of the submanifold `M' = f⁻¹(y)`. Therefore `dfₓ` maps the orthogonal complement
> of `TM'ₓ` isomorphically onto `TN_y`.

The first clause — that the null space of `dfₓ` is exactly the tangent space of `M' = f⁻¹(y)` — is
`Milnor.mem_range_mfderiv_val_iff` in `Milnor.Chapter2.LevelSet`. This file proves the second
clause. Writing `T` for the tangent space `TM'_p`, realised inside the model space `E ≅ TM_p` as
the range of the derivative of the inclusion `M' → M` (`Milnor.tangentSubspace`), we show that
`df_p` is injective on the orthogonal complement `Tᗮ`
(`Milnor.mfderiv_injOn_tangent_orthogonal`) and carries it onto `TN_y`
(`Milnor.mfderiv_surjOn_tangent_orthogonal`), and bundle the two into the isomorphism
`Milnor.normalEquiv : Tᗮ ≃L[ℝ] F`.

Milnor's `M` sits in some `ℝᵏ`, so his tangent spaces come with an inner product and "orthogonal
complement" needs no comment. For abstract manifolds the inner product has to be put in by hand:
the model space `E` of `M` carries `InnerProductSpace ℝ E` here, in place of the bare
`NormedSpace ℝ E` of `Milnor.Chapter2.LevelSet`, and `Tᗮ` is the orthogonal complement taken in
`E`. Everything else — `M`, `N`, and the boundaryless model with corners `I` — is as general as in
`Milnor.Chapter2.LevelSet`; in particular `N` needs no inner product.

The proof is the dimension count Milnor leaves to the reader. As `y` is a regular value, `df_p` is
onto, so `T = ker df_p` has dimension `dim E - dim F` and hence `dim Tᗮ = dim F`. Injectivity on
`Tᗮ` is immediate from `T ⊓ Tᗮ = ⊥` together with the first clause, and surjectivity then follows
because an injective linear map between spaces of the same finite dimension is onto.
-/

open Set Function Module
open scoped ContDiff Manifold

noncomputable section

namespace Milnor

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {H : Type*} [TopologicalSpace H] {G : Type*} [TopologicalSpace G]
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F G} [I.Boundaryless] [J.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N] [IsManifold J ∞ N]
  {f : M → N}
  {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z]

/-! ### The tangent space of `f⁻¹(y)` inside the model space -/

/-- Milnor's `TM'ₓ ⊆ TMₓ` for `M' = f⁻¹(y)`: the tangent space of the level set at `p`, realised
as a subspace of the model space `E ≅ TM_p`, namely the range of the derivative at `p` of the
inclusion `f⁻¹(y) → M`. -/
def tangentSubspace (hZ : finrank ℝ Z + finrank ℝ F = finrank ℝ E) (hf : ContMDiff I J ∞ f)
    {y : N} (hy : IsRegularValue I J f y) (p : f ⁻¹' {y}) : Submodule ℝ E :=
  letI := (isSliceSubmanifold_preimage hZ hf hy).chartedSpace
  LinearMap.range
    (mfderiv 𝓘(ℝ, Z) I (Subtype.val : f ⁻¹' {y} → M) p : Z →L[ℝ] E).toLinearMap

/-- **Milnor's Lemma 2** (p. 11), first clause, in the notation of this file: a vector of `TM_p`
lies in the tangent space of `f⁻¹(y)` if and only if it is annihilated by `df_p`. This is
`Milnor.mem_range_mfderiv_val_iff` restated for `Milnor.tangentSubspace`. -/
theorem mem_tangentSubspace_iff (hZ : finrank ℝ Z + finrank ℝ F = finrank ℝ E)
    (hf : ContMDiff I J ∞ f) {y : N} (hy : IsRegularValue I J f y) (p : f ⁻¹' {y}) (v : E) :
    v ∈ tangentSubspace hZ hf hy p ↔ mfderiv I J f p.1 v = 0 := by
  simp only [tangentSubspace]
  exact mem_range_mfderiv_val_iff hZ hf hy p v

/-! ### The normal space, and the second clause of Lemma 2 -/

/-- The normal space `Tᗮ` of the level set `f⁻¹(y)` at `p` has the dimension of `TN_y`: indeed
`T = ker df_p` has dimension `dim E - dim F`, because `df_p` is onto at a regular value. -/
theorem finrank_tangentSubspace_orthogonal (hZ : finrank ℝ Z + finrank ℝ F = finrank ℝ E)
    (hf : ContMDiff I J ∞ f) {y : N} (hy : IsRegularValue I J f y) (p : f ⁻¹' {y}) :
    finrank ℝ (tangentSubspace hZ hf hy p)ᗮ = finrank ℝ F := by
  -- `df_p`, read through the models as a linear map `E → F`; it is onto, with kernel `T`.
  obtain ⟨L, hker, hsurj⟩ : ∃ L : E →ₗ[ℝ] F,
      tangentSubspace hZ hf hy p = LinearMap.ker L ∧ Surjective L := by
    refine ⟨(mfderiv I J f p.1 : E →L[ℝ] F).toLinearMap, ?_, hy p.1 p.2⟩
    ext v
    exact mem_tangentSubspace_iff hZ hf hy p v
  have hrk := LinearMap.finrank_range_add_finrank_ker L
  rw [LinearMap.range_eq_top.2 hsurj, finrank_top] at hrk
  refine Submodule.finrank_add_finrank_orthogonal' ?_
  rw [hker]
  omega

/-- **Milnor's Lemma 2** (p. 11), second clause, injectivity: `df_p` is injective on the
orthogonal complement `Tᗮ` of the tangent space `T` of `f⁻¹(y)`. A vector of `Tᗮ` annihilated by
`df_p` lies in `T` by the first clause, hence in `T ⊓ Tᗮ = ⊥`. -/
theorem mfderiv_injOn_tangent_orthogonal (hZ : finrank ℝ Z + finrank ℝ F = finrank ℝ E)
    (hf : ContMDiff I J ∞ f) {y : N} (hy : IsRegularValue I J f y) (p : f ⁻¹' {y}) {v : E}
    (hv : v ∈ (tangentSubspace hZ hf hy p)ᗮ) (h0 : mfderiv I J f p.1 v = 0) : v = 0 :=
  Submodule.disjoint_def.1 (Submodule.orthogonal_disjoint _) v
    ((mem_tangentSubspace_iff hZ hf hy p v).2 h0) hv

/-- **Milnor's Lemma 2** (p. 11), second clause, surjectivity: every vector of `TN_y` is `df_p v`
for some `v` in the orthogonal complement `Tᗮ` of the tangent space of `f⁻¹(y)`. Injectivity on
`Tᗮ` together with `dim Tᗮ = dim TN_y` forces it. -/
theorem mfderiv_surjOn_tangent_orthogonal (hZ : finrank ℝ Z + finrank ℝ F = finrank ℝ E)
    (hf : ContMDiff I J ∞ f) {y : N} (hy : IsRegularValue I J f y) (p : f ⁻¹' {y}) (w : F) :
    ∃ v ∈ (tangentSubspace hZ hf hy p)ᗮ, mfderiv I J f p.1 v = w := by
  -- `df_p`, read through the models as a map `E →L[ℝ] F`, restricted to `Tᗮ`.
  obtain ⟨L, hL⟩ : ∃ L : E →L[ℝ] F, ∀ v, L v = mfderiv I J f p.1 v :=
    ⟨mfderiv I J f p.1, fun _ => rfl⟩
  -- It is injective on `Tᗮ` by the previous result, hence onto for dimension reasons.
  have hinj : Injective (L.toLinearMap.domRestrict (tangentSubspace hZ hf hy p)ᗮ) := by
    rw [injective_iff_map_eq_zero]
    intro u hu
    exact Subtype.ext
      (mfderiv_injOn_tangent_orthogonal hZ hf hy p u.2 ((hL u.1).symm.trans hu))
  obtain ⟨u, hu⟩ := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (finrank_tangentSubspace_orthogonal hZ hf hy p)).1 hinj w
  exact ⟨u.1, u.2, (hL u.1).symm.trans hu⟩

/-- **Milnor's Lemma 2** (p. 11), second clause, in bundled form: `df_p` "maps the orthogonal
complement of `TM'ₓ` isomorphically onto `TN_y`". The underlying map is the restriction of
`mfderiv I J f p.1` to the normal space, see `Milnor.normalEquiv_apply`. -/
def normalEquiv (hZ : finrank ℝ Z + finrank ℝ F = finrank ℝ E) (hf : ContMDiff I J ∞ f)
    {y : N} (hy : IsRegularValue I J f y) (p : f ⁻¹' {y}) :
    (tangentSubspace hZ hf hy p)ᗮ ≃L[ℝ] F :=
  let L : E →L[ℝ] F := mfderiv I J f p.1
  (LinearEquiv.ofBijective (L.toLinearMap.domRestrict (tangentSubspace hZ hf hy p)ᗮ)
    ⟨by
      rw [injective_iff_map_eq_zero]
      intro u hu
      exact Subtype.ext (mfderiv_injOn_tangent_orthogonal hZ hf hy p u.2 hu),
     fun w => by
      obtain ⟨v, hv, hvw⟩ := mfderiv_surjOn_tangent_orthogonal hZ hf hy p w
      exact ⟨⟨v, hv⟩, hvw⟩⟩).toContinuousLinearEquiv

/-- The isomorphism `Milnor.normalEquiv` of Lemma 2 is given by `df_p`. -/
@[simp]
theorem normalEquiv_apply (hZ : finrank ℝ Z + finrank ℝ F = finrank ℝ E)
    (hf : ContMDiff I J ∞ f) {y : N} (hy : IsRegularValue I J f y) (p : f ⁻¹' {y})
    (v : (tangentSubspace hZ hf hy p)ᗮ) :
    normalEquiv hZ hf hy p v = mfderiv I J f p.1 v.1 :=
  rfl

end Milnor
