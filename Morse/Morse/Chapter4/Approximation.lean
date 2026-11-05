import Morse.Chapter4.Focal

/-!
Milnor, *Morse Theory*, §6, p. 37.

# Approximation by Morse functions (Corollary 6.8)

Milnor, p. 37, paraphrased.  **Corollary 6.8.**  *Every bounded smooth `f : M → ℝ` can be
uniformly approximated by a smooth `g` without degenerate critical points; moreover `g` can be
chosen so that on a given compact set `K` its derivatives of order `i ≤ k` uniformly approximate
those of `f`.*  Milnor's proof: choose an embedding `h` of `M` as a bounded subset of some `ℝⁿ`
whose first coordinate is `h₁ = f`; for `c` large choose `p = (−c + ε₁, ε₂, …, εₙ)` near
`(−c, 0, …, 0)` with `L_p` non-degenerate on `h(M)` (Theorem 6.6), and put
`g = (L_p ∘ h − c²)/2c`.  A short computation gives
`g = f + Σ hᵢ²/2c − Σ εᵢhᵢ/c + Σ εᵢ²/2c − ε₁`, close to `f` when `c` is large and the `εᵢ` small.
(Milnor compares M. Morse, Trans. Amer. Math. Soc. 33 (1931).)

## What is proved here

For a slice submanifold `M ⊆ ℝⁿ` (setting of `Morse/Chapter4/NormalBundle.lean`) we prove the
standard variant in which `f` is perturbed by a small linear function:

* `Morse.ae_isMorseFunction_add_inner`: for every smooth `f : M → ℝ` and almost every `a ∈ ℝⁿ`
  (for every Haar measure), `f + ⟪a, ·⟫` is a Morse function on `M`.  No boundedness,
  compactness or closedness is needed.  `Morse.exists_mem_isMorseFunction_add_inner`: such `a`
  exist in every nonempty open subset of `ℝⁿ`.
* `Morse.exists_isMorseFunction_approx`, **Corollary 6.8 for compact `M`**: for every `ε > 0`,
  every finite family of smooth coordinate systems `y_j` of `M` with compact sets `K_j` in their
  domains, and every `r ∈ ℕ`, there is a Morse function `g` (namely `f + ⟪a, ·⟫` with `a` small)
  with `|g − f| < ε` on `M` and every derivative of order `≤ r` of `(g − f) ∘ y_j⁻¹` of norm
  `< ε` on `K_j`.

## The proof

It is Milnor's proof of Theorem 6.6 with `L_p` replaced by `f + ⟪a, ·⟫` and the endpoint map
replaced by `(q, v) ↦ −∇F(q) + v` on `N`, where `F` is a local extension of `f` to an open set of
`ℝⁿ` (`Morse.exists_local_extension_of_contMDiff`: `f` extended to be constant along the slices
of a slice chart).  The point `q` is a critical point of `f + ⟪a, ·⟫` iff `v = a + ∇F(q)` is
normal to `M` at `q`, i.e. iff `a = −∇F(q) + v` with `(q, v) ∈ N`; and the Hessian of
`f + ⟪a, ·⟫` at `q` is minus the form `(ξ, η) ↦ ⟪d(−∇F)(∂x/∂ξ), ∂x/∂η⟫ − ⟪v, ∂²x/∂ξ∂η⟫`, whose
nullity is that of the derivative of the map (`Morse.finrank_ker_mfd_normalEnd`).  A degenerate
critical point thus makes `a` a critical value
(`Morse.mem_image_critPoints_of_not_isNondegenerate`), and Sard's theorem on countably many pieces
of `N` (`Morse.measure_image_inter_critPoints_eq_zero`) shows that these `a` form a null set.
(For `f = ½‖·‖²` this is Theorem 6.6: `½‖x‖² + ⟪a, x⟫ = ½ L_{−a}(x) − ½‖a‖²`.)

## Gaps in Milnor's text, and what is not done

* **The embedding `h`.**  Milnor does not say why an embedding of `M` as a bounded set with
  `h₁ = f` exists.  One can take `h = (f, β ∘ h')` with `h'` any embedding and
  `β(y) = y/√(1 + ‖y‖²)`, a diffeomorphism of the Euclidean space onto its open unit ball; the
  boundedness of `f` is what makes `h(M)` bounded and the error terms `Σ hᵢ²/2c` uniformly small.
* **Derivatives on `M` exist only in charts**, so the approximation of derivatives on `K` must be
  read in fixed coordinate systems covering `K` (finitely many suffice, `K` being compact); this
  is how it is stated here.
* **Non-compact `M`.**  The perturbation `⟪a, ·⟫` is unbounded on an unbounded `M`, so for
  non-compact `M` the results here give approximation on compact sets only.  Uniform
  approximation on all of `M`, for every smooth `f` (bounded or not), is
  `Morse.exists_isMorseFunction_approx_uniform` in `Morse/Chapter4/Uniform.lean`, which perturbs
  by `⟪a, β(·)⟫` with `β` a diffeomorphism of `ℝⁿ` onto its unit ball.  Milnor's own route (the
  image of `h` is a submanifold, and the Morse property transported along `M ≅ h(M)`) is not
  followed, although both ingredients are proved (`Morse/Chapter4/WhitneySlice.lean`,
  `Morse/Chapter4/WhitneyInvariance.lean`).  The passage from abstract manifolds to submanifolds
  of Euclidean space is `Morse/Chapter4/Whitney.lean`: `Morse.ae_isMorseFunction_add_inner_comp`
  for any embedding, and, through Mathlib's Whitney embedding for compact manifolds,
  `Morse.exists_isMorseFunction_approx_of_compactSpace` (Corollary 6.8 for abstract compact
  manifolds).
-/

open Set Filter Topology Function Module MeasureTheory
open scoped ContDiff Manifold RealInnerProductSpace

noncomputable section

local notation "𝔼" n:max => EuclideanSpace ℝ (Fin n)

namespace Morse

open Milnor.Problems (normalBundleSet normalSum isSliceSubmanifold_normalBundle)

/-! ### Gradients -/

section Gradient

variable (n : ℕ)

/-- The Riesz isomorphism `ℝⁿ ≅ (ℝⁿ)*`, `u ↦ ⟪u, ·⟫`. -/
def rieszEquiv : 𝔼 n ≃L[ℝ] (𝔼 n →L[ℝ] ℝ) :=
  ContinuousLinearEquiv.ofBijective (innerBilin n)
    (by
      rw [LinearMap.ker_eq_bot']
      intro u hu
      have h := congrArg (fun ℓ : 𝔼 n →L[ℝ] ℝ => ℓ u) hu
      simp only [ContinuousLinearMap.coe_coe, innerBilin_apply, _root_.zero_apply,
        inner_self_eq_zero] at h
      exact h)
    (by
      rw [LinearMap.range_eq_top]
      intro ℓ
      obtain ⟨u, hu⟩ := (InnerProductSpace.toDual ℝ (𝔼 n)).surjective ℓ
      refine ⟨u, ContinuousLinearMap.ext fun v => ?_⟩
      rw [← hu]
      rfl)

variable {n}

@[simp] theorem rieszEquiv_apply (u v : 𝔼 n) : rieszEquiv n u v = ⟪u, v⟫ := rfl

theorem inner_rieszEquiv_symm_apply (ℓ : 𝔼 n →L[ℝ] ℝ) (v : 𝔼 n) :
    ⟪(rieszEquiv n).symm ℓ, v⟫ = ℓ v := by
  rw [← rieszEquiv_apply, ContinuousLinearEquiv.apply_symm_apply]

/-- The negative gradient `−∇F`. -/
def negGrad (F : 𝔼 n → ℝ) (y : 𝔼 n) : 𝔼 n := -(rieszEquiv n).symm (fderiv ℝ F y)

theorem inner_negGrad (F : 𝔼 n → ℝ) (y u : 𝔼 n) : ⟪negGrad F y, u⟫ = -fderiv ℝ F y u := by
  rw [negGrad, inner_neg_left, inner_rieszEquiv_symm_apply]

theorem contDiffOn_negGrad {F : 𝔼 n → ℝ} {U : Set (𝔼 n)} (hU : IsOpen U)
    (hF : ContDiffOn ℝ ∞ F U) : ContDiffOn ℝ ∞ (negGrad F) U :=
  ((rieszEquiv n).symm.contDiff.comp_contDiffOn
    (hF.fderiv_of_isOpen hU (by simp))).neg

theorem hasFDerivAt_negGrad {F : 𝔼 n → ℝ} {y : 𝔼 n} (hF : ContDiffAt ℝ 2 F y) :
    HasFDerivAt (negGrad F) (-((rieszEquiv n).symm : (𝔼 n →L[ℝ] ℝ) →L[ℝ] 𝔼 n).comp
      (hessian F y)) y := by
  have h1 : HasFDerivAt (fderiv ℝ F) (hessian F y) y :=
    ((hF.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)).hasFDerivAt
  exact (((rieszEquiv n).symm : (𝔼 n →L[ℝ] ℝ) →L[ℝ] 𝔼 n).hasFDerivAt.comp y h1).neg

/-- The derivative of `−∇F` is minus the Hessian: `⟪d(−∇F)_y u, w⟫ = −d²F_y(u, w)`. -/
theorem inner_fderiv_negGrad {F : 𝔼 n → ℝ} {y : 𝔼 n} (hF : ContDiffAt ℝ 2 F y) (u v : 𝔼 n) :
    ⟪fderiv ℝ (negGrad F) y u, v⟫ = -hessian F y u v := by
  rw [(hasFDerivAt_negGrad hF).fderiv]
  simp only [_root_.neg_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearEquiv.coe_coe, inner_neg_left, inner_rieszEquiv_symm_apply]

end Gradient

/-! ### The local argument -/

section Local

variable {n k w : ℕ} {M : Set (𝔼 n)}
  {hM : Milnor.IsSliceSubmanifold 𝓘(ℝ, 𝔼 n) (𝔼 k) (𝔼 w) M}

/-- An endomorphism of `ℝⁿ` has a nontrivial kernel iff it is not surjective. -/
theorem finrank_ker_pos_iff_not_surjective (L : 𝔼 n →L[ℝ] 𝔼 n) :
    0 < finrank ℝ (LinearMap.ker (L : 𝔼 n →ₗ[ℝ] 𝔼 n)) ↔ ¬ Surjective L := by
  rw [Nat.pos_iff_ne_zero, Ne, Submodule.finrank_eq_zero, LinearMap.ker_eq_bot,
    LinearMap.injective_iff_surjective]
  rfl

/-- The Hessian of `G` read in Milnor's parametrization at `q` (the second-order chain rule,
`Morse.hessian_comp_apply`). -/
theorem hessian_comp_xParam (q : M) {G : 𝔼 n → ℝ} (hG : ContDiffAt ℝ 2 G q) (ξ η : 𝔼 k) :
    hessian (G ∘ xParam hM q) (uParam hM q) ξ η =
      hessian G q (dParam hM q ξ) (dParam hM q η) + fderiv ℝ G q (d2Param hM q ξ η) := by
  have hG' : ContDiffAt ℝ 2 G (xParam hM q (uParam hM q)) := by rwa [xParam_uParam]
  have h := hessian_comp_apply hG' ((contDiffAt_xParam hM q).of_le (by norm_cast)) ξ η
  rw [xParam_uParam] at h
  exact h

/-- Adding a linear function does not change the Hessian. -/
theorem hessian_add_inner {F : 𝔼 n → ℝ} {y : 𝔼 n} (hF : ContDiffAt ℝ 2 F y) (a : 𝔼 n) :
    hessian (fun z => F z + ⟪a, z⟫) y = hessian F y := by
  have hev : fderiv ℝ (fun z => F z + ⟪a, z⟫) =ᶠ[𝓝 y] fun z => fderiv ℝ F z + innerBilin n a := by
    filter_upwards [hF.eventually (by simp)] with z hz
    exact ((hz.differentiableAt (by simp)).hasFDerivAt.add (innerBilin n a).hasFDerivAt).fderiv
  rw [hessian, hev.fderiv_eq, fderiv_add_const]
  rfl

theorem fderiv_add_inner {F : 𝔼 n → ℝ} {y : 𝔼 n} (hF : DifferentiableAt ℝ F y) (a u : 𝔼 n) :
    fderiv ℝ (fun z => F z + ⟪a, z⟫) y u = ⟪a - negGrad F y, u⟫ := by
  have h : HasFDerivAt (fun z => F z + ⟪a, z⟫) (fderiv ℝ F y + innerBilin n a) y :=
    hF.hasFDerivAt.add (innerBilin n a).hasFDerivAt
  rw [h.fderiv, inner_sub_left, inner_negGrad]
  simp only [_root_.add_apply, innerBilin_apply]
  ring

/-- **The local argument.**  Let `F` be smooth on an open set `U ⊆ ℝⁿ` and agree with `f` on
`M ∩ U`.  If `q ∈ M ∩ U` is a degenerate critical point of `f + ⟪a, ·⟫`, then `a` is a critical
value of the map `(q', v) ↦ −∇F(q') + v` on the part of the normal bundle over `U`: precisely,
`(q, a + ∇F(q))` is a critical point of it, with image `a`.  As for `L_p` (Lemma 6.5), the nullity
of the Hessian equals the nullity of the derivative of this map. -/
theorem mem_image_critPoints_of_not_isNondegenerate (hkw : k + w = n)
    {U : Set (𝔼 n)} (hU : IsOpen U) {F : 𝔼 n → ℝ} (hF : ContDiffOn ℝ ∞ F U)
    {f : M → ℝ} (hf : letI := hM.chartedSpace; ContMDiff 𝓘(ℝ, 𝔼 k) 𝓘(ℝ, ℝ) ∞ f)
    (hfF : ∀ x : M, (x : 𝔼 n) ∈ U → f x = F x) {a : 𝔼 n} {q : M} (hqU : (q : 𝔼 n) ∈ U)
    (hcrit : letI := hM.chartedSpace;
      IsCriticalPointM (𝔼 k) (fun x : M => f x + ⟪a, (x : 𝔼 n)⟫) q)
    (hdeg : letI := hM.chartedSpace;
      ¬ IsNondegenerate (hessianM (𝔼 k) (fun x : M => f x + ⟪a, (x : 𝔼 n)⟫) q)) :
    letI := (isSliceSubmanifold_normalBundle hM hkw).chartedSpace
    a ∈ normalEnd hM (negGrad F) '' ({x | x.1.1 ∈ U} ∩
      Milnor.critPoints 𝓘(ℝ, 𝔼 n) 𝓘(ℝ, 𝔼 n) (normalEnd hM (negGrad F))) := by
  let := hM.chartedSpace
  have := hM.isManifold
  set g : M → ℝ := fun x => f x + ⟪a, (x : 𝔼 n)⟫ with hg
  set G : 𝔼 n → ℝ := fun y => F y + ⟪a, y⟫ with hG
  have hFq : ContDiffAt ℝ ∞ F q := hF.contDiffAt (hU.mem_nhds hqU)
  have hGq : ContDiffAt ℝ ∞ G q := hFq.add (innerBilin n a).contDiff.contDiffAt
  -- `g = G` on `M` near `q`
  have hev : g =ᶠ[𝓝 q] G ∘ Subtype.val := by
    filter_upwards [(hU.preimage continuous_subtype_val).mem_nhds hqU] with x hx
    simp only [hg, hG, comp_apply, hfF x hx]
  -- the critical point condition: `v = a + ∇F(q)` is normal to `M` at `q`
  have hcritG : IsCriticalPointM (𝔼 k) (G ∘ Subtype.val) q := by
    have h : mfderiv 𝓘(ℝ, 𝔼 k) 𝓘(ℝ, ℝ) g q = 0 := hcrit
    rw [hev.mfderiv_eq] at h
    exact h
  rw [isCriticalPointM_comp_val_iff_forall_tangent hM (hGq.differentiableAt (by simp))] at hcritG
  set v := a - negGrad F q with hv
  have hvperp : v ∈ (tangentSubspace hM q)ᗮ := by
    rw [Submodule.mem_orthogonal']
    intro u hu
    rw [← fderiv_add_inner (hFq.differentiableAt (by simp))]
    exact hcritG u hu
  have hmem : ((q : 𝔼 n), v) ∈ normalBundleSet hM := (mem_normalBundleSet_iff hM).2 ⟨q.2, hvperp⟩
  refine ⟨⟨_, hmem⟩, ⟨hqU, ?_⟩, ?_⟩
  · -- `(q, v)` is a critical point: the nullity of the derivative is that of the Hessian
    let := (isSliceSubmanifold_normalBundle hM hkw).chartedSpace
    have hΓ : DifferentiableAt ℝ (negGrad F) q :=
      ((contDiffOn_negGrad hU hF).contDiffAt (hU.mem_nhds hqU)).differentiableAt (by simp)
    change ¬ Surjective (Milnor.mfd 𝓘(ℝ, 𝔼 n) 𝓘(ℝ, 𝔼 n) (normalEnd hM (negGrad F)) ⟨_, hmem⟩)
    rw [← finrank_ker_pos_iff_not_surjective, finrank_ker_mfd_normalEnd hM hkw ⟨_, hmem⟩ hΓ]
    have hgC2 : ContMDiffAt 𝓘(ℝ, 𝔼 k) 𝓘(ℝ, ℝ) 2 g q :=
      ((hf.add (contMDiff_comp_val hM (innerBilin n a).contDiff)) q).of_le (by norm_cast)
    have hnull : nullityM (𝔼 k) g q =
        nullity (normalForm hM (fderiv ℝ (negGrad F) q) q v) := by
      set σ := Milnor.Tub.σ hM q with hσ
      have hy := isSmoothCoord_toChart hM σ
      rw [← hy.nullity_eq (Milnor.Tub.mem_source hM q) hgC2 hcrit]
      have hz : σ.toChart q ∈ σ.toChart.target :=
        toChart_apply_mem_target σ (Milnor.Tub.mem_source hM q)
      have hev2 : g ∘ σ.toChart.symm =ᶠ[𝓝 (σ.toChart q)] G ∘ xParam hM q := by
        have ht : Tendsto σ.toChart.symm (𝓝 (σ.toChart q)) (𝓝 q) := by
          have := (σ.toChart.continuousAt_symm hz).tendsto
          rwa [σ.toChart.left_inv (Milnor.Tub.mem_source hM q)] at this
        exact (hev.comp_tendsto ht).trans (comp_val_comp_toChart_symm_eventuallyEq σ G hz)
      rw [hessian_congr hev2]
      have hH : hessian (G ∘ xParam hM q) (uParam hM q) =
          (-1 : ℝ) • normalForm hM (fderiv ℝ (negGrad F) q) q v := by
        ext ξ η
        rw [hessian_comp_xParam q (hGq.of_le (by norm_cast)),
          hessian_add_inner (hFq.of_le (by norm_cast)) a,
          fderiv_add_inner (hFq.differentiableAt (by simp)),
          ← neg_neg (hessian F q (dParam hM q ξ) (dParam hM q η)),
          ← inner_fderiv_negGrad (hFq.of_le (by norm_cast))]
        simp only [FunLike.coe_smul, Pi.smul_apply, normalForm_apply, smul_eq_mul]
        ring
      change nullity (hessian (G ∘ xParam hM q) (uParam hM q)) = _
      rw [hH, nullity_smul_of_ne_zero (by norm_num)]
    change 0 < nullity (normalForm hM (fderiv ℝ (negGrad F) q) q v)
    rw [← hnull]
    have h0 := (isNondegenerate_hessianM_iff_nullityM_eq_zero (E := 𝔼 k) (f := g) (p := q)).not.1
      hdeg
    omega
  · change negGrad F q + (a - negGrad F q) = a
    abel

end Local

/-! ### `f + ⟪a, ·⟫` is a Morse function for almost every `a` -/

section Global

variable {n k w : ℕ} {M : Set (𝔼 n)}
  (hM : Milnor.IsSliceSubmanifold 𝓘(ℝ, 𝔼 n) (𝔼 k) (𝔼 w) M)

/-- **Local extensions.**  A smooth function on `M` extends, near each point `p ∈ M`, to a smooth
function on an open subset of `ℝⁿ`: in the slice chart `σ` at `p`, put
`F(y) = f(σ⁻¹((σ y)₁, 0))`, i.e. extend `f` to be constant along the slices
`{(σ y)₁ = const}`. -/
theorem exists_local_extension_of_contMDiff {f : M → ℝ}
    (hf : letI := hM.chartedSpace; ContMDiff 𝓘(ℝ, 𝔼 k) 𝓘(ℝ, ℝ) ∞ f) (p : M) :
    ∃ U : Set (𝔼 n), IsOpen U ∧ (p : 𝔼 n) ∈ U ∧ ∃ F : 𝔼 n → ℝ, ContDiffOn ℝ ∞ F U ∧
      ∀ x : M, (x : 𝔼 n) ∈ U → f x = F x := by
  let := hM.chartedSpace
  have := hM.isManifold
  set σ := Milnor.Tub.σ hM p with hσ
  refine ⟨Milnor.Problems.NormalAux.V hM p, Milnor.Problems.NormalAux.isOpen_V hM p,
    Milnor.Problems.NormalAux.mem_V hM p, fun y => f (σ.toChart.symm ((σ.φ y).1)), ?_, ?_⟩
  · have h1 : ContDiffOn ℝ ∞ (f ∘ σ.toChart.symm) σ.toChart.target := by
      rw [← contMDiffOn_iff_contDiffOn]
      exact hf.comp_contMDiffOn (isSmoothCoord_toChart hM σ).contMDiffOn_symm
    have h2 : ContDiffOn ℝ ∞ (fun y => (σ.φ y).1) (Milnor.Problems.NormalAux.V hM p) :=
      contDiff_fst.comp_contDiffOn ((Milnor.Tub.contDiffOn_σφ hM p).mono inter_subset_left)
    exact h1.comp h2 fun y hy => hy.2
  · intro x hx
    have hxs : x ∈ σ.toChart.source := hx.1
    change f x = f (σ.toChart.symm (σ.toChart x))
    rw [σ.toChart.left_inv hxs]

/-- **`f + ⟪a, ·⟫` is a Morse function for almost every `a ∈ ℝⁿ`** (the standard substitute for
Milnor's Corollary 6.8; see the module docstring).  `M` is any slice submanifold of `ℝⁿ` and
`f : M → ℝ` any smooth function; the exceptional set of `a` is null for every Haar measure.
Proof: near each point, `f` extends to a smooth `F` on an open `U ⊆ ℝⁿ`, and a degenerate critical
point `q ∈ U` of `f + ⟪a, ·⟫` makes `a` a critical value of `(q', v) ↦ −∇F(q') + v` on the normal
bundle over `U` (`Morse.mem_image_critPoints_of_not_isNondegenerate`); countably many such `U`
cover `M`, and each set of critical values is null by Sard's theorem. -/
theorem ae_isMorseFunction_add_inner (μ : Measure (𝔼 n)) [μ.IsAddHaarMeasure] {f : M → ℝ}
    (hf : letI := hM.chartedSpace; ContMDiff 𝓘(ℝ, 𝔼 k) 𝓘(ℝ, ℝ) ∞ f) :
    letI := hM.chartedSpace
    ∀ᵐ a ∂μ, IsMorseFunction (𝔼 k) (fun x : M => f x + ⟪a, (x : 𝔼 n)⟫) := by
  let := hM.chartedSpace
  have := hM.isManifold
  have hsmooth : ∀ a : 𝔼 n, ContMDiff 𝓘(ℝ, 𝔼 k) 𝓘(ℝ, ℝ) ∞
      (fun x : M => f x + ⟪a, (x : 𝔼 n)⟫) :=
    fun a => hf.add (contMDiff_comp_val hM (innerBilin n a).contDiff)
  rcases M.eq_empty_or_nonempty with hempty | hne
  · subst hempty
    exact Eventually.of_forall fun a => ⟨hsmooth a, fun q => absurd q.2 (notMem_empty _)⟩
  have hkw := slice_dim_add_eq_of_nonempty hM hne
  choose U hUo hpU F hF hfF using exists_local_extension_of_contMDiff hM hf
  obtain ⟨s, hs_count, hs_cover⟩ := TopologicalSpace.countable_cover_nhds
    (f := fun p : M => Subtype.val ⁻¹' U p)
    fun p => ((hUo p).preimage continuous_subtype_val).mem_nhds (hpU p)
  let := (isSliceSubmanifold_normalBundle hM hkw).chartedSpace
  have := (isSliceSubmanifold_normalBundle hM hkw).isManifold
  have hnull : ∀ p : M, μ (normalEnd hM (negGrad (F p)) '' ({x | x.1.1 ∈ U p} ∩
      Milnor.critPoints 𝓘(ℝ, 𝔼 n) 𝓘(ℝ, 𝔼 n) (normalEnd hM (negGrad (F p))))) = 0 := fun p =>
    measure_image_inter_critPoints_eq_zero μ
      ((hUo p).preimage (continuous_fst.comp continuous_subtype_val))
      (contMDiffOn_normalEnd hM hkw (contDiffOn_negGrad (hUo p) (hF p)))
  rw [ae_iff]
  refine measure_mono_null ?_ ((measure_biUnion_null_iff hs_count).2 fun p _ => hnull p)
  intro a ha
  have hex : ∃ q : M, IsCriticalPointM (𝔼 k) (fun x : M => f x + ⟪a, (x : 𝔼 n)⟫) q ∧
      ¬ IsNondegenerate (hessianM (𝔼 k) (fun x : M => f x + ⟪a, (x : 𝔼 n)⟫) q) := by
    by_contra hcon
    push Not at hcon
    exact ha ⟨hsmooth a, hcon⟩
  obtain ⟨q, hcrit, hdeg⟩ := hex
  have hq : q ∈ ⋃ p ∈ s, Subtype.val ⁻¹' U p := by rw [hs_cover]; exact mem_univ q
  obtain ⟨p, hps, hqp⟩ := mem_iUnion₂.1 hq
  exact mem_iUnion₂.2 ⟨p, hps, mem_image_critPoints_of_not_isNondegenerate hkw (hUo p) (hF p) hf
    (hfF p) hqp hcrit hdeg⟩

/-- The `a` for which `f + ⟪a, ·⟫` is a Morse function are dense: every nonempty open set of
`ℝⁿ` contains one. -/
theorem exists_mem_isMorseFunction_add_inner {f : M → ℝ}
    (hf : letI := hM.chartedSpace; ContMDiff 𝓘(ℝ, 𝔼 k) 𝓘(ℝ, ℝ) ∞ f) {V : Set (𝔼 n)}
    (hV : IsOpen V) (hne : V.Nonempty) :
    letI := hM.chartedSpace
    ∃ a ∈ V, IsMorseFunction (𝔼 k) (fun x : M => f x + ⟪a, (x : 𝔼 n)⟫) := by
  let := hM.chartedSpace
  have hpos : (volume : Measure (𝔼 n)) V ≠ 0 := (hV.measure_pos volume hne).ne'
  exact Measure.exists_mem_of_measure_ne_zero_of_ae hpos
    (ae_restrict_of_ae (ae_isMorseFunction_add_inner hM volume hf))

end Global

/-! ### Corollary 6.8 for compact `M` -/

section Compact

variable {n k w : ℕ} {M : Set (𝔼 n)}
  (hM : Milnor.IsSliceSubmanifold 𝓘(ℝ, 𝔼 n) (𝔼 k) (𝔼 w) M)

/-- The iterated derivatives of the inclusion `M → ℝⁿ`, read in a smooth coordinate system `y`, are
bounded on every compact subset of the coordinate domain. -/
theorem exists_bound_iteratedFDeriv_val_comp_symm {y : OpenPartialHomeomorph M (𝔼 k)}
    (hy : letI := hM.chartedSpace; IsSmoothCoord (𝔼 k) y) {K : Set (𝔼 k)} (hK : IsCompact K)
    (hKy : K ⊆ y.target) (i : ℕ) :
    ∃ C, ∀ u ∈ K, ‖iteratedFDeriv ℝ i ((Subtype.val : M → 𝔼 n) ∘ y.symm) u‖ ≤ C := by
  let := hM.chartedSpace
  have := hM.isManifold
  have hsm : ContDiffOn ℝ ∞ ((Subtype.val : M → 𝔼 n) ∘ y.symm) y.target := by
    rw [← contMDiffOn_iff_contDiffOn]
    exact hM.contMDiff_val.comp_contMDiffOn hy.contMDiffOn_symm
  have hcont : ContinuousOn (iteratedFDeriv ℝ i ((Subtype.val : M → 𝔼 n) ∘ y.symm)) y.target :=
    (hsm.continuousOn_iteratedFDerivWithin (m := i) (by exact_mod_cast le_top)
      y.open_target.uniqueDiffOn).congr fun u hu =>
      (iteratedFDerivWithin_of_isOpen i y.open_target hu).symm
  exact hK.exists_bound_of_continuousOn (hcont.mono hKy)

/-- **Corollary 6.8** (Milnor, p. 37) **for a compact submanifold** `M ⊆ ℝⁿ`: every smooth
`f : M → ℝ` can be uniformly approximated by a Morse function `g`, and `g` can be chosen so that,
in finitely many given coordinate systems `y_j` and on given compact subsets `K_j` of their
domains, the derivatives of order `≤ r` of `g` are uniformly close to those of `f`.  One can take
`g = f + ⟪a, ·⟫` with `a` small (`Morse.ae_isMorseFunction_add_inner`). -/
theorem exists_isMorseFunction_approx (hc : IsCompact M) {f : M → ℝ}
    (hf : letI := hM.chartedSpace; ContMDiff 𝓘(ℝ, 𝔼 k) 𝓘(ℝ, ℝ) ∞ f)
    {ι : Type*} [Finite ι] (y : ι → OpenPartialHomeomorph M (𝔼 k))
    (hy : letI := hM.chartedSpace; ∀ j, IsSmoothCoord (𝔼 k) (y j)) (K : ι → Set (𝔼 k))
    (hK : ∀ j, IsCompact (K j)) (hKy : ∀ j, K j ⊆ (y j).target) (r : ℕ) {ε : ℝ} (hε : 0 < ε) :
    letI := hM.chartedSpace
    ∃ g : M → ℝ, IsMorseFunction (𝔼 k) g ∧ (∀ x, |g x - f x| < ε) ∧
      ∀ j, ∀ i ≤ r, ∀ u ∈ K j,
        ‖iteratedFDeriv ℝ i ((fun x => g x - f x) ∘ (y j).symm) u‖ < ε := by
  let := hM.chartedSpace
  have := hM.isManifold
  have := Fintype.ofFinite ι
  -- bounds for `‖x‖` on `M` and for the derivatives of the inclusion in the charts
  obtain ⟨R, hR⟩ := hc.exists_bound_of_continuousOn continuous_norm.continuousOn
  choose C hC using fun j i =>
    exists_bound_iteratedFDeriv_val_comp_symm hM (hy j) (hK j) (hKy j) i
  obtain ⟨D, hD0, hRD, hCD⟩ : ∃ D : ℝ, 0 ≤ D ∧ (∀ x : M, ‖(x : 𝔼 n)‖ ≤ D) ∧
      ∀ j, ∀ i ≤ r, C j i ≤ D := by
    refine ⟨|R| + ∑ j, ∑ i ∈ Finset.range (r + 1), |C j i|, by positivity, fun x => ?_,
      fun j i hi => ?_⟩
    · have h1 := hR x x.2
      rw [norm_norm] at h1
      have h2 : 0 ≤ ∑ j, ∑ i ∈ Finset.range (r + 1), |C j i| := by positivity
      linarith [le_abs_self R]
    · have h1 : |C j i| ≤ ∑ i ∈ Finset.range (r + 1), |C j i| :=
        Finset.single_le_sum (f := fun i => |C j i|) (fun _ _ => abs_nonneg _)
          (Finset.mem_range.2 (Nat.lt_succ_of_le hi))
      have h2 : ∑ i ∈ Finset.range (r + 1), |C j i| ≤
          ∑ j, ∑ i ∈ Finset.range (r + 1), |C j i| :=
        Finset.single_le_sum (f := fun j => ∑ i ∈ Finset.range (r + 1), |C j i|)
          (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ j)
      linarith [le_abs_self (C j i), abs_nonneg R]
  -- a small `a` with `f + ⟪a, ·⟫` Morse
  obtain ⟨δ, hδ0, hδD⟩ : ∃ δ : ℝ, 0 < δ ∧ δ * D < ε := by
    refine ⟨ε / (D + 1), div_pos hε (by linarith), ?_⟩
    rw [div_mul_eq_mul_div, div_lt_iff₀ (by linarith)]
    nlinarith
  obtain ⟨a, ha, hmorse⟩ := exists_mem_isMorseFunction_add_inner hM hf Metric.isOpen_ball
    (Metric.nonempty_ball.2 hδ0)
  have ha' : ‖a‖ < δ := by
    rw [Metric.mem_ball, dist_zero_right] at ha
    exact ha
  have hdiff : ∀ x : M, (f x + ⟪a, (x : 𝔼 n)⟫) - f x = innerBilin n a x := fun x => by
    rw [innerBilin_apply]
    ring
  have hnorm : ‖innerBilin n a‖ ≤ ‖a‖ :=
    ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg a) fun v => by
      rw [innerBilin_apply]
      exact norm_inner_le_norm a v
  refine ⟨fun x => f x + ⟪a, (x : 𝔼 n)⟫, hmorse, fun x => ?_, fun j i hi u hu => ?_⟩
  · rw [hdiff, innerBilin_apply, ← Real.norm_eq_abs]
    calc ‖⟪a, (x : 𝔼 n)⟫‖ ≤ ‖a‖ * ‖(x : 𝔼 n)‖ := norm_inner_le_norm _ _
      _ ≤ δ * D := mul_le_mul ha'.le (hRD x) (norm_nonneg _) hδ0.le
      _ < ε := hδD
  · have hfun : (fun x : M => (f x + ⟪a, (x : 𝔼 n)⟫) - f x) ∘ (y j).symm =
        innerBilin n a ∘ ((Subtype.val : M → 𝔼 n) ∘ (y j).symm) := by
      funext u
      exact hdiff _
    have hsm : ContDiffAt ℝ ∞ ((Subtype.val : M → 𝔼 n) ∘ (y j).symm) u := by
      have h : ContDiffOn ℝ ∞ ((Subtype.val : M → 𝔼 n) ∘ (y j).symm) (y j).target := by
        rw [← contMDiffOn_iff_contDiffOn]
        exact hM.contMDiff_val.comp_contMDiffOn (hy j).contMDiffOn_symm
      exact h.contDiffAt ((y j).open_target.mem_nhds (hKy j hu))
    rw [hfun, (innerBilin n a).iteratedFDeriv_comp_left hsm (by exact_mod_cast le_top)]
    calc _ ≤ ‖innerBilin n a‖ * ‖iteratedFDeriv ℝ i ((Subtype.val : M → 𝔼 n) ∘ (y j).symm) u‖ :=
          ContinuousLinearMap.norm_compContinuousMultilinearMap_le _ _
      _ ≤ δ * D := mul_le_mul (hnorm.trans ha'.le) ((hC j i u hu).trans (hCD j i hi))
          (norm_nonneg _) hδ0.le
      _ < ε := hδD

end Compact

end Morse
