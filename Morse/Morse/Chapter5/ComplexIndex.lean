import Morse.Chapter5.IndexBound
import Morse.Chapter7.GeodesicLocal

/-!
Milnor, *Morse Theory*, §7, pp. 39–41; Exposition/Chapter5.md, §§1–4 (the "shorter route to the
index bound").

# Complex submanifolds: the index of `L_p` is at most the complex dimension

## Milnor's text, paraphrased

(pp. 40–41) For a complex manifold `M` bianalytically embedded in `ℂⁿ` and a critical point `q`
of `L_p = ‖· − p‖²`, the focal points of `(M, q)` along the normal line through `p` come in pairs
symmetric about `q` (Assertion 2), so at most `k = dim_ℂ M` of them lie between `q` and `p`, and by
Lemma 6.9 the index of `L_p` at `q` is `≤ k`.

## What is formalized

The ambient space is a real inner product space `V` with a **complex structure** `J`
(`Morse.IsOrthComplexStructure`: `J² = −1`, `J` orthogonal; for `V = ℂⁿ = ℝ²ⁿ`, multiplication by
`i`), and `N ⊆ V` a slice submanifold.

* `Morse.IsComplexSubmanifold hN J`: **every tangent space `T_xN` is `J`-invariant**.
* `Morse.Jc σ J u`, `Morse.fderiv_sliceParam_Jc`: `J` read in the coordinates `x = sliceParam σ`
  of a slice chart, `dx_u ∘ J'(u) = J ∘ dx_u`.
* `Morse.inner_fderiv_fderiv_sliceParam_Jc`: **the second fundamental form commutes with `J` up
  to sign**: for `ν` normal at `x(u)`, `⟪ν, d²x(η, J'ξ)⟫ = ⟪ν, J d²x(η, ξ)⟫` (differentiate
  `dx ∘ J' = J ∘ dx`; the derivative of `J'` contributes a tangent vector).
* `Morse.two_mul_indexM_normSq_sub_le`: **at every critical point of `L_p` on a complex
  submanifold, `2 · index ≤ dim_ℝ N`**, degenerate or not: with `ν = q − p`, the Hessian
  `H(ξ, ξ) = 2(‖dx ξ‖² + ⟪d²x(ξ, ξ), ν⟫)` satisfies `H(J'ξ, J'ξ) = 4‖dx ξ‖² − H(ξ, ξ)`, so a
  negative definite subspace `W` meets `J'W` in `0` (`Morse.two_mul_index_le_finrank`).

## Deviations from Milnor, and what he leaves implicit

* **No focal points.**  The bound is proved by the exposition's "shorter route" (the
  Andreotti–Frankel mechanism), without Lemma 6.3 or 6.9 and without non-degeneracy.
* **Complex submanifolds are defined by `J`-invariant tangent spaces** rather than by holomorphic
  charts.  A complex submanifold in Milnor's sense has this property (the tangent space is the
  image of a complex-linear map); the converse (a real submanifold of `ℂⁿ` with complex tangent
  spaces is complex) is classical and not needed.  The anti-symmetry of the second fundamental
  form, which Milnor reads off a Taylor expansion in holomorphic coordinates ("clearly"), is
  derived here from the `J`-invariance of all tangent spaces near `q`.
-/

open Set Filter Topology Function Module
open scoped ContDiff Manifold RealInnerProductSpace

noncomputable section

namespace Morse

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z]
  {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  {N : Set V}

/-- A **complex structure** on the Euclidean space `V` (`V = ℂᵐ` as `ℝ²ᵐ`, `J` multiplication by
`i`): an orthogonal map with `J² = −1`. -/
structure IsOrthComplexStructure (J : V →L[ℝ] V) : Prop where
  sq : ∀ v, J (J v) = -v
  inner : ∀ v w, ⟪J v, J w⟫ = ⟪v, w⟫

theorem IsOrthComplexStructure.inner_left {J : V →L[ℝ] V} (hJ : IsOrthComplexStructure J) (v w : V) :
    ⟪J v, w⟫ = -⟪v, J w⟫ := by
  have := hJ.inner v (J w)
  rw [hJ.sq, inner_neg_right] at this
  linarith

variable (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) Z W N)

/-- **`N` is a complex submanifold** for the complex structure `J`: every tangent space is a
complex subspace, `J(T_xN) ⊆ T_xN`. -/
def IsComplexSubmanifold (J : V →L[ℝ] V) : Prop :=
  ∀ x : N, ∀ v ∈ tangentSubspace hN x, J v ∈ tangentSubspace hN x

variable {hN} {J : V →L[ℝ] V}

/-- The normal space of a complex submanifold is complex. -/
theorem IsComplexSubmanifold.inner_J_eq_zero (hJ : IsOrthComplexStructure J)
    (hc : IsComplexSubmanifold hN J) {x : N} {ν : V}
    (hν : ∀ t ∈ tangentSubspace hN x, ⟪ν, t⟫ = 0) {t : V} (ht : t ∈ tangentSubspace hN x) :
    ⟪J ν, t⟫ = 0 := by
  rw [hJ.inner_left, hν _ (hc x t ht), neg_zero]

section Param

variable (σ : Milnor.SliceChart 𝓘(ℝ, V) Z W N)

/-- The complex structure read in the coordinates of the parametrization `x = sliceParam σ`:
`J'(u) = (dσ ∘ J ∘ dx_u)₁`, so that `dx_u ∘ J'(u) = J ∘ dx_u` (`Morse.fderiv_sliceParam_Jc`). -/
def Jc (J : V →L[ℝ] V) (u : Z) : Z →L[ℝ] Z :=
  (ContinuousLinearMap.fst ℝ Z W).comp
    ((fderiv ℝ σ.φ (sliceParam σ u)).comp (J.comp (fderiv ℝ (sliceParam σ) u)))

theorem fderiv_sliceParam_Jc (hc : IsComplexSubmanifold hN J) {u : Z}
    (hu : u ∈ σ.toChart.target) (ξ : Z) :
    fderiv ℝ (sliceParam σ) u (Jc σ J u ξ) = J (fderiv ℝ (sliceParam σ) u ξ) := by
  have hT := tangentSubspace_sliceParam hN σ hu
  have hmem : J (fderiv ℝ (sliceParam σ) u ξ) ∈
      LinearMap.range (fderiv ℝ (sliceParam σ) u : Z →ₗ[ℝ] V) := by
    rw [← hT]
    refine hc _ _ ?_
    rw [hT]
    exact ⟨ξ, rfl⟩
  obtain ⟨z, hz⟩ := hmem
  have h1 : Jc σ J u ξ = z := by
    change (fderiv ℝ σ.φ (sliceParam σ u) (J (fderiv ℝ (sliceParam σ) u ξ))).1 = z
    rw [← hz]
    exact fst_fderiv_sliceChart_fderiv_sliceParam σ hu z
  rw [h1]
  exact hz

omit [FiniteDimensional ℝ V] [FiniteDimensional ℝ Z] [FiniteDimensional ℝ W] in
theorem differentiableAt_Jc_apply {u : Z} (hu : u ∈ σ.toChart.target) (ξ : Z) :
    DifferentiableAt ℝ (fun u' => Jc σ J u' ξ) u := by
  have hx : ContDiffAt ℝ ∞ (sliceParam σ) u := contDiffAt_sliceParam σ hu
  have hφ : ContDiffAt ℝ ∞ σ.φ (sliceParam σ u) :=
    (Milnor.Problems.sliceChart_contDiffOn σ).contDiffAt
      (σ.φ.open_source.mem_nhds (sliceParam_mem_source σ hu))
  have h1 : DifferentiableAt ℝ (fun u' => fderiv ℝ σ.φ (sliceParam σ u')) u :=
    ((hφ.fderiv_right (m := 1) (by norm_cast)).differentiableAt (by simp)).comp u
      (hx.differentiableAt (by simp))
  have h2 : DifferentiableAt ℝ (fun u' => fderiv ℝ (sliceParam σ) u') u :=
    (hx.fderiv_right (m := 1) (by norm_cast)).differentiableAt (by simp)
  change DifferentiableAt ℝ (fun u' => ((fderiv ℝ σ.φ (sliceParam σ u'))
    (J (fderiv ℝ (sliceParam σ) u' ξ))).1) u
  exact (h1.clm_apply ((J.differentiableAt).comp u (h2.clm_apply (differentiableAt_const ξ)))).fst

/-- **The second fundamental form of a complex submanifold anticommutes with `J`** (Milnor
p. 40, "the quadratic terms `Q'` determine the second fundamental form", whose eigenvalues come in
pairs `±K`): for `ν` normal at `x(u)`,
`⟪ν, d²x(η, J'ξ)⟫ = ⟪ν, J d²x(η, ξ)⟫`. -/
theorem inner_fderiv_fderiv_sliceParam_Jc (hc : IsComplexSubmanifold hN J) {u : Z}
    (hu : u ∈ σ.toChart.target) {ν : V}
    (hν : ∀ t ∈ LinearMap.range (fderiv ℝ (sliceParam σ) u : Z →ₗ[ℝ] V), ⟪ν, t⟫ = 0)
    (η ξ : Z) :
    ⟪ν, fderiv ℝ (fderiv ℝ (sliceParam σ)) u η (Jc σ J u ξ)⟫ =
      ⟪ν, J (fderiv ℝ (fderiv ℝ (sliceParam σ)) u η ξ)⟫ := by
  have hx : ContDiffAt ℝ ∞ (sliceParam σ) u := contDiffAt_sliceParam σ hu
  have hD : HasFDerivAt (fderiv ℝ (sliceParam σ)) (fderiv ℝ (fderiv ℝ (sliceParam σ)) u) u :=
    ((hx.fderiv_right (m := 1) (by norm_cast)).differentiableAt (by simp)).hasFDerivAt
  have hb := (differentiableAt_Jc_apply (J := J) σ hu ξ).hasFDerivAt
  have hg := hD.clm_apply hb
  have hh : HasFDerivAt (fun u' => J (fderiv ℝ (sliceParam σ) u' ξ))
      (J.comp ((fderiv ℝ (fderiv ℝ (sliceParam σ)) u).flip ξ)) u := by
    have := J.hasFDerivAt.comp u (hD.clm_apply (hasFDerivAt_const ξ u))
    refine this.congr_fderiv ?_
    ext η
    simp
  have hev : (fun u' => fderiv ℝ (sliceParam σ) u' (Jc σ J u' ξ)) =ᶠ[𝓝 u]
      fun u' => J (fderiv ℝ (sliceParam σ) u' ξ) := by
    filter_upwards [(isOpen_toChart_target σ).mem_nhds hu] with u' hu'
    exact fderiv_sliceParam_Jc σ hc hu' ξ
  have heq := (hg.congr_of_eventuallyEq hev.symm).unique hh
  have h := congrArg (fun L : Z →L[ℝ] V => ⟪ν, L η⟫) heq
  simp only [add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply, inner_add_right] at h
  rw [hν (fderiv ℝ (sliceParam σ) u (fderiv ℝ (fun u' => Jc σ J u' ξ) u η)) ⟨_, rfl⟩,
    zero_add] at h
  exact h

end Param

/-- **Milnor's index bound** (pp. 40–41, in the form of the exposition's "shorter route"): at a
critical point `q` of `L_p = ‖· − p‖²` on a complex submanifold, `2 · index ≤ dim_ℝ N`.  In the
coordinates `x = sliceParam σ`, with `J'` the complex structure read in them and `ν = q − p`, the
Hessian `H(ξ, ξ) = 2(‖dx ξ‖² + ⟪d²x(ξ, ξ), ν⟫)` satisfies `H(J'ξ, J'ξ) = 4‖dx ξ‖² − H(ξ, ξ)`. -/
theorem two_mul_indexM_normSq_sub_le (hJ : IsOrthComplexStructure J) (hc : IsComplexSubmanifold hN J)
    (p : V) (q : N)
    (hcrit : letI := hN.chartedSpace; IsCriticalPointM Z (fun x : N => ‖(x : V) - p‖ ^ 2) q) :
    letI := hN.chartedSpace
    2 * indexM Z (fun x : N => ‖(x : V) - p‖ ^ 2) q ≤ finrank ℝ Z := by
  let _ := hN.chartedSpace
  obtain ⟨σ, hqσ⟩ := hN q q.2
  rw [indexM_normSq_sub_eq hN σ p hqσ hcrit]
  have hu : (σ.φ q).1 ∈ σ.toChart.target := toChart_apply_mem_target σ hqσ
  set u := (σ.φ q).1 with hu_def
  have hx : ContDiffAt ℝ ∞ (sliceParam σ) u := contDiffAt_sliceParam σ hu
  set D := fderiv ℝ (sliceParam σ) u with hD_def
  set D2 := fderiv ℝ (fderiv ℝ (sliceParam σ)) u with hD2_def
  set ν := sliceParam σ u - p with hν_def
  -- `ν = q − p` is normal: `q` is a critical point
  have hcp : IsCriticalPoint ((fun y : V => ‖y - p‖ ^ 2) ∘ sliceParam σ) u :=
    (isCriticalPointM_comp_val_iff_sliceParam hN σ hqσ
      ((contDiff_normSq_sub p).differentiable (by simp) _)).1 hcrit
  have hν : ∀ t ∈ LinearMap.range (D : Z →ₗ[ℝ] V), ⟪ν, t⟫ = 0 := by
    rintro _ ⟨ξ, rfl⟩
    have h1 := hcp.fderiv
    have h2 : fderiv ℝ ((fun y : V => ‖y - p‖ ^ 2) ∘ sliceParam σ) u ξ = 2 * ⟪ν, D ξ⟫ := by
      rw [fderiv_comp u ((contDiff_normSq_sub p).differentiable (by simp) _)
        (hx.differentiableAt (by simp)), ContinuousLinearMap.comp_apply,
        fderiv_normSq_sub_apply]
    rw [h1] at h2
    simp only [ContinuousLinearMap.zero_apply] at h2
    change ⟪ν, D ξ⟫ = 0
    linarith
  have hJD : ∀ ξ, J (D ξ) = D (Jc σ J u ξ) := fun ξ => (fderiv_sliceParam_Jc σ hc hu ξ).symm
  have hJν : ∀ t ∈ LinearMap.range (D : Z →ₗ[ℝ] V), ⟪J ν, t⟫ = 0 := by
    rintro _ ⟨ξ, rfl⟩
    change ⟪J ν, D ξ⟫ = 0
    rw [hJ.inner_left, hJD, hν (D (Jc σ J u ξ)) ⟨_, rfl⟩, neg_zero]
  have hx2 : ContDiffAt ℝ 2 (sliceParam σ) u := hx.of_le (WithTop.coe_le_coe.2 le_top)
  have hsymm : ∀ v w, D2 v w = D2 w v := fun v w => (hx2.isSymmSndFDerivAt (by simp)) v w
  have hF2 : ∀ η ξ, ⟪ν, D2 η (Jc σ J u ξ)⟫ = ⟪ν, J (D2 η ξ)⟫ :=
    inner_fderiv_fderiv_sliceParam_Jc σ hc hu hν
  have hF2' : ∀ η ξ, ⟪J ν, D2 η (Jc σ J u ξ)⟫ = ⟪J ν, J (D2 η ξ)⟫ :=
    inner_fderiv_fderiv_sliceParam_Jc σ hc hu hJν
  have hHess : ∀ v w, hessian (fun z => ‖sliceParam σ z - p‖ ^ 2) u v w =
      2 * (⟪D v, D w⟫ + ⟪ν, D2 v w⟫) := fun v w => by
    rw [hessian_normSq_sub_comp hx2 p v w, real_inner_comm ν]
  refine two_mul_index_le_finrank _ (Jc σ J u : Z →ₗ[ℝ] Z) ?_ fun ξ => ?_
  · intro ξ ξ' h
    have h1 : D (Jc σ J u ξ) = D (Jc σ J u ξ') := congrArg D h
    rw [← hJD, ← hJD] at h1
    have h2 : D ξ = D ξ' := by
      have := congrArg J h1
      rwa [hJ.sq, hJ.sq, neg_inj] at this
    have h3 := congrArg (fun v => (fderiv ℝ σ.φ (sliceParam σ u) v).1) h2
    rwa [fst_fderiv_sliceChart_fderiv_sliceParam σ hu,
      fst_fderiv_sliceChart_fderiv_sliceParam σ hu] at h3
  · change 0 ≤ hessian _ u ξ ξ + hessian _ u (Jc σ J u ξ) (Jc σ J u ξ)
    rw [hHess, hHess, ← hJD, hJ.inner]
    have key : ⟪ν, D2 (Jc σ J u ξ) (Jc σ J u ξ)⟫ = -⟪ν, D2 ξ ξ⟫ := by
      rw [hF2, show ⟪ν, J (D2 (Jc σ J u ξ) ξ)⟫ = -⟪J ν, D2 (Jc σ J u ξ) ξ⟫ by
        rw [hJ.inner_left, neg_neg], hsymm, hF2', hJ.inner]
    rw [key]
    nlinarith [real_inner_self_nonneg (x := D ξ)]

end Morse
