import Morse.Chapter1.ManifoldSubmanifold
import Milnor.Chapter8.TangentBundle

/-!
Milnor, *Morse Theory*, Part II (§8, pp. 43–49), in the setting of submanifolds `N ⊆ ℝᴷ` with the
metric induced from `ℝᴷ`: the tangent projection and differentiation along `N`.

# The tangent projection `P_q` and derivatives along a submanifold

## Setting

Part II of Milnor is about an abstract Riemannian manifold.  Here, as in Part I of this project,
`N` is a submanifold of a finite-dimensional real inner product space `V` (Milnor's `ℝᴷ`) in the
sense of the companion project, `Milnor.IsSliceSubmanifold 𝓘(ℝ, V) Z W N`, with the Riemannian
metric induced from `V`: the inner product of two tangent vectors at `q` is their inner product in
`V`.  Every Riemannian manifold arises in this way, by Nash's embedding theorem (J. Nash, *The
imbedding problem for Riemannian manifolds*, Ann. of Math. 63 (1956)); that theorem is quoted, not
proved, and is not used in any proof.  In this setting the objects of §8 have explicit formulas,
and the notions that Milnor defines in coordinates become global:

* the tangent space `T_qN ⊆ V` is `Morse.tangentSubspace hN q`, the range of the derivative of the
  inclusion (`Morse/Chapter1/ManifoldSubmanifold.lean`);
* `Morse.tanProj hN q = P_q : V →L V` is the orthogonal projection onto `T_qN`;
* `Morse.dN hN F q : V →L E` is the derivative of a map `F : N → E` (`E` a normed space) at `q`,
  read on ambient tangent vectors: for `v ∈ T_qN` it is `dF_q(v)` (Mathlib's `mfderiv`, composed
  with the chart coordinates `Morse.tanCoord hN q` of `v`).  Its values on vectors not tangent
  to `N` are meaningless (they depend on the chart) and are never used.

## Main results

* `Morse.gramProj`, `Morse.gramProj_eq_starProjection`, `Morse.contDiffAt_gramProj`: for an
  injective operator `A : Y → V` (`Y` any finite-dimensional normed space), the projection onto
  `range A` is `A (AᵀA)⁻¹ Aᵀ`, where `Aᵀv = ⟪v, A ·⟫` and `AᵀA : Y → Y*` is the Gram operator;
  it depends smoothly on `A`.
* `Morse.tanProj_eq_gramProj`, `Morse.contMDiff_tanProj`: in a slice chart with parametrization
  `x(u)`, `P_{x(u)} = gramProj (dx_u)`; hence **`q ↦ P_q` is a smooth map `N → (V →L V)`**.  The
  ambient map `Morse.projRep σ : V → (V →L V)`, `y ↦ gramProj (dx_{(σ y)₁})`, is a smooth local
  extension of `P` (`Morse.contDiffAt_projRep`, `Morse.projRep_eq`).
* `Morse.dN_comp_val`, `Morse.dN_eq_fderiv`: for `F = G|N` near `q` with `G : V → E`
  differentiable at `q`, `dN F q v = dG_q(v)` for `v ∈ T_qN`.  Every `F` differentiable at `q` has
  such a local ambient representative (`Morse.exists_differentiableAt_rep`), and every smooth `F`
  a smooth one on an open set (`Morse.exists_contDiffOn_rep`).  All the calculus of `dN` (sums,
  Leibniz rules for scalars, operators and inner products: `Morse.dN_add`, `Morse.dN_smul`,
  `Morse.dN_clm_apply`, `Morse.dN_inner`) is reduced to ambient calculus in this way.
* The derivative `D_v = dN P q v` of the projection (`v ∈ T_qN`) is self-adjoint
  (`Morse.inner_dN_tanProj_comm`) and satisfies `D_v P + P D_v = D_v`
  (`Morse.dN_tanProj_comp_add`), hence `P D_v P = 0` and `(1 − P) D_v (1 − P) = 0`: `D_v` maps
  `T_qN` into the normal space and the normal space into `T_qN`
  (`Morse.tanProj_dN_tanProj_of_mem`, `Morse.dN_tanProj_mem_of_mem_orthogonal`).
* Curves: for a smooth curve `c` in `N`, the velocity `c'(t)` is tangent
  (`Morse.deriv_mem_tangentSubspace`), the chain rule `(F ∘ c)' = dN F (c t) (c' t)` holds
  (`Morse.hasDerivAt_comp_curve`), and `t ↦ P_{c(t)}` is smooth (`Morse.contDiff_tanProj_comp`).

## Relation to the companion project

For *compact* `N` the companion project's tubular neighbourhood theorem gives the nearest-point
retraction `r` (`Milnor.Tub.tubr`), and `dr_q = P_q` (`Morse.dret_eq_starProjection` in
`Morse/Chapter3/EulerCharGradient.lean`), from which the smoothness of the tangential gradient
`P_q ∇F(q)` is deduced there.  The local construction here needs no compactness and applies to
every slice submanifold; `P_q` is `(tangentSubspace hN q).starProjection` in both places.

## What Milnor leaves implicit

Milnor's §8 works in local coordinates throughout, and the smoothness of the objects he constructs
(the field `X ⊢ Y`, condition (1) on p. 44; vector fields along curves, p. 45) is checked chart by
chart.  In the embedded setting all of this is reduced to one fact, the smoothness of `q ↦ P_q`,
which Milnor never needs to state.  It is not automatic: the projection onto `range A` is a smooth
function of `A` only on the injective operators (the rank must not drop), which is why the Gram
operator must be shown to be invertible (`Morse.gramL_bijective`).
-/

open Set Filter Topology Function Module
open scoped ContDiff Manifold RealInnerProductSpace

noncomputable section

namespace Morse

/-! ### The projection onto the range of an injective operator -/

section Gram

variable {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
  {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- The transpose `Aᵀ : V → Y*`, `v ↦ ⟪v, A ·⟫`. -/
def transposeL (A : Y →L[ℝ] V) : V →L[ℝ] Y →L[ℝ] ℝ :=
  ((ContinuousLinearMap.compL ℝ Y V ℝ).flip A).comp (innerSL ℝ)

@[simp] theorem transposeL_apply (A : Y →L[ℝ] V) (v : V) (y : Y) :
    transposeL A v y = ⟪v, A y⟫ := rfl

/-- The Gram operator `AᵀA : Y → Y*`, `y ↦ ⟪A y, A ·⟫`. -/
def gramL (A : Y →L[ℝ] V) : Y →L[ℝ] Y →L[ℝ] ℝ := (transposeL A).comp A

@[simp] theorem gramL_apply (A : Y →L[ℝ] V) (y y' : Y) : gramL A y y' = ⟪A y, A y'⟫ := rfl

theorem gramL_injective {A : Y →L[ℝ] V} (hA : Injective A) : Injective (gramL A) := by
  intro y y' h
  have h1 : gramL A (y - y') (y - y') = 0 := by
    rw [show gramL A (y - y') = gramL A y - gramL A y' from map_sub _ _ _, h, sub_self,
      zero_apply]
  rw [gramL_apply, inner_self_eq_zero, map_sub, sub_eq_zero] at h1
  exact hA h1

variable [FiniteDimensional ℝ Y]

theorem finrank_clmDual_eq : finrank ℝ (Y →L[ℝ] ℝ) = finrank ℝ Y := by
  rw [← (LinearMap.toContinuousLinearMap : (Y →ₗ[ℝ] ℝ) ≃ₗ[ℝ] (Y →L[ℝ] ℝ)).finrank_eq]
  exact Subspace.dual_finrank_eq

theorem gramL_bijective {A : Y →L[ℝ] V} (hA : Injective A) : Bijective (gramL A) := by
  refine ⟨gramL_injective hA, ?_⟩
  have h := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank finrank_clmDual_eq.symm
    (f := ((gramL A : Y →L[ℝ] Y →L[ℝ] ℝ) : Y →ₗ[ℝ] Y →L[ℝ] ℝ))).1 (gramL_injective hA)
  exact h

/-- The Gram operator of an injective operator, as an isomorphism `Y ≃ Y*`. -/
def gramEquiv {A : Y →L[ℝ] V} (hA : Injective A) : Y ≃L[ℝ] (Y →L[ℝ] ℝ) :=
  ContinuousLinearEquiv.ofBijective (gramL A) (LinearMap.ker_eq_bot.2 (gramL_bijective hA).1)
    (LinearMap.range_eq_top.2 (gramL_bijective hA).2)

theorem coe_gramEquiv {A : Y →L[ℝ] V} (hA : Injective A) :
    (gramEquiv hA : Y →L[ℝ] Y →L[ℝ] ℝ) = gramL A :=
  ContinuousLinearEquiv.coe_ofBijective _ _ _

theorem gramL_inverse_apply {A : Y →L[ℝ] V} (hA : Injective A) (ℓ : Y →L[ℝ] ℝ) :
    gramL A ((gramL A).inverse ℓ) = ℓ := by
  rw [← coe_gramEquiv hA, ContinuousLinearMap.inverse_equiv]
  exact (gramEquiv hA).apply_symm_apply ℓ

/-- `A (AᵀA)⁻¹ Aᵀ`: for injective `A`, the orthogonal projection onto `range A`
(`Morse.gramProj_eq_starProjection`). -/
def gramProj (A : Y →L[ℝ] V) : V →L[ℝ] V := A.comp ((gramL A).inverse.comp (transposeL A))

/-- **The projection onto the range of an injective operator** is `A (AᵀA)⁻¹ Aᵀ`. -/
theorem gramProj_eq_starProjection {A : Y →L[ℝ] V} (hA : Injective A) :
    gramProj A = (LinearMap.range (A : Y →ₗ[ℝ] V)).starProjection := by
  ext v
  set y := (gramL A).inverse (transposeL A v) with hy
  have hgy : gramL A y = transposeL A v := gramL_inverse_apply hA _
  symm
  refine Submodule.eq_starProjection_of_mem_of_inner_eq_zero ⟨y, rfl⟩ ?_
  rintro w ⟨y', rfl⟩
  have h := congrArg (fun ℓ : Y →L[ℝ] ℝ => ℓ y') hgy
  simp only [gramL_apply, transposeL_apply] at h
  change ⟪v - A y, A y'⟫ = 0
  rw [inner_sub_left, ← h, sub_self]

/-- **The projection onto `range A` depends smoothly on `A`** near an injective operator. -/
theorem contDiffAt_gramProj {A : Y →L[ℝ] V} (hA : Injective A) {n : WithTop ℕ∞} :
    ContDiffAt ℝ n (gramProj : (Y →L[ℝ] V) → V →L[ℝ] V) A := by
  have h1 : ContDiff ℝ n (transposeL : (Y →L[ℝ] V) → V →L[ℝ] Y →L[ℝ] ℝ) :=
    ((ContinuousLinearMap.compL ℝ Y V ℝ).flip.contDiff).clm_comp contDiff_const
  have h2 : ContDiff ℝ n (gramL : (Y →L[ℝ] V) → Y →L[ℝ] Y →L[ℝ] ℝ) := h1.clm_comp contDiff_id
  have h3 : ContDiffAt ℝ n (fun B : Y →L[ℝ] V => (gramL B).inverse) A := by
    have h := contDiffAt_map_inverse (𝕜 := ℝ) (n := n) (gramEquiv hA)
    rw [coe_gramEquiv] at h
    exact h.comp A h2.contDiffAt
  exact contDiffAt_id.clm_comp (h3.clm_comp h1.contDiffAt)

/-- `gramProj_eq_starProjection`, for any submodule equal to `range A`. -/
theorem gramProj_eq_starProjection' {A : Y →L[ℝ] V} (hA : Injective A) (K : Submodule ℝ V)
    [K.HasOrthogonalProjection] (hK : K = LinearMap.range (A : Y →ₗ[ℝ] V)) :
    gramProj A = K.starProjection := by
  subst hK
  exact gramProj_eq_starProjection hA

end Gram

/-! ### Chart coordinates of tangent vectors, and derivatives along `N` -/

section Sub

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
  {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  {N : Set V} (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) Z W N)
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']

/-- The slice chart of `N` chosen at `q`; its induced chart is the chart `chartAt Z q` of the
manifold structure of `N`. -/
def sliceAt (q : N) : Milnor.SliceChart 𝓘(ℝ, V) Z W N := (hN q.1 q.2).choose

theorem mem_sliceAt_source (q : N) : q.1 ∈ (sliceAt hN q).φ.source := (hN q.1 q.2).choose_spec

theorem chartAt_eq_sliceAt (q : N) :
    @chartAt Z _ N _ hN.chartedSpace q = (sliceAt hN q).toChart := rfl

/-- **The chart coordinates of an ambient vector** at `q`: `v ↦ (dσ_q v)₁`, `σ` the slice chart
chosen at `q`.  On `T_qN` it inverts the derivative of the inclusion
(`Morse.tanCoord_mfderiv_val`, `Morse.mfderiv_val_tanCoord`). -/
def tanCoord (q : N) : V →L[ℝ] Z :=
  (ContinuousLinearMap.fst ℝ Z W).comp (fderiv ℝ (sliceAt hN q).φ q.1)

theorem tanCoord_mfderiv_val (q : N) (z : Z) :
    letI := hN.chartedSpace
    tanCoord hN q (mfderiv 𝓘(ℝ, Z) 𝓘(ℝ, V) (Subtype.val : N → V) q z) = z := by
  let _ := hN.chartedSpace
  have := hN.isManifold
  have hq := mem_sliceAt_source hN q
  have hφ : HasFDerivAt (sliceAt hN q).φ (fderiv ℝ (sliceAt hN q).φ q.1) q.1 :=
    (Milnor.Problems.sliceChart_differentiableAt (sliceAt hN q) hq).hasFDerivAt
  have hg : HasFDerivAt (fun y => ((sliceAt hN q).φ y).1) (tanCoord hN q) q.1 := hφ.fst
  have hval : MDifferentiableAt 𝓘(ℝ, Z) 𝓘(ℝ, V) (Subtype.val : N → V) q :=
    hN.contMDiff_val.mdifferentiableAt (by simp)
  have hcomp : mfderiv 𝓘(ℝ, Z) 𝓘(ℝ, Z) ((fun y => ((sliceAt hN q).φ y).1) ∘ Subtype.val) q =
      (tanCoord hN q).comp (mfderiv 𝓘(ℝ, Z) 𝓘(ℝ, V) (Subtype.val : N → V) q) := by
    rw [mfderiv_comp q hg.differentiableAt.mdifferentiableAt hval, mfderiv_eq_fderiv, hg.fderiv]
    rfl
  have hchart : mfderiv 𝓘(ℝ, Z) 𝓘(ℝ, Z) ((fun y => ((sliceAt hN q).φ y).1) ∘ Subtype.val) q =
      mfderiv 𝓘(ℝ, Z) 𝓘(ℝ, Z) (chartAt Z q) q := rfl
  rw [mfderiv_chartAt_eq_tangentCoordChange (mem_chart_source Z q), hcomp] at hchart
  have h2 := DFunLike.congr_fun hchart z
  have h3 := tangentCoordChange_self (I := 𝓘(ℝ, Z)) (x := q) (z := q) (v := z)
    (mem_extChartAt_source q)
  exact h2.trans h3

theorem mfderiv_val_tanCoord {q : N} {v : V} (hv : v ∈ tangentSubspace hN q) :
    letI := hN.chartedSpace
    mfderiv 𝓘(ℝ, Z) 𝓘(ℝ, V) (Subtype.val : N → V) q (tanCoord hN q v) = v := by
  let _ := hN.chartedSpace
  obtain ⟨z, rfl⟩ := (mem_tangentSubspace_iff hN).1 hv
  rw [tanCoord_mfderiv_val]

/-- **The derivative of `F : N → E` at `q` on ambient tangent vectors**: for `v ∈ T_qN`,
`dN F q v = dF_q(v)` (Mathlib's `mfderiv` at `q`, applied to the chart coordinates of `v`).  On
vectors not tangent to `N` its value depends on the chart and has no meaning. -/
def dN (F : N → E) (q : N) : V →L[ℝ] E :=
  letI := hN.chartedSpace
  (Milnor.mfd 𝓘(ℝ, Z) 𝓘(ℝ, E) F q).comp (tanCoord hN q)

theorem dN_apply (F : N → E) (q : N) (v : V) :
    letI := hN.chartedSpace
    dN hN F q v = mfderiv 𝓘(ℝ, Z) 𝓘(ℝ, E) F q (tanCoord hN q v) := rfl

theorem dN_congr {F F' : N → E} {q : N} (h : F =ᶠ[𝓝 q] F') : dN hN F q = dN hN F' q := by
  let _ := hN.chartedSpace
  unfold dN Milnor.mfd
  rw [h.mfderiv_eq]

theorem dN_const (c : E) (q : N) : dN hN (fun _ : N => c) q = 0 := by
  let _ := hN.chartedSpace
  ext v
  rw [dN_apply, mfderiv_const]
  rfl

/-- **The chain rule for `dN` and ambient maps**: `d(G|N)_q(v) = dG_q(v)` for `v ∈ T_qN`. -/
theorem dN_comp_val {G : V → E} {q : N} (hG : DifferentiableAt ℝ G q) {v : V}
    (hv : v ∈ tangentSubspace hN q) : dN hN (fun x : N => G x) q v = fderiv ℝ G q v := by
  let _ := hN.chartedSpace
  have := hN.isManifold
  have hval : MDifferentiableAt 𝓘(ℝ, Z) 𝓘(ℝ, V) (Subtype.val : N → V) q :=
    hN.contMDiff_val.mdifferentiableAt (by simp)
  have h := mfderiv_comp q hG.mdifferentiableAt hval
  rw [mfderiv_eq_fderiv] at h
  rw [dN_apply]
  change mfderiv 𝓘(ℝ, Z) 𝓘(ℝ, E) (G ∘ Subtype.val) q (tanCoord hN q v) = _
  rw [h]
  exact congrArg (fderiv ℝ G q) (mfderiv_val_tanCoord hN hv)

/-- If `F = G` on `N` near `q`, with `G : V → E` differentiable at `q`, then `dN F q v = dG_q(v)`
for `v ∈ T_qN`. -/
theorem dN_eq_fderiv {F : N → E} {G : V → E} {q : N} (hG : DifferentiableAt ℝ G q)
    (hFG : ∀ᶠ x in 𝓝 q, F x = G x) {v : V} (hv : v ∈ tangentSubspace hN q) :
    dN hN F q v = fderiv ℝ G q v := by
  rw [dN_congr hN (F' := fun x : N => G x) hFG, dN_comp_val hN hG hv]

/-- The derivative, in a tangent direction, of an ambient map vanishing on `N` near `q` is zero. -/
theorem fderiv_eq_zero_of_eventually {G : V → E} {q : N} (hG : DifferentiableAt ℝ G q)
    (h0 : ∀ᶠ x : N in 𝓝 q, G x = 0) {v : V} (hv : v ∈ tangentSubspace hN q) :
    fderiv ℝ G q v = 0 := by
  have h1 : ∀ᶠ x in 𝓝 q, (fun _ : N => (0 : E)) x = G x := h0.mono fun x hx => hx.symm
  rw [← dN_eq_fderiv hN hG h1 hv, dN_const]
  rfl

/-- **Every map differentiable at `q` has an ambient representative near `q`**:
`y ↦ F(σ⁻¹((σ y)₁, 0))`, `σ` the slice chart chosen at `q`. -/
theorem exists_differentiableAt_rep {F : N → E} {q : N}
    (hF : letI := hN.chartedSpace; MDifferentiableAt 𝓘(ℝ, Z) 𝓘(ℝ, E) F q) :
    ∃ G : V → E, DifferentiableAt ℝ G q ∧ ∀ᶠ x in 𝓝 q, F x = G x := by
  let _ := hN.chartedSpace
  set σ := sliceAt hN q with hσ
  have hq := mem_sliceAt_source hN q
  refine ⟨fun y => F (σ.toChart.symm (σ.φ y).1), ?_, ?_⟩
  · have h1 := (hF.mdifferentiableWithinAt (s := univ)).differentiableWithinAt_comp_extChartAt_symm
    rw [hN.extChartAt_eq q] at h1
    simp only [preimage_univ, modelWithCornersSelf_coe, range_id, inter_univ,
      differentiableWithinAt_univ] at h1
    have h2 : DifferentiableAt ℝ (fun y => (σ.φ y).1) q.1 :=
      (Milnor.Problems.sliceChart_differentiableAt σ hq).fst
    exact h1.comp (f := fun y => (σ.φ y).1) q.1 h2
  · filter_upwards [σ.toChart.open_source.mem_nhds hq] with x hx
    rw [show (σ.φ x.1).1 = σ.toChart x from rfl, σ.toChart.left_inv hx]

/-- **Every smooth map has a smooth ambient representative near each point**, on an open set
`U ∋ q` of `V`. -/
theorem exists_contDiffOn_rep {F : N → E}
    (hF : letI := hN.chartedSpace; ContMDiff 𝓘(ℝ, Z) 𝓘(ℝ, E) ∞ F) (q : N) :
    ∃ G : V → E, ∃ U : Set V, IsOpen U ∧ q.1 ∈ U ∧ ContDiffOn ℝ ∞ G U ∧
      ∀ x : N, x.1 ∈ U → F x = G x := by
  let _ := hN.chartedSpace
  have := hN.isManifold
  set σ := sliceAt hN q with hσ
  have hq := mem_sliceAt_source hN q
  refine ⟨fun y => F (σ.toChart.symm (σ.φ y).1),
    σ.φ.source ∩ (fun y => (σ.φ y).1) ⁻¹' σ.toChart.target, ?_, ⟨hq, σ.toChart.map_source hq⟩, ?_,
    ?_⟩
  · exact (continuous_fst.comp_continuousOn σ.φ.contMDiffOn.continuousOn).isOpen_inter_preimage
      σ.φ.open_source σ.toChart.open_target
  · have h1 : ContMDiffOn 𝓘(ℝ, Z) 𝓘(ℝ, Z) ∞ (chartAt Z q).symm (chartAt Z q).target :=
      contMDiffOn_chart_symm
    have h2 : ContMDiffOn 𝓘(ℝ, Z) 𝓘(ℝ, E) ∞ (fun z => F ((chartAt Z q).symm z))
        (chartAt Z q).target := hF.comp_contMDiffOn h1
    have h3 : ContMDiffOn 𝓘(ℝ, V) 𝓘(ℝ, Z) ∞ (fun a => (σ.φ a).1) σ.φ.source :=
      (contDiff_fst.contMDiff).comp_contMDiffOn σ.φ.contMDiffOn
    rw [← contMDiffOn_iff_contDiffOn]
    exact h2.comp (h3.mono inter_subset_left) fun a ha => ha.2
  · intro x hx
    change F x = F (σ.toChart.symm (σ.φ x.1).1)
    rw [show (σ.φ x.1).1 = σ.toChart x from rfl, σ.toChart.left_inv hx.1]

/-! ### The calculus of `dN` -/

theorem dN_add {F₁ F₂ : N → E} {q : N}
    (h₁ : letI := hN.chartedSpace; MDifferentiableAt 𝓘(ℝ, Z) 𝓘(ℝ, E) F₁ q)
    (h₂ : letI := hN.chartedSpace; MDifferentiableAt 𝓘(ℝ, Z) 𝓘(ℝ, E) F₂ q) :
    dN hN (fun x => F₁ x + F₂ x) q = dN hN F₁ q + dN hN F₂ q := by
  let _ := hN.chartedSpace
  ext v
  simp only [dN_apply, add_apply]
  rw [show (fun x => F₁ x + F₂ x) = F₁ + F₂ from rfl, mfderiv_add h₁ h₂]
  rfl

theorem dN_neg {F : N → E} {q : N} : dN hN (fun x => -F x) q = -dN hN F q := by
  let _ := hN.chartedSpace
  ext v
  simp only [dN_apply, neg_apply]
  rw [show (fun x => -F x) = -F from rfl, mfderiv_neg]
  rfl

theorem dN_sub {F₁ F₂ : N → E} {q : N}
    (h₁ : letI := hN.chartedSpace; MDifferentiableAt 𝓘(ℝ, Z) 𝓘(ℝ, E) F₁ q)
    (h₂ : letI := hN.chartedSpace; MDifferentiableAt 𝓘(ℝ, Z) 𝓘(ℝ, E) F₂ q) :
    dN hN (fun x => F₁ x - F₂ x) q = dN hN F₁ q - dN hN F₂ q := by
  let _ := hN.chartedSpace
  have h₂' : MDifferentiableAt 𝓘(ℝ, Z) 𝓘(ℝ, E) (fun x => -F₂ x) q := h₂.neg
  simp only [sub_eq_add_neg]
  rw [dN_add hN h₁ h₂', dN_neg]

/-- **`dN` commutes with continuous linear maps**: `d(L ∘ F) = L ∘ dF`. -/
theorem dN_clm_comp (L : E →L[ℝ] E') {F : N → E} {q : N}
    (hF : letI := hN.chartedSpace; MDifferentiableAt 𝓘(ℝ, Z) 𝓘(ℝ, E) F q) :
    dN hN (fun x => L (F x)) q = L.comp (dN hN F q) := by
  let _ := hN.chartedSpace
  ext v
  have h := (L.hasFDerivAt (x := F q)).hasMFDerivAt.comp q hF.hasMFDerivAt
  simp only [dN_apply, ContinuousLinearMap.comp_apply]
  rw [show (fun x => L (F x)) = L ∘ F from rfl, h.mfderiv]
  rfl

/-- **The Leibniz rule for a continuous bilinear map** `B`:
`d(B(F₁, F₂))_q(v) = B(dF₁(v), F₂(q)) + B(F₁(q), dF₂(v))` for `v ∈ T_qN`.  It specializes to the
rules for scalar multiples, inner products, evaluation and composition of operators. -/
theorem dN_bilinear {E₁ E₂ : Type*} [NormedAddCommGroup E₁] [NormedSpace ℝ E₁]
    [NormedAddCommGroup E₂] [NormedSpace ℝ E₂] (B : E₁ →L[ℝ] E₂ →L[ℝ] E) {F₁ : N → E₁}
    {F₂ : N → E₂} {q : N}
    (h₁ : letI := hN.chartedSpace; MDifferentiableAt 𝓘(ℝ, Z) 𝓘(ℝ, E₁) F₁ q)
    (h₂ : letI := hN.chartedSpace; MDifferentiableAt 𝓘(ℝ, Z) 𝓘(ℝ, E₂) F₂ q) {v : V}
    (hv : v ∈ tangentSubspace hN q) :
    dN hN (fun x => B (F₁ x) (F₂ x)) q v = B (dN hN F₁ q v) (F₂ q) + B (F₁ q) (dN hN F₂ q v) := by
  obtain ⟨G₁, hG₁, hFG₁⟩ := exists_differentiableAt_rep hN h₁
  obtain ⟨G₂, hG₂, hFG₂⟩ := exists_differentiableAt_rep hN h₂
  have hB : HasFDerivAt (fun y => B (G₁ y) (G₂ y))
      ((B (G₁ q)).comp (fderiv ℝ G₂ q) + (B.comp (fderiv ℝ G₁ q)).flip (G₂ q)) q :=
    (B.hasFDerivAt.comp (q : V) hG₁.hasFDerivAt).clm_apply hG₂.hasFDerivAt
  have hev : ∀ᶠ x in 𝓝 q, B (F₁ x) (F₂ x) = B (G₁ x) (G₂ x) := by
    filter_upwards [hFG₁, hFG₂] with x h1 h2
    rw [h1, h2]
  rw [dN_eq_fderiv hN hB.differentiableAt hev hv, hB.fderiv, dN_eq_fderiv hN hG₁ hFG₁ hv,
    dN_eq_fderiv hN hG₂ hFG₂ hv, hFG₁.self_of_nhds, hFG₂.self_of_nhds]
  simp only [add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply]
  abel

/-- The Leibniz rule for a function times a vector field, Milnor's rule (4) on p. 44 before
projection. -/
theorem dN_smul {f : N → ℝ} {F : N → E} {q : N}
    (hf : letI := hN.chartedSpace; MDifferentiableAt 𝓘(ℝ, Z) 𝓘(ℝ, ℝ) f q)
    (hF : letI := hN.chartedSpace; MDifferentiableAt 𝓘(ℝ, Z) 𝓘(ℝ, E) F q) {v : V}
    (hv : v ∈ tangentSubspace hN q) :
    dN hN (fun x => f x • F x) q v = dN hN f q v • F q + f q • dN hN F q v :=
  dN_bilinear hN (ContinuousLinearMap.lsmul ℝ ℝ) hf hF hv

/-- The Leibniz rule for inner products. -/
theorem dN_inner {F₁ F₂ : N → V} {q : N}
    (h₁ : letI := hN.chartedSpace; MDifferentiableAt 𝓘(ℝ, Z) 𝓘(ℝ, V) F₁ q)
    (h₂ : letI := hN.chartedSpace; MDifferentiableAt 𝓘(ℝ, Z) 𝓘(ℝ, V) F₂ q) {v : V}
    (hv : v ∈ tangentSubspace hN q) :
    dN hN (fun x => ⟪F₁ x, F₂ x⟫) q v = ⟪dN hN F₁ q v, F₂ q⟫ + ⟪F₁ q, dN hN F₂ q v⟫ :=
  dN_bilinear hN (innerSL ℝ) h₁ h₂ hv

/-- The Leibniz rule for an operator-valued map applied to a vector-valued one. -/
theorem dN_clm_apply {A : N → E →L[ℝ] E'} {F : N → E} {q : N}
    (hA : letI := hN.chartedSpace; MDifferentiableAt 𝓘(ℝ, Z) 𝓘(ℝ, E →L[ℝ] E') A q)
    (hF : letI := hN.chartedSpace; MDifferentiableAt 𝓘(ℝ, Z) 𝓘(ℝ, E) F q) {v : V}
    (hv : v ∈ tangentSubspace hN q) :
    dN hN (fun x => A x (F x)) q v = dN hN A q v (F q) + A q (dN hN F q v) :=
  dN_bilinear hN (ContinuousLinearMap.id ℝ (E →L[ℝ] E')) hA hF hv

/-- The Leibniz rule for a composition of operator-valued maps. -/
theorem dN_clm_comp' {E₁ : Type*} [NormedAddCommGroup E₁] [NormedSpace ℝ E₁]
    {A : N → E →L[ℝ] E'} {B : N → E₁ →L[ℝ] E} {q : N}
    (hA : letI := hN.chartedSpace; MDifferentiableAt 𝓘(ℝ, Z) 𝓘(ℝ, E →L[ℝ] E') A q)
    (hB : letI := hN.chartedSpace; MDifferentiableAt 𝓘(ℝ, Z) 𝓘(ℝ, E₁ →L[ℝ] E) B q) {v : V}
    (hv : v ∈ tangentSubspace hN q) :
    dN hN (fun x => (A x).comp (B x)) q v = (dN hN A q v).comp (B q) + (A q).comp (dN hN B q v) :=
  dN_bilinear hN (ContinuousLinearMap.compL ℝ E₁ E E') hA hB hv

/-- The derivative of the inclusion is the identity on `T_qN`. -/
theorem dN_val {q : N} {v : V} (hv : v ∈ tangentSubspace hN q) :
    dN hN (fun x : N => (x : V)) q v = v := by
  have h := dN_comp_val hN (G := id) differentiableAt_id hv
  rw [fderiv_id] at h
  exact h

/-! ### The tangent projection `P_q` and its smoothness -/

variable [FiniteDimensional ℝ V]

/-- **The orthogonal projection `P_q` of `V` onto the tangent space `T_qN`.** -/
def tanProj (q : N) : V →L[ℝ] V := (tangentSubspace hN q).starProjection

theorem tanProj_apply_mem (q : N) (v : V) : tanProj hN q v ∈ tangentSubspace hN q :=
  Submodule.starProjection_apply_mem _ _

theorem tanProj_eq_self {q : N} {v : V} (hv : v ∈ tangentSubspace hN q) : tanProj hN q v = v :=
  Submodule.starProjection_eq_self_iff.2 hv

theorem tanProj_eq_self_iff {q : N} {v : V} : tanProj hN q v = v ↔ v ∈ tangentSubspace hN q :=
  Submodule.starProjection_eq_self_iff

theorem tanProj_tanProj (q : N) (v : V) : tanProj hN q (tanProj hN q v) = tanProj hN q v :=
  tanProj_eq_self hN (tanProj_apply_mem hN q v)

theorem tanProj_comp_tanProj (q : N) : (tanProj hN q).comp (tanProj hN q) = tanProj hN q := by
  ext v
  exact tanProj_tanProj hN q v

/-- `P_q` is self-adjoint. -/
theorem inner_tanProj_left (q : N) (v w : V) : ⟪tanProj hN q v, w⟫ = ⟪v, tanProj hN q w⟫ :=
  Submodule.inner_starProjection_left_eq_right _ _ _

theorem inner_tanProj_of_mem {q : N} (v : V) {w : V} (hw : w ∈ tangentSubspace hN q) :
    ⟪tanProj hN q v, w⟫ = ⟪v, w⟫ := by
  rw [inner_tanProj_left, tanProj_eq_self hN hw]

theorem tanProj_eq_zero_iff {q : N} {v : V} :
    tanProj hN q v = 0 ↔ v ∈ (tangentSubspace hN q)ᗮ :=
  Submodule.starProjection_apply_eq_zero_iff _

theorem sub_tanProj_mem_orthogonal (q : N) (v : V) :
    v - tanProj hN q v ∈ (tangentSubspace hN q)ᗮ := by
  rw [← tanProj_eq_zero_iff, map_sub, tanProj_tanProj, sub_self]

theorem tanProj_sub_tanProj (q : N) (v : V) : tanProj hN q (v - tanProj hN q v) = 0 :=
  (tanProj_eq_zero_iff hN).2 (sub_tanProj_mem_orthogonal hN q v)

/-- A vector both tangent and normal is zero. -/
theorem eq_zero_of_mem_of_mem_orthogonal {q : N} {v : V} (h1 : v ∈ tangentSubspace hN q)
    (h2 : v ∈ (tangentSubspace hN q)ᗮ) : v = 0 := by
  rw [← tanProj_eq_self hN h1]
  exact (tanProj_eq_zero_iff hN).2 h2

omit [FiniteDimensional ℝ V] in
/-- The parametrization of a slice chart has injective derivative. -/
theorem injective_fderiv_sliceParam (σ : Milnor.SliceChart 𝓘(ℝ, V) Z W N) {u : Z}
    (hu : u ∈ σ.toChart.target) : Injective (fderiv ℝ (sliceParam σ) u) := by
  have hx : HasFDerivAt (sliceParam σ) (fderiv ℝ (sliceParam σ) u) u :=
    ((contDiffAt_sliceParam σ hu).differentiableAt (by simp)).hasFDerivAt
  have hmem : sliceParam σ u ∈ σ.φ.source := σ.φ.invFun_mem hu
  have hφ : HasFDerivAt σ.φ (fderiv ℝ σ.φ (sliceParam σ u)) (sliceParam σ u) :=
    (Milnor.Problems.sliceChart_differentiableAt σ hmem).hasFDerivAt
  have hev : (fun u' => σ.φ (sliceParam σ u')) =ᶠ[𝓝 u] fun u' : Z => (u', (0 : W)) := by
    filter_upwards [(isOpen_toChart_target σ).mem_nhds hu] with u' hu'
    exact σ.φ.apply_invFun hu'
  have h1 := (hφ.comp u hx).congr_of_eventuallyEq hev.symm
  have h2 : HasFDerivAt (fun u' : Z => (u', (0 : W))) (ContinuousLinearMap.inl ℝ Z W) u :=
    (hasFDerivAt_id u).prodMk (hasFDerivAt_const _ _)
  have h3 := h1.unique h2
  intro a b hab
  have ha := DFunLike.congr_fun h3 a
  have hb := DFunLike.congr_fun h3 b
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inl_apply] at ha hb
  rw [hab] at ha
  exact (Prod.ext_iff.1 (ha.symm.trans hb)).1

variable [FiniteDimensional ℝ Z]

/-- **`P_q` in a slice chart**: `P_q = gramProj (dx_u)` at `u = (σ q)₁`, `x` the parametrization
of `σ`. -/
theorem tanProj_eq_gramProj (σ : Milnor.SliceChart 𝓘(ℝ, V) Z W N) {q : N}
    (hq : q.1 ∈ σ.φ.source) : tanProj hN q = gramProj (fderiv ℝ (sliceParam σ) (σ.φ q).1) :=
  (gramProj_eq_starProjection' (injective_fderiv_sliceParam σ (toChart_apply_mem_target σ hq))
    _ (tangentSubspace_eq_range_fderiv_sliceParam hN σ hq)).symm

/-- **The local ambient extension of `P`** given by a slice chart `σ`:
`y ↦ gramProj (dx_{(σ y)₁})`, `x` the parametrization of `σ`.  It is smooth near every point of
`N` in the domain of `σ` (`Morse.contDiffAt_projRep`) and equals `P` on `N`
(`Morse.projRep_eq`). -/
def projRep (σ : Milnor.SliceChart 𝓘(ℝ, V) Z W N) (y : V) : V →L[ℝ] V :=
  gramProj (fderiv ℝ (sliceParam σ) (σ.φ y).1)

theorem projRep_eq (σ : Milnor.SliceChart 𝓘(ℝ, V) Z W N) {x : N} (hx : x.1 ∈ σ.φ.source) :
    projRep σ x = tanProj hN x :=
  (tanProj_eq_gramProj hN σ hx).symm

omit [FiniteDimensional ℝ V] in
theorem contDiffAt_projRep [FiniteDimensional ℝ V] (σ : Milnor.SliceChart 𝓘(ℝ, V) Z W N) {q : N}
    (hq : q.1 ∈ σ.φ.source) : ContDiffAt ℝ ∞ (projRep σ) q := by
  have hu : (σ.φ q).1 ∈ σ.toChart.target := toChart_apply_mem_target σ hq
  have hc : ContDiffAt ℝ ∞ (fun y => (σ.φ y).1) q.1 :=
    contDiff_fst.contDiffAt.comp _
      ((Milnor.Problems.sliceChart_contDiffOn σ).contDiffAt (σ.φ.open_source.mem_nhds hq))
  have hA : ContDiffAt ℝ ∞ (fderiv ℝ (sliceParam σ)) (σ.φ q).1 :=
    ((contDiffOn_sliceParam σ).fderiv_of_isOpen (isOpen_toChart_target σ) (by simp)).contDiffAt
      ((isOpen_toChart_target σ).mem_nhds hu)
  have hG := contDiffAt_gramProj (n := ∞) (injective_fderiv_sliceParam σ hu)
  change ContDiffAt ℝ ∞ (fun y => gramProj (fderiv ℝ (sliceParam σ) (σ.φ y).1)) q.1
  exact (hG.comp _ hA).comp (f := fun y => (σ.φ y).1) _ hc

/-- **The tangent projection `q ↦ P_q` is a smooth map `N → (V →L V)`.** -/
theorem contMDiff_tanProj :
    letI := hN.chartedSpace
    ContMDiff 𝓘(ℝ, Z) 𝓘(ℝ, V →L[ℝ] V) ∞ (tanProj hN) := by
  let _ := hN.chartedSpace
  have := hN.isManifold
  intro q
  have hq := mem_sliceAt_source hN q
  have h1 : ContMDiffAt 𝓘(ℝ, Z) 𝓘(ℝ, V →L[ℝ] V) ∞ (projRep (sliceAt hN q) ∘ Subtype.val) q :=
    (contDiffAt_projRep (sliceAt hN q) hq).comp_contMDiffAt (hN.contMDiff_val q)
  refine h1.congr_of_eventuallyEq ?_
  filter_upwards [(sliceAt hN q).toChart.open_source.mem_nhds hq] with x hx
  exact (projRep_eq hN _ hx).symm

theorem mdifferentiableAt_tanProj (q : N) :
    letI := hN.chartedSpace
    MDifferentiableAt 𝓘(ℝ, Z) 𝓘(ℝ, V →L[ℝ] V) (tanProj hN) q := by
  let _ := hN.chartedSpace
  exact (contMDiff_tanProj hN q).mdifferentiableAt (by simp)

/-- The derivative of `P` along `N` is the derivative of its ambient extension. -/
theorem dN_tanProj_eq_fderiv (σ : Milnor.SliceChart 𝓘(ℝ, V) Z W N)
    {q : N} (hq : q.1 ∈ σ.φ.source) {v : V} (hv : v ∈ tangentSubspace hN q) :
    dN hN (tanProj hN) q v = fderiv ℝ (projRep σ) q v := by
  refine dN_eq_fderiv hN ((contDiffAt_projRep σ hq).differentiableAt (by simp)) ?_ hv
  filter_upwards [σ.toChart.open_source.mem_nhds hq] with x hx
  exact (projRep_eq hN σ hx).symm

/-! ### The derivative of the projection

Write `D_v = dN P q v` for `v ∈ T_qN`.  Differentiating `P* = P` and `P² = P` along `N` shows
that `D_v` is self-adjoint and `D_v P + P D_v = D_v`.  Hence `P D_v P = 0`: `D_v` carries tangent
vectors to normal vectors, and normal vectors to tangent ones. -/

/-- `D_v` is self-adjoint. -/
theorem inner_dN_tanProj_comm (q : N) (v x y : V) :
    ⟪dN hN (tanProj hN) q v x, y⟫ = ⟪x, dN hN (tanProj hN) q v y⟫ := by
  let L : (V →L[ℝ] V) →L[ℝ] ℝ :=
    (innerSL ℝ y).comp (ContinuousLinearMap.apply ℝ V x) -
      (innerSL ℝ x).comp (ContinuousLinearMap.apply ℝ V y)
  have hL : ∀ T : V →L[ℝ] V, L T = ⟪T x, y⟫ - ⟪x, T y⟫ := fun T => by
    simp only [L, sub_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply,
      innerSL_apply_apply, real_inner_comm y]
  have h0 : (fun x' : N => L (tanProj hN x')) = fun _ => 0 := by
    funext x'
    rw [hL, inner_tanProj_left, sub_self]
  have h := dN_clm_comp hN L (mdifferentiableAt_tanProj hN q)
  rw [h0, dN_const] at h
  have h1 := DFunLike.congr_fun h v
  simp only [zero_apply, ContinuousLinearMap.comp_apply] at h1
  rw [hL] at h1
  linarith

/-- Differentiating `P² = P`: `D_v P + P D_v = D_v`. -/
theorem dN_tanProj_comp_add {q : N} {v : V} (hv : v ∈ tangentSubspace hN q) :
    (dN hN (tanProj hN) q v).comp (tanProj hN q) + (tanProj hN q).comp (dN hN (tanProj hN) q v) =
      dN hN (tanProj hN) q v := by
  have h := dN_clm_comp' hN (mdifferentiableAt_tanProj hN q) (mdifferentiableAt_tanProj hN q) hv
  have hfun : (fun x : N => (tanProj hN x).comp (tanProj hN x)) = tanProj hN :=
    funext (tanProj_comp_tanProj hN)
  rw [hfun] at h
  exact h.symm

theorem dN_tanProj_apply_add {q : N} {v : V} (hv : v ∈ tangentSubspace hN q) (w : V) :
    dN hN (tanProj hN) q v (tanProj hN q w) + tanProj hN q (dN hN (tanProj hN) q v w) =
      dN hN (tanProj hN) q v w := by
  have h := DFunLike.congr_fun (dN_tanProj_comp_add hN hv) w
  simpa only [add_apply, ContinuousLinearMap.comp_apply] using h

/-- `P D_v P = 0`. -/
theorem tanProj_dN_tanProj {q : N} {v : V} (hv : v ∈ tangentSubspace hN q) (w : V) :
    tanProj hN q (dN hN (tanProj hN) q v (tanProj hN q w)) = 0 := by
  have h := dN_tanProj_apply_add hN hv (tanProj hN q w)
  rw [tanProj_tanProj] at h
  have h2 := congrArg (tanProj hN q) h
  rw [map_add, tanProj_tanProj] at h2
  exact add_eq_left.1 h2

/-- **`D_v` maps tangent vectors to normal vectors**: `P(D_v w) = 0` for `w ∈ T_qN`. -/
theorem tanProj_dN_tanProj_of_mem {q : N} {v w : V} (hv : v ∈ tangentSubspace hN q)
    (hw : w ∈ tangentSubspace hN q) : tanProj hN q (dN hN (tanProj hN) q v w) = 0 := by
  have h := tanProj_dN_tanProj hN hv w
  rwa [tanProj_eq_self hN hw] at h

/-- **`D_v` maps normal vectors to tangent vectors**: `D_v ν ∈ T_qN` for `ν ⊥ T_qN`. -/
theorem dN_tanProj_mem_of_mem_orthogonal {q : N} {v ν : V} (hv : v ∈ tangentSubspace hN q)
    (hν : ν ∈ (tangentSubspace hN q)ᗮ) :
    dN hN (tanProj hN) q v ν ∈ tangentSubspace hN q := by
  have h := dN_tanProj_apply_add hN hv ν
  rw [(tanProj_eq_zero_iff hN).2 hν, map_zero, zero_add] at h
  rw [← h]
  exact tanProj_apply_mem hN q _

theorem dN_tanProj_mem_orthogonal_of_mem {q : N} {v w : V} (hv : v ∈ tangentSubspace hN q)
    (hw : w ∈ tangentSubspace hN q) :
    dN hN (tanProj hN) q v w ∈ (tangentSubspace hN q)ᗮ :=
  (tanProj_eq_zero_iff hN).1 (tanProj_dN_tanProj_of_mem hN hv hw)

/-! ### Curves in `N` -/

section Curve

omit [FiniteDimensional ℝ V] [FiniteDimensional ℝ Z]

variable {c : ℝ → N}

/-- A curve in `N` which is smooth as a curve in `V` is smooth as a map into the manifold `N`. -/
theorem contMDiff_curve (hc : ContDiff ℝ ∞ (fun t => (c t : V))) :
    letI := hN.chartedSpace
    ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, Z) ∞ c :=
  hN.contMDiff_codRestrict (F := fun t => (c t : V)) (contMDiff_iff_contDiff.2 hc) fun t => (c t).2

/-- **The velocity vector of a curve in `N` is tangent to `N`.** -/
theorem deriv_mem_tangentSubspace (hc : ContDiff ℝ ∞ (fun t => (c t : V))) (t : ℝ) :
    deriv (fun s => (c s : V)) t ∈ tangentSubspace hN (c t) := by
  let _ := hN.chartedSpace
  have := hN.isManifold
  have hcm : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, Z) c t :=
    (contMDiff_curve hN hc t).mdifferentiableAt (by simp)
  have hval : MDifferentiableAt 𝓘(ℝ, Z) 𝓘(ℝ, V) (Subtype.val : N → V) (c t) :=
    hN.contMDiff_val.mdifferentiableAt (by simp)
  have h := mfderiv_comp t hval hcm
  rw [show (Subtype.val ∘ c) = fun s => (c s : V) from rfl, mfderiv_eq_fderiv] at h
  refine (mem_tangentSubspace_iff hN).2 ⟨mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, Z) c t 1, ?_⟩
  rw [← fderiv_apply_one_eq_deriv]
  exact (DFunLike.congr_fun h 1).symm

/-- **The chain rule along a curve**: `(F ∘ c)'(t) = dN F (c t) (c'(t))`. -/
theorem hasDerivAt_comp_curve (hc : ContDiff ℝ ∞ (fun t => (c t : V))) {F : N → E} {t : ℝ}
    (hF : letI := hN.chartedSpace; MDifferentiableAt 𝓘(ℝ, Z) 𝓘(ℝ, E) F (c t)) :
    HasDerivAt (fun s => F (c s)) (dN hN F (c t) (deriv (fun s => (c s : V)) t)) t := by
  let _ := hN.chartedSpace
  obtain ⟨G, hG, hFG⟩ := exists_differentiableAt_rep hN hF
  have hct : ContinuousAt c t := (contMDiff_curve hN hc).continuous.continuousAt
  have hev : (fun s => F (c s)) =ᶠ[𝓝 t] fun s => G (c s) := hct.eventually hFG
  have hd : HasDerivAt (fun s => (c s : V)) (deriv (fun s => (c s : V)) t) t :=
    ((hc.differentiable (by simp)) t).hasDerivAt
  have h1 : HasDerivAt (fun s => G (c s)) (fderiv ℝ G (c t) (deriv (fun s => (c s : V)) t)) t :=
    hG.hasFDerivAt.comp_hasDerivAt t hd
  rw [dN_eq_fderiv hN hG hFG (deriv_mem_tangentSubspace hN hc t)]
  exact h1.congr_of_eventuallyEq hev

/-- A smooth map on `N` composed with a smooth curve is smooth. -/
theorem contDiff_comp_curve (hc : ContDiff ℝ ∞ (fun t => (c t : V))) {F : N → E}
    (hF : letI := hN.chartedSpace; ContMDiff 𝓘(ℝ, Z) 𝓘(ℝ, E) ∞ F) :
    ContDiff ℝ ∞ (fun t => F (c t)) := by
  let _ := hN.chartedSpace
  exact contMDiff_iff_contDiff.1 (hF.comp (contMDiff_curve hN hc))

include hN in
/-- `t ↦ P_{c(t)}` is smooth along a smooth curve. -/
theorem contDiff_tanProj_comp [FiniteDimensional ℝ V] [FiniteDimensional ℝ Z]
    (hc : ContDiff ℝ ∞ (fun t => (c t : V))) : ContDiff ℝ ∞ (fun t => tanProj hN (c t)) :=
  contDiff_comp_curve hN hc (contMDiff_tanProj hN)

/-- The derivative of `t ↦ P_{c(t)}` is `D_{c'(t)} = dN P (c t) (c'(t))`. -/
theorem hasDerivAt_tanProj_comp [FiniteDimensional ℝ V] [FiniteDimensional ℝ Z]
    (hc : ContDiff ℝ ∞ (fun t => (c t : V))) (t : ℝ) :
    HasDerivAt (fun s => tanProj hN (c s))
      (dN hN (tanProj hN) (c t) (deriv (fun s => (c s : V)) t)) t :=
  hasDerivAt_comp_curve hN hc (mdifferentiableAt_tanProj hN (c t))

end Curve

/-! ### Maps from a normed space into `N` (parametrized surfaces) -/

section Map

omit [FiniteDimensional ℝ V] [FiniteDimensional ℝ Z]

variable {E₀ : Type*} [NormedAddCommGroup E₀] [NormedSpace ℝ E₀] {g : E₀ → N}

/-- A map into `N` which is smooth as a map into `V` is smooth as a map into the manifold `N`. -/
theorem contMDiff_map (hg : ContDiff ℝ ∞ (fun p => (g p : V))) :
    letI := hN.chartedSpace
    ContMDiff 𝓘(ℝ, E₀) 𝓘(ℝ, Z) ∞ g :=
  hN.contMDiff_codRestrict (F := fun p => (g p : V)) (contMDiff_iff_contDiff.2 hg) fun p => (g p).2

/-- The partial derivatives of a smooth map into `N` are tangent to `N`. -/
theorem fderiv_mem_tangentSubspace (hg : ContDiff ℝ ∞ (fun p => (g p : V))) (p w : E₀) :
    fderiv ℝ (fun p => (g p : V)) p w ∈ tangentSubspace hN (g p) := by
  let _ := hN.chartedSpace
  have := hN.isManifold
  have hgm : MDifferentiableAt 𝓘(ℝ, E₀) 𝓘(ℝ, Z) g p :=
    (contMDiff_map hN hg p).mdifferentiableAt (by simp)
  have hval : MDifferentiableAt 𝓘(ℝ, Z) 𝓘(ℝ, V) (Subtype.val : N → V) (g p) :=
    hN.contMDiff_val.mdifferentiableAt (by simp)
  have h := mfderiv_comp p hval hgm
  rw [show (Subtype.val ∘ g) = fun p => (g p : V) from rfl, mfderiv_eq_fderiv] at h
  exact (mem_tangentSubspace_iff hN).2 ⟨mfderiv 𝓘(ℝ, E₀) 𝓘(ℝ, Z) g p w,
    (DFunLike.congr_fun h w).symm⟩

/-- **The chain rule for maps into `N`**: `d(F ∘ g)_p = dN F (g p) ∘ dg_p`. -/
theorem hasFDerivAt_comp_map (hg : ContDiff ℝ ∞ (fun p => (g p : V))) {F : N → E} {p : E₀}
    (hF : letI := hN.chartedSpace; MDifferentiableAt 𝓘(ℝ, Z) 𝓘(ℝ, E) F (g p)) :
    HasFDerivAt (fun p => F (g p))
      ((dN hN F (g p)).comp (fderiv ℝ (fun p => (g p : V)) p)) p := by
  let _ := hN.chartedSpace
  obtain ⟨G, hG, hFG⟩ := exists_differentiableAt_rep hN hF
  have hgc : ContinuousAt g p := (contMDiff_map hN hg).continuous.continuousAt
  have hev : (fun p => F (g p)) =ᶠ[𝓝 p] fun p => G (g p) := hgc.eventually hFG
  have hd : HasFDerivAt (fun p => (g p : V)) (fderiv ℝ (fun p => (g p : V)) p) p :=
    ((hg.differentiable (by simp)) p).hasFDerivAt
  have h1 := hG.hasFDerivAt.comp p hd
  have heq : (fderiv ℝ G (g p)).comp (fderiv ℝ (fun p => (g p : V)) p) =
      (dN hN F (g p)).comp (fderiv ℝ (fun p => (g p : V)) p) := by
    ext w
    simp only [ContinuousLinearMap.comp_apply]
    exact (dN_eq_fderiv hN hG hFG (fderiv_mem_tangentSubspace hN hg p w)).symm
  rw [← heq]
  exact h1.congr_of_eventuallyEq hev

/-- A smooth map on `N` composed with a smooth map into `N` is smooth. -/
theorem contDiff_comp_map (hg : ContDiff ℝ ∞ (fun p => (g p : V))) {F : N → E}
    (hF : letI := hN.chartedSpace; ContMDiff 𝓘(ℝ, Z) 𝓘(ℝ, E) ∞ F) :
    ContDiff ℝ ∞ (fun p => F (g p)) := by
  let _ := hN.chartedSpace
  exact contMDiff_iff_contDiff.1 (hF.comp (contMDiff_map hN hg))

end Map

end Sub

end Morse
