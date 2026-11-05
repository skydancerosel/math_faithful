import Milnor.Chapter7.Lemma1

/-!
# Composing with a diffeomorphism of the sphere (for Milnor §7, Lemma 2)

For `r : Sᵖ → Sᵖ` smooth with `dr_y` bijective and orientation preserving, the Pontryagin
manifold of `r ∘ f` at `r y` is the Pontryagin manifold of `f` at `y` with the framing pulled
back through `dr_y`: `(r ∘ f)⁻¹(r y) = f⁻¹(y)` and `(r ∘ f)^* e = f^* (dr_y⁻¹ e)`.  Since `dr_y`
preserves orientation, `dr_y⁻¹ e` is again a positive basis, and Lemma 1 (general form) shows the
two Pontryagin manifolds are framed cobordant.
-/

open Set Filter Topology Function Module Metric
open scoped ContDiff Manifold RealInnerProductSpace

noncomputable section

namespace Milnor

/-! ### Orientation-preserving maps carry orientations -/

section orsign

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] {n : ℕ}

theorem sgn_eq_one_iff {x : ℝ} : sgn x = 1 ↔ 0 < x := by
  constructor
  · intro h
    by_contra h'
    push_neg at h'
    rcases h'.lt_or_eq with h1 | h1
    · rw [sgn_neg h1] at h; norm_num at h
    · rw [h1, sgn_zero] at h; norm_num at h
  · exact sgn_pos

/-- If `orSign a b T = 1` then `T` carries `a` to `b`. -/
theorem orientation_map_of_orSign_eq_one (hE : finrank ℝ E = n) {a : Orientation ℝ E (Fin n)}
    {b : Orientation ℝ F (Fin n)} {T : E →L[ℝ] F} (hT : Bijective T) (h : orSign a b T = 1) :
    Orientation.map (Fin n) (LinearEquiv.ofBijective (T : E →ₗ[ℝ] F) hT) a = b := by
  obtain ⟨c, hc⟩ := exists_eq_smul_of_finrank hE a.someVector_ne_zero
    (b.someVector.compLinearMap T.toLinearMap)
  have hs := orSign_eq_sgn a.someVector_ne_zero b.someVector_ne_zero (someVector_ray' a)
    (someVector_ray' b) hc
  rw [h] at hs
  have hcpos : 0 < c := sgn_eq_one_iff.1 hs.symm
  set L := LinearEquiv.ofBijective (T : E →ₗ[ℝ] F) hT with hL
  rw [← someVector_ray' a, Orientation.map_apply, ← someVector_ray' b, ray_eq_iff]
  have hη : b.someVector = c • (a.someVector.compLinearMap (L.symm : F →ₗ[ℝ] E)) := by
    have h1 : b.someVector = (b.someVector.compLinearMap T.toLinearMap).compLinearMap
        (L.symm : F →ₗ[ℝ] E) := by
      rw [AlternatingMap.compLinearMap_assoc]
      have : T.toLinearMap.comp (L.symm : F →ₗ[ℝ] E) = LinearMap.id := by
        ext x; exact L.apply_symm_apply x
      rw [this, AlternatingMap.compLinearMap_id]
    rw [h1, hc, smul_compLinearMap]
  rw [hη]
  exact SameRay.sameRay_pos_smul_right _ hcpos

end orsign

open Sphere

namespace Framed

/-! ### The pseudo-inverse of a composition -/

section pinvcomp

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

/-- `pinv A c` is the unique vector in the range of `A^*` mapped to `c`. -/
theorem pinv_unique {A : E →L[ℝ] F} (hA : Surjective A) {v : E}
    (hv : v ∈ LinearMap.range (ContinuousLinearMap.adjoint A : F →ₗ[ℝ] E)) {c : F}
    (hAv : A v = c) : v = pinv A c := by
  have h1 : A (pinv A c) = c := comp_pinv hA c
  have h2 : pinv A c ∈ LinearMap.range (ContinuousLinearMap.adjoint A : F →ₗ[ℝ] E) :=
    ⟨Ring.inverse (A.comp (ContinuousLinearMap.adjoint A)) c, rfl⟩
  obtain ⟨t, ht⟩ := Submodule.sub_mem _ hv h2
  have ht' : ContinuousLinearMap.adjoint A t = v - pinv A c := ht
  have h3 : ⟪v - pinv A c, v - pinv A c⟫ = 0 := by
    rw [← ht', ContinuousLinearMap.adjoint_inner_left, ht', map_sub, h1, hAv, sub_self,
      inner_zero_right]
  exact sub_eq_zero.1 (inner_self_eq_zero.1 h3)

theorem adjoint_surjective_of_injective {D : F →L[ℝ] F} (hD : Injective D) :
    Surjective (ContinuousLinearMap.adjoint D) := by
  have hsurj : Surjective D :=
    LinearMap.injective_iff_surjective (f := (D : F →ₗ[ℝ] F)) |>.1 hD
  have hinj : Injective (ContinuousLinearMap.adjoint D) := by
    refine (injective_iff_map_eq_zero _).2 fun t ht => ?_
    have : ∀ v, ⟪t, D v⟫ = 0 := fun v => by
      rw [← ContinuousLinearMap.adjoint_inner_left, ht, inner_zero_left]
    obtain ⟨v, hv⟩ := hsurj t
    have h0 := this v
    rw [hv] at h0
    exact inner_self_eq_zero.1 h0
  exact LinearMap.injective_iff_surjective
    (f := (ContinuousLinearMap.adjoint D : F →ₗ[ℝ] F)) |>.1 hinj

/-- `pinv (D ∘ A) c = pinv A (D⁻¹ c)` for `D` bijective. -/
theorem pinv_comp {A : E →L[ℝ] F} (hA : Surjective A) {D : F →L[ℝ] F} (hD : Bijective D)
    {Dinv : F → F} (hDinv : ∀ c, D (Dinv c) = c) (c : F) :
    pinv (D.comp A) c = pinv A (Dinv c) := by
  symm
  have hDA : Surjective (D.comp A) := hD.2.comp hA
  apply pinv_unique hDA
  · rw [ContinuousLinearMap.adjoint_comp]
    obtain ⟨s, hs⟩ := adjoint_surjective_of_injective hD.1
      (Ring.inverse (A.comp (ContinuousLinearMap.adjoint A)) (Dinv c))
    refine ⟨s, ?_⟩
    show ContinuousLinearMap.adjoint A (ContinuousLinearMap.adjoint D s) = pinv A (Dinv c)
    rw [hs]; rfl
  · show D (A (pinv A (Dinv c))) = c
    rw [comp_pinv hA, hDinv]

end pinvcomp

variable {K m w : ℕ} {M : Set (EuclideanSpace ℝ (Fin (K + 1)))}
  (hM : IsSliceSubmanifold 𝓘(ℝ, EuclideanSpace ℝ (Fin (K + 1))) (EuclideanSpace ℝ (Fin m))
    (EuclideanSpace ℝ (Fin w)) M) (hMc : IsCompact M) (hne : M.Nonempty)
  {p n : ℕ}

section comp

variable {f : M → Sph p}
  (hf : letI := hM.chartedSpace; haveI := hM.isManifold;
    ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) ∞ f)
  {r : Sph p → Sph p}
  (hr : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) ∞ r)
  (y : Sph p)

include hr in
/-- The derivative of `r` read in the charts at `y` and `r y` is `mfd r y`. -/
theorem hasFDerivAt_written :
    HasFDerivAt (extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) (r y) ∘ r ∘
        (extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) y).symm)
      (mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) r y)
      (extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) y y) := by
  have h := (hr.mdifferentiableAt (by simp) : MDifferentiableAt 𝓘(ℝ, EuclideanSpace ℝ (Fin p))
    𝓘(ℝ, EuclideanSpace ℝ (Fin p)) r y).hasMFDerivAt
  have h2 := h.2
  rw [ModelWithCorners.range_eq_univ] at h2
  exact hasFDerivWithinAt_univ.1 h2

include hf hr in
/-- The chain rule for the extensions: `A_{r ∘ f}(x) = dr_y ∘ A_f(x)` at points of `f⁻¹(y)`. -/
theorem At_comp {x : EuclideanSpace ℝ (Fin (K + 1))} (hx : x ∈ M) (hfx : f ⟨x, hx⟩ = y) :
    At hM hMc hne (fun q => r (f q)) (r y) x =
      (mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) r y).comp
        (At hM hMc hne f y x) := by
  letI := hM.chartedSpace
  haveI := hM.isManifold
  have hsrc : f ⟨x, hx⟩ ∈ (extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) y).source := by
    rw [hfx]; exact mem_extChartAt_source y
  have hxW : x ∈ Wt hM hMc hne f y := mem_Wt_of_mem hM hMc hne hx hsrc
  have hev : Ft hM hMc hne (fun q => r (f q)) (r y) =ᶠ[𝓝 x]
      (extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) (r y) ∘ r ∘
        (extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) y).symm) ∘ Ft hM hMc hne f y := by
    filter_upwards [(isOpen_Wt hM hMc hne hf).mem_nhds hxW] with w hw
    simp only [Function.comp, Ft]
    rw [(extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) y).left_inv hw.2]
  have hFx : Ft hM hMc hne f y x = extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) y y := by
    rw [Ft_of_mem hM hMc hne hx, hfx]
  have hD := hasFDerivAt_written hr y
  rw [← hFx] at hD
  have hchain := hD.comp x (hasFDerivAt_Ft hM hMc hne hf hxW)
  have := hchain.congr_of_eventuallyEq hev
  unfold At
  exact this.fderiv

include hf hr in
/-- `r y` is a regular value of `r ∘ f` when `y` is one of `f` and `dr_y` is bijective. -/
theorem isRegularValue_comp
    (hy : letI := hM.chartedSpace; haveI := hM.isManifold;
      IsRegularValue 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) f y)
    (hbij : Bijective (mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) r y))
    (hinj : ∀ q, r (f q) = r y → f q = y) :
    letI := hM.chartedSpace; haveI := hM.isManifold;
    IsRegularValue 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 𝓘(ℝ, EuclideanSpace ℝ (Fin p))
      (fun q => r (f q)) (r y) := by
  letI := hM.chartedSpace
  haveI := hM.isManifold
  intro x hx
  have hfx : f x = y := hinj x hx
  have h1 := hasMFDerivAt_mfd (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin p)))
    (J := 𝓘(ℝ, EuclideanSpace ℝ (Fin p)))
    (hr.mdifferentiableAt (by simp) : MDifferentiableAt _ _ r (f x))
  have h2 := hasMFDerivAt_mfd (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin m)))
    (J := 𝓘(ℝ, EuclideanSpace ℝ (Fin p)))
    (hf.mdifferentiableAt (by simp) : MDifferentiableAt _ _ f x)
  have h3 := HasMFDerivAt.mfd_eq (h1.comp x h2)
  have h4 : (r ∘ f) = fun q => r (f q) := rfl
  rw [h4] at h3
  show Surjective (mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 𝓘(ℝ, EuclideanSpace ℝ (Fin p))
    (fun q => r (f q)) x)
  rw [h3]
  have hs1 : Surjective (mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) f x) :=
    hy x hfx
  have hs2 : Surjective (mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) r (f x)) := by
    rw [hfx]; exact hbij.2
  exact hs2.comp hs1

include hf hr in
/-- The framing of `r ∘ f` at `r y` is the framing of `f` at `y` pulled back through `dr_y⁻¹`. -/
theorem pontV_comp
    (hy : letI := hM.chartedSpace; haveI := hM.isManifold;
      IsRegularValue 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) f y)
    (hbij : Bijective (mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) r y))
    (e : Fin p → EuclideanSpace ℝ (Fin p)) (i : Fin p) (x : M) (hfx : f x = y)
    (hx' : x ∈ (fun q => r (f q)) ⁻¹' {r y}) (hxy : x ∈ f ⁻¹' {y}) :
    pontV hM hMc hne (fun q => r (f q)) (r y) e i ⟨x, hx'⟩ =
      pontV hM hMc hne f y (fun j => (LinearEquiv.ofBijective
        (mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) r y :
          EuclideanSpace ℝ (Fin p) →ₗ[ℝ] EuclideanSpace ℝ (Fin p)) hbij).symm (e j)) i ⟨x, hxy⟩ := by
  letI := hM.chartedSpace
  haveI := hM.isManifold
  set L := LinearEquiv.ofBijective (mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin p))
    𝓘(ℝ, EuclideanSpace ℝ (Fin p)) r y : EuclideanSpace ℝ (Fin p) →ₗ[ℝ] EuclideanSpace ℝ (Fin p)) hbij
    with hL
  show pinv (At hM hMc hne (fun q => r (f q)) (r y) x.1) (e i) =
    pinv (At hM hMc hne f y x.1) (L.symm (e i))
  rw [At_comp hM hMc hne hf hr y x.2 (by rw [Subtype.coe_eta]; exact hfx)]
  exact pinv_comp (surjective_At hM hMc hne hf hy x.2 (by rw [Subtype.coe_eta]; exact hfx)) hbij
    (fun c => L.apply_symm_apply c) (e i)

include hf hr in
/-- **Composition with an orientation-preserving diffeomorphism of the sphere.**  For positive
bases `e` at `r y` and `e₀` at `y`, the Pontryagin manifolds `(r ∘ f)⁻¹(r y)` and `f⁻¹(y)` are
framed cobordant. -/
theorem framedCobordant_comp (hnp : n + p = m)
    (hy : letI := hM.chartedSpace; haveI := hM.isManifold;
      IsRegularValue 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) f y)
    (hbij : Bijective (mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) r y))
    (hsign : signAt (sphOr p) (sphOr p) r y = 1)
    (hinj : ∀ q, r (f q) = r y → f q = y)
    (e : Basis (Fin p) ℝ (EuclideanSpace ℝ (Fin p))) (he : e.orientation = (sphOr p).or (r y))
    (e₀ : Basis (Fin p) ℝ (EuclideanSpace ℝ (Fin p))) (he₀ : e₀.orientation = (sphOr p).or y) :
    letI := hM.chartedSpace; haveI := hM.isManifold;
    FramedCobordant hM
      (pontryagin hM hMc hne (f := fun q => r (f q)) (hr.comp hf)
        (isRegularValue_comp hM hf hr y hy hbij hinj) hnp e e.linearIndependent)
      (pontryagin hM hMc hne hf hy hnp e₀ e₀.linearIndependent) := by
  letI := hM.chartedSpace
  haveI := hM.isManifold
  set L := LinearEquiv.ofBijective (mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin p))
    𝓘(ℝ, EuclideanSpace ℝ (Fin p)) r y : EuclideanSpace ℝ (Fin p) →ₗ[ℝ] EuclideanSpace ℝ (Fin p)) hbij
    with hL
  set e' : Basis (Fin p) ℝ (EuclideanSpace ℝ (Fin p)) := e.map L.symm with he'def
  have he' : e'.orientation = (sphOr p).or y := by
    rw [he'def, Basis.orientation_map, he]
    have hmap : Orientation.map (Fin p) L ((sphOr p).or y) = (sphOr p).or (r y) :=
      orientation_map_of_orSign_eq_one hZ hbij hsign
    rw [← hmap, ← Orientation.map_symm, Equiv.symm_apply_apply]
  obtain ⟨A, hA, hAe⟩ := GLp.exists_det_pos_of_orientation_eq e₀ e' (he₀.trans he'.symm)
  have hN : (fun q => r (f q)) ⁻¹' {r y} = f ⁻¹' {y} := by
    ext q
    constructor
    · intro h; exact hinj q h
    · intro h
      show r (f q) = r y
      have : f q = y := h
      rw [this]
  refine framedCobordant_of_det_pos' hM hMc hne hnp hf hy (hr.comp hf)
    (isRegularValue_comp hM hf hr y hy hbij hinj) e₀.linearIndependent e.linearIndependent hA hN ?_
  intro i x hx hx'
  rw [hAe]
  have hfx : f x = y := hx
  have hfun : (⇑e' : Fin p → EuclideanSpace ℝ (Fin p)) = fun j => L.symm (e j) := by
    funext j; rw [he'def, Basis.map_apply]
  rw [hfun]
  exact pontV_comp hM hMc hne hf hr y hy hbij e i x hfx hx' hx

end comp

end Framed

end Milnor
