import Milnor.Chapter3.Step2

/-!
Milnor, *Topology from the Differentiable Viewpoint*, §3, Step 1 (pp. 17–18).

# Step 1: `f(C ∖ C₁)` has measure zero

> This first step is perhaps the hardest. […] We will need the well known theorem of Fubini which
> asserts that a measurable set `A ⊆ ℝᵖ = ℝ¹ × ℝᵖ⁻¹` must have measure zero if it intersects each
> hyperplane `(constant) × ℝᵖ⁻¹` in a set of `(p-1)`-dimensional measure zero.
>
> For each `x̄ ∈ C ∖ C₁` we will find an open neighborhood `V ⊆ ℝⁿ` so that `f(V ∩ C)` has
> measure zero. […] Since `x̄ ∉ C₁`, there is some partial derivative, say `∂f₁/∂x₁`, which is
> not zero at `x̄`. Consider the map `h(x) = (f₁(x), x₂, …, xₙ)`. Since `dh_x̄` is nonsingular, `h`
> maps some neighborhood `V` of `x̄` diffeomorphically onto an open set `V'`. The composition
> `g = f ∘ h⁻¹` will then map `V'` into `ℝᵖ`. Note that the set `C'` of critical points of `g` is
> precisely `h(V ∩ C)`; hence the set `g(C')` of critical values of `g` is equal to `f(V ∩ C)`.
>
> For each `(t, x₂, …, xₙ) ∈ V'` note that `g(t, x₂, …, xₙ)` belongs to the hyperplane
> `t × ℝᵖ⁻¹ ⊆ ℝᵖ`: thus `g` carries hyperplanes into hyperplanes. Let `gᵗ` denote the restriction
> of `g` to `(t × ℝⁿ⁻¹) ∩ V'`. Note that a point of `t × ℝⁿ⁻¹` is critical for `gᵗ` if and only if
> it is critical for `g`; for the matrix of first derivatives of `g` has the form
> `[1 0; * ∂gᵗᵢ/∂xⱼ]`. According to the induction hypothesis, the set of critical values of `gᵗ` has
> measure zero in `t × ℝᵖ⁻¹`. Therefore the set of critical values of `g` intersects each
> hyperplane `t × ℝᵖ⁻¹` in a set of measure zero. This set `g(C')` is measurable, since it can
> be expressed as a countable union of compact subsets. Hence, by Fubini's theorem, the set
> `g(C') = f(V ∩ C)` has measure zero.

Coordinate-free version. Choose `ℓ₀ : F → ℝ` with `ℓ₀(df_x̄(u)) ≠ 0`, put `w = ℓ₀ ∘ f` (Milnor's
`f₁`) and straighten `w` (`Straightening`): `H : V → V' ⊆ ℝ × K`, `G = H⁻¹`. Split `F = ℝ × F₁`
along `ℓ₀` with `F₁ = ker ℓ₀`, via `e(y) = (ℓ₀(y), Q(y))`. Then `g = f ∘ G` satisfies
`ℓ₀ ∘ g = fst` on `V'`, and `gᵗ = Q ∘ g(t, ·) : K → F₁`. The block-matrix remark becomes
`e ∘ dg_{(t,z)} (s, u) = (s, ∗ + d(gᵗ)_z u)`, so `dg` is onto iff `d(gᵗ)` is (`hcrit` below). We
take `V` to be a closed ball, so that `f(C ∩ V)` is compact, hence measurable, and Milnor's
"countable union of compact subsets" is not needed.
-/

open Set Filter Topology Function MeasureTheory Module
open scoped ContDiff

noncomputable section

namespace Milnor

namespace Sard

universe u

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {F : Type u} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]

/-- **Step 1, local form** (Milnor pp. 17–18). Assuming Sard's theorem in dimension `n - 1`,
every `x̄ ∈ C ∖ C₁` has a neighbourhood `V` such that `f(C ∩ V)` has measure zero. -/
theorem step1_local (ih : SardStatement.{u} (finrank ℝ E - 1)) [Nontrivial F]
    (μ : Measure F) [μ.IsAddHaarMeasure] {f : E → F} {U : Set E} (hU : IsOpen U)
    (hf : ContDiffOn ℝ ∞ f U) {x₀ : E} (hx₀ : x₀ ∈ critSet f U \ vanishSet f U 1) :
    ∃ V ∈ 𝓝 x₀, μ (f '' (critSet f U ∩ V)) = 0 := by
  have hx₀U : x₀ ∈ U := hx₀.1.1
  have hf_diff : ∀ x ∈ U, DifferentiableAt ℝ f x := fun x hx =>
    (hf.contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp)
  -- `df_{x₀} ≠ 0` since `x₀ ∉ C₁`.
  have hdf : fderiv ℝ f x₀ ≠ 0 := by
    intro h0
    apply hx₀.2
    refine ⟨hx₀U, fun j hj hjk => ?_⟩
    have : j = 1 := by omega
    subst this
    rw [← norm_eq_zero, norm_iteratedFDeriv_one, h0, norm_zero]
  obtain ⟨u, hu⟩ : ∃ u, fderiv ℝ f x₀ u ≠ 0 := by
    by_contra h
    push Not at h
    exact hdf (ContinuousLinearMap.ext h)
  obtain ⟨ℓ₀, -, hℓ₀⟩ := exists_dual_vector ℝ (fderiv ℝ f x₀ u) (norm_ne_zero_iff.2 hu)
  have hℓ₀' : ℓ₀ (fderiv ℝ f x₀ u) ≠ 0 := by
    rw [hℓ₀]; exact_mod_cast norm_ne_zero_iff.2 hu
  -- `w = ℓ₀ ∘ f` (Milnor's `f₁`).
  set w : E → ℝ := fun x => ℓ₀ (f x) with hw_def
  have hw_smooth : ContDiffOn ℝ ∞ w U := ℓ₀.contDiff.comp_contDiffOn hf
  have hw_deriv : fderiv ℝ w x₀ ≠ 0 := by
    have hw' : HasFDerivAt w (ℓ₀.comp (fderiv ℝ f x₀)) x₀ :=
      ℓ₀.hasFDerivAt.comp x₀ (hf_diff x₀ hx₀U).hasFDerivAt
    rw [hw'.fderiv]
    intro h0
    have := congrArg (fun L : E →L[ℝ] ℝ => L u) h0
    simp only [ContinuousLinearMap.comp_apply, zero_apply] at this
    exact hℓ₀' this
  obtain ⟨S⟩ := exists_straightening hU hw_smooth hx₀U hw_deriv
  -- Split `F = ℝ × F₁` along `ℓ₀`.
  set y₀ : F := (ℓ₀ (fderiv ℝ f x₀ u))⁻¹ • fderiv ℝ f x₀ u with hy₀
  have hℓy₀ : ℓ₀ y₀ = 1 := by simp [hy₀, inv_mul_cancel₀ hℓ₀']
  set F₁ : Submodule ℝ F := LinearMap.ker (ℓ₀ : F →ₗ[ℝ] ℝ) with hF₁
  have hmemF₁ : ∀ z : F₁, ℓ₀ z = 0 := fun z => LinearMap.mem_ker.1 z.2
  have hQmem : ∀ y, (ContinuousLinearMap.id ℝ F - ℓ₀.smulRight y₀) y ∈ F₁ := fun y => by
    simp [hF₁, LinearMap.mem_ker, hℓy₀]
  set Q : F →L[ℝ] F₁ := (ContinuousLinearMap.id ℝ F - ℓ₀.smulRight y₀).codRestrict F₁ hQmem
    with hQ
  have hQ_apply : ∀ y, (Q y : F) = y - ℓ₀ y • y₀ := fun y => by simp [hQ]
  have hQ_of_mem : ∀ y, ℓ₀ y = 0 → (Q y : F) = y := fun y hy => by
    rw [hQ_apply, hy, zero_smul, sub_zero]
  let Rinv : ℝ × F₁ →L[ℝ] F :=
    F₁.subtypeL.comp (ContinuousLinearMap.snd ℝ ℝ F₁) + (ContinuousLinearMap.fst ℝ ℝ F₁).smulRight y₀
  have hRinv : ∀ p : ℝ × F₁, Rinv p = (p.2 : F) + p.1 • y₀ := fun p => by simp [Rinv]
  let e : F ≃L[ℝ] ℝ × F₁ :=
    ContinuousLinearEquiv.equivOfInverse (ℓ₀.prod Q) Rinv
      (fun y => by
        rw [hRinv]
        simp only [ContinuousLinearMap.prod_apply, hQ_apply]
        abel)
      (fun p => by
        rw [hRinv]
        have h1 : ℓ₀ ((p.2 : F) + p.1 • y₀) = p.1 := by simp [hmemF₁ p.2, hℓy₀]
        have h2 : Q ((p.2 : F) + p.1 • y₀) = p.2 := by
          apply Subtype.ext
          rw [hQ_apply, h1]
          simp
        simp only [ContinuousLinearMap.prod_apply, h1, h2])
  have he_apply : ∀ y, e y = (ℓ₀ y, Q y) := fun _ => rfl
  -- `g = f ∘ G` on `V'`; it satisfies `ℓ₀ ∘ g = fst`.
  set g : ℝ × S.K → F := fun p => f (S.G p) with hg
  have hg_smooth : ContDiffOn ℝ ∞ g S.V' :=
    hf.comp S.contDiffOn_G fun p hp => S.V_subset (S.mapsTo_G hp)
  have hg_fst : ∀ p ∈ S.V', ℓ₀ (g p) = p.1 := fun p hp => by
    have := S.H_fst (S.G p)
    rw [S.right_inv p hp] at this
    exact this.symm
  -- The slices `gᵗ = Q ∘ g(t, ·) : K → F₁` on `Vₜ = {z | (t, z) ∈ V'}`.
  set incl : ℝ → S.K → ℝ × S.K := fun t z => (t, z) with hincl
  set Vt : ℝ → Set S.K := fun t => {z | (t, z) ∈ S.V'} with hVt
  have hVt_open : ∀ t, IsOpen (Vt t) := fun t =>
    S.isOpen_V'.preimage (continuous_const.prodMk continuous_id)
  set gt : ℝ → S.K → F₁ := fun t z => Q (g (t, z)) with hgt
  have hgt_smooth : ∀ t, ContDiffOn ℝ ∞ (gt t) (Vt t) := fun t => by
    have h1 : ContDiffOn ℝ ∞ (incl t) (Vt t) := (contDiff_const.prodMk contDiff_id).contDiffOn
    exact Q.contDiff.comp_contDiffOn (hg_smooth.comp h1 fun z hz => hz)
  -- A Haar measure on `F₁`, and the induction hypothesis for each slice.
  let μ₁ : Measure F₁ := (Module.Basis.ofVectorSpace ℝ F₁).addHaar
  have hK : finrank ℝ S.K = finrank ℝ E - 1 := by have := S.finrank_K; omega
  have hslice : ∀ t, μ₁ (gt t '' critSet (gt t) (Vt t)) = 0 := fun t =>
    ih S.K hK F₁ μ₁ (Vt t) (hVt_open t) (gt t) (hgt_smooth t)
  -- Milnor's block-matrix remark: a critical point of `g` is a critical point of the slice map.
  have hcrit : ∀ p ∈ critSet g S.V', p.2 ∈ critSet (gt p.1) (Vt p.1) := by
    rintro ⟨t, z⟩ ⟨hp, hnsurj⟩
    refine ⟨hp, fun hsurj => hnsurj ?_⟩
    have hg_diff : DifferentiableAt ℝ g (t, z) :=
      (hg_smooth.contDiffAt (S.isOpen_V'.mem_nhds hp)).differentiableAt (by simp)
    set D := fderiv ℝ g (t, z) with hD
    -- `ℓ₀ ∘ D = fst`.
    have hℓD : ∀ q : ℝ × S.K, ℓ₀ (D q) = q.1 := by
      intro q
      have h1 : fderiv ℝ (fun p => ℓ₀ (g p)) (t, z) = ℓ₀.comp D :=
        (ℓ₀.hasFDerivAt.comp (t, z) hg_diff.hasFDerivAt).fderiv
      have h2 : fderiv ℝ (fun p => ℓ₀ (g p)) (t, z) = ContinuousLinearMap.fst ℝ ℝ S.K := by
        have heq : (fun p => ℓ₀ (g p)) =ᶠ[𝓝 (t, z)] Prod.fst := by
          filter_upwards [S.isOpen_V'.mem_nhds hp] with q hq
          exact hg_fst q hq
        rw [heq.fderiv_eq]
        exact (ContinuousLinearMap.fst ℝ ℝ S.K).fderiv
      have := congrArg (fun L : ℝ × S.K →L[ℝ] ℝ => L q) (h1.symm.trans h2)
      simpa using this
    -- `d(gᵗ)_z = Q ∘ D ∘ inr`.
    have hgt_fderiv : fderiv ℝ (gt t) z = Q.comp (D.comp (ContinuousLinearMap.inr ℝ ℝ S.K)) := by
      have h1 : HasFDerivAt (incl t) (ContinuousLinearMap.inr ℝ ℝ S.K) z :=
        (hasFDerivAt_const t z).prodMk (hasFDerivAt_id z)
      have h3 : HasFDerivAt (fun z => g (incl t z)) (D.comp (ContinuousLinearMap.inr ℝ ℝ S.K)) z :=
        hg_diff.hasFDerivAt.comp z h1
      exact (Q.hasFDerivAt.comp z h3).fderiv
    rw [hgt_fderiv] at hsurj
    -- Solve `D (s, u) = y`.
    intro y
    obtain ⟨u', hu'⟩ := hsurj (Q (y - D (ℓ₀ y, 0)))
    refine ⟨(ℓ₀ y, 0) + (0, u'), ?_⟩
    rw [map_add]
    have hQD : (Q (D (0, u')) : F) = D (0, u') := hQ_of_mem _ (by rw [hℓD])
    have hQy : (Q (y - D (ℓ₀ y, 0)) : F) = y - D (ℓ₀ y, 0) :=
      hQ_of_mem _ (by rw [map_sub, hℓD]; simp)
    have hu'' : (Q (D (0, u')) : F) = (Q (y - D (ℓ₀ y, 0)) : F) := by
      simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply] at hu'
      rw [hu']
    rw [hQD, hQy] at hu''
    rw [hu'']
    abel
  -- The compact neighbourhood `B` and the compact set `T = f(C ∩ B)`.
  obtain ⟨r, hr, hB⟩ : ∃ r > 0, Metric.closedBall x₀ r ⊆ S.V := by
    obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 S.isOpen_V x₀ S.mem_V
    exact ⟨r / 2, by positivity, (Metric.closedBall_subset_ball (by linarith)).trans hball⟩
  refine ⟨Metric.closedBall x₀ r, Metric.closedBall_mem_nhds x₀ hr, ?_⟩
  set B := Metric.closedBall x₀ r with hB_def
  have hBU : B ⊆ U := hB.trans S.V_subset
  have hCB : IsCompact (critSet f U ∩ B) :=
    isCompact_critSet_inter hU (hf.of_le (mod_cast le_top)) (isCompact_closedBall x₀ r) hBU
  set T := f '' (critSet f U ∩ B) with hT
  have hT_compact : IsCompact T :=
    hCB.image_of_continuousOn (hf.continuousOn.mono fun x hx => hx.1.1)
  -- Every slice of `e(T)` lies in the (null) set of critical values of the slice map.
  have hslice_sub : ∀ t, Prod.mk t ⁻¹' (e '' T) ⊆ gt t '' critSet (gt t) (Vt t) := by
    intro t y₁ hy₁
    obtain ⟨y, ⟨x, ⟨hxC, hxB⟩, rfl⟩, hey⟩ := hy₁
    have hxV : x ∈ S.V := hB hxB
    have hpV' : S.H x ∈ S.V' := S.mapsTo_H hxV
    have hGp : S.G (S.H x) = x := S.left_inv x hxV
    have hgp : g (S.H x) = f x := by simp only [hg, hGp]
    have hey1 : ℓ₀ (f x) = t := by
      have := congrArg Prod.fst hey
      simpa [he_apply] using this
    have hey2 : Q (f x) = y₁ := by
      have := congrArg Prod.snd hey
      simpa [he_apply] using this
    have hpt : (S.H x).1 = t := by
      rw [← hg_fst _ hpV', hgp, hey1]
    -- `H x` is a critical point of `g`, because `x` is a critical point of `f`.
    have hp_crit : S.H x ∈ critSet g S.V' := by
      refine ⟨hpV', fun hsurj => hxC.2 ?_⟩
      have hGdiff : DifferentiableAt ℝ S.G (S.H x) :=
        (S.contDiffOn_G.contDiffAt (S.isOpen_V'.mem_nhds hpV')).differentiableAt (by simp)
      have hfdiff : DifferentiableAt ℝ f (S.G (S.H x)) := by
        rw [hGp]; exact hf_diff x hxC.1
      have hchain : fderiv ℝ g (S.H x) = (fderiv ℝ f (S.G (S.H x))).comp (fderiv ℝ S.G (S.H x)) :=
        fderiv_comp _ hfdiff hGdiff
      rw [hGp] at hchain
      rw [hchain, ContinuousLinearMap.coe_comp] at hsurj
      exact hsurj.of_comp
    have hz_crit := hcrit _ hp_crit
    rw [hpt] at hz_crit
    refine ⟨(S.H x).2, hz_crit, ?_⟩
    have hp_eq : (t, (S.H x).2) = S.H x := by
      rw [← hpt]
    show Q (g (t, (S.H x).2)) = y₁
    rw [hp_eq, hgp, hey2]
  -- Fubini.
  have hTe_meas : MeasurableSet (e '' T) := (hT_compact.image e.continuous).measurableSet
  have hprod : ((volume : Measure ℝ).prod μ₁) (e '' T) = 0 := by
    rw [Measure.measure_prod_null hTe_meas]
    exact Filter.Eventually.of_forall fun t => measure_mono_null (hslice_sub t) (hslice t)
  have hmap : (μ.map e) ≪ ((volume : Measure ℝ).prod μ₁) :=
    Measure.absolutelyContinuous_isAddHaarMeasure _ _
  have hemb : MeasurableEmbedding e := e.toHomeomorph.measurableEmbedding
  have hμT : (μ.map e) (e '' T) = μ T := by
    rw [hemb.map_apply, e.injective.preimage_image]
  rw [← hμT]
  exact hmap hprod

end Sard

end Milnor
