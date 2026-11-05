import Milnor.Chapter5.OrSign
import Milnor.Chapter1.RegularValue

/-!
# Oriented manifolds and the sign of a derivative

An **orientation** of a manifold `M` modelled on `E` (Milnor p. 26) is a choice of orientation of
each tangent space `T_xM = E` which is continuous in the following sense: the chart at `x`
carries the orientation at each nearby point `y` to the orientation at `x`, i.e.
`orSign (or y) (or x) (d(extChartAt x)_y) = 1`.

For `f : M → N` between oriented manifolds of the same dimension, `signAt f x` is the sign of
`df_x` (`0` at a critical point).  The main result of this file is that `signAt f` is locally
constant near a regular point.  We also orient `M × ℝ` from an orientation of `M`.

Throughout, `mfd I J f x` is `mfderiv I J f x` typed as a map `E →L[ℝ] F` between the model
spaces; this avoids the dependent `TangentSpace` types in rewriting.
-/

open Set Module Filter Topology Function
open scoped ContDiff Manifold

noncomputable section

namespace Milnor

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {G : Type*} [TopologicalSpace G] {J : ModelWithCorners ℝ F G}
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N] {n : ℕ}

/-- `mfderiv I J f x`, typed as a linear map between the model spaces. -/
def mfd (I : ModelWithCorners ℝ E H) (J : ModelWithCorners ℝ F G) (f : M → N) (x : M) :
    E →L[ℝ] F :=
  mfderiv I J f x

theorem HasMFDerivAt.mfd_eq {f : M → N} {x : M} {f' : E →L[ℝ] F} (h : HasMFDerivAt I J f x f') :
    mfd I J f x = f' := h.mfderiv

theorem hasMFDerivAt_mfd {f : M → N} {x : M} (h : MDifferentiableAt I J f x) :
    HasMFDerivAt I J f x (mfd I J f x :) := h.hasMFDerivAt

/-- An orientation of `M`: an orientation of each tangent space `T_xM = E`, continuous in the
sense that the chart at `x` carries the orientation at nearby points `y` to the orientation
at `x`. -/
structure Orient (I : ModelWithCorners ℝ E H) (M : Type*) [TopologicalSpace M] [ChartedSpace H M]
    (n : ℕ) where
  or : M → Orientation ℝ E (Fin n)
  cont : ∀ x : M, ∀ᶠ y in 𝓝 x, orSign (or y) (or x) (mfd I 𝓘(ℝ, E) (extChartAt I x) y) = 1

/-- The sign of `df_x` relative to orientations of `M` and `N`: `±1` at a regular point, `0` at a
critical point. -/
def signAt (oM : Orient I M n) (oN : Orient J N n) (f : M → N) (x : M) : ℤ :=
  orSign (oM.or x) (oN.or (f x)) (mfd I J f x)

theorem signAt_ne_zero_iff (hE : finrank ℝ E = n) (hF : finrank ℝ F = n) (oM : Orient I M n)
    (oN : Orient J N n) (f : M → N) (x : M) :
    signAt oM oN f x ≠ 0 ↔ Function.Bijective (mfd I J f x) :=
  orSign_ne_zero_iff hE hF _ _ _

theorem signAt_mem (hE : finrank ℝ E = n) (hF : finrank ℝ F = n) (oM : Orient I M n)
    (oN : Orient J N n) (f : M → N) (x : M) :
    signAt oM oN f x = 1 ∨ signAt oM oN f x = -1 ∨ signAt oM oN f x = 0 := sgn_mem

/-- At a regular point the sign is `±1`. -/
theorem IsRegularPoint.signAt_ne_zero (hE : finrank ℝ E = n) (hF : finrank ℝ F = n)
    (oM : Orient I M n) (oN : Orient J N n) {f : M → N} {x : M} (hx : IsRegularPoint I J f x) :
    signAt oM oN f x ≠ 0 := by
  rw [signAt_ne_zero_iff hE hF]
  have hsurj : Function.Surjective (mfd I J f x) := hx
  exact ⟨(LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (f := (mfd I J f x : E →ₗ[ℝ] F)) (hE.trans hF.symm)).2 hsurj, hsurj⟩

/-- The sign of a continuous family of linear maps is locally constant where it is nonzero. -/
theorem eventually_orSign_eq_of_continuousAt (hE : finrank ℝ E = n) (hF : finrank ℝ F = n)
    (a : Orientation ℝ E (Fin n)) (b : Orientation ℝ F (Fin n)) {α : Type*} [TopologicalSpace α]
    {L : α → E →L[ℝ] F} {u₀ : α} (hL : ContinuousAt L u₀) (h0 : orSign a b (L u₀) ≠ 0) :
    ∀ᶠ u in 𝓝 u₀, orSign a b (L u) = orSign a b (L u₀) := by
  set e := finBasisOfFinrankEq ℝ E hE
  set f := finBasisOfFinrankEq ℝ F hF
  have hωe : (orEpsB e a • e.det) e ≠ 0 := by
    rw [smul_det_apply_self]; exact orEpsB_ne_zero e a
  have hform : ∀ u, orSign a b (L u) =
      sgn (orEpsB f b * f.det (fun i => L u (e i)) * orEpsB e a) := fun u => by
    rw [orSign_eq_sgn_mul hE _ _ (rayOfNeZero_orEpsB_det e a) (rayOfNeZero_orEpsB_det f b) (L u) hωe]
    simp only [AlternatingMap.compLinearMap_apply, AlternatingMap.smul_apply, smul_eq_mul,
      Basis.det_self, mul_one, ContinuousLinearMap.coe_coe, Function.comp_def]
  simp only [hform]
  have houter : Continuous (fun T : E →L[ℝ] F => f.toMatrix (fun i => T (e i))) := by
    refine continuous_matrix fun i j => ?_
    simp only [Basis.toMatrix_apply]
    exact ((f.coord i).continuous_of_finiteDimensional).comp
      (continuous_id.clm_apply continuous_const)
  have hmat : ContinuousAt (fun u => f.toMatrix (fun i => L u (e i))) u₀ :=
    houter.continuousAt.comp hL
  have hcont : ContinuousAt
      (fun u => orEpsB f b * f.det (fun i => L u (e i)) * orEpsB e a) u₀ := by
    simp only [Basis.det_apply]
    exact (continuousAt_const.mul ((continuous_id.matrix_det).continuousAt.comp hmat)).mul
      continuousAt_const
  have h0' : orEpsB f b * f.det (fun i => L u₀ (e i)) * orEpsB e a ≠ 0 := by
    rw [hform] at h0; exact sgn_ne_zero_iff.1 h0
  rcases lt_or_gt_of_ne h0' with hneg | hpos
  · filter_upwards [hcont.eventually_lt continuousAt_const hneg] with u hu
    rw [sgn_neg hu, sgn_neg hneg]
  · filter_upwards [continuousAt_const.eventually_lt hcont hpos] with u hu
    rw [sgn_pos hu, sgn_pos hpos]

/-- **Local constancy of the sign** near a regular point, for a map smooth on an open
neighbourhood `W` of the point. -/
theorem eventually_signAt_eq_of_contMDiffOn [IsManifold I ∞ M] [IsManifold J ∞ N] [I.Boundaryless]
    [J.Boundaryless] (hE : finrank ℝ E = n) (hF : finrank ℝ F = n) (oM : Orient I M n)
    (oN : Orient J N n) {f : M → N} {W : Set M} (hW : IsOpen W) (hf : ContMDiffOn I J ∞ f W)
    {x₀ : M} (hx₀W : x₀ ∈ W) (hx : IsRegularPoint I J f x₀) :
    ∀ᶠ x in 𝓝 x₀, signAt oM oN f x = signAt oM oN f x₀ := by
  have hfc : ContinuousAt f x₀ := hf.continuousOn.continuousAt (hW.mem_nhds hx₀W)
  -- the map in the charts at `x₀` and `f x₀`
  let g : E → F := fun u => extChartAt J (f x₀) (f ((extChartAt I x₀).symm u))
  let U : Set E := (extChartAt I x₀).target ∩
    (extChartAt I x₀).symm ⁻¹' (W ∩ f ⁻¹' (extChartAt J (f x₀)).source)
  have hWf : IsOpen (W ∩ f ⁻¹' (extChartAt J (f x₀)).source) :=
    hf.continuousOn.isOpen_inter_preimage hW (isOpen_extChartAt_source (f x₀))
  have hU : IsOpen U := (continuousOn_extChartAt_symm x₀).isOpen_inter_preimage
    (isOpen_extChartAt_target x₀) hWf
  have hg : ContDiffOn ℝ ∞ g U := by
    rw [← contMDiffOn_iff_contDiffOn]
    have h1 : ContMDiffOn 𝓘(ℝ, E) I ∞ (extChartAt I x₀).symm U :=
      (contMDiffOn_extChartAt_symm x₀).mono inter_subset_left
    have h3 : ContMDiffOn J 𝓘(ℝ, F) ∞ (extChartAt J (f x₀)) (extChartAt J (f x₀)).source := by
      rw [extChartAt_source]; exact contMDiffOn_extChartAt
    exact h3.comp (hf.comp h1 (fun u hu => hu.2.1)) (fun u hu => hu.2.2)
  have hfd : ContinuousOn (fderiv ℝ g) U := hg.continuousOn_fderiv_of_isOpen hU (by simp)
  have hx₀U : extChartAt I x₀ x₀ ∈ U := by
    refine ⟨(extChartAt I x₀).map_source (mem_extChartAt_source x₀), ?_⟩
    simp only [mem_preimage, mem_inter_iff]
    rw [(extChartAt I x₀).left_inv (mem_extChartAt_source x₀)]
    exact ⟨hx₀W, mem_extChartAt_source (f x₀)⟩
  -- the neighbourhood on which the chain rule identity holds
  have hV : (extChartAt I x₀).source ∩ (W ∩ f ⁻¹' (extChartAt J (f x₀)).source) ∈ 𝓝 x₀ :=
    inter_mem (extChartAt_source_mem_nhds x₀) (hWf.mem_nhds ⟨hx₀W, mem_extChartAt_source (f x₀)⟩)
  have key : ∀ x ∈ (extChartAt I x₀).source ∩ (W ∩ f ⁻¹' (extChartAt J (f x₀)).source),
      (mfd J 𝓘(ℝ, F) (extChartAt J (f x₀)) (f x)).comp (mfd I J f x) =
        (fderiv ℝ g (extChartAt I x₀ x)).comp (mfd I 𝓘(ℝ, E) (extChartAt I x₀) x) := by
    rintro x ⟨hxe, hxW, hxe'⟩
    have hxU : extChartAt I x₀ x ∈ U := by
      refine ⟨(extChartAt I x₀).map_source hxe, ?_⟩
      simp only [mem_preimage, mem_inter_iff]; rw [(extChartAt I x₀).left_inv hxe]; exact ⟨hxW, hxe'⟩
    have hD' := hasMFDerivAt_mfd (I := J) (J := 𝓘(ℝ, F)) ((contMDiffAt_extChartAt' (I := J)
      (n := ∞) (x := f x₀)
      (by rwa [← extChartAt_source J] : f x ∈ (chartAt G (f x₀)).source)).mdifferentiableAt
        (by simp))
    have hdf := hasMFDerivAt_mfd (I := I) (J := J)
      ((hf.contMDiffAt (hW.mem_nhds hxW)).mdifferentiableAt (by simp))
    have hDe := hasMFDerivAt_mfd (I := I) (J := 𝓘(ℝ, E)) ((contMDiffAt_extChartAt' (I := I)
      (n := ∞) (x := x₀)
      (by rwa [← extChartAt_source I] : x ∈ (chartAt H x₀).source)).mdifferentiableAt (by simp))
    have hdg : HasMFDerivAt 𝓘(ℝ, E) 𝓘(ℝ, F) g (extChartAt I x₀ x)
        (fderiv ℝ g (extChartAt I x₀ x)) :=
      ((hg.contDiffAt (hU.mem_nhds hxU)).differentiableAt (by simp)).hasFDerivAt.hasMFDerivAt
    have h1 := hD'.comp x hdf
    have h2 := hdg.comp x hDe
    have h3 : (extChartAt J (f x₀) ∘ f) =ᶠ[𝓝 x] (g ∘ extChartAt I x₀) := by
      filter_upwards [(isOpen_extChartAt_source x₀).mem_nhds hxe] with z hz
      simp only [Function.comp, g]
      rw [(extChartAt I x₀).left_inv hz]
    exact hasMFDerivAt_unique h1 (h2.congr_of_eventuallyEq h3)
  have hcontM := oM.cont x₀
  have hcontN : ∀ᶠ x in 𝓝 x₀, orSign (oN.or (f x)) (oN.or (f x₀))
      (mfd J 𝓘(ℝ, F) (extChartAt J (f x₀)) (f x)) = 1 :=
    hfc.eventually (oN.cont (f x₀))
  have hsign : ∀ᶠ x in 𝓝 x₀, signAt oM oN f x =
      orSign (oM.or x₀) (oN.or (f x₀)) (fderiv ℝ g (extChartAt I x₀ x)) := by
    filter_upwards [hV, hcontM, hcontN] with x hxV hM hN
    have hk := key x hxV
    have h1 := orSign_comp hE hF (oM.or x) (oN.or (f x)) (oN.or (f x₀)) (mfd I J f x)
      (mfd J 𝓘(ℝ, F) (extChartAt J (f x₀)) (f x))
    have h2 := orSign_comp hE hE (oM.or x) (oM.or x₀) (oN.or (f x₀))
      (mfd I 𝓘(ℝ, E) (extChartAt I x₀) x) (fderiv ℝ g (extChartAt I x₀ x))
    rw [hk] at h1
    rw [hN, one_mul] at h1
    rw [hM, mul_one] at h2
    show orSign (oM.or x) (oN.or (f x)) (mfd I J f x) = _
    rw [← h1, h2]
  -- the right-hand side is locally constant
  have h0 : orSign (oM.or x₀) (oN.or (f x₀)) (fderiv ℝ g (extChartAt I x₀ x₀)) ≠ 0 := by
    rw [← hsign.self_of_nhds]
    exact hx.signAt_ne_zero hE hF oM oN
  have hloc := eventually_orSign_eq_of_continuousAt hE hF (oM.or x₀) (oN.or (f x₀))
    (hfd.continuousAt (hU.mem_nhds hx₀U)) h0
  have hloc' := (continuousAt_extChartAt x₀).eventually hloc
  filter_upwards [hsign, hloc'] with x hx1 hx2
  rw [hx1, hx2, ← hsign.self_of_nhds]

/-- **Local constancy of the sign** near a regular point. -/
theorem eventually_signAt_eq [IsManifold I ∞ M] [IsManifold J ∞ N] [I.Boundaryless]
    [J.Boundaryless] (hE : finrank ℝ E = n) (hF : finrank ℝ F = n) (oM : Orient I M n)
    (oN : Orient J N n) {f : M → N} (hf : ContMDiff I J ∞ f) {x₀ : M}
    (hx : IsRegularPoint I J f x₀) :
    ∀ᶠ x in 𝓝 x₀, signAt oM oN f x = signAt oM oN f x₀ :=
  eventually_signAt_eq_of_contMDiffOn hE hF oM oN isOpen_univ hf.contMDiffOn (mem_univ x₀) hx

/-! ### The product `M × ℝ` -/

/-- The orientation of `M × ℝ` induced by an orientation of `M`. -/
def Orient.prodReal [IsManifold I ∞ M] [I.Boundaryless] (hE : finrank ℝ E = n)
    (oM : Orient I M n) : Orient (I.prod 𝓘(ℝ, ℝ)) (M × ℝ) (n + 1) where
  or p := orProd hE (oM.or p.1)
  cont := by
    rintro ⟨x, t⟩
    have h1 : ∀ᶠ y in 𝓝 x, y ∈ (extChartAt I x).source := extChartAt_source_mem_nhds x
    have hf1 : Tendsto (Prod.fst : M × ℝ → M) (𝓝 (x, t)) (𝓝 x) := continuousAt_fst
    have h := hf1.eventually (h1.and (oM.cont x))
    filter_upwards [h] with p hp
    obtain ⟨hpsrc, hpsign⟩ := hp
    have hchart : ⇑(extChartAt (I.prod 𝓘(ℝ, ℝ)) (x, t)) =
        fun q : M × ℝ => (extChartAt I x q.1, q.2) := by
      rw [extChartAt_prod]
      ext q
      · rfl
      · simp [extChartAt_self_apply, chartAt_self_eq]
    have hDe := hasMFDerivAt_mfd (I := I) (J := 𝓘(ℝ, E)) ((contMDiffAt_extChartAt' (I := I)
      (n := ∞) (x := x)
      (by rwa [← extChartAt_source I] : p.1 ∈ (chartAt H x).source)).mdifferentiableAt (by simp))
    have hD0 := (hDe.comp p (hasMFDerivAt_fst (I := I) (I' := 𝓘(ℝ, ℝ)) p)).prodMk
      (hasMFDerivAt_snd (I := I) (I' := 𝓘(ℝ, ℝ)) p)
    have hD1 := hD0.congr_of_eventuallyEq (f₁ := ⇑(extChartAt (I.prod 𝓘(ℝ, ℝ)) (x, t)))
      (Filter.Eventually.of_forall fun q => congrFun hchart q)
    have hD : HasMFDerivAt (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E × ℝ) (extChartAt (I.prod 𝓘(ℝ, ℝ)) (x, t)) p
        ((((mfd I 𝓘(ℝ, E) (extChartAt I x) p.1).comp (ContinuousLinearMap.fst ℝ E ℝ)).prod
          (ContinuousLinearMap.snd ℝ E ℝ) :)) := by
      rw [modelWithCornersSelf_prod]; exact hD1
    rw [HasMFDerivAt.mfd_eq hD]
    rw [orSign_orProd hE hE (oM.or p.1) (oM.or x) _ (mfd I 𝓘(ℝ, E) (extChartAt I x) p.1) 0 1
      (fun v s => by simp)]
    rw [hpsign, sgn_one, mul_one]

/-- The block formula for the sign of a map `M × ℝ → N × ℝ` of the form `(x, t) ↦ (F (x, t), c t)`
near `t = c₀`... stated for a general map with block-triangular derivative. -/
theorem signAt_prodReal [IsManifold I ∞ M] [I.Boundaryless] [IsManifold J ∞ N] [J.Boundaryless]
    (hE : finrank ℝ E = n) (hF : finrank ℝ F = n) (oM : Orient I M n) (oN : Orient J N n)
    {Φ : M × ℝ → N × ℝ} {p : M × ℝ} {A : E →L[ℝ] F} {w : F} {c : ℝ}
    (hΦ : ∀ v t, mfd (I.prod 𝓘(ℝ, ℝ)) (J.prod 𝓘(ℝ, ℝ)) Φ p (v, t) = (A v + t • w, c * t)) :
    signAt (oM.prodReal hE) (oN.prodReal hF) Φ p = orSign (oM.or p.1) (oN.or (Φ p).1) A * sgn c :=
  orSign_orProd hE hF _ _ _ A w c hΦ

end Milnor
