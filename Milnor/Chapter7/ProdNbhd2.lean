import Milnor.Chapter7.ProdNbhd

/-!
# The product neighbourhood theorem, abstract part II (Milnor §7, pp. 46–47)

Continuing `ProdNbhd.lean`: bijectivity of `dG` is an open condition, so bijectivity on
`K × {0}` (`K` compact) gives bijectivity on a tube `K × B_ε`; the image of a tube on which `dG`
is bijective is open; and the inverse of `G` on such a tube (when `G` is injective there) is
smooth.
-/

open Set Filter Topology Function Module Metric
open scoped ContDiff Manifold

noncomputable section

namespace Milnor

namespace PN

variable {n p : ℕ} {EX : Type*} [NormedAddCommGroup EX] [NormedSpace ℝ EX] [FiniteDimensional ℝ EX]
  {HX : Type*} [TopologicalSpace HX] {IX : ModelWithCorners ℝ EX HX} [IX.Boundaryless]
  [CompleteSpace EX]
  {N : Type*} [TopologicalSpace N] [ChartedSpace (EuclideanSpace ℝ (Fin n)) N]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ N] [FirstCountableTopology N]
  {X : Type*} [TopologicalSpace X] [ChartedSpace HX X]
  [IsManifold IX ∞ X] [T2Space X]
  {G : N × EuclideanSpace ℝ (Fin p) → X}
  (hG : ContMDiff (𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin p)))
    IX ∞ G)

/-- The tube `N × B_ε`. -/
def tube (N : Type*) (p : ℕ) (ε : ℝ) : Set (N × EuclideanSpace ℝ (Fin p)) := {q | ‖q.2‖ < ε}

theorem isOpen_tube (ε : ℝ) : IsOpen (tube N p ε) :=
  isOpen_lt (continuous_norm.comp continuous_snd) continuous_const

/-! ### Bijectivity is an open condition on linear maps -/

section linear

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

theorem isUnit_iff_bijective (u : E →L[ℝ] E) : IsUnit u ↔ Bijective u := by
  constructor
  · rintro ⟨v, rfl⟩
    exact (ContinuousLinearEquiv.ofUnit v).bijective
  · intro hu
    exact ⟨(ContinuousLinearEquiv.ofBijective u (LinearMap.ker_eq_bot.2 hu.1)
      (LinearMap.range_eq_top.2 hu.2)).toUnit, rfl⟩

theorem isOpen_bijective_clm : IsOpen {L : E →L[ℝ] F | Bijective L} := by
  by_cases h : ∃ L₀ : E →L[ℝ] F, Bijective L₀
  · obtain ⟨L₀, hL₀⟩ := h
    let L₀e : E ≃L[ℝ] F := ContinuousLinearEquiv.ofBijective L₀ (LinearMap.ker_eq_bot.2 hL₀.1)
      (LinearMap.range_eq_top.2 hL₀.2)
    have hΦ : Continuous fun L : E →L[ℝ] F => (L₀e.symm : F →L[ℝ] E).comp L :=
      continuous_const.clm_comp continuous_id
    have heq : {L : E →L[ℝ] F | Bijective L} =
        (fun L : E →L[ℝ] F => (L₀e.symm : F →L[ℝ] E).comp L) ⁻¹' {u | IsUnit u} := by
      ext L
      simp only [mem_ofPred_eq, mem_preimage, isUnit_iff_bijective, ContinuousLinearMap.coe_comp]
      constructor
      · intro hL
        exact L₀e.symm.bijective.comp hL
      · intro hL
        have : (L : E → F) = (L₀e : E → F) ∘ ((L₀e.symm : F →L[ℝ] E) ∘ L) := by
          funext x; simp
        rw [this]
        exact L₀e.bijective.comp hL
    rw [heq]
    exact Units.isOpen.preimage hΦ
  · push Not at h
    have : {L : E →L[ℝ] F | Bijective L} = ∅ := by
      ext L; simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false]; exact h L
    rw [this]; exact isOpen_empty

end linear

/-! ### Chart independence of bijectivity of the derivative -/

include hG in
/-- The derivative of the chart representative at `extChartAt q₀ q` is `dG q` conjugated by
invertible maps. -/
theorem fderiv_wr_eq {q₀ q : N × EuclideanSpace ℝ (Fin p)}
    (hq : q ∈ (extChartAt (𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin p))) q₀).source)
    (hGq : G q ∈ (extChartAt IX (G q₀)).source) :
    ∃ (A : EX ≃L[ℝ] EX)
      (B : (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin p)) ≃L[ℝ]
        (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin p))),
      fderiv ℝ (wr n IX G q₀)
        (extChartAt (𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin p))) q₀ q) =
      (A : EX →L[ℝ] EX).comp
        ((mfd (𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin p)))
          IX G q).comp
          (B : (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin p)) →L[ℝ]
            (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin p)))) := by
  set I := 𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) with hI
  set c := extChartAt I q₀ q with hc
  have hcq : (extChartAt I q₀).symm c = q := (extChartAt I q₀).left_inv hq
  have hct : c ∈ (extChartAt I q₀).target := (extChartAt I q₀).map_source hq
  -- the outer chart
  have hA0 := isInvertible_mfderiv_extChartAt (I := IX) hGq
  obtain ⟨A, hA⟩ := hA0
  have hAd : HasMFDerivAt IX 𝓘(ℝ, EX) (extChartAt IX (G q₀)) (G ((extChartAt I q₀).symm c))
      ((mfd IX 𝓘(ℝ, EX) (extChartAt IX (G q₀)) (G q) : EX →L[ℝ] EX)) := by
    rw [hcq]
    exact hasMFDerivAt_mfd (mdifferentiableAt_extChartAt (by rw [← extChartAt_source IX]; exact hGq))
  -- the inner chart
  have hB0 := isInvertible_mfderivWithin_extChartAt_symm (I := I) (x := q₀) hct
  rw [I.range_eq_univ, mfderivWithin_univ] at hB0
  obtain ⟨B, hB⟩ := hB0
  have hBd : HasMFDerivAt 𝓘(ℝ, EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin p)) I
      (extChartAt I q₀).symm c
      (mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin p)) I (extChartAt I q₀).symm c) := by
    have := mdifferentiableWithinAt_extChartAt_symm (I := I) (x := q₀) hct
    rw [I.range_eq_univ, mdifferentiableWithinAt_univ] at this
    exact hasMFDerivAt_mfd this
  -- the middle map
  have hGd : HasMFDerivAt I IX G ((extChartAt I q₀).symm c)
      ((mfd I IX G q : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin p) →L[ℝ] EX)) := by
    rw [hcq]; exact hasMFDerivAt_mfd ((hG q).mdifferentiableAt (by simp))
  have hcomp := hAd.comp c (hGd.comp c hBd)
  have hF : HasFDerivAt (wr n IX G q₀) ((mfd IX 𝓘(ℝ, EX) (extChartAt IX (G q₀)) (G q)).comp
      ((mfd I IX G q).comp
        (mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin p)) I (extChartAt I q₀).symm c))) c :=
    hcomp.hasFDerivAt
  refine ⟨A, B, ?_⟩
  rw [hF.fderiv]
  show (mfderiv IX 𝓘(ℝ, EX) (extChartAt IX (G q₀)) (G q)).comp ((mfd I IX G q).comp
    (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin p)) I (extChartAt I q₀).symm c)) = _
  rw [← hA, ← hB]
  rfl

include hG in
/-- Bijectivity of `dG q` can be read off from the chart representative at `q₀`. -/
theorem bijective_mfd_of_fderiv_wr {q₀ q : N × EuclideanSpace ℝ (Fin p)}
    (hq : q ∈ (extChartAt (𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin p))) q₀).source)
    (hGq : G q ∈ (extChartAt IX (G q₀)).source)
    (h : Bijective (fderiv ℝ (wr n IX G q₀)
      (extChartAt (𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin p))) q₀ q))) :
    Bijective (mfd (𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin p)))
      IX G q) := by
  obtain ⟨A, B, hAB⟩ := fderiv_wr_eq hG hq hGq
  rw [hAB] at h
  set L := mfd (𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin p)))
    IX G q with hL
  have : (L : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin p) → EX) =
      (A.symm : EX → EX) ∘
        ((A : EX →L[ℝ] EX).comp
          (L.comp (B : (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin p)) →L[ℝ]
            (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin p))))) ∘
        (B.symm : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin p) →
          EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin p)) := by
    funext x; simp
  rw [this]
  exact (A.symm.bijective.comp h).comp B.symm.bijective

include hG in
/-- Bijectivity of `dG` is an open condition. -/
theorem isOpen_bijective_mfd :
    IsOpen {q : N × EuclideanSpace ℝ (Fin p) | Function.Bijective
      (mfd (𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin p)))
        IX G q)} := by
  set I := 𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) with hI
  rw [isOpen_iff_mem_nhds]
  intro q₀ hq₀
  have hbij : Bijective (mfd I IX G q₀) := hq₀
  have hcont : ContinuousAt (fun q => fderiv ℝ (wr n IX G q₀) (extChartAt I q₀ q)) q₀ := by
    have h1 : ContinuousAt (fderiv ℝ (wr n IX G q₀)) (extChartAt I q₀ q₀) :=
      ((contDiffAt_wr hG q₀).fderiv_right (m := ∞) (by simp)).continuousAt
    show ContinuousAt (fderiv ℝ (wr n IX G q₀) ∘ extChartAt I q₀) q₀
    exact ContinuousAt.comp (g := fderiv ℝ (wr n IX G q₀)) (f := extChartAt I q₀) h1
      (continuousAt_extChartAt q₀)
  have hmem : (fun q => fderiv ℝ (wr n IX G q₀) (extChartAt I q₀ q)) ⁻¹'
      {L : (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin p)) →L[ℝ]
        EX | Bijective L} ∈ 𝓝 q₀ := by
    apply hcont.preimage_mem_nhds
    apply isOpen_bijective_clm.mem_nhds
    show Bijective (fderiv ℝ (wr n IX G q₀) (cpt n q₀))
    rw [(hasFDerivAt_wr hG q₀).fderiv]; exact hbij
  filter_upwards [hmem, extChartAt_source_mem_nhds (I := I) q₀,
    hG.continuous.continuousAt.preimage_mem_nhds (extChartAt_source_mem_nhds (I := IX) (G q₀))]
    with q h1 h2 h3
  exact bijective_mfd_of_fderiv_wr hG h2 h3 h1

include hG in
/-- Bijectivity on `K × {0}`, `K` compact, gives bijectivity on `K × B_ε`. -/
theorem exists_ball_bijective (K : Set N) (hK : IsCompact K)
    (hbij : ∀ x ∈ K, Function.Bijective (mfd (𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod
      𝓘(ℝ, EuclideanSpace ℝ (Fin p))) IX G (x, 0))) :
    ∃ ε > 0, ∀ x ∈ K, ∀ t : EuclideanSpace ℝ (Fin p), ‖t‖ < ε → Function.Bijective
      (mfd (𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin p)))
        IX G (x, t)) := by
  have hsub : K ×ˢ ({0} : Set (EuclideanSpace ℝ (Fin p))) ⊆
      {q : N × EuclideanSpace ℝ (Fin p) | Function.Bijective
        (mfd (𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin p)))
          IX G q)} := by
    rintro ⟨x, t⟩ ⟨hx, ht⟩
    have ht' : t = 0 := ht
    subst ht'
    exact hbij x hx
  obtain ⟨u, v, _, hv, hKu, h0v, huv⟩ :=
    generalized_tube_lemma hK isCompact_singleton (isOpen_bijective_mfd hG) hsub
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hv 0 (h0v rfl)
  refine ⟨ε, hε, fun x hx t ht => huv ⟨hKu hx, hball ?_⟩⟩
  rw [mem_ball_zero_iff]; exact ht

/-! ### The image of a tube is open -/

include hG in
theorem wrInv_chart (q₀ : N × EuclideanSpace ℝ (Fin p))
    (hbij : Bijective (mfd (𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin p)))
      IX G q₀)) :
    wrInv hG q₀ hbij (extChartAt IX (G q₀) (G q₀)) = cpt n q₀ := by
  have := (eventually_wrInv_wr hG q₀ hbij).self_of_nhds
  rwa [wr_cpt] at this

include hG in
/-- Near `G q₀`, the map `L = (extChartAt q₀)⁻¹ ∘ wrInv ∘ extChartAt (G q₀)` is a right inverse of
`G` with values in the tube. -/
theorem eventually_L {ε : ℝ} {q₀ : N × EuclideanSpace ℝ (Fin p)} (hq₀ : q₀ ∈ tube N p ε)
    (hbij : Bijective (mfd (𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin p)))
      IX G q₀)) :
    ∀ᶠ z in 𝓝 (G q₀),
      (extChartAt (𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin p))) q₀).symm
        (wrInv hG q₀ hbij (extChartAt IX (G q₀) z)) ∈ tube N p ε ∧
      G ((extChartAt (𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin p))) q₀).symm
        (wrInv hG q₀ hbij (extChartAt IX (G q₀) z))) = z := by
  set I := 𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) with hI
  set w := wrInv hG q₀ hbij with hw
  have hfix : w (extChartAt IX (G q₀) (G q₀)) = cpt n q₀ := wrInv_chart hG q₀ hbij
  have hL : ContinuousAt (fun z => (extChartAt I q₀).symm (w (extChartAt IX (G q₀) z))) (G q₀) := by
    have h1 : ContinuousAt w (extChartAt IX (G q₀) (G q₀)) := by
      have := (contDiffAt_wrInv hG q₀ hbij).continuousAt
      rwa [wr_cpt] at this
    have h2 : ContinuousAt (extChartAt I q₀).symm (w (extChartAt IX (G q₀) (G q₀))) := by
      rw [hfix]; exact continuousAt_extChartAt_symm q₀
    show ContinuousAt (((extChartAt I q₀).symm ∘ w) ∘ extChartAt IX (G q₀)) (G q₀)
    exact ContinuousAt.comp (g := (extChartAt I q₀).symm ∘ w) (f := extChartAt IX (G q₀))
      (ContinuousAt.comp (g := (extChartAt I q₀).symm) (f := w) h2 h1) (continuousAt_extChartAt (G q₀))
  have hL0 : (extChartAt I q₀).symm (w (extChartAt IX (G q₀) (G q₀))) = q₀ := by
    rw [hfix]; exact (extChartAt I q₀).left_inv (mem_extChartAt_source q₀)
  have hev1 : ∀ᶠ z in 𝓝 (G q₀),
      (extChartAt I q₀).symm (w (extChartAt IX (G q₀) z)) ∈ tube N p ε := by
    apply hL.eventually_mem
    rw [hL0]; exact (isOpen_tube ε).mem_nhds hq₀
  have hev2 : ∀ᶠ z in 𝓝 (G q₀),
      wr n IX G q₀ (w (extChartAt IX (G q₀) z)) = extChartAt IX (G q₀) z := by
    have := eventually_wr_wrInv hG q₀ hbij
    rw [wr_cpt] at this
    exact Filter.Tendsto.eventually (continuousAt_extChartAt (G q₀)) this
  have hev3 : ∀ᶠ z in 𝓝 (G q₀),
      G ((extChartAt I q₀).symm (w (extChartAt IX (G q₀) z))) ∈ (extChartAt IX (G q₀)).source := by
    apply (hG.continuous.continuousAt.comp hL).eventually_mem
    show (extChartAt IX (G q₀)).source ∈ 𝓝 (G ((extChartAt I q₀).symm (w (extChartAt IX (G q₀) (G q₀)))))
    rw [hL0]; exact extChartAt_source_mem_nhds (G q₀)
  filter_upwards [hev1, hev2, hev3, extChartAt_source_mem_nhds (I := IX) (G q₀)] with z h1 h2 h3 h4
  refine ⟨h1, ?_⟩
  have h2' : extChartAt IX (G q₀) (G ((extChartAt I q₀).symm (w (extChartAt IX (G q₀) z)))) =
    extChartAt IX (G q₀) z := h2
  exact (extChartAt IX (G q₀)).injOn h3 h4 h2'

include hG in
/-- The image of a tube on which `dG` is bijective is open. -/
theorem isOpen_image_tube {ε : ℝ}
    (hbij : ∀ q ∈ tube N p ε, Function.Bijective (mfd (𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod
      𝓘(ℝ, EuclideanSpace ℝ (Fin p))) IX G q)) :
    IsOpen (G '' tube N p ε) := by
  rw [isOpen_iff_mem_nhds]
  rintro z ⟨q₀, hq₀, rfl⟩
  filter_upwards [eventually_L hG hq₀ (hbij q₀ hq₀)] with z' hz'
  exact ⟨_, hz'.1, hz'.2⟩

/-! ### The inverse on the tube -/

/-- The inverse of `G` on the tube (junk outside its image). -/
def Ginv [Nonempty N] (G : N × EuclideanSpace ℝ (Fin p) → X) (ε : ℝ) : X → N × EuclideanSpace ℝ (Fin p) :=
  Function.invFunOn G (tube N p ε)

theorem Ginv_G [Nonempty N] {ε : ℝ} (hinj : Set.InjOn G (tube N p ε)) {q} (hq : q ∈ tube N p ε) :
    Ginv G ε (G q) = q :=
  hinj.leftInvOn_invFunOn hq

theorem G_Ginv [Nonempty N] {ε : ℝ} {z : X} (hz : z ∈ G '' tube N p ε) : G (Ginv G ε z) = z :=
  Function.invFunOn_eq hz

theorem Ginv_mem [Nonempty N] {ε : ℝ} {z : X} (hz : z ∈ G '' tube N p ε) : Ginv G ε z ∈ tube N p ε :=
  Function.invFunOn_mem hz

include hG in
/-- The inverse is smooth on the image of the tube. -/
theorem contMDiffAt_Ginv [Nonempty N] {ε : ℝ}
    (hbij : ∀ q ∈ tube N p ε, Function.Bijective (mfd (𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod
      𝓘(ℝ, EuclideanSpace ℝ (Fin p))) IX G q))
    (hinj : Set.InjOn G (tube N p ε)) {z : X} (hz : z ∈ G '' tube N p ε) :
    ContMDiffAt IX
      (𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin p))) ∞ (Ginv G ε) z := by
  set I := 𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) with hI
  obtain ⟨q₀, hq₀, rfl⟩ := hz
  have hb := hbij q₀ hq₀
  set w := wrInv hG q₀ hb with hw
  have hfix : w (extChartAt IX (G q₀) (G q₀)) = cpt n q₀ := wrInv_chart hG q₀ hb
  have h1 : ContMDiffAt IX 𝓘(ℝ, EX) ∞ (extChartAt IX (G q₀)) (G q₀) :=
    contMDiffAt_extChartAt
  have h2 : ContMDiffAt 𝓘(ℝ, EX)
      𝓘(ℝ, EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin p)) ∞ w (extChartAt IX (G q₀) (G q₀)) := by
    rw [contMDiffAt_iff_contDiffAt]
    have := contDiffAt_wrInv hG q₀ hb
    rwa [wr_cpt] at this
  have h3 : ContMDiffAt 𝓘(ℝ, EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin p)) I ∞
      (extChartAt I q₀).symm (w (extChartAt IX (G q₀) (G q₀))) := by
    rw [hfix]
    exact (contMDiffOn_extChartAt_symm q₀).contMDiffAt (extChartAt_target_mem_nhds q₀)
  have hL : ContMDiffAt IX I ∞
      ((extChartAt I q₀).symm ∘ (w ∘ extChartAt IX (G q₀))) (G q₀) :=
    h3.comp (G q₀) (h2.comp (G q₀) h1)
  refine hL.congr_of_eventuallyEq ?_
  filter_upwards [eventually_L hG hq₀ hb] with z hz
  have := Ginv_G hinj hz.1
  rw [hz.2] at this
  exact this

end PN

end Milnor

