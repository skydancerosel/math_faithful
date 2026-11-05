import Milnor.Chapter6.SignLemmas

/-!
# The induced orientation of a level set in an oriented manifold

Generalization of `Milnor.levelOrient` from a vector space to a manifold `M` with charts in `E`
(so open subsets of `E` are included): for `g : M → ℝ` smooth with `0` a regular value and `M`
oriented, the level set `g⁻¹(0)` is oriented by "outward vector first".
-/

open Set Module Filter Topology Function
open scoped ContDiff Manifold

noncomputable section

namespace Milnor

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z] {n : ℕ}

/-- If the sign is `1`, the pullback of a representative is a positive multiple. -/
theorem exists_pos_smul_of_orSign_eq_one {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F] {m : ℕ} (hE : finrank ℝ E = m) {a : Orientation ℝ E (Fin m)}
    {b : Orientation ℝ F (Fin m)} {T : E →L[ℝ] F} {om : E [⋀^Fin m]→ₗ[ℝ] ℝ}
    {η : F [⋀^Fin m]→ₗ[ℝ] ℝ} (hom : om ≠ 0) (hη : η ≠ 0) (ha : rayOfNeZero ℝ om hom = a)
    (hb : rayOfNeZero ℝ η hη = b) (h : orSign a b T = 1) :
    ∃ κ : ℝ, 0 < κ ∧ η.compLinearMap T.toLinearMap = κ • om := by
  obtain ⟨c, hc⟩ := exists_eq_smul_of_finrank hE hom (η.compLinearMap T.toLinearMap)
  refine ⟨c, ?_, hc⟩
  rw [orSign_eq_sgn _ _ ha hb hc] at h
  rcases lt_trichotomy c 0 with hlt | heq | hgt
  · rw [sgn_neg hlt] at h; exact absurd h (by decide)
  · rw [heq, sgn_zero] at h; exact absurd h (by decide)
  · exact hgt

theorem contractForm_pullback (om : E [⋀^Fin (n + 1)]→ₗ[ℝ] ℝ) (L : E →L[ℝ] E) (v : E)
    (T : Z →L[ℝ] E) :
    contractForm (om.compLinearMap L.toLinearMap) v T = contractForm om (L v) (L.comp T) := by
  ext u
  simp only [contractForm_apply, AlternatingMap.compLinearMap_apply]
  congr 1
  funext i
  refine Fin.cases ?_ (fun i => ?_) i <;> simp

/-- The outward vector `-∑ᵢ dg(eᵢ) eᵢ`, for the derivative in the chart at `x`. -/
def outwardM (hE : finrank ℝ E = n + 1) (g : M → ℝ) (x : M) : E :=
  -∑ i, mfd 𝓘(ℝ, E) 𝓘(ℝ, ℝ) g x (finBasisOfFinrankEq ℝ E hE i) • finBasisOfFinrankEq ℝ E hE i

theorem mfd_outwardM (hE : finrank ℝ E = n + 1) (g : M → ℝ) (x : M) :
    mfd 𝓘(ℝ, E) 𝓘(ℝ, ℝ) g x (outwardM hE g x) =
      -∑ i, mfd 𝓘(ℝ, E) 𝓘(ℝ, ℝ) g x (finBasisOfFinrankEq ℝ E hE i) ^ 2 := by
  simp only [outwardM, map_neg, map_sum, map_smul, smul_eq_mul, sq]

theorem lin_outward_neg (hE : finrank ℝ E = n + 1) {l : E →L[ℝ] ℝ} (hl : l ≠ 0) :
    l (-∑ i, l (finBasisOfFinrankEq ℝ E hE i) • finBasisOfFinrankEq ℝ E hE i) < 0 := by
  simp only [map_neg, map_sum, map_smul, smul_eq_mul, neg_lt_zero]
  set e := finBasisOfFinrankEq ℝ E hE
  have hne : ∃ i, l (e i) ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    refine hl (ContinuousLinearMap.coe_injective (e.ext fun i => ?_))
    simp [hcon i]
  obtain ⟨i, hi⟩ := hne
  exact Finset.sum_pos' (fun j _ => mul_self_nonneg _) ⟨i, Finset.mem_univ _, mul_self_pos.2 hi⟩

theorem mfd_outwardM_neg (hE : finrank ℝ E = n + 1) {g : M → ℝ} {x : M}
    (hx : mfd 𝓘(ℝ, E) 𝓘(ℝ, ℝ) g x ≠ 0) :
    mfd 𝓘(ℝ, E) 𝓘(ℝ, ℝ) g x (outwardM hE g x) < 0 :=
  lin_outward_neg hE hx

section level

variable (hE : finrank ℝ E = n + 1) (hZ : finrank ℝ Z = n) (oM : Orient 𝓘(ℝ, E) M (n + 1))
  {g : M → ℝ} (hg : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g) (h0 : IsRegularValue 𝓘(ℝ, E) 𝓘(ℝ, ℝ) g 0)


include hE hZ hg h0 in
/-- The derivative of `g` is nonzero on the level set. -/
theorem mfd_ne_zero_of_level (q : g ⁻¹' {0}) : mfd 𝓘(ℝ, E) 𝓘(ℝ, ℝ) g q.1 ≠ 0 := fun hz => by
  have hs : Function.Surjective (mfd 𝓘(ℝ, E) 𝓘(ℝ, ℝ) g q.1) := h0 q.1 q.2
  obtain ⟨v, hv⟩ := hs 1
  rw [hz] at hv
  simp at hv

include hE hZ hg h0 in
theorem mfd_level_comp_val (q : g ⁻¹' {0}) (w : Z) :
    letI := (isSliceSubmanifold_preimage (Z := Z) (finrank_Z_add hE hZ) hg h0).chartedSpace
    mfd 𝓘(ℝ, E) 𝓘(ℝ, ℝ) g q.1 (mfd 𝓘(ℝ, Z) 𝓘(ℝ, E) (Subtype.val : g ⁻¹' {0} → M) q w) = 0 :=
  (mem_range_mfderiv_val_iff (finrank_Z_add hE hZ) hg h0 q _).1 ⟨w, rfl⟩

include hE hZ hg h0 in
/-- A representative of the level-set orientation is nonzero on a basis of `Z`. -/
theorem levelOrientM_rep_ne_zero (q : g ⁻¹' {0}) {om : E [⋀^Fin (n + 1)]→ₗ[ℝ] ℝ} (hom : om ≠ 0) :
    letI := (isSliceSubmanifold_preimage (Z := Z) (finrank_Z_add hE hZ) hg h0).chartedSpace
    contractForm om (outwardM hE g q.1) (mfd 𝓘(ℝ, Z) 𝓘(ℝ, E) (Subtype.val : g ⁻¹' {0} → M) q)
      (finBasisOfFinrankEq ℝ Z hZ) ≠ 0 := by
  have hS := isSliceSubmanifold_preimage (Z := Z) (finrank_Z_add hE hZ) hg h0
  letI := hS.chartedSpace
  exact contractForm_basis_ne_zero hE hZ hom (injective_mfderiv_val hS q)
    (mfd_level_comp_val hE hZ hg h0 q) (mfd_outwardM_neg hE (mfd_ne_zero_of_level hE hZ hg h0 q)).ne _

include hE hZ hg h0 in
theorem levelOrientM_rep_ne_zero' (q : g ⁻¹' {0}) {om : E [⋀^Fin (n + 1)]→ₗ[ℝ] ℝ} (hom : om ≠ 0) :
    letI := (isSliceSubmanifold_preimage (Z := Z) (finrank_Z_add hE hZ) hg h0).chartedSpace
    contractForm om (outwardM hE g q.1) (mfd 𝓘(ℝ, Z) 𝓘(ℝ, E) (Subtype.val : g ⁻¹' {0} → M) q) ≠ 0 :=
  fun h => levelOrientM_rep_ne_zero hE hZ hg h0 q hom (by rw [h]; rfl)

include hE hZ hg h0 in
/-- **Continuity of the level-set orientation in an oriented manifold.** -/
theorem levelOrientM_cont :
    letI hS := isSliceSubmanifold_preimage (Z := Z) (finrank_Z_add hE hZ) hg h0
    letI := hS.chartedSpace
    ∀ q₀ : g ⁻¹' {0}, ∀ᶠ q in 𝓝 q₀,
      orSign (contractOr hZ (oM.or q.1) (outwardM hE g q.1)
          (mfd 𝓘(ℝ, Z) 𝓘(ℝ, E) (Subtype.val : g ⁻¹' {0} → M) q))
        (contractOr hZ (oM.or q₀.1) (outwardM hE g q₀.1)
          (mfd 𝓘(ℝ, Z) 𝓘(ℝ, E) (Subtype.val : g ⁻¹' {0} → M) q₀))
        (mfd 𝓘(ℝ, Z) 𝓘(ℝ, Z) (extChartAt 𝓘(ℝ, Z) q₀) q) = 1 := by
  have hS := isSliceSubmanifold_preimage (Z := Z) (finrank_Z_add hE hZ) hg h0
  letI := hS.chartedSpace
  haveI := hS.isManifold
  intro q₀
  -- basic facts at every point `q` of the level set
  have hreg : ∀ q : g ⁻¹' {0}, mfd 𝓘(ℝ, E) 𝓘(ℝ, ℝ) g q.1 ≠ 0 := fun q hz => by
    have hs : Function.Surjective (mfd 𝓘(ℝ, E) 𝓘(ℝ, ℝ) g q.1) := h0 q.1 q.2
    obtain ⟨v, hv⟩ := hs 1
    rw [hz] at hv
    simp at hv
  set T : ∀ q : g ⁻¹' {0}, Z →L[ℝ] E :=
    fun q => mfd 𝓘(ℝ, Z) 𝓘(ℝ, E) (Subtype.val : g ⁻¹' {0} → M) q with hT
  have hker : ∀ (q : g ⁻¹' {0}) (v : E), (∃ w, T q w = v) ↔ mfd 𝓘(ℝ, E) 𝓘(ℝ, ℝ) g q.1 v = 0 :=
    fun q v => mem_range_mfderiv_val_iff (finrank_Z_add hE hZ) hg h0 q v
  have hdgι : ∀ (q : g ⁻¹' {0}) (w : Z), mfd 𝓘(ℝ, E) 𝓘(ℝ, ℝ) g q.1 (T q w) = 0 :=
    fun q w => (hker q _).1 ⟨w, rfl⟩
  have hιinj : ∀ q : g ⁻¹' {0}, Function.Injective (T q) := by
    intro q
    have hrange : LinearMap.range (T q : Z →ₗ[ℝ] E) =
        LinearMap.ker (mfd 𝓘(ℝ, E) 𝓘(ℝ, ℝ) g q.1 : E →ₗ[ℝ] ℝ) := by
      ext v
      simp only [LinearMap.mem_range, LinearMap.mem_ker, ContinuousLinearMap.coe_coe]
      exact hker q v
    have h1 := LinearMap.finrank_range_add_finrank_ker (T q : Z →ₗ[ℝ] E)
    have h2 := LinearMap.finrank_range_add_finrank_ker
      (mfd 𝓘(ℝ, E) 𝓘(ℝ, ℝ) g q.1 : E →ₗ[ℝ] ℝ)
    have h3 : LinearMap.range (mfd 𝓘(ℝ, E) 𝓘(ℝ, ℝ) g q.1 : E →ₗ[ℝ] ℝ) = ⊤ := by
      rw [LinearMap.range_eq_top]
      have hex : ∃ v, mfd 𝓘(ℝ, E) 𝓘(ℝ, ℝ) g q.1 v ≠ 0 := by
        by_contra hcon
        push_neg at hcon
        exact hreg q (ContinuousLinearMap.ext hcon)
      obtain ⟨v, hv⟩ := hex
      intro t
      exact ⟨(t / mfd 𝓘(ℝ, E) 𝓘(ℝ, ℝ) g q.1 v) • v, by simp [div_mul_cancel₀ _ hv]⟩
    rw [h3, finrank_top, Module.finrank_self, hE] at h2
    rw [hrange, hZ] at h1
    have h4 : finrank ℝ (LinearMap.ker (T q : Z →ₗ[ℝ] E)) = 0 := by omega
    rw [Submodule.finrank_eq_zero] at h4
    exact LinearMap.ker_eq_bot.1 h4
  set u₀ := finBasisOfFinrankEq ℝ Z hZ with hu₀
  -- the representative of the orientation at `q`
  have hrep : ∀ q : g ⁻¹' {0},
      contractForm (oM.or q.1).someVector (outwardM hE g q.1) (T q) u₀ ≠ 0 := fun q =>
    contractForm_basis_ne_zero hE hZ (oM.or q.1).someVector_ne_zero (hιinj q) (hdgι q)
      (mfd_outwardM_neg hE (hreg q)).ne u₀
  have hrep' : ∀ q : g ⁻¹' {0},
      contractForm (oM.or q.1).someVector (outwardM hE g q.1) (T q) ≠ 0 :=
    fun q h => hrep q (by rw [h]; rfl)
  -- charts: `e` of `M` at `q₀.1`, `c₀` of the level set at `q₀`
  set e := extChartAt 𝓘(ℝ, E) q₀.1 with he
  set c₀ := extChartAt 𝓘(ℝ, Z) q₀ with hc₀
  set eb := finBasisOfFinrankEq ℝ E hE with heb
  set om₀ : E [⋀^Fin (n + 1)]→ₗ[ℝ] ℝ := orEpsB eb (oM.or q₀.1) • eb.det with hom₀def
  have hom₀ : om₀ ≠ 0 := orEpsB_smul_det_ne_zero eb (oM.or q₀.1)
  have hom₀ray : rayOfNeZero ℝ om₀ hom₀ = oM.or q₀.1 := rayOfNeZero_orEpsB_det eb (oM.or q₀.1)
  -- `ĝ = g ∘ e⁻¹` on `E`, and the outward vector in the chart
  set ĝ : E → ℝ := fun u => g (e.symm u) with hĝ
  have hĝs : ContDiffOn ℝ ∞ ĝ e.target := by
    rw [← contMDiffOn_iff_contDiffOn]
    exact hg.comp_contMDiffOn (contMDiffOn_extChartAt_symm q₀.1)
  have hĝd : ContinuousOn (fderiv ℝ ĝ) e.target :=
    hĝs.continuousOn_fderiv_of_isOpen (isOpen_extChartAt_target q₀.1) (by simp)
  set nq : g ⁻¹' {0} → E := fun q =>
    -∑ i, fderiv ℝ ĝ (e q.1) (finBasisOfFinrankEq ℝ E hE i) • finBasisOfFinrankEq ℝ E hE i with hnq
  -- `ψ = e ∘ val ∘ c₀⁻¹ : Z → E`
  set ψ : Z → E := fun z => e (c₀.symm z).1 with hψ_def
  set V₀ : Set Z := c₀.target ∩ c₀.symm ⁻¹' (Subtype.val ⁻¹' e.source) with hV₀
  have hV₀o : IsOpen V₀ := (continuousOn_extChartAt_symm q₀).isOpen_inter_preimage
    (isOpen_extChartAt_target q₀) ((isOpen_extChartAt_source q₀.1).preimage continuous_subtype_val)
  have hψ : ContDiffOn ℝ ∞ ψ V₀ := by
    rw [← contMDiffOn_iff_contDiffOn]
    have h1 : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ e e.source := by
      rw [extChartAt_source]; exact contMDiffOn_extChartAt
    exact h1.comp ((hS.contMDiff_val.comp_contMDiffOn (contMDiffOn_extChartAt_symm q₀)).mono
      inter_subset_left) (fun z hz => hz.2)
  have hψd : ContinuousOn (fderiv ℝ ψ) V₀ := hψ.continuousOn_fderiv_of_isOpen hV₀o (by simp)
  -- the good neighbourhood of `q₀`: chart sources
  set W : Set (g ⁻¹' {0}) := c₀.source ∩ Subtype.val ⁻¹' e.source with hW
  have hWo : IsOpen W :=
    (isOpen_extChartAt_source q₀).inter ((isOpen_extChartAt_source q₀.1).preimage continuous_subtype_val)
  have hq₀W : q₀ ∈ W := ⟨mem_extChartAt_source q₀, mem_extChartAt_source q₀.1⟩
  have hWV : ∀ q ∈ W, c₀ q ∈ V₀ := fun q hq =>
    ⟨c₀.map_source hq.1, by simp only [mem_preimage]; rw [c₀.left_inv hq.1]; exact hq.2⟩
  -- chain rules at `q ∈ W`
  set De : g ⁻¹' {0} → (E →L[ℝ] E) := fun q => mfd 𝓘(ℝ, E) 𝓘(ℝ, E) e q.1 with hDe
  set D : g ⁻¹' {0} → (Z →L[ℝ] Z) := fun q => mfd 𝓘(ℝ, Z) 𝓘(ℝ, Z) c₀ q with hD
  have hDeq : ∀ q ∈ W, HasMFDerivAt 𝓘(ℝ, E) 𝓘(ℝ, E) e q.1 (De q :) := fun q hq =>
    hasMFDerivAt_mfd ((contMDiffAt_extChartAt' (I := 𝓘(ℝ, E)) (n := ∞) (x := q₀.1)
      (by rw [← extChartAt_source 𝓘(ℝ, E)]; exact hq.2)).mdifferentiableAt
        (by simp))
  have hDq : ∀ q ∈ W, HasMFDerivAt 𝓘(ℝ, Z) 𝓘(ℝ, Z) c₀ q (D q :) := fun q hq =>
    hasMFDerivAt_mfd ((contMDiffAt_extChartAt' (I := 𝓘(ℝ, Z)) (n := ∞) (x := q₀)
      (by rw [← extChartAt_source 𝓘(ℝ, Z)]; exact hq.1)).mdifferentiableAt
        (by simp))
  have hTq : ∀ q, HasMFDerivAt 𝓘(ℝ, Z) 𝓘(ℝ, E) (Subtype.val : g ⁻¹' {0} → M) q (T q :) := fun q =>
    hasMFDerivAt_mfd (hS.contMDiff_val.mdifferentiableAt (by simp))
  have hchain : ∀ q ∈ W, (De q).comp (T q) = (fderiv ℝ ψ (c₀ q)).comp (D q) := by
    intro q hq
    have h1 := (hDeq q hq).comp q (hTq q)
    have hψq : HasMFDerivAt 𝓘(ℝ, Z) 𝓘(ℝ, E) ψ (c₀ q) (fderiv ℝ ψ (c₀ q)) :=
      ((hψ.contDiffAt (hV₀o.mem_nhds (hWV q hq))).differentiableAt (by simp)).hasFDerivAt.hasMFDerivAt
    have h2 := hψq.comp q (hDq q hq)
    have h3 : (e ∘ (Subtype.val : g ⁻¹' {0} → M)) =ᶠ[𝓝 q] (ψ ∘ c₀) := by
      filter_upwards [(isOpen_extChartAt_source q₀).mem_nhds hq.1] with z hz
      simp only [Function.comp, ψ]
      rw [c₀.left_inv hz]
    exact hasMFDerivAt_unique h1 (h2.congr_of_eventuallyEq h3)
  -- `mfd g = dĝ ∘ De` on `W`
  have hgchain : ∀ q ∈ W, mfd 𝓘(ℝ, E) 𝓘(ℝ, ℝ) g q.1 = (fderiv ℝ ĝ (e q.1)).comp (De q) := by
    intro q hq
    have hĝq : HasMFDerivAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ĝ (e q.1) (fderiv ℝ ĝ (e q.1)) :=
      ((hĝs.contDiffAt ((isOpen_extChartAt_target q₀.1).mem_nhds
        (e.map_source hq.2))).differentiableAt (by simp)).hasFDerivAt.hasMFDerivAt
    have h2 := hĝq.comp q.1 (hDeq q hq)
    have h3 : g =ᶠ[𝓝 q.1] (ĝ ∘ e) := by
      filter_upwards [(isOpen_extChartAt_source q₀.1).mem_nhds hq.2] with z hz
      simp only [Function.comp, ĝ]
      rw [e.left_inv hz]
    exact HasMFDerivAt.mfd_eq (h2.congr_of_eventuallyEq h3)
  -- `De` is invertible on `W`
  have hDeinv : ∀ q ∈ W, Function.Bijective (De q) := by
    intro q hq
    have hloc : IsLocalDiffeomorphAt 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ e q.1 :=
      ⟨PartialDiffeomorph.ofExtChartAt 𝓘(ℝ, E) q₀.1, hq.2, fun _ _ => rfl⟩
    have := hloc.mfderivToContinuousLinearEquiv_coe (by simp : (∞ : WithTop ℕ∞) ≠ 0)
    show Function.Bijective (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) e q.1)
    rw [← this]
    exact (hloc.mfderivToContinuousLinearEquiv (by simp)).bijective
  -- the forms `Λ q = contractForm om₀ (n q) (dψ (c₀ q))`
  set Λ : g ⁻¹' {0} → (Z [⋀^Fin n]→ₗ[ℝ] ℝ) := fun q =>
    contractForm om₀ (nq q) (fderiv ℝ ψ (c₀ q)) with hΛ
  -- key identity: the representative at `q ∈ W` is a positive multiple of `Λ q ∘ D q`
  have hkey : ∀ q ∈ W, orSign (oM.or q.1) (oM.or q₀.1) (De q) = 1 →
      ∃ a : ℝ, 0 < a ∧ contractForm (oM.or q.1).someVector (outwardM hE g q.1) (T q) =
        a • (Λ q).compLinearMap (D q).toLinearMap := by
    intro q hq hsign
    obtain ⟨κ, hκ, hκeq⟩ := exists_pos_smul_of_orSign_eq_one hE (oM.or q.1).someVector_ne_zero
      hom₀ (someVector_ray' _) hom₀ray hsign
    -- `om_q = κ⁻¹ • om₀ ∘ De`
    have h1 : (oM.or q.1).someVector = κ⁻¹ • om₀.compLinearMap (De q).toLinearMap := by
      rw [hκeq, smul_smul, inv_mul_cancel₀ hκ.ne', one_smul]
    rw [h1, contractForm_smul, contractForm_pullback]
    -- outward independence: `De (outward) = a' • n q + (De ∘ T) t`
    set l := fderiv ℝ ĝ (e q.1) with hl
    have hl0 : l ≠ 0 := by
      intro h
      apply hreg q
      have : l.comp (De q) = 0 := by rw [h]; rfl
      rw [hgchain q hq]; exact this
    have hln : l (nq q) < 0 := lin_outward_neg hE hl0
    have hlo : l (De q (outwardM hE g q.1)) < 0 := by
      have := mfd_outwardM_neg hE (hreg q)
      rwa [hgchain q hq] at this
    have hrange : LinearMap.range ((De q).comp (T q) : Z →ₗ[ℝ] E) = LinearMap.ker (l : E →ₗ[ℝ] ℝ) := by
      apply Submodule.eq_of_le_of_finrank_eq
      · rintro _ ⟨w, rfl⟩
        simp only [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, ContinuousLinearMap.comp_apply]
        have := hdgι q w
        rw [hgchain q hq] at this
        exact this
      · have h1 := LinearMap.finrank_range_add_finrank_ker ((De q).comp (T q) : Z →ₗ[ℝ] E)
        have hinj : Function.Injective ((De q).comp (T q)) := (hDeinv q hq).1.comp (hιinj q)
        rw [LinearMap.ker_eq_bot.2 hinj, finrank_bot, add_zero, hZ] at h1
        have h2 := LinearMap.finrank_range_add_finrank_ker (l : E →ₗ[ℝ] ℝ)
        have h3 : LinearMap.range (l : E →ₗ[ℝ] ℝ) = ⊤ := by
          rw [LinearMap.range_eq_top]
          intro t
          refine ⟨(t / l (nq q)) • nq q, ?_⟩
          simp [div_mul_cancel₀ _ hln.ne]
        rw [h3, finrank_top, Module.finrank_self, hE] at h2
        omega
    have hmem : De q (outwardM hE g q.1) - (l (De q (outwardM hE g q.1)) / l (nq q)) • nq q ∈
        LinearMap.range ((De q).comp (T q) : Z →ₗ[ℝ] E) := by
      rw [hrange, LinearMap.mem_ker]
      simp [div_mul_cancel₀ _ hln.ne]
    obtain ⟨t, ht⟩ := hmem
    have hdecomp : De q (outwardM hE g q.1) =
        (l (De q (outwardM hE g q.1)) / l (nq q)) • nq q + ((De q).comp (T q)) t := by
      rw [show ((De q).comp (T q)) t = _ from ht]; abel
    rw [contractForm_eq_smul hZ om₀ hdecomp, smul_smul, hchain q hq, ← contractForm_comp]
    refine ⟨κ⁻¹ * (l (De q (outwardM hE g q.1)) / l (nq q)), ?_, rfl⟩
    exact mul_pos (inv_pos.2 hκ) (div_pos_of_neg_of_neg hlo hln)
  -- at `q₀` the chart derivatives are the identity
  have hD₀ : D q₀ = ContinuousLinearMap.id ℝ Z := mfd_extChartAt_self q₀
  have hDe₀ : De q₀ = ContinuousLinearMap.id ℝ E := mfd_extChartAt_self q₀.1
  have hsign₀ : orSign (oM.or q₀.1) (oM.or q₀.1) (De q₀) = 1 := by
    rw [hDe₀]; exact orSign_id _
  obtain ⟨a₀, ha₀, hrep₀⟩ := hkey q₀ hq₀W hsign₀
  have hΛ₀u : Λ q₀ u₀ ≠ 0 := by
    intro h
    apply hrep q₀
    rw [hrep₀, hD₀]
    simp only [AlternatingMap.smul_apply, ContinuousLinearMap.coe_id,
      AlternatingMap.compLinearMap_id, smul_eq_mul, h, mul_zero]
  have hΛ₀ne : Λ q₀ ≠ 0 := fun h => hΛ₀u (by rw [h]; rfl)
  -- continuity of `q ↦ Λ q u₀` on `W`
  have hLcont : ContinuousOn (fun q : g ⁻¹' {0} => Λ q u₀) W := by
    have hfdĝ : ContinuousOn (fun q : g ⁻¹' {0} => fderiv ℝ ĝ (e q.1)) W :=
      hĝd.comp ((continuousOn_extChartAt q₀.1).comp continuous_subtype_val.continuousOn
        (fun q hq => hq.2)) (fun q hq => e.map_source hq.2)
    have hn : ContinuousOn nq W := by
      simp only [nq]
      exact (continuousOn_finsetSum _ fun i _ =>
        (hfdĝ.clm_apply continuousOn_const).smul continuousOn_const).neg
    have hfd : ContinuousOn (fun q : g ⁻¹' {0} => fderiv ℝ ψ (c₀ q)) W :=
      hψd.comp ((continuousOn_extChartAt q₀).mono inter_subset_left) hWV
    simp only [Λ, contractForm_apply, om₀, AlternatingMap.smul_apply, smul_eq_mul, Basis.det_apply]
    have houter : Continuous (fun w : Fin (n + 1) → E => eb.toMatrix w) := by
      refine continuous_matrix fun i j => ?_
      simp only [Basis.toMatrix_apply]
      exact ((eb.coord i).continuous_of_finiteDimensional).comp (continuous_apply j)
    have hinner : ContinuousOn (fun q : g ⁻¹' {0} =>
        Matrix.vecCons (nq q) (fun i => fderiv ℝ ψ (c₀ q) (u₀ i))) W := by
      rw [continuousOn_pi]; intro j
      refine Fin.cases ?_ (fun j => ?_) j
      · simp only [Matrix.cons_val_zero]
        exact hn
      · simp only [Matrix.cons_val_succ]
        exact hfd.clm_apply continuousOn_const
    exact continuousOn_const.mul
      ((continuous_id.matrix_det).comp_continuousOn (houter.comp_continuousOn hinner))
  -- proportionality: `Λ q = κ q • Λ q₀`
  have hprop : ∀ q, Λ q = (Λ q u₀ / Λ q₀ u₀) • Λ q₀ := by
    intro q
    obtain ⟨c, hc⟩ := exists_eq_smul_of_finrank hZ hΛ₀ne (Λ q)
    have hcu : Λ q u₀ = c * Λ q₀ u₀ := by rw [hc]; rfl
    rw [hcu, mul_div_cancel_right₀ _ hΛ₀u, hc]
  -- eventually `Λ q u₀` has the sign of `Λ q₀ u₀`
  have hev : ∀ᶠ q in 𝓝 q₀, 0 < Λ q u₀ / Λ q₀ u₀ := by
    have hc := hLcont.continuousAt (hWo.mem_nhds hq₀W)
    rcases lt_or_gt_of_ne hΛ₀u with hneg | hpos
    · filter_upwards [hc.eventually_lt continuousAt_const hneg] with q hq
      exact div_pos_of_neg_of_neg hq hneg
    · filter_upwards [continuousAt_const.eventually_lt hc hpos] with q hq
      exact div_pos hq hpos
  -- eventually the ambient chart derivative has sign `1`
  have hsev : ∀ᶠ q in 𝓝 q₀, orSign (oM.or q.1) (oM.or q₀.1) (De q) = 1 :=
    (continuous_subtype_val.continuousAt (x := q₀)).tendsto.eventually (oM.cont q₀.1)
  filter_upwards [hWo.mem_nhds hq₀W, hev, hsev] with q hq hκ hsq
  obtain ⟨a, ha, hrepq⟩ := hkey q hq hsq
  -- the derivative of the chart at `q` is invertible
  have hloc : IsLocalDiffeomorphAt 𝓘(ℝ, Z) 𝓘(ℝ, Z) ∞ c₀ q :=
    ⟨PartialDiffeomorph.ofExtChartAt 𝓘(ℝ, Z) q₀, hq.1, fun _ _ => rfl⟩
  obtain ⟨D', hD'⟩ : ∃ D' : Z ≃L[ℝ] Z, (D' : Z →L[ℝ] Z) = D q :=
    ⟨hloc.mfderivToContinuousLinearEquiv (by simp), hloc.mfderivToContinuousLinearEquiv_coe (by simp)⟩
  have hDu : (fun i => D q (D'.symm (u₀ i))) = u₀ := by
    funext i; rw [← hD', ContinuousLinearEquiv.coe_coe, D'.apply_symm_apply]
  -- rewrite the two orientations as rays of the representatives
  rw [← rayOfNeZero_contractForm hZ (oM.or q.1).someVector_ne_zero (someVector_ray' _) _ _ (hrep' q),
    ← rayOfNeZero_contractForm hZ (oM.or q₀.1).someVector_ne_zero (someVector_ray' _) _ _ (hrep' q₀)]
  -- evaluate on the tuple `z̄ = D⁻¹ u₀`
  have e1 : contractForm (oM.or q.1).someVector (outwardM hE g q.1) (T q)
      (fun i => D'.symm (u₀ i)) = a * ((Λ q u₀ / Λ q₀ u₀) * Λ q₀ u₀) := by
    rw [hrepq]
    show a * Λ q (fun i => D q (D'.symm (u₀ i))) = _
    rw [hDu, div_mul_cancel₀ _ hΛ₀u]
  have e2 : ((contractForm (oM.or q₀.1).someVector (outwardM hE g q₀.1) (T q₀)).compLinearMap
      (D q).toLinearMap) (fun i => D'.symm (u₀ i)) = a₀ * Λ q₀ u₀ := by
    rw [hrep₀, hD₀]
    show a₀ * Λ q₀ (fun i => D q (D'.symm (u₀ i))) = _
    rw [hDu]
  have hz : contractForm (oM.or q.1).someVector (outwardM hE g q.1) (T q)
      (fun i => D'.symm (u₀ i)) ≠ 0 := by
    rw [e1]
    exact mul_ne_zero ha.ne' (mul_ne_zero hκ.ne' hΛ₀u)
  rw [orSign_eq_sgn_mul hZ _ _ rfl rfl (D q) hz, e1, e2]
  have : a₀ * Λ q₀ u₀ * (a * (Λ q u₀ / Λ q₀ u₀ * Λ q₀ u₀)) =
      (Λ q₀ u₀ * Λ q₀ u₀) * (a₀ * a * (Λ q u₀ / Λ q₀ u₀)) := by ring
  rw [this, sgn_sq_mul hΛ₀u, sgn_pos (mul_pos (mul_pos ha₀ ha) hκ)]

/-- **The induced orientation of the level set** `g⁻¹(0)` in an oriented manifold `M`
(Milnor's boundary orientation of `∂X`, `X = {g ≥ 0}`). -/
def levelOrientM :
    letI hS := isSliceSubmanifold_preimage (Z := Z) (finrank_Z_add hE hZ) hg h0
    letI := hS.chartedSpace
    Orient 𝓘(ℝ, Z) (g ⁻¹' {0}) n :=
  letI hS := isSliceSubmanifold_preimage (Z := Z) (finrank_Z_add hE hZ) hg h0
  letI := hS.chartedSpace
  { or := fun q => contractOr hZ (oM.or q.1) (outwardM hE g q.1)
      (mfd 𝓘(ℝ, Z) 𝓘(ℝ, E) (Subtype.val : g ⁻¹' {0} → M) q)
    cont := levelOrientM_cont hE hZ oM hg h0 }

theorem levelOrientM_or (q : g ⁻¹' {0}) :
    letI := (isSliceSubmanifold_preimage (Z := Z) (finrank_Z_add hE hZ) hg h0).chartedSpace
    (levelOrientM hE hZ oM hg h0).or q = contractOr hZ (oM.or q.1) (outwardM hE g q.1)
      (mfd 𝓘(ℝ, Z) 𝓘(ℝ, E) (Subtype.val : g ⁻¹' {0} → M) q) := rfl

end level

end Milnor
