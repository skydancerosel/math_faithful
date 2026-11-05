import Milnor.Chapter2.Brown
import Milnor.Chapter5.HairyBall
import Milnor.Chapter6.Region

/-!
# A genericity toolbox for Milnor §8 (Problems 13, 14, 17)

Milnor, *Topology from the Differentiable Viewpoint*, §8. Several of the problems use the following
general facts, proved here once:

* **Small images are small.** If `dim P < dim N`, a smooth map `g : P → N` has no regular value in
  its image (`not_isRegularValue_of_finrank_lt`), so by Brown's theorem the complement of its image
  is dense (`dense_compl_range_of_finrank_lt`). For a map smooth on an open set `U`, the image of
  `U` is meagre (`isMeagre_image_of_finrank_lt`) and the image of a compact subset of `U` is closed
  and nowhere dense (`isNowhereDense_image_of_finrank_lt`).
* **The complement of the diagonal of `Sᵖ × Sᵖ` is connected** for `p ≥ 1`
  (`isConnected_offDiag_sph`): every pair `(a, b)` with `a ≠ b` is joined to the antipodal pair
  `(a, −a)` by `t ↦ (a, ((1 − t) b − t a)/‖(1 − t) b − t a‖)`, and the antipodal pairs form a
  connected set.
* **Local constancy on a dense set gives constancy** (`eq_of_locallyConst_on_dense`): a function
  which near every point of a preconnected set `S` is constant on the points of a dense subset
  `R ∩ S` is constant on `R ∩ S`.
* In a Baire space, a nonempty open set contains points outside any given meagre set
  (`exists_mem_open_not_mem_of_isMeagre`).
-/

open Set Filter Topology Function Module TopologicalSpace
open scoped ContDiff Manifold

noncomputable section

namespace Milnor

namespace Problems

open Sphere

/-! ### Small images -/

section finrankLt

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {H : Type*} [TopologicalSpace H] {G : Type*} [TopologicalSpace G]
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F G}
  {P : Type*} [TopologicalSpace P] [ChartedSpace H P]
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N]

/-- 1. When `dim P < dim N`, no point of the image is a regular value: the derivative
`dgₓ : E → F` cannot be onto. -/
theorem not_isRegularValue_of_finrank_lt (hdim : finrank ℝ E < finrank ℝ F) (g : P → N) (x : P) :
    ¬ IsRegularValue I J g (g x) := by
  intro h
  let L : E →L[ℝ] F := mfderiv I J g x
  have hsurj : Surjective L := h x rfl
  have hrange : LinearMap.range (L : E →ₗ[ℝ] F) = ⊤ := LinearMap.range_eq_top.2 hsurj
  have hle := LinearMap.finrank_range_le (L : E →ₗ[ℝ] F)
  rw [hrange, finrank_top] at hle
  omega

end finrankLt

section brown

universe u

variable {E F : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {H : Type*} [TopologicalSpace H] {G : Type*} [TopologicalSpace G]
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F G} [I.Boundaryless] [J.Boundaryless]
  {P : Type*} [TopologicalSpace P] [ChartedSpace H P] [IsManifold I ∞ P]
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N] [IsManifold J ∞ N]

/-- 2. **Small images are small**: when `dim P < dim N`, the complement of the image of a smooth
map `g : P → N` is dense. (By Brown's theorem the regular values are dense, and by 1 they all lie
outside the image.) -/
theorem dense_compl_range_of_finrank_lt [SecondCountableTopology P]
    (hdim : finrank ℝ E < finrank ℝ F) {g : P → N} (hg : ContMDiff I J ∞ g) :
    Dense (Set.range g)ᶜ := by
  refine (dense_regularValues hg).mono ?_
  rintro y hy ⟨x, rfl⟩
  exact not_isRegularValue_of_finrank_lt hdim g x hy

/-- The image of an open set under a map smooth on it has dense complement (apply 2 to the open
submanifold). -/
theorem Generic.dense_compl_image_of_finrank_lt [SecondCountableTopology P]
    (hdim : finrank ℝ E < finrank ℝ F) {g : P → N} {U : Set P} (hU : IsOpen U)
    (hg : ContMDiffOn I J ∞ g U) : Dense (g '' U)ᶜ := by
  let U' : Opens P := ⟨U, hU⟩
  have hg' : ContMDiff I J ∞ (g ∘ (Subtype.val : U' → P)) :=
    hg.comp_contMDiff contMDiff_subtype_val fun x => x.2
  have h := dense_compl_range_of_finrank_lt hdim hg'
  rwa [range_comp, Subtype.range_coe] at h

/-- 4. The image of a compact set inside an open set on which `g` is smooth is closed and nowhere
dense. -/
theorem isNowhereDense_image_of_finrank_lt [SecondCountableTopology P] [T2Space N]
    (hdim : finrank ℝ E < finrank ℝ F) {g : P → N} {U K : Set P} (hU : IsOpen U) (hKU : K ⊆ U)
    (hK : IsCompact K) (hg : ContMDiffOn I J ∞ g U) :
    IsClosed (g '' K) ∧ IsNowhereDense (g '' K) := by
  have hclosed : IsClosed (g '' K) := (hK.image_of_continuousOn (hg.continuousOn.mono hKU)).isClosed
  refine ⟨hclosed, ?_⟩
  rw [hclosed.isNowhereDense_iff, interior_eq_empty_iff_dense_compl]
  exact (Generic.dense_compl_image_of_finrank_lt hdim hU hg).mono
    (compl_subset_compl.2 (image_mono hKU))

/-- 3. The image of an open set under a map smooth on it is meagre (so it has dense complement
when `N` is a Baire space; see also `Generic.dense_compl_image_of_finrank_lt`). The open set is
a countable union of compact sets, whose images are closed nowhere dense by 4. -/
theorem isMeagre_image_of_finrank_lt [SecondCountableTopology P] [T2Space N]
    (hdim : finrank ℝ E < finrank ℝ F) {g : P → N} {U : Set P} (hU : IsOpen U)
    (hg : ContMDiffOn I J ∞ g U) : IsMeagre (g '' U) := by
  have : LocallyCompactSpace P := Manifold.locallyCompact_of_finiteDimensional I
  have : LocallyCompactSpace U := hU.locallyCompactSpace
  have : SigmaCompactSpace U := sigmaCompactSpace_of_locallyCompact_secondCountable
  have hcover : g '' U = ⋃ n, g '' (Subtype.val '' compactCovering U n) := by
    rw [← image_iUnion, ← image_iUnion, iUnion_compactCovering, image_univ, Subtype.range_coe]
  rw [hcover]
  refine isMeagre_iUnion fun n => ?_
  have hKU : Subtype.val '' compactCovering U n ⊆ U := by
    rintro _ ⟨x, _, rfl⟩
    exact x.2
  exact (isNowhereDense_image_of_finrank_lt hdim hU hKU
    ((isCompact_compactCovering U n).image continuous_subtype_val) hg).2.isMeagre

end brown

/-! ### The complement of the diagonal of `Sᵖ × Sᵖ` -/

section offDiag

variable {p : ℕ}

/-- 5. **The complement of the diagonal of `Sᵖ × Sᵖ` is connected** (`p ≥ 1`). -/
theorem isConnected_offDiag_sph (hp : 1 ≤ p) : IsConnected {q : Sph p × Sph p | q.1 ≠ q.2} := by
  have := preconnectedSpace (n := p) (by omega)
  have hantip_ne : ∀ c : Sph p, c ≠ antip c := by
    intro c hc
    have h1 : c.1 = -c.1 := congrArg Subtype.val hc
    have h2 : ‖c.1‖ = 1 := mem_iff_norm.1 c.2
    have h3 : (2 : ℝ) • c.1 = (2 : ℝ) • 0 := by
      rw [two_smul, smul_zero]
      nth_rewrite 2 [h1]
      exact add_neg_cancel _
    rw [smul_right_injective _ two_ne_zero h3, norm_zero] at h2
    exact zero_ne_one h2
  -- the antipodal pairs form a connected set
  set A : Set (Sph p × Sph p) := range fun c : Sph p => (c, antip c)
  have hAS : A ⊆ {q : Sph p × Sph p | q.1 ≠ q.2} := by
    rintro _ ⟨c, rfl⟩
    exact hantip_ne c
  have hAconn : IsPreconnected A :=
    isPreconnected_range (continuous_id.prodMk contMDiff_antip.continuous)
  obtain ⟨e⟩ := nonempty_sph (n := p)
  refine ⟨⟨(e, antip e), hantip_ne e⟩, isPreconnected_of_forall (e, antip e) ?_⟩
  rintro ⟨a, b⟩ hab
  have hab' : a ≠ b := hab
  have ha1 : ‖a.1‖ = 1 := mem_iff_norm.1 a.2
  have hb1 : ‖b.1‖ = 1 := mem_iff_norm.1 b.2
  -- the segment from `b` to `-a`, which avoids `0`
  set w : ℝ → EuclideanSpace ℝ (Fin (p + 1)) := fun t => (1 - t) • b.1 - t • a.1 with hw
  have hw0 : ∀ t, w t ≠ 0 := by
    intro t ht
    have h1 : (1 - t) • b.1 = t • a.1 := sub_eq_zero.1 ht
    have h2 := congrArg norm h1
    rw [norm_smul, norm_smul, ha1, hb1, mul_one, mul_one, Real.norm_eq_abs,
      Real.norm_eq_abs] at h2
    have ht2 : t = 1 / 2 := by
      rcases abs_eq_abs.1 h2 with h | h <;> linarith
    have h3 : (1 / 2 : ℝ) • b.1 = (1 / 2 : ℝ) • a.1 := by
      rw [ht2] at h1
      convert h1 using 2
      norm_num
    exact hab' (Subtype.ext (smul_right_injective _ (by norm_num : (1 / 2 : ℝ) ≠ 0) h3).symm)
  have hwsmooth : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, EuclideanSpace ℝ (Fin (p + 1))) ∞ w :=
    contMDiff_iff_contDiff.2
      (((contDiff_const.sub contDiff_id).smul contDiff_const).sub (contDiff_id.smul contDiff_const))
  set γ : ℝ → Sph p × Sph p := fun t => (a, nv0 (w t))
  have hγcont : Continuous γ :=
    continuous_const.prodMk (contMDiff_nv0_comp hwsmooth hw0).continuous
  have hγ0 : γ 0 = (a, b) := by
    refine Prod.ext rfl (Subtype.ext ?_)
    have hb0 : b.1 ≠ 0 := fun h => by rw [h, norm_zero] at hb1; exact zero_ne_one hb1
    show (nv0 (w 0)).1 = b.1
    have hw0' : w 0 = b.1 := by simp [hw]
    rw [hw0', nv0_val hb0, Sphere.normalize, hb1, inv_one, one_smul]
  have hγ1 : γ 1 = (a, antip a) := by
    refine Prod.ext rfl (Subtype.ext ?_)
    have ha0 : -a.1 ≠ 0 := fun h => by
      rw [neg_eq_zero] at h; rw [h, norm_zero] at ha1; exact zero_ne_one ha1
    show (nv0 (w 1)).1 = -a.1
    have hw1' : w 1 = -a.1 := by simp [hw]
    rw [hw1', nv0_val ha0, Sphere.normalize, norm_neg, ha1, inv_one, one_smul]
  have hγS : γ '' Icc 0 1 ⊆ {q : Sph p × Sph p | q.1 ≠ q.2} := by
    rintro _ ⟨t, ⟨ht0, ht1⟩, rfl⟩ h
    have h1 : (nv0 (w t)).1 = a.1 := congrArg Subtype.val h.symm
    rw [nv0_val (hw0 t), Sphere.normalize] at h1
    have hwpos : 0 < ‖w t‖ := norm_pos_iff.2 (hw0 t)
    have h2 : w t = ‖w t‖ • a.1 := by
      rw [← h1, smul_smul, mul_inv_cancel₀ hwpos.ne', one_smul]
    have h3 : (1 - t) • b.1 = (t + ‖w t‖) • a.1 := by
      have h4 : (1 - t) • b.1 - t • a.1 = ‖w t‖ • a.1 := h2
      rw [add_smul, ← h4]
      abel
    have h4 := congrArg norm h3
    rw [norm_smul, norm_smul, ha1, hb1, mul_one, mul_one, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)] at h4
    rw [← h4] at h3
    have ht : 1 - t ≠ 0 := fun h => by linarith
    exact hab' (Subtype.ext (smul_right_injective _ ht h3).symm)
  refine ⟨γ '' Icc 0 1 ∪ A, union_subset hγS hAS, Or.inr ⟨e, rfl⟩,
    Or.inl ⟨0, ⟨le_rfl, zero_le_one⟩, hγ0⟩, ?_⟩
  exact IsPreconnected.union (a, antip a) ⟨1, ⟨zero_le_one, le_rfl⟩, hγ1⟩ ⟨a, rfl⟩
    (isPreconnected_Icc.image γ hγcont.continuousOn) hAconn

end offDiag

/-! ### Local constancy on a dense set -/

/-- 6. **Local constancy on a dense set of a preconnected set gives constancy.** If near every
point of a preconnected set `S` the function `φ` is constant on the points of `R ∩ S`, and `R ∩ S`
is dense in `S`, then `φ` is constant on `R ∩ S`. -/
theorem eq_of_locallyConst_on_dense {X : Type*} [TopologicalSpace X] {Y : Type*} {S R : Set X}
    (hS : IsPreconnected S) (hR : S ⊆ closure (R ∩ S)) (φ : X → Y)
    (h : ∀ x ∈ S, ∃ V ∈ 𝓝 x, ∀ y ∈ V ∩ (R ∩ S), ∀ z ∈ V ∩ (R ∩ S), φ y = φ z) :
    ∀ y ∈ R ∩ S, ∀ z ∈ R ∩ S, φ y = φ z := by
  let _ : TopologicalSpace Y := ⊥
  have : DiscreteTopology Y := ⟨rfl⟩
  choose! V hV hVc using h
  have hne : ∀ x ∈ S, (V x ∩ (R ∩ S)).Nonempty := fun x hx =>
    mem_closure_iff_nhds.1 (hR hx) _ (hV x hx)
  choose! pt hpt using hne
  -- `ψ x` is the common value of `φ` on `V x ∩ (R ∩ S)`
  set ψ : X → Y := fun x => φ (pt x)
  have hψφ : ∀ y ∈ R ∩ S, ψ y = φ y := fun y hy =>
    hVc y hy.2 (pt y) (hpt y hy.2) y ⟨mem_of_mem_nhds (hV y hy.2), hy⟩
  -- `ψ` is locally constant on `S`
  have hcont : ContinuousOn ψ S := by
    intro x hx
    rw [ContinuousWithinAt, nhds_discrete, tendsto_pure]
    filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (interior_mem_nhds.2 (hV x hx))] with x' hx' hx'V
    obtain ⟨y, ⟨hyV', hyW⟩, hyRS⟩ : (V x' ∩ interior (V x) ∩ (R ∩ S)).Nonempty :=
      mem_closure_iff_nhds.1 (hR hx') _ (inter_mem (hV x' hx') (isOpen_interior.mem_nhds hx'V))
    calc ψ x' = φ y := hVc x' hx' (pt x') (hpt x' hx') y ⟨hyV', hyRS⟩
      _ = ψ x := hVc x hx y ⟨interior_subset hyW, hyRS⟩ (pt x) (hpt x hx)
  intro y hy z hz
  rw [← hψφ y hy, ← hψφ z hz]
  exact hS.constant hcont hy.2 hz.2

/-! ### Baire spaces -/

/-- 7. Points avoiding a meagre set (for instance a finite union of meagre sets, `IsMeagre.union`)
exist in any nonempty open subset of a Baire space. -/
theorem exists_mem_open_not_mem_of_isMeagre {X : Type*} [TopologicalSpace X] [BaireSpace X]
    {W : Set X} (hW : IsOpen W) (hWne : W.Nonempty) {s : Set X} (hs : IsMeagre s) :
    ∃ x ∈ W, x ∉ s := by
  obtain ⟨x, hxW, hxs⟩ := (dense_of_mem_residual hs).inter_open_nonempty W hW hWne
  exact ⟨x, hxW, hxs⟩

end Problems

end Milnor
