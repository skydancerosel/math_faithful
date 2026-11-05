import Milnor.Chapter5.ChartFun
import Milnor.Chapter5.MonoAt

/-!
# Chart functions on the level-set curve

`S` is a 1-manifold with a smooth injective map `ι : S → M` into the level set `f⁻¹(y)` whose
derivative spans the kernel line of `df` (this is what Lemma 2 gives for `f⁻¹(y)` itself).
A chart function `c` at `ι a` restricts to a local diffeomorphism `c ∘ ι` of `S` near `a`.
For two chart functions `c, c'` the transition `k = c' ∘ ι ∘ (c ∘ ι)⁻¹` is a real function
whose derivative at `c (ι a)` has the sign of `c'(v) c(v)`, `v` the tangent vector of `S`.
-/

open Set Module Filter Topology Function
open scoped ContDiff Manifold

noncomputable section

namespace Milnor

universe u

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {F : Type u} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {G : Type*} [TopologicalSpace G] {J : ModelWithCorners ℝ F G} [J.Boundaryless]
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N] [IsManifold J ∞ N] {n : ℕ}
  {S : Type*} [TopologicalSpace S] [ChartedSpace ℝ S] [IsManifold 𝓘(ℝ, ℝ) ∞ S]

variable (hE : finrank ℝ E = n + 1) (hF : finrank ℝ F = n)
  {f : M → N} (hf : ContMDiff I J ∞ f) {y : N} (hy : IsRegularValue I J f y)
  {ι : S → M} (hι : ContMDiff 𝓘(ℝ, ℝ) I ∞ ι) (hιf : ∀ a, f (ι a) = y)
  (hιker : ∀ a v, (∃ w, mfd 𝓘(ℝ, ℝ) I ι a w = v) ↔ mfd I J f (ι a) v = 0)

/-- A nonzero map `ℝ →L[ℝ] ℝ` is invertible. -/
theorem isInvertible_of_ne_zero {L : ℝ →L[ℝ] ℝ} (hL : L 1 ≠ 0) : L.IsInvertible := by
  have hinj : Function.Injective L := by
    intro u v huv
    have h1 : L (u - v) = 0 := by rw [map_sub, huv, sub_self]
    have h2 : (u - v) * L 1 = 0 := by
      rw [← smul_eq_mul, ← map_smul, smul_eq_mul, mul_one]; exact h1
    rcases mul_eq_zero.1 h2 with h | h
    · exact sub_eq_zero.1 h
    · exact absurd h hL
  have hbij : Function.Bijective L :=
    ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (f := L.toLinearMap) rfl).1 hinj⟩
  exact ⟨(LinearEquiv.ofBijective L.toLinearMap hbij).toContinuousLinearEquiv, by ext; rfl⟩

include hE hF hy hιf hιker in
/-- The tangent vector `dι_a(1)` of the curve is nonzero. -/
theorem mfd_ι_one_ne_zero (a : S) : mfd 𝓘(ℝ, ℝ) I ι a 1 ≠ 0 := by
  obtain ⟨v₀, hv₀, hv₀0⟩ := exists_ne_zero_of_surjective hE hF (hy (ι a) (hιf a))
  obtain ⟨w, hw⟩ := (hιker a v₀).2 hv₀
  intro h1
  apply hv₀0
  rw [← hw, show w = w • (1 : ℝ) by simp, map_smul, h1, smul_zero]

include hιker in
/-- The tangent vector of the curve lies in the kernel of `df`. -/
theorem mfd_f_mfd_ι (a : S) : mfd I J f (ι a) (mfd 𝓘(ℝ, ℝ) I ι a 1) = 0 :=
  (hιker a _).1 ⟨1, rfl⟩

include hι in
/-- Chain rule for `c ∘ ι`. -/
theorem mfd_comp_ι {c : M → ℝ} {W : Set M} (hW : IsOpen W) (hc : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ c W)
    {a : S} (ha : ι a ∈ W) :
    mfd 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (c ∘ ι) a = (mfd I 𝓘(ℝ, ℝ) c (ι a)).comp (mfd 𝓘(ℝ, ℝ) I ι a) :=
  HasMFDerivAt.mfd_eq ((hasMFDerivAt_mfd (I := I) (J := 𝓘(ℝ, ℝ))
    ((hc.contMDiffAt (hW.mem_nhds ha)).mdifferentiableAt (by simp))).comp a
    (hasMFDerivAt_mfd (I := 𝓘(ℝ, ℝ)) (J := I) (hι.mdifferentiableAt (by simp))))

include hι in
theorem contMDiffAt_comp_ι {c : M → ℝ} {W : Set M} (hW : IsOpen W)
    (hc : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ c W) {a : S} (ha : ι a ∈ W) :
    ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ (c ∘ ι) a :=
  (hc.contMDiffAt (hW.mem_nhds ha)).comp a hι.contMDiffAt

include hE hF hf hy hι hιf hιker in
/-- **The transition between two chart functions.** For chart functions `c, c'` at `ι a` there are
a neighbourhood `V` of `a` on which `c ∘ ι` is injective, an open interval `D` around `c (ι a)`,
and a function `k` with `k ∘ c ∘ ι = c' ∘ ι` on `V`, `k` strictly monotone on `D`, increasing
exactly when `c(v) c'(v) > 0` for the tangent vector `v = dι_a(1)`. -/
theorem exists_transition {a : S} (cf cf' : ChartFun I J f (ι a)) :
    ∃ (V : Set S) (D : Set ℝ) (k : ℝ → ℝ), IsOpen V ∧ a ∈ V ∧ InjOn (cf.c ∘ ι) V ∧
      (∀ z ∈ V, cf.c (ι z) ∈ D ∧ k (cf.c (ι z)) = cf'.c (ι z)) ∧
      ((StrictMonoOn k D ∧
          0 < mfd I 𝓘(ℝ, ℝ) cf.c (ι a) (mfd 𝓘(ℝ, ℝ) I ι a 1) *
            mfd I 𝓘(ℝ, ℝ) cf'.c (ι a) (mfd 𝓘(ℝ, ℝ) I ι a 1)) ∨
       (StrictAntiOn k D ∧
          mfd I 𝓘(ℝ, ℝ) cf.c (ι a) (mfd 𝓘(ℝ, ℝ) I ι a 1) *
            mfd I 𝓘(ℝ, ℝ) cf'.c (ι a) (mfd 𝓘(ℝ, ℝ) I ι a 1) < 0)) := by
  set v := mfd 𝓘(ℝ, ℝ) I ι a 1 with hv
  have hv0 : v ≠ 0 := mfd_ι_one_ne_zero hE hF hy hιf hιker a
  have hvker : mfd I J f (ι a) v = 0 := mfd_f_mfd_ι hιker a
  set α := mfd I 𝓘(ℝ, ℝ) cf.c (ι a) v with hα_def
  set α' := mfd I 𝓘(ℝ, ℝ) cf'.c (ι a) v with hα'_def
  have hα : α ≠ 0 := cf.trans v hvker hv0
  have hα' : α' ≠ 0 := cf'.trans v hvker hv0
  -- `c ∘ ι` is a local diffeomorphism of `S` at `a`
  have hcS : ∀ᶠ z in 𝓝 a, ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ (cf.c ∘ ι) z := by
    filter_upwards [(cf.open_W.preimage hι.continuous).mem_nhds (cf.mem_W : ι a ∈ cf.W)]
      with z hz
    exact contMDiffAt_comp_ι hι cf.open_W cf.smooth hz
  have hdcS : mfd 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (cf.c ∘ ι) a 1 = α := by
    rw [mfd_comp_ι hι cf.open_W cf.smooth cf.mem_W]; rfl
  have hdcS' : mfd 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (cf'.c ∘ ι) a 1 = α' := by
    rw [mfd_comp_ι hι cf'.open_W cf'.smooth cf'.mem_W]; rfl
  have hloc : IsLocalDiffeomorphAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ (cf.c ∘ ι) a :=
    Milnor.isLocalDiffeomorphAt_of_isInvertible_mfderiv hcS (by simp)
      (isInvertible_of_ne_zero (by
        show mfd 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (cf.c ∘ ι) a 1 ≠ 0
        rw [hdcS]; exact hα))
  obtain ⟨Φ, haΦ, hΦ⟩ := hloc
  have hΦ' : ∀ z ∈ Φ.source, cf.c (ι z) = Φ z := fun z hz => hΦ hz
  have hleft : ∀ z ∈ Φ.source, Φ.symm (Φ z) = z := fun z hz => Φ.left_inv hz
  have hΦa : Φ a = cf.c (ι a) := (hΦ' a haΦ).symm
  -- the transition `k = c' ∘ ι ∘ Φ⁻¹`
  let k : ℝ → ℝ := fun u => cf'.c (ι (Φ.symm u))
  let D₀ : Set ℝ := Φ.target ∩ Φ.symm ⁻¹' (ι ⁻¹' cf'.W)
  have hD₀ : IsOpen D₀ := Φ.contMDiffOn_invFun.continuousOn.isOpen_inter_preimage Φ.open_target
    (cf'.open_W.preimage hι.continuous)
  have hcaD₀ : cf.c (ι a) ∈ D₀ := by
    refine ⟨by rw [← hΦa]; exact Φ.map_source haΦ, ?_⟩
    simp only [mem_preimage]
    rw [← hΦa, hleft a haΦ]
    exact cf'.mem_W
  have hk : ContDiffOn ℝ ∞ k D₀ := by
    rw [← contMDiffOn_iff_contDiffOn]
    have h1 : ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ Φ.symm D₀ := Φ.contMDiffOn_invFun.mono inter_subset_left
    exact cf'.smooth.comp ((hι.contMDiffOn (s := ι ⁻¹' cf'.W)).comp h1 (fun u hu => hu.2))
      (fun u hu => hu.2)
  have hkd : ContinuousOn (deriv k) D₀ := hk.continuousOn_deriv_of_isOpen hD₀ (by simp)
  -- the derivative of `k` at `c (ι a)` is `α' / α`
  have ha' : Φ.symm (cf.c (ι a)) = a := by rw [← hΦa]; exact hleft a haΦ
  have hΦs := hasMFDerivAt_mfd (I := 𝓘(ℝ, ℝ)) (J := 𝓘(ℝ, ℝ))
    ((Φ.contMDiffOn_invFun.contMDiffAt (Φ.open_target.mem_nhds hcaD₀.1)).mdifferentiableAt
      (by simp))
  have hcS'a : HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (cf'.c ∘ ι) (Φ.symm (cf.c (ι a)))
      (mfd 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (cf'.c ∘ ι) a :) := by
    rw [ha']
    exact hasMFDerivAt_mfd ((contMDiffAt_comp_ι hι cf'.open_W cf'.smooth cf'.mem_W).mdifferentiableAt
      (by simp))
  have hk' := hcS'a.comp (cf.c (ι a)) hΦs
  have hcSa := hasMFDerivAt_mfd (I := 𝓘(ℝ, ℝ)) (J := 𝓘(ℝ, ℝ))
    ((contMDiffAt_comp_ι hι cf.open_W cf.smooth cf.mem_W).mdifferentiableAt (by simp))
  have hinv := hΦs.comp a hcSa
  have hid : (Φ.symm ∘ (cf.c ∘ ι)) =ᶠ[𝓝 a] id := by
    filter_upwards [Φ.open_source.mem_nhds haΦ] with z hz
    simp only [Function.comp, id]
    rw [hΦ' z hz]
    exact hleft z hz
  have hβ := hasMFDerivAt_unique (hinv.congr_of_eventuallyEq hid.symm) (hasMFDerivAt_id (I := 𝓘(ℝ, ℝ)) a)
  set β := mfd 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) Φ.symm (cf.c (ι a)) 1 with hβ_def
  have hβα : β * α = 1 := by
    have := DFunLike.congr_fun hβ (1 : ℝ)
    change mfd 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) Φ.symm (cf.c (ι a)) (mfd 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (cf.c ∘ ι) a 1) = (1 : ℝ)
      at this
    rw [hdcS, show α = α • (1 : ℝ) by simp, map_smul, smul_eq_mul] at this
    rw [mul_comm]; exact this
  have hderiv : deriv k (cf.c (ι a)) = β * α' := by
    rw [← fderiv_apply_one_eq_deriv, ← mfderiv_eq_fderiv]
    show mfd 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ((cf'.c ∘ ι) ∘ Φ.symm) (cf.c (ι a)) 1 = β * α'
    rw [HasMFDerivAt.mfd_eq hk']
    change mfd 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (cf'.c ∘ ι) a (mfd 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) Φ.symm (cf.c (ι a)) 1) = β * α'
    rw [← hβ_def]
    have e1 : mfd 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (cf'.c ∘ ι) a β = β * α' := by
      rw [show β = β • (1 : ℝ) by simp, map_smul, smul_eq_mul, hdcS']; simp
    exact e1
  have hd0 : deriv k (cf.c (ι a)) ≠ 0 := by
    rw [hderiv]; exact mul_ne_zero (fun h => by rw [h, zero_mul] at hβα; exact zero_ne_one hβα) hα'
  have hcont : ContinuousAt (deriv k) (cf.c (ι a)) := hkd.continuousAt (hD₀.mem_nhds hcaD₀)
  -- the sign of `β * α'` is the sign of `α * α'`
  have hsign : 0 < β * α' ↔ 0 < α * α' := by
    have hβ' : β = α⁻¹ := eq_inv_of_mul_eq_one_left hβα
    rw [hβ']
    constructor
    · intro h; rcases lt_or_gt_of_ne hα with ha | ha
      · have : α⁻¹ < 0 := inv_lt_zero.2 ha
        exact mul_pos_of_neg_of_neg ha (neg_of_mul_pos_right h this.le)
      · have : 0 < α⁻¹ := inv_pos.2 ha
        exact mul_pos ha (pos_of_mul_pos_right h this.le)
    · intro h; rcases lt_or_gt_of_ne hα with ha | ha
      · have : α⁻¹ < 0 := inv_lt_zero.2 ha
        exact mul_pos_of_neg_of_neg this (neg_of_mul_pos_right h ha.le)
      · have : 0 < α⁻¹ := inv_pos.2 ha
        exact mul_pos this (pos_of_mul_pos_right h ha.le)
  -- the neighbourhood `V := Φ.source ∩ Φ⁻¹(D)`
  have hVgen : ∀ D : Set ℝ, IsOpen D → cf.c (ι a) ∈ D →
      ∃ V : Set S, IsOpen V ∧ a ∈ V ∧ InjOn (cf.c ∘ ι) V ∧
        ∀ z ∈ V, cf.c (ι z) ∈ D ∧ k (cf.c (ι z)) = cf'.c (ι z) := by
    intro D hD haD
    refine ⟨Φ.source ∩ Φ ⁻¹' D, Φ.contMDiffOn_toFun.continuousOn.isOpen_inter_preimage
      Φ.open_source hD, ⟨haΦ, by simp only [mem_preimage]; rw [hΦa]; exact haD⟩, ?_, ?_⟩
    · intro z₁ hz₁ z₂ hz₂ h
      simp only [Function.comp] at h
      rw [hΦ' z₁ hz₁.1, hΦ' z₂ hz₂.1] at h
      exact Φ.injOn hz₁.1 hz₂.1 h
    · intro z hz
      refine ⟨by rw [hΦ' z hz.1]; exact hz.2, ?_⟩
      simp only [k]
      rw [hΦ' z hz.1, hleft z hz.1]
  rcases lt_or_gt_of_ne hd0 with hneg | hpos
  · -- `k` decreasing near `c (ι a)`
    obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.1
      (inter_mem (hD₀.mem_nhds hcaD₀) (hcont.eventually_lt continuousAt_const hneg))
    rw [Real.ball_eq_Ioo] at hball
    obtain ⟨V, hVo, haV, hinj, hV⟩ := hVgen (Ioo (cf.c (ι a) - r) (cf.c (ι a) + r)) isOpen_Ioo
      (by constructor <;> linarith)
    refine ⟨V, _, k, hVo, haV, hinj, hV, Or.inr ⟨?_, ?_⟩⟩
    · refine strictAntiOn_of_deriv_neg (convex_Ioo _ _) (hk.continuousOn.mono fun u hu => (hball hu).1)
        fun u hu => ?_
      rw [interior_Ioo] at hu
      exact (hball hu).2
    · have : ¬ 0 < β * α' := by rw [hderiv] at hneg; exact not_lt.2 hneg.le
      rw [hsign] at this
      exact lt_of_le_of_ne (not_lt.1 this) (mul_ne_zero hα hα')
  · obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.1
      (inter_mem (hD₀.mem_nhds hcaD₀) (continuousAt_const.eventually_lt hcont hpos))
    rw [Real.ball_eq_Ioo] at hball
    obtain ⟨V, hVo, haV, hinj, hV⟩ := hVgen (Ioo (cf.c (ι a) - r) (cf.c (ι a) + r)) isOpen_Ioo
      (by constructor <;> linarith)
    refine ⟨V, _, k, hVo, haV, hinj, hV, Or.inl ⟨?_, ?_⟩⟩
    · refine strictMonoOn_of_deriv_pos (convex_Ioo _ _) (hk.continuousOn.mono fun u hu => (hball hu).1)
        fun u hu => ?_
      rw [interior_Ioo] at hu
      exact (hball hu).2
    · rw [hderiv] at hpos; exact hsign.1 hpos

include hE hF hy in
/-- At a boundary point (`g = 0`) the boundary function `g` is a chart function. -/
def gChartFun {g : M → ℝ} (hg : ContMDiff I 𝓘(ℝ, ℝ) ∞ g)
    (hreg : ∀ x, f x = y → g x = 0 → ∃ v, mfd I J f x v = 0 ∧ mfd I 𝓘(ℝ, ℝ) g x v ≠ 0)
    (m : M) (hm : f m = y) (hm0 : g m = 0) : ChartFun I J f m where
  c := g
  W := univ
  open_W := isOpen_univ
  mem_W := mem_univ m
  smooth := hg.contMDiffOn
  trans := by
    intro v hv hv0
    obtain ⟨v₁, hv₁, hgv₁⟩ := hreg m hm hm0
    have hv₁0 : v₁ ≠ 0 := by rintro rfl; simp at hgv₁
    obtain ⟨a, ha⟩ := exists_smul_eq_of_ker hE hF (hy m hm) hv₁ hv₁0 hv
    have ha0 : a ≠ 0 := by rintro rfl; simp at ha; exact hv0 ha.symm
    rw [← ha, map_smul]
    exact smul_ne_zero ha0 hgv₁

@[simp] theorem gChartFun_c {g : M → ℝ} (hg : ContMDiff I 𝓘(ℝ, ℝ) ∞ g)
    (hreg : ∀ x, f x = y → g x = 0 → ∃ v, mfd I J f x v = 0 ∧ mfd I 𝓘(ℝ, ℝ) g x v ≠ 0)
    (m : M) (hm : f m = y) (hm0 : g m = 0) : (gChartFun hE hF hy hg hreg m hm hm0).c = g := rfl

end Milnor
