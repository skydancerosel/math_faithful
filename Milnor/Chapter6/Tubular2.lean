import Milnor.Chapter6.Tubular1

/-!
# Tubular neighbourhoods, II: the nearest-point equation

Near `p ∈ N` with parametrization `φ = φ_p`, a point `q = φ z` is the nearest point of `N` to
`x` only if `x - φ z` is orthogonal to the tangent space `range dφ_z`, i.e.
`Fn z x := (dφ_z)† (x - φ z) = 0`.  The map `(z, x) ↦ (Fn z x, x)` has invertible derivative
at `(z₀, φ z₀)`, so by the inverse function theorem the equation `Fn z x = 0` has, for `x` near
`φ z₀`, a unique solution `z = U x` near `z₀`, depending smoothly on `x`.
-/

open Set Filter Topology Function
open scoped ContDiff Manifold RealInnerProductSpace

noncomputable section

namespace Milnor

namespace Tub

variable {k n m : ℕ} {N : Set (EuclideanSpace ℝ (Fin k))}
  (hN : IsSliceSubmanifold 𝓘(ℝ, EuclideanSpace ℝ (Fin k)) (EuclideanSpace ℝ (Fin n))
    (EuclideanSpace ℝ (Fin m)) N) (p : N)

/-- The adjoint, as an `ℝ`-continuous linear map on operators. -/
def adjointCLM : (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin k)) →L[ℝ]
    (EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin n)) where
  toFun := ContinuousLinearMap.adjoint
  map_add' := map_add _
  map_smul' r A := by simpa using map_smulₛₗ ContinuousLinearMap.adjoint r A
  cont := ContinuousLinearMap.adjoint.continuous

@[simp] theorem adjointCLM_apply (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin k)) :
    adjointCLM A = ContinuousLinearMap.adjoint A := rfl

/-- `A z = (dφ_z)†`. -/
def A (z : EuclideanSpace ℝ (Fin n)) : EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
  ContinuousLinearMap.adjoint (fderiv ℝ (φ hN p) z)

theorem A_inner (z : EuclideanSpace ℝ (Fin n)) (y : EuclideanSpace ℝ (Fin k))
    (a : EuclideanSpace ℝ (Fin n)) : ⟪A hN p z y, a⟫ = ⟪y, fderiv ℝ (φ hN p) z a⟫ :=
  ContinuousLinearMap.adjoint_inner_left _ _ _

theorem contDiffOn_A : ContDiffOn ℝ ∞ (A hN p) (Ω hN p) := by
  have h1 : ContDiffOn ℝ ∞ (fderiv ℝ (φ hN p)) (Ω hN p) :=
    (contDiffOn_φ hN p).fderiv_of_isOpen (isOpen_Ω hN p) (by simp)
  exact adjointCLM.contDiff.comp_contDiffOn h1

/-- The nearest-point equation. -/
def Fn (z : EuclideanSpace ℝ (Fin n)) (x : EuclideanSpace ℝ (Fin k)) : EuclideanSpace ℝ (Fin n) :=
  A hN p z (x - φ hN p z)

/-- `Φ (z, x) = (Fn z x, x)`. -/
def Φ (q : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin k)) :
    EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin k) :=
  (Fn hN p q.1 q.2, q.2)

theorem contDiffOn_Φ : ContDiffOn ℝ ∞ (Φ hN p) (Ω hN p ×ˢ univ) := by
  have hA : ContDiffOn ℝ ∞ (fun q : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin k) =>
      A hN p q.1) (Ω hN p ×ˢ univ) :=
    (contDiffOn_A hN p).comp contDiff_fst.contDiffOn (fun q hq => hq.1)
  have hu : ContDiffOn ℝ ∞ (fun q : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin k) =>
      q.2 - φ hN p q.1) (Ω hN p ×ˢ univ) :=
    contDiff_snd.contDiffOn.sub ((contDiffOn_φ hN p).comp contDiff_fst.contDiffOn (fun q hq => hq.1))
  exact (hA.clm_apply hu).prodMk contDiff_snd.contDiffOn

/-- The derivative of `Φ` at `(z₀, φ z₀)`. -/
def DΦ (z₀ : EuclideanSpace ℝ (Fin n)) :
    EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin k) →L[ℝ]
      EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin k) :=
  ((A hN p z₀).comp (ContinuousLinearMap.snd ℝ _ _ -
    (fderiv ℝ (φ hN p) z₀).comp (ContinuousLinearMap.fst ℝ _ _))).prod
    (ContinuousLinearMap.snd ℝ _ _)

theorem hasFDerivAt_Φ {z₀ : EuclideanSpace ℝ (Fin n)} (hz₀ : z₀ ∈ Ω hN p) :
    HasFDerivAt (Φ hN p) (DΦ hN p z₀) (z₀, φ hN p z₀) := by
  have hAd : HasFDerivAt (A hN p) (fderiv ℝ (A hN p) z₀) z₀ :=
    (((contDiffOn_A hN p).differentiableOn (by simp)) z₀ hz₀).differentiableAt
      ((isOpen_Ω hN p).mem_nhds hz₀) |>.hasFDerivAt
  have h1 := hAd.comp (z₀, φ hN p z₀)
    (hasFDerivAt_fst (p := (z₀, φ hN p z₀)) : HasFDerivAt (Prod.fst : EuclideanSpace ℝ (Fin n) ×
      EuclideanSpace ℝ (Fin k) → EuclideanSpace ℝ (Fin n)) (ContinuousLinearMap.fst ℝ _ _) _)
  have hφ1 := (hasFDerivAt_φ hN p hz₀).comp (z₀, φ hN p z₀)
    (hasFDerivAt_fst (p := (z₀, φ hN p z₀)) : HasFDerivAt (Prod.fst : EuclideanSpace ℝ (Fin n) ×
      EuclideanSpace ℝ (Fin k) → EuclideanSpace ℝ (Fin n)) (ContinuousLinearMap.fst ℝ _ _) _)
  have h2 : HasFDerivAt (fun q : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin k) =>
      q.2 - φ hN p q.1) (ContinuousLinearMap.snd ℝ _ _ -
        (fderiv ℝ (φ hN p) z₀).comp (ContinuousLinearMap.fst ℝ _ _)) (z₀, φ hN p z₀) :=
    (hasFDerivAt_snd (p := (z₀, φ hN p z₀))).sub hφ1
  have h3 := (h1.clm_apply h2).prodMk (hasFDerivAt_snd (p := (z₀, φ hN p z₀)))
  simp only [sub_self, map_zero, add_zero] at h3
  exact h3

/-- `DΦ` is injective, hence bijective. -/
theorem injective_DΦ {z₀ : EuclideanSpace ℝ (Fin n)} (hz₀ : z₀ ∈ Ω hN p) :
    Injective (DΦ hN p z₀) := by
  refine (injective_iff_map_eq_zero _).2 ?_
  rintro ⟨a, b⟩ h
  simp only [DΦ, ContinuousLinearMap.prod_apply, ContinuousLinearMap.comp_apply, sub_apply,
    ContinuousLinearMap.coe_snd', ContinuousLinearMap.coe_fst', Prod.mk_eq_zero] at h
  obtain ⟨h1, hb⟩ := h
  subst hb
  rw [zero_sub, map_neg, neg_eq_zero] at h1
  have h2 : ⟪fderiv ℝ (φ hN p) z₀ a, fderiv ℝ (φ hN p) z₀ a⟫ = 0 := by
    rw [← A_inner, h1, inner_zero_left]
  have h3 : fderiv ℝ (φ hN p) z₀ a = 0 := inner_self_eq_zero.1 h2
  have h4 : a = 0 := injective_fderiv_φ hN p hz₀ (by rw [h3, map_zero])
  rw [h4]; rfl

/-- `DΦ` as a continuous linear equivalence. -/
def DΦe {z₀ : EuclideanSpace ℝ (Fin n)} (hz₀ : z₀ ∈ Ω hN p) :=
  ContinuousLinearEquiv.ofBijective (DΦ hN p z₀) (LinearMap.ker_eq_bot.2 (injective_DΦ hN p hz₀))
    (LinearMap.range_eq_top.2 (LinearMap.injective_iff_surjective
      (f := (DΦ hN p z₀).toLinearMap) |>.1 (injective_DΦ hN p hz₀)))

theorem DΦe_coe {z₀ : EuclideanSpace ℝ (Fin n)} (hz₀ : z₀ ∈ Ω hN p) :
    ↑(DΦe hN p hz₀) = DΦ hN p z₀ :=
  ContinuousLinearEquiv.coe_ofBijective _ _ _

theorem contDiffAt_Φ {z₀ : EuclideanSpace ℝ (Fin n)} (hz₀ : z₀ ∈ Ω hN p) :
    ContDiffAt ℝ ∞ (Φ hN p) (z₀, φ hN p z₀) :=
  (contDiffOn_Φ hN p).contDiffAt (((isOpen_Ω hN p).prod isOpen_univ).mem_nhds ⟨hz₀, mem_univ _⟩)

theorem hasFDerivAt_Φ' {z₀ : EuclideanSpace ℝ (Fin n)} (hz₀ : z₀ ∈ Ω hN p) :
    HasFDerivAt (Φ hN p) (DΦe hN p hz₀).toContinuousLinearMap (z₀, φ hN p z₀) := by
  rw [show (DΦe hN p hz₀).toContinuousLinearMap = DΦ hN p z₀ from DΦe_coe hN p hz₀]
  exact hasFDerivAt_Φ hN p hz₀

/-- The local inverse of `Φ` at `(z₀, φ z₀)`. -/
def Φinv {z₀ : EuclideanSpace ℝ (Fin n)} (hz₀ : z₀ ∈ Ω hN p) :
    EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin k) →
      EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin k) :=
  (contDiffAt_Φ hN p hz₀).localInverse (hasFDerivAt_Φ' hN p hz₀) (by simp)

/-- The solution `U x` of the nearest-point equation near `φ z₀`. -/
def U {z₀ : EuclideanSpace ℝ (Fin n)} (hz₀ : z₀ ∈ Ω hN p) (x : EuclideanSpace ℝ (Fin k)) :
    EuclideanSpace ℝ (Fin n) :=
  (Φinv hN p hz₀ (0, x)).1

theorem Fn_self (z : EuclideanSpace ℝ (Fin n)) : Fn hN p z (φ hN p z) = 0 := by
  simp [Fn]

theorem Φ_self (z : EuclideanSpace ℝ (Fin n)) : Φ hN p (z, φ hN p z) = (0, φ hN p z) := by
  simp [Φ, Fn_self]

theorem contDiffAt_U {z₀ : EuclideanSpace ℝ (Fin n)} (hz₀ : z₀ ∈ Ω hN p) :
    ContDiffAt ℝ ∞ (U hN p hz₀) (φ hN p z₀) := by
  have h1 := (contDiffAt_Φ hN p hz₀).to_localInverse (hasFDerivAt_Φ' hN p hz₀) (by simp)
  rw [Φ_self] at h1
  have h2 : ContDiffAt ℝ ∞ (fun x : EuclideanSpace ℝ (Fin k) =>
      ((0 : EuclideanSpace ℝ (Fin n)), x)) (φ hN p z₀) := contDiffAt_const.prodMk contDiffAt_id
  exact contDiff_fst.contDiffAt.comp _ (h1.comp _ h2)

theorem eventually_Φ_Φinv {z₀ : EuclideanSpace ℝ (Fin n)} (hz₀ : z₀ ∈ Ω hN p) :
    ∀ᶠ y in 𝓝 (0, φ hN p z₀), Φ hN p (Φinv hN p hz₀ y) = y := by
  have := ((contDiffAt_Φ hN p hz₀).hasStrictFDerivAt' (hasFDerivAt_Φ' hN p hz₀)
    (by simp)).eventually_right_inverse
  rwa [Φ_self] at this

theorem eventually_Φinv_Φ {z₀ : EuclideanSpace ℝ (Fin n)} (hz₀ : z₀ ∈ Ω hN p) :
    ∀ᶠ q in 𝓝 (z₀, φ hN p z₀), Φinv hN p hz₀ (Φ hN p q) = q :=
  ((contDiffAt_Φ hN p hz₀).hasStrictFDerivAt' (hasFDerivAt_Φ' hN p hz₀)
    (by simp)).eventually_left_inverse

/-- **Existence:** `U x` solves the nearest-point equation, for `x` near `φ z₀`. -/
theorem eventually_Fn_U {z₀ : EuclideanSpace ℝ (Fin n)} (hz₀ : z₀ ∈ Ω hN p) :
    ∀ᶠ x in 𝓝 (φ hN p z₀), Fn hN p (U hN p hz₀ x) x = 0 := by
  have h1 : Tendsto (fun x : EuclideanSpace ℝ (Fin k) => ((0 : EuclideanSpace ℝ (Fin n)), x))
      (𝓝 (φ hN p z₀)) (𝓝 (0, φ hN p z₀)) := (continuous_const.prodMk continuous_id).continuousAt
  filter_upwards [h1.eventually (eventually_Φ_Φinv hN p hz₀)] with x hx
  have h2 : Φ hN p (Φinv hN p hz₀ (0, x)) = (0, x) := hx
  have h3 := congrArg Prod.fst h2
  have h4 := congrArg Prod.snd h2
  simp only [Φ] at h3 h4
  rw [h4] at h3
  exact h3

theorem U_self {z₀ : EuclideanSpace ℝ (Fin n)} (hz₀ : z₀ ∈ Ω hN p) :
    U hN p hz₀ (φ hN p z₀) = z₀ := by
  have := (eventually_Φinv_Φ hN p hz₀).self_of_nhds
  rw [Φ_self] at this
  unfold U
  rw [this]

/-- **Uniqueness:** near `(z₀, φ z₀)`, solutions of the nearest-point equation are given by
`U`. -/
theorem eventually_eq_U {z₀ : EuclideanSpace ℝ (Fin n)} (hz₀ : z₀ ∈ Ω hN p) :
    ∀ᶠ q in 𝓝 (z₀, φ hN p z₀), Fn hN p q.1 q.2 = 0 → q.1 = U hN p hz₀ q.2 := by
  filter_upwards [eventually_Φinv_Φ hN p hz₀] with q hq hF
  have h1 : Φ hN p q = (0, q.2) := by simp [Φ, hF]
  rw [h1] at hq
  unfold U
  rw [hq]

/-- **Fermat:** a nearest point of `N` to `x` in the chart domain satisfies the nearest-point
equation. -/
theorem Fn_eq_zero_of_nearest {x : EuclideanSpace ℝ (Fin k)} {q : N}
    (hq : q.1 ∈ (σ hN p).φ.source) (hmin : ∀ q' ∈ N, dist x q.1 ≤ dist x q') :
    Fn hN p (c hN p q) x = 0 := by
  set z₀ := c hN p q with hz₀
  have hz₀Ω : z₀ ∈ Ω hN p := c_mem_Ω hN p hq
  have hφq : φ hN p z₀ = q.1 := φ_c hN p hq
  -- `z ↦ ‖x - φ z‖²` has a local minimum at `z₀`
  have hmin' : IsLocalMin (fun z => ‖x - φ hN p z‖ ^ 2) z₀ := by
    filter_upwards [(isOpen_Ω hN p).mem_nhds hz₀Ω] with z hz
    have := hmin (φ hN p z) (φ_mem hN p hz)
    rw [dist_eq_norm, dist_eq_norm, ← hφq] at this
    exact pow_le_pow_left₀ (norm_nonneg _) this 2
  have hd := ((hasFDerivAt_const x z₀).sub (hasFDerivAt_φ hN p hz₀Ω)).norm_sq
  have h0 := hmin'.hasFDerivAt_eq_zero hd
  -- hence `⟪x - φ z₀, dφ a⟫ = 0` for all `a`
  have hinner : ∀ a, ⟪x - φ hN p z₀, fderiv ℝ (φ hN p) z₀ a⟫ = 0 := by
    intro a
    have := congrArg (fun L => L a) h0
    simp only [smul_apply, ContinuousLinearMap.comp_apply, sub_apply, zero_apply, Pi.sub_apply,
      zero_sub, neg_apply, innerSL_apply_apply, inner_neg_right, nsmul_eq_mul,
      Nat.cast_ofNat, mul_neg, neg_eq_zero] at this
    rcases mul_eq_zero.1 this with h | h
    · norm_num at h
    · exact h
  have : ⟪Fn hN p z₀ x, Fn hN p z₀ x⟫ = 0 := by
    unfold Fn
    rw [A_inner, hinner]
  exact inner_self_eq_zero.1 this

set_option synthInstance.maxHeartbeats 400000 in
/-- **The local inverse is smooth on a neighbourhood** (invertibility of the derivative is an
open condition). -/
theorem exists_contDiffOn_U {z₀ : EuclideanSpace ℝ (Fin n)} (hz₀ : z₀ ∈ Ω hN p) :
    ∃ V : Set (EuclideanSpace ℝ (Fin k)), IsOpen V ∧ φ hN p z₀ ∈ V ∧
      ContDiffOn ℝ ∞ (U hN p hz₀) V := by
  set H := (contDiffAt_Φ hN p hz₀).toOpenPartialHomeomorph (Φ hN p) (hasFDerivAt_Φ' hN p hz₀)
    (by simp) with hH
  have hHc : (H : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin k) →
      EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin k)) = Φ hN p :=
    (contDiffAt_Φ hN p hz₀).toOpenPartialHomeomorph_coe _ _
  have hinv : Φinv hN p hz₀ = H.symm := rfl
  have hΩo : IsOpen (Ω hN p ×ˢ (univ : Set (EuclideanSpace ℝ (Fin k)))) :=
    (isOpen_Ω hN p).prod isOpen_univ
  have hfc : ContinuousOn (fderiv ℝ (Φ hN p)) (Ω hN p ×ˢ univ) :=
    (contDiffOn_Φ hN p).continuousOn_fderiv_of_isOpen hΩo (by simp)
  set W := (Ω hN p ×ˢ univ) ∩ (fderiv ℝ (Φ hN p)) ⁻¹' {L | IsUnit L} with hW
  have hWo : IsOpen W := hfc.isOpen_inter_preimage hΩo Units.isOpen
  have hz₀W : (z₀, φ hN p z₀) ∈ W := by
    refine ⟨⟨hz₀, mem_univ _⟩, ?_⟩
    show IsUnit (fderiv ℝ (Φ hN p) (z₀, φ hN p z₀))
    rw [(hasFDerivAt_Φ' hN p hz₀).fderiv]
    exact ⟨(DΦe hN p hz₀).toUnit, rfl⟩
  set T := H.target ∩ H.symm ⁻¹' W with hT
  have hTo : IsOpen T := H.continuousOn_symm.isOpen_inter_preimage H.open_target hWo
  have hmemT : ((0 : EuclideanSpace ℝ (Fin n)), φ hN p z₀) ∈ T := by
    refine ⟨?_, ?_⟩
    · have := (contDiffAt_Φ hN p hz₀).image_mem_toOpenPartialHomeomorph_target
        (hasFDerivAt_Φ' hN p hz₀) (by simp)
      rw [Φ_self] at this
      exact this
    · show H.symm (0, φ hN p z₀) ∈ W
      have : H.symm (0, φ hN p z₀) = (z₀, φ hN p z₀) := by
        have := (contDiffAt_Φ hN p hz₀).localInverse_apply_image (hasFDerivAt_Φ' hN p hz₀) (by simp)
        rw [Φ_self] at this
        exact this
      rw [this]
      exact hz₀W
  have hsymm : ∀ y ∈ T, ContDiffAt ℝ ∞ H.symm y := by
    intro y hy
    obtain ⟨hyT, hyW⟩ := hy
    obtain ⟨hyΩ, hyU⟩ := hyW
    obtain ⟨u, hu⟩ := hyU
    refine H.contDiffAt_symm hyT (f₀' := ContinuousLinearEquiv.ofUnit u) ?_ ?_
    · rw [hHc]
      have hd : HasFDerivAt (Φ hN p) (fderiv ℝ (Φ hN p) (H.symm y)) (H.symm y) :=
        (((contDiffOn_Φ hN p).differentiableOn (by simp) _ hyΩ).differentiableAt
          (hΩo.mem_nhds hyΩ)).hasFDerivAt
      have : (ContinuousLinearEquiv.ofUnit u).toContinuousLinearMap =
          fderiv ℝ (Φ hN p) (H.symm y) := by
        rw [← hu]
        exact ContinuousLinearMap.ext fun v => rfl
      rw [this]
      exact hd
    · rw [hHc]
      exact (contDiffOn_Φ hN p).contDiffAt (hΩo.mem_nhds hyΩ)
  refine ⟨{x | ((0 : EuclideanSpace ℝ (Fin n)), x) ∈ T},
    hTo.preimage (continuous_const.prodMk continuous_id), hmemT, ?_⟩
  intro x hx
  have h1 : ContDiffAt ℝ ∞ H.symm (0, x) := hsymm _ hx
  have h2 : ContDiffAt ℝ ∞ (fun x : EuclideanSpace ℝ (Fin k) =>
      ((0 : EuclideanSpace ℝ (Fin n)), x)) x := contDiffAt_const.prodMk contDiffAt_id
  exact (contDiff_fst.contDiffAt.comp _ (h1.comp _ h2)).contDiffWithinAt

end Tub

end Milnor
