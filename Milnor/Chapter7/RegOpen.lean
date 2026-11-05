import Milnor.Chapter7.Pontryagin

/-!
# The regular values of a map to the sphere form an open set (Milnor §7, p. 43)

For `f : M → Sᵖ` smooth on a compact manifold `M ⊆ ℝ^{K+1}`, the set of regular values of `f`
is open.  The regular points of `f` form an open subset of `M` (surjectivity of the derivative
is an open condition, read off through the ambient derivative `A x = dF̃_x` of Chapter 7), so
the critical points are closed, hence compact, and their image, the set of critical values, is
compact hence closed in `Sᵖ`.
-/

open Set Filter Topology Function Module Metric
open scoped ContDiff Manifold RealInnerProductSpace

noncomputable section

namespace Milnor

open Sphere

namespace Framed

/-! ### Surjectivity is an open condition -/

section surjOpen

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

omit [FiniteDimensional ℝ F] in
/-- A unit of `F →L[ℝ] F` is surjective. -/
theorem surjective_of_isUnit {B : F →L[ℝ] F} (hB : IsUnit B) : Surjective B := by
  obtain ⟨u, rfl⟩ := hB
  intro c
  refine ⟨(↑u⁻¹ : F →L[ℝ] F) c, ?_⟩
  rw [← mul_apply_eq_comp, u.mul_inv, one_apply_eq_self]

/-- `A` is surjective iff `A A^*` is a unit. -/
theorem surjective_iff_isUnit_comp_adjoint (A : E →L[ℝ] F) :
    Surjective A ↔ IsUnit (A.comp (ContinuousLinearMap.adjoint A)) := by
  refine ⟨isUnit_comp_adjoint, fun h => ?_⟩
  have := surjective_of_isUnit h
  exact Surjective.of_comp (g := ⇑(ContinuousLinearMap.adjoint A)) this

set_option synthInstance.maxHeartbeats 400000 in
/-- The surjective operators form an open subset of `E →L[ℝ] F`. -/
theorem isOpen_surjective : IsOpen {A : E →L[ℝ] F | Surjective A} := by
  have hcont : Continuous fun A : E →L[ℝ] F => A.comp (ContinuousLinearMap.adjoint A) :=
    continuous_id.clm_comp (ContinuousLinearMap.adjoint (𝕜 := ℝ) (E := E) (F := F)).continuous
  have hset : {A : E →L[ℝ] F | Surjective A} =
      (fun A : E →L[ℝ] F => A.comp (ContinuousLinearMap.adjoint A)) ⁻¹' {B | IsUnit B} := by
    ext A
    exact surjective_iff_isUnit_comp_adjoint A
  rw [hset]
  exact Units.isOpen.preimage hcont

end surjOpen

/-! ### Regular points via the ambient derivative -/

variable {K m w : ℕ} {M : Set (EuclideanSpace ℝ (Fin (K + 1)))}
  (hM : IsSliceSubmanifold 𝓘(ℝ, EuclideanSpace ℝ (Fin (K + 1))) (EuclideanSpace ℝ (Fin m))
    (EuclideanSpace ℝ (Fin w)) M) (hMc : IsCompact M) (hne : M.Nonempty) {p : ℕ}

variable {f : M → Sph p}
  (hf : letI := hM.chartedSpace; haveI := hM.isManifold;
    ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) ∞ f)
  {y : Sph p}

include hf in
/-- `dF̃_x` is surjective at a regular point `x` whose image lies in the chart at `y`. -/
theorem surjective_At_of_isRegularPoint {x : EuclideanSpace ℝ (Fin (K + 1))} (hx : x ∈ M)
    (hfx : f ⟨x, hx⟩ ∈ (extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) y).source)
    (hs1 : letI := hM.chartedSpace; haveI := hM.isManifold;
      Surjective (mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) f ⟨x, hx⟩)) :
    Surjective (At hM hMc hne f y x) := by
  letI := hM.chartedSpace
  haveI := hM.isManifold
  have h := At_comp_mfd_val hM hMc hne hf hx hfx
  have hs2 : Surjective (mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) 𝓘(ℝ, EuclideanSpace ℝ (Fin p))
      (extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) y) (f ⟨x, hx⟩)) := by
    obtain ⟨D, hD⟩ := isInvertible_mfderiv_extChartAt (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin p))) hfx
    show Surjective (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) 𝓘(ℝ, EuclideanSpace ℝ (Fin p))
      (extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) y) (f ⟨x, hx⟩))
    rw [← hD]; exact D.surjective
  have : Surjective ((At hM hMc hne f y x).comp (mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin m))
      𝓘(ℝ, EuclideanSpace ℝ (Fin (K + 1))) (Subtype.val : M → EuclideanSpace ℝ (Fin (K + 1))) ⟨x, hx⟩)) := by
    rw [h]; exact hs2.comp hs1
  exact Surjective.of_comp this

include hf in
/-- Converse: if `dF̃_x` is surjective at `x ∈ M` (with `f x` in the chart at `y`), then `x` is a
regular point of `f`. -/
theorem isRegularPoint_of_surjective_At {x : EuclideanSpace ℝ (Fin (K + 1))} (hx : x ∈ M)
    (hfx : f ⟨x, hx⟩ ∈ (extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) y).source)
    (hA : Surjective (At hM hMc hne f y x)) :
    letI := hM.chartedSpace; haveI := hM.isManifold;
    Surjective (mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) f ⟨x, hx⟩) := by
  letI := hM.chartedSpace
  haveI := hM.isManifold
  have h := At_comp_mfd_val hM hMc hne hf hx hfx
  -- `A ∘ d(val)` is surjective: every vector is tangent + normal, and `A` kills the normal part
  have hAv : Surjective ((At hM hMc hne f y x).comp (mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin m))
      𝓘(ℝ, EuclideanSpace ℝ (Fin (K + 1))) (Subtype.val : M → EuclideanSpace ℝ (Fin (K + 1))) ⟨x, hx⟩)) := by
    intro c
    obtain ⟨v, hv⟩ := hA c
    obtain ⟨t, ht, nv, hnv, hvt⟩ :=
      Submodule.exists_add_mem_mem_orthogonal (K := tangentM hM ⟨x, hx⟩) v
    obtain ⟨a, ha⟩ := LinearMap.mem_range.1 ht
    refine ⟨a, ?_⟩
    have hn0 : At hM hMc hne f y x nv = 0 :=
      At_normal_eq_zero hM hMc hne hf hx hfx ((Submodule.mem_orthogonal' _ _).1 hnv)
    rw [ContinuousLinearMap.comp_apply]
    have ha' : (mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 𝓘(ℝ, EuclideanSpace ℝ (Fin (K + 1)))
        (Subtype.val : M → EuclideanSpace ℝ (Fin (K + 1))) ⟨x, hx⟩) a = t := ha
    rw [ha', ← hv, hvt, map_add, hn0, add_zero]
  rw [h] at hAv
  -- `dc` is injective
  have hinj : Injective (mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) 𝓘(ℝ, EuclideanSpace ℝ (Fin p))
      (extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) y) (f ⟨x, hx⟩)) := by
    obtain ⟨D, hD⟩ := isInvertible_mfderiv_extChartAt (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin p))) hfx
    show Injective (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) 𝓘(ℝ, EuclideanSpace ℝ (Fin p))
      (extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) y) (f ⟨x, hx⟩))
    rw [← hD]; exact D.injective
  exact Surjective.of_comp_left hAv hinj

/-! ### Openness -/

include hf hMc hne in
/-- The regular points of `f` form an open subset of `M`. -/
theorem isOpen_regularPoints_sph :
    letI := hM.chartedSpace; haveI := hM.isManifold;
    IsOpen {x : M | IsRegularPoint 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) f x} := by
  letI := hM.chartedSpace
  haveI := hM.isManifold
  rw [isOpen_iff_eventually]
  intro x₀ hx₀
  have hs0 : Surjective (mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) f x₀) :=
    hx₀
  set y : Sph p := f x₀ with hy
  have hsrc0 : f ⟨x₀.1, x₀.2⟩ ∈ (extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) y).source := by
    rw [Subtype.coe_eta]; exact mem_extChartAt_source y
  have hA0 : Surjective (At hM hMc hne f y x₀.1) :=
    surjective_At_of_isRegularPoint hM hMc hne hf x₀.2 hsrc0 hs0
  have hW0 : x₀.1 ∈ Wt hM hMc hne f y := mem_Wt_of_mem hM hMc hne x₀.2 hsrc0
  -- three eventual facts near `x₀`
  have h1 : ∀ᶠ x : M in 𝓝 x₀, f x ∈ (extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) y).source :=
    hf.continuous.continuousAt.preimage_mem_nhds
      ((isOpen_extChartAt_source y).mem_nhds (by rw [Subtype.coe_eta] at hsrc0; exact hsrc0))
  have h2 : ∀ᶠ x : M in 𝓝 x₀, x.1 ∈ Wt hM hMc hne f y :=
    continuous_subtype_val.continuousAt.preimage_mem_nhds
      ((isOpen_Wt hM hMc hne hf).mem_nhds hW0)
  have hcA : ContinuousAt (fun x : M => At hM hMc hne f y x.1) x₀ :=
    ((contDiffOn_At hM hMc hne hf).continuousOn.continuousAt
      ((isOpen_Wt hM hMc hne hf).mem_nhds hW0)).comp continuous_subtype_val.continuousAt
  have h3 : ∀ᶠ x : M in 𝓝 x₀, Surjective (At hM hMc hne f y x.1) :=
    hcA.preimage_mem_nhds (isOpen_surjective.mem_nhds hA0)
  filter_upwards [h1, h2, h3] with x hx1 hx2 hx3
  have hx1' : f ⟨x.1, x.2⟩ ∈ (extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) y).source := by
    rw [Subtype.coe_eta]; exact hx1
  have := isRegularPoint_of_surjective_At hM hMc hne hf x.2 hx1' hx3
  exact this

include hf hMc hne in
/-- **The regular values of a smooth map `M → Sᵖ` on a compact manifold form an open set.** -/
theorem isOpen_regularValues_sph :
    letI := hM.chartedSpace; haveI := hM.isManifold;
    IsOpen {y : Sph p | IsRegularValue 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) f y} := by
  letI := hM.chartedSpace
  haveI := hM.isManifold
  haveI : CompactSpace M := isCompact_iff_compactSpace.1 hMc
  have hset : {y : Sph p | IsRegularValue 𝓘(ℝ, EuclideanSpace ℝ (Fin m))
      𝓘(ℝ, EuclideanSpace ℝ (Fin p)) f y} =
      (f '' {x : M | IsRegularPoint 𝓘(ℝ, EuclideanSpace ℝ (Fin m))
        𝓘(ℝ, EuclideanSpace ℝ (Fin p)) f x}ᶜ)ᶜ := by
    ext y
    simp only [mem_ofPred_eq, mem_compl_iff, mem_image, not_exists, not_and, IsRegularValue]
    constructor
    · intro h x hx hfx
      exact hx (h x hfx)
    · intro h x hfx
      by_contra hc
      exact h x hc hfx
  rw [hset]
  have hclosed : IsClosed {x : M | IsRegularPoint 𝓘(ℝ, EuclideanSpace ℝ (Fin m))
      𝓘(ℝ, EuclideanSpace ℝ (Fin p)) f x}ᶜ :=
    (isOpen_regularPoints_sph hM hMc hne hf).isClosed_compl
  exact ((hclosed.isCompact.image hf.continuous).isClosed).isOpen_compl

include hf hMc hne in
/-- The same statement for `regularValues`. -/
theorem isOpen_regularValues_sph' :
    letI := hM.chartedSpace; haveI := hM.isManifold;
    IsOpen (regularValues 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) f) :=
  isOpen_regularValues_sph hM hMc hne hf

end Framed

end Milnor
