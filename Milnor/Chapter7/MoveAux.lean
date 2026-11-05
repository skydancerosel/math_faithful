import Milnor.Chapter7.Hopf0
import Milnor.Chapter7.Glue
import Milnor.Chapter7.OrientTransport
import Milnor.Chapter5.OrSignAlg

/-!
# Frames in chart coordinates: the dual tuple

For a frame `v` at `x` (tangent, independent) and a chart `φ = extChartAt x_c` whose source
contains `x`, the map `B = dφ_x ∘ basisCLM (chart coordinates of v)` is bijective and the sign of
its determinant is the **chart sign** of the frame (`Chapter7/ChartSign.lean`).  The *dual tuple*
`τ` is the tuple of columns of `B⁻¹`; `basisCLM τ` is the inverse of `B` and has the same
determinant sign.  Two dual tuples of frames of the same determinant sign span bases of the same
orientation.

No orientation of `M` occurs in `chartFrameCLM_bijective` or in `exists_dualTuple`: the only thing
the old positivity hypothesis `orSign (oM.or x) (oM.or x_c) dφ_x = 1` was used for is that the
chart derivative at `x` is invertible, and `Milnor.bijective_mfd_extChartAt` gives that from
`x ∈ (extChartAt 𝓘(ℝ, ℝᵐ) x_c).source` alone.  The one lemma that still mentions an orientation is
`orSign_chartFrameCLM`, which is the *bridge* between the chart sign and the orientation-dependent
`frameSign`; see `Chapter7/ChartSign.lean`.
-/

open Set Filter Topology Function Module Metric
open scoped ContDiff Manifold RealInnerProductSpace Classical

noncomputable section

namespace Milnor

open Sphere

namespace Framed

variable {K m w : ℕ} {M : Set (EuclideanSpace ℝ (Fin (K + 1)))}
  {hM : IsSliceSubmanifold 𝓘(ℝ, EuclideanSpace ℝ (Fin (K + 1))) (EuclideanSpace ℝ (Fin m))
    (EuclideanSpace ℝ (Fin w)) M}

variable (hM) in
/-- `B = dφ_x ∘ basisCLM w`, `w` the chart coordinates of the frame `v` at `x`, `φ = extChartAt x_c`. -/
def chartFrameCLM (x_c x : M) (v : Fin m → EuclideanSpace ℝ (Fin (K + 1))) :
    EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m) :=
  letI := hM.chartedSpace
  haveI := hM.isManifold
  (mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 𝓘(ℝ, EuclideanSpace ℝ (Fin m))
    (extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) x_c) x).comp
    (basisCLM (fun i => chartCoord hM x (v i)))

variable (oM : letI := hM.chartedSpace; Orient 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) M m)

/-- **The frame read in a chart is bijective.**  Membership of the chart's source is all that is
needed: the chart derivative there is a linear automorphism
(`Milnor.bijective_mfd_extChartAt`). -/
theorem chartFrameCLM_bijective {x_c x : M}
    (hx : letI := hM.chartedSpace;
      x ∈ (extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) x_c).source)
    {v : Fin m → EuclideanSpace ℝ (Fin (K + 1))} (hvT : ∀ i, v i ∈ tangentM hM x)
    (hv : LinearIndependent ℝ v) : Function.Bijective (chartFrameCLM hM x_c x v) := by
  letI := hM.chartedSpace
  haveI := hM.isManifold
  exact (bijective_mfd_extChartAt hx).comp
    (basisCLM_bijective (linearIndependent_chartCoord hM hvT hv))

/-- **The bridge to the oriented sign.**  If the chart at `x_c` carries the orientation at `x` to
the orientation at `x_c`, then the sign of the frame read in that chart, taken from the standard
orientation to the orientation at the hub, is the frame sign of `Chapter7/Hopf0.lean`.  Taking the
hub orientation to be `stdOr m` turns the left-hand side into the chart sign of
`Chapter7/ChartSign.lean`. -/
theorem orSign_chartFrameCLM {x_c x : M}
    (hx : letI := hM.chartedSpace; haveI := hM.isManifold;
      orSign (oM.or x) (oM.or x_c) (mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 𝓘(ℝ, EuclideanSpace ℝ (Fin m))
        (extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) x_c) x) = 1)
    (v : Fin m → EuclideanSpace ℝ (Fin (K + 1))) :
    letI := hM.chartedSpace
    orSign (stdOr m) (oM.or x_c) (chartFrameCLM hM x_c x v) = frameSign hM oM v x := by
  letI := hM.chartedSpace
  haveI := hM.isManifold
  unfold chartFrameCLM frameSign
  rw [orSign_comp finrank_E finrank_E (stdOr m) (oM.or x) (oM.or x_c), hx, one_mul]

/-- **The dual tuple.**  The last conjunct says that the dual tuple has the same determinant sign
as the frame read in the chart, that is `chartSign hM x_c x v` of `Chapter7/ChartSign.lean` (which
is *by definition* the right-hand side; it cannot be named here, since that file imports this
one). -/
theorem exists_dualTuple {x_c x : M}
    (hx : letI := hM.chartedSpace;
      x ∈ (extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) x_c).source)
    {v : Fin m → EuclideanSpace ℝ (Fin (K + 1))} (hvT : ∀ i, v i ∈ tangentM hM x)
    (hv : LinearIndependent ℝ v) :
    letI := hM.chartedSpace
    ∃ τ : Fin m → EuclideanSpace ℝ (Fin m), LinearIndependent ℝ τ ∧
      (chartFrameCLM hM x_c x v).comp (basisCLM τ) = ContinuousLinearMap.id ℝ _ ∧
      (basisCLM τ).comp (chartFrameCLM hM x_c x v) = ContinuousLinearMap.id ℝ _ ∧
      sgn (LinearMap.det ((basisCLM τ :
          EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m)) :
          EuclideanSpace ℝ (Fin m) →ₗ[ℝ] EuclideanSpace ℝ (Fin m))) =
        sgn (LinearMap.det ((chartFrameCLM hM x_c x v :
          EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m)) :
          EuclideanSpace ℝ (Fin m) →ₗ[ℝ] EuclideanSpace ℝ (Fin m))) := by
  letI := hM.chartedSpace
  haveI := hM.isManifold
  set B := chartFrameCLM hM x_c x v with hBdef
  have hB : Function.Bijective B := chartFrameCLM_bijective hx hvT hv
  set τ : Fin m → EuclideanSpace ℝ (Fin m) :=
    fun i => Function.invFun B (EuclideanSpace.single i 1) with hτ
  have hBτ : ∀ i, B (τ i) = EuclideanSpace.single i 1 := fun i =>
    Function.invFun_eq (hB.2 _)
  have hcomp1 : B.comp (basisCLM τ) = ContinuousLinearMap.id ℝ _ := by
    rw [basisCLM_comp_eq hBτ, basisCLM_single_eq_id]
  have hinj : Function.Injective (basisCLM τ) := by
    intro a a' h
    have := congrArg B h
    have h1 := congrArg (fun T => T a) hcomp1
    have h2 := congrArg (fun T => T a') hcomp1
    simp only [ContinuousLinearMap.coe_comp', Function.comp_apply,
      ContinuousLinearMap.id_apply] at h1 h2
    rw [← h1, ← h2, this]
  have hcomp2 : (basisCLM τ).comp B = ContinuousLinearMap.id ℝ _ := by
    refine ContinuousLinearMap.ext fun s => ?_
    apply hB.1
    have h1 := congrArg (fun T => T (B s)) hcomp1
    simpa using h1
  have hindep : LinearIndependent ℝ τ := by
    have h := (EuclideanSpace.basisFun (Fin m) ℝ).toBasis.linearIndependent
    have h2 := h.map' (basisCLM τ : EuclideanSpace ℝ (Fin m) →ₗ[ℝ] EuclideanSpace ℝ (Fin m))
      (LinearMap.ker_eq_bot.2 hinj)
    have h3 : (⇑(basisCLM τ : EuclideanSpace ℝ (Fin m) →ₗ[ℝ] EuclideanSpace ℝ (Fin m)) ∘
        ⇑(EuclideanSpace.basisFun (Fin m) ℝ).toBasis) = τ := by
      funext i
      simp [basisCLM_single]
    rw [h3] at h2
    exact h2
  refine ⟨τ, hindep, hcomp1, hcomp2, ?_⟩
  have h1 := orSign_comp_eq_one finrank_E finrank_E (stdOr m) (stdOr m) hcomp1
  rw [orSign_self_eq_sgn_det finrank_E (stdOr m) B,
    orSign_self_eq_sgn_det finrank_E (stdOr m) (basisCLM τ)] at h1
  rcases Int.eq_one_or_neg_one_of_mul_eq_one' h1 with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · rw [ha, hb]
  · rw [ha, hb]

/-- Bases whose `basisCLM` have the same sign against a fixed orientation have the same
orientation. -/
theorem orientation_eq_of_orSign_basisCLM_eq (hm : 0 < m)
    {o : Orientation ℝ (EuclideanSpace ℝ (Fin m)) (Fin m)}
    (e₀ e₁ : Basis (Fin m) ℝ (EuclideanSpace ℝ (Fin m)))
    (h : orSign (stdOr m) o (basisCLM e₀) = orSign (stdOr m) o (basisCLM e₁)) :
    e₀.orientation = e₁.orientation := by
  have hb₀ := basisCLM_bijective e₀.linearIndependent
  have hb₁ := basisCLM_bijective e₁.linearIndependent
  have he₀ := orSign_stdOr_basisCLM e₀
  have he₁ := orSign_stdOr_basisCLM e₁
  rcases orSign_eq_one_or_neg_one finrank_E finrank_E (stdOr m) o hb₀ with h1 | h1
  · have h0 : e₀.orientation = o :=
      orientation_eq_of_orSign_eq hm finrank_E finrank_E (stdOr m) hb₀ (he₀.trans h1.symm)
    have h1' : e₁.orientation = o :=
      orientation_eq_of_orSign_eq hm finrank_E finrank_E (stdOr m) hb₁
        (he₁.trans (h.symm.trans h1).symm)
    rw [h0, h1']
  · have hn₀ : orSign (stdOr m) (-o) (basisCLM e₀) = 1 := by
      rw [orSign_neg_right finrank_E, h1]; norm_num
    have hn₁ : orSign (stdOr m) (-o) (basisCLM e₁) = 1 := by
      rw [orSign_neg_right finrank_E, ← h, h1]; norm_num
    have h0 : e₀.orientation = -o :=
      orientation_eq_of_orSign_eq hm finrank_E finrank_E (stdOr m) hb₀ (he₀.trans hn₀.symm)
    have h1' : e₁.orientation = -o :=
      orientation_eq_of_orSign_eq hm finrank_E finrank_E (stdOr m) hb₁ (he₁.trans hn₁.symm)
    rw [h0, h1']

end Framed

end Milnor
