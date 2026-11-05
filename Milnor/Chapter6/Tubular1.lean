import Milnor.Chapter6.Hopf
import Milnor.Chapter2.Corestrict

/-!
# Tubular neighbourhoods, I: local parametrizations of a submanifold of Euclidean space

For a slice submanifold `N ⊆ ℝᵏ` (model `ℝⁿ`, complement `ℝᵐ`) and `p ∈ N`, the slice chart at
`p` gives a local parametrization `φ_p : ℝⁿ ⊇ Ω_p → N`, smooth with injective derivative, whose
derivative spans the tangent space `T_q N = range (d val_q)` for `q` in the chart domain.
-/

open Set Filter Topology Function
open scoped ContDiff Manifold RealInnerProductSpace

noncomputable section

namespace Milnor

namespace Tub

variable {k n m : ℕ} {N : Set (EuclideanSpace ℝ (Fin k))}
  (hN : IsSliceSubmanifold 𝓘(ℝ, EuclideanSpace ℝ (Fin k)) (EuclideanSpace ℝ (Fin n))
    (EuclideanSpace ℝ (Fin m)) N)

/-- The slice chart at `p`. -/
def σ (p : N) : SliceChart 𝓘(ℝ, EuclideanSpace ℝ (Fin k)) (EuclideanSpace ℝ (Fin n))
    (EuclideanSpace ℝ (Fin m)) N := (hN p.1 p.2).choose

theorem mem_source (p : N) : p.1 ∈ (σ hN p).φ.source := (hN p.1 p.2).choose_spec

/-- The parametrization domain. -/
def Ω (p : N) : Set (EuclideanSpace ℝ (Fin n)) :=
  {z | (z, (0 : EuclideanSpace ℝ (Fin m))) ∈ (σ hN p).φ.target}

theorem isOpen_Ω (p : N) : IsOpen (Ω hN p) :=
  (σ hN p).φ.open_target.preimage (continuous_id.prodMk continuous_const)

/-- The local parametrization `φ_p`. -/
def φ (p : N) (z : EuclideanSpace ℝ (Fin n)) : EuclideanSpace ℝ (Fin k) :=
  (σ hN p).φ.invFun (z, 0)

theorem φ_mem (p : N) {z : EuclideanSpace ℝ (Fin n)} (hz : z ∈ Ω hN p) : φ hN p z ∈ N :=
  (σ hN p).symm_mem z hz

theorem φ_mem_source (p : N) {z : EuclideanSpace ℝ (Fin n)} (hz : z ∈ Ω hN p) :
    φ hN p z ∈ (σ hN p).φ.source :=
  (σ hN p).φ.invFun_mem hz

theorem contDiffOn_φ (p : N) : ContDiffOn ℝ ∞ (φ hN p) (Ω hN p) := by
  have h1 : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m))
      𝓘(ℝ, EuclideanSpace ℝ (Fin k)) ∞ (σ hN p).φ.invFun (σ hN p).φ.target :=
    (σ hN p).φ.contMDiffOn_invFun
  have h2 : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
      𝓘(ℝ, EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m)) ∞
      (fun z : EuclideanSpace ℝ (Fin n) => (z, (0 : EuclideanSpace ℝ (Fin m)))) :=
    contMDiff_iff_contDiff.2 (contDiff_id.prodMk contDiff_const)
  rw [← contMDiffOn_iff_contDiffOn]
  exact h1.comp h2.contMDiffOn (fun z hz => hz)

theorem contDiffOn_σφ (p : N) : ContDiffOn ℝ ∞ (σ hN p).φ (σ hN p).φ.source := by
  rw [← contMDiffOn_iff_contDiffOn]
  exact (σ hN p).φ.contMDiffOn_toFun

/-- The chart of `N` at `p`: `q ↦ (σ.φ q).1`. -/
def c (p : N) (q : N) : EuclideanSpace ℝ (Fin n) := ((σ hN p).φ q.1).1

theorem φ_c (p : N) {q : N} (hq : q.1 ∈ (σ hN p).φ.source) : φ hN p (c hN p q) = q.1 := by
  have h2 : ((σ hN p).φ q.1).2 = 0 := ((σ hN p).slice q.1 hq).1 q.2
  have h : (c hN p q, (0 : EuclideanSpace ℝ (Fin m))) = (σ hN p).φ q.1 := Prod.ext rfl h2.symm
  unfold φ
  rw [h]
  exact (σ hN p).φ.invFun_apply hq

theorem c_mem_Ω (p : N) {q : N} (hq : q.1 ∈ (σ hN p).φ.source) : c hN p q ∈ Ω hN p :=
  (σ hN p).mk_zero_mem_target hq q.2

theorem c_φ (p : N) {z : EuclideanSpace ℝ (Fin n)} (hz : z ∈ Ω hN p) :
    ((σ hN p).φ (φ hN p z)).1 = z := by
  unfold φ
  rw [(σ hN p).φ.apply_invFun hz]

/-- The extended chart of `N` at `p` is `c p`, with source `{q | q.1 ∈ σ.φ.source}`. -/
theorem extChartAt_eq' (p : N) :
    letI := hN.chartedSpace
    (extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) p : N → EuclideanSpace ℝ (Fin n)) = c hN p ∧
      (extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) p).source = {q : N | q.1 ∈ (σ hN p).φ.source} := by
  letI := hN.chartedSpace
  rw [IsSliceSubmanifold.extChartAt_eq hN p]
  exact ⟨rfl, rfl⟩

/-! ### Derivatives -/

theorem hasFDerivAt_φ (p : N) {z : EuclideanSpace ℝ (Fin n)} (hz : z ∈ Ω hN p) :
    HasFDerivAt (φ hN p) (fderiv ℝ (φ hN p) z) z :=
  (((contDiffOn_φ hN p).differentiableOn (by simp)) z hz).differentiableAt
    ((isOpen_Ω hN p).mem_nhds hz) |>.hasFDerivAt

theorem hasFDerivAt_σφ (p : N) {x : EuclideanSpace ℝ (Fin k)} (hx : x ∈ (σ hN p).φ.source) :
    HasFDerivAt (σ hN p).φ (fderiv ℝ (σ hN p).φ x) x :=
  (((contDiffOn_σφ hN p).differentiableOn (by simp)) x hx).differentiableAt
    ((σ hN p).φ.open_source.mem_nhds hx) |>.hasFDerivAt

/-- `dφ` is injective. -/
theorem injective_fderiv_φ (p : N) {z : EuclideanSpace ℝ (Fin n)} (hz : z ∈ Ω hN p) :
    Injective (fderiv ℝ (φ hN p) z) := by
  have hcomp : (fun z' => (σ hN p).φ (φ hN p z')) =ᶠ[𝓝 z]
      fun z' : EuclideanSpace ℝ (Fin n) => (z', (0 : EuclideanSpace ℝ (Fin m))) := by
    filter_upwards [(isOpen_Ω hN p).mem_nhds hz] with z' hz'
    exact (σ hN p).φ.apply_invFun hz'
  have h1 : HasFDerivAt (fun z' => (σ hN p).φ (φ hN p z'))
      ((fderiv ℝ (σ hN p).φ (φ hN p z)).comp (fderiv ℝ (φ hN p) z)) z :=
    (hasFDerivAt_σφ hN p (φ_mem_source hN p hz)).comp z (hasFDerivAt_φ hN p hz)
  have h2 : HasFDerivAt (fun z' : EuclideanSpace ℝ (Fin n) => (z', (0 : EuclideanSpace ℝ (Fin m))))
      (ContinuousLinearMap.inl ℝ (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin m))) z :=
    (hasFDerivAt_id z).prodMk (hasFDerivAt_const _ _)
  have h3 := h1.congr_of_eventuallyEq hcomp.symm
  have h4 := h3.unique h2
  intro a b hab
  have := congrArg (fun L => L a) h4
  have := congrArg (fun L => L b) h4
  have hab' : (fderiv ℝ (σ hN p).φ (φ hN p z)).comp (fderiv ℝ (φ hN p) z) a =
      (fderiv ℝ (σ hN p).φ (φ hN p z)).comp (fderiv ℝ (φ hN p) z) b := by
    simp only [ContinuousLinearMap.comp_apply, hab]
  rw [h4] at hab'
  simpa using hab'

/-- The tangent space `T_q N = range (d val_q)` is the range of `dφ_p` at `c p q`. -/
theorem range_mfd_val (p q : N) (hq : q.1 ∈ (σ hN p).φ.source) :
    letI := hN.chartedSpace
    LinearMap.range ((mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, EuclideanSpace ℝ (Fin k))
        (Subtype.val : N → EuclideanSpace ℝ (Fin k)) q :
          EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin k)) :
          EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin k)) =
      LinearMap.range ((fderiv ℝ (φ hN p) (c hN p q) :
        EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin k)) :
        EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin k)) := by
  letI := hN.chartedSpace
  haveI := hN.isManifold
  obtain ⟨hc, hsrc⟩ := extChartAt_eq' hN p
  have hqsrc : q ∈ (extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) p).source := by rw [hsrc]; exact hq
  -- `val = φ ∘ extChartAt p` near `q`
  have hev : (Subtype.val : N → EuclideanSpace ℝ (Fin k)) =ᶠ[𝓝 q]
      φ hN p ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) p) := by
    filter_upwards [(isOpen_extChartAt_source p).mem_nhds hqsrc] with q' hq'
    rw [hsrc] at hq'
    simp only [Function.comp, hc]
    exact (φ_c hN p hq').symm
  have hφd : HasMFDerivAt 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, EuclideanSpace ℝ (Fin k)) (φ hN p)
      (extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) p q) (fderiv ℝ (φ hN p) (c hN p q)) := by
    have := (hasFDerivAt_φ hN p (c_mem_Ω hN p hq)).hasMFDerivAt
    rw [hc]; exact this
  have hcd : HasMFDerivAt 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
      (extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) p) q
      (mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
        (extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) p) q :) :=
    hasMFDerivAt_mfd (mdifferentiableAt_extChartAt (by rwa [← extChartAt_source 𝓘(ℝ, EuclideanSpace ℝ (Fin n))]))
  have hchain := HasMFDerivAt.mfd_eq ((hφd.comp q hcd).congr_of_eventuallyEq hev)
  have hinv := isInvertible_mfderiv_extChartAt (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) hqsrc
  obtain ⟨D, hD⟩ := hinv
  have hsurj : Function.Surjective (mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
      (extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) p) q) := by
    show Function.Surjective (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
      (extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) p) q)
    rw [← hD]; exact D.surjective
  rw [hchain]
  exact LinearMap.range_comp_of_range_eq_top _ (LinearMap.range_eq_top.2 hsurj)

end Tub

end Milnor
