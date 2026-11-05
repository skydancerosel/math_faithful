import Milnor.Chapter7.MoveAux
import Milnor.Chapter7.MoveMap
import Milnor.Chapter7.TuplePath

/-!
# The moving homotopy `H = glueH (moveΦ …) k`

Given the data of a moving family `Φ = moveΦ hb c τ γ` (a point moving along `γ` in the chart,
with a path of dual tuples `τ`) and a map `k : M → Sᵐ` which is `south` near the frontier of the
chart ball, the glued homotopy `H` is smooth, `north` is a regular value of `H` and of every time
slice, `H(·, t)⁻¹(north)` is `{φ⁻¹(γ t)} ∪ (k⁻¹(north) \ U)`, and at the moving point the chart
derivative of the slice is `(c • basisCLM b) ∘ basisCLM (τ t) ∘ dφ`.

**No orientation of `M` occurs in this file.**  The regularity of `north` needs only that the
chart derivative is invertible on the chart's source (`Milnor.bijective_mfd_extChartAt`), so the
orientation `oM` and the positivity hypothesis `hpos` that the older version of these lemmas
carried have been dropped.
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

section moveH

variable {x_c : M} {R : ℝ} (hR : 0 < R)
  (hRt : letI := hM.chartedSpace;
    closedBall (extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) x_c x_c) R ⊆
      (extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) x_c).target)
  {b : Fin m → EuclideanSpace ℝ (Fin m)} (hb : LinearIndependent ℝ b) {c : ℝ} (hc : 0 < c)
  {ε₀ μ : ℝ} (hsouth : ∀ z, ε₀ / 2 ≤ ‖z‖ → collapse hb c z = south) (hμ : 0 < μ)
  (hε₀ : ε₀ = μ * R / 2)
  {τ : ℝ → Fin m → EuclideanSpace ℝ (Fin m)} (hτ : ContDiff ℝ ∞ (fun t => basisCLM (τ t)))
  (hτi : ∀ t, LinearIndependent ℝ (τ t)) (hτμ : ∀ t z, μ * ‖z‖ ≤ ‖basisCLM (τ t) z‖)
  {γ : ℝ → EuclideanSpace ℝ (Fin m)} (hγ : ContDiff ℝ ∞ γ)
  (hγR : letI := hM.chartedSpace; ∀ t, ‖γ t - extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) x_c x_c‖ < R / 4)
  {k : M → Sph m}
  (hk : letI := hM.chartedSpace; haveI := hM.isManifold;
    ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) ∞ k)
  (hkn : letI := hM.chartedSpace; haveI := hM.isManifold;
    IsRegularValue 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) k north)
  {O : Set M} (hO : IsOpen O) (hOU : closure (ballU hM x_c R) \ ballU hM x_c R ⊆ O)
  (hkO : ∀ z ∈ O, k z = south)

include hR hμ hε₀ hsouth hτμ hγR in
/-- The moving family is `south` at chart distance `≥ R/2` from the centre. -/
theorem moveΦ_south_of_le :
    letI := hM.chartedSpace
    ∀ s t, R / 2 ≤ ‖s - extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) x_c x_c‖ →
      moveΦ hb c τ γ (s, t) = south := by
  letI := hM.chartedSpace
  intro s t hs
  refine moveΦ_eq_south hb hsouth hτμ γ ?_
  have h1 := hγR t
  have h2 : R / 4 ≤ ‖s - γ t‖ := by
    have : ‖s - extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) x_c x_c‖ ≤
        ‖s - γ t‖ + ‖γ t - extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) x_c x_c‖ :=
      norm_sub_le_norm_sub_add_norm_sub _ _ _
    linarith
  rw [hε₀]
  calc μ * R / 2 / 2 = μ * (R / 4) := by ring
    _ ≤ μ * ‖s - γ t‖ := mul_le_mul_of_nonneg_left h2 hμ.le

include hR hRt hμ hε₀ hsouth hτ hτμ hγ hγR hk hO hOU hkO in
theorem contMDiff_moveH :
    letI := hM.chartedSpace; haveI := hM.isManifold;
    ContMDiff (𝓘(ℝ, EuclideanSpace ℝ (Fin m)).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) ∞
      (glueH hM x_c R (moveΦ hb c τ γ) k) :=
  contMDiff_glueH hR hRt (contMDiff_moveΦ hb c hτ hγ)
    (moveΦ_south_of_le (hM := hM) (x_c := x_c) (hR := hR) (hb := hb) (hsouth := hsouth) (hμ := hμ)
      (hε₀ := hε₀) (hτμ := hτμ) (hγR := hγR)) hk hO hOU hkO

include hc hτi in
/-- The preimage of `north` under a time slice. -/
theorem moveH_eq_north_iff (t : ℝ) (x : M) :
    letI := hM.chartedSpace
    glueH hM x_c R (moveΦ hb c τ γ) k (x, t) = north ↔
      (x ∈ ballU hM x_c R ∧ extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) x_c x = γ t) ∨
      (x ∉ ballU hM x_c R ∧ k x = north) := by
  letI := hM.chartedSpace
  by_cases hx : x ∈ ballU hM x_c R
  · rw [glueH_of_mem hx, moveΦ_eq_north_iff hb hc.ne' hτi]
    simp [hx]
  · rw [glueH_of_notMem hx]
    simp [hx]

include hτ hγ in
/-- The chart derivative of a slice at a point of the chart ball. -/
theorem mfd_moveH_slice_of_mem {x : M} (hx : x ∈ ballU hM x_c R) {t : ℝ}
    (hxt : letI := hM.chartedSpace; extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) x_c x = γ t) :
    letI := hM.chartedSpace; haveI := hM.isManifold;
    mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 𝓘(ℝ, EuclideanSpace ℝ (Fin m))
      (fun x => glueH hM x_c R (moveΦ hb c τ γ) k (x, t)) x =
      ((c • basisCLM b).comp (basisCLM (τ t))).comp
        (mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 𝓘(ℝ, EuclideanSpace ℝ (Fin m))
          (extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) x_c) x) := by
  letI := hM.chartedSpace
  haveI := hM.isManifold
  have h := hasMFDerivAt_glueH_slice_of_mem (Φ := moveΦ hb c τ γ) (k := k)
    (contMDiff_moveΦ hb c hτ hγ) hx t
  rw [hxt, HasMFDerivAt.mfd_eq (hasMFDerivAt_moveΦ_slice hb c τ γ t)] at h
  exact HasMFDerivAt.mfd_eq h

include hc hτ hτi hγ in
/-- At a point of the chart ball where the slice takes the value `north`, the slice derivative is
bijective. -/
theorem bijective_mfd_moveH_slice_of_mem {x : M} (hx : x ∈ ballU hM x_c R) {t : ℝ}
    (hxt : letI := hM.chartedSpace; extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) x_c x = γ t) :
    letI := hM.chartedSpace; haveI := hM.isManifold;
    Function.Bijective (mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 𝓘(ℝ, EuclideanSpace ℝ (Fin m))
      (fun x => glueH hM x_c R (moveΦ hb c τ γ) k (x, t)) x) := by
  letI := hM.chartedSpace
  haveI := hM.isManifold
  rw [mfd_moveH_slice_of_mem (hb := hb) (c := c) (k := k) (hτ := hτ) (hγ := hγ) hx hxt]
  have h1 : Function.Bijective (c • basisCLM b) := by
    have := basisCLM_bijective hb
    refine ⟨fun a a' h => ?_, fun y => ?_⟩
    · have h' : c • basisCLM b a = c • basisCLM b a' := h
      exact this.1 (smul_right_injective _ hc.ne' h')
    · obtain ⟨a, ha⟩ := this.2 (c⁻¹ • y)
      refine ⟨a, ?_⟩
      show c • basisCLM b a = y
      rw [ha, smul_smul, mul_inv_cancel₀ hc.ne', one_smul]
  exact (h1.comp (basisCLM_bijective (hτi t))).comp (bijective_mfd_extChartAt (mem_ballU.1 hx).1)

include hR hRt hc hsouth hμ hε₀ hτ hτi hτμ hγ hγR hkn hO hOU hkO in
/-- `north` is a regular value of every time slice. -/
theorem isRegularValue_moveH_slice (t : ℝ) :
    letI := hM.chartedSpace; haveI := hM.isManifold;
    IsRegularValue 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 𝓘(ℝ, EuclideanSpace ℝ (Fin m))
      (fun x => glueH hM x_c R (moveΦ hb c τ γ) k (x, t)) north := by
  letI := hM.chartedSpace
  haveI := hM.isManifold
  intro x hx
  rcases (moveH_eq_north_iff (hb := hb) (γ := γ) (k := k) (hc := hc) (hτi := hτi) t x).1 hx with
    ⟨hxU, hxt⟩ | ⟨hxU, hkx⟩
  · exact (bijective_mfd_moveH_slice_of_mem (hb := hb) (hc := hc) (k := k)
      (hτ := hτ) (hτi := hτi) (hγ := hγ) hxU hxt).2
  · have hev := glueH_slice_eventually_eq_of_notMem (Φ := moveΦ hb c τ γ) hR hRt
      (moveΦ_south_of_le (hM := hM) (x_c := x_c) (hR := hR) (hb := hb) (hsouth := hsouth)
        (hμ := hμ) (hε₀ := hε₀) (hτμ := hτμ) (hγR := hγR)) hO hOU hkO hxU t
    have hev' : (fun x => glueH hM x_c R (moveΦ hb c τ γ) k (x, t)) =ᶠ[𝓝 x] k := hev
    show Function.Surjective (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 𝓘(ℝ, EuclideanSpace ℝ (Fin m))
      (fun x => glueH hM x_c R (moveΦ hb c τ γ) k (x, t)) x)
    rw [hev'.mfderiv_eq]
    exact hkn x hkx

include hR hRt hc hsouth hμ hε₀ hτ hτi hτμ hγ hγR hk hkn hO hOU hkO in
/-- `north` is a regular value of the homotopy. -/
theorem isRegularValue_moveH :
    letI := hM.chartedSpace; haveI := hM.isManifold;
    IsRegularValue (𝓘(ℝ, EuclideanSpace ℝ (Fin m)).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, EuclideanSpace ℝ (Fin m))
      (glueH hM x_c R (moveΦ hb c τ γ) k) north := by
  letI := hM.chartedSpace
  haveI := hM.isManifold
  rintro ⟨x, t⟩ hxt
  have hΦ := contMDiff_moveΦ hb c hτ hγ
  rcases (moveH_eq_north_iff (hb := hb) (γ := γ) (k := k) (hc := hc) (hτi := hτi) t x).1 hxt with
    ⟨hxU, hxt'⟩ | ⟨hxU, hkx⟩
  · -- on `U × ℝ` the map is `Φ ∘ (φ × id)`
    have hev : ∀ᶠ q in 𝓝 (x, t), glueH hM x_c R (moveΦ hb c τ γ) k q =
        moveΦ hb c τ γ (extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) x_c q.1, q.2) := by
      filter_upwards [((isOpen_ballU x_c R).prod isOpen_univ).mem_nhds
        (show (x, t) ∈ ballU hM x_c R ×ˢ univ from ⟨hxU, mem_univ _⟩)] with q hq
      exact glueH_of_mem hq.1 q.2
    have hx' : x ∈ (chartAt (EuclideanSpace ℝ (Fin m)) x_c).source := by
      rw [← extChartAt_source 𝓘(ℝ, EuclideanSpace ℝ (Fin m))]; exact (mem_ballU.1 hxU).1
    have hφ := ((contMDiffAt_extChartAt' (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin m))) (n := ∞)
      hx').mdifferentiableAt (by simp)).hasMFDerivAt
    have hfst := hasMFDerivAt_fst (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin m))) (I' := 𝓘(ℝ, ℝ))
      (M := M) (M' := ℝ) (x, t)
    have hsnd := hasMFDerivAt_snd (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin m))) (I' := 𝓘(ℝ, ℝ))
      (M := M) (M' := ℝ) (x, t)
    have hpair := (hφ.comp (x, t) hfst).prodMk hsnd
    have hΦd := (hΦ.mdifferentiableAt (by simp)).hasMFDerivAt
      (x := (extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) x_c x, t))
    have hcomp := hΦd.comp (x, t) hpair
    have hH := hcomp.congr_of_eventuallyEq hev
    show Function.Surjective (mfderiv (𝓘(ℝ, EuclideanSpace ℝ (Fin m)).prod 𝓘(ℝ, ℝ))
      𝓘(ℝ, EuclideanSpace ℝ (Fin m)) (glueH hM x_c R (moveΦ hb c τ γ) k) (x, t))
    rw [hH.mfderiv]
    -- both factors are surjective
    have hsurj1 := surjective_mfderiv_moveΦ hb hc.ne' hτ hτi hγ t
    rw [← hxt'] at hsurj1
    have hbij := bijective_mfd_extChartAt (mem_ballU.1 hxU).1
    intro y
    obtain ⟨u, hu⟩ := hsurj1 y
    obtain ⟨a, ha⟩ := hbij.2 u.1
    refine ⟨(a, u.2), ?_⟩
    show mfderiv (𝓘(ℝ, EuclideanSpace ℝ (Fin m)).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, EuclideanSpace ℝ (Fin m))
      (moveΦ hb c τ γ) (extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) x_c x, t)
      (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 𝓘(ℝ, EuclideanSpace ℝ (Fin m))
        (extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) x_c) x a, u.2) = y
    have hpair' : ((mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 𝓘(ℝ, EuclideanSpace ℝ (Fin m))
        (extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) x_c) x a, u.2) :
        EuclideanSpace ℝ (Fin m) × ℝ) = u := Prod.ext ha rfl
    rw [hpair']
    exact hu
  · have hev := glueH_eventually_eq_of_notMem (Φ := moveΦ hb c τ γ) hR hRt
      (moveΦ_south_of_le (hM := hM) (x_c := x_c) (hR := hR) (hb := hb) (hsouth := hsouth)
        (hμ := hμ) (hε₀ := hε₀) (hτμ := hτμ) (hγR := hγR)) hO hOU hkO hxU t
    have hfst := hasMFDerivAt_fst (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin m))) (I' := 𝓘(ℝ, ℝ))
      (M := M) (M' := ℝ) (x, t)
    have hkd := (hk.mdifferentiableAt (by simp)).hasMFDerivAt (x := x)
    have hH := (hkd.comp (x, t) hfst).congr_of_eventuallyEq hev
    show Function.Surjective (mfderiv (𝓘(ℝ, EuclideanSpace ℝ (Fin m)).prod 𝓘(ℝ, ℝ))
      𝓘(ℝ, EuclideanSpace ℝ (Fin m)) (glueH hM x_c R (moveΦ hb c τ γ) k) (x, t))
    rw [hH.mfderiv]
    intro y
    obtain ⟨u, hu⟩ := hkn x hkx y
    exact ⟨(u, 0), hu⟩

end moveH

end Framed

end Milnor
