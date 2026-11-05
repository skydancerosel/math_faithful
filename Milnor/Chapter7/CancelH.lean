import Milnor.Chapter7.MoveAux
import Milnor.Chapter7.CancelMap

/-!
# The cancelling homotopy `H = glueH (cancelΦ …) k`

Given the data of a cancelling family `Ψ = cancelΦ hb c w a ρ c₀` (two zeros `c₀ ± a • w` in the
chart at time `0`, none at time `1`) and a map `k : M → Sᵐ` which is `south` near the frontier of
the chart ball, the glued homotopy `H` is smooth, `north` is a regular value of `H` and of every
time slice at which `ρ ≠ 0`, `H(·, t)⁻¹(north)` is `{φ⁻¹(c₀ + l • w) : l² = a² ρ t} ∪ (k⁻¹(north) \ U)`,
and at a zero of the slice the chart derivative is `(c • basisCLM b) ∘ Tcan w l ∘ dφ`.

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

variable {K m d : ℕ} {M : Set (EuclideanSpace ℝ (Fin (K + 1)))}
  {hM : IsSliceSubmanifold 𝓘(ℝ, EuclideanSpace ℝ (Fin (K + 1))) (EuclideanSpace ℝ (Fin m))
    (EuclideanSpace ℝ (Fin d)) M}

section cancelH

variable {x_c : M} {R : ℝ} (hR : 0 < R)
  (hRt : letI := hM.chartedSpace;
    closedBall (extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) x_c x_c) R ⊆
      (extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) x_c).target)
  {b : Fin m → EuclideanSpace ℝ (Fin m)} (hb : LinearIndependent ℝ b) {c : ℝ} (hc : 0 < c)
  {ε₀ : ℝ} (hsouth : ∀ z, ε₀ / 2 ≤ ‖z‖ → collapse hb c z = south)
  {w : EuclideanSpace ℝ (Fin m)} (hw : ‖w‖ = 1) {a : ℝ} (ha : 0 < a) (haR : 8 * a ≤ R)
  {ρ : ℝ → ℝ} (hρ : ContDiff ℝ ∞ ρ) (hρ1 : ∀ t, |ρ t| ≤ 1) (hρ' : ∀ t, ρ t = 0 → deriv ρ t ≠ 0)
  {c₀ : EuclideanSpace ℝ (Fin m)}
  (hc₀ : letI := hM.chartedSpace; ‖c₀ - extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) x_c x_c‖ < R / 8)
  (hε₀ : ε₀ = 2 * min (3 * R / 8 / 2) ((3 * R / 8) ^ 2 / 4))
  {k : M → Sph m}
  (hk : letI := hM.chartedSpace; haveI := hM.isManifold;
    ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) ∞ k)
  (hkn : letI := hM.chartedSpace; haveI := hM.isManifold;
    IsRegularValue 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) k north)
  {O : Set M} (hO : IsOpen O) (hOU : closure (ballU hM x_c R) \ ballU hM x_c R ⊆ O)
  (hkO : ∀ z ∈ O, k z = south)

include hsouth hw ha haR hρ1 hc₀ hε₀ in
/-- The cancelling family is `south` at chart distance `≥ R/2` from the centre. -/
theorem cancelΦ_south_of_le :
    letI := hM.chartedSpace
    ∀ s t, R / 2 ≤ ‖s - extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) x_c x_c‖ →
      cancelΦ hb c w a ρ c₀ (s, t) = south := by
  letI := hM.chartedSpace
  intro s t hs
  refine cancelΦ_eq_south hb hsouth hw ha hρ1 (r := 3 * R / 8) (by linarith) ?_ c₀ ?_
  · rw [hε₀]; linarith
  · have : ‖s - extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) x_c x_c‖ ≤
        ‖s - c₀‖ + ‖c₀ - extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) x_c x_c‖ :=
      norm_sub_le_norm_sub_add_norm_sub _ _ _
    linarith

include hR hRt hsouth hw ha haR hρ hρ1 hc₀ hε₀ hk hO hOU hkO in
theorem contMDiff_cancelH :
    letI := hM.chartedSpace; haveI := hM.isManifold;
    ContMDiff (𝓘(ℝ, EuclideanSpace ℝ (Fin m)).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) ∞
      (glueH hM x_c R (cancelΦ hb c w a ρ c₀) k) :=
  contMDiff_glueH hR hRt (contMDiff_cancelΦ hb c w a hρ c₀)
    (cancelΦ_south_of_le (hM := hM) (x_c := x_c) (hb := hb) (hsouth := hsouth) (hw := hw)
      (ha := ha) (haR := haR) (hρ1 := hρ1) (hc₀ := hc₀) (hε₀ := hε₀)) hk hO hOU hkO

include hc hw in
/-- The preimage of `north` under a time slice. -/
theorem cancelH_eq_north_iff (t : ℝ) (x : M) :
    letI := hM.chartedSpace
    glueH hM x_c R (cancelΦ hb c w a ρ c₀) k (x, t) = north ↔
      (x ∈ ballU hM x_c R ∧ ∃ l : ℝ,
        extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) x_c x = c₀ + l • w ∧ l ^ 2 = a ^ 2 * ρ t) ∨
      (x ∉ ballU hM x_c R ∧ k x = north) := by
  letI := hM.chartedSpace
  by_cases hx : x ∈ ballU hM x_c R
  · rw [glueH_of_mem hx, cancelΦ_eq_north_iff hb hc.ne' hw]
    simp [hx]
  · rw [glueH_of_notMem hx]
    simp [hx]

include hw hρ in
/-- The chart derivative of a slice at a zero in the chart ball. -/
theorem mfd_cancelH_slice_of_mem {x : M} (hx : x ∈ ballU hM x_c R) {t l : ℝ}
    (hl : l ^ 2 = a ^ 2 * ρ t)
    (hφ : letI := hM.chartedSpace; extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) x_c x = c₀ + l • w) :
    letI := hM.chartedSpace; haveI := hM.isManifold;
    mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 𝓘(ℝ, EuclideanSpace ℝ (Fin m))
      (fun x => glueH hM x_c R (cancelΦ hb c w a ρ c₀) k (x, t)) x =
      ((c • basisCLM b).comp (Tcan w l)).comp
        (mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 𝓘(ℝ, EuclideanSpace ℝ (Fin m))
          (extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) x_c) x) := by
  letI := hM.chartedSpace
  haveI := hM.isManifold
  have h := hasMFDerivAt_glueH_slice_of_mem (Φ := cancelΦ hb c w a ρ c₀) (k := k)
    (contMDiff_cancelΦ hb c w a hρ c₀) hx t
  rw [hφ, HasMFDerivAt.mfd_eq (hasMFDerivAt_cancelΦ_slice hb c hw a ρ c₀ t hl)] at h
  exact HasMFDerivAt.mfd_eq h

include hc hw hρ in
/-- At a zero of the slice in the chart ball with `l ≠ 0`, the slice derivative is bijective. -/
theorem bijective_mfd_cancelH_slice_of_mem {x : M} (hx : x ∈ ballU hM x_c R) {t l : ℝ}
    (hl : l ^ 2 = a ^ 2 * ρ t) (hl0 : l ≠ 0)
    (hφ : letI := hM.chartedSpace; extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) x_c x = c₀ + l • w) :
    letI := hM.chartedSpace; haveI := hM.isManifold;
    Function.Bijective (mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 𝓘(ℝ, EuclideanSpace ℝ (Fin m))
      (fun x => glueH hM x_c R (cancelΦ hb c w a ρ c₀) k (x, t)) x) := by
  letI := hM.chartedSpace
  haveI := hM.isManifold
  rw [mfd_cancelH_slice_of_mem (hb := hb) (c := c) (k := k) (hw := hw) (hρ := hρ) hx hl hφ]
  have h1 : Function.Bijective (c • basisCLM b) := by
    have := basisCLM_bijective hb
    refine ⟨fun a a' h => ?_, fun y => ?_⟩
    · have h' : c • basisCLM b a = c • basisCLM b a' := h
      exact this.1 (smul_right_injective _ hc.ne' h')
    · obtain ⟨a, ha⟩ := this.2 (c⁻¹ • y)
      refine ⟨a, ?_⟩
      show c • basisCLM b a = y
      rw [ha, smul_smul, mul_inv_cancel₀ hc.ne', one_smul]
  exact (h1.comp (Tcan_bijective hw hl0)).comp (bijective_mfd_extChartAt (mem_ballU.1 hx).1)

include hR hRt hc hsouth hw ha haR hρ hρ1 hc₀ hε₀ hkn hO hOU hkO in
/-- `north` is a regular value of every time slice at which `ρ ≠ 0`. -/
theorem isRegularValue_cancelH_slice (t : ℝ) (hρt : ρ t ≠ 0) :
    letI := hM.chartedSpace; haveI := hM.isManifold;
    IsRegularValue 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 𝓘(ℝ, EuclideanSpace ℝ (Fin m))
      (fun x => glueH hM x_c R (cancelΦ hb c w a ρ c₀) k (x, t)) north := by
  letI := hM.chartedSpace
  haveI := hM.isManifold
  intro x hx
  rcases (cancelH_eq_north_iff (hb := hb) (k := k) (hc := hc) (hw := hw) (a := a) (ρ := ρ)
      (c₀ := c₀) t x).1 hx with ⟨hxU, l, hφ, hl⟩ | ⟨hxU, hkx⟩
  · have hl0 : l ≠ 0 := by
      intro h
      rw [h] at hl
      have h2 : a ^ 2 * ρ t = 0 := by rw [← hl]; ring
      rcases mul_eq_zero.1 h2 with h' | h'
      · exact ha.ne' (pow_eq_zero_iff two_ne_zero |>.1 h')
      · exact hρt h'
    exact (bijective_mfd_cancelH_slice_of_mem (hb := hb) (hc := hc) (k := k)
      (hw := hw) (hρ := hρ) hxU hl hl0 hφ).2
  · have hev := glueH_slice_eventually_eq_of_notMem (Φ := cancelΦ hb c w a ρ c₀) hR hRt
      (cancelΦ_south_of_le (hM := hM) (x_c := x_c) (hb := hb) (hsouth := hsouth) (hw := hw)
        (ha := ha) (haR := haR) (hρ1 := hρ1) (hc₀ := hc₀) (hε₀ := hε₀)) hO hOU hkO hxU t
    have hev' : (fun x => glueH hM x_c R (cancelΦ hb c w a ρ c₀) k (x, t)) =ᶠ[𝓝 x] k := hev
    show Function.Surjective (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 𝓘(ℝ, EuclideanSpace ℝ (Fin m))
      (fun x => glueH hM x_c R (cancelΦ hb c w a ρ c₀) k (x, t)) x)
    rw [hev'.mfderiv_eq]
    exact hkn x hkx

include hR hRt hc hsouth hw ha haR hρ hρ1 hρ' hc₀ hε₀ hk hkn hO hOU hkO in
/-- `north` is a regular value of the homotopy. -/
theorem isRegularValue_cancelH :
    letI := hM.chartedSpace; haveI := hM.isManifold;
    IsRegularValue (𝓘(ℝ, EuclideanSpace ℝ (Fin m)).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, EuclideanSpace ℝ (Fin m))
      (glueH hM x_c R (cancelΦ hb c w a ρ c₀) k) north := by
  letI := hM.chartedSpace
  haveI := hM.isManifold
  rintro ⟨x, t⟩ hxt
  have hΦ := contMDiff_cancelΦ hb c w a hρ c₀
  rcases (cancelH_eq_north_iff (hb := hb) (k := k) (hc := hc) (hw := hw) (a := a) (ρ := ρ)
      (c₀ := c₀) t x).1 hxt with ⟨hxU, l, hφ, hl⟩ | ⟨hxU, hkx⟩
  · -- on `U × ℝ` the map is `Φ ∘ (φ × id)`
    have hev : ∀ᶠ q in 𝓝 (x, t), glueH hM x_c R (cancelΦ hb c w a ρ c₀) k q =
        cancelΦ hb c w a ρ c₀ (extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) x_c q.1, q.2) := by
      filter_upwards [((isOpen_ballU x_c R).prod isOpen_univ).mem_nhds
        (show (x, t) ∈ ballU hM x_c R ×ˢ univ from ⟨hxU, mem_univ _⟩)] with q hq
      exact glueH_of_mem hq.1 q.2
    have hx' : x ∈ (chartAt (EuclideanSpace ℝ (Fin m)) x_c).source := by
      rw [← extChartAt_source 𝓘(ℝ, EuclideanSpace ℝ (Fin m))]; exact (mem_ballU.1 hxU).1
    have hφd := ((contMDiffAt_extChartAt' (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin m))) (n := ∞)
      hx').mdifferentiableAt (by simp)).hasMFDerivAt
    have hfst := hasMFDerivAt_fst (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin m))) (I' := 𝓘(ℝ, ℝ))
      (M := M) (M' := ℝ) (x, t)
    have hsnd := hasMFDerivAt_snd (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin m))) (I' := 𝓘(ℝ, ℝ))
      (M := M) (M' := ℝ) (x, t)
    have hpair := (hφd.comp (x, t) hfst).prodMk hsnd
    have hΦd := (hΦ.mdifferentiableAt (by simp)).hasMFDerivAt
      (x := (extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) x_c x, t))
    have hcomp := hΦd.comp (x, t) hpair
    have hH := hcomp.congr_of_eventuallyEq hev
    show Function.Surjective (mfderiv (𝓘(ℝ, EuclideanSpace ℝ (Fin m)).prod 𝓘(ℝ, ℝ))
      𝓘(ℝ, EuclideanSpace ℝ (Fin m)) (glueH hM x_c R (cancelΦ hb c w a ρ c₀) k) (x, t))
    rw [hH.mfderiv]
    -- both factors are surjective
    have hsurj1 := surjective_mfderiv_cancelΦ hb hc.ne' hw ha hρ hρ' c₀ hl
    rw [← hφ] at hsurj1
    have hbij := bijective_mfd_extChartAt (mem_ballU.1 hxU).1
    intro y
    obtain ⟨u, hu⟩ := hsurj1 y
    obtain ⟨a', ha'⟩ := hbij.2 u.1
    refine ⟨(a', u.2), ?_⟩
    show mfderiv (𝓘(ℝ, EuclideanSpace ℝ (Fin m)).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, EuclideanSpace ℝ (Fin m))
      (cancelΦ hb c w a ρ c₀) (extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) x_c x, t)
      (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 𝓘(ℝ, EuclideanSpace ℝ (Fin m))
        (extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) x_c) x a', u.2) = y
    have hpair' : ((mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 𝓘(ℝ, EuclideanSpace ℝ (Fin m))
        (extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) x_c) x a', u.2) :
        EuclideanSpace ℝ (Fin m) × ℝ) = u := Prod.ext ha' rfl
    rw [hpair']
    exact hu
  · have hev := glueH_eventually_eq_of_notMem (Φ := cancelΦ hb c w a ρ c₀) hR hRt
      (cancelΦ_south_of_le (hM := hM) (x_c := x_c) (hb := hb) (hsouth := hsouth) (hw := hw)
        (ha := ha) (haR := haR) (hρ1 := hρ1) (hc₀ := hc₀) (hε₀ := hε₀)) hO hOU hkO hxU t
    have hfst := hasMFDerivAt_fst (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin m))) (I' := 𝓘(ℝ, ℝ))
      (M := M) (M' := ℝ) (x, t)
    have hkd := (hk.mdifferentiableAt (by simp)).hasMFDerivAt (x := x)
    have hH := (hkd.comp (x, t) hfst).congr_of_eventuallyEq hev
    show Function.Surjective (mfderiv (𝓘(ℝ, EuclideanSpace ℝ (Fin m)).prod 𝓘(ℝ, ℝ))
      𝓘(ℝ, EuclideanSpace ℝ (Fin m)) (glueH hM x_c R (cancelΦ hb c w a ρ c₀) k) (x, t))
    rw [hH.mfderiv]
    intro y
    obtain ⟨u, hu⟩ := hkn x hkx y
    exact ⟨(u, 0), hu⟩

end cancelH

end Framed

end Milnor
