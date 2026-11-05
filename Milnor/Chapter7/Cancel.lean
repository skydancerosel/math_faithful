import Milnor.Chapter7.CancelH
import Milnor.Chapter7.ChartSign
import Milnor.Chapter7.Cobordism
import Milnor.Chapter7.ThmBsupp

/-!
# Cancelling two framed points of opposite sign (Milnor §7, p. 51, "cancelling points")

If `F` is a framed `0`-manifold and `x₁, x₂ ∈ F.N` lie in a chart ball `U` (at chart positions
`c₀ ± a • w`) whose closure contains no other point of `F.N`, then `F` with the frames at `x₁, x₂`
replaced by the "standard" frames of the cancelling map (of **chart signs** `1` and `-1`, read in
the chart of the ball) is framed cobordant to `F` with `x₁, x₂` removed.  The cobordism is the
Pontryagin manifold of the cancelling homotopy `H = glueH (cancelΦ …) k`, `k` the Theorem-B map of
`F` supported away from the frontier of `U`.

The sign-free form is `exists_cancel_chartSign`: no orientation of `M`, no positivity hypothesis,
and the two signs are `±1` on the nose rather than `±ε` for a sign `ε` depending on the
orientation.  The oriented form `exists_cancel`, which the signed cancellation machinery of
`Chapter7/CancelStep.lean` consumes, is a short corollary through the bridge
`frameSign_eq_orEps_hub_mul_chartSign` of `Chapter7/ChartSign.lean`: there `ε` reappears as the
orientation factor at the centre of the ball.
-/

open Set Filter Topology Function Module Metric
open scoped ContDiff Manifold RealInnerProductSpace Classical

noncomputable section

namespace Milnor

open Sphere

namespace Framed

variable {K m d : ℕ} {M : Set (EuclideanSpace ℝ (Fin (K + 1)))}
  {hM : IsSliceSubmanifold 𝓘(ℝ, EuclideanSpace ℝ (Fin (K + 1))) (EuclideanSpace ℝ (Fin m))
    (EuclideanSpace ℝ (Fin d)) M} (hMc : IsCompact M) (hne : M.Nonempty)

/-- `basisCLM` of a rescaled tuple. -/
theorem basisCLM_smul (c : ℝ) (b : Fin m → EuclideanSpace ℝ (Fin m)) :
    basisCLM (fun i => c • b i) = c • basisCLM b := by
  ext s
  simp only [basisCLM_apply, smul_apply, Finset.smul_sum, smul_smul, mul_comm]

section ident

variable {x_c : M} {R : ℝ} (hR : 0 < R)
  (hRt : letI := hM.chartedSpace;
    closedBall (extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) x_c x_c) R ⊆
      (extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) x_c).target)
  {b : Fin m → EuclideanSpace ℝ (Fin m)} (hb : LinearIndependent ℝ b) {c : ℝ} (hc : 0 < c)
  {ε₀ : ℝ} (hsouth : ∀ z, ε₀ / 2 ≤ ‖z‖ → collapse hb c z = south)
  {w : EuclideanSpace ℝ (Fin m)} (hw : ‖w‖ = 1) {a : ℝ} (ha : 0 < a) (haR : 8 * a ≤ R)
  {ρ : ℝ → ℝ} (hρ : ContDiff ℝ ∞ ρ) (hρ1 : ∀ t, |ρ t| ≤ 1)
  {c₀ : EuclideanSpace ℝ (Fin m)}
  (hc₀ : letI := hM.chartedSpace; ‖c₀ - extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) x_c x_c‖ < R / 8)
  (hε₀ : ε₀ = 2 * min (3 * R / 8 / 2) ((3 * R / 8) ^ 2 / 4))
  {k : M → Sph m}
  {O : Set M} (hO : IsOpen O) (hOU : closure (ballU hM x_c R) \ ballU hM x_c R ⊆ O)
  (hkO : ∀ z ∈ O, k z = south)

include hc hw in
/-- The preimage of `north` under the slice at time `0` (where `ρ 0 = 1`): the two points
`x₁ = φ⁻¹(c₀ + a • w)`, `x₂ = φ⁻¹(c₀ - a • w)` together with the zeros of `k` off the ball. -/
theorem cancelH_slice_preimage_zero (hρ0 : ρ 0 = 1) {x₁ x₂ : M} (hx₁ : x₁ ∈ ballU hM x_c R)
    (hx₂ : x₂ ∈ ballU hM x_c R)
    (hφ₁ : letI := hM.chartedSpace; extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) x_c x₁ = c₀ + a • w)
    (hφ₂ : letI := hM.chartedSpace;
      extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) x_c x₂ = c₀ - a • w) :
    letI := hM.chartedSpace
    (fun x => glueH hM x_c R (cancelΦ hb c w a ρ c₀) k (x, 0)) ⁻¹' {north} =
      (k ⁻¹' {north} \ ballU hM x_c R) ∪ {x₁, x₂} := by
  letI := hM.chartedSpace
  haveI := hM.isManifold
  ext x
  simp only [mem_preimage, mem_singleton_iff, mem_union, Set.mem_sdiff, mem_insert_iff]
  rw [cancelH_eq_north_iff (hb := hb) (k := k) (hc := hc) (hw := hw) (a := a) (ρ := ρ) (c₀ := c₀)
    0 x, hρ0, mul_one]
  constructor
  · rintro (⟨hxU, l, hφ, hl⟩ | ⟨hxU, hx⟩)
    · right
      rcases sq_eq_sq_iff_eq_or_eq_neg.1 hl with rfl | rfl
      · left
        exact (extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) x_c).injOn (mem_ballU.1 hxU).1
          (mem_ballU.1 hx₁).1 (hφ.trans hφ₁.symm)
      · right
        refine (extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) x_c).injOn (mem_ballU.1 hxU).1
          (mem_ballU.1 hx₂).1 ?_
        rw [hφ, hφ₂, neg_smul, sub_eq_add_neg]
    · left; exact ⟨hx, hxU⟩
  · rintro (⟨hx, hxU⟩ | rfl | rfl)
    · right; exact ⟨hxU, hx⟩
    · left; exact ⟨hx₁, a, hφ₁, rfl⟩
    · left
      refine ⟨hx₂, -a, ?_, by ring⟩
      rw [hφ₂, neg_smul, sub_eq_add_neg]

include hc hw ha in
/-- The preimage of `north` under the slice at time `1` (where `ρ 1 = -1`): no zeros in the ball. -/
theorem cancelH_slice_preimage_one (hρ1' : ρ 1 = -1) :
    letI := hM.chartedSpace
    (fun x => glueH hM x_c R (cancelΦ hb c w a ρ c₀) k (x, 1)) ⁻¹' {north} =
      k ⁻¹' {north} \ ballU hM x_c R := by
  letI := hM.chartedSpace
  haveI := hM.isManifold
  ext x
  simp only [mem_preimage, mem_singleton_iff, Set.mem_sdiff]
  rw [cancelH_eq_north_iff (hb := hb) (k := k) (hc := hc) (hw := hw) (a := a) (ρ := ρ) (c₀ := c₀)
    1 x, hρ1']
  constructor
  · rintro (⟨hxU, l, hφ, hl⟩ | ⟨hxU, hx⟩)
    · exfalso
      nlinarith [sq_nonneg l, pow_pos ha 2]
    · exact ⟨hx, hxU⟩
  · rintro ⟨hx, hxU⟩
    right; exact ⟨hxU, hx⟩

include hR hRt hsouth hw ha haR hρ1 hc₀ hε₀ hO hOU hkO in
/-- Off the chart ball the slice has the frames of `k`. -/
theorem pontV_cancelH_slice_of_notMem (t : ℝ)
    (hf : letI := hM.chartedSpace; haveI := hM.isManifold;
      ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) ∞
        (fun x => glueH hM x_c R (cancelΦ hb c w a ρ c₀) k (x, t)))
    {x : EuclideanSpace ℝ (Fin (K + 1))} (hx : x ∈ M) (hxU : (⟨x, hx⟩ : M) ∉ ballU hM x_c R)
    (hfx : glueH hM x_c R (cancelΦ hb c w a ρ c₀) k (⟨x, hx⟩, t) = north)
    (hkx : k ⟨x, hx⟩ = north) (b' : Fin m → EuclideanSpace ℝ (Fin m)) (i : Fin m) :
    pontV hM hMc hne (fun x => glueH hM x_c R (cancelΦ hb c w a ρ c₀) k (x, t)) north b' i
      ⟨⟨x, hx⟩, hfx⟩ = pontV hM hMc hne k north b' i ⟨⟨x, hx⟩, hkx⟩ := by
  letI := hM.chartedSpace
  haveI := hM.isManifold
  refine pontV_congr hM hMc hne hx hfx hkx ?_ b' i
  exact glueH_slice_eventually_eq_of_notMem (Φ := cancelΦ hb c w a ρ c₀) hR hRt
    (cancelΦ_south_of_le (hM := hM) (x_c := x_c) (hb := hb) (hsouth := hsouth) (hw := hw)
      (ha := ha) (haR := haR) (hρ1 := hρ1) (hc₀ := hc₀) (hε₀ := hε₀)) hO hOU hkO hxU t

include hc hw hρ in
/-- **The chart sign of the frame at a zero of the cancelling map.**  When `basisCLM b = id`, the
frame produced by the slice at a zero `φ⁻¹(c₀ + l • w)`, read in the chart of the ball, has
determinant of sign `sgn l`.  No orientation of `M`, and no positivity hypothesis: the factor
`ε = orSign (oM.or x_c) (stdOr m) id` that the oriented version carried was exactly the orientation
factor at the centre of the ball, and it disappears with the orientation. -/
theorem chartSign_cancelH_slice (t : ℝ)
    (hf : letI := hM.chartedSpace; haveI := hM.isManifold;
      ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) ∞
        (fun x => glueH hM x_c R (cancelΦ hb c w a ρ c₀) k (x, t)))
    (hn : letI := hM.chartedSpace; haveI := hM.isManifold;
      IsRegularValue 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 𝓘(ℝ, EuclideanSpace ℝ (Fin m))
        (fun x => glueH hM x_c R (cancelΦ hb c w a ρ c₀) k (x, t)) north)
    {x_t : M} (hx_t : x_t ∈ ballU hM x_c R) {l : ℝ} (hl : l ^ 2 = a ^ 2 * ρ t)
    (hφ : letI := hM.chartedSpace; extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) x_c x_t = c₀ + l • w)
    (hfx : glueH hM x_c R (cancelΦ hb c w a ρ c₀) k (x_t, t) = north)
    (hb1 : basisCLM b = ContinuousLinearMap.id ℝ _) :
    chartSign hM x_c x_t (fun i => pontV hM hMc hne
      (fun x => glueH hM x_c R (cancelΦ hb c w a ρ c₀) k (x, t)) north (fun i => c • b i) i
        ⟨x_t, hfx⟩) = sgn l := by
  letI := hM.chartedSpace
  haveI := hM.isManifold
  set f : M → Sph m := fun x => glueH hM x_c R (cancelΦ hb c w a ρ c₀) k (x, t) with hfdef
  set D := mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) f x_t with hDdef
  have hD : D = ((c • basisCLM b).comp (Tcan w l)).comp
      (mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 𝓘(ℝ, EuclideanSpace ℝ (Fin m))
        (extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) x_c) x_t) :=
    mfd_cancelH_slice_of_mem (hb := hb) (c := c) (k := k) (hw := hw) (hρ := hρ) hx_t hl hφ
  set w₁ : Fin m → EuclideanSpace ℝ (Fin m) :=
    fun i => chartCoord hM x_t (pontV hM hMc hne f north (fun i => c • b i) i ⟨x_t, hfx⟩) with hw₁
  -- the chart derivative carries the chart coordinates of the frame to `c • b`
  have hDw : ∀ i, D (w₁ i) = c • b i := by
    intro i
    have h1 : At hM hMc hne f north x_t.1 (pontV hM hMc hne f north (fun i => c • b i) i
        ⟨x_t, hfx⟩) = c • b i := At_pontV hM hMc hne hf hn (fun i => c • b i) i ⟨x_t, hfx⟩
    rw [← mfd_val_chartCoord hM (pontV_tangent hM hMc hne hf hn (fun i => c • b i) i ⟨x_t, hfx⟩),
      At_apply_mfd_val hM hMc hne hf hfx] at h1
    exact h1
  have hcomp : D.comp (basisCLM w₁) =
      c • ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin m)) := by
    rw [basisCLM_comp_eq hDw, basisCLM_smul, hb1]
  -- the signs of the two Euclidean factors
  have hid : ((c • ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin m)) :
      EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m)) :
      EuclideanSpace ℝ (Fin m) →ₗ[ℝ] EuclideanSpace ℝ (Fin m)) = c • LinearMap.id := rfl
  have hS1 : orSign (stdOr m) (stdOr m)
      (c • ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin m))) = 1 := by
    rw [orSign_self_eq_sgn_det finrank_E, hid, LinearMap.det_smul, LinearMap.det_id, mul_one]
    exact sgn_pos (pow_pos hc _)
  have hS2 : orSign (stdOr m) (stdOr m) ((c • basisCLM b).comp (Tcan w l)) = sgn l := by
    rw [orSign_self_eq_sgn_det finrank_E, ContinuousLinearMap.toLinearMap_comp, LinearMap.det_comp,
      hb1, hid, LinearMap.det_smul, LinearMap.det_id, mul_one, det_Tcan hw, sgn_mul,
      sgn_pos (pow_pos hc _), one_mul, sgn_mul, sgn_pos two_pos, one_mul]
  -- multiplicativity: everything is read against the standard orientation
  have hmul1 := orSign_comp finrank_E finrank_E (stdOr m) (stdOr m) (stdOr m) (basisCLM w₁) D
  rw [hcomp, hS1] at hmul1
  have hmul2 := orSign_comp finrank_E finrank_E (stdOr m) (stdOr m) (stdOr m)
    (mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 𝓘(ℝ, EuclideanSpace ℝ (Fin m))
      (extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) x_c) x_t) ((c • basisCLM b).comp (Tcan w l))
  rw [← hD, hS2] at hmul2
  rw [hmul2] at hmul1
  -- the chart sign is the product of the two remaining factors
  have hgoal : chartSign hM x_c x_t
      (fun i => pontV hM hMc hne f north (fun i => c • b i) i ⟨x_t, hfx⟩) =
      orSign (stdOr m) (stdOr m)
        (mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 𝓘(ℝ, EuclideanSpace ℝ (Fin m))
          (extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) x_c) x_t) *
        orSign (stdOr m) (stdOr m) (basisCLM w₁) := by
    rw [chartSign_eq_orSign, chartFrameCLM_eq, hw₁]
    exact orSign_comp finrank_E finrank_E (stdOr m) (stdOr m) (stdOr m) _ _
  -- `sgn l * chartSign = 1`, and both factors are `±1`
  have hmul1' : sgn l * (orSign (stdOr m) (stdOr m)
      (mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 𝓘(ℝ, EuclideanSpace ℝ (Fin m))
        (extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) x_c) x_t) *
      orSign (stdOr m) (stdOr m) (basisCLM w₁)) = 1 := by
    rw [← mul_assoc]; exact hmul1.symm
  rw [hgoal]
  rcases Int.eq_one_or_neg_one_of_mul_eq_one' hmul1' with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
    exact h2.trans h1.symm

end ident

include hMc hne in
/-- **Cancelling two framed points of opposite chart sign.**  The sign-free form: the two frames
produced at `x₁` and `x₂` have chart signs `1` and `-1` relative to the centre of the ball.  No
orientation of `M`, no positivity hypothesis. -/
theorem exists_cancel_chartSign (hm : 0 < m)
    (F : FramedSub hM 0 m) (x_c : M) {R : ℝ} (hR : 0 < R)
    (hRt : letI := hM.chartedSpace;
      closedBall (extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) x_c x_c) R ⊆
        (extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) x_c).target)
    {c₀ : EuclideanSpace ℝ (Fin m)}
    (hc₀ : letI := hM.chartedSpace; ‖c₀ - extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) x_c x_c‖ < R / 8)
    {w : EuclideanSpace ℝ (Fin m)} (hw : ‖w‖ = 1) {a : ℝ} (ha : 0 < a) (haR : 8 * a ≤ R)
    {x₁ x₂ : M} (hx₁ : x₁ ∈ F.N) (hx₂ : x₂ ∈ F.N)
    (hx₁s : letI := hM.chartedSpace; x₁ ∈ (extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) x_c).source)
    (hx₂s : letI := hM.chartedSpace; x₂ ∈ (extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) x_c).source)
    (hφ₁ : letI := hM.chartedSpace; extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) x_c x₁ = c₀ + a • w)
    (hφ₂ : letI := hM.chartedSpace; extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) x_c x₂ = c₀ - a • w)
    (hFU : ∀ x ∈ F.N, x ≠ x₁ → x ≠ x₂ → x ∉ closure (ballU hM x_c R)) :
    letI := hM.chartedSpace
    ∃ F₀ F' : FramedSub hM 0 m,
      F₀.N = F.N ∧
      (∀ i x (hx : x ∈ F.N) (h1 : x ≠ x₁) (h2 : x ≠ x₂) (hx' : x ∈ F₀.N),
        F₀.v i ⟨x, hx'⟩ = F.v i ⟨x, hx⟩) ∧
      (∀ hx' : x₁ ∈ F₀.N, chartSign hM x_c x₁ (fun i => F₀.v i ⟨x₁, hx'⟩) = 1) ∧
      (∀ hx' : x₂ ∈ F₀.N, chartSign hM x_c x₂ (fun i => F₀.v i ⟨x₂, hx'⟩) = -1) ∧
      F'.N = F.N \ {x₁, x₂} ∧
      (∀ i x (hx : x ∈ F.N) (h1 : x ≠ x₁) (h2 : x ≠ x₂) (hx' : x ∈ F'.N),
        F'.v i ⟨x, hx'⟩ = F.v i ⟨x, hx⟩) ∧
      FramedCobordant hM F₀ F' := by
  letI := hM.chartedSpace
  haveI := hM.isManifold
  haveI : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  set φ := extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) x_c with hφdef
  have hsub : ∀ r, r ≤ R → ballU hM x_c r ⊆ ballU hM x_c R := fun r hr z hz => by
    rw [mem_ballU] at hz ⊢; exact ⟨hz.1, lt_of_lt_of_le hz.2 hr⟩
  -- the two points lie in the ball of radius `R / 4`
  have haw : ‖a • w‖ = a := by
    rw [norm_smul, hw, mul_one, Real.norm_eq_abs, abs_of_pos ha]
  have hx₁4 : ‖φ x₁ - φ x_c‖ < R / 4 := by
    rw [hφ₁]
    calc ‖c₀ + a • w - φ x_c‖ = ‖(c₀ - φ x_c) + a • w‖ := by congr 1; abel
      _ ≤ ‖c₀ - φ x_c‖ + ‖a • w‖ := norm_add_le _ _
      _ < R / 4 := by rw [haw]; linarith
  have hx₂4 : ‖φ x₂ - φ x_c‖ < R / 4 := by
    rw [hφ₂]
    calc ‖c₀ - a • w - φ x_c‖ = ‖(c₀ - φ x_c) - a • w‖ := by congr 1; abel
      _ ≤ ‖c₀ - φ x_c‖ + ‖a • w‖ := norm_sub_le _ _
      _ < R / 4 := by rw [haw]; linarith
  have hx₁U : x₁ ∈ ballU hM x_c R := mem_ballU.2 ⟨hx₁s, by linarith⟩
  have hx₂U : x₂ ∈ ballU hM x_c R := mem_ballU.2 ⟨hx₂s, by linarith⟩
  have hx₁U2 : x₁ ∈ ballU hM x_c (R / 2) := mem_ballU.2 ⟨hx₁s, by linarith⟩
  have hx₂U2 : x₂ ∈ ballU hM x_c (R / 2) := mem_ballU.2 ⟨hx₂s, by linarith⟩
  -- the collapse basis and scale
  set b : Fin m → EuclideanSpace ℝ (Fin m) := fun i => EuclideanSpace.single i 1 with hbdef
  have hb : LinearIndependent ℝ b := by
    have := (EuclideanSpace.basisFun (Fin m) ℝ).toBasis.linearIndependent
    have h3 : ⇑((EuclideanSpace.basisFun (Fin m) ℝ).toBasis) = b := by
      funext i; simp [hbdef]
    rw [h3] at this; exact this
  have hb1 : basisCLM b = ContinuousLinearMap.id ℝ _ := basisCLM_single_eq_id
  -- the time profile
  obtain ⟨ρ, hρ, hρ0, hρ1', hρb, hρ'⟩ := exists_rho (ε := 1 / 4) (by norm_num) (by norm_num)
  have hR' : 0 < 2 * min (3 * R / 8 / 2) ((3 * R / 8) ^ 2 / 4) := by positivity
  obtain ⟨c₁, hc₁, hc₁s⟩ := exists_scale_all hb hR'
  -- the Theorem-B map supported away from the frontier of the ball
  set W : Set M := (closure (ballU hM x_c R))ᶜ ∪ ballU hM x_c (R / 2) with hWdef
  have hW : IsOpen W := isClosed_closure.isOpen_compl.union (isOpen_ballU _ _)
  have hNW : F.N ⊆ W := by
    intro x hx
    by_cases h1 : x = x₁
    · right; rw [h1]; exact hx₁U2
    by_cases h2 : x = x₂
    · right; rw [h2]; exact hx₂U2
    left; exact hFU x hx h1 h2
  obtain ⟨k, hk, hkn, c, hc, hcb, hc₁c, hkF, Kc, hKc, hKcW, hkS⟩ :=
    exists_map_of_framedSub_subset hM hMc hne F b hb W hW hNW c₁
  have hsouth : ∀ z, 2 * min (3 * R / 8 / 2) ((3 * R / 8) ^ 2 / 4) / 2 ≤ ‖z‖ →
      collapse hb c z = south := hc₁s c hc₁c
  have hO : IsOpen Kcᶜ := hKc.isClosed.isOpen_compl
  have hOU : closure (ballU hM x_c R) \ ballU hM x_c R ⊆ Kcᶜ := by
    rintro z ⟨hz1, hz2⟩ hzK
    rcases hKcW hzK with h | h
    · exact h hz1
    · exact hz2 (hsub _ (by linarith) h)
  have hkO : ∀ z ∈ Kcᶜ, k z = south := fun z hz => hkS z hz
  have hkN : k ⁻¹' {north} = F.N := congrArg FramedSub.N hkF
  -- the homotopy
  set H := glueH hM x_c R (cancelΦ hb c w a ρ c₀) k with hHdef
  have hH : ContMDiff (𝓘(ℝ, EuclideanSpace ℝ (Fin m)).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, EuclideanSpace ℝ (Fin m))
      ∞ H :=
    contMDiff_cancelH (hM := hM) (x_c := x_c) (hR := hR) (hRt := hRt) (hb := hb)
      (hsouth := hsouth) (hw := hw) (ha := ha) (haR := haR) (hρ := hρ) (hρ1 := hρb) (hc₀ := hc₀)
      (hε₀ := rfl) (hk := hk) (hO := hO) (hOU := hOU) (hkO := hkO)
  have hHn : IsRegularValue (𝓘(ℝ, EuclideanSpace ℝ (Fin m)).prod 𝓘(ℝ, ℝ))
      𝓘(ℝ, EuclideanSpace ℝ (Fin m)) H north :=
    isRegularValue_cancelH (hR := hR) (hRt := hRt) (hb := hb) (hc := hc)
      (hsouth := hsouth) (hw := hw) (ha := ha) (haR := haR) (hρ := hρ) (hρ1 := hρb) (hρ' := hρ')
      (hc₀ := hc₀) (hε₀ := rfl) (hk := hk) (hkn := hkn) (hO := hO) (hOU := hOU) (hkO := hkO)
  have hslice : ∀ t, ρ t ≠ 0 → IsRegularValue 𝓘(ℝ, EuclideanSpace ℝ (Fin m))
      𝓘(ℝ, EuclideanSpace ℝ (Fin m)) (fun x => H (x, t)) north := fun t ht =>
    isRegularValue_cancelH_slice (hR := hR) (hRt := hRt) (hb := hb) (hc := hc)
      (hsouth := hsouth) (hw := hw) (ha := ha) (haR := haR) (hρ := hρ) (hρ1 := hρb)
      (hc₀ := hc₀) (hε₀ := rfl) (hkn := hkn) (hO := hO) (hOU := hOU) (hkO := hkO) t ht
  have hρ00 : ρ 0 = 1 := hρ0 0 (by norm_num)
  have hρ11 : ρ 1 = -1 := hρ1' 1 (by norm_num)
  have hs0 := hslice 0 (by rw [hρ00]; exact one_ne_zero)
  have hs1 := hslice 1 (by rw [hρ11]; norm_num)
  have hH0 : ∀ x t, t ≤ 1 / 4 → H (x, t) = H (x, 0) := by
    intro x t ht
    by_cases hx : x ∈ ballU hM x_c R
    · rw [hHdef, glueH_of_mem hx, glueH_of_mem hx]
      exact cancelΦ_congr_time hb c w a c₀ (by rw [hρ0 t ht, hρ00]) _
    · rw [hHdef, glueH_of_notMem hx, glueH_of_notMem hx]
  have hH1 : ∀ x t, 1 - 1 / 4 ≤ t → H (x, t) = H (x, 1) := by
    intro x t ht
    by_cases hx : x ∈ ballU hM x_c R
    · rw [hHdef, glueH_of_mem hx, glueH_of_mem hx]
      exact cancelΦ_congr_time hb c w a c₀ (by rw [hρ1' t ht, hρ11]) _
    · rw [hHdef, glueH_of_notMem hx, glueH_of_notMem hx]
  have hf0 : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) ∞
      (fun x => H (x, 0)) := hH.comp (contMDiff_id.prodMk contMDiff_const)
  have hf1 : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) ∞
      (fun x => H (x, 1)) := hH.comp (contMDiff_id.prodMk contMDiff_const)
  have hcob := framedCobordant_of_homotopy hM hMc hne (zero_add m) (ε := 1 / 4) (by norm_num)
    (by norm_num) hH hHn hH0 hH1 hf0 hs0 hf1 hs1 (fun i => c • b i) hcb
  -- the two ends
  have hpre0 := cancelH_slice_preimage_zero (hb := hb) (k := k) (hc := hc) (hw := hw) (ρ := ρ)
    (c₀ := c₀) hρ00 hx₁U hx₂U hφ₁ hφ₂
  have hpre1 := cancelH_slice_preimage_one (hM := hM) (x_c := x_c) (R := R) (hb := hb) (k := k)
    (hc := hc) (hw := hw) (ha := ha) (ρ := ρ) (c₀ := c₀) hρ11
  rw [hkN] at hpre0 hpre1
  have hN0 : (fun x => H (x, 0)) ⁻¹' {north} = F.N := by
    rw [hpre0]
    ext x
    simp only [mem_union, Set.mem_sdiff, mem_insert_iff, mem_singleton_iff]
    constructor
    · rintro (⟨hx, -⟩ | rfl | rfl)
      · exact hx
      · exact hx₁
      · exact hx₂
    · intro hx
      by_cases h1 : x = x₁
      · right; left; exact h1
      by_cases h2 : x = x₂
      · right; right; exact h2
      left; exact ⟨hx, fun hU => hFU x hx h1 h2 (subset_closure hU)⟩
  have hN1 : (fun x => H (x, 1)) ⁻¹' {north} = F.N \ {x₁, x₂} := by
    rw [hpre1]
    ext x
    simp only [Set.mem_sdiff, mem_insert_iff, mem_singleton_iff, not_or]
    constructor
    · rintro ⟨hx, hxU⟩
      exact ⟨hx, fun h => hxU (h ▸ hx₁U), fun h => hxU (h ▸ hx₂U)⟩
    · rintro ⟨hx, h1, h2⟩
      exact ⟨hx, fun hU => hFU x hx h1 h2 (subset_closure hU)⟩
  -- the frames off `{x₁, x₂}`
  have hoff : ∀ t (hf : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) ∞
      (fun x => H (x, t))) i x (hx : x ∈ F.N) (h1 : x ≠ x₁) (h2 : x ≠ x₂)
      (hfx : H (x, t) = north),
      pontV hM hMc hne (fun x => H (x, t)) north (fun i => c • b i) i ⟨x, hfx⟩ = F.v i ⟨x, hx⟩ := by
    intro t hf i x hx h1 h2 hfx
    have hxU : x ∉ ballU hM x_c R := fun hU => hFU x hx h1 h2 (subset_closure hU)
    have hkx : k x = north := by rw [← mem_singleton_iff, ← mem_preimage, hkN]; exact hx
    have h3 := pontV_cancelH_slice_of_notMem hMc hne (hb := hb) (k := k) (hR := hR) (hRt := hRt)
      (hsouth := hsouth) (hw := hw) (ha := ha) (haR := haR) (hρ1 := hρb) (hc₀ := hc₀) (hε₀ := rfl)
      (hO := hO) (hOU := hOU) (hkO := hkO) t hf x.2 hxU hfx hkx (fun i => c • b i) i
    have h4 := FramedSub.v_congr hkF i ⟨x, hkx⟩
    simp only at h4
    exact h3.trans h4
  -- the two framed `0`-manifolds
  refine ⟨pontryagin hM hMc hne hf0 hs0 (zero_add m) (fun i => c • b i) hcb,
    pontryagin hM hMc hne hf1 hs1 (zero_add m) (fun i => c • b i) hcb, hN0, ?_, ?_, ?_, hN1, ?_,
    hcob⟩
  · intro i x hx h1 h2 hx'
    exact hoff 0 hf0 i x hx h1 h2 hx'
  · intro hx'
    have h := chartSign_cancelH_slice hMc hne (hb := hb) (hc := hc) (hw := hw)
      (hρ := hρ) (k := k) 0 hf0 hs0 hx₁U (l := a) (by rw [hρ00, mul_one]) hφ₁ hx' hb1
    rw [sgn_pos ha] at h
    exact h
  · intro hx'
    have h := chartSign_cancelH_slice hMc hne (hb := hb) (hc := hc) (hw := hw)
      (hρ := hρ) (k := k) 0 hf0 hs0 hx₂U (l := -a) (by rw [hρ00, mul_one, neg_sq])
      (by rw [hφ₂, neg_smul, sub_eq_add_neg]) hx' hb1
    rw [sgn_neg (neg_lt_zero.2 ha)] at h
    exact h
  · intro i x hx h1 h2 hx'
    exact hoff 1 hf1 i x hx h1 h2 hx'

include hMc hne in
/-- **Cancelling two framed points of opposite sign**, in the oriented form consumed by the signed
cancellation machinery of `Chapter7/CancelStep.lean`.  It is `exists_cancel_chartSign` read through
the bridge `frameSign_eq_orEps_hub_mul_chartSign`: on a ball on which the chart at `x_c` is
orientation-preserving, the frame sign is the chart sign times the orientation factor at the
centre, and that factor is the `ε = orSign (oM.or x_c) (stdOr m) id` of the statement. -/
theorem exists_cancel (hm : 0 < m)
    (oM : letI := hM.chartedSpace; Orient 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) M m)
    (F : FramedSub hM 0 m) (x_c : M) {R : ℝ} (hR : 0 < R)
    (hRt : letI := hM.chartedSpace;
      closedBall (extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) x_c x_c) R ⊆
        (extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) x_c).target)
    (hpos : letI := hM.chartedSpace; haveI := hM.isManifold;
      ∀ z ∈ ballU hM x_c R, orSign (oM.or z) (oM.or x_c) (mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin m))
        𝓘(ℝ, EuclideanSpace ℝ (Fin m)) (extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) x_c) z) = 1)
    {c₀ : EuclideanSpace ℝ (Fin m)}
    (hc₀ : letI := hM.chartedSpace; ‖c₀ - extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) x_c x_c‖ < R / 8)
    {w : EuclideanSpace ℝ (Fin m)} (hw : ‖w‖ = 1) {a : ℝ} (ha : 0 < a) (haR : 8 * a ≤ R)
    {x₁ x₂ : M} (hx₁ : x₁ ∈ F.N) (hx₂ : x₂ ∈ F.N)
    (hx₁s : letI := hM.chartedSpace; x₁ ∈ (extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) x_c).source)
    (hx₂s : letI := hM.chartedSpace; x₂ ∈ (extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) x_c).source)
    (hφ₁ : letI := hM.chartedSpace; extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) x_c x₁ = c₀ + a • w)
    (hφ₂ : letI := hM.chartedSpace; extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) x_c x₂ = c₀ - a • w)
    (hFU : ∀ x ∈ F.N, x ≠ x₁ → x ≠ x₂ → x ∉ closure (ballU hM x_c R)) :
    letI := hM.chartedSpace
    ∃ F₀ F' : FramedSub hM 0 m,
      F₀.N = F.N ∧
      (∀ i x (hx : x ∈ F.N) (h1 : x ≠ x₁) (h2 : x ≠ x₂) (hx' : x ∈ F₀.N),
        F₀.v i ⟨x, hx'⟩ = F.v i ⟨x, hx⟩) ∧
      (∀ hx' : x₁ ∈ F₀.N, frameSign hM oM (fun i => F₀.v i ⟨x₁, hx'⟩) x₁ =
        orSign (oM.or x_c) (stdOr m) (ContinuousLinearMap.id ℝ _)) ∧
      (∀ hx' : x₂ ∈ F₀.N, frameSign hM oM (fun i => F₀.v i ⟨x₂, hx'⟩) x₂ =
        -orSign (oM.or x_c) (stdOr m) (ContinuousLinearMap.id ℝ _)) ∧
      F'.N = F.N \ {x₁, x₂} ∧
      (∀ i x (hx : x ∈ F.N) (h1 : x ≠ x₁) (h2 : x ≠ x₂) (hx' : x ∈ F'.N),
        F'.v i ⟨x, hx'⟩ = F.v i ⟨x, hx⟩) ∧
      FramedCobordant hM F₀ F' := by
  letI := hM.chartedSpace
  haveI := hM.isManifold
  obtain ⟨F₀, F', hN₀, hoff₀, hs₁, hs₂, hN', hoff', hcob⟩ :=
    exists_cancel_chartSign hMc hne hm F x_c hR hRt hc₀ hw ha haR hx₁ hx₂ hx₁s hx₂s hφ₁ hφ₂ hFU
  -- the two points lie in the ball, so the bridge applies at both
  have haw : ‖a • w‖ = a := by
    rw [norm_smul, hw, mul_one, Real.norm_eq_abs, abs_of_pos ha]
  have hx₁U : x₁ ∈ ballU hM x_c R := by
    refine mem_ballU.2 ⟨hx₁s, ?_⟩
    rw [hφ₁]
    calc ‖c₀ + a • w - extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) x_c x_c‖
        = ‖(c₀ - extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) x_c x_c) + a • w‖ := by congr 1; abel
      _ ≤ ‖c₀ - extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) x_c x_c‖ + ‖a • w‖ := norm_add_le _ _
      _ < R := by rw [haw]; linarith
  have hx₂U : x₂ ∈ ballU hM x_c R := by
    refine mem_ballU.2 ⟨hx₂s, ?_⟩
    rw [hφ₂]
    calc ‖c₀ - a • w - extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) x_c x_c‖
        = ‖(c₀ - extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) x_c x_c) - a • w‖ := by congr 1; abel
      _ ≤ ‖c₀ - extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) x_c x_c‖ + ‖a • w‖ := norm_sub_le _ _
      _ < R := by rw [haw]; linarith
  -- the orientation factor at the centre, read the other way round
  have hε : orEps hM oM x_c = orSign (oM.or x_c) (stdOr m)
      (ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin m))) :=
    orSign_symm finrank_E _ _ Function.bijective_id
  refine ⟨F₀, F', hN₀, hoff₀, fun hx' => ?_, fun hx' => ?_, hN', hoff', hcob⟩
  · rw [frameSign_eq_orEps_hub_mul_chartSign hM oM (hpos x₁ hx₁U), hs₁ hx', mul_one, hε]
  · rw [frameSign_eq_orEps_hub_mul_chartSign hM oM (hpos x₂ hx₂U), hs₂ hx', hε]
    ring

end Framed

end Milnor
