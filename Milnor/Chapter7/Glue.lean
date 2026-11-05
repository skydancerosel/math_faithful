import Milnor.Chapter7.ThmBsupp
import Milnor.Chapter7.Hopf0

/-!
# Gluing a chart-local homotopy into a map (tools for the Hopf theorem)

Two tools used to move and cancel framed points inside a chart ball.

* The Pontryagin framing at `x` depends only on the germ of the map at `x`
  (`At_congr`, `pontV_congr`).
* Given a chart `φ = extChartAt x_c` of `M`, a ball `U = φ⁻¹(B(c, R))`, a smooth family
  `Φ : ℝᵐ × ℝ → Sᵐ` which is `south` for `‖s - c‖ ≥ R/2`, and a smooth map `k : M → Sᵐ` which is
  `south` near the frontier of `U`, the map `H(x, t) = Φ(φ x, t)` on `U`, `H(x, t) = k x` off `U`
  is smooth (`glueH`, `contMDiff_glueH`), with derivatives computable on `U` and off `closure U`.
-/

open Set Filter Topology Function Module Metric
open scoped ContDiff Manifold RealInnerProductSpace Classical

noncomputable section

namespace Milnor

open Sphere

namespace Framed

variable {K m w : ℕ} {M : Set (EuclideanSpace ℝ (Fin (K + 1)))}
  (hM : IsSliceSubmanifold 𝓘(ℝ, EuclideanSpace ℝ (Fin (K + 1))) (EuclideanSpace ℝ (Fin m))
    (EuclideanSpace ℝ (Fin w)) M) (hMc : IsCompact M) (hne : M.Nonempty)

/-! ### The framing depends only on the germ -/

section germ

variable {p : ℕ} {f g : M → Sph p} {y : Sph p}

theorem At_congr {x : M} (hfg : letI := hM.chartedSpace; ∀ᶠ z in 𝓝 x, f z = g z) :
    At hM hMc hne f y x.1 = At hM hMc hne g y x.1 := by
  letI := hM.chartedSpace
  haveI := hM.isManifold
  unfold At
  apply Filter.EventuallyEq.fderiv_eq
  have hx0 : infDist x.1 M < Tub.tubε hM hMc hne := by
    rw [infDist_zero_of_mem x.2]; exact Tub.tubε_pos hM hMc hne
  have hc : ContinuousAt (Tub.tubr hM hMc hne) x.1 := by
    rw [IsInducing.subtypeVal.continuousAt_iff]
    exact ((Tub.tubr_spec hM hMc hne).2.2.2.1 x.1 hx0).continuousAt
  have hxx : Tub.tubr hM hMc hne x.1 = x :=
    Subtype.ext ((Tub.tubr_spec hM hMc hne).2.2.1 x.1 x.2)
  have hc' : Tendsto (Tub.tubr hM hMc hne) (𝓝 x.1) (𝓝 x) := by
    have h := hc; rw [ContinuousAt, hxx] at h; exact h
  have hev : ∀ᶠ z in 𝓝 x.1, f (Tub.tubr hM hMc hne z) = g (Tub.tubr hM hMc hne z) :=
    hc'.eventually hfg
  filter_upwards [hev] with z hz
  simp only [Ft, hz]

theorem pontV_congr {x : EuclideanSpace ℝ (Fin (K + 1))} (hx : x ∈ M) (hfx : f ⟨x, hx⟩ = y)
    (hgx : g ⟨x, hx⟩ = y)
    (hfg : letI := hM.chartedSpace; ∀ᶠ z in 𝓝 (⟨x, hx⟩ : M), f z = g z)
    (b : Fin p → EuclideanSpace ℝ (Fin p)) (i : Fin p) :
    pontV hM hMc hne f y b i ⟨⟨x, hx⟩, hfx⟩ = pontV hM hMc hne g y b i ⟨⟨x, hx⟩, hgx⟩ := by
  unfold pontV
  rw [At_congr hM hMc hne hfg]

end germ

/-! ### Chart balls -/

/-- The chart ball `φ⁻¹(B(φ x_c, R))` for `φ = extChartAt x_c`. -/
def ballU (x_c : M) (R : ℝ) : Set M :=
  letI := hM.chartedSpace
  (extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) x_c).source ∩
    (extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) x_c) ⁻¹'
      ball (extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) x_c x_c) R

variable {hM}

theorem mem_ballU {x_c : M} {R : ℝ} {z : M} :
    letI := hM.chartedSpace
    z ∈ ballU hM x_c R ↔ z ∈ (extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) x_c).source ∧
      ‖extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) x_c z -
        extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) x_c x_c‖ < R := by
  letI := hM.chartedSpace
  simp only [ballU, mem_inter_iff, mem_preimage, mem_ball, dist_eq_norm]

theorem isOpen_ballU (x_c : M) (R : ℝ) : IsOpen (ballU hM x_c R) := by
  letI := hM.chartedSpace
  haveI := hM.isManifold
  exact (continuousOn_extChartAt x_c).isOpen_inter_preimage (isOpen_extChartAt_source x_c) isOpen_ball

theorem x_c_mem_ballU (x_c : M) {R : ℝ} (hR : 0 < R) : x_c ∈ ballU hM x_c R := by
  letI := hM.chartedSpace
  rw [mem_ballU]
  exact ⟨mem_extChartAt_source x_c, by rw [sub_self, norm_zero]; exact hR⟩

/-- The "annulus" `{x ∈ source | r < ‖φ x - c‖}` is open. -/
theorem isOpen_annulus (x_c : M) (r : ℝ) :
    letI := hM.chartedSpace
    IsOpen {z : M | z ∈ (extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) x_c).source ∧
      r < ‖extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) x_c z -
        extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) x_c x_c‖} := by
  letI := hM.chartedSpace
  haveI := hM.isManifold
  have : {z : M | z ∈ (extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) x_c).source ∧
      r < ‖extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) x_c z -
        extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) x_c x_c‖} =
      (extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) x_c).source ∩
        (extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) x_c) ⁻¹'
          {s | r < ‖s - extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) x_c x_c‖} := rfl
  rw [this]
  refine (continuousOn_extChartAt x_c).isOpen_inter_preimage (isOpen_extChartAt_source x_c) ?_
  exact isOpen_lt continuous_const (continuous_id.sub continuous_const).norm

/-- If the closed ball `closedBall c R` lies in the chart target, the closure of the chart ball
consists of points of the chart source with `‖φ z - c‖ ≤ R`. -/
theorem closure_ballU_subset (x_c : M) {R : ℝ}
    (hRt : letI := hM.chartedSpace;
      closedBall (extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) x_c x_c) R ⊆
        (extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) x_c).target) :
    letI := hM.chartedSpace
    closure (ballU hM x_c R) ⊆ {z : M | z ∈ (extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) x_c).source ∧
      ‖extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) x_c z -
        extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) x_c x_c‖ ≤ R} := by
  letI := hM.chartedSpace
  haveI := hM.isManifold
  set φ := extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) x_c with hφ
  set c := φ x_c
  -- the compact set `φ.symm '' closedBall c R` contains `U` and is closed
  have hKc : IsCompact (φ.symm '' closedBall c R) :=
    (isCompact_closedBall c R).image_of_continuousOn
      ((continuousOn_extChartAt_symm x_c).mono hRt)
  have hUK : ballU hM x_c R ⊆ φ.symm '' closedBall c R := by
    intro z hz
    rw [mem_ballU] at hz
    refine ⟨φ z, ?_, φ.left_inv hz.1⟩
    rw [mem_closedBall, dist_eq_norm]; exact hz.2.le
  have hKsub : φ.symm '' closedBall c R ⊆ {z : M | z ∈ φ.source ∧ ‖φ z - c‖ ≤ R} := by
    rintro _ ⟨s, hs, rfl⟩
    have hst : s ∈ φ.target := hRt hs
    refine ⟨φ.map_target hst, ?_⟩
    rw [φ.right_inv hst, ← dist_eq_norm]; exact mem_closedBall.1 hs
  exact (closure_minimal hUK hKc.isClosed).trans hKsub

/-- A point of the closure of the chart ball not in it lies in the chart source at distance `≥ R`
from the centre. -/
theorem frontier_ballU (x_c : M) {R : ℝ}
    (hRt : letI := hM.chartedSpace;
      closedBall (extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) x_c x_c) R ⊆
        (extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) x_c).target)
    {z : M} (hz : z ∈ closure (ballU hM x_c R)) (hz' : z ∉ ballU hM x_c R) :
    letI := hM.chartedSpace
    z ∈ (extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) x_c).source ∧
      R ≤ ‖extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) x_c z -
        extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) x_c x_c‖ := by
  letI := hM.chartedSpace
  have h := closure_ballU_subset x_c hRt hz
  refine ⟨h.1, le_of_not_gt fun hlt => hz' ?_⟩
  rw [mem_ballU]; exact ⟨h.1, hlt⟩

/-! ### The glued homotopy -/

variable (hM) in
/-- `H(x, t) = Φ(φ x, t)` for `x ∈ U`, `H(x, t) = k x` otherwise. -/
def glueH (x_c : M) (R : ℝ) (Φ : EuclideanSpace ℝ (Fin m) × ℝ → Sph m) (k : M → Sph m)
    (q : M × ℝ) : Sph m :=
  letI := hM.chartedSpace
  if q.1 ∈ ballU hM x_c R then Φ (extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) x_c q.1, q.2)
  else k q.1

variable {x_c : M} {R : ℝ} {Φ : EuclideanSpace ℝ (Fin m) × ℝ → Sph m} {k : M → Sph m}

theorem glueH_of_mem {z : M} (hz : z ∈ ballU hM x_c R) (t : ℝ) :
    letI := hM.chartedSpace
    glueH hM x_c R Φ k (z, t) = Φ (extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) x_c z, t) := by
  simp [glueH, hz]

theorem glueH_of_notMem {z : M} (hz : z ∉ ballU hM x_c R) (t : ℝ) :
    glueH hM x_c R Φ k (z, t) = k z := by
  simp [glueH, hz]

section smooth

variable (hR : 0 < R)
  (hRt : letI := hM.chartedSpace;
      closedBall (extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) x_c x_c) R ⊆
        (extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) x_c).target)
  (hΦ : ContMDiff (𝓘(ℝ, EuclideanSpace ℝ (Fin m)).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) ∞ Φ)
  (hΦs : letI := hM.chartedSpace; ∀ s t, R / 2 ≤ ‖s - extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) x_c x_c‖ →
    Φ (s, t) = south)
  (hk : letI := hM.chartedSpace; haveI := hM.isManifold;
    ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) ∞ k)
  {O : Set M} (hO : IsOpen O) (hOU : closure (ballU hM x_c R) \ ballU hM x_c R ⊆ O)
  (hkO : ∀ z ∈ O, k z = south)

include hR hRt hΦs hO hOU hkO in
/-- Off the chart ball, `H` agrees with `k ∘ fst` near every point. -/
theorem glueH_eventually_eq_of_notMem {z : M} (hz : z ∉ ballU hM x_c R) (t : ℝ) :
    letI := hM.chartedSpace; haveI := hM.isManifold;
    ∀ᶠ q in 𝓝 (z, t), glueH hM x_c R Φ k q = k q.1 := by
  letI := hM.chartedSpace
  haveI := hM.isManifold
  set φ := extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) x_c
  -- the open neighbourhood of `z`
  set A : Set M := {x : M | x ∈ φ.source ∧ R / 2 < ‖φ x - φ x_c‖}
  have hA : IsOpen A := isOpen_annulus x_c (R / 2)
  set N₀ : Set M := (O ∩ A) ∪ (closure (ballU hM x_c R))ᶜ
  have hN₀ : IsOpen N₀ := (hO.inter hA).union isClosed_closure.isOpen_compl
  have hzN : z ∈ N₀ := by
    by_cases hzc : z ∈ closure (ballU hM x_c R)
    · left
      refine ⟨hOU ⟨hzc, hz⟩, ?_⟩
      obtain ⟨h1, h2⟩ := frontier_ballU x_c hRt hzc hz
      exact ⟨h1, by linarith⟩
    · right; exact hzc
  have hmem : N₀ ×ˢ (univ : Set ℝ) ∈ 𝓝 (z, t) :=
    (hN₀.prod isOpen_univ).mem_nhds ⟨hzN, mem_univ _⟩
  filter_upwards [hmem] with q hq
  obtain ⟨x, s⟩ := q
  simp only [mem_prod, mem_univ, and_true] at hq
  by_cases hxU : x ∈ ballU hM x_c R
  · rw [glueH_of_mem hxU]
    rcases hq with ⟨hxO, hxA⟩ | hxc
    · rw [hΦs _ _ hxA.2.le, hkO x hxO]
    · exact absurd (subset_closure hxU) hxc
  · rw [glueH_of_notMem hxU]

include hR hRt hΦ hΦs hk hO hOU hkO in
theorem contMDiff_glueH :
    letI := hM.chartedSpace; haveI := hM.isManifold;
    ContMDiff (𝓘(ℝ, EuclideanSpace ℝ (Fin m)).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) ∞
      (glueH hM x_c R Φ k) := by
  letI := hM.chartedSpace
  haveI := hM.isManifold
  rintro ⟨z, t⟩
  by_cases hz : z ∈ ballU hM x_c R
  · -- on `U × ℝ` the map is `Φ ∘ (φ × id)`
    have hev : ∀ᶠ q in 𝓝 (z, t), glueH hM x_c R Φ k q =
        Φ (extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) x_c q.1, q.2) := by
      filter_upwards [((isOpen_ballU x_c R).prod isOpen_univ).mem_nhds
        (show (z, t) ∈ ballU hM x_c R ×ˢ univ from ⟨hz, mem_univ _⟩)] with q hq
      exact glueH_of_mem hq.1 q.2
    refine ContMDiffAt.congr_of_eventuallyEq ?_ hev
    have hz' : z ∈ (chartAt (EuclideanSpace ℝ (Fin m)) x_c).source := by
      rw [← extChartAt_source 𝓘(ℝ, EuclideanSpace ℝ (Fin m))]; exact (mem_ballU.1 hz).1
    have h1 : ContMDiffAt (𝓘(ℝ, EuclideanSpace ℝ (Fin m)).prod 𝓘(ℝ, ℝ))
        (𝓘(ℝ, EuclideanSpace ℝ (Fin m)).prod 𝓘(ℝ, ℝ)) ∞
        (fun q : M × ℝ => (extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) x_c q.1, q.2)) (z, t) :=
      ((contMDiffAt_extChartAt' (n := ∞) hz').comp (z, t) contMDiffAt_fst).prodMk contMDiffAt_snd
    exact (hΦ.contMDiffAt).comp (z, t) h1
  · exact (hk.contMDiffAt.comp (z, t) contMDiffAt_fst).congr_of_eventuallyEq
      (glueH_eventually_eq_of_notMem hR hRt hΦs hO hOU hkO hz t)

include hR hRt hΦs hO hOU hkO in
theorem glueH_slice_eventually_eq_of_notMem {z : M} (hz : z ∉ ballU hM x_c R) (t : ℝ) :
    letI := hM.chartedSpace; haveI := hM.isManifold;
    ∀ᶠ x in 𝓝 z, glueH hM x_c R Φ k (x, t) = k x := by
  letI := hM.chartedSpace
  haveI := hM.isManifold
  have h := glueH_eventually_eq_of_notMem hR hRt hΦs hO hOU hkO hz t
  have hc : ContinuousAt (fun x : M => (x, t)) z := continuousAt_id.prodMk continuousAt_const
  exact hc.eventually h

end smooth

/-! ### Derivatives of the slices -/

section deriv

variable (hΦ : ContMDiff (𝓘(ℝ, EuclideanSpace ℝ (Fin m)).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) ∞ Φ)

include hΦ in
/-- On the chart ball the slice `H(·, t)` is `Φ(·, t) ∘ φ`, with the chain-rule derivative. -/
theorem hasMFDerivAt_glueH_slice_of_mem {z : M} (hz : z ∈ ballU hM x_c R) (t : ℝ) :
    letI := hM.chartedSpace; haveI := hM.isManifold;
    HasMFDerivAt 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 𝓘(ℝ, EuclideanSpace ℝ (Fin m))
      (fun x => glueH hM x_c R Φ k (x, t)) z
      ((mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) (fun s => Φ (s, t))
          (extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) x_c z)).comp
        (mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 𝓘(ℝ, EuclideanSpace ℝ (Fin m))
          (extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) x_c) z)) := by
  letI := hM.chartedSpace
  haveI := hM.isManifold
  have hz' : z ∈ (chartAt (EuclideanSpace ℝ (Fin m)) x_c).source := by
    rw [← extChartAt_source 𝓘(ℝ, EuclideanSpace ℝ (Fin m))]; exact (mem_ballU.1 hz).1
  have hev : ∀ᶠ x in 𝓝 z, glueH hM x_c R Φ k (x, t) =
      (fun s => Φ (s, t)) (extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) x_c x) := by
    filter_upwards [(isOpen_ballU x_c R).mem_nhds hz] with x hx
    exact glueH_of_mem hx t
  refine HasMFDerivAt.congr_of_eventuallyEq ?_ hev
  have hΦt : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) ∞
      (fun s => Φ (s, t)) := hΦ.comp (contMDiff_id.prodMk contMDiff_const)
  have h1 := (hΦt.mdifferentiableAt (by simp)).hasMFDerivAt
    (x := extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) x_c z)
  have h2 := ((contMDiffAt_extChartAt' (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin m))) (n := ∞)
    hz').mdifferentiableAt (by simp)).hasMFDerivAt
  exact h1.comp z h2

end deriv

end Framed

end Milnor
