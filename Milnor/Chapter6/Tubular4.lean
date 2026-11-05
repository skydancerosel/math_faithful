import Milnor.Chapter6.Tubular3
import Milnor.Chapter6.Extend

/-!
# Tubular neighbourhoods, IV: the region `N_{ε/2}` and the extended vector field

With the nearest-point retraction `r` on `N_ε`, the closed neighbourhood `X = {dist(·, N) ≤ ε/2}`
is a compact region `{G ≥ 0}` with `0` a regular value of a smooth `G` (equal to
`(ε/2)² - |x - r x|²` near `X`), and a tangent field `v` on `N` extends to
`w x = v (r x) + (x - r x)`, whose zeros in `X` are the zeros of `v` and which points outward
along `∂X` (Milnor, p. 38).
-/

open Set Filter Topology Function Metric
open scoped ContDiff Manifold RealInnerProductSpace

noncomputable section

namespace Milnor

namespace Tub

variable {K n m : ℕ} {N : Set (EuclideanSpace ℝ (Fin (K + 1)))}
  (hN : IsSliceSubmanifold 𝓘(ℝ, EuclideanSpace ℝ (Fin (K + 1))) (EuclideanSpace ℝ (Fin n))
    (EuclideanSpace ℝ (Fin m)) N) (hNc : IsCompact N) (hne : N.Nonempty)

/-- The tubular radius. -/
def tubε : ℝ := (tubular hN hNc hne).choose

theorem tubε_pos : 0 < tubε hN hNc hne := (tubular hN hNc hne).choose_spec.1

/-- The nearest-point retraction. -/
def tubr : EuclideanSpace ℝ (Fin (K + 1)) → N := (tubular hN hNc hne).choose_spec.2.choose

theorem tubr_spec :
    letI := hN.chartedSpace
    (∀ x, dist x (tubr hN hNc hne x).1 = infDist x N) ∧
    (∀ x, infDist x N < tubε hN hNc hne → ∀ q : N, (∀ q' ∈ N, dist x q.1 ≤ dist x q') →
      q = tubr hN hNc hne x) ∧
    (∀ x ∈ N, (tubr hN hNc hne x).1 = x) ∧
    (∀ x, infDist x N < tubε hN hNc hne → ContDiffAt ℝ ∞ (fun y => (tubr hN hNc hne y).1) x) ∧
    (∀ x, infDist x N < tubε hN hNc hne → ∀ w ∈ LinearMap.range ((mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
        𝓘(ℝ, EuclideanSpace ℝ (Fin (K + 1))) (Subtype.val : N → EuclideanSpace ℝ (Fin (K + 1)))
        (tubr hN hNc hne x) :
          EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin (K + 1))) :
          EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin (K + 1))),
      ⟪x - (tubr hN hNc hne x).1, w⟫ = 0) ∧
    (∀ x, infDist x N < tubε hN hNc hne → ∀ w, fderiv ℝ (fun y => (tubr hN hNc hne y).1) x w ∈
      LinearMap.range ((mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
        𝓘(ℝ, EuclideanSpace ℝ (Fin (K + 1))) (Subtype.val : N → EuclideanSpace ℝ (Fin (K + 1)))
        (tubr hN hNc hne x) :
          EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin (K + 1))) :
          EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin (K + 1)))) ∧
    (∀ x (hx : x ∈ N) (v : EuclideanSpace ℝ (Fin (K + 1))),
      (∀ w ∈ LinearMap.range ((mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
        𝓘(ℝ, EuclideanSpace ℝ (Fin (K + 1))) (Subtype.val : N → EuclideanSpace ℝ (Fin (K + 1)))
        ⟨x, hx⟩ : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin (K + 1))) :
          EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin (K + 1))), ⟪v, w⟫ = 0) →
      ∀ᶠ s : ℝ in 𝓝 0, (tubr hN hNc hne (x + s • v)).1 = x) :=
  (tubular hN hNc hne).choose_spec.2.choose_spec

/-- The open tubular neighbourhood `N_ε`. -/
def Nε : Set (EuclideanSpace ℝ (Fin (K + 1))) := {x | infDist x N < tubε hN hNc hne}

theorem isOpen_Nε : IsOpen (Nε hN hNc hne) :=
  isOpen_lt (continuous_infDist_pt N) continuous_const

/-- The compact region `X = {dist(·, N) ≤ ε/2}`. -/
def X : Set (EuclideanSpace ℝ (Fin (K + 1))) := {x | infDist x N ≤ tubε hN hNc hne / 2}

theorem isClosed_X : IsClosed (X hN hNc hne) := isClosed_le (continuous_infDist_pt N) continuous_const

theorem X_subset_Nε : X hN hNc hne ⊆ Nε hN hNc hne := fun x hx =>
  lt_of_le_of_lt hx (half_lt_self (tubε_pos hN hNc hne))

theorem N_subset_X : N ⊆ X hN hNc hne := fun x hx => by
  show infDist x N ≤ _
  rw [infDist_zero_of_mem hx]
  exact (half_pos (tubε_pos hN hNc hne)).le

theorem isCompact_X : IsCompact (X hN hNc hne) := by
  obtain ⟨p₀, hp₀⟩ := id hne
  obtain ⟨R, hR⟩ := hNc.isBounded.subset_closedBall p₀
  refine (isCompact_closedBall p₀ (R + tubε hN hNc hne / 2)).of_isClosed_subset
    (isClosed_X hN hNc hne) fun x hx => ?_
  rw [mem_closedBall]
  have h1 := (tubr_spec hN hNc hne).1 x
  have h2 := hR (tubr hN hNc hne x).2
  rw [mem_closedBall] at h2
  calc dist x p₀ ≤ dist x (tubr hN hNc hne x).1 + dist (tubr hN hNc hne x).1 p₀ := dist_triangle _ _ _
    _ ≤ tubε hN hNc hne / 2 + R := by rw [h1]; exact add_le_add hx h2
    _ = R + tubε hN hNc hne / 2 := add_comm _ _

/-- `G₀ x = (ε/2)² - |x - r x|²`. -/
def G₀ (x : EuclideanSpace ℝ (Fin (K + 1))) : ℝ :=
  (tubε hN hNc hne / 2) ^ 2 - ‖x - (tubr hN hNc hne x).1‖ ^ 2

theorem G₀_eq (x : EuclideanSpace ℝ (Fin (K + 1))) :
    G₀ hN hNc hne x = (tubε hN hNc hne / 2) ^ 2 - infDist x N ^ 2 := by
  unfold G₀; rw [← (tubr_spec hN hNc hne).1 x, dist_eq_norm]

theorem contDiffOn_G₀ : ContDiffOn ℝ ∞ (G₀ hN hNc hne) (Nε hN hNc hne) := by
  intro x hx
  have hr := (tubr_spec hN hNc hne).2.2.2.1 x hx
  exact (contDiffAt_const.sub (ContDiffAt.norm_sq (𝕜 := ℝ) (contDiffAt_id.sub hr))).contDiffWithinAt

theorem hasFDerivAt_G₀ {x : EuclideanSpace ℝ (Fin (K + 1))} (hx : x ∈ Nε hN hNc hne) :
    HasFDerivAt (G₀ hN hNc hne)
      (-(2 • (innerSL ℝ (x - (tubr hN hNc hne x).1)).comp
        (ContinuousLinearMap.id ℝ _ - fderiv ℝ (fun y => (tubr hN hNc hne y).1) x))) x := by
  have hr := ((tubr_spec hN hNc hne).2.2.2.1 x hx).differentiableAt (by simp) |>.hasFDerivAt
  have := ((hasFDerivAt_id x).sub hr).norm_sq
  have h2 := (hasFDerivAt_const ((tubε hN hNc hne / 2) ^ 2) x).sub this
  rw [zero_sub] at h2
  exact h2

/-- `dG₀_x (w) = -2 ⟪x - r x, w⟫` on `N_ε` (the `dr` term drops out by orthogonality). -/
theorem fderiv_G₀_apply {x : EuclideanSpace ℝ (Fin (K + 1))} (hx : x ∈ Nε hN hNc hne)
    (w : EuclideanSpace ℝ (Fin (K + 1))) :
    fderiv ℝ (G₀ hN hNc hne) x w = -2 * ⟪x - (tubr hN hNc hne x).1, w⟫ := by
  letI := hN.chartedSpace
  rw [(hasFDerivAt_G₀ hN hNc hne hx).fderiv]
  have horth := (tubr_spec hN hNc hne).2.2.2.2.1 x hx _ ((tubr_spec hN hNc hne).2.2.2.2.2.1 x hx w)
  simp only [ContinuousLinearMap.neg_apply, smul_apply, ContinuousLinearMap.comp_apply,
    sub_apply, ContinuousLinearMap.id_apply, innerSL_apply_apply, inner_sub_right, horth, sub_zero,
    nsmul_eq_mul, Nat.cast_ofNat]
  ring

/-- **The region function.**  A smooth `G` with `{G ≥ 0} = X` and `G = G₀` near `X`. -/
theorem exists_G : ∃ G : EuclideanSpace ℝ (Fin (K + 1)) → ℝ, ContDiff ℝ ∞ G ∧
    {x | 0 ≤ G x} = X hN hNc hne ∧ ∀ᶠ x in 𝓝ˢ (X hN hNc hne), G x = G₀ hN hNc hne x := by
  classical
  obtain ⟨χ, hχ0, hχ1, hχ01⟩ := exists_contMDiffMap_zero_one_nhds_of_isClosed
    𝓘(ℝ, EuclideanSpace ℝ (Fin (K + 1))) (n := ⊤) (isOpen_Nε hN hNc hne).isClosed_compl
    (isClosed_X hN hNc hne) (disjoint_compl_left_iff.2 (X_subset_Nε hN hNc hne))
  set G : EuclideanSpace ℝ (Fin (K + 1)) → ℝ :=
    fun x => if x ∈ Nε hN hNc hne then χ x * G₀ hN hNc hne x + (χ x - 1) else -1 with hG
  have hG1 : ∀ᶠ x in 𝓝ˢ (X hN hNc hne), G x = G₀ hN hNc hne x := by
    filter_upwards [(isOpen_Nε hN hNc hne).mem_nhdsSet.2 (X_subset_Nε hN hNc hne), hχ1] with x hx hχ
    simp only [hG, if_pos hx, hχ, one_mul, sub_self, add_zero]
  refine ⟨G, ?_, ?_, hG1⟩
  · rw [← contMDiff_iff_contDiff]
    intro x
    by_cases hx : x ∈ Nε hN hNc hne
    · have h1 : G =ᶠ[𝓝 x] fun x => χ x * G₀ hN hNc hne x + (χ x - 1) := by
        filter_upwards [(isOpen_Nε hN hNc hne).mem_nhds hx] with y hy
        simp only [hG, if_pos hy]
      refine ContMDiffAt.congr_of_eventuallyEq ?_ h1
      have hG₀ : ContMDiffAt 𝓘(ℝ, EuclideanSpace ℝ (Fin (K + 1))) 𝓘(ℝ, ℝ) ∞ (G₀ hN hNc hne) x := by
        rw [contMDiffAt_iff_contDiffAt]
        exact (contDiffOn_G₀ hN hNc hne).contDiffAt ((isOpen_Nε hN hNc hne).mem_nhds hx)
      exact (χ.contMDiff.contMDiffAt.mul hG₀).add (χ.contMDiff.contMDiffAt.sub contMDiffAt_const)
    · have h1 : G =ᶠ[𝓝 x] fun _ => -1 := by
        filter_upwards [eventually_nhdsSet_iff_forall.1 hχ0 x hx] with y hy
        by_cases hyN : y ∈ Nε hN hNc hne
        · simp only [hG, if_pos hyN, hy, zero_mul, zero_add, zero_sub]
        · simp only [hG, if_neg hyN]
      exact ContMDiffAt.congr_of_eventuallyEq contMDiffAt_const h1
  · ext x
    simp only [mem_setOf_eq]
    constructor
    · intro hx
      by_contra hxX
      have hxN : x ∈ Nε hN hNc hne := by
        by_contra h
        simp only [hG, if_neg h] at hx
        linarith
      simp only [hG, if_pos hxN] at hx
      have hχ := hχ01 x
      have hG₀ : G₀ hN hNc hne x < 0 := by
        rw [G₀_eq]
        have : tubε hN hNc hne / 2 < infDist x N := lt_of_not_ge hxX
        have h0 : 0 ≤ tubε hN hNc hne / 2 := (half_pos (tubε_pos hN hNc hne)).le
        nlinarith
      have h1 : χ x * G₀ hN hNc hne x ≤ 0 := by nlinarith [hχ.1, hG₀]
      have h2 : χ x = 1 := le_antisymm hχ.2 (by linarith)
      rw [h2, one_mul] at hx
      linarith
    · intro hx
      rw [hG1.self_of_nhdsSet x hx, G₀_eq]
      have h0 : 0 ≤ infDist x N := infDist_nonneg
      have : infDist x N ≤ tubε hN hNc hne / 2 := hx
      nlinarith

/-- `0` is a regular value of `G`. -/
theorem isRegularValue_G {G : EuclideanSpace ℝ (Fin (K + 1)) → ℝ} (hG : ContDiff ℝ ∞ G)
    (hGX : {x | 0 ≤ G x} = X hN hNc hne) (hGG : ∀ᶠ x in 𝓝ˢ (X hN hNc hne), G x = G₀ hN hNc hne x) :
    IsRegularValue 𝓘(ℝ, EuclideanSpace ℝ (Fin (K + 1))) 𝓘(ℝ, ℝ) G 0 := by
  intro x hx
  have hx0 : G x = 0 := hx
  have hxX : x ∈ X hN hNc hne := by rw [← hGX]; exact le_of_eq hx0.symm
  have hxN : x ∈ Nε hN hNc hne := X_subset_Nε hN hNc hne hxX
  have hev : G =ᶠ[𝓝 x] G₀ hN hNc hne := eventually_nhdsSet_iff_forall.1 hGG x hxX
  show Function.Surjective (mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin (K + 1))) 𝓘(ℝ, ℝ) G x)
  have h1 : mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin (K + 1))) 𝓘(ℝ, ℝ) G x = fderiv ℝ G x := mfderiv_eq_fderiv
  rw [h1, hev.fderiv_eq]
  have hne0 : x - (tubr hN hNc hne x).1 ≠ 0 := by
    intro h
    have := hev.self_of_nhds
    rw [hx0] at this
    unfold G₀ at this
    rw [h, norm_zero] at this
    have := tubε_pos hN hNc hne
    nlinarith
  intro t
  refine ⟨(t / (-2 * ‖x - (tubr hN hNc hne x).1‖ ^ 2)) • (x - (tubr hN hNc hne x).1), ?_⟩
  rw [map_smul, fderiv_G₀_apply hN hNc hne hxN, real_inner_self_eq_norm_sq, smul_eq_mul]
  have : -2 * ‖x - (tubr hN hNc hne x).1‖ ^ 2 ≠ 0 := by
    have := norm_pos_iff.2 hne0
    positivity
  field_simp

/-! ### The extended vector field -/

variable {v : N → EuclideanSpace ℝ (Fin (K + 1))}

/-- `w₀ x = v (r x) + (x - r x)`. -/
def w₀ (v : N → EuclideanSpace ℝ (Fin (K + 1))) (x : EuclideanSpace ℝ (Fin (K + 1))) :
    EuclideanSpace ℝ (Fin (K + 1)) :=
  v (tubr hN hNc hne x) + (x - (tubr hN hNc hne x).1)

theorem contMDiffOn_w₀ (hv : letI := hN.chartedSpace;
      ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, EuclideanSpace ℝ (Fin (K + 1))) ∞ v) :
    ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin (K + 1))) 𝓘(ℝ, EuclideanSpace ℝ (Fin (K + 1))) ∞
      (w₀ hN hNc hne v) (Nε hN hNc hne) := by
  letI := hN.chartedSpace
  haveI := hN.isManifold
  set U : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin (K + 1))) :=
    ⟨Nε hN hNc hne, isOpen_Nε hN hNc hne⟩ with hU
  -- `r` as a smooth map `U → N`
  have hrU : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin (K + 1))) 𝓘(ℝ, EuclideanSpace ℝ (Fin (K + 1))) ∞
      (fun x : U => (tubr hN hNc hne x.1).1) := by
    intro x
    have := (tubr_spec hN hNc hne).2.2.2.1 x.1 x.2
    rw [← contMDiffAt_iff_contDiffAt] at this
    exact (contMDiffAt_subtype_iff (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin (K + 1))))
      (I' := 𝓘(ℝ, EuclideanSpace ℝ (Fin (K + 1)))) (n := ∞) (U := U)
      (f := fun y => (tubr hN hNc hne y).1) (x := x)).2 this
  have hrN : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin (K + 1))) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞
      (fun x : U => tubr hN hNc hne x.1) := by
    have := hN.contMDiff_codRestrict hrU (fun x => (tubr hN hNc hne x.1).2)
    convert this using 1
  have hwU : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin (K + 1))) 𝓘(ℝ, EuclideanSpace ℝ (Fin (K + 1))) ∞
      (fun x : U => w₀ hN hNc hne v x.1) :=
    (hv.comp hrN).add (contMDiff_subtype_val.sub hrU)
  intro x hx
  exact ((contMDiffAt_subtype_iff (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin (K + 1))))
    (I' := 𝓘(ℝ, EuclideanSpace ℝ (Fin (K + 1)))) (n := ∞) (U := U) (f := w₀ hN hNc hne v)
    (x := ⟨x, hx⟩)).1 (hwU ⟨x, hx⟩)).contMDiffWithinAt

/-- Zeros of `w₀` in the tubular neighbourhood are zeros of `v` on `N`. -/
theorem w₀_eq_zero (hvT : letI := hN.chartedSpace; ∀ q : N, v q ∈ LinearMap.range
      ((mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, EuclideanSpace ℝ (Fin (K + 1)))
        (Subtype.val : N → EuclideanSpace ℝ (Fin (K + 1))) q :
          EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin (K + 1))) :
          EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin (K + 1))))
    {x : EuclideanSpace ℝ (Fin (K + 1))} (hx : x ∈ Nε hN hNc hne) (h0 : w₀ hN hNc hne v x = 0) :
    ∃ hxN : x ∈ N, v ⟨x, hxN⟩ = 0 := by
  letI := hN.chartedSpace
  have horth := (tubr_spec hN hNc hne).2.2.2.2.1 x hx _ (hvT (tubr hN hNc hne x))
  have h1 : ⟪w₀ hN hNc hne v x, x - (tubr hN hNc hne x).1⟫ = 0 := by rw [h0, inner_zero_left]
  unfold w₀ at h1
  rw [inner_add_left, real_inner_comm, horth, zero_add, real_inner_self_eq_norm_sq] at h1
  have h2 : x - (tubr hN hNc hne x).1 = 0 := by
    have := pow_eq_zero_iff (n := 2) (by norm_num) |>.1 h1
    exact norm_eq_zero.1 this
  have hxr : x = (tubr hN hNc hne x).1 := sub_eq_zero.1 h2
  refine ⟨hxr ▸ (tubr hN hNc hne x).2, ?_⟩
  have hq : (⟨x, hxr ▸ (tubr hN hNc hne x).2⟩ : N) = tubr hN hNc hne x := Subtype.ext hxr
  rw [hq]
  unfold w₀ at h0
  rw [h2, add_zero] at h0
  exact h0

theorem w₀_of_mem {x : EuclideanSpace ℝ (Fin (K + 1))} (hx : x ∈ N) :
    w₀ hN hNc hne v x = v ⟨x, hx⟩ := by
  unfold w₀
  have h := (tubr_spec hN hNc hne).2.2.1 x hx
  have hq : tubr hN hNc hne x = ⟨x, hx⟩ := Subtype.ext h
  rw [hq]; simp

/-- `w₀` points outward along `∂X`. -/
theorem fderiv_G₀_w₀ (hvT : letI := hN.chartedSpace; ∀ q : N, v q ∈ LinearMap.range
      ((mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, EuclideanSpace ℝ (Fin (K + 1)))
        (Subtype.val : N → EuclideanSpace ℝ (Fin (K + 1))) q :
          EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin (K + 1))) :
          EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin (K + 1))))
    {x : EuclideanSpace ℝ (Fin (K + 1))} (hx : x ∈ Nε hN hNc hne) :
    fderiv ℝ (G₀ hN hNc hne) x (w₀ hN hNc hne v x) = -2 * ‖x - (tubr hN hNc hne x).1‖ ^ 2 := by
  letI := hN.chartedSpace
  have horth := (tubr_spec hN hNc hne).2.2.2.2.1 x hx _ (hvT (tubr hN hNc hne x))
  rw [fderiv_G₀_apply hN hNc hne hx]
  unfold w₀
  rw [inner_add_right, horth, zero_add, real_inner_self_eq_norm_sq]

end Tub

end Milnor
