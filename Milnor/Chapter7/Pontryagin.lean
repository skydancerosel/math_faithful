import Milnor.Chapter7.Framed
import Milnor.Chapter7.Transition

/-!
# The Pontryagin manifold of a map to the sphere (Milnor §7, pp. 42–43)

For `f : M → Sᵖ` smooth with regular value `y`, `N = f⁻¹(y)` is a compact submanifold of `M`
of codimension `p`, and the derivative `df_x : T_xM → T_ySᵖ` carries the normal space of `N`
at `x` isomorphically onto `T_ySᵖ`.  Pulling back a positive basis `b` of `T_ySᵖ` (read in the
chart at `y`) gives a framing of `N`: the **Pontryagin manifold** `(f⁻¹(y), f^*b)`.

The framing is written down explicitly through the extension `F̃ = c ∘ f ∘ r` of `c ∘ f` to the
tubular neighbourhood of `M` (`c` the chart of `Sᵖ` at `y`, `r` the nearest-point retraction of
Chapter 6): `w_i(x) = A^*(A A^*)⁻¹ bᵢ` with `A = dF̃_x`, whose kernel contains `T_xN` and the
normal space of `M`, so `w_i(x)` is tangent to `M`, normal to `N`, and `df_x(w_i) = bᵢ`.
-/

open Set Filter Topology Function Module Metric
open scoped ContDiff Manifold RealInnerProductSpace

noncomputable section

namespace Milnor

open Sphere

namespace Framed

variable {K m w : ℕ} {M : Set (EuclideanSpace ℝ (Fin (K + 1)))}
  (hM : IsSliceSubmanifold 𝓘(ℝ, EuclideanSpace ℝ (Fin (K + 1))) (EuclideanSpace ℝ (Fin m))
    (EuclideanSpace ℝ (Fin w)) M) (hMc : IsCompact M) (hne : M.Nonempty)

/-! ### Linear algebra of the pseudo-inverse -/

section pinv

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

/-- `A A^*` is a unit when `A` is surjective. -/
theorem isUnit_comp_adjoint {A : E →L[ℝ] F} (hA : Surjective A) :
    IsUnit (A.comp (ContinuousLinearMap.adjoint A)) := by
  have hinj : Injective (A.comp (ContinuousLinearMap.adjoint A)) := by
    refine (injective_iff_map_eq_zero _).2 fun c hc => ?_
    have h1 : ⟪ContinuousLinearMap.adjoint A c, ContinuousLinearMap.adjoint A c⟫ = 0 := by
      rw [ContinuousLinearMap.adjoint_inner_left]
      simp only [ContinuousLinearMap.comp_apply] at hc
      rw [hc, inner_zero_right]
    have h2 : ContinuousLinearMap.adjoint A c = 0 := inner_self_eq_zero.1 h1
    obtain ⟨v, rfl⟩ := hA c
    have h3 : ⟪A v, A v⟫ = 0 := by
      rw [← ContinuousLinearMap.adjoint_inner_right, h2, inner_zero_right]
    exact inner_self_eq_zero.1 h3
  have hsurj : Surjective (A.comp (ContinuousLinearMap.adjoint A)) :=
    LinearMap.injective_iff_surjective (f := (A.comp (ContinuousLinearMap.adjoint A)).toLinearMap)
      |>.1 hinj
  exact ⟨(ContinuousLinearEquiv.ofBijective (A.comp (ContinuousLinearMap.adjoint A))
    (LinearMap.ker_eq_bot.2 hinj) (LinearMap.range_eq_top.2 hsurj)).toUnit, rfl⟩

/-- The pseudo-inverse `A^* (A A^*)⁻¹`. -/
def pinv (A : E →L[ℝ] F) : F →L[ℝ] E :=
  (ContinuousLinearMap.adjoint A).comp (Ring.inverse (A.comp (ContinuousLinearMap.adjoint A)))

theorem comp_pinv {A : E →L[ℝ] F} (hA : Surjective A) (c : F) : A (pinv A c) = c := by
  obtain ⟨u, hu⟩ := isUnit_comp_adjoint hA
  have : A (pinv A c) = (A.comp (ContinuousLinearMap.adjoint A))
      (Ring.inverse (A.comp (ContinuousLinearMap.adjoint A)) c) := rfl
  rw [this, ← hu, Ring.inverse_unit, ← ContinuousLinearMap.mul_apply, u.mul_inv,
    ContinuousLinearMap.one_apply]

theorem inner_pinv_eq_zero (A : E →L[ℝ] F) (c : F) {v : E} (hv : A v = 0) :
    ⟪pinv A c, v⟫ = 0 := by
  unfold pinv
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_left, hv, inner_zero_right]

end pinv

/-! ### The extension `F̃ = c ∘ f ∘ r` -/

variable {p n : ℕ}

section pont

variable {f : M → Sph p}
  (hf : letI := hM.chartedSpace; haveI := hM.isManifold;
    ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) ∞ f)
  {y : Sph p}
  (hy : letI := hM.chartedSpace; haveI := hM.isManifold;
    IsRegularValue 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) f y)

/-- The dimension count for the level set. -/
theorem levelDim (hnp : n + p = m) :
    finrank ℝ (EuclideanSpace ℝ (Fin n)) + finrank ℝ (EuclideanSpace ℝ (Fin p)) =
      finrank ℝ (EuclideanSpace ℝ (Fin m)) := by
  simp only [finrank_euclideanSpace_fin]; exact hnp

include hf hy in
/-- `f⁻¹(y)` is a submanifold of `M` of codimension `p`. -/
theorem isSliceSubmanifold_level (hnp : n + p = m) :
    letI := hM.chartedSpace; haveI := hM.isManifold;
    IsSliceSubmanifold 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) (EuclideanSpace ℝ (Fin n))
      (EuclideanSpace ℝ (Fin p)) (f ⁻¹' {y}) := by
  letI := hM.chartedSpace
  haveI := hM.isManifold
  exact isSliceSubmanifold_preimage (Z := EuclideanSpace ℝ (Fin n)) (levelDim hnp) hf hy

/-- The extension `F̃ z = c (f (r z))`, `c` the chart of `Sᵖ` at `y`. -/
def Ft (f : M → Sph p) (y : Sph p) (z : EuclideanSpace ℝ (Fin (K + 1))) :
    EuclideanSpace ℝ (Fin p) :=
  extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) y (f (Tub.tubr hM hMc hne z))

/-- The open set on which `F̃` is smooth. -/
def Wt (f : M → Sph p) (y : Sph p) : Set (EuclideanSpace ℝ (Fin (K + 1))) :=
  {z | infDist z M < Tub.tubε hM hMc hne ∧
    f (Tub.tubr hM hMc hne z) ∈ (extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) y).source}

theorem tubr_mem_of_mem {x : EuclideanSpace ℝ (Fin (K + 1))} (hx : x ∈ M) :
    Tub.tubr hM hMc hne x = ⟨x, hx⟩ :=
  Subtype.ext ((Tub.tubr_spec hM hMc hne).2.2.1 x hx)

/-- `r` is smooth as a map `N_ε → M`. -/
theorem contMDiff_tubr_opens :
    letI := hM.chartedSpace; haveI := hM.isManifold;
    ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin (K + 1))) 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) ∞
      (fun x : (⟨Tub.Nε hM hMc hne, Tub.isOpen_Nε hM hMc hne⟩ :
        TopologicalSpace.Opens (EuclideanSpace ℝ (Fin (K + 1)))) => Tub.tubr hM hMc hne x.1) := by
  letI := hM.chartedSpace
  haveI := hM.isManifold
  set U : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin (K + 1))) :=
    ⟨Tub.Nε hM hMc hne, Tub.isOpen_Nε hM hMc hne⟩ with hU
  have hrU : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin (K + 1))) 𝓘(ℝ, EuclideanSpace ℝ (Fin (K + 1))) ∞
      (fun x : U => (Tub.tubr hM hMc hne x.1).1) := by
    intro x
    have := (Tub.tubr_spec hM hMc hne).2.2.2.1 x.1 x.2
    rw [← contMDiffAt_iff_contDiffAt] at this
    exact (contMDiffAt_subtype_iff (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin (K + 1))))
      (I' := 𝓘(ℝ, EuclideanSpace ℝ (Fin (K + 1)))) (n := ∞) (U := U)
      (f := fun y => (Tub.tubr hM hMc hne y).1) (x := x)).2 this
  have := hM.contMDiff_codRestrict hrU (fun x => (Tub.tubr hM hMc hne x.1).2)
  convert this using 1

include hf in
theorem isOpen_Wt : IsOpen (Wt hM hMc hne f y) := by
  letI := hM.chartedSpace
  haveI := hM.isManifold
  set U : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin (K + 1))) :=
    ⟨Tub.Nε hM hMc hne, Tub.isOpen_Nε hM hMc hne⟩ with hU
  have hc : ContinuousOn (fun z => f (Tub.tubr hM hMc hne z)) U.1 := by
    rw [continuousOn_iff_continuous_restrict]
    exact hf.continuous.comp (contMDiff_tubr_opens hM hMc hne).continuous
  exact hc.isOpen_inter_preimage (Tub.isOpen_Nε hM hMc hne) (isOpen_extChartAt_source y)

include hf in
theorem contDiffOn_Ft : ContDiffOn ℝ ∞ (Ft hM hMc hne f y) (Wt hM hMc hne f y) := by
  letI := hM.chartedSpace
  haveI := hM.isManifold
  set U : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin (K + 1))) :=
    ⟨Tub.Nε hM hMc hne, Tub.isOpen_Nε hM hMc hne⟩ with hU
  have hfr : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin (K + 1))) 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) ∞
      (fun x : U => f (Tub.tubr hM hMc hne x.1)) := hf.comp (contMDiff_tubr_opens hM hMc hne)
  intro z hz
  have hzU : z ∈ Tub.Nε hM hMc hne := hz.1
  have h1 : ContMDiffAt 𝓘(ℝ, EuclideanSpace ℝ (Fin (K + 1))) 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) ∞
      (fun z => f (Tub.tubr hM hMc hne z)) z :=
    (contMDiffAt_subtype_iff (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin (K + 1))))
      (I' := 𝓘(ℝ, EuclideanSpace ℝ (Fin p))) (n := ∞) (U := U)
      (f := fun z => f (Tub.tubr hM hMc hne z)) (x := ⟨z, hzU⟩)).1 (hfr ⟨z, hzU⟩)
  have h2 : ContMDiffAt 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) ∞
      (extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) y) (f (Tub.tubr hM hMc hne z)) :=
    contMDiffAt_extChartAt' (n := ∞)
      (by rw [← extChartAt_source 𝓘(ℝ, EuclideanSpace ℝ (Fin p))]; exact hz.2)
  have := h2.comp z h1
  rw [contMDiffAt_iff_contDiffAt] at this
  exact this.contDiffWithinAt

/-- `F̃ = c ∘ f` on `M`. -/
theorem Ft_of_mem {x : EuclideanSpace ℝ (Fin (K + 1))} (hx : x ∈ M) :
    Ft hM hMc hne f y x = extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) y (f ⟨x, hx⟩) := by
  unfold Ft; rw [tubr_mem_of_mem hM hMc hne hx]

/-- Points of `M` lie in `Wt` (when their image lies in the chart source). -/
theorem mem_Wt_of_mem {x : EuclideanSpace ℝ (Fin (K + 1))} (hx : x ∈ M)
    (hfx : f ⟨x, hx⟩ ∈ (extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) y).source) :
    x ∈ Wt hM hMc hne f y := by
  refine ⟨?_, ?_⟩
  · show infDist x M < _
    rw [infDist_zero_of_mem hx]; exact Tub.tubε_pos hM hMc hne
  · rw [tubr_mem_of_mem hM hMc hne hx]; exact hfx

/-! ### The derivative of `F̃` -/

/-- `A x = dF̃_x`. -/
def At (f : M → Sph p) (y : Sph p) (x : EuclideanSpace ℝ (Fin (K + 1))) :
    EuclideanSpace ℝ (Fin (K + 1)) →L[ℝ] EuclideanSpace ℝ (Fin p) :=
  fderiv ℝ (Ft hM hMc hne f y) x

include hf in
theorem hasFDerivAt_Ft {x : EuclideanSpace ℝ (Fin (K + 1))} (hx : x ∈ Wt hM hMc hne f y) :
    HasFDerivAt (Ft hM hMc hne f y) (At hM hMc hne f y x) x :=
  (((contDiffOn_Ft hM hMc hne hf).differentiableOn (by simp)) x hx).differentiableAt
    ((isOpen_Wt hM hMc hne hf).mem_nhds hx) |>.hasFDerivAt

include hf in
theorem contDiffOn_At : ContDiffOn ℝ ∞ (At hM hMc hne f y) (Wt hM hMc hne f y) :=
  (contDiffOn_Ft hM hMc hne hf).fderiv_of_isOpen (isOpen_Wt hM hMc hne hf) (by simp)

include hf in
/-- The chain rule along `M`: `dF̃_x ∘ d(val)_x = dc_{f x} ∘ df_x`. -/
theorem At_comp_mfd_val {x : EuclideanSpace ℝ (Fin (K + 1))} (hx : x ∈ M)
    (hfx : f ⟨x, hx⟩ ∈ (extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) y).source) :
    letI := hM.chartedSpace; haveI := hM.isManifold;
    (At hM hMc hne f y x).comp (mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin m))
        𝓘(ℝ, EuclideanSpace ℝ (Fin (K + 1))) (Subtype.val : M → EuclideanSpace ℝ (Fin (K + 1))) ⟨x, hx⟩) =
      (mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) 𝓘(ℝ, EuclideanSpace ℝ (Fin p))
        (extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) y) (f ⟨x, hx⟩)).comp
        (mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) f ⟨x, hx⟩) := by
  letI := hM.chartedSpace
  haveI := hM.isManifold
  have h1 : Ft hM hMc hne f y ∘ (Subtype.val : M → EuclideanSpace ℝ (Fin (K + 1))) =
      fun q => extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) y (f q) :=
    funext fun q => Ft_of_mem hM hMc hne q.2
  have hd := (hasFDerivAt_Ft hM hMc hne hf (mem_Wt_of_mem hM hMc hne hx hfx)).hasMFDerivAt
  have h2 := hd.comp (⟨x, hx⟩ : M) (hasMFDerivAt_mfd (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin m)))
    (J := 𝓘(ℝ, EuclideanSpace ℝ (Fin (K + 1)))) (hM.contMDiff_val.mdifferentiableAt (by simp)))
  rw [h1] at h2
  have h3 := (hasMFDerivAt_mfd (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin p)))
    (J := 𝓘(ℝ, EuclideanSpace ℝ (Fin p)))
    (mdifferentiableAt_extChartAt (by rwa [← extChartAt_source 𝓘(ℝ, EuclideanSpace ℝ (Fin p))]))).comp
    (⟨x, hx⟩ : M) (hasMFDerivAt_mfd (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin m)))
      (J := 𝓘(ℝ, EuclideanSpace ℝ (Fin p))) (hf.mdifferentiableAt (by simp)))
  exact hasMFDerivAt_unique h2 h3

include hf hy in
/-- `dF̃_x` is surjective at points of `f⁻¹(y)`. -/
theorem surjective_At {x : EuclideanSpace ℝ (Fin (K + 1))} (hx : x ∈ M) (hfx : f ⟨x, hx⟩ = y) :
    Surjective (At hM hMc hne f y x) := by
  letI := hM.chartedSpace
  haveI := hM.isManifold
  have hsrc : f ⟨x, hx⟩ ∈ (extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) y).source := by
    rw [hfx]; exact mem_extChartAt_source y
  have h := At_comp_mfd_val hM hMc hne hf hx hsrc
  have hs1 : Surjective (mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) f ⟨x, hx⟩) :=
    hy ⟨x, hx⟩ hfx
  have hs2 : Surjective (mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) 𝓘(ℝ, EuclideanSpace ℝ (Fin p))
      (extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) y) (f ⟨x, hx⟩)) := by
    obtain ⟨D, hD⟩ := isInvertible_mfderiv_extChartAt (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin p))) hsrc
    show Surjective (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) 𝓘(ℝ, EuclideanSpace ℝ (Fin p))
      (extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) y) (f ⟨x, hx⟩))
    rw [← hD]; exact D.surjective
  have : Surjective ((At hM hMc hne f y x).comp (mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin m))
      𝓘(ℝ, EuclideanSpace ℝ (Fin (K + 1))) (Subtype.val : M → EuclideanSpace ℝ (Fin (K + 1))) ⟨x, hx⟩)) := by
    rw [h]; exact hs2.comp hs1
  exact Surjective.of_comp this

include hf in
/-- The normal space of `M` lies in the kernel of `dF̃_x` (`x ∈ M`). -/
theorem At_normal_eq_zero {x : EuclideanSpace ℝ (Fin (K + 1))} (hx : x ∈ M)
    (hfx : f ⟨x, hx⟩ ∈ (extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) y).source)
    {v : EuclideanSpace ℝ (Fin (K + 1))} (hv : ∀ w ∈ tangentM hM ⟨x, hx⟩, ⟪v, w⟫ = 0) :
    At hM hMc hne f y x v = 0 := by
  have hev := (Tub.tubr_spec hM hMc hne).2.2.2.2.2.2 x hx v hv
  have hd : HasDerivAt (fun s : ℝ => Ft hM hMc hne f y (x + s • v)) (At hM hMc hne f y x v) 0 := by
    have h1 : HasDerivAt (fun s : ℝ => x + s • v) v 0 := by
      have := (hasDerivAt_id (0 : ℝ)).smul_const v
      simpa using (this.const_add x)
    have h2 : HasFDerivAt (Ft hM hMc hne f y) (At hM hMc hne f y x) (x + (0 : ℝ) • v) := by
      rw [zero_smul, add_zero]; exact hasFDerivAt_Ft hM hMc hne hf (mem_Wt_of_mem hM hMc hne hx hfx)
    exact h2.comp_hasDerivAt (0 : ℝ) h1
  have hconst : (fun s : ℝ => Ft hM hMc hne f y (x + s • v)) =ᶠ[𝓝 (0 : ℝ)]
      fun _ => extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) y (f ⟨x, hx⟩) := by
    filter_upwards [hev] with s hs
    unfold Ft
    have : Tub.tubr hM hMc hne (x + s • v) = ⟨x, hx⟩ := Subtype.ext hs
    rw [this]
  have hd0 : HasDerivAt (fun s : ℝ => Ft hM hMc hne f y (x + s • v)) 0 0 :=
    (hasDerivAt_const (0 : ℝ) _).congr_of_eventuallyEq hconst
  exact hd.unique hd0

include hf hy in
/-- The tangent space of `f⁻¹(y)` lies in the kernel of `dF̃_x`. -/
theorem At_tangentN_eq_zero (hnp : n + p = m) (q : f ⁻¹' {y}) {w : EuclideanSpace ℝ (Fin (K + 1))}
    (hw : w ∈ tangentN hM (isSliceSubmanifold_level hM hf hy hnp) q) :
    At hM hMc hne f y q.1.1 w = 0 := by
  letI := hM.chartedSpace
  haveI := hM.isManifold
  have hN := isSliceSubmanifold_level hM hf hy hnp
  letI := hN.chartedSpace
  haveI := hN.isManifold
  obtain ⟨a, rfl⟩ := hw
  have hfq : f q.1 = y := q.2
  have hsrc : f ⟨q.1.1, q.1.2⟩ ∈ (extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) y).source := by
    rw [Subtype.coe_eta, hfq]; exact mem_extChartAt_source y
  -- `F̃ ∘ emb` is constant on `f⁻¹(y)`
  have hconst : (Ft hM hMc hne f y ∘ fun r : f ⁻¹' {y} => (r.1.1 : EuclideanSpace ℝ (Fin (K + 1)))) =
      fun _ => extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) y y := by
    funext r
    simp only [Function.comp]
    rw [Ft_of_mem hM hMc hne r.1.2, Subtype.coe_eta]
    have : f r.1 = y := r.2
    rw [this]
  have hemb : MDifferentiableAt 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, EuclideanSpace ℝ (Fin (K + 1)))
      (fun r : f ⁻¹' {y} => (r.1.1 : EuclideanSpace ℝ (Fin (K + 1)))) q :=
    (hM.contMDiff_val.comp hN.contMDiff_val).mdifferentiableAt (by simp)
  have hd := (hasFDerivAt_Ft hM hMc hne hf (mem_Wt_of_mem hM hMc hne q.1.2 hsrc)).hasMFDerivAt
  have h2 := hd.comp q (hasMFDerivAt_mfd (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
    (J := 𝓘(ℝ, EuclideanSpace ℝ (Fin (K + 1)))) hemb)
  rw [hconst] at h2
  have h3 := hasMFDerivAt_const (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
    (I' := 𝓘(ℝ, EuclideanSpace ℝ (Fin p))) (c := extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) y y) (x := q)
  have h4 := hasMFDerivAt_unique h2 h3
  have h5 : (At hM hMc hne f y q.1.1).comp (mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
      𝓘(ℝ, EuclideanSpace ℝ (Fin (K + 1))) (fun r : f ⁻¹' {y} => (r.1.1 : EuclideanSpace ℝ (Fin (K + 1)))) q) =
      (0 : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin p)) := h4
  have := congrArg (fun L : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin p) => L a) h5
  simpa using this

/-! ### The framing -/

/-- The pulled-back framing `w_i(x) = A^*(A A^*)⁻¹ bᵢ`. -/
def pontV (f : M → Sph p) (y : Sph p) (b : Fin p → EuclideanSpace ℝ (Fin p)) (i : Fin p)
    (q : f ⁻¹' {y}) : EuclideanSpace ℝ (Fin (K + 1)) :=
  pinv (At hM hMc hne f y q.1.1) (b i)

include hf hy in
theorem At_pontV (b : Fin p → EuclideanSpace ℝ (Fin p)) (i : Fin p) (q : f ⁻¹' {y}) :
    At hM hMc hne f y q.1.1 (pontV hM hMc hne f y b i q) = b i :=
  comp_pinv (surjective_At hM hMc hne hf hy q.1.2 q.2) (b i)

include hf hy in
theorem pontV_normal (hnp : n + p = m) (b : Fin p → EuclideanSpace ℝ (Fin p)) (i : Fin p)
    (q : f ⁻¹' {y}) : ∀ w ∈ tangentN hM (isSliceSubmanifold_level hM hf hy hnp) q,
      ⟪pontV hM hMc hne f y b i q, w⟫ = 0 := fun w hw =>
  inner_pinv_eq_zero _ _ (At_tangentN_eq_zero hM hMc hne hf hy hnp q hw)

include hf hy in
theorem pontV_tangent (b : Fin p → EuclideanSpace ℝ (Fin p)) (i : Fin p) (q : f ⁻¹' {y}) :
    pontV hM hMc hne f y b i q ∈ tangentM hM q.1 := by
  have hsrc : f ⟨q.1.1, q.1.2⟩ ∈ (extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) y).source := by
    rw [Subtype.coe_eta]
    have : f q.1 = y := q.2
    rw [this]; exact mem_extChartAt_source y
  -- `pontV ∈ (ker A)ᗮ ⊆ (T_xMᗮ)ᗮ = T_xM`
  have h1 : pontV hM hMc hne f y b i q ∈ (LinearMap.ker (At hM hMc hne f y q.1.1 :
      EuclideanSpace ℝ (Fin (K + 1)) →ₗ[ℝ] EuclideanSpace ℝ (Fin p)))ᗮ := by
    rw [Submodule.mem_orthogonal']
    intro v hv
    exact inner_pinv_eq_zero _ _ (LinearMap.mem_ker.1 hv)
  have h2 : (tangentM hM q.1)ᗮ ≤ LinearMap.ker (At hM hMc hne f y q.1.1 :
      EuclideanSpace ℝ (Fin (K + 1)) →ₗ[ℝ] EuclideanSpace ℝ (Fin p)) := by
    intro v hv
    rw [LinearMap.mem_ker]
    exact At_normal_eq_zero hM hMc hne hf q.1.2 hsrc ((Submodule.mem_orthogonal' _ _).1 hv)
  have h3 := Submodule.orthogonal_le h2 h1
  rwa [Submodule.orthogonal_orthogonal] at h3

include hf hy in
theorem pontV_indep {b : Fin p → EuclideanSpace ℝ (Fin p)} (hb : LinearIndependent ℝ b)
    (q : f ⁻¹' {y}) : LinearIndependent ℝ (fun i => pontV hM hMc hne f y b i q) := by
  refine LinearIndependent.of_comp (At hM hMc hne f y q.1.1 :
    EuclideanSpace ℝ (Fin (K + 1)) →ₗ[ℝ] EuclideanSpace ℝ (Fin p)) ?_
  have : ((At hM hMc hne f y q.1.1 : EuclideanSpace ℝ (Fin (K + 1)) →ₗ[ℝ] EuclideanSpace ℝ (Fin p)) ∘
      fun i => pontV hM hMc hne f y b i q) = b := by
    funext i; exact At_pontV hM hMc hne hf hy b i q
  rw [this]; exact hb

include hf hy in
/-- The framing is smooth along `f⁻¹(y)`. -/
theorem contMDiff_pontV (hnp : n + p = m) (b : Fin p → EuclideanSpace ℝ (Fin p)) (i : Fin p) :
    letI := hM.chartedSpace; haveI := hM.isManifold;
    letI := (isSliceSubmanifold_level hM hf hy hnp).chartedSpace;
    ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, EuclideanSpace ℝ (Fin (K + 1))) ∞
      (pontV hM hMc hne f y b i) := by
  letI := hM.chartedSpace
  haveI := hM.isManifold
  have hN := isSliceSubmanifold_level hM hf hy hnp
  letI := hN.chartedSpace
  haveI := hN.isManifold
  intro q
  have hsrc : f ⟨q.1.1, q.1.2⟩ ∈ (extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) y).source := by
    rw [Subtype.coe_eta]
    have : f q.1 = y := q.2
    rw [this]; exact mem_extChartAt_source y
  have hq : q.1.1 ∈ Wt hM hMc hne f y := mem_Wt_of_mem hM hMc hne q.1.2 hsrc
  have hA : ContDiffAt ℝ ∞ (At hM hMc hne f y) q.1.1 :=
    (contDiffOn_At hM hMc hne hf).contDiffAt ((isOpen_Wt hM hMc hne hf).mem_nhds hq)
  have hAd : ContDiffAt ℝ ∞ (fun z => ContinuousLinearMap.adjoint (At hM hMc hne f y z)) q.1.1 :=
    ((Tub.adjointCLM (k := p) (n := K + 1)).contDiff.contDiffAt).comp q.1.1 hA
  have hAA : ContDiffAt ℝ ∞ (fun z => (At hM hMc hne f y z).comp
      (ContinuousLinearMap.adjoint (At hM hMc hne f y z))) q.1.1 := hA.clm_comp hAd
  obtain ⟨u, hu⟩ := isUnit_comp_adjoint (surjective_At hM hMc hne hf hy q.1.2 q.2)
  have hinv : ContDiffAt ℝ ∞ (fun z => Ring.inverse ((At hM hMc hne f y z).comp
      (ContinuousLinearMap.adjoint (At hM hMc hne f y z)))) q.1.1 := by
    have := contDiffAt_ringInverse ℝ (n := ∞) u
    rw [hu] at this
    exact this.comp q.1.1 hAA
  have hpinv : ContDiffAt ℝ ∞ (fun z => pinv (At hM hMc hne f y z) (b i)) q.1.1 := by
    unfold pinv
    exact (hAd.clm_comp hinv).clm_apply contDiffAt_const
  have hemb : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, EuclideanSpace ℝ (Fin (K + 1))) ∞
      (fun r : f ⁻¹' {y} => (r.1.1 : EuclideanSpace ℝ (Fin (K + 1)))) :=
    hM.contMDiff_val.comp hN.contMDiff_val
  show ContMDiffAt 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, EuclideanSpace ℝ (Fin (K + 1))) ∞
    ((fun z => pinv (At hM hMc hne f y z) (b i)) ∘
      fun r : f ⁻¹' {y} => (r.1.1 : EuclideanSpace ℝ (Fin (K + 1)))) q
  exact ContMDiffAt.comp q hpinv.contMDiffAt hemb.contMDiffAt

include hf hMc in
theorem isCompact_level :
    letI := hM.chartedSpace; haveI := hM.isManifold; IsCompact (f ⁻¹' {y}) := by
  letI := hM.chartedSpace
  haveI := hM.isManifold
  haveI : CompactSpace M := isCompact_iff_compactSpace.1 hMc
  exact (isClosed_singleton.preimage hf.continuous).isCompact

/-- **The Pontryagin manifold** `(f⁻¹(y), f^*b)` of `f` at the regular value `y`, for a basis `b`
of the model space `ℝᵖ` of `Sᵖ` at `y` (read through the chart at `y`). -/
def pontryagin (hnp : n + p = m) (b : Fin p → EuclideanSpace ℝ (Fin p))
    (hb : LinearIndependent ℝ b) : FramedSub hM n p where
  N := f ⁻¹' {y}
  hN := isSliceSubmanifold_level hM hf hy hnp
  dim := hnp
  compact := isCompact_level hM hMc hf
  v := pontV hM hMc hne f y b
  smooth := fun i => contMDiff_pontV hM hMc hne hf hy hnp b i
  tangent := fun i q => pontV_tangent hM hMc hne hf hy b i q
  normal := fun i q w hw => pontV_normal hM hMc hne hf hy hnp b i q w hw
  indep := fun q => pontV_indep hM hMc hne hf hy hb q

end pont

end Framed

end Milnor
