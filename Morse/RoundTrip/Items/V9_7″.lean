import Morse
import RoundTrip.Check
import RoundTrip.Blind.«V9_7″»
import RoundTrip.Bridge

open Set Filter Topology Function Module
open scoped ContDiff Manifold RealInnerProductSpace

namespace RoundTrip.«V9_7″»

/-- The project's statement (no universe parameters): on the unit sphere `Sⁿ = Milnor.Sphere.Sph n
⊆ ℝⁿ⁺¹` with the slice structure `sphSub n` and the induced metric, for orthonormal `p ∈ Sⁿ`, `u`:
(1) the great circle `t ↦ cos(Lt) p + sin(Lt) u` is a geodesic on `ℝ`; (2) `sin(Lt) e`, `e ⊥ p, u`,
is a Jacobi field along it; (3) for `L > 0` and `t ∈ (0, 1]`, the multiplicity of `0` and `t` as
conjugate parameters is `n − 1` if `Lt ∈ πℕ` and `0` otherwise (vocabulary: `Morse.greatCircle`). -/
def A : Prop :=
  type_of% @Morse.isGeodesicOn_greatCircle ∧ type_of% @Morse.isJacobiField_sin_smul ∧
    type_of% @Morse.conjMultiplicity_greatCircle

theorem A_holds : A :=
  ⟨@Morse.isGeodesicOn_greatCircle, @Morse.isJacobiField_sin_smul,
    @Morse.conjMultiplicity_greatCircle⟩

/-! Neither `A → B` nor `B → A` is proved; see `V9_7″.json`.

## The embedded special case: dictionary (Jacobi fields copied from `Items/V9_8.lean`) -/

namespace Emb

set_option linter.unusedSectionVars false

open RoundTrip.Bridge

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W] {n : ℕ} {N : Set V}
  {hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) (Rn n) W N}

theorem intv_Icc : RoundTrip.BridgePrelude.IsIntv (Icc (0 : ℝ) 1) :=
  ⟨ordConnected_Icc, uniqueDiffOn_Icc zero_lt_one⟩

theorem prj_incl (x : Bridge.Sub hN) : Morse.prj hN (incl hN x) = P hN x := Morse.prj_of_mem hN x.2

/-- The ambient field of `D/dt U` (derivative within `s`). -/
theorem ambA_covA (γ : ℝ → Bridge.Sub hN) (s : Set ℝ) (U : FA n γ) (t : ℝ) :
    ambA γ (covA γ s U) t = P hN (γ t) (derivWithin (ambA γ U) s t) := D_covA γ s U t

theorem contDiffOn_ambA_covA {γ : ℝ → Bridge.Sub hN} (hc : IsSmoothCurve (n := n) γ (Icc 0 1))
    {U : FA n γ} (hU : ContDiffOn ℝ ∞ (ambA γ U) (Icc 0 1)) :
    ContDiffOn ℝ ∞ (ambA γ (covA γ (Icc 0 1) U)) (Icc 0 1) := by
  have hc' : ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, Rn n) ∞ γ (Icc 0 1) := hc
  have hP : ContDiffOn ℝ ∞ (fun t => P hN (γ t)) (Icc 0 1) :=
    contMDiffOn_iff_contDiffOn.1 (contMDiff_P.comp_contMDiffOn hc')
  have hd : ContDiffOn ℝ ∞ (derivWithin (ambA γ U) (Icc 0 1)) (Icc 0 1) :=
    hU.derivWithin (uniqueDiffOn_Icc zero_lt_one) (by simp)
  exact (hP.clm_apply hd).congr fun t _ => ambA_covA γ _ U t

/-- **Dictionary: Jacobi fields (blind ⇒ project).** -/
theorem isJacobiField_of_isJacobi {γ : ℝ → Bridge.Sub hN} (hc : IsSmoothCurve (n := n) γ (Icc 0 1))
    {J : FA n γ} (hJ : IsJacobi (Bridge.conn (hN := hN)) γ (Icc 0 1) J) :
    Morse.IsJacobiField hN (incl hN ∘ γ) (ambA γ J) := by
  obtain ⟨J', J'', h1, h2, h3⟩ := hJ
  have hs := intv_Icc
  have h1' := (hasCovDeriv_iff' hs hc).1 h1
  have h2' := (hasCovDeriv_iff' hs hc).1 h2
  have hJs := (isSmoothAlong_iff.1 h1'.1).2
  refine ⟨hJs, fun t _ => ?_, fun t ht => ?_⟩
  · rw [comp_apply, prj_incl]
    exact P_D (γ t) (J t)
  · have ht' : t ∈ Icc (0 : ℝ) 1 := Ioo_subset_Icc_self ht
    have hnhds : Icc (0 : ℝ) 1 ∈ 𝓝 t := Icc_mem_nhds ht.1 ht.2
    have hcov : Morse.covD hN (incl hN ∘ γ) (ambA γ J) =ᶠ[𝓝 t] ambA γ J' := by
      filter_upwards [Ioo_mem_nhds ht.1 ht.2] with x hx
      have hx' : x ∈ Icc (0 : ℝ) 1 := Ioo_subset_Icc_self hx
      rw [h1'.2 x hx', Morse.covD, derivWithin_of_mem_nhds (Icc_mem_nhds hx.1 hx.2), comp_apply,
        prj_incl]
    have e1 : Morse.covD hN (incl hN ∘ γ) (Morse.covD hN (incl hN ∘ γ) (ambA γ J)) t =
        ambA γ J'' t := by
      rw [Morse.covD, hcov.deriv_eq, h2'.2 t ht', derivWithin_of_mem_nhds hnhds, comp_apply,
        prj_incl]
    obtain ⟨r, hr, hr0⟩ := h3 t ht'
    have hr' := (isCurvVal_iff (γ t) (vel (n := n) γ (Icc 0 1) t) (J t)
      (vel (n := n) γ (Icc 0 1) t) r).1 hr
    have hv : D hN (γ t) (vel (n := n) γ (Icc 0 1) t) = deriv (incl hN ∘ γ) t :=
      (D_vel hc (uniqueDiffOn_Icc zero_lt_one) ht').trans (derivWithin_of_mem_nhds hnhds)
    rw [Morse.jacobiExpr, e1]
    have := congrArg (D hN (γ t)) hr0
    rw [D_tadd, D_tzero, hr', hv] at this
    exact this

/-- **Dictionary: Jacobi fields (project ⇒ blind)**, using that the Jacobi expression is
continuous on `[0, 1]` (so the equation on `(0, 1)` extends to the end points). -/
theorem isJacobi_of_isJacobiField {γ : ℝ → Bridge.Sub hN} (hc : IsSmoothCurve (n := n) γ (Icc 0 1))
    {J : FA n γ} (hJ : Morse.IsJacobiField hN (incl hN ∘ γ) (ambA γ J)) :
    IsJacobi (Bridge.conn (hN := hN)) γ (Icc 0 1) J := by
  have hs := intv_Icc
  have uI : UniqueDiffOn ℝ (Icc (0 : ℝ) 1) := uniqueDiffOn_Icc zero_lt_one
  have hJ'c : ContDiffOn ℝ ∞ (ambA γ (covA γ (Icc 0 1) J)) (Icc 0 1) :=
    contDiffOn_ambA_covA hc hJ.contDiffOn
  have hJ''c : ContDiffOn ℝ ∞ (ambA γ (covA γ (Icc 0 1) (covA γ (Icc 0 1) J))) (Icc 0 1) :=
    contDiffOn_ambA_covA hc hJ'c
  have hJs : RoundTrip.BridgePrelude.IsSmoothAlong γ (Icc 0 1) J :=
    isSmoothAlong_iff.2 ⟨hc, hJ.contDiffOn⟩
  have hJ's : RoundTrip.BridgePrelude.IsSmoothAlong γ (Icc 0 1) (covA γ (Icc 0 1) J) :=
    isSmoothAlong_iff.2 ⟨hc, hJ'c⟩
  refine ⟨covA γ (Icc 0 1) J, covA γ (Icc 0 1) (covA γ (Icc 0 1) J),
    (hasCovDeriv_iff hs hc).2 ⟨hJs, fun t _ => rfl⟩,
    (hasCovDeriv_iff hs hc).2 ⟨hJ's, fun t _ => rfl⟩, fun t ht => ?_⟩
  have hcd : ContDiffOn ℝ ∞ (incl hN ∘ γ) (Icc 0 1) := isSmoothCurve_iff.1 hc
  have hvc : ContinuousOn (derivWithin (incl hN ∘ γ) (Icc 0 1)) (Icc 0 1) :=
    (hcd.derivWithin uI (m := ∞) (by simp)).continuousOn
  have hvT : ∀ τ ∈ Icc (0 : ℝ) 1, Morse.prj hN ((incl hN ∘ γ) τ)
      (derivWithin (incl hN ∘ γ) (Icc 0 1) τ) = derivWithin (incl hN ∘ γ) (Icc 0 1) τ :=
    fun τ hτ => by
      rw [← D_vel hc uI hτ, comp_apply, prj_incl]
      exact P_D _ _
  -- the ambient Jacobi expression within `[0, 1]`
  set F : ℝ → V := fun τ => ambA γ (covA γ (Icc 0 1) (covA γ (Icc 0 1) J)) τ +
    Morse.curvR hN ((incl hN ∘ γ) τ) (derivWithin (incl hN ∘ γ) (Icc 0 1) τ) (ambA γ J τ)
      (derivWithin (incl hN ∘ γ) (Icc 0 1) τ) with hF
  have hF0 : EqOn F 0 (Ioo 0 1) := by
    intro τ hτ
    have hnhds : Icc (0 : ℝ) 1 ∈ 𝓝 τ := Icc_mem_nhds hτ.1 hτ.2
    have hcov : Morse.covD hN (incl hN ∘ γ) (ambA γ J) =ᶠ[𝓝 τ] ambA γ (covA γ (Icc 0 1) J) := by
      filter_upwards [Ioo_mem_nhds hτ.1 hτ.2] with x hx
      rw [ambA_covA, Morse.covD, derivWithin_of_mem_nhds (Icc_mem_nhds hx.1 hx.2), comp_apply,
        prj_incl]
    have := hJ.eq τ hτ
    rw [Morse.jacobiExpr, Morse.covD, hcov.deriv_eq] at this
    simp only [hF, Pi.zero_apply]
    rw [ambA_covA, derivWithin_of_mem_nhds hnhds, derivWithin_of_mem_nhds hnhds]
    rw [comp_apply, prj_incl] at this
    exact this
  have hFc : ContinuousOn F (Icc 0 1) := by
    refine hJ''c.continuousOn.add fun τ hτ => ?_
    exact Morse.continuousWithinAt_curvR hN hτ (hcd.continuousOn τ hτ) (fun τ _ => (γ τ).2)
      (hvc τ hτ) (hJ.contDiffOn.continuousOn τ hτ) (hvc τ hτ) hvT hJ.tangent
  have hFI : EqOn F 0 (Icc 0 1) :=
    hF0.of_subset_closure hFc continuousOn_const Ioo_subset_Icc_self
      (by rw [closure_Ioo zero_ne_one])
  have hvt : derivWithin (incl hN ∘ γ) (Icc 0 1) t = D hN (γ t) (vel (n := n) γ (Icc 0 1) t) :=
    (D_vel hc uI ht).symm
  have hRT : Morse.curvR hN ((incl hN ∘ γ) t) (derivWithin (incl hN ∘ γ) (Icc 0 1) t)
      (ambA γ J t) (derivWithin (incl hN ∘ γ) (Icc 0 1) t) ∈ Morse.tangentSubspace hN (γ t) := by
    have h := Morse.curvOp_mem hN (D_mem (γ t) (vel (n := n) γ (Icc 0 1) t)) (D_mem (γ t) (J t))
      (D_mem (γ t) (vel (n := n) γ (Icc 0 1) t))
    convert h using 1
    rw [hvt]
    exact Morse.curvR_of_mem hN (γ t).2 _ _ _
  refine ⟨L hN (γ t) (Morse.curvR hN ((incl hN ∘ γ) t) (derivWithin (incl hN ∘ γ) (Icc 0 1) t)
      (ambA γ J t) (derivWithin (incl hN ∘ γ) (Icc 0 1) t)),
    (isCurvVal_iff (γ t) (vel (n := n) γ (Icc 0 1) t) (J t) (vel (n := n) γ (Icc 0 1) t) _).2 ?_,
    ?_⟩
  · rw [D_L hRT, hvt]
    rfl
  · apply D_injective (γ t)
    refine (D_tadd (γ t) _ _).trans (Eq.trans ?_ (D_tzero (γ t)).symm)
    rw [D_L hRT]
    exact hFI ht

/-- Smoothness of maps from a normed space into `↥N`, read in `V` (Bridge's
`contMDiffWithinAt_curve_iff`, for any source space). -/
theorem contMDiffWithinAt_iff_incl {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → Bridge.Sub hN} {s : Set E} {x : E} :
    ContMDiffWithinAt 𝓘(ℝ, E) 𝓘(ℝ, Rn n) ∞ f s x ↔ ContDiffWithinAt ℝ ∞ (incl hN ∘ f) s x := by
  constructor
  · intro h
    exact contMDiffWithinAt_iff_contDiffWithinAt.1
      ((contMDiff_incl (f x)).comp_contMDiffWithinAt x h)
  · intro h
    have hcont : ContinuousWithinAt f s x :=
      (Topology.IsInducing.subtypeVal.continuousWithinAt_iff (f := f)).2 h.continuousWithinAt
    rw [contMDiffWithinAt_iff_target]
    refine ⟨hcont, ?_⟩
    set σ := Morse.sliceAt hN (f x)
    have hφ : ContDiffAt ℝ ∞ (fun y => (σ.φ y).1) (incl hN (f x)) :=
      contDiff_fst.contDiffAt.comp _ ((Milnor.Problems.sliceChart_contDiffOn σ).contDiffAt
        (σ.φ.open_source.mem_nhds (Morse.mem_sliceAt_source hN (f x))))
    have e : (extChartAt 𝓘(ℝ, Rn n) (f x) ∘ f) = (fun y => (σ.φ y).1) ∘ (incl hN ∘ f) := rfl
    rw [e]
    exact contMDiffWithinAt_iff_contDiffWithinAt.2 (hφ.comp_contDiffWithinAt x h)

/-- A project geodesic on `(0, 1)`, smooth on `[0, 1]`, lifts to a blind geodesic on `[0, 1]`. -/
theorem isGeodesic_lift_of {c : ℝ → V} (q : Bridge.Sub hN) (hc : ContDiffOn ℝ ∞ c (Icc 0 1))
    (hcN : ∀ t ∈ Icc (0 : ℝ) 1, c t ∈ N) (hgeo : Morse.IsGeodesicOn hN c (Ioo 0 1)) :
    IsGeodesic (Bridge.conn (hN := hN)) (lift c q) (Icc 0 1) := by
  have uI : UniqueDiffOn ℝ (Icc (0 : ℝ) 1) := uniqueDiffOn_Icc zero_lt_one
  have heq : EqOn (incl hN ∘ lift c q) c (Icc 0 1) := fun t ht => incl_lift q (hcN t ht)
  have hd : EqOn (derivWithin (incl hN ∘ lift c q) (Icc 0 1)) (derivWithin c (Icc 0 1))
      (Icc 0 1) := fun t ht => derivWithin_congr heq (heq ht)
  have hdd : EqOn (derivWithin (derivWithin (incl hN ∘ lift c q) (Icc 0 1)) (Icc 0 1))
      (derivWithin (derivWithin c (Icc 0 1)) (Icc 0 1)) (Icc 0 1) :=
    fun t ht => derivWithin_congr hd (hd ht)
  have hG : EqOn (fun t => Morse.prj hN (c t) (derivWithin (derivWithin c (Icc 0 1)) (Icc 0 1) t))
      0 (Icc 0 1) := by
    refine EqOn.of_subset_closure (s := Ioo 0 1) ?_ ?_ continuousOn_const Ioo_subset_Icc_self
      (by rw [closure_Ioo zero_ne_one])
    · intro t ht
      have hn : Icc (0 : ℝ) 1 ∈ 𝓝 t := Icc_mem_nhds ht.1 ht.2
      have e1 : derivWithin c (Icc 0 1) =ᶠ[𝓝 t] deriv c := by
        filter_upwards [Ioo_mem_nhds ht.1 ht.2] with x hx
        exact derivWithin_of_mem_nhds (Icc_mem_nhds hx.1 hx.2)
      simp only [Pi.zero_apply]
      rw [derivWithin_of_mem_nhds hn, e1.deriv_eq, Morse.prj_of_mem hN (hgeo.mem t ht)]
      exact hgeo.tanProj_deriv_deriv ht
    · exact (Morse.ContDiffOn.prj_comp hN hc hcN).continuousOn.clm_apply
        ((hc.derivWithin uI (m := ∞) (by simp)).derivWithin uI (m := ∞) (by simp)).continuousOn
  refine (isGeodesic_iff (c := lift c q) (s := Icc 0 1)).2 ⟨intv_Icc, hc.congr heq, fun t ht => ?_⟩
  rw [hdd ht]
  have := hG ht
  simp only [Pi.zero_apply, Morse.prj_of_mem hN (hcN t ht)] at this
  rw [lift_of_mem q (hcN t ht)]
  exact this

/-- A copy of the (trivial) fact that a Jacobi field along `γ` only depends on `γ|[0,1]`
(copied from `Items/V9_8.lean`). -/
theorem congr_curve' {γ γ' J : ℝ → V} (hJ : Morse.IsJacobiField hN γ J)
    (heq : EqOn γ γ' (Icc 0 1)) : Morse.IsJacobiField hN γ' J where
  contDiffOn := hJ.contDiffOn
  tangent t ht := by rw [← heq ht]; exact hJ.tangent t ht
  eq t ht := by
    have hev : γ =ᶠ[𝓝 t] γ' := eventually_of_mem (Icc_mem_nhds ht.1 ht.2) heq
    have hcov : ∀ X : ℝ → V, Morse.covD hN γ X =ᶠ[𝓝 t] Morse.covD hN γ' X := fun X => by
      filter_upwards [eventually_eventually_nhds.2 hev] with x hx
      rw [Morse.covD, Morse.covD, hx.self_of_nhds]
    have h1 : deriv (Morse.covD hN γ J) t = deriv (Morse.covD hN γ' J) t := (hcov J).deriv_eq
    have h2 : γ t = γ' t := hev.self_of_nhds
    have h3 : deriv γ t = deriv γ' t := hev.deriv_eq
    have := hJ.eq t ht
    rw [Morse.jacobiExpr] at this ⊢
    change Morse.prj hN (γ t) (deriv (Morse.covD hN γ J) t) +
      Morse.curvR hN (γ t) (deriv γ t) (J t) (deriv γ t) = 0 at this
    change Morse.prj hN (γ' t) (deriv (Morse.covD hN γ' J) t) +
      Morse.curvR hN (γ' t) (deriv γ' t) (J t) (deriv γ' t) = 0
    rw [← h1, ← h2, ← h3]
    exact this

/-- Smoothness of maps from any manifold into `↥N` is smoothness in `V`. -/
theorem contMDiff_of_incl {EB : Type} [NormedAddCommGroup EB] [NormedSpace ℝ EB] {HB : Type}
    [TopologicalSpace HB] {IB : ModelWithCorners ℝ EB HB} {MB : Type} [TopologicalSpace MB]
    [ChartedSpace HB MB] {f : MB → Bridge.Sub hN} (h : ContMDiff IB 𝓘(ℝ, V) ∞ (incl hN ∘ f)) :
    ContMDiff IB 𝓘(ℝ, Rn n) ∞ f := by
  intro x
  have hx := h x
  have hcont : ContinuousAt f x :=
    (Topology.IsInducing.subtypeVal.continuousAt_iff (f := f)).2 hx.continuousAt
  rw [← contMDiffWithinAt_univ, contMDiffWithinAt_iff_target]
  refine ⟨hcont.continuousWithinAt, ?_⟩
  set σ := Morse.sliceAt hN (f x)
  have hφ : ContDiffAt ℝ ∞ (fun y => (σ.φ y).1) (incl hN (f x)) :=
    contDiff_fst.contDiffAt.comp _ ((Milnor.Problems.sliceChart_contDiffOn σ).contDiffAt
      (σ.φ.open_source.mem_nhds (Morse.mem_sliceAt_source hN (f x))))
  have e : (extChartAt 𝓘(ℝ, Rn n) (f x) ∘ f) = (fun y => (σ.φ y).1) ∘ (incl hN ∘ f) := rfl
  rw [e]
  exact (hφ.comp_contMDiffAt (f := incl hN ∘ f) (x := x) hx).contMDiffWithinAt

/-! ### Jacobi fields vanishing at `0` and `1`: the blind set and the project's `conjSpace` -/

section Dim

variable (γ : ℝ → Bridge.Sub hN)

/-- `pI t = projIcc 0 1 t`. -/
noncomputable abbrev pI (t : ℝ) : ℝ := (projIcc (0 : ℝ) 1 zero_le_one t : ℝ)

theorem pI_of_mem {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : pI t = t := by
  simp [pI, projIcc_of_mem _ ht]

theorem pI_mem (t : ℝ) : pI t ∈ Icc (0 : ℝ) 1 := (projIcc (0 : ℝ) 1 zero_le_one t).2

/-- `J ↦ (t ↦ D(J(pI t)))`, the ambient field normalized to be constant off `[0, 1]`. -/
noncomputable def Φ : FA n γ →ₗ[ℝ] (ℝ → V) where
  toFun J t := D hN (γ (pI t)) (J (pI t))
  map_add' _ _ := funext fun _ => D_tadd _ _ _
  map_smul' _ _ := funext fun _ => D_tsmul _ _ _

/-- Fields vanishing off `[0, 1]`. -/
noncomputable def Zsub : Submodule ℝ (FA n γ) where
  carrier := {J | ∀ t, t ∉ Icc (0 : ℝ) 1 → J t = 0}
  add_mem' {J J'} hJ hJ' t ht := by
    show J t + J' t = 0
    rw [hJ t ht, hJ' t ht, add_zero]
  zero_mem' _ _ := rfl
  smul_mem' a J hJ t ht := by
    show a • J t = 0
    rw [hJ t ht, smul_zero]

variable {γ}

theorem Φ_apply_of_mem (J : FA n γ) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    Φ γ J t = ambA γ J t := by
  show D hN (γ (pI t)) (J (pI t)) = D hN (γ t) (J t)
  rw [pI_of_mem ht]

theorem Φ_normal (J : FA n γ) (t : ℝ) : Φ γ J t = Φ γ J (pI t) := by
  show D hN (γ (pI t)) (J (pI t)) = D hN (γ (pI (pI t))) (J (pI (pI t)))
  rw [pI_of_mem (pI_mem t)]


variable (hc : IsSmoothCurve (n := n) γ (Icc 0 1)) (hcc : Morse.IsSmoothCurveIn hN (incl hN ∘ γ))

include hc in
theorem memS_iff (J : FA n γ) :
    (J ∈ JacOn (Bridge.conn (hN := hN)) γ (Icc 0 1) ∧ J 0 = 0 ∧ J 1 = 0) ↔
      (J ∈ Zsub γ ∧ Φ γ J ∈ Morse.conjSpace hN (incl hN ∘ γ) hcc 0 1) := by
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have h1 : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨zero_le_one, le_rfl⟩
  have hΦ0 : Φ γ J 0 = D hN (γ 0) (J 0) := Φ_apply_of_mem J h0
  have hΦ1 : Φ γ J 1 = D hN (γ 1) (J 1) := Φ_apply_of_mem J h1
  rw [Morse.mem_conjSpace hcc]
  constructor
  · rintro ⟨⟨hJ, hz⟩, hJ0, hJ1⟩
    refine ⟨hz, ⟨(isJacobiField_of_isJacobi hc hJ).congr fun t ht => (Φ_apply_of_mem J ht).symm,
      Φ_normal J⟩, ?_, ?_⟩
    · rw [hΦ0, hJ0, D_tzero]
    · rw [hΦ1, hJ1, D_tzero]
  · rintro ⟨hz, ⟨hJ, -⟩, hJ0, hJ1⟩
    refine ⟨⟨isJacobi_of_isJacobiField hc (hJ.congr fun t ht => Φ_apply_of_mem J ht), hz⟩, ?_, ?_⟩
    · apply D_injective (γ 0)
      rw [← hΦ0, hJ0, D_tzero]
    · apply D_injective (γ 1)
      rw [← hΦ1, hJ1, D_tzero]

/-- The blind set, as a submodule. -/
noncomputable def Ssub : Submodule ℝ (FA n γ) :=
  Zsub γ ⊓ (Morse.conjSpace hN (incl hN ∘ γ) hcc 0 1).comap (Φ γ)

include hc in
theorem S_eq : {J | J ∈ JacOn (Bridge.conn (hN := hN)) γ (Icc 0 1) ∧ J 0 = 0 ∧ J 1 = 0} =
    (Ssub hcc : Set (FA n γ)) :=
  Set.ext fun J => (memS_iff hc hcc J).trans Iff.rfl

/-- `Φ` is a linear isomorphism from the blind space onto `conjSpace`. -/
noncomputable def Ψ : Ssub hcc →ₗ[ℝ] Morse.conjSpace hN (incl hN ∘ γ) hcc 0 1 :=
  ((Φ γ).domRestrict (Ssub hcc)).codRestrict _ fun J => J.2.2

theorem Ψ_bijective : Bijective (Ψ hcc) := by
  constructor
  · intro J J' h
    have h' : Φ γ J = Φ γ J' := congrArg Subtype.val h
    apply Subtype.ext
    funext t
    by_cases ht : t ∈ Icc (0 : ℝ) 1
    · apply D_injective (γ t)
      have := congrFun h' t
      rwa [Φ_apply_of_mem _ ht, Φ_apply_of_mem _ ht] at this
    · rw [J.2.1 t ht, J'.2.1 t ht]
  · rintro ⟨K, hK⟩
    classical
    have hK' := (Morse.mem_conjSpace hcc).1 hK
    set J : FA n γ := fun t => if t ∈ Icc (0 : ℝ) 1 then L hN (γ t) (K t) else 0 with hJdef
    have hΦJ : Φ γ J = K := by
      funext t
      show D hN (γ (pI t)) (J (pI t)) = K t
      have hT : P hN (γ (pI t)) (K (pI t)) = K (pI t) := by
        rw [← prj_incl]
        exact hK'.1.1.tangent _ (pI_mem t)
      have hJp : J (pI t) = L hN (γ (pI t)) (K (pI t)) := if_pos (pI_mem t)
      rw [hJp, hK'.1.2 t]
      have := D_L_P (γ (pI t)) (K (pI t))
      rw [hT] at this
      exact this
    have hJZ : J ∈ Zsub γ := fun t ht => if_neg ht
    refine ⟨⟨J, hJZ, ?_⟩, Subtype.ext hΦJ⟩
    show Φ γ J ∈ Morse.conjSpace hN (incl hN ∘ γ) hcc 0 1
    rw [hΦJ]
    exact hK

include hc in
/-- **The blind multiplicity is the project's multiplicity** (as ranks). -/
theorem conjMult_eq_rank :
    conjMult (Bridge.conn (hN := hN)) γ 0 1 =
      (Module.rank ℝ (Morse.conjSpace hN (incl hN ∘ γ) hcc 0 1)).toENat := by
  unfold conjMult setDim
  rw [S_eq hc hcc, Submodule.span_eq, (LinearEquiv.ofBijective (Ψ hcc) (Ψ_bijective hcc)).rank_eq]

include hc in
theorem conjMult_eq :
    conjMult (Bridge.conn (hN := hN)) γ 0 1 = (Morse.conjMultiplicity hN (incl hN ∘ γ) hcc 0 1 : ℕ∞) := by
  rw [conjMult_eq_rank hc hcc, Morse.conjMultiplicity, ← finrank_eq_rank]
  simp

include hc in
/-- A positive multiplicity gives a blind conjugate pair `0, 1`. -/
theorem isConj_of_pos (hpos : 0 < Morse.conjMultiplicity hN (incl hN ∘ γ) hcc 0 1) :
    IsConj (Bridge.conn (hN := hN)) γ 0 1 := by
  have hr : Module.rank ℝ (Ssub hcc) ≠ 0 := by
    rw [(LinearEquiv.ofBijective (Ψ hcc) (Ψ_bijective hcc)).rank_eq, ← finrank_eq_rank]
    exact_mod_cast hpos.ne'
  have hne : Ssub hcc ≠ ⊥ := fun h => hr (by rw [h]; exact rank_bot ℝ (FA n γ))
  obtain ⟨J, hJ, hJ0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  obtain ⟨hJj, hJa, hJb⟩ := (memS_iff hc hcc J).2 hJ
  exact ⟨zero_ne_one, J, hJj, hJ0, hJa, hJb⟩

end Dim

/-! ### The sphere -/

section Sphere

open Milnor.Sphere Real

variable {m : ℕ}

local notation "𝔼" => EuclideanSpace ℝ (Fin (m + 1))

/-- The conjugate spaces along two curves agreeing on `[0, 1]` coincide. -/
theorem conjSpace_congr {γ γ' : ℝ → 𝔼} (hc : Morse.IsSmoothCurveIn (sphSub m) γ)
    (hc' : Morse.IsSmoothCurveIn (sphSub m) γ') (heq : EqOn γ γ' (Icc 0 1)) :
    Morse.conjSpace (sphSub m) γ hc 0 1 = Morse.conjSpace (sphSub m) γ' hc' 0 1 := by
  ext K
  rw [Morse.mem_conjSpace hc, Morse.mem_conjSpace hc', Morse.mem_jacobiSpace hc,
    Morse.mem_jacobiSpace hc']
  exact ⟨fun h => ⟨⟨congr_curve' h.1.1 heq, h.1.2⟩, h.2⟩,
    fun h => ⟨⟨congr_curve' h.1.1 heq.symm, h.1.2⟩, h.2⟩⟩

/-- A copy of the project's proof that great circles are geodesics (`Morse.isGeodesicOn_greatCircle`
is one of the item's theorems, so `B_to_A_emb` uses this copy). -/
theorem isGeodesicOn_greatCircle' {p u : 𝔼} (hp : p ∈ Sph m) (hu : ‖u‖ = 1)
    (hpu : ⟪p, u⟫ = 0) (L : ℝ) : Morse.IsGeodesicOn (sphSub m) (Morse.greatCircle p u L) univ := by
  have hp1 := Morse.norm_of_mem_sph hp
  refine Morse.isGeodesicOn_of_deriv_deriv_eq (sphSub m) isOpen_univ
    (fun t _ => Morse.greatCircle_mem_sph hp hu hpu L t) (Morse.contDiff_greatCircle p u L).contDiffOn
    fun t _ => ?_
  have hT : deriv (Morse.greatCircle p u L) t ∈
      Morse.tangentSubspace (sphSub m) ⟨Morse.greatCircle p u L t, Morse.greatCircle_mem_sph hp hu hpu L t⟩ := by
    rw [Morse.mem_tangentSubspace_sph_iff, Morse.deriv_greatCircle]
    change ⟪Morse.greatCircle p u L t, L • Morse.greatCircle u (-p) L t⟫ = 0
    rw [real_inner_smul_right, Morse.inner_greatCircle_greatCircle hp1 hu hpu, mul_zero]
  rw [Morse.secondFundForm_sph hT hT, Morse.deriv_deriv_greatCircle, Morse.deriv_greatCircle]
  have hpu' : ⟪u, -p⟫ = 0 := by rw [inner_neg_right, real_inner_comm, hpu, neg_zero]
  rw [real_inner_smul_left, real_inner_smul_right,
    Morse.inner_greatCircle_self hu (by rw [norm_neg, hp1]) hpu' L t]
  simp only [mul_one, sq]

/-- On a great circle from `p` to `-p`, `cos L = -1` and `sin L = 0`. -/
theorem cos_sin_of_antipodal {p u : 𝔼} (hp : p ∈ Sph m) (hu : ‖u‖ = 1) (hpu : ⟪p, u⟫ = 0) {L : ℝ}
    (h : Morse.greatCircle p u L 1 = -p) : Real.cos L = -1 ∧ Real.sin L = 0 := by
  have hp1 := Morse.norm_of_mem_sph hp
  have hpp : ⟪p, p⟫ = 1 := by rw [real_inner_self_eq_norm_sq, hp1, one_pow]
  have huu : ⟪u, u⟫ = 1 := by rw [real_inner_self_eq_norm_sq, hu, one_pow]
  have hup : ⟪u, p⟫ = 0 := by rw [real_inner_comm, hpu]
  simp only [Morse.greatCircle, mul_one] at h
  have h1 := congrArg (fun x => ⟪p, x⟫) h
  have h2 := congrArg (fun x => ⟪u, x⟫) h
  simp only [inner_add_right, real_inner_smul_right, inner_neg_right, hpp, huu, hpu, hup] at h1 h2
  constructor <;> linarith

theorem sin_eq_zero_of_cos {L : ℝ} (h : Real.cos L = -1) : Real.sin L = 0 := by
  have := Real.sin_sq_add_cos_sq L
  rw [h] at this
  exact pow_eq_zero_iff (n := 2) (by norm_num) |>.1 (by linarith)

theorem exists_nat_of_sin {L : ℝ} (hL : 0 < L) (hsin : Real.sin L = 0) :
    ∃ j : ℕ, L * 1 = j * π := by
  obtain ⟨k, hk⟩ := Real.sin_eq_zero_iff.1 hsin
  have hk0 : 0 ≤ k := by
    by_contra hneg
    have : (k : ℝ) * π < 0 := mul_neg_of_neg_of_pos (by exact_mod_cast not_le.1 hneg) Real.pi_pos
    linarith
  exact ⟨k.toNat, by
    rw [mul_one, ← hk]
    congr 1
    exact_mod_cast (Int.toNat_of_nonneg hk0).symm⟩

end Sphere

end Emb

open Milnor.Sphere in
/-- Clauses (1), (2) of B on the embedded sphere: `M = ↥Sⁿ` (`Bridge.Sub (sphSub n)`, model `ℝⁿ`,
induced metric and connection `Bridge.conn`), antipodality read in `ℝⁿ⁺¹`. (Clause (3), the
nullity of `E_**`, needs a dictionary for the blind `HessT`, which is not available.) -/
def B_emb12 : Prop :=
  ∀ (n : ℕ), 2 ≤ n → ∀ (γ : ℝ → Bridge.Sub (sphSub n)),
    IsGeodesic (Bridge.conn (hN := sphSub n)) γ (Set.Icc 0 1) →
    Bridge.incl (sphSub n) (γ 1) = -Bridge.incl (sphSub n) (γ 0) →
    IsConj (Bridge.conn (hN := sphSub n)) γ 0 1 ∧
      conjMult (Bridge.conn (hN := sphSub n)) γ 0 1 = ((n - 1 : ℕ) : ℕ∞)

open Emb Bridge Milnor.Sphere Real in
/-- **A implies clauses (1), (2) of B on the embedded sphere** (uses A's `isGeodesicOn_greatCircle`
and `conjMultiplicity_greatCircle`; uniqueness of blind geodesics `Bridge.eqOn_Icc_of_isGeodesic`
identifies `γ` with a great circle). -/
theorem A_to_B_emb12 : A → B_emb12 := by
  intro hA n hn γ hγ hanti
  have hn1 : 1 ≤ n := by omega
  have uI : UniqueDiffOn ℝ (Icc (0 : ℝ) 1) := uniqueDiffOn_Icc zero_lt_one
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have h1 : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨zero_le_one, le_rfl⟩
  have hc : IsSmoothCurve (n := n) γ (Icc 0 1) := hγ.2.1
  have hcc : Morse.IsSmoothCurveIn (sphSub n) (incl (sphSub n) ∘ γ) :=
    ⟨isSmoothCurve_iff.1 hc, fun t _ => (γ t).2⟩
  set p := incl (sphSub n) (γ 0) with hpdef
  have hp : p ∈ Sph n := (γ 0).2
  set v := derivWithin (incl (sphSub n) ∘ γ) (Icc 0 1) 0 with hvdef
  have hv : ⟪p, v⟫ = 0 := by
    have := D_mem (γ 0) (vel (n := n) γ (Icc 0 1) 0)
    rw [show D (sphSub n) (γ 0) (vel (n := n) γ (Icc 0 1) 0) = v from D_vel hc uI h0] at this
    exact (Morse.mem_tangentSubspace_sph_iff (γ 0) v).1 this
  obtain ⟨u, hu, hpu, hLu⟩ : ∃ u, ‖u‖ = 1 ∧ ⟪p, u⟫ = 0 ∧ ‖v‖ • u = v := by
    by_cases hv0 : v = 0
    · obtain ⟨u, hu, hpu⟩ := Morse.exists_unit_orthogonal hn1 p
      exact ⟨u, hu, hpu, by rw [hv0, norm_zero, zero_smul]⟩
    · refine ⟨‖v‖⁻¹ • v, ?_, ?_, ?_⟩
      · rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.2 hv0)]
      · rw [real_inner_smul_right, hv, mul_zero]
      · rw [smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.2 hv0), one_smul]
  set L := ‖v‖ with hLdef
  set gc := Morse.greatCircle p u L with hgc
  have hgcN : ∀ t ∈ Icc (0 : ℝ) 1, gc t ∈ Sph n := fun t _ => Morse.greatCircle_mem_sph hp hu hpu L t
  have hgeo : IsGeodesic (Bridge.conn (hN := sphSub n)) (lift gc (γ 0)) (Icc 0 1) :=
    isGeodesic_lift_of (γ 0) (Morse.contDiff_greatCircle p u L).contDiffOn hgcN
      ((hA.1 hp hu hpu L).mono isOpen_Ioo (subset_univ _))
  have hlift : EqOn (incl (sphSub n) ∘ lift gc (γ 0)) gc (Icc 0 1) :=
    fun t ht => incl_lift (γ 0) (hgcN t ht)
  have heq : EqOn γ (lift gc (γ 0)) (Icc 0 1) := by
    refine eqOn_Icc_of_isGeodesic zero_lt_one hγ hgeo ?_ ?_
    · apply Subtype.ext
      show p = (incl (sphSub n) ∘ lift gc (γ 0)) 0
      rw [hlift h0]
      exact (Morse.greatCircle_zero p u L).symm
    · rw [derivWithin_congr hlift (hlift h0)]
      refine Eq.trans ?_ (Morse.velAlong_greatCircle p u L h0).symm
      rw [Morse.greatCircle_zero]
      exact hLu.symm
  have heq' : EqOn (incl (sphSub n) ∘ γ) gc (Icc 0 1) := fun t ht => by
    rw [comp_apply, heq ht]
    exact hlift ht
  -- antipodality forces `L ∈ πℕ`, `L > 0`
  have hanti' : gc 1 = -p := by rw [← heq' h1]; exact hanti
  obtain ⟨hcos, hsin⟩ := cos_sin_of_antipodal hp hu hpu hanti'
  have hL : 0 < L := by
    rcases (norm_nonneg v).lt_or_eq with h | h
    · exact h
    · exfalso
      have hL0 : L = 0 := h.symm
      rw [hL0, Real.cos_zero] at hcos
      norm_num at hcos
  obtain ⟨k, hk⟩ := Real.sin_eq_zero_iff.1 hsin
  have hk0 : 0 ≤ k := by
    by_contra hneg
    have : (k : ℝ) * π < 0 := mul_neg_of_neg_of_pos (by exact_mod_cast not_le.1 hneg) Real.pi_pos
    linarith
  have hex : ∃ j : ℕ, L * 1 = j * π := ⟨k.toNat, by
    rw [mul_one, ← hk]
    congr 1
    exact_mod_cast (Int.toNat_of_nonneg hk0).symm⟩
  have hcgc : Morse.IsSmoothCurveIn (sphSub n) gc := ⟨(Morse.contDiff_greatCircle p u L).contDiffOn, hgcN⟩
  have hmult := hA.2.2 hn1 hp hu hpu hL hcgc (t := 1) ⟨zero_lt_one, le_rfl⟩
  rw [if_pos hex] at hmult
  have hmult' : Morse.conjMultiplicity (sphSub n) (incl (sphSub n) ∘ γ) hcc 0 1 = n - 1 := by
    rw [Morse.conjMultiplicity, conjSpace_congr hcc hcgc heq']
    exact hmult
  refine ⟨isConj_of_pos hc hcc (by rw [hmult']; omega), ?_⟩
  rw [conjMult_eq hc hcc, hmult']

#rt_check RoundTrip.«V9_7″».A_to_B_emb12 [Morse.isGeodesicOn_greatCircle, Morse.isJacobiField_sin_smul,
  Morse.conjMultiplicity_greatCircle]

open Milnor.Sphere in
/-- The identity of `Sⁿ`, from the slice structure `sphSub n` (`Bridge.Sub`) to Mathlib's
`Metric.sphere 0 1`, is a diffeomorphism. -/
noncomputable def sphDiffeo (n : ℕ) [Fact (finrank ℝ (EuclideanSpace ℝ (Fin (n + 1))) = n + 1)] :
    Diffeomorph 𝓘(ℝ, Rn n) 𝓘(ℝ, Rn n) (Bridge.Sub (sphSub n))
      (Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) ∞ where
  toFun x := ⟨Bridge.incl (sphSub n) x, mem_sphere_zero_iff_norm.2 (mem_iff_norm.1 x.2)⟩
  invFun y := ⟨y.1, mem_iff_norm.2 (mem_sphere_zero_iff_norm.1 y.2)⟩
  left_inv _ := rfl
  right_inv _ := rfl
  contMDiff_toFun := ContMDiff.codRestrict_sphere Bridge.contMDiff_incl
    fun x => mem_sphere_zero_iff_norm.2 (mem_iff_norm.1 x.2)
  contMDiff_invFun := Emb.contMDiff_of_incl contMDiff_coe_sphere

open Milnor.Sphere in
/-- `B_emb12` follows from B: specialize to `M = ↥Sⁿ` (`Bridge.Sub (sphSub n)`, connected for
`n ≥ 1`), `Bridge.conn`, and the isometric diffeomorphism `sphDiffeo n` to Mathlib's sphere. -/
theorem B_to_B_emb12 : B → B_emb12 := by
  intro hB n hn γ hγ hanti
  have : Fact (finrank ℝ (EuclideanSpace ℝ (Fin (n + 1))) = n + 1) := ⟨finrank_euclideanSpace_fin⟩
  have : ConnectedSpace (Bridge.Sub (sphSub n)) := by
    have : PreconnectedSpace (Sph n) := preconnectedSpace (by omega)
    obtain ⟨x, hx⟩ := nonempty_sph_set (n := n)
    exact { toPreconnectedSpace := this, toNonempty := ⟨⟨x, hx⟩⟩ }
  have h := hB n hn (Bridge.Sub (sphSub n)) Bridge.conn Bridge.conn_isLC (sphDiffeo n)
    (fun p v w => rfl) γ hγ hanti
  exact ⟨h.1, h.2.1⟩

open Milnor.Sphere in
/-- The part of A that `B_emb12` covers: A's multiplicity formula at `t = 1` for a great circle
from `p` to `-p` (`cos L = −1`, `L > 0`), `n ≥ 2`. -/
def A_emb : Prop :=
  ∀ (n : ℕ), 2 ≤ n → ∀ (p u : EuclideanSpace ℝ (Fin (n + 1))) (L : ℝ), p ∈ Sph n → ‖u‖ = 1 →
    ⟪p, u⟫ = 0 → 0 < L → Real.cos L = -1 →
    ∀ hc : Morse.IsSmoothCurveIn (sphSub n) (Morse.greatCircle p u L),
      Morse.conjMultiplicity (sphSub n) (Morse.greatCircle p u L) hc 0 1 = n - 1

open Emb in
theorem A_to_A_emb : A → A_emb := fun hA n hn _ _ L hp hu hpu hL hcos hc => by
  have h := hA.2.2 (by omega) hp hu hpu hL hc (t := 1) ⟨zero_lt_one, le_rfl⟩
  rwa [if_pos (exists_nat_of_sin hL (sin_eq_zero_of_cos hcos))] at h

open Emb Bridge Milnor.Sphere in
/-- **B implies A's multiplicity formula for antipodal great circles** (`n ≥ 2`), by specializing
B to the embedded sphere and the lifted great circle (a geodesic by a copy of the project's
computation, `isGeodesicOn_greatCircle'`). -/
theorem B_to_A_emb : B → A_emb := by
  intro hB n hn p u L hp hu hpu hL hcos hc
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have h1 : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨zero_le_one, le_rfl⟩
  set q : Bridge.Sub (sphSub n) := ⟨p, hp⟩
  set gc := Morse.greatCircle p u L with hgc
  have hgcN : ∀ t ∈ Icc (0 : ℝ) 1, gc t ∈ Sph n := fun t _ => Morse.greatCircle_mem_sph hp hu hpu L t
  have hgeo : IsGeodesic (Bridge.conn (hN := sphSub n)) (lift gc q) (Icc 0 1) :=
    isGeodesic_lift_of q (Morse.contDiff_greatCircle p u L).contDiffOn hgcN
      ((isGeodesicOn_greatCircle' hp hu hpu L).mono isOpen_Ioo (subset_univ _))
  have hlift : EqOn (incl (sphSub n) ∘ lift gc q) gc (Icc 0 1) :=
    fun t ht => incl_lift q (hgcN t ht)
  have hanti : incl (sphSub n) (lift gc q 1) = -incl (sphSub n) (lift gc q 0) := by
    rw [show incl (sphSub n) (lift gc q 1) = gc 1 from hlift h1,
      show incl (sphSub n) (lift gc q 0) = gc 0 from hlift h0, hgc, Morse.greatCircle_zero]
    simp only [Morse.greatCircle, mul_one, hcos, sin_eq_zero_of_cos hcos, zero_smul, add_zero,
      neg_one_smul]
  have hc' : Morse.IsSmoothCurveIn (sphSub n) (incl (sphSub n) ∘ lift gc q) :=
    ⟨isSmoothCurve_iff.1 hgeo.2.1, fun t _ => (lift gc q t).2⟩
  have hm := (conjMult_eq_rank hgeo.2.1 hc').symm.trans (B_to_B_emb12 hB n hn _ hgeo hanti).2
  rw [Morse.conjMultiplicity, ← conjSpace_congr hc' hc hlift]
  exact Module.finrank_eq_of_rank_eq (Cardinal.toENat_eq_natCast.1 hm)

#rt_check RoundTrip.«V9_7″».B_to_A_emb [Morse.isGeodesicOn_greatCircle, Morse.isJacobiField_sin_smul,
  Morse.conjMultiplicity_greatCircle]
#rt_overlap RoundTrip.«V9_7″».B_to_A_emb [Morse.isGeodesicOn_greatCircle, Morse.isJacobiField_sin_smul,
  Morse.conjMultiplicity_greatCircle]

end RoundTrip.«V9_7″»
