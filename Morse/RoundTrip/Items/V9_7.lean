import Morse
import RoundTrip.Check
import RoundTrip.Blind.V9_7
import RoundTrip.Bridge

open Set Filter Topology Function Module
open scoped ContDiff Manifold

namespace RoundTrip.V9_7

/-- The project's statement (universes instantiated at 0), for a slice submanifold `N ⊆ V` with the
induced metric (model `Z`, `n = dim Z`): (1) for any smooth curve `γ : [0,1] → N`, the Jacobi fields
along `γ` (normalized to be constant off `[0,1]`) vanishing at `0` form an `n`-dimensional space;
(2) `t ↦ t V_t` is a Jacobi field along a geodesic; (3) `t ↦ t y` is a Jacobi field along a
constant curve; (4) **Remark 14.2**: for a geodesic `γ ∈ Ω(N; p, q)` (smooth on `[0,1]`, geodesic
on `(0,1)`) and `n ≥ 1`, the nullity of `E_**` is `< n` (constant geodesics included). -/
def A : Prop :=
  type_of% @Morse.finrank_jacobiSpace_zero.{0,0,0} ∧ type_of% @Morse.isJacobiField_smul_vel.{0,0,0} ∧
    type_of% @Morse.isJacobiField_const_curve.{0,0,0} ∧ type_of% @Morse.remark_14_2.{0,0,0}

theorem A_holds : A :=
  ⟨@Morse.finrank_jacobiSpace_zero, @Morse.isJacobiField_smul_vel, @Morse.isJacobiField_const_curve,
    @Morse.remark_14_2⟩

/-! Neither `A → B` nor `B → A` is proved; see `V9_7.json`.

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

/-! ### Jacobi fields vanishing at `0`: the blind set and the project's subspace -/

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

/-- The project's space of Jacobi fields along `incl ∘ γ` vanishing at `0`. -/
noncomputable abbrev Kc : Submodule ℝ (ℝ → V) :=
  Morse.jacobiSpace hN (incl hN ∘ γ) hcc ⊓ LinearMap.ker (LinearMap.proj (R := ℝ) (φ := fun _ : ℝ => V) 0)

include hc in
theorem memS_iff (J : FA n γ) :
    (J ∈ JacOn (Bridge.conn (hN := hN)) γ (Icc 0 1) ∧ J 0 = 0) ↔ (J ∈ Zsub γ ∧ Φ γ J ∈ Kc hcc) := by
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have hΦ0 : Φ γ J 0 = D hN (γ 0) (J 0) := Φ_apply_of_mem J h0
  constructor
  · rintro ⟨⟨hJ, hz⟩, hJ0⟩
    refine ⟨hz, ⟨(isJacobiField_of_isJacobi hc hJ).congr fun t ht => (Φ_apply_of_mem J ht).symm,
      Φ_normal J⟩, ?_⟩
    show Φ γ J 0 = 0
    rw [hΦ0, hJ0, D_tzero]
  · rintro ⟨hz, ⟨hJ, -⟩, hJ0⟩
    have hJ0' : Φ γ J 0 = 0 := hJ0
    refine ⟨⟨isJacobi_of_isJacobiField hc (hJ.congr fun t ht => Φ_apply_of_mem J ht), hz⟩, ?_⟩
    apply D_injective (γ 0)
    rw [← hΦ0, hJ0', D_tzero]

/-- The blind set, as a submodule. -/
noncomputable def Ssub : Submodule ℝ (FA n γ) := Zsub γ ⊓ (Kc hcc).comap (Φ γ)

include hc in
theorem S_eq : {J | J ∈ JacOn (Bridge.conn (hN := hN)) γ (Icc 0 1) ∧ J 0 = 0} = (Ssub hcc : Set (FA n γ)) :=
  Set.ext fun J => (memS_iff hc hcc J).trans Iff.rfl

/-- `Φ` is a linear isomorphism from the blind space onto the project's space. -/
noncomputable def Ψ : Ssub hcc →ₗ[ℝ] Kc hcc :=
  ((Φ γ).domRestrict (Ssub hcc)).codRestrict (Kc hcc) fun J => J.2.2

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
  · rintro ⟨K, hK, hK0⟩
    classical
    set J : FA n γ := fun t => if t ∈ Icc (0 : ℝ) 1 then L hN (γ t) (K t) else 0 with hJdef
    have hΦJ : Φ γ J = K := by
      funext t
      show D hN (γ (pI t)) (J (pI t)) = K t
      have hT : P hN (γ (pI t)) (K (pI t)) = K (pI t) := by
        rw [← prj_incl]
        exact hK.1.tangent _ (pI_mem t)
      have hJp : J (pI t) = L hN (γ (pI t)) (K (pI t)) := if_pos (pI_mem t)
      rw [hJp, hK.2 t]
      have := D_L_P (γ (pI t)) (K (pI t))
      rw [hT] at this
      exact this
    have hJZ : J ∈ Zsub γ := fun t ht => if_neg ht
    refine ⟨⟨J, hJZ, ?_⟩, Subtype.ext hΦJ⟩
    show Φ γ J ∈ Kc hcc
    rw [hΦJ]
    exact ⟨hK, hK0⟩

include hc in
/-- **The blind dimension is the project's dimension** (as ranks; no finiteness used). -/
theorem setDim_eq_rank :
    setDim {J | J ∈ JacOn (Bridge.conn (hN := hN)) γ (Icc 0 1) ∧ J 0 = 0} =
      (Module.rank ℝ (Kc hcc)).toENat := by
  unfold setDim
  rw [S_eq hc hcc, Submodule.span_eq, (LinearEquiv.ofBijective (Ψ hcc) (Ψ_bijective hcc)).rank_eq]

include hc in
theorem setDim_eq :
    setDim {J | J ∈ JacOn (Bridge.conn (hN := hN)) γ (Icc 0 1) ∧ J 0 = 0} =
      (finrank ℝ (Kc hcc) : ℕ∞) := by
  have hfin : FiniteDimensional ℝ (Kc hcc) :=
    Submodule.finiteDimensional_of_le (inf_le_left :
      Kc hcc ≤ Morse.jacobiSpace hN (incl hN ∘ γ) hcc)
  rw [setDim_eq_rank hc hcc, ← finrank_eq_rank]
  simp

theorem ambA_ite (F : FA n γ) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    ambA γ (fun s => if s ∈ Icc (0 : ℝ) 1 then F s else 0) t = ambA γ F t :=
  congrArg (D hN (γ t)) (if_pos ht)

end Dim

end Emb

/-- Clauses (2) and (3) of B on embedded manifolds (`M = ↥N`, model `ℝⁿ`, connected, induced
metric and connection `Bridge.conn`): the Jacobi fields vanishing at `0` form an `n`-dimensional
space, and `t V_t` is a Jacobi field vanishing at `0` and not at `1`. (Clause (1), the nullity of
`E_**`, needs a dictionary for the blind `HessT`, which is not available.) -/
def B_emb23 : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    (Y : Type) [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y] (n : ℕ)
    (N : Set V) (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) (Rn n) Y N) [ConnectedSpace (Bridge.Sub hN)]
    (γ : ℝ → Bridge.Sub hN), IsGeodesic (Bridge.conn (hN := hN)) γ (Set.Icc 0 1) →
    vel (n := n) γ (Set.Icc 0 1) 0 ≠ 0 →
    setDim {J | J ∈ JacOn (Bridge.conn (hN := hN)) γ (Set.Icc 0 1) ∧ J 0 = 0} = (n : ℕ∞) ∧
    (let Jt : FA n γ := fun t => if t ∈ Set.Icc (0:ℝ) 1 then t • vel (n := n) γ (Set.Icc 0 1) t else 0
     Jt ∈ JacOn (Bridge.conn (hN := hN)) γ (Set.Icc 0 1) ∧ Jt 0 = 0 ∧ Jt 1 ≠ 0)

/-- `B_emb23` follows from B (specialize to `↥N`, `Bridge.conn`, and drop clause (1)). -/
theorem B_to_B_emb23 : B → B_emb23 := fun hB _ _ _ _ _ _ _ _ n _ hN _ γ hγ hv =>
  (hB n (Bridge.Sub hN) (Bridge.conn (hN := hN)) Bridge.conn_isLC γ hγ hv).2

/-- The part of A that `B_emb23` covers: for connected slice submanifolds modelled on `ℝⁿ` and a
geodesic `γ : [0,1] → N` with `γ'(0) ≠ 0`, A's (1) and (2). -/
def A_emb : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    (Y : Type) [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y] (n : ℕ)
    (N : Set V) (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) (Rn n) Y N) [ConnectedSpace (Bridge.Sub hN)]
    (γ : ℝ → V) (hc : Morse.IsSmoothCurveIn hN γ), Morse.IsGeodesicOn hN γ (Ioo 0 1) →
    Morse.velAlong γ 0 ≠ 0 →
    finrank ℝ (Morse.jacobiSpace hN γ hc ⊓ LinearMap.ker (LinearMap.proj (R := ℝ)
      (φ := fun _ : ℝ => V) 0) : Submodule ℝ (ℝ → V)) = n ∧
    Morse.IsJacobiField hN γ (fun t => t • Morse.velAlong γ t)

theorem A_to_A_emb : A → A_emb := fun hA _ _ _ _ _ _ _ _ n _ _ _ _ hc hgeo _ =>
  ⟨(hA.1 hc).trans (finrank_euclideanSpace_fin (𝕜 := ℝ) (n := n)), hA.2.1 hc hgeo⟩

open Emb Bridge in
/-- **A implies clauses (2), (3) of B on embedded manifolds** (uses A's
`finrank_jacobiSpace_zero` and `isJacobiField_smul_vel`; the project lemma
`eq_const_of_velAlong_one_eq_zero` (constant speed) for `J_1 ≠ 0`). -/
theorem A_to_B_emb23 : A → B_emb23 := by
  intro hA V _ _ _ Y _ _ _ n N hN _ γ hγ hv
  have hc : IsSmoothCurve (n := n) γ (Icc 0 1) := hγ.2.1
  have uI : UniqueDiffOn ℝ (Icc (0 : ℝ) 1) := uniqueDiffOn_Icc zero_lt_one
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have h1 : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨zero_le_one, le_rfl⟩
  have hcc : Morse.IsSmoothCurveIn hN (incl hN ∘ γ) := ⟨isSmoothCurve_iff.1 hc, fun t _ => (γ t).2⟩
  have hgeo := isGeodesicOn_Ioo hγ
  have hvel : ∀ t ∈ Icc (0 : ℝ) 1, D hN (γ t) (vel (n := n) γ (Icc 0 1) t) =
      Morse.velAlong (incl hN ∘ γ) t := fun t ht => D_vel hc uI ht
  refine ⟨?_, ⟨?_, fun t ht => ?_⟩, ?_, ?_⟩
  · rw [setDim_eq hc hcc, hA.1 hcc, finrank_euclideanSpace_fin]
  · refine isJacobi_of_isJacobiField hc ((hA.2.1 hcc hgeo).congr fun t ht => ?_)
    rw [ambA_ite _ ht]
    show t • Morse.velAlong (incl hN ∘ γ) t = D hN (γ t) (t • vel (n := n) γ (Icc 0 1) t)
    rw [D_tsmul, hvel t ht]
  · exact if_neg ht
  · exact (if_pos h0).trans (zero_smul ℝ _)
  · intro h'
    have h : vel (n := n) γ (Icc 0 1) 1 = 0 :=
      (one_smul ℝ (vel (n := n) γ (Icc 0 1) 1)).symm.trans ((if_pos h1).symm.trans h')
    have hV1 : Morse.velAlong (incl hN ∘ γ) 1 = 0 := by rw [← hvel 1 h1, h, D_tzero]
    have hconst := Morse.eq_const_of_velAlong_one_eq_zero hcc hgeo hV1
    apply hv
    apply D_injective (γ 0)
    rw [hvel 0 h0, D_tzero]
    show derivWithin (incl hN ∘ γ) (Icc 0 1) 0 = 0
    rw [derivWithin_congr hconst (hconst 0 h0)]
    simp

open Emb Bridge in
/-- **B implies A's (1) and (2) for geodesics with `γ'(0) ≠ 0`** in connected slice submanifolds
modelled on `ℝⁿ`, by specializing B to `↥N` and the lifted geodesic. -/
theorem B_to_A_emb : B → A_emb := by
  intro hB V _ _ _ Y _ _ _ n N hN _ γ hc hgeo hv
  have uI : UniqueDiffOn ℝ (Icc (0 : ℝ) 1) := uniqueDiffOn_Icc zero_lt_one
  have h0I : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  set q : Bridge.Sub hN := ⟨γ 0, hc.mem 0 h0I⟩
  have hγ' : IsGeodesic (Bridge.conn (hN := hN)) (lift γ q) (Icc 0 1) :=
    isGeodesic_lift_of q hc.contDiffOn hc.mem hgeo
  have hc' : IsSmoothCurve (n := n) (lift γ q) (Icc 0 1) := hγ'.2.1
  have heq : EqOn (incl hN ∘ lift γ q) γ (Icc 0 1) := fun t ht => incl_lift q (hc.mem t ht)
  have hcc : Morse.IsSmoothCurveIn hN (incl hN ∘ lift γ q) :=
    ⟨isSmoothCurve_iff.1 hc', fun t _ => (lift γ q t).2⟩
  have hvel : ∀ t ∈ Icc (0 : ℝ) 1, D hN (lift γ q t) (vel (n := n) (lift γ q) (Icc 0 1) t) =
      Morse.velAlong γ t := fun t ht =>
    (D_vel hc' uI ht).trans (derivWithin_congr heq (heq ht))
  have hv' : vel (n := n) (lift γ q) (Icc 0 1) 0 ≠ 0 := fun h => hv (by
    rw [← hvel 0 h0I, h, D_tzero])
  obtain ⟨hdim, hJt, -, -⟩ := B_to_B_emb23 hB V Y n N hN (lift γ q) hγ' hv'
  refine ⟨?_, ?_⟩
  · -- the two project subspaces coincide (Jacobi fields only see `γ|[0,1]`)
    have e : (Morse.jacobiSpace hN γ hc ⊓ LinearMap.ker (LinearMap.proj (R := ℝ)
        (φ := fun _ : ℝ => V) 0) : Submodule ℝ (ℝ → V)) = Kc hcc := by
      ext K
      simp only [Submodule.mem_inf, Morse.mem_jacobiSpace]
      exact ⟨fun h => ⟨⟨congr_curve' h.1.1 heq.symm, h.1.2⟩, h.2⟩,
        fun h => ⟨⟨congr_curve' h.1.1 heq, h.1.2⟩, h.2⟩⟩
    rw [e]
    have := (setDim_eq_rank hc' hcc).symm.trans hdim
    exact Module.finrank_eq_of_rank_eq (Cardinal.toENat_eq_natCast.1 this)
  · have hJ := isJacobiField_of_isJacobi hc' hJt.1
    refine congr_curve' (hJ.congr fun t ht => ?_) heq
    rw [ambA_ite _ ht]
    show D hN (lift γ q t) (t • vel (n := n) (lift γ q) (Icc 0 1) t) = t • Morse.velAlong γ t
    rw [D_tsmul, hvel t ht]

#rt_check RoundTrip.V9_7.A_to_B_emb23 [Morse.finrank_jacobiSpace_zero, Morse.isJacobiField_smul_vel,
  Morse.isJacobiField_const_curve, Morse.remark_14_2]
#rt_check RoundTrip.V9_7.B_to_A_emb [Morse.finrank_jacobiSpace_zero, Morse.isJacobiField_smul_vel,
  Morse.isJacobiField_const_curve, Morse.remark_14_2]
#rt_overlap RoundTrip.V9_7.B_to_A_emb [Morse.finrank_jacobiSpace_zero, Morse.isJacobiField_smul_vel,
  Morse.isJacobiField_const_curve, Morse.remark_14_2]

end RoundTrip.V9_7
