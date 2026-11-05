import Morse
import RoundTrip.Check
import RoundTrip.Blind.«V9_7′»
import RoundTrip.Bridge

open Set Filter Topology Function Module
open scoped ContDiff Manifold

namespace RoundTrip.«V9_7′»

/-- The project's statement (universes instantiated at 0): (0) an open subset of `V` is a slice
submanifold (model `V`, `W` trivial); for a slice submanifold `N ⊆ V` of **codimension 0**
(`htop`: every tangent space is all of `V`): (1) the curvature vanishes; (2) along any curve lying
in `N` on `(0,1)`, every Jacobi field is affine on `[0,1]`; (3) no two parameter values are
conjugate along such a curve; (4) along a geodesic `γ ∈ Ω(N; p, q)` the nullity of `E_**` is `0`. -/
def A : Prop :=
  type_of% @Morse.isSliceSubmanifold_of_isOpen.{0,0} ∧ type_of% @Morse.curvR_eq_zero_of_top.{0,0,0} ∧
    type_of% @Morse.IsJacobiField.eqOn_affine_of_top.{0,0,0} ∧
    type_of% @Morse.not_isConjugate_of_top.{0,0,0} ∧ type_of% @Morse.hessNullity_eq_zero_of_top.{0,0,0}

theorem A_holds : A :=
  ⟨@Morse.isSliceSubmanifold_of_isOpen, @Morse.curvR_eq_zero_of_top,
    @Morse.IsJacobiField.eqOn_affine_of_top, @Morse.not_isConjugate_of_top,
    @Morse.hessNullity_eq_zero_of_top⟩

/-! Neither `A → B` nor `B → A` is proved; see `V9_7′.json`.

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

/-! ### Conjugate points -/

theorem exists_ne_zero_of_jacOn {γ : ℝ → Bridge.Sub hN} {J : FA n γ}
    (hJ : J ∈ JacOn (Bridge.conn (hN := hN)) γ (Icc 0 1)) (hJ0 : J ≠ 0) :
    ∃ t ∈ Icc (0 : ℝ) 1, J t ≠ 0 := by
  by_contra h
  simp only [not_exists, not_and, not_not] at h
  apply hJ0
  funext t
  by_cases ht : t ∈ Icc (0 : ℝ) 1
  · exact h t ht
  · exact hJ.2 t ht

/-- Blind conjugate parameters give project conjugate parameters. -/
theorem isConjugate_of_blind {γ : ℝ → Bridge.Sub hN} (hc : IsSmoothCurve (n := n) γ (Icc 0 1))
    {a b : ℝ} (ha : a ∈ Icc (0 : ℝ) 1) (hb : b ∈ Icc (0 : ℝ) 1)
    (h : IsConj (Bridge.conn (hN := hN)) γ a b) : Morse.IsConjugate hN (incl hN ∘ γ) a b := by
  obtain ⟨hab, J, hJ, hJ0, hJa, hJb⟩ := h
  obtain ⟨t, ht, hJt⟩ := exists_ne_zero_of_jacOn hJ hJ0
  refine ⟨ha, hb, hab, ambA γ J, isJacobiField_of_isJacobi hc hJ.1, ?_, ?_, t, ht, fun h => hJt ?_⟩
  · show D hN (γ a) (J a) = 0
    rw [hJa, D_tzero]
  · show D hN (γ b) (J b) = 0
    rw [hJb, D_tzero]
  · exact D_injective (γ t) (h.trans (D_tzero (γ t)).symm)

/-- Project conjugate parameters give blind conjugate parameters. -/
theorem blind_of_isConjugate {γ : ℝ → Bridge.Sub hN} (hc : IsSmoothCurve (n := n) γ (Icc 0 1))
    {a b : ℝ} (h : Morse.IsConjugate hN (incl hN ∘ γ) a b) : IsConj (Bridge.conn (hN := hN)) γ a b := by
  classical
  obtain ⟨ha, hb, hab, K, hK, hKa, hKb, t, ht, hKt⟩ := h
  set J : FA n γ := fun s => if s ∈ Icc (0 : ℝ) 1 then L hN (γ s) (K s) else 0 with hJdef
  have hJK : ∀ s ∈ Icc (0 : ℝ) 1, ambA γ J s = K s := fun s hs => by
    have hT : P hN (γ s) (K s) = K s := by rw [← prj_incl]; exact hK.tangent s hs
    have hJs : J s = L hN (γ s) (K s) := if_pos hs
    show D hN (γ s) (J s) = K s
    rw [hJs]
    have := D_L_P (γ s) (K s)
    rw [hT] at this
    exact this
  have hJ : J ∈ JacOn (Bridge.conn (hN := hN)) γ (Icc 0 1) :=
    ⟨isJacobi_of_isJacobiField hc (hK.congr fun s hs => (hJK s hs).symm), fun s hs => if_neg hs⟩
  refine ⟨hab, J, hJ, fun h0 => hKt ?_, ?_, ?_⟩
  · rw [← hJK t ht, h0]
    exact D_tzero (γ t)
  · apply D_injective (γ a)
    rw [D_tzero]
    exact (hJK a ha).trans hKa
  · apply D_injective (γ b)
    rw [D_tzero]
    exact (hJK b hb).trans hKb

end Emb

/-- B on embedded manifolds of **codimension 0** (`M = ↥N`, model `ℝⁿ`, connected, every tangent
space all of `V`; induced metric and connection `Bridge.conn`), clauses (1)–(3): for a geodesic
`γ : [0,1] → ↥N`, the Jacobi equation is `D²J/dt² = 0`, a non-zero Jacobi field has at most one
zero, and there are no conjugate points. (Clause (4), the nullity of `E_**`, needs a dictionary for
the blind `HessT`, which is not available.) -/
def B_emb_top : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    (Y : Type) [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y] (n : ℕ)
    (N : Set V) (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) (Rn n) Y N) [ConnectedSpace (Bridge.Sub hN)],
    (∀ q : N, Morse.tangentSubspace hN q = ⊤) →
    (∀ (p : Bridge.Sub hN) (x y z r : TangentSpace 𝓘(ℝ, Rn n) p),
      IsCurvVal (Bridge.conn (hN := hN)) p x y z r → r = 0) →
    ∀ (γ : ℝ → Bridge.Sub hN), IsGeodesic (Bridge.conn (hN := hN)) γ (Set.Icc 0 1) →
    (∀ J : FA n γ, IsJacobi (Bridge.conn (hN := hN)) γ (Set.Icc 0 1) J ↔
      ∃ J' J'' : FA n γ, HasCovDeriv (Bridge.conn (hN := hN)) γ (Set.Icc 0 1) J J' ∧
        HasCovDeriv (Bridge.conn (hN := hN)) γ (Set.Icc 0 1) J' J'' ∧
        ∀ t ∈ Set.Icc (0:ℝ) 1, J'' t = 0) ∧
    (∀ J ∈ JacOn (Bridge.conn (hN := hN)) γ (Set.Icc 0 1), J ≠ 0 → ∀ t₁ ∈ Set.Icc (0:ℝ) 1,
      ∀ t₂ ∈ Set.Icc (0:ℝ) 1, J t₁ = 0 → J t₂ = 0 → t₁ = t₂) ∧
    (∀ a ∈ Set.Icc (0:ℝ) 1, ∀ b ∈ Set.Icc (0:ℝ) 1, ¬ IsConj (Bridge.conn (hN := hN)) γ a b)

/-- `B_emb_top` follows from B (specialize to `↥N`, `Bridge.conn`, and drop clause (4)). -/
theorem B_to_B_emb_top : B → B_emb_top := fun hB _ _ _ _ _ _ _ _ n _ hN _ _ hflat γ hγ =>
  let h := hB n (Bridge.Sub hN) (Bridge.conn (hN := hN)) Bridge.conn_isLC hflat γ hγ
  ⟨h.1, h.2.1, h.2.2.1⟩

open Emb Bridge in
/-- **A implies clauses (1)–(3) of B on codimension-0 embedded manifolds** (uses A's
`curvR_eq_zero_of_top` and `not_isConjugate_of_top`). -/
theorem A_to_B_emb_top : A → B_emb_top := by
  intro hA V _ _ _ Y _ _ _ n N hN _ htop hflat γ hγ
  have hc : IsSmoothCurve (n := n) γ (Icc 0 1) := hγ.2.1
  have hnc : ∀ a ∈ Icc (0 : ℝ) 1, ∀ b ∈ Icc (0 : ℝ) 1, ¬ IsConj (Bridge.conn (hN := hN)) γ a b :=
    fun a ha b hb h => hA.2.2.2.1 htop (fun t _ => (γ t).2) a b (isConjugate_of_blind hc ha hb h)
  refine ⟨fun J => ⟨?_, ?_⟩, fun J hJ hJ0 t₁ ht₁ t₂ ht₂ h₁ h₂ => ?_, hnc⟩
  · rintro ⟨J', J'', h1, h2, h3⟩
    refine ⟨J', J'', h1, h2, fun t ht => ?_⟩
    obtain ⟨r, hr, hr0⟩ := h3 t ht
    rw [hflat _ _ _ _ _ hr, add_zero] at hr0
    exact hr0
  · rintro ⟨J', J'', h1, h2, h3⟩
    refine ⟨J', J'', h1, h2, fun t ht => ⟨0, ?_, by rw [h3 t ht, add_zero]⟩⟩
    refine (isCurvVal_iff (γ t) (vel (n := n) γ (Icc 0 1) t) (J t) (vel (n := n) γ (Icc 0 1) t) 0).2 ?_
    rw [D_tzero, hA.2.1 htop]
  · by_contra hne
    exact hnc t₁ ht₁ t₂ ht₂ ⟨hne, J, hJ, hJ0, h₁, h₂⟩

/-- The part of A that `B_emb_top` covers: A's (3) (no conjugate points) along geodesics `γ`
smooth on `[0,1]`, in connected codimension-0 slice submanifolds modelled on `ℝⁿ`. -/
def A_emb : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    (Y : Type) [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y] (n : ℕ)
    (N : Set V) (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) (Rn n) Y N) [ConnectedSpace (Bridge.Sub hN)],
    (∀ q : N, Morse.tangentSubspace hN q = ⊤) →
    ∀ (γ : ℝ → V), Morse.IsSmoothCurveIn hN γ → Morse.IsGeodesicOn hN γ (Ioo 0 1) →
    ∀ a b : ℝ, ¬ Morse.IsConjugate hN γ a b

theorem A_to_A_emb : A → A_emb := fun hA _ _ _ _ _ _ _ _ _ _ _ _ htop _ hc _ a b =>
  hA.2.2.2.1 htop (fun t ht => hc.mem t (Ioo_subset_Icc_self ht)) a b

open Emb Bridge in
/-- **B implies A's "no conjugate points"** along geodesics in connected codimension-0 slice
submanifolds modelled on `ℝⁿ` (flatness, B's hypothesis, is re-derived from the vanishing of
the second fundamental form, `Morse.secondFundForm_eq_zero_of_top`). -/
theorem B_to_A_emb : B → A_emb := by
  intro hB V _ _ _ Y _ _ _ n N hN _ htop γ hc hgeo a b h
  have h0I : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  set q : Bridge.Sub hN := ⟨γ 0, hc.mem 0 h0I⟩
  have hγ' : IsGeodesic (Bridge.conn (hN := hN)) (lift γ q) (Icc 0 1) :=
    isGeodesic_lift_of q hc.contDiffOn hc.mem hgeo
  have hflat : ∀ (p : Bridge.Sub hN) (x y z r : TangentSpace 𝓘(ℝ, Rn n) p),
      IsCurvVal (Bridge.conn (hN := hN)) p x y z r → r = 0 := by
    intro p x y z r hr
    have h1 := (isCurvVal_iff p x y z r).1 hr
    have e : ∀ a b c : V, Morse.curvR hN (incl hN p) a b c = 0 := fun a b c => by
      refine (Morse.curvR_of_mem hN p.2 a b c).trans ?_
      rw [Morse.curvOp_apply, Morse.secondFundForm_eq_zero_of_top htop,
        Morse.secondFundForm_eq_zero_of_top htop, sub_zero]
    rw [e] at h1
    exact D_injective p (h1.trans (D_tzero p).symm)
  have heq : EqOn γ (incl hN ∘ lift γ q) (Icc 0 1) := fun t ht => (incl_lift q (hc.mem t ht)).symm
  obtain ⟨ha, hb, hab, K, hK, hKa, hKb, t, ht, hKt⟩ := h
  have h' : Morse.IsConjugate hN (incl hN ∘ lift γ q) a b :=
    ⟨ha, hb, hab, K, congr_curve' hK heq, hKa, hKb, t, ht, hKt⟩
  exact (B_to_B_emb_top hB V Y n N hN htop hflat (lift γ q) hγ').2.2 a ha b hb
    (blind_of_isConjugate hγ'.2.1 h')

#rt_check RoundTrip.«V9_7′».A_to_B_emb_top [Morse.isSliceSubmanifold_of_isOpen,
  Morse.curvR_eq_zero_of_top, Morse.IsJacobiField.eqOn_affine_of_top, Morse.not_isConjugate_of_top,
  Morse.hessNullity_eq_zero_of_top]
#rt_check RoundTrip.«V9_7′».B_to_A_emb [Morse.isSliceSubmanifold_of_isOpen,
  Morse.curvR_eq_zero_of_top, Morse.IsJacobiField.eqOn_affine_of_top, Morse.not_isConjugate_of_top,
  Morse.hessNullity_eq_zero_of_top]
#rt_overlap RoundTrip.«V9_7′».B_to_A_emb [Morse.isSliceSubmanifold_of_isOpen,
  Morse.curvR_eq_zero_of_top, Morse.IsJacobiField.eqOn_affine_of_top, Morse.not_isConjugate_of_top,
  Morse.hessNullity_eq_zero_of_top]

end RoundTrip.«V9_7′»
