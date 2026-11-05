import Morse
import RoundTrip.Check
import RoundTrip.Blind.V9_10
import RoundTrip.Bridge

open Set Filter Topology Function Module
open scoped ContDiff Manifold

namespace RoundTrip.V9_10

/-- The project's statement (universes instantiated at `0`): for a slice submanifold `N ⊆ V` with
the induced metric and ANY smooth curve `γ` in `N` on `[0, 1]` (not only geodesics), if `a ≠ b` in
`[0, 1]` are not conjugate along `γ`, then `J ↦ (J(a), J(b))` is a linear isomorphism from the
space `𝒥(γ)` of Jacobi fields onto `T_{γ(a)}N × T_{γ(b)}N` (injective: determined by the values;
surjective: the values can be prescribed). `Morse.jacEvalEnds` is vocabulary. -/
def A : Prop := type_of% @Morse.jacEvalEnds_bijective_of_not_isConjugate.{0, 0, 0}

theorem A_holds : A := @Morse.jacEvalEnds_bijective_of_not_isConjugate

/-! Neither `A → B` nor `B → A` is proved: B quantifies over abstract connected Hausdorff
`ℝⁿ`-manifolds with an arbitrary smooth metric and an arbitrary Levi-Civita connection, A only
over slice submanifolds `N ⊆ V` with the induced metric. See `V9_10.json`.

## The embedded special case

Dictionary (namespace `Emb`): for the induced connection `Bridge.conn` on `↥N`, a blind Jacobi
field `J` along a curve `γ` on `[0, 1]` is exactly a field whose ambient image `ambA γ J` is a
project Jacobi field `Morse.IsJacobiField hN (incl ∘ γ)` (`isJacobiField_of_isJacobi`,
`isJacobi_of_isJacobiField`; the endpoint values of the Jacobi equation come from continuity,
`jacobi_Icc`), and blind conjugacy is the project's (`isConj_iff`). -/

namespace Emb

set_option linter.unusedSectionVars false

open RoundTrip.Bridge

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W] {n : ℕ} {N : Set V}
  {hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) (Rn n) W N}

theorem prj_incl (x : Bridge.Sub hN) : Morse.prj hN (incl hN x) = P hN x :=
  Morse.prj_of_mem hN x.2

theorem isIntv_Icc : RoundTrip.BridgePrelude.IsIntv (Icc (0 : ℝ) 1) :=
  ⟨ordConnected_Icc, uniqueDiffOn_Icc zero_lt_one⟩

/-- On the interior, `derivWithin [0,1]` of a function smooth on `[0, 1]` is `deriv`, near `t`. -/
theorem derivWithin_eventuallyEq {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : ℝ → E} (hF : ContDiffOn ℝ ∞ F (Icc 0 1)) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    derivWithin F (Icc 0 1) =ᶠ[𝓝 t] deriv F := by
  filter_upwards [Ioo_mem_nhds ht.1 ht.2] with x hx
  exact ((hF.contDiffAt (Icc_mem_nhds hx.1 hx.2)).differentiableAt (by simp)).hasDerivAt
    |>.hasDerivWithinAt.derivWithin (uniqueDiffOn_Icc zero_lt_one x (Ioo_subset_Icc_self hx))

/-- Project side: for a project Jacobi field, the Jacobi equation read with derivatives within
`[0, 1]` holds on all of `[0, 1]` (it is stated on `(0, 1)`; continuity). -/
theorem jacobi_Icc {c X : ℝ → V} (hc : Morse.IsSmoothCurveIn hN c)
    (hX : Morse.IsJacobiField hN c X) :
    ∀ t ∈ Icc (0 : ℝ) 1, Morse.covAlong hN c (Morse.covAlong hN c X) t +
      Morse.curvR hN (c t) (Morse.velAlong c t) (X t) (Morse.velAlong c t) = 0 := by
  have hu := uniqueDiffOn_Icc (zero_lt_one' ℝ)
  have hcov : ContDiffOn ℝ ∞ (Morse.covAlong hN c X) (Icc 0 1) :=
    hc.contDiffOn_prj.clm_apply (hX.contDiffOn.derivWithin hu (by simp))
  have hf : ContinuousOn (fun t => Morse.covAlong hN c (Morse.covAlong hN c X) t +
      Morse.curvR hN (c t) (Morse.velAlong c t) (X t) (Morse.velAlong c t)) (Icc 0 1) := by
    have h1 : ContinuousOn (Morse.covAlong hN c (Morse.covAlong hN c X)) (Icc 0 1) :=
      hc.contDiffOn_prj.continuousOn.clm_apply
        (hcov.derivWithin hu (m := 0) (by simp)).continuousOn
    have h2 : ContinuousOn (fun t => Morse.curvAlong hN c t (X t)) (Icc 0 1) :=
      hc.contDiffOn_curvAlong.continuousOn.clm_apply hX.contDiffOn.continuousOn
    refine h1.add (h2.congr fun t ht => ?_)
    show _ = Morse.curvAlong hN c t (X t)
    rw [Morse.curvAlong_apply (hc.mem t ht), hX.tangent t ht]
  refine EqOn.of_subset_closure (g := fun _ => (0 : V)) ?_ hf continuousOn_const
    Ioo_subset_Icc_self (by rw [closure_Ioo zero_ne_one])
  intro t ht
  have e1 : Morse.covAlong hN c X =ᶠ[𝓝 t] Morse.covD hN c X := by
    filter_upwards [derivWithin_eventuallyEq hX.contDiffOn ht] with x hx
    rw [Morse.covAlong, Morse.covD, hx]
  have e2 : Morse.covAlong hN c (Morse.covAlong hN c X) t =
      Morse.covD hN c (Morse.covD hN c X) t := by
    rw [Morse.covAlong, Morse.covD, (derivWithin_eventuallyEq hcov ht).eq_of_nhds, e1.deriv_eq]
  have := hX.eq t ht
  rw [Morse.jacobiExpr, ← hc.velAlong_eq ht, ← e2] at this
  exact this

/-- **Dictionary, blind ⇒ project**: a blind Jacobi field of the induced connection along `γ` on
`[0, 1]` is, read in `V`, a project Jacobi field along `incl ∘ γ`. -/
theorem isJacobiField_of_isJacobi {γ : ℝ → Bridge.Sub hN} {J : FA n γ}
    (hγ : IsSmoothCurve (n := n) γ (Icc 0 1)) (hJ : IsJacobi (conn (hN := hN)) γ (Icc 0 1) J) :
    Morse.IsJacobiField hN (incl hN ∘ γ) (ambA γ J) := by
  obtain ⟨J', J'', h1, h2, h3⟩ := hJ
  have hγ' : RoundTrip.BridgePrelude.IsSmoothCurve (n := n) γ (Icc 0 1) := hγ
  obtain ⟨h1s, h1e⟩ := (hasCovDeriv_iff' isIntv_Icc hγ').1 h1
  obtain ⟨h2s, h2e⟩ := (hasCovDeriv_iff' isIntv_Icc hγ').1 h2
  have hX := (isSmoothAlong_iff.1 h1s).2
  have hX' := (isSmoothAlong_iff.1 h2s).2
  have hu := uniqueDiffOn_Icc (zero_lt_one' ℝ)
  refine ⟨hX, fun t _ => ?_, fun t ht => ?_⟩
  · show Morse.prj hN (incl hN (γ t)) (D hN (γ t) (J t)) = D hN (γ t) (J t)
    rw [prj_incl]
    exact P_D _ _
  · have htI := Ioo_subset_Icc_self ht
    have e1 : Morse.covD hN (incl hN ∘ γ) (ambA γ J) =ᶠ[𝓝 t] ambA γ J' := by
      filter_upwards [derivWithin_eventuallyEq hX ht, Ioo_mem_nhds ht.1 ht.2] with x hx hx'
      rw [Morse.covD, ← hx, h1e x (Ioo_subset_Icc_self hx')]
      show Morse.prj hN (incl hN (γ x)) _ = _
      rw [prj_incl]
    have e2 : Morse.covD hN (incl hN ∘ γ) (Morse.covD hN (incl hN ∘ γ) (ambA γ J)) t =
        ambA γ J'' t := by
      rw [Morse.covD, e1.deriv_eq, ← (derivWithin_eventuallyEq hX' ht).eq_of_nhds, h2e t htI]
      show Morse.prj hN (incl hN (γ t)) _ = _
      rw [prj_incl]
    obtain ⟨r, hr, hr0⟩ := h3 t htI
    have hr' := (isCurvVal_iff (γ t) _ _ _ r).1 hr
    have hvel : D hN (γ t) (vel (n := n) γ (Icc 0 1) t) = deriv (incl hN ∘ γ) t := by
      have h := D_vel hγ' hu htI
      exact h.trans (derivWithin_eventuallyEq (isSmoothCurve_iff.1 hγ') ht).eq_of_nhds
    rw [hvel] at hr'
    rw [Morse.jacobiExpr, e2]
    show D hN (γ t) (J'' t) + Morse.curvR hN (incl hN (γ t)) _ (D hN (γ t) (J t)) _ = 0
    rw [← hr']
    exact (map_add (D hN (γ t)) (J'' t) r).symm.trans
      ((congrArg (D hN (γ t)) hr0).trans (map_zero _))

/-- **Dictionary, project ⇒ blind**: a field along `γ` whose ambient image is a project Jacobi
field along `incl ∘ γ` is a blind Jacobi field of the induced connection on `[0, 1]`. -/
theorem isJacobi_of_isJacobiField {γ : ℝ → Bridge.Sub hN} {J : FA n γ}
    (hγ : IsSmoothCurve (n := n) γ (Icc 0 1))
    (hX : Morse.IsJacobiField hN (incl hN ∘ γ) (ambA γ J)) :
    IsJacobi (conn (hN := hN)) γ (Icc 0 1) J := by
  have hγ' : RoundTrip.BridgePrelude.IsSmoothCurve (n := n) γ (Icc 0 1) := hγ
  have hc : Morse.IsSmoothCurveIn hN (incl hN ∘ γ) :=
    ⟨isSmoothCurve_iff.1 hγ', fun t _ => (γ t).2⟩
  have hu := uniqueDiffOn_Icc (zero_lt_one' ℝ)
  have hamb : ∀ U : FA n γ, ambA γ (covA γ (Icc 0 1) U) =
      Morse.covAlong hN (incl hN ∘ γ) (ambA γ U) := fun U => funext fun t => by
    refine (D_covA γ (Icc 0 1) U t).trans ?_
    show _ = Morse.prj hN (incl hN (γ t)) _
    rw [prj_incl]
  have hcov : ContDiffOn ℝ ∞ (ambA γ (covA γ (Icc 0 1) J)) (Icc 0 1) := by
    rw [hamb]
    exact hc.contDiffOn_prj.clm_apply (hX.contDiffOn.derivWithin hu (by simp))
  have hJs : RoundTrip.BridgePrelude.IsSmoothAlong γ (Icc 0 1) J :=
    isSmoothAlong_iff.2 ⟨hγ', hX.contDiffOn⟩
  have hJ's : RoundTrip.BridgePrelude.IsSmoothAlong γ (Icc 0 1) (covA γ (Icc 0 1) J) :=
    isSmoothAlong_iff.2 ⟨hγ', hcov⟩
  refine ⟨covA γ (Icc 0 1) J, covA γ (Icc 0 1) (covA γ (Icc 0 1) J),
    (hasCovDeriv_iff isIntv_Icc hγ').2 ⟨hJs, fun _ _ => rfl⟩,
    (hasCovDeriv_iff isIntv_Icc hγ').2 ⟨hJ's, fun _ _ => rfl⟩,
    fun t ht => ⟨-(covA γ (Icc 0 1) (covA γ (Icc 0 1) J) t), ?_, add_neg_cancel _⟩⟩
  refine (isCurvVal_iff (γ t) _ _ _ _).2 ?_
  have hvel : D hN (γ t) (vel (n := n) γ (Icc 0 1) t) = Morse.velAlong (incl hN ∘ γ) t :=
    D_vel hγ' hu ht
  have h1 : D hN (γ t) (covA γ (Icc 0 1) (covA γ (Icc 0 1) J) t) =
      Morse.covAlong hN (incl hN ∘ γ) (Morse.covAlong hN (incl hN ∘ γ) (ambA γ J)) t := by
    have := congrFun (hamb (covA γ (Icc 0 1) J)) t
    rw [hamb J] at this
    exact this
  rw [hvel]
  refine (map_neg (D hN (γ t)) (covA γ (Icc 0 1) (covA γ (Icc 0 1) J) t)).trans ?_
  refine (congrArg Neg.neg h1).trans ?_
  exact neg_eq_of_add_eq_zero_left ((add_comm _ _).trans (jacobi_Icc hc hX t ht))

/-- **Dictionary: conjugate parameters.** For `a, b ∈ [0, 1]`, blind conjugacy along `γ` for the
induced connection is the project's `Morse.IsConjugate` along `incl ∘ γ`. -/
theorem isConj_iff {γ : ℝ → Bridge.Sub hN} (hγ : IsSmoothCurve (n := n) γ (Icc 0 1)) {a b : ℝ}
    (ha : a ∈ Icc (0 : ℝ) 1) (hb : b ∈ Icc (0 : ℝ) 1) :
    IsConj (conn (hN := hN)) γ a b ↔ Morse.IsConjugate hN (incl hN ∘ γ) a b := by
  constructor
  · rintro ⟨hab, J, ⟨hJ, hJo⟩, hne, hJa, hJb⟩
    obtain ⟨t, ht⟩ := Function.ne_iff.1 hne
    have htI : t ∈ Icc (0 : ℝ) 1 := by
      by_contra h
      exact ht (hJo t h)
    refine ⟨ha, hb, hab, ambA γ J, isJacobiField_of_isJacobi hγ hJ, ?_, ?_, t, htI, ?_⟩
    · show D hN (γ a) (J a) = 0
      rw [hJa]
      exact map_zero _
    · show D hN (γ b) (J b) = 0
      rw [hJb]
      exact map_zero _
    · intro h
      exact ht (D_injective (γ t) (h.trans (map_zero _).symm))
  · rintro ⟨-, -, hab, X, hX, hXa, hXb, t, ht, hXt⟩
    classical
    let J : FA n γ := fun s => if s ∈ Icc (0 : ℝ) 1 then L hN (γ s) (X s) else 0
    have hJX : EqOn (ambA γ J) X (Icc 0 1) := fun s hs => by
      show D hN (γ s) (if s ∈ Icc (0 : ℝ) 1 then L hN (γ s) (X s) else 0) = X s
      rw [if_pos hs]
      exact D_L ((Morse.prj_eq_self_iff hN (γ s).2).1 (hX.tangent s hs))
    refine ⟨hab, J, ⟨isJacobi_of_isJacobiField hγ (hX.congr fun s hs => (hJX hs).symm),
      fun s hs => by
        show (if s ∈ Icc (0 : ℝ) 1 then L hN (γ s) (X s) else 0) = 0
        rw [if_neg hs]⟩, fun h => hXt ?_, ?_, ?_⟩
    · rw [← hJX ht]
      show D hN (γ t) (J t) = 0
      rw [show J t = 0 from congrFun h t]
      exact map_zero _
    · show (if a ∈ Icc (0 : ℝ) 1 then L hN (γ a) (X a) else 0) = 0
      rw [if_pos ha, hXa, map_zero]
    · show (if b ∈ Icc (0 : ℝ) 1 then L hN (γ b) (X b) else 0) = 0
      rw [if_pos hb, hXb, map_zero]

/-- A smooth curve in `N` on `[0, 1]` which is a geodesic on `(0, 1)` lifts to a blind geodesic of
the induced connection on the closed interval `[0, 1]` (endpoint condition by continuity). -/
theorem isGeodesic_lift {γ : ℝ → V} (hc : Morse.IsSmoothCurveIn hN γ)
    (hg : Morse.IsGeodesicOn hN γ (Ioo 0 1)) (q : Bridge.Sub hN) :
    IsGeodesic (conn (hN := hN)) (lift γ q) (Icc 0 1) ∧
      EqOn (incl hN ∘ lift γ q) γ (Icc 0 1) := by
  have hu := uniqueDiffOn_Icc (zero_lt_one' ℝ)
  have heq : EqOn (incl hN ∘ lift γ q) γ (Icc 0 1) := fun t ht => incl_lift q (hc.mem t ht)
  refine ⟨?_, heq⟩
  have h : RoundTrip.BridgePrelude.IsGeodesic (conn (hN := hN)) (lift γ q) (Icc 0 1) := by
    refine isGeodesic_iff.2 ⟨isIntv_Icc, hc.contDiffOn.congr heq, fun t ht => ?_⟩
    have hd1 : EqOn (derivWithin (incl hN ∘ lift γ q) (Icc 0 1)) (derivWithin γ (Icc 0 1))
        (Icc 0 1) := fun s hs => derivWithin_congr heq (heq hs)
    rw [derivWithin_congr hd1 (hd1 ht)]
    have hP : P hN (lift γ q t) = Morse.prj hN (γ t) := by
      rw [← prj_incl]
      exact congrArg (Morse.prj hN) (heq ht)
    rw [hP]
    -- the normal condition, extended from `(0, 1)` to `[0, 1]` by continuity
    have hf : ContinuousOn (fun s => Morse.prj hN (γ s)
        (derivWithin (derivWithin γ (Icc 0 1)) (Icc 0 1) s)) (Icc 0 1) :=
      hc.contDiffOn_prj.continuousOn.clm_apply
        ((hc.contDiffOn_velAlong.derivWithin hu (m := 0) (by simp)).continuousOn)
    refine EqOn.of_subset_closure (g := fun _ => (0 : V)) (fun s hs => ?_) hf continuousOn_const
      Ioo_subset_Icc_self (by rw [closure_Ioo zero_ne_one]) ht
    show Morse.prj hN (γ s) (derivWithin (derivWithin γ (Icc 0 1)) (Icc 0 1) s) = 0
    have hv : ContDiffOn ℝ ∞ (derivWithin γ (Icc 0 1)) (Icc 0 1) := hc.contDiffOn_velAlong
    rw [(derivWithin_eventuallyEq hv hs).eq_of_nhds,
      (derivWithin_eventuallyEq hc.contDiffOn hs).deriv_eq,
      Morse.prj_of_mem hN (hc.mem s (Ioo_subset_Icc_self hs))]
    exact (Morse.tanProj_eq_zero_iff hN).2 (hg.normal s hs)
  exact h

theorem isConjugate_congr {γ γ' : ℝ → V} (heq : EqOn γ γ' (Icc 0 1)) {a b : ℝ}
    (h : Morse.IsConjugate hN γ a b) : Morse.IsConjugate hN γ' a b := by
  obtain ⟨ha, hb, hab, J, hJ, hJa, hJb, t, ht, hJt⟩ := h
  exact ⟨ha, hb, hab, J, hJ.congr_curve heq, hJa, hJb, t, ht, hJt⟩

end Emb

/-- B on embedded manifolds: `M = ↥N` (model `ℝⁿ`, induced metric) with the induced Levi-Civita
connection `Bridge.conn` (a special case of B, see `B_to_B_emb`). -/
def B_emb : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    (W : Type) [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W] (n : ℕ)
    (N : Set V) (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) (Rn n) W N)
    [ConnectedSpace (Bridge.Sub hN)] (γ : ℝ → Bridge.Sub hN),
    IsGeodesic (Bridge.conn (hN := hN)) γ (Set.Icc 0 1) →
    ∀ a ∈ Set.Icc (0 : ℝ) 1, ∀ b ∈ Set.Icc (0 : ℝ) 1, a ≠ b →
      ¬ IsConj (Bridge.conn (hN := hN)) γ a b →
    ∀ J₁ J₂ : FA n γ, IsJacobi (Bridge.conn (hN := hN)) γ (Set.Icc 0 1) J₁ →
      IsJacobi (Bridge.conn (hN := hN)) γ (Set.Icc 0 1) J₂ →
      J₁ a = J₂ a → J₁ b = J₂ b → Set.EqOn J₁ J₂ (Set.Icc 0 1)

theorem B_to_B_emb : B → B_emb := fun hB _ _ _ _ _ _ _ _ n _ hN _ =>
  hB n (Bridge.Sub hN) (Bridge.conn (hN := hN)) Bridge.conn_isLC

/-- A, restricted to what B covers on embedded manifolds: model `ℝⁿ`, `↥N` connected, and `γ` a
geodesic (on `(0, 1)`, smooth on `[0, 1]`). -/
def A_geo : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    (W : Type) [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W] (n : ℕ)
    (N : Set V) (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) (Rn n) W N)
    [ConnectedSpace (Bridge.Sub hN)] (γ : ℝ → V) (hc : Morse.IsSmoothCurveIn hN γ),
    Morse.IsGeodesicOn hN γ (Ioo 0 1) →
    ∀ {a b : ℝ} (ha : a ∈ Icc (0 : ℝ) 1) (hb : b ∈ Icc (0 : ℝ) 1), a ≠ b →
      ¬ Morse.IsConjugate hN γ a b → Bijective (Morse.jacEvalEnds hc ha hb)

theorem A_to_A_geo : A → A_geo := fun hA _ _ _ _ _ _ _ _ _ _ _ _ _ hc _ _ _ ha hb hab hnc =>
  hA hc ha hb hab hnc

/-- **A implies B on embedded manifolds** (injectivity of A's `jacEvalEnds`, through the Jacobi
dictionary). -/
theorem A_to_B_emb : A → B_emb := by
  intro hA V _ _ _ W _ _ _ n N hN _ γ hγ a ha b hb hab hnc J₁ J₂ hJ₁ hJ₂ hJa hJb
  have hγs : IsSmoothCurve (n := n) γ (Icc 0 1) := hγ.2.1
  have hγs' : RoundTrip.BridgePrelude.IsSmoothCurve (n := n) γ (Icc 0 1) := hγs
  have hc : Morse.IsSmoothCurveIn hN (Bridge.incl hN ∘ γ) :=
    ⟨Bridge.isSmoothCurve_iff.1 hγs', fun t _ => (γ t).2⟩
  have hnc' : ¬ Morse.IsConjugate hN (Bridge.incl hN ∘ γ) a b := fun h =>
    hnc ((Emb.isConj_iff hγs ha hb).2 h)
  have hinj := (hA hc ha hb hab hnc').1
  have hX₁ := (Emb.isJacobiField_of_isJacobi hγs hJ₁).comp_projIcc_mem hc
  have hX₂ := (Emb.isJacobiField_of_isJacobi hγs hJ₂).comp_projIcc_mem hc
  have heq := @hinj ⟨_, hX₁⟩ ⟨_, hX₂⟩ (by
    refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
    · show Bridge.ambA γ J₁ (projIcc (0 : ℝ) 1 zero_le_one a) =
        Bridge.ambA γ J₂ (projIcc (0 : ℝ) 1 zero_le_one a)
      rw [projIcc_of_mem _ ha]
      show Bridge.D hN (γ a) (J₁ a) = Bridge.D hN (γ a) (J₂ a)
      rw [hJa]
    · show Bridge.ambA γ J₁ (projIcc (0 : ℝ) 1 zero_le_one b) =
        Bridge.ambA γ J₂ (projIcc (0 : ℝ) 1 zero_le_one b)
      rw [projIcc_of_mem _ hb]
      show Bridge.D hN (γ b) (J₁ b) = Bridge.D hN (γ b) (J₂ b)
      rw [hJb])
  intro t ht
  have h := congrFun (congrArg Subtype.val heq) t
  simp only [projIcc_of_mem _ ht] at h
  exact Bridge.D_injective (γ t) h

/-- **B on embedded manifolds implies A for geodesics** (injectivity from B through the
dictionary; surjectivity by the project's dimension count `finrank 𝒥(γ) = 2n`, which B does not
state). -/
theorem B_emb_to_A_geo : B_emb → A_geo := by
  intro hB V _ _ _ W _ _ _ n N hN _ γ hc hg a b ha hb hab hnc
  let q : Bridge.Sub hN := (⟨γ 0, hc.mem 0 ⟨le_rfl, zero_le_one⟩⟩ : N)
  obtain ⟨hgeo, heqc⟩ := Emb.isGeodesic_lift hc hg q
  set c' := Bridge.lift γ q
  have hc's : IsSmoothCurve (n := n) c' (Icc 0 1) := hgeo.2.1
  have hnc' : ¬ IsConj (Bridge.conn (hN := hN)) c' a b := fun h =>
    hnc (Emb.isConjugate_congr heqc ((Emb.isConj_iff hc's ha hb).1 h))
  -- a Jacobi field along `γ`, as a blind field along `c'`
  have key : ∀ Y : Morse.jacobiSpace hN γ hc, ∃ J : FA n c',
      IsJacobi (Bridge.conn (hN := hN)) c' (Icc 0 1) J ∧ EqOn (Bridge.ambA c' J) Y (Icc 0 1) := by
    intro Y
    let J : FA n c' := fun s => Bridge.L hN (c' s) ((Y : ℝ → V) s)
    have hJY : EqOn (Bridge.ambA c' J) Y (Icc 0 1) := fun s hs => by
      show Bridge.D hN (c' s) (Bridge.L hN (c' s) ((Y : ℝ → V) s)) = (Y : ℝ → V) s
      refine Bridge.D_L ((Morse.prj_eq_self_iff hN (c' s).2).1 ?_)
      have := Y.2.1.tangent s hs
      rwa [← heqc hs] at this
    refine ⟨J, Emb.isJacobi_of_isJacobiField hc's ?_, hJY⟩
    exact (Y.2.1.congr_curve fun s hs => (heqc hs).symm).congr fun s hs => (hJY hs).symm
  have hinj : Injective (Morse.jacEvalEnds hc ha hb) := by
    intro Y₁ Y₂ h
    obtain ⟨J₁, hJ₁, hJY₁⟩ := key Y₁
    obtain ⟨J₂, hJ₂, hJY₂⟩ := key Y₂
    have hYa : (Y₁ : ℝ → V) a = (Y₂ : ℝ → V) a := congrArg (fun z => (z.1 : V)) h
    have hYb : (Y₁ : ℝ → V) b = (Y₂ : ℝ → V) b := congrArg (fun z => (z.2 : V)) h
    have hEq := hB V W n N hN c' hgeo a ha b hb hab hnc' J₁ J₂ hJ₁ hJ₂
      (Bridge.D_injective (c' a) ((hJY₁ ha).trans (hYa.trans (hJY₂ ha).symm)))
      (Bridge.D_injective (c' b) ((hJY₁ hb).trans (hYb.trans (hJY₂ hb).symm)))
    refine Subtype.ext (funext fun t => ?_)
    rw [Y₁.2.2 t, Y₂.2.2 t]
    have hs := (projIcc (0 : ℝ) 1 zero_le_one t).2
    rw [← hJY₁ hs, ← hJY₂ hs]
    show Bridge.D hN _ (J₁ _) = Bridge.D hN _ (J₂ _)
    rw [hEq hs]
  refine ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank ?_).1 hinj⟩
  rw [Morse.finrank_jacobiSpace hc, Module.finrank_prod, Morse.finrank_tanAt hN (hc.mem a ha),
    Morse.finrank_tanAt hN (hc.mem b hb)]
  ring

#rt_check RoundTrip.V9_10.A_to_B_emb [Morse.jacEvalEnds_bijective_of_not_isConjugate]
#rt_check RoundTrip.V9_10.B_emb_to_A_geo [Morse.jacEvalEnds_bijective_of_not_isConjugate]
#rt_overlap RoundTrip.V9_10.B_emb_to_A_geo [Morse.jacEvalEnds_bijective_of_not_isConjugate]

end RoundTrip.V9_10
