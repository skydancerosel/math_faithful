import Morse
import RoundTrip.Check
import RoundTrip.Blind.V11_14
import RoundTrip.Bridge

open Set Filter Topology Function Module MeasureTheory
open scoped ContDiff Manifold ENNReal unitInterval RealInnerProductSpace

namespace RoundTrip.V11_14

/-- The project's statement (no universe parameters): on the unit sphere `Sⁿ ⊆ ℝⁿ⁺¹`
(`Milnor.Sphere.sphSub n`, induced metric), `K(U, U) = (n − 1)‖U‖²` (`ricci_sph`); the hypothesis
of Myers' theorem holds with `r = 1` (`ricciLowerBound_sph`); and for `n ≥ 2` every geodesic of
`Ω(Sⁿ; p, q)` of length `> π` has a point `γ(t)`, `0 < t < 1`, conjugate to `γ(0)` and is not
minimal, and any two points are at distance `≤ π` (`sphere_myers`). -/
def A : Prop :=
  type_of% @Morse.ricci_sph ∧ type_of% @Morse.ricciLowerBound_sph ∧ type_of% @Morse.sphere_myers

theorem A_holds : A := ⟨@Morse.ricci_sph, @Morse.ricciLowerBound_sph, @Morse.sphere_myers⟩

/-! ## Dictionary (copied from `Items/V10_23.lean`, `Items/V11_24.lean`) -/

namespace Emb

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

open RoundTrip.Bridge

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W] {n : ℕ} {N : Set V}
  {hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) (Bridge.Rn n) W N}

theorem isIntv_Icc : RoundTrip.BridgePrelude.IsIntv (Icc (0 : ℝ) 1) :=
  ⟨ordConnected_Icc, uniqueDiffOn_Icc zero_lt_one⟩

theorem isSmoothCurveIn {γ : ℝ → Bridge.Sub hN} (hγ : IsSmoothCurve (n := n) γ (Icc 0 1)) :
    Morse.IsSmoothCurveIn hN (incl hN ∘ γ) :=
  ⟨isSmoothCurve_iff.1 hγ, fun t _ => (γ t).2⟩

theorem prj_incl (x : Bridge.Sub hN) : Morse.prj hN (incl hN x) = P hN x :=
  Morse.prj_of_mem hN x.2

theorem tangent_ambA {γ : ℝ → Bridge.Sub hN} (J : FA n γ) (t : ℝ) :
    Morse.prj hN ((incl hN ∘ γ) t) (ambA γ J t) = ambA γ J t := by
  show Morse.prj hN (incl hN (γ t)) (D hN (γ t) (J t)) = D hN (γ t) (J t)
  rw [prj_incl]
  exact P_D _ _

theorem covD_eventuallyEq {γ : ℝ → Bridge.Sub hN} {X : ℝ → V} {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    Morse.covD hN (incl hN ∘ γ) X =ᶠ[𝓝 t]
      fun τ => P hN (γ τ) (derivWithin X (Icc 0 1) τ) := by
  filter_upwards [isOpen_Ioo.mem_nhds ht] with τ hτ
  show Morse.prj hN (incl hN (γ τ)) (deriv X τ) = _
  rw [prj_incl, derivWithin_of_mem_nhds (Icc_mem_nhds hτ.1 hτ.2)]

/-- Blind Jacobi field ⇒ project Jacobi field (one direction of `Emb.isJacobi_iff` of
`Items/V10_23.lean`). -/
theorem isJacobiField_of_isJacobi {γ : ℝ → Bridge.Sub hN}
    (hγ : IsSmoothCurve (n := n) γ (Icc 0 1)) (J : FA n γ)
    (hJ : IsJacobi (conn (hN := hN)) γ (Icc 0 1) J) :
    Morse.IsJacobiField hN (incl hN ∘ γ) (ambA γ J) := by
  have hc := isSmoothCurveIn hγ
  have hγ' : RoundTrip.BridgePrelude.IsSmoothCurve (n := n) γ (Icc 0 1) := hγ
  have u : UniqueDiffOn ℝ (Icc (0 : ℝ) 1) := uniqueDiffOn_Icc zero_lt_one
  have hvel : ∀ t ∈ Icc (0 : ℝ) 1, D hN (γ t) (vel (n := n) γ (Icc 0 1) t) =
      Morse.velAlong (incl hN ∘ γ) t := fun t ht => D_vel hγ' u ht
  obtain ⟨J', J'', h1, h2, h3⟩ := hJ
  have h1' := (hasCovDeriv_iff' isIntv_Icc hγ').1 h1
  have h2' := (hasCovDeriv_iff' isIntv_Icc hγ').1 h2
  refine ⟨(isSmoothAlong_iff.1 h1'.1).2, fun t _ => tangent_ambA J t, fun t ht => ?_⟩
  have ht' := Ioo_subset_Icc_self ht
  have e1 : Morse.covD hN (incl hN ∘ γ) (ambA γ J) =ᶠ[𝓝 t] ambA γ J' := by
    filter_upwards [covD_eventuallyEq (γ := γ) (X := ambA γ J) ht,
      isOpen_Ioo.mem_nhds ht] with τ hτ hτ'
    rw [hτ, h1'.2 τ (Ioo_subset_Icc_self hτ')]
  have e2 : Morse.covD hN (incl hN ∘ γ) (Morse.covD hN (incl hN ∘ γ) (ambA γ J)) t =
      ambA γ J'' t := by
    show Morse.prj hN (incl hN (γ t)) (deriv _ t) = _
    rw [prj_incl, e1.deriv_eq, ← derivWithin_of_mem_nhds (Icc_mem_nhds ht.1 ht.2),
      h2'.2 t ht']
  obtain ⟨r, hr, hr0⟩ := h3 t ht'
  have hr' := (isCurvVal_iff (γ t) _ _ _ r).1 hr
  have hd : deriv (incl hN ∘ γ) t = D hN (γ t) (vel (n := n) γ (Icc 0 1) t) := by
    rw [hvel t ht', hc.velAlong_eq ht]
  rw [Morse.jacobiExpr, e2, hd]
  show D hN (γ t) (J'' t) + Morse.curvR hN (incl hN (γ t)) _ (D hN (γ t) (J t)) _ = 0
  rw [← hr', ← D_tadd, hr0, D_tzero]

/-- Blind conjugate points ⇒ project conjugate points (one direction of `Emb.isConj_iff` of
`Items/V10_23.lean`). -/
theorem isConjugate_of_isConj {γ : ℝ → Bridge.Sub hN} (hγ : IsSmoothCurve (n := n) γ (Icc 0 1))
    {a b : ℝ} (ha : a ∈ Icc (0 : ℝ) 1) (hb : b ∈ Icc (0 : ℝ) 1)
    (h : IsConj (conn (hN := hN)) γ a b) : Morse.IsConjugate hN (incl hN ∘ γ) a b := by
  obtain ⟨hab, J, ⟨hJ, hJo⟩, hJ0, hJa, hJb⟩ := h
  obtain ⟨t, ht⟩ : ∃ t, J t ≠ 0 := by
    by_contra h
    push Not at h
    exact hJ0 (funext h)
  have htI : t ∈ Icc (0 : ℝ) 1 := by
    by_contra h
    exact ht (hJo t h)
  refine ⟨ha, hb, hab, ambA γ J, isJacobiField_of_isJacobi hγ J hJ, ?_, ?_, t, htI, ?_⟩
  · show D hN (γ a) (J a) = 0
    rw [hJa, D_tzero]
  · show D hN (γ b) (J b) = 0
    rw [hJb, D_tzero]
  · intro h
    exact ht (D_injective (γ t) (h.trans (D_tzero (γ t)).symm))

/-! #### Both directions (copied from `Items/V10_23.lean`) -/

theorem contDiffOn_P {γ : ℝ → Bridge.Sub hN} (hγ : IsSmoothCurve (n := n) γ (Icc 0 1)) :
    ContDiffOn ℝ ∞ (fun t => P hN (γ t)) (Icc 0 1) := by
  have := (isSmoothCurveIn hγ).contDiffOn_prj
  refine this.congr fun t _ => ?_
  exact (prj_incl (γ t)).symm

/-- **Dictionary: Jacobi fields.** For a smooth curve `γ` in `N` on `[0, 1]`, a blind Jacobi field
of the induced connection (`IsJacobi`, Milnor's equation with curvature `IsCurvVal`, on the closed
interval with derivatives within `[0,1]`) is exactly a project Jacobi field (`Morse.IsJacobiField`)
read in `V`. -/
theorem isJacobi_iff {γ : ℝ → Bridge.Sub hN} (hγ : IsSmoothCurve (n := n) γ (Icc 0 1))
    (J : FA n γ) :
    IsJacobi (conn (hN := hN)) γ (Icc 0 1) J ↔ Morse.IsJacobiField hN (incl hN ∘ γ) (ambA γ J) := by
  have hc := isSmoothCurveIn hγ
  have hγ' : RoundTrip.BridgePrelude.IsSmoothCurve (n := n) γ (Icc 0 1) := hγ
  have u : UniqueDiffOn ℝ (Icc (0 : ℝ) 1) := uniqueDiffOn_Icc zero_lt_one
  have hvel : ∀ t ∈ Icc (0 : ℝ) 1, D hN (γ t) (vel (n := n) γ (Icc 0 1) t) =
      Morse.velAlong (incl hN ∘ γ) t := fun t ht => D_vel hγ' u ht
  constructor
  · rintro ⟨J', J'', h1, h2, h3⟩
    have h1' := (hasCovDeriv_iff' isIntv_Icc hγ').1 h1
    have h2' := (hasCovDeriv_iff' isIntv_Icc hγ').1 h2
    refine ⟨(isSmoothAlong_iff.1 h1'.1).2, fun t _ => tangent_ambA J t, fun t ht => ?_⟩
    have ht' := Ioo_subset_Icc_self ht
    have e1 : Morse.covD hN (incl hN ∘ γ) (ambA γ J) =ᶠ[𝓝 t] ambA γ J' := by
      filter_upwards [covD_eventuallyEq (γ := γ) (X := ambA γ J) ht,
        isOpen_Ioo.mem_nhds ht] with τ hτ hτ'
      rw [hτ, h1'.2 τ (Ioo_subset_Icc_self hτ')]
    have e2 : Morse.covD hN (incl hN ∘ γ) (Morse.covD hN (incl hN ∘ γ) (ambA γ J)) t =
        ambA γ J'' t := by
      show Morse.prj hN (incl hN (γ t)) (deriv _ t) = _
      rw [prj_incl, e1.deriv_eq, ← derivWithin_of_mem_nhds (Icc_mem_nhds ht.1 ht.2),
        h2'.2 t ht']
    obtain ⟨r, hr, hr0⟩ := h3 t ht'
    have hr' := (isCurvVal_iff (γ t) _ _ _ r).1 hr
    have hd : deriv (incl hN ∘ γ) t = D hN (γ t) (vel (n := n) γ (Icc 0 1) t) := by
      rw [hvel t ht', hc.velAlong_eq ht]
    rw [Morse.jacobiExpr, e2, hd]
    show D hN (γ t) (J'' t) + Morse.curvR hN (incl hN (γ t)) _ (D hN (γ t) (J t)) _ = 0
    rw [← hr', ← D_tadd, hr0, D_tzero]
  · intro hX
    have hXs : IsSmoothAlong γ (Icc 0 1) J := isSmoothAlong_iff.2 ⟨hγ', hX.contDiffOn⟩
    have hdX : ContDiffOn ℝ ∞ (derivWithin (ambA γ J) (Icc 0 1)) (Icc 0 1) :=
      hX.contDiffOn.derivWithin u (by simp)
    have hamb1 : ambA γ (covA γ (Icc 0 1) J) =
        fun t => P hN (γ t) (derivWithin (ambA γ J) (Icc 0 1) t) := funext fun t => D_covA _ _ _ _
    have hJ's : IsSmoothAlong γ (Icc 0 1) (covA γ (Icc 0 1) J) := by
      refine isSmoothAlong_iff.2 ⟨hγ', ?_⟩
      rw [hamb1]
      exact (contDiffOn_P hγ).clm_apply hdX
    set J' := covA γ (Icc 0 1) J
    set J'' := covA γ (Icc 0 1) J'
    have hamb2 : ambA γ J'' = fun t => P hN (γ t) (derivWithin (ambA γ J') (Icc 0 1) t) :=
      funext fun t => D_covA _ _ _ _
    refine ⟨J', J'', (hasCovDeriv_iff isIntv_Icc hγ').2 ⟨hXs, fun _ _ => rfl⟩,
      (hasCovDeriv_iff isIntv_Icc hγ').2 ⟨hJ's, fun _ _ => rfl⟩, fun t ht => ?_⟩
    -- the curvature term
    set F : ℝ → V := fun τ => Morse.curvR hN (incl hN (γ τ)) (Morse.velAlong (incl hN ∘ γ) τ)
      (ambA γ J τ) (Morse.velAlong (incl hN ∘ γ) τ)
    have hFmem : F t ∈ Morse.tangentSubspace hN (γ t) := by
      show Morse.curvR hN (γ t).1 _ _ _ ∈ _
      rw [Morse.curvR_of_mem hN (γ t).2]
      rw [← hvel t ht]
      exact Morse.curvOp_mem hN (D_mem _ _) (D_mem _ _) (D_mem _ _)
    refine ⟨L hN (γ t) (F t), (isCurvVal_iff (γ t) _ _ _ _).2 ?_, ?_⟩
    · rw [D_L hFmem, hvel t ht]
      rfl
    · apply D_injective (γ t)
      refine (D_tadd (γ t) (J'' t) (L hN (γ t) (F t))).trans ?_
      rw [D_L hFmem, D_tzero]
      -- `G = D/dt(DJ/dt) + R(V, J)V` read in `V` is continuous on `[0,1]` and zero on `(0,1)`
      set G : ℝ → V := fun τ => ambA γ J'' τ + F τ
      have hGc : ContinuousOn G (Icc 0 1) := by
        have hJ'c : ContDiffOn ℝ ∞ (ambA γ J') (Icc 0 1) := (isSmoothAlong_iff.1 hJ's).2
        have h1 : ContinuousOn (ambA γ J'') (Icc 0 1) := by
          rw [hamb2]
          exact ((contDiffOn_P hγ).clm_apply (hJ'c.derivWithin u (m := ∞) (by simp))).continuousOn
        have h2 : ContinuousOn F (Icc 0 1) := by
          have := (hc.contDiffOn_curvAlong.clm_apply hX.contDiffOn).continuousOn
          refine this.congr fun τ hτ => ?_
          show F τ = Morse.curvAlong hN (incl hN ∘ γ) τ (ambA γ J τ)
          rw [Morse.curvAlong_apply (γ τ).2, tangent_ambA]
          rfl
        exact h1.add h2
      have hG0 : EqOn G 0 (Ioo 0 1) := by
        intro τ hτ
        have hτ' := Ioo_subset_Icc_self hτ
        have e1 : Morse.covD hN (incl hN ∘ γ) (ambA γ J) =ᶠ[𝓝 τ] ambA γ J' := by
          filter_upwards [covD_eventuallyEq (γ := γ) (X := ambA γ J) hτ,
            isOpen_Ioo.mem_nhds hτ] with x hx hx'
          rw [hx, hamb1]
        have e2 : Morse.covD hN (incl hN ∘ γ) (Morse.covD hN (incl hN ∘ γ) (ambA γ J)) τ =
            ambA γ J'' τ := by
          show Morse.prj hN (incl hN (γ τ)) (deriv _ τ) = _
          rw [prj_incl, e1.deriv_eq, ← derivWithin_of_mem_nhds (Icc_mem_nhds hτ.1 hτ.2), hamb2]
        have := hX.eq τ hτ
        rw [Morse.jacobiExpr, e2, ← hc.velAlong_eq hτ] at this
        exact this
      have := hG0.of_subset_closure hGc continuousOn_const Ioo_subset_Icc_self
        (by rw [closure_Ioo zero_ne_one]) ht
      exact this

open Classical in
/-- A blind field along `γ` from an ambient field `X`: `t ↦ L_{γ t}(X t)` on `[0,1]`, `0` outside. -/
noncomputable def toFA (γ : ℝ → Bridge.Sub hN) (X : ℝ → V) : FA n γ :=
  fun t => if t ∈ Icc (0 : ℝ) 1 then L hN (γ t) (X t) else 0

theorem toFA_of_mem {γ : ℝ → Bridge.Sub hN} (X : ℝ → V) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    toFA γ X t = L hN (γ t) (X t) := by
  unfold toFA
  exact if_pos ht

theorem toFA_of_not_mem {γ : ℝ → Bridge.Sub hN} (X : ℝ → V) {t : ℝ} (ht : t ∉ Icc (0 : ℝ) 1) :
    toFA γ X t = 0 := by
  unfold toFA
  exact if_neg ht

theorem ambA_toFA {γ : ℝ → Bridge.Sub hN} {X : ℝ → V}
    (hX : ∀ t ∈ Icc (0 : ℝ) 1, Morse.prj hN ((incl hN ∘ γ) t) (X t) = X t) :
    EqOn (ambA γ (toFA γ X)) X (Icc 0 1) := fun t ht => by
  show D hN (γ t) (toFA γ X t) = X t
  rw [toFA_of_mem X ht]
  exact D_L ((Morse.prj_eq_self_iff hN (γ t).2).1 (hX t ht))

/-- `toFA` as a linear map. -/
noncomputable def toFAₗ (γ : ℝ → Bridge.Sub hN) : (ℝ → V) →ₗ[ℝ] FA n γ where
  toFun := toFA γ
  map_add' X Y := by
    funext t
    by_cases ht : t ∈ Icc (0 : ℝ) 1
    · show toFA γ (X + Y) t = toFA γ X t + toFA γ Y t
      rw [toFA_of_mem _ ht, toFA_of_mem _ ht, toFA_of_mem _ ht]
      exact map_add (L hN (γ t)) (X t) (Y t)
    · show toFA γ (X + Y) t = toFA γ X t + toFA γ Y t
      rw [toFA_of_not_mem _ ht, toFA_of_not_mem _ ht, toFA_of_not_mem _ ht, add_zero]
  map_smul' c X := by
    funext t
    by_cases ht : t ∈ Icc (0 : ℝ) 1
    · show toFA γ (c • X) t = c • toFA γ X t
      rw [toFA_of_mem _ ht, toFA_of_mem _ ht]
      exact map_smul (L hN (γ t)) c (X t)
    · show toFA γ (c • X) t = c • toFA γ X t
      rw [toFA_of_not_mem _ ht, toFA_of_not_mem _ ht, smul_zero]

theorem toFA_mem_JacOn {γ : ℝ → Bridge.Sub hN} (hγ : IsSmoothCurve (n := n) γ (Icc 0 1)) {X : ℝ → V}
    (hX : Morse.IsJacobiField hN (incl hN ∘ γ) X) :
    toFA γ X ∈ JacOn (conn (hN := hN)) γ (Icc 0 1) :=
  ⟨(isJacobi_iff hγ _).2 (hX.congr fun t ht => (ambA_toFA hX.tangent ht).symm),
    fun t ht => toFA_of_not_mem X ht⟩

/-- On fields tangent along `γ` on `[0,1]` and constant off `[0,1]`, `toFA` is injective. -/
theorem toFA_injOn {γ : ℝ → Bridge.Sub hN} {X Y : ℝ → V}
    (hX : ∀ t ∈ Icc (0 : ℝ) 1, Morse.prj hN ((incl hN ∘ γ) t) (X t) = X t)
    (hY : ∀ t ∈ Icc (0 : ℝ) 1, Morse.prj hN ((incl hN ∘ γ) t) (Y t) = Y t)
    (h : toFA γ X = toFA γ Y) : EqOn X Y (Icc 0 1) := fun t ht => by
  rw [← ambA_toFA hX ht, ← ambA_toFA hY ht, h]

/-- **Dictionary: conjugate points.** For a smooth curve `γ` in `N` on `[0,1]` and `a, b ∈ [0,1]`,
B's `IsConj` (for the induced connection) is the project's `IsConjugate`. -/
theorem isConj_iff {γ : ℝ → Bridge.Sub hN} (hγ : IsSmoothCurve (n := n) γ (Icc 0 1)) {a b : ℝ}
    (ha : a ∈ Icc (0 : ℝ) 1) (hb : b ∈ Icc (0 : ℝ) 1) :
    IsConj (conn (hN := hN)) γ a b ↔ Morse.IsConjugate hN (incl hN ∘ γ) a b := by
  constructor
  · rintro ⟨hab, J, ⟨hJ, hJo⟩, hJ0, hJa, hJb⟩
    obtain ⟨t, ht⟩ : ∃ t, J t ≠ 0 := by
      by_contra h
      push Not at h
      exact hJ0 (funext h)
    have htI : t ∈ Icc (0 : ℝ) 1 := by
      by_contra h
      exact ht (hJo t h)
    refine ⟨ha, hb, hab, ambA γ J, (isJacobi_iff hγ J).1 hJ, ?_, ?_, t, htI, ?_⟩
    · show D hN (γ a) (J a) = 0
      rw [hJa, D_tzero]
    · show D hN (γ b) (J b) = 0
      rw [hJb, D_tzero]
    · intro h
      exact ht (D_injective (γ t) (h.trans (D_tzero (γ t)).symm))
  · rintro ⟨-, -, hab, X, hX, hXa, hXb, t, ht, hXt⟩
    refine ⟨hab, toFA γ X, toFA_mem_JacOn hγ hX, ?_, ?_, ?_⟩
    · intro h
      apply hXt
      rw [← ambA_toFA hX.tangent ht]
      show D hN (γ t) (toFA γ X t) = 0
      rw [h]
      exact D_tzero (γ t)
    · rw [toFA_of_mem X ha, hXa, map_zero] <;> rfl
    · rw [toFA_of_mem X hb, hXb, map_zero] <;> rfl

/-- A blind geodesic on `[0, 1]` of `↥N` from `p` to `q` is, in `V`, a project geodesic of
`Ω(N; p, q)` (from `Items/V10_23.lean`). -/
theorem mem_pathSpace_of_isGeodesic {γ : ℝ → Bridge.Sub hN} {p q : Bridge.Sub hN}
    (h : IsGeodesic (conn (hN := hN)) γ (Icc 0 1)) (h0 : γ 0 = p) (h1 : γ 1 = q) :
    incl hN ∘ γ ∈ Morse.pathSpace N (incl hN p) (incl hN q) ∧
      Morse.IsUnbrokenGeodesic hN (incl hN ∘ γ) := by
  have h' : RoundTrip.BridgePrelude.IsGeodesic (conn (hN := hN)) γ (Icc 0 1) := h
  obtain ⟨-, hc, -⟩ := isGeodesic_iff.1 h'
  exact ⟨⟨Morse.IsPiecewiseSmooth.of_contDiffOn hc zero_le_one subset_rfl, fun t _ => (γ t).2,
    congrArg (incl hN) h0, congrArg (incl hN) h1⟩, hc, isGeodesicOn_Ioo h'⟩

/-- On the interior, `derivWithin [0,1]` of a function smooth on `[0, 1]` is `deriv`, near `t`. -/
theorem derivWithin_eventuallyEq {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : ℝ → E} (hF : ContDiffOn ℝ ∞ F (Icc 0 1)) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    derivWithin F (Icc 0 1) =ᶠ[𝓝 t] deriv F := by
  filter_upwards [Ioo_mem_nhds ht.1 ht.2] with x hx
  exact ((hF.contDiffAt (Icc_mem_nhds hx.1 hx.2)).differentiableAt (by simp)).hasDerivAt
    |>.hasDerivWithinAt.derivWithin (uniqueDiffOn_Icc zero_lt_one x (Ioo_subset_Icc_self hx))

/-- A smooth curve in `N` on `[0, 1]` which is a geodesic on `(0, 1)` lifts to a blind geodesic of
the induced connection on `[0, 1]` (from `Items/V9_10.lean`). -/
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

/-! ### The Ricci tensor (from `Items/V11_24.lean`) -/

/-- The coordinate isomorphism `ℝⁿ ≃ T_xN`, `z ↦ D_x z`. -/
noncomputable def eT (x : Bridge.Sub hN) : Bridge.Rn n ≃ₗ[ℝ] Morse.tangentSubspace hN x :=
  LinearEquiv.ofBijective
    ((D hN x : Bridge.Rn n →ₗ[ℝ] V).codRestrict (Morse.tangentSubspace hN x) (D_mem x))
    ⟨fun _ _ h => D_injective x (congrArg Subtype.val h),
      fun v => ⟨L hN x v, Subtype.ext (D_L v.2)⟩⟩

/-- **Dictionary: curvature values.** -/
theorem curvR_eq (x : Bridge.Sub hN) (a b c : TangentSpace 𝓘(ℝ, Bridge.Rn n) x) :
    curvR (Bridge.conn (hN := hN)) x a b c =
      L hN x (Morse.curvOp hN x (D hN x a) (D hN x b) (D hN x c)) := by
  have hr : ∀ r, IsCurvVal (Bridge.conn (hN := hN)) x a b c r ↔
      D hN x r = Morse.curvOp hN x (D hN x a) (D hN x b) (D hN x c) := fun r => by
    have h := Bridge.isCurvVal_iff x a b c r
    have e : Morse.curvR hN (incl hN x) (D hN x a) (D hN x b) (D hN x c) =
        Morse.curvOp hN x (D hN x a) (D hN x b) (D hN x c) := Morse.curvR_of_mem hN x.2 _ _ _
    rw [e] at h
    exact h
  have hmem : Morse.curvOp hN x (D hN x a) (D hN x b) (D hN x c) ∈ Morse.tangentSubspace hN x :=
    Morse.curvOp_mem hN (D_mem x a) (D_mem x b) (D_mem x c)
  have hex : ∃ r, IsCurvVal (Bridge.conn (hN := hN)) x a b c r :=
    ⟨L hN x _, (hr _).2 (D_L hmem)⟩
  unfold curvR
  rw [dif_pos hex]
  apply D_injective x
  rw [(hr _).1 hex.choose_spec, D_L hmem]

/-- **Dictionary: the Ricci tensor** (diagonal). -/
theorem ricci_eq (x : Bridge.Sub hN) (U : TangentSpace 𝓘(ℝ, Bridge.Rn n) x) :
    ricci (Bridge.conn (hN := hN)) x U U =
      Morse.ricci hN x ⟨D hN x U, D_mem x U⟩ ⟨D hN x U, D_mem x U⟩ := by
  set U' : Morse.tangentSubspace hN x := ⟨D hN x U, D_mem x U⟩
  set T := (Morse.curvTensor hN x U').flip U'
  have hT : ∀ W : Bridge.Rn n, ((eT x).symm.conj T) W = curvR (Bridge.conn (hN := hN)) x U W U := by
    intro W
    have hmem : Morse.curvOp hN x (D hN x U) (D hN x W) (D hN x U) ∈
        Morse.tangentSubspace hN x :=
      Morse.curvOp_mem hN (D_mem x U) (D_mem x W) (D_mem x U)
    have h1 : ((eT x).symm.conj T) W = (eT x).symm (T (eT x W)) := rfl
    have h2 : (eT x).symm (T (eT x W)) =
        L hN x (Morse.curvOp hN x (D hN x U) (D hN x W) (D hN x U)) := by
      apply (eT x).injective
      rw [LinearEquiv.apply_symm_apply]
      apply Subtype.ext
      show Morse.curvOp hN x (D hN x U) (D hN x W) (D hN x U) = D hN x (L hN x _)
      exact (D_L hmem).symm
    exact h1.trans (h2.trans (curvR_eq x U W U).symm)
  have hex : ∃ L' : Bridge.Rn n →ₗ[ℝ] Bridge.Rn n, ∀ W : Bridge.Rn n,
      L' W = curvR (Bridge.conn (hN := hN)) x U W U := ⟨_, hT⟩
  have hch : hex.choose = (eT x).symm.conj T :=
    LinearMap.ext fun W => (hex.choose_spec W).trans (hT W).symm
  unfold ricci
  rw [dif_pos hex, hch, LinearMap.trace_conj']
  rfl

end Emb

/-! ## The counter-model: `S¹ ⊆ ℝ²` (as in `Items/V10_23.lean`) -/

namespace S1

open RoundTrip.Bridge Milnor.Sphere

/-- `S¹ = Milnor.Sphere.Sph 1 ⊆ ℝ²` as a blind manifold (model `ℝ¹`, induced metric). -/
abbrev S : Type := Bridge.Sub (sphSub 1)

theorem connectedSpace : ConnectedSpace S := by
  have hrank : 1 < Module.rank ℝ (EuclideanSpace ℝ (Fin (1 + 1))) := by
    rw [← Module.finrank_eq_rank, finrank_euclideanSpace, Fintype.card_fin]
    exact_mod_cast (by omega : 1 < 1 + 1)
  have h : IsConnected (Sph 1) := by
    rw [show Sph 1 = Metric.sphere (0 : EuclideanSpace ℝ (Fin (1 + 1))) 1 from preimage_eq_sphere]
    exact isConnected_sphere hrank 0 zero_le_one
  exact Subtype.connectedSpace h

theorem finrank_tangent (q : Sph 1) : finrank ℝ (Morse.tangentSubspace (sphSub 1) q) = 1 := by
  have := Morse.finrank_tanAt (sphSub 1) q.2
  rwa [Morse.tanAt_of_mem (sphSub 1) q.2, finrank_euclideanSpace_fin] at this

/-- **`S¹` has curvature `≤ 0`** (indeed `0`): its tangent spaces are lines, and `R(A, A) = 0`. -/
theorem nonposCurvature : Morse.NonposCurvature (sphSub 1) := by
  intro q A hA B hB
  by_cases h0 : (⟨A, hA⟩ : Morse.tangentSubspace (sphSub 1) q) = 0
  · have : A = 0 := congrArg Subtype.val h0
    subst this
    rw [show (0 : EuclideanSpace ℝ (Fin (1 + 1))) = (0 : ℝ) • (0 : EuclideanSpace ℝ (Fin (1 + 1)))
      from (zero_smul ℝ _).symm, Morse.curvOp_smul_left]
    simp
  · obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' _ h0).1 (finrank_tangent q) ⟨B, hB⟩
    have hB' : B = c • A := (congrArg Subtype.val hc).symm
    have hAA : Morse.curvOp (sphSub 1) q A A = 0 := by simp [Morse.curvOp]
    rw [hB', Morse.curvOp_smul_right, hAA]
    simp

/-- **No conjugate points on `S¹`**: along a blind geodesic of `S¹` (induced connection), no two
parameters of `[0, 1]` are conjugate (Lemma 19.1's argument, `Morse.IsJacobiField.eqOn_zero_of_nonpos`). -/
theorem not_isConj {γ : ℝ → S} (hγ : IsGeodesic (Bridge.conn (hN := sphSub 1)) γ (Icc 0 1))
    {a b : ℝ} (ha : a ∈ Icc (0 : ℝ) 1) (hb : b ∈ Icc (0 : ℝ) 1) :
    ¬ IsConj (Bridge.conn (hN := sphSub 1)) γ a b := by
  intro h
  have hγ' : RoundTrip.BridgePrelude.IsGeodesic (Bridge.conn (hN := sphSub 1)) γ (Icc 0 1) := hγ
  have hsm : IsSmoothCurve (n := 1) γ (Icc 0 1) := hγ.2.1
  have hc := Emb.isSmoothCurveIn hsm
  have hg := isGeodesicOn_Ioo hγ'
  obtain ⟨-, -, hab, J, hJ, hJa, hJb, t, ht, hJt⟩ := Emb.isConjugate_of_isConj hsm ha hb h
  rcases lt_or_gt_of_ne hab with hlt | hlt
  · exact hJt (hJ.eqOn_zero_of_nonpos nonposCurvature hc hg ha hb hlt hJa hJb ht)
  · exact hJt (hJ.eqOn_zero_of_nonpos nonposCurvature hc hg hb ha hlt hJb hJa ht)

theorem single_mem (i : Fin 2) : (EuclideanSpace.single i (1 : ℝ)) ∈ Sph 1 :=
  mem_iff_norm.2 (by simp)

/-- The base point `e₀` and the unit tangent `e₁`. -/
noncomputable abbrev e (i : Fin 2) : EuclideanSpace ℝ (Fin (1 + 1)) := EuclideanSpace.single i 1

theorem norm_e (i : Fin 2) : ‖e i‖ = 1 := by simp [e]

theorem inner_e01 : ⟪e 0, e 1⟫ = 0 := by simp [e, EuclideanSpace.inner_single_left]

noncomputable abbrev p₀ : S := (⟨e 0, single_mem 0⟩ : Sph 1)

/-- The great circle `t ↦ cos(Lt) e₀ + sin(Lt) e₁` of speed `L`, as a blind curve in `S¹`. -/
noncomputable def G (L : ℝ) : ℝ → S := Bridge.lift (Morse.greatCircle (e 0) (e 1) L) p₀

theorem incl_G (L : ℝ) : Bridge.incl (sphSub 1) ∘ G L = Morse.greatCircle (e 0) (e 1) L := by
  funext t
  exact Bridge.incl_lift p₀ (Morse.greatCircle_mem_sph (single_mem 0) (norm_e 1) inner_e01 _ t)

theorem isGeodesic_G (L : ℝ) : IsGeodesic (Bridge.conn (hN := sphSub 1)) (G L) (Icc 0 1) := by
  have hc : Morse.IsSmoothCurveIn (sphSub 1) (Morse.greatCircle (e 0) (e 1) L) :=
    Morse.isSmoothCurveIn_greatCircle (single_mem 0) (norm_e 1) inner_e01 L
  have hg : Morse.IsGeodesicOn (sphSub 1) (Morse.greatCircle (e 0) (e 1) L) (Ioo 0 1) :=
    (Morse.isGeodesicOn_greatCircle (single_mem 0) (norm_e 1) inner_e01 L).mono isOpen_Ioo
      (subset_univ _)
  exact (Emb.isGeodesic_lift hc hg p₀).1

theorem norm_deriv_G {L : ℝ} (hL : 0 ≤ L) (t : ℝ) :
    ‖deriv (Morse.greatCircle (e 0) (e 1) L) t‖ = L := by
  have huv' : ⟪e 1, -e 0⟫ = 0 := by rw [inner_neg_right, real_inner_comm, inner_e01, neg_zero]
  rw [Morse.deriv_greatCircle, norm_smul,
    Morse.norm_greatCircle (norm_e 1) (by rw [norm_neg, norm_e]) huv' L t, mul_one,
    Real.norm_eq_abs, abs_of_nonneg hL]

theorem arcLen_G {L : ℝ} (hL : 0 ≤ L) : arcLen (n := 1) (G L) 0 1 = L := by
  refine (Bridge.arcLen_eq (G L) 0 1).trans ?_
  rw [incl_G]
  simp only [Morse.pathLength, norm_deriv_G hL, intervalIntegral.integral_const, sub_zero,
    one_smul]

end S1

/-! ## B is false (`n = 1`)

B allows `n = 1` (the circle). Its clause (d) ("best possible": a geodesic of length exactly `πR`
whose end points are conjugate) fails on `S¹`, which has no conjugate points (curvature `0`).
Counter-model: `S¹ ⊆ ℝ²` with the induced metric and connection, `R = 1`, `ψ` the inclusion. -/

section NotB

open S1 Milnor.Sphere

/-- The inclusion `S¹ → ℝ²` is a blind round sphere of radius `1`. -/
theorem isRoundSphereR_incl : IsRoundSphereR (n := 1) 1 (Bridge.incl (sphSub 1)) := by
  refine ⟨Bridge.contMDiff_incl (hN := sphSub 1), Subtype.val_injective, ?_, fun x v w => ?_⟩
  · show range (Subtype.val : Sph 1 → _) = _
    rw [Subtype.range_coe]
    exact preimage_eq_sphere
  · exact Bridge.inner_eq x v w

theorem not_B : ¬ B := by
  intro hB
  have := S1.connectedSpace
  obtain ⟨-, -, -, ⟨γ, hγ, -, hconj⟩, -⟩ :=
    hB 1 S (Bridge.conn (hN := sphSub 1)) Bridge.conn_isLC 1 one_pos (Bridge.incl (sphSub 1))
      isRoundSphereR_incl
  exact S1.not_isConj hγ ⟨le_rfl, zero_le_one⟩ ⟨zero_le_one, le_rfl⟩ hconj

/-- `A ⇒ B` is false (A holds, B does not). -/
theorem not_A_to_B : ¬ (A → B) := fun h => not_B (h A_holds)

/-- `B ⇒ A`, ex falso (B is false). -/
theorem B_to_A : B → A := fun hB => absurd hB not_B

end NotB

#rt_check RoundTrip.V11_14.B_to_A [Morse.ricci_sph, Morse.ricciLowerBound_sph, Morse.sphere_myers]
#rt_overlap RoundTrip.V11_14.B_to_A [Morse.ricci_sph, Morse.ricciLowerBound_sph, Morse.sphere_myers]

/-! ## The corrected reading (`n ≥ 2`) on the embedded unit sphere

`Bcorr` is B with Milnor's implicit `2 ≤ n`.  Its embedded special case with `R = 1`
(`M = Sⁿ ⊆ ℝⁿ⁺¹` through the Bridge, `ψ` the inclusion, induced connection) is `BcorrEmb1`.
Proved below: A gives clauses (b) (`K(U, U) = n − 1`, from `ricci_sph` through the Ricci
dictionary) and (c) (Myers on `Sⁿ`, from `sphere_myers` through the geodesic/conjugate-point
dictionary) — `A_to_BcorrEmb1_bc`; clauses (a) (sectional curvature `1`, from the project's
`Morse.curvOp_sph`) and (d) (a half great circle has conjugate end points, from
`Morse.conjMultiplicity_greatCircle`) hold by project lemmas OUTSIDE A — `BcorrEmb1_ad`.  Clause
(e) (no conjugate pair at all along a great circle of length `< π`) is not proved: the project
computes conjugate multiplicities along great circles only from `t = 0`
(`conjMultiplicity_greatCircle`); arbitrary pairs `a < b` need an affine-reparametrization
transport of conjugacy (`Morse.IsJacobiField.comp_affine` exists; glue only).  Not covered at all:
radius `R ≠ 1` and abstract `M` isometric to the sphere via `ψ`. -/

open Bundle in
/-- B with Milnor's implicit `n ≥ 2`. -/
def Bcorr : Prop :=
  ∀ (n : ℕ) (M : Type) [TopologicalSpace M] [T2Space M] [ChartedSpace (Rn n) M] [IsManifold 𝓘(ℝ, Rn n) ∞ M] [Bundle.RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, Rn n) x)] [IsContMDiffRiemannianBundle 𝓘(ℝ, Rn n) ∞ (Rn n) (fun x : M => TangentSpace 𝓘(ℝ, Rn n) x)] [ConnectedSpace M], ∀ (cov : Conn n M), IsLC cov → 2 ≤ n → ∀ (R : ℝ), 0 < R → ∀ ψ : M → EuclideanSpace ℝ (Fin (n + 1)), IsRoundSphereR R ψ →
    (∀ (p : M) (A B : TangentSpace 𝓘(ℝ, Rn n) p), LinearIndependent ℝ ![A, B] →
      inner ℝ (curvR cov p A B A) B = (1 / R ^ 2) * (‖A‖ ^ 2 * ‖B‖ ^ 2 - inner ℝ A B ^ 2)) ∧
    (∀ (p : M) (U : TangentSpace 𝓘(ℝ, Rn n) p), ‖U‖ = 1 → ricci cov p U U = ((n : ℝ) - 1) / R ^ 2) ∧
    (∀ γ : ℝ → M, IsGeodesic cov γ (Set.Icc 0 1) → Real.pi * R < arcLen (n := n) γ 0 1 →
      ∃ a ∈ Set.Icc (0 : ℝ) 1, ∃ b ∈ Set.Icc (0 : ℝ) 1, IsConj cov γ a b) ∧
    (∃ γ : ℝ → M, IsGeodesic cov γ (Set.Icc 0 1) ∧ arcLen (n := n) γ 0 1 = Real.pi * R ∧ IsConj cov γ 0 1) ∧
    (∀ ℓ : ℝ, 0 < ℓ → ℓ < Real.pi * R → ∃ γ : ℝ → M, IsGeodesic cov γ (Set.Icc 0 1) ∧ arcLen (n := n) γ 0 1 = ℓ ∧
      ∀ a ∈ Set.Icc (0 : ℝ) 1, ∀ b ∈ Set.Icc (0 : ℝ) 1, ¬ IsConj cov γ a b)

theorem B_to_Bcorr : B → Bcorr := fun hB n M _ _ _ _ _ _ _ cov hcov _ => hB n M cov hcov

namespace SphN

open RoundTrip.Bridge Milnor.Sphere

abbrev S (n : ℕ) : Type := Bridge.Sub (sphSub n)

theorem connectedSpace (n : ℕ) (hn : 1 ≤ n) : ConnectedSpace (S n) := by
  have hrank : 1 < Module.rank ℝ (EuclideanSpace ℝ (Fin (n + 1))) := by
    rw [← Module.finrank_eq_rank, finrank_euclideanSpace, Fintype.card_fin]
    exact_mod_cast (by omega : 1 < n + 1)
  have h : IsConnected (Sph n) := by
    rw [show Sph n = Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 from preimage_eq_sphere]
    exact isConnected_sphere hrank 0 zero_le_one
  exact Subtype.connectedSpace h

theorem isRoundSphereR_incl (n : ℕ) : IsRoundSphereR (n := n) 1 (Bridge.incl (sphSub n)) := by
  refine ⟨Bridge.contMDiff_incl (hN := sphSub n), Subtype.val_injective, ?_, fun x v w => ?_⟩
  · show range (Subtype.val : Sph n → _) = _
    rw [Subtype.range_coe]
    exact preimage_eq_sphere
  · exact Bridge.inner_eq x v w

variable {n : ℕ}

/-- The standard vectors `e₀`, `e₁` of `ℝⁿ⁺¹` (`n ≥ 1`). -/
noncomputable abbrev e0 (n : ℕ) : EuclideanSpace ℝ (Fin (n + 1)) := EuclideanSpace.single 0 1
noncomputable abbrev e1 (n : ℕ) (hn : 1 ≤ n) : EuclideanSpace ℝ (Fin (n + 1)) :=
  EuclideanSpace.single ⟨1, by omega⟩ 1

theorem e0_mem : e0 n ∈ Sph n := mem_iff_norm.2 (by simp [e0])
theorem norm_e1 (hn : 1 ≤ n) : ‖e1 n hn‖ = 1 := by simp [e1]
theorem inner_e01 (hn : 1 ≤ n) : ⟪e0 n, e1 n hn⟫ = 0 := by
  simp [e0, e1, EuclideanSpace.inner_single_left, Fin.ext_iff]

noncomputable abbrev p₀ (n : ℕ) : S n := (⟨e0 n, e0_mem⟩ : Sph n)

/-- The great circle `t ↦ cos(Lt) e₀ + sin(Lt) e₁` as a blind curve in `Sⁿ`. -/
noncomputable def G (hn : 1 ≤ n) (L : ℝ) : ℝ → S n :=
  Bridge.lift (Morse.greatCircle (e0 n) (e1 n hn) L) (p₀ n)

theorem incl_G (hn : 1 ≤ n) (L : ℝ) :
    Bridge.incl (sphSub n) ∘ G hn L = Morse.greatCircle (e0 n) (e1 n hn) L := by
  funext t
  exact Bridge.incl_lift (p₀ n)
    (Morse.greatCircle_mem_sph e0_mem (norm_e1 hn) (inner_e01 hn) _ t)

theorem smoothIn_G (hn : 1 ≤ n) (L : ℝ) :
    Morse.IsSmoothCurveIn (sphSub n) (Morse.greatCircle (e0 n) (e1 n hn) L) :=
  Morse.isSmoothCurveIn_greatCircle e0_mem (norm_e1 hn) (inner_e01 hn) L

theorem isGeodesic_G (hn : 1 ≤ n) (L : ℝ) :
    IsGeodesic (Bridge.conn (hN := sphSub n)) (G hn L) (Icc 0 1) := by
  have hg : Morse.IsGeodesicOn (sphSub n) (Morse.greatCircle (e0 n) (e1 n hn) L) (Ioo 0 1) :=
    (Morse.isGeodesicOn_greatCircle e0_mem (norm_e1 hn) (inner_e01 hn) L).mono isOpen_Ioo
      (subset_univ _)
  exact (Emb.isGeodesic_lift (smoothIn_G hn L) hg (p₀ n)).1

theorem arcLen_G (hn : 1 ≤ n) {L : ℝ} (hL : 0 ≤ L) : arcLen (n := n) (G hn L) 0 1 = L := by
  refine (Bridge.arcLen_eq (G hn L) 0 1).trans ?_
  rw [incl_G]
  have huv' : ⟪e1 n hn, -e0 n⟫ = 0 := by
    rw [inner_neg_right, real_inner_comm, inner_e01, neg_zero]
  have h : ∀ t, ‖deriv (Morse.greatCircle (e0 n) (e1 n hn) L) t‖ = L := fun t => by
    rw [Morse.deriv_greatCircle, norm_smul, Morse.norm_greatCircle (norm_e1 hn)
      (by rw [norm_neg]; simp [e0]) huv' L t, mul_one, Real.norm_eq_abs, abs_of_nonneg hL]
  simp only [Morse.pathLength, h, intervalIntegral.integral_const, sub_zero, one_smul]

end SphN

open SphN Milnor.Sphere Bundle in
/-- Clauses (a)–(d) of `Bcorr` on the embedded unit sphere `Sⁿ`, `n ≥ 2` (`R = 1`). -/
def BcorrEmb1_abcd : Prop :=
  ∀ n : ℕ, 2 ≤ n →
    (∀ (p : S n) (A B : TangentSpace 𝓘(ℝ, Rn n) p), LinearIndependent ℝ ![A, B] →
      inner ℝ (curvR (Bridge.conn (hN := sphSub n)) p A B A) B =
        (1 / 1 ^ 2) * (‖A‖ ^ 2 * ‖B‖ ^ 2 - inner ℝ A B ^ 2)) ∧
    (∀ (p : S n) (U : TangentSpace 𝓘(ℝ, Rn n) p), ‖U‖ = 1 →
      ricci (Bridge.conn (hN := sphSub n)) p U U = ((n : ℝ) - 1) / 1 ^ 2) ∧
    (∀ γ : ℝ → S n, IsGeodesic (Bridge.conn (hN := sphSub n)) γ (Set.Icc 0 1) →
      Real.pi * 1 < arcLen (n := n) γ 0 1 →
      ∃ a ∈ Set.Icc (0 : ℝ) 1, ∃ b ∈ Set.Icc (0 : ℝ) 1, IsConj (Bridge.conn (hN := sphSub n)) γ a b) ∧
    (∃ γ : ℝ → S n, IsGeodesic (Bridge.conn (hN := sphSub n)) γ (Set.Icc 0 1) ∧
      arcLen (n := n) γ 0 1 = Real.pi * 1 ∧ IsConj (Bridge.conn (hN := sphSub n)) γ 0 1)

theorem Bcorr_to_BcorrEmb1_abcd : Bcorr → BcorrEmb1_abcd := fun hB n hn => by
  have := SphN.connectedSpace n (by omega)
  obtain ⟨ha, hb, hc, hd, -⟩ := hB n (SphN.S n) (Bridge.conn (hN := Milnor.Sphere.sphSub n))
    Bridge.conn_isLC hn 1 one_pos _ (SphN.isRoundSphereR_incl n)
  exact ⟨ha, hb, hc, hd⟩

open SphN Milnor.Sphere Bridge Emb Bundle in
/-- **A gives clauses (b) and (c)** on the embedded unit sphere (uses A's `ricci_sph` and
`sphere_myers`). -/
theorem A_to_BcorrEmb1_bc : A → ∀ n : ℕ, 2 ≤ n →
    (∀ (p : S n) (U : TangentSpace 𝓘(ℝ, Rn n) p), ‖U‖ = 1 →
      ricci (Bridge.conn (hN := sphSub n)) p U U = ((n : ℝ) - 1) / 1 ^ 2) ∧
    (∀ γ : ℝ → S n, IsGeodesic (Bridge.conn (hN := sphSub n)) γ (Set.Icc 0 1) →
      Real.pi * 1 < arcLen (n := n) γ 0 1 →
      ∃ a ∈ Set.Icc (0 : ℝ) 1, ∃ b ∈ Set.Icc (0 : ℝ) 1, IsConj (Bridge.conn (hN := sphSub n)) γ a b) := by
  intro hA n hn
  refine ⟨fun p U hU => ?_, fun γ hγ hL => ?_⟩
  · rw [ricci_eq]
    refine (hA.1 (show Sph n from p) _).trans ?_
    have hU' : ‖(⟨D (sphSub n) p U, D_mem p U⟩ : Morse.tangentSubspace (sphSub n) p)‖ = 1 := by
      show ‖D (sphSub n) p U‖ = 1
      rw [← Bridge.norm_eq]
      exact hU
    rw [hU']
    ring
  · obtain ⟨hmem, hunb⟩ := mem_pathSpace_of_isGeodesic hγ rfl rfl
    have hL' : Real.pi < Morse.pathLength (incl (sphSub n) ∘ γ) 0 1 := by
      have e : arcLen (n := n) γ 0 1 = Morse.pathLength (incl (sphSub n) ∘ γ) 0 1 :=
        arcLen_eq γ 0 1
      rw [e, mul_one] at hL
      exact hL
    obtain ⟨⟨t, ht, hconj⟩, -⟩ := hA.2.2 hn |>.1 hmem hunb hL'
    have hsm : IsSmoothCurve (n := n) γ (Icc 0 1) := hγ.2.1
    exact ⟨0, ⟨le_rfl, zero_le_one⟩, t, Ioo_subset_Icc_self ht,
      (isConj_iff hsm ⟨le_rfl, zero_le_one⟩ (Ioo_subset_Icc_self ht)).2 hconj⟩

#rt_check RoundTrip.V11_14.A_to_BcorrEmb1_bc [Morse.ricci_sph, Morse.ricciLowerBound_sph, Morse.sphere_myers]
#rt_overlap RoundTrip.V11_14.A_to_BcorrEmb1_bc [Morse.ricci_sph, Morse.ricciLowerBound_sph, Morse.sphere_myers]

open SphN Milnor.Sphere Bridge Emb Bundle in
/-- **Clauses (a) and (d) hold by project lemmas outside A** (`Morse.curvOp_sph`,
`Morse.conjMultiplicity_greatCircle`). -/
theorem BcorrEmb1_ad : ∀ n : ℕ, 2 ≤ n →
    (∀ (p : S n) (A B : TangentSpace 𝓘(ℝ, Rn n) p), LinearIndependent ℝ ![A, B] →
      inner ℝ (curvR (Bridge.conn (hN := sphSub n)) p A B A) B =
        (1 / 1 ^ 2) * (‖A‖ ^ 2 * ‖B‖ ^ 2 - inner ℝ A B ^ 2)) ∧
    (∃ γ : ℝ → S n, IsGeodesic (Bridge.conn (hN := sphSub n)) γ (Set.Icc 0 1) ∧
      arcLen (n := n) γ 0 1 = Real.pi * 1 ∧ IsConj (Bridge.conn (hN := sphSub n)) γ 0 1) := by
  intro n hn
  have hn1 : 1 ≤ n := by omega
  refine ⟨fun p A B _ => ?_, ⟨G hn1 Real.pi, isGeodesic_G hn1 _, by
    rw [arcLen_G hn1 Real.pi_pos.le, mul_one], ?_⟩⟩
  · have hmem : Morse.curvOp (sphSub n) p (D (sphSub n) p A) (D (sphSub n) p B)
        (D (sphSub n) p A) ∈ Morse.tangentSubspace (sphSub n) p :=
      Morse.curvOp_mem (sphSub n) (D_mem p A) (D_mem p B) (D_mem p A)
    show ⟪D (sphSub n) p (curvR (Bridge.conn (hN := sphSub n)) p A B A), D (sphSub n) p B⟫ = _
    rw [curvR_eq, D_L hmem, Morse.curvOp_sph (D_mem p A) (D_mem p B) (D_mem p A),
      Bridge.norm_eq p A, Bridge.norm_eq p B, Bridge.inner_eq p A B, inner_sub_left,
      real_inner_smul_left, real_inner_smul_left, real_inner_self_eq_norm_sq,
      real_inner_self_eq_norm_sq, real_inner_comm (D (sphSub n) p A) (D (sphSub n) p B)]
    ring
  · have hsm : IsSmoothCurve (n := n) (G hn1 Real.pi) (Icc 0 1) := (isGeodesic_G hn1 _).2.1
    refine (isConj_iff hsm ⟨le_rfl, zero_le_one⟩ ⟨zero_le_one, le_rfl⟩).2 ?_
    rw [incl_G]
    refine (Morse.isConjugate_iff (smoothIn_G hn1 _)).2 ⟨⟨le_rfl, zero_le_one⟩,
      ⟨zero_le_one, le_rfl⟩, zero_ne_one, ?_⟩
    rw [Morse.conjMultiplicity_greatCircle hn1 e0_mem (norm_e1 hn1) (inner_e01 hn1) Real.pi_pos
      (smoothIn_G hn1 _) ⟨zero_lt_one, le_rfl⟩, if_pos ⟨1, by simp⟩]
    omega

end RoundTrip.V11_14
