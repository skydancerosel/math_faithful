import Morse
import RoundTrip.Check
import RoundTrip.Bridge
import RoundTrip.Blind.V9_3

open Set Filter Topology Function Module
open scoped ContDiff Manifold

namespace RoundTrip.V9_3

/-- The project's statement (universes instantiated at 0), for a slice submanifold `N ⊆ V` with
model `Z` and any smooth curve `γ` in `N` on `[0, 1]` (`IsSmoothCurveIn`, not necessarily a
geodesic): for every `s ∈ [0, 1]`, `J ↦ (J(s), DJ/dt(s))` is a bijection from the space
`jacobiSpace` of Jacobi fields (normalized constant off `[0, 1]`) onto `T_{γ(s)}N × T_{γ(s)}N`;
and `finrank (jacobiSpace) = 2 · dim Z`. -/
def A : Prop :=
  type_of% @Morse.jacEval_bijective.{0,0,0} ∧ type_of% @Morse.finrank_jacobiSpace.{0,0,0}

theorem A_holds : A := ⟨@Morse.jacEval_bijective, @Morse.finrank_jacobiSpace⟩

/-! Neither `A → B` nor `B → A` is proved; see `V9_3.json`. B quantifies over abstract Riemannian
manifolds and geodesics, A over slice submanifolds `N ⊆ V` and arbitrary smooth curves. Below:
the embedded special case, `A ⇒ B_emb` and `B_emb ⇒ A0` (A at `s = 0` for blind geodesics). -/

/-! ## The embedded special case: dictionary for Jacobi fields -/

namespace Emb

set_option linter.unusedSectionVars false

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

theorem contDiffOn_P {γ : ℝ → Bridge.Sub hN} (hγ : IsSmoothCurve (n := n) γ (Icc 0 1)) :
    ContDiffOn ℝ ∞ (fun t => P hN (γ t)) (Icc 0 1) := by
  have := (isSmoothCurveIn hγ).contDiffOn_prj
  refine this.congr fun t _ => ?_
  exact (prj_incl (γ t)).symm

/-- For a field `X` smooth on `[0,1]`, `covD` (two-sided derivative) agrees near interior points
with `P (derivWithin X [0,1])`. -/
theorem covD_eventuallyEq {γ : ℝ → Bridge.Sub hN} {X : ℝ → V} {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    Morse.covD hN (incl hN ∘ γ) X =ᶠ[𝓝 t]
      fun τ => P hN (γ τ) (derivWithin X (Icc 0 1) τ) := by
  filter_upwards [isOpen_Ioo.mem_nhds ht] with τ hτ
  show Morse.prj hN (incl hN (γ τ)) (deriv X τ) = _
  rw [prj_incl, derivWithin_of_mem_nhds (Icc_mem_nhds hτ.1 hτ.2)]

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

theorem eq_of_eqOn_jacobiSpace {c : ℝ → V} {hc : Morse.IsSmoothCurveIn hN c} {X Y : ℝ → V}
    (hX : X ∈ Morse.jacobiSpace hN c hc) (hY : Y ∈ Morse.jacobiSpace hN c hc)
    (h : EqOn X Y (Icc 0 1)) : X = Y := by
  funext t
  rw [hX.2 t, hY.2 t]
  exact h (projIcc (0 : ℝ) 1 zero_le_one t).2

end Emb

/-! ## `B` on embedded manifolds and `A ⇒ B_emb` -/

/-- B on embedded manifolds: `M = ↥N` with the induced metric and the induced Levi-Civita
connection `Bridge.conn` (a special case of B, see `B_to_B_emb`). -/
def B_emb : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    (W : Type) [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W] (n : ℕ)
    (N : Set V) (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) (Rn n) W N)
    [ConnectedSpace (Bridge.Sub hN)] (γ : ℝ → Bridge.Sub hN),
    IsGeodesic (Bridge.conn (hN := hN)) γ (Set.Icc 0 1) →
    ((2 * n : ℕ) ≤ setDim (JacOn (Bridge.conn (hN := hN)) γ (Set.Icc 0 1))) ∧
    (∀ J₁ J₂ J₁' J₂' : FA n γ, IsJacobi (Bridge.conn (hN := hN)) γ (Set.Icc 0 1) J₁ →
      IsJacobi (Bridge.conn (hN := hN)) γ (Set.Icc 0 1) J₂ →
      HasCovDeriv (Bridge.conn (hN := hN)) γ (Set.Icc 0 1) J₁ J₁' →
      HasCovDeriv (Bridge.conn (hN := hN)) γ (Set.Icc 0 1) J₂ J₂' →
      HEq (J₁ 0) (J₂ 0) → HEq (J₁' 0) (J₂' 0) → Set.EqOn J₁ J₂ (Set.Icc 0 1))

/-- `B_emb` is a special case of B (the induced connection is Levi-Civita, `Bridge.conn_isLC`). -/
theorem B_to_B_emb : B → B_emb := fun hB _ _ _ _ _ _ _ _ n _ hN _ γ hγ =>
  hB n (Bridge.Sub hN) (Bridge.conn (hN := hN)) Bridge.conn_isLC γ hγ

namespace Emb

open RoundTrip.Bridge

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W] {n : ℕ} {N : Set V}
  {hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) (Bridge.Rn n) W N}

/-- From A: the blind Jacobi fields span a space of dimension `≥ 2n`. -/
theorem two_mul_le_setDim (hA : A) {γ : ℝ → Bridge.Sub hN}
    (hγ : IsSmoothCurve (n := n) γ (Icc 0 1)) :
    ((2 * n : ℕ) : ℕ∞) ≤ setDim (JacOn (conn (hN := hN)) γ (Icc 0 1)) := by
  have hc := isSmoothCurveIn hγ
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  set S := Morse.jacobiSpace hN (incl hN ∘ γ) hc
  have hfin : FiniteDimensional ℝ S :=
    LinearEquiv.finiteDimensional (LinearEquiv.ofBijective _ (hA.1 hc h0)).symm
  set Φ : S →ₗ[ℝ] FA n γ := (toFAₗ γ).comp S.subtype
  have hinj : Injective Φ := fun X Y h =>
    Subtype.ext (eq_of_eqOn_jacobiSpace X.2 Y.2 (toFA_injOn X.2.1.tangent Y.2.1.tangent h))
  have hle : LinearMap.range Φ ≤ Submodule.span ℝ (JacOn (conn (hN := hN)) γ (Icc 0 1)) := by
    rintro _ ⟨X, rfl⟩
    exact Submodule.subset_span (toFA_mem_JacOn hγ X.2.1)
  have hrank : Module.rank ℝ S = ((2 * n : ℕ) : Cardinal) := by
    rw [← Module.finrank_eq_rank, hA.2 hc, finrank_euclideanSpace_fin]
  unfold setDim
  rw [Cardinal.natCast_le_toENat, ← hrank, ← rank_range_of_injective Φ hinj]
  exact Submodule.rank_mono hle

/-- From A: blind Jacobi fields with the same `J(0)`, `DJ/dt(0)` agree on `[0,1]`. -/
theorem eqOn_of_initial (hA : A) {γ : ℝ → Bridge.Sub hN}
    (hγ : IsSmoothCurve (n := n) γ (Icc 0 1)) (J₁ J₂ J₁' J₂' : FA n γ)
    (h1 : IsJacobi (conn (hN := hN)) γ (Icc 0 1) J₁) (h2 : IsJacobi (conn (hN := hN)) γ (Icc 0 1) J₂)
    (h1' : HasCovDeriv (conn (hN := hN)) γ (Icc 0 1) J₁ J₁')
    (h2' : HasCovDeriv (conn (hN := hN)) γ (Icc 0 1) J₂ J₂')
    (e0 : HEq (J₁ 0) (J₂ 0)) (e0' : HEq (J₁' 0) (J₂' 0)) : EqOn J₁ J₂ (Icc 0 1) := by
  have hc := isSmoothCurveIn hγ
  have hγ' : RoundTrip.BridgePrelude.IsSmoothCurve (n := n) γ (Icc 0 1) := hγ
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have X1 := (isJacobi_iff hγ J₁).1 h1
  have X2 := (isJacobi_iff hγ J₂).1 h2
  have m1 := X1.comp_projIcc_mem hc
  have m2 := X2.comp_projIcc_mem hc
  have hp : ∀ {X : ℝ → V}, EqOn (fun t => X (projIcc (0 : ℝ) 1 zero_le_one t)) X (Icc 0 1) :=
    fun ht => by simp only [projIcc_of_mem _ ht]
  have hcov : ∀ (J J' : FA n γ), HasCovDeriv (conn (hN := hN)) γ (Icc 0 1) J J' →
      Morse.covAlong hN (incl hN ∘ γ) (fun t => ambA γ J (projIcc (0 : ℝ) 1 zero_le_one t)) 0 =
        ambA γ J' 0 := by
    intro J J' hJ
    have hJ' : RoundTrip.BridgePrelude.HasCovDeriv (conn (hN := hN)) γ (Icc 0 1) J J' := hJ
    rw [((hasCovDeriv_iff' isIntv_Icc hγ').1 hJ').2 0 h0, Morse.covAlong,
      derivWithin_congr hp (hp h0)]
    exact congrFun (congrArg DFunLike.coe (prj_incl (γ 0))) _
  have key : Morse.jacEval hc h0 ⟨_, m1⟩ = Morse.jacEval hc h0 ⟨_, m2⟩ := by
    refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
    · show ambA γ J₁ (projIcc (0 : ℝ) 1 zero_le_one 0) = ambA γ J₂ (projIcc (0 : ℝ) 1 zero_le_one 0)
      rw [projIcc_of_mem _ h0]
      show D hN (γ 0) (J₁ 0) = D hN (γ 0) (J₂ 0)
      rw [eq_of_heq e0]
    · show Morse.covAlong hN (incl hN ∘ γ) (fun t => ambA γ J₁ (projIcc (0 : ℝ) 1 zero_le_one t)) 0 =
        Morse.covAlong hN (incl hN ∘ γ) (fun t => ambA γ J₂ (projIcc (0 : ℝ) 1 zero_le_one t)) 0
      rw [hcov J₁ J₁' h1', hcov J₂ J₂' h2']
      show D hN (γ 0) (J₁' 0) = D hN (γ 0) (J₂' 0)
      rw [eq_of_heq e0']
  have heq := congrArg Subtype.val ((hA.1 hc h0).1 key)
  intro t ht
  apply D_injective (γ t)
  have := congrFun heq t
  simp only [projIcc_of_mem _ ht] at this
  exact this

end Emb

/-- **A implies B on embedded manifolds** (uses A's `jacEval_bijective` and
`finrank_jacobiSpace` through the hypothesis, and the dictionary `Emb.isJacobi_iff`). -/
theorem A_to_B_emb : A → B_emb := fun hA _ _ _ _ _ _ _ _ _ _ _ _ γ hγ =>
  ⟨Emb.two_mul_le_setDim hA hγ.2.1, Emb.eqOn_of_initial hA hγ.2.1⟩

#rt_check RoundTrip.V9_3.A_to_B_emb [Morse.jacEval_bijective, Morse.finrank_jacobiSpace]

/-! ## `B_emb ⇒` the part of A that `B_emb` covers

`A0`: A's conclusions at `s = 0`, for curves `incl ∘ γ` with `γ` a blind geodesic of the induced
connection on `[0,1]` in a connected slice submanifold modelled on `ℝⁿ`. -/

/-- The part of A covered by `B_emb`: `jacEval` at `s = 0` is bijective and `dim = 2n`, for the
curve `incl ∘ γ`, `γ` a blind geodesic on `[0,1]` of `↥N` (connected, model `ℝⁿ`). -/
def A0 : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    (W : Type) [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W] (n : ℕ)
    (N : Set V) (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) (Rn n) W N)
    [ConnectedSpace (Bridge.Sub hN)] (γ : ℝ → Bridge.Sub hN)
    (hγ : IsGeodesic (Bridge.conn (hN := hN)) γ (Set.Icc 0 1)),
    Bijective (Morse.jacEval (Emb.isSmoothCurveIn hγ.2.1) (s := 0) ⟨le_rfl, zero_le_one⟩) ∧
      finrank ℝ (Morse.jacobiSpace hN (Bridge.incl hN ∘ γ) (Emb.isSmoothCurveIn hγ.2.1)) =
        2 * finrank ℝ (Rn n)

/-- `A0` is an instance of A. -/
theorem A_to_A0 : A → A0 := fun hA _ _ _ _ _ _ _ _ _ _ _ _ _ hγ =>
  ⟨hA.1 (Emb.isSmoothCurveIn hγ.2.1) _, hA.2 (Emb.isSmoothCurveIn hγ.2.1)⟩

namespace Emb

open RoundTrip.Bridge

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W] {n : ℕ} {N : Set V}
  {hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) (Bridge.Rn n) W N}

/-- Every blind Jacobi field (normalized to `0` off `[0,1]`) is `toFA` of an element of
`jacobiSpace`. -/
theorem JacOn_subset_range {γ : ℝ → Bridge.Sub hN} (hγ : IsSmoothCurve (n := n) γ (Icc 0 1))
    {J : FA n γ} (hJ : J ∈ JacOn (conn (hN := hN)) γ (Icc 0 1)) :
    ∃ X ∈ Morse.jacobiSpace hN (incl hN ∘ γ) (isSmoothCurveIn hγ), toFA γ X = J := by
  refine ⟨_, ((isJacobi_iff hγ J).1 hJ.1).comp_projIcc_mem (isSmoothCurveIn hγ), funext fun t => ?_⟩
  by_cases ht : t ∈ Icc (0 : ℝ) 1
  · rw [toFA_of_mem _ ht]
    simp only [projIcc_of_mem _ ht]
    exact L_D (γ t) (J t)
  · rw [toFA_of_not_mem _ ht, hJ.2 t ht]

end Emb

/-- **B on embedded manifolds implies the part `A0` of A** (uses `B_emb`'s two clauses: the
dimension bound gives `dim ≥ 2n`, uniqueness gives injectivity of `jacEval` at `0`, hence
`dim ≤ 2n`, and bijectivity by counting dimensions). -/
theorem B_emb_to_A0 : B_emb → A0 := by
  intro hB V _ _ _ W _ _ _ n N hN _ γ hγ
  obtain ⟨hdim, huniq⟩ := hB V W n N hN γ hγ
  have hγs : IsSmoothCurve (n := n) γ (Set.Icc 0 1) := hγ.2.1
  have hγ' : RoundTrip.BridgePrelude.IsSmoothCurve (n := n) γ (Set.Icc 0 1) := hγs
  set hc := Emb.isSmoothCurveIn hγs
  have h0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  set S := Morse.jacobiSpace hN (Bridge.incl hN ∘ γ) hc
  -- `DJ/dt (0)` of `toFA γ X`, read in `V`, is `covAlong X 0`
  have hcov : ∀ (X : S) (J' : FA n γ),
      HasCovDeriv (Bridge.conn (hN := hN)) γ (Set.Icc 0 1) (Emb.toFA γ (X : ℝ → V)) J' →
      Bridge.D hN (γ 0) (J' 0) = Morse.covAlong hN (Bridge.incl hN ∘ γ) X 0 := by
    intro X J' hJ
    have hJ' : RoundTrip.BridgePrelude.HasCovDeriv (Bridge.conn (hN := hN)) γ (Set.Icc 0 1)
        (Emb.toFA γ (X : ℝ → V)) J' := hJ
    have e := ((Bridge.hasCovDeriv_iff' Emb.isIntv_Icc hγ').1 hJ').2 0 h0
    refine e.trans ?_
    rw [Morse.covAlong, derivWithin_congr (Emb.ambA_toFA X.2.1.tangent)
      (Emb.ambA_toFA X.2.1.tangent h0)]
    exact (congrFun (congrArg DFunLike.coe (Emb.prj_incl (γ 0))) _).symm
  have hinj : Injective (Morse.jacEval hc h0) := by
    intro X Y hXY
    have h1 : (X : ℝ → V) 0 = (Y : ℝ → V) 0 := congrArg (fun z => (z.1 : V)) hXY
    have h2 : Morse.covAlong hN (Bridge.incl hN ∘ γ) X 0 =
        Morse.covAlong hN (Bridge.incl hN ∘ γ) Y 0 := congrArg (fun z => (z.2 : V)) hXY
    obtain ⟨J₁', -, hJ₁', -⟩ := (Emb.toFA_mem_JacOn hγs X.2.1).1
    obtain ⟨J₂', -, hJ₂', -⟩ := (Emb.toFA_mem_JacOn hγs Y.2.1).1
    have heq := huniq _ _ J₁' J₂' (Emb.toFA_mem_JacOn hγs X.2.1).1
      (Emb.toFA_mem_JacOn hγs Y.2.1).1 hJ₁' hJ₂'
      (heq_of_eq (by rw [Emb.toFA_of_mem _ h0, Emb.toFA_of_mem _ h0, h1]))
      (heq_of_eq (Bridge.D_injective (γ 0) (by rw [hcov X J₁' hJ₁', hcov Y J₂' hJ₂', h2])))
    refine Subtype.ext (Emb.eq_of_eqOn_jacobiSpace X.2 Y.2 fun t ht => ?_)
    rw [← Emb.ambA_toFA X.2.1.tangent ht, ← Emb.ambA_toFA Y.2.1.tangent ht]
    show Bridge.D hN (γ t) _ = Bridge.D hN (γ t) _
    rw [heq ht]
  have hfin : FiniteDimensional ℝ S := FiniteDimensional.of_injective (Morse.jacEval hc h0) hinj
  have htan : finrank ℝ (Morse.tanAt hN ((Bridge.incl hN ∘ γ) 0)) = n := by
    rw [Morse.finrank_tanAt hN (hc.mem 0 h0), finrank_euclideanSpace_fin]
  have hle : finrank ℝ S ≤ 2 * n := by
    have := LinearMap.finrank_le_finrank_of_injective hinj
    rwa [Module.finrank_prod, htan, ← two_mul] at this
  have hge : 2 * n ≤ finrank ℝ S := by
    set Φ : S →ₗ[ℝ] FA n γ := (Emb.toFAₗ γ).comp S.subtype
    have hsp : Submodule.span ℝ (JacOn (Bridge.conn (hN := hN)) γ (Set.Icc 0 1)) ≤
        LinearMap.range Φ := by
      refine Submodule.span_le.2 fun J hJ => ?_
      obtain ⟨X, hX, rfl⟩ := Emb.JacOn_subset_range hγs hJ
      exact ⟨⟨X, hX⟩, rfl⟩
    have h1 := (Submodule.rank_mono hsp).trans (rank_range_le Φ)
    have h2 := hdim
    unfold setDim at h2
    rw [Cardinal.natCast_le_toENat] at h2
    have h3 := h2.trans h1
    rw [← Module.finrank_eq_rank] at h3
    exact_mod_cast h3
  have hS : finrank ℝ S = 2 * n := le_antisymm hle hge
  refine ⟨⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank ?_).1 hinj⟩, ?_⟩
  · rw [hS, Module.finrank_prod, htan, two_mul]
  · rw [hS, finrank_euclideanSpace_fin]

/-- **B implies the part `A0` of A**, by specializing B to `↥N` with the induced connection. -/
theorem B_to_A0 : B → A0 := fun hB => B_emb_to_A0 (B_to_B_emb hB)

#rt_check RoundTrip.V9_3.B_emb_to_A0 [Morse.jacEval_bijective, Morse.finrank_jacobiSpace]
#rt_check RoundTrip.V9_3.B_to_A0 [Morse.jacEval_bijective, Morse.finrank_jacobiSpace]
#rt_overlap RoundTrip.V9_3.B_to_A0 [Morse.jacEval_bijective, Morse.finrank_jacobiSpace]

end RoundTrip.V9_3
