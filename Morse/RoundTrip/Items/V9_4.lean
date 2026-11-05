import Morse
import RoundTrip.Check
import RoundTrip.Bridge
import RoundTrip.Blind.V9_4

open Set Filter Topology Function Module
open scoped ContDiff Manifold

namespace RoundTrip.V9_4

/-- The project's statement (universes instantiated at 0), for a slice submanifold `N ⊆ V` and a
smooth curve `γ` in `N` on `[0,1]` (`IsSmoothCurveIn`): `IsConjugate hN γ a b` (`a, b ∈ [0,1]`,
`a ≠ b`, some Jacobi field vanishes at `a`, `b` and is nonzero somewhere on `[0,1]`) iff
`a, b ∈ [0,1]`, `a ≠ b` and `0 < conjMultiplicity hN γ hc a b` (the `finrank` of the space
`conjSpace` of normalized Jacobi fields vanishing at `a` and `b`). -/
def A : Prop := type_of% @Morse.isConjugate_iff.{0,0,0}

theorem A_holds : A := @Morse.isConjugate_iff

/-- **B is provable outright**, on every abstract manifold, by linear algebra alone: a set of
vectors spans a space of positive dimension iff it contains a nonzero vector. -/
theorem B_holds : B := by
  intro n M _ _ _ _ _ _ _ cov _ γ _ a _ b _ hab
  unfold IsConj conjMult setDim
  have key : ∀ r : Cardinal, Cardinal.toENat r ≠ 0 ↔ r ≠ 0 := fun r =>
    not_congr Cardinal.toENat_eq_zero
  rw [pos_iff_ne_zero]
  constructor
  · rintro ⟨-, J, hJ, hJ0, hJa, hJb⟩
    rw [key, Ne, Submodule.rank_eq_zero, Submodule.span_eq_bot]
    push Not
    exact ⟨J, ⟨hJ, hJa, hJb⟩, hJ0⟩
  · intro h
    rw [key, Ne, Submodule.rank_eq_zero, Submodule.span_eq_bot] at h
    push Not at h
    obtain ⟨J, ⟨hJ, hJa, hJb⟩, hJ0⟩ := h
    exact ⟨hab, J, hJ, hJ0, hJa, hJb⟩

/-- A ⇒ B, vacuously: B is proved outright (`B_holds`), the hypothesis is not used. -/
theorem A_to_B : A → B := fun _ => B_holds

/-- B ⇒ A, vacuously: A is re-proved outright (the project's proof of `isConjugate_iff`, from
non-item lemmas of `Morse/Chapter9/JacobiSpace.lean`); B is not used. -/
theorem B_to_A : B → A := by
  intro _ V _ _ _ Z _ _ _ W _ _ _ N hN γ hc a b
  constructor
  · rintro ⟨ha, hb, hab, J, hJ, hJa, hJb, t, ht, hJt⟩
    refine ⟨ha, hb, hab, Module.finrank_pos_iff_exists_ne_zero.2
      ⟨⟨fun t => J (projIcc (0 : ℝ) 1 zero_le_one t), ?_⟩, ?_⟩⟩
    · exact (Morse.mem_conjSpace hc).2 ⟨hJ.comp_projIcc_mem hc, by simp [projIcc_of_mem _ ha, hJa],
        by simp [projIcc_of_mem _ hb, hJb]⟩
    · intro h
      have := congrFun (congrArg Subtype.val h) t
      exact hJt (by simpa [projIcc_of_mem _ ht] using this)
  · rintro ⟨ha, hb, hab, hpos⟩
    obtain ⟨⟨J, hJ⟩, hJ0⟩ := Module.finrank_pos_iff_exists_ne_zero.1 hpos
    obtain ⟨hJs, hJa, hJb⟩ := (Morse.mem_conjSpace hc).1 hJ
    refine ⟨ha, hb, hab, J, hJs.1, hJa, hJb, ?_⟩
    by_contra hall
    push Not at hall
    exact hJ0 (Subtype.ext (Morse.jacobiSpace_eq_zero hc hJs hall))

#rt_check RoundTrip.V9_4.A_to_B [Morse.isConjugate_iff]
#rt_check RoundTrip.V9_4.B_to_A [Morse.isConjugate_iff]
#rt_overlap RoundTrip.V9_4.B_to_A [Morse.isConjugate_iff]

/-! ## The embedded special case: the definitions agree

On `M = ↥N` with the induced metric and connection, B's `IsConj` / `conjMult` are the project's
`IsConjugate` / `conjMultiplicity` (`Emb.isConj_iff`, `Emb.conjMult_eq`), through the dictionary
`Emb.isJacobi_iff` for Jacobi fields. -/

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

namespace Emb

open RoundTrip.Bridge

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W] {n : ℕ} {N : Set V}
  {hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) (Bridge.Rn n) W N}

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

/-- **Dictionary: multiplicity.** For a smooth curve `γ` in `N` on `[0,1]` and `a, b ∈ [0,1]`,
B's `conjMult` (an `ℕ∞`-valued dimension of a span) is the project's `conjMultiplicity`. -/
theorem conjMult_eq {γ : ℝ → Bridge.Sub hN} (hγ : IsSmoothCurve (n := n) γ (Icc 0 1)) {a b : ℝ}
    (ha : a ∈ Icc (0 : ℝ) 1) (hb : b ∈ Icc (0 : ℝ) 1) :
    conjMult (conn (hN := hN)) γ a b =
      (Morse.conjMultiplicity hN (incl hN ∘ γ) (isSmoothCurveIn hγ) a b : ℕ∞) := by
  have hc := isSmoothCurveIn hγ
  set C := Morse.conjSpace hN (incl hN ∘ γ) hc a b
  set S := {J : FA n γ | J ∈ JacOn (conn (hN := hN)) γ (Icc 0 1) ∧ J a = 0 ∧ J b = 0}
  set Φ : C →ₗ[ℝ] FA n γ := (toFAₗ γ).comp C.subtype
  have hmem : ∀ X : C, Φ X ∈ S := fun X => by
    obtain ⟨hXs, hXa, hXb⟩ := (Morse.mem_conjSpace hc).1 X.2
    refine ⟨toFA_mem_JacOn hγ hXs.1, ?_, ?_⟩
    · show toFA γ (X : ℝ → V) a = 0
      rw [toFA_of_mem _ ha, hXa, map_zero] <;> rfl
    · show toFA γ (X : ℝ → V) b = 0
      rw [toFA_of_mem _ hb, hXb, map_zero] <;> rfl
  have hinj : Injective Φ := fun X Y h => by
    have hX := ((Morse.mem_conjSpace hc).1 X.2).1
    have hY := ((Morse.mem_conjSpace hc).1 Y.2).1
    exact Subtype.ext (eq_of_eqOn_jacobiSpace hX hY (toFA_injOn hX.1.tangent hY.1.tangent h))
  have hspan : Submodule.span ℝ S = LinearMap.range Φ := by
    refine le_antisymm (Submodule.span_le.2 ?_) ?_
    · rintro J ⟨⟨hJ, hJo⟩, hJa, hJb⟩
      have hX := ((isJacobi_iff hγ J).1 hJ).comp_projIcc_mem hc
      have hXC : (fun t => ambA γ J (projIcc (0 : ℝ) 1 zero_le_one t)) ∈ C := by
        refine (Morse.mem_conjSpace hc).2 ⟨hX, ?_, ?_⟩
        · show ambA γ J (projIcc (0 : ℝ) 1 zero_le_one a) = 0
          rw [projIcc_of_mem _ ha]
          show D hN (γ a) (J a) = 0
          rw [hJa, D_tzero]
        · show ambA γ J (projIcc (0 : ℝ) 1 zero_le_one b) = 0
          rw [projIcc_of_mem _ hb]
          show D hN (γ b) (J b) = 0
          rw [hJb, D_tzero]
      refine ⟨⟨_, hXC⟩, funext fun t => ?_⟩
      by_cases ht : t ∈ Icc (0 : ℝ) 1
      · show toFA γ (fun t => ambA γ J (projIcc (0 : ℝ) 1 zero_le_one t)) t = J t
        rw [toFA_of_mem _ ht]
        simp only [projIcc_of_mem _ ht]
        exact L_D (γ t) (J t)
      · show toFA γ (fun t => ambA γ J (projIcc (0 : ℝ) 1 zero_le_one t)) t = J t
        rw [toFA_of_not_mem _ ht, hJo t ht]
    · rintro _ ⟨X, rfl⟩
      exact Submodule.subset_span (hmem X)
  unfold conjMult setDim
  rw [hspan, rank_range_of_injective Φ hinj, ← Module.finrank_eq_rank, Cardinal.toENat_nat]
  rfl

/-- Hence, on embedded manifolds, B's claim is literally A's (for geodesics, model `ℝⁿ`). -/
theorem isConj_iff_pos {γ : ℝ → Bridge.Sub hN} (hγ : IsSmoothCurve (n := n) γ (Icc 0 1)) {a b : ℝ}
    (ha : a ∈ Icc (0 : ℝ) 1) (hb : b ∈ Icc (0 : ℝ) 1) (hab : a ≠ b) :
    (IsConj (conn (hN := hN)) γ a b ↔ 0 < conjMult (conn (hN := hN)) γ a b) ↔
      (Morse.IsConjugate hN (incl hN ∘ γ) a b ↔
        a ∈ Icc (0 : ℝ) 1 ∧ b ∈ Icc (0 : ℝ) 1 ∧ a ≠ b ∧
          0 < Morse.conjMultiplicity hN (incl hN ∘ γ) (isSmoothCurveIn hγ) a b) := by
  rw [isConj_iff hγ ha hb, conjMult_eq hγ ha hb, Nat.cast_pos]
  simp only [ha, hb, hab, true_and, ne_eq, not_false_eq_true]

end Emb

#rt_check RoundTrip.V9_4.Emb.isConj_iff [Morse.isConjugate_iff]
#rt_check RoundTrip.V9_4.Emb.conjMult_eq [Morse.isConjugate_iff]

end RoundTrip.V9_4
