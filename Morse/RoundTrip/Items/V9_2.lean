import Morse
import RoundTrip.Check
import RoundTrip.Bridge
import RoundTrip.Blind.V9_2

open Set Filter Topology Function Module
open scoped ContDiff Manifold

namespace RoundTrip.V9_2

/-- The project's statement (universes instantiated at 0), for a slice submanifold `N ⊆ V` with
the induced metric and ANY smooth curve `γ` in `N` on `[0,1]` (`IsSmoothCurveIn`, not necessarily a
geodesic). There is no parallel frame: the Jacobi equation is the frameless first-order linear
system `jacSys` in `V × V` for `(J, DJ/dt)` (coefficients `S = P'P − PP'` and `K = R(V, P·)V`),
`jacSol hN γ s ζ` its solution with value `ζ` at `s`. A says: (1) for tangent data `ζ` at
`s ∈ [0,1]`, the first component of `jacSol` is a Jacobi field (`IsJacobiField`: smooth on `[0,1]`,
tangent, `D²J/dt² + R(V,J)V = 0` on `(0,1)`) whose covariant derivative (within `[0,1]`) is the
second component; (2) every Jacobi field `J` satisfies `(J, DJ/dt) = jacSol s (J s, DJ/dt s)` on
`[0,1]`, for every `s ∈ [0,1]`; (3) a Jacobi field with `J(s) = 0`, `DJ/dt(s) = 0` vanishes on
`[0,1]`. -/
def A : Prop :=
  type_of% @Morse.isJacobiField_jacSol.{0,0,0} ∧
    type_of% @Morse.IsJacobiField.eqOn_jacSol.{0,0,0} ∧
    type_of% @Morse.IsJacobiField.eqOn_zero.{0,0,0}

theorem A_holds : A :=
  ⟨@Morse.isJacobiField_jacSol, @Morse.IsJacobiField.eqOn_jacSol, @Morse.IsJacobiField.eqOn_zero⟩

/-! Neither `A → B` nor `B → A` is proved; see `V9_2.json`.

## The embedded special case

Dictionary `Emb.isJacobi_iff` (blind Jacobi fields of the induced connection on `↥N` ↔ the
project's `IsJacobiField`, read in `V`), then `A ⇒` clause (iii) of `B_emb` (uniqueness from the
initial data). Clauses (i) (existence of orthonormal parallel frames along `γ|[0,1]`) and (ii) (the
Jacobi equation in such a frame is `f'' + c f = 0`) are not in A, which works without frames. -/

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

open Bundle in
/-- B on embedded manifolds: `M = ↥N` with the induced metric and the induced Levi-Civita
connection `Bridge.conn` (a special case of B, see `B_to_B_emb`). -/
def B_emb : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    (W : Type) [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W] (n : ℕ)
    (N : Set V) (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) (Rn n) W N)
    [ConnectedSpace (Bridge.Sub hN)] (γ : ℝ → Bridge.Sub hN),
    IsGeodesic (Bridge.conn (hN := hN)) γ (Set.Icc 0 1) →
  (∃ P : Fin n → FA n γ, (∀ i, IsParallel (Bridge.conn (hN := hN)) γ (Set.Icc 0 1) (P i)) ∧
      ∀ i j, ∀ t ∈ Set.Icc (0:ℝ) 1, inner ℝ (P i t) (P j t) = if i = j then (1:ℝ) else 0) ∧
  (∀ P : Fin n → FA n γ, (∀ i, IsParallel (Bridge.conn (hN := hN)) γ (Set.Icc 0 1) (P i)) →
    (∀ i j, ∀ t ∈ Set.Icc (0:ℝ) 1, inner ℝ (P i t) (P j t) = if i = j then (1:ℝ) else 0) →
    ∀ (c : Fin n → Fin n → ℝ → ℝ),
      (∀ i j, ∀ t ∈ Set.Icc (0:ℝ) 1, ∃ r, IsCurvVal (Bridge.conn (hN := hN)) (γ t)
          (vel (n := n) γ (Set.Icc 0 1) t) (P j t) (vel (n := n) γ (Set.Icc 0 1) t) r ∧
          c i j t = inner ℝ (P i t) r) →
      ∀ (J : FA n γ) (f : Fin n → ℝ → ℝ), (∀ t ∈ Set.Icc (0:ℝ) 1, J t = ∑ i, f i t • P i t) →
        (IsJacobi (Bridge.conn (hN := hN)) γ (Set.Icc 0 1) J ↔
          ∀ i, ContDiffOn ℝ ∞ (f i) (Set.Icc 0 1) ∧ ∀ t ∈ Set.Icc (0:ℝ) 1,
            iteratedDerivWithin 2 (f i) (Set.Icc 0 1) t + ∑ j, c i j t * f j t = 0)) ∧
  (∀ J₁ J₂ J₁' J₂' : FA n γ, IsJacobi (Bridge.conn (hN := hN)) γ (Set.Icc 0 1) J₁ →
      IsJacobi (Bridge.conn (hN := hN)) γ (Set.Icc 0 1) J₂ →
      HasCovDeriv (Bridge.conn (hN := hN)) γ (Set.Icc 0 1) J₁ J₁' →
      HasCovDeriv (Bridge.conn (hN := hN)) γ (Set.Icc 0 1) J₂ J₂' →
      HEq (J₁ 0) (J₂ 0) → HEq (J₁' 0) (J₂' 0) → Set.EqOn J₁ J₂ (Set.Icc 0 1))

open Bundle in
/-- `B_emb` is a special case of B (the induced connection is Levi-Civita, `Bridge.conn_isLC`). -/
theorem B_to_B_emb : B → B_emb := fun hB _ _ _ _ _ _ _ _ n _ hN _ γ hγ =>
  hB n (Bridge.Sub hN) (Bridge.conn (hN := hN)) Bridge.conn_isLC γ hγ

/-- Clause (iii) of `B_emb`: uniqueness of Jacobi fields from `J(0)`, `DJ/dt(0)`. -/
def B_emb_iii : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    (W : Type) [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W] (n : ℕ)
    (N : Set V) (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) (Rn n) W N)
    [ConnectedSpace (Bridge.Sub hN)] (γ : ℝ → Bridge.Sub hN),
    IsGeodesic (Bridge.conn (hN := hN)) γ (Set.Icc 0 1) →
  (∀ J₁ J₂ J₁' J₂' : FA n γ, IsJacobi (Bridge.conn (hN := hN)) γ (Set.Icc 0 1) J₁ →
      IsJacobi (Bridge.conn (hN := hN)) γ (Set.Icc 0 1) J₂ →
      HasCovDeriv (Bridge.conn (hN := hN)) γ (Set.Icc 0 1) J₁ J₁' →
      HasCovDeriv (Bridge.conn (hN := hN)) γ (Set.Icc 0 1) J₂ J₂' →
      HEq (J₁ 0) (J₂ 0) → HEq (J₁' 0) (J₂' 0) → Set.EqOn J₁ J₂ (Set.Icc 0 1))

theorem B_emb_to_B_emb_iii : B_emb → B_emb_iii := fun h V _ _ _ W _ _ _ n N hN _ γ hγ =>
  (h V W n N hN γ hγ).2.2

namespace Emb

open RoundTrip.Bridge

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W] {n : ℕ} {N : Set V}
  {hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) (Bridge.Rn n) W N}

/-- From A (clause (2), `eqOn_jacSol` at `s = 0`): blind Jacobi fields with the same `J(0)`,
`DJ/dt(0)` agree on `[0,1]`. -/
theorem eqOn_of_initial (hA : A) {γ : ℝ → Bridge.Sub hN}
    (hγ : IsSmoothCurve (n := n) γ (Icc 0 1)) (J₁ J₂ J₁' J₂' : FA n γ)
    (h1 : IsJacobi (conn (hN := hN)) γ (Icc 0 1) J₁) (h2 : IsJacobi (conn (hN := hN)) γ (Icc 0 1) J₂)
    (h1' : HasCovDeriv (conn (hN := hN)) γ (Icc 0 1) J₁ J₁')
    (h2' : HasCovDeriv (conn (hN := hN)) γ (Icc 0 1) J₂ J₂')
    (e0 : HEq (J₁ 0) (J₂ 0)) (e0' : HEq (J₁' 0) (J₂' 0)) : EqOn J₁ J₂ (Icc 0 1) := by
  have hc := isSmoothCurveIn hγ
  have hγ' : RoundTrip.BridgePrelude.IsSmoothCurve (n := n) γ (Icc 0 1) := hγ
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have hcov : ∀ (J J' : FA n γ), HasCovDeriv (conn (hN := hN)) γ (Icc 0 1) J J' →
      Morse.covAlong hN (incl hN ∘ γ) (ambA γ J) 0 = ambA γ J' 0 := by
    intro J J' hJ
    have hJ' : RoundTrip.BridgePrelude.HasCovDeriv (conn (hN := hN)) γ (Icc 0 1) J J' := hJ
    rw [((hasCovDeriv_iff' isIntv_Icc hγ').1 hJ').2 0 h0, Morse.covAlong]
    exact congrFun (congrArg DFunLike.coe (prj_incl (γ 0))) _
  have hinit : (ambA γ J₁ 0, Morse.covAlong hN (incl hN ∘ γ) (ambA γ J₁) 0) =
      (ambA γ J₂ 0, Morse.covAlong hN (incl hN ∘ γ) (ambA γ J₂) 0) := by
    rw [hcov J₁ J₁' h1', hcov J₂ J₂' h2']
    show (D hN (γ 0) (J₁ 0), D hN (γ 0) (J₁' 0)) = (D hN (γ 0) (J₂ 0), D hN (γ 0) (J₂' 0))
    rw [eq_of_heq e0, eq_of_heq e0']
  intro t ht
  have k1 := hA.2.1 hc ((isJacobi_iff hγ J₁).1 h1) h0 ht
  have k2 := hA.2.1 hc ((isJacobi_iff hγ J₂).1 h2) h0 ht
  rw [hinit] at k1
  apply D_injective (γ t)
  exact congrArg Prod.fst (k1.trans k2.symm)

end Emb

/-- **A implies clause (iii) of B on embedded manifolds** (uses A's `eqOn_jacSol` through the
hypothesis, and the dictionary `Emb.isJacobi_iff`). -/
theorem A_to_B_emb_iii : A → B_emb_iii := fun hA _ _ _ _ _ _ _ _ _ _ _ _ γ hγ =>
  Emb.eqOn_of_initial hA hγ.2.1

#rt_check RoundTrip.V9_2.A_to_B_emb_iii [Morse.isJacobiField_jacSol,
  Morse.IsJacobiField.eqOn_jacSol, Morse.IsJacobiField.eqOn_zero]

/-! ### `B_emb (iii) ⇒` the uniqueness clause of A at `s = 0`, for blind geodesics -/

namespace Emb

open RoundTrip.Bridge

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W] {n : ℕ} {N : Set V}
  {hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) (Bridge.Rn n) W N}

omit [FiniteDimensional ℝ W] in
theorem isJacobiField_zero {c : ℝ → V} : Morse.IsJacobiField hN c 0 where
  contDiffOn := contDiffOn_const
  tangent _ _ := map_zero _
  eq t _ := by
    have h1 : Morse.covD hN c (0 : ℝ → V) = 0 := funext fun τ => by simp [Morse.covD]
    rw [Morse.jacobiExpr, h1, h1]
    by_cases hN' : c t ∈ N
    · rw [Morse.curvR_of_mem hN hN']
      simp [Morse.curvOp]
    · simp [Morse.curvR, hN']

/-- `DJ'/dt` of `toFA γ X`, read in `V`, is the project's `covAlong X`. -/
theorem D_of_hasCovDeriv_toFA {γ : ℝ → Bridge.Sub hN} (hγ : IsSmoothCurve (n := n) γ (Icc 0 1))
    {X : ℝ → V} (hX : ∀ t ∈ Icc (0 : ℝ) 1, Morse.prj hN ((incl hN ∘ γ) t) (X t) = X t)
    {J' : FA n γ} (hJ : HasCovDeriv (conn (hN := hN)) γ (Icc 0 1) (toFA γ X) J') {s : ℝ}
    (hs : s ∈ Icc (0 : ℝ) 1) : D hN (γ s) (J' s) = Morse.covAlong hN (incl hN ∘ γ) X s := by
  have hγ' : RoundTrip.BridgePrelude.IsSmoothCurve (n := n) γ (Icc 0 1) := hγ
  have hJ' : RoundTrip.BridgePrelude.HasCovDeriv (conn (hN := hN)) γ (Icc 0 1) (toFA γ X) J' := hJ
  refine (((hasCovDeriv_iff' isIntv_Icc hγ').1 hJ').2 s hs).trans ?_
  rw [Morse.covAlong, derivWithin_congr (ambA_toFA hX) (ambA_toFA hX hs)]
  exact (congrFun (congrArg DFunLike.coe (prj_incl (γ s))) _).symm

end Emb

/-- The part of A that `B_emb (iii)` covers: A's uniqueness clause (`eqOn_zero`) at `s = 0`, for
the curves `incl ∘ γ`, `γ` a blind geodesic on `[0,1]` of `↥N` (connected, model `ℝⁿ`). -/
def A3_0 : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    (W : Type) [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W] (n : ℕ)
    (N : Set V) (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) (Rn n) W N)
    [ConnectedSpace (Bridge.Sub hN)] (γ : ℝ → Bridge.Sub hN),
    IsGeodesic (Bridge.conn (hN := hN)) γ (Set.Icc 0 1) → ∀ J : ℝ → V,
    Morse.IsJacobiField hN (Bridge.incl hN ∘ γ) J → J 0 = 0 →
    Morse.covAlong hN (Bridge.incl hN ∘ γ) J 0 = 0 → Set.EqOn J 0 (Set.Icc 0 1)

/-- `A3_0` is an instance of A. -/
theorem A_to_A3_0 : A → A3_0 := fun hA _ _ _ _ _ _ _ _ _ _ _ _ _ hγ _ hJ h0 h0' =>
  hA.2.2 (Emb.isSmoothCurveIn hγ.2.1) hJ ⟨le_rfl, zero_le_one⟩ h0 h0'

/-- **`B_emb (iii)` implies `A3_0`**: compare the Jacobi field with the zero field. -/
theorem B_emb_iii_to_A3_0 : B_emb_iii → A3_0 := by
  intro hB V _ _ _ W _ _ _ n N hN _ γ hγ J hJ hJ0 hJ0'
  have hγs : IsSmoothCurve (n := n) γ (Set.Icc 0 1) := hγ.2.1
  have h0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have hZ : Morse.IsJacobiField hN (Bridge.incl hN ∘ γ) (0 : ℝ → V) := Emb.isJacobiField_zero
  obtain ⟨J₁', -, hJ₁', -⟩ := (Emb.toFA_mem_JacOn hγs hJ).1
  obtain ⟨J₂', -, hJ₂', -⟩ := (Emb.toFA_mem_JacOn hγs hZ).1
  have heq := hB V W n N hN γ hγ _ _ J₁' J₂' (Emb.toFA_mem_JacOn hγs hJ).1
    (Emb.toFA_mem_JacOn hγs hZ).1 hJ₁' hJ₂'
    (heq_of_eq (by rw [Emb.toFA_of_mem _ h0, Emb.toFA_of_mem _ h0, hJ0]; rfl))
    (heq_of_eq (Bridge.D_injective (γ 0) (by
      rw [Emb.D_of_hasCovDeriv_toFA hγs hJ.tangent hJ₁' h0,
        Emb.D_of_hasCovDeriv_toFA hγs hZ.tangent hJ₂' h0, hJ0']
      simp [Morse.covAlong])))
  intro t ht
  rw [← Emb.ambA_toFA hJ.tangent ht]
  show Bridge.D hN (γ t) _ = 0
  rw [heq ht, Emb.toFA_of_mem _ ht]
  simp

/-- **B implies `A3_0`**, by specializing B to `↥N` with the induced connection. -/
theorem B_to_A3_0 : B → A3_0 := fun hB => B_emb_iii_to_A3_0 (B_emb_to_B_emb_iii (B_to_B_emb hB))

#rt_check RoundTrip.V9_2.B_to_A3_0 [Morse.isJacobiField_jacSol,
  Morse.IsJacobiField.eqOn_jacSol, Morse.IsJacobiField.eqOn_zero]
#rt_overlap RoundTrip.V9_2.B_to_A3_0 [Morse.isJacobiField_jacSol,
  Morse.IsJacobiField.eqOn_jacSol, Morse.IsJacobiField.eqOn_zero]

end RoundTrip.V9_2
