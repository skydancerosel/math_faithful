import Morse
import RoundTrip.Check
import RoundTrip.Blind.V10_23
import RoundTrip.Bridge
import RoundTrip.EnergyC2

open Set Filter Topology Function Module MeasureTheory
open scoped ContDiff Manifold ENNReal unitInterval RealInnerProductSpace

namespace RoundTrip.V10_23

/-- The project's statement (no universe parameters; `sphLen`, `sphGeod` are vocabulary): for
`p, q ∈ Sⁿ ⊆ ℝⁿ⁺¹`, `q ≠ ±p`, with `γ_k = sphGeod p q k` the great circle through `p`, `q` of
length `L_k = sphLen p q k` (`θ + 2πj` for `k = 2j`, `2π(j+1) − θ` for `k = 2j + 1`):
`kπ < L_k` (`mul_pi_lt_sphLen`), `E(γ_k) = L_k²` (`energy_sphGeod`), every geodesic from `p` to `q`
agrees on `[0, 1]` with some `γ_k` (`exists_eqOn_sphGeod`, `n ≥ 1`), `q ∉ conjLocus p`
(`notMem_conjLocus_sph`), and the index of `γ_k`, and of any geodesic agreeing with it on
`[0, 1]`, is `k(n − 1)` (`formIndex_sphGeod`, `formIndex_eq_of_eqOn_sphGeod`). -/
def A : Prop :=
  type_of% @Morse.mul_pi_lt_sphLen ∧ type_of% @Morse.energy_sphGeod ∧
    type_of% @Morse.exists_eqOn_sphGeod ∧ type_of% @Morse.notMem_conjLocus_sph ∧
    type_of% @Morse.formIndex_sphGeod ∧ type_of% @Morse.formIndex_eq_of_eqOn_sphGeod

theorem A_holds : A := ⟨@Morse.mul_pi_lt_sphLen, @Morse.energy_sphGeod, @Morse.exists_eqOn_sphGeod,
  @Morse.notMem_conjLocus_sph, @Morse.formIndex_sphGeod, @Morse.formIndex_eq_of_eqOn_sphGeod⟩

/-! **Summary** (see `V10_23.json`).  B is false (`not_B`): it allows `n = 1`, where the claimed
conjugate points (multiplicity `n − 1 = 0`) do not exist; counter-model `S¹ ⊆ ℝ²` through the
Bridge.  Hence `¬ (A → B)` (`not_A_to_B`) and `B → A` only ex falso (`B_to_A`).  For the corrected
reading `Bcorr` (`n ≥ 2`) on the embedded sphere, A gives every clause but the index clause
(`A_to_Bcorr_emb_noLam`), and the index clause under the unproved bridge `LamEq`
(`A_to_BcorrEmbAt_of_lamEq`).  Dictionary: `Emb` (Jacobi fields / conjugate points / multiplicity,
copied from `Items/V9_4.lean`, geodesic lifting from `Items/V9_10.lean`), `Sph` (the embedded
round sphere as a blind `IsRoundSphere`). -/

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


/-! #### From `Items/V9_10.lean` -/

/-- On the interior, `derivWithin [0,1]` of a function smooth on `[0, 1]` is `deriv`, near `t`. -/
theorem derivWithin_eventuallyEq {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : ℝ → E} (hF : ContDiffOn ℝ ∞ F (Icc 0 1)) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    derivWithin F (Icc 0 1) =ᶠ[𝓝 t] deriv F := by
  filter_upwards [Ioo_mem_nhds ht.1 ht.2] with x hx
  exact ((hF.contDiffAt (Icc_mem_nhds hx.1 hx.2)).differentiableAt (by simp)).hasDerivAt
    |>.hasDerivWithinAt.derivWithin (uniqueDiffOn_Icc zero_lt_one x (Ioo_subset_Icc_self hx))

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

/-- A blind geodesic on `[0, 1]` of `↥N` from `p` to `q` is, in `V`, a project geodesic of
`Ω(N; p, q)`. -/
theorem mem_pathSpace_of_isGeodesic {γ : ℝ → Bridge.Sub hN} {p q : Bridge.Sub hN}
    (h : IsGeodesic (conn (hN := hN)) γ (Icc 0 1)) (h0 : γ 0 = p) (h1 : γ 1 = q) :
    incl hN ∘ γ ∈ Morse.pathSpace N (incl hN p) (incl hN q) ∧
      Morse.IsUnbrokenGeodesic hN (incl hN ∘ γ) := by
  have h' : RoundTrip.BridgePrelude.IsGeodesic (conn (hN := hN)) γ (Icc 0 1) := h
  obtain ⟨-, hc, -⟩ := isGeodesic_iff.1 h'
  exact ⟨⟨Morse.IsPiecewiseSmooth.of_contDiffOn hc zero_le_one subset_rfl, fun t _ => (γ t).2,
    congrArg (incl hN) h0, congrArg (incl hN) h1⟩, hc, isGeodesicOn_Ioo h'⟩

end Emb

/-! ### The round sphere through the Bridge -/

namespace Sph

open RoundTrip.Bridge Milnor.Sphere

/-- `Sⁿ = Milnor.Sphere.Sph n ⊆ ℝⁿ⁺¹` as a blind manifold (model `ℝⁿ`, induced metric). -/
abbrev S (n : ℕ) : Type := Bridge.Sub (sphSub n)

/-- `ψ = incl : Sⁿ → ℝⁿ⁺¹`. -/
noncomputable abbrev ψ (n : ℕ) : S n → EuclideanSpace ℝ (Fin (n + 1)) := Bridge.incl (sphSub n)

/-- The inclusion of the project's sphere is a blind `IsRoundSphere`. -/
theorem isRoundSphere (n : ℕ) : IsRoundSphere n (ψ n) := by
  refine ⟨Bridge.contMDiff_incl (hN := sphSub n), Subtype.val_injective, ?_, fun x v w => ?_⟩
  · show range (Subtype.val : Sph n → _) = _
    rw [Subtype.range_coe]
    exact preimage_eq_sphere
  · exact Bridge.inner_eq x v w

theorem connectedSpace (n : ℕ) (hn : 1 ≤ n) : ConnectedSpace (S n) := by
  have hrank : 1 < Module.rank ℝ (EuclideanSpace ℝ (Fin (n + 1))) := by
    rw [← Module.finrank_eq_rank, finrank_euclideanSpace, Fintype.card_fin]
    exact_mod_cast (by omega : 1 < n + 1)
  have h : IsConnected (Sph n) := by
    rw [show Sph n = Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 from preimage_eq_sphere]
    exact isConnected_sphere hrank 0 zero_le_one
  exact Subtype.connectedSpace h

end Sph

/-! ## B is false for `n = 1`

B allows `n = 1`, where it claims that each interior passage of `γ_k` through `p` or `p'` is
CONJUGATE to `p` (`IsConj`, a non-zero Jacobi field vanishing at both ends) with multiplicity
`n − 1 = 0`.  On `S¹` there are no conjugate points at all (curvature `0`): `IsConj` fails.
Counter-model: `S¹ ⊆ ℝ²` (`Bridge.Sub (sphSub 1)`, induced metric and connection, `ψ` the
inclusion), `p = e₀`, `q = e₁`; B's `γ_1` passes once through `p'` in `(0, 1)` (the count clause),
and the conjugacy clause there contradicts `Morse.conjMultiplicity_greatCircle` (multiplicity
`n − 1 = 0`). -/

section NotB

open Sph Milnor.Sphere

/-- On `S¹` a blind geodesic from `p` to `q ≠ p` has no point conjugate to `t = 0`. -/
theorem not_isConj_S1 {γ : ℝ → S 1} {p q : S 1} (hpq : ψ 1 q ≠ ψ 1 p)
    (hγ : IsGeodPQ 1 (Bridge.conn (hN := sphSub 1)) p q γ) {t : ℝ} (ht : t ∈ Ioc (0 : ℝ) 1) :
    ¬ IsConj (Bridge.conn (hN := sphSub 1)) γ 0 t := by
  intro hconj
  obtain ⟨hgeo, h0, h1⟩ := hγ
  have hsm : IsSmoothCurve (n := 1) γ (Icc 0 1) := hgeo.2.1
  have hI0 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have hIt : t ∈ Icc (0 : ℝ) 1 := ⟨ht.1.le, ht.2⟩
  have hc := (Emb.isConj_iff hsm hI0 hIt).1 hconj
  obtain ⟨hmem, hunb⟩ := Emb.mem_pathSpace_of_isGeodesic hgeo h0 h1
  obtain ⟨u, L, hu, hpu, hL, heq⟩ := Morse.exists_eqOn_greatCircle le_rfl hmem hunb
  have hp : ψ 1 p ∈ Sph 1 := p.2
  have hL0 : 0 < L := by
    rcases hL.lt_or_eq with h | h
    · exact h
    · exfalso
      apply hpq
      have e1 := heq (show (1 : ℝ) ∈ Icc (0 : ℝ) 1 from ⟨zero_le_one, le_rfl⟩)
      rw [← h] at e1
      simp only [Function.comp_apply, h1, Morse.greatCircle, zero_mul, Real.cos_zero,
        Real.sin_zero, one_smul, zero_smul, add_zero] at e1
      exact e1
  have hgc := Morse.isSmoothCurveIn_greatCircle hp hu hpu L
  have hconj' := Emb.isConjugate_congr heq hc
  have hpos := ((Morse.isConjugate_iff hgc).1 hconj').2.2.2
  rw [Morse.conjMultiplicity_greatCircle le_rfl hp hu hpu hL0 hgc ht] at hpos
  split_ifs at hpos <;> simp at hpos

theorem single_mem (i : Fin 2) : (EuclideanSpace.single i (1 : ℝ)) ∈ Sph 1 :=
  mem_iff_norm.2 (by simp)

/-- **B is false** (at `n = 1`, on the embedded `S¹`). -/
theorem not_B : ¬ B := by
  intro hB
  haveI := Sph.connectedSpace 1 le_rfl
  let p₀ : S 1 := (⟨EuclideanSpace.single 0 1, single_mem 0⟩ : Sph 1)
  let q₀ : S 1 := (⟨EuclideanSpace.single 1 1, single_mem 1⟩ : Sph 1)
  have e10 : ψ 1 q₀ ≠ ψ 1 p₀ := by
    intro h
    have := congrArg (fun x : EuclideanSpace ℝ (Fin 2) => x 1) h
    simp [p₀, q₀, Sph.ψ, Bridge.incl] at this
  have e11 : ψ 1 q₀ ≠ -ψ 1 p₀ := by
    intro h
    have := congrArg (fun x : EuclideanSpace ℝ (Fin 2) => x 1) h
    simp [p₀, q₀, Sph.ψ, Bridge.incl] at this
  obtain ⟨γ, hgeo, -, -, -, hcard, hconj, -⟩ :=
    hB 1 (S 1) (Bridge.conn (hN := sphSub 1)) Bridge.conn_isLC le_rfl (ψ 1) (isRoundSphere 1)
      p₀ q₀ e10 e11
  obtain ⟨t, ht, hpt⟩ := Set.nonempty_of_ncard_ne_zero (by rw [hcard 1]; exact one_ne_zero)
  exact not_isConj_S1 e10 (hgeo 1) ⟨ht.1, ht.2.le⟩ (hconj 1 t ht hpt).1

/-- B ⇒ A, ex falso (B is false). -/
theorem B_to_A : B → A := fun hB => absurd hB not_B

end NotB

#rt_check RoundTrip.V10_23.B_to_A [Morse.mul_pi_lt_sphLen, Morse.energy_sphGeod, Morse.exists_eqOn_sphGeod, Morse.notMem_conjLocus_sph, Morse.formIndex_sphGeod, Morse.formIndex_eq_of_eqOn_sphGeod]

/-! ## The corrected reading (`n ≥ 2`) on the embedded sphere

`Bcorr` is B with `2 ≤ n` (Milnor's setting; for `n = 1` the "conjugate with multiplicity
`n − 1 = 0`" clause fails).  `BcorrEmbAt n` is its conclusion on the embedded `Sⁿ` (`ψ` the
inclusion, induced connection).  A gives all of it except the index clause (`A_to_Bcorr_emb_noLam`),
and the index clause too under the (unproved) bridge `LamEq n`: B's variational index
`lam 1 γ` of a blind geodesic is the project's `formIndex (energyHessian …)`. -/

open Bundle in
/-- B with Milnor's implicit `n ≥ 2`. -/
def Bcorr : Prop :=
  ∀ (n : ℕ) (M : Type) [TopologicalSpace M] [T2Space M] [ChartedSpace (Rn n) M] [IsManifold 𝓘(ℝ, Rn n) ∞ M] [Bundle.RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, Rn n) x)] [IsContMDiffRiemannianBundle 𝓘(ℝ, Rn n) ∞ (Rn n) (fun x : M => TangentSpace 𝓘(ℝ, Rn n) x)] [ConnectedSpace M], ∀ (cov : Conn n M), IsLC cov → 2 ≤ n → ∀ ψ : M → EuclideanSpace ℝ (Fin (n + 1)), IsRoundSphere n ψ →
  ∀ (p q : M), ψ q ≠ ψ p → ψ q ≠ -ψ p →
    ∃ γ : ℕ → ℝ → M, (∀ k, IsGeodPQ n cov p q (γ k)) ∧
      (∀ k k', Set.EqOn (γ k) (γ k') (Set.Icc 0 1) → k = k') ∧
      (∀ g, IsGeodPQ n cov p q g → ∃ k, Set.EqOn g (γ k) (Set.Icc 0 1)) ∧
      (∀ k : ℕ, arcLen (n := n) (γ k) 0 1 =
        if Even k then k * Real.pi + Real.arccos (inner ℝ (ψ p) (ψ q)) else (k + 1) * Real.pi - Real.arccos (inner ℝ (ψ p) (ψ q))) ∧
      (∀ k : ℕ, {t : ℝ | t ∈ Set.Ioo (0 : ℝ) 1 ∧ (ψ (γ k t) = ψ p ∨ ψ (γ k t) = -ψ p)}.ncard = k) ∧
      (∀ k : ℕ, ∀ t ∈ Set.Ioo (0 : ℝ) 1, (ψ (γ k t) = ψ p ∨ ψ (γ k t) = -ψ p) →
        IsConj cov (γ k) 0 t ∧ conjMult cov (γ k) 0 t = ((n - 1 : ℕ) : ℕ∞)) ∧
      (∀ k : ℕ, lam (n := n) 1 (γ k) = ((k * (n - 1) : ℕ) : ℕ∞))

theorem B_to_Bcorr : B → Bcorr := fun hB n M _ _ _ _ _ _ _ cov hcov hn =>
  hB n M cov hcov (by omega)

section Corr

open Sph Milnor.Sphere

/-- The six clauses of B other than the index clause, on the embedded `Sⁿ`. -/
def ClausesNoLam (n : ℕ) (p q : S n) (γ : ℕ → ℝ → S n) : Prop :=
  (∀ k, IsGeodPQ n (Bridge.conn (hN := sphSub n)) p q (γ k)) ∧
  (∀ k k', Set.EqOn (γ k) (γ k') (Set.Icc 0 1) → k = k') ∧
  (∀ g, IsGeodPQ n (Bridge.conn (hN := sphSub n)) p q g → ∃ k, Set.EqOn g (γ k) (Set.Icc 0 1)) ∧
  (∀ k : ℕ, arcLen (n := n) (γ k) 0 1 =
    if Even k then k * Real.pi + Real.arccos (inner ℝ (ψ n p) (ψ n q))
    else (k + 1) * Real.pi - Real.arccos (inner ℝ (ψ n p) (ψ n q))) ∧
  (∀ k : ℕ, {t : ℝ | t ∈ Set.Ioo (0 : ℝ) 1 ∧ (ψ n (γ k t) = ψ n p ∨ ψ n (γ k t) = -ψ n p)}.ncard = k) ∧
  (∀ k : ℕ, ∀ t ∈ Set.Ioo (0 : ℝ) 1, (ψ n (γ k t) = ψ n p ∨ ψ n (γ k t) = -ψ n p) →
    IsConj (Bridge.conn (hN := sphSub n)) (γ k) 0 t ∧
      conjMult (Bridge.conn (hN := sphSub n)) (γ k) 0 t = ((n - 1 : ℕ) : ℕ∞))

/-- The conclusion of `Bcorr` on the embedded `Sⁿ`. -/
def BcorrEmbAt (n : ℕ) : Prop :=
  ∀ (p q : S n), ψ n q ≠ ψ n p → ψ n q ≠ -ψ n p →
    ∃ γ : ℕ → ℝ → S n, ClausesNoLam n p q γ ∧
      (∀ k : ℕ, lam (n := n) 1 (γ k) = ((k * (n - 1) : ℕ) : ℕ∞))

/-- `Bcorr` on the embedded round sphere (`ψ` the inclusion, induced connection). -/
def Bcorr_emb : Prop := ∀ n : ℕ, 2 ≤ n → BcorrEmbAt n

theorem Bcorr_to_Bcorr_emb : Bcorr → Bcorr_emb := fun hB n hn p q h1 h2 => by
  haveI := Sph.connectedSpace n (by omega)
  obtain ⟨γ, c1, c2, c3, c4, c5, c6, c7⟩ :=
    hB n (S n) (Bridge.conn (hN := sphSub n)) Bridge.conn_isLC hn (ψ n) (isRoundSphere n) p q h1 h2
  exact ⟨γ, ⟨c1, c2, c3, c4, c5, c6⟩, c7⟩

/-- `Bcorr_emb` without the index clause. -/
def Bcorr_emb_noLam : Prop :=
  ∀ n : ℕ, 2 ≤ n → ∀ (p q : S n), ψ n q ≠ ψ n p → ψ n q ≠ -ψ n p →
    ∃ γ : ℕ → ℝ → S n, ClausesNoLam n p q γ

/-- **The missing bridge** (not proved): B's variational index of a blind geodesic from `p` to `q`
on the embedded `Sⁿ` is the project's index of the formula-defined `energyHessian`. -/
def LamEq (n : ℕ) : Prop :=
  ∀ (p q : S n) (γ : ℝ → S n)
    (hγ : Bridge.incl (sphSub n) ∘ γ ∈ Morse.pathSpace (Sph n) (ψ n p) (ψ n q)),
    IsGeodPQ n (Bridge.conn (hN := sphSub n)) p q γ →
      lam (n := n) 1 γ = Morse.formIndex (Morse.energyHessian (sphSub n) hγ)

/-! ### Glue: Milnor's `γ_k` as blind curves -/

variable {n : ℕ} {p q : S n}

theorem mem_p (p : S n) : ψ n p ∈ Sph n := p.2

/-- Milnor's `γ_k` (`Morse.sphGeod`), lifted to a blind curve in `Sⁿ`. -/
noncomputable def G (p q : S n) (k : ℕ) : ℝ → S n :=
  Bridge.lift (Morse.sphGeod (ψ n p) (ψ n q) k) p

/-- The direction of `γ_k`. -/
noncomputable abbrev dir (p q : S n) (k : ℕ) : EuclideanSpace ℝ (Fin (n + 1)) :=
  (if Even k then (1 : ℝ) else -1) • Morse.sphDir (ψ n p) (ψ n q)

theorem norm_dir (h1 : ψ n q ≠ ψ n p) (h2 : ψ n q ≠ -ψ n p) (k : ℕ) : ‖dir p q k‖ = 1 :=
  Morse.norm_sphGeodDir (mem_p p) (mem_p q) h1 h2 k

theorem inner_dir (h1 : ψ n q ≠ ψ n p) (h2 : ψ n q ≠ -ψ n p) (k : ℕ) : ⟪ψ n p, dir p q k⟫ = 0 :=
  Morse.inner_sphGeodDir (mem_p p) (mem_p q) h1 h2 k

theorem sphGeod_eq (k : ℕ) : Morse.sphGeod (ψ n p) (ψ n q) k =
    Morse.greatCircle (ψ n p) (dir p q k) (Morse.sphLen (ψ n p) (ψ n q) k) := rfl

theorem incl_G (h1 : ψ n q ≠ ψ n p) (h2 : ψ n q ≠ -ψ n p) (k : ℕ) :
    Bridge.incl (sphSub n) ∘ G p q k = Morse.sphGeod (ψ n p) (ψ n q) k := by
  funext t
  exact Bridge.incl_lift p (Morse.greatCircle_mem_sph (mem_p p) (norm_dir h1 h2 k)
    (inner_dir h1 h2 k) _ t)

theorem isGeodPQ_G (h1 : ψ n q ≠ ψ n p) (h2 : ψ n q ≠ -ψ n p) (k : ℕ) :
    IsGeodPQ n (Bridge.conn (hN := sphSub n)) p q (G p q k) := by
  have hc : Morse.IsSmoothCurveIn (sphSub n) (Morse.sphGeod (ψ n p) (ψ n q) k) :=
    Morse.isSmoothCurveIn_greatCircle (mem_p p) (norm_dir h1 h2 k)
      (inner_dir h1 h2 k) _
  obtain ⟨hgeo, -⟩ := Emb.isGeodesic_lift hc (Morse.isUnbrokenGeodesic_sphGeod (mem_p p) (mem_p q) h1 h2 k).2 p
  refine ⟨hgeo, Subtype.ext ?_, Subtype.ext ?_⟩
  · show (Bridge.incl (sphSub n) ∘ G p q k) 0 = ψ n p
    rw [incl_G h1 h2 k, sphGeod_eq]
    exact Morse.greatCircle_zero _ _ _
  · show (Bridge.incl (sphSub n) ∘ G p q k) 1 = ψ n q
    rw [incl_G h1 h2 k]
    exact Morse.sphGeod_one (mem_p p) (mem_p q) h1 h2 k

theorem sphLen_pos' (hA : A) (h1 : ψ n q ≠ ψ n p) (h2 : ψ n q ≠ -ψ n p) (k : ℕ) :
    0 < Morse.sphLen (ψ n p) (ψ n q) k :=
  lt_of_le_of_lt (by positivity) (hA.1 (mem_p p) (mem_p q) h1 h2 k)

theorem G_inj (hA : A) (h1 : ψ n q ≠ ψ n p) (h2 : ψ n q ≠ -ψ n p) {k k' : ℕ}
    (h : EqOn (G p q k) (G p q k') (Icc 0 1)) : k = k' := by
  have hE : Morse.energy (Morse.sphGeod (ψ n p) (ψ n q) k) 0 1 =
      Morse.energy (Morse.sphGeod (ψ n p) (ψ n q) k') 0 1 := by
    rw [← incl_G h1 h2 k, ← incl_G h1 h2 k']
    exact Morse.energy_congr fun t ht => by simp only [Function.comp_apply, h ht]
  rw [hA.2.1 (mem_p p) (mem_p q) h1 h2 k, hA.2.1 (mem_p p) (mem_p q) h1 h2 k'] at hE
  have hp0 := sphLen_pos' hA h1 h2 k
  have hp0' := sphLen_pos' hA h1 h2 k'
  have hL : Morse.sphLen (ψ n p) (ψ n q) k = Morse.sphLen (ψ n p) (ψ n q) k' := by
    nlinarith
  by_contra hne
  have key : ∀ {a b : ℕ}, a < b →
      Morse.sphLen (ψ n p) (ψ n q) a < Morse.sphLen (ψ n p) (ψ n q) b := fun {a b} hab => by
    have e1 := Morse.sphLen_lt (mem_p p) (mem_p q) h1 h2 a
    have e2 := hA.1 (mem_p p) (mem_p q) h1 h2 b
    have e3 : ((a : ℝ) + 1) ≤ b := by exact_mod_cast hab
    nlinarith [Real.pi_pos]
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · exact absurd hL (key hlt).ne
  · exact absurd hL (key hlt).ne'

theorem exists_G (hA : A) (hn : 1 ≤ n) (h1 : ψ n q ≠ ψ n p) (h2 : ψ n q ≠ -ψ n p) {g : ℝ → S n}
    (hg : IsGeodPQ n (Bridge.conn (hN := sphSub n)) p q g) : ∃ k, EqOn g (G p q k) (Icc 0 1) := by
  obtain ⟨hmem, hunb⟩ := Emb.mem_pathSpace_of_isGeodesic hg.1 hg.2.1 hg.2.2
  obtain ⟨k, hk⟩ := hA.2.2.1 (mem_p p) (mem_p q) h1 h2 hn hmem hunb
  refine ⟨k, fun t ht => Subtype.ext ?_⟩
  have e := hk ht
  rw [← incl_G h1 h2 k] at e
  exact e

theorem pathLength_greatCircle {u v : EuclideanSpace ℝ (Fin (n + 1))} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    (huv : ⟪u, v⟫ = 0) {L : ℝ} (hL : 0 ≤ L) : Morse.pathLength (Morse.greatCircle u v L) 0 1 = L := by
  have huv' : ⟪v, -u⟫ = 0 := by rw [inner_neg_right, real_inner_comm, huv, neg_zero]
  have h : ∀ t, ‖deriv (Morse.greatCircle u v L) t‖ = L := fun t => by
    rw [Morse.deriv_greatCircle, norm_smul, Morse.norm_greatCircle hv (by rw [norm_neg, hu]) huv' L t,
      mul_one, Real.norm_eq_abs, abs_of_nonneg hL]
  simp only [Morse.pathLength, h, intervalIntegral.integral_const, sub_zero, one_smul]

theorem arcLen_G (hA : A) (h1 : ψ n q ≠ ψ n p) (h2 : ψ n q ≠ -ψ n p) (k : ℕ) :
    arcLen (n := n) (G p q k) 0 1 =
      if Even k then k * Real.pi + Real.arccos (inner ℝ (ψ n p) (ψ n q))
      else (k + 1) * Real.pi - Real.arccos (inner ℝ (ψ n p) (ψ n q)) := by
  have e : arcLen (n := n) (G p q k) 0 1 = Morse.sphLen (ψ n p) (ψ n q) k := by
    refine (Bridge.arcLen_eq (G p q k) 0 1).trans ?_
    rw [incl_G h1 h2 k, sphGeod_eq]
    exact pathLength_greatCircle (Morse.norm_of_mem_sph (mem_p p)) (norm_dir h1 h2 k)
      (inner_dir h1 h2 k) (sphLen_pos' hA h1 h2 k).le
  rw [e, Morse.sphLen, Morse.sphAngle]
  split_ifs with hk
  · have : ((k / 2 : ℕ) : ℝ) * 2 = k := by exact_mod_cast Nat.div_two_mul_two_of_even hk
    rw [← this]; ring
  · have hk' : Odd k := Nat.not_even_iff_odd.1 hk
    have : ((k / 2 : ℕ) : ℝ) * 2 + 1 = k := by exact_mod_cast Nat.div_two_mul_two_add_one_of_odd hk'
    rw [← this]; ring

theorem greatCircle_eq_pm_iff {u v : EuclideanSpace ℝ (Fin (n + 1))} (hv : ‖v‖ = 1)
    (huv : ⟪u, v⟫ = 0) (L t : ℝ) :
    (Morse.greatCircle u v L t = u ∨ Morse.greatCircle u v L t = -u) ↔ Real.sin (L * t) = 0 := by
  have hvv : ⟪v, v⟫ = 1 := by rw [real_inner_self_eq_norm_sq, hv, one_pow]
  constructor
  · intro h
    have key : ⟪Morse.greatCircle u v L t, v⟫ = Real.sin (L * t) := by
      rw [Morse.inner_greatCircle_left, huv, hvv]; ring
    rcases h with h | h
    · rw [h, huv] at key; exact key.symm
    · rw [h, inner_neg_left, huv, neg_zero] at key; exact key.symm
  · intro hs
    have hc : (Real.cos (L * t) - 1) * (Real.cos (L * t) + 1) = 0 := by
      nlinarith [Real.sin_sq_add_cos_sq (L * t)]
    rcases mul_eq_zero.1 hc with h | h
    · left
      rw [Morse.greatCircle, hs, show Real.cos (L * t) = 1 by linarith]; simp
    · right
      rw [Morse.greatCircle, hs, show Real.cos (L * t) = -1 by linarith]; simp

/-- For `0 < t < 1` and `kπ < L < (k+1)π`: `sin(Lt) = 0` iff `Lt = jπ` with `j ∈ ℕ` (necessarily
`1 ≤ j ≤ k`). -/
theorem sin_eq_zero_iff_nat {L t : ℝ} (hL : 0 < L) (ht : 0 < t) :
    Real.sin (L * t) = 0 ↔ ∃ j : ℕ, L * t = j * Real.pi := by
  constructor
  · intro hs
    obtain ⟨m, hm⟩ := Real.sin_eq_zero_iff.1 hs
    have hm0 : (0 : ℝ) < m := by
      have : 0 < (m : ℝ) * Real.pi := by rw [hm]; exact mul_pos hL ht
      exact pos_of_mul_pos_left this Real.pi_pos.le
    have hm0' : 0 ≤ m := by exact_mod_cast hm0.le
    lift m to ℕ using hm0'
    exact ⟨m, by rw [← hm]; push_cast; ring⟩
  · rintro ⟨j, hj⟩
    rw [hj]; exact Real.sin_nat_mul_pi j

theorem ncard_G (hA : A) (h1 : ψ n q ≠ ψ n p) (h2 : ψ n q ≠ -ψ n p) (k : ℕ) :
    {t : ℝ | t ∈ Set.Ioo (0 : ℝ) 1 ∧
      (ψ n (G p q k t) = ψ n p ∨ ψ n (G p q k t) = -ψ n p)}.ncard = k := by
  set L := Morse.sphLen (ψ n p) (ψ n q) k with hLdef
  have hk1 : k * Real.pi < L := hA.1 (mem_p p) (mem_p q) h1 h2 k
  have hk2 : L < (k + 1) * Real.pi := Morse.sphLen_lt (mem_p p) (mem_p q) h1 h2 k
  have hL : 0 < L := sphLen_pos' hA h1 h2 k
  have hψ : ∀ t, ψ n (G p q k t) = Morse.greatCircle (ψ n p) (dir p q k) L t := fun t =>
    congrFun (incl_G h1 h2 k) t
  have hinj : Injective (fun j : ℕ => (j : ℝ) * Real.pi / L) := by
    intro i j hij
    have : (i : ℝ) = j := by
      have := hij
      simp only at this
      field_simp at this
      nlinarith [Real.pi_pos]
    exact_mod_cast this
  have hset : {t : ℝ | t ∈ Set.Ioo (0 : ℝ) 1 ∧
      (ψ n (G p q k t) = ψ n p ∨ ψ n (G p q k t) = -ψ n p)} =
      (((Finset.Icc 1 k).image (fun j : ℕ => (j : ℝ) * Real.pi / L) : Finset ℝ) : Set ℝ) := by
    ext t
    simp only [mem_ofPred_eq, Finset.coe_image, Finset.coe_Icc, mem_image, mem_Icc, hψ]
    rw [greatCircle_eq_pm_iff (u := ψ n p) (v := dir p q k) (norm_dir h1 h2 k)
      (inner_dir h1 h2 k)]
    constructor
    · rintro ⟨ht, hs⟩
      obtain ⟨j, hj⟩ := (sin_eq_zero_iff_nat hL ht.1).1 hs
      have hj0 : (0 : ℝ) < j := by
        have : 0 < (j : ℝ) * Real.pi := by rw [← hj]; exact mul_pos hL ht.1
        exact pos_of_mul_pos_left this Real.pi_pos.le
      have hjk : (j : ℝ) < k + 1 := by
        have : (j : ℝ) * Real.pi < (k + 1) * Real.pi := by rw [← hj]; nlinarith [ht.2]
        exact lt_of_mul_lt_mul_right this Real.pi_pos.le
      refine ⟨j, ⟨?_, ?_⟩, ?_⟩
      · exact_mod_cast hj0
      · have : j < k + 1 := by exact_mod_cast hjk
        omega
      · rw [← hj]; field_simp
    · rintro ⟨j, ⟨hj1, hjk⟩, rfl⟩
      have hj1' : (1 : ℝ) ≤ j := by exact_mod_cast hj1
      have hjk' : (j : ℝ) ≤ k := by exact_mod_cast hjk
      refine ⟨⟨div_pos (mul_pos (by linarith) Real.pi_pos) hL, ?_⟩, ?_⟩
      · rw [div_lt_one hL]
        nlinarith [Real.pi_pos]
      · rw [show L * ((j : ℝ) * Real.pi / L) = j * Real.pi by field_simp]
        exact Real.sin_nat_mul_pi j
  rw [hset, Set.ncard_coe_finset, Finset.card_image_of_injective _ hinj, Nat.card_Icc,
    Nat.add_sub_cancel]

theorem conjMultiplicity_congr {c c' : ℝ → EuclideanSpace ℝ (Fin (n + 1))} (h : c = c')
    (hc : Morse.IsSmoothCurveIn (sphSub n) c) (hc' : Morse.IsSmoothCurveIn (sphSub n) c') (a b : ℝ) :
    Morse.conjMultiplicity (sphSub n) c hc a b = Morse.conjMultiplicity (sphSub n) c' hc' a b := by
  subst h; rfl

theorem conj_G (hA : A) (hn : 2 ≤ n) (h1 : ψ n q ≠ ψ n p) (h2 : ψ n q ≠ -ψ n p) (k : ℕ) {t : ℝ}
    (ht : t ∈ Set.Ioo (0 : ℝ) 1) (hpt : ψ n (G p q k t) = ψ n p ∨ ψ n (G p q k t) = -ψ n p) :
    IsConj (Bridge.conn (hN := sphSub n)) (G p q k) 0 t ∧
      conjMult (Bridge.conn (hN := sphSub n)) (G p q k) 0 t = ((n - 1 : ℕ) : ℕ∞) := by
  have hL : 0 < Morse.sphLen (ψ n p) (ψ n q) k := sphLen_pos' hA h1 h2 k
  have hgeo := (isGeodPQ_G h1 h2 k).1
  have hsm : IsSmoothCurve (n := n) (G p q k) (Icc 0 1) := hgeo.2.1
  have hI0 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have hIt : t ∈ Icc (0 : ℝ) 1 := ⟨ht.1.le, ht.2.le⟩
  have hu := norm_dir h1 h2 k
  have hpu := inner_dir h1 h2 k
  have hj : ∃ j : ℕ, Morse.sphLen (ψ n p) (ψ n q) k * t = j * Real.pi := by
    have e : ψ n (G p q k t) =
        Morse.greatCircle (ψ n p) (dir p q k) (Morse.sphLen (ψ n p) (ψ n q) k) t :=
      congrFun (incl_G h1 h2 k) t
    rw [e] at hpt
    exact (sin_eq_zero_iff_nat hL ht.1).1 ((greatCircle_eq_pm_iff hu hpu _ t).1 hpt)
  have hgc : Morse.IsSmoothCurveIn (sphSub n)
      (Morse.greatCircle (ψ n p) (dir p q k) (Morse.sphLen (ψ n p) (ψ n q) k)) :=
    Morse.isSmoothCurveIn_greatCircle (mem_p p) hu hpu _
  have hmult : Morse.conjMultiplicity (sphSub n) (Bridge.incl (sphSub n) ∘ G p q k)
      (Emb.isSmoothCurveIn hsm) 0 t = n - 1 := by
    rw [conjMultiplicity_congr ((incl_G h1 h2 k).trans (sphGeod_eq k)) _ hgc,
      Morse.conjMultiplicity_greatCircle (by omega) (mem_p p) hu hpu hL hgc ⟨ht.1, ht.2.le⟩, if_pos hj]
  refine ⟨(Emb.isConj_iff hsm hI0 hIt).2 ?_, ?_⟩
  · exact (Morse.isConjugate_iff (Emb.isSmoothCurveIn hsm)).2
      ⟨hI0, hIt, (ne_of_lt ht.1), by rw [hmult]; omega⟩
  · rw [Emb.conjMult_eq hsm hI0 hIt, hmult]

theorem clauses_G (hA : A) (hn : 2 ≤ n) (h1 : ψ n q ≠ ψ n p) (h2 : ψ n q ≠ -ψ n p) :
    ClausesNoLam n p q (G p q) :=
  ⟨isGeodPQ_G h1 h2, fun _ _ h => G_inj hA h1 h2 h, fun _ hg => exists_G hA (by omega) h1 h2 hg,
    arcLen_G hA h1 h2, ncard_G hA h1 h2, fun k _ ht hpt => conj_G hA hn h1 h2 k ht hpt⟩

theorem lam_G (hA : A) (hn : 1 ≤ n) (hlam : LamEq n) (h1 : ψ n q ≠ ψ n p) (h2 : ψ n q ≠ -ψ n p)
    (k : ℕ) : lam (n := n) 1 (G p q k) = ((k * (n - 1) : ℕ) : ℕ∞) := by
  have hg := isGeodPQ_G h1 h2 k
  obtain ⟨hmem, hunb⟩ := Emb.mem_pathSpace_of_isGeodesic hg.1 hg.2.1 hg.2.2
  rw [hlam p q (G p q k) hmem hg]
  exact hA.2.2.2.2.2 (mem_p p) (mem_p q) h1 h2 hn hmem hunb (fun t _ => congrFun (incl_G h1 h2 k) t)

end Corr

/-- B on the embedded round sphere (`n ≥ 1` as in B; `ψ` the inclusion, induced connection). -/
def B_emb : Prop := ∀ n : ℕ, 1 ≤ n → BcorrEmbAt n

theorem B_to_B_emb : B → B_emb := fun hB n hn p q h1 h2 => by
  haveI := Sph.connectedSpace n hn
  obtain ⟨γ, c1, c2, c3, c4, c5, c6, c7⟩ :=
    hB n (Sph.S n) (Bridge.conn (hN := Milnor.Sphere.sphSub n)) Bridge.conn_isLC hn (Sph.ψ n)
      (Sph.isRoundSphere n) p q h1 h2
  exact ⟨γ, ⟨c1, c2, c3, c4, c5, c6⟩, c7⟩

open Sph Milnor.Sphere in
/-- **`B_emb` is false** (at `n = 1`): the same counter-model as `not_B`. -/
theorem not_B_emb : ¬ B_emb := by
  intro h
  let p₀ : S 1 := (⟨EuclideanSpace.single 0 1, single_mem 0⟩ : Sph 1)
  let q₀ : S 1 := (⟨EuclideanSpace.single 1 1, single_mem 1⟩ : Sph 1)
  have e10 : ψ 1 q₀ ≠ ψ 1 p₀ := by
    intro h
    have := congrArg (fun x : EuclideanSpace ℝ (Fin 2) => x 1) h
    simp [p₀, q₀, Sph.ψ, Bridge.incl] at this
  have e11 : ψ 1 q₀ ≠ -ψ 1 p₀ := by
    intro h
    have := congrArg (fun x : EuclideanSpace ℝ (Fin 2) => x 1) h
    simp [p₀, q₀, Sph.ψ, Bridge.incl] at this
  obtain ⟨γ, ⟨hgeo, -, -, -, hcard, hconj⟩, -⟩ := h 1 le_rfl p₀ q₀ e10 e11
  obtain ⟨t, ht, hpt⟩ := Set.nonempty_of_ncard_ne_zero (by rw [hcard 1]; exact one_ne_zero)
  exact not_isConj_S1 e10 (hgeo 1) ⟨ht.1, ht.2.le⟩ (hconj 1 t ht hpt).1

/-- A holds and B is false, so `A → B` is false. -/
theorem not_A_to_B : ¬ (A → B) := fun h => not_B (h A_holds)

/-- **A gives the corrected B on the embedded sphere, except the index clause.** -/
theorem A_to_Bcorr_emb_noLam : A → Bcorr_emb_noLam := fun hA _ hn _ _ h1 h2 =>
  ⟨_, clauses_G hA hn h1 h2⟩

/-- **A gives the corrected B on the embedded sphere, given the bridge `LamEq`** (B's variational
index = the project's `formIndex energyHessian` for blind geodesics of `Sⁿ`). -/
theorem A_to_BcorrEmbAt_of_lamEq (hA : A) (n : ℕ) (hn : 2 ≤ n) (hlam : LamEq n) : BcorrEmbAt n :=
  fun _ _ h1 h2 => ⟨_, clauses_G hA hn h1 h2, lam_G hA (by omega) hlam h1 h2⟩

#rt_check RoundTrip.V10_23.A_to_Bcorr_emb_noLam [Morse.mul_pi_lt_sphLen, Morse.energy_sphGeod, Morse.exists_eqOn_sphGeod, Morse.notMem_conjLocus_sph, Morse.formIndex_sphGeod, Morse.formIndex_eq_of_eqOn_sphGeod]
#rt_overlap RoundTrip.V10_23.B_to_A [Morse.mul_pi_lt_sphLen, Morse.energy_sphGeod, Morse.exists_eqOn_sphGeod, Morse.notMem_conjLocus_sph, Morse.formIndex_sphGeod, Morse.formIndex_eq_of_eqOn_sphGeod]
#rt_overlap RoundTrip.V10_23.A_to_Bcorr_emb_noLam [Morse.mul_pi_lt_sphLen, Morse.energy_sphGeod, Morse.exists_eqOn_sphGeod, Morse.notMem_conjLocus_sph, Morse.formIndex_sphGeod, Morse.formIndex_eq_of_eqOn_sphGeod]
#rt_check RoundTrip.V10_23.A_to_BcorrEmbAt_of_lamEq [Morse.mul_pi_lt_sphLen, Morse.energy_sphGeod, Morse.exists_eqOn_sphGeod, Morse.notMem_conjLocus_sph, Morse.formIndex_sphGeod, Morse.formIndex_eq_of_eqOn_sphGeod]

namespace LamPf

/-! ### `λ = indexUpTo` on `↥N` (copied from `Items/V9_23.lean`, namespace `Emb` there; the blind
vocabulary of this item's blind file is textually the same as V9_23's) -/

open Set Filter Topology Function
open scoped ContDiff Manifold
open Bundle

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-- `e₀, e₁ ∈ ℝ²`. -/
noncomputable abbrev e0 : Rn 2 := EuclideanSpace.single 0 (1 : ℝ)
noncomputable abbrev e1 : Rn 2 := EuclideanSpace.single 1 (1 : ℝ)

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W] {n : ℕ} {N : Set V}
  {hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) (Rn n) W N}

/-! ### Maps into `↥N` (copied from `Items/V8_10.lean`, `Items/V8_12.lean`) -/

theorem contMDiffWithinAt_map_iff {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → Bridge.Sub hN} {s : Set E} {x : E} :
    ContMDiffWithinAt 𝓘(ℝ, E) 𝓘(ℝ, Rn n) ∞ f s x ↔
      ContDiffWithinAt ℝ ∞ (Bridge.incl hN ∘ f) s x := by
  constructor
  · intro h
    exact contMDiffWithinAt_iff_contDiffWithinAt.1
      ((Bridge.contMDiff_incl (f x)).comp_contMDiffWithinAt x h)
  · intro h
    have hcont : ContinuousWithinAt f s x :=
      (Topology.IsInducing.subtypeVal.continuousWithinAt_iff (f := f)).2 h.continuousWithinAt
    rw [contMDiffWithinAt_iff_target]
    refine ⟨hcont, ?_⟩
    set sl := Morse.sliceAt hN (f x)
    have hφ : ContDiffAt ℝ ∞ (fun y => (sl.φ y).1) (Bridge.incl hN (f x)) :=
      contDiff_fst.contDiffAt.comp _ ((Milnor.Problems.sliceChart_contDiffOn sl).contDiffAt
        (sl.φ.open_source.mem_nhds (Morse.mem_sliceAt_source hN (f x))))
    have e : (extChartAt 𝓘(ℝ, Rn n) (f x) ∘ f) =
        (fun y => (sl.φ y).1) ∘ (Bridge.incl hN ∘ f) := rfl
    rw [e]
    exact contMDiffWithinAt_iff_contDiffWithinAt.2 (hφ.comp_contDiffWithinAt x h)

theorem contMDiffOn_map_iff {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → Bridge.Sub hN} {s : Set E} :
    ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, Rn n) ∞ f s ↔ ContDiffOn ℝ ∞ (Bridge.incl hN ∘ f) s :=
  forall₂_congr fun _ _ => contMDiffWithinAt_map_iff

/-- The derivative of a map from a normed space into `N`, read in `V`. -/
theorem D_mfderiv_map {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : E → Bridge.Sub hN}
    {x : E} (hf : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, Rn n) f x) (v : E) :
    Bridge.D hN (f x) (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, Rn n) f x v) = fderiv ℝ (Bridge.incl hN ∘ f) x v := by
  have h := HasMFDerivAt.comp x
    ((Bridge.contMDiff_incl (f x)).mdifferentiableAt (by simp)).hasMFDerivAt hf.hasMFDerivAt
  have h' : HasFDerivAt (Bridge.incl hN ∘ f)
      ((Bridge.D hN (f x)).comp (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, Rn n) f x : E →L[ℝ] Rn n)) x :=
    hasMFDerivAt_iff_hasFDerivAt.1 h
  have h'' : fderiv ℝ (Bridge.incl hN ∘ f) x =
      (Bridge.D hN (f x)).comp (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, Rn n) f x : E →L[ℝ] Rn n) :=
    HasFDerivAt.fderiv h'
  exact (DFunLike.congr_fun h'' v).symm

/-- A map into `N` that is `C^∞` at `x` when read in `V` has its derivative read in `V`. -/
theorem D_mfderiv_of_contDiffAt {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → Bridge.Sub hN} {x : E} (hf : ContDiffAt ℝ ∞ (Bridge.incl hN ∘ f) x) (v : E) :
    Bridge.D hN (f x) (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, Rn n) f x v) = fderiv ℝ (Bridge.incl hN ∘ f) x v := by
  have : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, Rn n) ∞ f x := by
    rw [← contMDiffWithinAt_univ]
    exact contMDiffWithinAt_map_iff.2 (contDiffWithinAt_univ.2 hf)
  exact D_mfderiv_map (this.mdifferentiableAt (by simp)) v

/-! ### Paths, geodesics and `TΩ` -/

/-- A blind geodesic on `[0, 1]` (induced connection) is a project unbroken geodesic. -/
theorem isUnbrokenGeodesic_of_isGeodesic {pw : ℝ → Bridge.Sub hN}
    (h : IsGeodesic (Bridge.conn (hN := hN)) pw (Icc 0 1)) :
    Morse.IsUnbrokenGeodesic hN (Bridge.incl hN ∘ pw) := by
  have h' : RoundTrip.BridgePrelude.IsGeodesic (Bridge.conn (hN := hN)) pw (Icc 0 1) := h
  exact ⟨(Bridge.isGeodesic_iff.1 h').2.1, Bridge.isGeodesicOn_Ioo h'⟩

theorem mem_pathSpace_of_isGeodesic {pw : ℝ → Bridge.Sub hN}
    (h : IsGeodesic (Bridge.conn (hN := hN)) pw (Icc 0 1)) :
    Bridge.incl hN ∘ pw ∈ Morse.pathSpace N (Bridge.incl hN (pw 0)) (Bridge.incl hN (pw 1)) := by
  have hcd := (isUnbrokenGeodesic_of_isGeodesic h).1
  exact ⟨⟨zero_le_one, hcd.continuousOn, ∅, fun s u hs _ hu _ => hcd.mono (Icc_subset_Icc hs hu)⟩,
    fun t _ => (pw t).2, rfl, rfl⟩
/-! ### 2-parameter variations -/

/-- The ambient family `(u, s) ↦ α(u, s) ∈ N ⊆ V`. -/
def amb {m : ℕ} (α : Rn m → ℝ → Bridge.Sub hN) : Rn m → ℝ → V := fun u s => Bridge.incl hN (α u s)

/-- Theorem 13.1 for `N` (the statement of `Morse.second_variation`, or of
`Morse.hasDerivAt_energyHessian` unfolded), taken as a hypothesis. -/
def SV (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) (Rn n) W N) : Prop :=
  ∀ {γ : ℝ → V} {p q : V}, γ ∈ Morse.pathSpace N p q → Morse.IsUnbrokenGeodesic hN γ →
    ∀ {U : Set (ℝ × ℝ)} {α : ℝ × ℝ → ℝ → V} {B : Finset ℝ}, Morse.IsVariation N U α B →
    (∀ t ∈ Icc (0 : ℝ) 1, α 0 t = γ t) →
    HasDerivAt (fun u₁ => deriv (fun u₂ => Morse.energy (α (u₁, u₂)) 0 1) 0)
      (2 * Morse.secondVariation hN γ (fun t => deriv (fun u₁ => α (u₁, 0) t) 0)
        (fun t => deriv (fun u₂ => α (0, u₂) t) 0)) 0

/-! ### Existence of `IsHess` values (Lemma 11.A on `↥N`, fields matched on all of `ℝ`) -/

/-- Near the zero section `exp` is smooth with `d(exp_q)₀ = id` (from `Morse.exists_isOpen_exp`
and `Morse.hasFDerivAt_exp_zero`), along any linear map into `T_qN`. -/
theorem exp_local {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] {q : V} (hq : q ∈ N)
    (Λ : P →L[ℝ] V) (hΛ : ∀ u, Morse.prj hN q (Λ u) = Λ u) :
    (∀ᶠ u in 𝓝 (0 : P), Morse.exp hN q (Λ u) ∈ N) ∧
    ContDiffAt ℝ ∞ (fun u => Morse.exp hN q (Λ u)) 0 ∧
    HasFDerivAt (fun u => Morse.exp hN q (Λ u)) Λ 0 := by
  obtain ⟨O, hO, hO0, hexp⟩ := Morse.exists_isOpen_exp (hN := hN)
  have hTN : ∀ u, (q, Λ u) ∈ Milnor.Problems.tangentBundleSet hN :=
    fun u => ⟨hq, (Morse.prj_eq_self_iff hN hq).1 (hΛ u)⟩
  have hc : Continuous (fun u : P => (q, Λ u)) := continuous_const.prodMk Λ.continuous
  have hq0 : (q, Λ 0) ∈ O := by rw [map_zero]; exact hO0 q hq
  have hev : ∀ᶠ u in 𝓝 (0 : P), (q, Λ u) ∈ O :=
    hc.continuousAt.preimage_mem_nhds (hO.mem_nhds hq0)
  refine ⟨?_, ?_, ?_⟩
  · filter_upwards [hev] with u hu
    exact Morse.exp_mem_of_mem_expDom (hexp _ hu (hTN u)).1
  · obtain ⟨-, F, O', hO', hzO', hF, hFeq⟩ := hexp _ hq0 (hTN 0)
    have h1 : ContDiffAt ℝ ∞ (fun u => F (q, Λ u)) 0 :=
      (hF.contDiffAt (hO'.mem_nhds hzO')).comp (0 : P)
        (contDiff_const.prodMk Λ.contDiff).contDiffAt
    refine h1.congr_of_eventuallyEq ?_
    filter_upwards [hc.continuousAt.preimage_mem_nhds (hO'.mem_nhds hzO')] with u hu
    exact hFeq _ hu (hTN u)
  · set qt : N := ⟨q, hq⟩
    let L : P →L[ℝ] Morse.tangentSubspace hN qt :=
      Λ.codRestrict (Morse.tangentSubspace hN qt) fun u =>
        (Morse.prj_eq_self_iff hN hq).1 (hΛ u)
    have h1 := Morse.hasFDerivAt_exp_zero (hN := hN) qt
    rw [← map_zero L] at h1
    have h2 := h1.comp (0 : P) L.hasFDerivAt
    have hL : ((Morse.tangentSubspace hN qt).subtypeL.comp L) = Λ :=
      ContinuousLinearMap.ext fun u => rfl
    rw [hL] at h2
    exact h2

open Classical in
/-- Milnor's `α(u, t) = exp_{γ(t)}(Λ(t) u)`, as a map into `↥N` (junk `γ t` where `exp` leaves
`N`, which does not happen near `u = 0`). -/
noncomputable def liftE (γ : ℝ → Bridge.Sub hN) (Λ : ℝ → Rn 2 →L[ℝ] V) (u : Rn 2) (t : ℝ) :
    Bridge.Sub hN :=
  if h : Morse.exp hN (Bridge.incl hN (γ t)) (Λ t u) ∈ N then (⟨_, h⟩ : N) else γ t

theorem liftE_of_mem {γ : ℝ → Bridge.Sub hN} {Λ : ℝ → Rn 2 →L[ℝ] V} {u : Rn 2} {t : ℝ}
    (h : Morse.exp hN (Bridge.incl hN (γ t)) (Λ t u) ∈ N) :
    liftE γ Λ u t = (⟨_, h⟩ : N) := by
  unfold liftE; exact dif_pos h

theorem incl_liftE {γ : ℝ → Bridge.Sub hN} {Λ : ℝ → Rn 2 →L[ℝ] V} {u : Rn 2} {t : ℝ}
    (h : Morse.exp hN (Bridge.incl hN (γ t)) (Λ t u) ∈ N) :
    Bridge.incl hN (liftE γ Λ u t) = Morse.exp hN (Bridge.incl hN (γ t)) (Λ t u) := by
  rw [liftE_of_mem h]; rfl

open RoundTrip.Bridge

theorem isSmoothCurveIn {γ : ℝ → Bridge.Sub hN} (hγ : IsSmoothCurve (n := n) γ (Icc 0 1)) :
    Morse.IsSmoothCurveIn hN (incl hN ∘ γ) :=
  ⟨isSmoothCurve_iff.1 hγ, fun t _ => (γ t).2⟩

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


/-- On fields tangent along `γ` on `[0,1]` and constant off `[0,1]`, `toFA` is injective. -/
theorem toFA_injOn {γ : ℝ → Bridge.Sub hN} {X Y : ℝ → V}
    (hX : ∀ t ∈ Icc (0 : ℝ) 1, Morse.prj hN ((incl hN ∘ γ) t) (X t) = X t)
    (hY : ∀ t ∈ Icc (0 : ℝ) 1, Morse.prj hN ((incl hN ∘ γ) t) (Y t) = Y t)
    (h : toFA γ X = toFA γ Y) : EqOn X Y (Icc 0 1) := fun t ht => by
  rw [← ambA_toFA hX ht, ← ambA_toFA hY ht, h]

/-- Theorem 13.1 (`Morse.second_variation`, not a theorem of this item) in the form `SV`. -/
theorem sv_holds : SV hN := by
  intro _ _ _ _ hub _ _ _ hβ hβγ
  exact Morse.second_variation hN hub hβ hβγ


/-- Continuity on `[0, t_k]` from continuity on the closed pieces of a subdivision. -/
theorem continuousOn_of_pieces {β : Type*} [TopologicalSpace β] {f : ℝ → β} {t : ℕ → ℝ}
    (ht0 : t 0 = 0) : ∀ {k : ℕ}, (∀ i < k, t i < t (i + 1)) →
    (∀ i < k, ContinuousOn f (Icc (t i) (t (i + 1)))) → ContinuousOn f (Icc 0 (t k))
  | 0, _, _ => by rw [ht0, Icc_self]; exact continuousOn_singleton f 0
  | k + 1, hlt, h => by
    have hlt' : ∀ i < k, t i < t (i + 1) := fun i hi => hlt i (by omega)
    have h0k : 0 ≤ t k := ht0 ▸ Bridge.le_of_strictSeq hlt' (Nat.zero_le k) le_rfl
    rw [← Icc_union_Icc_eq_Icc h0k (hlt k (by omega)).le]
    exact (continuousOn_of_pieces ht0 hlt' fun i hi => h i (by omega)).union_of_isClosed
      (h k (by omega)) isClosed_Icc isClosed_Icc

/-! #### Subdivisions of `[0, τ]` -/

theorem exists_piece_of_memT {τ : ℝ} (hτ : 0 < τ) {k : ℕ} {t : ℕ → ℝ} (h0 : t 0 = 0)
    (hk : t k = τ) (hlt : ∀ i < k, t i < t (i + 1)) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) τ) :
    ∃ i < k, s ∈ Icc (t i) (t (i + 1)) := by
  classical
  have hk0 : k ≠ 0 := by rintro rfl; rw [h0] at hk; exact hτ.ne hk
  have hP : ∃ j, s ≤ t j ∧ j ≤ k := ⟨k, hk ▸ hs.2, le_rfl⟩
  have hm := Nat.find_spec hP
  by_cases hm0 : Nat.find hP = 0
  · refine ⟨0, Nat.pos_of_ne_zero hk0, ?_, ?_⟩
    · rw [h0]; exact hs.1
    · have : s ≤ t 0 := by rw [← hm0]; exact hm.1
      exact this.trans (hlt 0 (Nat.pos_of_ne_zero hk0)).le
  · refine ⟨Nat.find hP - 1, by omega, ?_, ?_⟩
    · by_contra hcon
      exact Nat.find_min hP (Nat.sub_lt (Nat.pos_of_ne_zero hm0) one_pos)
        ⟨(lt_of_not_ge hcon).le, by omega⟩
    · rw [Nat.sub_add_cancel (Nat.pos_of_ne_zero hm0)]; exact hm.1

theorem exists_piece_of_subdivT {τ : ℝ} {t : ℕ → ℝ} {k : ℕ} (h0 : t 0 = 0) (hk : t k = τ)
    (hlt : ∀ i < k, t i < t (i + 1)) {s u : ℝ} (hs : 0 ≤ s) (hsu : s < u) (hub : u ≤ τ)
    (hB : ∀ x ∈ (Finset.range (k + 1)).image t, x ∉ Ioo s u) :
    ∃ i < k, t i ≤ s ∧ u ≤ t (i + 1) := by
  have hP : ∃ j, s < t j ∧ j ≤ k := ⟨k, by rw [hk]; linarith, le_rfl⟩
  classical
  set m := Nat.find hP
  have hm : s < t m ∧ m ≤ k := Nat.find_spec hP
  have hm0 : m ≠ 0 := by
    intro h; have := hm.1; rw [h, h0] at this; linarith
  have hi : t (m - 1) ≤ s := by
    by_contra hcon
    exact Nat.find_min hP (Nat.sub_lt (Nat.pos_of_ne_zero hm0) one_pos)
      ⟨lt_of_not_ge hcon, by omega⟩
  have hu : u ≤ t m := by
    by_contra hcon
    exact hB (t m) (Finset.mem_image.2 ⟨m, Finset.mem_range.2 (by omega), rfl⟩)
      ⟨hm.1, lt_of_not_ge hcon⟩
  have hm1 : m - 1 + 1 = m := Nat.sub_add_cancel (Nat.pos_of_ne_zero hm0)
  exact ⟨m - 1, by omega, hi, hm1.symm ▸ hu⟩

/-- A subdivision `0 = t₀ < ⋯ < t_k = τ` whose open pieces avoid a finite set `B`. -/
theorem exists_subdivT {τ : ℝ} (hτ : 0 < τ) (B : Finset ℝ) : ∃ (k : ℕ) (t : ℕ → ℝ), t 0 = 0 ∧
    t k = τ ∧ (∀ i < k, t i < t (i + 1)) ∧
    ∀ i < k, 0 ≤ t i ∧ t (i + 1) ≤ τ ∧ ∀ x ∈ B, x ∉ Ioo (t i) (t (i + 1)) := by
  classical
  have hlt : (0 : ℝ) < τ := hτ
  set a : ℝ := 0
  set b : ℝ := τ
  set S : Finset ℝ := insert a (insert b (B.filter (· ∈ Ioo a b)))
  have hS : ∀ x ∈ S, a ≤ x ∧ x ≤ b := by
    intro x hx
    simp only [S, Finset.mem_insert, Finset.mem_filter] at hx
    rcases hx with rfl | rfl | ⟨-, hx⟩
    · exact ⟨le_rfl, hlt.le⟩
    · exact ⟨hlt.le, le_rfl⟩
    · exact ⟨hx.1.le, hx.2.le⟩
  have haS : a ∈ S := Finset.mem_insert_self _ _
  have hbS : b ∈ S := Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
  set m := S.card
  have hm : 1 < m := Finset.one_lt_card.2 ⟨a, haS, b, hbS, hlt.ne⟩
  set e := S.orderEmbOfFin rfl
  set t : ℕ → ℝ := fun j => if h : j < m then e ⟨j, h⟩ else b
  have ht : ∀ j (h : j < m), t j = e ⟨j, h⟩ := fun j h => dif_pos h
  refine ⟨m - 1, t, ?_, ?_, ?_, ?_⟩
  · rw [ht 0 (by omega), Finset.orderEmbOfFin_zero rfl (by omega)]
    exact le_antisymm (Finset.min'_le _ _ haS) ((hS _ (Finset.min'_mem _ _)).1)
  · rw [ht (m - 1) (by omega), Finset.orderEmbOfFin_last rfl (by omega)]
    exact le_antisymm ((hS _ (Finset.max'_mem _ _)).2) (Finset.le_max' _ _ hbS)
  · intro i hi
    rw [ht i (by omega), ht (i + 1) (by omega)]
    exact e.strictMono (Fin.mk_lt_mk.2 (Nat.lt_succ_self i))
  · intro i hi
    rw [ht i (by omega), ht (i + 1) (by omega)]
    refine ⟨(hS _ (Finset.orderEmbOfFin_mem _ _ _)).1, (hS _ (Finset.orderEmbOfFin_mem _ _ _)).2,
      fun x hx hxi => ?_⟩
    have hxS : x ∈ S := Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
      (Finset.mem_filter.2 ⟨hx, (hS _ (Finset.orderEmbOfFin_mem _ _ _)).1.trans_lt hxi.1,
        hxi.2.trans_le (hS _ (Finset.orderEmbOfFin_mem _ _ _)).2⟩))
    obtain ⟨j, rfl⟩ : x ∈ Set.range e := by
      rw [Finset.range_orderEmbOfFin]; exact hxS
    have h1 := e.lt_iff_lt.1 hxi.1
    have h2 := e.lt_iff_lt.1 hxi.2
    rw [Fin.lt_def] at h1 h2
    simp only at h1 h2
    omega

/-! #### `TΩ(γ|[0, τ])`: blind `TOm τ` vs the project's `fieldsUpTo τ` -/

/-- **Blind ⇒ project**: the ambient field of a blind `W ∈ TΩ(γ|[0,τ])` lies in the project's
`TΩ_γ` and vanishes outside `[0, τ]`. -/
theorem mem_pathTangent_of_inTOmegaT {τ : ℝ} (hτ1 : τ ≤ 1) {γ : ℝ → Bridge.Sub hN}
    {X : FA n γ} (h : InTOmegaT (n := n) τ γ X) :
    Bridge.ambA γ X ∈ Morse.pathTangent hN (Bridge.incl hN ∘ γ) ∧
      ∀ t, t ∉ Icc (0 : ℝ) τ → Bridge.ambA γ X t = 0 := by
  obtain ⟨⟨k, t, ht0, htk, hlt, -, hsm⟩, hX0, hXτ, hout⟩ := h
  have hzero : ∀ s, τ ≤ s → Bridge.ambA γ X s = 0 := by
    intro s hs
    rcases eq_or_lt_of_le hs with rfl | hs'
    · show Bridge.D hN (γ τ) (X τ) = 0
      rw [hXτ]; exact map_zero _
    · show Bridge.D hN (γ s) (X s) = 0
      rw [hout s fun h => absurd h.2 (not_le.2 hs')]; exact map_zero _
  have hsm' : ∀ i < k, ContDiffOn ℝ ∞ (Bridge.ambA γ X) (Icc (t i) (t (i + 1))) := fun i hi => by
    have h' : RoundTrip.BridgePrelude.IsSmoothAlong γ (Icc (t i) (t (i + 1))) X := hsm i hi
    exact (Bridge.isSmoothAlong_iff.1 h').2
  have hpiece : ∀ s u, 0 ≤ s → s < u → u ≤ 1 →
      (∀ x ∈ insert τ ((Finset.range (k + 1)).image t), x ∉ Ioo s u) →
      ContDiffOn ℝ ∞ (Bridge.ambA γ X) (Icc s u) := by
    intro s u hs hsu hu hB
    by_cases huτ : u ≤ τ
    · obtain ⟨i, hi, hti, hui⟩ := exists_piece_of_subdivT ht0 htk hlt hs hsu huτ
        fun x hx => hB x (Finset.mem_insert_of_mem hx)
      exact (hsm' i hi).mono (Icc_subset_Icc hti hui)
    · have hτs : τ ≤ s := by
        by_contra h
        exact hB τ (Finset.mem_insert_self _ _) ⟨lt_of_not_ge h, lt_of_not_ge huτ⟩
      exact contDiffOn_const.congr fun x hx => hzero x (hτs.trans hx.1)
  refine ⟨(Morse.mem_pathTangent hN).2 ⟨⟨zero_le_one, Morse.continuousOn_of_piecewise
    fun s u hs hsu hu hB => (hpiece s u hs hsu hu hB).continuousOn, _, hpiece⟩,
    fun τ' _ => (Morse.prj_eq_self_iff hN (γ τ').2).2 (Bridge.D_mem (γ τ') (X τ')), ?_, ?_⟩, ?_⟩
  · show Bridge.D hN (γ 0) (X 0) = 0
    rw [hX0]; exact map_zero _
  · exact hzero 1 hτ1
  · intro s hs
    show Bridge.D hN (γ s) (X s) = 0
    rw [hout s hs]; exact map_zero _

/-- **Project ⇒ blind**: a project field in `TΩ_γ` vanishing outside `[0, τ]` gives a blind field
`toFA γ X ∈ TΩ(γ|[0,τ])`. -/
theorem inTOmegaT_toFA_T {τ : ℝ} (hτ : 0 < τ) (hτ1 : τ ≤ 1) {γ : ℝ → Bridge.Sub hN}
    (hγ : IsSmoothCurve (n := n) γ (Icc 0 1)) {X : ℝ → V}
    (hX : X ∈ Morse.pathTangent hN (Bridge.incl hN ∘ γ))
    (hXτ : ∀ t, t ∉ Icc (0 : ℝ) τ → X t = 0) :
    InTOmegaT (n := n) τ γ (toFA γ X) := by
  obtain ⟨⟨-, -, B, hB⟩, hT, hX0, -⟩ := (Morse.mem_pathTangent hN).1 hX
  have hmem : (⟨X, hX⟩ : Morse.pathTangent hN (Bridge.incl hN ∘ γ)) ∈
      Morse.fieldsUpTo hN (Bridge.incl hN ∘ γ) τ := hXτ
  have hXτ0 : X τ = 0 := Morse.fieldsUpTo_apply_self hτ.le hτ1 hmem
  obtain ⟨k, t, ht0, htk, hlt, hgood⟩ := exists_subdivT hτ B
  have hsm : ∀ i < k, IsSmoothAlong γ (Icc (t i) (t (i + 1))) (toFA γ X) := by
    intro i hi
    obtain ⟨h0i, hi1, hBi⟩ := hgood i hi
    have hsub : Icc (t i) (t (i + 1)) ⊆ Icc 0 1 := Icc_subset_Icc h0i (hi1.trans hτ1)
    exact Bridge.isSmoothAlong_iff.2 ⟨ContMDiffOn.mono hγ hsub,
      (hB _ _ h0i (hlt i hi) (hi1.trans hτ1) hBi).congr fun s hs => ambA_toFA hT (hsub hs)⟩
  refine ⟨⟨k, t, ht0, htk, hlt, ?_, hsm⟩, ?_, ?_, fun s hs => ?_⟩
  · rw [← htk]
    exact continuousOn_of_pieces ht0 hlt fun i hi => ContMDiffOn.continuousOn (hsm i hi)
  · rw [toFA_of_mem X ⟨le_rfl, zero_le_one⟩, hX0, map_zero]; rfl
  · rw [toFA_of_mem X ⟨hτ.le, hτ1⟩, hXτ0, map_zero]; rfl
  · by_cases hs1 : s ∈ Icc (0 : ℝ) 1
    · rw [toFA_of_mem X hs1, hXτ s hs, map_zero]; rfl
    · exact toFA_of_not_mem X hs1

/-! #### Variations of `γ|[0, τ]` -/

/-- The extension of a blind variation of `γ|[0, τ]` by `α 0` on `(τ, 1]`, read in `V`. -/
noncomputable def extA {m : ℕ} (τ : ℝ) (α : Rn m → ℝ → Bridge.Sub hN) : Rn m → ℝ → V :=
  fun u s => if s ≤ τ then Bridge.incl hN (α u s) else Bridge.incl hN (α 0 s)

theorem extA_zero {m : ℕ} (τ : ℝ) (α : Rn m → ℝ → Bridge.Sub hN) (s : ℝ) :
    extA τ α 0 s = Bridge.incl hN (α 0 s) := by
  unfold extA; split_ifs <;> rfl

/-- **The extension is a project variation** of `incl ∘ α 0` on `[0, 1]`. -/
theorem isVariation_extA {τ : ℝ} (hτ : 0 < τ) (hτ1 : τ ≤ 1) {m : ℕ} {U : Set (Rn m)}
    {α : Rn m → ℝ → Bridge.Sub hN} {k : ℕ} {t : ℕ → ℝ} (hα : IsVarSubT (n := n) τ U α k t)
    (hγ : ContDiffOn ℝ ∞ (Bridge.incl hN ∘ α 0) (Icc 0 1)) :
    Morse.IsVariation N U (extA τ α) (insert τ ((Finset.range (k + 1)).image t)) := by
  obtain ⟨hU, h0U, ht0, htk, hlt, hend, hsm⟩ := hα
  refine ⟨hU, h0U, fun u _ s _ => ?_, fun u hu => ?_, fun u hu => ?_,
    fun s u hs hsu hu hB => ?_⟩
  · unfold extA
    split_ifs
    · exact (α u s).2
    · exact (α 0 s).2
  · rw [extA_zero]
    unfold extA
    rw [if_pos hτ.le, (hend u hu).2.1]
  · rw [extA_zero]
    unfold extA
    split_ifs with h1
    · have : τ = 1 := le_antisymm hτ1 h1
      subst this
      rw [(hend u hu).2.2]
    · rfl
  · by_cases huτ : u ≤ τ
    · obtain ⟨i, hi, hti, hui⟩ := exists_piece_of_subdivT ht0 htk hlt hs hsu huτ
        fun x hx => hB x (Finset.mem_insert_of_mem hx)
      refine ((contMDiffOn_map_iff.1 (hsm i hi)).mono
        (prod_mono subset_rfl (Icc_subset_Icc hti hui))).congr fun p hp => ?_
      show extA τ α p.1 p.2 = Bridge.incl hN (α p.1 p.2)
      unfold extA
      rw [if_pos (hp.2.2.trans huτ)]
    · have hτs : τ ≤ s := by
        by_contra h
        exact hB τ (Finset.mem_insert_self _ _) ⟨lt_of_not_ge h, lt_of_not_ge huτ⟩
      have hg : ContDiffOn ℝ ∞ ((Bridge.incl hN ∘ α 0) ∘ Prod.snd) (U ×ˢ Icc s u) :=
        hγ.comp contDiff_snd.contDiffOn fun p hp => ⟨hs.trans hp.2.1, hp.2.2.trans hu⟩
      refine hg.congr fun p hp => ?_
      show extA τ α p.1 p.2 = Bridge.incl hN (α 0 p.2)
      unfold extA
      split_ifs with h
      · have hpτ : p.2 = τ := le_antisymm h (hτs.trans hp.2.1)
        rw [hpτ, (hend p.1 hp.1).2.2]
      · rfl

/-- `E_0^1` of the extension is `E_0^τ` of the blind path plus the constant `E_τ^1(γ)`. -/
theorem energy_extA {τ : ℝ} (hτ : 0 < τ) (hτ1 : τ ≤ 1) {m : ℕ} {U : Set (Rn m)}
    {α : Rn m → ℝ → Bridge.Sub hN} {B : Finset ℝ}
    (hvar : Morse.IsVariation N U (extA τ α) B) {v : Rn m} (hv : v ∈ U) :
    Morse.energy (extA τ α v) 0 1 =
      Morse.energy (Bridge.incl hN ∘ α v) 0 τ + Morse.energy (Bridge.incl hN ∘ α 0) τ 1 := by
  have hint := (hvar.isPiecewiseSmooth hv).intervalIntegrable_norm_deriv_sq
  have h1 : IntervalIntegrable (fun s => ‖deriv (extA τ α v) s‖ ^ 2) MeasureTheory.volume 0 τ :=
    hint.mono_set (by
      rw [uIcc_of_le hτ.le, uIcc_of_le zero_le_one]; exact Icc_subset_Icc le_rfl hτ1)
  have h2 : IntervalIntegrable (fun s => ‖deriv (extA τ α v) s‖ ^ 2) MeasureTheory.volume τ 1 :=
    hint.mono_set (by
      rw [uIcc_of_le hτ1, uIcc_of_le zero_le_one]; exact Icc_subset_Icc hτ.le le_rfl)
  unfold Morse.energy
  rw [← intervalIntegral.integral_add_adjacent_intervals h1 h2]
  congr 1
  · refine intervalIntegral.integral_congr_Ioo_of_le hτ.le fun s hs => ?_
    have : extA τ α v =ᶠ[𝓝 s] Bridge.incl hN ∘ α v := by
      filter_upwards [Iio_mem_nhds hs.2] with x hx
      unfold extA
      rw [if_pos (le_of_lt hx)]
      rfl
    simp only [this.deriv_eq]
  · refine intervalIntegral.integral_congr_Ioo_of_le hτ1 fun s hs => ?_
    have : extA τ α v =ᶠ[𝓝 s] Bridge.incl hN ∘ α 0 := by
      filter_upwards [Ioi_mem_nhds hs.1] with x hx
      unfold extA
      rw [if_neg (not_le.2 hx)]
      rfl
    simp only [this.deriv_eq]

/-- Variation fields of a blind variation of `γ|[0, τ]`, read in `V`, on `[0, τ]`. -/
theorem D_varFieldT {τ : ℝ} (hτ : 0 < τ) {m : ℕ} {U : Set (Rn m)}
    {α : Rn m → ℝ → Bridge.Sub hN} {k : ℕ} {t : ℕ → ℝ} (hα : IsVarSubT (n := n) τ U α k t)
    (i : Fin m) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) τ) :
    Bridge.D hN (α 0 s) (varField (n := n) α i s) =
      deriv (fun r : ℝ => amb α (r • EuclideanSpace.single i (1 : ℝ)) s) 0 := by
  obtain ⟨hU, h0U, ht0, htk, hlt, -, hsm⟩ := hα
  obtain ⟨j, hj, hsj⟩ := exists_piece_of_memT hτ ht0 htk hlt hs
  have hG : ContDiffOn ℝ ∞ (Bridge.incl hN ∘ fun x : Rn m × ℝ => α x.1 x.2)
      (U ×ˢ Icc (t j) (t (j + 1))) := contMDiffOn_map_iff.1 (hsm j hj)
  have hcd : ContDiffAt ℝ ∞ (Bridge.incl hN ∘ fun u => α u s) 0 :=
    (hG.comp (contDiff_id.prodMk contDiff_const).contDiffOn fun u hu => ⟨hu, hsj⟩).contDiffAt
      (hU.mem_nhds h0U)
  have h1 := D_mfderiv_of_contDiffAt hcd (EuclideanSpace.single i (1 : ℝ))
  have h2 := RoundTrip.EnergyC2.hasDerivAt_line (hcd.differentiableAt (by simp))
    (EuclideanSpace.single i (1 : ℝ))
  simp only [zero_add] at h2
  exact h1.trans h2.deriv.symm

/-- The variation fields of the extension: the blind ones on `[0, τ]`, `0` beyond. -/
theorem deriv_extA {τ : ℝ} (hτ : 0 < τ) {m : ℕ} {U : Set (Rn m)}
    {α : Rn m → ℝ → Bridge.Sub hN} {k : ℕ} {t : ℕ → ℝ} (hα : IsVarSubT (n := n) τ U α k t)
    (i : Fin m) {s : ℝ} (hs : 0 ≤ s) :
    deriv (fun r : ℝ => extA τ α (r • EuclideanSpace.single i (1 : ℝ)) s) 0 =
      if s ≤ τ then Bridge.ambA (α 0) (varField (n := n) α i) s else 0 := by
  split_ifs with h
  · have e : (fun r : ℝ => extA τ α (r • EuclideanSpace.single i (1 : ℝ)) s) =
        fun r : ℝ => amb α (r • EuclideanSpace.single i (1 : ℝ)) s := funext fun r => by
      unfold extA
      rw [if_pos h]
      rfl
    rw [e, ← D_varFieldT hτ hα i ⟨hs, h⟩]
    rfl
  · have e : (fun r : ℝ => extA τ α (r • EuclideanSpace.single i (1 : ℝ)) s) =
        fun _ : ℝ => Bridge.incl hN (α 0 s) := funext fun r => by
      unfold extA
      rw [if_neg h]
    rw [e, deriv_const]

/-- **`E_0^τ ∘ α` is `C²` and its blind `mixedD` is `2 secondVariation`** of the fields
(extended by `0` beyond `τ`), for every blind variation of `γ|[0, τ]`, `γ` a geodesic of `↥N`. -/
theorem hessT_data {τ : ℝ} (hτ : 0 < τ) (hτ1 : τ ≤ 1) {U : Set (Rn 2)}
    {α : Rn 2 → ℝ → Bridge.Sub hN} {k : ℕ} {t : ℕ → ℝ} (hα : IsVarSubT (n := n) τ U α k t)
    (hgeo : IsGeodesic (Bridge.conn (hN := hN)) (α 0) (Icc 0 1)) :
    DifferentiableAt ℝ
        (fun u : Rn 2 => fderiv ℝ (fun v : Rn 2 => energy (n := n) (α v) 0 τ) u e0) 0 ∧
      mixedD (fun v : Rn 2 => energy (n := n) (α v) 0 τ) =
        2 * Morse.secondVariation hN (Bridge.incl hN ∘ α 0)
          (fun s => if s ≤ τ then Bridge.ambA (α 0) (varField (n := n) α 0) s else 0)
          (fun s => if s ≤ τ then Bridge.ambA (α 0) (varField (n := n) α 1) s else 0) := by
  have hub := isUnbrokenGeodesic_of_isGeodesic hgeo
  have hvar := isVariation_extA hτ hτ1 hα hub.1
  have hU := hvar.isOpen
  have h0U := hvar.zero_mem
  have hFG : ∀ v ∈ U, energy (n := n) (α v) 0 τ =
      Morse.energy (extA τ α v) 0 1 - Morse.energy (Bridge.incl hN ∘ α 0) τ 1 := by
    intro v hv
    have h1 : energy (n := n) (α v) 0 τ = Morse.energy (Bridge.incl hN ∘ α v) 0 τ :=
      Bridge.energy_eq (α v) 0 τ
    rw [h1, energy_extA hτ hτ1 hvar hv]
    ring
  have hG : ContDiffOn ℝ 2 (fun v => Morse.energy (extA τ α v) 0 1) U :=
    hvar.contDiffOn_energy.of_le ENat.LEInfty.out
  have hF : ContDiffOn ℝ 2 (fun v : Rn 2 => energy (n := n) (α v) 0 τ) U :=
    (hG.sub contDiffOn_const).congr hFG
  have hev : (fun v : Rn 2 => energy (n := n) (α v) 0 τ) =ᶠ[𝓝 0]
      fun v => Morse.energy (extA τ α v) 0 1 - Morse.energy (Bridge.incl hN ∘ α 0) τ 1 :=
    Filter.eventuallyEq_of_mem (hU.mem_nhds h0U) hFG
  have hD : (fun u => fderiv ℝ (fun v : Rn 2 => energy (n := n) (α v) 0 τ) u e0) =ᶠ[𝓝 0]
      fun u => fderiv ℝ (fun v => Morse.energy (extA τ α v) 0 1) u e0 := by
    filter_upwards [hev.fderiv (𝕜 := ℝ)] with u hu
    rw [hu, fderiv_sub_const]
  refine ⟨RoundTrip.EnergyC2.differentiableAt_fderiv_apply hU hF h0U e0, ?_⟩
  have hmix : mixedD (fun v : Rn 2 => energy (n := n) (α v) 0 τ) =
      fderiv ℝ (fun u => fderiv ℝ (fun v => Morse.energy (extA τ α v) 0 1) u e0) 0 e1 := by
    unfold mixedD
    rw [hD.fderiv_eq]
  have h := RoundTrip.EnergyC2.fderiv_fderiv_apply_eq_deriv_deriv hU hG h0U e0 e1
  simp only [zero_add] at h
  rw [hmix, h]
  have hφ : ContDiff ℝ ∞ (fun p : ℝ × ℝ => p.1 • e0 + p.2 • e1) :=
    (contDiff_fst.smul contDiff_const).add (contDiff_snd.smul contDiff_const)
  have hφ0 : (fun p : ℝ × ℝ => p.1 • e0 + p.2 • e1) 0 ∈ U := by
    simpa using h0U
  have hvar2 := hvar.comp hφ hφ0
  have hαγ : ∀ s ∈ Icc (0 : ℝ) 1,
      (fun p : ℝ × ℝ => extA τ α (p.1 • e0 + p.2 • e1)) 0 s = (Bridge.incl hN ∘ α 0) s := by
    intro s _
    simp only [Prod.fst_zero, Prod.snd_zero, zero_smul, add_zero]
    exact extA_zero τ α s
  have hd := sv_holds (mem_pathSpace_of_isGeodesic hgeo) hub hvar2 hαγ
  simp only [zero_smul, add_zero, zero_add] at hd
  rw [hd.deriv]
  congr 1
  refine Morse.secondVariation_congr hN (fun s hs => ?_) (fun s hs => ?_)
  · exact deriv_extA hτ hα 0 hs.1
  · exact deriv_extA hτ hα 1 hs.1

/-- **Every `IsHessT τ` value is `2 secondVariation`** of the ambient fields, for blind fields in
`TΩ(γ|[0,τ])` (`0` beyond `τ`). -/
theorem hessT_eqT {τ : ℝ} (hτ : 0 < τ) (hτ1 : τ ≤ 1) {γ : ℝ → Bridge.Sub hN}
    (hgeo : IsGeodesic (Bridge.conn (hN := hN)) γ (Icc 0 1)) {W₁ W₂ : FA n γ}
    (h₁ : InTOmegaT (n := n) τ γ W₁) (h₂ : InTOmegaT (n := n) τ γ W₂) {r : ℝ}
    (h : IsHessT (n := n) τ γ W₁ W₂ r) :
    r = 2 * Morse.secondVariation hN (Bridge.incl hN ∘ γ) (Bridge.ambA γ W₁) (Bridge.ambA γ W₂) := by
  obtain ⟨U, α, k, t, hα, rfl, hW₁, hW₂, -, hr⟩ := h
  rw [← hr, (hessT_data hτ hτ1 hα hgeo).2]
  congr 1
  refine Morse.secondVariation_congr hN (fun s _ => ?_) (fun s _ => ?_)
  · split_ifs with hs
    · show Bridge.D hN (α 0 s) (varField (n := n) α 0 s) = Bridge.D hN (α 0 s) (W₁ s)
      rw [eq_of_heq (hW₁ s)]
    · show (0 : V) = Bridge.D hN (α 0 s) (W₁ s)
      rw [h₁.2.2.2 s fun h' => hs h'.2]
      exact (map_zero _).symm
  · split_ifs with hs
    · show Bridge.D hN (α 0 s) (varField (n := n) α 1 s) = Bridge.D hN (α 0 s) (W₂ s)
      rw [eq_of_heq (hW₂ s)]
    · show (0 : V) = Bridge.D hN (α 0 s) (W₂ s)
      rw [h₂.2.2.2 s fun h' => hs h'.2]
      exact (map_zero _).symm

/-- **Existence of `E_**(W₁, W₂)` for `E_0^τ` on `↥N`** (Lemma 11.A on `[0, 1]`, restricted to a
subdivision of `[0, τ]`; fields matched on all of `ℝ`). -/
theorem exists_isHessT {τ : ℝ} (hτ : 0 < τ) (hτ1 : τ ≤ 1) {γ : ℝ → Bridge.Sub hN}
    (hgeo : IsGeodesic (Bridge.conn (hN := hN)) γ (Icc 0 1)) {W₁ W₂ : FA n γ}
    (h₁ : InTOmegaT (n := n) τ γ W₁) (h₂ : InTOmegaT (n := n) τ γ W₂) :
    ∃ r, IsHessT (n := n) τ γ W₁ W₂ r := by
  have hc := mem_pathSpace_of_isGeodesic hgeo
  obtain ⟨hXs₁, -, hX0₁, hX1₁⟩ := (Morse.mem_pathTangent hN).1 (mem_pathTangent_of_inTOmegaT hτ1 h₁).1
  obtain ⟨hXs₂, -, hX0₂, hX1₂⟩ := (Morse.mem_pathTangent hN).1 (mem_pathTangent_of_inTOmegaT hτ1 h₂).1
  set X₁ := Bridge.ambA γ W₁
  set X₂ := Bridge.ambA γ W₂
  have hXτ₁ : X₁ τ = 0 := by
    show Bridge.D hN (γ τ) (W₁ τ) = 0
    rw [h₁.2.2.1]; exact map_zero _
  have hXτ₂ : X₂ τ = 0 := by
    show Bridge.D hN (γ τ) (W₂ τ) = 0
    rw [h₂.2.2.1]; exact map_zero _
  set Λ : ℝ → Rn 2 →L[ℝ] V := fun t =>
    (EuclideanSpace.proj (0 : Fin 2) : Rn 2 →L[ℝ] ℝ).smulRight (X₁ t) +
      (EuclideanSpace.proj (1 : Fin 2) : Rn 2 →L[ℝ] ℝ).smulRight (X₂ t) with hΛdef
  have hΛapp : ∀ t u, Λ t u = u 0 • X₁ t + u 1 • X₂ t := fun t u => by
    simp [hΛdef]
  have hΛT : ∀ t u, Morse.prj hN (Bridge.incl hN (γ t)) (Λ t u) = Λ t u := fun t u =>
    (Morse.prj_eq_self_iff hN (γ t).2).2 (by
      rw [hΛapp]
      exact add_mem (Submodule.smul_mem _ _ (Bridge.D_mem (γ t) (W₁ t)))
        (Submodule.smul_mem _ _ (Bridge.D_mem (γ t) (W₂ t))))
  have hΛs : Morse.IsPiecewiseSmooth Λ 0 1 :=
    (hXs₁.smulRight (EuclideanSpace.proj (0 : Fin 2) : Rn 2 →L[ℝ] ℝ)).add
      (hXs₂.smulRight (EuclideanSpace.proj (1 : Fin 2) : Rn 2 →L[ℝ] ℝ))
  have hΛ0 : Λ 0 = 0 := ContinuousLinearMap.ext fun u => by
    rw [hΛapp]; simp [hX0₁, hX0₂]
  have hΛ1 : Λ 1 = 0 := ContinuousLinearMap.ext fun u => by
    rw [hΛapp]; simp [hX1₁, hX1₂]
  have hΛτ : Λ τ = 0 := ContinuousLinearMap.ext fun u => by
    rw [hΛapp]; simp [hXτ₁, hXτ₂]
  obtain ⟨ε, hε, B, hα, -, -⟩ := Morse.exists_variation hN hc (P := Rn 2) hΛs
    (fun t _ u => hΛT t u) hΛ0 hΛ1
  set α := liftE γ Λ
  have hinc : ∀ u ∈ Metric.ball (0 : Rn 2) ε, ∀ t ∈ Icc (0 : ℝ) 1,
      Bridge.incl hN (α u t) = Morse.exp hN (Bridge.incl hN (γ t)) (Λ t u) :=
    fun u hu t ht => incl_liftE (hα.mem u hu t ht)
  have hinj : Function.Injective (Bridge.incl hN) := Subtype.val_injective
  have hα0 : α 0 = γ := funext fun t => by
    have e : Morse.exp hN (Bridge.incl hN (γ t)) (Λ t 0) = Bridge.incl hN (γ t) := by
      rw [map_zero]; exact Morse.exp_zero (γ t).2
    exact hinj ((incl_liftE (γ := γ) (Λ := Λ) (u := 0) (t := t) (by rw [e]; exact (γ t).2)).trans e)
  obtain ⟨k, tt, ht0, htk, hlt, hgood⟩ := exists_subdivT hτ B
  have hstrip : ∀ i < k, ContMDiffOn 𝓘(ℝ, Rn 2 × ℝ) 𝓘(ℝ, Rn n) ∞
      (fun x : Rn 2 × ℝ => α x.1 x.2) (Metric.ball (0 : Rn 2) ε ×ˢ Icc (tt i) (tt (i + 1))) := by
    intro i hi
    obtain ⟨hi0, hi1, hiB⟩ := hgood i hi
    refine contMDiffOn_map_iff.2
      ((hα.smooth _ _ hi0 (hlt i hi) (hi1.trans hτ1) hiB).congr fun p hp => ?_)
    exact hinc p.1 hp.1 p.2 ⟨hi0.trans hp.2.1, hp.2.2.trans (hi1.trans hτ1)⟩
  have hvs : IsVarSubT (n := n) τ (Metric.ball (0 : Rn 2) ε) α k tt := by
    refine ⟨Metric.isOpen_ball, Metric.mem_ball_self hε, ht0, htk, hlt, fun u hu => ⟨?_, ?_, ?_⟩,
      hstrip⟩
    · refine ⟨k, tt, ht0, htk, hlt, fun i hi => ?_⟩
      have hι : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, Rn 2 × ℝ) ∞ (fun s : ℝ => (u, s)) :=
        contMDiff_iff_contDiff.2 (contDiff_const.prodMk contDiff_id)
      exact (hstrip i hi).comp hι.contMDiffOn fun s hs => ⟨hu, hs⟩
    · refine hinj ?_
      rw [hinc u hu 0 ⟨le_rfl, zero_le_one⟩, hinc 0 (Metric.mem_ball_self hε) 0 ⟨le_rfl, zero_le_one⟩,
        hΛ0]
      rfl
    · refine hinj ?_
      rw [hinc u hu τ ⟨hτ.le, hτ1⟩, hinc 0 (Metric.mem_ball_self hε) τ ⟨hτ.le, hτ1⟩, hΛτ]
      rfl
  have hfield : ∀ (i : Fin 2) (t : ℝ),
      Bridge.D hN (γ t) (varField (n := n) α i t) = Λ t (EuclideanSpace.single i (1 : ℝ)) := by
    intro i t
    obtain ⟨hmem, hcd, hfd⟩ := exp_local (hN := hN) (γ t).2 (Λ t) (hΛT t)
    have hev : (Bridge.incl hN ∘ fun u => α u t) =ᶠ[𝓝 0]
        fun u => Morse.exp hN (Bridge.incl hN (γ t)) (Λ t u) := by
      filter_upwards [hmem] with u hu
      exact incl_liftE hu
    have h1 := D_mfderiv_of_contDiffAt (hcd.congr_of_eventuallyEq hev)
      (EuclideanSpace.single i (1 : ℝ))
    have h2 := (hfd.congr_of_eventuallyEq hev).fderiv
    rw [h2] at h1
    calc Bridge.D hN (γ t) (varField (n := n) α i t)
        = Bridge.D hN (α 0 t) (varField (n := n) α i t) := by rw [congrFun hα0 t]
      _ = _ := h1
  have hW : ∀ (i : Fin 2) (Wi : FA n γ), (∀ t, Λ t (EuclideanSpace.single i (1 : ℝ)) =
      Bridge.D hN (γ t) (Wi t)) → ∀ t, HEq (Wi t) (varField (n := n) α i t) := by
    intro i Wi hWi t
    have := Bridge.D_injective (γ t) ((hfield i t).trans (hWi t))
    exact heq_of_eq this.symm
  have hgeo' : IsGeodesic (Bridge.conn (hN := hN)) (α 0) (Icc 0 1) := by rw [hα0]; exact hgeo
  refine ⟨_, Metric.ball (0 : Rn 2) ε, α, k, tt, hvs, hα0,
    hW 0 W₁ fun t => by rw [hΛapp]; simp [X₁, Bridge.ambA],
    hW 1 W₂ fun t => by rw [hΛapp]; simp [X₂, Bridge.ambA], (hessT_data hτ hτ1 hvs hgeo').1, rfl⟩

theorem isHessT_iffT {τ : ℝ} (hτ : 0 < τ) (hτ1 : τ ≤ 1) {γ : ℝ → Bridge.Sub hN}
    (hgeo : IsGeodesic (Bridge.conn (hN := hN)) γ (Icc 0 1)) {W₁ W₂ : FA n γ}
    (h₁ : InTOmegaT (n := n) τ γ W₁) (h₂ : InTOmegaT (n := n) τ γ W₂) {r : ℝ} :
    IsHessT (n := n) τ γ W₁ W₂ r ↔
      r = 2 * Morse.secondVariation hN (Bridge.incl hN ∘ γ) (Bridge.ambA γ W₁) (Bridge.ambA γ W₂) := by
  refine ⟨hessT_eqT hτ hτ1 hgeo h₁ h₂, fun h => ?_⟩
  obtain ⟨r', hr'⟩ := exists_isHessT hτ hτ1 hgeo h₁ h₂
  rw [h, ← hessT_eqT hτ hτ1 hgeo h₁ h₂ hr']
  exact hr'

/-- **The choice function `HessT τ γ` is `2 secondVariation`** on `TΩ(γ|[0,τ])`. -/
theorem hessT_eq_T {τ : ℝ} (hτ : 0 < τ) (hτ1 : τ ≤ 1) {γ : ℝ → Bridge.Sub hN}
    (hgeo : IsGeodesic (Bridge.conn (hN := hN)) γ (Icc 0 1)) {W₁ W₂ : FA n γ}
    (h₁ : InTOmegaT (n := n) τ γ W₁) (h₂ : InTOmegaT (n := n) τ γ W₂) :
    HessT (n := n) τ γ W₁ W₂ =
      2 * Morse.secondVariation hN (Bridge.incl hN ∘ γ) (Bridge.ambA γ W₁) (Bridge.ambA γ W₂) := by
  have hex := exists_isHessT hτ hτ1 hgeo h₁ h₂
  unfold HessT
  rw [dif_pos hex]
  exact hessT_eqT hτ hτ1 hgeo h₁ h₂ hex.choose_spec


section LinAlgT

variable {E M : Type} [AddCommGroup E] [Module ℝ E] [AddCommGroup M] [Module ℝ M]

theorem bIndex_eq_formIndex_of {T : Set E} {H : E → E → ℝ} (B : LinearMap.BilinForm ℝ M)
    (φ : M →ₗ[ℝ] E) (hφ : Injective φ) (hT : Set.range φ = T)
    (hH : ∀ x y, H (φ x) (φ y) = B x y) : bIndex T H = Morse.formIndex B := by
  apply le_antisymm
  · unfold bIndex
    refine iSup₂_le fun S ⟨hST, hfd, hneg⟩ => ?_
    have hSR : S ≤ LinearMap.range φ := fun v hv => by
      have := hST hv
      rw [← hT] at this
      exact this
    have hmap : (S.comap φ).map φ = S := Submodule.map_comap_eq_of_le hSR
    let e : S.comap φ ≃ₗ[ℝ] S :=
      (Submodule.equivMapOfInjective φ hφ (S.comap φ)).trans (LinearEquiv.ofEq _ _ hmap)
    haveI : FiniteDimensional ℝ (S.comap φ) := LinearEquiv.finiteDimensional e.symm
    have hneg' : Morse.IsNegDefOn B (S.comap φ) := fun x hx hx0 => by
      rw [← hH]
      exact hneg (φ x) hx fun h => hx0 (hφ (h.trans (map_zero φ).symm))
    calc (Module.finrank ℝ S : ℕ∞) = Module.finrank ℝ (S.comap φ) := by rw [e.finrank_eq]
      _ ≤ Morse.formIndex B := Morse.le_formIndex hneg'
  · refine Morse.formIndex_le fun S' hfd hneg => ?_
    let e : S' ≃ₗ[ℝ] S'.map φ := Submodule.equivMapOfInjective φ hφ S'
    haveI : FiniteDimensional ℝ (S'.map φ) := LinearEquiv.finiteDimensional e
    have hST : ((S'.map φ : Submodule ℝ E) : Set E) ⊆ T := by
      rintro _ ⟨x, -, rfl⟩
      rw [← hT]
      exact ⟨x, rfl⟩
    have hneg' : IsNegDefSub H (S'.map φ) := by
      rintro _ ⟨x, hx, rfl⟩ hx0
      rw [hH]
      exact hneg x hx fun h => hx0 (by rw [h, map_zero])
    calc (Module.finrank ℝ S' : ℕ∞) = Module.finrank ℝ (S'.map φ) := by rw [e.finrank_eq]
      _ ≤ bIndex T H := by
        unfold bIndex
        exact le_iSup₂_of_le (f := fun (S : Submodule ℝ E)
          (_ : (S : Set E) ⊆ T ∧ FiniteDimensional ℝ S ∧ IsNegDefSub H S) =>
            (Module.finrank ℝ S : ℕ∞)) (S'.map φ) ⟨hST, inferInstance, hneg'⟩ le_rfl


end LinAlgT

/-- The dictionary map `fieldsUpTo τ → FA n γ`, `X ↦ toFA γ X`. -/
noncomputable def φT (γ : ℝ → Bridge.Sub hN) (τ : ℝ) :
    Morse.fieldsUpTo hN (Bridge.incl hN ∘ γ) τ →ₗ[ℝ] FA n γ :=
  (toFAₗ γ).comp ((Morse.pathTangent hN (Bridge.incl hN ∘ γ)).subtype.comp
    (Morse.fieldsUpTo hN (Bridge.incl hN ∘ γ) τ).subtype)

theorem φT_apply (γ : ℝ → Bridge.Sub hN) (τ : ℝ) (x : Morse.fieldsUpTo hN (Bridge.incl hN ∘ γ) τ) :
    φT (n := n) γ τ x = toFA γ ((x : Morse.pathTangent hN (Bridge.incl hN ∘ γ)) : ℝ → V) := rfl

theorem φT_injective {τ : ℝ} (hτ1 : τ ≤ 1) (γ : ℝ → Bridge.Sub hN) :
    Injective (φT (n := n) γ τ) := by
  intro x y h
  have hx := ((Morse.mem_pathTangent hN).1 (x : Morse.pathTangent hN (Bridge.incl hN ∘ γ)).2).2.1
  have hy := ((Morse.mem_pathTangent hN).1 (y : Morse.pathTangent hN (Bridge.incl hN ∘ γ)).2).2.1
  have h' := toFA_injOn hx hy h
  have hx0 : ∀ t, t ∉ Icc (0 : ℝ) τ →
      ((x : Morse.pathTangent hN (Bridge.incl hN ∘ γ)) : ℝ → V) t = 0 := x.2
  have hy0 : ∀ t, t ∉ Icc (0 : ℝ) τ →
      ((y : Morse.pathTangent hN (Bridge.incl hN ∘ γ)) : ℝ → V) t = 0 := y.2
  refine Subtype.ext (Subtype.ext (funext fun t => ?_))
  by_cases ht : t ∈ Icc (0 : ℝ) τ
  · exact h' ⟨ht.1, ht.2.trans hτ1⟩
  · rw [hx0 t ht, hy0 t ht]

theorem range_φT {τ : ℝ} (hτ : 0 < τ) (hτ1 : τ ≤ 1) {γ : ℝ → Bridge.Sub hN}
    (hγ : IsSmoothCurve (n := n) γ (Icc 0 1)) :
    Set.range (φT (n := n) γ τ) = TOm (n := n) τ γ := by
  ext Wf
  constructor
  · rintro ⟨x, rfl⟩
    exact inTOmegaT_toFA_T hτ hτ1 hγ (x : Morse.pathTangent hN (Bridge.incl hN ∘ γ)).2 x.2
  · intro hW
    have hW' : InTOmegaT (n := n) τ γ Wf := hW
    obtain ⟨hm, hout⟩ := mem_pathTangent_of_inTOmegaT hτ1 hW'
    refine ⟨⟨⟨_, hm⟩, hout⟩, funext fun t => ?_⟩
    rw [φT_apply]
    by_cases ht : t ∈ Icc (0 : ℝ) 1
    · rw [toFA_of_mem _ ht]
      exact Bridge.L_D (γ t) (Wf t)
    · rw [toFA_of_not_mem _ ht, hW'.2.2.2 t fun h => ht ⟨h.1, h.2.trans hτ1⟩]

/-- **`HessT τ` pulled back by `toFA` is `energyHessian` on `fieldsUpTo τ`.** -/
theorem hessT_φT {τ : ℝ} (hτ : 0 < τ) (hτ1 : τ ≤ 1) {γ : ℝ → Bridge.Sub hN}
    (hgeo : IsGeodesic (Bridge.conn (hN := hN)) γ (Icc 0 1))
    (hc : Morse.IsSmoothCurveIn hN (Bridge.incl hN ∘ γ))
    (x y : Morse.fieldsUpTo hN (Bridge.incl hN ∘ γ) τ) :
    HessT (n := n) τ γ (φT γ τ x) (φT γ τ y) =
      ((Morse.energyHessian hN hc.mem_pathSpace).restrict
        (Morse.fieldsUpTo hN (Bridge.incl hN ∘ γ) τ)) x y := by
  have hγs : IsSmoothCurve (n := n) γ (Icc 0 1) := hgeo.2.1
  have hx := inTOmegaT_toFA_T hτ hτ1 hγs (x : Morse.pathTangent hN (Bridge.incl hN ∘ γ)).2 x.2
  have hy := inTOmegaT_toFA_T hτ hτ1 hγs (y : Morse.pathTangent hN (Bridge.incl hN ∘ γ)).2 y.2
  have hxT := ((Morse.mem_pathTangent hN).1 (x : Morse.pathTangent hN (Bridge.incl hN ∘ γ)).2).2.1
  have hyT := ((Morse.mem_pathTangent hN).1 (y : Morse.pathTangent hN (Bridge.incl hN ∘ γ)).2).2.1
  rw [φT_apply, φT_apply, hessT_eq_T hτ hτ1 hgeo hx hy]
  show _ = Morse.energyHessian hN hc.mem_pathSpace (x : Morse.pathTangent hN (Bridge.incl hN ∘ γ))
    (y : Morse.pathTangent hN (Bridge.incl hN ∘ γ))
  rw [Morse.energyHessian_apply]
  congr 1
  exact Morse.secondVariation_congr hN (fun t ht => ambA_toFA hxT ht) (fun t ht => ambA_toFA hyT ht)

/-- **`λ(τ)` of B is the project's `indexUpTo τ`** on `↥N` (for a geodesic, `0 < τ ≤ 1`). -/
theorem lam_eq_indexUpTo {τ : ℝ} (hτ : 0 < τ) (hτ1 : τ ≤ 1) {γ : ℝ → Bridge.Sub hN}
    (hgeo : IsGeodesic (Bridge.conn (hN := hN)) γ (Icc 0 1))
    (hc : Morse.IsSmoothCurveIn hN (Bridge.incl hN ∘ γ)) :
    lam (n := n) τ γ = Morse.indexUpTo hN (Bridge.incl hN ∘ γ) hc τ := by
  unfold lam Morse.indexUpTo
  exact bIndex_eq_formIndex_of _ (φT γ τ) (φT_injective hτ1 γ) (range_φT hτ hτ1 hgeo.2.1)
    (hessT_φT hτ hτ1 hgeo hc)

end LamPf

/-! ## Third attempt: the index dictionary `LamEq n` is a theorem

`LamPf` above is a copy of the proof of `Emb.lamEqOne` of `Items/V9_23.lean` (Lemma 11.A and
Theorem 13.1 = `Morse.second_variation` for `E_0^τ` on `↥N`, `EnergyC2`'s `C²` regularity of
`u ↦ E(α(u))`, the `TΩ(γ|[0,τ])` dictionary `toFA`/`φT`, index transport `bIndex_eq_formIndex_of`,
then `Morse.indexUpTo_one`), here at `N = Sⁿ`. So A gives the whole corrected reading on the
embedded sphere. -/

open Milnor.Sphere in
/-- **`LamEq n` holds** (`Items/V9_23.lean`, `Emb.lamEqOne`, at the sphere). -/
theorem lamEq_holds (n : ℕ) : LamEq n := by
  intro p q γ hγ hg
  have hcs := LamPf.isSmoothCurveIn (hg.1.2.1 : IsSmoothCurve (n := n) γ (Icc 0 1))
  rw [LamPf.lam_eq_indexUpTo one_pos le_rfl hg.1 hcs, Morse.indexUpTo_one]
  congr 1

/-- **A gives the corrected B (`n ≥ 2`) on the embedded sphere** (unconditional). -/
theorem A_to_Bcorr_emb : A → Bcorr_emb := fun hA n hn =>
  A_to_BcorrEmbAt_of_lamEq hA n hn (lamEq_holds n)

#rt_check RoundTrip.V10_23.A_to_Bcorr_emb [Morse.mul_pi_lt_sphLen, Morse.energy_sphGeod, Morse.exists_eqOn_sphGeod, Morse.notMem_conjLocus_sph, Morse.formIndex_sphGeod, Morse.formIndex_eq_of_eqOn_sphGeod]
#rt_overlap RoundTrip.V10_23.A_to_Bcorr_emb [Morse.mul_pi_lt_sphLen, Morse.energy_sphGeod, Morse.exists_eqOn_sphGeod, Morse.notMem_conjLocus_sph, Morse.formIndex_sphGeod, Morse.formIndex_eq_of_eqOn_sphGeod]

end RoundTrip.V10_23
