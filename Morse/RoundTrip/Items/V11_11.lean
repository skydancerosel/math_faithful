import Morse
import RoundTrip.Check
import RoundTrip.Blind.V11_11
import RoundTrip.Bridge

open Set Filter Topology Function Module MeasureTheory
open scoped ContDiff Manifold ENNReal unitInterval RealInnerProductSpace

namespace RoundTrip.V11_11

/-- The project's statement (universes instantiated at `0`): `∫₀¹ sin²(πt) = ∫₀¹ cos²(πt) = 1/2`;
for a geodesic `γ ∈ Ω(N; p, q)` agreeing on `[0, 1]` with a smooth curve `c : ℝ → N`, a parallel
unit field `P` along `c` and `Vf = γ'` on `(0, 1)`: `sin(πt) P ∈ TΩ_γ` and
`E_**(W, W) = 2∫₀¹ (π² cos²(πt) − sin²(πt)⟨R(Vf, P)Vf, P⟩)` (`energyHessian_sin_parallel`); and for
`dim N ≥ 2`, `K ≥ (n − 1)/r²`, a geodesic of length `> πr` has `E_**(X, X) < 0` for some
`X ∈ TΩ_γ` (`exists_energyHessian_neg`). -/
def A : Prop :=
  type_of% @Morse.integral_sin_sq_pi_mul ∧ type_of% @Morse.integral_cos_sq_pi_mul ∧
    type_of% @Morse.energyHessian_sin_parallel.{0,0,0} ∧
    type_of% @Morse.exists_energyHessian_neg.{0,0,0}

theorem A_holds : A := ⟨@Morse.integral_sin_sq_pi_mul, @Morse.integral_cos_sq_pi_mul,
  @Morse.energyHessian_sin_parallel, @Morse.exists_energyHessian_neg⟩

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

/-- **The Ricci tensor of `S¹` vanishes** (blind `ricci`, induced connection). -/
theorem ricci_eq_zero (x : S) (U : TangentSpace 𝓘(ℝ, Bridge.Rn 1) x) :
    ricci (Bridge.conn (hN := sphSub 1)) x U U = 0 := by
  rw [Emb.ricci_eq]
  refine (Morse.ricci_sph (n := 1) (show Sph 1 from x) _).trans ?_
  simp

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

B allows `n = 1`, where there is no index `i ≠ n` and `(n − 1)π² − L²K(P_n, P_n) = 0`, so the
"negative" clause (d) fails. Counter-model: `S¹ ⊆ ℝ²` with the induced metric and connection, the
great circle `γ` of speed `L = 4 > π` (`r = 1`), the parallel unit field `P₁ = γ'/L`; the Ricci
tensor of `S¹` vanishes, so the hypothesis `K(P_n, P_n) ≥ 0` of (d) holds, and (d) asks for an
index `i ≠ n` in `Fin 1`. -/

section NotB

open S1 Milnor.Sphere RoundTrip.Bridge Bundle

/-- The velocity of `G L`, read in `ℝ²`, has norm `L`. -/
theorem norm_vel_G {L : ℝ} (hL : 0 ≤ L) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    ‖D (sphSub 1) (G L t) (vel (n := 1) (G L) (Icc 0 1) t)‖ = L := by
  have hγ := isGeodesic_G L
  have hsm : RoundTrip.BridgePrelude.IsSmoothCurve (n := 1) (G L) (Icc 0 1) := hγ.2.1
  have e : D (sphSub 1) (G L t) (vel (n := 1) (G L) (Icc 0 1) t) =
      derivWithin (incl (sphSub 1) ∘ G L) (Icc 0 1) t := D_vel hsm (uniqueDiffOn_Icc zero_lt_one) ht
  rw [e, incl_G,
    ((Morse.contDiff_greatCircle _ _ L).differentiable (by simp) t).hasDerivAt.hasDerivWithinAt
      |>.derivWithin (uniqueDiffOn_Icc zero_lt_one t ht)]
  exact norm_deriv_G hL t

theorem not_B : ¬ B := by
  intro hB
  have := S1.connectedSpace
  set γ := G 4 with hγdef
  have hγ := isGeodesic_G 4
  have hL : arcLen (n := 1) γ 0 1 = 4 := arcLen_G (by norm_num)
  set c : ℝ := (arcLen (n := 1) γ 0 1)⁻¹ with hc
  obtain ⟨-, hsm, hvs, -, D', hD', hDv⟩ := hγ
  have hsm' : RoundTrip.BridgePrelude.IsSmoothCurve (n := 1) γ (Icc 0 1) := hsm
  -- the parallel field `P = c • γ'`
  set P : Fin 1 → FA 1 γ := fun _ t => c • vel (n := 1) γ (Icc 0 1) t with hP
  have hpar : ∀ i, IsParallel (Bridge.conn (hN := sphSub 1)) γ (Icc 0 1) (P i) := by
    intro i
    refine ⟨Bridge.isSmoothAlong_smul hsm' (f := fun _ => c) contDiffOn_const hvs, D', hD',
      fun t ht => ?_⟩
    have := hD'.2.1 (fun _ => c) contDiffOn_const _ hvs t ht
    have h0 : derivWithin (fun _ : ℝ => c) (Icc 0 1) t = 0 := by simp
    beta_reduce at this
    rw [h0, zero_smul, zero_add, hDv t ht, smul_zero] at this
    exact this
  refine absurd (hB 1 S (Bridge.conn (hN := sphSub 1)) Bridge.conn_isLC one_pos γ
    (isGeodesic_G 4) P hpar ?_ ?_) ?_
  · intro t ht
    rw [orthonormal_iff_ite]
    intro i j
    rw [Subsingleton.elim i j, if_pos rfl, real_inner_self_eq_norm_sq]
    show ‖c • vel (n := 1) γ (Icc 0 1) t‖ ^ 2 = 1
    rw [norm_smul, Bridge.norm_eq, norm_vel_G (by norm_num) ht, hc, hL]
    norm_num
  · intro t ht
    show _ = arcLen (n := 1) γ 0 1 • c • vel (n := 1) γ (Icc 0 1) t
    rw [smul_smul, hc, mul_inv_cancel₀ (by rw [hL]; norm_num), one_smul]
  · intro h
    obtain ⟨-, -, -, h4⟩ := h
    obtain ⟨-, i, hi, -⟩ := h4 1 one_pos (fun t _ => by
      rw [S1.ricci_eq_zero]
      norm_num) (by rw [hL, mul_one]; linarith [Real.pi_lt_d2])
    exact hi (Subsingleton.elim _ _)

/-- `A ⇒ B` is false (A holds, B does not). -/
theorem not_A_to_B : ¬ (A → B) := fun h => not_B (h A_holds)

/-- `B ⇒ A`, ex falso (B is false). -/
theorem B_to_A : B → A := fun hB => absurd hB not_B

end NotB

#rt_check RoundTrip.V11_11.B_to_A [Morse.integral_sin_sq_pi_mul, Morse.integral_cos_sq_pi_mul, Morse.energyHessian_sin_parallel, Morse.exists_energyHessian_neg]
#rt_overlap RoundTrip.V11_11.B_to_A [Morse.integral_sin_sq_pi_mul, Morse.integral_cos_sq_pi_mul, Morse.energyHessian_sin_parallel, Morse.exists_energyHessian_neg]

end RoundTrip.V11_11
