import Morse
import RoundTrip.Check
import RoundTrip.Blind.V12_18
import RoundTrip.Bridge

/-!
# V12_18 (Milnor §20, Theorem 20.5, for matrix groups along `exp(tA)`)

`A` (universes `0`): for a matrix group `G ⊆ U(n)` (a slice submanifold of `Mₙ(𝕜)`, `Morse.IsMatrixGroup hG 𝔤`,
induced metric), `A ∈ 𝔤`, `γ(t) = exp(tA)`, `h(t) = exp(tA/2)` (`halfExp`) and `K_A(U) = ¼[[A,U],A]` (`jacK`,
vocabulary): for a `𝔤`-valued `U`, `D/dt(hUh) = hU'h` (`covD_conj`), `R(γ', hMh)γ' = h K_A(M) h`
(`curvR_conj`), `hUh` is a Jacobi field when `U'' + K_A(U) = 0` (`isJacobiField_conj`), and its covariant
derivative at `0` is `U'(0)` (`covAlong_conj_zero`).

`B` (blind): Theorem 20.5 for an abstract locally symmetric manifold (Mathlib `RiemannianBundle`, any
Levi-Civita connection, `IsLocSymm`), any geodesic on an interval `s ∋ 0` and any orthonormal eigenbasis
`U_i` of `K_V`: (1) the conjugate parameters are `πk/√e_i`, (2) the multiplicities are the counts of `e_i`,
(3) parallel fields `P_i` with `P_i(0) = U_i` stay eigenvectors of `K_{γ'}` and `Σ w_iP_i` is a Jacobi field iff
`w_i'' + e_iw_i = 0`.

* `A → B` fails genuinely, also for matrix groups (the embedded case): `A` has no conjugate points or
  multiplicities (Milnor's (1), (2); for `SU(n)` they are in `SUJacobi.lean`, not in this item), only the
  "if" half of the Jacobi equation in the frame, only along `exp(tA)` through `I`, and it never identifies
  Milnor's parallel frame (uniqueness of parallel transport) or the eigenvalues of the blind `K_V`.
* `B → A` fails: `B` says nothing about matrices, `halfExp`, `jacK`.

**Partial bridge** (`A_to_jacobi_blind`, uses `A`): read in the blind vocabulary through the Bridge (for `G` with
model `ℝᵐ` as `Bridge.Sub hG`, induced connection `Bridge.conn`), `A`'s `isJacobiField_conj` says that
`t ↦ h(t)U(t)h(t)` is a blind Jacobi field (`IsJacobi`) along `t ↦ exp(tA)` on `[0, 1]` — the "if" half of
`B`'s (3)(b) in the frame `h U_i h` (which `covD_conj` shows parallel); dictionary for Jacobi fields from V9_10.
-/

open Matrix Set Filter Topology Function Module
open scoped Morse.MatrixInner RealInnerProductSpace Manifold ContDiff

noncomputable section
set_option linter.unusedSectionVars false

namespace RoundTrip.V12_18

/-- The project's statement (universes `0`). -/
def A : Prop :=
  type_of% @Morse.IsMatrixGroup.covD_conj.{0,0,0,0} ∧
    type_of% @Morse.IsMatrixGroup.curvR_conj.{0,0,0,0} ∧
    type_of% @Morse.IsMatrixGroup.isJacobiField_conj.{0,0,0,0} ∧
    type_of% @Morse.IsMatrixGroup.covAlong_conj_zero.{0,0,0,0}

theorem A_holds : A :=
  ⟨@Morse.IsMatrixGroup.covD_conj, @Morse.IsMatrixGroup.curvR_conj,
    @Morse.IsMatrixGroup.isJacobiField_conj, @Morse.IsMatrixGroup.covAlong_conj_zero⟩

/-! ## Jacobi fields of a slice submanifold in the blind vocabulary (copied from V9_10) -/

namespace Emb

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

end Emb

open Emb RoundTrip.Bridge

/-- `A`'s Jacobi equation along `exp(tA)`, in the blind vocabulary (for `G` with model `ℝᵐ`, as `Bridge.Sub hG`
with the induced connection): `t ↦ h(t)U(t)h(t)` (in chart coordinates) is a blind Jacobi field on `[0, 1]`
along `t ↦ exp(tA)` whenever `U'' + K_A(U) = 0`. -/
def A_blind : Prop :=
  ∀ (𝕜 : Type) [RCLike 𝕜] (k m : ℕ) (W : Type) [NormedAddCommGroup W] [NormedSpace ℝ W]
    [FiniteDimensional ℝ W] (G : Set (Matrix (Fin k) (Fin k) 𝕜))
    (hG : Milnor.IsSliceSubmanifold 𝓘(ℝ, Matrix (Fin k) (Fin k) 𝕜) (Rn m) W G)
    (𝔤 : LieSubalgebra ℝ (Matrix (Fin k) (Fin k) 𝕜)) (h : Morse.IsMatrixGroup hG 𝔤)
    (X : Matrix (Fin k) (Fin k) 𝕜) (hX : X ∈ 𝔤) (U : ℝ → Matrix (Fin k) (Fin k) 𝕜),
    (∀ s, U s ∈ 𝔤) → ContDiff ℝ ∞ U → (∀ s, deriv (deriv U) s + Morse.jacK X (U s) = 0) →
      IsJacobi (Bridge.conn (hN := hG))
        (fun t => ((⟨NormedSpace.exp (t • X), h.exp_smul_mem hX t⟩ : G) : Bridge.Sub hG)) (Icc 0 1)
        (fun t => L hG ((⟨NormedSpace.exp (t • X), h.exp_smul_mem hX t⟩ : G) : Bridge.Sub hG)
          (Morse.halfExp X t * U t * Morse.halfExp X t))

theorem A_to_jacobi_blind : A → A_blind := by
  intro hA 𝕜 _ k m W _ _ _ G hG 𝔤 h X hX U hU𝔤 hU hODE
  set γ : ℝ → Bridge.Sub hG := fun t => ((⟨NormedSpace.exp (t • X), h.exp_smul_mem hX t⟩ : G) : Bridge.Sub hG)
  have hγ : IsSmoothCurve (n := m) γ (Icc 0 1) :=
    isSmoothCurve_iff.2 (Morse.contDiff_exp_smul X).contDiffOn
  refine isJacobi_of_isJacobiField hγ ?_
  have hamb : ambA γ (fun t => L hG (γ t) (Morse.halfExp X t * U t * Morse.halfExp X t)) =
      fun t => Morse.halfExp X t * U t * Morse.halfExp X t := by
    funext t
    refine D_L ?_
    rw [h.mem_tangentSubspace_iff]
    change (NormedSpace.exp (t • X))ᴴ * (Morse.halfExp X t * U t * Morse.halfExp X t) ∈ 𝔤
    have hu := h.unitary _ (h.halfExp_mem hX t)
    have e : (Morse.halfExp X t)ᴴ * (Morse.halfExp X t * U t * Morse.halfExp X t) =
        U t * Morse.halfExp X t := by
      rw [Matrix.mul_assoc, ← Matrix.mul_assoc _ (Morse.halfExp X t), hu, Matrix.one_mul]
    rw [← Morse.halfExp_mul_halfExp, conjTranspose_mul, Matrix.mul_assoc, e, ← Matrix.mul_assoc]
    exact h.conj_mem' (h.halfExp_mem hX t) (hU𝔤 t)
  rw [hamb]
  exact hA.2.2.1 h hX hU𝔤 hU hODE

#rt_check RoundTrip.V12_18.A_to_jacobi_blind [Morse.IsMatrixGroup.covD_conj, Morse.IsMatrixGroup.curvR_conj,
  Morse.IsMatrixGroup.isJacobiField_conj, Morse.IsMatrixGroup.covAlong_conj_zero]
#rt_overlap RoundTrip.V12_18.A_to_jacobi_blind [Morse.IsMatrixGroup.covD_conj, Morse.IsMatrixGroup.curvR_conj,
  Morse.IsMatrixGroup.isJacobiField_conj, Morse.IsMatrixGroup.covAlong_conj_zero]

end RoundTrip.V12_18
