import Milnor.Chapter8.FramedOps
import Milnor.Chapter8.Transversality
import Milnor.Chapter7.ThmAconv
import Milnor.Chapter7.ThmA

/-!
# The intersection product of framed cobordism classes (Milnor §8, Problem 17, first part)

Let `Πᵖ(M)` be the set of framed cobordism classes of framed submanifolds of `M` of codimension
`p` (`FramedClass`).  Transverse intersection defines a correspondence
`Πᵖ(M) × Π^q(M) → Π^{p+q}(M)`.

## Main definitions and results

* `FramedSub.dual F x : ℝᴷ⁺¹ → ℝᵖ`: the dual forms of the framing `v` of `F` at `x`,
  `α y = Gram(v)⁻¹ (⟪vᵢ, y⟫)ᵢ`, with `α vᵢ = eᵢ` (`InterProd.dual_v`), vanishing on `span(v)ᗮ`
  (`InterProd.dual_eq_zero_of_forall_inner`), in particular on `TₓN` and on `(TₓM)ᗮ`; smooth in
  `x` (`InterProd.contMDiff_dual`).
* `FramedSub.inter F G htr hr`: for transverse `F`, `G`, the submanifold `N ∩ N'` framed by the
  vectors `w_k` tangent to `M`, normal to `N ∩ N'`, with `(α_F w_k, α_G w_k)` the `k`-th standard
  basis vector of `ℝᵖ × ℝ^q` (`InterProd.dual_inter_v`): `w_k = A^*(A A^*)⁻¹ e_k` for
  `A = (α_F, α_G)`, which is surjective at the points of `N ∩ N'` by transversality.
* `exists_transverse_rep`: every pair of classes has transverse representatives.
* `exists_intersection_product`: for `p, q ≥ 1` there is `μ : Πᵖ(M) → Π^q(M) → Π^{p+q}(M)` with
  `μ [F] [G] = [F ∩ G]` whenever `F` and `G` meet transversally; it is unique
  (`intersection_product_unique`).

## Proofs

* Transverse representatives.  For a Theorem-B map `f` of `F`, pick a common regular value `z`
  of `f` and of `f|N'` (the first set is open and contains the north pole, the second is dense by
  Brown's theorem).  Then `f⁻¹(z)` is framed cobordant to `F` (Lemmas 1 and 2 of §7), and it
  meets `N'` transversally since `df` maps `TN'` onto `T_zSᵖ` and has kernel `T f⁻¹(z)`.
* Invariance.  A smooth `μ : Sᵖ × S^q → S^{p+q}` with `μ⁻¹(north) = {(north, north)}` and
  prescribed derivative `Γ` at `(north, north)`: `μ (a, b) = stdMap (E (σ a, σ b))` if neither
  `a` nor `b` is the south pole (`σ` the stereographic projection from the south pole, `E` a
  linear isomorphism), `μ = south` otherwise.  If `F = Pont(f, north, c b)` and
  `G = Pont(g, north, c' b')` (Theorem B) meet transversally, then `north` is a regular value of
  `h = μ ∘ (f, g)` and `Pont(h, north, β) = F ∩ G` exactly (`InterProd.pontryagin_mu_eq`), since
  `dF̃_h = Γ ∘ (dF̃_f, dF̃_g)` and `dF̃_f = B_{c b} ∘ α_F`.  With `Γ` sending the positive bases
  `b`, `b'` to a positive basis `γ`, `β` is a positive diagonal rescaling of `γ`.  If `F ∼ F₁` and
  `G ∼ G₁`, then `f ≃ f₁` and `g ≃ g₁` (Theorem A, converse), hence `h ≃ h₁`, and Theorem A with
  Lemma 1 gives `F ∩ G ∼ F₁ ∩ G₁` (`InterProd.framedCobordant_inter`).

The auxiliary declarations live in `Milnor.Problems.InterProd`.
-/

open Set Filter Topology Function Module Metric
open scoped ContDiff Manifold RealInnerProductSpace

noncomputable section

namespace Milnor

namespace Problems

open Sphere Framed

namespace InterProd

/-! ### The dual family of a linearly independent family -/

section dualOf

variable {k p : ℕ}

/-- The linear map `c ↦ ∑ⱼ cⱼ Vⱼ`. -/
def frameCLM (V : Fin p → EuclideanSpace ℝ (Fin k)) :
    EuclideanSpace ℝ (Fin p) →L[ℝ] EuclideanSpace ℝ (Fin k) :=
  ∑ j, (EuclideanSpace.proj j : EuclideanSpace ℝ (Fin p) →L[ℝ] ℝ).smulRight (V j)

theorem frameCLM_apply (V : Fin p → EuclideanSpace ℝ (Fin k)) (c : EuclideanSpace ℝ (Fin p)) :
    frameCLM V c = ∑ j, c j • V j := by
  simp [frameCLM]

theorem frameCLM_single (V : Fin p → EuclideanSpace ℝ (Fin k)) (i : Fin p) :
    frameCLM V (EuclideanSpace.single i 1) = V i := by
  rw [frameCLM_apply]
  simp

theorem injective_frameCLM {V : Fin p → EuclideanSpace ℝ (Fin k)} (hV : LinearIndependent ℝ V) :
    Injective (frameCLM V) := by
  refine (injective_iff_map_eq_zero _).2 fun c hc => ?_
  rw [frameCLM_apply] at hc
  have := (Fintype.linearIndependent_iff.1 hV) (fun j => c j) hc
  ext i
  simp [this i]

theorem adjoint_frameCLM_eq_zero {V : Fin p → EuclideanSpace ℝ (Fin k)}
    {y : EuclideanSpace ℝ (Fin k)} (hy : ∀ i, ⟪V i, y⟫ = 0) :
    ContinuousLinearMap.adjoint (frameCLM V) y = 0 := by
  have h : ∀ c, ⟪ContinuousLinearMap.adjoint (frameCLM V) y, c⟫ = 0 := by
    intro c
    rw [ContinuousLinearMap.adjoint_inner_left, frameCLM_apply, inner_sum]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [real_inner_smul_right, real_inner_comm, hy j, mul_zero]
  exact inner_self_eq_zero.1 (h _)

theorem inner_eq_zero_of_adjoint_frameCLM {V : Fin p → EuclideanSpace ℝ (Fin k)}
    {y : EuclideanSpace ℝ (Fin k)} (hy : ContinuousLinearMap.adjoint (frameCLM V) y = 0)
    (i : Fin p) : ⟪V i, y⟫ = 0 := by
  have h := ContinuousLinearMap.adjoint_inner_left (frameCLM V) (EuclideanSpace.single i 1) y
  rw [hy, inner_zero_left, frameCLM_single] at h
  rw [real_inner_comm]
  exact h.symm

theorem surjective_adjoint_frameCLM {V : Fin p → EuclideanSpace ℝ (Fin k)}
    (hV : LinearIndependent ℝ V) : Surjective (ContinuousLinearMap.adjoint (frameCLM V)) := by
  have h := range_adjoint_eq (frameCLM V)
  rw [LinearMap.ker_eq_bot.2 (injective_frameCLM hV), Submodule.bot_orthogonal_eq_top] at h
  exact LinearMap.range_eq_top.1 h

/-- The Gram operator `U^* U` of an independent family is invertible. -/
theorem isUnit_gram {V : Fin p → EuclideanSpace ℝ (Fin k)} (hV : LinearIndependent ℝ V) :
    IsUnit ((ContinuousLinearMap.adjoint (frameCLM V)).comp (frameCLM V)) := by
  have := isUnit_comp_adjoint (surjective_adjoint_frameCLM hV)
  rwa [ContinuousLinearMap.adjoint_adjoint] at this

/-- **The dual family**: `α y = (U^* U)⁻¹ U^* y = Gram(V)⁻¹ (⟪Vᵢ, y⟫)ᵢ`. -/
def dualOf (V : Fin p → EuclideanSpace ℝ (Fin k)) :
    EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin p) :=
  (Ring.inverse ((ContinuousLinearMap.adjoint (frameCLM V)).comp (frameCLM V))).comp
    (ContinuousLinearMap.adjoint (frameCLM V))

theorem dualOf_frameCLM {V : Fin p → EuclideanSpace ℝ (Fin k)} (hV : LinearIndependent ℝ V)
    (c : EuclideanSpace ℝ (Fin p)) : dualOf V (frameCLM V c) = c := by
  obtain ⟨u, hu⟩ := isUnit_gram hV
  have h1 : dualOf V (frameCLM V c) =
      Ring.inverse ((ContinuousLinearMap.adjoint (frameCLM V)).comp (frameCLM V))
        (((ContinuousLinearMap.adjoint (frameCLM V)).comp (frameCLM V)) c) := rfl
  rw [h1, ← hu, Ring.inverse_unit, ← mul_apply_eq_comp, u.inv_mul, one_apply_eq_self]

theorem dualOf_self {V : Fin p → EuclideanSpace ℝ (Fin k)} (hV : LinearIndependent ℝ V)
    (i : Fin p) : dualOf V (V i) = EuclideanSpace.single i 1 := by
  rw [← frameCLM_single V i, dualOf_frameCLM hV]

theorem dualOf_eq_zero {V : Fin p → EuclideanSpace ℝ (Fin k)} {y : EuclideanSpace ℝ (Fin k)}
    (hy : ∀ i, ⟪V i, y⟫ = 0) : dualOf V y = 0 := by
  show Ring.inverse ((ContinuousLinearMap.adjoint (frameCLM V)).comp (frameCLM V))
    (ContinuousLinearMap.adjoint (frameCLM V) y) = 0
  rw [adjoint_frameCLM_eq_zero hy, map_zero]

theorem inner_eq_zero_of_dualOf_eq_zero {V : Fin p → EuclideanSpace ℝ (Fin k)}
    (hV : LinearIndependent ℝ V) {y : EuclideanSpace ℝ (Fin k)} (hy : dualOf V y = 0) (i : Fin p) :
    ⟪V i, y⟫ = 0 := by
  obtain ⟨u, hu⟩ := isUnit_gram hV
  have h1 : ContinuousLinearMap.adjoint (frameCLM V) y =
      ((ContinuousLinearMap.adjoint (frameCLM V)).comp (frameCLM V)) (dualOf V y) := by
    show _ = ((ContinuousLinearMap.adjoint (frameCLM V)).comp (frameCLM V))
      (Ring.inverse ((ContinuousLinearMap.adjoint (frameCLM V)).comp (frameCLM V))
        (ContinuousLinearMap.adjoint (frameCLM V) y))
    rw [← hu, Ring.inverse_unit, ← mul_apply_eq_comp, u.mul_inv, one_apply_eq_self]
  rw [hy, map_zero] at h1
  exact inner_eq_zero_of_adjoint_frameCLM h1 i

theorem surjective_dualOf {V : Fin p → EuclideanSpace ℝ (Fin k)} (hV : LinearIndependent ℝ V) :
    Surjective (dualOf V) := fun c => ⟨frameCLM V c, dualOf_frameCLM hV c⟩

theorem contDiff_frameCLM : ContDiff ℝ ∞ (frameCLM (k := k) (p := p)) := by
  have h : (frameCLM (k := k) (p := p)) = fun V => ∑ j,
      (EuclideanSpace.proj j : EuclideanSpace ℝ (Fin p) →L[ℝ] ℝ).smulRight (V j) := rfl
  rw [h]
  exact ContDiff.sum fun j _ => contDiff_const.smulRight (contDiff_apply ℝ _ j)

theorem contDiffAt_dualOf {V : Fin p → EuclideanSpace ℝ (Fin k)} (hV : LinearIndependent ℝ V) :
    ContDiffAt ℝ ∞ (dualOf (k := k) (p := p)) V := by
  have hU := (contDiff_frameCLM (k := k) (p := p)).contDiffAt (x := V)
  have hUad : ContDiffAt ℝ ∞ (fun V : Fin p → EuclideanSpace ℝ (Fin k) =>
      ContinuousLinearMap.adjoint (frameCLM V)) V :=
    ((Tub.adjointCLM (k := k) (n := p)).contDiff.contDiffAt).comp V hU
  have hG : ContDiffAt ℝ ∞ (fun V : Fin p → EuclideanSpace ℝ (Fin k) =>
      (ContinuousLinearMap.adjoint (frameCLM V)).comp (frameCLM V)) V := hUad.clm_comp hU
  obtain ⟨u, hu⟩ := isUnit_gram hV
  have hinv : ContDiffAt ℝ ∞ (fun V : Fin p → EuclideanSpace ℝ (Fin k) =>
      Ring.inverse ((ContinuousLinearMap.adjoint (frameCLM V)).comp (frameCLM V))) V := by
    have := contDiffAt_ringInverse ℝ (n := ∞) u
    rw [hu] at this
    exact this.comp V hG
  exact hinv.clm_comp hUad

end dualOf

/-! ### Pairs of dual families and the intersection framing -/

section pair

variable {k p q : ℕ}

/-- The standard identification `ℝᵖ × ℝ^q ≅ ℝ^{p+q}`. -/
abbrev prodEuc (p q : ℕ) :
    (EuclideanSpace ℝ (Fin p) × EuclideanSpace ℝ (Fin q)) ≃L[ℝ] EuclideanSpace ℝ (Fin (p + q)) :=
  (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := p) (m := q)).symm

/-- The pair of dual families `y ↦ (α_V y, α_V' y)`, read in `ℝ^{p+q}`. -/
def pairA (V : Fin p → EuclideanSpace ℝ (Fin k)) (V' : Fin q → EuclideanSpace ℝ (Fin k)) :
    EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin (p + q)) :=
  (prodEuc p q : (EuclideanSpace ℝ (Fin p) × EuclideanSpace ℝ (Fin q)) →L[ℝ]
    EuclideanSpace ℝ (Fin (p + q))).comp ((dualOf V).prod (dualOf V'))

variable {V : Fin p → EuclideanSpace ℝ (Fin k)} {V' : Fin q → EuclideanSpace ℝ (Fin k)}

theorem pairA_apply (y : EuclideanSpace ℝ (Fin k)) :
    pairA V V' y = prodEuc p q (dualOf V y, dualOf V' y) := rfl

theorem pairA_eq_zero_iff {y : EuclideanSpace ℝ (Fin k)} :
    pairA V V' y = 0 ↔ dualOf V y = 0 ∧ dualOf V' y = 0 := by
  rw [pairA_apply, (prodEuc p q).map_eq_zero_iff, Prod.mk_eq_zero]

theorem surjective_pairA (hV : LinearIndependent ℝ V) (hV' : LinearIndependent ℝ V')
    (h : LinearMap.ker (dualOf V : EuclideanSpace ℝ (Fin k) →ₗ[ℝ] EuclideanSpace ℝ (Fin p)) ⊔
      LinearMap.ker (dualOf V' : EuclideanSpace ℝ (Fin k) →ₗ[ℝ] EuclideanSpace ℝ (Fin q)) = ⊤) :
    Surjective (pairA V V') := by
  have hs := Transversality.surjective_prod_of_ker_sup
    (A := (dualOf V : EuclideanSpace ℝ (Fin k) →ₗ[ℝ] EuclideanSpace ℝ (Fin p)))
    (B := (dualOf V' : EuclideanSpace ℝ (Fin k) →ₗ[ℝ] EuclideanSpace ℝ (Fin q)))
    (surjective_dualOf hV) (surjective_dualOf hV') h
  intro c
  obtain ⟨y, hy⟩ := hs ((prodEuc p q).symm c)
  refine ⟨y, ?_⟩
  have h1 : (dualOf V y, dualOf V' y) = (prodEuc p q).symm c := hy
  rw [pairA_apply, h1, ContinuousLinearEquiv.apply_symm_apply]

/-- The intersection framing `w_k = A^*(A A^*)⁻¹ e_k`, `A = pairA V V'`. -/
def interV (V : Fin p → EuclideanSpace ℝ (Fin k)) (V' : Fin q → EuclideanSpace ℝ (Fin k))
    (i : Fin (p + q)) : EuclideanSpace ℝ (Fin k) :=
  pinv (pairA V V') (EuclideanSpace.single i 1)

theorem pairA_interV (hA : Surjective (pairA V V')) (i : Fin (p + q)) :
    pairA V V' (interV V V' i) = EuclideanSpace.single i 1 :=
  comp_pinv hA _

theorem inner_interV_eq_zero {y : EuclideanSpace ℝ (Fin k)} (hy : pairA V V' y = 0)
    (i : Fin (p + q)) : ⟪interV V V' i, y⟫ = 0 :=
  inner_pinv_eq_zero _ _ hy

theorem linearIndependent_interV (hA : Surjective (pairA V V')) :
    LinearIndependent ℝ (interV V V') := by
  refine LinearIndependent.of_comp
    (pairA V V' : EuclideanSpace ℝ (Fin k) →ₗ[ℝ] EuclideanSpace ℝ (Fin (p + q))) ?_
  have : ((pairA V V' : EuclideanSpace ℝ (Fin k) →ₗ[ℝ] EuclideanSpace ℝ (Fin (p + q))) ∘
      interV V V') = fun i => EuclideanSpace.single i (1 : ℝ) :=
    funext fun i => pairA_interV hA i
  rw [this]
  exact linearIndependent_single

theorem interV_mem {T : Submodule ℝ (EuclideanSpace ℝ (Fin k))}
    (hT : ∀ y ∈ Tᗮ, pairA V V' y = 0) (i : Fin (p + q)) : interV V V' i ∈ T := by
  have h1 : interV V V' i ∈ (LinearMap.ker (pairA V V' :
      EuclideanSpace ℝ (Fin k) →ₗ[ℝ] EuclideanSpace ℝ (Fin (p + q))))ᗮ := by
    rw [Submodule.mem_orthogonal']
    intro v hv
    exact inner_pinv_eq_zero _ _ (LinearMap.mem_ker.1 hv)
  have h2 : Tᗮ ≤ LinearMap.ker (pairA V V' :
      EuclideanSpace ℝ (Fin k) →ₗ[ℝ] EuclideanSpace ℝ (Fin (p + q))) := fun y hy =>
    LinearMap.mem_ker.2 (hT y hy)
  have h3 := Submodule.orthogonal_le h2 h1
  rwa [Submodule.orthogonal_orthogonal] at h3

theorem contDiffAt_pairA (hV : LinearIndependent ℝ V) (hV' : LinearIndependent ℝ V') :
    ContDiffAt ℝ ∞ (fun W : (Fin p → EuclideanSpace ℝ (Fin k)) × (Fin q → EuclideanSpace ℝ (Fin k)) =>
      pairA W.1 W.2) (V, V') := by
  have h1 : ContDiffAt ℝ ∞ (fun W : (Fin p → EuclideanSpace ℝ (Fin k)) ×
      (Fin q → EuclideanSpace ℝ (Fin k)) => dualOf W.1) (V, V') :=
    (contDiffAt_dualOf hV).comp (V, V') contDiffAt_fst
  have h2 : ContDiffAt ℝ ∞ (fun W : (Fin p → EuclideanSpace ℝ (Fin k)) ×
      (Fin q → EuclideanSpace ℝ (Fin k)) => dualOf W.2) (V, V') :=
    (contDiffAt_dualOf hV').comp (V, V') contDiffAt_snd
  have h3 := ((ContinuousLinearMap.prodL ℝ : ((EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin p)) ×
      (EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin q))) ≃L[ℝ]
      (EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin p) × EuclideanSpace ℝ (Fin q))).contDiff.contDiffAt).comp
      (V, V') (h1.prodMk h2)
  have h4 : ContDiffAt ℝ ∞ (fun W : (Fin p → EuclideanSpace ℝ (Fin k)) ×
      (Fin q → EuclideanSpace ℝ (Fin k)) => (dualOf W.1).prod (dualOf W.2)) (V, V') := h3
  exact contDiffAt_const.clm_comp h4

theorem contDiffAt_interV (hV : LinearIndependent ℝ V) (hV' : LinearIndependent ℝ V')
    (hA : Surjective (pairA V V')) (i : Fin (p + q)) :
    ContDiffAt ℝ ∞ (fun W : (Fin p → EuclideanSpace ℝ (Fin k)) × (Fin q → EuclideanSpace ℝ (Fin k)) =>
      interV W.1 W.2 i) (V, V') := by
  have hP := contDiffAt_pairA hV hV'
  have hPad : ContDiffAt ℝ ∞ (fun W : (Fin p → EuclideanSpace ℝ (Fin k)) ×
      (Fin q → EuclideanSpace ℝ (Fin k)) => ContinuousLinearMap.adjoint (pairA W.1 W.2)) (V, V') :=
    ((Tub.adjointCLM (k := p + q) (n := k)).contDiff.contDiffAt).comp (V, V') hP
  have hPP : ContDiffAt ℝ ∞ (fun W : (Fin p → EuclideanSpace ℝ (Fin k)) ×
      (Fin q → EuclideanSpace ℝ (Fin k)) =>
      (pairA W.1 W.2).comp (ContinuousLinearMap.adjoint (pairA W.1 W.2))) (V, V') :=
    hP.clm_comp hPad
  obtain ⟨u, hu⟩ := isUnit_comp_adjoint hA
  have hinv : ContDiffAt ℝ ∞ (fun W : (Fin p → EuclideanSpace ℝ (Fin k)) ×
      (Fin q → EuclideanSpace ℝ (Fin k)) =>
      Ring.inverse ((pairA W.1 W.2).comp (ContinuousLinearMap.adjoint (pairA W.1 W.2)))) (V, V') := by
    have := contDiffAt_ringInverse ℝ (n := ∞) u
    rw [hu] at this
    exact this.comp (V, V') hPP
  exact (hPad.clm_comp hinv).clm_apply contDiffAt_const

end pair

end InterProd

/-! ### The dual forms of a framing and the intersection of framed submanifolds -/

variable {K m w : ℕ} {M : Set (EuclideanSpace ℝ (Fin (K + 1)))}
  {hM : IsSliceSubmanifold 𝓘(ℝ, EuclideanSpace ℝ (Fin (K + 1))) (EuclideanSpace ℝ (Fin m))
    (EuclideanSpace ℝ (Fin w)) M} {n p n' q r : ℕ}

/-- **The dual forms of a framing.** The linear map `α_F(x) : ℝᴷ⁺¹ → ℝᵖ` with `α_F(x) vᵢ(x) = eᵢ`,
vanishing on `span(v(x))ᗮ` (in particular on `TₓN` and on `(TₓM)ᗮ`):
`α_F(x) y = Gram(v(x))⁻¹ (⟪vᵢ(x), y⟫)ᵢ`. -/
def _root_.Milnor.Framed.FramedSub.dual (F : FramedSub hM n p) (x : F.N) :
    EuclideanSpace ℝ (Fin (K + 1)) →L[ℝ] EuclideanSpace ℝ (Fin p) :=
  InterProd.dualOf (fun i => F.v i x)

namespace InterProd

theorem dual_v (F : FramedSub hM n p) (x : F.N) (i : Fin p) :
    F.dual x (F.v i x) = EuclideanSpace.single i 1 :=
  dualOf_self (F.indep x) i

theorem dual_eq_zero_of_forall_inner (F : FramedSub hM n p) (x : F.N)
    {y : EuclideanSpace ℝ (Fin (K + 1))} (hy : ∀ i, ⟪F.v i x, y⟫ = 0) : F.dual x y = 0 :=
  dualOf_eq_zero hy

theorem inner_v_eq_zero_of_dual (F : FramedSub hM n p) (x : F.N)
    {y : EuclideanSpace ℝ (Fin (K + 1))} (hy : F.dual x y = 0) (i : Fin p) : ⟪F.v i x, y⟫ = 0 :=
  inner_eq_zero_of_dualOf_eq_zero (F.indep x) hy i

theorem dual_eq_zero_of_mem_tangentN (F : FramedSub hM n p) (x : F.N)
    {y : EuclideanSpace ℝ (Fin (K + 1))} (hy : y ∈ tangentN hM F.hN x) : F.dual x y = 0 :=
  dualOf_eq_zero fun i => F.normal i x y hy

theorem dual_eq_zero_of_mem_orthogonal (F : FramedSub hM n p) (x : F.N)
    {y : EuclideanSpace ℝ (Fin (K + 1))} (hy : y ∈ (tangentM hM x.1)ᗮ) : F.dual x y = 0 :=
  dualOf_eq_zero fun i => Submodule.inner_right_of_mem_orthogonal (F.tangent i x) hy

theorem surjective_dual (F : FramedSub hM n p) (x : F.N) : Surjective (F.dual x) :=
  surjective_dualOf (F.indep x)

/-- The dual forms depend smoothly on the point of `N`. -/
theorem contMDiff_dual (F : FramedSub hM n p) :
    letI := hM.chartedSpace; haveI := hM.isManifold; letI := F.hN.chartedSpace;
    ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
      𝓘(ℝ, EuclideanSpace ℝ (Fin (K + 1)) →L[ℝ] EuclideanSpace ℝ (Fin p)) ∞ F.dual := by
  letI := hM.chartedSpace
  haveI := hM.isManifold
  letI := F.hN.chartedSpace
  haveI := F.hN.isManifold
  have hV : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, Fin p → EuclideanSpace ℝ (Fin (K + 1)))
      ∞ (fun x : F.N => fun i => F.v i x) :=
    contMDiff_pi_space.2 fun i => F.smooth i
  intro x
  exact (contDiffAt_dualOf (F.indep x)).comp_contMDiffAt
    (f := fun x : F.N => fun i => F.v i x) (hV x)

/-- **Transversality makes the pair of dual forms surjective** at the points of `N ∩ N'`. -/
theorem surjective_pairA_of_transverse (F : FramedSub hM n p) (G : FramedSub hM n' q)
    (htr : Transverse hM F.hN G.hN) (x : M) (hx : x ∈ F.N) (hx' : x ∈ G.N) :
    Surjective (pairA (fun i => F.v i ⟨x, hx⟩) (fun j => G.v j ⟨x, hx'⟩)) := by
  refine surjective_pairA (F.indep _) (G.indep _) ?_
  rw [eq_top_iff]
  have h1 : (tangentN hM F.hN ⟨x, hx⟩ ⊔ tangentN hM G.hN ⟨x, hx'⟩) ⊔ (tangentM hM x)ᗮ = ⊤ := by
    rw [htr x hx hx']
    exact Submodule.sup_orthogonal_of_hasOrthogonalProjection
  rw [← h1]
  refine sup_le (sup_le ?_ ?_) ?_
  · intro y hy
    exact Submodule.mem_sup_left (LinearMap.mem_ker.2 (dual_eq_zero_of_mem_tangentN F _ hy))
  · intro y hy
    exact Submodule.mem_sup_right (LinearMap.mem_ker.2 (dual_eq_zero_of_mem_tangentN G _ hy))
  · intro y hy
    exact Submodule.mem_sup_left (LinearMap.mem_ker.2 (dual_eq_zero_of_mem_orthogonal F
      ⟨x, hx⟩ hy))

/-- The framing vectors of the intersection. -/
def interFrame (F : FramedSub hM n p) (G : FramedSub hM n' q) (i : Fin (p + q))
    (x : ↥(F.N ∩ G.N)) : EuclideanSpace ℝ (Fin (K + 1)) :=
  interV (fun j => F.v j ⟨x.1, x.2.1⟩) (fun j => G.v j ⟨x.1, x.2.2⟩) i

theorem contMDiff_interFrame (F : FramedSub hM n p) (G : FramedSub hM n' q)
    (htr : Transverse hM F.hN G.hN) (hr : r + (p + q) = m) (i : Fin (p + q)) :
    letI := hM.chartedSpace; haveI := hM.isManifold;
    letI := (isSliceSubmanifold_inter hM F.hN G.hN F.dim G.dim hr htr).chartedSpace;
    ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin r)) 𝓘(ℝ, EuclideanSpace ℝ (Fin (K + 1))) ∞
      (interFrame F G i) := by
  letI := hM.chartedSpace
  haveI := hM.isManifold
  have hS := isSliceSubmanifold_inter hM F.hN G.hN F.dim G.dim hr htr
  letI := hS.chartedSpace
  haveI := hS.isManifold
  letI := F.hN.chartedSpace
  haveI := F.hN.isManifold
  letI := G.hN.chartedSpace
  haveI := G.hN.isManifold
  have hincF : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin r)) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞
      (fun x : ↥(F.N ∩ G.N) => (⟨x.1, x.2.1⟩ : F.N)) :=
    F.hN.contMDiff_codRestrict hS.contMDiff_val (fun x => x.2.1)
  have hincG : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin r)) 𝓘(ℝ, EuclideanSpace ℝ (Fin n')) ∞
      (fun x : ↥(F.N ∩ G.N) => (⟨x.1, x.2.2⟩ : G.N)) :=
    G.hN.contMDiff_codRestrict hS.contMDiff_val (fun x => x.2.2)
  have hVF : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin r)) 𝓘(ℝ, Fin p → EuclideanSpace ℝ (Fin (K + 1))) ∞
      (fun x : ↥(F.N ∩ G.N) => fun j => F.v j ⟨x.1, x.2.1⟩) :=
    contMDiff_pi_space.2 fun j => (F.smooth j).comp hincF
  have hVG : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin r)) 𝓘(ℝ, Fin q → EuclideanSpace ℝ (Fin (K + 1))) ∞
      (fun x : ↥(F.N ∩ G.N) => fun j => G.v j ⟨x.1, x.2.2⟩) :=
    contMDiff_pi_space.2 fun j => (G.smooth j).comp hincG
  intro x
  exact (contDiffAt_interV (F.indep _) (G.indep _)
    (surjective_pairA_of_transverse F G htr x.1 x.2.1 x.2.2) i).comp_contMDiffAt
    (f := fun x : ↥(F.N ∩ G.N) => ((fun j => F.v j ⟨x.1, x.2.1⟩), (fun j => G.v j ⟨x.1, x.2.2⟩)))
    ((hVF.prodMk_space hVG) x)

end InterProd

open InterProd in
/-- **The transverse intersection of framed submanifolds**, framed by the vectors `w_k` normal to
`N ∩ N'`, tangent to `M`, with `(α_F w_k, α_G w_k)` the standard basis of `ℝᵖ × ℝ^q`:
`w_k := pinv (A x) e_k`, `A x := (α_F x, α_G x)` read in `ℝ^{p+q}`. -/
def _root_.Milnor.Framed.FramedSub.inter (F : FramedSub hM n p) (G : FramedSub hM n' q)
    (htr : Transverse hM F.hN G.hN) (hr : r + (p + q) = m) : FramedSub hM r (p + q) where
  N := F.N ∩ G.N
  hN := isSliceSubmanifold_inter hM F.hN G.hN F.dim G.dim hr htr
  dim := hr
  compact := F.compact.inter_right G.compact.isClosed
  v := interFrame F G
  smooth := contMDiff_interFrame F G htr hr
  tangent i x := by
    refine interV_mem (fun y hy => pairA_eq_zero_iff.2 ⟨?_, ?_⟩) i
    · exact dual_eq_zero_of_mem_orthogonal F ⟨x.1, x.2.1⟩ hy
    · exact dual_eq_zero_of_mem_orthogonal G ⟨x.1, x.2.2⟩ hy
  normal i x y hy := by
    rw [tangentN_inter hM F.hN G.hN F.dim G.dim hr htr x] at hy
    exact inner_interV_eq_zero (pairA_eq_zero_iff.2
      ⟨dual_eq_zero_of_mem_tangentN F _ hy.1, dual_eq_zero_of_mem_tangentN G _ hy.2⟩) i
  indep x := linearIndependent_interV (surjective_pairA_of_transverse F G htr x.1 x.2.1 x.2.2)

namespace InterProd

theorem inter_N (F : FramedSub hM n p) (G : FramedSub hM n' q) (htr : Transverse hM F.hN G.hN)
    (hr : r + (p + q) = m) : (F.inter G htr hr).N = F.N ∩ G.N := rfl

/-- **The defining property of the intersection framing**: `(α_F w_k, α_G w_k)` is the `k`-th
standard basis vector of `ℝᵖ × ℝ^q`. -/
theorem dual_inter_v (F : FramedSub hM n p) (G : FramedSub hM n' q)
    (htr : Transverse hM F.hN G.hN) (hr : r + (p + q) = m) (k : Fin (p + q))
    (x : ↥(F.N ∩ G.N)) :
    (F.dual ⟨x.1, x.2.1⟩ ((F.inter G htr hr).v k x),
      G.dual ⟨x.1, x.2.2⟩ ((F.inter G htr hr).v k x)) =
      EuclideanSpace.finAddEquivProd (EuclideanSpace.single k 1) := by
  have h := pairA_interV (surjective_pairA_of_transverse F G htr x.1 x.2.1 x.2.2) k
  rw [← h]
  exact (ContinuousLinearEquiv.apply_symm_apply _ _).symm

end InterProd

/-! ### Stereographic coordinates from the south pole -/

namespace InterProd

section stereo

variable {p : ℕ}

/-- Dropping the last coordinate, `ℝ^{p+1} → ℝᵖ` (as a linear map). -/
def dropₗ : EuclideanSpace ℝ (Fin (p + 1)) →ₗ[ℝ] EuclideanSpace ℝ (Fin p) where
  toFun u := WithLp.toLp 2 (fun i => u (Fin.castSucc i))
  map_add' u v := by ext i; simp
  map_smul' c u := by ext i; simp

/-- Dropping the last coordinate, `ℝ^{p+1} → ℝᵖ`. -/
def drop : EuclideanSpace ℝ (Fin (p + 1)) →L[ℝ] EuclideanSpace ℝ (Fin p) :=
  LinearMap.toContinuousLinearMap dropₗ

theorem drop_apply (u : EuclideanSpace ℝ (Fin (p + 1))) (i : Fin p) :
    drop u i = u (Fin.castSucc i) := rfl

theorem drop_ι (s : EuclideanSpace ℝ (Fin p)) : drop (ι s) = s := by
  ext i
  rw [drop_apply, ι_apply_castSucc]

theorem drop_northV : drop (northV : EuclideanSpace ℝ (Fin (p + 1))) = 0 := by
  ext i
  rw [drop_apply, northV]
  simp [Fin.castSucc_ne_last]

theorem northV_last : (northV : EuclideanSpace ℝ (Fin (p + 1))) (Fin.last p) = 1 := by
  simp [northV]

theorem eq_ι_drop_add (u : EuclideanSpace ℝ (Fin (p + 1))) :
    u = ι (drop u) + u (Fin.last p) • northV := by
  ext j
  refine Fin.lastCases ?_ (fun i => ?_) j
  · simp [ι_apply_last, northV_last]
  · simp only [PiLp.add_apply, PiLp.smul_apply, ι_apply_castSucc, drop_apply, northV,
      smul_eq_mul]
    simp [Fin.castSucc_ne_last]

theorem norm_sq_eq_drop (u : EuclideanSpace ℝ (Fin (p + 1))) :
    ‖u‖ ^ 2 = ‖drop u‖ ^ 2 + u (Fin.last p) ^ 2 := by
  conv_lhs => rw [eq_ι_drop_add u]
  rw [norm_add_sq_real, real_inner_smul_right, inner_ι_northV, mul_zero, mul_zero, add_zero,
    norm_ι, norm_smul, norm_northV, mul_one, Real.norm_eq_abs, sq_abs]

theorem last_sq_le (a : Sph p) : a.1 (Fin.last p) ^ 2 ≤ 1 := by
  have h := norm_sq_eq_drop a.1
  rw [mem_iff_norm.1 a.2] at h
  nlinarith [sq_nonneg ‖drop a.1‖]

theorem neg_one_le_last (a : Sph p) : -1 ≤ a.1 (Fin.last p) := by
  nlinarith [last_sq_le a]

theorem eq_south_of_last (a : Sph p) (h : a.1 (Fin.last p) = -1) : a = south := by
  have h1 := norm_sq_eq_drop a.1
  rw [mem_iff_norm.1 a.2, h] at h1
  have h2 : ‖drop a.1‖ = 0 := by nlinarith [norm_nonneg (drop a.1)]
  have h3 : drop a.1 = 0 := norm_eq_zero.1 h2
  apply Subtype.ext
  rw [south_val, eq_ι_drop_add a.1, h3, h, map_zero, zero_add, neg_one_smul]

theorem neg_one_lt_last {a : Sph p} (ha : a ≠ south) : -1 < a.1 (Fin.last p) :=
  lt_of_le_of_ne (neg_one_le_last a) fun h => ha (eq_south_of_last a h.symm)

/-- Stereographic projection from the south pole, `Sᵖ ∖ {south} → ℝᵖ`. -/
def sig (a : Sph p) : EuclideanSpace ℝ (Fin p) := (1 + a.1 (Fin.last p))⁻¹ • drop a.1

theorem sig_north : sig (north : Sph p) = 0 := by
  rw [sig, north_val, drop_northV, smul_zero]

theorem eq_north_of_sig_eq_zero {a : Sph p} (ha : a ≠ south) (h : sig a = 0) : a = north := by
  have hl := neg_one_lt_last ha
  have hne : (1 + a.1 (Fin.last p))⁻¹ ≠ 0 := inv_ne_zero (by linarith)
  have h0 : drop a.1 = 0 := (smul_eq_zero.1 h).resolve_left hne
  have h1 := norm_sq_eq_drop a.1
  rw [mem_iff_norm.1 a.2, h0, norm_zero] at h1
  have h2 : a.1 (Fin.last p) = 1 := by nlinarith
  apply Subtype.ext
  rw [north_val, eq_ι_drop_add a.1, h0, h2, map_zero, zero_add, one_smul]

theorem sig_eq_zero_iff {a : Sph p} (ha : a ≠ south) : sig a = 0 ↔ a = north :=
  ⟨eq_north_of_sig_eq_zero ha, fun h => by rw [h, sig_north]⟩

theorem norm_sig_sq_mul {a : Sph p} (ha : a ≠ south) :
    ‖sig a‖ ^ 2 * (1 + a.1 (Fin.last p)) = 1 - a.1 (Fin.last p) := by
  have hl := neg_one_lt_last ha
  have hpos : 0 < 1 + a.1 (Fin.last p) := by linarith
  have h1 := norm_sq_eq_drop a.1
  rw [mem_iff_norm.1 a.2] at h1
  rw [sig, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, inv_pow]
  field_simp
  nlinarith

/-- Near the south pole, the stereographic coordinate is large. -/
theorem lt_norm_sig {a : Sph p} (ha : a ≠ south) {C : ℝ} (hC : 0 ≤ C)
    (h : a.1 (Fin.last p) < -1 + 1 / (C ^ 2 + 1)) : C < ‖sig a‖ := by
  have hl := neg_one_lt_last ha
  have h1 := norm_sig_sq_mul ha
  have hd : 1 / (C ^ 2 + 1) ≤ 1 := by
    rw [div_le_one (by positivity)]; nlinarith
  have hpos : 0 < 1 + a.1 (Fin.last p) := by linarith
  have hlt : 1 + a.1 (Fin.last p) < 1 / (C ^ 2 + 1) := by linarith
  have hs : 0 ≤ ‖sig a‖ ^ 2 := sq_nonneg _
  have h2 : 1 < ‖sig a‖ ^ 2 * (1 / (C ^ 2 + 1)) := by nlinarith
  have h3 : C ^ 2 + 1 < ‖sig a‖ ^ 2 := by
    rw [mul_one_div, lt_div_iff₀ (by positivity), one_mul] at h2
    exact h2
  nlinarith [norm_nonneg (sig a)]

theorem contMDiffAt_sig {a : Sph p} (ha : a ≠ south) :
    ContMDiffAt 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) ∞ sig a := by
  have hl := neg_one_lt_last ha
  have hg : ContDiffAt ℝ ∞ (fun u : EuclideanSpace ℝ (Fin (p + 1)) =>
      (1 + u (Fin.last p))⁻¹ • drop u) a.1 := by
    have h1 : ContDiff ℝ ∞ (fun u : EuclideanSpace ℝ (Fin (p + 1)) => 1 + u (Fin.last p)) :=
      contDiff_const.add (EuclideanSpace.proj (Fin.last p) :
        EuclideanSpace ℝ (Fin (p + 1)) →L[ℝ] ℝ).contDiff
    exact (h1.contDiffAt.inv (by linarith)).smul drop.contDiff.contDiffAt
  exact hg.contMDiffAt.comp a contMDiff_val.contMDiffAt

/-- Inverse stereographic projection `ℝᵖ → Sᵖ ∖ {south}`. -/
def tauV (s : EuclideanSpace ℝ (Fin p)) : EuclideanSpace ℝ (Fin (p + 1)) :=
  (2 / (‖s‖ ^ 2 + 1)) • ι s + ((1 - ‖s‖ ^ 2) / (‖s‖ ^ 2 + 1)) • northV

theorem tauV_mem (s : EuclideanSpace ℝ (Fin p)) : tauV s ∈ Sph p := by
  rw [mem_iff_norm]
  have hd : ‖s‖ ^ 2 + 1 ≠ 0 := by positivity
  have h : ‖tauV s‖ ^ 2 = 1 := by
    rw [tauV, norm_add_sq_real, real_inner_smul_left, real_inner_smul_right, inner_ι_northV,
      norm_smul, norm_smul, norm_ι, norm_northV, Real.norm_eq_abs, Real.norm_eq_abs, mul_pow,
      mul_pow, sq_abs, sq_abs]
    field_simp
    ring
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) (by norm_num)).1 h

/-- Inverse stereographic projection, as a map to the sphere. -/
def tau (s : EuclideanSpace ℝ (Fin p)) : Sph p := ⟨tauV s, tauV_mem s⟩

theorem tau_zero : tau (0 : EuclideanSpace ℝ (Fin p)) = north := by
  apply Subtype.ext
  show tauV 0 = northV
  simp [tauV]

theorem sig_tau (s : EuclideanSpace ℝ (Fin p)) : sig (tau s) = s := by
  have hd : ‖s‖ ^ 2 + 1 ≠ 0 := by positivity
  have hlast : (tau s).1 (Fin.last p) = (1 - ‖s‖ ^ 2) / (‖s‖ ^ 2 + 1) := by
    show tauV s (Fin.last p) = _
    simp only [tauV, PiLp.add_apply, PiLp.smul_apply, ι_apply_last, northV_last, smul_eq_mul,
      mul_zero, zero_add, mul_one]
  have hdrop : drop (tau s).1 = (2 / (‖s‖ ^ 2 + 1)) • s := by
    show drop (tauV s) = _
    rw [tauV, map_add, map_smul, map_smul, drop_ι, drop_northV, smul_zero, add_zero]
  rw [sig, hlast, hdrop, smul_smul]
  have h1 : (1 + (1 - ‖s‖ ^ 2) / (‖s‖ ^ 2 + 1))⁻¹ * (2 / (‖s‖ ^ 2 + 1)) = 1 := by
    field_simp
    ring
  rw [h1, one_smul]

theorem contMDiff_tau :
    ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) ∞
      (tau (p := p)) := by
  have h : ContDiff ℝ ∞ (tauV (p := p)) := by
    have hs : ContDiff ℝ ∞ (fun s : EuclideanSpace ℝ (Fin p) => ‖s‖ ^ 2) := contDiff_norm_sq ℝ
    have hd : ∀ s : EuclideanSpace ℝ (Fin p), ‖s‖ ^ 2 + 1 ≠ 0 := fun s => by positivity
    have h1 : ContDiff ℝ ∞ (fun s : EuclideanSpace ℝ (Fin p) => 2 / (‖s‖ ^ 2 + 1)) :=
      contDiff_const.div (hs.add contDiff_const) hd
    have h2 : ContDiff ℝ ∞ (fun s : EuclideanSpace ℝ (Fin p) => (1 - ‖s‖ ^ 2) / (‖s‖ ^ 2 + 1)) :=
      (contDiff_const.sub hs).div (hs.add contDiff_const) hd
    exact (h1.smul ι.contDiff).add (h2.smul contDiff_const)
  exact (sphS p).contMDiff_codRestrict (F := tauV) (contMDiff_iff_contDiff.2 h) tauV_mem

/-- `dσ_north ∘ dτ_0 = id`. -/
theorem mfd_sig_comp_mfd_tau :
    (mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) (sig (p := p)) north).comp
      (mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) (tau (p := p)) 0) =
      ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin p)) := by
  have hn : (north : Sph p) ≠ south := fun h => south_ne_north h.symm
  have h1 : HasMFDerivAt 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) sig
      ((tau (p := p)) 0) (mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) (sig (p := p)) north) := by
    rw [tau_zero]
    exact hasMFDerivAt_mfd ((contMDiffAt_sig hn).mdifferentiableAt (by simp))
  have h2 : HasMFDerivAt 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) (tau (p := p)) 0
      (mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) (tau (p := p)) 0) :=
    hasMFDerivAt_mfd (contMDiff_tau.mdifferentiableAt (by simp))
  have h3 := h1.comp (0 : EuclideanSpace ℝ (Fin p)) h2
  have h4 : sig ∘ tau = (id : EuclideanSpace ℝ (Fin p) → EuclideanSpace ℝ (Fin p)) :=
    funext sig_tau
  rw [h4] at h3
  exact hasMFDerivAt_unique h3 (hasMFDerivAt_id (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin p))) _)

theorem bijective_mfd_sig :
    Bijective (mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) (sig (p := p)) north) := by
  have hsurj : Surjective (mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) 𝓘(ℝ, EuclideanSpace ℝ (Fin p))
      (sig (p := p)) north) := fun v =>
    ⟨mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) (tau (p := p)) 0 v, by
      have := congrArg (fun L : EuclideanSpace ℝ (Fin p) →L[ℝ] EuclideanSpace ℝ (Fin p) => L v)
        (mfd_sig_comp_mfd_tau (p := p))
      simpa using this⟩
  exact ⟨LinearMap.injective_iff_surjective (f := (mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin p))
    𝓘(ℝ, EuclideanSpace ℝ (Fin p)) (sig (p := p)) north : EuclideanSpace ℝ (Fin p) →ₗ[ℝ]
      EuclideanSpace ℝ (Fin p))) |>.2 hsurj, hsurj⟩

/-- `dσ_north` as an equivalence. -/
def sigE (p : ℕ) : EuclideanSpace ℝ (Fin p) ≃L[ℝ] EuclideanSpace ℝ (Fin p) :=
  ContinuousLinearEquiv.ofBijective
    (mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) (sig (p := p)) north)
    (LinearMap.ker_eq_bot.2 (bijective_mfd_sig (p := p)).1)
    (LinearMap.range_eq_top.2 (bijective_mfd_sig (p := p)).2)

theorem sigE_apply (v : EuclideanSpace ℝ (Fin p)) :
    sigE p v = mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) (sig (p := p)) north v := rfl

end stereo

/-! ### The map `μ : Sᵖ × S^q → S^{p+q}` -/

section mu

variable {p q : ℕ}

/-- `E_Γ = (d stdMap₀)⁻¹ ∘ Γ ∘ (dσ_north × dσ_north)⁻¹`, so that `dμ_(north, north) = Γ`. -/
def muE (Γ : (EuclideanSpace ℝ (Fin p) × EuclideanSpace ℝ (Fin q)) ≃L[ℝ]
    EuclideanSpace ℝ (Fin (p + q))) :
    (EuclideanSpace ℝ (Fin p) × EuclideanSpace ℝ (Fin q)) ≃L[ℝ] EuclideanSpace ℝ (Fin (p + q)) :=
  ((sigE p).prodCongr (sigE q)).symm.trans (Γ.trans De.symm)

open Classical in
/-- **The map `μ : Sᵖ × S^q → S^{p+q}`**: `μ (a, b) = stdMap (E_Γ (σ a, σ b))` if neither `a`
nor `b` is the south pole, and `μ (a, b) = south` otherwise. -/
def mu (Γ : (EuclideanSpace ℝ (Fin p) × EuclideanSpace ℝ (Fin q)) ≃L[ℝ]
    EuclideanSpace ℝ (Fin (p + q))) (x : Sph p × Sph q) : Sph (p + q) :=
  if x.1 ≠ south ∧ x.2 ≠ south then stdMap (muE Γ (sig x.1, sig x.2)) else south

variable (Γ : (EuclideanSpace ℝ (Fin p) × EuclideanSpace ℝ (Fin q)) ≃L[ℝ]
    EuclideanSpace ℝ (Fin (p + q)))

theorem mu_of_ne {x : Sph p × Sph q} (hx : x.1 ≠ south ∧ x.2 ≠ south) :
    mu Γ x = stdMap (muE Γ (sig x.1, sig x.2)) := by
  classical
  rw [mu, if_pos hx]

theorem mu_of_not {x : Sph p × Sph q} (hx : ¬(x.1 ≠ south ∧ x.2 ≠ south)) : mu Γ x = south := by
  classical
  rw [mu, if_neg hx]

theorem north_ne_south' {p : ℕ} : (north : Sph p) ≠ south := fun h => south_ne_north h.symm

theorem mu_eq_north_iff (x : Sph p × Sph q) : mu Γ x = north ↔ x.1 = north ∧ x.2 = north := by
  constructor
  · intro h
    by_cases hx : x.1 ≠ south ∧ x.2 ≠ south
    · rw [mu_of_ne Γ hx, stdMap_eq_north_iff, (muE Γ).map_eq_zero_iff, Prod.mk_eq_zero] at h
      exact ⟨eq_north_of_sig_eq_zero hx.1 h.1, eq_north_of_sig_eq_zero hx.2 h.2⟩
    · rw [mu_of_not Γ hx] at h
      exact absurd h south_ne_north
  · rintro ⟨h1, h2⟩
    have hx : x.1 ≠ south ∧ x.2 ≠ south := by
      rw [h1, h2]; exact ⟨north_ne_south', north_ne_south'⟩
    rw [mu_of_ne Γ hx, h1, h2, sig_north, sig_north, Prod.mk_zero_zero, map_zero, stdMap_zero]

theorem mu_north : mu Γ (north, north) = north := (mu_eq_north_iff Γ _).2 ⟨rfl, rfl⟩

theorem eventually_mu_eq_south {x : Sph p × Sph q} (hx : ¬(x.1 ≠ south ∧ x.2 ≠ south)) :
    ∀ᶠ y in 𝓝 x, mu Γ y = south := by
  obtain ⟨C, hC⟩ : ∃ C : NNReal, AntilipschitzWith C (muE Γ) := ⟨_, (muE Γ).antilipschitz⟩
  have key : ∀ w : EuclideanSpace ℝ (Fin p) × EuclideanSpace ℝ (Fin q),
      ((C : ℝ) < ‖w.1‖ ∨ (C : ℝ) < ‖w.2‖) → 1 / 2 ≤ ‖muE Γ w‖ := by
    intro w hw
    have hC0 : (0 : ℝ) ≤ C := C.2
    have h1 : ‖w‖ ≤ C * ‖muE Γ w‖ := by
      have := hC.le_mul_dist w 0
      simpa [dist_zero_right] using this
    have h2 : (C : ℝ) < ‖w‖ := by
      rcases hw with hw | hw
      · exact hw.trans_le (norm_fst_le w)
      · exact hw.trans_le (norm_snd_le w)
    by_contra hlt
    push Not at hlt
    nlinarith [norm_nonneg (muE Γ w)]
  have hδ : (0 : ℝ) < 1 / ((C : ℝ) ^ 2 + 1) := by positivity
  have hlast : (south : Sph p).1 (Fin.last p) = -1 := by
    rw [south_val, PiLp.neg_apply, northV_last]
  have hlast' : (south : Sph q).1 (Fin.last q) = -1 := by
    rw [south_val, PiLp.neg_apply, northV_last]
  rw [not_and_or, not_not, not_not] at hx
  rcases hx with hx | hx
  · have hopen : IsOpen {y : Sph p × Sph q | y.1.1 (Fin.last p) < -1 + 1 / ((C : ℝ) ^ 2 + 1)} :=
      isOpen_lt ((EuclideanSpace.proj (Fin.last p) : EuclideanSpace ℝ (Fin (p + 1)) →L[ℝ] ℝ).continuous.comp
        (continuous_subtype_val.comp continuous_fst)) continuous_const
    have hmem : x ∈ {y : Sph p × Sph q | y.1.1 (Fin.last p) < -1 + 1 / ((C : ℝ) ^ 2 + 1)} := by
      show x.1.1 (Fin.last p) < _
      rw [hx, hlast]; linarith
    filter_upwards [hopen.mem_nhds hmem] with y hy
    by_cases hy' : y.1 ≠ south ∧ y.2 ≠ south
    · rw [mu_of_ne Γ hy']
      exact stdMap_of_half_le (key _ (Or.inl (lt_norm_sig hy'.1 C.2 hy)))
    · exact mu_of_not Γ hy'
  · have hopen : IsOpen {y : Sph p × Sph q | y.2.1 (Fin.last q) < -1 + 1 / ((C : ℝ) ^ 2 + 1)} :=
      isOpen_lt ((EuclideanSpace.proj (Fin.last q) : EuclideanSpace ℝ (Fin (q + 1)) →L[ℝ] ℝ).continuous.comp
        (continuous_subtype_val.comp continuous_snd)) continuous_const
    have hmem : x ∈ {y : Sph p × Sph q | y.2.1 (Fin.last q) < -1 + 1 / ((C : ℝ) ^ 2 + 1)} := by
      show x.2.1 (Fin.last q) < _
      rw [hx, hlast']; linarith
    filter_upwards [hopen.mem_nhds hmem] with y hy
    by_cases hy' : y.1 ≠ south ∧ y.2 ≠ south
    · rw [mu_of_ne Γ hy']
      exact stdMap_of_half_le (key _ (Or.inr (lt_norm_sig hy'.2 C.2 hy)))
    · exact mu_of_not Γ hy'

theorem isOpen_ne_south :
    IsOpen {y : Sph p × Sph q | y.1 ≠ south ∧ y.2 ≠ south} :=
  (isOpen_ne.preimage continuous_fst).inter (isOpen_ne.preimage continuous_snd)

theorem contMDiff_mu :
    ContMDiff (𝓘(ℝ, EuclideanSpace ℝ (Fin p)).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin q)))
      𝓘(ℝ, EuclideanSpace ℝ (Fin (p + q))) ∞ (mu Γ) := by
  intro x
  by_cases hx : x.1 ≠ south ∧ x.2 ≠ south
  · have h1 : ContMDiffAt (𝓘(ℝ, EuclideanSpace ℝ (Fin p)).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin q)))
        𝓘(ℝ, EuclideanSpace ℝ (Fin p)) ∞ (fun y : Sph p × Sph q => sig y.1) x :=
      (contMDiffAt_sig hx.1).comp x contMDiffAt_fst
    have h2 : ContMDiffAt (𝓘(ℝ, EuclideanSpace ℝ (Fin p)).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin q)))
        𝓘(ℝ, EuclideanSpace ℝ (Fin q)) ∞ (fun y : Sph p × Sph q => sig y.2) x :=
      (contMDiffAt_sig hx.2).comp x contMDiffAt_snd
    have h3 : ContMDiffAt (𝓘(ℝ, EuclideanSpace ℝ (Fin p)).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin q)))
        𝓘(ℝ, EuclideanSpace ℝ (Fin (p + q))) ∞
        (fun y : Sph p × Sph q => muE Γ (sig y.1, sig y.2)) x :=
      (muE Γ).contDiff.contMDiff.contMDiffAt.comp x (h1.prodMk_space h2)
    have h4 := (contMDiff_stdMap (p := p + q)).contMDiffAt.comp x h3
    refine h4.congr_of_eventuallyEq ?_
    filter_upwards [isOpen_ne_south.mem_nhds hx] with y hy
    exact mu_of_ne Γ hy
  · exact contMDiffAt_const.congr_of_eventuallyEq (eventually_mu_eq_south Γ hx)

/-- **The derivative of `μ` at `(north, north)` is `Γ`.** -/
theorem hasMFDerivAt_mu :
    HasMFDerivAt (𝓘(ℝ, EuclideanSpace ℝ (Fin p)).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin q)))
      𝓘(ℝ, EuclideanSpace ℝ (Fin (p + q))) (mu Γ) (north, north)
      (Γ : EuclideanSpace ℝ (Fin p) × EuclideanSpace ℝ (Fin q) →L[ℝ]
        EuclideanSpace ℝ (Fin (p + q))) := by
  have h1 : HasMFDerivAt (𝓘(ℝ, EuclideanSpace ℝ (Fin p)).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin q)))
      𝓘(ℝ, EuclideanSpace ℝ (Fin p)) ((sig (p := p)) ∘ Prod.fst) (north, north)
      ((mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) (sig (p := p))
        north).comp (ContinuousLinearMap.fst ℝ (EuclideanSpace ℝ (Fin p))
          (EuclideanSpace ℝ (Fin q)))) :=
    (hasMFDerivAt_mfd ((contMDiffAt_sig (north_ne_south' (p := p))).mdifferentiableAt
      (by simp))).comp (north, north) (hasMFDerivAt_fst ((north, north) : Sph p × Sph q))
  have h2 : HasMFDerivAt (𝓘(ℝ, EuclideanSpace ℝ (Fin p)).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin q)))
      𝓘(ℝ, EuclideanSpace ℝ (Fin q)) ((sig (p := q)) ∘ Prod.snd) (north, north)
      ((mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin q)) 𝓘(ℝ, EuclideanSpace ℝ (Fin q)) (sig (p := q))
        north).comp (ContinuousLinearMap.snd ℝ (EuclideanSpace ℝ (Fin p))
          (EuclideanSpace ℝ (Fin q)))) :=
    (hasMFDerivAt_mfd ((contMDiffAt_sig (north_ne_south' (p := q))).mdifferentiableAt
      (by simp))).comp (north, north) (hasMFDerivAt_snd ((north, north) : Sph p × Sph q))
  have h3 := Transversality.hasMFDerivAt_prodMk_space h1 h2
  have h4 : HasMFDerivAt (𝓘(ℝ, EuclideanSpace ℝ (Fin p)).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin q)))
      𝓘(ℝ, EuclideanSpace ℝ (Fin (p + q)))
      (fun y : Sph p × Sph q => muE Γ (sig y.1, sig y.2)) (north, north)
      ((muE Γ : EuclideanSpace ℝ (Fin p) × EuclideanSpace ℝ (Fin q) →L[ℝ]
        EuclideanSpace ℝ (Fin (p + q))).comp
        (((mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) (sig (p := p))
          north).comp (ContinuousLinearMap.fst ℝ (EuclideanSpace ℝ (Fin p))
            (EuclideanSpace ℝ (Fin q)))).prod
        ((mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin q)) 𝓘(ℝ, EuclideanSpace ℝ (Fin q)) (sig (p := q))
          north).comp (ContinuousLinearMap.snd ℝ (EuclideanSpace ℝ (Fin p))
            (EuclideanSpace ℝ (Fin q)))))) :=
    (muE Γ).hasFDerivAt.hasMFDerivAt.comp (north, north) h3
  have h5 : HasMFDerivAt 𝓘(ℝ, EuclideanSpace ℝ (Fin (p + q))) 𝓘(ℝ, EuclideanSpace ℝ (Fin (p + q)))
      stdMap (muE Γ (sig (north : Sph p), sig (north : Sph q)))
      (mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin (p + q))) 𝓘(ℝ, EuclideanSpace ℝ (Fin (p + q)))
        (stdMap (p := p + q)) 0) := by
    rw [sig_north, sig_north, Prod.mk_zero_zero, map_zero]
    exact hasMFDerivAt_mfd (contMDiff_stdMap.mdifferentiableAt (by simp))
  have h6 := h5.comp (north, north) h4
  have hev : mu Γ =ᶠ[𝓝 (north, north)]
      (stdMap ∘ fun y : Sph p × Sph q => muE Γ (sig y.1, sig y.2)) := by
    filter_upwards [isOpen_ne_south.mem_nhds ⟨north_ne_south', north_ne_south'⟩] with y hy
    exact mu_of_ne Γ hy
  have h7 := h6.congr_of_eventuallyEq hev
  refine h7.congr_mfderiv ?_
  refine ContinuousLinearMap.ext fun v => ?_
  show mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin (p + q))) 𝓘(ℝ, EuclideanSpace ℝ (Fin (p + q)))
      (stdMap (p := p + q)) 0 (muE Γ
        (mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) (sig (p := p)) north v.1,
         mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin q)) 𝓘(ℝ, EuclideanSpace ℝ (Fin q)) (sig (p := q)) north v.2)) =
    Γ v
  rw [← De_apply, ← sigE_apply, ← sigE_apply]
  simp [muE]
  rfl

theorem mfd_mu :
    mfd (𝓘(ℝ, EuclideanSpace ℝ (Fin p)).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin q)))
      𝓘(ℝ, EuclideanSpace ℝ (Fin (p + q))) (mu Γ) (north, north) =
      (Γ : EuclideanSpace ℝ (Fin p) × EuclideanSpace ℝ (Fin q) →L[ℝ]
        EuclideanSpace ℝ (Fin (p + q))) :=
  HasMFDerivAt.mfd_eq (hasMFDerivAt_mu Γ)

end mu

end InterProd

/-! ### The Pontryagin manifold of `μ ∘ (f, g)` is the transverse intersection -/

section pontMu

variable (hM) (hMc : IsCompact M) (hne : M.Nonempty)

namespace InterProd

/-- A vector orthogonal to the Pontryagin framing is in the kernel of `dF̃`. -/
theorem At_eq_zero_of_forall_inner {f : M → Sph p}
    (hf : letI := hM.chartedSpace; haveI := hM.isManifold;
      ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) ∞ f)
    {y : Sph p}
    (hy : letI := hM.chartedSpace; haveI := hM.isManifold;
      IsRegularValue 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) f y)
    {e : Fin p → EuclideanSpace ℝ (Fin p)} (he : LinearIndependent ℝ e) (x : f ⁻¹' {y})
    {t : EuclideanSpace ℝ (Fin (K + 1))} (ht : ∀ i, ⟪pontV hM hMc hne f y e i x, t⟫ = 0) :
    At hM hMc hne f y x.1.1 t = 0 := by
  obtain ⟨A, hA⟩ : ∃ A, At hM hMc hne f y x.1.1 = A := ⟨_, rfl⟩
  have hsurj : Surjective A := hA ▸ surjective_At hM hMc hne hf hy x.1.2 x.2
  obtain ⟨u, hu⟩ := isUnit_comp_adjoint hsurj
  have h1 : ContinuousLinearMap.adjoint A (A t) =
      pinv A ((A.comp (ContinuousLinearMap.adjoint A)) (A t)) := by
    show _ = ContinuousLinearMap.adjoint A (Ring.inverse (A.comp (ContinuousLinearMap.adjoint A))
      ((A.comp (ContinuousLinearMap.adjoint A)) (A t)))
    rw [← hu, Ring.inverse_unit, ← mul_apply_eq_comp, u.inv_mul, one_apply_eq_self]
  obtain ⟨c, hc⟩ := (basisCLM_bijective he).2 ((A.comp (ContinuousLinearMap.adjoint A)) (A t))
  have h2 : pinv A (basisCLM e c) = ∑ j, c j • pontV hM hMc hne f y e j x := by
    rw [basisCLM_apply, map_sum]
    simp only [map_smul]
    rw [← hA]
    rfl
  have h3 : ⟪A t, A t⟫ = 0 := by
    rw [← ContinuousLinearMap.adjoint_inner_right, h1, ← hc, h2, inner_sum]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [real_inner_smul_right, real_inner_comm, ht j, mul_zero]
  rw [hA]
  exact inner_self_eq_zero.1 h3

/-- **`dF̃_x = B ∘ α_F(x)`** along the Pontryagin manifold, `B eᵢ = bᵢ` the basis. -/
theorem At_eq_basisCLM_dual (hnp : n + p = m) {f : M → Sph p}
    (hf : letI := hM.chartedSpace; haveI := hM.isManifold;
      ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) ∞ f)
    {y : Sph p}
    (hy : letI := hM.chartedSpace; haveI := hM.isManifold;
      IsRegularValue 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) f y)
    {e : Fin p → EuclideanSpace ℝ (Fin p)} (he : LinearIndependent ℝ e) (x : f ⁻¹' {y})
    (z : EuclideanSpace ℝ (Fin (K + 1))) :
    At hM hMc hne f y x.1.1 z = basisCLM e ((pontryagin hM hMc hne hf hy hnp e he).dual x z) := by
  have hv : LinearIndependent ℝ (fun i => pontV hM hMc hne f y e i x) :=
    pontV_indep hM hMc hne hf hy he x
  have hα : (pontryagin hM hMc hne hf hy hnp e he).dual x =
      dualOf (fun i => pontV hM hMc hne f y e i x) := rfl
  rw [hα]
  obtain ⟨c, hc⟩ : ∃ c, dualOf (fun i => pontV hM hMc hne f y e i x) z = c := ⟨_, rfl⟩
  have ht : dualOf (fun i => pontV hM hMc hne f y e i x)
      (z - frameCLM (fun i => pontV hM hMc hne f y e i x) c) = 0 := by
    rw [map_sub, dualOf_frameCLM hv, hc, sub_self]
  have h0 : At hM hMc hne f y x.1.1 (z - frameCLM (fun i => pontV hM hMc hne f y e i x) c) = 0 :=
    At_eq_zero_of_forall_inner hM hMc hne hf hy he x
      (fun i => inner_eq_zero_of_dualOf_eq_zero hv ht i)
  have h1 : At hM hMc hne f y x.1.1 (frameCLM (fun i => pontV hM hMc hne f y e i x) c) =
      basisCLM e c := by
    rw [frameCLM_apply, map_sum, basisCLM_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul, At_pontV hM hMc hne hf hy e j x]
  have hz : z = frameCLM (fun i => pontV hM hMc hne f y e i x) c +
      (z - frameCLM (fun i => pontV hM hMc hne f y e i x) c) := by abel
  rw [hc]
  conv_lhs => rw [hz]
  rw [map_add, h0, add_zero, h1]

/-- **The chain rule for `μ ∘ (f, g)`**: `dF̃_{μ∘(f,g)} = Γ ∘ (dF̃_f, dF̃_g)` at common points of
`f⁻¹(north)` and `g⁻¹(north)`. -/
theorem At_mu {p q : ℕ} (Γ : (EuclideanSpace ℝ (Fin p) × EuclideanSpace ℝ (Fin q)) ≃L[ℝ]
      EuclideanSpace ℝ (Fin (p + q))) {f : M → Sph p} {g : M → Sph q}
    (hf : letI := hM.chartedSpace; haveI := hM.isManifold;
      ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) ∞ f)
    (hg : letI := hM.chartedSpace; haveI := hM.isManifold;
      ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 𝓘(ℝ, EuclideanSpace ℝ (Fin q)) ∞ g)
    {x : EuclideanSpace ℝ (Fin (K + 1))} (hx : x ∈ M) (hfx : f ⟨x, hx⟩ = north)
    (hgx : g ⟨x, hx⟩ = north) :
    At hM hMc hne (fun z => mu Γ (f z, g z)) north x =
      (Γ : EuclideanSpace ℝ (Fin p) × EuclideanSpace ℝ (Fin q) →L[ℝ]
        EuclideanSpace ℝ (Fin (p + q))).comp
        ((At hM hMc hne f north x).prod (At hM hMc hne g north x)) := by
  letI := hM.chartedSpace
  haveI := hM.isManifold
  have hsrc : f ⟨x, hx⟩ ∈ (extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) north).source := by
    rw [hfx]; exact mem_extChartAt_source north
  have hsrc' : g ⟨x, hx⟩ ∈ (extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin q)) north).source := by
    rw [hgx]; exact mem_extChartAt_source north
  have hxW : x ∈ Wt hM hMc hne f north := mem_Wt_of_mem hM hMc hne hx hsrc
  have hxW' : x ∈ Wt hM hMc hne g north := mem_Wt_of_mem hM hMc hne hx hsrc'
  have hev : Ft hM hMc hne (fun z => mu Γ (f z, g z)) north =ᶠ[𝓝 x]
      (writtenInExtChartAt (𝓘(ℝ, EuclideanSpace ℝ (Fin p)).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin q)))
        𝓘(ℝ, EuclideanSpace ℝ (Fin (p + q))) ((north, north) : Sph p × Sph q) (mu Γ)) ∘
        (fun z => (Ft hM hMc hne f north z, Ft hM hMc hne g north z)) := by
    filter_upwards [(isOpen_Wt hM hMc hne hf).mem_nhds hxW,
      (isOpen_Wt hM hMc hne hg).mem_nhds hxW'] with z hz hz'
    simp only [Function.comp, Ft, writtenInExtChartAt, extChartAt_prod, PartialEquiv.prod_symm,
      PartialEquiv.prod_coe]
    rw [mu_north Γ, (extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) north).left_inv hz.2,
      (extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin q)) north).left_inv hz'.2]
  have hD : HasFDerivAt (writtenInExtChartAt (𝓘(ℝ, EuclideanSpace ℝ (Fin p)).prod
      𝓘(ℝ, EuclideanSpace ℝ (Fin q))) 𝓘(ℝ, EuclideanSpace ℝ (Fin (p + q)))
      ((north, north) : Sph p × Sph q) (mu Γ))
      (Γ : EuclideanSpace ℝ (Fin p) × EuclideanSpace ℝ (Fin q) →L[ℝ]
        EuclideanSpace ℝ (Fin (p + q)))
      (Ft hM hMc hne f north x, Ft hM hMc hne g north x) := by
    have h := (hasMFDerivAt_mu Γ).2
    rw [ModelWithCorners.range_eq_univ] at h
    have hpt : (extChartAt (𝓘(ℝ, EuclideanSpace ℝ (Fin p)).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin q)))
        ((north, north) : Sph p × Sph q)) (north, north) =
        (Ft hM hMc hne f north x, Ft hM hMc hne g north x) := by
      rw [extChartAt_prod, Ft_of_mem hM hMc hne hx, Ft_of_mem hM hMc hne hx, hfx, hgx]
      rfl
    rw [hpt] at h
    exact hasFDerivWithinAt_univ.1 h
  have hpair : HasFDerivAt (fun z => (Ft hM hMc hne f north z, Ft hM hMc hne g north z))
      ((At hM hMc hne f north x).prod (At hM hMc hne g north x)) x :=
    (hasFDerivAt_Ft hM hMc hne hf hxW).prodMk (hasFDerivAt_Ft hM hMc hne hg hxW')
  have hchain := (hD.comp x hpair).congr_of_eventuallyEq hev
  show fderiv ℝ (Ft hM hMc hne (fun z => mu Γ (f z, g z)) north) x = _
  exact hchain.fderiv

section muBasis

variable {p q : ℕ} (Γ : (EuclideanSpace ℝ (Fin p) × EuclideanSpace ℝ (Fin q)) ≃L[ℝ]
      EuclideanSpace ℝ (Fin (p + q)))

/-- `B = Γ ∘ (b × b') ∘ (ℝ^{p+q} ≅ ℝᵖ × ℝ^q)`, where `b eᵢ = bᵢ`, `b' eⱼ = b'ⱼ`. -/
def muB (e : Fin p → EuclideanSpace ℝ (Fin p)) (e' : Fin q → EuclideanSpace ℝ (Fin q)) :
    EuclideanSpace ℝ (Fin (p + q)) →L[ℝ] EuclideanSpace ℝ (Fin (p + q)) :=
  (Γ : EuclideanSpace ℝ (Fin p) × EuclideanSpace ℝ (Fin q) →L[ℝ]
    EuclideanSpace ℝ (Fin (p + q))).comp (((basisCLM e).prodMap (basisCLM e')).comp
      (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := p) (m := q) :
        EuclideanSpace ℝ (Fin (p + q)) →L[ℝ] EuclideanSpace ℝ (Fin p) × EuclideanSpace ℝ (Fin q)))

/-- **The basis of `T_north S^{p+q}` for the product**: `β_k = B e_k`. -/
def muBasis (e : Fin p → EuclideanSpace ℝ (Fin p)) (e' : Fin q → EuclideanSpace ℝ (Fin q))
    (k : Fin (p + q)) : EuclideanSpace ℝ (Fin (p + q)) :=
  muB Γ e e' (EuclideanSpace.single k 1)

variable {e : Fin p → EuclideanSpace ℝ (Fin p)} {e' : Fin q → EuclideanSpace ℝ (Fin q)}

theorem injective_muB (he : LinearIndependent ℝ e) (he' : LinearIndependent ℝ e') :
    Injective (muB Γ e e') :=
  Γ.injective.comp (((basisCLM_injective he).prodMap (basisCLM_injective he')).comp
    (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := p) (m := q)).injective)

theorem surjective_muB (he : LinearIndependent ℝ e) (he' : LinearIndependent ℝ e') :
    Surjective (muB Γ e e') :=
  Γ.surjective.comp (((basisCLM_bijective he).2.prodMap (basisCLM_bijective he').2).comp
    (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := p) (m := q)).surjective)

theorem linearIndependent_muBasis (he : LinearIndependent ℝ e) (he' : LinearIndependent ℝ e') :
    LinearIndependent ℝ (muBasis Γ e e') :=
  (linearIndependent_single (m := p + q)).map'
    (muB Γ e e' : EuclideanSpace ℝ (Fin (p + q)) →ₗ[ℝ] EuclideanSpace ℝ (Fin (p + q)))
    (LinearMap.ker_eq_bot.2 (injective_muB Γ he he'))

end muBasis

section pontMuEq

variable {f : M → Sph p} {g : M → Sph q}
  (hf : letI := hM.chartedSpace; haveI := hM.isManifold;
    ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) ∞ f)
  (hg : letI := hM.chartedSpace; haveI := hM.isManifold;
    ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 𝓘(ℝ, EuclideanSpace ℝ (Fin q)) ∞ g)
  (hy : letI := hM.chartedSpace; haveI := hM.isManifold;
    IsRegularValue 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) f north)
  (hy' : letI := hM.chartedSpace; haveI := hM.isManifold;
    IsRegularValue 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 𝓘(ℝ, EuclideanSpace ℝ (Fin q)) g north)
  {e : Fin p → EuclideanSpace ℝ (Fin p)} {e' : Fin q → EuclideanSpace ℝ (Fin q)}
  (he : LinearIndependent ℝ e) (he' : LinearIndependent ℝ e')
  (Γ : (EuclideanSpace ℝ (Fin p) × EuclideanSpace ℝ (Fin q)) ≃L[ℝ] EuclideanSpace ℝ (Fin (p + q)))

include hf hg hy hy' he he' in
/-- `dF̃_{μ∘(f,g)} = B ∘ (α_F, α_G)` at the points of `f⁻¹(north) ∩ g⁻¹(north)`. -/
theorem At_mu_eq (hnp : n + p = m) (hnq : n' + q = m) (x : M) (hxf : f x = north)
    (hxg : g x = north) :
    At hM hMc hne (fun z => mu Γ (f z, g z)) north x.1 =
      (muB Γ e e').comp (pairA (fun i => pontV hM hMc hne f north e i ⟨x, hxf⟩)
        (fun j => pontV hM hMc hne g north e' j ⟨x, hxg⟩)) := by
  rw [At_mu hM hMc hne Γ hf hg x.2 hxf hxg]
  refine ContinuousLinearMap.ext fun z => ?_
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
    At_eq_basisCLM_dual hM hMc hne hnp hf hy he ⟨x, hxf⟩ z,
    At_eq_basisCLM_dual hM hMc hne hnq hg hy' he' ⟨x, hxg⟩ z]
  show Γ (basisCLM e (dualOf (fun i => pontV hM hMc hne f north e i ⟨x, hxf⟩) z),
      basisCLM e' (dualOf (fun j => pontV hM hMc hne g north e' j ⟨x, hxg⟩) z)) =
    Γ ((basisCLM e).prodMap (basisCLM e') (EuclideanSpace.finAddEquivProd
      ((prodEuc p q) (dualOf (fun i => pontV hM hMc hne f north e i ⟨x, hxf⟩) z,
        dualOf (fun j => pontV hM hMc hne g north e' j ⟨x, hxg⟩) z))))
  rw [ContinuousLinearEquiv.apply_symm_apply]
  rfl

include hf hg hy hy' he he' in
/-- **The Pontryagin manifold of `μ ∘ (f, g)` at the north pole is the transverse intersection**
of the Pontryagin manifolds of `f` and `g` (with the framing basis `β = muBasis`). -/
theorem pontryagin_mu_eq (hnp : n + p = m) (hnq : n' + q = m)
    (htr : Transverse hM (pontryagin hM hMc hne hf hy hnp e he).hN
      (pontryagin hM hMc hne hg hy' hnq e' he').hN) (hr : r + (p + q) = m) :
    letI := hM.chartedSpace; haveI := hM.isManifold;
    ∃ (hh : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 𝓘(ℝ, EuclideanSpace ℝ (Fin (p + q))) ∞
        (fun z => mu Γ (f z, g z)))
      (hyh : IsRegularValue 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 𝓘(ℝ, EuclideanSpace ℝ (Fin (p + q)))
        (fun z => mu Γ (f z, g z)) north),
      pontryagin hM hMc hne hh hyh hr (muBasis Γ e e') (linearIndependent_muBasis Γ he he') =
        (pontryagin hM hMc hne hf hy hnp e he).inter (pontryagin hM hMc hne hg hy' hnq e' he')
          htr hr := by
  letI := hM.chartedSpace
  haveI := hM.isManifold
  have hh : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 𝓘(ℝ, EuclideanSpace ℝ (Fin (p + q))) ∞
      (fun z => mu Γ (f z, g z)) := (contMDiff_mu Γ).comp (hf.prodMk hg)
  have hpre : (fun z => mu Γ (f z, g z)) ⁻¹' {north} = f ⁻¹' {north} ∩ g ⁻¹' {north} := by
    ext z
    simp only [mem_preimage, mem_singleton_iff, mem_inter_iff]
    exact mu_eq_north_iff Γ _
  have hyh : IsRegularValue 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 𝓘(ℝ, EuclideanSpace ℝ (Fin (p + q)))
      (fun z => mu Γ (f z, g z)) north := by
    intro x hx
    have hx' : f x = north ∧ g x = north := (mu_eq_north_iff Γ _).1 hx
    have hsrc : (fun z => mu Γ (f z, g z)) ⟨x.1, x.2⟩ ∈
        (extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin (p + q))) north).source := by
      rw [Subtype.coe_eta, hx]; exact mem_extChartAt_source _
    have hsurj : Surjective (At hM hMc hne (fun z => mu Γ (f z, g z)) north x.1) := by
      rw [At_mu_eq hM hMc hne hf hg hy hy' he he' Γ hnp hnq x hx'.1 hx'.2]
      exact (surjective_muB Γ he he').comp (surjective_pairA_of_transverse
        (pontryagin hM hMc hne hf hy hnp e he) (pontryagin hM hMc hne hg hy' hnq e' he') htr x
          hx'.1 hx'.2)
    exact isRegularPoint_of_surjective_At hM hMc hne hh x.2 hsrc hsurj
  refine ⟨hh, hyh, FramedSub.ext' hM hpre ?_⟩
  intro k x hx hx'
  have hx'' : f x = north ∧ g x = north := hx'
  show pontV hM hMc hne (fun z => mu Γ (f z, g z)) north (muBasis Γ e e') k ⟨x, hx⟩ =
    interFrame (pontryagin hM hMc hne hf hy hnp e he) (pontryagin hM hMc hne hg hy' hnq e' he') k
      ⟨x, hx'⟩
  refine pontV_eq_of hM hMc hne hh hyh hr ⟨x, hx⟩
    (((pontryagin hM hMc hne hf hy hnp e he).inter (pontryagin hM hMc hne hg hy' hnq e' he') htr
      hr).tangent k ⟨x, hx'⟩) ?_ _ k ?_
  · intro v hv
    rw [tangentN_congr hM hpre (isSliceSubmanifold_level hM hh hyh hr)
      ((pontryagin hM hMc hne hf hy hnp e he).inter (pontryagin hM hMc hne hg hy' hnq e' he') htr
        hr).hN ⟨x, hx⟩] at hv
    exact ((pontryagin hM hMc hne hf hy hnp e he).inter (pontryagin hM hMc hne hg hy' hnq e' he')
      htr hr).normal k ⟨x, hx'⟩ v hv
  · rw [At_mu_eq hM hMc hne hf hg hy hy' he he' Γ hnp hnq x hx''.1 hx''.2,
      ContinuousLinearMap.comp_apply]
    exact congrArg (muB Γ e e') (pairA_interV (surjective_pairA_of_transverse
      (pontryagin hM hMc hne hf hy hnp e he) (pontryagin hM hMc hne hg hy' hnq e' he') htr x
        hx''.1 hx''.2) k)

end pontMuEq

end InterProd

end pontMu

/-! ### Changing the framing basis by positive scalings -/

section bases

variable (hM) (hMc : IsCompact M) (hne : M.Nonempty)

namespace InterProd

theorem pontryagin_congr_fun {f f' : M → Sph p} (h : f = f')
    (hf : letI := hM.chartedSpace; haveI := hM.isManifold;
      ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) ∞ f)
    (hf' : letI := hM.chartedSpace; haveI := hM.isManifold;
      ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) ∞ f')
    {y : Sph p}
    (hy : letI := hM.chartedSpace; haveI := hM.isManifold;
      IsRegularValue 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) f y)
    (hy' : letI := hM.chartedSpace; haveI := hM.isManifold;
      IsRegularValue 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) f' y)
    (hnp : n + p = m) (e : Fin p → EuclideanSpace ℝ (Fin p)) (he : LinearIndependent ℝ e) :
    pontryagin hM hMc hne hf hy hnp e he = pontryagin hM hMc hne hf' hy' hnp e he := by
  subst h; rfl

theorem pontryagin_congr_basis {f : M → Sph p}
    (hf : letI := hM.chartedSpace; haveI := hM.isManifold;
      ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) ∞ f)
    {y : Sph p}
    (hy : letI := hM.chartedSpace; haveI := hM.isManifold;
      IsRegularValue 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) f y)
    (hnp : n + p = m) {e e' : Fin p → EuclideanSpace ℝ (Fin p)} (h : e = e')
    (he : LinearIndependent ℝ e) (he' : LinearIndependent ℝ e') :
    pontryagin hM hMc hne hf hy hnp e he = pontryagin hM hMc hne hf hy hnp e' he' := by
  subst h; rfl

/-- **Lemma 1 for positive diagonal changes of basis.** -/
theorem framedCobordant_diag (hnp : n + p = m) {f : M → Sph p}
    (hf : letI := hM.chartedSpace; haveI := hM.isManifold;
      ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) ∞ f)
    {y : Sph p}
    (hy : letI := hM.chartedSpace; haveI := hM.isManifold;
      IsRegularValue 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) f y)
    {e : Fin p → EuclideanSpace ℝ (Fin p)} (he : LinearIndependent ℝ e) {d : Fin p → ℝ}
    (hd : ∀ i, 0 < d i) (hde : LinearIndependent ℝ (fun i => d i • e i)) :
    FramedCobordant hM (pontryagin hM hMc hne hf hy hnp (fun i => d i • e i) hde)
      (pontryagin hM hMc hne hf hy hnp e he) :=
  framedCobordant_of_det_pos hM hMc hne hnp hf hy he hde (A := Matrix.diagonal d)
    (by rw [Matrix.det_diagonal]; exact Finset.prod_pos fun i _ => hd i)
    (by funext j; simp [GLp.mulTuple, Matrix.diagonal_apply])

end InterProd

end bases

namespace InterProd

section gamma

variable {p q : ℕ}

/-- The linear equivalence `ℝᵖ × ℝ^q ≃ ℝ^{p+q}` with `(bᵢ, 0) ↦ γ_{castAdd i}` and
`(0, b'ⱼ) ↦ γ_{natAdd j}`. -/
def gammaOf (b : Basis (Fin p) ℝ (EuclideanSpace ℝ (Fin p)))
    (b' : Basis (Fin q) ℝ (EuclideanSpace ℝ (Fin q)))
    (γ : Basis (Fin (p + q)) ℝ (EuclideanSpace ℝ (Fin (p + q)))) :
    (EuclideanSpace ℝ (Fin p) × EuclideanSpace ℝ (Fin q)) ≃L[ℝ] EuclideanSpace ℝ (Fin (p + q)) :=
  LinearEquiv.toContinuousLinearEquiv
    ((b.prod b').equiv (γ.reindex finSumFinEquiv.symm) (Equiv.refl _))

variable (b : Basis (Fin p) ℝ (EuclideanSpace ℝ (Fin p)))
  (b' : Basis (Fin q) ℝ (EuclideanSpace ℝ (Fin q)))
  (γ : Basis (Fin (p + q)) ℝ (EuclideanSpace ℝ (Fin (p + q))))

theorem gammaOf_inl (i : Fin p) : gammaOf b b' γ (b i, 0) = γ (Fin.castAdd q i) := by
  have h : ((b i, 0) : EuclideanSpace ℝ (Fin p) × EuclideanSpace ℝ (Fin q)) =
      (b.prod b') (Sum.inl i) := by
    ext1
    · rw [Module.Basis.prod_apply_inl_fst]
    · rw [Module.Basis.prod_apply_inl_snd]
  show ((b.prod b').equiv (γ.reindex finSumFinEquiv.symm) (Equiv.refl _)) (b i, 0) = _
  rw [h, Module.Basis.equiv_apply, Module.Basis.reindex_apply]
  simp

theorem gammaOf_inr (j : Fin q) : gammaOf b b' γ (0, b' j) = γ (Fin.natAdd p j) := by
  have h : ((0, b' j) : EuclideanSpace ℝ (Fin p) × EuclideanSpace ℝ (Fin q)) =
      (b.prod b') (Sum.inr j) := by
    ext1
    · rw [Module.Basis.prod_apply_inr_fst]
    · rw [Module.Basis.prod_apply_inr_snd]
  show ((b.prod b').equiv (γ.reindex finSumFinEquiv.symm) (Equiv.refl _)) (0, b' j) = _
  rw [h, Module.Basis.equiv_apply, Module.Basis.reindex_apply]
  simp

theorem finAddEquivProd_single_castAdd (i : Fin p) :
    EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := p) (m := q)
      (EuclideanSpace.single (Fin.castAdd q i) 1) = (EuclideanSpace.single i 1, 0) := by
  ext j
  · simp [EuclideanSpace.finAddEquivProd, EuclideanSpace.sumEquivProd]
  · simp [EuclideanSpace.finAddEquivProd, EuclideanSpace.sumEquivProd]

theorem finAddEquivProd_single_natAdd (j : Fin q) :
    EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := p) (m := q)
      (EuclideanSpace.single (Fin.natAdd p j) 1) = (0, EuclideanSpace.single j 1) := by
  ext i
  · simp [EuclideanSpace.finAddEquivProd, EuclideanSpace.sumEquivProd]
  · simp [EuclideanSpace.finAddEquivProd, EuclideanSpace.sumEquivProd]

/-- The scalings of the product basis. -/
def scal (c c' : ℝ) (k : Fin (p + q)) : ℝ := Fin.addCases (motive := fun _ => ℝ) (fun _ => c) (fun _ => c') k

theorem scal_pos {c c' : ℝ} (hc : 0 < c) (hc' : 0 < c') (k : Fin (p + q)) : 0 < scal c c' k := by
  induction k using Fin.addCases with
  | left i => simpa [scal] using hc
  | right j => simpa [scal] using hc'

/-- **The framing basis of the product is a positive diagonal rescaling of `γ`.** -/
theorem muBasis_gammaOf (c c' : ℝ) :
    muBasis (gammaOf b b' γ) (fun i => c • b i) (fun j => c' • b' j) =
      fun k => scal c c' k • γ k := by
  funext k
  induction k using Fin.addCases with
  | left i =>
    show gammaOf b b' γ ((basisCLM (fun i => c • b i)).prodMap (basisCLM (fun j => c' • b' j))
      (EuclideanSpace.finAddEquivProd (EuclideanSpace.single (Fin.castAdd q i) 1))) = _
    rw [finAddEquivProd_single_castAdd, ContinuousLinearMap.coe_prodMap', Prod.map_apply,
      basisCLM_single, map_zero]
    have : ((c • b i, 0) : EuclideanSpace ℝ (Fin p) × EuclideanSpace ℝ (Fin q)) = c • (b i, 0) := by
      simp
    rw [this, map_smul, gammaOf_inl]
    simp [scal]
  | right j =>
    show gammaOf b b' γ ((basisCLM (fun i => c • b i)).prodMap (basisCLM (fun j => c' • b' j))
      (EuclideanSpace.finAddEquivProd (EuclideanSpace.single (Fin.natAdd p j) 1))) = _
    rw [finAddEquivProd_single_natAdd, ContinuousLinearMap.coe_prodMap', Prod.map_apply,
      basisCLM_single, map_zero]
    have : ((0, c' • b' j) : EuclideanSpace ℝ (Fin p) × EuclideanSpace ℝ (Fin q)) = c' • (0, b' j) := by
      simp
    rw [this, map_smul, gammaOf_inr]
    simp [scal]

end gamma

end InterProd

/-! ### Transverse representatives -/

section transverse

variable (hM) (hMc : IsCompact M) (hne : M.Nonempty)

namespace InterProd

/-- The tangent space of a level set `f⁻¹(y)` (chart level) is the kernel of `df`. -/
theorem range_mfd_val_level (hnp : n + p = m) {f : M → Sph p}
    (hf : letI := hM.chartedSpace; haveI := hM.isManifold;
      ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) ∞ f)
    {y : Sph p}
    (hy : letI := hM.chartedSpace; haveI := hM.isManifold;
      IsRegularValue 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) f y)
    (x : f ⁻¹' {y}) :
    letI := hM.chartedSpace; haveI := hM.isManifold;
    letI := (isSliceSubmanifold_level hM hf hy hnp).chartedSpace;
    LinearMap.range ((mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, EuclideanSpace ℝ (Fin m))
      (Subtype.val : f ⁻¹' {y} → M) x : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m)) :
        EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin m)) =
      LinearMap.ker ((mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) f x.1 :
        EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin p)) :
          EuclideanSpace ℝ (Fin m) →ₗ[ℝ] EuclideanSpace ℝ (Fin p)) := by
  letI := hM.chartedSpace
  haveI := hM.isManifold
  have hS := isSliceSubmanifold_level hM hf hy hnp
  letI := hS.chartedSpace
  haveI := hS.isManifold
  have hle : LinearMap.range ((mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, EuclideanSpace ℝ (Fin m))
      (Subtype.val : f ⁻¹' {y} → M) x : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m)) :
        EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin m)) ≤
      LinearMap.ker ((mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) f x.1 :
        EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin p)) :
          EuclideanSpace ℝ (Fin m) →ₗ[ℝ] EuclideanSpace ℝ (Fin p)) := by
    rintro _ ⟨v, rfl⟩
    have h0 := mfderiv_comp_val_eq_zero hf hS x
    exact LinearMap.mem_ker.2 (DFunLike.congr_fun h0 v)
  have h1 : finrank ℝ (LinearMap.range ((mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
      𝓘(ℝ, EuclideanSpace ℝ (Fin m)) (Subtype.val : f ⁻¹' {y} → M) x :
        EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m)) :
          EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin m))) = n := by
    have hinj : Injective (mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, EuclideanSpace ℝ (Fin m))
        (Subtype.val : f ⁻¹' {y} → M) x) := injective_mfderiv_val hS x
    rw [LinearMap.finrank_range_of_inj hinj, finrank_euclideanSpace_fin]
  have hsurj : Surjective (mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 𝓘(ℝ, EuclideanSpace ℝ (Fin p))
      f x.1) := hy x.1 x.2
  have h2 := LinearMap.finrank_range_add_finrank_ker ((mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin m))
    𝓘(ℝ, EuclideanSpace ℝ (Fin p)) f x.1 : EuclideanSpace ℝ (Fin m) →L[ℝ]
      EuclideanSpace ℝ (Fin p)) : EuclideanSpace ℝ (Fin m) →ₗ[ℝ] EuclideanSpace ℝ (Fin p))
  rw [LinearMap.range_eq_top.2 hsurj, finrank_top, finrank_euclideanSpace_fin,
    finrank_euclideanSpace_fin] at h2
  exact Submodule.eq_of_le_of_finrank_eq hle (by omega)

include hMc hne in
/-- **Moving a framed submanifold within its class to meet `N'` transversally**: replace the
regular value `north` of a Theorem-B map `f` of `F₀` by a nearby common regular value of `f` and
of `f|N'` (Brown's theorem), and use Lemmas 1 and 2 of §7. -/
theorem exists_transverse_cobordant (hp : 1 ≤ p) (F₀ : FramedSub hM n p)
    (G : FramedSub hM n' q) :
    ∃ F : FramedSub hM n p, FramedCobordant hM F F₀ ∧ Transverse hM F.hN G.hN := by
  letI := hM.chartedSpace
  haveI := hM.isManifold
  have hnp : n + p = m := F₀.dim
  obtain ⟨b, hb⟩ := exists_posBasis hp (north : Sph p)
  obtain ⟨f, hf, hy, c, hc, hcb, hF₀⟩ :=
    exists_map_of_framedSub hM hMc hne F₀ b b.linearIndependent
  letI := G.hN.chartedSpace
  haveI := G.hN.isManifold
  have hfG : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n')) 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) ∞
      (fun x : G.N => f x.1) := hf.comp G.hN.contMDiff_val
  obtain ⟨z, hzf, hzG⟩ := (dense_regularValues hfG).inter_open_nonempty _
    (isOpen_regularValues_sph hM hMc hne hf) ⟨north, hy⟩
  have hzf' : IsRegularValue 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) f z :=
    hzf
  obtain ⟨e, he⟩ := exists_posBasis hp z
  refine ⟨pontryagin hM hMc hne hf hzf' hnp e e.linearIndependent, ?_, ?_⟩
  · have h1 := framedCobordant_of_regularValues hM hMc hne hf hnp hp hzf' hy e he b hb
    have h2 := framedCobordant_diag hM hMc hne hnp hf hy b.linearIndependent (d := fun _ => c)
      (fun _ => hc) hcb
    rw [← hF₀]
    exact h1.trans h2.symm
  · refine (Transversality.transverse_iff hM (isSliceSubmanifold_level hM hf hzf' hnp) G.hN).2
      fun x hx hx' => ?_
    have hreg : Surjective (mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin n')) 𝓘(ℝ, EuclideanSpace ℝ (Fin p))
        (fun x : G.N => f x.1) ⟨x, hx'⟩) := hzG ⟨x, hx'⟩ hx
    have hval : MDifferentiableAt 𝓘(ℝ, EuclideanSpace ℝ (Fin n')) 𝓘(ℝ, EuclideanSpace ℝ (Fin m))
        (Subtype.val : G.N → M) ⟨x, hx'⟩ := G.hN.contMDiff_val.mdifferentiableAt (by simp)
    have hfx : MDifferentiableAt 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) f x :=
      hf.mdifferentiableAt (by simp)
    have hchain : mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin n')) 𝓘(ℝ, EuclideanSpace ℝ (Fin p))
        (fun x : G.N => f x.1) ⟨x, hx'⟩ =
        (mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) f x).comp
          (mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin n')) 𝓘(ℝ, EuclideanSpace ℝ (Fin m))
            (Subtype.val : G.N → M) ⟨x, hx'⟩) :=
      HasMFDerivAt.mfd_eq ((hasMFDerivAt_mfd hfx).comp (⟨x, hx'⟩ : G.N) (hasMFDerivAt_mfd hval))
    rw [hchain] at hreg
    rw [range_mfd_val_level hM hnp hf hzf' ⟨x, hx⟩]
    exact Transversality.ker_sup_range_eq_top_of_surjective_comp hreg

end InterProd

/-- **Every pair of classes has transverse representatives.** -/
theorem exists_transverse_rep (hp : 1 ≤ p) (c : FramedClass hM hMc hne n p)
    (c' : FramedClass hM hMc hne n' q) :
    ∃ (F : FramedSub hM n p) (G : FramedSub hM n' q), ⟦F⟧ = c ∧ ⟦G⟧ = c' ∧
      Transverse hM F.hN G.hN := by
  obtain ⟨F₀, rfl⟩ := Quotient.exists_rep c
  obtain ⟨G, rfl⟩ := Quotient.exists_rep c'
  obtain ⟨F, hF, htr⟩ := InterProd.exists_transverse_cobordant hM hMc hne hp F₀ G
  exact ⟨F, G, Quotient.sound hF, rfl, htr⟩

end transverse

/-! ### Invariance and the product of classes -/

section product

variable (hM) (hMc : IsCompact M) (hne : M.Nonempty)

namespace InterProd

include hMc hne in
/-- **Invariance of the intersection under framed cobordism.** If `F ∼ F₁` and `G ∼ G₁` (both
pairs transverse), then `F ∩ G ∼ F₁ ∩ G₁`.  Proof: by Theorem B, `F = Pont(f, north, c b)` etc.;
by Theorem A (converse), `f ≃ f₁` and `g ≃ g₁`, so `μ ∘ (f, g) ≃ μ ∘ (f₁, g₁)`; the Pontryagin
manifolds of these maps are the intersections, with framing bases which are positive diagonal
rescalings of the positive basis `γ` (by the choice of `μ`), so Lemma 1 and Theorem A apply. -/
theorem framedCobordant_inter (hp : 1 ≤ p) (hq : 1 ≤ q) (hr : r + (p + q) = m)
    {F F₁ : FramedSub hM n p} {G G₁ : FramedSub hM n' q}
    (hF : FramedCobordant hM F F₁) (hG : FramedCobordant hM G G₁)
    (htr : Transverse hM F.hN G.hN) (htr₁ : Transverse hM F₁.hN G₁.hN) :
    FramedCobordant hM (F.inter G htr hr) (F₁.inter G₁ htr₁ hr) := by
  letI := hM.chartedSpace
  haveI := hM.isManifold
  have hnp : n + p = m := F.dim
  have hnq : n' + q = m := G.dim
  have hpq : 1 ≤ p + q := by omega
  obtain ⟨b, hb⟩ := exists_posBasis hp (north : Sph p)
  obtain ⟨b', hb'⟩ := exists_posBasis hq (north : Sph q)
  obtain ⟨γ, hγ⟩ := exists_posBasis hpq (north : Sph (p + q))
  obtain ⟨f, hf, hy, c, hc, hcb, hF'⟩ := exists_map_of_framedSub hM hMc hne F b b.linearIndependent
  obtain ⟨f₁, hf₁, hy₁, c₁, hc₁, hcb₁, hF₁'⟩ :=
    exists_map_of_framedSub hM hMc hne F₁ b b.linearIndependent
  obtain ⟨g, hg, hz, d, hd, hdb, hG'⟩ := exists_map_of_framedSub hM hMc hne G b' b'.linearIndependent
  obtain ⟨g₁, hg₁, hz₁, d₁, hd₁, hdb₁, hG₁'⟩ :=
    exists_map_of_framedSub hM hMc hne G₁ b' b'.linearIndependent
  have e1 : pontryagin hM hMc hne hf hy hnp (fun i => c • b i) hcb = F := hF'
  have e2 : pontryagin hM hMc hne hf₁ hy₁ hnp (fun i => c₁ • b i) hcb₁ = F₁ := hF₁'
  have e3 : pontryagin hM hMc hne hg hz hnq (fun i => d • b' i) hdb = G := hG'
  have e4 : pontryagin hM hMc hne hg₁ hz₁ hnq (fun i => d₁ • b' i) hdb₁ = G₁ := hG₁'
  clear hF' hF₁' hG' hG₁'
  subst e1 e2 e3 e4
  -- `f ≃ f₁` and `g ≃ g₁` (Theorem A, converse)
  have hff : SmoothHomotopic 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) f f₁ :=
    smoothHomotopic_of_framedCobordant hM hMc hne hnp hp hf hf₁ hy hy₁ b hb b hb
      (((framedCobordant_diag hM hMc hne hnp hf hy b.linearIndependent (d := fun _ => c)
        (fun _ => hc) hcb).symm.trans hF).trans
        (framedCobordant_diag hM hMc hne hnp hf₁ hy₁ b.linearIndependent (d := fun _ => c₁)
          (fun _ => hc₁) hcb₁))
  have hgg : SmoothHomotopic 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 𝓘(ℝ, EuclideanSpace ℝ (Fin q)) g g₁ :=
    smoothHomotopic_of_framedCobordant hM hMc hne hnq hq hg hg₁ hz hz₁ b' hb' b' hb'
      (((framedCobordant_diag hM hMc hne hnq hg hz b'.linearIndependent (d := fun _ => d)
        (fun _ => hd) hdb).symm.trans hG).trans
        (framedCobordant_diag hM hMc hne hnq hg₁ hz₁ b'.linearIndependent (d := fun _ => d₁)
          (fun _ => hd₁) hdb₁))
  obtain ⟨Hf, hHf, hHf0, hHf1⟩ := hff
  obtain ⟨Hg, hHg, hHg0, hHg1⟩ := hgg
  -- the homotopy `μ ∘ (Hf, Hg)`
  obtain ⟨Γ, hΓ⟩ : ∃ Γ, gammaOf b b' γ = Γ := ⟨_, rfl⟩
  obtain ⟨H, hHdef⟩ : ∃ H : M × ℝ → Sph (p + q), H = fun w => mu Γ (Hf w, Hg w) := ⟨_, rfl⟩
  have hH : ContMDiff (𝓘(ℝ, EuclideanSpace ℝ (Fin m)).prod 𝓘(ℝ, ℝ))
      𝓘(ℝ, EuclideanSpace ℝ (Fin (p + q))) ∞ H := by
    rw [hHdef]; exact (contMDiff_mu Γ).comp (hHf.prodMk hHg)
  have hH0 : (fun x => H (x, 0)) = fun z => mu Γ (f z, g z) := by
    funext x; rw [hHdef]; simp only [hHf0, hHg0]
  have hH1 : (fun x => H (x, 1)) = fun z => mu Γ (f₁ z, g₁ z) := by
    funext x; rw [hHdef]; simp only [hHf1, hHg1]
  -- the Pontryagin manifolds of `μ ∘ (f, g)` and `μ ∘ (f₁, g₁)` are the intersections
  obtain ⟨hh, hyh, heq⟩ := pontryagin_mu_eq hM hMc hne hf hg hy hz hcb hdb Γ hnp hnq htr hr
  obtain ⟨hh₁, hyh₁, heq₁⟩ :=
    pontryagin_mu_eq hM hMc hne hf₁ hg₁ hy₁ hz₁ hcb₁ hdb₁ Γ hnp hnq htr₁ hr
  rw [← heq, ← heq₁]
  -- Theorem A for the homotopy, with the positive basis `γ`
  have hA := framedCobordant_of_homotopic hM hMc hne hr hpq hH (hH0 ▸ hh) (hH1 ▸ hh₁)
    (hH0 ▸ hyh) (hH1 ▸ hyh₁) γ hγ γ hγ
  rw [pontryagin_congr_fun hM hMc hne hH0 _ hh _ hyh, pontryagin_congr_fun hM hMc hne hH1 _ hh₁ _
    hyh₁] at hA
  -- Lemma 1 for the diagonal rescalings
  have hβ := muBasis_gammaOf b b' γ c d
  have hβ₁ := muBasis_gammaOf b b' γ c₁ d₁
  rw [hΓ] at hβ hβ₁
  have hL : FramedCobordant hM
      (pontryagin hM hMc hne hh hyh hr (muBasis Γ (fun i => c • b i) (fun j => d • b' j))
        (linearIndependent_muBasis Γ hcb hdb))
      (pontryagin hM hMc hne hh hyh hr γ γ.linearIndependent) := by
    rw [pontryagin_congr_basis hM hMc hne hh hyh hr hβ _ (hβ ▸ linearIndependent_muBasis Γ hcb hdb)]
    exact framedCobordant_diag hM hMc hne hr hh hyh γ.linearIndependent (scal_pos hc hd) _
  have hL₁ : FramedCobordant hM
      (pontryagin hM hMc hne hh₁ hyh₁ hr (muBasis Γ (fun i => c₁ • b i) (fun j => d₁ • b' j))
        (linearIndependent_muBasis Γ hcb₁ hdb₁))
      (pontryagin hM hMc hne hh₁ hyh₁ hr γ γ.linearIndependent) := by
    rw [pontryagin_congr_basis hM hMc hne hh₁ hyh₁ hr hβ₁ _
      (hβ₁ ▸ linearIndependent_muBasis Γ hcb₁ hdb₁)]
    exact framedCobordant_diag hM hMc hne hr hh₁ hyh₁ γ.linearIndependent (scal_pos hc₁ hd₁) _
  exact (hL.trans hA).trans hL₁.symm

end InterProd

/-- **Milnor §8, Problem 17 (first part): the intersection product.** Transverse intersection
induces a well defined correspondence `Πᵖ(M) × Π^q(M) → Π^{p+q}(M)` on framed cobordism classes:
there is a map `μ` with `μ [F] [G] = [F ∩ G]` whenever `F` and `G` meet transversally. -/
theorem exists_intersection_product (hr : r + (p + q) = m) (hp : 1 ≤ p) (hq : 1 ≤ q) :
    ∃ μ : FramedClass hM hMc hne n p → FramedClass hM hMc hne n' q →
        FramedClass hM hMc hne r (p + q),
      ∀ (F : FramedSub hM n p) (G : FramedSub hM n' q) (htr : Transverse hM F.hN G.hN),
        μ ⟦F⟧ ⟦G⟧ = ⟦F.inter G htr hr⟧ := by
  choose Fc Gc hFc hGc htrc using fun (c : FramedClass hM hMc hne n p)
    (c' : FramedClass hM hMc hne n' q) => exists_transverse_rep hM hMc hne hp c c'
  refine ⟨fun c c' => ⟦(Fc c c').inter (Gc c c') (htrc c c') hr⟧, fun F G htr => ?_⟩
  apply Quotient.sound
  have h1 : FramedCobordant hM (Fc ⟦F⟧ ⟦G⟧) F := Quotient.exact (hFc ⟦F⟧ ⟦G⟧)
  have h2 : FramedCobordant hM (Gc ⟦F⟧ ⟦G⟧) G := Quotient.exact (hGc ⟦F⟧ ⟦G⟧)
  exact InterProd.framedCobordant_inter hM hMc hne hp hq hr h1 h2 (htrc _ _) htr

/-- The product of classes is uniquely determined by its values on transverse representatives. -/
theorem intersection_product_unique (hr : r + (p + q) = m) (hp : 1 ≤ p)
    {μ₁ μ₂ : FramedClass hM hMc hne n p → FramedClass hM hMc hne n' q →
      FramedClass hM hMc hne r (p + q)}
    (h₁ : ∀ (F : FramedSub hM n p) (G : FramedSub hM n' q) (htr : Transverse hM F.hN G.hN),
      μ₁ ⟦F⟧ ⟦G⟧ = ⟦F.inter G htr hr⟧)
    (h₂ : ∀ (F : FramedSub hM n p) (G : FramedSub hM n' q) (htr : Transverse hM F.hN G.hN),
      μ₂ ⟦F⟧ ⟦G⟧ = ⟦F.inter G htr hr⟧) : μ₁ = μ₂ := by
  funext c c'
  obtain ⟨F, G, rfl, rfl, htr⟩ := exists_transverse_rep hM hMc hne hp c c'
  rw [h₁ F G htr, h₂ F G htr]

end product

end Problems

end Milnor
