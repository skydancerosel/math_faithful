import Morse
import RoundTrip.Check
import RoundTrip.Blind.V4_10

open Module
open scoped ContDiff Manifold RealInnerProductSpace

namespace RoundTrip.V4_10

/-- The project's statement: the two listed theorems; no universe parameters. -/
def A : Prop :=
  type_of% @Morse.isCriticalPointM_normSq_sub_iff_mem_normalBundleSet ∧
  type_of% @Morse.hessian_normSq_sub_xParam

theorem A_holds : A :=
  ⟨@Morse.isCriticalPointM_normSq_sub_iff_mem_normalBundleSet, @Morse.hessian_normSq_sub_xParam⟩

/-- Membership in the normal bundle, in B's words: `(q, p − q) ∈ N` iff `q − p ⊥ T_qM`. -/
theorem mem_normalBundleSet_iff' {n k w : ℕ} {M : Set (Rn n)}
    (hM : Milnor.IsSliceSubmanifold 𝓘(ℝ, Rn n) (Rn k) (Rn w) M) (p : Rn n) (q : M) :
    ((q : Rn n), p - q) ∈ Milnor.Problems.normalBundleSet hM ↔
      ∀ v ∈ Morse.tangentSubspace hM q, ⟪(q : Rn n) - p, v⟫ = 0 := by
  rw [Morse.mem_normalBundleSet_iff]
  constructor
  · rintro ⟨hq, h⟩ v hv
    have := (Submodule.mem_orthogonal' _ _).1 h v hv
    rw [← neg_sub, inner_neg_left, this, neg_zero]
  · intro h
    refine ⟨q.2, (Submodule.mem_orthogonal' _ _).2 fun v hv ↦ ?_⟩
    have := h v hv
    rw [← neg_sub, inner_neg_left, neg_eq_zero] at this
    exact this

section Calc

variable {k n : ℕ}

lemma d2x_eq {x : Rn k → Rn n} {u : Rn k} (hx : DifferentiableAt ℝ (fderiv ℝ x) u) (i j : Fin k) :
    d2x x u i j = fderiv ℝ (fderiv ℝ x) u (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) := by
  unfold d2x dx
  rw [fderiv_clm_apply hx (differentiableAt_const _)]
  simp

/-- **B's calculus clause holds outright** (any `C²` map `x` on an open set): chain rule, the
project's second-order formula `Morse.hessian_normSq_sub_comp`, and `ℓ_ij = ` normal part of
`∂²x`. -/
theorem B2_holds (x : Rn k → Rn n) (U : Set (Rn k)) (hU : IsOpen U) (hx : ContDiffOn ℝ 2 x U)
    (p : Rn n) (u : Rn k) (hu : u ∈ U) :
    (∀ i, fderiv ℝ (fun w => Lp p (x w)) u (EuclideanSpace.single i 1) =
      2 * inner ℝ (dx x u i) (x u - p)) ∧
    ((∀ i, inner ℝ (dx x u i) (x u - p) = 0) →
      ∀ i j, fderiv ℝ (fun w => fderiv ℝ (fun w' => Lp p (x w')) w (EuclideanSpace.single j 1)) u
          (EuclideanSpace.single i 1) = 2 * (gmat x u i j + inner ℝ (d2x x u i j) (x u - p))) ∧
    ∀ (t : ℝ) (v : Rn n), (∀ l, inner ℝ v (dx x u l) = 0) → p = x u + t • v →
      ∀ i j, fderiv ℝ (fun w => fderiv ℝ (fun w' => Lp p (x w')) w (EuclideanSpace.single j 1)) u
          (EuclideanSpace.single i 1) = 2 * (gmat x u i j - t * sff x u v i j) := by
  have hxu : ContDiffAt ℝ 2 x u := hx.contDiffAt (hU.mem_nhds hu)
  have hdx : DifferentiableAt ℝ (fderiv ℝ x) u :=
    (hxu.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hL : ContDiffAt ℝ 2 (fun w => Lp p (x w)) u :=
    ((Morse.contDiff_normSq_sub p).contDiffAt.of_le (by norm_cast)).comp u hxu
  have hdL : DifferentiableAt ℝ (fderiv ℝ (fun w => Lp p (x w))) u :=
    (hL.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  -- second partials are the Hessian
  have hsec : ∀ i j, fderiv ℝ (fun w => fderiv ℝ (fun w' => Lp p (x w')) w
      (EuclideanSpace.single j 1)) u (EuclideanSpace.single i 1) =
      2 * (gmat x u i j + inner ℝ (d2x x u i j) (x u - p)) := by
    intro i j
    rw [fderiv_clm_apply hdL (differentiableAt_const _)]
    simp
    have := Morse.hessian_normSq_sub_comp hxu p (EuclideanSpace.single i 1)
      (EuclideanSpace.single j 1)
    unfold Morse.hessian at this
    change fderiv ℝ (fderiv ℝ (fun z => ‖x z - p‖ ^ 2)) u _ _ = _
    rw [this, d2x_eq hdx]
    rfl
  refine ⟨fun i ↦ ?_, fun _ ↦ hsec, fun t v hv hp i j ↦ ?_⟩
  · have hxd : DifferentiableAt ℝ x u := hxu.differentiableAt (by norm_num)
    have hc : (fun w => Lp p (x w)) = (fun y : Rn n => ‖y - p‖ ^ 2) ∘ x := rfl
    rw [hc, fderiv_comp u ((Morse.contDiff_normSq_sub p).differentiable (by simp) _) hxd,
      ContinuousLinearMap.comp_apply, Morse.fderiv_normSq_sub_apply, real_inner_comm]
    rfl
  · rw [hsec]
    have hvt : v ∈ (tangSp x u)ᗮ := by
      rw [tangSp, Submodule.mem_orthogonal]
      intro w hw
      induction hw using Submodule.span_induction with
      | mem w hw =>
        obtain ⟨l, rfl⟩ := hw
        rw [real_inner_comm]
        exact hv l
      | zero => exact inner_zero_left _
      | add a b _ _ ha hb => rw [inner_add_left, ha, hb, add_zero]
      | smul c a _ ha => rw [inner_smul_left, ha, mul_zero]
    have hsff : sff x u v i j = inner ℝ v (d2x x u i j) := by
      simp only [sff, ell, Matrix.of_apply]
      rw [← Submodule.inner_starProjection_left_eq_right,
        Submodule.starProjection_eq_self_iff.2 hvt]
    rw [hsff, hp, show x u - (x u + t • v) = -(t • v) by abel, inner_neg_right, inner_smul_right,
      real_inner_comm]
    ring

end Calc

/-- **A ⇒ B.** Clause (1) is A's `isCriticalPointM_normSq_sub_iff_mem_normalBundleSet` read with
`mem_normalBundleSet_iff`; clause (2) (calculus in an arbitrary parametrization) holds outright
(`B2_holds`; A's Hessian formula is only for the project's parametrization `xParam`). -/
theorem A_to_B : A → B := by
  intro hA
  refine ⟨fun K d m M hM p q ↦ ?_, fun k n x U hU hx p u hu ↦ B2_holds x U hU hx p u hu⟩
  let _ := hM.chartedSpace
  exact (hA.1 p q).trans (mem_normalBundleSet_iff' hM p q)

/-- **B ⇒ A.** Clause (1) from B's first clause for `dim M ≥ 1` (dimension `0`: everything is
critical and `T_qM = 0`). Clause (2), the Hessian of `L_p ∘ xParam` at every point (B states the
second partials only where the first partials vanish), is re-proved outright from the project's
`hessian_normSq_sub_comp` (as in the project). -/
theorem B_to_A : B → A := by
  intro hB
  refine ⟨fun {n k w M hM} p q ↦ ?_, fun {n k w M hM} p q ↦ ?_⟩
  · let _ := hM.chartedSpace
    rw [mem_normalBundleSet_iff']
    rcases k with _ | d
    · refine iff_of_true (Morse.isCriticalPointM_of_finrank_eq_zero finrank_euclideanSpace_fin _ q)
        fun v hv ↦ ?_
      obtain ⟨z, rfl⟩ := hv
      rw [show z = 0 from Subsingleton.elim _ _, map_zero, inner_zero_right]
    · have hkw := Morse.slice_dim_add_eq_of_nonempty hM ⟨q.1, q.2⟩
      obtain ⟨K, rfl⟩ : ∃ K, n = K + 1 := ⟨d + w, by omega⟩
      exact hB.1 K d w M hM p q
  · ext ξ η
    rw [Morse.hessian_normSq_sub_comp ((Morse.contDiffAt_xParam hM q).of_le (by norm_cast)) p ξ η,
      Morse.xParam_uParam]
    simp only [FunLike.coe_smul, FunLike.coe_sub, Pi.smul_apply,
      Pi.sub_apply, Morse.firstFF_apply, Morse.secondFF_apply, smul_eq_mul]
    rw [show (q : Rn n) - p = -(p - q) by abel, inner_neg_right, real_inner_comm (p - q)]
    simp only [Morse.dParam, Morse.d2Param]
    ring

#rt_check RoundTrip.V4_10.A_to_B [Morse.isCriticalPointM_normSq_sub_iff_mem_normalBundleSet,
  Morse.hessian_normSq_sub_xParam]
#rt_check RoundTrip.V4_10.B_to_A [Morse.isCriticalPointM_normSq_sub_iff_mem_normalBundleSet,
  Morse.hessian_normSq_sub_xParam]
#rt_overlap RoundTrip.V4_10.B_to_A [Morse.isCriticalPointM_normSq_sub_iff_mem_normalBundleSet,
  Morse.hessian_normSq_sub_xParam]

end RoundTrip.V4_10
